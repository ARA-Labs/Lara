-- | Property tests for the strict-certificate seam ("Lara.Strict") and the
-- reference natural-deduction adapter ("Lara.Strict.ND").
--
-- These cover the backend obligations of @docs/strict-backend-decision.md@ §2
-- and the reference-adapter results of §5 as /conformance evidence/ (not
-- soundness proofs — those are the Lean mechanization, spec §9 closing note):
--
--   * __decidable replay__ (obligation 1) — 'inferType' is total: it returns
--     @Right@ on every well-typed certificate we build and @Left@ on an
--     out-of-range index, never diverging.
--   * __normalization fidelity__ (obligation 2) — @p ≡ q@ iff
--     @encodeND p == encodeND q@.
--   * __certificate soundness__ (Theorem 4) — every valuation satisfying the
--     free context an accepted certificate depends on satisfies its conclusion.
--   * __dependency exactness__ (Lemma 5) — the free slots 'inferType' reports
--     equal the ones the generator actually wired in, computed independently.
--   * __closed registration + seam__ (obligation 5) — an unregistered backend is
--     rejected; a registered adapter, driven through the opaque 'SExpr' wire
--     form, seals a 'StrictJudgment' with the expected conclusion and
--     dependencies.
module StrictSpec (strictSpecProps) where

import Data.List (isPrefixOf, nub)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Test.QuickCheck

import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..), nf)
import Lara.Strict
  ( BackendId (..)
  , Dependency (..)
  , SExpr (..)
  , StrictError (..)
  , TheoryDigest (..)
  , mkRegistry
  , sjConclusion
  , sjDependencies
  , strictCheck
  )
import Lara.Strict.ND
  ( Cert (..)
  , Formula (..)
  , Tag (..)
  , encodeND
  , encodeAtomKey
  , decodeAtomKey
  , decodeFormula
  , decodeCert
  , inferType
  , mkNDBackend
  , ndBackendId
  , parseFrameTag
  , parseTag
  , frameTagToString
  , tagToString
  )
import Lara.Strict.ND.Internal (AtomId (..))
import qualified Lara.AST as A
import qualified Lara.Strict.Cell as Cell
import qualified Lara.Strict.Ord as OrdB
import Lara.Strict.Deps (CertDep (..), certDeps, encodeCertDeps)
import Lara.Driver (buildCertOk)
import Lara.SupportTerm
  ( CertOk
  , CertOutcome (..)
  , CheckError
  , CheckLoc (..)
  , SupportResult (..)
  , inferSupport
  )

-- ---------------------------------------------------------------------------
-- ND formula generators
-- ---------------------------------------------------------------------------

-- | A small pool of atomic formulas keeps the valuation space enumerable.
genAtomF :: Gen Formula
genAtomF = FAtom . AtomId . (: []) <$> elements ['P' .. 'T']

genFormula :: Gen Formula
genFormula = sized go
  where
    go n
      | n <= 0 = oneof [genAtomF, pure FFalse]
      | otherwise =
          frequency
            [ (3, genAtomF)
            , (1, pure FFalse)
            , (2, FImp <$> go (n `div` 2) <*> go (n `div` 2))
            ]

-- ---------------------------------------------------------------------------
-- Well-typed certificates, by construction
--
-- Each builder returns the free context Δ, a certificate, the formula it
-- concludes, and the set of free-context slots it depends on — all computed
-- structurally, so comparing them against 'inferType' is a genuine differential
-- check (Lemma 5), not a restatement.
-- ---------------------------------------------------------------------------

data WellTyped = WellTyped
  { wtFree :: [Formula]
  , wtCert :: Cert
  , wtType :: Formula
  , wtDeps :: Set Int
  }
  deriving (Show)

-- | Pad a core free context with @pre@ formulas in front and @post@ behind. The
-- core's free de Bruijn indices start at @length pre@; the continuation is told
-- that shift so it can address the core.
withPadding :: [Formula] -> ([Formula] -> Int -> a) -> Gen a
withPadding core k = do
  pre <- listOf genAtomF
  post <- listOf genAtomF
  pure (k (pre ++ core ++ post) (length pre))

-- | Family 1: closed tautologies with no free dependencies.
genIdentityFamily :: Gen WellTyped
genIdentityFamily = do
  a <- genFormula
  b <- genFormula
  variant <- elements [True, False]
  let (cert, ty)
        | variant = (Lam a (Hyp 0), FImp a a) -- a -> a
        | otherwise = (Lam a (Lam b (Hyp 1)), FImp a (FImp b a)) -- a -> b -> a
  withPadding [] $ \free _shift ->
    WellTyped {wtFree = free, wtCert = cert, wtType = ty, wtDeps = Set.empty}

-- | Family 2: modus ponens over the free context.
-- Core Δ = [A, A -> B]; @app (hyp 1) (hyp 0) : B@; depends on both slots.
genModusPonensFamily :: Gen WellTyped
genModusPonensFamily = do
  a <- genFormula
  b <- genFormula
  let core = [a, FImp a b]
  withPadding core $ \free shift ->
    WellTyped
      { wtFree = free
      , wtCert = App (Hyp (toInteger (shift + 1))) (Hyp (toInteger shift))
      , wtType = b
      , wtDeps = Set.fromList [shift, shift + 1]
      }

-- | Family 3: falsum elimination. Core Δ = [false]; @abort T (hyp 0) : T@.
genAbortFamily :: Gen WellTyped
genAbortFamily = do
  t <- genFormula
  withPadding [FFalse] $ \free shift ->
    WellTyped
      { wtFree = free
      , wtCert = Abort t (Hyp (toInteger shift))
      , wtType = t
      , wtDeps = Set.singleton shift
      }

genWellTyped :: Gen WellTyped
genWellTyped = oneof [genIdentityFamily, genModusPonensFamily, genAbortFamily]

instance Arbitrary WellTyped where
  arbitrary = genWellTyped

-- ---------------------------------------------------------------------------
-- Boolean interpretation (for Theorem 4)
-- ---------------------------------------------------------------------------

interp :: Map.Map String Bool -> Formula -> Bool
interp _ FFalse = False
interp v (FAtom (AtomId s)) = Map.findWithDefault False s v
interp v (FImp a b) = not (interp v a) || interp v b

atomsOf :: Formula -> [String]
atomsOf FFalse = []
atomsOf (FAtom (AtomId s)) = [s]
atomsOf (FImp a b) = atomsOf a ++ atomsOf b

-- | Every Boolean valuation over the relevant atoms. The atom pool is 5 symbols,
-- so this is at most 2^5 valuations — fully enumerable.
allValuations :: [String] -> [Map.Map String Bool]
allValuations names =
  [Map.fromList (zip syms bits) | bits <- sequence (replicate (length syms) [False, True])]
  where
    syms = nub names

-- ---------------------------------------------------------------------------
-- Cert/Formula -> SExpr serialization (mirrors the adapter's grammar)
-- ---------------------------------------------------------------------------

-- These share the adapter's 'Tag' table via 'tagToString', so the wire
-- keywords are defined in exactly one place; a keyword change in the decoder
-- flows here automatically instead of silently diverging.
tag :: Tag -> SExpr
tag = SAtom . tagToString

formulaToSExpr :: Formula -> SExpr
formulaToSExpr FFalse = tag TFalse
formulaToSExpr (FAtom (AtomId s)) = SList [tag TAtom, SAtom s]
formulaToSExpr (FImp a b) = SList [tag TImp, formulaToSExpr a, formulaToSExpr b]

certToSExpr :: Cert -> SExpr
certToSExpr (Hyp i) = SList [tag THyp, SAtom (show i)]
certToSExpr (Lam phi e) = SList [tag TLam, formulaToSExpr phi, certToSExpr e]
certToSExpr (App f x) = SList [tag TApp, certToSExpr f, certToSExpr x]
certToSExpr (Abort phi e) = SList [tag TAbort, formulaToSExpr phi, certToSExpr e]

-- ---------------------------------------------------------------------------
-- Properties
-- ---------------------------------------------------------------------------

-- | Decidable replay + dependency exactness (obligation 1, Lemma 5): every
-- constructed well-typed certificate replays to exactly its built type and its
-- built free-dependency set.
prop_replayAndDeps :: WellTyped -> Bool
prop_replayAndDeps (WellTyped free cert ty deps) =
  inferType [] free cert == Right (ty, deps)

-- | Certificate soundness (Theorem 4): every valuation satisfying all free
-- context formulas the certificate depends on satisfies its conclusion.
prop_ndSound :: WellTyped -> Bool
prop_ndSound (WellTyped free _ ty deps) =
  let usedFormulas = [free !! j | j <- Set.toList deps]
      names = concatMap atomsOf (ty : usedFormulas)
   in all (\v -> not (all (interp v) usedFormulas) || interp v ty) (allValuations names)

-- | An out-of-range free de Bruijn index is rejected, not silently accepted.
prop_outOfRangeRejected :: Bool
prop_outOfRangeRejected =
  case inferType [] [FAtom (AtomId "P")] (Hyp 5) of
    Left _ -> True
    Right _ -> False

-- | A locally bound assumption is not a dependency (Lemma 5): @lam P (hyp 0)@
-- reports the empty free-dependency set even though its context is nonempty.
prop_localNotDependency :: Bool
prop_localNotDependency =
  inferType [] [FAtom (AtomId "Q")] (Lam (FAtom (AtomId "P")) (Hyp 0))
    == Right (FImp (FAtom (AtomId "P")) (FAtom (AtomId "P")), Set.empty)

-- | Normalization fidelity (obligation 2): @p ≡ q@ iff
-- @encodeND p == encodeND q@.
prop_normalizationFidelity :: PropPair -> Bool
prop_normalizationFidelity (PropPair p q) =
  (nf p == nf q) == (encodeND p == encodeND q)

-- | Exact shared Lean/Haskell golden vectors for the UTF-8 framed atom key.
prop_atomKeyGoldenVectors :: Bool
prop_atomKeyGoldenVectors =
  prop_frameTagRoundTrip
    && all
      (\(p, bytes) ->
        encodeAtomKey p == bytes
          && decodeAtomKey bytes == Just p)
      [ (Prop (Pred "") [], "1:A0:1:L1:0")
      , (Prop (Pred ":") [TStr "a:b"], "1:A1::1:L1:18:1:S3:a:b")
      , (Prop (Pred "π") [TStr "雪"], "1:A2:π1:L1:18:1:S3:雪")
      , (Prop (Pred "p") [TCon (FunSym "z") []], "1:A1:p1:L1:112:1:C1:z1:L1:0")
      , ( Prop (Pred "p") [TCon (FunSym "f") [TNum "2", TCon (FunSym "g") [TStr "x"]]]
        , "1:A1:p1:L1:143:1:C1:f1:L1:26:1:N1:220:1:C1:g1:L1:16:1:S1:x"
        )
      , (Prop (Pred "p") [TNum "1", TNum "2"], "1:A1:p1:L1:26:1:N1:16:1:N1:2")
      , (Prop (Pred "p") [TNum "2", TNum "1"], "1:A1:p1:L1:26:1:N1:26:1:N1:1")
      ]

prop_atomKeyMalformedRejected :: Bool
prop_atomKeyMalformedRejected =
  all
    ((== Nothing) . decodeAtomKey)
    [ "01:A0:1:L1:0" -- non-canonical length
    , "1:A0:1:L1:0x" -- trailing bytes
    , "1:X0:1:L1:0" -- unknown root tag
    , "1:A0:1:L1:1" -- child-count mismatch
    , "1:A3:π1:L1:0" -- length crosses a UTF-8 boundary
    ]

-- | Generated left-inverse coverage for nested source atoms, including
-- multibyte identifiers and payloads. This complements the exact shared
-- Lean/Haskell vectors with structural recursion coverage.
prop_atomKeyRoundTrip :: Property
prop_atomKeyRoundTrip =
  forAll genAtomKeyProp $ \p ->
    counterexample ("atom key failed to round-trip: " ++ show p) $
      decodeAtomKey (encodeAtomKey p) == Just p
  where
    genAtomKeyProp = sized $ \n ->
      let depth = min 4 n
       in Prop <$> (Pred <$> genText)
            <*> resize depth (listOf (genTerm depth))
    genTerm n
      | n <= 0 =
          oneof
            [ TNum <$> elements ["0", "+02.10", "-0.0", "雪"]
            , TStr <$> genText
            , TCon <$> (FunSym <$> genText) <*> pure []
            ]
      | otherwise =
          frequency
            [ (3, genTerm 0)
            , (2, TCon <$> (FunSym <$> genText)
                <*> resize (min 3 (n `div` 2))
                  (listOf (genTerm (n `div` 2))))
            ]
    genText = listOf (elements ['a', ':', 'π', '雪', '🙂'])

-- | The framed atom-key tag table is coherent and exhaustive.
prop_frameTagRoundTrip :: Bool
prop_frameTagRoundTrip =
  all
    (\t -> parseFrameTag (frameTagToString t) == Just t)
    [minBound .. maxBound]

-- | The wire keyword table is coherent: 'parseTag' inverts 'tagToString' on
-- every 'Tag'. Exhaustive over the closed set, so a keyword typo or a missing
-- 'parseTag' case is caught here rather than by drift between the two.
prop_tagRoundTrip :: Bool
prop_tagRoundTrip = all (\t -> parseTag (tagToString t) == Just t) [minBound .. maxBound]

-- | Literal wire vectors pin the public Formula/Cert grammar independently of
-- 'tagToString'. If producer and decoder spelling drift together, these
-- production-independent fixtures still fail.
prop_wireKeywordGoldenVectors :: Bool
prop_wireKeywordGoldenVectors =
  and
    [ decodeFormula (SAtom "false") == Right FFalse
    , decodeFormula (SList [SAtom "atom", SAtom "P"]) == Right p
    , decodeFormula
        (SList [SAtom "imp", SList [SAtom "atom", SAtom "P"], SAtom "false"])
        == Right (FImp p FFalse)
    , decodeCert (SList [SAtom "hyp", SAtom "0"]) == Right (Hyp 0)
    , decodeCert
        (SList [SAtom "lam", SList [SAtom "atom", SAtom "P"], SList [SAtom "hyp", SAtom "0"]])
        == Right (Lam p (Hyp 0))
    , decodeCert
        (SList [SAtom "app", SList [SAtom "hyp", SAtom "0"], SList [SAtom "hyp", SAtom "1"]])
        == Right (App (Hyp 0) (Hyp 1))
    , decodeCert
        (SList [SAtom "abort", SList [SAtom "atom", SAtom "P"], SList [SAtom "hyp", SAtom "0"]])
        == Right (Abort p (Hyp 0))
    ]
  where
    p = FAtom (AtomId "P")

-- | Every string outside the closed tag table is rejected in each syntactic
-- position where a Formula or Cert keyword could otherwise occur.
prop_unknownTagRejected :: Property
prop_unknownTagRejected =
  forAll genUnknownTag $ \k ->
    counterexample ("unexpectedly decoded unknown tag " ++ show k) $
      all isLeft
        [ decodeFormula (SAtom k)
        , decodeFormula (SList [SAtom k, SAtom "P"])
        , decodeFormula (SList [SAtom k, formulaToSExpr p, formulaToSExpr q])
        ]
        && all isLeft
          [ decodeCert (SList [SAtom k, SAtom "0"])
          , decodeCert (SList [SAtom k, formulaToSExpr p, certToSExpr (Hyp 0)])
          ]
  where
    p = FAtom (AtomId "P")
    q = FAtom (AtomId "Q")
    isLeft (Left _) = True
    isLeft _ = False
    genUnknownTag =
      suchThat (resize 16 arbitrary) ((== Nothing) . parseTag)

isCanonicalNatString :: String -> Bool
isCanonicalNatString s =
  case reads s :: [(Integer, String)] of
    [(n, "")]
      | n >= 0
      , show n == s -> True
    _ -> False

genMalformedIndex :: Gen String
genMalformedIndex =
  suchThat candidate (not . isCanonicalNatString)
  where
    digits = listOf1 (elements ['0' .. '9'])
    candidate =
      frequency
        [ (4, elements ["", "-1", "01", "x"])
        , (3, do ds <- digits; elements ["-" ++ ds, "+" ++ ds, "0" ++ ds])
        , (2, resize 16 (listOf (elements (['0' .. '9'] ++ "+-_x"))))
        ]

-- | Bounded generative coverage of strings outside the canonical non-negative
-- unbounded natural-number grammar accepted by a de Bruijn index.
prop_malformedIndexRejected :: Property
prop_malformedIndexRejected =
  forAll genMalformedIndex $ \s ->
    counterexample ("unexpectedly decoded malformed index " ++ show s) $
      isLeft (decodeCert (SList [tag THyp, SAtom s]))
  where
    isLeft (Left _) = True
    isLeft _ = False

-- | The Lean wire grammar uses unbounded 'Nat' indices. A canonical value
-- beyond the host 'Int' range must therefore decode successfully, then be
-- rejected by replay as out of range without ever being converted to 'Int'.
prop_unboundedIndexDecodedThenRejected :: Bool
prop_unboundedIndexDecodedThenRejected =
  decodeCert wire == Right (Hyp huge)
    && case decodeCert wire >>= inferType [] [] of
      Left err -> "free de Bruijn index out of range" `isPrefixOf` err
      Right _ -> False
  where
    huge = 9223372036854775808
    wire = SList [SAtom "hyp", SAtom "9223372036854775808"]

prop_closedDecoderMatrix :: Bool
prop_closedDecoderMatrix =
  and
    [ decodeFormula (tag TFalse) == Right FFalse
    , decodeFormula (formulaToSExpr p) == Right p
    , decodeFormula (formulaToSExpr (FImp p q)) == Right (FImp p q)
    , decodeCert (certToSExpr (Hyp 0)) == Right (Hyp 0)
    , decodeCert (certToSExpr (Lam p (Hyp 0))) == Right (Lam p (Hyp 0))
    , decodeCert (certToSExpr (App (Hyp 0) (Hyp 1))) == Right (App (Hyp 0) (Hyp 1))
    , decodeCert (certToSExpr (Abort q (Hyp 0))) == Right (Abort q (Hyp 0))
    , all isLeft
        [ decodeFormula (SList [tag TAtom])
        , decodeFormula (SList [tag TAtom, SAtom "P", SAtom "extra"])
        , decodeFormula (SList [])
        , decodeFormula (SList [tag TFalse])
        , decodeFormula (SList [tag TFalse, SAtom "extra"])
        , decodeFormula (SList [tag TImp, formulaToSExpr p])
        , decodeFormula
            (SList [tag TImp, formulaToSExpr p, formulaToSExpr q, SAtom "extra"])
        ]
    , all isLeft
        [ decodeCert (SList [tag THyp, SAtom ""])
        , decodeCert (SList [tag THyp, SAtom "-1"])
        , decodeCert (SList [tag THyp, SAtom "01"])
        , decodeCert (SList [tag THyp, SAtom "x"])
        , decodeCert (SList [tag THyp])
        , decodeCert (SList [tag THyp, SAtom "0", SAtom "extra"])
        , decodeCert (SList [tag TLam, formulaToSExpr p])
        , decodeCert
            (SList [tag TLam, formulaToSExpr p, certToSExpr (Hyp 0), SAtom "extra"])
        , decodeCert (SList [tag TApp, certToSExpr (Hyp 0)])
        , decodeCert
            (SList [tag TApp, certToSExpr (Hyp 0), certToSExpr (Hyp 1), SAtom "extra"])
        , decodeCert (SList [tag TAbort, formulaToSExpr q])
        , decodeCert
            (SList [tag TAbort, formulaToSExpr q, certToSExpr (Hyp 0), SAtom "extra"])
        , decodeCert (SList [SAtom "unknown", SAtom "0"])
        ]
    , isLeft (inferType [] [p] (App (Hyp 1) (Hyp 0)))
    , isLeft (inferType [] [FImp p q, p] (App (Hyp 0) (Hyp 2)))
    , isLeft (inferType [] [p] (App (Hyp 0) (Hyp 0)))
    , isLeft (inferType [] [FImp p q, q] (App (Hyp 0) (Hyp 1)))
    , inferType [] [FFalse] (Abort q (Hyp 0)) == Right (q, Set.singleton 0)
    , isLeft (inferType [] [p] (Abort q (Hyp 0)))
    ]
  where
    p = FAtom (AtomId "P")
    q = FAtom (AtomId "Q")
    isLeft (Left _) = True
    isLeft _ = False

-- | Closed registration (obligation 5): a backend absent from the registry is
-- rejected with 'UnregisteredBackend' before any certificate work.
prop_unregisteredRejected :: Bool
prop_unregisteredRejected =
  let reg = mkRegistry [] -- empty registry
      goal = Prop (Pred "p") []
      cert = certToSExpr (Lam (encodeND goal) (Hyp 0))
   in case strictCheck reg ndBackendId (TheoryDigest "t0") [] goal cert of
        Left (UnregisteredBackend bid) -> bid == ndBackendId
        _ -> False

-- | End-to-end through the opaque 'SExpr' wire form (obligations 3–5 composed).
-- With a single source premise @p@, the certificate @hyp 0@ discharges the goal
-- @p@ directly; the sealed 'StrictJudgment' reports conclusion @p@ and premise
-- slot 0 as its sole dependency. (@encodeND@ maps every source proposition to
-- an ND /atom/, so implication between propositions is expressed by supplying a
-- proposition that already encodes to an implication, not exercised here.)
prop_strictCheckSeals :: Bool
prop_strictCheckSeals =
  let digest = TheoryDigest "empty"
      backend = mkNDBackend [(digest, [])]
      reg = mkRegistry [backend]
      p = Prop (Pred "p") []
      cert = certToSExpr (Hyp 0)
   in case strictCheck reg ndBackendId digest [p] p cert of
        Right j ->
          sjConclusion j == p
            && sjDependencies j == Set.singleton (PremiseSlot 0)
        _ -> False

-- ---------------------------------------------------------------------------
-- Heterogeneous backend composition (issue #182; spec §6 @certDeps@)
--
-- One support term may carry certificates from /different/ backends, and the
-- dependency report of the whole term is the union of the per-step reports —
-- the Haskell mirror of Lean's @Lara.Support.certDeps@ and of
-- @lean\/Lara\/BackendComposition.lean@'s heterogeneity results.
--
-- Every vector below runs on the __shipped__ path: the oracle is the one
-- 'Lara.Driver.buildCertOk' builds over the fixed registry (@nd\@1@, @ra\@1@,
-- @ord\@1@), and acceptance is decided by the production 'inferSupport'.
-- 'certDeps' validates nothing on its own, so each collection vector is paired
-- with an acceptance assertion on the same term: a report collected from a term
-- the checker rejects would prove nothing about the checker.
-- ---------------------------------------------------------------------------

-- | The ground atom pattern that instantiates, under the empty substitution, to
-- exactly this proposition. Every rule in this section is parameter-free: what
-- these vectors exercise is the backend seam, not 'Lara.SupportTerm.instAPat'.
patOf :: Prop -> A.AtomPat
patOf (Prop p ts) = A.AtomPat p (map A.PLit ts)

-- | @(prem N)@, spelled through "Lara.Strict.Cell"'s own keyword table so the
-- wire spelling stays defined in exactly one place — the discipline 'tag'
-- already applies to the ND grammar above.
premSlot :: Int -> SExpr
premSlot i = SList [SAtom (Cell.tagToString Cell.TPrem), SAtom (show i)]

ndDigest, ordDigest :: A.TheoryDigest
ndDigest = A.TheoryDigest "sha256:nd0"
ordDigest = A.TheoryDigest "sha256:ord0"

-- | The @nd\@1@ background theory: one entry. It is non-empty on purpose. A
-- 'CertPremise' carries no backend identity (it names a source-visible premise
-- slot, which is the reporting node's own), so 'CertTheory' is the /only/
-- 'CertDep' that carries one — and @ord\@1@ refuses to cite theory entries at
-- all. A mixed-backend vector whose reports were all premise slots therefore
-- could not witness per-step backend tagging; this entry is what makes the
-- root's report say @nd\@1@ and nothing else.
ndTheory :: [Prop]
ndTheory = [Prop (Pred "within_compute_budget") []]

-- | The theory table the oracle is built over — the same shape the wire
-- @theories@ section lowers to.
depsTheories :: [(A.TheoryDigest, [Prop])]
depsTheories = [(ndDigest, ndTheory), (ordDigest, [])]

-- | The production oracle. Not a stub: 'buildCertOk' is exactly what
-- "Lara.Check" is handed on the shipped path.
depsCertOk :: CertOk
depsCertOk = buildCertOk depsTheories

-- | Two measurement cells and the comparison they license. Each cell carries
-- exactly one numeric literal, which is @ord\@1@'s premise-cell convention
-- ('Lara.Strict.Cell.premiseCell').
cellOurs, cellTheirs, comparison, budgetRespected :: Prop
cellOurs = Prop (Pred "cell") [TCon (FunSym "ours") [], TNum "28.4"]
cellTheirs = Prop (Pred "cell") [TCon (FunSym "theirs") [], TNum "31.6"]
comparison = Prop (Pred "num_lt") [TNum "28.4", TNum "31.6"]
budgetRespected = head ndTheory

-- | The second golden vector's atoms (Lean @depsCellSelf@, @depsNumLeSelf@,
-- @depsNoteAtom@, mirrored atom for atom).
--
-- 'cellSelf' keeps the one-numeral cell shape 'cellOurs' has, so the shipped
-- @ord\@1@ premise-cell convention accepts it. 'numLeSelf' is the reflexive
-- family member: 'dupOrdPayload' compares slot 0 with itself, and @7.5 <= 7.5@
-- is the goal that holds where @num_lt@ would be rejected — the collector
-- sees a report only through 'CertAccepted', so the certificate must accept.
--
-- 'noteAtom' carries everything the first vector's atoms leave untested in
-- the golden encoders: a 'TStr' whose encoding must escape both @\"@ and @\\@,
-- and 'TCon's with arguments nested two deep.
cellSelf, numLeSelf, noteAtom :: Prop
cellSelf = Prop (Pred "cell") [TCon (FunSym "self") [], TNum "7.5"]
numLeSelf = Prop (Pred "num_le") [TNum "7.5", TNum "7.5"]
noteAtom =
  Prop
    (Pred "note")
    [ TCon (FunSym "quote") [TStr "say \"hi\"\\bye"]
    , TCon (FunSym "wrap") [TCon (FunSym "inner") []]
    ]

ordRuleId, ndRuleId, bridgeRuleId, trustedRuleId :: A.RuleId
ordRuleId = A.RuleId "compare_cells"
ndRuleId = A.RuleId "restate_budget"
bridgeRuleId = A.RuleId "bridge"
trustedRuleId = A.RuleId "assume_budget"

dupOrdRuleId, dupNdRuleId :: A.RuleId
dupOrdRuleId = A.RuleId "compare_self"
dupNdRuleId = A.RuleId "restate_note"

-- | The @ord\@1@ step: two measurement premises, a comparison conclusion.
ordRule :: A.Rule
ordRule =
  A.Rule
    { A.ruleId = ordRuleId
    , A.ruleParams = []
    , A.ruleMode = A.Strict
    , A.rulePremises = [patOf cellOurs, patOf cellTheirs]
    , A.rulePremiseLabels = []
    , A.ruleConclusion = patOf comparison
    , A.ruleAllowTrusted = False
    , A.ruleCertifiers = [A.CertRef (A.BackendId "ord") 1 ordDigest]
    , A.ruleQuestions = []
    }

-- | The @nd\@1@ step sitting /above/ the @ord\@1@ one. Its certificate is
-- @(hyp 1)@: the free context an ND certificate sees is @premises ++ theory@,
-- so index 1 is theory entry 0 and the accepted report is a theory dependency,
-- not a premise one. That the comparison premise is structurally required by
-- the checker but is not part of this step's certificate report is the
-- factivity firewall showing through — the report says what the /certificate/
-- consulted, not what the term is built from.
ndRule :: A.Rule
ndRule =
  A.Rule
    { A.ruleId = ndRuleId
    , A.ruleParams = []
    , A.ruleMode = A.Strict
    , A.rulePremises = [patOf comparison]
    , A.rulePremiseLabels = []
    , A.ruleConclusion = patOf budgetRespected
    , A.ruleAllowTrusted = False
    , A.ruleCertifiers = [A.CertRef (A.BackendId "nd") 1 ndDigest]
    , A.ruleQuestions = []
    }

-- | The @ord\@1@ self-comparison step: one measurement premise, the reflexive
-- comparison as conclusion (Lean @depsDupOrdRule@).
dupOrdRule :: A.Rule
dupOrdRule =
  A.Rule
    { A.ruleId = dupOrdRuleId
    , A.ruleParams = []
    , A.ruleMode = A.Strict
    , A.rulePremises = [patOf cellSelf]
    , A.rulePremiseLabels = []
    , A.ruleConclusion = patOf numLeSelf
    , A.ruleAllowTrusted = False
    , A.ruleCertifiers = [A.CertRef (A.BackendId "ord") 1 ordDigest]
    , A.ruleQuestions = []
    }

-- | The @nd\@1@ step above it: two premises (the note atom and the
-- self-comparison), the note atom restated as conclusion (Lean
-- @depsDupNdRule@). Its certificate is @(hyp 0)@, so its report names premise
-- slot 0 — the note atom, not the comparison.
dupNdRule :: A.Rule
dupNdRule =
  A.Rule
    { A.ruleId = dupNdRuleId
    , A.ruleParams = []
    , A.ruleMode = A.Strict
    , A.rulePremises = [patOf noteAtom, patOf numLeSelf]
    , A.rulePremiseLabels = []
    , A.ruleConclusion = patOf noteAtom
    , A.ruleAllowTrusted = False
    , A.ruleCertifiers = [A.CertRef (A.BackendId "nd") 1 ndDigest]
    , A.ruleQuestions = []
    }

-- | A defeasible rule with one mandatory critical question answered by the
-- comparison. A strict rule declares no questions, so a certified node can
-- never carry a discharge itself: the only way a certificate reaches a
-- @srDischarge@ position at all is under a defeasible ancestor, which is what
-- this rule provides.
bridgeQuestion :: A.QuestionId
bridgeQuestion = A.QuestionId "q_measured"

bridgeRule :: A.Rule
bridgeRule =
  A.Rule
    { A.ruleId = bridgeRuleId
    , A.ruleParams = []
    , A.ruleMode = A.Defeasible
    , A.rulePremises = []
    , A.rulePremiseLabels = []
    , A.ruleConclusion = patOf betterThanBaseline
    , A.ruleAllowTrusted = False
    , A.ruleCertifiers = []
    , A.ruleQuestions = [A.Question bridgeQuestion (patOf comparison) A.Mandatory]
    }

betterThanBaseline :: Prop
betterThanBaseline = Prop (Pred "better") [TCon (FunSym "ours") []]

-- | A strict rule discharged by author trust rather than by a backend.
trustedRule :: A.Rule
trustedRule =
  A.Rule
    { A.ruleId = trustedRuleId
    , A.ruleParams = []
    , A.ruleMode = A.Strict
    , A.rulePremises = []
    , A.rulePremiseLabels = []
    , A.ruleConclusion = patOf budgetRespected
    , A.ruleAllowTrusted = True
    , A.ruleCertifiers = []
    , A.ruleQuestions = []
    }

depsPi :: A.RuleId -> Maybe A.Rule
depsPi r =
  lookup
    r
    [ (ordRuleId, ordRule)
    , (ndRuleId, ndRule)
    , (bridgeRuleId, bridgeRule)
    , (trustedRuleId, trustedRule)
    , (dupOrdRuleId, dupOrdRule)
    , (dupNdRuleId, dupNdRule)
    ]

oursLeaf, theirsLeaf, selfLeaf, noteLeaf :: A.LeafId
oursLeaf = A.LeafId "e_ours"
theirsLeaf = A.LeafId "e_theirs"
selfLeaf = A.LeafId "e_self"
noteLeaf = A.LeafId "e_note"

depsGamma :: A.LeafId -> Maybe Prop
depsGamma l =
  lookup
    l
    [ (oursLeaf, cellOurs)
    , (theirsLeaf, cellTheirs)
    , (selfLeaf, cellSelf)
    , (noteLeaf, noteAtom)
    ]

ordPayload, ndPayload :: SExpr
ordPayload = SList [SAtom (OrdB.tagToString OrdB.TOrdcmp), premSlot 0, premSlot 1]
ndPayload = certToSExpr (Hyp 1)

-- | The second vector's payloads (Lean @depsDupOrdCert@ / @depsSlot0Cert@).
-- 'dupOrdPayload' names the same premise slot twice — the certificate whose
-- multiplicity the two mechanizations carry differently.
dupOrdPayload, dupNdPayload :: SExpr
dupOrdPayload = SList [SAtom (OrdB.tagToString OrdB.TOrdcmp), premSlot 0, premSlot 0]
dupNdPayload = certToSExpr (Hyp 0)

-- | The @ord\@1@-certified node, used as a premise subterm and as a discharge
-- subterm below.
ordNode :: A.SupportTerm
ordNode =
  A.SRule
    ordRuleId
    []
    [A.SLeaf oursLeaf, A.SLeaf theirsLeaf]
    []
    []
    (A.AssuranceCert (A.Cert (A.BackendId "ord") 1 ordDigest ordPayload))

-- | The two-level heterogeneous term: an @nd\@1@ root over an @ord\@1@ premise.
mixedTerm :: A.SupportTerm
mixedTerm =
  A.SRule
    ndRuleId
    []
    [ordNode]
    []
    []
    (A.AssuranceCert (A.Cert (A.BackendId "nd") 1 ndDigest ndPayload))

-- | The repeated-slot @ord\@1@ node (Lean @depsDupOrdNode@): one measurement
-- premise, consulted twice by the same certificate.
dupOrdNode :: A.SupportTerm
dupOrdNode =
  A.SRule
    dupOrdRuleId
    []
    [A.SLeaf selfLeaf]
    []
    []
    (A.AssuranceCert (A.Cert (A.BackendId "ord") 1 ordDigest dupOrdPayload))

-- | The second heterogeneous term (Lean @depsDupTerm@): an @nd\@1@ root over
-- a note leaf and the repeated-slot @ord\@1@ node. Together with 'mixedTerm'
-- it is what the cross-language golden pins — see the golden section below.
dupTerm :: A.SupportTerm
dupTerm =
  A.SRule
    dupNdRuleId
    []
    [A.SLeaf noteLeaf, dupOrdNode]
    []
    []
    (A.AssuranceCert (A.Cert (A.BackendId "nd") 1 ndDigest dupNdPayload))

-- | The same @ord\@1@ node in a __discharge__ position under a defeasible root.
bridgeTerm :: A.SupportTerm
bridgeTerm = A.SRule bridgeRuleId [] [] [(bridgeQuestion, ordNode)] [] A.AssuranceNone

trustedTerm :: A.SupportTerm
trustedTerm = A.SRule trustedRuleId [] [] [] [] A.AssuranceTrusted

-- | Run the production checker on a term, from the root.
checkDeps :: A.SupportTerm -> Either CheckError SupportResult
checkDeps = inferSupport depsPi depsGamma depsCertOk LocRoot

-- | The mixed-backend term is __accepted by the production checker__. This is
-- the assertion that discharges "a heterogeneous vector passes in Haskell"; the
-- collection properties below only read a report off a term this one has shown
-- the checker takes.
prop_mixedBackendAccepted :: Property
prop_mixedBackendAccepted =
  checkDeps mixedTerm === Right (SupportResult budgetRespected [])

-- | 'certDeps' collects /both/ steps' reports, each resolved against its own
-- reporting node and tagged with the backend that produced it: the root's
-- @nd\@1@ theory entry (carrying @nd\@1@ and its digest) and the @ord\@1@
-- node's two premise slots (each resolved to that node's own premise atom).
-- Root-first, then the premise walk — the order of Lean's @certDeps@.
prop_mixedBackendDepsCollected :: Property
prop_mixedBackendDepsCollected =
  certDeps depsCertOk depsPi mixedTerm
    === [ CertTheory (BackendId "nd" 1) (TheoryDigest "sha256:nd0") 0
        , CertPremise 0 cellOurs
        , CertPremise 1 cellTheirs
        ]

-- | A certificate in a __discharge__ position is collected too. A walker that
-- recursed only into 'A.srPremises' passes every vector above and fails here.
prop_dischargeDepsCollected :: Property
prop_dischargeDepsCollected =
  conjoin
    [ checkDeps bridgeTerm === Right (SupportResult betterThanBaseline [])
    , certDeps depsCertOk depsPi bridgeTerm
        === [CertPremise 0 cellOurs, CertPremise 1 cellTheirs]
    ]

-- | The edge vectors: a leaf and a trust-assured instance report nothing. Both
-- are accepted terms, so this is the collector staying silent where there is no
-- certificate — not a rejection in disguise.
prop_uncertifiedNodesReportNothing :: Property
prop_uncertifiedNodesReportNothing =
  conjoin
    [ checkDeps (A.SLeaf oursLeaf) === Right (SupportResult cellOurs [])
    , certDeps depsCertOk depsPi (A.SLeaf oursLeaf) === []
    , checkDeps trustedTerm === Right (SupportResult budgetRespected [])
    , certDeps depsCertOk depsPi trustedTerm === []
    ]

-- | The backend firewall on the wire: an @nd\@1@ certificate whose payload is
-- an @ord\@1@ sub-payload is rejected by the @nd\@1@ decoder, with @nd\@1@'s own
-- reason. No backend may read another's certificate — a parent step cannot
-- inspect, reuse, or re-interpret a child backend's proof term.
--
-- The vector exists in Haskell precisely because the wire form is untyped: an
-- 'SExpr' payload can /syntactically/ be another backend's. In Lean the
-- leakage is inexpressible — @Assurance@ carries only @(β, hd, κ)@ and there is
-- no syntax naming another backend's formula type — so this artifact, not a
-- Lean theorem, is what discharges the leakage criterion. It runs through
-- 'buildCertOk' rather than @strictCheck@ because @strictCheck@ is reached only
-- from tests, and a firewall vector that never runs on the shipped path checks
-- the wrong checker.
prop_crossBackendPayloadRejected :: Property
prop_crossBackendPayloadRejected =
  depsCertOk leakedCert [comparison] budgetRespected
    === CertRejected ("malformed ND certificate: " ++ show ordPayload)

-- | An @nd\@1@ certificate carrying an @ord\@1@ payload. Shared by
-- 'prop_crossBackendPayloadRejected', which pins @nd\@1@'s exact rejection
-- reason for it, and 'prop_rejectedStepKeepsDepsBeneath', which relies on that
-- rejection. One binding rather than two copies, so the vector that assumes it
-- is rejected cannot drift from the vector that proves it.
leakedCert :: A.Cert
leakedCert = A.Cert (A.BackendId "nd") 1 ndDigest ordPayload

-- | __A rejected step never hides the accounting of the steps beneath it__ —
-- the totality contract stated in "Lara.Strict.Deps"' module header.
--
-- 'mixedTerm' with its @nd\@1@ root certificate replaced by 'leakedCert': the
-- root is now a certificate node the oracle /rejects/
-- ('prop_crossBackendPayloadRejected' pins the exact reason), so it contributes
-- no report of its own — the @nd\@1@ theory entry that
-- 'prop_mixedBackendDepsCollected' sees is gone. The walk continues into the
-- premise regardless, so the accepted @ord\@1@ node beneath it still reports
-- both of its premise slots.
--
-- Without this vector a @go@ that short-circuited the entire subtree at a
-- non-contributing node would pass every other property in this section: in
-- 'mixedTerm' every rule id resolves, every rule is parameter-free with ground
-- 'PLit' patterns so instantiation never fails, and every certificate is
-- accepted — so no other vector ever walks /past/ a node that reports nothing.
prop_rejectedStepKeepsDepsBeneath :: Property
prop_rejectedStepKeepsDepsBeneath =
  certDeps depsCertOk depsPi leakedRootTerm
    === [CertPremise 0 cellOurs, CertPremise 1 cellTheirs]
  where
    leakedRootTerm = case mixedTerm of
      A.SRule rn theta ws d o _ ->
        A.SRule rn theta ws d o (A.AssuranceCert leakedCert)
      w -> w

-- | The second golden vector is __accepted by the production checker__ — the
-- same discipline 'prop_mixedBackendAccepted' applies to 'mixedTerm'. Note
-- what makes it acceptable: @ord\@1@ accepts the same-slot certificate
-- because the goal is the reflexive @num_le(7.5, 7.5)@, and @nd\@1@ accepts
-- @(hyp 0)@ because the note atom is premise slot 0 of its own step.
prop_dupBackendAccepted :: Property
prop_dupBackendAccepted =
  checkDeps dupTerm === Right (SupportResult noteAtom [])

-- | __The multiplicity asymmetry, pinned as a Haskell value.__ The @ord\@1@
-- adapter reports a 'Set' 'Dependency', so @(ordcmp (prem 0) (prem 0))@
-- collapses to a single 'PremiseSlot' before 'resolve' ever runs — this list
-- has TWO entries. Lean's @Backend.uses@ is a @List Nat@ and carries the
-- duplicate through: @depsDupTerm_certDeps@ pins a THREE-entry list with
-- @premise 0 cell(self, 7.5)@ twice. The two mechanizations reach the golden
-- encoder holding different multiplicities, and agree only because both
-- encoders dedup — which is exactly what the shared golden file records.
prop_dupBackendDepsCollected :: Property
prop_dupBackendDepsCollected =
  certDeps depsCertOk depsPi dupTerm
    === [CertPremise 0 noteAtom, CertPremise 0 cellSelf]

-- ---------------------------------------------------------------------------
-- The cross-language certDeps golden (B0)
--
-- 'prop_mixedBackendDepsCollected' and 'prop_dupBackendDepsCollected' above
-- pin the Haskell results as Haskell values. This section pins them as /text/,
-- against the same bytes the Lean witness emits, so the two mechanizations
-- cannot drift apart silently.
--
-- Lean's half is @Lara.Examples.BackendComposition.depsMixedTerm@ together
-- with @depsDupTerm@, whose constants mirror 'mixedTerm' and 'dupTerm' atom
-- for atom: same two backend identities, same rule shapes, same premise
-- atoms, same certificate payloads, same digests, same theory-entry index.
-- Both halves of each Lean term run on the
-- __shipped__ backend cores (@Lara.Strict.ndBackend@, @Lara.Ord.ordBackend@) —
-- the @ord\@1@ acceptance blocker that forces the rest of that module onto a
-- fixture core does not reach a dependency report, because
-- @Lara.Support.stepDeps@ never calls acceptance. See
-- @scripts/check-backend-deps-golden.sh@ for the full argument.
--
-- 'mixedTerm' alone leaves both encoders' interesting branches dead — no
-- escape character, no 'TCon' with arguments, no duplicate slot. 'dupTerm'
-- is the vector that reaches them: its note atom exercises the escape and
-- recursion branches of both encoders, and its same-slot @ord\@1@ certificate
-- exercises both dedup paths, pinning the @List Nat@-versus-@Set Dependency@
-- multiplicity reconciliation as an artifact rather than an argument.
-- ---------------------------------------------------------------------------

-- | The canonical encoding is the library's since \#204
-- ("Lara.Strict.Deps".'encodeCertDeps'), not a copy defined here. It moved
-- because the shipped @lara deps@ report and this golden must be the /same/
-- text: a report format defined separately from the one
-- @scripts\/check-backend-deps-golden.sh@ diffs against Lean would be a format
-- nothing pins. The alias keeps this section's prose reading as it did.
--
-- Its grammar, sort order and dedup rule — and why each is what it is — are
-- documented on 'encodeCertDep' and 'encodeCertDeps'.
encodeCertDepsGolden :: [CertDep] -> String
encodeCertDepsGolden = encodeCertDeps

-- | The Haskell collector's answer on the two golden vectors, concatenated
-- and encoded canonically, equals the committed golden that Lean emits. This
-- is the cross-language half of the assertions 'prop_mixedBackendDepsCollected'
-- and 'prop_dupBackendDepsCollected' make in Haskell terms;
-- @scripts\/check-backend-deps-golden.sh@ is the other half, and keeps the
-- file from going stale against Lean. The concatenation happens /before/
-- encoding, so the sort and dedup run over the union — mirroring
-- @backendDepsGolden@ on the Lean side.
prop_mixedBackendDepsGolden :: Property
prop_mixedBackendDepsGolden = once $ ioProperty $ do
  golden <- readFile "test/backend-deps.golden"
  pure
    ( encodeCertDepsGolden
        (certDeps depsCertOk depsPi mixedTerm ++ certDeps depsCertOk depsPi dupTerm)
        === golden
    )

-- ---------------------------------------------------------------------------
-- Prop pair generator for normalization fidelity
-- ---------------------------------------------------------------------------

data PropPair = PropPair Prop Prop deriving (Show)

instance Arbitrary PropPair where
  arbitrary = do
    p <- genSimpleProp
    sharesNf <- elements [True, False]
    q <- if sharesNf then pure (renoise p) else genSimpleProp
    pure (PropPair p q)

-- | A small Prop generator with numeric literals carrying cosmetic noise.
genSimpleProp :: Gen Prop
genSimpleProp = Prop <$> genPred <*> listOf genT
  where
    genPred = Pred . (: []) <$> elements ['p' .. 'r']
    genT =
      oneof
        [ TNum <$> genNoisyNum
        , TCon <$> (FunSym . (: []) <$> elements ['a' .. 'c']) <*> pure []
        ]
    genNoisyNum = do
      sign <- elements ["", "+"]
      digits <- listOf1 (elements ['0' .. '9'])
      pure (sign ++ digits)

-- | Perturb a Prop's numeric literals cosmetically without changing its normal
-- form, so equal-nf instances of the fidelity property actually occur.
renoise :: Prop -> Prop
renoise (Prop p ts) = Prop p (map noise ts)
  where
    noise (TNum s) = TNum ("+0" ++ s)
    noise t = t

-- ---------------------------------------------------------------------------
-- Exported runner
-- ---------------------------------------------------------------------------

strictSpecProps :: [(String, IO Result)]
strictSpecProps =
  [ ("ND replay + dependency exactness", quickCheckResult prop_replayAndDeps)
  , ("ND certificate soundness (Thm 4)", quickCheckResult prop_ndSound)
  , ("ND out-of-range index rejected", quickCheckResult prop_outOfRangeRejected)
  , ("ND local is not a dependency", quickCheckResult prop_localNotDependency)
  , ("encodeND normalization fidelity", quickCheckResult prop_normalizationFidelity)
  , ("atom-key exact golden vectors", quickCheckResult prop_atomKeyGoldenVectors)
  , ("atom-key malformed inputs rejected", quickCheckResult prop_atomKeyMalformedRejected)
  , ("atom-key generated round-trip", quickCheckResult prop_atomKeyRoundTrip)
  , ("ND wire tag round-trip", quickCheckResult prop_tagRoundTrip)
  , ("ND literal wire keyword vectors", quickCheckResult prop_wireKeywordGoldenVectors)
  , ("ND unknown tags universally rejected", quickCheckResult prop_unknownTagRejected)
  , ("ND malformed indices universally rejected", quickCheckResult prop_malformedIndexRejected)
  , ("ND unbounded canonical index reaches replay", quickCheckResult prop_unboundedIndexDecodedThenRejected)
  , ("ND closed decoder/infer matrix", quickCheckResult prop_closedDecoderMatrix)
  , ("strict unregistered backend rejected", quickCheckResult prop_unregisteredRejected)
  , ("strictCheck seals a judgment", quickCheckResult prop_strictCheckSeals)
  , ("mixed nd@1/ord@1 term accepted by the checker", quickCheckResult prop_mixedBackendAccepted)
  , ("mixed nd@1/ord@1 certDeps unions both steps' reports", quickCheckResult prop_mixedBackendDepsCollected)
  , ("certDeps collects a discharge-position certificate", quickCheckResult prop_dischargeDepsCollected)
  , ("certDeps of leaf and trusted instance is empty", quickCheckResult prop_uncertifiedNodesReportNothing)
  , ("cross-backend payload leakage rejected by nd@1", quickCheckResult prop_crossBackendPayloadRejected)
  , ("a rejected step does not hide the deps beneath it", quickCheckResult prop_rejectedStepKeepsDepsBeneath)
  , ("repeated-slot nd@1/ord@1 term accepted by the checker", quickCheckResult prop_dupBackendAccepted)
  , ("repeated-slot certDeps collapses to a set in Haskell", quickCheckResult prop_dupBackendDepsCollected)
  , ("mixed nd@1/ord@1 certDeps matches the Lean-emitted golden", quickCheckResult prop_mixedBackendDepsGolden)
  ]
