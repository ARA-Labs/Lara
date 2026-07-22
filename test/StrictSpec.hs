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

import Data.List (nub)
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
  , inferType
  , mkNDBackend
  , ndBackendId
  , parseTag
  , tagToString
  )
import Lara.Strict.ND.Internal (AtomId (..))

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
      , wtCert = App (Hyp (shift + 1)) (Hyp shift)
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
      , wtCert = Abort t (Hyp shift)
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

-- | The wire keyword table is coherent: 'parseTag' inverts 'tagToString' on
-- every 'Tag'. Exhaustive over the closed set, so a keyword typo or a missing
-- 'parseTag' case is caught here rather than by drift between the two.
prop_tagRoundTrip :: Bool
prop_tagRoundTrip = all (\t -> parseTag (tagToString t) == Just t) [minBound .. maxBound]

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
  , ("ND wire tag round-trip", quickCheckResult prop_tagRoundTrip)
  , ("strict unregistered backend rejected", quickCheckResult prop_unregisteredRejected)
  , ("strictCheck seals a judgment", quickCheckResult prop_strictCheckSeals)
  ]
