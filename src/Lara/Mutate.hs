-- | Seeded mutation generators for the M5 evaluation corpus (tracker #48, T1;
-- spec §10.1 mutation table; plan @plans/2026-08-01-m5-mutation-suite-worked-cases.md@).
--
-- Each 'MutationOp' is a surgical, single-defect transformation of a decoded
-- worked-example 'CheckInput' (or, for the codec family, of its wire bytes)
-- whose outcome is specified a priori: a rejection class, a codec-boundary
-- reject, or — for the constructed attack-cycle family — an accept whose
-- labels are all @undec@ and whose statuses are all @contested@. The
-- generators are deterministic: every random choice flows from
-- 'mutationSeed' through a SplitMix64 stream keyed by @(base, operator)@, so
-- re-running the generator over unchanged base anchors reproduces the
-- committed mutant bytes exactly (the seeded-reproducibility freshness
-- guard in @test/MutationSpec.hs@).
--
-- The module only /proposes/ mutants; @scripts\/gen-mutants.hs@ verifies each
-- one against the production checker before writing it (a mutant whose actual
-- verdict differs from its specified outcome aborts generation), and
-- @scripts\/differential.sh@ then holds every committed mutant byte-identical
-- across the Haskell and Lean drivers.
module Lara.Mutate
  ( -- * Operators (closed vocabulary, one name table)
    MutationOp (..)
  , opName
  , opFamily
    -- * Specified outcomes
  , Expected (..)
  , expectedText
  , codecDiagnostics
    -- * Mutants
  , Mutant (..)
  , mutantPath
  , mutationSeed
  , mutationBases
  , mutantsForBase
  , codecMutantsForBase
  , cycleMutants
  , manifestFor
    -- * Seeded stream (exposed for tests)
  , splitMix64
  , stringSeed
  ) where

import Data.Bits (shiftR, xor)
import Data.Char (ord)
import Data.List (find)
import Data.Word (Word64)

import Lara.AST
import Lara.Prop (Prop (..), Term (..), equiv)
import Lara.Replay
  ( CheckInput
  , CoreVersion (..)
  , inputReplayId
  , inputUnit
  , mkCheckInput
  , mkReplayId
  , replayArtifact
  , replayBackends
  , replayCore
  , replayPolicy
  , replayTheories
  )
import Lara.Strict (SExpr (..))
import Lara.SupportTerm (instAPat, instAPats)
import Lara.Wire (encodeCheckInput, parseSExpr, printSExpr)

-- ---------------------------------------------------------------------------
-- Operators
-- ---------------------------------------------------------------------------

-- | The closed mutation vocabulary. The first block realizes the Phase D
-- list (wrong formulas, undeclared leaves, hidden policy extension, bad
-- attack targets, open obligations); the second block extends it to the
-- remaining executable rejection classes (assurance\/certificate\/replay
-- tampering, duplicate-report integrity); 'OpRebutCycle' is the specified
-- non-rejection (cycles → @undec@\/@contested@, spec §10.1); the @OpCodec*@
-- family is codec corruption (R14: exit 2, no verdict).
data MutationOp
  = OpWrongPremise -- ^ premise child ≢ instantiated pattern → R4
  | OpWrongSubstDomain -- ^ rename a θ key off the rule params → R3
  | OpWrongDischarge -- ^ discharge answers with a ≢ leaf → R6
  | OpUndeclaredLeaf -- ^ reference a leaf missing from Γ → R1
  | OpHiddenRule -- ^ instantiate a rule the policy never declared → R1
  | OpHiddenContrary -- ^ smuggle in a strict rule + contrary on it → R12
  | OpBadAttackPosition -- ^ attack position off the term / wrong kind → R10
  | OpUnlicensedAttack -- ^ self-rebut with no declared contrary → R11
  | OpOpenObligation -- ^ drop a mandatory discharge, no hole → R5
  | OpTrustedAssurance -- ^ @trusted@ on a defeasible instance → R7
  | OpCertTheorySwap -- ^ certificate theory not allowlisted → R7
  | OpCertPayloadTamper -- ^ corrupt an allowlisted cert payload → R13
  | OpDuplicateBackend -- ^ replay selects one backend twice → R13
  | OpUnknownBackend -- ^ replay selects an unknown backend → R13
  | OpGroupConflict -- ^ escalated ≢ duplicate-report group → R9
  | OpRebutCycle -- ^ constructed rebut N-cycle → accept, all contested
  | OpCodecJunkSection -- ^ trailing junk form in the envelope
  | OpCodecCoreVersion -- ^ unsupported core version
  | OpCodecReplayOrder -- ^ replay-id sections out of order
  | OpCodecTheoryMismatch -- ^ replay theories ≠ unit theories
  | OpCodecDanglingAttack -- ^ attack endpoint names no declared arg
  | OpCodecTruncate -- ^ drop the closing paren (parse error)
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The one place the concrete operator spelling exists.
opName :: MutationOp -> String
opName op = case op of
  OpWrongPremise -> "wrong-premise"
  OpWrongSubstDomain -> "wrong-subst-domain"
  OpWrongDischarge -> "wrong-discharge"
  OpUndeclaredLeaf -> "undeclared-leaf"
  OpHiddenRule -> "hidden-rule"
  OpHiddenContrary -> "hidden-contrary"
  OpBadAttackPosition -> "bad-attack-position"
  OpUnlicensedAttack -> "unlicensed-attack"
  OpOpenObligation -> "open-obligation"
  OpTrustedAssurance -> "trusted-assurance"
  OpCertTheorySwap -> "cert-theory-swap"
  OpCertPayloadTamper -> "cert-payload-tamper"
  OpDuplicateBackend -> "duplicate-backend"
  OpUnknownBackend -> "unknown-backend"
  OpGroupConflict -> "group-conflict"
  OpRebutCycle -> "rebut-cycle"
  OpCodecJunkSection -> "codec-junk-section"
  OpCodecCoreVersion -> "codec-core-version"
  OpCodecReplayOrder -> "codec-replay-order"
  OpCodecTheoryMismatch -> "codec-theory-mismatch"
  OpCodecDanglingAttack -> "codec-dangling-attack"
  OpCodecTruncate -> "codec-truncate"

-- | The Phase D mutation family an operator realizes (manifest column).
opFamily :: MutationOp -> String
opFamily op = case op of
  OpWrongPremise -> "wrong-formulas"
  OpWrongSubstDomain -> "wrong-formulas"
  OpWrongDischarge -> "open-obligations"
  OpUndeclaredLeaf -> "undeclared-leaves"
  OpHiddenRule -> "hidden-policy-extension"
  OpHiddenContrary -> "hidden-policy-extension"
  OpBadAttackPosition -> "bad-attack-targets"
  OpUnlicensedAttack -> "bad-attack-targets"
  OpOpenObligation -> "open-obligations"
  OpTrustedAssurance -> "certificate-tampering"
  OpCertTheorySwap -> "certificate-tampering"
  OpCertPayloadTamper -> "certificate-tampering"
  OpDuplicateBackend -> "certificate-tampering"
  OpUnknownBackend -> "certificate-tampering"
  OpGroupConflict -> "data-integrity"
  OpRebutCycle -> "cycles"
  OpCodecJunkSection -> "codec-corruption"
  OpCodecCoreVersion -> "codec-corruption"
  OpCodecReplayOrder -> "codec-corruption"
  OpCodecTheoryMismatch -> "codec-corruption"
  OpCodecDanglingAttack -> "codec-corruption"
  OpCodecTruncate -> "codec-corruption"

-- ---------------------------------------------------------------------------
-- Specified outcomes
-- ---------------------------------------------------------------------------

-- | The outcome a mutant is specified to have (spec §10.1): a rejection with
-- a fixed class, a codec-boundary reject (exit 2, no verdict), or — for the
-- cycle family — an accept in which every label is @undec@ and every queried
-- status is @contested@.
data Expected
  = ExpectClass RejectClass
  | ExpectCodecReject
  | ExpectAllContested
  deriving (Eq, Ord, Show)

-- | Manifest spelling of an expected outcome.
expectedText :: Expected -> String
expectedText e = case e of
  ExpectClass c -> "reject-" ++ show c
  ExpectCodecReject -> "codec-reject"
  ExpectAllContested -> "accept-all-contested"

-- | The deletion-sensitivity pin of a codec-corruption operator: a fixed
-- substring of the Haskell decode failure (the driver's
-- @codec error at \<context\>: \<message\>@ rendering of 'Lara.Wire.WireError')
-- and of the Lean driver's stderr diagnostic, identifying WHICH codec check
-- fired. \"Any decode failure\" is not enough: e.g. with the replay-id
-- section-order check deleted, a swapped @codec-replay-order@ mutant would
-- still exit 2 via the downstream core-version check, so exit-2-only
-- verification stays green while the intended validation is gone. The
-- generator, @test\/MutationSpec.hs@, and @scripts\/differential.sh@'s
-- negative loop all assert these substrings (carried as the last two
-- manifest columns). 'Nothing' for every non-codec operator.
codecDiagnostics :: MutationOp -> Maybe (String, String)
codecDiagnostics op = case op of
  OpCodecJunkSection ->
    Just
      ( "wrong number of fields for check-input"
      , "check-input: malformed check input"
      )
  OpCodecCoreVersion ->
    Just
      ( "unsupported core version"
      , "unsupported core version"
      )
  OpCodecReplayOrder ->
    Just
      ( "replay-id core: expected (core"
      , "replay-id: wrong field order"
      )
  OpCodecTheoryMismatch ->
    Just
      ( "theory identity does not match replay identity"
      , "replay theories differ from unit theories"
      )
  OpCodecDanglingAttack ->
    Just
      ( "attack endpoint is not a declared argument"
      , "attack endpoint is not a declared argument"
      )
  OpCodecTruncate ->
    Just
      ( "unclosed list"
      , "unclosed list"
      )
  _ -> Nothing

-- ---------------------------------------------------------------------------
-- Mutants
-- ---------------------------------------------------------------------------

-- | One generated mutant: its fixture basename, provenance, specified
-- outcome, and exact file bytes.
data Mutant = Mutant
  { mutantName :: String -- ^ fixture basename (without directory)
  , mutantBase :: String -- ^ base anchor label (worked-example name), or @-@
  , mutantOp :: MutationOp
  , mutantExpected :: Expected
  , mutantBytes :: String
  }
  deriving (Eq, Show)

-- | The committed generation seed (T5 freeze discipline: fixed before the
-- final measurement runs; changing it regenerates a different — equally
-- valid — suite and must be an explicit, reviewed decision).
mutationSeed :: Word64
mutationSeed = 20260801

-- | The accept-verdict worked examples the operators mutate (anchors at
-- @examples\/<NAME>\/example.core.sexp@). The R-series examples already
-- reject and are excluded: a second defect would make the specified class
-- ambiguous.
mutationBases :: [String]
mutationBases = ["A", "B", "E1", "E2", "E3", "E4", "E5", "S1"]

-- | Where a mutant lives relative to the suite root: codec-corruption
-- mutants sit in the @malformed/@ negative half (both drivers must exit 2
-- with no verdict), every other mutant is a verdict-bearing anchor.
mutantPath :: Mutant -> FilePath
mutantPath m = case mutantExpected m of
  ExpectCodecReject -> "malformed/" ++ mutantName m
  _ -> mutantName m

-- | Render the manifest rows for a mutant list (TSV: file, base, family,
-- operator, expected, hs-diagnostic, lean-diagnostic). The diagnostic
-- columns are the 'codecDiagnostics' deletion-sensitivity pins — non-empty
-- exactly for the codec-corruption rows.
manifestFor :: [Mutant] -> String
manifestFor ms =
  unlines
    ( "# file\tbase\tfamily\toperator\texpected\ths-diagnostic\tlean-diagnostic"
        : [ mutantPath m
              ++ "\t"
              ++ mutantBase m
              ++ "\t"
              ++ opFamily (mutantOp m)
              ++ "\t"
              ++ opName (mutantOp m)
              ++ "\t"
              ++ expectedText (mutantExpected m)
              ++ "\t"
              ++ hsDiag
              ++ "\t"
              ++ leanDiag
          | m <- ms
          , let (hsDiag, leanDiag) =
                  maybe ("", "") id (codecDiagnostics (mutantOp m))
          ]
    )

-- ---------------------------------------------------------------------------
-- SplitMix64 (deterministic, dependency-free)
-- ---------------------------------------------------------------------------

-- | One SplitMix64 step: @(next state, output)@.
splitMix64 :: Word64 -> (Word64, Word64)
splitMix64 s0 =
  let s = s0 + 0x9E3779B97F4A7C15
      z1 = (s `xor` (s `shiftR` 30)) * 0xBF58476D1CE4E5B9
      z2 = (z1 `xor` (z1 `shiftR` 27)) * 0x94D049BB133111EB
   in (s, z2 `xor` (z2 `shiftR` 31))

-- | FNV-1a over a string, for keying per-@(base, operator)@ streams.
stringSeed :: String -> Word64
stringSeed = foldl step 0xCBF29CE484222325
  where
    step h c = (h `xor` fromIntegral (ord c)) * 0x100000001B3

-- | The infinite output stream of the @(base, operator)@-keyed generator.
streamFor :: String -> MutationOp -> [Word64]
streamFor base op = go (mutationSeed `xor` stringSeed (base ++ "/" ++ opName op))
  where
    go s = let (s', w) = splitMix64 s in w : go s'

-- | Deterministically pick at most @k@ elements (first-draw order, no
-- repeats) from the applicable sites.
pickSome :: String -> MutationOp -> Int -> [a] -> [a]
pickSome base op k xs
  | n <= k = xs
  | otherwise = [xs !! i | i <- chosen]
  where
    n = length xs
    chosen = go [] (take (16 * k) (streamFor base op))
    go acc _ | length acc == k = reverse acc
    go acc [] = reverse acc
    go acc (w : ws)
      | i `elem` acc = go acc ws
      | otherwise = go (i : acc) ws
      where
        i = fromIntegral (w `mod` fromIntegral n)

-- ---------------------------------------------------------------------------
-- Support-term sites
-- ---------------------------------------------------------------------------

-- | Every subterm occurrence of a term, keyed by its 'Position'.
occurrences :: SupportTerm -> [(Position, SupportTerm)]
occurrences w = go [] w
  where
    go pos t =
      (reverse pos, t) : case t of
        SLeaf _ -> []
        SRule _ _ ws d _ _ ->
          concat
            [ go (StepPremise i : pos) wi
            | (i, wi) <- zip [0 ..] ws
            ]
            ++ concat
              [ go (StepQuestion q : pos) wq
              | (q, wq) <- d
              ]

-- | Rewrite the subterm at a position (total: an unreachable position is the
-- identity, but sites always come from 'occurrences').
rewriteAt :: Position -> (SupportTerm -> SupportTerm) -> SupportTerm -> SupportTerm
rewriteAt [] f t = f t
rewriteAt (step : rest) f t = case t of
  SLeaf _ -> t
  SRule r theta ws d hs a -> case step of
    StepPremise i ->
      SRule r theta [if j == i then rewriteAt rest f w else w | (j, w) <- zip [0 ..] ws] d hs a
    StepQuestion q ->
      SRule r theta ws [(q', if q' == q then rewriteAt rest f w else w) | (q', w) <- d] hs a

-- | Rewrite one declared argument's term.
rewriteArg :: Int -> (SupportTerm -> SupportTerm) -> Unit -> Unit
rewriteArg ix f u =
  u
    { unitArgs =
        [ (aid, if j == ix then f t else t)
        | (j, (aid, t)) <- zip [0 ..] (unitArgs u)
        ]
    }

-- | All rule occurrences across the declared arguments:
-- @(arg index, position, occurrence)@.
ruleSites :: Unit -> [(Int, Position, SupportTerm)]
ruleSites u =
  [ (ix, pos, t)
  | (ix, (_, w)) <- zip [0 ..] (unitArgs u)
  , (pos, t@SRule{}) <- occurrences w
  ]

-- | All leaf-reference occurrences across the declared arguments.
leafSites :: Unit -> [(Int, Position, LeafId)]
leafSites u =
  [ (ix, pos, l)
  | (ix, (_, w)) <- zip [0 ..] (unitArgs u)
  , (pos, SLeaf l) <- occurrences w
  ]

ruleOf :: Unit -> RuleId -> Maybe Rule
ruleOf u rn = find ((== rn) . ruleId) (unitRules u)

-- | A declared leaf whose proposition is ≢ the wanted one (the swap target
-- for premise\/discharge mismatch mutations).
inequivLeaf :: Unit -> Prop -> Maybe LeafId
inequivLeaf u p = fst <$> find (not . equiv p . snd) (unitLeaves u)

-- ---------------------------------------------------------------------------
-- Verdict-level mutants
-- ---------------------------------------------------------------------------

-- | All verdict-level mutants of one decoded base anchor, in fixed operator
-- order, sites picked by the seeded stream. Inapplicable operators produce no
-- mutants for the base. Codec mutants are separate ('codecMutantsForBase').
mutantsForBase :: String -> CheckInput -> [Mutant]
mutantsForBase base input =
  concat
    [ unitMutants base input OpUndeclaredLeaf 2 undeclaredLeafSites
    , unitMutants base input OpHiddenRule 1 hiddenRuleSites
    , unitMutants base input OpHiddenContrary 1 hiddenContrarySites
    , unitMutants base input OpWrongSubstDomain 1 wrongSubstSites
    , unitMutants base input OpWrongPremise 1 wrongPremiseSites
    , unitMutants base input OpOpenObligation 1 openObligationSites
    , unitMutants base input OpWrongDischarge 1 wrongDischargeSites
    , unitMutants base input OpTrustedAssurance 1 trustedAssuranceSites
    , unitMutants base input OpCertTheorySwap 1 certTheorySwapSites
    , unitMutants base input OpCertPayloadTamper 1 certPayloadSites
    , unitMutants base input OpBadAttackPosition 2 badAttackPositionSites
    , unitMutants base input OpUnlicensedAttack 1 unlicensedAttackSites
    , unitMutants base input OpGroupConflict 1 groupConflictSites
    , replayMutants base input
    ]

-- | Assemble the picked unit-mutation sites of one operator into mutants.
unitMutants
  :: String
  -> CheckInput
  -> MutationOp
  -> Int
  -> (Unit -> [(Expected, Unit -> Unit)])
  -> [Mutant]
unitMutants base input op cap sites =
  [ Mutant (mutantFileName base op k) base op expected bytes
  | (k, (expected, mutate)) <- zip [0 :: Int ..] picked
  , Right mutated <- [mkCheckInput (inputReplayId input) (mutate u)]
  , let bytes = printSExpr (encodeCheckInput mutated) ++ "\n"
  ]
  where
    u = inputUnit input
    picked = pickSome base op cap (sites u)

mutantFileName :: String -> MutationOp -> Int -> String
mutantFileName base op k =
  base ++ "--" ++ opName op ++ "-" ++ show k ++ ".sexp"

-- R1: rewrite one leaf reference to an undeclared id.
undeclaredLeafSites :: Unit -> [(Expected, Unit -> Unit)]
undeclaredLeafSites u =
  [ ( ExpectClass R1
    , rewriteArg ix (rewriteAt pos (const (SLeaf (LeafId "mut_undeclared"))))
    )
  | (ix, pos, _) <- leafSites u
  ]

-- R1: instantiate a rule id the policy section never declares.
hiddenRuleSites :: Unit -> [(Expected, Unit -> Unit)]
hiddenRuleSites u =
  [ ( ExpectClass R1
    , rewriteArg ix (rewriteAt pos setRule)
    )
  | (ix, pos, _) <- ruleSites u
  ]
  where
    setRule (SRule _ theta ws d hs a) = SRule (RuleId "mut_hidden_rule") theta ws d hs a
    setRule t = t

-- R12: extend the carried policy with a strict rule and a contrary pair on
-- its conclusion (spec §8.1 Path-B well-formedness violation).
hiddenContrarySites :: Unit -> [(Expected, Unit -> Unit)]
hiddenContrarySites _ =
  [ ( ExpectClass R12
    , \u ->
        u
          { unitRules = unitRules u ++ [mutStrictRule]
          , unitContraries = unitContraries u ++ [mutContrary]
          }
    )
  ]
  where
    mutP = AtomPat (Pred "mut_p") []
    mutQ = AtomPat (Pred "mut_q") []
    mutStrictRule =
      Rule (RuleId "mut_strict") [] Strict [] mutP False [] []
    mutContrary = Contrary mutQ mutP

-- R3: rename one substitution key off the rule's parameter list.
wrongSubstSites :: Unit -> [(Expected, Unit -> Unit)]
wrongSubstSites u =
  [ ( ExpectClass R3
    , rewriteArg ix (rewriteAt pos renameKey)
    )
  | (ix, pos, SRule _ theta _ _ _ _) <- ruleSites u
  , not (null theta)
  ]
  where
    renameKey (SRule r ((_, t0) : theta) ws d hs a) =
      SRule r ((Param "mut_x", t0) : theta) ws d hs a
    renameKey t = t

-- R4: swap the first premise child for a declared leaf whose proposition is
-- ≢ the instantiated premise pattern.
wrongPremiseSites :: Unit -> [(Expected, Unit -> Unit)]
wrongPremiseSites u =
  [ ( ExpectClass R4
    , rewriteArg ix (rewriteAt pos (swapPremise l'))
    )
  | (ix, pos, SRule rn theta (_ : _) _ _ _) <- ruleSites u
  , Just r <- [ruleOf u rn]
  , Just (expected0 : _) <- [instAPats theta (rulePremises r)]
  , Just l' <- [inequivLeaf u expected0]
  ]
  where
    swapPremise l' (SRule r theta (_ : ws) d hs a) = SRule r theta (SLeaf l' : ws) d hs a
    swapPremise _ t = t

-- R5: drop one discharge of a mandatory question without opening a hole.
openObligationSites :: Unit -> [(Expected, Unit -> Unit)]
openObligationSites u =
  [ ( ExpectClass R5
    , rewriteArg ix (rewriteAt pos (dropDischarge q))
    )
  | (ix, pos, SRule rn _ _ d _ _) <- ruleSites u
  , Just r <- [ruleOf u rn]
  , (q, _) <- take 1 [entry | entry@(q, _) <- d, mandatoryIn r q]
  ]
  where
    mandatoryIn r q =
      any (\qd -> questionId qd == q && questionNecessity qd == Mandatory) (ruleQuestions r)
    dropDischarge q (SRule r theta ws d hs a) =
      SRule r theta ws [entry | entry@(q', _) <- d, q' /= q] hs a
    dropDischarge _ t = t

-- R6: answer one known question with a declared-but-≢ leaf.
wrongDischargeSites :: Unit -> [(Expected, Unit -> Unit)]
wrongDischargeSites u =
  [ ( ExpectClass R6
    , rewriteArg ix (rewriteAt pos (swapDischarge q l'))
    )
  | (ix, pos, SRule rn theta _ d _ _) <- ruleSites u
  , Just r <- [ruleOf u rn]
  , (q, answer) <-
      take
        1
        [ (q, answer)
        | (q, _) <- d
        , Just qd <- [find ((== q) . questionId) (ruleQuestions r)]
        , Just answer <- [instAPat theta (questionAnswer qd)]
        ]
  , Just l' <- [inequivLeaf u answer]
  ]
  where
    swapDischarge q l' (SRule r theta ws d hs a) =
      SRule r theta ws [(q', if q' == q then SLeaf l' else w) | (q', w) <- d] hs a
    swapDischarge _ _ t = t

-- R7: claim @trusted@ assurance on a defeasible instance.
trustedAssuranceSites :: Unit -> [(Expected, Unit -> Unit)]
trustedAssuranceSites u =
  [ ( ExpectClass R7
    , rewriteArg ix (rewriteAt pos setTrusted)
    )
  | (ix, pos, SRule _ _ _ _ _ AssuranceNone) <- ruleSites u
  ]
  where
    setTrusted (SRule r theta ws d hs _) = SRule r theta ws d hs AssuranceTrusted
    setTrusted t = t

-- R7: point an allowlisted certificate at a theory digest no certifier lists.
certTheorySwapSites :: Unit -> [(Expected, Unit -> Unit)]
certTheorySwapSites u =
  [ ( ExpectClass R7
    , rewriteArg ix (rewriteAt pos swapTheory)
    )
  | (ix, pos, SRule _ _ _ _ _ (AssuranceCert _)) <- ruleSites u
  ]
  where
    swapTheory (SRule r theta ws d hs (AssuranceCert cert)) =
      SRule r theta ws d hs (AssuranceCert cert {certTheory = TheoryDigest "sha256:mut"})
    swapTheory t = t

-- R13: corrupt an allowlisted certificate's opaque payload (replay reject).
certPayloadSites :: Unit -> [(Expected, Unit -> Unit)]
certPayloadSites u =
  [ ( ExpectClass R13
    , rewriteArg ix (rewriteAt pos tamper)
    )
  | (ix, pos, SRule _ _ _ _ _ (AssuranceCert _)) <- ruleSites u
  ]
  where
    tamper (SRule r theta ws d hs (AssuranceCert cert)) =
      SRule r theta ws d hs (AssuranceCert cert {certPayload = SAtom "mut_corrupt"})
    tamper t = t

-- R10: push an attack position off the target term (undercut/undermine) or
-- retarget a rebut at a leaf-rooted argument (wrong occurrence kind).
badAttackPositionSites :: Unit -> [(Expected, Unit -> Unit)]
badAttackPositionSites u =
  [ (ExpectClass R10, \u' -> u' {unitAttacks = replaceIx i k' (unitAttacks u')})
  | (i, k) <- zip [0 :: Int ..] (unitAttacks u)
  , Just k' <- [mutateAttack k]
  ]
  where
    leafRootedArg = fst <$> find (isLeaf . snd) (unitArgs u)
    isLeaf SLeaf{} = True
    isLeaf _ = False
    mutateAttack k = case k of
      Rebut w _ -> Rebut w <$> leafRootedArg
      Undercut w t _ -> Just (Undercut w t [StepPremise 99])
      Undermine w t _ -> Just (Undermine w t [StepPremise 99])
    replaceIx i x xs = [if j == i then x else y | (j, y) <- zip [0 ..] xs]

-- R11: declare a self-rebut on a rule-rooted argument; no contrary pair
-- relates a conclusion to itself in any base policy.
unlicensedAttackSites :: Unit -> [(Expected, Unit -> Unit)]
unlicensedAttackSites u =
  [ ( ExpectClass R11
    , \u' -> u' {unitAttacks = unitAttacks u' ++ [Rebut aid aid]}
    )
  | Just aid <- [fst <$> find (isRule . snd) (unitArgs u)]
  ]
  where
    isRule SRule{} = True
    isRule _ = False

-- R9: group two ≢ leaves as duplicate reports of one cell under the
-- escalating conflict mode.
groupConflictSites :: Unit -> [(Expected, Unit -> Unit)]
groupConflictSites u =
  [ ( ExpectClass R9
    , \u' ->
        u'
          { unitGroups = unitGroups u' ++ [DupGroup (GroupId "mut_g") [l1, l2]]
          , unitGroupMode = RejectOnConflict
          }
    )
  | null (unitGroups u)
  , Just (l1, l2) <- [conflictPair]
  ]
  where
    conflictPair =
      case [ (a, b)
           | ((a, pa) : rest) <- [unitLeaves u]
           , (b, pb) <- rest
           , not (equiv pa pb)
           ] of
        (pair : _) -> Just pair
        [] -> Nothing

-- R13 (replay preflight): duplicate or unknown selected backend.
replayMutants :: String -> CheckInput -> [Mutant]
replayMutants base input =
  concat
    [ replayMutant OpDuplicateBackend (backends ++ take 1 backends)
    , replayMutant OpUnknownBackend (backends ++ [(BackendId "mut_backend", "9")])
    ]
  where
    rid = inputReplayId input
    backends = replayBackends rid
    replayMutant op backends'
      | null backends = []
      | otherwise =
          [ Mutant (mutantFileName base op 0) base op (ExpectClass R13) bytes
          | Right rid' <-
              [ mkReplayId
                  (replayCore rid)
                  (replayPolicy rid)
                  backends'
                  (replayTheories rid)
                  (replayArtifact rid)
              ]
          , Right mutated <- [mkCheckInput rid' (inputUnit input)]
          , let bytes = printSExpr (encodeCheckInput mutated) ++ "\n"
          ]

-- ---------------------------------------------------------------------------
-- Codec-corruption mutants (R14 family: exit 2, no verdict)
-- ---------------------------------------------------------------------------

-- | Codec-corruption mutants of one base anchor's exact file bytes. Each is a
-- structured corruption of the parsed envelope (or, for 'OpCodecTruncate', of
-- the raw bytes) that must fail 'Lara.Wire.decodeCheckInputFile' on both
-- drivers: exit 2, empty stdout.
codecMutantsForBase :: String -> String -> [Mutant]
codecMutantsForBase base bytes = case parseSExpr bytes of
  Left _ -> []
  Right top ->
    [ Mutant (mutantFileName base op 0) base op ExpectCodecReject out
    | (op, mutate) <- ops
    , Just mutated <- [mutate top]
    , let out = printSExpr mutated ++ "\n"
    ]
      ++ [ Mutant
             (mutantFileName base OpCodecTruncate 0)
             base
             OpCodecTruncate
             ExpectCodecReject
             (truncateBytes bytes)
         ]
  where
    ops =
      [ (OpCodecJunkSection, junkSection)
      , (OpCodecCoreVersion, coreVersion)
      , (OpCodecReplayOrder, replayOrder)
      , (OpCodecTheoryMismatch, theoryMismatch)
      , (OpCodecDanglingAttack, danglingAttack)
      ]
    junkSection (SList kids) = Just (SList (kids ++ [SList [SAtom "mut_junk"]]))
    junkSection _ = Nothing
    coreVersion = mapAtom (\a -> if a == "lara-core@0.1" then "lara-core@0.2" else a)
    replayOrder (SList [ci, SList (ridTag : core : policy : rest), unit]) =
      Just (SList [ci, SList (ridTag : policy : core : rest), unit])
    replayOrder _ = Nothing
    theoryMismatch = mapSection "theories" (\kids -> Just (kids ++ [SAtom "sha256:zzz_mut"]))
    danglingAttack = mapSection "attacks" retargetFirst
    retargetFirst (SList (kind : w : SAtom _ : rest) : ks) =
      Just (SList (kind : w : SAtom "mut_missing" : rest) : ks)
    retargetFirst _ = Nothing
    truncateBytes b =
      let trimmed = reverse (dropWhile (/= ')') (reverse b))
       in case reverse trimmed of
            (')' : prefix) -> reverse prefix ++ "\n"
            _ -> b ++ "("

-- | Rewrite every atom in a tree.
mapAtom :: (String -> String) -> SExpr -> Maybe SExpr
mapAtom f = Just . go
  where
    go (SAtom a) = SAtom (f a)
    go (SList kids) = SList (map go kids)

-- | Rewrite the children of the first @(tag …)@ form found anywhere in the
-- tree; 'Nothing' when the section is absent or the rewrite declines.
mapSection :: String -> ([SExpr] -> Maybe [SExpr]) -> SExpr -> Maybe SExpr
mapSection tag f = go
  where
    go (SList (SAtom t : kids))
      | t == tag = SList . (SAtom t :) <$> f kids
    go (SList kids) = SList <$> goKids kids
    go _ = Nothing
    goKids [] = Nothing
    goKids (k : ks) = case go k of
      Just k' -> Just (k' : ks)
      Nothing -> (k :) <$> goKids ks

-- ---------------------------------------------------------------------------
-- The constructed rebut-cycle family (specified statuses, not a rejection)
-- ---------------------------------------------------------------------------

-- | Attack N-cycles are the one Phase D mutation class that is specified NOT
-- to reject (spec §10.1): grounded semantics labels every cycle member
-- @undec@, so every queried claim is @contested@. Sizes are drawn from the
-- seeded stream; the units are constructed (they mutate no base anchor).
cycleMutants :: [Mutant]
cycleMutants =
  [ Mutant
      ("cycle-rebut-" ++ show n ++ ".sexp")
      "-"
      OpRebutCycle
      ExpectAllContested
      (cycleBytes n)
  | n <- sizes
  ]
  where
    draws = take 16 (streamFor "-" OpRebutCycle)
    sizes = takeDistinct 4 [2 + fromIntegral (w `mod` 8) | w <- draws]
    takeDistinct k = go []
      where
        go acc _ | length acc == k = reverse acc
        go acc [] = reverse acc
        go acc (x : xs)
          | x `elem` acc = go acc xs
          | otherwise = go (x : acc) xs

cycleBytes :: Int -> String
cycleBytes n = case checkInput of
  Right input -> printSExpr (encodeCheckInput input) ++ "\n"
  Left err -> error ("cycleBytes: impossible replay identity error: " ++ show err)
  where
    checkInput = do
      rid <-
        mkReplayId
          LaraCoreV01
          (PolicyId "mutation-cycles-v1")
          [(BackendId "nd", "1")]
          []
          (Digest "sha256:mutation-cycles-v1")
      mkCheckInput rid unit
    conName i = "c" ++ show i
    conTerm i = TCon (FunSym (conName i)) []
    holds i = Prop (Pred "holds") [conTerm i]
    obs i = Prop (Pred "obs") [conTerm i]
    holdsPat = AtomPat (Pred "holds") [PVar (Param "X")]
    obsPat = AtomPat (Pred "obs") [PVar (Param "X")]
    cyc = Rule (RuleId "cyc") [Param "X"] Defeasible [obsPat] holdsPat False [] []
    groundPat i = AtomPat (Pred "holds") [PLit (conTerm i)]
    contraries = [Contrary (groundPat i) (groundPat (succIx i)) | i <- ixes]
    leaves = [(LeafId ("l" ++ show i), obs i) | i <- ixes]
    args =
      [ ( ArgId ("a" ++ show i)
        , SRule
            (RuleId "cyc")
            [(Param "X", conTerm i)]
            [SLeaf (LeafId ("l" ++ show i))]
            []
            []
            AssuranceNone
        )
      | i <- ixes
      ]
    attacks = [Rebut (ArgId ("a" ++ show i)) (ArgId ("a" ++ show (succIx i))) | i <- ixes]
    queries = map holds ixes
    ixes = [0 .. n - 1]
    succIx i = (i + 1) `mod` n
    unit =
      Unit
        [cyc]
        contraries
        []
        []
        leaves
        args
        attacks
        queries
        []
        QuarantineOnConflict
