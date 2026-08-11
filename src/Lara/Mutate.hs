-- | Seeded mutation generators for the M5 evaluation corpus (tracker #48, T1;
-- spec §10.1 mutation table; freeze @docs/m5-freeze-checklist.md@).
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
  , parseExpected
  , statusText
  , codecDiagnostics
    -- * Mutants
  , Mutant (..)
  , mutantPath
  , mutantFileName
  , mutationSeed
  , mutationBases
  , mutantsForBase
  , codecMutantsForBase
  , cycleMutants
  , manifestFor
    -- * Corpus sweep (uniform derived-applicability, D9)
  , corpusBudget
  , corpusMutants
  , corpusSweepReport
    -- * Seeded stream (exposed for tests)
  , splitMix64
  , stringSeed
  ) where

import Data.Bits (shiftR, xor)
import Data.Char (ord)
import Data.List (find)
import Data.Word (Word64)

import Lara.AST
import Lara.Diagnostics (Constituent (..), constituentText)
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
import qualified Lara.Mutate.Sorts as Sorts
import Lara.Sigma
  ( ConSig (..)
  , PredSig (..)
  , Sigma (..)
  , Sort (..)
  , SortName (..)
  , declarePred
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
  | OpHoleObligation -- ^ swap a mandatory discharge for a declared hole → obligation gate
  | OpTrustedAssurance -- ^ @trusted@ on a defeasible instance → R7
  | OpCertTheorySwap -- ^ certificate theory not allowlisted → R7
  | OpCertPayloadTamper -- ^ corrupt an allowlisted cert payload → R13
  | OpDuplicateBackend -- ^ replay selects one backend twice → R13
  | OpUnknownBackend -- ^ replay selects an unknown backend → R13
  | OpGroupConflict -- ^ escalated ≢ duplicate-report group → R9
  | OpUndeclaredPred -- ^ atom head with no @pred@ declaration → R2
  | OpWrongPredArity -- ^ drop an atom argument → R2
  | OpWrongArgSort -- ^ swap in a differently-sorted term from the unit → R2
  | OpUndeclaredCon -- ^ constructor head with no @con@ declaration → R2
  | OpWrongThetaSort -- ^ θ range term of the wrong sort at a declared param → R2
  | OpOutOfScopeVar -- ^ rule pattern variable off @ruleParams@ → R12
  | OpSigmaDuplicateSort -- ^ duplicate declared sort → R2
  | OpSigmaShadowBase -- ^ declared @Num@ shadows a base sort → R2
  | OpSigmaDuplicateCon -- ^ duplicate constructor declaration → R2
  | OpSigmaDuplicatePred -- ^ duplicate predicate declaration → R2
  | OpSigmaConUndeclaredSort -- ^ constructor signature names undeclared sort → R2
  | OpSigmaPredUndeclaredSort -- ^ predicate signature names undeclared sort → R2
  | OpRebutCycle -- ^ constructed rebut N-cycle → accept, all contested
  | OpDropSupport -- ^ remove the claim's support → accept, gap
  | OpAttachUndercut -- ^ undercut via the rule's exception → accept, defeated
  | OpAttachRebutCycle -- ^ symmetric-contrary rebut 2-cycle → accept, contested
  | OpAttachUndermine -- ^ undermine a premise leaf (1-dir contrary) → accept, defeated
  | OpAttachReinstate -- ^ undercut + counter-undercut → accept, justified under attack
  | OpQuarantineAttacker -- ^ quarantine the sole attacker → accept, evidence-blocked
  | OpCodecSigmaJunk -- ^ extra field inside the @sigma@ section
  | OpCodecSigmaOrder -- ^ @sigma@ appears after @policy@
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
  OpHoleObligation -> "hole-obligation"
  OpTrustedAssurance -> "trusted-assurance"
  OpCertTheorySwap -> "cert-theory-swap"
  OpCertPayloadTamper -> "cert-payload-tamper"
  OpDuplicateBackend -> "duplicate-backend"
  OpUnknownBackend -> "unknown-backend"
  OpGroupConflict -> "group-conflict"
  OpUndeclaredPred -> "undeclared-pred"
  OpWrongPredArity -> "wrong-pred-arity"
  OpWrongArgSort -> "wrong-arg-sort"
  OpUndeclaredCon -> "undeclared-con"
  OpWrongThetaSort -> "wrong-theta-sort"
  OpOutOfScopeVar -> "out-of-scope-var"
  OpSigmaDuplicateSort -> "sigma-duplicate-sort"
  OpSigmaShadowBase -> "sigma-shadow-base"
  OpSigmaDuplicateCon -> "sigma-duplicate-con"
  OpSigmaDuplicatePred -> "sigma-duplicate-pred"
  OpSigmaConUndeclaredSort -> "sigma-con-undeclared-sort"
  OpSigmaPredUndeclaredSort -> "sigma-pred-undeclared-sort"
  OpRebutCycle -> "rebut-cycle"
  OpDropSupport -> "drop-support"
  OpAttachUndercut -> "attach-undercut"
  OpAttachRebutCycle -> "attach-rebut-cycle"
  OpAttachUndermine -> "attach-undermine"
  OpAttachReinstate -> "attach-reinstate"
  OpQuarantineAttacker -> "quarantine-attacker"
  OpCodecSigmaJunk -> "codec-sigma-junk"
  OpCodecSigmaOrder -> "codec-sigma-order"
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
  OpHoleObligation -> "open-obligations"
  OpTrustedAssurance -> "certificate-tampering"
  OpCertTheorySwap -> "certificate-tampering"
  OpCertPayloadTamper -> "certificate-tampering"
  OpDuplicateBackend -> "certificate-tampering"
  OpUnknownBackend -> "certificate-tampering"
  OpGroupConflict -> "data-integrity"
  OpUndeclaredPred -> "signature"
  OpWrongPredArity -> "signature"
  OpWrongArgSort -> "signature"
  OpUndeclaredCon -> "signature"
  OpWrongThetaSort -> "signature"
  OpOutOfScopeVar -> "hidden-policy-extension"
  OpSigmaDuplicateSort -> "signature"
  OpSigmaShadowBase -> "signature"
  OpSigmaDuplicateCon -> "signature"
  OpSigmaDuplicatePred -> "signature"
  OpSigmaConUndeclaredSort -> "signature"
  OpSigmaPredUndeclaredSort -> "signature"
  OpRebutCycle -> "cycles"
  OpDropSupport -> "accept-verdict"
  OpAttachUndercut -> "accept-verdict"
  OpAttachRebutCycle -> "accept-verdict"
  OpAttachUndermine -> "accept-verdict"
  OpAttachReinstate -> "accept-verdict"
  OpQuarantineAttacker -> "accept-verdict"
  OpCodecSigmaJunk -> "codec-corruption"
  OpCodecSigmaOrder -> "codec-corruption"
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
-- a fixed class, the structural obligation-gate reject, a codec-boundary
-- reject (exit 2, no verdict), or — for the cycle family — an accept in which
-- every label is @undec@ and every queried status is @contested@.
data Expected
  = ExpectClass RejectClass
  | ExpectIncompleteArgument
  -- ^ the structural obligation-gate reject ('Lara.AST.IncompleteArgument', a
  -- 'Rejection' with no R-class by design): the mutant is schema-valid — R5
  -- coverage holds because the open question is covered by a declared hole —
  -- and the full system rejects it only at the obligation gate
  -- ('Lara.Check.ccObligationGate'), i.e. an argument reaching the root with
  -- an open mandatory obligation.
  | ExpectCodecReject
  | ExpectAllContested
  | ExpectEvidenceBlocked
  -- ^ the conservative-reporting outcome (spec §4.3, issue #76, spelled
  -- @accept-evidence-blocked@): the verdict accepts, but §4.3 quarantine edited
  -- the program under the queried claim, so its four-state label is only a
  -- conditional diagnostic and its public status is @evidence-blocked@. A
  -- mutant of this class that reported an ordinary status would be the #76 bug
  -- back again.
  | ExpectPrimaryStatus Status
  -- ^ the accept-family outcome: the verdict accepts and the queried claim's
  -- status is exactly this one (spelled @accept-\<status\>@). Structural
  -- verification of the constructed attack shape lives in "Lara.Mutate.Accept"
  -- ('Lara.Mutate.Accept.acceptStructureOk'), not in the manifest spelling.
  deriving (Eq, Ord, Show)

-- | Manifest spelling of an expected outcome.
expectedText :: Expected -> String
expectedText e = case e of
  ExpectClass c -> "reject-" ++ show c
  ExpectIncompleteArgument -> "reject-" ++ show IncompleteArgument
  ExpectCodecReject -> "codec-reject"
  ExpectAllContested -> "accept-all-contested"
  ExpectEvidenceBlocked -> "accept-evidence-blocked"
  ExpectPrimaryStatus s -> "accept-" ++ statusText s

-- | Manifest spelling of a claim status (the accept-family @accept-\<status\>@
-- suffix; matches @corpus-units/expected.json@'s status strings).
statusText :: Status -> String
statusText s = case s of
  Gap -> "gap"
  Justified -> "justified"
  Contested -> "contested"
  Defeated -> "defeated"

-- | Inverse of 'expectedText' — the one parse table for the @expected@ manifest
-- column (shared by @test\/MutationSpec.hs@, "Lara.Measure", and
-- @scripts\/measure.hs@). 'Nothing' on any spelling this table does not produce.
parseExpected :: String -> Maybe Expected
parseExpected s =
  lookup s $
    ("codec-reject", ExpectCodecReject)
      : ("accept-all-contested", ExpectAllContested)
      : (expectedText ExpectEvidenceBlocked, ExpectEvidenceBlocked)
      : (expectedText ExpectIncompleteArgument, ExpectIncompleteArgument)
      : [(expectedText (ExpectClass c), ExpectClass c) | c <- [minBound .. maxBound]]
      ++ [ (expectedText (ExpectPrimaryStatus st), ExpectPrimaryStatus st)
         | st <- [Gap, Justified, Contested, Defeated]
         ]

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
  OpCodecSigmaJunk ->
    Just
      ( "wrong number of fields for sigma"
      , "sigma: arity"
      )
  OpCodecSigmaOrder ->
    Just
      ( "unit: unexpected section"
      , "unit: unexpected section"
      )
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
  , mutantSite :: Maybe Constituent
  -- ^ the seeded ground-truth location (the constituent the operator mutated),
  -- rendered as the @expected-location@ manifest column; 'Nothing' for mutants
  -- with no single seeded site (the codec family and the constructed
  -- rebut-cycle family), which render @-@.
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
-- operator, expected, hs-diagnostic, lean-diagnostic, expected-location). The
-- diagnostic columns are the 'codecDiagnostics' deletion-sensitivity pins —
-- non-empty exactly for the codec-corruption rows. @expected-location@ is the
-- seeded ground-truth constituent ('mutantSite'), appended as column 8 (@-@
-- when there is no single seeded site); it is appended, never inserted earlier,
-- because @scripts\/differential.sh@ hardcodes the expected column (@$5@) and
-- the diagnostic pins (@$6@\/@$7@).
manifestFor :: [Mutant] -> String
manifestFor ms =
  unlines
    ( "# file\tbase\tfamily\toperator\texpected\ths-diagnostic\tlean-diagnostic\texpected-location"
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
              ++ "\t"
              ++ maybe "-" constituentText (mutantSite m)
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

-- | The infinite output stream of a string-keyed generator (the one place the
-- @mutationSeed@ is folded into a stream key).
streamForKey :: String -> [Word64]
streamForKey key = go (mutationSeed `xor` stringSeed key)
  where
    go s = let (s', w) = splitMix64 s in w : go s'

-- | The infinite output stream of the @(base, operator)@-keyed generator.
streamFor :: String -> MutationOp -> [Word64]
streamFor base op = streamForKey (base ++ "/" ++ opName op)

-- | Deterministically pick at most @k@ elements (first-draw order, no repeats)
-- from a list, driven by a given stream.
pickWithStream :: [Word64] -> Int -> [a] -> [a]
pickWithStream ws k xs
  | n <= k = xs
  | otherwise = [xs !! i | i <- chosen]
  where
    n = length xs
    chosen = go [] (take (16 * k) ws)
    go acc _ | length acc == k = reverse acc
    go acc [] = reverse acc
    go acc (w : rest)
      | i `elem` acc = go acc rest
      | otherwise = go (i : acc) rest
      where
        i = fromIntegral (w `mod` fromIntegral n)

-- | Deterministically pick at most @k@ elements from the applicable sites,
-- keyed by @(base, operator)@.
pickSome :: String -> MutationOp -> Int -> [a] -> [a]
pickSome base op = pickWithStream (streamFor base op)

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
    , unitMutants base input OpHoleObligation 1 holeObligationSites
    , unitMutants base input OpWrongDischarge 1 wrongDischargeSites
    , unitMutants base input OpTrustedAssurance 1 trustedAssuranceSites
    , unitMutants base input OpCertTheorySwap 1 certTheorySwapSites
    , unitMutants base input OpCertPayloadTamper 1 certPayloadSites
    , unitMutants base input OpBadAttackPosition 2 badAttackPositionSites
    , unitMutants base input OpUnlicensedAttack 1 unlicensedAttackSites
    , unitMutants base input OpGroupConflict 1 groupConflictSites
    , -- The signature family (@lara-core\@0.2@, #89 D10): R2 had zero mutants
      -- before this pass, and spec §10.1 requires every class to be exercised.
      unitMutants base input OpUndeclaredPred 1 (classed Sorts.undeclaredPredSites)
    , unitMutants base input OpWrongPredArity 1 (classed Sorts.wrongPredAritySites)
    , unitMutants base input OpWrongArgSort 2 (classed Sorts.wrongArgSortSites)
    , unitMutants base input OpUndeclaredCon 1 (classed Sorts.undeclaredConSites)
    , unitMutants base input OpWrongThetaSort 1 (classed Sorts.wrongThetaSortSites)
    , unitMutants base input OpOutOfScopeVar 1 (classed Sorts.outOfScopeVarSites)
    , -- Integrated Σ well-formedness fixtures are dedicated negatives, not a
      -- sweep: one row per clause, anchored once at the first worked example.
      dedicatedSigma OpSigmaDuplicateSort Sorts.duplicateSortSites
    , dedicatedSigma OpSigmaShadowBase Sorts.shadowBaseSortSites
    , dedicatedSigma OpSigmaDuplicateCon Sorts.duplicateConSites
    , dedicatedSigma OpSigmaDuplicatePred Sorts.duplicatePredSites
    , dedicatedSigma OpSigmaConUndeclaredSort Sorts.conUndeclaredSortSites
    , dedicatedSigma OpSigmaPredUndeclaredSort Sorts.predUndeclaredSortSites
    , replayMutants base input
    ]
  where
    -- "Lara.Mutate.Sorts" sits below the operator vocabulary and yields bare
    -- rejection classes; wrapping them here keeps 'Expected' owned by exactly
    -- one module.
    classed sites u = [(ExpectClass c, loc, f) | (c, loc, f) <- sites u]
    dedicatedSigma op sites
      | base == "A" = unitMutants base input op 1 (classed sites)
      | otherwise = []

-- | Assemble the picked unit-mutation sites of one operator into mutants. Each
-- site carries its seeded ground-truth 'Constituent', threaded into
-- 'mutantSite'.
unitMutants
  :: String
  -> CheckInput
  -> MutationOp
  -> Int
  -> (Unit -> [(Expected, Constituent, Unit -> Unit)])
  -> [Mutant]
unitMutants base input op cap sites =
  [ Mutant (mutantFileName base op k) base op expected (Just site) bytes
  | (k, (expected, site, mutate)) <- zip [0 :: Int ..] picked
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
undeclaredLeafSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
undeclaredLeafSites u =
  [ ( ExpectClass R1
    , CArgument ix
    , rewriteArg ix (rewriteAt pos (const (SLeaf (LeafId "mut_undeclared"))))
    )
  | (ix, pos, _) <- leafSites u
  ]

-- R1: instantiate a rule id the policy section never declares.
hiddenRuleSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
hiddenRuleSites u =
  [ ( ExpectClass R1
    , CArgument ix
    , rewriteArg ix (rewriteAt pos setRule)
    )
  | (ix, pos, _) <- ruleSites u
  ]
  where
    setRule (SRule _ theta ws d hs a) = SRule (RuleId "mut_hidden_rule") theta ws d hs a
    setRule t = t

-- R12: extend the carried policy with a strict rule and a contrary pair on
-- its conclusion (spec §8.1 Path-B well-formedness violation).
hiddenContrarySites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
hiddenContrarySites _ =
  [ ( ExpectClass R12
    , CPolicy
    , \u ->
        u
          { unitRules = unitRules u ++ [mutStrictRule]
          , unitContraries = unitContraries u ++ [mutContrary]
          , unitSigma = declareMut (unitSigma u)
          }
    )
  ]
  where
    mutP = AtomPat (Pred "mut_p") []
    mutQ = AtomPat (Pred "mut_q") []
    mutStrictRule =
      Rule (RuleId "mut_strict") [] Strict [] [] mutP False [] []
    mutContrary = Contrary mutQ mutP
    -- Σ-aware injection (#89 §8): the operator that invents `mut_p`/`mut_q`
    -- declares them, so the mutant tests R12 — the class it seeds — instead of
    -- flipping to R2 on incidental signature noise.
    declareMut sg = declarePred (Pred "mut_p") [] (declarePred (Pred "mut_q") [] sg)

-- R3: rename one substitution key off the rule's parameter list.
wrongSubstSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
wrongSubstSites u =
  [ ( ExpectClass R3
    , CArgument ix
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
wrongPremiseSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
wrongPremiseSites u =
  [ ( ExpectClass R4
    , CArgument ix
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
openObligationSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
openObligationSites u =
  [ ( ExpectClass R5
    , CArgument ix
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

-- Obligation gate: replace one mandatory discharge with a declared hole. The
-- clone of 'openObligationSites' that swaps the entry into the hole set
-- instead of deleting it: R5 coverage still holds (the question is covered by
-- the hole), so the schema-valid argument reaches the obligation gate with an
-- open mandatory obligation — the full system rejects with
-- 'IncompleteArgument', and only 'Lara.Check.noCQConfig' accepts it. Only
-- mandatory discharges are sites: holing an optional question's discharge
-- contributes no obligation ('Lara.SupportTerm.openMandatory') and the full
-- system would accept.
holeObligationSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
holeObligationSites u =
  [ ( ExpectIncompleteArgument
    , CArgument ix
    , rewriteArg ix (rewriteAt pos (holeDischarge q))
    )
  | (ix, pos, SRule rn _ _ d _ _) <- ruleSites u
  , Just r <- [ruleOf u rn]
  , (q, _) <- take 1 [entry | entry@(q, _) <- d, mandatoryIn r q]
  ]
  where
    mandatoryIn r q =
      any (\qd -> questionId qd == q && questionNecessity qd == Mandatory) (ruleQuestions r)
    holeDischarge q (SRule r theta ws d hs a) =
      SRule r theta ws [entry | entry@(q', _) <- d, q' /= q] (hs ++ [holeOf q]) a
    holeDischarge _ t = t
    holeOf (QuestionId s) = ObligationId s

-- R6: answer one known question with a declared-but-≢ leaf.
wrongDischargeSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
wrongDischargeSites u =
  [ ( ExpectClass R6
    , CArgument ix
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
trustedAssuranceSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
trustedAssuranceSites u =
  [ ( ExpectClass R7
    , CArgument ix
    , rewriteArg ix (rewriteAt pos setTrusted)
    )
  | (ix, pos, SRule _ _ _ _ _ AssuranceNone) <- ruleSites u
  ]
  where
    setTrusted (SRule r theta ws d hs _) = SRule r theta ws d hs AssuranceTrusted
    setTrusted t = t

-- R7: point an allowlisted certificate at a theory digest no certifier lists.
certTheorySwapSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
certTheorySwapSites u =
  [ ( ExpectClass R7
    , CArgument ix
    , rewriteArg ix (rewriteAt pos swapTheory)
    )
  | (ix, pos, SRule _ _ _ _ _ (AssuranceCert _)) <- ruleSites u
  ]
  where
    swapTheory (SRule r theta ws d hs (AssuranceCert cert)) =
      SRule r theta ws d hs (AssuranceCert cert {certTheory = TheoryDigest "sha256:mut"})
    swapTheory t = t

-- R13: corrupt an allowlisted certificate's opaque payload (replay reject).
certPayloadSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
certPayloadSites u =
  [ ( ExpectClass R13
    , CArgument ix
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
badAttackPositionSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
badAttackPositionSites u =
  [ (ExpectClass R10, CAttack i, \u' -> u' {unitAttacks = replaceIx i k' (unitAttacks u')})
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
unlicensedAttackSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
unlicensedAttackSites u =
  [ ( ExpectClass R11
    , CAttack (length (unitAttacks u)) -- the appended self-rebut's index
    , \u' -> u' {unitAttacks = unitAttacks u' ++ [Rebut aid aid]}
    )
  | Just aid <- [fst <$> find (isRule . snd) (unitArgs u)]
  ]
  where
    isRule SRule{} = True
    isRule _ = False

-- R9: group two ≢ leaves as duplicate reports of one cell under the
-- escalating conflict mode.
groupConflictSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
groupConflictSites u =
  [ ( ExpectClass R9
    , CGroup (GroupId "mut_g")
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

-- R13 (replay preflight): duplicate or unknown selected backend. Both replay
-- operators over one base.
replayMutants :: String -> CheckInput -> [Mutant]
replayMutants base input =
  replayMutant base input OpDuplicateBackend
    ++ replayMutant base input OpUnknownBackend

-- | The single R13 replay-preflight mutant of one base for one replay operator
-- ('OpDuplicateBackend' repeats a selected backend, 'OpUnknownBackend' appends
-- an unselected one). Empty when the base declares no backends to corrupt; the
-- seeded ground truth is the replay envelope ('CReplayEnvelope').
replayMutant :: String -> CheckInput -> MutationOp -> [Mutant]
replayMutant base input op
  | null backends = []
  | otherwise =
      [ Mutant (mutantFileName base op 0) base op (ExpectClass R13) (Just CReplayEnvelope) bytes
      | Right rid' <-
          [ mkReplayId
              (replayCore rid)
              (replayPolicy rid)
              (corruptedBackends op)
              (replayTheories rid)
              (replayArtifact rid)
          ]
      , Right mutated <- [mkCheckInput rid' (inputUnit input)]
      , let bytes = printSExpr (encodeCheckInput mutated) ++ "\n"
      ]
  where
    rid = inputReplayId input
    backends = replayBackends rid
    corruptedBackends OpUnknownBackend = backends ++ [(BackendId "mut_backend", "9")]
    corruptedBackends OpDuplicateBackend = backends ++ take 1 backends
    corruptedBackends other = error ("replayMutant: not a replay operator: " ++ opName other)

-- ---------------------------------------------------------------------------
-- Corpus sweep (uniform derived-applicability rule, eng review D9)
-- ---------------------------------------------------------------------------

-- | The per-operator base budget for the corpus sweep. When an operator's
-- applicable set exceeds this, a budget-sized subset is picked by the
-- operator-keyed stream; at or below it, the whole set is taken (full
-- coverage). A frozen generation constant — changing it regenerates a
-- different, equally valid corpus half and must be an explicit decision.
corpusBudget :: Int
corpusBudget = 12

-- | One rejection operator, viewed for the corpus sweep: its applicability
-- predicate (does this base carry ≥1 site?) and its cap-1 producer at a base.
data SweepOp = SweepOp
  { sweepOp :: MutationOp
  , sweepApplicable :: CheckInput -> Bool
  , sweepAt :: String -> CheckInput -> [Mutant]
  }

-- | The rejection operators swept over corpus bases, in fixed order. This is
-- the same operator set 'mutantsForBase' runs over the worked examples (cert
-- and other arg-dependent operators self-gate via their site enumerators — a
-- gap corpus unit with no args yields no sites, so they propose nothing there,
-- no special casing). Codec corruption and the constructed cycle family are not
-- part of the corpus sweep (they are base-independent structural families).
sweepOps :: [SweepOp]
sweepOps =
  [ unitSweep OpUndeclaredLeaf undeclaredLeafSites
  , unitSweep OpHiddenRule hiddenRuleSites
  , unitSweep OpHiddenContrary hiddenContrarySites
  , unitSweep OpWrongSubstDomain wrongSubstSites
  , unitSweep OpWrongPremise wrongPremiseSites
  , unitSweep OpOpenObligation openObligationSites
  , unitSweep OpHoleObligation holeObligationSites
  , unitSweep OpWrongDischarge wrongDischargeSites
  , unitSweep OpTrustedAssurance trustedAssuranceSites
  , unitSweep OpCertTheorySwap certTheorySwapSites
  , unitSweep OpCertPayloadTamper certPayloadSites
  , unitSweep OpBadAttackPosition badAttackPositionSites
  , unitSweep OpUnlicensedAttack unlicensedAttackSites
  , unitSweep OpGroupConflict groupConflictSites
  , -- The signature family. Sweeping it over the corpus is what makes the
    -- applicability assertion meaningful: `wrong-arg-sort` must find real sites
    -- in corpus-v1's own vocabulary, not only in hand-built examples (#89 §8).
    unitSweep OpUndeclaredPred (classedSites Sorts.undeclaredPredSites)
  , unitSweep OpWrongPredArity (classedSites Sorts.wrongPredAritySites)
  , unitSweep OpWrongArgSort (classedSites Sorts.wrongArgSortSites)
  , unitSweep OpUndeclaredCon (classedSites Sorts.undeclaredConSites)
  , unitSweep OpWrongThetaSort (classedSites Sorts.wrongThetaSortSites)
  , unitSweep OpOutOfScopeVar (classedSites Sorts.outOfScopeVarSites)
  , replaySweep OpDuplicateBackend
  , replaySweep OpUnknownBackend
  ]
  where
    classedSites sites u = [(ExpectClass c, loc, f) | (c, loc, f) <- sites u]
    unitSweep op sites =
      SweepOp
        op
        (\input -> not (null (sites (inputUnit input))))
        (\base input -> unitMutants base input op 1 sites)
    replaySweep op =
      SweepOp
        op
        (\input -> not (null (replayBackends (inputReplayId input))))
        (\base input -> replayMutant base input op)

-- | The bases at which a sweep operator finds ≥1 site (corpus manifest order).
sweepApplicableBases :: SweepOp -> [(String, CheckInput)] -> [(String, CheckInput)]
sweepApplicableBases op bases = [b | b@(_, input) <- bases, sweepApplicable op input]

-- | The bases one sweep operator selects: all applicable bases when they number
-- ≤ 'corpusBudget', else a 'corpusBudget'-sized subset picked by the
-- operator-keyed stream. Order is the applicable-set order (corpus manifest
-- order), so the selection is deterministic.
sweepSelected :: SweepOp -> [(String, CheckInput)] -> [(String, CheckInput)]
sweepSelected op bases =
  pickWithStream
    (streamForKey ("corpus-sweep/" ++ opName (sweepOp op)))
    corpusBudget
    (sweepApplicableBases op bases)

-- | Every corpus-base mutant, operator-major: for each rejection operator, one
-- mutant at each selected base (the seeded first site). The @(base, input)@
-- list is the corpus units in manifest order, each base labelled
-- @\<artifact\>.\<claim_id\>@; @scripts\/gen-mutants.hs@ and
-- @test\/MutationSpec.hs@ pass the same list, so the output is identical.
corpusMutants :: [(String, CheckInput)] -> [Mutant]
corpusMutants bases =
  concat
    [ sweepAt op base input
    | op <- sweepOps
    , (base, input) <- sweepSelected op bases
    ]

-- | The measured per-operator applicable and selected base counts of the corpus
-- sweep, in operator order — the "no silent caps" record the regenerated
-- @README.md@ prints and @test\/MutationSpec.hs@ pins against the manifest.
-- Operators that find no corpus site (the cert operators) appear with
-- @(applicable, selected) = (0, 0)@, so absence is documented, not hidden.
corpusSweepReport :: [(String, CheckInput)] -> [(MutationOp, Int, Int)]
corpusSweepReport bases =
  [ (sweepOp op, length (sweepApplicableBases op bases), length (sweepSelected op bases))
  | op <- sweepOps
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
    [ Mutant (mutantFileName base op 0) base op ExpectCodecReject Nothing out
    | (op, mutate) <- ops
    , Just mutated <- [mutate top]
    , let out = printSExpr mutated ++ "\n"
    ]
      ++ [ Mutant
             (mutantFileName base OpCodecTruncate 0)
             base
             OpCodecTruncate
             ExpectCodecReject
             Nothing
             (truncateBytes bytes)
         ]
  where
    ops =
      sigmaOps
        ++ [ (OpCodecJunkSection, junkSection)
           , (OpCodecCoreVersion, coreVersion)
           , (OpCodecReplayOrder, replayOrder)
           , (OpCodecTheoryMismatch, theoryMismatch)
           , (OpCodecDanglingAttack, danglingAttack)
           ]
    -- The two Sigma decoder corruptions are dedicated fixtures rather than a
    -- per-base sweep: their failure is independent of the unit payload.
    sigmaOps
      | base == "A" =
          [ (OpCodecSigmaJunk, sigmaJunk)
          , (OpCodecSigmaOrder, sigmaOrder)
          ]
      | otherwise = []
    sigmaJunk = mapSection "sigma" (\kids -> Just (kids ++ [SList [SAtom "mut_junk"]]))
    sigmaOrder (SList kids) = SList <$> swapUnit kids
    sigmaOrder _ = Nothing
    swapUnit
      ( SList
          ( SAtom "unit"
              : sigma@(SList (SAtom "sigma" : _))
              : policy@(SList (SAtom "policy" : _))
              : rest
            )
          : siblings
        ) =
        Just
          ( SList (SAtom "unit" : policy : sigma : rest)
              : siblings
          )
    swapUnit (kid : siblings) = (kid :) <$> swapUnit siblings
    swapUnit [] = Nothing
    junkSection (SList kids) = Just (SList (kids ++ [SList [SAtom "mut_junk"]]))
    junkSection _ = Nothing
    -- The fixture text moves with the core-version bump; the expectation does
    -- not. `lara-core@0.1` is retired (#91 decision 5), so it is exactly the
    -- kind of unsupported version this operator must present.
    coreVersion = mapAtom (\a -> if a == "lara-core@0.2" then "lara-core@0.1" else a)
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
      Nothing
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
          LaraCoreV02
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
    cyc = Rule (RuleId "cyc") [Param "X"] Defeasible [obsPat] [] holdsPat False [] []
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
    -- The synthetic unit's own generated Σ (#89 §8): the operator that invents
    -- a vocabulary is the site that knows its sorts, so `mutation-cycles-v1`
    -- declares one opaque sort for its cycle nodes rather than tripping the new
    -- stage-2 check on incidental Σ noise.
    nodeSort = SortDecl (SortName "Node")
    sigma =
      Sigma
        { sigmaSorts = [SortName "Node"]
        , sigmaCons = [ConSig (FunSym (conName i)) [] nodeSort | i <- ixes]
        , sigmaPreds =
            [ PredSig (Pred "holds") [nodeSort]
            , PredSig (Pred "obs") [nodeSort]
            ]
        }
    unit =
      Unit
        sigma
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
