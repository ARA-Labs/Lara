-- | The shared core of the seeded mutation generators for the M5 evaluation
-- corpus (tracker #48, T1; spec §10.1 mutation table; freeze
-- @docs/m5-freeze-checklist.md@): the closed operator vocabulary, the
-- specified-outcome type, and the 'Mutant' record every generator produces.
--
-- Each 'MutationOp' is a surgical, single-defect transformation of a decoded
-- worked-example 'Lara.Replay.CheckInput' (or, for the codec family, of its
-- wire bytes) whose outcome is specified a priori: a rejection class, a
-- codec-boundary reject, or — for the constructed attack-cycle family — an
-- accept whose labels are all @undec@ and whose statuses are all @contested@.
--
-- == The namespace
--
-- The generators themselves live in siblings, each owning one job. This module
-- sits below all of them and imports none of them, so the namespace graph is
-- acyclic and the vocabulary has exactly one home.
--
-- * "Lara.Mutate.Manifest" — the @MANIFEST.tsv@ contract and suite layout
-- * "Lara.Mutate.Seed" — the SplitMix64 stream and seeded selection (internal)
-- * "Lara.Mutate.Sites" — per-operator site enumerators (internal)
-- * "Lara.Mutate.Sorts" — the signature-family site enumerators
-- * "Lara.Mutate.Suite" — worked-example assembly and the corpus sweep
-- * "Lara.Mutate.Codec" — the codec-corruption family (R14)
-- * "Lara.Mutate.Cycle" — the constructed rebut-cycle family
-- * "Lara.Mutate.Accept" — the constructed accept-verdict family
-- * "Lara.Mutate.Accept.Ops" — the six accept constructions (internal)
-- * "Lara.Mutate.Accept.Build" — accept mutant assembly and site helpers (internal)
--
-- The ownership contract behind this layout — which module owns which
-- names, why the root deliberately does not re-export the ones that moved,
-- and the re-export façade alternative that was rejected as cycle-forming —
-- is recorded in @docs\/mutate-module-ownership-decision.md@.
--
-- == Namespace invariants
--
-- The generators are deterministic: every random choice flows from
-- 'mutationSeed' through a SplitMix64 stream keyed by @(base, operator)@, so
-- re-running the generator over unchanged base anchors reproduces the
-- committed mutant bytes exactly (the seeded-reproducibility freshness guard
-- in @test\/MutationSpec.hs@). Because the key threads through 'opName' and
-- selection draws from each enumerator's list in order, renaming an operator
-- or reordering a site list moves committed bytes.
--
-- The namespace only /proposes/ mutants; @scripts\/gen-mutants.hs@ verifies
-- each one against the production checker before writing it (a mutant whose
-- actual verdict differs from its specified outcome aborts generation), and
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
  , mutantFileName
  , mutationSeed
  , mutationBases
  ) where

import Data.Word (Word64)

import Lara.AST
import Lara.Diagnostics (Constituent (..))

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


mutantFileName :: String -> MutationOp -> Int -> String
mutantFileName base op k =
  base ++ "--" ++ opName op ++ "-" ++ show k ++ ".sexp"
