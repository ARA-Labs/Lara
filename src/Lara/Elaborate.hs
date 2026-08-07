-- | The trusted surface boundary: lower a presentation 'Program' (+ its
-- 'Policy') to the frozen checker anchor 'Unit' under the policy's source
-- admission decision (spec plan A1b, D1/D3).
--
-- == Position in the pipeline
--
-- "Lara.Syntax" decodes @.lara@ text to the /presentation/ AST but records
-- support terms __shallowly__ (premises implicit, θ positional under synthetic
-- names @\"1\"..\"n\"@, discharges as bare 'SLeaf' refs; see the "Lara.Syntax"
-- header). "Lara.Elaborate.Internal" rebuilds the __full__ 'SupportTerm' the
-- checker consumes: it re-associates θ with the rule's real parameter names,
-- reconstructs each implicit premise by unique @≡@-match against the declared
-- leaves and prior arguments (spec §5), and re-points discharge targets.
--
-- __That structural lowering is admission-free.__ Presentation callers enter
-- here, through 'prepareSource' and 'runSourceCheck', which bind the full
-- elaboration to its admission decision (the R8 stop and the policy quarantine
-- seed), to the resulting one-pass prune, and to the replay identity — so the
-- four cannot be paired independently. The bare elaborator is not part of this
-- module's API; it lives in "Lara.Elaborate.Internal" as a test\/tooling escape
-- hatch.
--
-- == Trusted, pure, deterministic, total on well-formed input
--
-- This boundary is __inside the TCB__ (plan D1) and __pure__: it does __no IO,
-- no parsing, no filesystem access__. The caller (@app\/Main.hs@, Task A1c) does
-- file IO and co-located policy resolution and hands these functions
-- already-parsed values. Keeping this boundary pure keeps M4b a two-way door: a
-- machine producer can build a 'Program' in memory and reuse this exact
-- lowering (plan A1 "D1 ripple").
--
-- Premise resolution is a total function on well-formed input (plan D3): the
-- declared leaf+arg set is finite and @≡@ is decidable, so "the declared
-- conclusions @≡ Apᵢ·θ@" is computable — __exactly one__ ⇒ that sub-term,
-- __zero__ ⇒ 'UnresolvedPremise', __≥2__ ⇒ 'AmbiguousPremise'. No search, no
-- backtracking.
--
-- == Assurance
--
-- Strict /rules/ pass through into 'unitRules' as policy declarations.
-- Support-term assurance (lara-syntax@0.2, grammar App. A.1) is lowered
-- verbatim from the surface; the elaborator performs no mode or certifier
-- check — R7/R13 at @checkUnit@ are the single enforcement point.
module Lara.Elaborate
  ( -- * Caller-supplied environment inputs
    Sigma (..)
  , emptySigma
  , defeasibleSuiteSigma
  , TheoryRegistry (..)
  , emptyRegistry
  , registryOf
    -- * Elaboration errors (located-ish: they name the arg/rule/leaf/claim)
  , ElabError (..)
  , elabErrorMessage
    -- * Safe source boundary
  , PreparedSource (..)
  , SourceCheckInput
  , SourceInvalid (..)
  , renderSourceInvalid
  , prepareSource
  , SourceResult
  , runSourceCheck
  , sourceResultVerdict
  , sourceResultAudit
  , sourceResultDiagnostics
  , sourceResultLocatedRejection
  , sourceResultCheckedArgIds
  , sourceResultCheckInput
  ) where

import Data.Bifunctor (first)
import Data.List (sort)
import qualified Data.Set as Set

import Lara.AST
import Lara.Admission.Internal
  ( AdmissionAudit
  , admissionAuditHasPolicyQuarantine
  , AdmissionRejection
  , buildAdmissionAudit
  , firstAdmissionRejection
  , policyQuarantineSeed
  , validateAdmissionKeys
  )
import Lara.Blocked (Prune, pruneChecked, pruneWithPolicySeed)
import Lara.Check (fullConfig)
import Lara.Diagnostics (LocatedRejection)
import Lara.Driver.Internal (runCheckReported)
import Lara.Elaborate.Internal
  ( ElabError (..)
  , Sigma (..)
  , TheoryRegistry (..)
  , defeasibleSuiteSigma
  , elabErrorMessage
  , elaborate
  , emptyRegistry
  , emptySigma
  , registryOf
  )
import Lara.Replay
  ( CheckInput
  , CoreVersion (..)
  , ReplayError
  , mkCheckInput
  , mkReplayId
  , replayErrorMessage
  )
import Lara.Wire (Verdict)

-- ---------------------------------------------------------------------------
-- Safe source boundary
-- ---------------------------------------------------------------------------

-- | All source invalidity that precedes an R8 decision.  Elaboration and replay
-- constructors are retained as payloads so every old boundary failure has one
-- exhaustive source-level mapping.
data SourceInvalid
  = DuplicateAdmissionKey LeafKind Provenance
  | DuplicateSourceLeafId LeafId
  | SourceElaborationError ElabError
  | SourceReplayError ReplayError
  deriving (Eq, Show)

renderSourceInvalid :: SourceInvalid -> String
renderSourceInvalid invalid = case invalid of
  DuplicateAdmissionKey kind provenance ->
    "duplicate admission key (" ++ sourceKindText kind ++ ", "
      ++ sourceProvenanceText provenance ++ ")"
  DuplicateSourceLeafId (LeafId leaf) -> "duplicate leaf id '" ++ leaf ++ "'"
  SourceElaborationError err -> elabErrorMessage err
  SourceReplayError err -> replayErrorMessage err

-- | A successfully validated source is either stopped at the first exact R8
-- row or accepted as an opaque, replay-bound carrier.
data PreparedSource
  = SourceRejected AdmissionRejection
  | SourceAccepted SourceCheckInput

-- | The constructor is hidden.  Program, policy, fully elaborated declared
-- unit, explicit policy seed, final one-pass prune, audit, and replay identity
-- travel together, so a presentation caller cannot forge independently paired
-- halves.
data SourceCheckInput = SourceCheckInput
  Program
  Policy
  Unit
  [LeafId]
  Prune
  AdmissionAudit
  CheckInput

-- | Public source result.  Diagnostics and the located rejection are produced by
-- the same declared input and prune that produced the verdict; callers observe
-- verdict, audit, and location through total projections.
data SourceResult = SourceResult
  Verdict
  AdmissionAudit
  [String]
  (Maybe LocatedRejection)
  [ArgId]
  CheckInput

sourceResultVerdict :: SourceResult -> Verdict
sourceResultVerdict (SourceResult verdict _ _ _ _ _) = verdict

sourceResultAudit :: SourceResult -> AdmissionAudit
sourceResultAudit (SourceResult _ audit _ _ _ _) = audit

-- | The @stderr@ lines this result's rejection warrants, in the raw driver's
-- established precedence: a replay-preflight R13
-- ('Lara.Replay.replayFailureMessage'), an escalated group-conflict R9
-- ('Lara.Driver.groupConflictMessage'), or a checker-side R13
-- ('Lara.Driver.backendRejectionMessage' — the registered backend replayed the
-- certificate and refused it, and this carries the reason it gave).
--
-- Empty on acceptance, and empty for a rejection whose class already says what
-- went wrong; those carry their location in 'sourceResultLocatedRejection'
-- instead.  All of it comes from the same single pass that produced the
-- verdict, so a line here can never explain a rejection this result did not
-- make.
sourceResultDiagnostics :: SourceResult -> [String]
sourceResultDiagnostics (SourceResult _ _ diagnostics _ _ _) = diagnostics

-- | The located rejection that produced this result's verdict, from the /same/
-- decision path ("Lara.Driver.Internal".@runCheckReported@): its class, failing
-- stage, and offending constituent.  'Nothing' exactly on acceptance.
--
-- Without this projection a policy-pruned rejection would be renderable only
-- through 'sourceResultDiagnostics', which stays empty for the ordinary checker
-- rejections — every class but a backend-reason R13 carries its location here
-- rather than in a message line — so an R1 on a pruned source would print an
-- empty diagnostic.
sourceResultLocatedRejection :: SourceResult -> Maybe LocatedRejection
sourceResultLocatedRejection (SourceResult _ _ _ located _ _) = located

-- | The argument ids of the __checked__ (post-prune) program, in the order the
-- checker indexed them.  A 'LocatedRejection' constituent names arguments by
-- that index, so a renderer must resolve names against this list and not
-- against the declared one: indexing the declared arguments would misattribute
-- every constituent after a pruned argument.  Ids alone are exported — the
-- checked 'Unit' is deliberately not, so a caller still cannot rebuild a
-- policy-pruned envelope and re-run it without the blocked-status overlay.
sourceResultCheckedArgIds :: SourceResult -> [ArgId]
sourceResultCheckedArgIds (SourceResult _ _ _ _ argIds _) = argIds

-- | The validated raw core envelope bound into this source result, unless
-- policy admission removed source material. Duplicate-group quarantine is
-- already represented in @lara-core\@0.1@ and the raw checker performs that
-- same prune, so a group-only audit remains exportable. Policy pruning and its
-- blocked-status overlay are not encodable; legacy artifact consumers must
-- fail closed rather than recompute the declared envelope through
-- 'Lara.Driver.runCheck'.
sourceResultCheckInput :: SourceResult -> Either AdmissionAudit CheckInput
sourceResultCheckInput (SourceResult _ audit _ _ _ checkInput)
  | admissionAuditHasPolicyQuarantine audit = Left audit
  | otherwise = Right checkInput

-- | Validate and lower one presentation source.  Structural elaboration sees
-- every declared leaf; admission is considered only after elaboration and
-- replay identity construction have succeeded.
--
-- @
-- identity/keys/leaf ids -> elaborate(all leaves) -> replay identity -> R8
--                         -> seed union -> one prune -> opaque source input
-- @
prepareSource :: Sigma -> Program -> Policy -> Either SourceInvalid PreparedSource
prepareSource sigma program policy = do
  if programPolicy program /= policyId policy
    then Left (SourceElaborationError (PolicyIdMismatch (programPolicy program) (policyId policy)))
    else Right ()
  case validateAdmissionKeys (policyAdmission policy) of
    Left (kind, provenance) -> Left (DuplicateAdmissionKey kind provenance)
    Right () -> Right ()
  let leaves = [leaf | DeclLeaf leaf <- programDecls program]
  case firstDuplicateLeafId leaves of
    Just leaf -> Left (DuplicateSourceLeafId leaf)
    Nothing -> Right ()
  declared <-
    first SourceElaborationError
      (elaborate sigma (registryOf policy) program policy)
  checkInput <- first SourceReplayError (sourceReplayInput program policy declared)
  case firstAdmissionRejection (policyAdmission policy) leaves of
    Just rejection -> Right (SourceRejected rejection)
    Nothing ->
      let policySeed = policyQuarantineSeed (policyAdmission policy) leaves
          finalPrune = pruneWithPolicySeed policySeed declared
          audit = buildAdmissionAudit finalPrune
       in Right
            ( SourceAccepted
                (SourceCheckInput program policy declared policySeed finalPrune audit checkInput)
            )

runSourceCheck :: SourceCheckInput -> SourceResult
runSourceCheck (SourceCheckInput _ _ _ _ finalPrune audit checkInput) =
  let (verdict, located, diagnostics) =
        runCheckReported fullConfig checkInput finalPrune
   in SourceResult
        verdict
        audit
        diagnostics
        located
        (map fst (unitArgs (pruneChecked finalPrune)))
        checkInput

sourceReplayInput :: Program -> Policy -> Unit -> Either ReplayError CheckInput
sourceReplayInput program policy declared = do
  replayId <-
    mkReplayId
      LaraCoreV01
      (policyId policy)
      (programBackends program)
      (sort (map fst (policyTheories policy)))
      (programDigest program)
  mkCheckInput replayId declared

firstDuplicateLeafId :: [Leaf] -> Maybe LeafId
firstDuplicateLeafId = go Set.empty
  where
    go _ [] = Nothing
    go seen (leaf : leaves)
      | Set.member (leafId leaf) seen = Just (leafId leaf)
      | otherwise = go (Set.insert (leafId leaf) seen) leaves

sourceKindText :: LeafKind -> String
sourceKindText kind = case kind of
  Observed -> "observed"
  Attested -> "attested"
  Assumed -> "assumed"
  Certified -> "certified"

sourceProvenanceText :: Provenance -> String
sourceProvenanceText provenance = case provenance of
  User -> "user"
  AiExecuted -> "ai-executed"
  Checker name version -> "checker(" ++ name ++ ", " ++ version ++ ")"
