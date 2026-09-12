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
    TheoryRegistry (..)
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
  , sourceResultCertDeps
  , sourceResultVerdict
  , sourceResultAudit
  , sourceResultDiagnostics
  , sourceResultAuthorDiagnostics
  , sourceResultLocatedRejection
  , sourceResultCheckedArgIds
  , sourceResultCheckInput
  , preparedCheckInput
    -- * Surface provenance (plan D5)
  , GeneratedArg (..)
  , sourceResultGeneratedArgs
    -- * Premise-slot attribution (#130)
  , sourceResultSlotSources
  , sourceResultAuthoredSlots
  , slotMappingFor
    -- * Formula attribution (#148)
  , sourceResultAuthoredFormulas
  ) where

import Data.Bifunctor (first)
import Data.List (find, sort)
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
import Lara.Elaborate.FormulaNames
  ( AuthoredFormula
  , authoredFormulaMap
  , formulaMappingLines
  )
import Lara.Elaborate.SlotNames
  ( AuthoredSlot
  , authoredSlotMap
  , renderAuthoredSlots
  )
import Lara.Check (fullConfig)
import Lara.Diagnostics
  ( Constituent (..)
  , LocatedRejection (..)
  , Stage (..)
  )
import Lara.Driver.Internal (runCheckReported, slotMappingLines)
import Lara.Strict.Deps (CertDep)
import Lara.SupportTerm (SlotSource)
import Lara.Elaborate.Internal
  ( ElabError (..)
  , GeneratedArg (..)
  , TheoryRegistry (..)
  , elabErrorMessage
  , elaborateWithProvenance
  , emptyRegistry
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
-- unit, explicit policy seed, final one-pass prune, audit, replay identity, and
-- the @comparison@ expansion's surface breadcrumb travel together, so a
-- presentation caller cannot forge independently paired halves.
--
-- The breadcrumb rides __beside__ the 'Unit', in this carrier, exactly because
-- it must not reach it (plan D5): the elaborated 'Unit' is byte-identical with
-- and without it, and the @examples\/*\/example.core.sexp@ goldens are the
-- standing check.
data SourceCheckInput = SourceCheckInput
  Program
  Policy
  Unit
  [LeafId]
  Prune
  AdmissionAudit
  CheckInput
  [GeneratedArg]

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
  [GeneratedArg]
  [SlotSource]
  [(ArgId, [AuthoredSlot])]
  [AuthoredFormula]
  [(ArgId, [CertDep])]

sourceResultVerdict :: SourceResult -> Verdict
sourceResultVerdict (SourceResult verdict _ _ _ _ _ _ _ _ _ _) = verdict

sourceResultAudit :: SourceResult -> AdmissionAudit
sourceResultAudit (SourceResult _ audit _ _ _ _ _ _ _ _ _) = audit

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
sourceResultDiagnostics (SourceResult _ _ diagnostics _ _ _ _ _ _ _ _) = diagnostics

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
sourceResultLocatedRejection (SourceResult _ _ _ located _ _ _ _ _ _ _) = located

-- | The argument ids of the __checked__ (post-prune) program, in the order the
-- checker indexed them.  A 'LocatedRejection' constituent names arguments by
-- that index, so a renderer must resolve names against this list and not
-- against the declared one: indexing the declared arguments would misattribute
-- every constituent after a pruned argument.  Ids alone are exported — the
-- checked 'Unit' is deliberately not, so a caller still cannot rebuild a
-- policy-pruned envelope and re-run it without the blocked-status overlay.
sourceResultCheckedArgIds :: SourceResult -> [ArgId]
sourceResultCheckedArgIds (SourceResult _ _ _ _ argIds _ _ _ _ _ _) = argIds

-- | Every argument this source's @comparison@ blocks generated, tied back to
-- the block that minted it (plan D5).  Empty for a program that authors no
-- @comparison@ — which is every raw @.sexp@ input, and every @lara-syntax\@0.2@
-- program.
sourceResultGeneratedArgs :: SourceResult -> [GeneratedArg]
sourceResultGeneratedArgs (SourceResult _ _ _ _ _ _ generated _ _ _ _) = generated

-- | The __structural__ premise-slot mapping of a checker-side R13 (#130): what
-- the checked term put in each slot the refused certificate cites, read off the
-- same decision that produced the verdict
-- ("Lara.Driver.Internal".@backendRejectionSlots@). Empty for every other
-- outcome.
--
-- This is the reading a raw @.sexp@ input also gets. It is exported beside the
-- authored one so a caller can tell the two apart rather than parsing them back
-- out of a rendered line.
sourceResultSlotSources :: SourceResult -> [SlotSource]
sourceResultSlotSources (SourceResult _ _ _ _ _ _ _ slots _ _ _) = slots

-- | The __authored__ premise-slot spelling of every checked argument (#130),
-- keyed by argument id: the leaf, prior-argument, and premise-label names the
-- source actually used ("Lara.Elaborate.SlotNames").
--
-- Present for every checked argument, not only a rejected one, because it is a
-- property of the source rather than of the verdict. Empty for a program with
-- no rule-instance arguments — which is every raw @.sexp@ input, since a wire
-- program has no authored names to recover.
sourceResultAuthoredSlots :: SourceResult -> [(ArgId, [AuthoredSlot])]
sourceResultAuthoredSlots (SourceResult _ _ _ _ _ _ _ _ authored _ _) = authored

-- | The __authored__ spelling of every formula this source can name (#148):
-- the @lara-syntax\@0.10@ @(prop TEXT)@ annotations of its @nd\@1@ payloads,
-- and the propositions of its declared leaves, each paired with the opaque
-- 'Lara.Strict.ND.encodeAtomKey' framing a backend names it by
-- ("Lara.Elaborate.FormulaNames").
--
-- Present for every source, not only a rejected one, because it is a property
-- of the program rather than of the verdict. Empty for a raw @.sexp@ input,
-- which has no authored spellings to recover.
sourceResultAuthoredFormulas :: SourceResult -> [AuthoredFormula]
sourceResultAuthoredFormulas (SourceResult _ _ _ _ _ _ _ _ _ formulas _) = formulas

-- | The validated raw core envelope bound into this source result, unless
-- policy admission removed source material. Duplicate-group quarantine is
-- already represented in @lara-core\@0.1@ and the raw checker performs that
-- same prune, so a group-only audit remains exportable. Policy pruning and its
-- blocked-status overlay are not encodable; legacy artifact consumers must
-- fail closed rather than recompute the declared envelope through
-- 'Lara.Driver.runCheck'.
sourceResultCheckInput :: SourceResult -> Either AdmissionAudit CheckInput
sourceResultCheckInput (SourceResult _ audit _ _ _ checkInput _ _ _ _ _)
  | admissionAuditHasPolicyQuarantine audit = Left audit
  | otherwise = Right checkInput

-- | The same envelope, read off the prepared source __before__ it is checked,
-- under the same rule: exportable unless policy admission removed source
-- material. For a consumer that will run the raw checker on the envelope
-- itself (@lara pw@'s @lara@ world sources, \#327), checking here as well would
-- only compute a verdict nobody reads.
preparedCheckInput :: SourceCheckInput -> Either AdmissionAudit CheckInput
preparedCheckInput (SourceCheckInput _ _ _ _ _ audit checkInput _)
  | admissionAuditHasPolicyQuarantine audit = Left audit
  | otherwise = Right checkInput

-- | The certificate dependency report of the unit this source result accepted,
-- keyed by the checked unit's argument ids (\#204).
--
-- @[]@ on rejection. On acceptance the ids are exactly
-- 'sourceResultCheckedArgIds' — both read the same checked unit — so the report
-- and the argument list beside it index each other without a join.
--
-- This is the @.lara@ door's half of the report; the raw wire door reaches the
-- same pair through 'Lara.Driver.runCheckDeps'. The two differ only in which
-- prune produced the checked unit: this one carries the source-boundary prune
-- (policy admission included), the raw one the ordinary group-only prune. That
-- is the same asymmetry 'sourceResultCheckInput' already documents, and it is
-- why the source door cannot simply be routed through the raw entry point.
sourceResultCertDeps :: SourceResult -> [(ArgId, [CertDep])]
sourceResultCertDeps (SourceResult _ _ _ _ _ _ _ _ _ _ deps) = deps

-- | Validate and lower one presentation source.  Structural elaboration sees
-- every declared leaf; admission is considered only after elaboration and
-- replay identity construction have succeeded.
--
-- @
-- identity/keys/leaf ids -> elaborate(all leaves) -> replay identity -> R8
--                         -> seed union -> one prune -> opaque source input
-- @
prepareSource :: Program -> Policy -> Either SourceInvalid PreparedSource
prepareSource program policy = do
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
  (declared, generated) <-
    first SourceElaborationError
      (elaborateWithProvenance (registryOf policy) program policy)
  checkInput <- first SourceReplayError (sourceReplayInput program policy declared)
  case firstAdmissionRejection (policyAdmission policy) leaves of
    Just rejection -> Right (SourceRejected rejection)
    Nothing ->
      let policySeed = policyQuarantineSeed (policyAdmission policy) leaves
          finalPrune = pruneWithPolicySeed policySeed declared
          audit = buildAdmissionAudit finalPrune
       in Right
            ( SourceAccepted
                ( SourceCheckInput
                    program
                    policy
                    declared
                    policySeed
                    finalPrune
                    audit
                    checkInput
                    generated
                )
            )

runSourceCheck :: SourceCheckInput -> SourceResult
runSourceCheck (SourceCheckInput program policy declared _ finalPrune audit checkInput generated) =
  let checked = pruneChecked finalPrune
      (verdict, located, diagnostics, slots, deps) =
        runCheckReported fullConfig checkInput finalPrune
   in SourceResult
        verdict
        audit
        diagnostics
        located
        (map fst (unitArgs checked))
        checkInput
        generated
        slots
        (authoredSlotMap policy (unitArgs checked))
        -- Built from the __declared__ unit, not the checked one: a leaf a
        -- policy prune removed can still be named by a rejection reason, and
        -- an entry the reason never mentions costs nothing (#148).
        (authoredFormulaMap program declared)
        deps

-- ---------------------------------------------------------------------------
-- The author-facing layer (plan D5, eng review 2A)
-- ---------------------------------------------------------------------------

-- | The @stderr@ lines the __@.lara@ door__ prints: 'sourceResultDiagnostics'
-- with one surface-context line prepended when the rejected constituent is an
-- argument a @comparison@ block generated.
--
-- __Why this exists.__ A kernel diagnostic is worded in the kernel's
-- vocabulary. When @ord\@1@ refuses a certificate the @comparison@ form
-- generated, the author reads about premise slots they never wrote — the whole
-- point of the form is that slot indices are no longer authored (plan §1.1).
-- The kernel line is right and is byte-pinned; what was missing is the sentence
-- above it that says which authored block the machinery below came from, and
-- which of its fields to look at.
--
-- __What it is not.__ It is strictly additive framing: the kernel line follows
-- unchanged and in the same order, the verdict class, the exit code, and
-- @stdout@ are untouched, and nothing is added when there is no kernel line to
-- sit above. The raw @.sexp@ door does not call this — a wire program has no
-- surface, no @comparison@, and no breadcrumb — so its bytes are unchanged by
-- construction. 'sourceResultDiagnostics' also stays as it was, because
-- "Lara.ExpectedJson" pins its @messages@ field in every @expected.json@.
sourceResultAuthorDiagnostics :: SourceResult -> [String]
sourceResultAuthorDiagnostics result = case sourceResultDiagnostics result of
  [] -> []
  diagnostics ->
    surfaceContextLines result
      ++ diagnostics
      ++ slotLines result
      ++ formulaLines result diagnostics

-- | The authored spelling of every formula a rejection reason names (#148), in
-- the order the reason names them, under the slot mapping it sits beside.
--
-- __The gap this closes.__ @lara-syntax\@0.9@ removed hand-computed de Bruijn
-- indices from /authoring/ and @\@0.10@ removed the last out-of-band key from
-- the formula annotations. Neither reaches a /rejection/: a certificate that
-- lowers cleanly and is then refused at R13 is reported over the lowered image,
-- so the author reads @FAtom (AtomId \"1:A5:holds1:L1:2…\")@ for a formula they
-- wrote as @(prop \"holds(safety_invariant, D)\")@. That is the one point where
-- the named surface still leaks its lowered image, and it arrives exactly when
-- it is hardest to read.
--
-- __What is not done here.__ The @hyp i@ de Bruijn indices in the same reason
-- are __not__ mapped back to binder names. That index is relative to the local
-- binder context at the failure site inside the adapter, and the adapter
-- reports through a flat 'String' ('Lara.SupportTerm.ReplayRejected'), so no
-- sound recovery exists from outside it. Doing it properly means giving the
-- registered-backend seam a structured rejection — the one boundary the
-- @\@0.6@-@\@0.10@ arc kept frozen — and is tracked separately rather than
-- smuggled in here.
--
-- Strictly additive, like the slot lines it follows: the kernel line is
-- unchanged and in the same order, @stdout@, the verdict class and the exit
-- code are untouched, and 'sourceResultDiagnostics' — whose bytes
-- "Lara.ExpectedJson" pins in every @expected.json@ — is not this channel.
formulaLines :: SourceResult -> [String] -> [String]
formulaLines result diagnostics =
  formulaMappingLines (unlines diagnostics) (sourceResultAuthoredFormulas result)

-- | The premise-slot mapping under a checker-side R13's reason line (#130), in
-- the authored spelling where the source door has one.
--
-- __Why the mapping is worth printing at all.__ The backend's reason names a
-- @(prem i)@. Nothing else in the rejection says what @i@ /is/, so the reader
-- decodes it by hand against the policy declarations — for a numeric
-- certificate, an @nd\@1@ proof term, or a third-party artifact, every time.
--
-- __Why the source door prints a different one.__ The structural reading
-- ('Lara.Driver.slotMappingLines') is what the checked 'Unit' can say: leaf
-- ids, and the rule of an inline sub-derivation. The @.lara@ author wrote
-- names — leaves, prior arguments, and @lara-syntax\@0.8@ premise labels — and
-- a diagnosis in the kernel's vocabulary makes them translate. Where those
-- names survive ('Lara.Elaborate.SlotNames'), they are printed instead.
--
-- __Fallback, and why it is a fallback rather than a failure.__ The authored
-- map is keyed by argument id and only a located argument rejection resolves
-- one. When the rejection does not locate at an argument, or the located
-- argument has no recovered spelling, or the two readings disagree on how many
-- slots there are, the structural lines are printed unchanged: the mapping is
-- still true, it is just phrased in the kernel's vocabulary. Printing nothing
-- would be the one outcome worse than printing the indices the author already
-- had.
slotLines :: SourceResult -> [String]
slotLines result =
  slotMappingFor (sourceResultSlotSources result) (authoredForRejection result)

-- | Choose between the two readings of one rejection's slot block: the authored
-- spelling when it was recovered and the two readings agree on how many slots
-- there are, the structural spelling otherwise, and nothing at all when there
-- are no slots to explain.
--
-- Split out of 'slotLines' as a total function of the two readings because the
-- fallback is the arm that has to keep working. By construction the authored and
-- structural lists are built from the same premise list, so their lengths agree
-- and no artifact reaches the mismatch arm today; only a direct test can hold
-- the documented fallback in place if a later change to 'authoredSlotMap' or to
-- the backend's reported slots breaks that assumption.
slotMappingFor :: [SlotSource] -> Maybe [AuthoredSlot] -> [String]
slotMappingFor [] _ = []
slotMappingFor structural authored = case authored of
  Just as
    | length as == length structural -> renderAuthoredSlots as
  _ -> slotMappingLines structural

-- | The authored slot spelling of the argument this result's rejection located
-- at, when it located at one (#130).
--
-- Gated on 'StageSupport' + 'CArgument' for the same reason
-- 'surfaceContextLines' is: that pair is exactly the checker-side backend
-- rejection, the only class whose slots this explains.
authoredForRejection :: SourceResult -> Maybe [AuthoredSlot]
authoredForRejection result = case sourceResultLocatedRejection result of
  Just (LocatedRejection _ StageSupport (CArgument i))
    | Just aid <- nth i (sourceResultCheckedArgIds result) ->
        lookup aid (sourceResultAuthoredSlots result)
  _ -> Nothing
  where
    nth i xs
      | i < 0 = Nothing
      | otherwise = case drop i xs of
          x : _ -> Just x
          [] -> Nothing

-- | The surface-context line, or none.
--
-- Gated on 'StageSupport' + 'CArgument', which is exactly the checker-side
-- backend rejection ("Lara.Driver".@backendRejectionMessage@): its
-- 'Lara.Diagnostics.locate' arm is @PERejection (DLArgument i)@.  The other two
-- message-bearing rejections are excluded deliberately — a replay-preflight R13
-- indexes the /declared/ arguments rather than the checked ones, and an
-- escalated group conflict locates at a 'Lara.Diagnostics.CGroup', so neither
-- can be resolved against 'sourceResultCheckedArgIds'.
surfaceContextLines :: SourceResult -> [String]
surfaceContextLines result = case sourceResultLocatedRejection result of
  Just (LocatedRejection _ StageSupport (CArgument i))
    | Just aid <- nth i (sourceResultCheckedArgIds result)
    , Just crumb <- find ((== aid) . gaArgId) (sourceResultGeneratedArgs result) ->
        [renderGeneratedArg crumb]
  _ -> []
  where
    nth i xs
      | i < 0 = Nothing
      | otherwise = case drop i xs of
          x : _ -> Just x
          [] -> Nothing

-- | One line, in the vocabulary the author wrote: the block (named by its
-- @claims@ id, as every other @comparison@ diagnostic names it —
-- 'Lara.Elaborate.elabErrorMessage'), the argument it generated, and the three
-- fields that decided the arithmetic below.
renderGeneratedArg :: GeneratedArg -> String
renderGeneratedArg crumb =
  "lara: comparison claiming '"
    ++ claimName
    ++ "': argument '"
    ++ argName
    ++ "' was generated by that block from result = '"
    ++ resultName
    ++ "', baseline = '"
    ++ baselineName
    ++ "', on '"
    ++ measurandName
    ++ "'"
  where
    PropId claimName = gaClaimId crumb
    ArgId argName = gaArgId crumb
    LeafId resultName = gaResult crumb
    LeafId baselineName = gaBaseline crumb
    MeasurandId measurandName = gaMeasurand crumb

sourceReplayInput :: Program -> Policy -> Unit -> Either ReplayError CheckInput
sourceReplayInput program policy declared = do
  replayId <-
    mkReplayId
      LaraCoreV02
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
