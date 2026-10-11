/-
Worked P5 impact fixtures (issue #22, plan P5).

Every fixture runs the **real** checked-source pipeline: authoritative
`Surface.Input`s through `Lara.Process.Source.checkSource`, compared by the
repaired `Lara.Process.Impact` layer (`impactResult`, `endpointReport`,
`impactCarrier`/`impactNodeDiff`/`impactEdgeDiff`, `impactReads`,
`impactCertificate`/`verifyImpact`). Nothing is hand-built: each pinned equation
below is the kernel value of the executable definition on the fixture, and each
comparison-record equation is the **one** equation a fixture binds, whose
changed/unchanged partition and transition are then projections of it.

The fixtures, in the acceptance order:

1. `quarantine_*` — the *same* declarations under one policy that differs by a
   single admission row (`blockedInput` is a record update of `liveInput`, so
   declarations, program and replay identity are shared by construction). The
   quarantine prunes the extra attacker, so the public tag moves
   `published` → `evidenceBlocked` while the **grounded** four-state answer the
   tag wraps stays `defeated` at both endpoints.
2. `blockedConditional_*` — both endpoints `evidenceBlocked`, with *different*
   retained conditional labels (`defeated` vs `justified`): the query is changed
   although the outer tags agree, and the conditional diagnostic is retained
   inside the `evidenceBlocked` constructor.
3. `normalization_*` — the numeric query `t(1)`: an argument whose conclusion is
   written `t(01)` joins the queried support because the resolver compares
   *normalized* atoms. The displayed claim declaration and the queried atom are
   the same terms and the witness occurrence is untouched, yet support
   membership grows and a certificate that ignores the recorded normalizing
   membership read is rejected (`.falseReadEvidence`).
4. `freshAttacker_*` (a new attacker reaching the old support) and
   `discharge_*` (an attacker undermining the leaf inside a shared discharge
   subterm, so the closure edges land on the wrapper). `backendReads_*` states
   the read-layer reason a backend dependency change is captured at all: the
   backend theory/digest/certificate-input keys are whole-input bound, and any
   two endpoints agreeing on the recorded `wholeInput` read agree on them.
5. `transition_*` / `rejectedEndpoint_*` — rejected-to-accepted,
   accepted-to-rejected and rejected-to-rejected as first-class outcomes: the
   per-endpoint report carries the exact `SourceRejection` payload, a rejected
   endpoint contributes `none` (never an invented status), and each honest mixed
   certificate still verifies.
6. `sibling_*` — the existing unchanged-status/different-entitlement and
   failed-sibling distinctions: the graph and the public status agree while the
   guarantee changes and the strict audit fails, so
   `no_entitlement_from_public_status` transports no entitlement.
7. `certLB_*` / `mut*` — one honest certificate verifies (`verifyImpact =
   .verified`, `verifyImpactBool = true`, and all eight checks true), and mutating
   each certificate field class in turn (a snapshot, an identity, the transition,
   a row, the changed/unchanged partition, the query list, a node map, the
   locality evidence, a read value, a conditional status) returns the matching
   closed fault. The fault results are closed kernel evaluations of `verifyImpact`
   / `firstFault` on each closed mutant - they carry no premises at all, so no
   desired status equality is assumed.
8. `*_partition` — the exact changed/unchanged query partitions and their
   lengths for every pair, never a bare boolean.

**Read-footprint honesty.** The audit-phase material keys (including the backend
ones) are whole-input bound in the repaired module: this file records that as
`backendReads_*` instead of claiming a smaller footprint, and the individually
resolved grounded/run-level keys are the ones the module's own coverage theorems
name (`impactReads_covers_status`). No desired status or fault is assumed.

**Reduction discipline.** Each fixture binds its comparison record with one
kernel equation (`*_result`) and each remaining value with one equation of its
own; the partition and transition assertions are syntactic projections of the
record equation. Every kernel evaluation here was measured before it was
written, and no proof step asks the unifier to unfold `checkSource` (which is
what explodes: `change`/`congrArg`/`simp` between differently-headed but
definitionally equal terms; `decide +kernel` on the closed proposition and
syntactic `rw` do not). The rejected fixtures use the minimal two-leaf
duplicate / policy-reject programs, where the nested diagnostic reduces in
fractions of a second.
-/

import Lara.Process.Impact
import Lara.Examples.ProcessSource
import Lara.Examples.ProcessSourceProfiles

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option pp.deepTerms false

namespace Lara.Examples.ProcessImpact

open Lara
open Lara.Process
open Lara.Process.Source
open Lara.Process.Impact
open Lara.Examples.ProcessSource

/-! ## Fixture vocabulary -/

/-- The fixed atom of the quarantine/attacker fixtures. -/
def qT : Atom := .atom "t" .nil

/-- The numeric query atom `t(1)` of the normalization fixture. -/
def qN : Atom := .atom "t" (.cons (.num "1") .nil)

/-- A defeasible rule with exactly one premise. -/
def rule (name premise conclusion : String) : Presentation.Rule :=
  { id := ⟨name⟩, params := [], mode := .defeasible, premises := [⟨premise, .nil⟩]
    premiseLabels := [], conclusion := ⟨conclusion, .nil⟩, allowTrusted := false
    certifiers := [], questions := [] }

/-- A defeasible rule with no premises and one mandatory question. -/
def ruleQ (name conclusion question answer : String) : Presentation.Rule :=
  { id := ⟨name⟩, params := [], mode := .defeasible, premises := []
    premiseLabels := [], conclusion := ⟨conclusion, .nil⟩, allowTrusted := false
    certifiers := [], questions := [⟨⟨question⟩, ⟨answer, .nil⟩, .mandatory⟩] }

/-- A user-observed leaf. -/
def leafM (name : String) (k : Presentation.LeafKind) (prop : Atom) : Presentation.Leaf :=
  ⟨⟨name⟩, prop, k, .user, [], none⟩

/-- The claim declaration of a fixed formal atom. -/
def claimFor (formal : Atom) : Presentation.Decl :=
  .claim ⟨⟨"claim"⟩, "Target", formal, ⟨"reader", "target interpretation", .reviewed⟩⟩

/-- An argument concluding by a rule instance over one premise leaf. -/
def argRule (name premise ruleId : String) (concl : Presentation.ArgConcl) : Presentation.Decl :=
  .arg ⟨⟨name⟩, concl, .inferTheta ⟨ruleId⟩ [⟨premise⟩] [] [] .none⟩

/-- An argument that is exactly a leaf occurrence. -/
def argLeaf (name leafId : String) (concl : Presentation.ArgConcl) : Presentation.Decl :=
  .arg ⟨⟨name⟩, concl, .explicitTheta (.leaf ⟨leafId⟩)⟩

/-- The fixture policy: exactly the predicates, rules, contraries and admission
rows a fixture uses, so each kernel-checked acceptance stays small. -/
def policyFor (preds : List Presentation.PredSig) (contraries : List Presentation.Contrary)
    (rules : List Presentation.Rule) (admission : List Presentation.AdmissionEntry) :
    Presentation.Policy :=
  { Lara.Examples.ProcessSource.ordinaryInput.policy with
    sigma := ⟨[], [], preds⟩
    rules
    contraries
    admission
    theories := [] }

/-- A source input over a fixture policy, with the replay identity the production
observer accepts and no capture. -/
def sourceFor (policy : Presentation.Policy) (decls : List Presentation.Decl) : SourceInput :=
  { surface :=
      { Lara.Examples.ProcessSource.ordinaryInput with
        policy
        program := { Lara.Examples.ProcessSource.ordinaryInput.program with
          policy := policy.id, backends := [], decls } }
    replay :=
      { core := ⟨Driver.coreVersionText⟩, policy := policy.id, backends := [], theories := []
        artifact := Lara.Examples.ProcessSource.ordinaryInput.program.digest }
    capture := none }

def pSeed : Presentation.PredSig := ⟨⟨"seed"⟩, []⟩
def pT : Presentation.PredSig := ⟨⟨"t"⟩, []⟩
def pS : Presentation.PredSig := ⟨⟨"s"⟩, []⟩
def pU : Presentation.PredSig := ⟨⟨"u"⟩, []⟩
def pExtra : Presentation.PredSig := ⟨⟨"extra"⟩, []⟩
def pTN : Presentation.PredSig := ⟨⟨"t"⟩, [.num]⟩
def pDseed : Presentation.PredSig := ⟨⟨"dseed"⟩, []⟩
def pAnswer : Presentation.PredSig := ⟨⟨"answer"⟩, []⟩

def cST : Presentation.Contrary := ⟨⟨"s", .nil⟩, ⟨"t", .nil⟩⟩
def cUS : Presentation.Contrary := ⟨⟨"u", .nil⟩, ⟨"s", .nil⟩⟩
def cSD : Presentation.Contrary := ⟨⟨"s", .nil⟩, ⟨"dseed", .nil⟩⟩

def rT : Presentation.Rule := rule "r-t" "seed" "t"
def rS : Presentation.Rule := rule "r-s" "seed" "s"
def rU : Presentation.Rule := rule "r-u" "seed" "u"
def rSx : Presentation.Rule := rule "r-sx" "extra" "s"
def rE : Presentation.Rule := rule "r-e" "dseed" "answer"
def rD : Presentation.Rule := ruleQ "r-d" "t" "qd" "answer"

def witnessD : Presentation.Decl := argRule "witness" "seed" "r-t" (.supportsClaim ⟨"claim"⟩)
def attackerD : Presentation.Decl :=
  argRule "attacker" "seed" "r-s" (.supportsDerived ⟨"attack-claim"⟩)
def defenderD : Presentation.Decl :=
  argRule "defender" "seed" "r-u" (.supportsDerived ⟨"defense-claim"⟩)
def extraD : Presentation.Decl :=
  argRule "extra" "extra" "r-sx" (.supportsDerived ⟨"extra-claim"⟩)

def seedLeaf : Presentation.Decl := .leaf (leafM "seed" .observed (.atom "seed" .nil))

/-- The extra leaf carries its own provenance class (`aiExecuted`), so one policy
row can quarantine it without touching the ordinary observed leaves. -/
def extraLeaf : Presentation.Decl :=
  .leaf ⟨⟨"extra"⟩, .atom "extra" .nil, .observed, .aiExecuted, [], none⟩

def atkAW : Presentation.Decl := .attack (.rebut ⟨"attacker"⟩ ⟨"witness"⟩)
def atkDA : Presentation.Decl := .attack (.rebut ⟨"defender"⟩ ⟨"attacker"⟩)
def atkEW : Presentation.Decl := .attack (.rebut ⟨"extra"⟩ ⟨"witness"⟩)

def liveDecls : List Presentation.Decl :=
  [seedLeaf, claimFor qT, witnessD, attackerD, extraLeaf, extraD, atkAW, atkEW]

def defendedDecls : List Presentation.Decl :=
  [seedLeaf, claimFor qT, witnessD, attackerD, defenderD, extraLeaf, extraD, atkAW, atkDA,
   atkEW]

/-! ### The quarantine pair (requirement 1) -/

def liveInput : SourceInput :=
  sourceFor (policyFor [pSeed, pT, pS, pExtra] [cST] [rT, rS, rSx] []) liveDecls

def quarantineRow : Presentation.AdmissionEntry := ((.observed, .aiExecuted), .quarantine)

/-- The quarantined source: a record update of `liveInput` in one admission row. -/
def blockedInput : SourceInput :=
  { liveInput with surface :=
      { liveInput.surface with policy :=
          { liveInput.surface.policy with admission := [quarantineRow] } } }

/-! ### The both-blocked pair (requirement 2) -/

/-- Under the same quarantine this adds a defender of the attacker, so the
attacker is defeated and the *conditional* label of the blocked result becomes
`justified` while the outer tag stays `evidenceBlocked`. -/
def defendedInput : SourceInput :=
  sourceFor (policyFor [pSeed, pT, pS, pU, pExtra] [cST, cUS] [rT, rS, rU, rSx] [quarantineRow])
    defendedDecls

/-! ### The normalization pair (requirement 3) -/

def l1 : Presentation.Leaf := leafM "w1" .observed (.atom "t" (.cons (.num "1") .nil))
def l2 : Presentation.Leaf := leafM "w2" .observed (.atom "t" (.cons (.num "01") .nil))
def witnessLeafD : Presentation.Decl := argLeaf "witness" "w1" (.supportsClaim ⟨"claim"⟩)
def aliasD : Presentation.Decl := argLeaf "alias" "w2" (.supportsClaim ⟨"claim"⟩)

def normSingleInput : SourceInput :=
  sourceFor (policyFor [pTN] [] [] []) [.leaf l1, claimFor qN, witnessLeafD]

def normAliasInput : SourceInput :=
  sourceFor (policyFor [pTN] [] [] []) [.leaf l1, .leaf l2, claimFor qN, witnessLeafD, aliasD]

/-! ### The attacker pair and the discharge pair (requirement 4) -/

def plainInput : SourceInput :=
  sourceFor (policyFor [pSeed, pT, pS] [cST] [rT, rS] []) [seedLeaf, claimFor qT, witnessD]

def attackedInput : SourceInput :=
  sourceFor (policyFor [pSeed, pT, pS] [cST] [rT, rS] [])
    [seedLeaf, claimFor qT, witnessD, attackerD, atkAW]

def dseedLeaf : Presentation.Decl := .leaf (leafM "dseed" .observed (.atom "dseed" .nil))
def dischargerD : Presentation.Decl :=
  argRule "discharger" "dseed" "r-e" (.supportsDerived ⟨"answer-claim"⟩)

/-- The wrapper's question `qd` is discharged by `discharger`, so the shared
discharge subterm is part of the query support's term. -/
def wrapperD : Presentation.Decl :=
  .arg ⟨⟨"wrapper"⟩, .supportsClaim ⟨"claim"⟩,
    .inferTheta ⟨"r-d"⟩ [] [⟨⟨"qd"⟩, ⟨"discharger"⟩⟩] [] .none⟩

def dischargeBaseDecls : List Presentation.Decl :=
  [seedLeaf, dseedLeaf, claimFor qT, dischargerD, wrapperD]

def dischargeAttackDecls : List Presentation.Decl :=
  dischargeBaseDecls ++
    [attackerD, .attack (.undermine ⟨"attacker"⟩ ⟨"wrapper"⟩ [.name "qd", .index 0])]

def dischargePolicy : Presentation.Policy :=
  policyFor [pSeed, pDseed, pAnswer, pT, pS] [cST, cSD] [rE, rD, rS] []

def dischargeBaseInput : SourceInput := sourceFor dischargePolicy dischargeBaseDecls
def dischargeAttackInput : SourceInput := sourceFor dischargePolicy dischargeAttackDecls

/-! ### The rejected programs (requirements 5 and 7)

Both rejected sources are minimal: a re-declared leaf (a duplicate id) and a
policy row rejecting the observed/user class. A rejected `checkSource` forces its
whole nested diagnostic, so the programs stay at two leaves. -/

def dupInput : SourceInput :=
  sourceFor (policyFor [pSeed, pT] [] [rT] []) [seedLeaf, seedLeaf, claimFor qT, witnessD]

def rejectInput : SourceInput :=
  sourceFor (policyFor [pSeed, pT] [] [rT] [((.observed, .user), .reject)])
    [seedLeaf, claimFor qT, witnessD]

/-! ## The real checked-source pipeline -/

theorem live_accepted : (checkSource liveInput).isOk = true := by decide +kernel

theorem blocked_accepted : (checkSource blockedInput).isOk = true := by decide +kernel

theorem defended_accepted : (checkSource defendedInput).isOk = true := by decide +kernel

theorem normSingle_accepted : (checkSource normSingleInput).isOk = true := by decide +kernel

theorem normAlias_accepted : (checkSource normAliasInput).isOk = true := by decide +kernel

theorem plain_accepted : (checkSource plainInput).isOk = true := by decide +kernel

theorem attacked_accepted : (checkSource attackedInput).isOk = true := by decide +kernel

theorem dischargeBase_accepted : (checkSource dischargeBaseInput).isOk = true := by
  decide +kernel

theorem dischargeAttack_accepted : (checkSource dischargeAttackInput).isOk = true := by
  decide +kernel

theorem dup_rejected : (checkSource dupInput).isOk = false := by decide +kernel

theorem reject_rejected : (checkSource rejectInput).isOk = false := by decide +kernel

/-- A successful check exposes an accepted observation. -/
theorem checkSource_eq_ok_of_isOk {input : SourceInput} (h : (checkSource input).isOk = true) :
    ∃ observation : AcceptedObservation input, checkSource input = .ok observation := by
  cases equation : checkSource input with
  | ok observation => exact ⟨observation, rfl⟩
  | error rejection => rw [equation] at h; exact absurd h Bool.false_ne_true

/-- A failed check exposes its exact rejection payload. -/
theorem checkSource_eq_error_of_not_isOk {input : SourceInput}
    (h : (checkSource input).isOk = false) :
    ∃ rejection : SourceRejection, checkSource input = .error rejection := by
  cases equation : checkSource input with
  | ok observation => rw [equation] at h; exact absurd h (fun hh => Bool.false_ne_true hh.symm)
  | error rejection => exact ⟨rejection, rfl⟩

/-! ## Public-status vocabulary

`BHL.ordinaryStatus` wraps the grounded four-state status of the compiled checked
framework (`Grounded.statusC` at `Compile.checkedAF` of the accepted
observation's program); `rowPayload` extracts that payload from the tag so the
fixtures can assert it as a four-state value. -/

/-- The four-state status a public tag wraps. -/
def rowPayload : Option Driver.PublicStatus → Option Grounded.Status
  | none => none
  | some (.published s) => some s
  | some (.evidenceBlocked s) => some s

/-- One query's row, written as data. -/
def qrow (q : Atom) (b a : Option Driver.PublicStatus) (c l : Bool) : QueryImpact :=
  { query := q, beforeStatus := b, afterStatus := a, changed := c, localityAccepted := l }

/-- The `published` tag at a four-state status. -/
def pub (s : Grounded.Status) : Option Driver.PublicStatus := some (.published s)

/-- The `evidenceBlocked` tag at a four-state status. -/
def evBlocked (s : Grounded.Status) : Option Driver.PublicStatus :=
  some (.evidenceBlocked s)

/-! ## The comparison record of each fixture, one equation each -/

theorem liveBlocked_result :
    impactResult liveInput blockedInput [qT] =
      { transition := .acceptedToAccepted
        rows := [qrow qT (pub .defeated) (evBlocked .defeated) true false]
        changed := [qT]
        unchanged := [] } := by decide +kernel

theorem blockedDefended_result :
    impactResult blockedInput defendedInput [qT] =
      { transition := .acceptedToAccepted
        rows := [qrow qT (evBlocked .defeated) (evBlocked .justified) true false]
        changed := [qT]
        unchanged := [] } := by decide +kernel

theorem norm_result :
    impactResult normSingleInput normAliasInput [qN] =
      { transition := .acceptedToAccepted
        rows := [qrow qN (pub .justified) (pub .justified) false false]
        changed := []
        unchanged := [qN] } := by decide +kernel

theorem attacker_result :
    impactResult plainInput attackedInput [qT] =
      { transition := .acceptedToAccepted
        rows := [qrow qT (pub .justified) (pub .defeated) true false]
        changed := [qT]
        unchanged := [] } := by decide +kernel

theorem discharge_result :
    impactResult dischargeBaseInput dischargeAttackInput [qT] =
      { transition := .acceptedToAccepted
        rows := [qrow qT (pub .justified) (pub .defeated) true false]
        changed := [qT]
        unchanged := [] } := by decide +kernel

theorem dupPlain_result :
    impactResult dupInput plainInput [qT] =
      { transition := .rejectedToAccepted
        rows := [qrow qT none (pub .justified) true false]
        changed := [qT]
        unchanged := [] } := by decide +kernel

theorem plainReject_result :
    impactResult plainInput rejectInput [qT] =
      { transition := .acceptedToRejected
        rows := [qrow qT (pub .justified) none true false]
        changed := [qT]
        unchanged := [] } := by decide +kernel

theorem rejectBlocked_result :
    impactResult rejectInput blockedInput [qT] =
      { transition := .rejectedToAccepted
        rows := [qrow qT none (evBlocked .defeated) true false]
        changed := [qT]
        unchanged := [] } := by decide +kernel

theorem rejectDup_result :
    impactResult rejectInput dupInput [qT] =
      { transition := .rejectedToRejected
        rows := [qrow qT none none false false]
        changed := []
        unchanged := [] } := by decide +kernel

/-! ## Requirement 1: the quarantine moves the public tag, not the grounded status -/

/-- The two sources differ in exactly one policy admission row: declarations,
program and replay identity are shared by construction. -/
theorem quarantine_only_admission :
    blockedInput.surface.program = liveInput.surface.program ∧
    liveInput.surface.policy.admission = [] ∧
    blockedInput.surface.policy.admission = [quarantineRow] ∧
    blockedInput.replay = liveInput.replay := ⟨rfl, rfl, rfl, rfl⟩

/-- Both endpoints are real checked sources. -/
theorem quarantine_checked :
    (checkSource liveInput).isOk = true ∧ (checkSource blockedInput).isOk = true :=
  ⟨live_accepted, blocked_accepted⟩

/-- The public tags: `published` before the quarantine row, `evidenceBlocked`
after it. -/
theorem quarantine_public_tags :
    statusRowOf liveInput qT = some (.published .defeated) ∧
    statusRowOf blockedInput qT = some (.evidenceBlocked .defeated) := by decide +kernel

/-- The tags really are different statuses. -/
theorem quarantine_public_tag_differs :
    statusRowOf liveInput qT ≠ statusRowOf blockedInput qT := by decide +kernel

/-- The quarantine is exactly what blocks the query. -/
theorem quarantine_blocking :
    blockedQueriesOf liveInput [qT] = [] ∧ blockedQueriesOf blockedInput [qT] = [qT] := by
  decide +kernel

/-- The **grounded** status the tag wraps is `defeated` at both endpoints: the
tag moved, the four-state answer did not. -/
theorem quarantine_grounded_status_unchanged :
    Grounded.statusC (compiledAF liveInput) (claimOfInput liveInput qT) = .defeated ∧
    Grounded.statusC (compiledAF blockedInput) (claimOfInput blockedInput qT) = .defeated := by
  decide +kernel

/-- The payloads the two tags carry, and that those payloads are the checked
grounded statuses above. -/
theorem quarantine_row_payloads :
    rowPayload (statusRowOf liveInput qT) = some .defeated ∧
    rowPayload (statusRowOf blockedInput qT) = some .defeated := by decide +kernel

/-! ## Requirement 2: both blocked, different retained conditional labels -/

/-- Both outer tags are `evidenceBlocked`, and the retained conditional labels
differ (`defeated` vs `justified`). -/
theorem blockedConditional_tags :
    statusRowOf blockedInput qT = some (.evidenceBlocked .defeated) ∧
    statusRowOf defendedInput qT = some (.evidenceBlocked .justified) := by decide +kernel

/-- The retained conditional diagnostics, read as the wrapped payloads. -/
theorem blockedConditional_payloads :
    rowPayload (statusRowOf blockedInput qT) = some .defeated ∧
    rowPayload (statusRowOf defendedInput qT) = some .justified := by decide +kernel

/-- The outer constructors agree while the statuses differ: the conditional
diagnostic is retained inside `evidenceBlocked` and never projected away. -/
theorem blockedConditional_tags_differ :
    statusRowOf blockedInput qT ≠ statusRowOf defendedInput qT := by decide +kernel

/-- Requirement 2 at the row level: the queried row is counted changed, and its
two endpoint statuses are the two *different* retained conditional labels under
the same `evidenceBlocked` outer tag. -/
theorem blockedConditional_changed_partition :
    (queryImpacts blockedInput defendedInput [qT]).map (fun r => r.changed) = [true] ∧
    (queryImpacts blockedInput defendedInput [qT]).map (fun r => r.beforeStatus) =
      [evBlocked .defeated] ∧
    (queryImpacts blockedInput defendedInput [qT]).map (fun r => r.afterStatus) =
      [evBlocked .justified] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The module's retention lemma at the two conditional labels: equal outer
tags, different wrapped statuses. -/
theorem blockedConditional_outer_tags_agree :
    Driver.PublicStatus.evidenceBlocked Grounded.Status.defeated ≠
      Driver.PublicStatus.evidenceBlocked Grounded.Status.justified :=
  evidenceBlocked_conditional_changed (by decide +kernel)

/-- The retained diagnostic is recorded as a decision. -/
theorem blockedConditional_diagnostic_recorded :
    decide (Driver.PublicStatus.evidenceBlocked Grounded.Status.defeated ≠
      Driver.PublicStatus.evidenceBlocked Grounded.Status.justified) = true := by
  decide +kernel

/-! ## Requirement 3: normalization changes support membership -/

/-- The alias conclusion is written `t(01)` while the query is `t(1)`: the raw
texts differ, and the trusted numeral normalizer identifies them. -/
theorem normalization_alias_text :
    l1.prop = qN ∧ l2.prop ≠ qN ∧ Lara.equiv Lara.canonNum l2.prop qN :=
  ⟨rfl, by decide +kernel, by decide +kernel⟩

/-- The displayed declaration material is shared: `claimFor qN` and the witness
occurrence `witnessLeafD` are the same terms in both sources, and the alias
fixture adds exactly one leaf and its argument. -/
theorem normalization_declarations :
    normSingleInput.surface.program.decls = [.leaf l1, claimFor qN, witnessLeafD] ∧
    normAliasInput.surface.program.decls =
      [.leaf l1, .leaf l2, claimFor qN, witnessLeafD, aliasD] := by decide +kernel

/-- The queried support membership *grows* through the normalizing resolver. -/
theorem normalization_support_membership :
    supportsOf normSingleInput qN = [⟨"witness"⟩] ∧
    supportsOf normAliasInput qN = [⟨"witness"⟩, ⟨"alias"⟩] := by decide +kernel

/-- The alias membership read of the after endpoint, exactly as recorded. -/
def aliasRead : Side × ReadKey × ReadVal :=
  (Side.after, ReadKey.supportMember qN 1,
    inputReading normAliasInput [qN] (ReadKey.supportMember qN 1))

/-- The recorded reads carry the normalizing alias membership in the after
endpoint (node `1` is the alias of the second support). -/
theorem normalization_alias_read_recorded :
    aliasRead ∈ impactReads normSingleInput normAliasInput [qN] := by decide +kernel

/-- The recorded value of that read is exactly `true` on the membership. -/
theorem normalization_alias_read_value : aliasRead.2.2 = ReadVal.bool true := by
  decide +kernel

/-- Recorded reads are functional in `(side, key)`: the module's determinacy
property, restated at this file's read sets. -/
theorem reads_functional {bi ai : SourceInput} {queries : List Atom} {s : Side} {k : ReadKey}
    {v v' : ReadVal} (h : (s, k, v) ∈ impactReads bi ai queries)
    (h' : (s, k, v') ∈ impactReads bi ai queries) : v = v' :=
  impactReads_functional h h'

/-- The same pair's honest certificate verifies. -/
theorem normalization_honest_verified :
    verifyImpact (impactCertificate normSingleInput normAliasInput [qN]) = .verified :=
  impactCertificate_verified _ _ _

/-- The certificate that ignores the normalizing alias membership read. -/
def normalizationIgnoringCert : ImpactCertificate :=
  { impactCertificate normSingleInput normAliasInput [qN] with
    reads := (impactCertificate normSingleInput normAliasInput [qN]).reads.filter
      (fun entry => entry ≠ aliasRead) }

/-- The recorded read set of the ignoring certificate is false: it drops the
alias membership read. -/
theorem normalization_readsOk_false : readsOk normalizationIgnoringCert = false := by
  decide +kernel

/-- That certificate is rejected. The fault is the ignored read, not a malformed
claim: the honest certificate over the same pair verifies
(`normalization_honest_verified`). -/
theorem normalization_ignoring_alias_rejected :
    verifyImpact normalizationIgnoringCert = .invalidCertificate .falseReadEvidence := by
  decide +kernel

/-- The verifier's first fault for the ignoring certificate. -/
theorem normalization_ignoring_alias_fault :
    firstFault normalizationIgnoringCert = some .falseReadEvidence := by decide +kernel

/-! ## Requirement 4: a fresh attacker and a discharge dependency -/

/-- The fresh attacker reaches the old support: both tags stay `published`, and
the support moves `justified` → `defeated`. -/
theorem freshAttacker_tags :
    statusRowOf plainInput qT = some (.published .justified) ∧
    statusRowOf attackedInput qT = some (.published .defeated) := by decide +kernel

/-- The difference the fresh attacker makes is one new node and its edge into the
support. -/
theorem freshAttacker_graph :
    impactCarrier plainInput attackedInput = [⟨"witness"⟩, ⟨"attacker"⟩] ∧
    impactNodeDiff plainInput attackedInput = [1] ∧
    impactEdgeDiff plainInput attackedInput = [(1, 0)] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The discharge dependency changes: the attacker undermines the leaf inside the
wrapper's shared discharge subterm, so the closure edges land on both the
discharger and the wrapper. -/
theorem discharge_dependency_changes :
    statusRowOf dischargeBaseInput qT = some (.published .justified) ∧
    statusRowOf dischargeAttackInput qT = some (.published .defeated) ∧
    impactCarrier dischargeBaseInput dischargeAttackInput =
      [⟨"discharger"⟩, ⟨"wrapper"⟩, ⟨"attacker"⟩] ∧
    impactEdgeDiff dischargeBaseInput dischargeAttackInput = [(2, 0), (2, 1)] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- A backend theory/digest/certificate-input read is a whole-input bound
material read: any two endpoints agreeing on the recorded `wholeInput` read agree
on it, so a backend dependency change is captured by the recorded whole input. -/
theorem backendReads_wholeInput_bound (bi ai : SourceInput) (queries : List Atom)
    (h : inputReading bi queries ReadKey.wholeInput =
      inputReading ai queries ReadKey.wholeInput)
    (key : ReadKey) (hkey : ReadKey.material key = true) :
    inputReading bi queries key = inputReading ai queries key :=
  materialReads_determined_by_wholeInput bi ai queries h key hkey

/-- The backend read classes are in the material (whole-input bound) inventory,
and the recorded read set of the quarantine pair carries both endpoints' whole
inputs. -/
theorem backendReads_recorded :
    ReadKey.material (ReadKey.backendTheory ⟨"b", 0⟩) = true ∧
    ReadKey.material (ReadKey.backendDigest ⟨"b", 0⟩) = true ∧
    ReadKey.material (ReadKey.certificateInput ⟨"b", 0⟩) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The recorded read set of the quarantine pair carries both endpoints' whole
inputs, so every material (including backend) read is determined by it. -/
theorem backendReads_wholeInput_recorded :
    (Side.before, ReadKey.wholeInput, ReadVal.source liveInput) ∈
      impactReads liveInput blockedInput [qT] ∧
    (Side.after, ReadKey.wholeInput, ReadVal.source blockedInput) ∈
      impactReads liveInput blockedInput [qT] := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-! ## Requirement 5: rejection transitions are first-class -/

theorem transition_rejected_to_accepted :
    (impactResult rejectInput blockedInput [qT]).transition = .rejectedToAccepted := by
  rw [rejectBlocked_result]

theorem transition_accepted_to_rejected :
    (impactResult plainInput rejectInput [qT]).transition = .acceptedToRejected := by
  rw [plainReject_result]

theorem transition_rejected_to_rejected :
    (impactResult rejectInput dupInput [qT]).transition = .rejectedToRejected := by
  rw [rejectDup_result]

/-- The three non-trivial transitions at `transitionOf` itself. -/
theorem transitionOf_rejected_to_accepted : transitionOf rejectInput blockedInput =
    .rejectedToAccepted := by decide +kernel

theorem transitionOf_accepted_to_rejected : transitionOf plainInput rejectInput =
    .acceptedToRejected := by decide +kernel

theorem transitionOf_rejected_to_rejected : transitionOf dupInput rejectInput =
    .rejectedToRejected := by decide +kernel

/-- A rejected endpoint contributes `none` and never an invented status; the
accepted side keeps its own status, so a mixed transition is a change. -/
theorem rejectedEndpoint_rows :
    queryImpacts dupInput plainInput [qT] = [qrow qT none (pub .justified) true false] ∧
    queryImpacts plainInput rejectInput [qT] = [qrow qT (pub .justified) none true false] ∧
    queryImpacts rejectInput dupInput [qT] = [qrow qT none none false false] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The exact rejection payloads the per-endpoint reports record. -/
theorem endpointReport_reject_rejection :
    (endpointReport rejectInput [qT]).rejection =
      some (.source (.source (.structural (.admissionRejected ⟨"seed"⟩)))) := by
  decide +kernel

theorem endpointReport_dup_rejection :
    (endpointReport dupInput [qT]).rejection =
      some (.source (.source (.structural (.duplicateLeafId ⟨"seed"⟩)))) := by
  decide +kernel

/-- Rejected endpoints record no acceptance; the accepted endpoint records no
rejection. -/
theorem endpointReport_rejected_not_accepted :
    (endpointReport rejectInput [qT]).accepted = false ∧
    (endpointReport dupInput [qT]).accepted = false ∧
    (endpointReport plainInput [qT]).accepted = true ∧
    (endpointReport plainInput [qT]).rejection = none := by decide +kernel

/-- A mixed transition records no compiled graph difference and an empty carrier
when both endpoints are rejected; the accepted endpoint of a mixed pair
contributes its own stable names. -/
theorem rejectedEndpoint_graphs :
    impactNodeDiff rejectInput dupInput = [] ∧
    impactEdgeDiff rejectInput dupInput = [] ∧
    impactCarrier rejectInput dupInput = [] ∧
    impactCarrier dupInput plainInput = [⟨"witness"⟩] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Every mixed certificate over these pairs still verifies: the rejection is an
outcome of the comparison, not a refusal to compare. -/
theorem rejectedEndpoint_mixed_verified :
    verifyImpact (impactCertificate dupInput plainInput [qT]) = .verified ∧
    verifyImpact (impactCertificate plainInput rejectInput [qT]) = .verified ∧
    verifyImpact (impactCertificate rejectInput dupInput [qT]) = .verified ∧
    verifyImpact (impactCertificate rejectInput blockedInput [qT]) = .verified :=
  ⟨impactCertificate_verified _ _ _, impactCertificate_verified _ _ _,
   impactCertificate_verified _ _ _, impactCertificate_verified _ _ _⟩

/-! ## Requirement 6: public-status equality transports no entitlement -/

/-- The failed-sibling pair of the profile fixtures. -/
abbrev Sibling := Bool

/-- The public observable of the pair: the graph summary together with the
public-status summary. -/
def siblingPublic (b : Sibling) :
    Except SourceRejection
      ((List Nat × List (Nat × Nat)) × List (Atom × Driver.PublicStatus)) :=
  (if b then Lara.Examples.ProcessSourceProfiles.siblingRow.view
    else Lara.Examples.ProcessSourceProfiles.selectedRow.view).map (fun view =>
    (Lara.Examples.ProcessSourceProfiles.graphSummary view,
      Lara.Examples.ProcessSourceProfiles.statusSummary view))

/-- The pair's public status at the fixed claim, read off the row's
public-status summary. -/
def siblingStatus (b : Sibling) : Driver.PublicStatus :=
  match (if b then Lara.Examples.ProcessSourceProfiles.siblingRow.view
      else Lara.Examples.ProcessSourceProfiles.selectedRow.view).map
      Lara.Examples.ProcessSourceProfiles.statusSummary with
  | .ok (entry :: _) => entry.2
  | _ => .published .gap

/-- The sibling entitlement: the strict-profile warrant at the fixed claim. -/
def siblingEntitled (b : Sibling) : Prop :=
  warranted _ (if b then Lara.Examples.ProcessSourceProfiles.siblingRow
    else Lara.Examples.ProcessSourceProfiles.selectedRow)
    Lara.Examples.ProcessSourceProfiles.strict Lara.Examples.ProcessSourceProfiles.claim.claim
    ⟨0⟩ = true

/-- Graph and status summaries agree across the pair. -/
theorem sibling_public_equal : siblingPublic false = siblingPublic true :=
  Lara.Examples.ProcessSourceProfiles.failed_sibling_same_graph_status.1

/-- The pinned public status agrees across the pair. -/
theorem sibling_status_equal : siblingStatus false = siblingStatus true := by
  decide +kernel

/-- Entitlement differs: the selected completion warrants the claim, the failed
sibling does not. -/
theorem sibling_entitlement_differs :
    siblingEntitled false ∧ ¬ siblingEntitled true := by
  refine ⟨?_, ?_⟩
  · exact Lara.Examples.ProcessSourceProfiles.failed_sibling_changes_guarantee_warrant.2.2.1
  · intro h
    have hfalse :=
      Lara.Examples.ProcessSourceProfiles.failed_sibling_changes_guarantee_warrant.2.2.2.1
    have h' : warranted Lara.Examples.ProcessSourceProfiles.siblingContext
        Lara.Examples.ProcessSourceProfiles.siblingRow
        Lara.Examples.ProcessSourceProfiles.strict
        Lara.Examples.ProcessSourceProfiles.claim.claim ⟨0⟩ = true := h
    rw [hfalse] at h'
    exact Bool.false_ne_true h'

/-- The guarantee the two rows' witnesses achieve changes while the public status
is unchanged, and the audit of the sibling family fails. -/
theorem sibling_guarantee_changes :
    Lara.Examples.ProcessSourceProfiles.selectedRow.view.map (fun view =>
      view.witnesses.map (fun entry => entry.2.map (·.achieved))) =
      .ok [.ok (.fwer, 1 / 40)] ∧
    Lara.Examples.ProcessSourceProfiles.siblingRow.view.map (fun view =>
      view.witnesses.map (fun entry => entry.2.map (·.achieved))) =
      .ok [.error (.guarantee (.ledger .exceededBound))] ∧
    audit Lara.Examples.ProcessSourceProfiles.siblingChecked
      Lara.Examples.ProcessSourceProfiles.strict
      Lara.Examples.ProcessSourceProfiles.claim.claim ⟨0⟩ = false :=
  ⟨Lara.Examples.ProcessSourceProfiles.failed_sibling_changes_guarantee_warrant.1,
   Lara.Examples.ProcessSourceProfiles.failed_sibling_changes_guarantee_warrant.2.1,
   Lara.Examples.ProcessSourceProfiles.failed_sibling_changes_guarantee_warrant.2.2.2.2⟩

/-- **No entitlement is transported from public-status equality.** -/
theorem sibling_no_entitlement_transport :
    ¬ (∀ x y, siblingStatus x = siblingStatus y →
      (siblingEntitled x ↔ siblingEntitled y)) :=
  no_entitlement_from_public_status siblingStatus siblingEntitled
    ⟨false, true, sibling_status_equal, sibling_entitlement_differs.1,
     sibling_entitlement_differs.2⟩

/-- The recorded shape of the distinction: a pair with equal graph, equal public
status and changed entitlement refutes entitlement transport. -/
theorem sibling_distinction_recorded :
    siblingPublic false = siblingPublic true ∧
      (∃ u v, siblingStatus u = siblingStatus v) ∧
      ¬ (∀ u v, siblingStatus u = siblingStatus v →
        (siblingEntitled u ↔ siblingEntitled v)) :=
  ⟨sibling_public_equal,
   impact_records_distinction siblingStatus siblingEntitled false true sibling_status_equal
     sibling_entitlement_differs.1 sibling_entitlement_differs.2⟩

/-- The distinction as an `EntitlementDistinction` record: graph same, public
status same, entitlement changed. -/
def siblingDistinction : EntitlementDistinction Sibling :=
  { before := false
    after := true
    graphSame := siblingPublic false = siblingPublic true
    publicStatusSame := siblingStatus false = siblingStatus true
    auditCountChanged := siblingEntitled false ∧ ¬ siblingEntitled true }

theorem siblingDistinction_holds :
    siblingDistinction.graphSame ∧ siblingDistinction.publicStatusSame ∧
      siblingDistinction.auditCountChanged :=
  ⟨sibling_public_equal, sibling_status_equal, sibling_entitlement_differs⟩

/-! ## Requirement 7: certificate verification and its closed faults -/

/-- The honest certificate of the quarantine pair. -/
def certLB : ImpactCertificate := impactCertificate liveInput blockedInput [qT]

/-- A snapshot that is not the empty capture-less snapshot of the fixtures. -/
def probeSnapshot : Evidence.Snapshot := [(⟨"probe"⟩, .error "probe")]

/-- A replay identity that differs from the fixture identity in its core. -/
def probeIdentity : Source.ReplayIdentity := { liveInput.replay with core := ⟨"probe-core"⟩ }

/-- **The honest certificate verifies**, in both closed and Boolean form. -/
theorem certLB_verified : verifyImpact certLB = .verified :=
  impactCertificate_verified liveInput blockedInput [qT]

theorem certLB_verified_bool : verifyImpactBool certLB = true :=
  (verified_iff_verifyImpact_true certLB).mp certLB_verified

/-- The eight checks of the honest certificate all come out true. -/
theorem certLB_checks :
    snapshotOk certLB = true ∧ identityOk certLB = true ∧ outcomeOk certLB = true ∧
    rowsOk certLB = true ∧ supportOk certLB = true ∧ graphOk certLB = true ∧
    localityOk certLB = true ∧ readsOk certLB = true :=
  verifyImpact_verified_fields certLB certLB_verified

/-! ### The ten field-class mutations -/

/-- A mutated snapshot. -/
def mutSnapshot : ImpactCertificate := { certLB with beforeSnapshot := probeSnapshot }

/-- A mutated replay identity. -/
def mutIdentity : ImpactCertificate := { certLB with beforeIdentity := probeIdentity }

/-- A mutated transition. -/
def mutTransition : ImpactCertificate := { certLB with transition := .rejectedToRejected }

/-- A mutated row (its `changed` flag). -/
def mutRow : ImpactCertificate :=
  { certLB with rows := certLB.rows.map (fun r => { r with changed := !r.changed }) }

/-- A mutated support partition: the `changed` map is emptied while the rows stay
put, so only `supportOk` fails. -/
def mutSupports : ImpactCertificate := { certLB with changed := [] }

/-- A mutated query list. -/
def mutQuery : ImpactCertificate := { certLB with queries := [] }

/-- A mutated node map (the comparison carrier). -/
def mutNode : ImpactCertificate := { certLB with carrier := [] }

/-- A mutated locality-evidence row. -/
def mutLocality : ImpactCertificate := { certLB with locality := [] }

/-- A mutated read value: the compiled-carrier key is re-recorded as a boolean,
which no endpoint ever records for it. -/
def mutRead : ImpactCertificate :=
  { certLB with reads := insert (Side.before, ReadKey.compiledCarrier, ReadVal.bool true) certLB.reads }

/-- A mutated conditional status: the outer `evidenceBlocked` tag stays, the
retained conditional label becomes `justified`. -/
def mutConditional : ImpactCertificate :=
  { certLB with rows := certLB.rows.map (fun r => { r with afterStatus := evBlocked .justified }) }

theorem mutSnapshot_false : snapshotOk mutSnapshot = false := by decide +kernel

theorem mutIdentity_false : identityOk mutIdentity = false := by decide +kernel

theorem mutTransition_false : outcomeOk mutTransition = false := by decide +kernel

theorem mutRow_false : rowsOk mutRow = false := by decide +kernel

theorem mutSupports_false : supportOk mutSupports = false := by decide +kernel

theorem mutQuery_false : outcomeOk mutQuery = false := by decide +kernel

theorem mutNode_false : graphOk mutNode = false := by decide +kernel

theorem mutLocality_false : localityOk mutLocality = false := by decide +kernel

theorem mutConditional_false : rowsOk mutConditional = false := by decide +kernel

/-- The read-value mutation leaves the read set false: the compiled-carrier key
is already recorded with its list value, and re-recording it as a boolean makes
the recorded set fail its own comparison. -/
theorem mutRead_false : readsOk mutRead = false := by decide +kernel

/-! ### The closed fault each mutation yields

The verifier result and the fault identity are both the kernel value of the
executable definitions on each mutant: no desired status equality is a premise. -/

theorem mutSnapshot_verify :
    verifyImpact mutSnapshot = .invalidCertificate .mismatchedSnapshots := by decide +kernel

theorem mutSnapshot_fault : firstFault mutSnapshot = some .mismatchedSnapshots := by decide +kernel

theorem mutIdentity_verify :
    verifyImpact mutIdentity = .invalidCertificate .mismatchedIdentities := by decide +kernel

theorem mutIdentity_fault : firstFault mutIdentity = some .mismatchedIdentities := by decide +kernel

theorem mutTransition_verify :
    verifyImpact mutTransition = .invalidCertificate .outcomeMismatch := by decide +kernel

theorem mutTransition_fault : firstFault mutTransition = some .outcomeMismatch := by decide +kernel

theorem mutRow_verify :
    verifyImpact mutRow = .invalidCertificate .statusMismatch := by decide +kernel

theorem mutRow_fault : firstFault mutRow = some .statusMismatch := by decide +kernel

theorem mutSupports_verify :
    verifyImpact mutSupports = .invalidCertificate .invalidSupports := by decide +kernel

theorem mutSupports_fault : firstFault mutSupports = some .invalidSupports := by decide +kernel

theorem mutQuery_verify :
    verifyImpact mutQuery = .invalidCertificate .outcomeMismatch := by decide +kernel

theorem mutQuery_fault : firstFault mutQuery = some .outcomeMismatch := by decide +kernel

theorem mutNode_verify :
    verifyImpact mutNode = .invalidCertificate .invalidGraph := by decide +kernel

theorem mutNode_fault : firstFault mutNode = some .invalidGraph := by decide +kernel

theorem mutLocality_verify :
    verifyImpact mutLocality = .invalidCertificate .falseLocality := by decide +kernel

theorem mutLocality_fault : firstFault mutLocality = some .falseLocality := by decide +kernel

theorem mutRead_verify : verifyImpact mutRead = .invalidCertificate .falseReadEvidence := by
  decide +kernel

theorem mutRead_fault : firstFault mutRead = some .falseReadEvidence := by decide +kernel

theorem mutConditional_verify :
    verifyImpact mutConditional = .invalidCertificate .statusMismatch := by decide +kernel

theorem mutConditional_fault : firstFault mutConditional = some .statusMismatch := by decide +kernel

/-! ## Requirement 8: exact partitions and counts -/

theorem liveBlocked_partition :
    (impactResult liveInput blockedInput [qT]).changed = [qT] ∧
    (impactResult liveInput blockedInput [qT]).changed.length = 1 ∧
    (impactResult liveInput blockedInput [qT]).unchanged = [] ∧
    (impactResult liveInput blockedInput [qT]).unchanged.length = 0 := by
  rw [liveBlocked_result]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem blockedDefended_partition :
    (impactResult blockedInput defendedInput [qT]).changed = [qT] ∧
    (impactResult blockedInput defendedInput [qT]).changed.length = 1 ∧
    (impactResult blockedInput defendedInput [qT]).unchanged = [] ∧
    (impactResult blockedInput defendedInput [qT]).unchanged.length = 0 := by
  rw [blockedDefended_result]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem norm_partition :
    (impactResult normSingleInput normAliasInput [qN]).changed = [] ∧
    (impactResult normSingleInput normAliasInput [qN]).changed.length = 0 ∧
    (impactResult normSingleInput normAliasInput [qN]).unchanged = [qN] ∧
    (impactResult normSingleInput normAliasInput [qN]).unchanged.length = 1 := by
  rw [norm_result]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem attacker_partition :
    (impactResult plainInput attackedInput [qT]).changed = [qT] ∧
    (impactResult plainInput attackedInput [qT]).changed.length = 1 ∧
    (impactResult plainInput attackedInput [qT]).unchanged = [] ∧
    (impactResult plainInput attackedInput [qT]).unchanged.length = 0 := by
  rw [attacker_result]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem discharge_partition :
    (impactResult dischargeBaseInput dischargeAttackInput [qT]).changed = [qT] ∧
    (impactResult dischargeBaseInput dischargeAttackInput [qT]).changed.length = 1 ∧
    (impactResult dischargeBaseInput dischargeAttackInput [qT]).unchanged = [] ∧
    (impactResult dischargeBaseInput dischargeAttackInput [qT]).unchanged.length = 0 := by
  rw [discharge_result]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem dupPlain_partition :
    (impactResult dupInput plainInput [qT]).changed = [qT] ∧
    (impactResult dupInput plainInput [qT]).changed.length = 1 ∧
    (impactResult dupInput plainInput [qT]).unchanged = [] ∧
    (impactResult dupInput plainInput [qT]).unchanged.length = 0 := by
  rw [dupPlain_result]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem plainReject_partition :
    (impactResult plainInput rejectInput [qT]).changed = [qT] ∧
    (impactResult plainInput rejectInput [qT]).changed.length = 1 ∧
    (impactResult plainInput rejectInput [qT]).unchanged = [] ∧
    (impactResult plainInput rejectInput [qT]).unchanged.length = 0 := by
  rw [plainReject_result]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem rejectBlocked_partition :
    (impactResult rejectInput blockedInput [qT]).changed = [qT] ∧
    (impactResult rejectInput blockedInput [qT]).changed.length = 1 ∧
    (impactResult rejectInput blockedInput [qT]).unchanged = [] ∧
    (impactResult rejectInput blockedInput [qT]).unchanged.length = 0 := by
  rw [rejectBlocked_result]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Rejected-to-rejected leaves the query in **neither** partition: no status is
invented on either endpoint. -/
theorem rejectDup_partition :
    (impactResult rejectInput dupInput [qT]).changed = [] ∧
    (impactResult rejectInput dupInput [qT]).changed.length = 0 ∧
    (impactResult rejectInput dupInput [qT]).unchanged = [] ∧
    (impactResult rejectInput dupInput [qT]).unchanged.length = 0 := by
  rw [rejectDup_result]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Lara.Examples.ProcessImpact
