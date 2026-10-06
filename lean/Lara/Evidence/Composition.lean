import Lara.Evidence.Admission
import Lara.Surface.Source
import Lara.Admission

namespace Lara.Evidence
open Lara Lara.Support Lara.Admission
open Lara.BlockedProgram Lara.Consistency

/-- Evidence adds a rejecting boundary, not a new prune. The continuation is
literally the existing ordinary policy/group pipeline on unchanged arguments. -/
def gate (snapshot : Snapshot) (policy : EvidencePolicy) (manifest : List ObjectMeta)
    (registry : Registry) (leaves : List Presentation.Leaf) (ordinary : α) :
    Except AdmissionError (List Judgment × α) := do
  let judgments ← admit snapshot policy manifest registry leaves
  .ok (judgments, ordinary)

theorem successful_gate_conservativity {α : Type} {snapshot : Snapshot} {policy : EvidencePolicy}
    {manifest : List ObjectMeta} {registry : Registry} {leaves : List Presentation.Leaf}
    {ordinary : α} {judgments : List Judgment} {output : α}
    (h : gate snapshot policy manifest registry leaves ordinary = .ok (judgments, output)) :
    output = ordinary ∧ Admitted snapshot policy manifest registry leaves judgments := by
  unfold gate at h
  cases he : admit snapshot policy manifest registry leaves with
  | error e => simp [he] at h
  | ok js =>
    simp [he] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, admit_iff.mp he⟩

/-- The same accepted ordinary admission supplies exact policy/group context.
Evidence success never admits a leaf quarantined by either ordinary boundary. -/
theorem package_checked_context_exact
    (snapshot : Snapshot) (evidencePolicy : EvidencePolicy) (manifest : List ObjectMeta)
    (registry : Registry) (sourceLeaves : List Presentation.Leaf) (judgments : List Judgment)
    (canon : String → String) (table : List AdmissionRow) (metas : List LeafMeta)
    (leaves : List (LeafId × Atom)) (argsRaw : List (String × SupportTerm))
    (rawAtts : List Lara.RawAttack.RawAttack) (groups : List Groups.DupGroup)
    (declared : AlignedAttacks argsRaw rawAtts)
    (sameLeaves : leaves = sourceLeaves.map (fun l => (⟨l.id.val⟩, l.prop)))
    (sameMetas : metas = sourceLeaves.map (fun l => ⟨⟨l.id.val⟩, l.kind, l.provenance⟩))
    (evidence : admit snapshot evidencePolicy manifest registry sourceLeaves = .ok judgments)
    (ordinary : evaluateAdmission canon table metas leaves argsRaw rawAtts groups declared = .accepted r) :
    Admitted snapshot evidencePolicy manifest registry sourceLeaves judgments ∧
      metadataLeafAligned metas leaves ∧
      r.prune.checkedLeaves.map (·.1) = checkedAdmittedIds canon table metas leaves groups ∧
      ∀ l, l ∈ r.prune.checkedLeaves.map (·.1) ↔
        l ∈ policyAdmittedIds table metas ∧ l ∉ Groups.quarantined canon leaves groups := by
  exact ⟨admit_iff.mp evidence,
    accepted_checked_context_exact canon table metas leaves argsRaw rawAtts groups declared ordinary⟩

theorem package_retained_gamma_agree
    (canon : String → String) (table : List AdmissionRow) (metas : List LeafMeta)
    (leaves : List (LeafId × Atom)) (argsRaw : List (String × SupportTerm))
    (rawAtts : List Lara.RawAttack.RawAttack) (groups : List Groups.DupGroup) (declaredResolved : List Lara.Attack.Attack) :
    let prune := buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved
    ∀ arg, prune.keep arg = true → ∀ leaf ∈ Support.leaves arg.2,
      buildGamma prune.checkedLeaves leaf = buildGamma leaves leaf :=
  prune_gamma_agree canon table metas leaves argsRaw rawAtts groups declaredResolved

/-- End-to-end source preservation uses an actual accepted source equation and
its derived Checks judgment. Complete nodes, typed holes, authored open roots,
and resolved attacks are the ordinary source/core ones, not empirical truth. -/
theorem package_source_preserves
    {env : Surface.Env canonNum} {input snapshot manifest registry output judgments}
    (h : Surface.sourceWithEvidence env input snapshot manifest registry = .ok (output, judgments)) :
    (∃ lowered, Surface.elaborateWithAudit env input = .ok lowered ∧
      Admitted snapshot input.policy.evidenceCheckers manifest registry
        (Surface.leafRecords lowered.declared.semanticProgram) judgments) ∧
    ∃ checked,
      Surface.elaborate env input = .ok output ∧
      Check.Unit.checkUnit output.gamma env.registry output.ground output.unit = .ok checked ∧
      checked.program.args = Check.completeArgs output.unit.policy.ruleLookup
        output.gamma env.registry output.unit.args ∧
      checked.program.holes = Check.holeArgs output.unit.policy.ruleLookup
        output.gamma env.registry output.unit.args ∧
      output.openQuestions.map Prod.fst = output.argIds ∧
      output.openQuestions.map Prod.snd = Surface.coreOpenQuestions output.unit ∧
      output.unit.atts = output.resolvedAttacks := by
  have hs := Surface.sourceWithEvidence_sound h
  exact ⟨hs.2, Surface.elaborate_preserves env input output hs.1⟩

theorem package_holes_iff
    {canon : String → String} {gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {ground unit accepted} (core : Check.Unit.checkUnit gamma reg ground unit = .ok accepted)
    {i : Nat} {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (hi : unit.args[i]? = some w)
    (hw : HasSupport canon unit.policy.ruleLookup gamma (certOkOf reg) w C O) :
    (∃ h ∈ accepted.holes, h.index = i) ↔ O ≠ [] :=
  (Check.Unit.checkUnit_sound core).holes_iff hi hw

theorem package_hole_reports_exact
    {canon : String → String} {gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {ground unit accepted} (core : Check.Unit.checkUnit gamma reg ground unit = .ok accepted)
    {hole : Compile.CheckedHole canon accepted.policy.ruleLookup gamma (certOkOf reg)}
    (hh : hole ∈ accepted.holes) {C : Atom} {O : List QuestionId}
    (hw : HasSupport canon unit.policy.ruleLookup gamma (certOkOf reg) hole.term C O) :
    unit.args[hole.index]? = some hole.term ∧ hole.conclusion = C ∧ hole.obligations = O :=
  (Check.Unit.checkUnit_sound core).hole_reports_exact hh hw

/-- Useful non-definitional composition: certification witnesses for every
source declaration (even unused or later quarantined ones) coexist with the
ordinary directed justified non-promotion theorem. The actual query membership,
unblocked exclusion, same ordinary admission and grounded premise are required. -/
theorem package_source_justified_nonpromotion
    (snapshot : Snapshot) (evidencePolicy : EvidencePolicy) (manifest : List ObjectMeta)
    (registry : Registry) (sourceLeaves : List Presentation.Leaf) (judgments : List Judgment)
    (reg : BackendRegistry canonNum) (policy : Lara.Policy.Policy)
    (table : List AdmissionRow) (argsRaw : List (String × SupportTerm))
    (rawAtts : List Lara.RawAttack.RawAttack) (groups : List Groups.DupGroup)
    (declared : AlignedAttacks argsRaw rawAtts) (queries : List Atom) (query : Atom)
    (sigma : Lara.Sigma.Sigma) (ground : List Atom)
    (evidence : admit snapshot evidencePolicy manifest registry sourceLeaves = .ok judgments)
    (ordinary : evaluateAdmission canonNum table
      (sourceLeaves.map (fun l => (⟨⟨l.id.val⟩, l.kind, l.provenance⟩ : LeafMeta)))
      (sourceLeaves.map (fun l => (⟨l.id.val⟩, l.prop))) argsRaw rawAtts groups declared = .accepted r)
    (accepted : Lara.Unit.CheckedUnit canonNum (buildGamma r.prune.checkedLeaves) (certOkOf reg))
    (core : Check.Unit.checkUnit (buildGamma r.prune.checkedLeaves) reg ground
      (⟨sigma, policy, r.prune.keptArgs.map (·.2), r.prune.keptAttacks⟩ : Lara.Unit) = .ok accepted)
    (member : query ∈ queries)
    (unblocked : query ∉ BlockedProgram.blockedQueries r.prune.keep (checkedDone accepted)
      (referenceLive r.prune.keep (checkedDone accepted) policy.ruleLookup
        (buildGamma (sourceLeaves.map (fun l => (⟨l.id.val⟩, l.prop)))) reg)
      argsRaw declared.resolved r.prune.keptAttacks
      (fun q => claimSupportFor accepted q) queries)
    (justified : Grounded.statusC (Compile.checkedAF accepted.program)
      (completeClaimFor accepted query) = .justified) :
    Admitted snapshot evidencePolicy manifest registry sourceLeaves judgments ∧
    Grounded.statusC
      (BlockedProgram.declaredAF argsRaw declared.resolved
        (retainedIndices (notHole policy.ruleLookup
          (buildGamma (sourceLeaves.map (fun l => (⟨l.id.val⟩, l.prop)))) reg) argsRaw))
      (BlockedProgram.liftClaim (checkedCarrier accepted r.prune.keep argsRaw)
        (completeClaimFor accepted query)) = .justified := by
  refine ⟨admit_iff.mp evidence, ?_⟩
  exact source_justified_nonpromotion reg policy table _ _ argsRaw rawAtts groups
    declared queries query sigma ground ordinary accepted core member unblocked justified

/-- Refinement requirements are explicit parameters, never unproved axioms.
Hash collision resistance, safe descriptor capture, concrete byte parsing, and
compiler/runtime correctness are outside the finite selector/admission model. -/
theorem package_same_source_witness
    {env : Surface.Env canonNum} {input snapshot manifest registry output judgments}
    (h : Surface.sourceWithEvidence env input snapshot manifest registry = .ok (output, judgments))
    {leaf : Presentation.Leaf} (hl : leaf ∈ Surface.leafRecords output.semanticProgram)
    (hk : leaf.kind = .certified) :
    ∃ request, RequestBound input.policy.evidenceCheckers manifest leaf request ∧
      ∃ judgment ∈ judgments, judgment.leaf = leaf.id.val ∧ judgment.request = request ∧
        ∃ result, run snapshot registry request = .ok result ∧
          judgment.normalized = nf canonNum leaf.prop :=
  retained_certified_witness (Surface.sourceWithEvidence_semantic h) (fun _ => true)
    (by simpa using hl) hk

theorem concrete_admission_refinement {Bytes : Type}
    (implementation : Bytes → Except AdmissionError (List Judgment)) (bytes : Bytes)
    (snapshot : Snapshot) (policy : EvidencePolicy) (manifest : List ObjectMeta)
    (registry : Registry) (leaves : List Presentation.Leaf) (judgments : List Judgment)
    (refinement : implementation bytes = admit snapshot policy manifest registry leaves)
    (accepted : implementation bytes = .ok judgments) :
    Admitted snapshot policy manifest registry leaves judgments := by
  apply admit_iff.mp
  rw [← refinement]
  exact accepted

end Lara.Evidence
