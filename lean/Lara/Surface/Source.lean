import Lara.Surface.Correctness
import Lara.Evidence.Admission

namespace Lara.Surface

/-- Evidence rejection is an outer source boundary, not a fabricated ordinary
policy-table rejection. Structural assembly is untrusted until the gate and
ordinary core continuation have both succeeded. -/
inductive SourceError where
  | structural : Error → SourceError
  | evidence : Presentation.LeafId → SourceError
  | evidenceSyntax : SourceError
  deriving DecidableEq

def needsEvidence (leaf : Presentation.Leaf) : Bool :=
  leaf.kind == .certified || leaf.extraction.isSome

/-- The same ordinary core continuation as `check`, without re-expanding source. -/
def finishAssembled (env : Env canon) (output : Elaborated canon) : Except Error (Elaborated canon) :=
  match Check.Unit.checkUnit output.gamma env.registry output.ground output.unit with
  | .ok _ => .ok output
  | .error _ => .error .unsupported

theorem finishAssembled_eq_check {env : Env canon} {input output}
    (h : assemble env input = .ok output) : finishAssembled env output = check env input := by
  rw [check_eq_of_assemble env input output h]
  rfl

def elaborateSourceWithoutEvidence (env : Env canon) (input : Input) :
    Except SourceError (Elaborated canon) := do
  if !(decide input.policy.evidenceCheckers.Nodup) then .error .evidenceSyntax else do
    let lowered ← (assemble env input).mapError .structural
    match (leafRecords lowered.semanticProgram).find? needsEvidence with
    | some leaf => .error (.evidence leaf.id)
    | none => .ok lowered

def sourceWithoutEvidence (env : Env canon) (input : Input) :
    Except SourceError (Elaborated canon) := do
  let lowered ← elaborateSourceWithoutEvidence env input
  (finishAssembled env lowered).mapError .structural

theorem elaborateSourceWithoutEvidence_assembled {env : Env canon} {input output}
    (h : elaborateSourceWithoutEvidence env input = .ok output) : assemble env input = .ok output := by
  have hn : input.policy.evidenceCheckers.Nodup := by
    by_cases hp : input.policy.evidenceCheckers.Nodup
    · exact hp
    · simp [elaborateSourceWithoutEvidence, hp] at h
  unfold elaborateSourceWithoutEvidence at h
  simp [hn] at h
  cases hs : assemble env input with
  | error e => simp [hs, Except.mapError, Lara.Evidence.except_bind_error] at h
  | ok lowered =>
    simp only [hs, Except.mapError, Lara.Evidence.except_bind_ok] at h
    cases hf : (leafRecords lowered.semanticProgram).find? needsEvidence with
    | some leaf => simp [hf] at h
    | none =>
      simp only [hf] at h
      injection h with hlo
      subst hlo
      rfl

theorem sourceWithoutEvidence_core {env : Env canon} {input output}
    (h : sourceWithoutEvidence env input = .ok output) : check env input = .ok output := by
  unfold sourceWithoutEvidence at h
  cases hs : elaborateSourceWithoutEvidence env input with
  | error e => simp [hs, Except.mapError, Lara.Evidence.except_bind_error] at h
  | ok lowered =>
    have ha := elaborateSourceWithoutEvidence_assembled hs
    have hf : (finishAssembled env lowered).mapError SourceError.structural = .ok output := by
      simpa [hs, Lara.Evidence.except_bind_ok] using h
    rw [finishAssembled_eq_check ha] at hf
    cases hc : check env input with
    | error e => simp [hc, Except.mapError] at hf
    | ok checked =>
      simp only [hc, Except.mapError] at hf
      injection hf with hco
      subst hco
      rfl

theorem sourceWithoutEvidence_sound {env : Env canon} {input output}
    (h : sourceWithoutEvidence env input = .ok output) : Checks env input output :=
  check_sound env input output (sourceWithoutEvidence_core h)

theorem sourceWithoutEvidence_conservative {env : Env canon} {input output}
    (assembled : assemble env input = .ok output)
    (nodup : input.policy.evidenceCheckers.Nodup)
    (ordinary : (leafRecords output.semanticProgram).find? needsEvidence = none)
    (checked : check env input = .ok output) :
    sourceWithoutEvidence env input = .ok output := by
  have finish : finishAssembled env output = .ok output := by
    rw [finishAssembled_eq_check assembled]
    exact checked
  simp [sourceWithoutEvidence, elaborateSourceWithoutEvidence, nodup, assembled, ordinary,
    finish, Except.mapError]

/-- Expand values/comparisons and perform ordinary structural/policy assembly
once. Replay ALL semantic declarations before the unchanged core continuation.
The full semanticProgram remains available even for pruned or unused leaves. -/
def sourceWithEvidence (env : Env canonNum) (input : Input)
    (snapshot : Evidence.Snapshot) (manifest : List Evidence.ObjectMeta)
    (registry : Evidence.Registry) :
    Except (Sum SourceError Evidence.AdmissionError) (Elaborated canonNum × List Evidence.Judgment) := do
  if !(decide input.policy.evidenceCheckers.Nodup) then
    .error (Sum.inl .evidenceSyntax) else do
    let lowered ← (assemble env input).mapError (Sum.inl ∘ SourceError.structural)
    let judgments ← (Evidence.admit snapshot input.policy.evidenceCheckers manifest registry
      (leafRecords lowered.semanticProgram)).mapError Sum.inr
    let checked ← (finishAssembled env lowered).mapError (Sum.inl ∘ SourceError.structural)
    .ok (checked, judgments)

theorem sourceWithEvidence_core_and_semantic {env : Env canonNum}
    {input snapshot manifest registry output judgments}
    (h : sourceWithEvidence env input snapshot manifest registry = .ok (output, judgments)) :
    check env input = .ok output ∧
    Evidence.Admitted snapshot input.policy.evidenceCheckers manifest registry
      (leafRecords output.semanticProgram) judgments := by
  unfold sourceWithEvidence at h
  have hn : input.policy.evidenceCheckers.Nodup := by
    by_cases hp : input.policy.evidenceCheckers.Nodup
    · exact hp
    · simp [sourceWithEvidence, hp] at h
  simp [hn] at h
  cases hs : assemble env input with
  | error e => simp [hs, Except.mapError, Lara.Evidence.except_bind_error] at h
  | ok lowered =>
    simp only [hs, Except.mapError, Lara.Evidence.except_bind_ok] at h
    cases he : Evidence.admit snapshot input.policy.evidenceCheckers manifest registry
        (leafRecords lowered.semanticProgram) with
    | error e => simp [he, Except.mapError, Lara.Evidence.except_bind_error] at h
    | ok js =>
      simp only [he, Except.mapError, Lara.Evidence.except_bind_ok] at h
      cases hc : Check.Unit.checkUnit lowered.gamma env.registry lowered.ground lowered.unit with
      | error e => simp [finishAssembled, hc, Except.mapError, Lara.Evidence.except_bind_error] at h
      | ok checked =>
        simp only [finishAssembled, hc, Except.mapError, Lara.Evidence.except_bind_ok] at h
        injection h with hpair
        rcases hpair with ⟨rfl, rfl⟩
        exact ⟨by simp [check, hs, hc], Evidence.admit_iff.mp he⟩

theorem sourceWithEvidence_semantic {env : Env canonNum}
    {input snapshot manifest registry output judgments}
    (h : sourceWithEvidence env input snapshot manifest registry = .ok (output, judgments)) :
    Evidence.Admitted snapshot input.policy.evidenceCheckers manifest registry
      (leafRecords output.semanticProgram) judgments :=
  (sourceWithEvidence_core_and_semantic h).2

theorem sourceWithEvidence_sound {env : Env canonNum} {input snapshot manifest registry output judgments}
    (h : sourceWithEvidence env input snapshot manifest registry = .ok (output, judgments)) :
    Checks env input output ∧ ∃ lowered,
      elaborateWithAudit env input = .ok lowered ∧
      Evidence.Admitted snapshot input.policy.evidenceCheckers manifest registry
        (leafRecords lowered.declared.semanticProgram) judgments := by
  have core := sourceWithEvidence_core_and_semantic h
  have checks := check_sound env input output core.1
  have helab := elaborate_complete env input output checks
  cases hl : elaborateWithAudit env input with
  | error error => simp [elaborate, hl, Except.map] at helab
  | ok lowered =>
    have ho : lowered.output = output := by
      simpa [elaborate, hl, Except.map] using helab
    have hs : output.semanticProgram = lowered.declared.semanticProgram := by
      rw [← ho]
      exact (elaborateWithAudit_alignment hl).outputSemanticProgram
    exact ⟨checks, lowered, rfl, by simpa [hs] using core.2⟩

end Lara.Surface
