/-
Focused executable fixtures for the conflict-coverage boundary. These pin the
fact that compilation records edges, rather than attack-reason labels: direct
and closure coverage are both sufficient, including when a different typed
attack reaches the same compiled target.
-/

import Lara.Examples

namespace Lara.Examples.AttackCompleteness

open Lara.Support Lara.Attack Lara.Compile Lara.Check

/-! ### Conflict attackability -/

theorem leaf_conflict_attackable :
    conflictAttackableB PiEx (.leaf l1) = true := by decide

theorem defeasible_root_conflict_attackable :
    conflictAttackableB PiEx vWrap = true := by decide

theorem strict_root_not_conflict_attackable :
    conflictAttackableB PiStrict strictTarget = false := by decide

theorem unknown_rule_not_conflict_attackable :
    conflictAttackableB PiEx absentTarget = false := by decide

/-! ### Declared-attack coverage -/

theorem direct_attack_covered :
    coveredB [kAtk] (.leaf l2) (.leaf l1) = true := by decide

/-- An undermine on the contained leaf already covers its wrapper target. No
redundant rebut at the wrapper root is required. -/
theorem wrapper_closure_covered :
    coveredB [kAtk] (.leaf l2) vWrap = true := by decide

theorem wrong_target_not_covered :
    coveredB [kAtk] (.leaf l2) (.leaf l2) = false := by decide

theorem no_attacks_not_covered :
    coveredB [] (.leaf l2) (.leaf l1) = false := by decide

/-! ### Edge completeness is reason-independent -/

/-- A rebut with the same source as `kAtk`, targeting its wrapper closure
target directly. Its contrary declaration differs from the undermine's. -/
def sameEdgeDifferentReasonPolicy : DefeatPolicy :=
  ⟨[(apB, apA), (apB, apB)], []⟩

theorem same_edge_rebut_typed :
    HasAttack id PiEx ΓEx certOkNone sameEdgeDifferentReasonPolicy
      (.rebut (.leaf l2) vWrap) := by
  refine .rebut
    (w := .leaf l2) (rn := rWrapId) (θ := []) (ws := [.leaf l1])
    (D := []) (H := []) (a := .none)
    (r := ruleWrap) (Cw := pB) (Cu := pB) (Ow := [])
    (.leaf (by decide))
    (by simp [PiEx, rMixId, rWrapId])
    rfl
    (by decide)
    ⟨(apB, apB), by simp [sameEdgeDifferentReasonPolicy], [], pB, pB,
      by decide, by decide, equiv_refl id pB, equiv_refl id pB⟩

/-- The compiled AF keeps only this resulting edge. A typed rebut therefore
covers the very same source/closure target pair as the typed undermine. -/
theorem same_edge_different_reason_covered :
    kReb.source = kAtk.source ∧
    coveredB [kReb] kAtk.source vWrap = true := by
  constructor
  · simp [kReb, kAtk, Attack.source]
  · decide

/-! ### Detailed program acceptance -/

theorem missing_conflict_no_reject_class :
    (ProgramError.missingConflict
      ⟨0, 1, pB, pA⟩).rejectClass = none := by rfl

theorem first_missing_pair :
    checkProgramDetailed PiEx ΓEx registryEx dpEx
      [.leaf l2, .leaf l1, vWrap] [] =
      .error (.missingConflict ⟨0, 1, pB, pA⟩) := by rfl

/-- The later source has the smaller target index, but source-major ordering
still reports `(0, 1)` before `(1, 0)`. -/
def crossingPolicy : DefeatPolicy :=
  ⟨[(apA, apB), (apB, apA)], []⟩

theorem crossing_pair_source_major :
    checkProgramDetailed PiEx ΓEx registryEx crossingPolicy
      [.leaf l1, .leaf l2] [] =
      .error (.missingConflict ⟨0, 1, pA, pB⟩) := by rfl

/-- A self-undermine on `l1` covers both the leaf and its declared wrapper by
subargument closure. The extra `(p,p)` contrary makes the self-pair real and
covered; `(p,q)` exercises closure coverage onto `vWrap`. -/
def closureCompletePolicy : DefeatPolicy :=
  ⟨[(apA, apA), (apA, apB)], []⟩

def kSelfA : Attack :=
  .undermine (.leaf l1) (.leaf l1) []

theorem closure_covered_wrapper_accepted :
    (checkProgramDetailed PiEx ΓEx registryEx closureCompletePolicy
      [.leaf l1, vWrap] [kSelfA]).isOk = true := by decide

/-- A typed attack from the right source can still be a decoy when its attacked
occurrence is absent from the contrary target. -/
def decoyPolicy : DefeatPolicy :=
  ⟨[(apB, apB), (apB, apA)], []⟩

def kSelfB : Attack :=
  .undermine (.leaf l2) (.leaf l2) []

theorem nonmatching_attack_decoy :
    checkProgramDetailed PiEx ΓEx registryEx decoyPolicy
      [.leaf l2, .leaf l1] [kSelfB] =
      .error (.missingConflict ⟨0, 1, pB, pA⟩) := by rfl

def selfConflictPolicy : DefeatPolicy :=
  ⟨[(apA, apA)], []⟩

theorem self_conflict_missing_at_origin :
    checkProgramDetailed PiEx ΓEx registryEx selfConflictPolicy
      [.leaf l1] [] =
      .error (.missingConflict ⟨0, 0, pA, pA⟩) := by rfl

theorem support_error_precedes_missing_conflict :
    checkProgramDetailed PiEx ΓEx registryEx selfConflictPolicy
      [.leaf l1, badSource] [] =
      .error (.rejection (.argument 1)
        (.R1 .root (.missingLeaf ⟨"missing-source"⟩))) := by rfl

theorem attack_error_precedes_missing_conflict :
    checkProgramDetailed PiEx ΓEx registryEx dpEx
      [.leaf l2, .leaf l1] [.rebut (.leaf l2) (.leaf l1)] =
      .error (.rejection (.attack 0)
        (.R10 .root [] .rebut
          (.wrongOccurrenceKind .rule .leaf))) := by rfl

theorem detailed_empty_accepted :
    (checkProgramDetailed PiEx ΓEx registryEx dpEx [] []).isOk = true := by
  decide

theorem detailed_no_contrary_accepted :
    (checkProgramDetailed PiEx ΓEx registryEx dpEx
      [.leaf l1] []).isOk = true := by decide

theorem detailed_strict_root_contrary_not_required :
    (checkProgramDetailed PiStrict ΓEx registryEx dpEx
      [.leaf l2, strictTarget] []).isOk = true := by decide

/-! The detailed path must not perturb the legacy projection. -/

theorem legacy_acceptance_unchanged :
    (checkProgram PiEx ΓEx registryEx dpEx
      [.leaf l2, .leaf l1] []).isOk = true := by decide

theorem legacy_support_error_unchanged :
    checkProgram PiEx ΓEx registryEx selfConflictPolicy
      [.leaf l1, badSource] [] =
      .error (.rejection (.argument 1)
        (.R1 .root (.missingLeaf ⟨"missing-source"⟩))) := by rfl

theorem legacy_attack_error_unchanged :
    checkProgram PiEx ΓEx registryEx dpEx
      [.leaf l2, .leaf l1] [.rebut (.leaf l2) (.leaf l1)] =
      .error (.rejection (.attack 0)
        (.R10 .root [] .rebut
          (.wrongOccurrenceKind .rule .leaf))) := by rfl

/-! ### Retained nodes, adequacy theorems, and stress guard -/

def noRules : RuleId → Option Rule := fun _ => none

def sl0 : LeafId := ⟨"stress-0"⟩
def sl1 : LeafId := ⟨"stress-1"⟩
def sl2 : LeafId := ⟨"stress-2"⟩
def sl3 : LeafId := ⟨"stress-3"⟩
def sl4 : LeafId := ⟨"stress-4"⟩
def sl5 : LeafId := ⟨"stress-5"⟩
def sl6 : LeafId := ⟨"stress-6"⟩
def sl7 : LeafId := ⟨"stress-7"⟩

def ΓStress : LeafId → Option Atom := fun l =>
  if l = sl0 then some pA
  else if l = sl1 then some pB
  else if l = sl2 then some pC
  else if l = sl3 then some pA
  else if l = sl4 then some pB
  else if l = sl5 then some pC
  else if l = sl6 then some pA
  else if l = sl7 then some pB
  else none

def stressArgs : List SupportTerm :=
  [.leaf sl0, .leaf sl1, .leaf sl2, .leaf sl3,
    .leaf sl4, .leaf sl5, .leaf sl6, .leaf sl7]

def stressDetailed :=
  checkProgramDetailed noRules ΓStress registryEx ⟨[], []⟩ stressArgs []

/-- Default-heartbeat regression: the successful path checks eight nodes,
builds all source buckets once, and traverses 64 ordered pairs to the final
no-gap result. -/
theorem detailed_default_heartbeat_stress :
    stressDetailed.isOk = true := by decide

def stressAcceptance :
    ProgramAcceptance noRules ΓStress registryEx ⟨[], []⟩ stressArgs [] :=
  stressDetailed.toOption.get (by decide)

theorem stressDetailed_ok :
    stressDetailed = .ok stressAcceptance := by
  cases h : stressDetailed with
  | error e =>
      have hs := detailed_default_heartbeat_stress
      rw [h] at hs
      contradiction
  | ok accepted =>
      have hopt : stressDetailed.toOption = some accepted :=
        congrArg Except.toOption h
      have heq : stressAcceptance = accepted := by
        unfold stressAcceptance
        apply Option.get_of_eq_some
        exact hopt
      rw [heq]

theorem retained_node_alignment :
    stressAcceptance.nodes.map (·.term) = stressArgs := by
  exact stressAcceptance.nodes_terms.trans stressAcceptance.arguments_eq

/-- Concrete PRG-08 regression: the generated source cache retains exactly
the one declared attack in the first source bucket and leaves the second
source bucket empty. -/
def acceptedUnitCache :=
  conflictCache unitPolicyEx.ruleLookup acceptedUnitEx.program.atts
    acceptedUnitEx.nodes

theorem nonempty_source_buckets_exact :
    acceptedUnitCache.map (·.attacks) = [[kAtk], []] := by
  rfl

def stressCache :=
  conflictCache noRules ([] : List Attack) stressAcceptance.nodes

theorem stress_source_bucket_adequacy
    (source : ConflictNode id noRules ΓStress (certOkOf registryEx) [])
    (_hsource : source ∈ stressCache) (k : Attack) :
    k ∈ source.attacks ↔ k ∈ ([] : List Attack) ∧
      k.source = source.term := by
  exact sourceAttackBucket_mem_iff source k

theorem detailed_sound_fixture :
    Compile.AttackComplete id noRules ΓStress (certOkOf registryEx)
      ⟨[], []⟩ stressAcceptance.program.args
      stressAcceptance.program.atts :=
  (checkProgramDetailed_sound stressDetailed_ok).2.2.1

theorem detailed_complete_fixture :
    ∃ accepted,
      checkProgramDetailed PiEx ΓEx registryEx dpEx [] [] =
        .ok accepted := by
  apply checkProgramDetailed_complete
  · simp
  · simp
  · simp
  · simp
  · simp
  · intro source hsource
    simp at hsource

end Lara.Examples.AttackCompleteness
