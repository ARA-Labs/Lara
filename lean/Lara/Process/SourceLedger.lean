import Lara.Process.Ledger
import Lara.Process.Order

/-!
A count-bound ledger is checked against a complete *modeled* history. Run and
result membership are checked independently of the supplied statistic metadata:
`outcome` is a label, not an automatic interpretation as a p-value or e-value.
Source fidelity, history completeness and statistical calibration remain explicit
modeling assumptions. A count bound is not a full ordered ledger; this path
supplies neither online, FDR nor mFDR guarantees.
-/

namespace Lara.Process.Source

/-- The statistic interpretation and its declared bound belong to `ledger`, not
to the natural-number result label. -/
structure LedgerBinding where
  run : RunId
  family : FamilyId
  outcome : Nat
  ledger : Statistics.Ledger
  deriving DecidableEq, Repr

/-- Closed failure vocabulary; failures carry no fallback level. -/
inductive LedgerFault where
  | absentRun
  | familyMismatch
  | absentResult
  | missingKind
  | missingValue
  | missingGuarantee
  | missingBound
  | zeroBound
  | unsupportedGuarantee
  | exceededBound
  | nonFiniteLevel
  deriving DecidableEq, Repr, Fintype

/-- The independent acceptance domain: literal run/result membership, present
metadata, a positive bound on *all* runs, FWER, and the existing finite warrant. -/
def LedgerValid (history : ProcessHistory) (binding : LedgerBinding) (level : ℚ) : Prop :=
  (∃ event ∈ history, ∃ plan version inputs,
    event.event = .run binding.run plan version inputs binding.family) ∧
  (∃ event ∈ history, event.event = .result binding.run binding.outcome) ∧
  binding.ledger.kind.isSome = true ∧
  binding.ledger.value.isSome = true ∧
  (∃ bound, binding.ledger.countBound = some bound ∧ 0 < bound ∧
    familyCount history binding.family ≤ bound) ∧
  binding.ledger.guarantee = some .fwer ∧
  Statistics.warrantedLevel binding.ledger = (level : WithTop ℚ)

/-- Only the actual count and finite level survive proof erasure. In particular,
no caller-supplied desired level is an acceptance premise. -/
structure LedgerCertificate (history : ProcessHistory) (binding : LedgerBinding) where
  count : Nat
  level : ℚ
  count_eq : count = familyCount history binding.family
  run_present : ∃ event ∈ history, ∃ plan version inputs,
    event.event = .run binding.run plan version inputs binding.family
  result_present : ∃ event ∈ history, event.event = .result binding.run binding.outcome
  kind_present : binding.ledger.kind.isSome = true
  value_present : binding.ledger.value.isSome = true
  bound_valid : ∃ bound, binding.ledger.countBound = some bound ∧ 0 < bound ∧ count ≤ bound
  guarantee : binding.ledger.guarantee = some .fwer
  warranted : Statistics.warrantedLevel binding.ledger = (level : WithTop ℚ)

private def hasLedgerRun (history : ProcessHistory) (binding : LedgerBinding) : Bool :=
  history.any fun event => match event.event with
    | .run run _ _ _ family => run == binding.run && family == binding.family
    | _ => false

private theorem hasLedgerRun_iff (history : ProcessHistory) (binding : LedgerBinding) :
    hasLedgerRun history binding = true ↔
      ∃ event ∈ history, ∃ plan version inputs,
        event.event = .run binding.run plan version inputs binding.family := by
  simp only [hasLedgerRun, List.any_eq_true]
  constructor
  · rintro ⟨event, member, matched⟩
    cases he : event.event with
    | run run plan version inputs family =>
      simp only [he, Bool.and_eq_true, beq_iff_eq] at matched
      exact ⟨event, member, plan, version, inputs, by rw [he, matched.1, matched.2]⟩
    | _ => simp [he] at matched
  · rintro ⟨event, member, plan, version, inputs, exactEvent⟩
    exact ⟨event, member, by simp [exactEvent]⟩

/-- Check one complete modeled history. An audit over a compatibility family
must apply this check to every history, not just the selected successful run. -/
def checkLedger (history : ProcessHistory) (binding : LedgerBinding) :
    Except LedgerFault (LedgerCertificate history binding) :=
  if run : hasLedgerRun history binding = true then
    if result : ∃ event ∈ history, event.event = .result binding.run binding.outcome then
      if kind : binding.ledger.kind.isSome = true then
        if value : binding.ledger.value.isSome = true then
          if guarantee : binding.ledger.guarantee = some .fwer then
            match boundAt : binding.ledger.countBound with
            | none => .error .missingBound
            | some bound =>
              if positive : 0 < bound then
                let count := familyCount history binding.family
                if bounded : count ≤ bound then
                  match levelAt : Statistics.warrantedLevel binding.ledger with
                  | none => .error .nonFiniteLevel
                  | some level => .ok
                    { count := count
                      level := level
                      count_eq := rfl
                      run_present := (hasLedgerRun_iff history binding).mp run
                      result_present := result
                      kind_present := kind
                      value_present := value
                      bound_valid := ⟨bound, boundAt, positive, bounded⟩
                      guarantee := guarantee
                      warranted := levelAt }
                else .error .exceededBound
              else .error .zeroBound
          else if binding.ledger.guarantee = none then .error .missingGuarantee
            else .error .unsupportedGuarantee
        else .error .missingValue
      else .error .missingKind
    else .error .absentResult
  else if history.any (fun event => match event.event with
      | .run run _ _ _ _ => run == binding.run
      | _ => false) then .error .familyMismatch
    else .error .absentRun

/-- The finite public result carries a guarantee class only on success. -/
def observeLedger (history : ProcessHistory) (binding : LedgerBinding) :
    Except LedgerFault (GuaranteeClass × ℚ) :=
  (checkLedger history binding).map fun certificate => (.fwer, certificate.level)

theorem LedgerCertificate.sound {history : ProcessHistory} {binding : LedgerBinding}
    (certificate : LedgerCertificate history binding) :
    LedgerValid history binding certificate.level := by
  refine ⟨certificate.run_present, certificate.result_present, certificate.kind_present,
    certificate.value_present, ?_, certificate.guarantee, certificate.warranted⟩
  simpa only [certificate.count_eq] using certificate.bound_valid

theorem checkLedger_sound {history : ProcessHistory} {binding : LedgerBinding}
    {certificate : LedgerCertificate history binding}
    (_checked : checkLedger history binding = .ok certificate) :
    LedgerValid history binding certificate.level := certificate.sound

/-- Completeness is for the independent modeled domain, not physical observation
or calibration of the supplied statistic interpretation. -/
theorem checkLedger_complete {history : ProcessHistory} {binding : LedgerBinding} {level : ℚ}
    (valid : LedgerValid history binding level) :
    ∃ certificate, checkLedger history binding = .ok certificate ∧ certificate.level = level := by
  rcases valid with ⟨run, result, kind, value, ⟨bound, boundAt, positive, bounded⟩,
    guarantee, warranted⟩
  have runChecked := (hasLedgerRun_iff history binding).mpr run
  unfold checkLedger
  simp only [runChecked, result, kind, value, guarantee, ↓reduceDIte]
  split
  · rename_i missing
    rw [boundAt] at missing
    cases missing
  · rename_i found foundAt
    have same : found = bound := Option.some.inj (foundAt.symm.trans boundAt)
    subst found
    simp only [positive, bounded, ↓reduceDIte]
    split
    · rename_i nonFinite
      rw [warranted] at nonFinite
      cases nonFinite
    · rename_i foundLevel foundAt
      have same : foundLevel = level := WithTop.coe_injective (foundAt.symm.trans warranted)
      subst foundLevel
      exact ⟨_, rfl, rfl⟩

theorem checkLedger_success_iff (history : ProcessHistory) (binding : LedgerBinding) :
    (∃ certificate, checkLedger history binding = .ok certificate) ↔
      ∃ level, LedgerValid history binding level := by
  constructor
  · rintro ⟨certificate, checked⟩
    exact ⟨certificate.level, checkLedger_sound checked⟩
  · rintro ⟨level, valid⟩
    obtain ⟨certificate, checked, _⟩ := checkLedger_complete valid
    exact ⟨certificate, checked⟩

/-- No existentially selected compatible history can replace this universal
obligation. What counts as compatible is supplied by the surrounding model. -/
theorem checkLedger_all_iff (compatible : ProcessHistory → Prop) (binding : LedgerBinding) :
    (∀ history, compatible history → ∃ certificate, checkLedger history binding = .ok certificate) ↔
      ∀ history, compatible history → ∃ level, LedgerValid history binding level := by
  constructor <;> intro all history member
  · exact (checkLedger_success_iff history binding).mp (all history member)
  · exact (checkLedger_success_iff history binding).mpr (all history member)

theorem observeLedger_success_iff (history : ProcessHistory) (binding : LedgerBinding)
    (guarantee : GuaranteeClass) (level : ℚ) :
    observeLedger history binding = .ok (guarantee, level) ↔
      guarantee = .fwer ∧ LedgerValid history binding level := by
  constructor
  · intro observed
    unfold observeLedger at observed
    cases checked : checkLedger history binding with
    | error fault => simp [checked, Except.map] at observed
    | ok certificate =>
      simp only [checked, Except.map, Except.ok.injEq, Prod.mk.injEq] at observed
      rcases observed with ⟨classEq, levelEq⟩
      exact ⟨classEq.symm, levelEq ▸ certificate.sound⟩
  · rintro ⟨rfl, valid⟩
    obtain ⟨certificate, checked, levelEq⟩ := checkLedger_complete valid
    simp [observeLedger, checked, Except.map, levelEq]

theorem observeLedger_failure_iff (history : ProcessHistory) (binding : LedgerBinding) :
    (∃ fault, observeLedger history binding = .error fault) ↔
      ¬ ∃ level, LedgerValid history binding level := by
  rw [← checkLedger_success_iff history binding]
  cases checked : checkLedger history binding <;> simp [observeLedger, checked, Except.map]

/-- These are threshold consequences only. Empirical error bounds additionally
need the existing statistical theorems' explicit calibration premises. -/
theorem LedgerCertificate.pValue_threshold {history : ProcessHistory} {binding : LedgerBinding}
    (certificate : LedgerCertificate history binding)
    (kind : binding.ledger.kind = some .pValue) :
    ∃ p bound, binding.ledger.value = some p ∧ binding.ledger.countBound = some bound ∧
      0 < certificate.level ∧ p ≤ certificate.level / bound :=
  Statistics.warrantedLevel_pValue certificate.warranted kind

theorem LedgerCertificate.eValue_threshold {history : ProcessHistory} {binding : LedgerBinding}
    (certificate : LedgerCertificate history binding)
    (kind : binding.ledger.kind = some .eValue) :
    ∃ e bound, binding.ledger.value = some e ∧ binding.ledger.countBound = some bound ∧
      0 < certificate.level ∧ (bound : ℚ) / certificate.level ≤ e :=
  Statistics.warrantedLevel_eValue certificate.warranted kind

/-- Appending a run counts even without a result; success is not a premise. -/
theorem ledger_failed_run_counts (history : ProcessHistory) (id : EventId) (run : RunId)
    (plan : PlanId) (version : VersionId) (inputs : List (DataId × VersionId)) (family : FamilyId) :
    familyCount (history ++ [⟨id, .run run plan version inputs family⟩]) family =
      familyCount history family + 1 :=
  familyCount_append_run history ⟨id, .run run plan version inputs family⟩
    ⟨run, plan, version, inputs, family⟩ rfl

/-- A previously valid tight bound is invalidated by an additional sibling run,
regardless of whether that sibling later produces a result. -/
theorem ledger_extension_invalidates {history : ProcessHistory} {binding : LedgerBinding}
    (certificate : LedgerCertificate history binding)
    (tight : binding.ledger.countBound = some certificate.count)
    (id : EventId) (run : RunId) (plan : PlanId) (version : VersionId)
    (inputs : List (DataId × VersionId)) :
    ∃ fault, observeLedger
      (history ++ [⟨id, .run run plan version inputs binding.family⟩]) binding = .error fault := by
  apply (observeLedger_failure_iff _ _).mpr
  rintro ⟨level, valid⟩
  obtain ⟨bound, boundAt, _, bounded⟩ := valid.2.2.2.2.1
  have same : bound = certificate.count := Option.some.inj (boundAt.symm.trans tight)
  rw [same, ledger_failed_run_counts, ← certificate.count_eq] at bounded
  omega

end Lara.Process.Source
