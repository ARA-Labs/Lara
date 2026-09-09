/-
Executable orchestration of the public unit-acceptance boundary.

`checkUnit` is the canonical executable constructor of `Unit.CheckedUnit`.
Its public seven-stage order is: duplicate rule identifiers, R2 signature
well-formedness and well-sortedness, policy R12, duplicate arguments, support,
typed attacks, then missing conflict. The first three stages run before program
checking; the remaining four are the detailed program checker's fixed order.

Σ conformance sits at position 2 because it is a precondition for reading the
policy as patterns at all: both the R12 Path-B validator and support inference
instantiate patterns, and both should be entitled to assume well-sortedness
rather than re-derive it. Running it after duplicate-rule detection means the
stage never has to reason about which of two same-named rules it is checking.

The finite ground atoms of the environment — Γ's leaf conclusions, the backend
theory table, and the queried claim atoms — are passed in as `ground` rather
than read off the unit, because `Unit` deliberately carries Γ as a *function*.
They are checked inside this stage, in the same position the Haskell mirror
checks them, so the two drivers cannot disagree about which stage rejects
first. Successful construction carries that checker's
exact retained-node cache, so it neither rechecks support terms nor asks
callers to provide alignment proofs. Manual proof-level construction of
`CheckedUnit` still requires every invariant.
-/

import Lara.Unit
import Lara.Check.Program

namespace Lara.Check.Unit

open Lara Lara.Support Lara.Attack

/-- Which clause of stage 2 failed. Every arm is rejection class R2; the payload
is the located diagnostic, which never reaches the wire (the wire carries the
class atom only). -/
inductive SignatureFault where
  | malformedSigma
  | policyIllSorted
  | groundIllSorted
  | argsIllSorted
deriving DecidableEq

/-- Closed diagnostics for whole-unit acceptance. -/
inductive UnitError where
  | duplicateRule : Policy.DuplicateRule → UnitError
  | signature : SignatureFault → UnitError
  | scopeViolation : Policy.ScopeViolation → UnitError
  | policyViolation : Policy.Violation → UnitError
  | program : ProgramError → UnitError
deriving DecidableEq

/-- Only the signature stage, policy R12, and wrapped frozen checker failures
have rejection classes.  Structural duplicate-rule errors preserve their typed
payload without inventing a frozen rejection class. -/
def UnitError.rejectClass : UnitError → Option RejectClass
  | .duplicateRule _ => none
  | .signature _ => some .R2
  | .scopeViolation _ => some .R12
  | .policyViolation _ => some .R12
  | .program error => error.rejectClass

/-- Stage 2, in the Haskell mirror's order: Σ itself, then the policy's
patterns, then the environment's ground atoms, then θ. -/
def signatureStage (ground : List Atom) (unit : Lara.Unit) : Option SignatureFault :=
  if Sigma.sigmaWellFormed unit.sigma = false then some .malformedSigma
  else if Lara.policyWellSorted unit.sigma unit.policy = false then some .policyIllSorted
  else if Lara.groundWellSorted unit.sigma ground = false then some .groundIllSorted
  else if Lara.argsWellSorted unit.sigma unit.policy unit.args = false then
    some .argsIllSorted
  else none

/-! ### The three facts stage 2 establishes

Each is read straight off the deterministic scan: `signatureStage` returning
`none` means every guard fell through, so each guarded condition is `false`,
i.e. the corresponding check is `true`. -/

theorem signatureStage_sigma_wf {ground : List Atom} {unit : Lara.Unit}
    (h : signatureStage ground unit = none) :
    Sigma.sigmaWellFormed unit.sigma = true := by
  unfold signatureStage at h
  by_cases h1 : Sigma.sigmaWellFormed unit.sigma = false
  · rw [if_pos h1] at h; exact absurd h (by simp)
  · exact Bool.not_eq_false _ |>.mp h1

theorem signatureStage_policy {ground : List Atom} {unit : Lara.Unit}
    (h : signatureStage ground unit = none) :
    Lara.policyWellSorted unit.sigma unit.policy = true := by
  unfold signatureStage at h
  by_cases h1 : Sigma.sigmaWellFormed unit.sigma = false
  · rw [if_pos h1] at h; exact absurd h (by simp)
  · rw [if_neg h1] at h
    by_cases h2 : Lara.policyWellSorted unit.sigma unit.policy = false
    · rw [if_pos h2] at h; exact absurd h (by simp)
    · exact Bool.not_eq_false _ |>.mp h2

theorem signatureStage_ground {ground : List Atom} {unit : Lara.Unit}
    (h : signatureStage ground unit = none) :
    Lara.groundWellSorted unit.sigma ground = true := by
  unfold signatureStage at h
  by_cases h1 : Sigma.sigmaWellFormed unit.sigma = false
  · rw [if_pos h1] at h; exact absurd h (by simp)
  · rw [if_neg h1] at h
    by_cases h2 : Lara.policyWellSorted unit.sigma unit.policy = false
    · rw [if_pos h2] at h; exact absurd h (by simp)
    · rw [if_neg h2] at h
      by_cases h3 : Lara.groundWellSorted unit.sigma ground = false
      · rw [if_pos h3] at h; exact absurd h (by simp)
      · exact Bool.not_eq_false _ |>.mp h3

theorem signatureStage_args {ground : List Atom} {unit : Lara.Unit}
    (h : signatureStage ground unit = none) :
    Lara.argsWellSorted unit.sigma unit.policy unit.args = true := by
  unfold signatureStage at h
  by_cases h1 : Sigma.sigmaWellFormed unit.sigma = false
  · rw [if_pos h1] at h; exact absurd h (by simp)
  · rw [if_neg h1] at h
    by_cases h2 : Lara.policyWellSorted unit.sigma unit.policy = false
    · rw [if_pos h2] at h; exact absurd h (by simp)
    · rw [if_neg h2] at h
      by_cases h3 : Lara.groundWellSorted unit.sigma ground = false
      · rw [if_pos h3] at h; exact absurd h (by simp)
      · rw [if_neg h3] at h
        by_cases h4 : Lara.argsWellSorted unit.sigma unit.policy unit.args = false
        · rw [if_pos h4] at h; exact absurd h (by simp)
        · exact Bool.not_eq_false _ |>.mp h4

/-- The canonical executable constructor for proof-bearing accepted units. -/
def checkUnit {canon : String → String}
    (Gamma : LeafId → Option Atom) (reg : BackendRegistry canon)
    (ground : List Atom) (unit : Lara.Unit) :
    Except UnitError (Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)) :=
  match hduplicate : Policy.firstDuplicateRuleId? unit.policy.rules with
  | some duplicate => .error (.duplicateRule duplicate)
  | none =>
      match hsignature : signatureStage ground unit with
      | some fault => .error (.signature fault)
      | none =>
          match hscope : Policy.firstOutOfScope? unit.policy with
          | some scope => .error (.scopeViolation scope)
          | none =>
          match hviolation : Policy.firstViolation? canon unit.policy with
          | some violation => .error (.policyViolation violation)
          | none =>
              match checkProgramDetailed unit.policy.ruleLookup Gamma reg
                  unit.policy.defeat unit.args unit.atts with
              | .error error => .error (.program error)
              | .ok accepted =>
                  .ok
                    { sigma := unit.sigma
                    , policy := unit.policy
                    , ruleIds_nodup :=
                        (Policy.firstDuplicateRuleId?_none_iff
                          unit.policy.rules).mp hduplicate
                    , sigma_wf := signatureStage_sigma_wf hsignature
                    , policy_well_sorted := signatureStage_policy hsignature
                    , scopes_wf := hscope
                    , policy_wf :=
                        (Policy.firstViolation_none_iff).mp hviolation
                    , program := accepted.program
                    , attack_complete := accepted.attack_complete
                    , nodes := accepted.nodes
                    , nodes_terms := accepted.nodes_terms
                    , args_well_sorted := by
                        have hargs : accepted.program.args = unit.args :=
                          accepted.arguments_eq
                        rw [hargs]
                        exact signatureStage_args hsignature }

/-- The facts supplied by successful unit checking. Named projections keep
clients independent of the order in which these obligations are recorded. -/
structure CheckUnitSound (canon : String → String)
    (Gamma : LeafId → Option Atom) (reg : BackendRegistry canon)
    (ground : List Atom) (unit : Lara.Unit)
    (accepted : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)) : Prop where
  sigma_eq : accepted.sigma = unit.sigma
  sigma_wf : Sigma.sigmaWellFormed accepted.sigma = true
  policy_sorted : Lara.policyWellSorted accepted.sigma accepted.policy = true
  ground_sorted : Lara.groundWellSorted accepted.sigma ground = true
  args_sorted : Lara.argsWellSorted accepted.sigma accepted.policy accepted.program.args = true
  policy_eq : accepted.policy = unit.policy
  ruleIds_nodup : (accepted.policy.rules.map (·.id)).Nodup
  policy_wf : Policy.WellFormed canon accepted.policy
  args_eq : accepted.program.args = unit.args
  atts_eq : accepted.program.atts = unit.atts
  attack_complete : Compile.AttackComplete canon accepted.policy.ruleLookup Gamma
    (certOkOf reg) accepted.policy.defeat accepted.program.args accepted.program.atts
  nodes_terms : accepted.nodes.map (·.term) = accepted.program.args

/-- Successful executable acceptance exposes every field of `CheckedUnit` by
its public name, together with exact correspondence to the raw declaration
lists supplied to the checker. -/
theorem checkUnit_sound {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {ground : List Atom} {unit : Lara.Unit}
    {accepted : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (h : checkUnit Gamma reg ground unit = .ok accepted) :
    CheckUnitSound canon Gamma reg ground unit accepted := by
  unfold checkUnit at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · split at h
          · contradiction
          · rename_i _ hsignature _ _ _ programAcceptance hprogram
            have hargsEq : accepted.program.args = unit.args := by
              have := Except.ok.inj h
              subst this
              exact programAcceptance.arguments_eq
            have hacc := Except.ok.inj h
            subst hacc
            exact {
              sigma_eq := rfl
              sigma_wf := signatureStage_sigma_wf hsignature
              policy_sorted := signatureStage_policy hsignature
              ground_sorted := signatureStage_ground hsignature
              args_sorted := by rw [hargsEq]; exact signatureStage_args hsignature
              policy_eq := rfl
              ruleIds_nodup :=
                (Policy.firstDuplicateRuleId?_none_iff unit.policy.rules).mp (by assumption)
              policy_wf := (Policy.firstViolation_none_iff).mp (by assumption)
              args_eq := programAcceptance.arguments_eq
              atts_eq := programAcceptance.attacks_eq
              attack_complete := programAcceptance.attack_complete
              nodes_terms := programAcceptance.nodes_terms }

/-- Exact completeness of the unit checker.  The premises are precisely the
raw policy and detailed-program obligations checked in the public fixed
order. -/
theorem checkUnit_complete {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {ground : List Atom} {unit : Lara.Unit}
    (hsignature : signatureStage ground unit = none)
    (hscope : Policy.firstOutOfScope? unit.policy = none)
    (hruleIds : (unit.policy.rules.map (·.id)).Nodup)
    (hpolicy : Policy.WellFormed canon unit.policy)
    (hargs : unit.args.Nodup)
    (hsupport : ∀ w ∈ unit.args, ∃ C,
      HasSupport canon unit.policy.ruleLookup Gamma (certOkOf reg) w C [])
    (htyped : ∀ k ∈ unit.atts,
      HasAttack canon unit.policy.ruleLookup Gamma (certOkOf reg)
        unit.policy.defeat k)
    (hsource : ∀ k ∈ unit.atts, k.source ∈ unit.args)
    (htarget : ∀ k ∈ unit.atts, k.target ∈ unit.args)
    (hattackComplete :
      Compile.AttackComplete canon unit.policy.ruleLookup Gamma
        (certOkOf reg) unit.policy.defeat unit.args unit.atts) :
    ∃ accepted, checkUnit Gamma reg ground unit = .ok accepted := by
  have hduplicate :
      Policy.firstDuplicateRuleId? unit.policy.rules = none :=
    (Policy.firstDuplicateRuleId?_none_iff unit.policy.rules).mpr hruleIds
  have hviolation : Policy.firstViolation? canon unit.policy = none :=
    (Policy.firstViolation_none_iff).mpr hpolicy
  obtain ⟨programAcceptance, hprogram⟩ :=
    checkProgramDetailed_complete hargs hsupport htyped hsource htarget
      hattackComplete
  unfold checkUnit
  split
  · rename_i duplicate hfound
    rw [hduplicate] at hfound
    contradiction
  · split
    · rename_i fault hfound
      rw [hsignature] at hfound
      contradiction
    · split
      · rename_i scope hfound
        rw [hscope] at hfound
        contradiction
      · split
        · rename_i violation hfound
          rw [hviolation] at hfound
          contradiction
        · split
          · rename_i error hfound
            rw [hprogram] at hfound
            contradiction
          · rename_i found hfound
            have hfound_eq : found = programAcceptance :=
              Except.ok.inj (hfound.symm.trans hprogram)
            subst found
            exact ⟨_, rfl⟩

/-! ### Naming a successful check's accepted output (issue #211)

The generated families and closed fixtures all follow one assembly: prove a
checker call succeeds, name the accepted payload, and export the `.ok`
equation for that name. `okValue`/`okValue_eq` package the assembly once —
`checkUnit_complete` supplies the existential directly, and
`exists_ok_of_isOk` admits the closed fixtures' decidable `isOk` form. -/

/-- A decidably successful `Except` is an `.ok`. -/
theorem exists_ok_of_isOk {ε α : Type _} {e : Except ε α}
    (h : e.isOk = true) : ∃ a, e = .ok a := by
  cases e with
  | error _ => simp [Except.isOk, Except.toBool] at h
  | ok a => exact ⟨a, rfl⟩

/-- The accepted payload of a checker call known to succeed. -/
def okValue {ε α : Type _} {e : Except ε α} (h : ∃ a, e = .ok a) : α :=
  e.toOption.get (by obtain ⟨a, rfl⟩ := h; rfl)

/-- The `.ok` equation for the named payload. -/
theorem okValue_eq {ε α : Type _} {e : Except ε α} (h : ∃ a, e = .ok a) :
    e = .ok (okValue h) := by
  cases e with
  | error _ => exact h.elim fun a ha => nomatch ha
  | ok a => rfl

private theorem lookupSubst_mem {θ : Subst} {x : VarId} {t : Term}
    (h : lookupSubst θ x = some t) : (x, t) ∈ θ := by
  induction θ with
  | nil => simp [lookupSubst] at h
  | cons b rest ih =>
      rcases b with ⟨y, u⟩
      simp only [lookupSubst] at h
      split at h
      · rename_i heq
        subst y
        simp only [Option.some.injEq] at h
        subst u
        simp
      · exact List.mem_cons_of_mem _ (ih h)

theorem thetaWellSorted_sortRespecting
    {sg : Sigma.Sigma} {r : Rule} {env : Sigma.ParamSorts} {θ : Subst}
    (hθ : Lara.thetaWellSorted sg r env θ = true)
    (hdom : ∀ x : VarId, x ∈ θ.map Prod.fst ↔ x ∈ r.params) :
    Sigma.SortRespecting sg env θ := by
  intro x s henv t ht
  have hpair : (x, t) ∈ θ := lookupSubst_mem ht
  have hxθ : x ∈ θ.map Prod.fst := List.mem_map.mpr ⟨(x, t), hpair, rfl⟩
  have hxparams : x ∈ r.params := (hdom x).mp hxθ
  have hchecked := List.all_eq_true.mp hθ (x, t) hpair
  have hcontains : r.params.contains x = true := by
    simpa using hxparams
  simp only [hcontains, if_true] at hchecked
  cases hsort : Sigma.sortOf sg t with
  | none => simp [hsort] at hchecked
  | some actual =>
      simp only [hsort, henv] at hchecked
      have heq : actual = s := of_decide_eq_true hchecked
      subst actual
      rfl

theorem thetaWellSorted_ruleSortRespecting
    {sg : Sigma.Sigma} {r : Rule} {env : Sigma.ParamSorts} {θ : Subst}
    (henv : Sigma.ruleParamSorts sg r = some env)
    (hθ : Lara.thetaWellSorted sg r env θ = true)
    (hdom : ∀ x : VarId, x ∈ θ.map Prod.fst ↔ x ∈ r.params) :
    Sigma.RuleSortRespecting sg r θ := by
  intro env' henv'
  have henvEq : env' = env := Option.some.inj (henv'.symm.trans henv)
  subst env'
  exact thetaWellSorted_sortRespecting hθ hdom

private theorem termsWellSorted_mem {sg : Sigma.Sigma} {P : Policy.Policy}
    {ws : List SupportTerm} (h : Lara.termsWellSorted sg P ws = true)
    {w : SupportTerm} (hw : w ∈ ws) :
    Lara.termWellSorted sg P w = true := by
  induction ws with
  | nil => simp at hw
  | cons u us ih =>
      simp only [Lara.termsWellSorted, Bool.and_eq_true] at h
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact h.1
      · exact ih h.2 hw

private theorem dischargesWellSorted_mem
    {sg : Sigma.Sigma} {P : Policy.Policy}
    {D : List (QuestionId × SupportTerm)}
    (h : Lara.dischargesWellSorted sg P D = true)
    {d : QuestionId × SupportTerm} (hd : d ∈ D) :
    Lara.termWellSorted sg P d.2 = true := by
  induction D with
  | nil => simp at hd
  | cons e es ih =>
      simp only [Lara.dischargesWellSorted, Bool.and_eq_true] at h
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact h.1
      · exact ih h.2 hd

private theorem allInstancesWellSortedList_iff
    {sg : Sigma.Sigma} {Pi : RuleId → Option Rule}
    {ws : List SupportTerm} :
    Lara.AllInstancesWellSortedList sg Pi ws ↔
      ∀ w ∈ ws, Lara.AllInstancesWellSorted sg Pi w := by
  induction ws with
  | nil => simp [Lara.AllInstancesWellSortedList]
  | cons w ws ih =>
      simp [Lara.AllInstancesWellSortedList, ih]

private theorem allInstancesWellSortedDischarges_iff
    {sg : Sigma.Sigma} {Pi : RuleId → Option Rule}
    {D : List (QuestionId × SupportTerm)} :
    Lara.AllInstancesWellSortedDischarges sg Pi D ↔
      ∀ d ∈ D, Lara.AllInstancesWellSorted sg Pi d.2 := by
  induction D with
  | nil => simp [Lara.AllInstancesWellSortedDischarges]
  | cons d D ih =>
      simp [Lara.AllInstancesWellSortedDischarges, ih]

private theorem hasSupport_allInstancesWellSorted
    {canon : String → String} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {sg : Sigma.Sigma} {P : Policy.Policy}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (hs : HasSupport canon P.ruleLookup Gamma CertOk w C O)
    (hws : Lara.termWellSorted sg P w = true) :
    Lara.AllInstancesWellSorted sg P.ruleLookup w := by
  induction hs with
  | leaf =>
      trivial
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis ihprems ihdis =>
      simp only [Lara.termWellSorted, hside.rule] at hws
      cases henv : Sigma.ruleParamSorts sg r with
      | none => simp [henv] at hws
      | some env =>
          simp only [henv, Bool.and_eq_true] at hws
          refine ⟨?_, ?_, ?_⟩
          · intro r' hr'
            have hr : r' = r := Option.some.inj (hr'.symm.trans hside.rule)
            subst r'
            have hrespect :=
              thetaWellSorted_ruleSortRespecting henv hws.1.1 hside.θDom
            exact Sigma.wellSorted_rule henv (hrespect env henv)
          · rw [allInstancesWellSortedList_iff]
            intro w hw
            obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
            have hiLt := lt_of_getElem?_some hi
            obtain ⟨A, hA⟩ := getElem?_some_of_lt Cs i
              (by have := hside.lenCs; omega)
            obtain ⟨O', hO⟩ := getElem?_some_of_lt Os i
              (by have := hside.lenOs; omega)
            exact ihprems i w A O' hi hA hO
              (termsWellSorted_mem hws.1.2 hw)
          · rw [allInstancesWellSortedDischarges_iff]
            intro d hd
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hd
            have hjLt := lt_of_getElem?_some hj
            rcases d with ⟨q, w⟩
            obtain ⟨A, hA⟩ := getElem?_some_of_lt DCs j
              (by have := hside.lenDCs; omega)
            obtain ⟨O', hO⟩ := getElem?_some_of_lt DOs j
              (by have := hside.lenDOs; omega)
            exact ihdis j q w A O' hj hA hO
              (dischargesWellSorted_mem hws.2 hd)

/-! ### Result 13(c): accepted support instances and their ground environment

The statement the paper cites, and the justification for the per-instance half
of stage 2 being as thin as it is. It derives the following acceptance facts
from the executable checks:

* Σ itself is well-formed, so `sortOf` is total on declared data;
* every ground atom the environment contributed — Γ's leaf conclusions, the
  backend theory table, and the queried claim atoms — is well-sorted;
* every premise, conclusion, and critical-question answer instantiated by an
  actual rule instance recursively reachable through an accepted support term
  is well-sorted.

The bridge uses both executable halves that constrain an actual θ: stage 2
checks its range terms, while accepted support supplies R3's exact-domain
invariant. Nothing checks the instantiated atoms directly; they are reached
through `Sigma.wellSorted_rule`, the substitution lemma. -/
theorem checkUnit_wellSorted {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {ground : List Atom} {unit : Lara.Unit}
    {accepted : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (h : checkUnit Gamma reg ground unit = .ok accepted) :
    Sigma.sigmaWellFormed accepted.sigma = true ∧
    (∀ a ∈ ground, Sigma.WellSorted accepted.sigma a) ∧
    (∀ w ∈ accepted.program.args,
      Lara.AllInstancesWellSorted accepted.sigma accepted.policy.ruleLookup w) := by
  have hs := checkUnit_sound h
  have hwf := hs.sigma_wf
  have hground := hs.ground_sorted
  have hargs := hs.args_sorted
  refine ⟨hwf, ?_, ?_⟩
  · intro a ha
    unfold Lara.groundWellSorted at hground
    exact List.all_eq_true.mp hground a ha
  · intro w hw
    obtain ⟨C, hsupport⟩ := accepted.program.complete w hw
    exact hasSupport_allInstancesWellSorted hsupport
      (termsWellSorted_mem hargs hw)

end Lara.Check.Unit
