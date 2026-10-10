import Lara.Process.Entitlement

/-!
R2 witnesses for entitlement.

One two-history model carries every witness. In history `left` the claim's
witness `w1` is unattacked and `w2` is defeated; in `right` the roles swap. A
third witness `w3` rests on conditional evidence. The claim is true only in
`left`.

* `entitled_not_argument`: the claim is entitled (some witness warrants in each
  history) but no submitted witness is `ArgumentEntitled`.
* `defeated_not_warranted`, `conditional_not_warranted`, `warranted_not_true`,
  `entitled_not_known`: non-collapse countermodels. The BHL form of
  "conditional but not applied" is `Lara.Process.conditional_not_applied`.
* `promotion_needs_wellKinded`: without the rule-kind discipline a derivation
  with a hypothetical leaf can conclude `observed`.
* `stricter_directional_instance`: removing an argument outside the witness's
  ancestry preserves warrant, as `stricter_directional` predicts.
-/

namespace Lara.Examples.ProcessEntitlement

open Lara.Grounded
open Lara.Process

inductive Hist where
  | left
  | right
  deriving DecidableEq, Repr, Fintype

inductive Wit where
  | w1
  | w2
  | w3
  deriving DecidableEq, Repr, Fintype

def claimC : ClaimId := ⟨0⟩

/-- Argument `3` attacks `w2`'s argument in `left` and `w1`'s in `right`.
Argument `4` is conditional and `5` is supported; neither attacks anything. -/
def af : Hist → AF
  | .left => ⟨[1, 2, 3, 4, 5], fun a b => a == 3 && b == 2⟩
  | .right => ⟨[1, 2, 3, 4, 5], fun a b => a == 3 && b == 1⟩

def kindOf : Arg → EvidenceKind
  | 4 => .conditional
  | 5 => .supported
  | _ => .observed

abbrev model : WarrantModel Hist ClaimId Wit where
  af := af
  kind _ := kindOf
  argOf
    | .w1 => 1
    | .w2 => 2
    | .w3 => 4
  concludes _ _ c := c = claimC
  probed _ _ := {.sampling}
  achieved _ _ := (.fwer, 1 / 20)
  artifact _ _ := True
  truth h _ := h = .left

abbrev strict : Profile Empty := Profile.strict (1 / 20)

/-- A laxer profile that also admits supported and conditional evidence. -/
abbrev lax : Profile Empty :=
  { strict with admissible := {.conditional, .supported, .observed} }

/-- Every history reports the same empty record. -/
abbrev reporting : ProcessModel Hist _root_.Unit _root_.Unit where
  Valid _ := True
  Report _ _ := ()

def scope : CoverageScope := ⟨[.analysisRun], none, none, none, 10⟩

def noPolicy : Empty → ProcessHistory → List Stamped → Prop := fun e => e.elim

instance (p : Empty) (h : ProcessHistory) (r : List Stamped) : Decidable (noPolicy p h r) :=
  p.elim

/-- Complete coverage of an empty analysis-run scope: no history has runs, so
the coverage restricts nothing here. -/
abbrev admitted : Admitted Hist _root_.Unit Empty :=
  ⟨.complete scope, noPolicy, fun _ => [], fun _ _ => [], Assumptions.trivial⟩

instance : DecidablePred reporting.Valid := fun _ => isTrue True.intro

/-- Some witness warrants in each history, so the claim is entitled; no single
submitted witness warrants in both. -/
theorem entitled_not_argument :
    Entitled model strict reporting admitted () claimC ∧
      ¬ ∃ w, ArgumentEntitled model strict reporting admitted () claimC w :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- Support is not warrant: `w2`'s argument is present and observed in `left`
but defeated there. -/
theorem defeated_not_warranted :
    2 ∈ (model.underProfile strict .left).args ∧ ¬ Warranted model strict .left claimC .w2 := by
  decide +kernel

/-- Conditional evidence is grounded `in` but not warranted under the strict
profile; a laxer profile admitting it warrants it. -/
theorem conditional_not_warranted :
    labelC (model.af .left) 4 = .inn ∧ ¬ Warranted model strict .left claimC .w3 ∧
      Warranted model lax .left claimC .w3 := by
  decide +kernel

/-- Warrant is not truth: `w2` warrants the claim in `right`, where it is false. -/
theorem warranted_not_true :
    Warranted model strict .right claimC .w2 ∧ ¬ model.truth .right claimC := by
  decide +kernel

/-- Two histories are indistinguishable to the record's reader when they produce
the same report. -/
abbrev sameReport (h h' : Hist) : Prop := reporting.Report h () = reporting.Report h' ()

instance (h : Hist) : Decidable (Known model sameReport h claimC) :=
  inferInstanceAs (Decidable (∀ h', sameReport h h' → model.truth h' claimC))

/-- Entitlement is not knowledge: the claim is entitled, but at `left` the
record's reader cannot exclude `right`, which reports the same and where the
claim is false. -/
theorem entitled_not_known :
    Entitled model strict reporting admitted () claimC ∧
      ¬ Known model sameReport .left claimC :=
  ⟨entitled_not_argument.1, by decide +kernel⟩

/-- Without `WellKinded`, a rule may promote: a hypothetical leaf yields an
observed conclusion. -/
theorem promotion_needs_wellKinded :
    ¬ (KindDerivation.unary .observed (.leaf .hypothetical)).WellKinded ∧
      (KindDerivation.unary .observed (.leaf .hypothetical)).kind = .observed := by
  decide +kernel

/-- A well-kinded derivation with a conditional leaf stays below `observed`. -/
theorem wellKinded_no_promotion :
    (KindDerivation.binary .conditional (.leaf .observed) (.leaf .conditional)).WellKinded ∧
      (KindDerivation.binary .conditional (.leaf .observed) (.leaf .conditional)).kind ≠
        .observed := by
  decide +kernel

/-- The strict profile is stricter than the laxer one. The arguments it removes
(the conditional `4` and the supported `5`) are outside `w1`'s ancestry in
`left`, so `w1`'s warrant transfers from the strict to the laxer profile. -/
theorem stricter_directional_instance :
    Warranted model strict .left claimC .w1 ∧ Warranted model lax .left claimC .w1 := by
  have stricter : strict.Stricter lax :=
    ⟨by decide, fun _ h => h, fun _ h => h, rfl, le_rfl⟩
  have strictWarrant : Warranted model strict .left claimC .w1 := by decide +kernel
  refine ⟨strictWarrant, stricter_directional stricter ?_ strictWarrant⟩
  intro x hxP hxQ anc
  have attackers : ∀ y, Ancestor (model.underProfile lax .left) 1 y → y = 1 := by
    intro y hy
    induction hy with
    | self => rfl
    | attacker _ _ hxy ih => subst ih; revert hxy; decide +revert
  have := attackers x anc
  subst this
  exact hxQ (by decide +kernel)

end Lara.Examples.ProcessEntitlement
