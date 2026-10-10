import Lara.Process.Verdict

/-!
The compositional three-valued evaluator and its soundness.

The reference verdict is supervaluational: it quantifies over every compatible
history. A checker may instead evaluate a formula compositionally, combining
the verdicts of its atoms with strong Kleene connectives. That evaluator is
cheaper but incomplete: it loses classical truths such as `p ∨ ¬p` for an
undetermined `p` (`Lara.Examples.ProcessCore.kleene_incomplete`).
`kleene_sound` proves it never contradicts the reference, and its empty-set
check takes precedence over every atom value.
-/

namespace Lara.Process

universe u v

/-- Propositional formulas over atoms. -/
inductive Formula (Atom : Type v) where
  | atom (a : Atom)
  | neg (f : Formula Atom)
  | conj (f g : Formula Atom)
  | disj (f g : Formula Atom)
  deriving DecidableEq, Repr

variable {X : Type u} {Atom : Type v}

/-- Classical satisfaction of a formula at one complete history. -/
def Formula.holds (val : Atom → X → Prop) : Formula Atom → X → Prop
  | .atom a, x => val a x
  | .neg f, x => ¬ f.holds val x
  | .conj f g, x => f.holds val x ∧ g.holds val x
  | .disj f g, x => f.holds val x ∨ g.holds val x

/-- Satisfaction is decidable when every atom is. -/
@[reducible] def Formula.decHolds (val : Atom → X → Prop) [∀ a, DecidablePred (val a)] :
    (f : Formula Atom) → DecidablePred (f.holds val)
  | .atom a => fun x => inferInstanceAs (Decidable (val a x))
  | .neg f => fun x => @instDecidableNot _ (f.decHolds val x)
  | .conj f g => fun x => @instDecidableAnd _ _ (f.decHolds val x) (g.decHolds val x)
  | .disj f g => fun x => @instDecidableOr _ _ (f.decHolds val x) (g.decHolds val x)

instance (val : Atom → X → Prop) [∀ a, DecidablePred (val a)] (f : Formula Atom) :
    DecidablePred (f.holds val) := f.decHolds val

/-- Strong Kleene values: `some b` is determined, `none` is undetermined. -/
abbrev K3 := Option Bool

def K3.not : K3 → K3
  | some b => some (!b)
  | none => none

def K3.and : K3 → K3 → K3
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

def K3.or : K3 → K3 → K3
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- Compositional evaluation from a three-valued atom valuation. -/
def Formula.kleene (atomV : Atom → K3) : Formula Atom → K3
  | .atom a => atomV a
  | .neg f => (f.kleene atomV).not
  | .conj f g => (f.kleene atomV).and (g.kleene atomV)
  | .disj f g => (f.kleene atomV).or (g.kleene atomV)

/-- An atom valuation is sound for a compatible set when every determined atom
value holds at every compatible history. -/
def AtomSound (compat : X → Prop) (val : Atom → X → Prop) (atomV : Atom → K3) : Prop :=
  ∀ a b, atomV a = some b → ∀ x, compat x → (val a x ↔ b = true)

/-- A determined compositional value is the classical value at every compatible
history. -/
theorem kleene_value_sound {compat : X → Prop} {val : Atom → X → Prop} {atomV : Atom → K3}
    (sound : AtomSound compat val atomV) :
    ∀ (f : Formula Atom) b, f.kleene atomV = some b → ∀ x, compat x → (f.holds val x ↔ b = true)
  | .atom a, b, h, x, hx => sound a b h x hx
  | .neg f, b, h, x, hx => by
      simp only [Formula.kleene] at h
      cases hf : f.kleene atomV with
      | none => rw [hf] at h; cases h
      | some c =>
          rw [hf] at h
          simp only [K3.not, Option.some.injEq] at h
          subst h
          have ih := kleene_value_sound sound f c hf x hx
          simp only [Formula.holds, ih]
          cases c <;> simp
  | .conj f g, b, h, x, hx => by
      simp only [Formula.kleene] at h
      have ihf := kleene_value_sound sound f
      have ihg := kleene_value_sound sound g
      cases hf : f.kleene atomV with
      | none =>
          cases hg : g.kleene atomV with
          | none => rw [hf, hg] at h; cases h
          | some c =>
              cases c with
              | false =>
                  rw [hf, hg] at h
                  simp only [K3.and, Option.some.injEq] at h
                  subst h
                  simp [Formula.holds, ihg false hg x hx]
              | true => rw [hf, hg] at h; cases h
      | some c =>
          cases c with
          | false =>
              rw [hf] at h
              simp only [K3.and, Option.some.injEq] at h
              subst h
              simp [Formula.holds, ihf false hf x hx]
          | true =>
              cases hg : g.kleene atomV with
              | none => rw [hf, hg] at h; cases h
              | some d =>
                  rw [hf, hg] at h
                  cases d <;> simp only [K3.and, Option.some.injEq] at h <;> subst h <;>
                    simp [Formula.holds, ihf true hf x hx, ihg _ hg x hx]
  | .disj f g, b, h, x, hx => by
      simp only [Formula.kleene] at h
      have ihf := kleene_value_sound sound f
      have ihg := kleene_value_sound sound g
      cases hf : f.kleene atomV with
      | none =>
          cases hg : g.kleene atomV with
          | none => rw [hf, hg] at h; cases h
          | some c =>
              cases c with
              | true =>
                  rw [hf, hg] at h
                  simp only [K3.or, Option.some.injEq] at h
                  subst h
                  simp [Formula.holds, ihg true hg x hx]
              | false => rw [hf, hg] at h; cases h
      | some c =>
          cases c with
          | true =>
              rw [hf] at h
              simp only [K3.or, Option.some.injEq] at h
              subst h
              simp [Formula.holds, ihf true hf x hx]
          | false =>
              cases hg : g.kleene atomV with
              | none => rw [hf, hg] at h; cases h
              | some d =>
                  rw [hf, hg] at h
                  cases d <;> simp only [K3.or, Option.some.injEq] at h <;> subst h <;>
                    simp [Formula.holds, ihf false hf x hx, ihg _ hg x hx]

/-- The Kleene verdict: the empty-set check first, then the compositional value. -/
noncomputable def kleeneVerdict (compat : X → Prop) (atomV : Atom → K3) (f : Formula Atom) :
    Verdict := by
  classical
  exact
    if ¬ ∃ x, compat x then .inconsistent
    else match f.kleene atomV with
      | some true => .certainTrue
      | some false => .certainFalse
      | none => .unknown

/-- Soundness against supervaluation: whenever the Kleene verdict is not
`unknown`, the reference verdict is the same. -/
theorem kleene_sound {compat : X → Prop} {val : Atom → X → Prop} {atomV : Atom → K3}
    (sound : AtomSound compat val atomV) (f : Formula Atom) {v : Verdict}
    (hv : kleeneVerdict compat atomV f = v) (known : v ≠ .unknown) :
    verdictOf compat (f.holds val) = v := by
  unfold kleeneVerdict at hv
  by_cases e : ∃ x, compat x
  · rw [if_neg (not_not.mpr e)] at hv
    cases hk : f.kleene atomV with
    | none => rw [hk] at hv; exact absurd hv.symm known
    | some b =>
        rw [hk] at hv
        have values := kleene_value_sound sound f b hk
        cases b
        · subst hv
          exact (verdictOf_certainFalse_iff _ _).mpr
            ⟨e, fun x hx px => by simpa using (values x hx).mp px⟩
        · subst hv
          exact (verdictOf_certainTrue_iff _ _).mpr ⟨e, fun x hx => (values x hx).mpr rfl⟩
  · rw [if_pos e] at hv
    subst hv
    exact (verdictOf_inconsistent_iff _ _).mpr e

/-- The Kleene evaluator is conservative for the reference verdict. -/
theorem kleene_conservative {compat : X → Prop} {val : Atom → X → Prop} {atomV : Atom → K3}
    (sound : AtomSound compat val atomV) (f : Formula Atom) :
    ConservativeFor (kleeneVerdict compat atomV f) (verdictOf compat (f.holds val)) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun known => (kleene_sound sound f rfl known).symm⟩
  · exact kleene_sound sound f h (by simp)
  · have empty := (verdictOf_inconsistent_iff _ _).mp h
    unfold kleeneVerdict
    rw [if_pos empty]

/-- The atom valuation read off the reference verdict of each atom. -/
noncomputable def referenceAtoms (compat : X → Prop) (val : Atom → X → Prop) : Atom → K3 :=
  fun a => match verdictOf compat (val a) with
    | .certainTrue => some true
    | .certainFalse => some false
    | _ => none

theorem referenceAtoms_sound (compat : X → Prop) (val : Atom → X → Prop) :
    AtomSound compat val (referenceAtoms compat val) := by
  intro a b h x hx
  unfold referenceAtoms at h
  cases hv : verdictOf compat (val a) <;> rw [hv] at h <;> simp only [reduceCtorEq] at h
  · simp only [Option.some.injEq] at h
    subst h
    simpa using verdict_sound hv x hx
  · simp only [Option.some.injEq] at h
    subst h
    simpa using verdict_sound_false hv x hx

/-! ### Executable evaluator over a declared finite carrier -/

section Finite

variable [Fintype X] (compat : X → Prop) [DecidablePred compat]

/-- The executable atom valuation: each atom's own finite verdict. -/
def finiteAtoms (val : Atom → X → Prop) [∀ a, DecidablePred (val a)] : Atom → K3 :=
  fun a => match verdict compat (val a) with
    | .certainTrue => some true
    | .certainFalse => some false
    | _ => none

theorem finiteAtoms_eq (val : Atom → X → Prop) [∀ a, DecidablePred (val a)] :
    finiteAtoms compat val = referenceAtoms compat val := by
  funext a
  simp only [finiteAtoms, referenceAtoms, verdict_eq_verdictOf]

/-- The executable Kleene verdict. -/
def kleeneVerdictFinite (atomV : Atom → K3) (f : Formula Atom) : Verdict :=
  if ¬ ∃ x, compat x then .inconsistent
  else match f.kleene atomV with
    | some true => .certainTrue
    | some false => .certainFalse
    | none => .unknown

theorem kleeneVerdictFinite_eq (atomV : Atom → K3) (f : Formula Atom) :
    kleeneVerdictFinite compat atomV f = kleeneVerdict compat atomV f := by
  unfold kleeneVerdictFinite kleeneVerdict
  by_cases e : ∃ x, compat x
  · rw [if_neg (not_not.mpr e), if_neg (not_not.mpr e)]
  · rw [if_pos e, if_pos e]

end Finite

end Lara.Process
