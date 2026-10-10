import Lara.Process.Contract

/-!
R1: the compatible-history core.

Every result here is a law of the four-valued verdict over a compatibility
predicate. It is the incomplete-database notion of certain answers, moved from
tables to research histories: `certainTrue` means the property holds in every
compatible history *and* there is one. The nonemptiness guard is part of every
positive law, because supervaluation over an empty set certifies everything
(`Lara.Examples.ProcessFalseLaws.empty_compatible_vacuous`).

The laws are stated for the classical reference `verdictOf` over an arbitrary
carrier; `verdict_eq_verdictOf` transfers them to the executable `verdict`.
-/

namespace Lara.Process

universe u v w

variable {X : Type u}

/-! ### Exact characterization of each verdict -/

section Characterization

variable (compat φ : X → Prop)

/-- The four branches of the reference verdict, one per case. -/
theorem verdictOf_cases :
    ((¬ ∃ x, compat x) → verdictOf compat φ = .inconsistent) ∧
    ((∃ x, compat x) → (∀ x, compat x → φ x) → verdictOf compat φ = .certainTrue) ∧
    ((∃ x, compat x) → ¬ (∀ x, compat x → φ x) → (∀ x, compat x → ¬ φ x) →
      verdictOf compat φ = .certainFalse) ∧
    ((∃ x, compat x) → ¬ (∀ x, compat x → φ x) → ¬ (∀ x, compat x → ¬ φ x) →
      verdictOf compat φ = .unknown) := by
  unfold verdictOf
  refine ⟨fun e => if_pos e, fun e t => ?_, fun e t f => ?_, fun e t f => ?_⟩
  · rw [if_neg (not_not.mpr e), if_pos t]
  · rw [if_neg (not_not.mpr e), if_neg t, if_pos f]
  · rw [if_neg (not_not.mpr e), if_neg t, if_neg f]

theorem verdictOf_inconsistent_iff :
    verdictOf compat φ = .inconsistent ↔ ¬ ∃ x, compat x := by
  obtain ⟨c₀, c₁, c₂, c₃⟩ := verdictOf_cases compat φ
  refine ⟨fun h e => ?_, c₀⟩
  by_cases t : ∀ x, compat x → φ x
  · rw [c₁ e t] at h; cases h
  · by_cases f : ∀ x, compat x → ¬ φ x
    · rw [c₂ e t f] at h; cases h
    · rw [c₃ e t f] at h; cases h

theorem verdictOf_certainTrue_iff :
    verdictOf compat φ = .certainTrue ↔ (∃ x, compat x) ∧ ∀ x, compat x → φ x := by
  obtain ⟨c₀, c₁, c₂, c₃⟩ := verdictOf_cases compat φ
  refine ⟨fun h => ?_, fun ⟨e, t⟩ => c₁ e t⟩
  by_cases e : ∃ x, compat x
  · by_cases t : ∀ x, compat x → φ x
    · exact ⟨e, t⟩
    · by_cases f : ∀ x, compat x → ¬ φ x
      · rw [c₂ e t f] at h; cases h
      · rw [c₃ e t f] at h; cases h
  · rw [c₀ e] at h; cases h

theorem verdictOf_certainFalse_iff :
    verdictOf compat φ = .certainFalse ↔ (∃ x, compat x) ∧ ∀ x, compat x → ¬ φ x := by
  obtain ⟨c₀, c₁, c₂, c₃⟩ := verdictOf_cases compat φ
  constructor
  · intro h
    by_cases e : ∃ x, compat x
    · by_cases t : ∀ x, compat x → φ x
      · rw [c₁ e t] at h; cases h
      · by_cases f : ∀ x, compat x → ¬ φ x
        · exact ⟨e, f⟩
        · rw [c₃ e t f] at h; cases h
    · rw [c₀ e] at h; cases h
  · rintro ⟨⟨x, hx⟩, f⟩
    exact c₂ ⟨x, hx⟩ (fun t => f x hx (t x hx)) f

theorem verdictOf_unknown_iff :
    verdictOf compat φ = .unknown ↔ ∃ x y, compat x ∧ compat y ∧ φ x ∧ ¬ φ y := by
  obtain ⟨c₀, c₁, c₂, c₃⟩ := verdictOf_cases compat φ
  constructor
  · intro h
    by_cases e : ∃ x, compat x
    · by_cases t : ∀ x, compat x → φ x
      · rw [c₁ e t] at h; cases h
      · by_cases f : ∀ x, compat x → ¬ φ x
        · rw [c₂ e t f] at h; cases h
        · push Not at t f
          obtain ⟨y, hy, hny⟩ := t
          obtain ⟨x, hx, hpx⟩ := f
          exact ⟨x, y, hx, hy, hpx, hny⟩
    · rw [c₀ e] at h; cases h
  · rintro ⟨x, y, hx, hy, hpx, hny⟩
    exact c₃ ⟨x, hx⟩ (fun t => hny (t y hy)) (fun f => f x hx hpx)

end Characterization

/-- The executable verdict agrees with the classical reference. -/
theorem verdict_eq_verdictOf [Fintype X] (compat : X → Prop) [DecidablePred compat]
    (φ : X → Prop) [DecidablePred φ] : verdict compat φ = verdictOf compat φ := by
  obtain ⟨c₀, c₁, c₂, c₃⟩ := verdictOf_cases compat φ
  unfold verdict
  by_cases e : ∃ x, compat x
  · rw [if_neg (not_not.mpr e)]
    by_cases t : ∀ x, compat x → φ x
    · rw [if_pos t, c₁ e t]
    · rw [if_neg t]
      by_cases f : ∀ x, compat x → ¬ φ x
      · rw [if_pos f, c₂ e t f]
      · rw [if_neg f, c₃ e t f]
  · rw [if_pos e, c₀ e]

/-! ### Soundness and non-vacuity -/

section Laws

variable {compat φ : X → Prop}

/-- `certainTrue` implies the property at every compatible history. -/
theorem verdict_sound (h : verdictOf compat φ = .certainTrue) : ∀ x, compat x → φ x :=
  ((verdictOf_certainTrue_iff compat φ).mp h).2

/-- `certainFalse` refutes the property at every compatible history. -/
theorem verdict_sound_false (h : verdictOf compat φ = .certainFalse) :
    ∀ x, compat x → ¬ φ x :=
  ((verdictOf_certainFalse_iff compat φ).mp h).2

/-- A positive verdict is never vacuous: some history is compatible. -/
theorem positive_needs_nonempty
    (h : verdictOf compat φ = .certainTrue ∨ verdictOf compat φ = .certainFalse) :
    ∃ x, compat x := by
  rcases h with h | h
  · exact ((verdictOf_certainTrue_iff compat φ).mp h).1
  · exact ((verdictOf_certainFalse_iff compat φ).mp h).1

/-- A verdict is *determinate* when it is `certainTrue` or `certainFalse`. -/
def Determinate (v : Verdict) : Prop := v = .certainTrue ∨ v = .certainFalse

instance (v : Verdict) : Decidable (Determinate v) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Refinement: if the refined record's compatible set is contained in the
original's and is nonempty, a determinate verdict transfers. Without
nonemptiness the refined verdict is `inconsistent`. -/
theorem certain_refine {compat' : X → Prop} (sub : ∀ x, compat' x → compat x)
    (nonempty : ∃ x, compat' x) {v : Verdict} (hv : verdictOf compat φ = v)
    (det : Determinate v) : verdictOf compat' φ = v := by
  rcases det with rfl | rfl
  · exact (verdictOf_certainTrue_iff compat' φ).mpr
      ⟨nonempty, fun x hx => verdict_sound hv x (sub x hx)⟩
  · exact (verdictOf_certainFalse_iff compat' φ).mpr
      ⟨nonempty, fun x hx => verdict_sound_false hv x (sub x hx)⟩

/-- Determinacy is exactly nonemptiness plus the absence of a disagreeing pair:
the 2-safety reading of "the record determines φ". -/
theorem determined_iff_no_witness :
    Determinate (verdictOf compat φ) ↔
      (∃ x, compat x) ∧ ∀ x y, compat x → compat y → (φ x ↔ φ y) := by
  constructor
  · intro det
    refine ⟨positive_needs_nonempty det, fun x y hx hy => ?_⟩
    rcases det with h | h
    · exact iff_of_true (verdict_sound h x hx) (verdict_sound h y hy)
    · exact iff_of_false (verdict_sound_false h x hx) (verdict_sound_false h y hy)
  · rintro ⟨⟨x₀, h₀⟩, agree⟩
    by_cases p : φ x₀
    · exact Or.inl ((verdictOf_certainTrue_iff compat φ).mpr
        ⟨⟨x₀, h₀⟩, fun x hx => (agree x₀ x h₀ hx).mp p⟩)
    · exact Or.inr ((verdictOf_certainFalse_iff compat φ).mpr
        ⟨⟨x₀, h₀⟩, fun x hx px => p ((agree x₀ x h₀ hx).mpr px)⟩)

/-- A realized record whose compatible histories all agree with its generating
history `x₀` on `φ` has the verdict of `φ x₀`. This is the shape of every
conservativity result: complete observation of the inputs `φ` reads. -/
theorem verdict_of_generator {x₀ : X} (realized : compat x₀)
    (determines : ∀ x, compat x → (φ x ↔ φ x₀)) :
    (verdictOf compat φ = .certainTrue ↔ φ x₀) ∧
      (verdictOf compat φ = .certainFalse ↔ ¬ φ x₀) := by
  constructor
  · rw [verdictOf_certainTrue_iff]
    exact ⟨fun h => h.2 x₀ realized, fun p => ⟨⟨x₀, realized⟩, fun x hx => (determines x hx).mpr p⟩⟩
  · rw [verdictOf_certainFalse_iff]
    exact ⟨fun h => h.2 x₀ realized,
      fun p => ⟨⟨x₀, realized⟩, fun x hx px => p ((determines x hx).mp px)⟩⟩

/-- A property that does not depend on the history gets the verdict of its
constant truth value on every consistent record: the layer agrees with the core
on claims that do not read history. -/
theorem history_independent_verdict {P : Prop} (nonempty : ∃ x, compat x) :
    (verdictOf compat (fun _ => P) = .certainTrue ↔ P) ∧
      (verdictOf compat (fun _ => P) = .certainFalse ↔ ¬ P) := by
  obtain ⟨x₀, h₀⟩ := nonempty
  exact verdict_of_generator h₀ (fun _ _ => Iff.rfl)

end Laws

/-! ### Conservative evaluators -/

/-- An evaluator's verdict `ev` is conservative for the reference verdict `ref`
when it reports inconsistency exactly when the reference does and every other
answer is either the reference's or `unknown`. A conservative evaluator may
refuse certification, but never confuses uncertainty with inconsistency. -/
def ConservativeFor (ev ref : Verdict) : Prop :=
  (ev = .inconsistent ↔ ref = .inconsistent) ∧ (ev ≠ .unknown → ev = ref)

theorem conservativeFor_refl (v : Verdict) : ConservativeFor v v :=
  ⟨Iff.rfl, fun _ => rfl⟩

/-- The evaluator that always refuses, except on inconsistent records. -/
def refuse (ref : Verdict) : Verdict :=
  if ref = .inconsistent then .inconsistent else .unknown

theorem refuse_conservative (ref : Verdict) : ConservativeFor (refuse ref) ref := by
  unfold refuse ConservativeFor
  by_cases h : ref = .inconsistent
  · simp [h]
  · simp [h]

/-! ### Assumptions and observations -/

section Process

variable {H : Type u} {Rho : Type v} {R : Type w}

instance (h : H) : DecidablePred ((Assumptions.trivial : Assumptions H Rho).Allowed h) :=
  fun _ => isTrue True.intro

instance (A B : Assumptions H Rho) [∀ h, DecidablePred (A.Allowed h)]
    [∀ h, DecidablePred (B.Allowed h)] (h : H) : DecidablePred ((A.and B).Allowed h) :=
  fun rho => inferInstanceAs (Decidable (A.Allowed h rho ∧ B.Allowed h rho))

/-- Stronger admitted assumptions shrink the compatible set; a determinate
verdict under weaker assumptions transfers only when the stronger set is still
nonempty. -/
theorem certain_weaken_assumption (M : ProcessModel H Rho R) {A B : Assumptions H Rho}
    (stronger : A.Stronger B) {r : R} (nonempty : ∃ x, Compatible M A r x)
    {φ : H × Rho → Prop} {v : Verdict} (hv : verdictOf (Compatible M B r) φ = v)
    (det : Determinate v) : verdictOf (Compatible M A r) φ = v :=
  certain_refine (fun _ ⟨valid, allowed, report⟩ => ⟨valid, stronger _ _ allowed, report⟩)
    nonempty hv det

/-- The record semantics of an observation function on valid histories. -/
def observes (valid : X → Prop) (obs : X → R) (r : R) (x : X) : Prop :=
  valid x ∧ obs x = r

/-- Factoring: if the coarse observation is a function `g` of a finer one, a
determinate coarse verdict transfers to every realized finer observation. -/
theorem certain_factor {R₁ : Type v} {R₂ : Type w} {valid : X → Prop}
    {obs₁ : X → R₁} {obs₂ : X → R₂} {g : R₂ → R₁} (factor : ∀ x, obs₁ x = g (obs₂ x))
    {r₂ : R₂} (realized : ∃ x, observes valid obs₂ r₂ x) {φ : X → Prop} {v : Verdict}
    (hv : verdictOf (observes valid obs₁ (g r₂)) φ = v) (det : Determinate v) :
    verdictOf (observes valid obs₂ r₂) φ = v :=
  certain_refine (fun x ⟨hvalid, hobs⟩ => ⟨hvalid, by rw [factor, hobs]⟩) realized hv det

/-- `φ` factors through the observation on valid histories. -/
def Factors (valid : X → Prop) (obs : X → R) (φ : X → Prop) : Prop :=
  ∀ x y, valid x → valid y → obs x = obs y → (φ x ↔ φ y)

/-- Naive evaluation: an exact evaluator reading only the record exists iff `φ`
factors through the observation on realizable records. -/
theorem naive_sound_iff_factors (valid : X → Prop) (obs : X → R) (φ : X → Prop) :
    (∃ f : R → Bool, ∀ x, valid x → (f (obs x) = true ↔ φ x)) ↔ Factors valid obs φ := by
  classical
  constructor
  · rintro ⟨f, hf⟩ x y hx hy hobs
    rw [← hf x hx, ← hf y hy, hobs]
  · intro fac
    refine ⟨fun r => decide (∃ x, valid x ∧ obs x = r ∧ φ x), fun x hx => ?_⟩
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨y, hy, hobs, py⟩
      exact (fac y x hy hx hobs).mp py
    · exact fun px => ⟨x, hx, rfl, px⟩

/-- Equivalently, `φ` factors exactly when every realizable record gets a
determinate verdict. -/
theorem factors_iff_determinate (valid : X → Prop) (obs : X → R) (φ : X → Prop) :
    Factors valid obs φ ↔
      ∀ r, (∃ x, observes valid obs r x) → Determinate (verdictOf (observes valid obs r) φ) := by
  constructor
  · intro fac r realized
    refine (determined_iff_no_witness).mpr ⟨realized, fun x y hx hy => ?_⟩
    exact fac x y hx.1 hy.1 (hx.2.trans hy.2.symm)
  · intro det x y hx hy hobs
    have d := (determined_iff_no_witness).mp (det (obs x) ⟨x, hx, rfl⟩)
    exact d.2 x y ⟨hx, rfl⟩ ⟨hy, hobs.symm⟩

end Process

/-! ### Record-semantics wrappers -/

namespace RecordSemantics

variable {R : Type v}

/-- The reference verdict of a record under a record semantics. -/
noncomputable def verdictOf (S : RecordSemantics X R) (r : R) (φ : X → Prop) : Verdict :=
  Lara.Process.verdictOf (S.compat r) φ

/-- The executable verdict of a record under a record semantics. -/
def verdict [Fintype X] (S : RecordSemantics X R) [∀ r, DecidablePred (S.compat r)]
    (r : R) (φ : X → Prop) [DecidablePred φ] : Verdict :=
  Lara.Process.verdict (S.compat r) φ

theorem verdict_eq_verdictOf [Fintype X] (S : RecordSemantics X R)
    [∀ r, DecidablePred (S.compat r)] (r : R) (φ : X → Prop) [DecidablePred φ] :
    S.verdict r φ = S.verdictOf r φ :=
  Lara.Process.verdict_eq_verdictOf _ _

end RecordSemantics

end Lara.Process
