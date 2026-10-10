import Lara.Process.Order

/-!
A Hennessy–Milner characterization for process histories.

Histories evolve by appending events, and each history has atomic facts chosen
by the user of the theory; the intended choice is the warrant, order and
statistical predicates an entitlement verdict reads, but the results hold for
any atoms. Profile formulas combine atoms with truth, negation, conjunction and
a possibility modality over one more event. Two histories are
*formula-equivalent* when no formula separates them; with entitlement-relevant
atoms this is the plan's entitlement equivalence. Nothing here shows that an
entitlement verdict depends only on these formulas.

For image-finite systems, where each state has finitely many successors per
label, formula equivalence is exactly bisimilarity
(`formulaEquivalent_iff_bisimilar`). Process histories step deterministically
(appending one event gives at most one successor), so they are image-finite for
any alphabet (`processSystem_imageFinite`), and the characterization applies
(`process_characterization`). For such deterministic systems the result is
close to the standard Hennessy–Milner theorem.
-/

namespace Lara.Process

universe u v w

/-- A labelled transition system with atomic predicates. -/
structure TransitionSystem (S : Type u) (L : Type v) (A : Type w) where
  step : S → L → S → Prop
  atom : A → S → Prop

/-- Profile formulas: atoms, truth, negation, conjunction and possibility after
one labelled step. -/
inductive ProfileFormula (L : Type v) (A : Type w) where
  | tt
  | atom (a : A)
  | neg (φ : ProfileFormula L A)
  | conj (φ ψ : ProfileFormula L A)
  | dia (l : L) (φ : ProfileFormula L A)

variable {S : Type u} {L : Type v} {A : Type w}

/-- Satisfaction of a profile formula at a state. -/
def ProfileFormula.sat (M : TransitionSystem S L A) : ProfileFormula L A → S → Prop
  | .tt, _ => True
  | .atom a, s => M.atom a s
  | .neg φ, s => ¬ φ.sat M s
  | .conj φ ψ, s => φ.sat M s ∧ ψ.sat M s
  | .dia l φ, s => ∃ s', M.step s l s' ∧ φ.sat M s'

/-- No profile formula separates the two states. -/
def FormulaEquivalent (M : TransitionSystem S L A) (s t : S) : Prop :=
  ∀ φ : ProfileFormula L A, φ.sat M s ↔ φ.sat M t

/-- A bisimulation: related states agree on atoms and match each other's
labelled steps into related states. -/
def IsBisimulation (M : TransitionSystem S L A) (B : S → S → Prop) : Prop :=
  ∀ s t, B s t → (∀ a, M.atom a s ↔ M.atom a t) ∧
    (∀ l s', M.step s l s' → ∃ t', M.step t l t' ∧ B s' t') ∧
    (∀ l t', M.step t l t' → ∃ s', M.step s l s' ∧ B s' t')

def Bisimilar (M : TransitionSystem S L A) (s t : S) : Prop :=
  ∃ B, IsBisimulation M B ∧ B s t

/-- Every state is bisimilar to itself. -/
theorem bisimilar_refl (M : TransitionSystem S L A) (s : S) : Bisimilar M s s :=
  ⟨Eq, fun s t h => by subst h; exact ⟨fun _ => Iff.rfl, fun _ s' st => ⟨s', st, rfl⟩,
    fun _ t' st => ⟨t', st, rfl⟩⟩, rfl⟩

/-- Image-finiteness: the successors of each state under each label form a
finite list. -/
structure ImageFinite (M : TransitionSystem S L A) where
  succ : S → L → List S
  spec : ∀ s l s', M.step s l s' ↔ s' ∈ succ s l

/-- Bisimilar states satisfy the same profile formulas. -/
theorem bisimilar_sat {M : TransitionSystem S L A} {B : S → S → Prop} (bisim : IsBisimulation M B) :
    ∀ (φ : ProfileFormula L A) s t, B s t → (φ.sat M s ↔ φ.sat M t)
  | .tt, _, _, _ => Iff.rfl
  | .atom a, s, t, h => (bisim s t h).1 a
  | .neg φ, s, t, h => not_congr (bisimilar_sat bisim φ s t h)
  | .conj φ ψ, s, t, h => and_congr (bisimilar_sat bisim φ s t h) (bisimilar_sat bisim ψ s t h)
  | .dia l φ, s, t, h => by
      constructor
      · rintro ⟨s', step, sat⟩
        obtain ⟨t', step', rel⟩ := (bisim s t h).2.1 l s' step
        exact ⟨t', step', (bisimilar_sat bisim φ s' t' rel).mp sat⟩
      · rintro ⟨t', step, sat⟩
        obtain ⟨s', step', rel⟩ := (bisim s t h).2.2 l t' step
        exact ⟨s', step', (bisimilar_sat bisim φ s' t' rel).mpr sat⟩

theorem bisimilar_formulaEquivalent {M : TransitionSystem S L A} {s t : S}
    (h : Bisimilar M s t) : FormulaEquivalent M s t := by
  obtain ⟨B, bisim, rel⟩ := h
  exact fun φ => bisimilar_sat bisim φ s t rel

/-- One formula true at `s'` and false at every listed state, when each listed
state is separated from `s'` by some formula. -/
theorem separating_conjunction {M : TransitionSystem S L A} {s' : S} :
    ∀ ts : List S, (∀ t ∈ ts, ∃ ψ : ProfileFormula L A, ψ.sat M s' ∧ ¬ ψ.sat M t) →
      ∃ Ψ : ProfileFormula L A, Ψ.sat M s' ∧ ∀ t ∈ ts, ¬ Ψ.sat M t
  | [], _ => ⟨.tt, trivial, fun _ h => absurd h (List.not_mem_nil)⟩
  | t :: ts, sep => by
      obtain ⟨ψ, yes, no⟩ := sep t List.mem_cons_self
      obtain ⟨Ψ, yes', no'⟩ := separating_conjunction ts fun t' ht' => sep t' (List.mem_cons_of_mem _ ht')
      refine ⟨.conj ψ Ψ, ⟨yes, yes'⟩, fun t'' ht'' sat => ?_⟩
      rcases List.mem_cons.mp ht'' with rfl | mem
      · exact no sat.1
      · exact no' t'' mem sat.2

/-- A step of one state is matched by a formula-equivalent step of any
formula-equivalent state, in an image-finite system. -/
theorem formulaEquivalent_forth {M : TransitionSystem S L A} (fin : ImageFinite M) {s t : S}
    (eqv : FormulaEquivalent M s t) {l : L} {s' : S} (step : M.step s l s') :
    ∃ t', M.step t l t' ∧ FormulaEquivalent M s' t' := by
  classical
  by_contra none
  push Not at none
  have sep : ∀ t' ∈ fin.succ t l, ∃ ψ : ProfileFormula L A, ψ.sat M s' ∧ ¬ ψ.sat M t' := by
    intro t' mem
    have notEq := none t' ((fin.spec t l t').mpr mem)
    unfold FormulaEquivalent at notEq
    push Not at notEq
    obtain ⟨φ, diff⟩ := notEq
    rcases diff with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact ⟨φ, hs, ht⟩
    · exact ⟨.neg φ, hs, fun h => h ht⟩
  obtain ⟨Ψ, yes, no⟩ := separating_conjunction (fin.succ t l) sep
  have atS : (ProfileFormula.dia l Ψ).sat M s := ⟨s', step, yes⟩
  obtain ⟨t', step', sat⟩ := (eqv (.dia l Ψ)).mp atS
  exact no t' ((fin.spec t l t').mp step') sat

/-- In an image-finite system, formula equivalence is a bisimulation. -/
theorem formulaEquivalent_isBisimulation {M : TransitionSystem S L A} (fin : ImageFinite M) :
    IsBisimulation M (FormulaEquivalent M) := by
  intro s t eqv
  refine ⟨fun a => eqv (.atom a), fun l s' step => formulaEquivalent_forth fin eqv step,
    fun l t' step => ?_⟩
  obtain ⟨s', step', eqv'⟩ := formulaEquivalent_forth fin (fun φ => (eqv φ).symm) step
  exact ⟨s', step', fun φ => (eqv' φ).symm⟩

/-- Hennessy–Milner: in an image-finite system, two states are
formula-equivalent iff they are bisimilar. -/
theorem formulaEquivalent_iff_bisimilar {M : TransitionSystem S L A} (fin : ImageFinite M)
    (s t : S) : FormulaEquivalent M s t ↔ Bisimilar M s t :=
  ⟨fun eqv => ⟨_, formulaEquivalent_isBisimulation fin, eqv⟩, bisimilar_formulaEquivalent⟩

/-! ### Process histories -/

/-- Process histories over an event alphabet: a history steps by an event of the
alphabet to its valid one-event extension. Atoms are any predicates on
histories, intended to be warrant, order and statistical predicates. -/
def processSystem {A : Type w} (alphabet : List Stamped) (atoms : A → ProcessHistory → Prop) :
    TransitionSystem ProcessHistory Stamped A where
  step h e h' := e ∈ alphabet ∧ h' = h ++ [e] ∧ ValidHistory h'
  atom := atoms

/-- Process histories are image-finite: appending one event gives at most one
successor per label. -/
def processSystem_imageFinite {A : Type w} (alphabet : List Stamped)
    (atoms : A → ProcessHistory → Prop) : ImageFinite (processSystem alphabet atoms) where
  succ h e := if e ∈ alphabet ∧ ValidHistory (h ++ [e]) then [h ++ [e]] else []
  spec h e h' := by
    simp only [processSystem]
    constructor
    · rintro ⟨mem, rfl, valid⟩
      simp [mem, valid]
    · intro mem
      split at mem
      · rename_i cond
        simp only [List.mem_singleton] at mem
        subst mem
        exact ⟨cond.1, rfl, cond.2⟩
      · simp at mem

/-- The characterization for process histories: two histories are
formula-equivalent iff they are bisimilar. -/
theorem process_characterization {A : Type w} (alphabet : List Stamped)
    (atoms : A → ProcessHistory → Prop) (h h' : ProcessHistory) :
    FormulaEquivalent (processSystem alphabet atoms) h h' ↔
      Bisimilar (processSystem alphabet atoms) h h' :=
  formulaEquivalent_iff_bisimilar (processSystem_imageFinite alphabet atoms) h h'

end Lara.Process
