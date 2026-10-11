import Lara.Process.Bridge
import Lara.Process.Kleene
import Lara.Process.Entitlement
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Dedup

/-!
The declared universe carrier of the `process-input 1` contract.

`verdict` quantifies over a declared finite carrier. For a decoded record that
nobody hand-modeled, the carrier comes from a declared *universe*: a finite list
of events that may have happened without being recorded. The completions of a
record over a universe are exactly the duplicate-free histories that are
compatible with the extracted record and contain only recorded or universe
events (`mem_completions`). Declaring the universe is a modeling assumption; an
empty universe asserts that nothing unrecorded happened.

* `mem_completions`: the exact characterization of the enumerated completions.
* `completions_mono`, `certain_antitone_universe`: a larger universe gives more
  completions, so a verdict can only lose certainty.
* `answerVerdict_eq_verdict`: over the candidate carrier, the reported verdict
  is the landed `verdict` of the record's compatibility predicate, so the wire
  layer adds no second semantics.
* `answer_witnesses`: an `unknown` answer names one completion where the
  formula holds and one where it fails.
* `auditHolds_iff`: an audit is `ArgumentEntitledBy` over the completions, with
  the profile accepting every admitted coverage assertion.

The enumerator here is the plain reference one: sublists of the universe,
interleaved with the recorded events by permutation, then filtered. It is meant
to be obviously correct on small inputs, not fast.
-/

namespace Lara.Process.Universe

open Lara.Process

/-! ### Permutations by structural recursion

`List.permutations` is defined by well-founded recursion, which the kernel does
not reduce, so the reference enumerator uses this structural version and small
fixtures stay checkable by `decide`. -/

/-- Every way to insert `x` into a list. -/
def interleave {α : Type} (x : α) : List α → List (List α)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (interleave x ys).map (y :: ·)

/-- Every ordering of a list. -/
def perms {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap (interleave x)

theorem mem_interleave {α : Type} (x : α) :
    ∀ (ys l : List α), l ∈ interleave x ys ↔ ∃ a b, ys = a ++ b ∧ l = a ++ x :: b
  | [], l => by
    simp only [interleave, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨[], [], rfl, rfl⟩
    · rintro ⟨a, b, h, rfl⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h.symm
      rfl
  | y :: ys, l => by
    simp only [interleave, List.mem_cons, List.mem_map, mem_interleave x ys]
    constructor
    · rintro (rfl | ⟨l', ⟨a, b, rfl, rfl⟩, rfl⟩)
      · exact ⟨[], y :: ys, rfl, rfl⟩
      · exact ⟨y :: a, b, rfl, rfl⟩
    · rintro ⟨a, b, h, rfl⟩
      cases a with
      | nil => left; simp only [List.nil_append] at h ⊢; rw [h]
      | cons c a =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inr ⟨a ++ x :: b, ⟨a, b, rfl, rfl⟩, rfl⟩

theorem mem_perms {α : Type} : ∀ (l l' : List α), l' ∈ perms l ↔ l'.Perm l
  | [], l' => by simp [perms, List.perm_nil]
  | x :: xs, l' => by
    simp only [perms, List.mem_flatMap, mem_perms xs, mem_interleave]
    constructor
    · rintro ⟨p, hp, a, b, rfl, rfl⟩
      exact List.perm_middle.trans (hp.cons x)
    · intro h
      obtain ⟨a, b, rfl⟩ := List.append_of_mem (h.symm.subset List.mem_cons_self)
      exact ⟨a ++ b, (List.perm_middle.symm.trans h).cons_inv, a, b, rfl, rfl⟩

theorem interleave_map {α β : Type} (f : α → β) (x : α) :
    ∀ ys, (interleave x ys).map (List.map f) = interleave (f x) (ys.map f)
  | [] => rfl
  | y :: ys => by
    simp only [interleave, List.map_cons, List.map_map, Function.comp_def, ← interleave_map f x ys]

theorem perms_map {α β : Type} (f : α → β) :
    ∀ l, (perms l).map (List.map f) = perms (l.map f)
  | [] => rfl
  | x :: xs => by
    simp only [perms, List.map_cons, List.map_flatMap, interleave_map, ← perms_map f xs,
      List.flatMap_map]

/-! ### The problem and its completions -/

/-- Version 1 interprets no declared reporting policy. -/
def noPolicy : Empty → ProcessHistory → List Stamped → Prop := fun p => p.elim

instance (p : Empty) (h : ProcessHistory) (r : List Stamped) : Decidable (noPolicy p h r) :=
  p.elim

/-- A decoded process problem: the extracted record and the declared universe
of events that may have happened unrecorded. -/
structure Problem where
  record : DecodedRecord Empty
  unrecorded : List Stamped
  deriving DecidableEq, Repr

namespace Problem

/-- The recorded events, each once. Two entries reporting the same event (for
example from two files) state it once. -/
def base (p : Problem) : List Stamped := (p.record.events.map DecodedEvent.event).dedup

/-- The record's compatibility predicate, with duplicate-free histories. -/
def Compat (p : Problem) (h : ProcessHistory) : Prop :=
  h.Nodup ∧ p.record.Compatible noPolicy h

instance (p : Problem) : DecidablePred p.Compat :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Every interleaving of the recorded events with a sublist of the universe. -/
def candidates (p : Problem) : List ProcessHistory :=
  p.unrecorded.dedup.sublists.flatMap fun sub => perms (p.base ++ sub)

/-- The completions: compatible candidates, each once. -/
def completions (p : Problem) : List ProcessHistory :=
  (p.candidates.filter fun h => decide (p.Compat h)).dedup

theorem completions_nodup (p : Problem) : p.completions.Nodup := List.nodup_dedup _

theorem mem_base {p : Problem} {e : Stamped} :
    e ∈ p.base ↔ e ∈ p.record.events.map DecodedEvent.event := List.mem_dedup

/-- The exact characterization of the completions over a universe. -/
theorem mem_completions (p : Problem) (h : ProcessHistory) :
    h ∈ p.completions ↔ p.Compat h ∧ ∀ e ∈ h, e ∈ p.base ∨ e ∈ p.unrecorded := by
  unfold completions candidates
  rw [List.mem_dedup, List.mem_filter, decide_eq_true_iff, List.mem_flatMap]
  constructor
  · rintro ⟨⟨sub, hsub, hperm⟩, hc⟩
    refine ⟨hc, fun e he => ?_⟩
    have := ((mem_perms _ _).1 hperm).subset he
    rcases List.mem_append.1 this with hb | hs
    · exact .inl hb
    · exact .inr (List.mem_dedup.1 ((List.mem_sublists.1 hsub).subset hs))
  · rintro ⟨hc, hall⟩
    refine ⟨⟨p.unrecorded.dedup.filter fun e => decide (e ∈ h ∧ e ∉ p.base), ?_, ?_⟩, hc⟩
    · exact List.mem_sublists.2 List.filter_sublist
    · apply (mem_perms _ _).2
      have hnd : (p.base ++ p.unrecorded.dedup.filter fun e => decide (e ∈ h ∧ e ∉ p.base)).Nodup := by
        refine List.nodup_append.2 ⟨List.nodup_dedup _, (List.nodup_dedup _).filter _, ?_⟩
        intro a ha b hb hab
        subst hab
        simp only [List.mem_filter, decide_eq_true_iff] at hb
        exact hb.2.2 ha
      refine (List.perm_ext_iff_of_nodup hc.1 hnd).2 fun e => ?_
      simp only [List.mem_append, List.mem_filter, List.mem_dedup, decide_eq_true_iff]
      constructor
      · intro he
        by_cases hb : e ∈ p.base
        · exact .inl hb
        · rcases hall e he with hb' | hu
          · exact absurd hb' hb
          · exact .inr ⟨hu, he, hb⟩
      · rintro (hb | ⟨_, he, _⟩)
        · exact hc.2.1.2.1 e (mem_base.1 hb)
        · exact he

/-- A larger universe gives a superset of completions. -/
theorem completions_mono {p q : Problem} (record : p.record = q.record)
    (sub : ∀ e ∈ p.unrecorded, e ∈ q.unrecorded) {h : ProcessHistory} (mem : h ∈ p.completions) :
    h ∈ q.completions := by
  rw [mem_completions] at mem ⊢
  obtain ⟨hc, hall⟩ := mem
  have hb : p.base = q.base := by simp [base, record]
  refine ⟨by simpa [Compat, record] using hc, fun e he => ?_⟩
  rcases hall e he with b | u
  · exact .inl (hb ▸ b)
  · exact .inr (sub e u)

end Problem

open Problem

/-! ### Query atoms, formulas and answers -/

/-- The closed atom vocabulary of version 1, read from the analysis-order
predicates of `Lara.Process.Order`. -/
inductive Atom where
  | runPrecommitted (run : RunId)
  | predictable
  | splitSelection (selection test : List DataId)
  | familyCountAtMost (family : FamilyId) (bound : Nat)
  deriving DecidableEq, Repr

def Atom.holds : Atom → ProcessHistory → Prop
  | .runPrecommitted run, h => RunPrecommitted h run
  | .predictable, h => Predictable h
  | .splitSelection selection test, h => SplitSelection h selection test
  | .familyCountAtMost family bound, h => familyCount h family ≤ bound

instance (a : Atom) : DecidablePred a.holds := by
  intro h; cases a <;> unfold Atom.holds <;> infer_instance

/-- A query formula. -/
abbrev Query := Formula Atom

/-- The verdict of a property over a list of completions. The empty check comes
first, so no completions is never a positive answer. -/
def listVerdict {X : Type} (xs : List X) (φ : X → Prop) [DecidablePred φ] : Verdict :=
  if xs = [] then .inconsistent
  else if xs.all (fun x => decide (φ x)) then .certainTrue
  else if xs.all (fun x => decide ¬ φ x) then .certainFalse
  else .unknown

/-- One answer: the verdict, the number of completions and, for `unknown`, one
completion where the formula holds and one where it fails. The two witnesses
are present exactly when the verdict is `unknown` (`answer_witnesses`,
`answer_no_witnesses`), so the result encoder, which prints whichever are
present, prints both or neither. -/
structure Answer where
  verdict : Verdict
  count : Nat
  holds : Option ProcessHistory
  fails : Option ProcessHistory
  deriving DecidableEq, Repr

def answerOf (xs : List ProcessHistory) (q : Query) : Answer :=
  let v := listVerdict xs (q.holds Atom.holds)
  { verdict := v
    count := xs.length
    holds := if v = .unknown then xs.find? fun h => decide (q.holds Atom.holds h) else none
    fails := if v = .unknown then xs.find? fun h => decide ¬ q.holds Atom.holds h else none }

def answer (p : Problem) (q : Query) : Answer := answerOf p.completions q

/-- An `unknown` answer names a completion where the formula holds and one where
it fails. -/
theorem answer_witnesses (p : Problem) (q : Query) (unk : (answer p q).verdict = .unknown) :
    (∃ h, (answer p q).holds = some h ∧ h ∈ p.completions ∧ q.holds Atom.holds h) ∧
      ∃ h, (answer p q).fails = some h ∧ h ∈ p.completions ∧ ¬ q.holds Atom.holds h := by
  simp only [answer, answerOf] at unk ⊢
  rw [if_pos unk, if_pos unk]
  simp only [listVerdict] at unk
  split_ifs at unk with e t f
  simp only [List.all_eq_true, decide_eq_true_eq, not_forall, not_not] at t f
  obtain ⟨x, hx, nx⟩ := t
  obtain ⟨y, hy, ny⟩ := f
  have key : ∀ P : ProcessHistory → Bool, (∃ y ∈ p.completions, P y = true) →
      ∃ z, p.completions.find? P = some z ∧ z ∈ p.completions ∧ P z = true := by
    rintro P ⟨y, hy, py⟩
    cases hz : p.completions.find? P with
    | none => exact absurd (List.find?_eq_none.1 hz y hy) (by simp [py])
    | some z => exact ⟨z, rfl, List.mem_of_find?_eq_some hz, List.find?_some hz⟩
  constructor
  · obtain ⟨z, hz, mz, pz⟩ := key (fun h => decide (q.holds Atom.holds h)) ⟨y, hy, decide_eq_true ny⟩
    exact ⟨z, hz, mz, of_decide_eq_true pz⟩
  · obtain ⟨z, hz, mz, pz⟩ := key (fun h => decide ¬ q.holds Atom.holds h) ⟨x, hx, decide_eq_true nx⟩
    exact ⟨z, hz, mz, of_decide_eq_true pz⟩

/-- A verdict other than `unknown` carries no witnesses. -/
theorem answer_no_witnesses (p : Problem) (q : Query) (h : (answer p q).verdict ≠ .unknown) :
    (answer p q).holds = none ∧ (answer p q).fails = none := by
  simp only [answer, answerOf] at h ⊢
  exact ⟨if_neg h, if_neg h⟩

/-- Over the declared candidate carrier, the reported verdict is the landed
`verdict` of the record's compatibility predicate. -/
theorem answerVerdict_eq_verdict (p : Problem) (q : Query) :
    (answer p q).verdict =
      verdict (X := {h // h ∈ p.candidates.toFinset}) (fun x => p.Compat x.1)
        (fun x => q.holds Atom.holds x.1) := by
  have mem : ∀ h, h ∈ p.completions ↔ h ∈ p.candidates ∧ p.Compat h := by
    intro h; simp [completions, List.mem_dedup, List.mem_filter]
  simp only [answer, answerOf, listVerdict, verdict]
  have ne : (p.completions = []) ↔ ¬ ∃ x : {h // h ∈ p.candidates.toFinset}, p.Compat x.1 := by
    rw [List.eq_nil_iff_forall_not_mem]
    constructor
    · rintro hn ⟨⟨x, hx⟩, hc⟩; exact hn x ((mem x).2 ⟨List.mem_toFinset.1 hx, hc⟩)
    · intro hn x hx; exact hn ⟨⟨x, List.mem_toFinset.2 ((mem x).1 hx).1⟩, ((mem x).1 hx).2⟩
  have allT : (p.completions.all fun x => decide (q.holds Atom.holds x)) = true ↔
      ∀ x : {h // h ∈ p.candidates.toFinset}, p.Compat x.1 → q.holds Atom.holds x.1 := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    constructor
    · rintro hall ⟨x, hx⟩ hc; exact hall x ((mem x).2 ⟨List.mem_toFinset.1 hx, hc⟩)
    · intro hall x hx; exact hall ⟨x, List.mem_toFinset.2 ((mem x).1 hx).1⟩ ((mem x).1 hx).2
  have allF : (p.completions.all fun x => decide ¬ q.holds Atom.holds x) = true ↔
      ∀ x : {h // h ∈ p.candidates.toFinset}, p.Compat x.1 → ¬ q.holds Atom.holds x.1 := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    constructor
    · rintro hall ⟨x, hx⟩ hc; exact hall x ((mem x).2 ⟨List.mem_toFinset.1 hx, hc⟩)
    · intro hall x hx; exact hall ⟨x, List.mem_toFinset.2 ((mem x).1 hx).1⟩ ((mem x).1 hx).2
  by_cases e : p.completions = []
  · rw [if_pos e, if_pos (ne.1 e)]
  · rw [if_neg e, if_neg (fun h => e (ne.2 h))]
    by_cases t : (p.completions.all fun x => decide (q.holds Atom.holds x)) = true
    · rw [if_pos t, if_pos (allT.1 t)]
    · rw [if_neg t, if_neg (fun h => t (allT.2 h))]
      by_cases f : (p.completions.all fun x => decide ¬ q.holds Atom.holds x) = true
      · rw [if_pos f, if_pos (allF.1 f)]
      · rw [if_neg f, if_neg (fun h => f (allF.2 h))]

/-- Certainty is antitone in the universe: if a larger universe makes a formula
certain, a smaller universe with any completion at all makes it certain the
same way, and an inconsistent larger universe makes the smaller one
inconsistent. -/
theorem certain_antitone_universe {p q : Problem} (record : p.record = q.record)
    (sub : ∀ e ∈ p.unrecorded, e ∈ q.unrecorded) (φ : Query) :
    ((answer q φ).verdict = .inconsistent → (answer p φ).verdict = .inconsistent) ∧
      (p.completions ≠ [] → (answer q φ).verdict = .certainTrue →
        (answer p φ).verdict = .certainTrue) ∧
      (p.completions ≠ [] → (answer q φ).verdict = .certainFalse →
        (answer p φ).verdict = .certainFalse) := by
  have mono := fun {h} (m : h ∈ p.completions) => completions_mono record sub m
  simp only [answer, answerOf, listVerdict]
  refine ⟨fun hq => ?_, fun hne hq => ?_, fun hne hq => ?_⟩
  · split_ifs at hq with e
    rw [List.eq_nil_iff_forall_not_mem] at e
    have : p.completions = [] := List.eq_nil_iff_forall_not_mem.2 fun h hm => e h (mono hm)
    simp [this]
  · split_ifs at hq with e t
    rw [if_neg hne, if_pos]
    simp only [List.all_eq_true] at t ⊢
    exact fun h hm => t h (mono hm)
  · split_ifs at hq with e t f
    have fp : (p.completions.all fun x => decide ¬ φ.holds Atom.holds x) = true := by
      simp only [List.all_eq_true] at f ⊢
      exact fun h hm => f h (mono hm)
    rw [if_neg hne, if_neg, if_pos fp]
    intro tp
    obtain ⟨h, hm⟩ := List.exists_mem_of_ne_nil _ hne
    simp only [List.all_eq_true, decide_eq_true_eq] at tp fp
    exact fp h hm (tp h hm)

/-! ### Audits -/

/-- The coverage a profile must accept: every admitted assertion, or open-world
coverage of an empty scope when none is admitted (absence of attestation is
open world, never complete). -/
def admittedCoverage (p : Problem) : List (RecordCoverage Empty) :=
  match p.record.coverage.map CoverageAssertion.coverage with
  | [] => [.openWorld ⟨[], none, none, none, 0⟩]
  | cs => cs

/-- An audit of the submitted witness `w` for claim `c`: the profile accepts the
admitted coverage, and `w` warrants `c` in every completion. Its warrant model is
supplied; version 1 has no runtime that builds one from a checked source. -/
def AuditHolds (M : WarrantModel ProcessHistory ClaimId WitnessId) (P : Profile Empty)
    (p : Problem) (c : ClaimId) (w : WitnessId) : Prop :=
  (∀ cov ∈ admittedCoverage p, P.acceptsCoverage cov = true) ∧
    ArgumentEntitledBy (· ∈ p.completions) (fun h w => Warranted M P h c w) w

theorem auditHolds_iff (M : WarrantModel ProcessHistory ClaimId WitnessId) (P : Profile Empty)
    (p : Problem) (c : ClaimId) (w : WitnessId) :
    AuditHolds M P p c w ↔
      (∀ cov ∈ admittedCoverage p, P.acceptsCoverage cov = true) ∧ p.completions ≠ [] ∧
        ∀ h, p.Compat h → (∀ e ∈ h, e ∈ p.base ∨ e ∈ p.unrecorded) → Warranted M P h c w := by
  simp only [AuditHolds, ArgumentEntitledBy]
  constructor
  · rintro ⟨acc, ⟨x, hx⟩, all⟩
    exact ⟨acc, List.ne_nil_of_mem hx, fun h hc hu => all h ((mem_completions p h).2 ⟨hc, hu⟩)⟩
  · rintro ⟨acc, ne, all⟩
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ ne
    exact ⟨acc, ⟨x, hx⟩,
      fun h hm => all h ((mem_completions p h).1 hm).1 ((mem_completions p h).1 hm).2⟩

end Lara.Process.Universe
