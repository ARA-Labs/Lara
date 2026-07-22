/-
Mechanized whole-status layer (`Lara.Grounded`). Mechanizes the abstract
argumentation-framework core of spec §9 **result 6** (status preservation) and the
determinism / termination core of **result 5** (grounded evaluation + claim
aggregation).

**Scope — read before citing this as "result 6" (honest boundary).** What is
proved here is the equivalence, over an *arbitrary* finite framework `F : AF`, of
two definitions of the grounded semantics: a **declarative** least-fixed-point
judgment (`DirectIn`/`DirectOut`) and the **executable** bounded-iteration
labelling (`labelC`), aggregated to four-state status. This is genuine and
non-trivial, but it is *not yet* the full spec §9 result 6, which is preservation
between a direct semantics on the *source program* and the semantics of the
*compiled* AF (`grounded(compile(W))`). `compile : Source → AF` and its subargument
closure are defined and characterized (`compile_attack_iff`) but are **not
exercised** by the equivalence theorems below — every one of them quantifies over a
single already-given `F : AF`, and `statusDirect`/`statusC` read the *same*
`F.attack`. Instantiating the equivalence at `F := compile W` and proving a
source-level status matches it (thereby exercising the subargument-closure edges)
is M1 work. Provenance docs label this "result 6 — abstract AF layer" accordingly.

Background (why this file exists). Spec §8 originally defined claim status *only*
through the compiled route `compile → grounded → aggregate`, so result 6 had
nothing to preserve — a documented dead end (exploration tree **N16**). This
development supplies the first half: an **independent, declarative** grounded
semantics (`DirectIn` / `DirectOut`), defined as the least fixed point of the
defense operator *without* running the iteration, proved to agree with the
executable labelling over any AF. That closes the "no independent semantics
exists" gap at the abstract layer; the compile step remains.

Two semantics over one finite framework `AF = (args, attack)`:

* **Compiled / executable** (`grounded`, `labelC`): the grounded extension as the
  least fixed point of Dung's characteristic operator, computed by bounded
  iteration from `∅`. Finite carrier ⇒ the ascending chain stabilizes within
  `|args|` steps (`grounded_stable`), so this is a *total, deterministic* function
  — the determinism/termination content of result 5 (spec §8, C07).
* **Direct / declarative** (`DirectIn`, `DirectOut`): a big-step judgment — the
  least predicate closed under "`a` is `in` when every attacker of `a` is itself
  attacked by something already `in`". This is the source semantics N16 asked for;
  it never materializes the iteration.

`directIn_iff` proves the two coincide argument-by-argument; the `labelC_*` lemmas
lift it to a three-way label partition and `status_preservation` to four-state
claim status. The status function addresses the two N17 points (see `statusC`):
`gap` fires only on empty complete support (`statusC_gap_iff`, mechanized), so a
complete `in` alternative dominates open holes (which become a defined
`incompleteAlternative` diagnostic — a modeling convention, not a theorem); and
`contested := grounded undec`.

Kept deliberately abstract (spec §8 is the whole-status layer, above the frozen
strict-step layer): `compile` carries the one distinctive compilation feature,
ASPIC+ subargument closure (an attack on an occurrence defeats every complete term
built on it), and `compile_attack_iff` characterizes exactly which edges it emits —
but, per the scope note above, no equivalence theorem here consumes `compile`, so
the subargument-closure construction is defined and characterized, not yet shown
preserving. The metatheory does not depend on the shape of support terms, which are
corpus-gated (M0/M3). No Mathlib: the finite-fixpoint argument is done by hand in
core Lean 4.
-/

namespace Lara.Grounded

/-- Arguments are identified by opaque ids at this layer. -/
abbrev Arg := Nat

/-- Grounded labels. -/
inductive Label where
  | inn | out | undec
deriving DecidableEq, Repr

/-- Four-state claim status (spec §8). -/
inductive Status where
  | justified | contested | defeated | gap
deriving DecidableEq, Repr

/-- A compiled argumentation framework: a finite carrier `args` and a decidable
attack relation. Target of `compile`. -/
structure AF where
  /-- the finite set of complete checked support arguments -/
  args : List Arg
  /-- `attack a b`: argument `a` attacks argument `b` -/
  attack : Arg → Arg → Bool

/-! ### Boolean membership helper -/

/-- Decidable membership as a `Bool`, so it composes with `List.all`/`any`. -/
def memB (a : Arg) (S : List Arg) : Bool := decide (a ∈ S)

@[simp] theorem memB_iff {a : Arg} {S : List Arg} : memB a S = true ↔ a ∈ S := by
  simp [memB]

/-! ### The characteristic operator and the grounded extension (compiled semantics) -/

/-- `a` is **defended** by `S`: every attacker of `a` (within the framework) is
itself attacked by some member of `S`. Executable form of Dung's acceptability. -/
def defendedB (F : AF) (S : List Arg) (a : Arg) : Bool :=
  F.args.all (fun b => (! F.attack b a) || S.any (fun c => F.attack c b))

theorem defendedB_iff {F : AF} {S : List Arg} {a : Arg} :
    defendedB F S a = true ↔ ∀ b ∈ F.args, F.attack b a → ∃ c ∈ S, F.attack c b := by
  unfold defendedB
  rw [List.all_eq_true]
  constructor
  · intro h b hb hab
    have hh := h b hb
    rw [Bool.or_eq_true, List.any_eq_true] at hh
    rcases hh with hcontra | hc
    · rw [Bool.not_eq_true'] at hcontra; rw [hcontra] at hab; exact absurd hab (by simp)
    · exact hc
  · intro h b hb
    rw [Bool.or_eq_true, List.any_eq_true]
    by_cases hab : F.attack b a = true
    · exact Or.inr (h b hb hab)
    · exact Or.inl (by simp only [Bool.not_eq_true', Bool.not_eq_true] at hab ⊢; exact hab)

/-- One round of the characteristic operator: the arguments defended by `S`. -/
def step (F : AF) (S : List Arg) : List Arg :=
  F.args.filter (fun a => defendedB F S a)

theorem mem_step {F : AF} {S : List Arg} {a : Arg} :
    a ∈ step F S ↔ a ∈ F.args ∧ defendedB F S a = true := by
  simp [step, List.mem_filter]

theorem step_subset_args {F : AF} {S : List Arg} {a : Arg} (h : a ∈ step F S) :
    a ∈ F.args := (mem_step.mp h).1

/-- The operator is monotone in `S`. -/
theorem step_mono {F : AF} {S T : List Arg} (hST : ∀ x, x ∈ S → x ∈ T) :
    ∀ a, a ∈ step F S → a ∈ step F T := by
  intro a ha
  rw [mem_step] at ha ⊢
  refine ⟨ha.1, ?_⟩
  rw [defendedB_iff] at ha ⊢
  intro b hb hab
  obtain ⟨c, hcS, hcb⟩ := ha.2 b hb hab
  exact ⟨c, hST c hcS, hcb⟩

/-- The iteration from `∅`. Structural recursion, so `iter (k+1) = step F (iter k)`
holds definitionally. -/
def iter (F : AF) : Nat → List Arg
  | 0 => []
  | k + 1 => step F (iter F k)

/-- The grounded extension: iterate `|args|` times. `grounded_stable` proves this
is already the least fixed point (the chain stabilizes within `|args|` steps). -/
def grounded (F : AF) : List Arg := iter F F.args.length

theorem iter_subset_args {F : AF} : ∀ k a, a ∈ iter F k → a ∈ F.args
  | 0, _, h => by simp [iter] at h
  | _ + 1, _, h => step_subset_args h

/-- The iteration is ascending. -/
theorem iter_mono {F : AF} : ∀ k a, a ∈ iter F k → a ∈ iter F (k + 1)
  | 0, _, h => by simp [iter] at h
  | k + 1, a, h => by
    have IH : ∀ x, x ∈ iter F k → x ∈ iter F (k + 1) := iter_mono k
    exact step_mono IH a h

/-! ### The direct (declarative) semantics

The **direct** big-step judgment, as mutually-inductive least fixed points:

* `DirectIn F a`: `a` is a framework argument and every attacker of `a` is
  directly *out* (the existential witness is carried by `DirectOut`'s constructor,
  which keeps the definition strictly positive — no nesting through `Exists`).
* `DirectOut F b`: some directly-`in` argument attacks `b`.

This is the source semantics N16 asked for: it defines claim justification directly
on the attack structure, without constructing the grounded iteration. -/
mutual
  inductive DirectIn (F : AF) : Arg → Prop where
    | intro {a : Arg} (ha : a ∈ F.args)
        (h : ∀ b, b ∈ F.args → F.attack b a = true → DirectOut F b) : DirectIn F a
  inductive DirectOut (F : AF) : Arg → Prop where
    | intro {b c : Arg} (hc : DirectIn F c) (hcb : F.attack c b = true) : DirectOut F b
end

/-- `DirectOut` unfolds to the intended existential. -/
theorem directOut_iff {F : AF} {b : Arg} :
    DirectOut F b ↔ ∃ c, DirectIn F c ∧ F.attack c b = true := by
  constructor
  · intro h; cases h with | intro hc hcb => exact ⟨_, hc, hcb⟩
  · rintro ⟨c, hc, hcb⟩; exact DirectOut.intro hc hcb

/-- A directly-`in` argument is a framework argument. -/
theorem directIn_mem_args {F : AF} {a : Arg} (h : DirectIn F a) : a ∈ F.args := by
  cases h with | intro ha _ => exact ha

/-! ### Soundness of the iteration against the direct judgment (grounded ⊆ direct) -/

/-- Everything the iteration accepts is directly `in`. No fixpoint reasoning. -/
theorem iter_directIn {F : AF} : ∀ k a, a ∈ iter F k → DirectIn F a
  | 0, _, h => by simp [iter] at h
  | k + 1, a, h => by
    rw [iter, mem_step] at h
    refine DirectIn.intro h.1 ?_
    intro b hb hab
    obtain ⟨c, hck, hcb⟩ := defendedB_iff.mp h.2 b hb hab
    exact DirectOut.intro (iter_directIn k c hck) hcb

/-! ### Finite stabilization: `grounded` is a fixed point -/

/-- Deficit of `S`: how many framework arguments are still outside `S`. Strictly
decreases on each strict growth step, which bounds the iteration. -/
def deficit (F : AF) (S : List Arg) : Nat :=
  (F.args.filter (fun a => ! memB a S)).length

/-- Filter length is monotone under pointwise-weaker predicates. -/
theorem filter_length_le {l : List Arg} {p q : Arg → Bool}
    (hpq : ∀ a ∈ l, p a = true → q a = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have ih' := ih (fun a ha => hpq a (List.mem_cons_of_mem x ha))
    by_cases hpx : p x = true
    · have hqx : q x = true := hpq x List.mem_cons_self hpx
      rw [List.filter_cons_of_pos hpx, List.filter_cons_of_pos hqx,
        List.length_cons, List.length_cons]; omega
    · by_cases hqx : q x = true
      · rw [List.filter_cons_of_neg hpx, List.filter_cons_of_pos hqx, List.length_cons]; omega
      · rw [List.filter_cons_of_neg hpx, List.filter_cons_of_neg hqx]; omega

/-- With a witness that `q` strictly dominates `p` on `l`, filter length is strict. -/
theorem filter_length_lt {l : List Arg} {p q : Arg → Bool}
    (hpq : ∀ a ∈ l, p a = true → q a = true) {w : Arg} (hw : w ∈ l) (hqw : q w = true)
    (hpw : p w = false) : (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at hw
  | cons x xs ih =>
    have hpq' : ∀ a ∈ xs, p a = true → q a = true :=
      fun a ha => hpq a (List.mem_cons_of_mem x ha)
    rcases List.mem_cons.mp hw with hx | hx
    · subst hx
      rw [List.filter_cons_of_neg (by simp [hpw]), List.filter_cons_of_pos hqw, List.length_cons]
      exact Nat.lt_succ_of_le (filter_length_le hpq')
    · have ih' := ih hpq' hx
      by_cases hpx : p x = true
      · have hqx : q x = true := hpq x List.mem_cons_self hpx
        rw [List.filter_cons_of_pos hpx, List.filter_cons_of_pos hqx, List.length_cons,
          List.length_cons]; omega
      · by_cases hqx : q x = true
        · rw [List.filter_cons_of_neg hpx, List.filter_cons_of_pos hqx, List.length_cons]; omega
        · rw [List.filter_cons_of_neg hpx, List.filter_cons_of_neg hqx]; omega

/-- `stable k`: iterate `k+1` is contained in iterate `k`. With `iter_mono` this
means the iteration has reached a fixed point at step `k`. -/
def stable (F : AF) (k : Nat) : Prop := ∀ a, a ∈ iter F (k + 1) → a ∈ iter F k

/-- Stability persists one step. -/
theorem stable_succ {F : AF} {k : Nat} (h : stable F k) : stable F (k + 1) := by
  intro a ha
  rw [iter] at ha ⊢
  exact step_mono h a ha

theorem stable_add {F : AF} {k : Nat} (h : stable F k) : ∀ j, stable F (k + j)
  | 0 => h
  | j + 1 => stable_succ (stable_add h j)

/-- A non-stable step strictly drops the deficit. -/
theorem deficit_lt {F : AF} {k : Nat} (h : ¬ stable F k) :
    deficit F (iter F (k + 1)) < deficit F (iter F k) := by
  have hex : ∃ a, a ∈ iter F (k + 1) ∧ ¬ a ∈ iter F k :=
    Classical.byContradiction (fun hcon =>
      h (fun a hain => Classical.byContradiction (fun hnotin => hcon ⟨a, hain, hnotin⟩)))
  obtain ⟨a, ha1, ha0⟩ := hex
  unfold deficit
  apply filter_length_lt (w := a)
  · intro x _ hx
    have hb1 : memB x (iter F (k + 1)) = false := by
      cases hh : memB x (iter F (k + 1)) with
      | false => rfl
      | true => rw [hh] at hx; simp at hx
    have hnx : ¬ x ∈ iter F (k + 1) := by
      simp only [memB, decide_eq_false_iff_not] at hb1; exact hb1
    have hb0 : memB x (iter F k) = false := by
      simp only [memB, decide_eq_false_iff_not]; intro hc; exact hnx (iter_mono k x hc)
    simp [hb0]
  · exact iter_subset_args (k + 1) a ha1
  · have : memB a (iter F k) = false := by
      simp only [memB, decide_eq_false_iff_not]; exact ha0
    simp [this]
  · have : memB a (iter F (k + 1)) = true := by
      simp only [memB, decide_eq_true_eq]; exact ha1
    simp [this]

/-- `deficit (iter 0) = |args|`. -/
theorem deficit_iter_zero {F : AF} : deficit F (iter F 0) = F.args.length := by
  have h : F.args.filter (fun a => ! memB a (iter F 0)) = F.args := by
    apply List.filter_eq_self.mpr
    intro a _
    have h0 : iter F 0 = ([] : List Arg) := rfl
    simp [memB, h0]
  unfold deficit
  rw [h]

/-- If no step in `[0,k)` is stable, the deficit has dropped by at least `k`. -/
theorem deficit_bound {F : AF} : ∀ k, (∀ j, j < k → ¬ stable F j) →
    deficit F (iter F k) + k ≤ F.args.length
  | 0, _ => by rw [deficit_iter_zero]; omega
  | k + 1, h => by
    have hk : ¬ stable F k := h k (Nat.lt_succ_self k)
    have IH : deficit F (iter F k) + k ≤ F.args.length :=
      deficit_bound k (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hlt := deficit_lt hk
    omega

/-- **Termination/determinism core (result 5).** The grounded iteration reaches a
fixed point within `|args|` steps: `iter (|args|)` is stable. -/
theorem grounded_stable {F : AF} : stable F F.args.length := by
  by_cases hs : ∃ j, j < F.args.length ∧ stable F j
  · obtain ⟨j, hj, hjs⟩ := hs
    have := stable_add hjs (F.args.length - j)
    rwa [Nat.add_sub_cancel' (Nat.le_of_lt hj)] at this
  · have hs : ∀ j, j < F.args.length → ¬ stable F j := fun j hj hst => hs ⟨j, hj, hst⟩
    have hb := deficit_bound F.args.length (fun j hj => hs j hj)
    have hdef : deficit F (iter F F.args.length) = 0 := by omega
    have hall : ∀ a ∈ F.args, a ∈ iter F F.args.length := by
      intro a ha
      apply Classical.byContradiction
      intro hna
      have hmem : a ∈ F.args.filter (fun a => ! memB a (iter F F.args.length)) := by
        rw [List.mem_filter]
        refine ⟨ha, ?_⟩
        have : memB a (iter F F.args.length) = false := by
          simp only [memB, decide_eq_false_iff_not]; exact hna
        simp [this]
      have : 0 < deficit F (iter F F.args.length) := by
        unfold deficit; exact List.length_pos_of_mem hmem
      omega
    intro a ha
    exact hall a (step_subset_args ha)

/-- `grounded` is a fixed point of the characteristic operator. -/
theorem grounded_fixpoint {F : AF} (a : Arg) :
    a ∈ step F (grounded F) ↔ a ∈ grounded F := by
  unfold grounded
  constructor
  · intro h; exact grounded_stable a h
  · intro h; exact iter_mono F.args.length a h

/-! ### Result 6 (abstract AF layer): the declarative and executable grounded semantics coincide -/

/- Completeness of the iteration (direct ⊆ grounded), proved simultaneously with
its `DirectOut` companion by mutual structural recursion on the derivation. -/
mutual
  theorem directIn_sound {F : AF} {a : Arg} : DirectIn F a → a ∈ grounded F
    | .intro ha hb =>
        (grounded_fixpoint a).mp (mem_step.mpr
          ⟨ha, defendedB_iff.mpr (fun b hbm hab => directOut_sound (hb b hbm hab))⟩)
  theorem directOut_sound {F : AF} {b : Arg} :
      DirectOut F b → ∃ c ∈ grounded F, F.attack c b = true
    | .intro hc hcb => ⟨_, directIn_sound hc, hcb⟩
end

/-- **Result 6 (abstract AF layer, argument level).** The declarative direct judgment `DirectIn` and
the executable grounded extension accept exactly the same arguments. -/
theorem directIn_iff {F : AF} (a : Arg) : DirectIn F a ↔ a ∈ grounded F :=
  ⟨directIn_sound, iter_directIn F.args.length a⟩

/-- `DirectIn` is therefore decidable — its executable checker is grounded
membership. -/
instance instDecidableDirectIn {F : AF} (a : Arg) : Decidable (DirectIn F a) :=
  decidable_of_iff _ (directIn_iff a).symm

/-- `DirectOut` reduces to a bounded search over `args`, hence is decidable. -/
theorem directOut_iff_bex {F : AF} {a : Arg} :
    DirectOut F a ↔ ∃ c ∈ F.args, DirectIn F c ∧ F.attack c a = true := by
  rw [directOut_iff]
  constructor
  · rintro ⟨c, hc, hca⟩; exact ⟨c, directIn_mem_args hc, hc, hca⟩
  · rintro ⟨c, _, hc, hca⟩; exact ⟨c, hc, hca⟩

instance instDecidableDirectOut {F : AF} (a : Arg) : Decidable (DirectOut F a) :=
  decidable_of_iff _ directOut_iff_bex.symm

/-! ### Labels and four-state status -/

/-- The compiled labelling read off `grounded`. -/
def labelC (F : AF) (a : Arg) : Label :=
  if memB a (grounded F) = true then Label.inn
  else if F.args.any (fun c => memB c (grounded F) && F.attack c a) = true then Label.out
  else Label.undec

/-- The list-search form of "some `in` argument attacks `a`" equals `DirectOut`. -/
theorem attackedByIn_iff {F : AF} (a : Arg) :
    (F.args.any (fun c => memB c (grounded F) && F.attack c a) = true) ↔ DirectOut F a := by
  rw [directOut_iff_bex, List.any_eq_true]
  constructor
  · rintro ⟨c, hc, hcc⟩
    rw [Bool.and_eq_true] at hcc
    exact ⟨c, hc, (directIn_iff c).mpr (memB_iff.mp hcc.1), hcc.2⟩
  · rintro ⟨c, hc, hcin, hca⟩
    exact ⟨c, hc, by rw [Bool.and_eq_true]; exact ⟨memB_iff.mpr ((directIn_iff c).mp hcin), hca⟩⟩

/-- The compiled labelling is exactly the direct three-way partition. -/
theorem labelC_spec {F : AF} (a : Arg) :
    labelC F a = (if DirectIn F a then Label.inn
                  else if DirectOut F a then Label.out else Label.undec) := by
  unfold labelC
  by_cases h1 : DirectIn F a
  · rw [if_pos (memB_iff.mpr ((directIn_iff a).mp h1)), if_pos h1]
  · rw [if_neg (fun hc => h1 ((directIn_iff a).mpr (memB_iff.mp hc))), if_neg h1]
    by_cases h2 : DirectOut F a
    · rw [if_pos ((attackedByIn_iff a).mpr h2), if_pos h2]
    · rw [if_neg (fun hc => h2 ((attackedByIn_iff a).mp hc)), if_neg h2]

/-- **Result 6 (abstract AF layer, in).** `labelC = in` exactly on the directly-`in` arguments. -/
theorem labelC_inn_iff {F : AF} (a : Arg) : labelC F a = Label.inn ↔ DirectIn F a := by
  rw [labelC_spec]
  by_cases h : DirectIn F a
  · simp [h]
  · by_cases h2 : DirectOut F a <;> simp [h, h2]

/-- **Result 6 (abstract AF layer, out).** `labelC = out` exactly on the arguments that are not
directly `in` but are directly out (defeated by an `in` argument). -/
theorem labelC_out_iff {F : AF} (a : Arg) :
    labelC F a = Label.out ↔ ¬ DirectIn F a ∧ DirectOut F a := by
  rw [labelC_spec]
  by_cases h : DirectIn F a
  · simp [h]
  · by_cases h2 : DirectOut F a <;> simp [h, h2]

/-- **Result 6 (abstract AF layer, undec).** `labelC = undec` exactly on the arguments that are
neither directly `in` nor directly out — the grounded `undec` set. -/
theorem labelC_undec_iff {F : AF} (a : Arg) :
    labelC F a = Label.undec ↔ ¬ DirectIn F a ∧ ¬ DirectOut F a := by
  rw [labelC_spec]
  by_cases h : DirectIn F a
  · simp [h]
  · by_cases h2 : DirectOut F a <;> simp [h, h2]

/-! ### Compilation with subargument closure (spec §8) -/

/-- A source program at the whole-status layer. `base a o`: a typed attack lands on
occurrence `o`. `sub o b`: occurrence `o` is a subargument of complete term `b`. -/
structure Source where
  /-- complete checked support arguments -/
  args : List Arg
  /-- base typed attacks, on occurrences -/
  base : Arg → Arg → Bool
  /-- subargument relation on occurrences (reflexive in practice) -/
  sub  : Arg → Arg → Bool

/-- **Compilation (spec §8).** ASPIC+ subargument closure: an attack on occurrence
`o` compiles to an edge onto every complete argument `b` that contains `o`, so
defeating a subterm defeats each complete term built on it. -/
def compile (W : Source) : AF where
  args := W.args
  attack := fun a b => W.args.any (fun o => W.base a o && W.sub o b)

/-- Characterization of the compiled attack relation: `a` attacks `b` in
`compile W` iff some occurrence `o` of `b` (`sub o b`) carries a base attack from
`a`. This is the subargument-closure edge rule made explicit. NOTE: this only
*characterizes* the edges `compile` emits; it does not establish that grounded
status is preserved across compilation (see the file-level scope note). -/
theorem compile_attack_iff (W : Source) (a b : Arg) :
    (compile W).attack a b = true ↔ ∃ o ∈ W.args, W.base a o = true ∧ W.sub o b = true := by
  simp only [compile, List.any_eq_true, Bool.and_eq_true]

/-! ### Four-state claim status — resolving the two N17 points -/

/-- A claim, with its complete checked support arguments and its (incomplete)
hole-bearing supporting arguments. -/
structure Claim where
  /-- complete checked support arguments `support(P, p)` -/
  support : List Arg
  /-- incomplete supporting arguments with unresolved root obligations -/
  holes   : List Arg

/-- **Compiled claim status (spec §8, priority order).**

N17 point (1): a complete `in` alternative dominates open holes. `statusC` decides
`gap` on empty complete support only (`statusC_gap_iff`); holes on *other*
alternatives are a separate *diagnostic* (`incompleteAlternative`), which by
construction `statusC` does not read, so a complete winning argument is not
downgraded. The "gap only on empty complete support" half is mechanized
(`statusC_gap_iff`); "holes surface via a diagnostic" is a modeling convention (the
diagnostic is defined, not tied to `statusC` by a theorem).

N17 point (2): `contested := grounded undec` (the broad reading). The finer SCC /
mutual-defeat provenance is a separate reporting obligation, not part of the status.
The function is total and deterministic (a function of `labelC`). -/
def statusC (F : AF) (c : Claim) : Status :=
  if c.support = [] then Status.gap
  else if c.support.any (fun a => labelC F a == Label.inn) then Status.justified
  else if c.support.any (fun a => labelC F a == Label.undec) then Status.contested
  else Status.defeated

/-- **N17 point (1), mechanized half.** `statusC` returns `gap` exactly when the
complete support set is empty — an open hole on some other alternative never yields
`gap` when a complete argument exists. -/
theorem statusC_gap_iff (F : AF) (c : Claim) : statusC F c = Status.gap ↔ c.support = [] := by
  constructor
  · intro h
    unfold statusC at h
    by_cases hs : c.support = []
    · exact hs
    · rw [if_neg hs] at h
      split at h
      · exact absurd h (by decide)
      · split at h
        · exact absurd h (by decide)
        · exact absurd h (by decide)
  · intro h; unfold statusC; rw [if_pos h]

/-- Diagnostic accompanying `statusC`: an incomplete alternative exists (N17 (1)).
Defined for reporting; `statusC` does not consume it. -/
def incompleteAlternative (c : Claim) : Bool := decide (c.holes ≠ [])

/-- **Declarative-grounded claim status**, read from the declarative `DirectIn` /
`DirectOut` judgments rather than the executable `labelC`. Over `F := compile W`
this is a status computed without the grounded iteration; it is *not* an
independent source semantics (it reads `F.attack` directly — see the file scope
note). Decidable because `DirectIn`/`DirectOut` are. -/
def statusDirect (F : AF) (c : Claim) : Status :=
  if c.support = [] then Status.gap
  else if c.support.any (fun a => decide (DirectIn F a)) then Status.justified
  else if c.support.any (fun a => decide (¬ DirectIn F a ∧ ¬ DirectOut F a)) then Status.contested
  else Status.defeated

/-- **Result 6 (abstract AF layer).** Over any single framework `F`, the
declarative-grounded status and the executable-grounded status agree on every
claim. This is the equivalence of the two grounded *definitions* aggregated to
four-state status; it does **not** exercise `compile` (both sides read the same
`F.attack`), so it is the abstract core of spec §9 result 6, not the full
source-vs-compiled preservation. See the file-level scope note. -/
theorem status_preservation {F : AF} (c : Claim) : statusDirect F c = statusC F c := by
  unfold statusDirect statusC
  have beq_inn : ∀ a, (labelC F a == Label.inn) = decide (labelC F a = Label.inn) := by
    intro a; cases labelC F a <;> rfl
  have beq_und : ∀ a, (labelC F a == Label.undec) = decide (labelC F a = Label.undec) := by
    intro a; cases labelC F a <;> rfl
  have hin : ∀ a, decide (DirectIn F a) = (labelC F a == Label.inn) := by
    intro a; rw [beq_inn]; exact decide_eq_decide.mpr (labelC_inn_iff a).symm
  have hun : ∀ a, decide (¬ DirectIn F a ∧ ¬ DirectOut F a) = (labelC F a == Label.undec) := by
    intro a; rw [beq_und]; exact decide_eq_decide.mpr (labelC_undec_iff a).symm
  simp only [hin, hun]

end Lara.Grounded
