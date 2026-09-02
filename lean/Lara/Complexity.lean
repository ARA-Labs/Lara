/-
Cost-instrumented grounded kernel (`Lara.Complexity`, issue #209).

Mirrors of the proof-oriented grounded evaluator in `Lara.Grounded` —
`anyAttackerC`, `defendedAuxC`/`defendedC`, `stepC`, `iterC`, `groundedC` —
each returning the original result paired with the number of `F.attack`
queries the run evaluates. The mirrors keep the exact recursive structure of
`Grounded.defendedB`/`step`/`iter`/`grounded`: the library folds
(`List.any`, `List.all`, `List.filter`) become explicit list recursions so
the counter can be threaded, with the same guard order and the left-to-right
short-circuit evaluation the boolean connectives actually perform — a
defense scan stops at its first undefeated attacker, and the inner attacker
scan runs only when `F.attack b a` has already answered `true`. The counter
increments exactly once per `F.attack` evaluation and nowhere else.

Four layers are mechanized here:

* **Agreement** (`*_fst`): every mirror's first projection equals its
  `Lara.Grounded` original, so each cost theorem is a statement about the
  existing evaluator, not about a variant algorithm.
* **Upper bounds** (`*_cost_le`): the full grounded run costs at most
  `n³ · (1 + n)` attack queries for `n = F.args.length`.
* **Short-circuit scan composition**: generic unfolding and composition
  lemmas for the mirrors, from which consumers (e.g. the quartic witness in
  `Lara.Examples.Complexity`) assemble exact per-round costs.
* **Universal lower bounds** (`*_cost_ge*`): `n² ≤ (groundedC F).2`
  for every framework (constraint D4, `docs/theory-m2b-complexity.md`).
  The two-node all-attacks evaluation
  `groundedC_twoNodeAllAttacks_cost` refutes the rejected exact pointwise
  cubic inequality at `n = 2`: its full run costs `4 = 2²`, strictly below
  `2³ = 8`. It does not establish an asymptotically tight universal degree.
  Quartic statements are *existential* worst-case results on a realizable
  family (`Lara.Examples.Complexity`); documentation must never merge the
  two quantifiers.

On top of the same cost model, the **shared carrier-status evaluator**
(issue #209) instruments the claim-status surface: `labelFromGroundedC`
reads one label off a shared grounded result, counting exactly the attack
queries of `Grounded.labelC`'s `out` scan; `statusSharedC` preserves
`Grounded.statusC`'s observable guard order — empty support first, then an
`inn` pass, then an `undec` pass, then `defeated` — while computing
`groundedC` at most once, and only after the empty-support guard; and
`carrierStatusC` is the exposed carrier query over `Invariants.eraseAF` and
`Invariants.claim`.  **Citation discipline** (see the cost-results citation
discipline in `docs/theory-m2b-complexity.md`, and constraint D4 there for
the quantifier rule):
`carrierStatusC_cost_le` is the paper-citable GroundedStatus upper theorem
for the carrier surface; the generic Claim bound `statusSharedC_cost_le` is
internal accounting and must not be cited as the restricted-class headline.
-/
import Lara.Grounded
import Lara.Invariants

namespace Lara.Complexity

open Grounded (AF Arg Label Status Claim)

/-! ### The instrumented mirrors -/

/-- Instrumented mirror of the attacker scan `S.any (fun c => F.attack c b)`
inside `Grounded.defendedB`. Short-circuits at the first attacker found,
exactly like `List.any`; each `F.attack` query costs one. -/
def anyAttackerC (F : AF) (S : List Arg) (b : Arg) : Bool × Nat :=
  match S with
  | [] => (false, 0)
  | c :: rest =>
    if F.attack c b then (true, 1)
    else
      let r := anyAttackerC F rest b
      (r.1, 1 + r.2)

/-- Instrumented mirror of the `List.all` scan inside `Grounded.defendedB`,
recursing over the candidate-attacker list. Each candidate `b` first pays the
one `F.attack b a` query of the disjunct `(! F.attack b a) || …`; only a
confirmed attacker triggers the `anyAttackerC` scan of `S`, and a failed
defense stops the scan exactly like `&&`. -/
def defendedAuxC (F : AF) (S : List Arg) (a : Arg) : List Arg → Bool × Nat
  | [] => (true, 0)
  | b :: rest =>
    if F.attack b a then
      let r := anyAttackerC F S b
      if r.1 then
        let r' := defendedAuxC F S a rest
        (r'.1, (1 + r.2) + r'.2)
      else (false, 1 + r.2)
    else
      let r' := defendedAuxC F S a rest
      (r'.1, 1 + r'.2)

/-- Instrumented `Grounded.defendedB`: scan the whole carrier, as the
original does. -/
def defendedC (F : AF) (S : List Arg) (a : Arg) : Bool × Nat :=
  defendedAuxC F S a F.args

/-- Instrumented mirror of the `List.filter` scan in `Grounded.step`. The
kept/dropped decision is exactly `defendedC`'s first projection; the cost of
each candidate's defense check is paid either way. -/
def stepAuxC (F : AF) (S : List Arg) : List Arg → List Arg × Nat
  | [] => ([], 0)
  | a :: rest =>
    let d := defendedC F S a
    let r := stepAuxC F S rest
    if d.1 then (a :: r.1, d.2 + r.2) else (r.1, d.2 + r.2)

/-- Instrumented `Grounded.step`: filter the carrier by defense. -/
def stepC (F : AF) (S : List Arg) : List Arg × Nat :=
  stepAuxC F S F.args

/-- Instrumented `Grounded.iter`: the same structural recursion, accumulating
each round's query count. -/
def iterC (F : AF) : Nat → List Arg × Nat
  | 0 => ([], 0)
  | k + 1 =>
    let r := iterC F k
    let s := stepC F r.1
    (s.1, r.2 + s.2)

/-- Instrumented `Grounded.grounded`: iterate `|args|` times. -/
def groundedC (F : AF) : List Arg × Nat :=
  iterC F F.args.length

/-! ### Evaluator agreement -/

theorem anyAttackerC_fst (F : AF) (S : List Arg) (b : Arg) :
    (anyAttackerC F S b).1 = S.any (fun c => F.attack c b) := by
  induction S with
  | nil => rfl
  | cons c rest ih =>
    by_cases h : F.attack c b = true
    · simp [anyAttackerC, h]
    · simp only [Bool.not_eq_true] at h
      simp [anyAttackerC, h, ih]

theorem defendedAuxC_fst (F : AF) (S : List Arg) (a : Arg) (l : List Arg) :
    (defendedAuxC F S a l).1 =
      l.all (fun b => (! F.attack b a) || S.any (fun c => F.attack c b)) := by
  induction l with
  | nil => rfl
  | cons b rest ih =>
    rw [List.all_cons, ← anyAttackerC_fst]
    by_cases hab : F.attack b a = true
    · by_cases hany : (anyAttackerC F S b).1 = true
      · simp [defendedAuxC, hab, hany, ih]
      · simp only [Bool.not_eq_true] at hany
        simp [defendedAuxC, hab, hany]
    · simp only [Bool.not_eq_true] at hab
      simp [defendedAuxC, hab, ih]

theorem defendedC_fst (F : AF) (S : List Arg) (a : Arg) :
    (defendedC F S a).1 = Grounded.defendedB F S a := by
  unfold defendedC Grounded.defendedB
  exact defendedAuxC_fst F S a F.args

theorem stepAuxC_fst (F : AF) (S : List Arg) (l : List Arg) :
    (stepAuxC F S l).1 = l.filter (fun a => Grounded.defendedB F S a) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    have hd := defendedC_fst F S a
    by_cases h : Grounded.defendedB F S a = true
    · rw [List.filter_cons_of_pos h]
      simp [stepAuxC, hd, h, ih]
    · rw [List.filter_cons_of_neg (by simp [h])]
      simp [stepAuxC, hd, h, ih]

theorem stepC_fst (F : AF) (S : List Arg) : (stepC F S).1 = Grounded.step F S := by
  unfold stepC Grounded.step
  exact stepAuxC_fst F S F.args

theorem iterC_fst (F : AF) (k : Nat) : (iterC F k).1 = Grounded.iter F k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (stepC F (iterC F k).1).1 = Grounded.step F (Grounded.iter F k)
    rw [ih, stepC_fst]

theorem groundedC_fst (F : AF) : (groundedC F).1 = Grounded.grounded F :=
  iterC_fst F F.args.length

/-! ### Upper bounds

`Grounded.grounded` runs `|args|` rounds; each round's `stepC` pays one
`defendedC` per carrier node, and each `defendedC` pays at most `1 + |S|`
queries per carrier node. The iterate handed to each round is a filter of
the carrier, so `|S| ≤ |args|` throughout. -/

variable {F : AF} {S : List Arg} {a b : Arg}

theorem anyAttackerC_cost_le : (anyAttackerC F S b).2 ≤ S.length := by
  induction S with
  | nil => exact Nat.le_refl 0
  | cons c rest ih =>
    by_cases h : F.attack c b = true
    · simp [anyAttackerC, h]
    · simp only [Bool.not_eq_true] at h
      simp only [anyAttackerC, h, Bool.false_eq_true, if_false, List.length_cons]
      omega

theorem defendedAuxC_cost_le (l : List Arg) :
    (defendedAuxC F S a l).2 ≤ l.length * (1 + S.length) := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons b' rest ih =>
    have hexp : (b' :: rest).length * (1 + S.length)
        = rest.length * (1 + S.length) + (1 + S.length) := by
      rw [List.length_cons, Nat.succ_mul]
    have hany : (anyAttackerC F S b').2 ≤ S.length := anyAttackerC_cost_le
    rw [hexp]
    by_cases hab : F.attack b' a = true
    · by_cases hany1 : (anyAttackerC F S b').1 = true
      · simp only [defendedAuxC, hab, hany1, if_pos]
        omega
      · simp only [Bool.not_eq_true] at hany1
        simp only [defendedAuxC, hab, hany1, if_pos, Bool.false_eq_true, if_false]
        omega
    · simp only [Bool.not_eq_true] at hab
      simp only [defendedAuxC, hab, Bool.false_eq_true, if_false]
      omega

theorem defendedC_cost_le :
    (defendedC F S a).2 ≤ F.args.length * (1 + S.length) :=
  defendedAuxC_cost_le F.args

/-- Both branches of the filter step pay the same defense cost, so the
counter is branch-independent. -/
theorem stepAuxC_cost_cons (a' : Arg) (rest : List Arg) :
    (stepAuxC F S (a' :: rest)).2 = (defendedC F S a').2 + (stepAuxC F S rest).2 := by
  by_cases h : (defendedC F S a').1 = true <;> simp [stepAuxC, h]

theorem stepAuxC_cost_le (l : List Arg) :
    (stepAuxC F S l).2 ≤ l.length * (F.args.length * (1 + S.length)) := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a' rest ih =>
    rw [stepAuxC_cost_cons, List.length_cons, Nat.succ_mul,
      Nat.add_comm ((defendedC F S a').2)]
    exact Nat.add_le_add ih defendedC_cost_le

theorem stepC_cost_le :
    (stepC F S).2 ≤ F.args.length * (F.args.length * (1 + S.length)) :=
  stepAuxC_cost_le F.args

/-- Every iterate is a filter of the carrier (the iterate-length input to
the round bounds). -/
theorem iter_length_le (F : AF) (k : Nat) :
    (Grounded.iter F k).length ≤ F.args.length := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k => exact List.length_filter_le _ _

theorem iterC_cost_le (F : AF) (k : Nat) :
    (iterC F k).2 ≤ k * (F.args.length * (F.args.length * (1 + F.args.length))) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hlen : (iterC F k).1.length ≤ F.args.length := by
      rw [iterC_fst]; exact iter_length_le F k
    have hstep : (stepC F (iterC F k).1).2
        ≤ F.args.length * (F.args.length * (1 + F.args.length)) :=
      Nat.le_trans stepC_cost_le
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add_left hlen 1)))
    show (iterC F k).2 + (stepC F (iterC F k).1).2 ≤ _
    rw [Nat.succ_mul]
    exact Nat.add_le_add ih hstep

theorem groundedC_cost_le :
    (groundedC F).2 ≤ F.args.length ^ 3 * (1 + F.args.length) := by
  have hpow : F.args.length ^ 3
      = F.args.length * F.args.length * F.args.length := by
    rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ,
      show (2 : Nat) = 1 + 1 from rfl, Nat.pow_succ, Nat.pow_one]
  rw [hpow, Nat.mul_assoc, Nat.mul_assoc]
  exact iterC_cost_le F F.args.length

/-! ### Short-circuit scan composition

Generic unfolding and composition lemmas for the instrumented mirrors.
All counts follow the file's short-circuit model: one count per `F.attack`
evaluation, an attacker scan stops at its first hit, a defense scan stops
at its first undefeated attacker.  Consumers (e.g. the quartic witness in
`Lara.Examples.Complexity`) assemble exact per-round costs from these. -/

theorem anyAttackerC_cons_hit {F : Grounded.AF} {S : List Nat}
    {b c : Nat} (h : F.attack c b = true) :
    anyAttackerC F (c :: S) b = (true, 1) := by
  simp [anyAttackerC, h]

theorem anyAttackerC_cons_miss {F : Grounded.AF} {S : List Nat}
    {b c : Nat} (h : F.attack c b = false) :
    anyAttackerC F (c :: S) b
      = ((anyAttackerC F S b).1, 1 + (anyAttackerC F S b).2) := by
  simp [anyAttackerC, h]

theorem anyAttackerC_prefix {F : Grounded.AF} {S₁ S₂ : List Nat}
    {b : Nat} (h : ∀ c ∈ S₁, F.attack c b = false) :
    anyAttackerC F (S₁ ++ S₂) b
      = ((anyAttackerC F S₂ b).1, S₁.length + (anyAttackerC F S₂ b).2) := by
  induction S₁ with
  | nil => simp
  | cons c rest ih =>
      rw [List.cons_append, anyAttackerC_cons_miss (h c List.mem_cons_self),
        ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
      refine Prod.ext rfl ?_
      simp only [List.length_cons]
      omega

theorem defendedAuxC_cons_miss {F : Grounded.AF} {S : List Nat}
    {a b : Nat} {l : List Nat} (h : F.attack b a = false) :
    defendedAuxC F S a (b :: l)
      = ((defendedAuxC F S a l).1, 1 + (defendedAuxC F S a l).2) := by
  simp [defendedAuxC, h]

theorem defendedAuxC_cons_defended {F : Grounded.AF} {S : List Nat}
    {a b : Nat} {l : List Nat} (h : F.attack b a = true)
    (hany : (anyAttackerC F S b).1 = true) :
    defendedAuxC F S a (b :: l)
      = ((defendedAuxC F S a l).1,
          (1 + (anyAttackerC F S b).2) + (defendedAuxC F S a l).2) := by
  simp [defendedAuxC, h, hany]

theorem defendedAuxC_no_attack {F : Grounded.AF} {S : List Nat}
    {a : Nat} {l : List Nat} (h : ∀ b ∈ l, F.attack b a = false) :
    defendedAuxC F S a l = (true, l.length) := by
  induction l with
  | nil => rfl
  | cons b rest ih =>
      rw [defendedAuxC_cons_miss (h b List.mem_cons_self),
        ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
      refine Prod.ext rfl ?_
      simp only [List.length_cons]
      omega

theorem defendedAuxC_append_true {F : Grounded.AF} {S : List Nat}
    {a : Nat} {l₁ l₂ : List Nat} (h : (defendedAuxC F S a l₁).1 = true) :
    defendedAuxC F S a (l₁ ++ l₂)
      = ((defendedAuxC F S a l₂).1,
          (defendedAuxC F S a l₁).2 + (defendedAuxC F S a l₂).2) := by
  induction l₁ with
  | nil => simp [defendedAuxC]
  | cons b rest ih =>
      by_cases hab : F.attack b a = true
      · by_cases hany : (anyAttackerC F S b).1 = true
        · have hrest : (defendedAuxC F S a rest).1 = true := by
            rw [defendedAuxC_cons_defended hab hany] at h
            exact h
          rw [List.cons_append, defendedAuxC_cons_defended hab hany,
            defendedAuxC_cons_defended hab hany, ih hrest]
          refine Prod.ext rfl ?_
          omega
        · exfalso
          rw [Bool.not_eq_true] at hany
          rw [show defendedAuxC F S a (b :: rest)
              = (false, 1 + (anyAttackerC F S b).2) from by
            simp [defendedAuxC, hab, hany]] at h
          exact absurd h (by simp)
      · rw [Bool.not_eq_true] at hab
        have hrest : (defendedAuxC F S a rest).1 = true := by
          rw [defendedAuxC_cons_miss hab] at h
          exact h
        rw [List.cons_append, defendedAuxC_cons_miss hab,
          defendedAuxC_cons_miss hab, ih hrest]
        refine Prod.ext rfl ?_
        omega

theorem defendedAuxC_uniform {F : Grounded.AF} {S : List Nat}
    {a : Nat} {l : List Nat} {c : Nat}
    (hatt : ∀ b ∈ l, F.attack b a = true)
    (hscan : ∀ b ∈ l, anyAttackerC F S b = (true, c)) :
    defendedAuxC F S a l = (true, l.length * (1 + c)) := by
  induction l with
  | nil => simp [defendedAuxC]
  | cons b rest ih =>
      have h2 := hscan b List.mem_cons_self
      rw [defendedAuxC_cons_defended (hatt b List.mem_cons_self) (by rw [h2]),
        ih (fun x hx => hatt x (List.mem_cons_of_mem _ hx))
          (fun x hx => hscan x (List.mem_cons_of_mem _ hx)), h2]
      refine Prod.ext rfl ?_
      rw [List.length_cons, Nat.succ_mul]
      exact Nat.add_comm _ _

theorem stepAuxC_cost_append {F : Grounded.AF} {S : List Nat}
    (l₁ l₂ : List Nat) :
    (stepAuxC F S (l₁ ++ l₂)).2 = (stepAuxC F S l₁).2 + (stepAuxC F S l₂).2 := by
  induction l₁ with
  | nil => simp [stepAuxC]
  | cons a rest ih =>
      rw [List.cons_append, stepAuxC_cost_cons, stepAuxC_cost_cons, ih]
      omega

theorem stepAuxC_cost_uniform {F : Grounded.AF} {S : List Nat}
    {l : List Nat} {c : Nat} (h : ∀ a ∈ l, (defendedC F S a).2 = c) :
    (stepAuxC F S l).2 = l.length * c := by
  induction l with
  | nil => simp [stepAuxC]
  | cons a rest ih =>
      rw [stepAuxC_cost_cons, h a List.mem_cons_self,
        ih fun x hx => h x (List.mem_cons_of_mem _ hx),
        List.length_cons, Nat.succ_mul]
      exact Nat.add_comm _ _

/-! ### Universal quadratic lower bound and exact cubic counterexample

A defense scan may stop after a single query, but it can never stop before
one. So on a nonempty carrier every `defendedC` pays at least one query, every
`stepC` pays at least `|args|`, and the `|args|`-round grounded run pays at
least `|args|²`. The fixed-size regression below separately falsifies the
rejected exact pointwise cubic inequality at `n = 2`; it makes no asymptotic
tightness claim. -/

theorem defendedAuxC_cost_ge_one (b' : Arg) (rest : List Arg) :
    1 ≤ (defendedAuxC F S a (b' :: rest)).2 := by
  by_cases hab : F.attack b' a = true
  · by_cases hany : (anyAttackerC F S b').1 = true
    · simp only [defendedAuxC, hab, hany, if_pos]
      omega
    · simp only [Bool.not_eq_true] at hany
      simp only [defendedAuxC, hab, hany, if_pos, Bool.false_eq_true, if_false]
      omega
  · simp only [Bool.not_eq_true] at hab
    simp only [defendedAuxC, hab, Bool.false_eq_true, if_false]
    omega

theorem defendedC_cost_ge_one (h : 0 < F.args.length) : 1 ≤ (defendedC F S a).2 := by
  unfold defendedC
  cases hargs : F.args with
  | nil => rw [hargs] at h; exact absurd h (by simp)
  | cons b' rest => exact defendedAuxC_cost_ge_one b' rest

theorem stepAuxC_cost_ge (hne : 0 < F.args.length) (l : List Arg) :
    l.length ≤ (stepAuxC F S l).2 := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a' rest ih =>
    have h1 : 1 ≤ (defendedC F S a').2 := defendedC_cost_ge_one hne
    rw [stepAuxC_cost_cons, List.length_cons]
    omega

theorem stepC_cost_ge : F.args.length ≤ (stepC F S).2 := by
  unfold stepC
  by_cases h : 0 < F.args.length
  · exact stepAuxC_cost_ge h F.args
  · rw [Nat.eq_zero_of_not_pos h]
    exact Nat.zero_le _

theorem iterC_cost_ge (F : AF) (k : Nat) : k * F.args.length ≤ (iterC F k).2 := by
  induction k with
  | zero => simp [iterC]
  | succ k ih =>
    show _ ≤ (iterC F k).2 + (stepC F (iterC F k).1).2
    rw [Nat.succ_mul]
    exact Nat.add_le_add ih stepC_cost_ge

theorem groundedC_cost_ge : F.args.length ^ 2 ≤ (groundedC F).2 := by
  have hpow : F.args.length ^ 2 = F.args.length * F.args.length := by
    rw [show (2 : Nat) = 1 + 1 from rfl, Nat.pow_succ, Nat.pow_one]
  rw [hpow]
  exact iterC_cost_ge F F.args.length

/-- The two-node all-attacks framework: two arguments, every attack edge
present (self-attacks included). -/
def twoNodeAllAttacks : AF := { args := [0, 1], attack := fun _ _ => true }

/-- Negative regression against the rejected exact pointwise cubic inequality
(constraint 4), kept next to `groundedC_cost_ge`: the full grounded run on
the two-node all-attacks framework costs exactly `4 = 2²` attack queries —
each of the two rounds pays one query per node, because every defense scan
stops at its first undefeated attacker — strictly below `2³ = 8`. This
fixed-size fixture makes no claim about asymptotic lower bounds. -/
theorem groundedC_twoNodeAllAttacks_cost :
    (groundedC twoNodeAllAttacks).2 = 4 := by decide

/-! ### The shared carrier-status evaluator (issue #209)

`Grounded.statusC` recomputes the grounded extension inside every per-member
`labelC` read.  The evaluator below computes `groundedC F` **once** — and
only after the empty-support guard — then feeds the shared result to every
label query, preserving `statusC`'s observable guard order exactly: empty
support first, then an `inn` pass over the support, then an `undec` pass,
then `defeated`.  Only `F.attack` evaluations count, under the same
short-circuit discipline as the mirrors above; grounded-membership tests
(`memB`) are not attack queries and cost zero. -/

/-- Instrumented mirror of the `out` scan
`F.args.any (fun c => memB c (grounded F) && F.attack c a)` inside
`Grounded.labelC`, over a shared grounded result `G`.  Only the second
conjunct is an attack query, and `&&` short-circuits left-to-right: a
candidate outside `G` never evaluates `F.attack`, and the scan stops at its
first confirmed attacker, exactly like `List.any`. -/
def outScanC (F : AF) (G : List Arg) (a : Arg) : List Arg → Bool × Nat
  | [] => (false, 0)
  | c :: rest =>
    if Grounded.memB c G then
      if F.attack c a then (true, 1)
      else
        let r := outScanC F G a rest
        (r.1, 1 + r.2)
    else outScanC F G a rest

/-- Instrumented `Grounded.labelC` over a shared grounded result `G`: the
`inn` guard is a free membership test; a non-member pays exactly its `out`
scan.  At `G = Grounded.grounded F` this is the original label
(`labelFromGroundedC_fst`). -/
def labelFromGroundedC (F : AF) (G : List Arg) (a : Arg) : Label × Nat :=
  if Grounded.memB a G then (Label.inn, 0)
  else
    let r := outScanC F G a F.args
    (if r.1 then Label.out else Label.undec, r.2)

theorem outScanC_fst (F : AF) (G : List Arg) (a : Arg) (l : List Arg) :
    (outScanC F G a l).1 = l.any (fun c => Grounded.memB c G && F.attack c a) := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    by_cases hm : Grounded.memB c G = true
    · by_cases hc : F.attack c a = true
      · simp [outScanC, hm, hc]
      · simp only [Bool.not_eq_true] at hc
        simp [outScanC, hm, hc, ih]
    · simp only [Bool.not_eq_true] at hm
      simp [outScanC, hm, ih]

theorem outScanC_cost_le (F : AF) (G : List Arg) (a : Arg) (l : List Arg) :
    (outScanC F G a l).2 ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons c rest ih =>
    by_cases hm : Grounded.memB c G = true
    · by_cases hc : F.attack c a = true
      · simp only [outScanC, hm, hc, if_pos, List.length_cons]
        omega
      · simp only [Bool.not_eq_true] at hc
        simp only [outScanC, hm, hc, if_pos, Bool.false_eq_true, if_false,
          List.length_cons]
        omega
    · simp only [Bool.not_eq_true] at hm
      simp only [outScanC, hm, Bool.false_eq_true, if_false, List.length_cons]
      omega

/-- **Label agreement over the shared grounded result**: at
`G = Grounded.grounded F` the shared label is `labelC`. -/
theorem labelFromGroundedC_fst (F : AF) (a : Arg) :
    (labelFromGroundedC F (Grounded.grounded F) a).1 = Grounded.labelC F a := by
  unfold labelFromGroundedC Grounded.labelC
  by_cases hm : Grounded.memB a (Grounded.grounded F) = true
  · simp [hm]
  · simp only [Bool.not_eq_true] at hm
    simp [hm, outScanC_fst]

/-- One shared label read pays at most one full `out` scan of the carrier. -/
theorem labelFromGroundedC_cost_le (F : AF) (G : List Arg) (a : Arg) :
    (labelFromGroundedC F G a).2 ≤ F.args.length := by
  unfold labelFromGroundedC
  by_cases hm : Grounded.memB a G = true
  · simp only [hm, if_pos]
    exact Nat.zero_le _
  · simp only [Bool.not_eq_true] at hm
    simp only [hm, Bool.false_eq_true, if_false]
    exact outScanC_cost_le F G a F.args

/-- Instrumented mirror of one `statusC` support pass
`c.support.any (fun a => labelC F a == lbl)`, with every label computed from
the shared grounded result `G`.  The pass stops at the first match, exactly
like `List.any`; each visited member pays its label read. -/
def supportScanC (F : AF) (G : List Arg) (lbl : Label) : List Arg → Bool × Nat
  | [] => (false, 0)
  | a :: rest =>
    let r := labelFromGroundedC F G a
    if r.1 == lbl then (true, r.2)
    else
      let s := supportScanC F G lbl rest
      (s.1, r.2 + s.2)

theorem supportScanC_fst (F : AF) (lbl : Label) (l : List Arg) :
    (supportScanC F (Grounded.grounded F) lbl l).1
      = l.any (fun a => Grounded.labelC F a == lbl) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    have hl := labelFromGroundedC_fst F a
    by_cases h : (Grounded.labelC F a == lbl) = true
    · simp [supportScanC, hl, h]
    · simp only [Bool.not_eq_true] at h
      simp [supportScanC, hl, h, ih]

theorem supportScanC_cost_le (F : AF) (G : List Arg) (lbl : Label)
    (l : List Arg) :
    (supportScanC F G lbl l).2 ≤ l.length * F.args.length := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a rest ih =>
    have hr := labelFromGroundedC_cost_le F G a
    have hexp : (a :: rest).length * F.args.length
        = rest.length * F.args.length + F.args.length := by
      rw [List.length_cons, Nat.succ_mul]
    rw [hexp]
    by_cases h : ((labelFromGroundedC F G a).1 == lbl) = true
    · simp only [supportScanC, h, if_pos]
      omega
    · simp only [Bool.not_eq_true] at h
      simp only [supportScanC, h, Bool.false_eq_true, if_false]
      omega

/-- **The shared status evaluator**.  Guard order is
exactly `Grounded.statusC`'s: empty support first, then an `inn` pass, then
an `undec` pass, then `defeated`.  `groundedC F` is computed at most once —
the single `let` below — and only after the empty-support guard; both
passes read the one shared result.  A hit in the `inn` pass short-circuits
the `undec` pass, exactly as `statusC`'s `if`-chain does. -/
def statusSharedC (F : AF) (c : Claim) : Status × Nat :=
  if c.support = [] then (Status.gap, 0)
  else
    let g := groundedC F
    let inn := supportScanC F g.1 Label.inn c.support
    if inn.1 then (Status.justified, g.2 + inn.2)
    else
      let und := supportScanC F g.1 Label.undec c.support
      if und.1 then (Status.contested, g.2 + (inn.2 + und.2))
      else (Status.defeated, g.2 + (inn.2 + und.2))

/-- **Status agreement**: sharing the grounded result changes no answer. -/
theorem statusSharedC_fst (F : AF) (c : Claim) :
    (statusSharedC F c).1 = Grounded.statusC F c := by
  have hscan : ∀ lbl, (supportScanC F (groundedC F).1 lbl c.support).1
      = c.support.any (fun a => Grounded.labelC F a == lbl) := fun lbl => by
    rw [groundedC_fst]
    exact supportScanC_fst F lbl c.support
  unfold statusSharedC Grounded.statusC
  by_cases hs : c.support = []
  · rw [if_pos hs, if_pos hs]
  · rw [if_neg hs, if_neg hs]
    by_cases h1 : c.support.any (fun a => Grounded.labelC F a == Label.inn) = true
    · simp only [hscan, h1, if_pos]
    · simp only [Bool.not_eq_true] at h1
      by_cases h2 : c.support.any
          (fun a => Grounded.labelC F a == Label.undec) = true
      · simp only [hscan, h1, h2, Bool.false_eq_true, if_false, if_pos]
      · simp only [Bool.not_eq_true] at h2
        simp only [hscan, h1, h2, Bool.false_eq_true, if_false]

/-- **The generic Claim bound**: one grounded run plus two support passes.
**INTERNAL** (the cost-results citation discipline in
`docs/theory-m2b-complexity.md`): this bound
is generic-claim accounting; the paper must **not** cite it as the
restricted-class headline — the paper-citable GroundedStatus upper theorem
for the carrier surface is `carrierStatusC_cost_le`. -/
theorem statusSharedC_cost_le (F : AF) (c : Claim) :
    (statusSharedC F c).2 ≤
      F.args.length ^ 3 * (1 + F.args.length) + 2 * c.support.length * F.args.length := by
  have hg : (groundedC F).2 ≤ F.args.length ^ 3 * (1 + F.args.length) :=
    groundedC_cost_le
  have hin := supportScanC_cost_le F (groundedC F).1 Label.inn c.support
  have hun := supportScanC_cost_le F (groundedC F).1 Label.undec c.support
  have h2 : 2 * c.support.length * F.args.length
      = c.support.length * F.args.length + c.support.length * F.args.length := by
    rw [Nat.mul_assoc, Nat.two_mul]
  unfold statusSharedC
  by_cases hs : c.support = []
  · rw [if_pos hs]
    exact Nat.zero_le _
  · rw [if_neg hs, h2]
    by_cases hi : (supportScanC F (groundedC F).1 Label.inn c.support).1 = true
    · simp only [hi, if_pos]
      exact Nat.add_le_add hg (Nat.le_trans hin (Nat.le_add_right _ _))
    · simp only [Bool.not_eq_true] at hi
      simp only [hi, Bool.false_eq_true, if_false]
      by_cases hu : (supportScanC F (groundedC F).1 Label.undec c.support).1 = true
      · simp only [hu, if_pos]
        exact Nat.add_le_add hg (Nat.add_le_add hin hun)
      · simp only [Bool.not_eq_true] at hu
        simp only [hu, Bool.false_eq_true, if_false]
        exact Nat.add_le_add hg (Nat.add_le_add hin hun)

/-- On nonempty complete support the shared evaluator takes the grounded
branch, so its count includes the complete `groundedC` count (used by the
quartic transfer in `Lara.Examples.Complexity`). -/
theorem statusSharedC_cost_ge_grounded (F : AF) (c : Claim)
    (hs : c.support ≠ []) :
    (groundedC F).2 ≤ (statusSharedC F c).2 := by
  unfold statusSharedC
  rw [if_neg hs]
  by_cases hi : (supportScanC F (groundedC F).1 Label.inn c.support).1 = true
  · simp only [hi, if_pos]
    exact Nat.le_add_right _ _
  · simp only [Bool.not_eq_true] at hi
    simp only [hi, Bool.false_eq_true, if_false]
    by_cases hu : (supportScanC F (groundedC F).1 Label.undec c.support).1 = true
    · simp only [hu, if_pos]
      exact Nat.le_add_right _ _
    · simp only [Bool.not_eq_true] at hu
      simp only [hu, Bool.false_eq_true, if_false]
      exact Nat.le_add_right _ _

/-! ### The carrier query (issue #209) -/

open Invariants (eraseAF claim)

/-- A carrier claim's complete support is a `filterMap` of the node list,
so it never exceeds the node count. -/
theorem support_length_le (canon : String → String)
    (F : Invariants.StructuredAF) (p : Atom) :
    (Invariants.support canon F p).length ≤ F.size := by
  unfold Invariants.support
  have h := List.length_filterMap_le
    (fun entry : Atom × Nat =>
      if equiv canon entry.1 p then some entry.2 else none)
    F.nodes.zipIdx
  rw [List.length_zipIdx] at h
  exact h

/-- **The carrier status query**: the shared
evaluator on the erased carrier at the carrier claim for `p`.  This is the
only exposed status surface; the generic `statusSharedC` bound is internal
accounting behind it. -/
def carrierStatusC (canon : String → String) (F : Invariants.StructuredAF)
    (p : Atom) : Status × Nat :=
  statusSharedC (eraseAF F) (claim canon F p)

/-- **Carrier-status agreement**: the shared carrier
query returns exactly `Invariants.status`. -/
theorem carrierStatusC_fst (canon : String → String)
    (F : Invariants.StructuredAF) (p : Atom) :
    (carrierStatusC canon F p).1 = Invariants.status canon F p :=
  statusSharedC_fst (eraseAF F) (claim canon F p)

/-- **The paper-citable GroundedStatus upper theorem**
(`docs/theory-m2b-complexity.md`): the carrier status query pays at most
`n³(1 + n) + 2n²` attack
queries for `n = F.size`.  Cite this — not the generic Claim bound
`statusSharedC_cost_le` — as the restricted-class headline. -/
theorem carrierStatusC_cost_le (canon : String → String)
    (F : Invariants.StructuredAF) (p : Atom) :
    (carrierStatusC canon F p).2 ≤ F.size ^ 3 * (1 + F.size) + 2 * F.size ^ 2 := by
  unfold carrierStatusC
  have h := statusSharedC_cost_le (eraseAF F) (claim canon F p)
  have hargs : (eraseAF F).args.length = F.size := by
    show (List.range F.size).length = F.size
    exact List.length_range
  rw [hargs] at h
  refine Nat.le_trans h (Nat.add_le_add_left ?_ _)
  have hsup : (claim canon F p).support.length ≤ F.size :=
    support_length_le canon F p
  have hpow : F.size ^ 2 = F.size * F.size := by
    rw [show (2 : Nat) = 1 + 1 from rfl, Nat.pow_succ, Nat.pow_one]
  rw [hpow, ← Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsup)

end Lara.Complexity
