/-
The direction-of-goodness contract behind the `comparison` surface form
(`docs/lara-surface-grammar.md` Appendix B.3, landed as `lara-syntax@0.3`).


## What the surface form is for, and what goes wrong without it

Direction of goodness is a property of the *measurand*, not of the comparison.
Higher accuracy is better; lower perplexity, latency, error rate, and FLOPs are
better.  So "we beat the baseline" is `num_lt(base, ours)` for accuracy but
`num_lt(ours, base)` for perplexity.  Authored by hand, that conversion is
performed unaided every time and nothing checks it: a swapped argument order
still produces a well-formed artifact — one that certifies the opposite of what
was meant.  The `comparison` form exists to move that conversion from the
author to a fixed table:

  | `relation`         | `higher-is-better`  | `lower-is-better`   |
  |--------------------|---------------------|---------------------|
  | `strictly-better`  | `num_lt(base, ours)`| `num_lt(ours, base)`|
  | `at-least-as-good` | `num_le(base, ours)`| `num_le(ours, base)`|

## What this module proves

`goalOf` realizes that table over the frozen `ord@1` goal shape
(`Lara.Ord.Goal`), and `Better` states the *intended research meaning*
("ours beats base under this measurand's declared polarity") directly in terms
of `Lara.Cell`'s cross-multiplied comparisons, without mentioning `goalOf`.
The headline theorem `goalOf_iff_better` says the two agree on every one of the
four cells: the goal the form generates holds exactly when ours is better than
base in the declared sense.  `goalOf_polarity_swap` and
`goalOf_polarity_mismatch_excl` turn §1.2's hazard into formal statements — the
two polarities generate the *same relation on transposed operands*, and under a
strict relation the two never hold together, so a polarity swap cannot be
silently harmless.  The remaining lemmas are the order facts the two relations
carry: strict betterness is asymmetric (`better_excl`), mutual
at-least-as-good pins down a tie (`better_atLeastAsGood_antisymm`, the case
`examples/S3` exercises), and strict implies non-strict
(`better_strict_imp_atLeastAsGood`).

## What this module does NOT prove

This is the surface-level *direction contract*, not a theorem about the Haskell
elaborator.  Nothing here says that the elaborator maps a `comparison` block to
`goalOf`'s output, nor that its expansion is deterministic: the concrete `.lara`
parser and the structural elaborator stay **validated, not verified**
(`Lara/Admission.lean:16`), and the Lean side's entry point is the wire decoder
on an already-elaborated `.sexp` (`Lara/Driver.lean`), not the elaborator.  A
determinism theorem would first require a Lean elaborator and a differential
validation against the Haskell one; that is out of scope here.

What the Haskell side *does* do — and what makes the table above a
specification of it rather than a parallel model beside it — is **check** the
table.  `Lara.Elaborate.Comparison`'s direction-of-goodness check rejects a
`comparison-scheme` whose `recheck` rule realizes the other row than its
declared `polarity` names (grammar App. B.2).  That is a check written in
Haskell, not a proof about Haskell, so the disclaimer above stands unchanged.
What it removes is the possibility of *silent* disagreement: before that check,
a self-consistently mis-declared policy elaborated to a goal `goalOf` would
never have produced, and `goalOf_iff_better` was true of a model the shipped
elaborator was not held to.

## Why the contract is stated over `Cell.Dec`, not over surface syntax

The hazard is arithmetic, not syntactic.  Once the two measured cells are in
hand the whole contract is a claim about exact rational order, and `Cell.Dec`
is precisely where the `ord@1` family already states its relations — so the
lemmas below reuse `Lara.Ord`'s exclusivity facts and `Lara.Cell`'s order facts
verbatim instead of re-deriving arithmetic against a surface AST that would add
no content.  Like its neighbours the development stays in core Lean: no `Rat`,
no Mathlib.
-/

import Lara.Ord
import Lara.Presentation

namespace Lara.Comparison

open Lara.Cell (Dec RatEq RatLt RatLe ratLtB ratLeB ratLtB_iff ratLeB_iff
  ratLe_iff_lt_or_eq)

/-! ### The two closed surface vocabularies -/

/-- The measurand direction used by the executable presentation AST. This is
an alias, not a parallel copy: every theorem below consumes exactly the
`Polarity` decoded by `Lara.Presentation`. -/
abbrev Polarity := Lara.Presentation.Polarity

/-- The comparison relation used by the executable presentation AST. As with
`Polarity`, definitional equality is the cross-module correspondence. -/
abbrev Relation := Lara.Presentation.Relation

/-- Which `ord@1` family member each surface relation generates.  Polarity does
*not* appear: the relation is chosen here and here only, so the sole thing
polarity can change downstream is the argument order. -/
def Relation.rel : Relation → Lara.Ord.Rel
  | .strictlyBetter => .lt
  | .atLeastAsGood => .le

/-! ### The generated goal (the B.3 lookup contract) -/

/-- The goal a `comparison` block expands to, given the declared relation, the
measurand's polarity, and the two measured cells.  This is Appendix B.3's 2×2
table verbatim: the relation comes from `Relation.rel` alone, and polarity only
transposes the operands — `(base, ours)` under `higher-is-better`,
`(ours, base)` under `lower-is-better`. -/
def goalOf (rel : Relation) (pol : Polarity) (ours base : Dec) : Lara.Ord.Goal :=
  match pol with
  | .higherIsBetter => ⟨rel.rel, base, ours⟩
  | .lowerIsBetter => ⟨rel.rel, ours, base⟩

/-- A generated goal holds when its family member holds of its two operands.
`Lara.Ord.RelHolds` takes the relation and the two cells separately; this is
the same statement bundled at the `Goal` shape, which is how the surface form
sees it. -/
def GoalHolds (g : Lara.Ord.Goal) : Prop :=
  Lara.Ord.RelHolds g.rel g.left g.right

/-! ### The intended research meaning

Defined independently of `goalOf` — directly in terms of the cross-multiplied
comparisons — so that `goalOf_iff_better` below is an agreement statement
between two separately given definitions rather than a restatement of one. -/

/-- "Ours is better than base", in the sense the author declared: strictly or
non-strictly, on a measurand where higher or lower is the good direction. -/
def Better : Relation → Polarity → Dec → Dec → Prop
  | .strictlyBetter, .higherIsBetter, ours, base => RatLt base ours
  | .strictlyBetter, .lowerIsBetter, ours, base => RatLt ours base
  | .atLeastAsGood, .higherIsBetter, ours, base => RatLe base ours
  | .atLeastAsGood, .lowerIsBetter, ours, base => RatLe ours base

/-- Decidable mirror of `Better`, built from `Lara.Cell`'s Boolean
comparisons — the `decide`-level form an executable check would use. -/
def betterB : Relation → Polarity → Dec → Dec → Bool
  | .strictlyBetter, .higherIsBetter, ours, base => ratLtB base ours
  | .strictlyBetter, .lowerIsBetter, ours, base => ratLtB ours base
  | .atLeastAsGood, .higherIsBetter, ours, base => ratLeB base ours
  | .atLeastAsGood, .lowerIsBetter, ours, base => ratLeB ours base

theorem betterB_iff (rel : Relation) (pol : Polarity) (ours base : Dec) :
    betterB rel pol ours base = true ↔ Better rel pol ours base := by
  cases rel <;> cases pol
  · exact ratLtB_iff base ours
  · exact ratLtB_iff ours base
  · exact ratLeB_iff base ours
  · exact ratLeB_iff ours base

/-! ### The headline: the generated goal means what was declared -/

/-- **The direction-of-goodness contract.**  The goal a `comparison` block
generates holds exactly when "ours is better than base" holds in the sense the
author declared — for every (relation, polarity) cell of the B.3 table.  The
two sides are given by separate definitions (`Better` never mentions `goalOf`),
so this is a genuine agreement statement; it discharges by computation on the
four closed cells, which is what a lookup contract should do. -/
theorem goalOf_iff_better (rel : Relation) (pol : Polarity) (ours base : Dec) :
    GoalHolds (goalOf rel pol ours base) ↔ Better rel pol ours base := by
  cases rel <;> cases pol <;> exact Iff.rfl

/-! ### The no-silent-swap lemmas (§1.2's hazard, made formal) -/

/-- The two polarities generate the **same relation on transposed operands** —
nothing else about the goal changes.  This is the precise sense in which a
mis-declared polarity is exactly an argument swap: the artifact stays
well-formed and the family member stays the same, so no downstream check on the
goal's *shape* can catch the error. -/
theorem goalOf_polarity_swap (rel : Relation) (ours base : Dec) :
    (goalOf rel .higherIsBetter ours base).rel
        = (goalOf rel .lowerIsBetter ours base).rel ∧
      (goalOf rel .higherIsBetter ours base).left
        = (goalOf rel .lowerIsBetter ours base).right ∧
      (goalOf rel .higherIsBetter ours base).right
        = (goalOf rel .lowerIsBetter ours base).left :=
  ⟨rfl, rfl, rfl⟩

/-- The same swap at the level of meaning: being better on a
`higher-is-better` measurand is being *worse* on a `lower-is-better` one.  So
the polarity field is not decoration — it selects which of two contradictory
readings the artifact asserts. -/
theorem better_polarity_swap (rel : Relation) (ours base : Dec) :
    Better rel .higherIsBetter ours base ↔ Better rel .lowerIsBetter base ours := by
  cases rel <;> exact Iff.rfl

/-- **The hazard.**  If ours genuinely outperforms base on a
`higher-is-better` measurand, the goal generated under the *wrong* polarity
cannot hold — and symmetrically.  A polarity swap therefore never merely
weakens the claim: it certifies the opposite one. -/
theorem goalOf_polarity_mismatch_excl {ours base : Dec}
    (h : GoalHolds (goalOf .strictlyBetter .higherIsBetter ours base)) :
    ¬ GoalHolds (goalOf .strictlyBetter .lowerIsBetter ours base) := by
  intro h2
  exact Lara.Ord.lt_excl_lt h h2

/-! ### Order facts carried by the two relations

Each reuses the `ord@1` / `Lara.Cell` arithmetic rather than reproving it. -/

/-- Strict betterness is asymmetric, under either polarity: at most one of two
systems strictly outperforms the other on a given measurand. -/
theorem better_excl {pol : Polarity} {a b : Dec}
    (h : Better .strictlyBetter pol a b) : ¬ Better .strictlyBetter pol b a := by
  cases pol
  · intro h2; exact Lara.Ord.lt_excl_lt h h2
  · intro h2; exact Lara.Ord.lt_excl_lt h2 h

/-- The tie case (`examples/S3`): if each of two systems is at-least-as-good as
the other, they are equal as rationals.  This is why mutual non-inferiority is a
consequence, not a conflict. -/
theorem better_atLeastAsGood_antisymm {pol : Polarity} {a b : Dec}
    (h1 : Better .atLeastAsGood pol a b) (h2 : Better .atLeastAsGood pol b a) :
    RatEq a b := by
  cases pol
  · exact Lara.Ord.le_le_iff_eq h2 h1
  · exact Lara.Ord.le_le_iff_eq h1 h2

/-- Strictly better implies at least as good, under either polarity — so an
author who has the stronger claim can always weaken it without re-deriving the
direction. -/
theorem better_strict_imp_atLeastAsGood {pol : Polarity} {a b : Dec}
    (h : Better .strictlyBetter pol a b) : Better .atLeastAsGood pol a b := by
  cases pol
  · exact (ratLe_iff_lt_or_eq _ _).mpr (Or.inl h)
  · exact (ratLe_iff_lt_or_eq _ _).mpr (Or.inl h)

end Lara.Comparison
