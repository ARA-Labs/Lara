/-
Executable witnesses for the `Query_κ` well-sortedness refinement (issue #307).

The headline fixture is **one world at which PW0 reports `gap` three times for
three different reasons**, and at which the refinement reports three different
things. It reuses `Lara.Examples.PW`'s overlapping-fields pair unchanged —
`sigmaEx` declares `p`, `q`, `s` (and the sort `Item` with the constructor `z`);
`sigmaOverlap` declares `p`, `q`, `r` and *not* `s` — because that pair already
exists precisely to make "neither vocabulary contains the other" concrete, and
`overlap_local_gap` already pins the PW0 answer this module refines.

At `wOverlap`, whose single admitted argument concludes `q`:

| authored claim | PW0 (`cmpStatus`) | refined (`report`) |
|---|---|---|
| `p()` | `gap` | `unaddressed` — a genuine query nothing here argues for |
| `s()` | `gap` | `outOfVocabulary "s"` — this field cannot state it |
| `q(z)` | `gap` | `illSorted "q"` — `q` is nullary here |
| `q()` | `justified` | `observed justified` — unchanged |

The bridge half does the same for the three posing faults, and
`sorted_s_targetQuery` is the sharpened form of `overlap_translationUndefined`:
PW0 could only say the translation was undefined, which conflates "outside the
bridge's symbol map" with "the target field cannot state this". The refinement
names which.

Everything decidable is closed by `decide`; `native_decide` is banned by the
axiom audit. `sortedWorld_wOverlap`, the two `Presents`-free satisfaction cells
and the erasure instantiation are ordinary proofs.
-/

import Lara.Examples.PW
import Lara.PW.Sorted

namespace Lara.Examples.PWSorted

open Lara.Support
open Lara.PW Lara.PW.Instance Lara.PW.Sorted
open Lara.Examples Lara.Examples.PW
open Lara.Grounded (Status)

/-! ### The four conditions, separated at one world -/

/-- `q` applied to the constructor `z`. Ill-sorted in **both** signatures: `q`
is declared nullary in each, so the argument list fails its declared sort
vector. (`z` is undeclared in `sigmaOverlap` too, but the arity clause fires
first and either way the atom is not a query.) -/
def qOfZ : Atom := .atom "q" (.cons (.con "z" .nil) .nil)

/-- A predicate no signature in this fixture declares. -/
def rNullary : Atom := .atom "r" .nil

/-! #### PW0's answer: one report for three conditions -/

/-- A genuine query of `sigmaOverlap` that this world argues nothing for. -/
theorem pw0_gap_p : cmpStatus wOverlap pA = Status.gap := by decide

/-- A claim `sigmaOverlap` cannot state. This is `overlap_local_gap`, restated
here so the three PW0 answers sit together. -/
theorem pw0_gap_s : cmpStatus wOverlap pC = Status.gap := by decide

/-- An ill-sorted claim. -/
theorem pw0_gap_illSorted : cmpStatus wOverlap qOfZ = Status.gap := by decide

/-- The one claim this world does argue for. -/
theorem pw0_justified_q : cmpStatus wOverlap pB = Status.justified := by decide

/-! #### The refined answer: three reports, and the fourth unchanged -/

theorem report_p : report wOverlap pA = .unaddressed := by decide

theorem report_s : report wOverlap pC = .outOfVocabulary ⟨"s"⟩ := by decide

theorem report_illSorted : report wOverlap qOfZ = .illSorted ⟨"q"⟩ := by decide

theorem report_q : report wOverlap pB = .observed Status.justified := by decide

/-- **The split is real.** The three claims PW0 answered `gap` for get three
pairwise distinct reports, so the refinement is not a renaming of one answer. -/
theorem reports_distinct :
    report wOverlap pA ≠ report wOverlap pC ∧
    report wOverlap pC ≠ report wOverlap qOfZ ∧
    report wOverlap pA ≠ report wOverlap qOfZ := by decide

/-- **And it is a split, not a change.** Every one of the three is still a PW0
`gap`: the refinement partitions one report rather than moving any answer.
`report_ne_observed_iff_gap` is the general statement; this is its instance. -/
theorem split_not_change :
    (∀ s, report wOverlap pA ≠ .observed s) ∧
    (∀ s, report wOverlap pC ≠ .observed s) ∧
    (∀ s, report wOverlap qOfZ ≠ .observed s) :=
  ⟨fun s => by rw [report_p]; simp,
   fun s => by rw [report_s]; simp,
   fun s => by rw [report_illSorted]; simp⟩

/-- The overlap world's declared conclusions are all well-sorted, so it meets
the hypothesis `report_ne_observed_iff_gap` needs. Discharged through
`sortedWorld_of_nodes`, whose `canon = id` premise the fixture satisfies. -/
theorem sortedWorld_wOverlap : SortedWorld wOverlap :=
  sortedWorld_of_nodes rfl wOverlap (by decide)

/-! ### The three posing faults at a bridge

Source field `ctxT7` (signature `sigmaEx`), target field `ctxOverlap`
(signature `sigmaOverlap`), identity symbol map except where noted. -/

/-- The identity symbol map: every symbol is in the bridge's vocabulary. -/
def symId : SymMap := SymMap.id

/-- A symbol map that is undefined at `q` — the bridge simply does not carry
that predicate across. -/
def symNoQ : SymMap where
  predMap := fun p => if p = "q" then none else some p
  conMap := some

/-- **Source fault, out of vocabulary.** `r` is not in `sigmaEx`, so the claim
never becomes a query and no target world is consulted. -/
theorem sorted_r_sourceQuery :
    crossComparePosed sigmaEx sigmaOverlap symId rNullary [wOverlap]
        (fun _ => true) (fun v q => cmpStatus v q.val)
      = .notPosable (.sourceQuery (.undeclaredPredicate ⟨"r"⟩)) := by decide

/-- **Source fault, ill-sorted.** `q` is declared in `sigmaEx`, nullary. -/
theorem sorted_qz_sourceQuery :
    crossComparePosed sigmaEx sigmaOverlap symId qOfZ [wOverlap]
        (fun _ => true) (fun v q => cmpStatus v q.val)
      = .notPosable (.sourceQuery (.illSortedArguments ⟨"q"⟩)) := by decide

/-- **Bridge fault.** `q` *is* a query at both ends, but this bridge's symbol
map does not carry it — and the report names the symbol, in the predicate
namespace. -/
theorem sorted_q_bridgeVocabulary :
    crossComparePosed sigmaEx sigmaOverlap symNoQ pB [wOverlap]
        (fun _ => true) (fun v q => cmpStatus v q.val)
      = .notPosable (.bridgeVocabulary (.pred ⟨"q"⟩)) := by decide

/-- **Target fault** — the sharpened `overlap_translationUndefined`. `s` is a
query of the source field and the identity map carries it, but the target field
cannot state it. PW0 reported `translationUndefined`, which conflates this with
the previous case; here the two have different reports, and the target one
names the offending predicate. -/
theorem sorted_s_targetQuery :
    crossComparePosed sigmaEx sigmaOverlap symId pC [wOverlap]
        (fun _ => true) (fun v q => cmpStatus v q.val)
      = .notPosable (.targetQuery (.undeclaredPredicate ⟨"s"⟩)) := by decide

/-! #### The target-side arity fault, and the constructor namespace

The two cells above leave two branches of the bridge half unexercised. The
target-query fault has only ever been *undeclared at the target*, which a plain
vocabulary-membership test would also catch; and the vocabulary fault has only
ever named a predicate. A signature pair declaring the same predicate at both
ends with **different arities** closes the first, and a symbol map that carries
the predicate but not its argument's constructor closes the second. -/

/-- A source signature declaring `t` as a *unary* predicate over `Item`. -/
def sigmaAritySrc : Lara.Sigma.Sigma :=
  { sorts := ["Item"], cons := [⟨⟨"z"⟩, [], .decl "Item"⟩]
  , preds := [⟨⟨"t"⟩, [.decl "Item"]⟩] }

/-- The target declares `t` too — *nullary*. Vocabulary membership is therefore
satisfied at both ends, and the only thing that can reject `t(z)` here is the
declared sort vector. -/
def sigmaArityTgt : Lara.Sigma.Sigma :=
  { sorts := ["Item"], cons := [⟨⟨"z"⟩, [], .decl "Item"⟩]
  , preds := [⟨⟨"t"⟩, []⟩] }

/-- `t` applied to `z`: a query of `sigmaAritySrc`, not one of
`sigmaArityTgt`. -/
def tOfZ : Atom := .atom "t" (.cons (.con "z" .nil) .nil)

/-- A symbol map total on predicates and undefined at the constructor `z`. -/
def symNoZ : SymMap where
  predMap := some
  conMap := fun k => if k = "z" then none else some k

/-- **Target fault, ill-sorted.** The identity map carries `t` and `z`, so the
claim is inside the bridge's vocabulary and the target signature declares its
head — and it is still not a target query, because `t` is nullary there. This
is the branch that distinguishes `trQueryFault`'s `queryFault sgT` from a
vocabulary-membership test. -/
theorem sorted_t_targetIllSorted :
    crossComparePosed sigmaAritySrc sigmaArityTgt symId tOfZ [wOverlap]
        (fun _ => true) (fun v q => cmpStatus v q.val)
      = .notPosable (.targetQuery (.illSortedArguments ⟨"t"⟩)) := by decide

/-- **Bridge fault, in the constructor namespace.** The head predicate is
carried and the target could state the claim; the argument's constructor is
what falls outside the map, and the located report says so. -/
theorem sorted_t_bridgeVocabulary_con :
    crossComparePosed sigmaAritySrc sigmaAritySrc symNoZ tOfZ [wOverlap]
        (fun _ => true) (fun v q => cmpStatus v q.val)
      = .notPosable (.bridgeVocabulary (.con ⟨"z"⟩)) := by decide

/-- The two undefined-translation cases PW0 could not tell apart get distinct
answers *from the comparison itself* — not merely distinct constructors. This
is the `reports_distinct` shape: two `crossComparePosed` applications at the
same bridge, differing only in the authored claim and the symbol map PW0 could
not distinguish between. -/
theorem bridge_and_target_faults_distinct :
    crossComparePosed sigmaEx sigmaOverlap symNoQ pB [wOverlap]
        (fun _ => true) (fun v q => cmpStatus v q.val)
      ≠ crossComparePosed sigmaEx sigmaOverlap symId pC [wOverlap]
        (fun _ => true) (fun v q => cmpStatus v q.val) := by decide

/-- **The comparison still works where PW0's did.** `q` under the identity map
is a query at both ends, and the refined interface returns PW0's unchanged
profile. -/
theorem sorted_q_compared :
    crossComparePosed sigmaEx sigmaOverlap symId pB [wOverlap]
        (fun _ => true) (fun v q => cmpStatus v q.val)
      = .compared (.comparable Status.justified []) := by decide

/-! ### A sorted frame, and its erasure to PW0 -/

/-- The two scientific fields of the fixture. -/
inductive Field | source | target
deriving DecidableEq

def ctxOf : Field → Context
  | .source => ctxT7
  | .target => ctxOverlap

/-- The sorted bridge datum: one bridge from the first field to the second,
carrying the identity symbol map. -/
def bridgeSorted : SortedBridgeData where
  K := Field
  ctx := ctxOf
  B := OneBridge
  bsrc := fun _ => .source
  btgt := fun _ => .target
  R := fun _ _ v => v = wOverlap
  accept := fun _ _ _ => True
  sym := fun _ => symId

/-- `q` as a query of each field. -/
def qSrc : Query sigmaEx := ⟨pB, by decide⟩
def qTgt : Query sigmaOverlap := ⟨pB, by decide⟩

/-- The bridge's typed translation is defined at the shared claim. -/
theorem trQuery_q : trQuery symId sigmaOverlap qSrc = some qTgt := by decide

/-- **The modal reading, at the sorted frame.** The one accepted target world
reports `q` justified, so the source world satisfies `⟨b⟩Justified(q)`. -/
theorem sorted_dia_q :
    Sat bridgeSorted.frame (cmpVal bridgeSorted)
      (.dia OneBridge.it (.status Status.justified qTgt)) wT7src :=
  ⟨wOverlap, ⟨rfl, trivial⟩, pw0_justified_q⟩

/-- **Conservativity, instantiated.** The same formula with its sorting
forgotten holds in the PW0 model underneath — `sat_erase` at this frame. -/
theorem sorted_dia_q_erased :
    Sat bridgeSorted.erase.frame (Instance.cmpVal bridgeSorted.erase)
      (eraseForm bridgeSorted
        (.dia OneBridge.it (.status Status.justified qTgt))) wT7src :=
  (sat_erase bridgeSorted (κ := Field.source) _ wT7src).mp sorted_dia_q

/-- The same cell under the source valuation, through T4 on both sides. -/
theorem sorted_dia_q_src :
    Sat bridgeSorted.frame (srcVal bridgeSorted)
      (.dia OneBridge.it (.status Status.justified qTgt)) wT7src :=
  (Sorted.sat_src_iff_cmp bridgeSorted (κ := Field.source) wT7src _).mpr
    sorted_dia_q

end Lara.Examples.PWSorted
