/-
Conservative reporting with located holes (spec §4.3,
`docs/located-gap-decision.md` §5): kernel-checked witnesses for the reference
carrier `D`, the checked carrier `K` and the seed
`(D \ K) ∪ {j ∈ K | ∃ i ∈ K, G.attack i j ∧ ¬ F.attack i j}`.

Each fixture evaluates the exact production `BlockedProgram.blockedQueries`
with the production reference mask `referenceLive`, which classifies each
quarantined declaration by support inference under the full declared leaf
table `ΓEx`. The cache test `done` is membership in the complete view
`completeArgs` of the retained terms under the checked context `ΓAfter qs`
(`ΓEx` without the quarantined leaves) — the AF argument list a successful
checker returns for them (`CheckUnitSound.args_eq`); retained holes are not in
it.

* `hole_alone_quarantine_not_blocked` — quarantining a hole alone blocks
  nothing, although the hole carries a raw attack onto a claim's only support;
  `hole_alone_quarantine_blocked_under_all_declared` shows the `@0.2` carrier
  (every declaration a node) would have blocked it.
* `dropped_attack_onto_hole_blocks_support` — an attack from a retained
  complete source onto an occurrence inside a quarantined hole, dropped at the
  raw endpoint boundary, still blocks the retained complete argument sharing
  that occurrence.
* `unclassified_quarantine_blocks_support` — a quarantined term, removed for
  a declared leaf, whose support inference also fails for another reason (an
  undeclared rule) stays a conservative node and blocks the complete argument
  it attacks; it is not a typed hole.
* `clean_unit_with_hole_not_blocked` — a unit that quarantines nothing reports
  no `evidence-blocked`, whatever its holes.
-/

import Lara.Examples
import Lara.BlockedProgram
import Lara.Groups

namespace Lara.Examples.EvidenceBlocked

open Lara.Support Lara.Attack Lara.Compile Lara.Check Lara.BlockedProgram

/-- The checked context after quarantining `qs`: the declared table `ΓEx`
without the quarantined leaves. -/
def ΓAfter (qs : List LeafId) : LeafId → Option Atom :=
  fun l => if l ∈ qs then none else ΓEx l

/-- The checked cache for the declarations `keep` retains: membership in their
complete view under `ΓAfter qs`. -/
def doneFor (qs : List LeafId) (declared : List (String × SupportTerm)) :
    SupportTerm → Bool :=
  fun w => decide (w ∈ completeArgs PiEx (ΓAfter qs) registryEx
    ((retainedArguments (Groups.keepArg qs) declared).map (·.2)))

/-- A complete instance of `ruleMix` concluding `pA`: the mandatory `q1` is
discharged by `leaf l2`, and only the optional `q2` stays open. -/
def tMixDone : SupportTerm := .inst rMixId [] [] [(q1, .leaf l2)] [q2] .none

/-- A hole concluding `pA` that uses `l2`: the optional `q2` is discharged,
the mandatory `q1` is open. -/
def tMixOpen : SupportTerm := .inst rMixId [] [] [(q2, .leaf l2)] [q1] .none

/-- A hole with the complete premise `leaf l1` beside `tMixOpen`. -/
def tHoleL2 : SupportTerm := .inst rPairId [] [.leaf l1, tMixOpen] [] [] .none

theorem tMixDone_complete : argComplete PiEx ΓEx registryEx tMixDone = true := by
  decide

theorem tHolePair_hole : argHole PiEx ΓEx registryEx tHolePair = true := by
  decide

theorem tHoleL2_hole : argHole PiEx ΓEx registryEx tHoleL2 = true := by
  decide

/-! ### Quarantine of a hole alone -/

/-- Complete support `c` for `pA`, and a hole `h` using `l1` that rebuts it. -/
def declHole : List (String × SupportTerm) :=
  [("c", tMixDone), ("h", tHolePair)]

def attsHole : List Attack := [.rebut tHolePair tMixDone]

/-- Quarantining `l1` removes the hole and its attack, and nothing else. -/
def keepHole : (String × SupportTerm) → Bool := Groups.keepArg [l1]

def doneHole : SupportTerm → Bool := doneFor [l1] declHole

theorem hole_alone_reference_eq_complete :
    retainedIndices (referenceLive keepHole doneHole PiEx ΓEx registryEx)
        declHole = [0] ∧
      retainedIndices (keepComplete keepHole doneHole) declHole = [0] := by
  decide

/-- **Quarantine of a hole alone: no spurious `evidence-blocked`.** -/
theorem hole_alone_quarantine_not_blocked :
    blockedQueries keepHole doneHole
        (referenceLive keepHole doneHole PiEx ΓEx registryEx)
        declHole attsHole [] (fun _ => [0]) [pA] = [] := by
  decide

/-- Under the all-declarations carrier the same quarantine would block `pA`:
the hole would be a removed node whose attack reaches `c`. -/
theorem hole_alone_quarantine_blocked_under_all_declared :
    blockedQueriesFor [0]
        (Blocked.blockedSet (declaredAF declHole attsHole [0, 1])
          (blockedSeed declHole attsHole [] [0, 1] [0]))
        (fun _ => [0]) [pA] = [pA] := by
  decide

/-! ### A dropped attack onto a quarantined hole -/

/-- `vWrap` (concluding `pB`) attacks the occurrence `leaf l1` inside the hole
`h`; the complete argument `c = leaf l1` shares that occurrence. -/
def declDrop : List (String × SupportTerm) :=
  [("s", vWrap), ("c", .leaf l1), ("h", tHoleL2)]

def attsDrop : List Attack := [.undermine vWrap tHoleL2 [.prem 0]]

/-- Quarantining `l2` removes only the hole, and with it the attack. -/
def keepDrop : (String × SupportTerm) → Bool := Groups.keepArg [l2]

def doneDrop : SupportTerm → Bool := doneFor [l2] declDrop

/-- The hole is not a reference node, so nothing is removed from `D`; the seed
is the lost closure edges onto `c` (and onto `s`, which also contains the
attacked occurrence). -/
theorem dropped_attack_seed :
    blockedSeed declDrop attsDrop []
        (retainedIndices (referenceLive keepDrop doneDrop PiEx ΓEx registryEx)
          declDrop)
        (retainedIndices (keepComplete keepDrop doneDrop) declDrop) = [0, 1] := by
  decide

/-- **A dropped attack onto a hole blocks the complete support it covers.** -/
theorem dropped_attack_onto_hole_blocks_support :
    blockedQueries keepDrop doneDrop
        (referenceLive keepDrop doneDrop PiEx ΓEx registryEx)
        declDrop attsDrop [] (fun _ => [1]) [pA] = [pA] := by
  decide

/-! ### An unclassified quarantined term -/

/-- An instance of an undeclared rule over the declared leaf `l3`. Quarantine
removes it for `l3`; independently, its inference fails on the missing rule. -/
def tNoRule : SupportTerm := .inst ⟨"rmissing"⟩ [] [.leaf l3] [] [] .none

def declBad : List (String × SupportTerm) :=
  [("c", .leaf l1), ("u", tNoRule)]

def attsBad : List Attack := [.undermine tNoRule (.leaf l1) []]

def keepBad : (String × SupportTerm) → Bool := Groups.keepArg [l3]

def doneBad : SupportTerm → Bool := doneFor [l3] declBad

/-- The quarantined leaf is declared; the term is neither a typed hole nor
complete under the full declared table, and it is a reference node. -/
theorem unclassified_not_hole :
    ΓEx l3 = some pC ∧
      keepBad ("u", tNoRule) = false ∧
      argHole PiEx ΓEx registryEx tNoRule = false ∧
      argComplete PiEx ΓEx registryEx tNoRule = false ∧
      retainedIndices (referenceLive keepBad doneBad PiEx ΓEx registryEx)
        declBad = [0, 1] := by
  decide

/-- **An unclassified quarantined term keeps the conservative block.** -/
theorem unclassified_quarantine_blocks_support :
    blockedQueries keepBad doneBad
        (referenceLive keepBad doneBad PiEx ΓEx registryEx)
        declBad attsBad [] (fun _ => [0]) [pA] = [pA] := by
  decide

/-! ### A clean unit with a hole -/

/-- Nothing quarantined: the retained hole and its raw attack block nothing. -/
theorem clean_unit_with_hole_not_blocked :
    blockedQueries (fun _ => true) doneHole
        (referenceLive (fun _ => true) doneHole PiEx ΓEx registryEx)
        declHole attsHole attsHole (fun _ => [0]) [pA] = [] :=
  blockedQueries_eq_nil_of_keep_all (fun _ _ => rfl)

end Lara.Examples.EvidenceBlocked
