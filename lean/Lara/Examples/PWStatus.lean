/-
# PW-T8 examples (issue #193)

Two halves.

**Negative — a forward attack homomorphism is insufficient.** The T7 identity
edge (`wT7src → wT7tgt`, `StructuralBridge.refl`) satisfies the *forward*
half of `StatusBridge`: `admits` (T6's `admitsIdT7`) and `forth` (vacuous: the
source program has no attacks). It fails `matched`: the target's attacker
`leaf l2` is the transport of no source argument. And the status flips. So
`StatusBridge` does not hold, and `status_transport`'s contrapositive says the
same thing from the flip alone.

**Positive — off the identity.** Two contexts sharing the T7 shape but
disjoint vocabularies: `ctxS` (predicates `p q s`, leaves `l1 l2 l3`) and
`ctxR` (`p_r q_r s_r`, leaves `l1-tgt l2-tgt l3-tgt`), both with the empty
registry so `cert_ok` is vacuous *and honest* (`certOkOf regEmpty` is `False`
everywhere; the units carry no strict rules, so `checkUnit` accepts them
unchanged). The renaming bridge `bridgeR` discharges all three contract
clauses under a translation that actually renames, and `StatusBridge` holds
between the one-argument worlds (`justified` transports) and between the
two-argument attacked worlds (`defeated` transports, through a real forth/back
pair on the compiled edge). `gap` transports on the unsupported claim, and
`contested` transports between a third pair of worlds whose policies declare
`p`/`q` as mutual contraries (two matched attacks each way). One modal cell
instantiates `sat_status_iff_box` at a two-context `BridgeData`.

Everything decidable is closed by `decide`; `native_decide` is banned.
`sigma_eq`/`policy_eq` close by `rfl`.
-/

import Lara.Examples.PW
import Lara.Examples.PWStructural
import Lara.PW.Status

-- The namespace's last segment coincides with the `Status` type opened below.
-- Do not name any declaration here after a `Status` constructor
-- (`justified`/`contested`/`defeated`/`gap`): `Status.gap` would then resolve
-- to it, from this namespace and from the parent `Lara.Examples.PW`.
namespace Lara.Examples.PW.Status

open Lara.Support Lara.Compile Lara.Check Lara.Check.Unit
open Lara.PW Lara.PW.Instance Lara.Examples.PW
open Lara.Grounded (Status)

/-! ### Negative: T7 is a forward homomorphism and nothing more -/

/-- The source program has no attacks, so `forth` holds vacuously. -/
theorem t7_forth : ∀ i j k, Corr SymMap.id (fun l => l) wT7src wT7tgt i j →
    edgeB wT7src.unit.program k i = true →
    ∃ k', Corr SymMap.id (fun l => l) wT7src wT7tgt k k' ∧
      edgeB wT7tgt.unit.program k' j = true := by
  intro i j k _ hE
  obtain ⟨hk, hi⟩ := (edgeB_faithful wT7src.unit.program).ranged k i hE
  have hlen : wT7src.unit.program.args.length = 1 := by decide
  rw [hlen] at hk hi
  have hk0 : k = 0 := by omega
  have hi0 : i = 0 := by omega
  subst hk0; subst hi0
  exact absurd hE (by decide)

/-- The target's attacker is in the target program … -/
theorem t7_l2_mem : SupportTerm.leaf l2 ∈ wT7tgt.unit.program.args := by decide

/-- … and is the transport of no source argument: `matched` fails. -/
theorem t7_unmatched :
    ¬ ∃ t, t ∈ wT7src.unit.program.args ∧
      trSupport SymMap.id (fun l => l) t = some (.leaf l2) := by decide

/-- The T7 identity edge is not a status bridge — directly, at `matched`. -/
theorem t7_not_statusBridge :
    ¬ StatusBridge SymMap.id (fun l => l) wT7src wT7tgt :=
  fun h => t7_unmatched (h.matched (.leaf l2) t7_l2_mem)

/-- … and via T8's contrapositive, from the status flip alone. -/
theorem t7_not_statusBridge_of_flip :
    ¬ StatusBridge SymMap.id (fun l => l) wT7src wT7tgt := by
  intro h
  have := status_transport (κ := ctxT7) (lam := ctxT7) rfl
    (.refl ctxT7.canon ctxT7.policy.ruleLookup ctxT7.Gamma ctxT7.CertOk)
    h SymMap.id_injective (trAtom_id pA)
  rw [t7_src_justified, t7_tgt_defeated] at this
  exact absurd this (by decide)

/-- **A forward attack homomorphism is insufficient**: left-totality and
forth hold, and the status still flips. -/
theorem t7_forward_hom_insufficient :
    Admits SymMap.id (fun l => l) wT7src wT7tgt ∧
      (∀ i j k, Corr SymMap.id (fun l => l) wT7src wT7tgt i j →
        edgeB wT7src.unit.program k i = true →
        ∃ k', Corr SymMap.id (fun l => l) wT7src wT7tgt k k' ∧
          edgeB wT7tgt.unit.program k' j = true) ∧
      cmpStatus wT7src pA = Status.justified ∧
      cmpStatus wT7tgt pA = Status.defeated :=
  ⟨admitsIdT7, t7_forth, t7_src_justified, t7_tgt_defeated⟩

/-! ### Positive: a renaming pair off the identity -/

/-- The empty registry: `certOkOf regEmpty` is `False` at every step, so a
bridge into or out of it discharges `cert_ok` from a false hypothesis — and
`checkUnit` still accepts units with no strict rules. -/
def regEmpty : BackendRegistry id := fun _ => none

/-- Source context: the T7 environment over the empty registry. -/
def ctxS : Context :=
  { canon := id, Gamma := ΓEx, CertOk := certOkOf regEmpty
  , sigma := sigmaEx, policy := polT7 }

def unitS1Check := checkUnit ΓEx regEmpty groundEx unitT7src
theorem unitS1_accepted : unitS1Check.isOk = true := by decide
def acceptedS1 : Lara.Unit.CheckedUnit id ΓEx (certOkOf regEmpty) :=
  unitS1Check.toOption.get (by decide)
def wS1 : World ctxS := { unit := acceptedS1, sigma_eq := rfl, policy_eq := rfl }

def unitS2Check := checkUnit ΓEx regEmpty groundEx unitT7tgt
theorem unitS2_accepted : unitS2Check.isOk = true := by decide
def acceptedS2 : Lara.Unit.CheckedUnit id ΓEx (certOkOf regEmpty) :=
  unitS2Check.toOption.get (by decide)
def wS2 : World ctxS := { unit := acceptedS2, sigma_eq := rfl, policy_eq := rfl }

/-- Renamed vocabulary. -/
def pR : Atom := .atom "p_r" .nil
def qR : Atom := .atom "q_r" .nil
def sR : Atom := .atom "s_r" .nil
def apAr : APat := ⟨⟨"p_r"⟩, .nil⟩
def apBr : APat := ⟨⟨"q_r"⟩, .nil⟩
def l1r : LeafId := ⟨"l1-tgt"⟩
def l2r : LeafId := ⟨"l2-tgt"⟩
def l3r : LeafId := ⟨"l3-tgt"⟩

def ΓR : LeafId → Option Atom := fun l =>
  if l = l1r then some pR
  else if l = l2r then some qR
  else if l = l3r then some sR
  else none

def sigmaR : Lara.Sigma.Sigma :=
  { sorts := ["Item"]
  , cons := [⟨⟨"z"⟩, [], .decl "Item"⟩]
  , preds := [⟨⟨"p_r"⟩, []⟩, ⟨⟨"q_r"⟩, []⟩, ⟨⟨"s_r"⟩, []⟩] }

def groundR : List Atom := [pR, qR, sR]

/-- `q_r` defeats `p_r`, directionally — the T7 policy, renamed. -/
def polR : Lara.Policy.Policy := { rules := [], defeat := ⟨[(apBr, apAr)], []⟩ }

def ctxR : Context :=
  { canon := id, Gamma := ΓR, CertOk := certOkOf regEmpty
  , sigma := sigmaR, policy := polR }

def unitR1 : Lara.Unit :=
  { sigma := sigmaR, policy := polR, args := [.leaf l1r], atts := [] }
def unitR1Check := checkUnit ΓR regEmpty groundR unitR1
theorem unitR1_accepted : unitR1Check.isOk = true := by decide
def acceptedR1 : Lara.Unit.CheckedUnit id ΓR (certOkOf regEmpty) :=
  unitR1Check.toOption.get (by decide)
def wR1 : World ctxR := { unit := acceptedR1, sigma_eq := rfl, policy_eq := rfl }

def unitR2 : Lara.Unit :=
  { sigma := sigmaR, policy := polR
  , args := [.leaf l1r, .leaf l2r]
  , atts := [.undermine (.leaf l2r) (.leaf l1r) []] }
def unitR2Check := checkUnit ΓR regEmpty groundR unitR2
theorem unitR2_accepted : unitR2Check.isOk = true := by decide
def acceptedR2 : Lara.Unit.CheckedUnit id ΓR (certOkOf regEmpty) :=
  unitR2Check.toOption.get (by decide)
def wR2 : World ctxR := { unit := acceptedR2, sigma_eq := rfl, policy_eq := rfl }

/-- The renaming: predicates `p q s ↦ p_r q_r s_r`, constructors fixed. -/
def symR : SymMap :=
  { predMap := fun p =>
      if p = "p" then some "p_r"
      else if p = "q" then some "q_r"
      else if p = "s" then some "s_r"
      else none
  , conMap := some }

def leafMapR : LeafId → LeafId := fun l => ⟨l.name ++ "-tgt"⟩

/-- `symR` is injective where defined. `split` opens only the outermost `if`,
so each hypothesis is split to its leaves; the contradictory branches reduce to
a disequality between two string literals, which `decide` settles. -/
theorem symR_injective : symR.Injective := by
  constructor
  · intro x y z hx hy
    simp only [symR] at hx hy
    repeat' split at hx
    repeat' split at hy
    all_goals (try simp_all)
    all_goals exact absurd (hy.trans hx.symm) (by decide)
  · intro x y z hx hy
    exact Option.some.inj (hx.trans hy.symm)

/-- The structural bridge `ctxS → ctxR`. `leaf_ok` is checked at the three
leaves of `ΓEx`; `rule_ok` is vacuous (no rules); `cert_ok` is discharged
from the false `certOkOf regEmpty` hypothesis. -/
def bridgeR : StructuralBridge ctxS.canon ctxS.policy.ruleLookup
    ctxR.policy.ruleLookup ctxS.Gamma ctxR.Gamma ctxS.CertOk ctxR.CertOk where
  sym := symR
  leafMap := leafMapR
  leaf_ok := by
    intro l p h
    simp only [ctxS, ΓEx] at h
    split at h
    · next hl => cases h; subst hl; exact ⟨pR, rfl, by decide⟩
    · split at h
      · next hl => cases h; subst hl; exact ⟨qR, rfl, by decide⟩
      · split at h
        · next hl => cases h; subst hl; exact ⟨sR, rfl, by decide⟩
        · cases h
  rule_ok := by
    intro rn r h
    exact absurd h (by simp [ctxS, polT7, Lara.Policy.Policy.ruleLookup, Lara.Policy.lookupRuleDecl])
  cert_ok := by
    intro β hd κ' As C As' C' _ _ h
    exact absurd h (by simp [ctxS, certOkOf, regEmpty])

/-! ### Status bridges between the renamed worlds -/

/-- One argument each, no attacks: `forth`/`back` are vacuous, and the two
totality clauses are `decide`-able memberships. -/
theorem s1_r1_statusBridge : StatusBridge symR leafMapR wS1 wR1 where
  admits := by
    intro t ht
    have : t = .leaf l1 := by
      have hargs : wS1.unit.program.args = [.leaf l1] := by decide
      rw [hargs] at ht
      simpa using ht
    subst this
    exact ⟨.leaf l1r, rfl, by decide⟩
  matched := by
    intro t' ht'
    have : t' = .leaf l1r := by
      have hargs : wR1.unit.program.args = [.leaf l1r] := by decide
      rw [hargs] at ht'
      simpa using ht'
    subst this
    exact ⟨.leaf l1, by decide, rfl⟩
  forth := by
    intro i j k _ hE
    obtain ⟨hk, hi⟩ := (edgeB_faithful wS1.unit.program).ranged k i hE
    have hlen : wS1.unit.program.args.length = 1 := by decide
    rw [hlen] at hk hi
    have hk0 : k = 0 := by omega
    have hi0 : i = 0 := by omega
    subst hk0; subst hi0
    exact absurd hE (by decide)
  back := by
    intro i j k' _ hE
    obtain ⟨hk, hj⟩ := (edgeB_faithful wR1.unit.program).ranged k' j hE
    have hlen : wR1.unit.program.args.length = 1 := by decide
    rw [hlen] at hk hj
    have hk0 : k' = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hk0; subst hj0
    exact absurd hE (by decide)

/-- Two arguments each, one attack `1 → 0` on each side: `forth` and `back`
are exercised on a real edge, index by index. The bounded quantifiers are
stated `∀ k, k < 2 → ∀ i, i < 2 → …` so `Nat.decidableBallLT` applies; the
inverse of `Corr` on the source side is a case split on the index rather than
a `decide`, since it would otherwise quantify over all of `SupportTerm`. -/
theorem s2_r2_statusBridge : StatusBridge symR leafMapR wS2 wR2 where
  admits := by
    intro t ht
    have hargs : wS2.unit.program.args = [.leaf l1, .leaf l2] := by decide
    rw [hargs] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨.leaf l1r, rfl, by decide⟩
    · exact ⟨.leaf l2r, rfl, by decide⟩
  matched := by
    intro t' ht'
    have hargs : wR2.unit.program.args = [.leaf l1r, .leaf l2r] := by decide
    rw [hargs] at ht'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl
    · exact ⟨.leaf l1, by decide, rfl⟩
    · exact ⟨.leaf l2, by decide, rfl⟩
  forth := by
    intro i j k hC hE
    obtain ⟨hk, hi⟩ := (edgeB_faithful wS2.unit.program).ranged k i hE
    have hlen : wS2.unit.program.args.length = 2 := by decide
    rw [hlen] at hk hi
    -- the only source edge is 1 → 0
    have hki : k = 1 ∧ i = 0 := by
      have hall : ∀ k, k < 2 → ∀ i, i < 2 → edgeB wS2.unit.program k i = true →
          k = 1 ∧ i = 0 := by decide
      exact hall k hk i hi hE
    obtain ⟨rfl, rfl⟩ := hki
    -- Corr 0 j pins j = 0
    have hj : j = 0 := by
      obtain ⟨t, t', ht, ht', htr⟩ := hC
      have ht0 : t = .leaf l1 := by
        have hargs : wS2.unit.program.args = [.leaf l1, .leaf l2] := by decide
        rw [hargs] at ht; exact Option.some.inj ht.symm
      subst ht0
      have : t' = .leaf l1r := Option.some.inj htr.symm
      subst this
      have hargs' : wR2.unit.program.args = [.leaf l1r, .leaf l2r] := by decide
      rw [hargs'] at ht'
      have hjlt := (List.getElem?_eq_some_iff.mp ht').1
      simp only [List.length_cons, List.length_nil] at hjlt
      have : ∀ j, j < 2 → ([SupportTerm.leaf l1r, .leaf l2r])[j]? = some (.leaf l1r) →
          j = 0 := by decide
      exact this j hjlt ht'
    subst hj
    refine ⟨1, ⟨.leaf l2, .leaf l2r, by decide, by decide, rfl⟩, by decide⟩
  back := by
    intro i j k' hC hE
    obtain ⟨hk, hj⟩ := (edgeB_faithful wR2.unit.program).ranged k' j hE
    have hlen : wR2.unit.program.args.length = 2 := by decide
    rw [hlen] at hk hj
    have hkj : k' = 1 ∧ j = 0 := by
      have hall : ∀ k, k < 2 → ∀ j, j < 2 → edgeB wR2.unit.program k j = true →
          k = 1 ∧ j = 0 := by decide
      exact hall k' hk j hj hE
    obtain ⟨rfl, rfl⟩ := hkj
    have hi : i = 0 := by
      obtain ⟨t, t', ht, ht', htr⟩ := hC
      have ht0' : t' = .leaf l1r := by
        have hargs' : wR2.unit.program.args = [.leaf l1r, .leaf l2r] := by decide
        rw [hargs'] at ht'; exact Option.some.inj ht'.symm
      subst ht0'
      have hargs : wS2.unit.program.args = [.leaf l1, .leaf l2] := by decide
      rw [hargs] at ht
      have hilt := (List.getElem?_eq_some_iff.mp ht).1
      simp only [List.length_cons, List.length_nil] at hilt
      have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with rfl | rfl
      · rfl
      · have ht1 : t = .leaf l2 := Option.some.inj ht.symm
        subst ht1
        exact absurd htr (by decide)
    subst hi
    refine ⟨1, ⟨.leaf l2, .leaf l2r, by decide, by decide, rfl⟩, by decide⟩

/-- **`justified` transports** through the renaming bridge. -/
theorem t8_justified_preserved : cmpStatus wR1 pR = cmpStatus wS1 pA :=
  status_transport (κ := ctxS) (lam := ctxR) rfl bridgeR s1_r1_statusBridge
    symR_injective rfl

theorem t8_justified_cells :
    cmpStatus wS1 pA = Status.justified ∧ cmpStatus wR1 pR = Status.justified :=
  ⟨by decide, by decide⟩

/-- **`defeated` transports**, through a real matched attacker. -/
theorem t8_defeated_preserved : cmpStatus wR2 pR = cmpStatus wS2 pA :=
  status_transport (κ := ctxS) (lam := ctxR) rfl bridgeR s2_r2_statusBridge
    symR_injective rfl

theorem t8_defeated_cells :
    cmpStatus wS2 pA = Status.defeated ∧ cmpStatus wR2 pR = Status.defeated :=
  ⟨by decide, by decide⟩

/-- **`gap` transports**: `q` has no support in `wS1`, and neither does
`q_r` in `wR1`. -/
theorem t8_gap_preserved : cmpStatus wR1 qR = cmpStatus wS1 pB :=
  status_transport (κ := ctxS) (lam := ctxR) rfl bridgeR s1_r1_statusBridge
    symR_injective rfl

theorem t8_gap_cells :
    cmpStatus wS1 pB = Status.gap ∧ cmpStatus wR1 qR = Status.gap :=
  ⟨by decide, by decide⟩

/-- The translation is not the identity on the transported claim. -/
theorem t8_renamed : trAtom symR pA = some pR ∧ pR ≠ pA := ⟨rfl, by decide⟩

/-! ### Optional: the `contested` cell, on symmetric contraries -/

/-- `p` and `q` are mutual contraries; each argument undermines the other. -/
def polS3 : Lara.Policy.Policy :=
  { rules := [], defeat := ⟨[(apB, apA), (apA, apB)], []⟩ }

/-- `ctxS` with the symmetric policy — nothing else changes. -/
def ctxS3 : Context := { ctxS with policy := polS3 }

def unitS3 : Lara.Unit :=
  { sigma := sigmaEx, policy := polS3
  , args := [.leaf l1, .leaf l2]
  , atts := [.undermine (.leaf l2) (.leaf l1) [], .undermine (.leaf l1) (.leaf l2) []] }
def unitS3Check := checkUnit ΓEx regEmpty groundEx unitS3
theorem unitS3_accepted : unitS3Check.isOk = true := by decide
def acceptedS3 : Lara.Unit.CheckedUnit id ΓEx (certOkOf regEmpty) :=
  unitS3Check.toOption.get (by decide)
def wS3 : World ctxS3 := { unit := acceptedS3, sigma_eq := rfl, policy_eq := rfl }

/-- The renamed twin. -/
def polR3 : Lara.Policy.Policy :=
  { rules := [], defeat := ⟨[(apBr, apAr), (apAr, apBr)], []⟩ }

/-- `ctxR` with the symmetric policy. -/
def ctxR3 : Context := { ctxR with policy := polR3 }

def unitR3 : Lara.Unit :=
  { sigma := sigmaR, policy := polR3
  , args := [.leaf l1r, .leaf l2r]
  , atts := [.undermine (.leaf l2r) (.leaf l1r) [], .undermine (.leaf l1r) (.leaf l2r) []] }
def unitR3Check := checkUnit ΓR regEmpty groundR unitR3
theorem unitR3_accepted : unitR3Check.isOk = true := by decide
def acceptedR3 : Lara.Unit.CheckedUnit id ΓR (certOkOf regEmpty) :=
  unitR3Check.toOption.get (by decide)
def wR3 : World ctxR3 := { unit := acceptedR3, sigma_eq := rfl, policy_eq := rfl }

/-- The structural bridge `ctxS3 → ctxR3`. `ctxS3`/`ctxR3` share `ctxS`/`ctxR`'s
`Gamma` and `CertOk` definitionally, so `leaf_ok` and `cert_ok` are
`bridgeR`'s own; only `rule_ok` is re-discharged, against the symmetric
policy (which still has no rules). -/
def bridgeR3 : StructuralBridge ctxS3.canon ctxS3.policy.ruleLookup
    ctxR3.policy.ruleLookup ctxS3.Gamma ctxR3.Gamma ctxS3.CertOk ctxR3.CertOk where
  sym := symR
  leafMap := leafMapR
  leaf_ok := bridgeR.leaf_ok
  rule_ok := by
    intro rn r h
    exact absurd h (by simp [ctxS3, polS3, Lara.Policy.Policy.ruleLookup, Lara.Policy.lookupRuleDecl])
  cert_ok := bridgeR.cert_ok

/-- `Corr` between the two-argument worlds is the diagonal: the `i`-th source
leaf translates to the `i`-th target leaf and to nothing else. -/
theorem s3_corr_diag : ∀ i j, Corr symR leafMapR wS3 wR3 i j → i = j := by
  intro i j ⟨t, t', ht, ht', htr⟩
  have hargs : wS3.unit.program.args = [.leaf l1, .leaf l2] := by decide
  have hargs' : wR3.unit.program.args = [.leaf l1r, .leaf l2r] := by decide
  rw [hargs] at ht
  rw [hargs'] at ht'
  have hilt := (List.getElem?_eq_some_iff.mp ht).1
  have hjlt := (List.getElem?_eq_some_iff.mp ht').1
  simp only [List.length_cons, List.length_nil] at hilt hjlt
  have hi2 : i = 0 ∨ i = 1 := by omega
  have hj2 : j = 0 ∨ j = 1 := by omega
  rcases hi2 with rfl | rfl <;> rcases hj2 with rfl | rfl
  · rfl
  · have ht0 : t = .leaf l1 := Option.some.inj ht.symm
    have ht1 : t' = .leaf l2r := Option.some.inj ht'.symm
    subst ht0; subst ht1
    exact absurd htr (by decide)
  · have ht0 : t = .leaf l2 := Option.some.inj ht.symm
    have ht1 : t' = .leaf l1r := Option.some.inj ht'.symm
    subst ht0; subst ht1
    exact absurd htr (by decide)
  · rfl

/-- Two arguments, two attacks each way: the edge relation is `{1→0, 0→1}`
on both sides, and `Corr` is the diagonal, so `forth`/`back` each split into
the two edges. -/
theorem s3_r3_statusBridge : StatusBridge symR leafMapR wS3 wR3 where
  admits := by
    intro t ht
    have hargs : wS3.unit.program.args = [.leaf l1, .leaf l2] := by decide
    rw [hargs] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨.leaf l1r, rfl, by decide⟩
    · exact ⟨.leaf l2r, rfl, by decide⟩
  matched := by
    intro t' ht'
    have hargs : wR3.unit.program.args = [.leaf l1r, .leaf l2r] := by decide
    rw [hargs] at ht'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl
    · exact ⟨.leaf l1, by decide, rfl⟩
    · exact ⟨.leaf l2, by decide, rfl⟩
  forth := by
    intro i j k hC hE
    obtain ⟨hk, hi⟩ := (edgeB_faithful wS3.unit.program).ranged k i hE
    have hlen : wS3.unit.program.args.length = 2 := by decide
    rw [hlen] at hk hi
    have hall : ∀ k, k < 2 → ∀ i, i < 2 → edgeB wS3.unit.program k i = true →
        (k = 1 ∧ i = 0) ∨ (k = 0 ∧ i = 1) := by decide
    have hji := s3_corr_diag i j hC
    subst hji
    rcases hall k hk i hi hE with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨1, ⟨.leaf l2, .leaf l2r, by decide, by decide, rfl⟩, by decide⟩
    · exact ⟨0, ⟨.leaf l1, .leaf l1r, by decide, by decide, rfl⟩, by decide⟩
  back := by
    intro i j k' hC hE
    obtain ⟨hk, hj⟩ := (edgeB_faithful wR3.unit.program).ranged k' j hE
    have hlen : wR3.unit.program.args.length = 2 := by decide
    rw [hlen] at hk hj
    have hall : ∀ k, k < 2 → ∀ j, j < 2 → edgeB wR3.unit.program k j = true →
        (k = 1 ∧ j = 0) ∨ (k = 0 ∧ j = 1) := by decide
    have hji := s3_corr_diag i j hC
    subst hji
    rcases hall k' hk i hj hE with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨1, ⟨.leaf l2, .leaf l2r, by decide, by decide, rfl⟩, by decide⟩
    · exact ⟨0, ⟨.leaf l1, .leaf l1r, by decide, by decide, rfl⟩, by decide⟩

/-- **`contested` transports**, through a symmetric pair of matched attacks. -/
theorem t8_contested_preserved : cmpStatus wR3 pR = cmpStatus wS3 pA :=
  status_transport (κ := ctxS3) (lam := ctxR3) rfl bridgeR3 s3_r3_statusBridge
    symR_injective rfl

theorem t8_contested_cells :
    cmpStatus wS3 pA = Status.contested ∧ cmpStatus wR3 pR = Status.contested :=
  ⟨by decide, by decide⟩

/-! ### One modal cell: the `[b]` reading under the T8 hypotheses -/

/-- Two contexts, one bridge `ctxS → ctxR`; the single candidate edge is
`wS2 → wR2`, accepted by T6's `Admits`. -/
def bridgeDataR : BridgeData :=
  { K := Bool
  , ctx := fun k => match k with | false => ctxS | true => ctxR
  , B := OneBridge
  , bsrc := fun _ => false
  , btgt := fun _ => true
  , R := fun _ w v => w = wS2 ∧ v = wR2
  , accept := fun _ w v => Admits symR leafMapR w v
  , translate := fun _ a => trAtom symR a }

theorem r_edge_accepted : bridgeDataR.frame.A OneBridge.it wS2 wR2 :=
  ⟨⟨rfl, rfl⟩, s2_r2_statusBridge.admits⟩

/-- Every accepted successor of `wS2` is `wR2`, which is T8-related. -/
theorem r_all_bridged : ∀ v, bridgeDataR.frame.A OneBridge.it wS2 v →
    StatusBridge symR leafMapR wS2 v := by
  rintro v ⟨⟨_, rfl⟩, _⟩
  exact s2_r2_statusBridge

/-- `wS2 ⊨ Defeated(p) ↔ wS2 ⊨ [b] Defeated(p_r)` — the design's
`RobustlyJustified` shape, at `defeated`, with the guard discharged. The
context index is spelled explicitly (`@Sat … false`) — the usual annotation,
as at `Examples.PW.t7_no_two_status`: a bare `.status` atom carries no
modality to fix `κ`, and a world does not determine its context. -/
theorem t8_box_defeated_r :
    @Sat bridgeDataR.frame (cmpVal bridgeDataR) false
        (.status Status.defeated pA) wS2 ↔
      @Sat bridgeDataR.frame (cmpVal bridgeDataR) false
        (.box OneBridge.it (.status Status.defeated pR)) wS2 :=
  sat_status_iff_box bridgeDataR OneBridge.it rfl bridgeR symR_injective rfl
    r_all_bridged ⟨wR2, r_edge_accepted⟩

/-- … and the left side is true, so the box is inhabited, not vacuous. -/
theorem t8_box_defeated_r_holds :
    @Sat bridgeDataR.frame (cmpVal bridgeDataR) false
      (.box OneBridge.it (.status Status.defeated pR)) wS2 :=
  t8_box_defeated_r.mp t8_defeated_cells.1

end Lara.Examples.PW.Status
