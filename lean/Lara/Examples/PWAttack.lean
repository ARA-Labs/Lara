/-
Conformance cells for declared-attack transport.

The S2/R2 renaming pair is re-established as an `AttackBridge` — T8's attack
hypotheses stated on the source language — and its `StatusBridge` is
rederived through `AttackBridge.toStatusBridge`. Two negative cells exercise
the derivation's actual boundaries (eng review, decision 2A): a declared
attack whose vocabulary the symbol map rejects (`atts_eq` is refutable, not
vacuous), and a collapsing leaf map breaking `containsB` commutation (the
reason `toStatusBridge` assumes `Function.Injective lm`, which the frozen
`StatusBridge` contract does not). A focused `ques`-position cell pins
`Attack.subterm` commuting through `trSupport` at a discharge key (eng
review, decision 7A): that step of the ladder holds only because T6's
`trSupportDis` carries question keys verbatim in order, so a weakening of
T6's key preservation fails here, locally.
-/

import Lara.PW.AttackTransport
import Lara.Examples.PWStatus
import Lara.Examples.PWCompose

namespace Lara.Examples.PW.Attack

open Lara.Support Lara.Compile Lara.PW Lara.Examples.PW
  Lara.Examples.PW.Status Lara.Examples.PW.Compose

/-- The renaming leaf map is injective: `⟨n ++ "-tgt"⟩` determines `n`. -/
theorem leafMapR_injective : Function.Injective leafMapR := by
  intro a b h
  cases a; cases b
  simp only [leafMapR, LeafId.mk.injEq] at h ⊢
  exact String.ext (List.append_cancel_right
    (by rw [← String.toList_append, ← String.toList_append, h]))

/-- The R2 declared attacks are exactly the transports of S2's.
**`decide`, not `rfl`** — `Lara.Attack.Attack` derives `DecidableEq`
(`Lara/Attack.lean:519`), so `Decidable (trAttackList … = some …)` is
synthesized. -/
theorem s2_r2_atts_transported :
    trAttackList symR leafMapR wS2.unit.program.atts =
      some wR2.unit.program.atts := by decide

/-- The S2/R2 pair as an `AttackBridge` (source-language clauses only). The
`admits`/`matched` fields reuse the frozen T8 witness's components
verbatim. -/
theorem s2_r2_attackBridge :
    Lara.PW.AttackBridge (κ := ctxS) (lam := ctxR) symR leafMapR wS2 wR2 :=
  ⟨s2_r2_statusBridge.admits, s2_r2_statusBridge.matched,
    s2_r2_atts_transported⟩

/-- T8's `StatusBridge`, rederived from the source-language contract. -/
theorem s2_r2_statusBridge_via_attacks :
    Lara.PW.StatusBridge (κ := ctxS) (lam := ctxR) symR leafMapR wS2 wR2 :=
  s2_r2_attackBridge.toStatusBridge symR_injective leafMapR_injective

/-! ### Negative: an attack-vocabulary gap makes `atts_eq` refutable -/

/-- A declared attack whose stored target carries a substitution binding
`gapSym` rejects (`conMap "payload_r" = none`, `Lara/Examples/PWCompose.lean`). -/
def gapAttack : Lara.Attack.Attack :=
  .undermine (.leaf ⟨"a-src"⟩)
    (.inst ⟨"r"⟩ [(⟨"X"⟩, .con "payload_r" .nil)] [] [] [] .none) []

/-- The gap kills the attack's translation, hence the attack list's — so no
`AttackBridge` can relate a program declaring `gapAttack` to one declaring
its "translation": `atts_eq` is refutable rather than vacuously satisfiable. -/
theorem gap_attack_undefined :
    trAttack gapSym (fun l => l) gapAttack = none ∧
      trAttackList gapSym (fun l => l) [gapAttack] = none :=
  ⟨rfl, rfl⟩

/-! ### Negative: a collapsing leaf map breaks `containsB` commutation -/

/-- Every leaf collapses to one target — not injective. -/
def collapsedMap : LeafId → LeafId := fun _ => ⟨"collapsed"⟩

/-- Two distinct source leaves translate to the same target under
`collapsedMap`, and `containsB`'s `decide (v = t)` component
(`Lara/Compile.lean:120-123`) sees them as equal after translation but not
before — exactly why `containsB_trSupport`, and hence
`AttackBridge.toStatusBridge`, assumes `Function.Injective lm`. -/
theorem collapsed_containsB_breaks :
    trSupport SymMap.id collapsedMap (.leaf ⟨"l1-src"⟩) =
      some (.leaf ⟨"collapsed"⟩) ∧
      trSupport SymMap.id collapsedMap (.leaf ⟨"l2-src"⟩) =
        some (.leaf ⟨"collapsed"⟩) ∧
      containsB (.leaf ⟨"collapsed"⟩) (.leaf ⟨"collapsed"⟩) = true ∧
      containsB (.leaf ⟨"l1-src"⟩) (.leaf ⟨"l2-src"⟩) = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### The `ques`-position commutation, pinned -/

/-- A small `.inst` fixture with a nonempty discharge map, on the first
rename's vocabulary (the `supportDisRenSrc` shape). -/
def quesInstSrc : SupportTerm :=
  .inst ⟨"r-ren"⟩ [] [] supportDisRenSrc [] .none

/-- Its translation under the first rename. -/
def quesInstTgt : SupportTerm :=
  .inst ⟨"r-ren"⟩ [] [] supportDisRenTgt [] .none

/-- Navigating to the `q-ren` discharge before and after translation reaches
the two corresponding leaves — by computation. -/
theorem ques_position_computes :
    trSupport renSym leafMapRen quesInstSrc = some quesInstTgt ∧
      Lara.Attack.subterm quesInstSrc [.ques ⟨"q-ren"⟩] =
        some (.leaf lRen) ∧
      Lara.Attack.subterm quesInstTgt [.ques ⟨"q-ren"⟩] =
        some (.leaf (leafMapRen lRen)) :=
  ⟨rfl, rfl, rfl⟩

/-- The same commutation *derived* by `trSupport_subterm`, pinning the law
itself at a `ques` position. -/
theorem ques_position_law :
    Lara.Attack.subterm quesInstTgt [.ques ⟨"q-ren"⟩] =
      (Lara.Attack.subterm quesInstSrc [.ques ⟨"q-ren"⟩]).bind
        (trSupport renSym leafMapRen) :=
  trSupport_subterm ques_position_computes.1 _

end Lara.Examples.PW.Attack
