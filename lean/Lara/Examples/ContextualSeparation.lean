/-
# Grounded contextual equivalence does not determine arbitrary semantics

The fragments share all linking and checking inputs and export different
unattacked supported conclusions. Their grounded observations agree in every
context, including every detailed failure. A positional singleton semantics
family distinguishes them in an accepted empty context. This resolves only the
arbitrary `ExtensionSemantics` implication, not any standard-five implication
or the restriction to fragments with identical exports.
-/
import Lara.Examples
import Lara.Context.Observation

namespace Lara.Examples.ContextualSeparation

open Lara.Support Lara.Attack Lara.Compile Lara.Semantics
open Lara.Context hiding Context

/-- Fixed policy without rules, contraries, or exceptions. -/
def policy : Policy.Policy :=
  { unitPolicyEx with rules := [], defeat := ⟨[], []⟩ }

/-- Two owned supported atoms; only the observed export varies. -/
def fragment (p : Atom) : Fragment :=
  { sigma := sigmaEx, policy := policy
  , gammaFrag := [(l1, pA), (l2, pB)], ground := [pA, pB]
  , args := [.leaf l1, .leaf l2], atts := []
  , imports := Interface.closed, exports := [p] }

/-- Empty compatible frame for the separating observation. -/
def emptyCtx : Lara.Context.Context :=
  ⟨{ fragment pA with gammaFrag := [], ground := [], args := [], exports := [] }⟩

/-- Adequate singleton selection parameterized by argument position.
This open-interface family is not one of the five standard Dung semantics. -/
def singletonSem (a : Grounded.Arg) : ExtensionSemantics where
  spec := fun _ S => S = [a]
  enumerate := fun F => (candidates F).filter (fun S => decide (S = [a]))
  sound := by intro F _ S; rw [mem_filter_candidates]; simp

private theorem no_attack {Gamma : LeafId → Option Atom} {k : Attack}
    (h : HasAttack id policy.ruleLookup Gamma (certOkOf registryEx) policy.defeat k) :
    False := by
  cases h <;> simp_all [ContraryMatch, policy]

private theorem accepted_status (C : Lara.Context.Context)
    (hok : linkOk C (fragment pA) = true)
    (u : Unit.CheckedUnit id (linkGamma C (fragment pA)) (certOkOf registryEx))
    (hc : Check.Unit.checkUnit (linkGamma C (fragment pA)) registryEx
      (linkGround C (fragment pA)) (linkedUnit registryEx C (fragment pA)) = .ok u)
    (l : LeafId) (p : Atom)
    (hm : SupportTerm.leaf l ∈ (fragment pA).args)
    (hg : Admission.buildGamma (fragment pA).gammaFrag l = some p) :
    Invariants.status id (Invariants.compileUnit u) p = Grounded.Status.justified := by
  have hs := Check.Unit.checkUnit_sound hc
  have hp : u.policy = policy := hs.policy_eq
  have ht : SupportTerm.leaf l ∈ u.program.args := by
    rw [hs.args_eq]
    exact mem_dedupList.mpr (List.mem_append_right _ hm)
  rw [← u.nodes_terms, List.mem_map] at ht
  obtain ⟨n, hn, hnt⟩ := ht
  have hsup : HasSupport id u.policy.ruleLookup (linkGamma C (fragment pA))
      (certOkOf registryEx) (.leaf l) p [] := .leaf (linkGamma_extends_right hok l p hg)
  have heq : n.conclusion = p :=
    (hasSupport_unique (hnt ▸ n.valid) hsup).1
  obtain ⟨i, hi, hni⟩ := List.mem_iff_getElem.mp hn
  have hget : u.nodes[i]? = some n := by simp [hi, hni]
  have hempty : u.program.atts = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro k hk
    have hk' := u.program.typed k hk
    rw [hp] at hk'
    exact no_attack hk'
  rw [Invariants.status_compileUnit]
  apply (Grounded.statusC_justified_iff _ _).mpr
  refine ⟨i, Consistency.mem_claimSupportFor_iff.mpr ⟨n, hget, ?_⟩, ?_⟩
  · rw [heq]
  · apply (Grounded.labelC_inn_iff i).mpr
    apply Grounded.DirectIn.intro
    · change i ∈ List.range u.program.args.length
      rw [List.mem_range, ← u.nodes_terms, List.length_map]
      exact hi
    · intro b _ hb
      change edgeB u.program b i = true at hb
      unfold edgeB at hb
      split at hb <;> simp_all [coveredB]

/-- Agreement includes every context, with identical detailed failures. -/
theorem grounded_ctxEquiv : CtxEquiv registryEx (fragment pA) (fragment pB) := by
  intro C
  unfold obs
  have hfault : linkFault C (fragment pB) = linkFault C (fragment pA) := rfl
  have hunit : linkedUnit registryEx C (fragment pB) =
      linkedUnit registryEx C (fragment pA) := rfl
  have hground : linkGround C (fragment pB) = linkGround C (fragment pA) := rfl
  simp only [hfault, hunit, hground]
  dsimp only [linkGamma, fragment]
  cases hf : linkFault C (fragment pA) with
  | some fault => simp only [fragment] at hf; simp only [hf]
  | none =>
    have hok : linkOk C (fragment pA) = true := by simp [linkOk, hf]
    cases hc : Check.Unit.checkUnit (linkGamma C (fragment pA)) registryEx
        (linkGround C (fragment pA)) (linkedUnit registryEx C (fragment pA)) with
    | error e => simp only [linkGamma, fragment] at hc; simp only [hc]
    | ok u =>
      simp only [linkGamma, fragment] at hc
      simp only [hc, List.map_cons, List.map_nil]
      simp only [fragment] at hf
      simp only [hf]
      change ObservationOf.observed [Invariants.status id (Invariants.compileUnit u) pA] =
        ObservationOf.observed [Invariants.status id (Invariants.compileUnit u) pB]
      rw [accepted_status C hok u hc l1 pA (by simp [fragment]) (by decide),
        accepted_status C hok u hc l2 pB (by simp [fragment]) (by decide)]

/-- Both separating links pass the compatibility guard. -/
theorem separating_link_ok :
    linkOk emptyCtx (fragment pA) = true ∧
    linkOk emptyCtx (fragment pB) = true := by decide

/-- Both distinguishing links reach accepted carriers. -/
theorem separating_accepted :
    (Check.Unit.checkUnit (linkGamma emptyCtx (fragment pA)) registryEx
      (linkGround emptyCtx (fragment pA))
      (linkedUnit registryEx emptyCtx (fragment pA))).isOk = true ∧
    (Check.Unit.checkUnit (linkGamma emptyCtx (fragment pB)) registryEx
      (linkGround emptyCtx (fragment pB))
      (linkedUnit registryEx emptyCtx (fragment pB))).isOk = true := by decide

/-- The selector justifies the first export and leaves the second contested. -/
theorem separating_observations :
    obsSem (singletonSem 0) registryEx emptyCtx (fragment pA) =
      .observed [.observed .justified] ∧
    obsSem (singletonSem 0) registryEx emptyCtx (fragment pB) =
      .observed [.observed .contested] := by decide

/-- One accepted context refutes equivalence under singleton selection. -/
theorem singleton_not_ctxEquivSem :
    ¬ CtxEquivSem (singletonSem 0) registryEx (fragment pA) (fragment pB) := by
  intro h
  have he := h emptyCtx
  rw [separating_observations.1, separating_observations.2] at he
  cases he

/-- Separation of equivalence relations, including universal grounded agreement. -/
theorem counterexample : ∃ (sem : ExtensionSemantics) (F G : Fragment),
    CtxEquiv registryEx F G ∧ ¬ CtxEquivSem sem registryEx F G :=
  ⟨singletonSem 0, fragment pA, fragment pB, grounded_ctxEquiv, singleton_not_ctxEquivSem⟩

/-- The arbitrary-semantics implication is false; no standard-five implication
is refuted by this statement. -/
theorem grounded_does_not_imply_semantic :
    ¬ ∀ (sem : ExtensionSemantics) (F G : Fragment),
      CtxEquiv registryEx F G → CtxEquivSem sem registryEx F G := by
  intro h
  exact singleton_not_ctxEquivSem (h _ _ _ grounded_ctxEquiv)

end Lara.Examples.ContextualSeparation
