import Lara.Context.Holes.Link
import Lara.Context.Holes.Template

/-! Typed hole instantiation supplies the support premise of the old checked
linking theorem. Attack typing and complete conflict coverage remain explicit:
substitution may identify distinct terms, and no injectivity is assumed. -/
set_option autoImplicit false

namespace Lara.Context.Holes
open Lara.Support Lara.Attack Lara.Compile

/-- A successful fragment instantiation inherits support from independently
checked templates and independently typed fillings. -/
theorem instantiated_support {canon : String → String} {reg : BackendRegistry canon}
    {Γ : LeafId → Option Atom} {Δ : HoleSignature} {ρ : Filling}
    {F : HoleFragment} {G : Fragment}
    (hi : instantiateFragment ρ F = .ok G)
    (ht : ∀ t ∈ F.args, ∃ A, HasTemplate canon F.policy.ruleLookup Γ (certOkOf reg) Δ t A [])
    (hρ : FillingTyped canon F.policy.ruleLookup Γ (certOkOf reg) Δ ρ) :
    ∀ w ∈ G.args, ∃ A, HasSupport canon G.policy.ruleLookup Γ (certOkOf reg) w A [] := by
  obtain ⟨hn, ws, ks, hw, _, rfl⟩ := instantiateFragment_inv hi
  intro w hm
  obtain ⟨t, htm, htw⟩ := mem_instantiateList hw hm
  obtain ⟨A, hA⟩ := ht t htm
  obtain ⟨v, hv, hs⟩ := instantiate_hasSupport hA hρ hn
  rw [instantiate_eq_aux hn, htw] at hv
  cases hv
  exact ⟨A, hs⟩

/-- Support is derived by substitution; the remaining old side conditions
continue to describe the actual post-substitution attack terms. -/
theorem sideOk_of_typed {canon : String → String} {reg : BackendRegistry canon}
    {Γ : LeafId → Option Atom} {Δ : HoleSignature} {ρ : Filling}
    {F : HoleFragment} {G : Fragment}
    (hi : instantiateFragment ρ F = .ok G)
    (ht : ∀ t ∈ F.args, ∃ A, HasTemplate canon F.policy.ruleLookup Γ (certOkOf reg) Δ t A [])
    (hρ : FillingTyped canon F.policy.ruleLookup Γ (certOkOf reg) Δ ρ)
    (ha : ∀ k ∈ G.atts, HasAttack canon G.policy.ruleLookup Γ (certOkOf reg) G.policy.defeat k)
    (hs : ∀ k ∈ G.atts, k.source ∈ G.args)
    (hd : ∀ k ∈ G.atts, k.target ∈ G.args)
    (hc : AttackComplete canon G.policy.ruleLookup Γ (certOkOf reg) G.policy.defeat G.args G.atts) :
    SideOk canon reg Γ G.policy G.args G.atts :=
  ⟨instantiated_support hi ht hρ, ha, hs, hd, hc⟩

/-- Linking supplies cross-boundary attack coverage after typed substitution. -/
theorem link_attackComplete {canon : String → String} {reg : BackendRegistry canon}
    {C : HoleContext} {F : HoleFragment} {G : Fragment} {Δ : HoleSignature}
    (hi : instantiateFragment C.filling F = .ok G)
    (ht : ∀ t ∈ F.args, ∃ A, HasTemplate canon F.policy.ruleLookup
      (linkGamma C.frame G) (certOkOf reg) Δ t A [])
    (hρ : FillingTyped canon F.policy.ruleLookup (linkGamma C.frame G) (certOkOf reg) Δ C.filling)
    (hC : SideOk canon reg (linkGamma C.frame G) G.policy C.frame.frame.args C.frame.frame.atts)
    (ha : ∀ k ∈ G.atts, HasAttack canon G.policy.ruleLookup
      (linkGamma C.frame G) (certOkOf reg) G.policy.defeat k)
    (hs : ∀ k ∈ G.atts, k.source ∈ G.args)
    (hd : ∀ k ∈ G.atts, k.target ∈ G.args)
    (hc : AttackComplete canon G.policy.ruleLookup (linkGamma C.frame G)
      (certOkOf reg) G.policy.defeat G.args G.atts) :
    AttackComplete canon G.policy.ruleLookup (linkGamma C.frame G) (certOkOf reg)
      G.policy.defeat (dedupList (C.frame.frame.args ++ G.args))
      (C.frame.frame.atts ++ G.atts ++ crossAtts reg (linkGamma C.frame G) C.frame G) :=
  Lara.Context.link_attackComplete hC (sideOk_of_typed hi ht hρ ha hs hd hc)

/-- Acceptance follows from typed templates and fillings, not a hypothesis that
the substituted arguments already type-check. The old checker still owns sorting,
policy validity, attack typing, and explicit within-side coverage. -/
theorem link_checked {canon : String → String} {reg : BackendRegistry canon}
    {C : HoleContext} {F : HoleFragment} {G : Fragment} {Δ : HoleSignature}
    (hi : instantiateFragment C.filling F = .ok G)
    (hok : linkOk C.frame G = true)
    (ht : ∀ t ∈ F.args, ∃ A, HasTemplate canon F.policy.ruleLookup
      (linkGamma C.frame G) (certOkOf reg) Δ t A [])
    (hρ : FillingTyped canon F.policy.ruleLookup (linkGamma C.frame G) (certOkOf reg) Δ C.filling)
    (hC : SideOk canon reg (linkGamma C.frame G) G.policy C.frame.frame.args C.frame.frame.atts)
    (ha : ∀ k ∈ G.atts, HasAttack canon G.policy.ruleLookup
      (linkGamma C.frame G) (certOkOf reg) G.policy.defeat k)
    (hs : ∀ k ∈ G.atts, k.source ∈ G.args)
    (hd : ∀ k ∈ G.atts, k.target ∈ G.args)
    (hc : AttackComplete canon G.policy.ruleLookup (linkGamma C.frame G)
      (certOkOf reg) G.policy.defeat G.args G.atts)
    (hstage : Check.Unit.signatureStage (linkGround C.frame G) (linkedUnit reg C.frame G) = none)
    (hscope : Policy.firstOutOfScope? G.policy = none)
    (hids : (G.policy.rules.map (·.id)).Nodup)
    (hpolicy : Policy.WellFormed canon G.policy) :
    ∃ accepted, Check.Unit.checkUnit (linkGamma C.frame G) reg
      (linkGround C.frame G) (linkedUnit reg C.frame G) = .ok accepted :=
  Lara.Context.link_checked (link_eq_some hok) hstage hscope hids hpolicy hC
    (sideOk_of_typed hi ht hρ ha hs hd hc)

/-- A checked instantiated link produces exactly the old carrier observation. -/
theorem obsGen_eq_of_ok {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} {reg : BackendRegistry canon}
    {C : HoleContext} {F : HoleFragment} {G : Fragment}
    {accepted : Unit.CheckedUnit canon (linkGamma C.frame G) (certOkOf reg)}
    (hi : instantiateFragment C.filling F = .ok G)
    (hok : linkOk C.frame G = true)
    (hc : Check.Unit.checkUnit (linkGamma C.frame G) reg
      (linkGround C.frame G) (linkedUnit reg C.frame G) = .ok accepted) :
    obsGen g reg C F = .ok (.observed (G.exports.map (fun p => g (Invariants.compileUnit accepted) p))) := by
  rw [obsGen_of_instantiate g reg hi, Lara.Context.obsGen_eq_of_ok g hok hc]

end Lara.Context.Holes
