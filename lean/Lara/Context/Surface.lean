/-
# Theory M4, phase F3 — the surface corollary (D1)

Contexts live at the **core** `Lara.Unit` level (D1): quantifying over surface
contexts would entangle the congruence with M5's elaboration guards for no gain
in strength, since the surface layer's own framework is *equal* to the compiled
core one. This module states the corollary that makes the choice honest — what
the core result says about a link, the surface layer sees.

The bridge is M5's `Lara.Surface.direct_compiled_agree`: the framework a
surface derivation exposes before compilation is exactly
`Compile.checkedAF` of the accepted unit. So two surface programs whose
elaborated units are the two sides of the congruence present the *same*
framework, and every semantics coherent with that framework
(`Lara.Surface.observe_coherent`) therefore agrees about them.
-/

import Lara.Context.Equivalence
import Lara.Surface.Observation

namespace Lara.Context

open Lara.Support Lara.Attack Lara.Compile Lara.Erase

variable {canon : String → String}

/-- **The compiled framework is relabel-invariant.** `Compile.checkedAF` reads
only the declared arguments and attacks, so — unlike the carrier equality of
`compileUnit_map` — this needs neither a shared Γ nor a shared policy, only the
two lists being related by an injective relabel. That is what lets it be
applied across two independently elaborated surface programs. -/
theorem checkedAF_map {f : Assurance → Assurance}
    {Pi₁ Pi₂ : RuleId → Option Rule} {Gamma₁ Gamma₂ : LeafId → Option Atom}
    {CertOk₁ CertOk₂ : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {dp₁ dp₂ : DefeatPolicy}
    {P₁ : CheckedProgram canon Pi₁ Gamma₁ CertOk₁ dp₁}
    {P₂ : CheckedProgram canon Pi₂ Gamma₂ CertOk₂ dp₂}
    (hf : Function.Injective f)
    (hargs : P₂.args = P₁.args.map (mapAssur f))
    (hatts : P₂.atts = P₁.atts.map (mapAssurAtt f)) :
    Compile.checkedAF P₂ = Compile.checkedAF P₁ := by
  have hlen : P₂.args.length = P₁.args.length := by rw [hargs, List.length_map]
  simp only [Compile.checkedAF, Compile.toAF]
  congr 1
  · rw [hlen]
  · funext i j
    simp only [Compile.edgeB, hargs, hatts, List.getElem?_map]
    cases P₁.args[i]? with
    | none => rfl
    | some source =>
        cases P₁.args[j]? with
        | none => rfl
        | some target => exact coveredB_relabel hf P₁.atts source target

/-- **Surface transport (D1).** Two accepted surface programs whose elaborated
units are related by an injective certificate relabel present the *same*
framework. Everything the surface layer reports off that framework —
`Lara.Surface.observe` for any carrier-local extension semantics, by
`Lara.Surface.observe_coherent` — therefore agrees about them. -/
theorem surface_directAF_relabel
    {env₁ env₂ : Surface.Env canon} {input₁ input₂ : Surface.Input}
    {output₁ output₂ : Surface.Elaborated canon}
    {f : Assurance → Assurance}
    {acc₁ : Lara.Unit.CheckedUnit canon output₁.gamma (certOkOf env₁.registry)}
    {acc₂ : Lara.Unit.CheckedUnit canon output₂.gamma (certOkOf env₂.registry)}
    (hsurface₁ : Surface.Checks env₁ input₁ output₁)
    (hchecked₁ : Check.Unit.checkUnit output₁.gamma env₁.registry output₁.ground
      output₁.unit = .ok acc₁)
    (hsurface₂ : Surface.Checks env₂ input₂ output₂)
    (hchecked₂ : Check.Unit.checkUnit output₂.gamma env₂.registry output₂.ground
      output₂.unit = .ok acc₂)
    (hf : Function.Injective f)
    (hargs : acc₂.program.args = acc₁.program.args.map (mapAssur f))
    (hatts : acc₂.program.atts = acc₁.program.atts.map (mapAssurAtt f)) :
    Surface.directAF hsurface₂ = Surface.directAF hsurface₁ := by
  rw [Surface.direct_compiled_agree hsurface₁ hchecked₁,
    Surface.direct_compiled_agree hsurface₂ hchecked₂,
    checkedAF_map hf hargs hatts]

/-- **The link instance.** When the two surface programs elaborate to the two
sides of a link — a fragment and its relabeling, in one admissible context —
the argument and attack correspondence is exactly what `link_relabel_commutes`
already establishes, so the surface frameworks coincide. -/
theorem surface_directAF_link
    {env₁ env₂ : Surface.Env canon} {input₁ input₂ : Surface.Input}
    {output₁ output₂ : Surface.Elaborated canon}
    {f : Assurance → Assurance} {C : Context} {F : Fragment}
    {acc₁ : Lara.Unit.CheckedUnit canon output₁.gamma (certOkOf env₁.registry)}
    {acc₂ : Lara.Unit.CheckedUnit canon output₂.gamma (certOkOf env₂.registry)}
    (hsurface₁ : Surface.Checks env₁ input₁ output₁)
    (hchecked₁ : Check.Unit.checkUnit output₁.gamma env₁.registry output₁.ground
      output₁.unit = .ok acc₁)
    (hsurface₂ : Surface.Checks env₂ input₂ output₂)
    (hchecked₂ : Check.Unit.checkUnit output₂.gamma env₂.registry output₂.ground
      output₂.unit = .ok acc₂)
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf env₁.registry) (certOkOf env₂.registry))
    (hadm : Admissible env₁.registry C F) (hfix : FixesContext f C)
    (hunit₁ : output₁.unit = linkedUnit env₁.registry C F)
    (hunit₂ : output₂.unit = linkedUnit env₂.registry C (mapAssurFrag f F)) :
    Surface.directAF hsurface₂ = Surface.directAF hsurface₁ := by
  have hsound₁ := Check.Unit.checkUnit_sound hchecked₁
  have hsound₂ := Check.Unit.checkUnit_sound hchecked₂
  obtain ⟨hargs, hatts⟩ :=
    link_relabel_commutes hf hpres hfix.args hfix.atts hadm.ctx.support hadm.frag.support
  refine surface_directAF_relabel hsurface₁ hchecked₁ hsurface₂ hchecked₂ hf ?_ ?_
  · rw [hsound₂.2.2.2.2.2.2.2.2.1, hsound₁.2.2.2.2.2.2.2.2.1, hunit₁, hunit₂]
    exact hargs
  · rw [hsound₂.2.2.2.2.2.2.2.2.2.1, hsound₁.2.2.2.2.2.2.2.2.2.1, hunit₁, hunit₂]
    exact hatts

end Lara.Context
