import Lara.BHL.WeakestLiberal

namespace Lara.BHL

variable {D : Type} [MeasurableSpace D]

noncomputable section

/-- A mathematical contract for a family of finite legal assertion trees.
The concrete control-log family must instantiate this contract by proof; it is
not an interpretation callback or an additional BHL derivation rule. -/
structure WlpAssertionFamily (ctx : ProgramContext D) where
  formula : {Γ : List GhostSort} → Program → Assertion Γ → Assertion Γ
  represents : ∀ {Γ : List GhostSort} (env : GhostEnv D Primitive Γ)
    (before : World D Primitive) (program : Program) (post : Assertion Γ),
    Admitted ctx.model.dynamics before →
      (satisfies ctx.interpretation ctx.model env before (formula program post) ↔
        weakestLiberalPrecondition ctx env program post before)

end
end Lara.BHL
