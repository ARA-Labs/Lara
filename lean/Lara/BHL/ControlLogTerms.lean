import Lara.BHL.ControlLogSyntax

namespace Lara.BHL.ControlLogSyntax

variable {D : Type} [MeasurableSpace D] {Γ Δ : List GhostSort}

noncomputable section

namespace Terms

/-- Rigid log terms denote the same four actual carriers at every modal view. -/
def Denotes (terms : Terms Γ) (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (log : ControlLog D) : Prop :=
  ∀ view,
    evalTerm ctx.interpretation ctx.model env view terms.source = some log.source ∧
    evalTerm ctx.interpretation ctx.model env view terms.programStates = some log.programStates ∧
    evalTerm ctx.interpretation ctx.model env view terms.controlSeed = some log.controlSeed ∧
    evalTerm ctx.interpretation ctx.model env view terms.controlStates = some log.controlStates

 def environment (log : ControlLog D) (env : GhostEnv D Primitive Γ) :
    GhostEnv D Primitive (Context Γ) :=
  GhostEnv.push log.controlStates (GhostEnv.push log.controlSeed
    (GhostEnv.push log.programStates (GhostEnv.push log.source env)))

 theorem denotes_bound (ctx : ProgramContext D) (log : ControlLog D)
    (env : GhostEnv D Primitive Γ) : bound.Denotes ctx (environment log env) log := by
  intro view
  exact ⟨rfl, rfl, rfl, rfl⟩

 theorem denotes_rename (terms : Terms Γ) (ctx : ProgramContext D)
    (ρ : GhostRenaming Γ Δ) (env : GhostEnv D Primitive Δ) (log : ControlLog D) :
    (terms.rename ρ).Denotes ctx env log ↔
      terms.Denotes ctx (GhostEnv.reindex ρ env) log := by
  simp only [Denotes, rename, evalTerm_renameGhosts]

 theorem eval_traceTake (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (view : SemanticView D) (trace : AssertionTerm Γ .trace)
    (index : AssertionTerm Γ (.value .integer)) (states : List (State D Primitive)) (j : Nat)
    (traceEvaluated : evalTerm ctx.interpretation ctx.model env view trace = some states)
    (indexEvaluated : evalTerm ctx.interpretation ctx.model env view index = some (j : Int)) :
    evalTerm ctx.interpretation ctx.model env view (.traceTake trace index) =
      some (states.take j) := by
  simp [evalTerm, traceEvaluated, indexEvaluated]

 theorem eval_metadataWorld (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (view : SemanticView D) (index : AssertionTerm Γ (.value .integer)) (j : Nat)
    (indexEvaluated : evalTerm ctx.interpretation ctx.model env view index = some (j : Int)) :
    evalTerm ctx.interpretation ctx.model env view (terms.metadataWorld index) =
      some (log.metadataPrefix j) := by
  exact ControlMetadata.evalTerm_appendWorld ctx.interpretation ctx.model env view _ _ _ _
    (denotes view).2.2.1
    (eval_traceTake ctx env view terms.controlStates index log.controlStates j
      (denotes view).2.2.2 indexEvaluated)

 theorem eval_cell (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (view : SemanticView D) (index : AssertionTerm Γ (.value .integer)) (j : Nat)
    (indexEvaluated : evalTerm ctx.interpretation ctx.model env view index = some (j : Int))
    (name : LogCell) :
    evalTerm ctx.interpretation ctx.model env view (terms.cell index name) =
      log.readCell j name := by
  exact ControlMetadata.evalTerm_valueRead_currentView ctx.interpretation ctx.model env view
    _ _ (eval_metadataWorld terms ctx env log denotes view index j indexEvaluated) name.toVariable

 theorem eval_count (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (view : SemanticView D) (index : AssertionTerm Γ (.value .integer)) (j : Nat)
    (indexEvaluated : evalTerm ctx.interpretation ctx.model env view index = some (j : Int)) :
    evalTerm ctx.interpretation ctx.model env view (terms.count index) =
      log.readCell j .commands :=
  eval_cell terms ctx env log denotes view index j indexEvaluated .commands

 theorem eval_programWorld (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (view : SemanticView D) (index : AssertionTerm Γ (.value .integer)) (j count : Nat)
    (indexEvaluated : evalTerm ctx.interpretation ctx.model env view index = some (j : Int))
    (countEvaluated : log.readCell j .commands = some (count : Int)) :
    evalTerm ctx.interpretation ctx.model env view (terms.programWorld index) =
      some (log.programPrefix count) := by
  exact ControlMetadata.evalTerm_appendWorld ctx.interpretation ctx.model env view _ _ _ _
    (denotes view).1
    (eval_traceTake ctx env view terms.programStates (terms.count index) log.programStates count
      (denotes view).2.1
      ((eval_count terms ctx env log denotes view index j indexEvaluated).trans countEvaluated))

 theorem eval_programView (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (view : SemanticView D) (index : AssertionTerm Γ (.value .integer)) (j count : Nat)
    (indexEvaluated : evalTerm ctx.interpretation ctx.model env view index = some (j : Int))
    (countEvaluated : log.readCell j .commands = some (count : Int)) :
    evalTerm ctx.interpretation ctx.model env view (terms.programView index) =
      some (semanticView ctx.model.dynamics (log.programPrefix count)) := by
  simp only [programView, evalTerm,
    eval_programWorld terms ctx env log denotes view index j count indexEvaluated countEvaluated,
    Option.map_some]

 theorem eval_terminal (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (view : SemanticView D) :
    evalTerm ctx.interpretation ctx.model env view terms.terminal = some log.terminal := by
  exact ControlMetadata.evalTerm_appendWorld ctx.interpretation ctx.model env view _ _ _ _
    (denotes view).1 (denotes view).2.1

 theorem eval_programLength (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (view : SemanticView D) :
    evalTerm ctx.interpretation ctx.model env view (.traceLength terms.programStates) =
      some (log.programStates.length : Int) := by
  simp only [evalTerm, (denotes view).2.1, Option.map_some]
  rfl

 theorem eval_controlLength (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (view : SemanticView D) :
    evalTerm ctx.interpretation ctx.model env view (.traceLength terms.controlStates) =
      some (log.controlStates.length : Int) := by
  simp only [evalTerm, (denotes view).2.2.2, Option.map_some]
  rfl

end Terms

omit [MeasurableSpace D] in
 theorem reindex_original (log : ControlLog D) (env : GhostEnv D Primitive Γ) :
    GhostEnv.reindex weakenOriginal (Terms.environment log env) = env := rfl

 theorem eval_nextIndex (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (view : SemanticView D) (index : AssertionTerm Γ (.value .integer)) (j : Nat)
    (evaluated : evalTerm ctx.interpretation ctx.model env view index = some (j : Int)) :
    evalTerm ctx.interpretation ctx.model env view (.intAdd index (.integer 1)) =
      some ((j + 1 : Nat) : Int) := by
  simp [evalTerm, evaluated]

end
end Lara.BHL.ControlLogSyntax
