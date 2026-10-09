import Lara.BHL.ControlLogEdges

namespace Lara.BHL.ControlLogSyntax

variable {D : Type} [MeasurableSpace D] {Γ : List GhostSort}

noncomputable section

private theorem equal_atom_right (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (view : SemanticView D) {sort : TermSort} (left right : AssertionTerm Γ sort)
    (value : TermValue D Primitive sort)
    (rightEvaluated : evalTerm ctx.interpretation ctx.model env view right = some value) :
    atomMeaning ctx.interpretation ctx.model env view (.equal left right) ↔
      evalTerm ctx.interpretation ctx.model env view left = some value := by
  change (∃ actual, evalTerm ctx.interpretation ctx.model env view left = some actual ∧
    evalTerm ctx.interpretation ctx.model env view right = some actual) ↔ _
  constructor
  · rintro ⟨actual, leftEvaluated, actualRight⟩
    have valueEqual : value = actual := Option.some.inj (rightEvaluated.symm.trans actualRight)
    exact leftEvaluated.trans (congrArg some valueEqual.symm)
  · intro leftEvaluated
    exact ⟨value, leftEvaluated, rightEvaluated⟩

private theorem int_compare_atom (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (view : SemanticView D) (comparison : Comparison)
    (left right : AssertionTerm Γ (.value .integer)) (a b : Int)
    (leftEvaluated : evalTerm ctx.interpretation ctx.model env view left = some a)
    (rightEvaluated : evalTerm ctx.interpretation ctx.model env view right = some b) :
    atomMeaning ctx.interpretation ctx.model env view (.intCompare comparison left right) ↔
      compareInt comparison a b := by
  change (∃ actualLeft actualRight,
    evalTerm ctx.interpretation ctx.model env view left = some actualLeft ∧
    evalTerm ctx.interpretation ctx.model env view right = some actualRight ∧
    compareInt comparison actualLeft actualRight) ↔ _
  constructor
  · rintro ⟨actualLeft, actualRight, actualLeftEvaluated, actualRightEvaluated, compared⟩
    have leftEqual : a = actualLeft :=
      Option.some.inj (leftEvaluated.symm.trans actualLeftEvaluated)
    have rightEqual : b = actualRight :=
      Option.some.inj (rightEvaluated.symm.trans actualRightEvaluated)
    simpa only [← leftEqual, ← rightEqual] using compared
  · intro compared
    exact ⟨a, b, leftEvaluated, rightEvaluated, compared⟩

private theorem zero_equal_atom (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (view : SemanticView D) :
    atomMeaning ctx.interpretation ctx.model env view (.equal (.integer 0) (.integer 0)) :=
  ⟨0, rfl, rfl⟩

/-- The header checks admission only for the program source, while metadata reads
retain their ordinary partial evaluation at rigid, possibly non-admitted worlds. -/
theorem header_satisfaction (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (program : Program) (view : SemanticView D) :
    viewModalSatisfaction ctx.interpretation ctx.model env view (header terms program) ↔
      Admitted ctx.model.dynamics log.source ∧
        semanticView ctx.model.dynamics log.source = view ∧
        log.readCell 0 .control = some (program.controlCode (some program)) ∧
        log.readCell 0 .commands = some 0 ∧
        log.readCell log.controlStates.length .control = some 0 ∧
        log.readCell log.controlStates.length .commands = some (log.programStates.length : Int) := by
  have sourceView :
      evalTerm ctx.interpretation ctx.model env view (.currentView terms.source) =
        some (semanticView ctx.model.dynamics log.source) := by
    simp only [evalTerm, (denotes view).1, Option.map_some]
  have firstCode := Terms.eval_cell terms ctx env log denotes view (.integer 0) 0 rfl .control
  have firstCount := Terms.eval_count terms ctx env log denotes view (.integer 0) 0 rfl
  have finalIndex := Terms.eval_controlLength terms ctx env log denotes view
  have finalCode := Terms.eval_cell terms ctx env log denotes view
    (.traceLength terms.controlStates) log.controlStates.length finalIndex .control
  have finalCount := Terms.eval_count terms ctx env log denotes view
    (.traceLength terms.controlStates) log.controlStates.length finalIndex
  have programLength := Terms.eval_programLength terms ctx env log denotes view
  have sourceAdmission :
      atomMeaning ctx.interpretation ctx.model env view (.admitted terms.source) ↔
        Admitted ctx.model.dynamics log.source := by
    change (∃ source, evalTerm ctx.interpretation ctx.model env view terms.source = some source ∧
      Admitted ctx.model.dynamics source) ↔ _
    rw [(denotes view).1]
    simp only [Option.some.injEq]
    constructor
    · rintro ⟨source, rfl, admitted⟩
      exact admitted
    · intro admitted
      exact ⟨log.source, rfl, admitted⟩
  have sourceEquality :
      atomMeaning ctx.interpretation ctx.model env view
        (.equal (.currentView terms.source) .ambient) ↔
        semanticView ctx.model.dynamics log.source = view := by
    rw [equal_atom_right ctx env view _ _ view rfl, sourceView, Option.some.injEq]
  have initialCode :
      atomMeaning ctx.interpretation ctx.model env view
        (.equal (terms.cell (.integer 0) .control)
          (.integer (program.controlCode (some program)))) ↔
        log.readCell 0 .control = some (program.controlCode (some program)) := by
    rw [equal_atom_right ctx env view _ _ (program.controlCode (some program)) rfl, firstCode]
  have initialCount :
      atomMeaning ctx.interpretation ctx.model env view
        (.equal (terms.count (.integer 0)) (.integer 0)) ↔
        log.readCell 0 .commands = some 0 := by
    rw [equal_atom_right ctx env view _ _ 0 rfl, firstCount]
  have terminalCode :
      atomMeaning ctx.interpretation ctx.model env view
        (.equal (terms.cell (.traceLength terms.controlStates) .control) (.integer 0)) ↔
        log.readCell log.controlStates.length .control = some 0 := by
    rw [equal_atom_right ctx env view _ _ 0 rfl, finalCode]
  have terminalCount :
      atomMeaning ctx.interpretation ctx.model env view
        (.equal (terms.count (.traceLength terms.controlStates))
          (.traceLength terms.programStates)) ↔
        log.readCell log.controlStates.length .commands = some (log.programStates.length : Int) := by
    rw [equal_atom_right ctx env view _ _ (log.programStates.length : Int) programLength, finalCount]
  simp only [header, conjunction, List.foldr_cons, List.foldr_nil, trueFormula,
    viewModalSatisfaction, sourceAdmission, sourceEquality, initialCode, initialCount,
    terminalCode, terminalCount, zero_equal_atom ctx env view, and_true]

private theorem denotes_push_integer (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (value : Int) :
    (terms.rename (GhostRenaming.weaken (other := .value .integer))).Denotes ctx
      (GhostEnv.push (sort := .value .integer) value env) log := by
  apply (Terms.denotes_rename terms ctx (GhostRenaming.weaken (other := .value .integer))
    (GhostEnv.push (sort := .value .integer) value env) log).mpr
  simpa only [GhostEnv.reindex_weaken_push] using denotes

private theorem index_range_satisfaction (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (value : Int) (view : SemanticView D) :
    viewModalSatisfaction ctx.interpretation ctx.model
      (GhostEnv.push (sort := .value .integer) value env) view (conjunction [
        .atom (.intCompare .lessEqual (.integer 0) (.ghost (.bound .here))),
        .atom (.intCompare .less (.ghost (.bound .here))
          (.traceLength (terms.rename GhostRenaming.weaken).controlStates))]) ↔
      0 ≤ value ∧ value < (log.controlStates.length : Int) := by
  have renamedDenotes := denotes_push_integer terms ctx env log denotes value
  have indexEvaluated :
      evalTerm ctx.interpretation ctx.model
        (GhostEnv.push (sort := .value .integer) value env) view
        (.ghost (.bound .here) : AssertionTerm (.value .integer :: Γ) (.value .integer)) =
        some value := rfl
  have lengthEvaluated := Terms.eval_controlLength (terms.rename GhostRenaming.weaken)
    ctx (GhostEnv.push (sort := .value .integer) value env) log renamedDenotes view
  have lowerBound :
      atomMeaning ctx.interpretation ctx.model
        (GhostEnv.push (sort := .value .integer) value env) view
        (.intCompare .lessEqual (.integer 0) (.ghost (.bound .here))) ↔ 0 ≤ value :=
    int_compare_atom ctx (GhostEnv.push (sort := .value .integer) value env) view
      .lessEqual _ _ 0 value rfl indexEvaluated
  have upperBound :
      atomMeaning ctx.interpretation ctx.model
        (GhostEnv.push (sort := .value .integer) value env) view
        (.intCompare .less (.ghost (.bound .here))
          (.traceLength (terms.rename GhostRenaming.weaken).controlStates)) ↔
        value < (log.controlStates.length : Int) :=
    int_compare_atom ctx (GhostEnv.push (sort := .value .integer) value env) view
      .less _ _ value (log.controlStates.length : Int) indexEvaluated lengthEvaluated
  simp only [conjunction, List.foldr_cons, List.foldr_nil, trueFormula,
    viewModalSatisfaction, lowerBound, upperBound,
    zero_equal_atom ctx (GhostEnv.push (sort := .value .integer) value env) view, and_true]

private theorem ranged_edges_satisfaction (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (program : Program) (view : SemanticView D) :
    (∀ value : Int, viewAssertionSatisfaction ctx.interpretation ctx.model
      (GhostEnv.push (sort := .value .integer) value env) view
      ((Assertion.modal (conjunction [
        .atom (.intCompare .lessEqual (.integer 0) (.ghost (.bound .here))),
        .atom (.intCompare .less (.ghost (.bound .here))
          (.traceLength (terms.rename GhostRenaming.weaken).controlStates))])).implies
        (.modal (edges (terms.rename GhostRenaming.weaken) program (.ghost (.bound .here)))))) ↔
      ∀ index, index < log.controlStates.length → log.edge ctx program index := by
  constructor
  · intro allEdges index indexBound
    have renamedDenotes := denotes_push_integer terms ctx env log denotes (index : Int)
    have guarded := (viewAssertionSatisfaction_implies ctx.interpretation ctx.model
      (GhostEnv.push (sort := .value .integer) (index : Int) env) view _ _).mp
        (allEdges (index : Int))
    have rangeSatisfied := (index_range_satisfaction terms ctx env log denotes (index : Int) view).mpr
      (show 0 ≤ (index : Int) ∧ (index : Int) < (log.controlStates.length : Int) by omega)
    exact (edges_satisfaction (terms.rename GhostRenaming.weaken) ctx
      (GhostEnv.push (sort := .value .integer) (index : Int) env) log renamedDenotes program
      (.ghost (.bound .here)) index (by intro actualView; rfl) view).mp
        (guarded rangeSatisfied)
  · intro localEdges value
    apply (viewAssertionSatisfaction_implies ctx.interpretation ctx.model
      (GhostEnv.push (sort := .value .integer) value env) view _ _).mpr
    intro rangeSatisfied
    have bounds := (index_range_satisfaction terms ctx env log denotes value view).mp rangeSatisfied
    let index := value.toNat
    have valueEqual : value = (index : Int) := by
      dsimp [index]
      omega
    have indexBound : index < log.controlStates.length := by omega
    have renamedDenotes := denotes_push_integer terms ctx env log denotes value
    have indexEvaluated : ∀ actualView,
        evalTerm ctx.interpretation ctx.model
          (GhostEnv.push (sort := .value .integer) value env) actualView
          (.ghost (.bound .here) : AssertionTerm (.value .integer :: Γ) (.value .integer)) =
          some (index : Int) := by
      intro actualView
      change some value = some (index : Int)
      rw [valueEqual]
    exact (edges_satisfaction (terms.rename GhostRenaming.weaken) ctx
      (GhostEnv.push (sort := .value .integer) value env) log renamedDenotes program
      (.ghost (.bound .here)) index indexEvaluated view).mpr (localEdges index indexBound)

/-- The integer binder enforces exactly the finite Nat-indexed local edges;
negative and out-of-range integers have a false antecedent, not a truncated edge. -/
theorem validLocalLog_satisfaction (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (program : Program) (before : World D Primitive) :
    referenceAssertionSatisfaction ctx.interpretation ctx.model env before
      (validLocalLog terms program) ↔
      log.Valid ctx program ∧
        semanticView ctx.model.dynamics log.source = semanticView ctx.model.dynamics before := by
  rw [reference_view_assertion_correspondence]
  change (viewModalSatisfaction ctx.interpretation ctx.model env
      (semanticView ctx.model.dynamics before) (header terms program) ∧
    ∀ value : Int, viewAssertionSatisfaction ctx.interpretation ctx.model
      (GhostEnv.push (sort := .value .integer) value env) (semanticView ctx.model.dynamics before)
      ((Assertion.modal (conjunction [
        .atom (.intCompare .lessEqual (.integer 0) (.ghost (.bound .here))),
        .atom (.intCompare .less (.ghost (.bound .here))
          (.traceLength (terms.rename GhostRenaming.weaken).controlStates))])).implies
        (.modal (edges (terms.rename GhostRenaming.weaken) program (.ghost (.bound .here)))))) ↔ _
  rw [header_satisfaction terms ctx env log denotes program,
    ranged_edges_satisfaction terms ctx env log denotes program]
  constructor
  · rintro ⟨⟨admitted, sourceView, initialCode, initialCount, finalCode, finalCount⟩, localEdges⟩
    exact ⟨⟨admitted, initialCode, initialCount, finalCode, finalCount, localEdges⟩, sourceView⟩
  · rintro ⟨⟨admitted, initialCode, initialCount, finalCode, finalCount, localEdges⟩, sourceView⟩
    exact ⟨⟨admitted, sourceView, initialCode, initialCount, finalCode, finalCount⟩, localEdges⟩

private theorem terminal_reference_iff (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (before : World D Primitive) (log : ControlLog D) (post : Assertion Γ) :
    referenceAssertionSatisfaction ctx.interpretation ctx.model (Terms.environment log env) before
      (.atWorld Terms.bound.terminal (post.renameGhosts weakenOriginal)) ↔
      satisfies ctx.interpretation ctx.model env log.terminal post := by
  have terminalEvaluated := Terms.eval_terminal (Terms.bound (Γ := Γ)) ctx
    (Terms.environment log env) log (Terms.denotes_bound ctx log env)
    (semanticView ctx.model.dynamics before)
  change (∃ terminalWorld,
    evalTerm ctx.interpretation ctx.model (Terms.environment log env)
      (semanticView ctx.model.dynamics before) Terms.bound.terminal = some terminalWorld ∧
    Admitted ctx.model.dynamics terminalWorld ∧
    referenceAssertionSatisfaction ctx.interpretation ctx.model (Terms.environment log env)
      terminalWorld (post.renameGhosts weakenOriginal)) ↔
    Admitted ctx.model.dynamics log.terminal ∧
      referenceAssertionSatisfaction ctx.interpretation ctx.model env log.terminal post
  rw [terminalEvaluated]
  simp only [Option.some.injEq, referenceAssertionSatisfaction_renameGhosts, reindex_original]
  constructor
  · rintro ⟨terminalWorld, rfl, satisfied⟩
    exact satisfied
  · intro satisfied
    exact ⟨log.terminal, rfl, satisfied⟩

/-- Four typed outer binders quantify over actual log records. The arbitrary
postcondition is preserved by the full capture-avoiding renaming theorem. -/
theorem representative_reference_iff (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (before : World D Primitive) (program : Program) (post : Assertion Γ) :
    referenceAssertionSatisfaction ctx.interpretation ctx.model env before
      (representative program post) ↔
      ∀ log : ControlLog D, log.Valid ctx program →
        semanticView ctx.model.dynamics log.source = semanticView ctx.model.dynamics before →
        satisfies ctx.interpretation ctx.model env log.terminal post := by
  constructor
  · intro represented log valid sourceView
    have guarded : referenceAssertionSatisfaction ctx.interpretation ctx.model
        (Terms.environment log env) before
        ((validLocalLog Terms.bound program).implies
          (.atWorld Terms.bound.terminal (post.renameGhosts weakenOriginal))) :=
      represented log.source log.programStates log.controlSeed log.controlStates
    have localLogSatisfied := (validLocalLog_satisfaction Terms.bound ctx
      (Terms.environment log env) log (Terms.denotes_bound ctx log env) program before).mpr
        ⟨valid, sourceView⟩
    have terminalSatisfied := (referenceAssertionSatisfaction_implies ctx.interpretation ctx.model
      (Terms.environment log env) before _ _).mp guarded localLogSatisfied
    exact (terminal_reference_iff ctx env before log post).mp terminalSatisfied
  · intro represented source programStates controlSeed controlStates
    let log : ControlLog D := ⟨source, programStates, controlSeed, controlStates⟩
    change referenceAssertionSatisfaction ctx.interpretation ctx.model
      (Terms.environment log env) before
      ((validLocalLog Terms.bound program).implies
        (.atWorld Terms.bound.terminal (post.renameGhosts weakenOriginal)))
    apply (referenceAssertionSatisfaction_implies ctx.interpretation ctx.model
      (Terms.environment log env) before _ _).mpr
    intro localLogSatisfied
    obtain ⟨valid, sourceView⟩ := (validLocalLog_satisfaction Terms.bound ctx
      (Terms.environment log env) log (Terms.denotes_bound ctx log env) program before).mp
        localLogSatisfied
    exact (terminal_reference_iff ctx env before log post).mpr (represented log valid sourceView)

end
end Lara.BHL.ControlLogSyntax
