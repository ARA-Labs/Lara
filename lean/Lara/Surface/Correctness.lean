import Lara.Surface.Elaborate

namespace Lara.Surface
open Lara

/-- The core-visible open-question sequence. Authored argument identifiers are
tracked separately because `Lara.Unit` erases them. -/
def coreOpenQuestions (unit : Lara.Unit) : List (List Support.QuestionId) :=
  unit.args.map rootHoles

private theorem bind_error_reduce2 {α β} (error : Error)
    (next : α → Except Error β) :
    (do let value ← (Except.error error : Except Error α); next value) =
      Except.error error := rfl

private theorem admissionArgs_filter_alignment2
    (pairs : List ReconstructedArgument)
    (keep : String × Lara.Support.SupportTerm → Bool) :
    (admissionArgs pairs).filter keep =
      (pairs.filter fun pair => keep (pair.argument.id.val, pair.core)).map
        fun pair => (pair.argument.id.val, pair.core) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      simp only [admissionArgs, List.map_cons, List.filter_cons]
      split <;> simp_all [admissionArgs]

private theorem wrap_argId_vals2 (ids : List Presentation.ArgId) :
    (ids.map (·.val)).map (fun id => (⟨id⟩ : Presentation.ArgId)) = ids := by
  induction ids with
  | nil => rfl
  | cons id rest ih =>
      cases id
      simp [ih]

private def admissionLeafMetasOfDecls2 (decls : List Presentation.Decl) :
    List Lara.Admission.LeafMeta :=
  decls.filterMap fun
    | .leaf leaf => some ⟨toSupportLeafId leaf.id, leaf.kind, leaf.provenance⟩
    | _ => none

private theorem DeclsExpand_admissionLeafMetas2
    {env gamma source target}
    (h : DeclsExpand env gamma source target) :
    admissionLeafMetasOfDecls2 source = admissionLeafMetasOfDecls2 target := by
  induction h <;> simp_all [admissionLeafMetasOfDecls2]

private theorem admissionLeafMetasOfDecls2_cons
    (declaration : Presentation.Decl) {left right : List Presentation.Decl}
    (h : admissionLeafMetasOfDecls2 left = admissionLeafMetasOfDecls2 right) :
    admissionLeafMetasOfDecls2 (declaration :: left) =
      admissionLeafMetasOfDecls2 (declaration :: right) := by
  cases declaration <;> simpa [admissionLeafMetasOfDecls2] using h

private theorem DeclsExpandComparisons_admissionLeafMetas2
    {policy program source target generated}
    (h : DeclsExpandComparisons policy program source target generated) :
    admissionLeafMetasOfDecls2 source = admissionLeafMetasOfDecls2 target := by
  induction h with
  | nil => rfl
  | keep hkeep tail ih => exact admissionLeafMetasOfDecls2_cons _ ih
  | expand hdata tail ih =>
      simpa [admissionLeafMetasOfDecls2, generatedDecls] using ih

private theorem admissionLeafMetas_eq_ofDecls2 (program : Presentation.Program) :
    admissionLeafMetas program = admissionLeafMetasOfDecls2 program.decls := by
  unfold admissionLeafMetas leafRecords
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp_all [admissionLeafMetasOfDecls2]

private theorem expansions_admissionLeafMetas2
    {source mid target generated}
    (hvalues : ExpandsValues source mid)
    (hcomparisons : ExpandsComparisons policy mid target generated) :
    admissionLeafMetas source = admissionLeafMetas target := by
  cases hvalues with
  | intro henv hgamma hbindings hartifact hdigest hpolicy hbackends hdecls =>
      cases hcomparisons with
      | intro hcomparisons hartifact' hdigest' hpolicy' hbackends' hbindings' =>
          rw [admissionLeafMetas_eq_ofDecls2 source,
            admissionLeafMetas_eq_ofDecls2 target]
          exact (DeclsExpand_admissionLeafMetas2 hdecls).trans
            (DeclsExpandComparisons_admissionLeafMetas2 hcomparisons)

private theorem decisionFor_admissionRows2 (policy : Presentation.Policy)
    (kind : Presentation.LeafKind) (provenance : Presentation.Provenance) :
    Lara.Admission.decisionFor (admissionRows policy) kind provenance =
      admissionDecision policy.admission kind provenance := by
  unfold admissionRows admissionDecision Lara.Admission.decisionFor
  have findMap :
      ∀ entries : List Presentation.AdmissionEntry,
        (entries.map fun row : Presentation.AdmissionEntry =>
          (⟨row.1, row.2⟩ : Lara.Admission.AdmissionRow)).find?
            (fun row => decide (row.key = (kind, provenance))) =
          (entries.find?
            (fun row => decide (row.1 = (kind, provenance)))).map
              (fun row => (⟨row.1, row.2⟩ : Lara.Admission.AdmissionRow)) := by
    intro entries
    induction entries with
    | nil => rfl
    | cons entry rest ih =>
        by_cases hkey : entry.1 = (kind, provenance)
        · simp [hkey]
        · simp [hkey, ih]
  rw [findMap policy.admission]
  cases policy.admission.find?
      (fun row => decide (row.1 = (kind, provenance))) <;> rfl

private theorem decision_ne_reject_of_first_none2
    (table : List Lara.Admission.AdmissionRow)
    (metas : List Lara.Admission.LeafMeta)
    (hn : Lara.Admission.firstAdmissionRejection table metas = none) :
    ∀ m ∈ metas,
      Lara.Admission.decisionFor table m.kind m.provenance ≠ .reject := by
  intro m hm
  induction metas with
  | nil => simp at hm
  | cons head tail ih =>
      by_cases hd :
          Lara.Admission.decisionFor table head.kind head.provenance = .reject
      · simp [Lara.Admission.firstAdmissionRejection,
          Lara.Admission.firstAdmissionRejection.go, hd] at hn
      · have htail :
            Lara.Admission.firstAdmissionRejection table tail = none := by
          simpa [Lara.Admission.firstAdmissionRejection,
            Lara.Admission.firstAdmissionRejection.go, hd] using hn
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hd
        · exact ih htail hm

private theorem pass_inv {env : Env canon} {input : Input}
    {result : ElaboratedWithAudit canon}
    (hsuccess : elaborateWithAudit env input = .ok result) :
    ∃ mid generated,
      elaborationPrologue input = .ok () ∧
      expandValues input.policy input.program = .ok mid ∧
      expandComparisons input.policy mid =
        .ok (result.declared.semanticProgram, generated) ∧
      semanticIdentifierChecks input.policy input.program = .ok () := by
  unfold elaborateWithAudit at hsuccess
  cases hprologue : elaborationPrologue input with
  | error error =>
    rw [hprologue] at hsuccess
    simp only [bind_error_reduce2] at hsuccess
    cases hsuccess
  | ok ignored =>
    cases ignored
    simp only [hprologue, bind_ok_reduce] at hsuccess
    cases hvalues : expandValues input.policy input.program with
    | error error =>
      rw [hvalues] at hsuccess
      simp only [bind_error_reduce2] at hsuccess
      cases hsuccess
    | ok mid =>
      simp only [hvalues, bind_ok_reduce] at hsuccess
      cases hcomparisons : expandComparisons input.policy mid with
      | error error =>
        rw [hcomparisons] at hsuccess
        simp only [bind_error_reduce2] at hsuccess
        cases hsuccess
      | ok comparisonResult =>
        rcases comparisonResult with ⟨semantic, generated⟩
        simp only [hcomparisons, bind_ok_reduce] at hsuccess
        cases hsemantic : semanticIdentifierChecks input.policy input.program with
        | error error =>
          rw [hsemantic] at hsuccess
          simp only [bind_error_reduce2] at hsuccess
          cases hsuccess
        | ok ignored =>
          cases ignored
          simp only [hsemantic, bind_ok_reduce] at hsuccess
          cases hgroups : validateGroups semantic with
          | error error =>
            rw [hgroups] at hsuccess
            simp only [bind_error_reduce2] at hsuccess
            cases hsuccess
          | ok ignoredGroups =>
            simp only [hgroups, bind_ok_reduce] at hsuccess
            cases hreconstruct : reconstructArgs env semantic input.policy semantic.decls [] with
            | error failure =>
              cases failure <;>
                rw [hreconstruct] at hsuccess <;>
                simp only [bind_error_reduce2] at hsuccess <;>
                cases hsuccess
            | ok pairs =>
              simp only [hreconstruct, bind_ok_reduce] at hsuccess
              cases hsurface : resolveSurfaceAttacks input.policy
                  (pairs.map fun pair => (pair.argument.id, pair.core))
                  (surfaceAttacksOf semantic) with
              | error endpoints =>
                rw [hsurface] at hsuccess
                simp only [bind_error_reduce2] at hsuccess
                cases hsuccess
              | ok surfaceResolved =>
                simp only [hsurface, bind_ok_reduce] at hsuccess
                cases hraw : rawAttacksOfResolved (surfaceAttacksOf semantic) surfaceResolved with
                | none =>
                  rw [hraw] at hsuccess
                  simp only [bind_error_reduce2] at hsuccess
                  cases hsuccess
                | some rawAttacks =>
                  simp only [hraw, bind_ok_reduce] at hsuccess
                  cases hstatuses : resolveStatuses semantic with
                  | error error =>
                    rw [hstatuses] at hsuccess
                    simp only [bind_error_reduce2] at hsuccess
                    cases hsuccess
                  | ok statusAtoms =>
                    simp only [hstatuses, bind_ok_reduce] at hsuccess
                    by_cases hids : ((admissionArgs pairs).map (·.1)).Nodup
                    · simp only [hids, ↓reduceDIte] at hsuccess
                      cases haligned : resolveAligned (admissionArgs pairs) rawAttacks hids with
                      | error error =>
                        rw [haligned] at hsuccess
                        cases hsuccess
                      | ok aligned =>
                        simp only [haligned] at hsuccess
                        cases hadmission : Lara.Admission.evaluateAdmission canon
                            (admissionRows input.policy) (admissionLeafMetas semantic)
                            (admissionLeafTable semantic) (admissionArgs pairs) rawAttacks
                            (admissionGroups semantic) aligned with
                        | invalid invalid =>
                          cases invalid <;> rw [hadmission] at hsuccess <;> cases hsuccess
                        | rejected rejection =>
                          rw [hadmission] at hsuccess
                          cases hsuccess
                        | accepted admission =>
                          simp only [hadmission, Except.ok.injEq] at hsuccess
                          subst result
                          refine ⟨mid, generated, ?_, ?_, ?_, ?_⟩ <;> simpa
                    · rw [dif_neg hids] at hsuccess
                      cases hsuccess


private theorem assemble_from_audit {env : Env canon} {input : Input}
    {result : ElaboratedWithAudit canon}
    (hsupported : Supported input) (hadmission : AdmissionOK input)
    (hfresh : GeneratedIdsFresh input.program = true)
    (hsuccess : elaborateWithAudit env input = .ok result) :
    assemble env input = .ok result.output := by
  obtain ⟨mid, generated, hprologue, hvalues, hcomparisons, hsemantic⟩ :=
    pass_inv hsuccess
  have halign := elaborateWithAudit_alignment hsuccess
  have hguards := assembleGuards_complete hsupported hadmission hfresh
  have hgroups := validateGroups_complete halign.groupsWellFormed
  have hstatuses := resolveStatuses_complete halign.statusesWellFormed
  have hpairIds :
      (result.declared.pairs.map fun pair => pair.argument.id.val).Nodup := by
    simpa [admissionArgs, List.map_map, Function.comp_def] using halign.idsNodup
  have hchecks := resolveSurfaceAttacks_sound input.policy halign.surfaceResolution
  have hselection := checksAttacks_raw_selection_alignment hchecks halign.rawOrder
      ((keptReconstructed canon input.policy result.declared.semanticProgram
        result.declared.pairs).map (·.argument.id))
  let keepArgument : String × Lara.Support.SupportTerm → Bool := fun argument =>
    !Lara.Groups.usesLeaf
      (Lara.Admission.policyQuarantineSeed (admissionRows input.policy)
          (admissionLeafMetas result.declared.semanticProgram) ++
        Lara.Groups.quarantined canon
          (admissionLeafTable result.declared.semanticProgram)
          (admissionGroups result.declared.semanticProgram))
      argument.2
  have hkeptRows :=
    admissionArgs_filter_alignment2 result.declared.pairs keepArgument
  have hargsEq :
      (keptReconstructed canon input.policy result.declared.semanticProgram
          result.declared.pairs).map (·.core) =
        ((admissionArgs result.declared.pairs).filter keepArgument).map Prod.snd := by
    have h := congrArg (List.map Prod.snd) hkeptRows
    simpa [keptReconstructed, keepArgument, List.map_map, Function.comp_def] using h.symm
  have hidsRaw :
      ((keptReconstructed canon input.policy result.declared.semanticProgram
          result.declared.pairs).map (·.argument.id)).map (·.val) =
        ((admissionArgs result.declared.pairs).filter keepArgument).map Prod.fst := by
    have h := congrArg (List.map Prod.fst) hkeptRows
    simpa [keptReconstructed, keepArgument, List.map_map, Function.comp_def] using h.symm
  have hidsWrapped :
      (keptReconstructed canon input.policy result.declared.semanticProgram
          result.declared.pairs).map (·.argument.id) =
        ((admissionArgs result.declared.pairs).filter keepArgument).map
          (fun row => (⟨row.1⟩ : Presentation.ArgId)) := by
    calc
      _ = (((keptReconstructed canon input.policy
            result.declared.semanticProgram result.declared.pairs).map
              (·.argument.id)).map (·.val)).map
            (fun id => (⟨id⟩ : Presentation.ArgId)) :=
        (wrap_argId_vals2 _).symm
      _ = (((admissionArgs result.declared.pairs).filter keepArgument).map
            Prod.fst).map (fun id => (⟨id⟩ : Presentation.ArgId)) := by
        rw [hidsRaw]
      _ = _ := by simp [List.map_map, Function.comp_def]
  have hselection' := hselection
  rw [hidsRaw] at hselection'
  unfold assemble
  simp only [hprologue, hvalues, hcomparisons, hsemantic, hgroups,
    halign.reconstruction, dif_pos hpairIds, halign.surfaceResolution,
    hstatuses, hguards]
  apply congrArg Except.ok
  rw [halign.retainedOutput]
  simp only [outputFromAdmission, admissionKeptPairs]
  rw [halign.prune]
  simp [Lara.Admission.buildPrune, admissionArgs, keptReconstructed,
    surfaceGamma, surfaceGround, List.map_map, Function.comp_def]
  constructor
  · exact ⟨by
      simpa [admissionArgs, keepArgument, keptReconstructed] using hargsEq,
      by simpa [admissionArgs, keepArgument, keptReconstructed] using hselection'⟩
  · exact ⟨by
      simpa [admissionArgs, keepArgument, keptReconstructed] using hidsWrapped,
      by simpa [admissionArgs, keepArgument, keptReconstructed] using hselection'⟩

/-- Independent surface derivability preserves core acceptance, authored
argument order, core-visible open questions, and resolved attacks. -/
theorem elaborate_preserves (env : Env canon) (input : Input)
    (output : Elaborated canon) (h : Checks env input output) :
    ∃ checked,
      elaborate env input = .ok output ∧
      Check.Unit.checkUnit output.gamma env.registry output.ground output.unit =
        .ok checked ∧
      output.openQuestions.map Prod.fst = output.argIds ∧
      output.openQuestions.map Prod.snd = coreOpenQuestions output.unit ∧
      output.unit.atts = output.resolvedAttacks := by
  obtain ⟨checked, hchecked⟩ := h.core.checkUnit_complete
  rcases h.program with
    ⟨pairs, declaredResolved, hprogram, hpairIds, hattacks, hselected,
      hargIds, hargs, hclaims, hquestions⟩
  refine ⟨checked, elaborate_complete env input output h, hchecked, ?_, ?_,
    h.unitAttacks.symm⟩
  · rw [← hquestions, ← hargIds]
    simp [openQuestionsOf]
  · rw [← hquestions, coreOpenQuestions, ← hargs]
    simp [openQuestionsOf]

/-- Canonical elaboration and core acceptance reflect the independent surface
judgment on the supported fragment. -/
theorem elaborate_reflects (env : Env canon) (input : Input)
    (output : Elaborated canon)
    (checked :
      Lara.Unit.CheckedUnit canon output.gamma (Support.certOkOf env.registry))
    (hsupported : Supported input)
    (helab : elaborate env input = .ok output)
    (hcore : Check.Unit.checkUnit output.gamma env.registry output.ground output.unit =
      .ok checked) :
    Checks env input output := by
  cases haudit : elaborateWithAudit env input with
  | error error =>
      have : elaborate env input = .error error := by
        simp [elaborate, haudit, Except.map]
      rw [this] at helab
      cases helab
  | ok result =>
      have houtput : result.output = output := by
        simpa [elaborate, haudit, Except.map] using helab
      subst output
      obtain ⟨mid, generated, hprologue, hvalues, hcomparisons, hsemantic⟩ :=
        pass_inv haudit
      have hargNone : findDuplicate (argIds input.program) = none := by
        cases harg : findDuplicate (argIds input.program) with
        | none => rfl
        | some id =>
            simp [semanticIdentifierChecks, harg] at hsemantic
      have hclaimNone : findDuplicate (claimIds input.program) = none := by
        cases hclaim : findDuplicate (claimIds input.program) with
        | none => rfl
        | some id =>
            simp [semanticIdentifierChecks, hargNone, hclaim] at hsemantic
      have hfresh : GeneratedIdsFresh input.program = true :=
        generatedIdsFresh_of_ids_nodup
          (findDuplicate_none_nodup hargNone)
          (findDuplicate_none_nodup hclaimNone)
      have hvaluesRelation := expandValues_sound input.policy hvalues
      have hcomparisonsRelation := expandComparisons_sound input.policy hcomparisons
      have halign := elaborateWithAudit_alignment haudit
      have hmetaEq := expansions_admissionLeafMetas2
        hvaluesRelation hcomparisonsRelation
      have hadmissionConditions := Lara.Admission.evaluateAdmission_accepted_conditions
        halign.admissionEvaluation
      have hnoReject := hadmissionConditions.2.2.2
      have hlabels := (canonicalPremiseLabelsB_iff input.policy).2
        hsupported.canonical_labels
      have hadmissionKeys : (input.policy.admission.map Prod.fst).Nodup := by
        cases hdup : findDuplicate (input.policy.admission.map Prod.fst) with
        | none => exact findDuplicate_none_nodup hdup
        | some key =>
            simp [elaborationPrologue, hsupported.policy_matches, hlabels, hdup]
              at hprologue
      have hadmissionNoReject : ∀ leaf ∈ leafRecords input.program,
          admissionDecision input.policy.admission leaf.kind leaf.provenance ≠ .reject := by
        intro leaf hleaf
        have hmetaSource :
            (⟨toSupportLeafId leaf.id, leaf.kind, leaf.provenance⟩ :
              Lara.Admission.LeafMeta) ∈ admissionLeafMetas input.program := by
          exact List.mem_map_of_mem (f := fun (sourceLeaf : Presentation.Leaf) =>
            (⟨toSupportLeafId sourceLeaf.id, sourceLeaf.kind, sourceLeaf.provenance⟩ :
              Lara.Admission.LeafMeta)) hleaf
        have hmetaSemantic :
            (⟨toSupportLeafId leaf.id, leaf.kind, leaf.provenance⟩ :
              Lara.Admission.LeafMeta) ∈
              admissionLeafMetas result.declared.semanticProgram := by
          rw [← hmetaEq]
          exact hmetaSource
        have hdecision := decision_ne_reject_of_first_none2
          (admissionRows input.policy)
          (admissionLeafMetas result.declared.semanticProgram)
          hnoReject _ hmetaSemantic
        simpa [decisionFor_admissionRows2] using hdecision
      have hadmission : AdmissionOK input := by
        constructor
        · exact hadmissionKeys
        · exact hadmissionNoReject
      have hassemble := assemble_from_audit hsupported hadmission hfresh haudit
      exact assemble_sound env input result.output hassemble
        (CoreObligations.of_checkUnit_ok hcore)


/-- The authored obligation ledger is copied exactly from the source program. -/
theorem obligations_preserved {env : Env canon} {input : Input}
    {output : Elaborated canon} (h : Checks env input output) :
    output.authoredObligations = authoredObligationsOf input.program :=
  h.authoredObligations.symm

/-- The checked unit contains exactly the attacks retained by surface admission. -/
theorem attacks_preserved {env : Env canon} {input : Input}
    {output : Elaborated canon} (h : Checks env input output) :
    output.unit.atts = output.resolvedAttacks :=
  h.unitAttacks.symm

/-- Every successfully reconstructed and lowered argument retains its
presentation conclusion. -/
theorem conclusions_preserved (env : Env canon)
    (program : Presentation.Program) (policy : Presentation.Policy)
    (priors : List PriorArgument) (argument : Presentation.Arg)
    (built : PriorArgument) (core : Lara.Support.SupportTerm)
    (hbuild : reconstructArgument canon program policy priors argument = some built)
    (hlower : lowerToSupportTerm env program policy priors built.term = some core) :
    conclOfTerm program policy built.term = some built.conclusion :=
  reconstructArgument_preserves_conclusion env program policy priors argument
    built core hbuild hlower

/-- Authored argument identifiers and checked core arguments have the same
declaration order. -/
theorem argument_order_preserved {env : Env canon} {input : Input}
    {output : Elaborated canon} (h : Checks env input output) :
    output.openQuestions.map Prod.fst = output.argIds ∧
      output.openQuestions.map Prod.snd = coreOpenQuestions output.unit := by
  rcases h.program with
    ⟨pairs, declaredResolved, hprogram, hpairIds, hattacks, hselected,
      hargIds, hargs, hclaims, hquestions⟩
  constructor
  · rw [← hquestions, ← hargIds]
    simp [openQuestionsOf]
  · rw [← hquestions, coreOpenQuestions, ← hargs]
    simp [openQuestionsOf]

/-- Binder alpha-renaming cannot change the lowered named certificate. -/
theorem alpha_elaboration_invariant
    (startsIdent : String → Bool) (resolver : String → Option Nat)
    (encodeProp : String → Option String) (nPrem : Nat)
    (hNat : ∀ n, startsIdent (Nat.repr n) = false)
    {left right : Lara.NDNamed.NCert}
    (leftWF : Lara.NDNamed.WellFormed startsIdent resolver encodeProp nPrem [] left)
    (rightWF : Lara.NDNamed.WellFormed startsIdent resolver encodeProp nPrem [] right)
    (halpha : Lara.NDNamed.Alpha left right) :
    Lara.NDNamed.lowerNamed startsIdent resolver encodeProp nPrem []
        (Lara.NDNamed.render left) =
      Lara.NDNamed.lowerNamed startsIdent resolver encodeProp nPrem []
        (Lara.NDNamed.render right) :=
  lowerCertificate_alpha_invariant startsIdent resolver encodeProp nPrem hNat
    leftWF rightWF halpha


/-! ### Typed global-renaming equivariance -/

namespace Renaming

private def SemanticDeclsRelated (ρg : Binding.GlobalRenaming)
    (source target : List Presentation.Decl) : Prop :=
  target.map eraseDeclNl =
    (source.map (Binding.renameDecl ρg [])).map eraseDeclNl

private theorem renamedExcept_mono
    {source : Except Surface.Error α} {target : Except Surface.Error β}
    (implication : ∀ sourceValue targetValue,
      sourceRelated sourceValue targetValue →
        targetRelated sourceValue targetValue)
    (related : RenamedExcept (ExpandValuesErrorRelated ρg)
      sourceRelated source target) :
    RenamedExcept (ExpandValuesErrorRelated ρg)
      targetRelated source target := by
  cases related with
  | error errorRelated => exact RenamedExcept.error errorRelated
  | ok valueRelated => exact RenamedExcept.ok (implication _ _ valueRelated)

private theorem renamedExcept_map
    {source : Except Surface.Error α} {target : Except Surface.Error β}
    (sourceMap : α → γ) (targetMap : β → δ)
    (implication : ∀ sourceValue targetValue,
      sourceRelated sourceValue targetValue →
        targetRelated (sourceMap sourceValue) (targetMap targetValue))
    (related : RenamedExcept (ExpandValuesErrorRelated ρg)
      sourceRelated source target) :
    RenamedExcept (ExpandValuesErrorRelated ρg) targetRelated
      (source.map sourceMap) (target.map targetMap) := by
  cases related with
  | error errorRelated => exact RenamedExcept.error errorRelated
  | ok valueRelated => exact RenamedExcept.ok (implication _ _ valueRelated)

private theorem renamedExcept_cons
    {headSource : Except Surface.Error α}
    {headTarget : Except Surface.Error β}
    {tailSource tailTarget : Except Surface.Error (List Presentation.Decl)}
    (sourceDecl : α → Presentation.Decl)
    (targetDecl : β → Presentation.Decl)
    (headRelated : RenamedExcept (ExpandValuesErrorRelated ρg)
      (fun source target =>
        eraseDeclNl (targetDecl target) =
          eraseDeclNl (Binding.renameDecl ρg [] (sourceDecl source)))
      headSource headTarget)
    (tailRelated : RenamedExcept (ExpandValuesErrorRelated ρg)
      (SemanticDeclsRelated ρg) tailSource tailTarget) :
    RenamedExcept (ExpandValuesErrorRelated ρg)
      (SemanticDeclsRelated ρg)
      (do
        let head ← headSource
        let tail ← tailSource
        .ok (sourceDecl head :: tail))
      (do
        let head ← headTarget
        let tail ← tailTarget
        .ok (targetDecl head :: tail)) := by
  cases headRelated with
  | error related => exact RenamedExcept.error related
  | ok headEq =>
      cases tailRelated with
      | error related => exact RenamedExcept.error related
      | ok tailEq =>
          apply RenamedExcept.ok
          simp only [SemanticDeclsRelated, List.map_cons]
          rw [headEq, tailEq]

private theorem expandDeclNls_rename_related
    (sound : RenamingSound ρg program policy)
    (gamma : List (Presentation.LeafId × Atom))
    (gammaLeaves : ∀ entry ∈ gamma, entry.1 ∈ leafIds program) :
    ∀ (declarations : List Presentation.Decl),
      (∀ declaration ∈ declarations, declaration ∈ program.decls) →
      RenamedExcept (ExpandValuesErrorRelated ρg)
        (SemanticDeclsRelated ρg)
        (expandDeclNls program.valueBindings gamma
          (declarations.map (substDecl program.valueBindings)))
        (expandDeclNls
          (Binding.renameProgram ρg program).valueBindings
          (gamma.map fun entry => (ρg.leaf entry.1, entry.2))
          ((declarations.map (substDecl program.valueBindings)).map
            (Binding.renameDecl ρg []))) := by
  intro declarations contained
  induction declarations with
  | nil =>
      exact RenamedExcept.ok rfl
  | cons declaration rest ih =>
      have headMember : declaration ∈ program.decls :=
        contained declaration (by simp)
      have tailContained : ∀ candidate ∈ rest, candidate ∈ program.decls := by
        intro candidate member
        exact contained candidate (by simp [member])
      have tailRelated := ih tailContained
      cases declaration with
      | claim claim =>
          have textMember : claim.nl ∈ claimNls program := by
            simp only [claimNls, List.mem_filterMap]
            exact ⟨.claim claim, headMember, rfl⟩
          have headRelated := expandNl_rename_related sound gamma gammaLeaves
            claim.id claim.nl textMember
          have sequenced := renamedExcept_cons
            (ρg := ρg)
            (fun prose => Presentation.Decl.claim
              { claim with
                formal := substituteValueAtom program.valueBindings claim.formal
                nl := prose })
            (fun prose => Presentation.Decl.claim
              { claim with
                id := ρg.prop claim.id
                formal := substituteValueAtom program.valueBindings claim.formal
                nl := prose })
            (renamedExcept_mono
              (fun _ _ _ => by simp [eraseDeclNl, Binding.renameDecl])
              headRelated)
            tailRelated
          simpa [expandDeclNls, substDecl, Binding.renameDecl] using sequenced
      | comparison comparison =>
          have textMember : comparison.claim.nlRaw ∈ claimNls program := by
            simp only [claimNls, List.mem_filterMap]
            exact ⟨.comparison comparison, headMember, rfl⟩
          have headRelated := expandNl_rename_related sound gamma gammaLeaves
            comparison.claim.id comparison.claim.nlRaw textMember
          have sequenced := renamedExcept_cons
            (ρg := ρg)
            (fun prose => Presentation.Decl.comparison
              { comparison with
                conclusion := substituteValueAtom program.valueBindings
                  comparison.conclusion
                claim := { comparison.claim with nlRaw := prose } })
            (fun prose => Presentation.Decl.comparison
              { comparison with
                conclusion := substituteValueAtom program.valueBindings
                  comparison.conclusion
                measurand := ρg.measurand comparison.measurand
                dataset := ρg.dataset comparison.dataset
                recheckArg := ρg.arg comparison.recheckArg
                bridgeArg := ρg.arg comparison.bridgeArg
                result := ρg.leaf comparison.result
                baseline := ρg.leaf comparison.baseline
                binding := ρg.leaf comparison.binding
                claim :=
                  { comparison.claim with
                    id := ρg.prop comparison.claim.id
                    nlRaw := prose }
                supports := comparison.supports.map ρg.prop })
            (renamedExcept_mono
              (fun _ _ _ => by
                simp [eraseDeclNl, Binding.renameDecl,
                  Binding.renameComparison])
              headRelated)
            tailRelated
          simpa [expandDeclNls, substDecl, Binding.renameDecl,
            Binding.renameComparison] using sequenced
      | leaf leaf =>
          have sequenced := renamedExcept_cons
            (ρg := ρg)
            (headSource := .ok ()) (headTarget := .ok ())
            (fun _ : _root_.Unit => substDecl program.valueBindings (.leaf leaf))
            (fun _ : _root_.Unit => Binding.renameDecl ρg []
              (substDecl program.valueBindings (.leaf leaf)))
            (RenamedExcept.ok rfl) tailRelated
          simpa [expandDeclNls, substDecl, Binding.renameDecl,
            bind_ok_reduce] using sequenced
      | arg argument =>
          have sequenced := renamedExcept_cons
            (ρg := ρg)
            (headSource := .ok ()) (headTarget := .ok ())
            (fun _ : _root_.Unit => substDecl program.valueBindings (.arg argument))
            (fun _ : _root_.Unit => Binding.renameDecl ρg []
              (substDecl program.valueBindings (.arg argument)))
            (RenamedExcept.ok rfl) tailRelated
          simpa [expandDeclNls, substDecl, Binding.renameDecl,
            bind_ok_reduce] using sequenced
      | attack attack =>
          have sequenced := renamedExcept_cons
            (ρg := ρg)
            (headSource := .ok ()) (headTarget := .ok ())
            (fun _ : _root_.Unit => substDecl program.valueBindings (.attack attack))
            (fun _ : _root_.Unit => Binding.renameDecl ρg []
              (substDecl program.valueBindings (.attack attack)))
            (RenamedExcept.ok rfl) tailRelated
          simpa [expandDeclNls, substDecl, Binding.renameDecl,
            bind_ok_reduce] using sequenced
      | status proposition =>
          have sequenced := renamedExcept_cons
            (ρg := ρg)
            (headSource := .ok ()) (headTarget := .ok ())
            (fun _ : _root_.Unit => substDecl program.valueBindings (.status proposition))
            (fun _ : _root_.Unit => Binding.renameDecl ρg []
              (substDecl program.valueBindings (.status proposition)))
            (RenamedExcept.ok rfl) tailRelated
          simpa [expandDeclNls, substDecl, Binding.renameDecl,
            bind_ok_reduce] using sequenced
      | group group =>
          have sequenced := renamedExcept_cons
            (ρg := ρg)
            (headSource := .ok ()) (headTarget := .ok ())
            (fun _ : _root_.Unit => substDecl program.valueBindings (.group group))
            (fun _ : _root_.Unit => Binding.renameDecl ρg []
              (substDecl program.valueBindings (.group group)))
            (RenamedExcept.ok rfl) tailRelated
          simpa [expandDeclNls, substDecl, Binding.renameDecl,
            bind_ok_reduce] using sequenced

private def firstInvalidClaimIdForRenaming? (sigma : Lara.Sigma.Sigma)
    (declarations : List Presentation.Decl) : Option String :=
  declarations.findSome? fun declaration =>
    match declaration with
    | .claim claim =>
        if !Lara.Sigma.wsAtom sigma claim.formal then some claim.id.val else none
    | _ => none

private theorem firstInvalidClaimIdForRenaming?_rename
    (ρg : Binding.GlobalRenaming) (sigma : Lara.Sigma.Sigma)
    (declarations : List Presentation.Decl) :
    firstInvalidClaimIdForRenaming? sigma
        (declarations.map (Binding.renameDecl ρg [])) =
      (firstInvalidClaimIdForRenaming? sigma declarations).map
        (fun name => (ρg.prop (⟨name⟩ : Presentation.PropId)).val) := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
      unfold firstInvalidClaimIdForRenaming? at ih ⊢
      cases declaration with
      | claim claim =>
          simp only [List.map_cons, Binding.renameDecl,
            List.findSome?_cons]
          rw [ih]
          cases wellSorted : Lara.Sigma.wsAtom sigma claim.formal <;>
            simp [wellSorted]
      | leaf leaf => simpa [Binding.renameDecl] using ih
      | arg argument => simpa [Binding.renameDecl] using ih
      | attack attack => simpa [Binding.renameDecl] using ih
      | status proposition => simpa [Binding.renameDecl] using ih
      | group group => simpa [Binding.renameDecl] using ih
      | comparison comparison =>
          simpa [Binding.renameDecl, Binding.renameComparison] using ih

private theorem declaredLeaves_map_renameDecl_empty
    (ρg : Binding.GlobalRenaming) (declarations : List Presentation.Decl) :
    (declarations.map (Binding.renameDecl ρg [])).filterMap
        (fun declaration => match declaration with
          | .leaf leaf => some (leaf.id, leaf.prop)
          | _ => none) =
      (declarations.filterMap
        (fun declaration => match declaration with
          | .leaf leaf => some (leaf.id, leaf.prop)
          | _ => none)).map
        (fun entry => (ρg.leaf entry.1, entry.2)) := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;>
        simp [Binding.renameDecl, Binding.renameComparison, ih]

private theorem claimFormalErrors_eq_forRenaming
    (policy : Presentation.Policy)
    (bindings : List Presentation.ValueBinding)
    (substituted : Presentation.Program) :
    claimFormalErrors policy bindings substituted =
      if bindings.isEmpty then none
      else
        match firstInvalidClaimIdForRenaming? policy.sigma substituted.decls with
        | some claimId => some (Surface.Error.invalidValueBinding ⟨claimId⟩)
        | none => none := by
  unfold claimFormalErrors firstInvalidClaimIdForRenaming?
  rfl

private theorem claimFormalErrors_rename_result
    (sound : RenamingSound ρg program policy) :
    claimFormalErrors (Binding.renamePolicy ρg policy)
        (Binding.renameProgram ρg program).valueBindings
        ({ (Binding.renameProgram ρg program) with
          decls :=
            (Binding.renameProgram ρg program).decls.map
              (substDecl
                (Binding.renameProgram ρg program).valueBindings) }) =
      (claimFormalErrors policy program.valueBindings
        ({ program with
          decls := program.decls.map
            (substDecl program.valueBindings) })).map
        (fun error => match error with
          | .invalidValueBinding name =>
              .invalidValueBinding
                ⟨(ρg.prop (⟨name.val⟩ : Presentation.PropId)).val⟩
          | other => other) := by
  have substituted := substitutedDecls_rename sound
  have emptyEq :
      (Binding.renameProgram ρg program).valueBindings.isEmpty =
        program.valueBindings.isEmpty := by
    simp [Binding.renameProgram]
  rw [claimFormalErrors_eq_forRenaming,
    claimFormalErrors_eq_forRenaming]
  rw [emptyEq, substituted]
  simp only [Binding.renamePolicy]
  rw [firstInvalidClaimIdForRenaming?_rename]
  cases program.valueBindings.isEmpty <;>
    cases firstInvalidClaimIdForRenaming? policy.sigma
      (program.decls.map (substDecl program.valueBindings)) <;>
    rfl

private theorem valueBindingError_related
    (sound : RenamingSound ρg program policy)
    (found : valueBindingErrors policy program = some error) :
    ExpandValuesErrorRelated ρg error
      (renameValueBindingError ρg error) := by
  unfold valueBindingErrors at found
  dsimp only at found
  split at found
  · rename_i name selected
    simp only [Option.some.injEq] at found
    subst error
    exact ExpandValuesErrorRelated.duplicateBinding name
  · split at found
    · rename_i binding selected
      simp only [Option.some.injEq] at found
      subst error
      exact ExpandValuesErrorRelated.invalidBinding binding.name
    · split at found
      · rename_i binding selected
        simp only [Option.some.injEq] at found
        subst error
        exact ExpandValuesErrorRelated.invalidBinding binding.name
      · split at found
        · rename_i binding selected
          simp only [Option.some.injEq] at found
          subst error
          exact ExpandValuesErrorRelated.invalidBinding binding.name
        · simp at found

private theorem claimFormalError_related
    {ρg : Binding.GlobalRenaming} {program : Presentation.Program}
    {policy : Presentation.Policy} {error : Surface.Error}
    (found : claimFormalErrors policy program.valueBindings
      ({ program with
        decls := program.decls.map
          (substDecl program.valueBindings) }) = some error) :
    ExpandValuesErrorRelated ρg error
      (match error with
        | .invalidValueBinding name =>
            .invalidValueBinding
              ⟨(ρg.prop (⟨name.val⟩ : Presentation.PropId)).val⟩
        | other => other) := by
  rw [claimFormalErrors_eq_forRenaming] at found
  split at found
  · simp at found
  · split at found
    · rename_i claimId selected
      simp only [Option.some.injEq] at found
      subst error
      exact ExpandValuesErrorRelated.invalidClaim ⟨claimId⟩
    · simp at found

/-- Value expansion preserves exact failure provenance and every executable
field under a sound all-namespace renaming.  Expanded prose is compared only
after erasure, because interpolation may synthesize directive-shaped text. -/
theorem expandValues_rename_related
    (sound : RenamingSound ρg program policy) :
    RenamedExcept (ExpandValuesErrorRelated ρg)
      (SemanticProgramRelated ρg)
      (expandValues policy program)
      (expandValues (Binding.renamePolicy ρg policy)
        (Binding.renameProgram ρg program)) := by
  have checks := valueBindingErrors_rename sound
  cases sourceChecks : valueBindingErrors policy program with
  | some error =>
      have targetChecks :
          valueBindingErrors (Binding.renamePolicy ρg policy)
              (Binding.renameProgram ρg program) =
            some (renameValueBindingError ρg error) := by
        simpa [sourceChecks] using checks
      simp only [expandValues, sourceChecks, targetChecks]
      exact RenamedExcept.error (valueBindingError_related sound sourceChecks)
  | none =>
      have targetChecks :
          valueBindingErrors (Binding.renamePolicy ρg policy)
              (Binding.renameProgram ρg program) = none := by
        simpa [sourceChecks] using checks
      have claims := claimFormalErrors_rename_result sound
      cases sourceClaims : claimFormalErrors policy program.valueBindings
          ({ program with
            decls := program.decls.map (substDecl program.valueBindings) }) with
      | some error =>
          have targetClaims :
              claimFormalErrors (Binding.renamePolicy ρg policy)
                  (Binding.renameProgram ρg program).valueBindings
                  ({ (Binding.renameProgram ρg program) with
                    decls :=
                      (Binding.renameProgram ρg program).decls.map
                        (substDecl
                          (Binding.renameProgram ρg program).valueBindings) }) =
                some
                  (match error with
                  | .invalidValueBinding name =>
                      .invalidValueBinding
                        ⟨(ρg.prop
                          (⟨name.val⟩ : Presentation.PropId)).val⟩
                  | other => other) := by
            rw [sourceClaims] at claims
            cases error <;> simpa only [Option.map_some] using claims
          simp only [expandValues, sourceChecks, targetChecks, sourceClaims,
            targetClaims]
          exact RenamedExcept.error
            (claimFormalError_related (ρg := ρg) sourceClaims)
      | none =>
          have targetClaims :
              claimFormalErrors (Binding.renamePolicy ρg policy)
                  (Binding.renameProgram ρg program).valueBindings
                  ({ (Binding.renameProgram ρg program) with
                    decls :=
                      (Binding.renameProgram ρg program).decls.map
                        (substDecl
                          (Binding.renameProgram ρg program).valueBindings) }) =
                none := by
            rw [sourceClaims] at claims
            simpa only [Option.map_none] using claims
          let sourceSubstituted : Presentation.Program :=
            { program with
              decls := program.decls.map (substDecl program.valueBindings) }
          let targetSubstituted : Presentation.Program :=
            { (Binding.renameProgram ρg program) with
              decls :=
                (Binding.renameProgram ρg program).decls.map
                  (substDecl
                    (Binding.renameProgram ρg program).valueBindings) }
          have substituted := substitutedDecls_rename sound
          have gammaEq :
              declaredLeaves targetSubstituted =
                (declaredLeaves sourceSubstituted).map
                  (fun entry => (ρg.leaf entry.1, entry.2)) := by
            simp only [targetSubstituted, sourceSubstituted, declaredLeaves]
            rw [substituted]
            exact declaredLeaves_map_renameDecl_empty ρg _
          have nls := expandDeclNls_rename_related sound
            (declaredLeaves sourceSubstituted)
            (by
              intro entry member
              simp only [sourceSubstituted, declaredLeaves,
                List.mem_filterMap] at member
              rcases member with ⟨declaration, declarationMember, declarationEq⟩
              rcases List.mem_map.mp declarationMember with
                ⟨sourceDeclaration, sourceMember, rfl⟩
              cases sourceDeclaration <;> simp [substDecl] at declarationEq
              obtain ⟨rfl, rfl⟩ := declarationEq
              exact List.mem_filterMap.mpr ⟨_, sourceMember, rfl⟩)
            program.decls (by simp)
          rw [← gammaEq, ← substituted] at nls
          have mapped := renamedExcept_map
            (ρg := ρg)
            (targetRelated := SemanticProgramRelated ρg)
            (fun decls =>
              { sourceSubstituted with valueBindings := [], decls := decls })
            (fun decls =>
              { targetSubstituted with valueBindings := [], decls := decls })
            (by
              intro sourceDecls targetDecls related
              unfold SemanticProgramRelated eraseProgramNl
              cases program
              simpa [Binding.renameProgram, targetSubstituted,
                sourceSubstituted, SemanticDeclsRelated] using related)
            nls
          have sourceExpansion :
              expandValues policy program =
                (expandDeclNls sourceSubstituted.valueBindings
                  (declaredLeaves sourceSubstituted)
                  sourceSubstituted.decls).map
                    (fun decls =>
                      { sourceSubstituted with
                        valueBindings := [], decls := decls }) := by
            unfold expandValues
            simp only [sourceChecks]
            rw [sourceClaims]
            simp only [sourceSubstituted]
            cases expandDeclNls program.valueBindings
                (declaredLeaves
                  { program with
                    decls := program.decls.map
                      (substDecl program.valueBindings) })
                (program.decls.map
                  (substDecl program.valueBindings)) <;>
              rfl
          have targetExpansion :
              expandValues (Binding.renamePolicy ρg policy)
                  (Binding.renameProgram ρg program) =
                (expandDeclNls targetSubstituted.valueBindings
                  (declaredLeaves targetSubstituted)
                  targetSubstituted.decls).map
                    (fun decls =>
                      { targetSubstituted with
                        valueBindings := [], decls := decls }) := by
            unfold expandValues
            simp only [targetChecks]
            rw [targetClaims]
            simp only [targetSubstituted]
            cases expandDeclNls
                (Binding.renameProgram ρg program).valueBindings
                (declaredLeaves
                  { (Binding.renameProgram ρg program) with
                    decls :=
                      (Binding.renameProgram ρg program).decls.map
                        (substDecl
                          (Binding.renameProgram ρg program).valueBindings) })
                ((Binding.renameProgram ρg program).decls.map
                  (substDecl
                    (Binding.renameProgram ρg program).valueBindings)) <;>
              rfl
          rw [sourceExpansion, targetExpansion]
          exact mapped

private def eraseComparisonNl
    (comparison : Presentation.Comparison) : Presentation.Comparison :=
  { comparison with
    claim := { comparison.claim with nlRaw := "" } }

@[simp] private theorem eraseDeclNl_comparison
    (comparison : Presentation.Comparison) :
    eraseDeclNl (.comparison comparison) =
      .comparison (eraseComparisonNl comparison) :=
  rfl

private theorem declaredLeaves_eraseProgramNl
    (program : Presentation.Program) :
    declaredLeaves (eraseProgramNl program) = declaredLeaves program := by
  unfold declaredLeaves eraseProgramNl
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp [eraseDeclNl, ih]

private theorem comparisonDecls_eraseProgramNl
    (program : Presentation.Program) :
    comparisonDecls (eraseProgramNl program) =
      (comparisonDecls program).map eraseComparisonNl := by
  unfold comparisonDecls eraseProgramNl
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp [eraseDeclNl, eraseComparisonNl, ih]

private theorem comparisonExpansion?_erase
    (program : Presentation.Program) (policy : Presentation.Policy)
    (comparison : Presentation.Comparison) :
    comparisonExpansion? (eraseProgramNl program) policy
        (eraseComparisonNl comparison) =
      comparisonExpansion? program policy comparison := by
  unfold comparisonExpansion?
  rw [show leafProp? (eraseProgramNl program) = leafProp? program by
    funext leaf
    unfold leafProp?
    rw [declaredLeaves_eraseProgramNl]]
  rfl

private theorem eraseProgramNl_renameProgram
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program) :
    eraseProgramNl (Binding.renameProgram ρg program) =
      Binding.renameProgram ρg (eraseProgramNl program) := by
  unfold eraseProgramNl Binding.renameProgram
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro declaration _
  cases declaration <;>
    simp [eraseDeclNl, Binding.renameDecl,
      Binding.renameComparison, Binding.renameNl, Binding.renameNlChars]

private theorem eraseProgramNl_idempotent
    (program : Presentation.Program) :
    eraseProgramNl (eraseProgramNl program) = eraseProgramNl program := by
  unfold eraseProgramNl
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro declaration _
  cases declaration <;> simp [eraseDeclNl]

private theorem programNullaryCons_eraseProgramNl
    (program : Presentation.Program) :
    programNullaryCons (eraseProgramNl program) =
      programNullaryCons program := by
  change (program.decls.map eraseDeclNl).flatMap declNullaryCons =
    program.decls.flatMap declNullaryCons
  rw [List.flatMap_map]
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      simp only [List.flatMap_cons]
      rw [ih]
      cases declaration <;> rfl

private theorem comparisonRenamingSound_eraseProgramNl
    (sound : ComparisonRenamingSound ρg program policy) :
    ComparisonRenamingSound ρg (eraseProgramNl program) policy := by
  constructor
  · intro spelling member notValue
    apply sound.atoms spelling
    · rw [← programNullaryCons_eraseProgramNl program]
      exact member
    · simpa [eraseProgramNl, valueSpellings, programValues] using notValue
  · exact sound.patterns

private theorem generatedIdCollisionClaim?_erase
    (program : Presentation.Program) :
    generatedIdCollisionClaim? (eraseProgramNl program) =
      generatedIdCollisionClaim? program := by
  have args :
      ((eraseProgramNl program).decls.filterMap fun declaration =>
        match declaration with
        | .arg argument => some argument.id
        | _ => none) =
      (program.decls.filterMap fun declaration =>
        match declaration with
        | .arg argument => some argument.id
        | _ => none) := by
    unfold eraseProgramNl
    induction program.decls with
    | nil => rfl
    | cons declaration rest ih =>
        cases declaration <;> simp [eraseDeclNl, ih]
  have claims :
      ((eraseProgramNl program).decls.filterMap fun declaration =>
        match declaration with
        | .claim claim => some claim.id
        | _ => none) =
      (program.decls.filterMap fun declaration =>
        match declaration with
        | .claim claim => some claim.id
        | _ => none) := by
    unfold eraseProgramNl
    induction program.decls with
    | nil => rfl
    | cons declaration rest ih =>
        cases declaration <;> simp [eraseDeclNl, ih]
  unfold generatedIdCollisionClaim?
  rw [comparisonDecls_eraseProgramNl]
  generalize hleftArgs :
    ((eraseProgramNl program).decls.filterMap fun declaration =>
      match declaration with
      | .arg argument => some argument.id
      | _ => none) = leftArgs
  generalize hrightArgs :
    (program.decls.filterMap fun declaration =>
      match declaration with
      | .arg argument => some argument.id
      | _ => none) = rightArgs
  have argsEq : leftArgs = rightArgs := by
    rw [← hleftArgs, ← hrightArgs]
    exact args
  subst leftArgs
  generalize hleftClaims :
    ((eraseProgramNl program).decls.filterMap fun declaration =>
      match declaration with
      | .claim claim => some claim.id
      | _ => none) = leftClaims
  generalize hrightClaims :
    (program.decls.filterMap fun declaration =>
      match declaration with
      | .claim claim => some claim.id
      | _ => none) = rightClaims
  have claimsEq : leftClaims = rightClaims := by
    rw [← hleftClaims, ← hrightClaims]
    exact claims
  subst leftClaims
  generalize comparisonDecls program = comparisons
  generalize hseenArgs : ([] : List Presentation.ArgId) = seenArgs
  generalize hseenClaims : ([] : List Presentation.PropId) = seenClaims
  clear hseenArgs hseenClaims
  induction comparisons generalizing seenArgs seenClaims with
  | nil => rfl
  | cons comparison rest ih =>
      change
        (if comparison.recheckArg = comparison.bridgeArg ||
              ((eraseProgramNl program).decls.filterMap fun declaration =>
                match declaration with
                | .arg argument => some argument.id
                | _ => none).contains comparison.recheckArg ||
              ((eraseProgramNl program).decls.filterMap fun declaration =>
                match declaration with
                | .arg argument => some argument.id
                | _ => none).contains comparison.bridgeArg ||
              seenArgs.contains comparison.recheckArg ||
              seenArgs.contains comparison.bridgeArg ||
              ((eraseProgramNl program).decls.filterMap fun declaration =>
                match declaration with
                | .claim claim => some claim.id
                | _ => none).contains comparison.claim.id ||
              seenClaims.contains comparison.claim.id then
            some comparison.claim.id
          else _) =
          (if comparison.recheckArg = comparison.bridgeArg ||
              (program.decls.filterMap fun declaration =>
                match declaration with
                | .arg argument => some argument.id
                | _ => none).contains comparison.recheckArg ||
              (program.decls.filterMap fun declaration =>
                match declaration with
                | .arg argument => some argument.id
                | _ => none).contains comparison.bridgeArg ||
              seenArgs.contains comparison.recheckArg ||
              seenArgs.contains comparison.bridgeArg ||
              (program.decls.filterMap fun declaration =>
                match declaration with
                | .claim claim => some claim.id
                | _ => none).contains comparison.claim.id ||
              seenClaims.contains comparison.claim.id then
            some comparison.claim.id
          else _)
      rw [args, claims]
      split
      · rfl
      · exact ih _ _

private theorem duplicateComparisonClaim?_erase
    (program : Presentation.Program) :
    duplicateComparisonClaim? (eraseProgramNl program) =
      duplicateComparisonClaim? program := by
  unfold duplicateComparisonClaim?
  rw [comparisonDecls_eraseProgramNl]
  generalize comparisonDecls program = comparisons
  generalize hseen : [] = seen
  clear hseen
  induction comparisons generalizing seen with
  | nil => rfl
  | cons comparison rest ih =>
      change
        (if comparisonKey comparison ∈ seen then
            some comparison.claim.id
          else _) =
          (if comparisonKey comparison ∈ seen then
            some comparison.claim.id
          else _)
      split
      · rfl
      · exact ih _

private theorem generatedDecls_eraseComparisonNl
    (data : ComparisonExpansionData)
    (comparison : Presentation.Comparison) :
    generatedDecls data (eraseComparisonNl comparison) =
      (generatedDecls data comparison).map eraseDeclNl := by
  exact generatedDecls_eraseNl data comparison

private theorem generatedArgs_eraseComparisonNl
    (comparison : Presentation.Comparison) :
    generatedArgs (eraseComparisonNl comparison) =
      generatedArgs comparison := by
  rfl

private theorem expandDecls_erase
    (policy : Presentation.Policy) (program : Presentation.Program) :
    ∀ declarations : List Presentation.Decl,
      expandDecls policy (eraseProgramNl program)
          (declarations.map eraseDeclNl) =
        (expandDecls policy program declarations).map fun result =>
          (result.1.map eraseDeclNl, result.2)
  | [] => rfl
  | declaration :: rest => by
      cases declaration with
      | comparison comparison =>
          simp only [List.map_cons, eraseDeclNl_comparison, expandDecls]
          rw [comparisonExpansion?_erase]
          cases expansion : comparisonExpansion? program policy comparison with
          | none => rfl
          | some data =>
              rw [expandDecls_erase policy program rest]
              cases tail : expandDecls policy program rest with
              | error error => rfl
              | ok result =>
                  rcases result with ⟨declarations, generated⟩
                  simp [Except.map, generatedDecls_eraseComparisonNl,
                    generatedArgs_eraseComparisonNl, List.map_append]
      | leaf leaf =>
          simp only [List.map_cons, eraseDeclNl, expandDecls]
          rw [expandDecls_erase policy program rest]
          cases expandDecls policy program rest <;> rfl
      | claim claim =>
          simp only [List.map_cons, eraseDeclNl, expandDecls]
          rw [expandDecls_erase policy program rest]
          cases expandDecls policy program rest <;> rfl
      | arg argument =>
          simp only [List.map_cons, eraseDeclNl, expandDecls]
          rw [expandDecls_erase policy program rest]
          cases expandDecls policy program rest <;> rfl
      | attack attack =>
          simp only [List.map_cons, eraseDeclNl, expandDecls]
          rw [expandDecls_erase policy program rest]
          cases expandDecls policy program rest <;> rfl
      | status proposition =>
          simp only [List.map_cons, eraseDeclNl, expandDecls]
          rw [expandDecls_erase policy program rest]
          cases expandDecls policy program rest <;> rfl
      | group group =>
          simp only [List.map_cons, eraseDeclNl, expandDecls]
          rw [expandDecls_erase policy program rest]
          cases expandDecls policy program rest <;> rfl

private theorem expandComparisons_erase
    (policy : Presentation.Policy) (program : Presentation.Program) :
    expandComparisons policy (eraseProgramNl program) =
      (expandComparisons policy program).map fun result =>
        (eraseProgramNl result.1, result.2) := by
  unfold expandComparisons
  rw [generatedIdCollisionClaim?_erase,
    duplicateComparisonClaim?_erase]
  cases collision : generatedIdCollisionClaim? program with
  | some claim => rfl
  | none =>
      cases duplicate : duplicateComparisonClaim? program with
      | some claim => rfl
      | none =>
          rw [show (eraseProgramNl program).decls =
            program.decls.map eraseDeclNl by rfl]
          rw [expandDecls_erase policy program program.decls]
          cases expanded : expandDecls policy program program.decls with
          | error error => rfl
          | ok result =>
              rcases result with ⟨declarations, generated⟩
              rfl

private def DeclExpansionResultsRelated
    (ρg : Binding.GlobalRenaming) (values : List Presentation.ValueName)
    (source target : List Presentation.Decl × List GeneratedArg) : Prop :=
  target.1 = source.1.map (Binding.renameDecl ρg values) ∧
    target.2 = source.2.map (renameGeneratedArg ρg)

private theorem expandDecls_rename_related
    (sound : ComparisonRenamingSound ρg program policy) :
    ∀ (declarations : List Presentation.Decl),
      (∀ declaration ∈ declarations, declaration ∈ program.decls) →
      RenamedExcept (ExpandComparisonsErrorRelated ρg)
        (DeclExpansionResultsRelated ρg (programValues program))
        (expandDecls policy program declarations)
        (expandDecls (Binding.renamePolicy ρg policy)
          (Binding.renameProgram ρg program)
          (declarations.map
            (Binding.renameDecl ρg (programValues program))))
  | [], _ => RenamedExcept.ok ⟨rfl, rfl⟩
  | declaration :: rest, contained => by
      have headMember : declaration ∈ program.decls :=
        contained declaration (by simp)
      have tailContained : ∀ candidate ∈ rest,
          candidate ∈ program.decls := by
        intro candidate member
        exact contained candidate (by simp [member])
      have tailRelated := expandDecls_rename_related sound rest tailContained
      generalize sourceTailEq :
        expandDecls policy program rest = sourceTail at tailRelated ⊢
      generalize targetTailEq :
        expandDecls (Binding.renamePolicy ρg policy)
          (Binding.renameProgram ρg program)
          (rest.map (Binding.renameDecl ρg (programValues program))) =
            targetTail at tailRelated ⊢
      cases declaration with
      | comparison comparison =>
          have expansionRenamed := comparisonExpansion?_rename sound comparison
            headMember
          cases sourceExpansion :
              comparisonExpansion? program policy comparison with
          | none =>
              have targetExpansion :
                  comparisonExpansion?
                      (Binding.renameProgram ρg program)
                      (Binding.renamePolicy ρg policy)
                      (Binding.renameComparison ρg
                        (programValues program) comparison) = none := by
                simpa [sourceExpansion] using expansionRenamed
              simp only [expandDecls, List.map_cons, Binding.renameDecl]
              rw [sourceExpansion, targetExpansion]
              simpa [Binding.renameComparison] using
                (RenamedExcept.error
                  (ExpandComparisonsErrorRelated.invalidComparison
                    (ρg := ρg) comparison.claim.id) :
                  RenamedExcept (ExpandComparisonsErrorRelated ρg)
                    (DeclExpansionResultsRelated ρg (programValues program))
                    (.error (.invalidComparison comparison.claim.id))
                    (.error (.invalidComparison
                      (ρg.prop comparison.claim.id))))
          | some data =>
              have targetExpansion :
                  comparisonExpansion?
                      (Binding.renameProgram ρg program)
                      (Binding.renamePolicy ρg policy)
                      (Binding.renameComparison ρg
                        (programValues program) comparison) =
                    some (renameComparisonExpansionData ρg
                      (programValues program) data) := by
                simpa [sourceExpansion] using expansionRenamed
              simp only [expandDecls, List.map_cons, Binding.renameDecl]
              rw [sourceExpansion, targetExpansion,
                sourceTailEq, targetTailEq]
              cases tailRelated with
              | error errorRelated => exact RenamedExcept.error errorRelated
              | ok resultRelated =>
                  apply RenamedExcept.ok
                  rcases resultRelated with ⟨declarationsEq, generatedEq⟩
                  constructor
                  · rw [generatedDecls_rename, declarationsEq,
                      List.map_append]
                  · rw [generatedArgs_rename, generatedEq,
                      List.map_append]
                    rfl
      | leaf leaf =>
          simp only [expandDecls, List.map_cons, Binding.renameDecl]
          rw [sourceTailEq, targetTailEq]
          cases tailRelated with
          | error errorRelated => exact RenamedExcept.error errorRelated
          | ok resultRelated =>
              exact RenamedExcept.ok
                ⟨by simp [Binding.renameDecl, resultRelated.1],
                  resultRelated.2⟩
      | claim claim =>
          simp only [expandDecls, List.map_cons, Binding.renameDecl]
          rw [sourceTailEq, targetTailEq]
          cases tailRelated with
          | error errorRelated => exact RenamedExcept.error errorRelated
          | ok resultRelated =>
              exact RenamedExcept.ok
                ⟨by simp [Binding.renameDecl, resultRelated.1],
                  resultRelated.2⟩
      | arg argument =>
          simp only [expandDecls, List.map_cons, Binding.renameDecl]
          rw [sourceTailEq, targetTailEq]
          cases tailRelated with
          | error errorRelated => exact RenamedExcept.error errorRelated
          | ok resultRelated =>
              exact RenamedExcept.ok
                ⟨by simp [Binding.renameDecl, resultRelated.1],
                  resultRelated.2⟩
      | attack attack =>
          simp only [expandDecls, List.map_cons, Binding.renameDecl]
          rw [sourceTailEq, targetTailEq]
          cases tailRelated with
          | error errorRelated => exact RenamedExcept.error errorRelated
          | ok resultRelated =>
              exact RenamedExcept.ok
                ⟨by simp [Binding.renameDecl, resultRelated.1],
                  resultRelated.2⟩
      | status proposition =>
          simp only [expandDecls, List.map_cons, Binding.renameDecl]
          rw [sourceTailEq, targetTailEq]
          cases tailRelated with
          | error errorRelated => exact RenamedExcept.error errorRelated
          | ok resultRelated =>
              exact RenamedExcept.ok
                ⟨by simp [Binding.renameDecl, resultRelated.1],
                  resultRelated.2⟩
      | group group =>
          simp only [expandDecls, List.map_cons, Binding.renameDecl]
          rw [sourceTailEq, targetTailEq]
          cases tailRelated with
          | error errorRelated => exact RenamedExcept.error errorRelated
          | ok resultRelated =>
              exact RenamedExcept.ok
                ⟨by simp [Binding.renameDecl, resultRelated.1],
                  resultRelated.2⟩

private theorem expandComparisons_exact_rename_related
    (sound : ComparisonRenamingSound ρg program policy) :
    RenamedExcept (ExpandComparisonsErrorRelated ρg)
      (GeneratedResultsRelated ρg)
      (expandComparisons policy program)
      (expandComparisons (Binding.renamePolicy ρg policy)
        (Binding.renameProgram ρg program)) := by
  have collisions := generatedIdCollisionClaim?_rename ρg program
  cases sourceCollision : generatedIdCollisionClaim? program with
  | some claim =>
      have targetCollision :
          generatedIdCollisionClaim? (Binding.renameProgram ρg program) =
            some (ρg.prop claim) := by
        simpa [sourceCollision] using collisions
      simp only [expandComparisons, sourceCollision, targetCollision]
      exact RenamedExcept.error
        (ExpandComparisonsErrorRelated.invalidComparison claim)
  | none =>
      have targetCollision :
          generatedIdCollisionClaim? (Binding.renameProgram ρg program) =
            none := by
        simpa [sourceCollision] using collisions
      have duplicates := duplicateComparisonClaim?_rename ρg program
      cases sourceDuplicate : duplicateComparisonClaim? program with
      | some claim =>
          have targetDuplicate :
              duplicateComparisonClaim? (Binding.renameProgram ρg program) =
                some (ρg.prop claim) := by
            simpa [sourceDuplicate] using duplicates
          simp only [expandComparisons, sourceCollision, targetCollision,
            sourceDuplicate, targetDuplicate]
          exact RenamedExcept.error
            (ExpandComparisonsErrorRelated.invalidComparison claim)
      | none =>
          have targetDuplicate :
              duplicateComparisonClaim? (Binding.renameProgram ρg program) =
                none := by
            simpa [sourceDuplicate] using duplicates
          have declarations := expandDecls_rename_related sound program.decls
            (by simp)
          generalize sourceDeclarationsEq :
            expandDecls policy program program.decls =
              sourceDeclarations at declarations
          generalize targetDeclarationsEq :
            expandDecls (Binding.renamePolicy ρg policy)
              (Binding.renameProgram ρg program)
              (program.decls.map
                (Binding.renameDecl ρg (programValues program))) =
              targetDeclarations at declarations
          simp only [expandComparisons, sourceCollision, targetCollision,
            sourceDuplicate, targetDuplicate]
          rw [sourceDeclarationsEq,
            show (Binding.renameProgram ρg program).decls =
              program.decls.map
                (Binding.renameDecl ρg (programValues program)) by rfl,
            targetDeclarationsEq]
          cases declarations with
          | error errorRelated => exact RenamedExcept.error errorRelated
          | ok resultRelated =>
              apply RenamedExcept.ok
              rcases resultRelated with ⟨declarationsEq, generatedEq⟩
              constructor
              · unfold SemanticProgramRelated
                congr 1
                cases program
                simpa [Binding.renameProgram, programValues] using
                  declarationsEq
              · exact generatedEq

private theorem generatedResultsRelated_of_erased
    (related : GeneratedResultsRelated ρg
      (eraseProgramNl source.1, source.2)
      (eraseProgramNl target.1, target.2)) :
    GeneratedResultsRelated ρg source target := by
  rcases related with ⟨programRelated, generatedRelated⟩
  constructor
  · unfold SemanticProgramRelated at programRelated ⊢
    rw [eraseProgramNl_idempotent] at programRelated
    rw [eraseProgramNl_renameProgram,
      eraseProgramNl_idempotent] at programRelated
    calc
      eraseProgramNl target.1 =
          Binding.renameProgram ρg (eraseProgramNl source.1) :=
        programRelated
      _ = eraseProgramNl (Binding.renameProgram ρg source.1) :=
        (eraseProgramNl_renameProgram ρg source.1).symm
  · exact generatedRelated

/-- Comparison expansion consumes the executable fields of value expansion's
prose-erased relation, preserving exact comparison errors and generated
provenance without asserting false literal equality of interpolated prose. -/
theorem expandComparisons_semantic_related
    (sound : ComparisonRenamingSound ρg source policy)
    (related : SemanticProgramRelated ρg source target) :
    RenamedExcept (ExpandComparisonsErrorRelated ρg)
      (GeneratedResultsRelated ρg)
      (expandComparisons policy source)
      (expandComparisons (Binding.renamePolicy ρg policy) target) := by
  have erasedSound := comparisonRenamingSound_eraseProgramNl sound
  have exact := expandComparisons_exact_rename_related erasedSound
  have erasedPrograms :
      eraseProgramNl target =
        Binding.renameProgram ρg (eraseProgramNl source) := by
    calc
      eraseProgramNl target =
          eraseProgramNl (Binding.renameProgram ρg source) := related
      _ = Binding.renameProgram ρg (eraseProgramNl source) :=
        eraseProgramNl_renameProgram ρg source
  rw [← erasedPrograms] at exact
  rw [expandComparisons_erase policy source,
    expandComparisons_erase (Binding.renamePolicy ρg policy) target] at exact
  cases sourceResult : expandComparisons policy source with
  | error sourceError =>
      cases targetResult :
          expandComparisons (Binding.renamePolicy ρg policy) target with
      | error targetError =>
          simp [sourceResult, targetResult] at exact
          cases exact with
          | error errorRelated => exact RenamedExcept.error errorRelated
      | ok targetValue =>
          simp [sourceResult, targetResult] at exact
          cases exact
  | ok sourceValue =>
      cases targetResult :
          expandComparisons (Binding.renamePolicy ρg policy) target with
      | error targetError =>
          simp [sourceResult, targetResult] at exact
          cases exact
      | ok targetValue =>
          simp [sourceResult, targetResult] at exact
          cases exact with
          | ok resultRelated =>
              exact RenamedExcept.ok
                (generatedResultsRelated_of_erased resultRelated)

private theorem valueBindingErrors_none_of_expandValues_ok
    (expanded : expandValues policy program = .ok target) :
    valueBindingErrors policy program = none := by
  unfold expandValues at expanded
  cases checks : valueBindingErrors policy program with
  | none => rfl
  | some error => simp [checks] at expanded

private theorem valueBinding_sorted_of_errors_none
    (checks : valueBindingErrors policy program = none)
    (binding : Presentation.ValueBinding)
    (member : binding ∈ program.valueBindings) :
    ∃ sort, Lara.Sigma.sortOf policy.sigma binding.term = some sort := by
  have sortedFind :
      program.valueBindings.find? (fun candidate =>
        (Lara.Sigma.sortOf policy.sigma candidate.term).isNone) = none := by
    unfold valueBindingErrors at checks
    dsimp only at checks
    split at checks <;> try contradiction
    split at checks <;> try contradiction
    split at checks <;> try contradiction
    cases sorted : program.valueBindings.find? (fun candidate =>
        (Lara.Sigma.sortOf policy.sigma candidate.term).isNone) with
    | none => rfl
    | some binding => simp [sorted] at checks
  have selectedFalse := (List.find?_eq_none.mp sortedFind) binding member
  cases found : Lara.Sigma.sortOf policy.sigma binding.term with
  | none => simp [found] at selectedFalse
  | some sort => exact ⟨sort, rfl⟩

private theorem lookupValue_some_member
    (found : lookupValue bindings name = some term) :
    ∃ binding ∈ bindings, binding.name = name ∧ binding.term = term := by
  induction bindings with
  | nil => simp [lookupValue] at found
  | cons binding rest ih =>
      simp only [lookupValue, List.findSome?_cons] at found
      by_cases equal : binding.name = name
      · rw [if_pos equal] at found
        simp only [Option.some.injEq] at found
        exact ⟨binding, by simp, equal, found⟩
      · rw [if_neg equal] at found
        obtain ⟨candidate, member, nameEq, termEq⟩ := ih found
        exact ⟨candidate, by simp [member], nameEq, termEq⟩

private theorem lookupValue_none_not_mem
    (found : lookupValue bindings name = none) :
    name ∉ bindings.map (fun binding => binding.name) := by
  induction bindings with
  | nil => simp
  | cons binding rest ih =>
      simp only [lookupValue, List.findSome?_cons] at found
      by_cases equal : binding.name = name
      · rw [if_pos equal] at found
        contradiction
      · rw [if_neg equal] at found
        simp only [List.map_cons, List.mem_cons, not_or]
        exact ⟨fun reversed => equal reversed.symm, ih found⟩

mutual
  private theorem substituteValueTerm_nullaries_fixed
      (bindingFixed : ∀ binding ∈ bindings, ∀ spelling,
        spelling ∈ termNullaryCons binding.term →
          Binding.renameText ρg spelling = spelling) :
      ∀ (term : Term),
        (∀ spelling, spelling ∈ termNullaryCons term →
          spelling ∉ (bindings.map (fun binding => binding.name)).map
            (fun name => name.val) →
          Binding.renameText ρg spelling = spelling) →
        ∀ spelling, spelling ∈
            termNullaryCons (substituteValueTerm bindings term) →
          Binding.renameText ρg spelling = spelling
    | .num _, _, spelling, member => by
        change spelling ∈ [] at member
        contradiction
    | .str _, _, spelling, member => by
        change spelling ∈ [] at member
        contradiction
    | .con name .nil, fixed, spelling, member => by
        change spelling ∈ termNullaryCons
          (match lookupValue bindings ⟨name⟩ with
          | some replacement => replacement
          | none => .con name .nil) at member
        cases found : lookupValue bindings ⟨name⟩ with
        | some replacement =>
            simp only [found] at member
            obtain ⟨binding, bindingMember, _, rfl⟩ :=
              lookupValue_some_member found
            exact bindingFixed binding bindingMember spelling member
        | none =>
            simp only [found, termNullaryCons, List.mem_singleton] at member
            subst spelling
            apply fixed name (by simp [termNullaryCons])
            intro spellingMember
            apply lookupValue_none_not_mem found
            rcases List.mem_map.mp spellingMember with
              ⟨valueName, valueMember, valueEq⟩
            rcases List.mem_map.mp valueMember with
              ⟨binding, bindingMember, bindingNameEq⟩
            apply List.mem_map.mpr
            refine ⟨binding, bindingMember, ?_⟩
            rw [bindingNameEq]
            cases valueName with
            | mk raw =>
                simp only at valueEq
                subst raw
                rfl
    | .con name (.cons first rest), fixed, spelling, member =>
        substituteValueTerms_nullaries_fixed bindingFixed (.cons first rest)
          (by
            intro candidate candidateMember notValue
            exact fixed candidate candidateMember notValue)
          spelling member

  private theorem substituteValueTerms_nullaries_fixed
      (bindingFixed : ∀ binding ∈ bindings, ∀ spelling,
        spelling ∈ termNullaryCons binding.term →
          Binding.renameText ρg spelling = spelling) :
      ∀ (terms : Terms),
        (∀ spelling, spelling ∈ termsNullaryCons terms →
          spelling ∉ (bindings.map (fun binding => binding.name)).map
            (fun name => name.val) →
          Binding.renameText ρg spelling = spelling) →
        ∀ spelling, spelling ∈
            termsNullaryCons (substituteValueTerms bindings terms) →
          Binding.renameText ρg spelling = spelling
    | .nil, _, spelling, member => by
        change spelling ∈ [] at member
        contradiction
    | .cons first rest, fixed, spelling, member => by
        simp only [substituteValueTerms, termsNullaryCons,
          List.mem_append] at member
        rcases member with headMember | tailMember
        · exact substituteValueTerm_nullaries_fixed bindingFixed first
            (by
              intro candidate candidateMember notValue
              exact fixed candidate (List.mem_append_left _ candidateMember)
                notValue)
            spelling headMember
        · exact substituteValueTerms_nullaries_fixed bindingFixed rest
            (by
              intro candidate candidateMember notValue
              exact fixed candidate (List.mem_append_right _ candidateMember)
                notValue)
            spelling tailMember
end

private theorem substituteValueAtom_nullaries_fixed
    (bindingFixed : ∀ binding ∈ bindings, ∀ spelling,
      spelling ∈ termNullaryCons binding.term →
        Binding.renameText ρg spelling = spelling)
    (atom : Atom)
    (fixed : ∀ spelling, spelling ∈ atomNullaryCons atom →
      spelling ∉ (bindings.map (fun binding => binding.name)).map
        (fun name => name.val) →
      Binding.renameText ρg spelling = spelling) :
    ∀ spelling, spelling ∈
        atomNullaryCons (substituteValueAtom bindings atom) →
      Binding.renameText ρg spelling = spelling := by
  cases atom with
  | atom predicate terms =>
      intro spelling member
      apply substituteValueTerms_nullaries_fixed bindingFixed terms
      · intro candidate candidateMember notValue
        exact fixed candidate candidateMember notValue
      · exact member

private theorem substituteSubst_nullaries_fixed
    (bindingFixed : ∀ binding ∈ bindings, ∀ spelling,
      spelling ∈ termNullaryCons binding.term →
        Binding.renameText ρg spelling = spelling) :
    ∀ (substitution : List (Presentation.Param × Term)),
      (∀ spelling,
        spelling ∈ substitution.flatMap
          (fun entry => termNullaryCons entry.2) →
        spelling ∉ (bindings.map (fun binding => binding.name)).map
          (fun name => name.val) →
        Binding.renameText ρg spelling = spelling) →
      ∀ spelling,
        spelling ∈ (substitution.map fun entry =>
          (entry.1, substituteValueTerm bindings entry.2)).flatMap
            (fun entry => termNullaryCons entry.2) →
        Binding.renameText ρg spelling = spelling
  | [], _, spelling, member => by
      change spelling ∈ [] at member
      contradiction
  | entry :: rest, fixed, spelling, member => by
      rcases entry with ⟨parameter, term⟩
      simp only [List.map_cons, List.flatMap_cons, List.mem_append] at member
      rcases member with headMember | tailMember
      · exact substituteValueTerm_nullaries_fixed bindingFixed term
          (by
            intro candidate candidateMember notValue
            exact fixed candidate (List.mem_append_left _ candidateMember)
              notValue)
          spelling headMember
      · exact substituteSubst_nullaries_fixed bindingFixed rest
          (by
            intro candidate candidateMember notValue
            exact fixed candidate (List.mem_append_right _ candidateMember)
              notValue)
          spelling tailMember

mutual
  private theorem substSupportTerm_nullaries_fixed
      (bindingFixed : ∀ binding ∈ bindings, ∀ spelling,
        spelling ∈ termNullaryCons binding.term →
          Binding.renameText ρg spelling = spelling) :
      ∀ (term : Presentation.SupportTerm),
        SupportTermFixed ρg
          (bindings.map (fun binding => binding.name)) term →
        ∀ spelling, spelling ∈
            supportTermNullaryCons (substSupportTerm bindings term) →
          Binding.renameText ρg spelling = spelling
    | .leaf _, _, spelling, member => by
        change spelling ∈ [] at member
        contradiction
    | .rule rule substitution premises discharges holes assurance,
        fixed, spelling, member => by
        simp only [substSupportTerm, supportTermNullaryCons,
          List.mem_append] at member
        rcases member with (substitutionMember | premisesMember) |
          dischargesMember
        · exact substituteSubst_nullaries_fixed bindingFixed substitution
            (by
              intro candidate candidateMember notValue
              exact fixed candidate
                (List.mem_append_left _
                  (List.mem_append_left _ candidateMember)) notValue)
            spelling substitutionMember
        · exact substSupportTerms_nullaries_fixed bindingFixed premises
            (by
              intro candidate candidateMember notValue
              exact fixed candidate
                (List.mem_append_left _
                  (List.mem_append_right _ candidateMember)) notValue)
            spelling premisesMember
        · exact substSupportDischarges_nullaries_fixed bindingFixed discharges
            (by
              intro candidate candidateMember notValue
              exact fixed candidate
                (List.mem_append_right _ candidateMember) notValue)
            spelling dischargesMember

  private theorem substSupportTerms_nullaries_fixed
      (bindingFixed : ∀ binding ∈ bindings, ∀ spelling,
        spelling ∈ termNullaryCons binding.term →
          Binding.renameText ρg spelling = spelling) :
      ∀ (terms : Presentation.SupportTerms),
        (∀ spelling, spelling ∈ supportTermsNullaryCons terms →
          spelling ∉ (bindings.map (fun binding => binding.name)).map
            (fun name => name.val) →
          Binding.renameText ρg spelling = spelling) →
        ∀ spelling, spelling ∈
            supportTermsNullaryCons (substSupportTerms bindings terms) →
          Binding.renameText ρg spelling = spelling
    | .nil, _, spelling, member => by
        change spelling ∈ [] at member
        contradiction
    | .cons first rest, fixed, spelling, member => by
        simp only [substSupportTerms, supportTermsNullaryCons,
          List.mem_append] at member
        rcases member with headMember | tailMember
        · exact substSupportTerm_nullaries_fixed bindingFixed first
            (by
              intro candidate candidateMember notValue
              exact fixed candidate (List.mem_append_left _ candidateMember)
                notValue)
            spelling headMember
        · exact substSupportTerms_nullaries_fixed bindingFixed rest
            (by
              intro candidate candidateMember notValue
              exact fixed candidate (List.mem_append_right _ candidateMember)
                notValue)
            spelling tailMember

  private theorem substSupportDischarges_nullaries_fixed
      (bindingFixed : ∀ binding ∈ bindings, ∀ spelling,
        spelling ∈ termNullaryCons binding.term →
          Binding.renameText ρg spelling = spelling) :
      ∀ (discharges : Presentation.Discharges),
        (∀ spelling, spelling ∈ supportDischargesNullaryCons discharges →
          spelling ∉ (bindings.map (fun binding => binding.name)).map
            (fun name => name.val) →
          Binding.renameText ρg spelling = spelling) →
        ∀ spelling, spelling ∈ supportDischargesNullaryCons
            (substSupportDischarges bindings discharges) →
          Binding.renameText ρg spelling = spelling
    | .nil, _, spelling, member => by
        change spelling ∈ [] at member
        contradiction
    | .cons question first rest, fixed, spelling, member => by
        simp only [substSupportDischarges, supportDischargesNullaryCons,
          List.mem_append] at member
        rcases member with headMember | tailMember
        · exact substSupportTerm_nullaries_fixed bindingFixed first
            (by
              intro candidate candidateMember notValue
              exact fixed candidate (List.mem_append_left _ candidateMember)
                notValue)
            spelling headMember
        · exact substSupportDischarges_nullaries_fixed bindingFixed rest
            (by
              intro candidate candidateMember notValue
              exact fixed candidate (List.mem_append_right _ candidateMember)
                notValue)
            spelling tailMember
end

private def DeclsNullariesFixed (ρg : Binding.GlobalRenaming)
    (declarations : List Presentation.Decl) : Prop :=
  ∀ declaration ∈ declarations, ∀ spelling,
    spelling ∈ declNullaryCons declaration →
      Binding.renameText ρg spelling = spelling

private theorem declsExpand_nullaries_fixed
    (sound : RenamingSound ρg program policy)
    (bindingFixed : ∀ binding ∈ program.valueBindings, ∀ spelling,
      spelling ∈ termNullaryCons binding.term →
        Binding.renameText ρg spelling = spelling)
    (expanded : DeclsExpand program.valueBindings gamma source target)
    (contained : ∀ declaration ∈ source,
      declaration ∈ program.decls) :
    DeclsNullariesFixed ρg target := by
  induction expanded with
  | nil =>
      intro declaration member
      simp at member
  | @leaf leaf ds ts tail ih =>
      intro declaration member spelling spellingMember
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · change spelling ∈ atomNullaryCons
          (substituteValueAtom program.valueBindings _ ) at spellingMember
        apply substituteValueAtom_nullaries_fixed bindingFixed _
        · intro candidate candidateMember notValue
          apply sound.atoms candidate
          · apply List.mem_flatMap.mpr
            exact ⟨.leaf leaf, contained (.leaf leaf) (by simp),
              by simpa [declNullaryCons] using candidateMember⟩
          · simpa [programValues, valueSpellings] using notValue
        · exact spellingMember
      · apply ih
        · intro candidate candidateMember
          exact contained candidate (by simp [candidateMember])
        · exact member
        · exact spellingMember
  | @claim claim nl' ds ts prose tail ih =>
      intro declaration member spelling spellingMember
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · change spelling ∈ atomNullaryCons
          (substituteValueAtom program.valueBindings _) at spellingMember
        apply substituteValueAtom_nullaries_fixed bindingFixed _
        · intro candidate candidateMember notValue
          apply sound.atoms candidate
          · apply List.mem_flatMap.mpr
            exact ⟨.claim claim, contained (.claim claim) (by simp),
              by simpa [declNullaryCons] using candidateMember⟩
          · simpa [programValues, valueSpellings] using notValue
        · exact spellingMember
      · apply ih
        · intro candidate candidateMember
          exact contained candidate (by simp [candidateMember])
        · exact member
        · exact spellingMember
  | @arg argument ds ts tail ih =>
      intro declaration member spelling spellingMember
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · have argumentMember : Presentation.Decl.arg argument ∈ program.decls :=
          contained _ (by simp)
        cases instantiation : argument.instantiation with
        | explicitTheta term =>
            rw [instantiation] at spellingMember
            change spelling ∈ supportTermNullaryCons
              (substSupportTerm program.valueBindings term) at spellingMember
            have fixed := supportTermFixed_of_explicitArg sound argument term
              argumentMember instantiation
            exact substSupportTerm_nullaries_fixed bindingFixed term fixed
              spelling spellingMember
        | inferTheta rule references discharges obligations assurance =>
            rw [instantiation] at spellingMember
            change spelling ∈ assuranceBinderSpellings assurance at spellingMember
            apply sound.certBinders spelling
            apply (argumentPayloadsFromProgram argumentMember).1
            simpa [argBinderSpellings, instantiation] using spellingMember
      · apply ih
        · intro candidate candidateMember
          exact contained candidate (by simp [candidateMember])
        · exact member
        · exact spellingMember
  | @comparison comparison nl' ds ts prose tail ih =>
      intro declaration member spelling spellingMember
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · change spelling ∈ atomNullaryCons
          (substituteValueAtom program.valueBindings _) at spellingMember
        apply substituteValueAtom_nullaries_fixed bindingFixed _
        · intro candidate candidateMember notValue
          apply sound.atoms candidate
          · apply List.mem_flatMap.mpr
            exact ⟨.comparison comparison,
              contained (.comparison comparison) (by simp),
              by simpa [declNullaryCons] using candidateMember⟩
          · simpa [programValues, valueSpellings] using notValue
        · exact spellingMember
      · apply ih
        · intro candidate candidateMember
          exact contained candidate (by simp [candidateMember])
        · exact member
        · exact spellingMember
  | @attack attack ds ts tail ih =>
      intro declaration member spelling spellingMember
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · change spelling ∈ [] at spellingMember
        contradiction
      · apply ih
        · intro candidate candidateMember
          exact contained candidate (by simp [candidateMember])
        · exact member
        · exact spellingMember
  | @status proposition ds ts tail ih =>
      intro declaration member spelling spellingMember
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · change spelling ∈ [] at spellingMember
        contradiction
      · apply ih
        · intro candidate candidateMember
          exact contained candidate (by simp [candidateMember])
        · exact member
        · exact spellingMember
  | @group group ds ts tail ih =>
      intro declaration member spelling spellingMember
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · change spelling ∈ [] at spellingMember
        contradiction
      · apply ih
        · intro candidate candidateMember
          exact contained candidate (by simp [candidateMember])
        · exact member
        · exact spellingMember

private theorem comparisonRenamingSound_of_expandValues
    (sound : RenamingSound ρg program policy)
    (expanded : expandValues policy program = .ok target) :
    ComparisonRenamingSound ρg target policy := by
  have checks := valueBindingErrors_none_of_expandValues_ok expanded
  have bindingFixed : ∀ binding ∈ program.valueBindings, ∀ spelling,
      spelling ∈ termNullaryCons binding.term →
        Binding.renameText ρg spelling = spelling := by
    intro binding bindingMember spelling spellingMember
    obtain ⟨sort, sorted⟩ :=
      valueBinding_sorted_of_errors_none checks binding bindingMember
    obtain ⟨constructor, constructorMember, constructorName⟩ :=
      termNullaryCons_of_sortOf_some sorted spellingMember
    calc
      Binding.renameText ρg spelling =
          Binding.renameText ρg constructor.sym.name := by
        rw [constructorName]
      _ = constructor.sym.name :=
        sound.sigma constructor constructorMember
      _ = spelling := constructorName
  have relation := expandValues_sound policy expanded
  cases relation with
  | @intro environment gamma environmentEq gammaEq bindingsEq artifactEq
      digestEq policyEq backendsEq declarations =>
      rw [environmentEq] at declarations
      have declarationsFixed := declsExpand_nullaries_fixed sound bindingFixed
        declarations (by simp)
      constructor
      · intro spelling spellingMember _
        rcases List.mem_flatMap.mp spellingMember with
          ⟨declaration, declarationMember, contained⟩
        exact declarationsFixed declaration declarationMember spelling contained
      · exact sound.patterns

/-- Value expansion's prose-erased relation composes with the executable
comparison pass while retaining each pass's exact typed error provenance. -/
theorem expandValuesThenComparisons_rename_related
    (sound : RenamingSound ρg program policy) :
    RenamedExcept (ExpandValuesErrorRelated ρg)
      (fun source target =>
        RenamedExcept (ExpandComparisonsErrorRelated ρg)
          (GeneratedResultsRelated ρg)
          (expandComparisons policy source)
          (expandComparisons (Binding.renamePolicy ρg policy) target))
      (expandValues policy program)
      (expandValues (Binding.renamePolicy ρg policy)
        (Binding.renameProgram ρg program)) := by
  have values := expandValues_rename_related sound
  cases sourceResult : expandValues policy program with
  | error sourceError =>
      cases targetResult : expandValues (Binding.renamePolicy ρg policy)
          (Binding.renameProgram ρg program) with
      | error targetError =>
          simp [sourceResult, targetResult] at values
          cases values with
          | error errorRelated => exact RenamedExcept.error errorRelated
      | ok targetValue =>
          simp [sourceResult, targetResult] at values
          cases values
  | ok sourceValue =>
      cases targetResult : expandValues (Binding.renamePolicy ρg policy)
          (Binding.renameProgram ρg program) with
      | error targetError =>
          simp [sourceResult, targetResult] at values
          cases values
      | ok targetValue =>
          simp [sourceResult, targetResult] at values
          cases values with
          | ok programsRelated =>
              have comparisonSound :=
                comparisonRenamingSound_of_expandValues sound sourceResult
              exact RenamedExcept.ok
                (expandComparisons_semantic_related comparisonSound
                  programsRelated)

private theorem admission_mem_map_injective_iff
    (rename : α → β) (injective : Function.Injective rename)
    (value : α) (values : List α) :
    rename value ∈ values.map rename ↔ value ∈ values := by
  constructor
  · intro member
    obtain ⟨source, sourceMember, equal⟩ := List.mem_map.mp member
    exact injective equal ▸ sourceMember
  · exact fun member => List.mem_map.mpr ⟨value, member, rfl⟩

private theorem renameCoreLeafId_injective (rho : Binding.GlobalRenaming) :
    Function.Injective (renameCoreLeafId rho) := by
  intro left right equal
  cases left with
  | mk left =>
      cases right with
      | mk right =>
          have typed :
              rho.leaf (⟨left⟩ : Presentation.LeafId) =
                rho.leaf (⟨right⟩ : Presentation.LeafId) := by
            apply congrArg Presentation.LeafId.mk
            exact congrArg Lara.Support.LeafId.name equal
          have original := rho.leaf_injective typed
          exact congrArg Lara.Support.LeafId.mk
            (congrArg Presentation.LeafId.val original)

private theorem renameCoreArgString_injective (rho : Binding.GlobalRenaming) :
    Function.Injective (fun value : String => (rho.arg ⟨value⟩).val) := by
  intro left right equal
  have typed :
      rho.arg (⟨left⟩ : Presentation.ArgId) =
        rho.arg (⟨right⟩ : Presentation.ArgId) := by
    apply congrArg Presentation.ArgId.mk
    exact equal
  exact congrArg Presentation.ArgId.val (rho.arg_injective typed)

private theorem firstDuplicateLeafIdAux_rename
    (rename : Lara.Support.LeafId → Lara.Support.LeafId)
    (injective : Function.Injective rename) :
    ∀ (ids seen : List Lara.Support.LeafId),
      Lara.Admission.firstDuplicateLeafIdAux (ids.map rename)
          (seen.map rename) =
        (Lara.Admission.firstDuplicateLeafIdAux ids seen).map rename
  | [], _ => rfl
  | head :: tail, seen => by
      by_cases member : head ∈ seen
      · have renamedMember : rename head ∈ seen.map rename :=
          (admission_mem_map_injective_iff rename injective head seen).2 member
        simp [Lara.Admission.firstDuplicateLeafIdAux, member, renamedMember]
      · have renamedNotMember : rename head ∉ seen.map rename := by
          simpa [admission_mem_map_injective_iff rename injective] using member
        simp only [List.map_cons, Lara.Admission.firstDuplicateLeafIdAux,
          renamedNotMember, member, ↓reduceIte]
        exact firstDuplicateLeafIdAux_rename rename injective tail (head :: seen)

private theorem firstDuplicateLeafId_rename
    (metas : List Lara.Admission.LeafMeta) :
    Lara.Admission.firstDuplicateLeafId
        (metas.map (renameLeafMeta ρg)) =
      (Lara.Admission.firstDuplicateLeafId metas).map
        (renameCoreLeafId ρg) := by
  unfold Lara.Admission.firstDuplicateLeafId
  rw [show (metas.map (renameLeafMeta ρg)).map
      (fun item => item.id) =
        (metas.map (fun item => item.id)).map (renameCoreLeafId ρg) by
    simp [List.map_map, Function.comp_def, renameLeafMeta]]
  simpa using firstDuplicateLeafIdAux_rename (renameCoreLeafId ρg)
    (renameCoreLeafId_injective ρg) (metas.map (fun item => item.id)) []

private theorem admission_list_map_injective
    (rename : α → β) (injective : Function.Injective rename) :
    Function.Injective (List.map rename) := by
  intro left right equal
  induction left generalizing right with
  | nil =>
      cases right <;> simp_all
  | cons head tail ih =>
      cases right with
      | nil => simp at equal
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at equal
          have headEq := injective equal.1
          have tailEq := ih equal.2
          simp [headEq, tailEq]

private theorem metadataLeafAligned_rename
    (metas : List Lara.Admission.LeafMeta)
    (leaves : List (Lara.Support.LeafId × Lara.Atom)) :
    Lara.Admission.metadataLeafAligned
        (metas.map (renameLeafMeta ρg))
        (leaves.map fun entry =>
          (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2)) ↔
      Lara.Admission.metadataLeafAligned metas leaves := by
  unfold Lara.Admission.metadataLeafAligned
  rw [show (metas.map (renameLeafMeta ρg)).map (fun item => item.id) =
      List.map (renameCoreLeafId ρg)
        (metas.map (fun item => item.id)) by
    simp [List.map_map, Function.comp_def, renameLeafMeta]]
  rw [show (leaves.map fun entry =>
      (renameCoreLeafId ρg entry.1,
        renameResidualAtom ρg entry.2)).map (fun entry => entry.1) =
      List.map (renameCoreLeafId ρg)
        (leaves.map (fun entry => entry.1)) by
    simp [List.map_map, Function.comp_def]]
  constructor
  · exact fun equal =>
      (admission_list_map_injective (renameCoreLeafId ρg)
        (renameCoreLeafId_injective ρg)) equal
  · exact congrArg (List.map (renameCoreLeafId ρg))

private theorem firstAdmissionRejection_rename
    (table : List Lara.Admission.AdmissionRow)
    (metas : List Lara.Admission.LeafMeta) :
    Lara.Admission.firstAdmissionRejection table
        (metas.map (renameLeafMeta ρg)) =
      (Lara.Admission.firstAdmissionRejection table metas).map
        (renameAdmissionRejection ρg) := by
  induction metas with
  | nil => rfl
  | cons item rest ih =>
      unfold Lara.Admission.firstAdmissionRejection at ih ⊢
      by_cases rejected :
          Lara.Admission.decisionFor table item.kind item.provenance =
            .reject
      · simp [Lara.Admission.firstAdmissionRejection.go, renameLeafMeta,
          renameAdmissionRejection, rejected]
      · simp [Lara.Admission.firstAdmissionRejection.go, renameLeafMeta,
          rejected, ih]

private theorem policyQuarantineSeed_rename
    (table : List Lara.Admission.AdmissionRow)
    (metas : List Lara.Admission.LeafMeta) :
    Lara.Admission.policyQuarantineSeed table
        (metas.map (renameLeafMeta ρg)) =
      (Lara.Admission.policyQuarantineSeed table metas).map
        (renameCoreLeafId ρg) := by
  induction metas with
  | nil => rfl
  | cons item rest ih =>
      unfold Lara.Admission.policyQuarantineSeed at ih ⊢
      by_cases quarantined :
          Lara.Admission.decisionFor table item.kind item.provenance =
            .quarantine
      · simp [renameLeafMeta, quarantined, ih]
      · simp [renameLeafMeta, quarantined, ih]

mutual
  private theorem admission_nfTerm_renameResidual (canon : String → String)
      (rho : Binding.GlobalRenaming) (term : Lara.Term) :
      Lara.nfTerm canon (renameResidualTerm rho term) =
        renameResidualTerm rho (Lara.nfTerm canon term) := by
    cases term with
    | num source => rfl
    | str source => rfl
    | con name terms =>
        cases terms with
        | nil => rfl
        | cons term rest =>
            change Lara.Term.con name
                (Lara.nfTerms canon
                  (renameResidualTerms rho (.cons term rest))) =
              Lara.Term.con name (renameResidualTerms rho
                (Lara.nfTerms canon (.cons term rest)))
            rw [admission_nfTerms_renameResidual]
  private theorem admission_nfTerms_renameResidual (canon : String → String)
      (rho : Binding.GlobalRenaming) (terms : Lara.Terms) :
      Lara.nfTerms canon (renameResidualTerms rho terms) =
        renameResidualTerms rho (Lara.nfTerms canon terms) := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp [Lara.nfTerms, renameResidualTerms,
          admission_nfTerm_renameResidual canon rho term,
          admission_nfTerms_renameResidual canon rho rest]
end

private theorem admission_nfAtom_renameResidual (canon : String → String)
    (rho : Binding.GlobalRenaming) (atom : Lara.Atom) :
    Lara.nf canon (renameResidualAtom rho atom) =
      renameResidualAtom rho (Lara.nf canon atom) := by
  cases atom
  simp [Lara.nf, renameResidualAtom,
    admission_nfTerms_renameResidual]

private theorem admission_residualAtom_injective
    (rho : Binding.GlobalRenaming) :
    Function.Injective (renameResidualAtom rho) := by
  intro left right equal
  cases left with
  | atom leftPred leftTerms =>
      cases right with
      | atom rightPred rightTerms =>
          simp only [renameResidualAtom, Lara.Atom.atom.injEq] at equal
          have terms := (renameResidualTerms_eq_iff rho).mp equal.2
          simp [equal.1, terms]

private theorem admission_equiv_renameResidual (canon : String → String)
    (rho : Binding.GlobalRenaming) (left right : Lara.Atom) :
    Lara.equiv canon (renameResidualAtom rho left)
        (renameResidualAtom rho right) ↔
      Lara.equiv canon left right := by
  simp only [Lara.equiv, admission_nfAtom_renameResidual]
  exact (admission_residualAtom_injective rho).eq_iff

private theorem admission_find?_map
    (mapValue : α → β) (sourcePredicate : α → Bool)
    (targetPredicate : β → Bool) (values : List α)
    (predicateEq : ∀ value,
      targetPredicate (mapValue value) = sourcePredicate value) :
    (values.map mapValue).find? targetPredicate =
      (values.find? sourcePredicate).map mapValue := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.map_cons, List.find?_cons]
      rw [predicateEq, ih]
      cases sourcePredicate value <;> rfl

private theorem groupLeafProp_rename
    (leaves : List (Lara.Support.LeafId × Lara.Atom))
    (leaf : Lara.Support.LeafId) :
    Lara.Groups.leafProp
        (leaves.map fun entry =>
          (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2))
        (renameCoreLeafId ρg leaf) =
      (Lara.Groups.leafProp leaves leaf).map (renameResidualAtom ρg) := by
  unfold Lara.Groups.leafProp
  rw [admission_find?_map
    (fun entry : Lara.Support.LeafId × Lara.Atom =>
      (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2))
    (fun entry => decide (entry.1 = leaf))
    (fun entry => decide (entry.1 = renameCoreLeafId ρg leaf)) leaves]
  · simp [Option.map_map, Function.comp_def]
  · intro entry
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (renameCoreLeafId_injective ρg).eq_iff

private theorem groupMemberProps_rename
    (leaves : List (Lara.Support.LeafId × Lara.Atom))
    (group : Lara.Groups.DupGroup) :
    Lara.Groups.memberProps
        (leaves.map fun entry =>
          (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2))
        (renameDupGroup ρg group) =
      (Lara.Groups.memberProps leaves group).map
        (List.map (renameResidualAtom ρg)) := by
  cases group with
  | mk id members =>
      simp only [Lara.Groups.memberProps, renameDupGroup]
      induction members with
      | nil => rfl
      | cons leaf rest ih =>
          simp only [List.map_cons, List.mapM_cons]
          rw [groupLeafProp_rename, ih]
          cases Lara.Groups.leafProp leaves leaf <;>
            cases rest.mapM (Lara.Groups.leafProp leaves) <;>
            simp

private theorem groupAllEquiv_rename
    (canon : String → String) (head : Lara.Atom)
    (rest : List Lara.Atom) :
    (rest.map (renameResidualAtom ρg)).all
        (fun value => decide (Lara.equiv canon
          (renameResidualAtom ρg head) value)) =
      rest.all (fun value => decide (Lara.equiv canon head value)) := by
  induction rest with
  | nil => rfl
  | cons value tail ih =>
      simp only [List.map_cons, List.all_cons]
      have decided :
          decide (Lara.equiv canon (renameResidualAtom ρg head)
              (renameResidualAtom ρg value)) =
            decide (Lara.equiv canon head value) := by
        apply Bool.eq_iff_iff.mpr
        simpa only [decide_eq_true_eq] using
          (admission_equiv_renameResidual canon ρg head value)
      rw [decided, ih]

private theorem groupConsistentB_rename
    (canon : String → String)
    (leaves : List (Lara.Support.LeafId × Lara.Atom))
    (group : Lara.Groups.DupGroup) :
    Lara.Groups.consistentB canon
        (leaves.map fun entry =>
          (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2))
        (renameDupGroup ρg group) =
      Lara.Groups.consistentB canon leaves group := by
  unfold Lara.Groups.consistentB
  rw [groupMemberProps_rename]
  cases props : Lara.Groups.memberProps leaves group with
  | none => rfl
  | some values =>
      simp only [Option.map_some]
      cases values with
      | nil => rfl
      | cons head rest =>
          simpa using groupAllEquiv_rename (ρg := ρg) canon head rest

private theorem groupsQuarantined_rename
    (canon : String → String)
    (leaves : List (Lara.Support.LeafId × Lara.Atom))
    (groups : List Lara.Groups.DupGroup) :
    Lara.Groups.quarantined canon
        (leaves.map fun entry =>
          (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2))
        (groups.map (renameDupGroup ρg)) =
      (Lara.Groups.quarantined canon leaves groups).map
        (renameCoreLeafId ρg) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      unfold Lara.Groups.quarantined at ih ⊢
      simp only [List.map_cons, List.filter_cons]
      rw [groupConsistentB_rename]
      cases consistent : Lara.Groups.consistentB canon leaves group <;>
        simp [renameDupGroup, ih, List.map_append]

private theorem inconsistentGroups_rename
    (canon : String → String)
    (leaves : List (Lara.Support.LeafId × Lara.Atom))
    (groups : List Lara.Groups.DupGroup) :
    Lara.Admission.inconsistentGroups canon
        (leaves.map fun entry =>
          (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2))
        (groups.map (renameDupGroup ρg)) =
      (Lara.Admission.inconsistentGroups canon leaves groups).map
        (renameDupGroup ρg) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      unfold Lara.Admission.inconsistentGroups at ih ⊢
      simp only [List.map_cons, List.filter_cons]
      rw [groupConsistentB_rename]
      cases consistent : Lara.Groups.consistentB canon leaves group <;>
        simp [ih]

private theorem admission_filter_map
    (mapValue : α → β) (sourcePredicate : α → Bool)
    (targetPredicate : β → Bool) (values : List α)
    (predicateEq : ∀ value,
      targetPredicate (mapValue value) = sourcePredicate value) :
    (values.map mapValue).filter targetPredicate =
      (values.filter sourcePredicate).map mapValue := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.map_cons, List.filter_cons]
      rw [predicateEq, ih]
      cases sourcePredicate value <;> rfl

private theorem admission_filterMap_map
    (mapValue : α → β) (mapOutput : γ → δ)
    (sourceSelect : α → Option γ)
    (targetSelect : β → Option δ) (values : List α)
    (selectEq : ∀ value,
      targetSelect (mapValue value) = (sourceSelect value).map mapOutput) :
    (values.map mapValue).filterMap targetSelect =
      (values.filterMap sourceSelect).map mapOutput := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.map_cons, List.filterMap_cons]
      rw [selectEq, ih]
      cases sourceSelect value <;> rfl

private theorem quarantineLeaves_rename
    (removed : List Lara.Support.LeafId)
    (leaves : List (Lara.Support.LeafId × Lara.Atom)) :
    Lara.Groups.quarantineLeaves
        (removed.map (renameCoreLeafId ρg))
        (leaves.map fun entry =>
          (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2)) =
      (Lara.Groups.quarantineLeaves removed leaves).map fun entry =>
        (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2) := by
  unfold Lara.Groups.quarantineLeaves
  apply admission_filter_map
  intro entry
  have memberDecide :
      decide (renameCoreLeafId ρg entry.1 ∈
          removed.map (renameCoreLeafId ρg)) =
        decide (entry.1 ∈ removed) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using
      (admission_mem_map_injective_iff
        (renameCoreLeafId ρg) (renameCoreLeafId_injective ρg)
        entry.1 removed)
  exact congrArg (fun value => !value) memberDecide

mutual
  private theorem usesLeaf_rename
      (removed : List Lara.Support.LeafId)
      (term : Lara.Support.SupportTerm) :
      Lara.Groups.usesLeaf (removed.map (renameCoreLeafId ρg))
          (renameCoreSupportTerm ρg term) =
        Lara.Groups.usesLeaf removed term := by
    cases term with
    | leaf leaf =>
        simp only [renameCoreSupportTerm, Lara.Groups.usesLeaf]
        apply Bool.eq_iff_iff.mpr
        simpa only [decide_eq_true_eq] using
          (admission_mem_map_injective_iff
            (renameCoreLeafId ρg) (renameCoreLeafId_injective ρg)
            leaf removed)
    | inst rule subst premises discharges holes assurance =>
        simp only [Lara.Groups.usesLeaf, renameCoreSupportTerm]
        rw [usesLeafList_rename (ρg := ρg) removed premises,
          usesLeafDisch_rename (ρg := ρg) removed discharges]
  private theorem usesLeafList_rename
      (removed : List Lara.Support.LeafId)
      (terms : List Lara.Support.SupportTerm) :
      Lara.Groups.usesLeafList (removed.map (renameCoreLeafId ρg))
          (renameCoreSupportTerms ρg terms) =
        Lara.Groups.usesLeafList removed terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp only [Lara.Groups.usesLeafList, renameCoreSupportTerms]
        rw [usesLeaf_rename (ρg := ρg) removed term,
          usesLeafList_rename (ρg := ρg) removed rest]
  private theorem usesLeafDisch_rename
      (removed : List Lara.Support.LeafId)
      (discharges : List
        (Lara.Support.QuestionId × Lara.Support.SupportTerm)) :
      Lara.Groups.usesLeafDisch (removed.map (renameCoreLeafId ρg))
          (renameCoreSupportDischarges ρg discharges) =
        Lara.Groups.usesLeafDisch removed discharges := by
    cases discharges with
    | nil => rfl
    | cons discharge rest =>
        cases discharge with
        | mk question term =>
            simp only [Lara.Groups.usesLeafDisch,
              renameCoreSupportDischarges]
            rw [usesLeaf_rename (ρg := ρg) removed term,
              usesLeafDisch_rename (ρg := ρg) removed rest]
end

private theorem rawAttackEndpoints_rename
    (attack : Lara.RawAttack.RawAttack) :
    (renameRawAttack ρg attack).endpoints =
      ((ρg.arg ⟨attack.endpoints.1⟩).val,
        (ρg.arg ⟨attack.endpoints.2⟩).val) := by
  cases attack <;>
    simp [renameRawAttack, Lara.RawAttack.RawAttack.endpoints]

private theorem selectAligned_rename
    (sourceKeep : Lara.RawAttack.RawAttack → Bool)
    (targetKeep : Lara.RawAttack.RawAttack → Bool)
    (commutes : ∀ attack,
      targetKeep (renameRawAttack ρg attack) = sourceKeep attack) :
    ∀ (raw : List Lara.RawAttack.RawAttack)
      (resolved : List Lara.Attack.Attack),
      Lara.RawAttack.selectAligned targetKeep
          (raw.map (renameRawAttack ρg))
          (resolved.map (renameCoreAttack ρg)) =
        (Lara.RawAttack.selectAligned sourceKeep raw resolved).map
          (renameCoreAttack ρg)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | attack :: raw, semantic :: resolved => by
      simp only [List.map_cons, Lara.RawAttack.selectAligned]
      rw [commutes, selectAligned_rename sourceKeep targetKeep commutes raw resolved]
      cases sourceKeep attack <;> rfl

private theorem auditGroupCauses_rename
    (leaf : Lara.Support.LeafId)
    (groups : List Lara.Groups.DupGroup) :
    (groups.map (renameDupGroup ρg)).filterMap (fun group =>
        if renameCoreLeafId ρg leaf ∈ group.members then
          some (Lara.Admission.AdmissionCause.group group.id)
        else none) =
      (groups.filterMap (fun group =>
        if leaf ∈ group.members then
          some (Lara.Admission.AdmissionCause.group group.id)
        else none)).map (renameAdmissionCause ρg) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      simp only [List.map_cons, List.filterMap_cons]
      have memberEq :
          renameCoreLeafId ρg leaf ∈
              (renameDupGroup ρg group).members ↔
            leaf ∈ group.members := by
        simpa [renameDupGroup] using
          (admission_mem_map_injective_iff
            (renameCoreLeafId ρg) (renameCoreLeafId_injective ρg)
            leaf group.members)
      by_cases member : leaf ∈ group.members
      · have renamedMember := memberEq.2 member
        rw [if_pos renamedMember, if_pos member, ih]
        simp [renameDupGroup, renameAdmissionCause]
      · have renamedNotMember :
            renameCoreLeafId ρg leaf ∉
              (renameDupGroup ρg group).members :=
          fun found => member (memberEq.1 found)
        rw [if_neg renamedNotMember, if_neg member, ih]

private theorem auditLeaves_rename
    (policySeed : List Lara.Support.LeafId)
    (inconsistent : List Lara.Groups.DupGroup)
    (removedLeaves : List Lara.Support.LeafId) :
    Lara.Admission.auditLeaves
        (policySeed.map (renameCoreLeafId ρg))
        (inconsistent.map (renameDupGroup ρg))
        (removedLeaves.map (renameCoreLeafId ρg)) =
      (Lara.Admission.auditLeaves policySeed inconsistent removedLeaves).map
        (fun entry =>
          (renameCoreLeafId ρg entry.1,
            entry.2.map (renameAdmissionCause ρg))) := by
  induction removedLeaves with
  | nil => rfl
  | cons leaf rest ih =>
      unfold Lara.Admission.auditLeaves at ih
      simp only [Lara.Admission.auditLeaves, List.map_cons]
      have policyMember :
          renameCoreLeafId ρg leaf ∈
              policySeed.map (renameCoreLeafId ρg) ↔
            leaf ∈ policySeed :=
        admission_mem_map_injective_iff
          (renameCoreLeafId ρg) (renameCoreLeafId_injective ρg)
          leaf policySeed
      by_cases member : leaf ∈ policySeed
      · have renamedMember := policyMember.2 member
        have groupCauses :=
          auditGroupCauses_rename (ρg := ρg) leaf inconsistent
        simp only [renamedMember, member, ↓reduceIte]
        rw [groupCauses, ih]
        simp [renameAdmissionCause]
      · have renamedNotMember :
            renameCoreLeafId ρg leaf ∉
              policySeed.map (renameCoreLeafId ρg) :=
          fun found => member (policyMember.1 found)
        have groupCauses :=
          auditGroupCauses_rename (ρg := ρg) leaf inconsistent
        simp only [renamedNotMember, member, ↓reduceIte]
        rw [groupCauses, ih]
        simp

private theorem removedLeaves_rename
    (removed : List Lara.Support.LeafId)
    (leaves : List (Lara.Support.LeafId × Lara.Atom)) :
    (leaves.map fun entry =>
      (renameCoreLeafId ρg entry.1,
        renameResidualAtom ρg entry.2)).filterMap (fun entry =>
        if entry.1 ∈ removed.map (renameCoreLeafId ρg) then
          some entry.1 else none) =
      (leaves.filterMap (fun entry =>
        if entry.1 ∈ removed then some entry.1 else none)).map
          (renameCoreLeafId ρg) := by
  apply admission_filterMap_map
  intro entry
  have memberEq := admission_mem_map_injective_iff
    (renameCoreLeafId ρg) (renameCoreLeafId_injective ρg)
    entry.1 removed
  by_cases member : entry.1 ∈ removed
  · simp [member, memberEq.2 member]
  · have renamedNot :
        renameCoreLeafId ρg entry.1 ∉
          removed.map (renameCoreLeafId ρg) :=
      fun found => member (memberEq.1 found)
    simp [member, renamedNot]

private theorem checkedLeafTable_rename
    (canon : String → String)
    (table : List Lara.Admission.AdmissionRow)
    (metas : List Lara.Admission.LeafMeta)
    (leaves : List (Lara.Support.LeafId × Lara.Atom))
    (groups : List Lara.Groups.DupGroup) :
    Lara.Admission.checkedLeafTable canon table
        (metas.map (renameLeafMeta ρg))
        (leaves.map fun entry =>
          (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2))
        (groups.map (renameDupGroup ρg)) =
      (Lara.Admission.checkedLeafTable canon table metas leaves groups).map
        (fun entry =>
          (renameCoreLeafId ρg entry.1,
            renameResidualAtom ρg entry.2)) := by
  unfold Lara.Admission.checkedLeafTable
  rw [policyQuarantineSeed_rename, groupsQuarantined_rename]
  simpa [List.map_append] using quarantineLeaves_rename (ρg := ρg)
    (Lara.Admission.policyQuarantineSeed table metas ++
      Lara.Groups.quarantined canon leaves groups) leaves

private theorem keptArgs_rename
    (removed : List Lara.Support.LeafId)
    (argsRaw : List (String × Lara.Support.SupportTerm)) :
    (argsRaw.map fun entry =>
      ((ρg.arg ⟨entry.1⟩).val,
        renameCoreSupportTerm ρg entry.2)).filter (fun entry =>
        !Lara.Groups.usesLeaf (removed.map (renameCoreLeafId ρg))
          entry.2) =
      (argsRaw.filter (fun entry =>
        !Lara.Groups.usesLeaf removed entry.2)).map (fun entry =>
          ((ρg.arg ⟨entry.1⟩).val,
            renameCoreSupportTerm ρg entry.2)) := by
  apply admission_filter_map
  intro entry
  exact congrArg (fun value => !value)
    (usesLeaf_rename (ρg := ρg) removed entry.2)

private theorem keptIds_rename
    (removed : List Lara.Support.LeafId)
    (argsRaw : List (String × Lara.Support.SupportTerm)) :
    ((argsRaw.map fun entry =>
      ((ρg.arg ⟨entry.1⟩).val,
        renameCoreSupportTerm ρg entry.2)).filter (fun entry =>
        !Lara.Groups.usesLeaf (removed.map (renameCoreLeafId ρg))
          entry.2)).map (fun entry => entry.1) =
      ((argsRaw.filter (fun entry =>
        !Lara.Groups.usesLeaf removed entry.2)).map
          (fun entry => entry.1)).map
            (fun argument => (ρg.arg ⟨argument⟩).val) := by
  rw [keptArgs_rename (ρg := ρg)]
  simp [List.map_map, Function.comp_def]

private theorem removedArgs_rename
    (removed : List Lara.Support.LeafId)
    (argsRaw : List (String × Lara.Support.SupportTerm)) :
    (argsRaw.map fun entry =>
      ((ρg.arg ⟨entry.1⟩).val,
        renameCoreSupportTerm ρg entry.2)).filterMap (fun entry =>
        if !Lara.Groups.usesLeaf
            (removed.map (renameCoreLeafId ρg)) entry.2 then
          none else some entry.1) =
      (argsRaw.filterMap (fun entry =>
        if !Lara.Groups.usesLeaf removed entry.2 then
          none else some entry.1)).map
            (fun argument => (ρg.arg ⟨argument⟩).val) := by
  apply admission_filterMap_map
  intro entry
  rw [usesLeaf_rename (ρg := ρg) removed entry.2]
  cases !Lara.Groups.usesLeaf removed entry.2 <;> rfl

private theorem keepAttack_rename
    (keptIds : List String) (attack : Lara.RawAttack.RawAttack) :
    (let endpoints := (renameRawAttack ρg attack).endpoints;
      decide (endpoints.1 ∈ keptIds.map
          (fun argument => (ρg.arg ⟨argument⟩).val)) &&
        decide (endpoints.2 ∈ keptIds.map
          (fun argument => (ρg.arg ⟨argument⟩).val))) =
      (let endpoints := attack.endpoints;
        decide (endpoints.1 ∈ keptIds) &&
          decide (endpoints.2 ∈ keptIds)) := by
  simp only [rawAttackEndpoints_rename]
  have sourceEq :
      decide ((ρg.arg ⟨attack.endpoints.1⟩).val ∈
          keptIds.map (fun argument => (ρg.arg ⟨argument⟩).val)) =
        decide (attack.endpoints.1 ∈ keptIds) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using
      (admission_mem_map_injective_iff _
        (renameCoreArgString_injective ρg) attack.endpoints.1 keptIds)
  have targetEq :
      decide ((ρg.arg ⟨attack.endpoints.2⟩).val ∈
          keptIds.map (fun argument => (ρg.arg ⟨argument⟩).val)) =
        decide (attack.endpoints.2 ∈ keptIds) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using
      (admission_mem_map_injective_iff _
        (renameCoreArgString_injective ρg) attack.endpoints.2 keptIds)
  rw [sourceEq, targetEq]

private theorem removedAttacks_rename
    (keptIds : List String) (rawAtts : List Lara.RawAttack.RawAttack) :
    (rawAtts.map (renameRawAttack ρg)).filter (fun attack =>
        !(let endpoints := attack.endpoints
          decide (endpoints.1 ∈ keptIds.map
              (fun argument => (ρg.arg ⟨argument⟩).val)) &&
            decide (endpoints.2 ∈ keptIds.map
              (fun argument => (ρg.arg ⟨argument⟩).val)))) =
      (rawAtts.filter (fun attack =>
        !(let endpoints := attack.endpoints
          decide (endpoints.1 ∈ keptIds) &&
            decide (endpoints.2 ∈ keptIds)))).map (renameRawAttack ρg) := by
  apply admission_filter_map
  intro attack
  exact congrArg (fun value => !value)
    (keepAttack_rename (ρg := ρg) keptIds attack)

private theorem keptAttacks_rename
    (keptIds : List String) (rawAtts : List Lara.RawAttack.RawAttack)
    (declaredResolved : List Lara.Attack.Attack) :
    Lara.RawAttack.selectAligned
        (fun attack =>
          let endpoints := attack.endpoints
          decide (endpoints.1 ∈ keptIds.map
              (fun argument => (ρg.arg ⟨argument⟩).val)) &&
            decide (endpoints.2 ∈ keptIds.map
              (fun argument => (ρg.arg ⟨argument⟩).val)))
        (rawAtts.map (renameRawAttack ρg))
        (declaredResolved.map (renameCoreAttack ρg)) =
      (Lara.RawAttack.selectAligned
        (fun attack =>
          let endpoints := attack.endpoints
          decide (endpoints.1 ∈ keptIds) &&
            decide (endpoints.2 ∈ keptIds))
        rawAtts declaredResolved).map (renameCoreAttack ρg) := by
  apply selectAligned_rename
  exact keepAttack_rename (ρg := ρg) keptIds

private theorem keepAttackFromArgs_rename
    (removed : List Lara.Support.LeafId)
    (argsRaw : List (String × Lara.Support.SupportTerm))
    (attack : Lara.RawAttack.RawAttack) :
    (let keptIds :=
        ((argsRaw.map fun entry =>
          ((ρg.arg ⟨entry.1⟩).val,
            renameCoreSupportTerm ρg entry.2)).filter (fun entry =>
              !Lara.Groups.usesLeaf
                (removed.map (renameCoreLeafId ρg)) entry.2)).map
                  (fun entry => entry.1)
      let endpoints := (renameRawAttack ρg attack).endpoints
      decide (endpoints.1 ∈ keptIds) && decide (endpoints.2 ∈ keptIds)) =
      (let keptIds :=
        (argsRaw.filter (fun entry =>
          !Lara.Groups.usesLeaf removed entry.2)).map (fun entry => entry.1)
       let endpoints := attack.endpoints
       decide (endpoints.1 ∈ keptIds) && decide (endpoints.2 ∈ keptIds)) := by
  rw [keptIds_rename (ρg := ρg) removed argsRaw]
  exact keepAttack_rename (ρg := ρg)
    ((argsRaw.filter (fun entry =>
      !Lara.Groups.usesLeaf removed entry.2)).map (fun entry => entry.1)) attack

private theorem keptAttacksFromArgs_rename
    (removed : List Lara.Support.LeafId)
    (argsRaw : List (String × Lara.Support.SupportTerm))
    (rawAtts : List Lara.RawAttack.RawAttack)
    (declaredResolved : List Lara.Attack.Attack) :
    Lara.RawAttack.selectAligned
        (fun attack =>
          let keptIds :=
            ((argsRaw.map fun entry =>
              ((ρg.arg ⟨entry.1⟩).val,
                renameCoreSupportTerm ρg entry.2)).filter (fun entry =>
                  !Lara.Groups.usesLeaf
                    (removed.map (renameCoreLeafId ρg)) entry.2)).map
                      (fun entry => entry.1)
          let endpoints := attack.endpoints
          decide (endpoints.1 ∈ keptIds) && decide (endpoints.2 ∈ keptIds))
        (rawAtts.map (renameRawAttack ρg))
        (declaredResolved.map (renameCoreAttack ρg)) =
      (Lara.RawAttack.selectAligned
        (fun attack =>
          let keptIds :=
            (argsRaw.filter (fun entry =>
              !Lara.Groups.usesLeaf removed entry.2)).map (fun entry => entry.1)
          let endpoints := attack.endpoints
          decide (endpoints.1 ∈ keptIds) && decide (endpoints.2 ∈ keptIds))
        rawAtts declaredResolved).map (renameCoreAttack ρg) := by
  apply selectAligned_rename
  exact keepAttackFromArgs_rename (ρg := ρg) removed argsRaw

private theorem removedAttacksFromArgs_rename
    (removed : List Lara.Support.LeafId)
    (argsRaw : List (String × Lara.Support.SupportTerm))
    (rawAtts : List Lara.RawAttack.RawAttack) :
    (rawAtts.map (renameRawAttack ρg)).filter (fun attack =>
        !(let keptIds :=
            ((argsRaw.map fun entry =>
              ((ρg.arg ⟨entry.1⟩).val,
                renameCoreSupportTerm ρg entry.2)).filter (fun entry =>
                  !Lara.Groups.usesLeaf
                    (removed.map (renameCoreLeafId ρg)) entry.2)).map
                      (fun entry => entry.1)
          let endpoints := attack.endpoints
          decide (endpoints.1 ∈ keptIds) &&
            decide (endpoints.2 ∈ keptIds))) =
      (rawAtts.filter (fun attack =>
        !(let keptIds :=
            (argsRaw.filter (fun entry =>
              !Lara.Groups.usesLeaf removed entry.2)).map (fun entry => entry.1)
          let endpoints := attack.endpoints
          decide (endpoints.1 ∈ keptIds) &&
            decide (endpoints.2 ∈ keptIds)))).map (renameRawAttack ρg) := by
  apply admission_filter_map
  intro attack
  exact congrArg (fun value => !value)
    (keepAttackFromArgs_rename (ρg := ρg) removed argsRaw attack)

private theorem buildPrune_rename
    (canon : String → String)
    (table : List Lara.Admission.AdmissionRow)
    (metas : List Lara.Admission.LeafMeta)
    (leaves : List (Lara.Support.LeafId × Lara.Atom))
    (argsRaw : List (String × Lara.Support.SupportTerm))
    (rawAtts : List Lara.RawAttack.RawAttack)
    (groups : List Lara.Groups.DupGroup)
    (declaredResolved : List Lara.Attack.Attack) :
    Lara.Admission.buildPrune canon table
        (metas.map (renameLeafMeta ρg))
        (leaves.map fun entry =>
          (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2))
        (argsRaw.map fun entry =>
          ((ρg.arg ⟨entry.1⟩).val, renameCoreSupportTerm ρg entry.2))
        (rawAtts.map (renameRawAttack ρg))
        (groups.map (renameDupGroup ρg))
        (declaredResolved.map (renameCoreAttack ρg)) =
      renameAdmissionPrune ρg
        (Lara.Admission.buildPrune canon table metas leaves argsRaw rawAtts
          groups declaredResolved) := by
  unfold Lara.Admission.buildPrune renameAdmissionPrune
  simp only [policyQuarantineSeed_rename, groupsQuarantined_rename,
    List.map_append]
  congr 1
  case e_removedLeaves =>
    simpa only [List.map_append] using removedLeaves_rename (ρg := ρg)
      (Lara.Admission.policyQuarantineSeed table metas ++
        Lara.Groups.quarantined canon leaves groups) leaves
  case e_checkedLeaves =>
    exact checkedLeafTable_rename (ρg := ρg) canon table metas leaves groups
  case e_keptArgs =>
    simpa only [List.map_append] using keptArgs_rename (ρg := ρg)
      (Lara.Admission.policyQuarantineSeed table metas ++
        Lara.Groups.quarantined canon leaves groups) argsRaw
  case e_keptIds =>
    simpa only [List.map_append] using keptIds_rename (ρg := ρg)
      (Lara.Admission.policyQuarantineSeed table metas ++
        Lara.Groups.quarantined canon leaves groups) argsRaw
  case e_removedArgs =>
    simpa only [List.map_append] using removedArgs_rename (ρg := ρg)
      (Lara.Admission.policyQuarantineSeed table metas ++
        Lara.Groups.quarantined canon leaves groups) argsRaw
  case e_keptAttacks =>
    simpa only [List.map_append] using keptAttacksFromArgs_rename (ρg := ρg)
      (Lara.Admission.policyQuarantineSeed table metas ++
        Lara.Groups.quarantined canon leaves groups) argsRaw rawAtts
          declaredResolved
  case e_removedAttacks =>
    simpa only [List.map_append] using removedAttacksFromArgs_rename (ρg := ρg)
      (Lara.Admission.policyQuarantineSeed table metas ++
        Lara.Groups.quarantined canon leaves groups) argsRaw rawAtts
  case e_keepAttack =>
    funext attack
    simpa only [List.map_append] using congrArg
      (fun keptIds =>
        let endpoints := attack.endpoints
        decide (endpoints.1 ∈ keptIds) && decide (endpoints.2 ∈ keptIds))
      (keptIds_rename (ρg := ρg)
        (Lara.Admission.policyQuarantineSeed table metas ++
          Lara.Groups.quarantined canon leaves groups) argsRaw)

private theorem buildAdmissionAudit_rename
    (canon : String → String)
    (table : List Lara.Admission.AdmissionRow)
    (metas : List Lara.Admission.LeafMeta)
    (leaves : List (Lara.Support.LeafId × Lara.Atom))
    (argsRaw : List (String × Lara.Support.SupportTerm))
    (rawAtts : List Lara.RawAttack.RawAttack)
    (groups : List Lara.Groups.DupGroup)
    (declaredResolved : List Lara.Attack.Attack) :
    Lara.Admission.buildAdmissionAudit canon table
        (metas.map (renameLeafMeta ρg))
        (leaves.map fun entry =>
          (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2))
        (argsRaw.map fun entry =>
          ((ρg.arg ⟨entry.1⟩).val, renameCoreSupportTerm ρg entry.2))
        (rawAtts.map (renameRawAttack ρg))
        (groups.map (renameDupGroup ρg))
        (declaredResolved.map (renameCoreAttack ρg)) =
      renameAdmissionAudit ρg
        (Lara.Admission.buildAdmissionAudit canon table metas leaves argsRaw
          rawAtts groups declaredResolved) := by
  unfold Lara.Admission.buildAdmissionAudit
  rw [buildPrune_rename]
  simp only [renameAdmissionPrune, renameAdmissionAudit,
    inconsistentGroups_rename]
  rw [auditLeaves_rename]

/-- Executable source admission commutes with typed global renaming exactly:
validation and R8 rejection provenance are preserved, and successful pruning
renames the complete accepted carrier, including arguments, attacks, and the
canonical audit. -/
theorem evaluateAdmission_rename
    (canon : String → String)
    (table : List Lara.Admission.AdmissionRow)
    (metas : List Lara.Admission.LeafMeta)
    (leaves : List (Lara.Support.LeafId × Lara.Atom))
    (argsRaw : List (String × Lara.Support.SupportTerm))
    (rawAtts : List Lara.RawAttack.RawAttack)
    (groups : List Lara.Groups.DupGroup)
    (declared : Lara.Admission.AlignedAttacks argsRaw rawAtts) :
    Lara.Admission.evaluateAdmission canon table
        (metas.map (renameLeafMeta ρg))
        (leaves.map fun entry =>
          (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2))
        (argsRaw.map fun entry =>
          ((ρg.arg ⟨entry.1⟩).val, renameCoreSupportTerm ρg entry.2))
        (rawAtts.map (renameRawAttack ρg))
        (groups.map (renameDupGroup ρg))
        (renameAlignedAttacks ρg declared) =
      renameSourceAdmission ρg
        (Lara.Admission.evaluateAdmission canon table metas leaves argsRaw
          rawAtts groups declared) := by
  unfold Lara.Admission.evaluateAdmission
  cases duplicateKey : Lara.Admission.firstDuplicateKey table with
  | some key =>
      simp [renameSourceAdmission, renameSourceInvalid]
  | none =>
      have duplicateLeaf := firstDuplicateLeafId_rename (ρg := ρg) metas
      cases sourceDuplicate : Lara.Admission.firstDuplicateLeafId metas with
      | some leaf =>
          have targetDuplicate :
              Lara.Admission.firstDuplicateLeafId
                  (metas.map (renameLeafMeta ρg)) =
                some (renameCoreLeafId ρg leaf) := by
            simpa [sourceDuplicate] using duplicateLeaf
          simp [targetDuplicate,
            renameSourceAdmission, renameSourceInvalid]
      | none =>
          have targetDuplicate :
              Lara.Admission.firstDuplicateLeafId
                  (metas.map (renameLeafMeta ρg)) = none := by
            simpa [sourceDuplicate] using duplicateLeaf
          have alignment := metadataLeafAligned_rename (ρg := ρg)
            metas leaves
          by_cases sourceAligned :
              Lara.Admission.metadataLeafAligned metas leaves
          · have targetAligned := alignment.mpr sourceAligned
            have rejection := firstAdmissionRejection_rename (ρg := ρg)
              table metas
            cases sourceRejection :
                Lara.Admission.firstAdmissionRejection table metas with
            | some rejected =>
                have targetRejection :
                    Lara.Admission.firstAdmissionRejection table
                        (metas.map (renameLeafMeta ρg)) =
                      some (renameAdmissionRejection ρg rejected) := by
                  simpa [sourceRejection] using rejection
                simp [targetDuplicate, sourceAligned, targetAligned,
                  targetRejection, renameSourceAdmission]
            | none =>
                have targetRejection :
                    Lara.Admission.firstAdmissionRejection table
                        (metas.map (renameLeafMeta ρg)) = none := by
                  simpa [sourceRejection] using rejection
                simp only [targetDuplicate, sourceAligned, targetAligned,
                  targetRejection, ↓reduceIte]
                simp only [renameAlignedAttacks]
                rw [buildPrune_rename, buildAdmissionAudit_rename]
                rfl
          · have targetNotAligned :
                ¬ Lara.Admission.metadataLeafAligned
                    (metas.map (renameLeafMeta ρg))
                    (leaves.map fun entry =>
                      (renameCoreLeafId ρg entry.1,
                        renameResidualAtom ρg entry.2)) :=
              fun target => sourceAligned (alignment.mp target)
            simp [targetDuplicate,
              sourceAligned, targetNotAligned, renameSourceAdmission,
              renameSourceInvalid]

/-- A typed global renaming leaves every constructor spelling declared by the
core signature fixed.  This is the checker-local specialization of
`RenamingSound.sigma`; identifiers in the support judgment are still renamed
in their own typed namespaces. -/
def CoreSigmaRenamingSound (ρg : Binding.GlobalRenaming)
    (sigma : Lara.Sigma.Sigma) : Prop :=
  ∀ declaration, declaration ∈ sigma.cons →
    Binding.renameText ρg declaration.sym.name = declaration.sym.name

/-- Task 6's surface renaming contract supplies the checker-local signature
premise directly; later checker composition only has to rewrite the elaborated
unit's sigma alignment. -/
theorem RenamingSound.coreSigma
    (sound : RenamingSound ρg program policy) :
    CoreSigmaRenamingSound ρg policy.sigma :=
  sound.sigma

private theorem renameCoreRuleId_injective_support
    (ρg : Binding.GlobalRenaming) :
    Function.Injective (renameCoreRuleId ρg) := by
  intro left right equal
  cases left with
  | mk leftName =>
    cases right with
    | mk rightName =>
      congr
      apply Binding.renameText_injective ρg
      simpa [renameCoreRuleId, Binding.renameText] using
        Support.RuleId.mk.inj equal

private theorem renameCoreQuestionId_injective_support
    (ρg : Binding.GlobalRenaming) :
    Function.Injective (renameCoreQuestionId ρg) := by
  intro left right equal
  cases left with
  | mk leftName =>
    cases right with
    | mk rightName =>
      congr
      apply Binding.renameText_injective ρg
      simpa [renameCoreQuestionId, Binding.renameText] using
        Support.QuestionId.mk.inj equal

private theorem listMap_injective_support
    (injective : Function.Injective f) :
    Function.Injective (List.map f) := by
  intro left
  induction left with
  | nil =>
      intro right equal
      cases right <;> simp at equal ⊢
  | cons head tail ih =>
      intro right equal
      cases right with
      | nil => simp at equal
      | cons rightHead rightTail =>
          simp only [List.map_cons, List.cons.injEq] at equal
          rw [injective equal.1, ih equal.2]

private theorem optionMap_injective_support
    (injective : Function.Injective f) :
    Function.Injective (Option.map f) := by
  intro left right equal
  cases left with
  | none => cases right <;> simp_all
  | some value =>
      cases right with
      | none => simp at equal
      | some rightValue =>
          simp only [Option.map_some, Option.some.injEq] at equal
          exact congrArg some (injective equal)

private theorem renameCoreQuestion_injective
    (ρg : Binding.GlobalRenaming) :
    Function.Injective (fun question : Support.Question =>
      { question with name := renameCoreQuestionId ρg question.name }) := by
  intro left right equal
  cases left
  cases right
  simp only [Support.Question.mk.injEq] at equal ⊢
  exact ⟨renameCoreQuestionId_injective_support ρg equal.1,
    equal.2.1, equal.2.2⟩

private theorem renameCoreRule_injective
    (ρg : Binding.GlobalRenaming) :
    Function.Injective (renameCoreRule ρg) := by
  intro left right equal
  cases left
  cases right
  simp only [renameCoreRule, Support.Rule.mk.injEq] at equal ⊢
  exact ⟨equal.1, equal.2.1, equal.2.2.1, equal.2.2.2.1,
    listMap_injective_support (renameCoreQuestion_injective ρg)
      equal.2.2.2.2.1,
    equal.2.2.2.2.2.1, equal.2.2.2.2.2.2⟩

private theorem renameGamma_image
    (ρg : Binding.GlobalRenaming)
    (gamma : Support.LeafId → Option Atom) (leaf : Support.LeafId) :
    renameGamma ρg gamma (renameCoreLeafId ρg leaf) =
      (gamma leaf).map (renameResidualAtom ρg) := by
  classical
  unfold renameGamma
  let witness : ∃ source : Support.LeafId,
      renameCoreLeafId ρg source = renameCoreLeafId ρg leaf :=
    ⟨leaf, rfl⟩
  rw [dif_pos witness]
  have chosen := Classical.choose_spec witness
  have sourceEq : Classical.choose witness = leaf :=
    renameCoreLeafId_injective ρg chosen
  rw [sourceEq]

private theorem lookupRuleDecl_rename
    (ρg : Binding.GlobalRenaming)
    (rules : List Lara.Policy.RuleDecl) (id : Support.RuleId) :
    Lara.Policy.lookupRuleDecl
        (rules.map fun declaration =>
          { id := renameCoreRuleId ρg declaration.id
            rule := renameCoreRule ρg declaration.rule })
        (renameCoreRuleId ρg id) =
      (Lara.Policy.lookupRuleDecl rules id).map (renameCoreRule ρg) := by
  induction rules with
  | nil => rfl
  | cons declaration rest ih =>
      simp only [List.map_cons, Lara.Policy.lookupRuleDecl]
      by_cases equal : declaration.id = id
      · have renamedEqual : renameCoreRuleId ρg declaration.id =
            renameCoreRuleId ρg id := congrArg _ equal
        simp [equal, renamedEqual]
      · have renamedDifferent : renameCoreRuleId ρg declaration.id ≠
            renameCoreRuleId ρg id :=
          fun renamed => equal
            (renameCoreRuleId_injective_support ρg renamed)
        simp [equal, renamedDifferent, ih]

private theorem ruleLookup_rename
    (ρg : Binding.GlobalRenaming) (policy : Lara.Policy.Policy)
    (id : Support.RuleId) :
    (renameCorePolicy ρg policy).ruleLookup (renameCoreRuleId ρg id) =
      (policy.ruleLookup id).map (renameCoreRule ρg) := by
  exact lookupRuleDecl_rename ρg policy.rules id

private theorem lookupSubst_rename
    (ρg : Binding.GlobalRenaming) (subst : Support.Subst)
    (varId : Support.VarId) :
    Support.lookupSubst
        (subst.map fun entry =>
          (entry.1, renameResidualTerm ρg entry.2)) varId =
      (Support.lookupSubst subst varId).map
        (renameResidualTerm ρg) := by
  induction subst with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨key, value⟩ := entry
      simp only [List.map_cons, Support.lookupSubst]
      by_cases equal : key = varId <;> simp [equal, ih]

mutual
  private def CorePatRenamingSound (ρg : Binding.GlobalRenaming) :
      Support.Pat → Prop
    | .var _ => True
    | .num _ => True
    | .str _ => True
    | .con constructor .nil =>
        Binding.renameText ρg constructor.name = constructor.name
    | .con _ (.cons pattern rest) =>
        CorePatRenamingSound ρg pattern ∧
          CorePatsRenamingSound ρg rest
  private def CorePatsRenamingSound (ρg : Binding.GlobalRenaming) :
      Support.Pats → Prop
    | .nil => True
    | .cons pattern rest =>
        CorePatRenamingSound ρg pattern ∧
          CorePatsRenamingSound ρg rest
end

private def CoreAPatRenamingSound (ρg : Binding.GlobalRenaming)
    (pattern : Support.APat) : Prop :=
  CorePatsRenamingSound ρg pattern.args

mutual
  private theorem instPat_rename
      (ρg : Binding.GlobalRenaming) (subst : Support.Subst) :
      ∀ (pattern : Support.Pat), CorePatRenamingSound ρg pattern →
        Support.instPat
            (subst.map fun entry =>
              (entry.1, renameResidualTerm ρg entry.2)) pattern =
          (Support.instPat subst pattern).map
            (renameResidualTerm ρg) := by
    intro pattern fixed
    cases pattern with
    | var varId =>
        exact lookupSubst_rename ρg subst varId
    | num source => rfl
    | str source => rfl
    | con constructor patterns =>
        cases patterns with
        | nil =>
            have renamed := congrArg
              (fun name => some (Term.con name .nil)) fixed.symm
            simpa [Support.instPat, Support.instPats,
              renameResidualTerm] using renamed
        | cons pattern rest =>
            simp only [CorePatRenamingSound] at fixed
            simp only [Support.instPat, Support.instPats]
            rw [instPat_rename ρg subst pattern fixed.1,
              instPats_rename ρg subst rest fixed.2]
            cases Support.instPat subst pattern <;>
              cases Support.instPats subst rest <;> rfl
  private theorem instPats_rename
      (ρg : Binding.GlobalRenaming) (subst : Support.Subst) :
      ∀ (patterns : Support.Pats), CorePatsRenamingSound ρg patterns →
        Support.instPats
            (subst.map fun entry =>
              (entry.1, renameResidualTerm ρg entry.2)) patterns =
          (Support.instPats subst patterns).map
            (renameResidualTerms ρg) := by
    intro patterns fixed
    cases patterns with
    | nil => rfl
    | cons pattern rest =>
        simp only [CorePatsRenamingSound] at fixed
        simp only [Support.instPats]
        rw [instPat_rename ρg subst pattern fixed.1,
          instPats_rename ρg subst rest fixed.2]
        cases Support.instPat subst pattern <;>
          cases Support.instPats subst rest <;> rfl
end

private theorem instAPat_rename
    (ρg : Binding.GlobalRenaming) (subst : Support.Subst)
    (pattern : Support.APat) (fixed : CoreAPatRenamingSound ρg pattern) :
    Support.instAPat
        (subst.map fun entry =>
          (entry.1, renameResidualTerm ρg entry.2)) pattern =
      (Support.instAPat subst pattern).map
        (renameResidualAtom ρg) := by
  cases pattern
  simp only [Support.instAPat, CoreAPatRenamingSound] at fixed ⊢
  rw [instPats_rename ρg subst _ fixed]
  cases Support.instPats subst _ <;> rfl

private theorem instAPats_rename
    (ρg : Binding.GlobalRenaming) (subst : Support.Subst)
    (patterns : List Support.APat)
    (fixed : ∀ pattern ∈ patterns, CoreAPatRenamingSound ρg pattern) :
    Support.instAPats
        (subst.map fun entry =>
          (entry.1, renameResidualTerm ρg entry.2)) patterns =
      (Support.instAPats subst patterns).map
        (List.map (renameResidualAtom ρg)) := by
  induction patterns with
  | nil => rfl
  | cons pattern rest ih =>
      simp only [Support.instAPats]
      rw [instAPat_rename ρg subst pattern (fixed pattern (by simp)),
        ih (fun candidate member => fixed candidate (by simp [member]))]
      cases Support.instAPat subst pattern <;>
        cases Support.instAPats subst rest <;> rfl

private theorem lookupCon_fixed
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    {constructor : Support.ConSym} {declaration : Lara.Sigma.ConSig}
    (found : sigma.lookupCon constructor = some declaration) :
    Binding.renameText ρg constructor.name = constructor.name := by
  have member : declaration ∈ sigma.cons := by
    unfold Lara.Sigma.Sigma.lookupCon at found
    exact List.mem_of_find?_eq_some found
  have nameEq : declaration.sym = constructor := by
    unfold Lara.Sigma.Sigma.lookupCon at found
    have predicate := List.find?_some found
    simpa only [decide_eq_true_eq] using predicate
  simpa [nameEq] using sigmaSound declaration member

mutual
  private theorem corePatRenamingSound_of_check
      (sigmaSound : CoreSigmaRenamingSound ρg sigma) :
      ∀ {env expected pattern env'},
        Lara.Sigma.checkPat sigma env expected pattern = some env' →
        CorePatRenamingSound ρg pattern := by
    intro env expected pattern env' checked
    cases pattern with
    | var varId => trivial
    | num source => trivial
    | str source => trivial
    | con constructor patterns =>
        cases found : sigma.lookupCon constructor with
        | none =>
            simp [Lara.Sigma.checkPat, found] at checked
        | some declaration =>
            have constructorFixed := lookupCon_fixed sigmaSound found
            by_cases resultEq : declaration.result = expected
            · have patternsChecked : Lara.Sigma.checkPats sigma env
                  declaration.args patterns = some env' := by
                simpa [Lara.Sigma.checkPat, found, resultEq] using checked
              cases patterns with
              | nil => exact constructorFixed
              | cons pattern rest =>
                  exact corePatsRenamingSound_of_check sigmaSound
                    patternsChecked
            · simp [Lara.Sigma.checkPat, found, resultEq] at checked
  private theorem corePatsRenamingSound_of_check
      (sigmaSound : CoreSigmaRenamingSound ρg sigma) :
      ∀ {env expected patterns env'},
        Lara.Sigma.checkPats sigma env expected patterns = some env' →
        CorePatsRenamingSound ρg patterns := by
    intro env expected patterns env' checked
    cases patterns with
    | nil => trivial
    | cons pattern rest =>
        cases expected with
        | nil => simp [Lara.Sigma.checkPats] at checked
        | cons expected restExpected =>
            cases headFound : Lara.Sigma.checkPat sigma env expected pattern with
            | none =>
                simp [Lara.Sigma.checkPats, headFound] at checked
            | some next =>
                have tailFound : Lara.Sigma.checkPats sigma next restExpected rest =
                    some env' := by
                  simpa [Lara.Sigma.checkPats, headFound] using checked
                exact ⟨corePatRenamingSound_of_check sigmaSound headFound,
                  corePatsRenamingSound_of_check sigmaSound tailFound⟩
end

private theorem coreAPatRenamingSound_of_check
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    {env pattern env'}
    (checked : Lara.Sigma.checkAPat sigma env pattern = some env') :
    CoreAPatRenamingSound ρg pattern := by
  cases pattern with
  | mk predicate arguments =>
      cases found : sigma.lookupPred predicate with
      | none => simp [Lara.Sigma.checkAPat, found] at checked
      | some declaration =>
          apply corePatsRenamingSound_of_check sigmaSound
          simpa [Lara.Sigma.checkAPat, found] using checked

private theorem coreAPatsRenamingSound_of_check
    (sigmaSound : CoreSigmaRenamingSound ρg sigma) :
    ∀ {env patterns env'},
      Lara.Sigma.checkAPats sigma env patterns = some env' →
      ∀ pattern ∈ patterns, CoreAPatRenamingSound ρg pattern := by
  intro env patterns env' checked
  induction patterns generalizing env env' with
  | nil => simp
  | cons pattern rest ih =>
      cases headFound : Lara.Sigma.checkAPat sigma env pattern with
      | none => simp [Lara.Sigma.checkAPats, headFound] at checked
      | some next =>
          have tailFound : Lara.Sigma.checkAPats sigma next rest = some env' := by
            simpa [Lara.Sigma.checkAPats, headFound] using checked
          intro candidate member
          rcases List.mem_cons.mp member with rfl | member
          · exact coreAPatRenamingSound_of_check sigmaSound headFound
          · exact ih tailFound candidate member

private structure CoreRuleRenamingSound (ρg : Binding.GlobalRenaming)
    (rule : Support.Rule) : Prop where
  premises : ∀ pattern ∈ rule.premises,
    CoreAPatRenamingSound ρg pattern
  conclusion : CoreAPatRenamingSound ρg rule.concl
  answers : ∀ question ∈ rule.questions,
    CoreAPatRenamingSound ρg question.answer

private theorem coreRuleRenamingSound_of_sorted
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    {rule : Support.Rule} {env : Lara.Sigma.ParamSorts}
    (sorted : Lara.Sigma.ruleParamSorts sigma rule = some env) :
    CoreRuleRenamingSound ρg rule := by
  unfold Lara.Sigma.ruleParamSorts at sorted
  cases premisesFound : Lara.Sigma.checkAPats sigma [] rule.premises with
  | none => simp [premisesFound] at sorted
  | some afterPremises =>
      cases conclusionFound :
          Lara.Sigma.checkAPat sigma afterPremises rule.concl with
      | none => simp [premisesFound, conclusionFound] at sorted
      | some afterConclusion =>
          have answersFound : Lara.Sigma.checkAPats sigma afterConclusion
              (rule.questions.map (·.answer)) = some env := by
            simpa [premisesFound, conclusionFound] using sorted
          refine
            { premises := coreAPatsRenamingSound_of_check sigmaSound
                premisesFound
              conclusion := coreAPatRenamingSound_of_check sigmaSound
                conclusionFound
              answers := ?_ }
          intro question member
          apply coreAPatsRenamingSound_of_check sigmaSound answersFound
            question.answer
          exact List.mem_map.mpr ⟨question, member, rfl⟩

private theorem coreRuleRenamingSound_of_lookup
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    {ruleId : Support.RuleId} {rule : Support.Rule}
    (found : policy.ruleLookup ruleId = some rule) :
    CoreRuleRenamingSound ρg rule := by
  have ruleMember := Lara.Policy.lookupRuleDecl_some_mem found
  obtain ⟨declaration, declarationMember, _, declarationRule⟩ := ruleMember
  have allRules : policy.rules.all
      (fun declaration =>
        (Lara.Sigma.ruleParamSorts sigma declaration.rule).isSome) = true := by
    simp only [Lara.policyWellSorted, Bool.and_eq_true] at policySorted
    exact policySorted.1.1
  have checked := List.all_eq_true.mp allRules declaration declarationMember
  rw [declarationRule] at checked
  cases sorted : Lara.Sigma.ruleParamSorts sigma rule with
  | none => simp [sorted] at checked
  | some env => exact coreRuleRenamingSound_of_sorted sigmaSound sorted

@[simp] private theorem renameCoreSupportTerms_eq_map_support
    (ρg : Binding.GlobalRenaming) (terms : List Support.SupportTerm) :
    renameCoreSupportTerms ρg terms =
      terms.map (renameCoreSupportTerm ρg) := by
  induction terms <;> simp_all [renameCoreSupportTerms]

@[simp] private theorem renameCoreSupportDischarges_eq_map_support
    (ρg : Binding.GlobalRenaming)
    (discharges : List (Support.QuestionId × Support.SupportTerm)) :
    renameCoreSupportDischarges ρg discharges =
      discharges.map fun entry =>
        (renameCoreQuestionId ρg entry.1,
          renameCoreSupportTerm ρg entry.2) := by
  induction discharges with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨question, term⟩ := entry
      simp [renameCoreSupportDischarges, ih]

private theorem renameCoreSupportDischargeKeys
    (ρg : Binding.GlobalRenaming)
    (discharges : List (Support.QuestionId × Support.SupportTerm)) :
    (discharges.map fun entry =>
      (renameCoreQuestionId ρg entry.1,
        renameCoreSupportTerm ρg entry.2)).map Prod.fst =
      (discharges.map Prod.fst).map (renameCoreQuestionId ρg) := by
  induction discharges with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨question, term⟩ := entry
      simp [ih]

private theorem questionNames_renameCoreRule
    (ρg : Binding.GlobalRenaming) (rule : Support.Rule) :
    Support.questionNames (renameCoreRule ρg rule) =
      (Support.questionNames rule).map (renameCoreQuestionId ρg) := by
  simp [Support.questionNames, renameCoreRule]

private theorem mandatoryNames_renameCoreRule
    (ρg : Binding.GlobalRenaming) (rule : Support.Rule) :
    Support.mandatoryNames (renameCoreRule ρg rule) =
      (Support.mandatoryNames rule).map (renameCoreQuestionId ρg) := by
  cases rule with
  | mk mode params premises conclusion questions allowTrusted certifiers =>
      simp only [Support.mandatoryNames, renameCoreRule]
      induction questions with
      | nil => rfl
      | cons question rest ih =>
          cases question
          rename_i name answer mandatory
          cases mandatory <;> simp_all

private theorem memB_map_injective
    [DecidableEq α] [DecidableEq β] (f : α → β)
    (injective : Function.Injective f) (value : α) (values : List α) :
    Support.memB (f value) (values.map f) = Support.memB value values := by
  apply Bool.eq_iff_iff.mpr
  simp only [Support.memB_iff, List.mem_map]
  constructor
  · rintro ⟨source, member, equal⟩
    simpa [injective equal] using member
  · intro member
    exact ⟨value, member, rfl⟩

private theorem dedupQuestions_rename
    (ρg : Binding.GlobalRenaming) (questions : List Support.QuestionId) :
    Support.dedupQuestions
        (questions.map (renameCoreQuestionId ρg)) =
      (Support.dedupQuestions questions).map
        (renameCoreQuestionId ρg) := by
  induction questions with
  | nil => rfl
  | cons question rest ih =>
      simp only [List.map_cons, Support.dedupQuestions]
      rw [ih, memB_map_injective _
        (renameCoreQuestionId_injective_support ρg)]
      cases Support.memB question (Support.dedupQuestions rest) <;> rfl

private theorem flatten_map_map
    (f : α → β) (lists : List (List α)) :
    (lists.map (List.map f)).flatten = lists.flatten.map f := by
  induction lists with
  | nil => rfl
  | cons values rest ih =>
      simp only [List.map_cons, List.flatten_cons, List.map_append, ih]

private theorem unionAll_rename
    (ρg : Binding.GlobalRenaming)
    (obligations : List (List Support.QuestionId)) :
    Support.unionAll
        (obligations.map (List.map (renameCoreQuestionId ρg))) =
      (Support.unionAll obligations).map
        (renameCoreQuestionId ρg) := by
  change Support.dedupQuestions
      (obligations.map (List.map (renameCoreQuestionId ρg))).flatten =
    (Support.dedupQuestions obligations.flatten).map
      (renameCoreQuestionId ρg)
  rw [flatten_map_map, dedupQuestions_rename]

private theorem openMandatory_rename
    (ρg : Binding.GlobalRenaming) (rule : Support.Rule)
    (holes : List Support.QuestionId) :
    Support.openMandatory (renameCoreRule ρg rule)
        (holes.map (renameCoreQuestionId ρg)) =
      (Support.openMandatory rule holes).map
        (renameCoreQuestionId ρg) := by
  unfold Support.openMandatory
  rw [mandatoryNames_renameCoreRule]
  induction holes with
  | nil => rfl
  | cons hole rest ih =>
      simp only [List.map_cons, List.filter_cons]
      rw [memB_map_injective _
        (renameCoreQuestionId_injective_support ρg), ih]
      cases Support.memB hole (Support.mandatoryNames rule) <;> rfl

private theorem collectObligations_rename
    (ρg : Binding.GlobalRenaming)
    (premiseObligations dischargeObligations :
      List (List Support.QuestionId))
    (rule : Support.Rule) (holes : List Support.QuestionId) :
    Support.collectObligations
        (premiseObligations.map (List.map (renameCoreQuestionId ρg)))
        (dischargeObligations.map (List.map (renameCoreQuestionId ρg)))
        (renameCoreRule ρg rule)
        (holes.map (renameCoreQuestionId ρg)) =
      (Support.collectObligations premiseObligations dischargeObligations
        rule holes).map (renameCoreQuestionId ρg) := by
  unfold Support.collectObligations
  rw [openMandatory_rename]
  simpa [List.map_append] using unionAll_rename ρg
    (premiseObligations ++ dischargeObligations ++
      [Support.openMandatory rule holes])

private theorem certOkOf_rename_iff
    (envSound : EnvRenamingSound env ρg)
    (backend : Support.BackendId) (digest : Support.Digest)
    (certificate : Support.CertRef) (premises : List Atom)
    (conclusion : Atom) :
    Support.certOkOf env.registry backend digest
        (renameCoreCertRef ρg certificate)
        (premises.map (renameResidualAtom ρg))
        (renameResidualAtom ρg conclusion) ↔
      Support.certOkOf env.registry backend digest certificate
        premises conclusion := by
  constructor
  · intro accepted
    apply (Support.certOkBOf_iff env.registry backend digest certificate
      premises conclusion).mp
    rw [← envSound.registryReplay backend digest certificate premises conclusion]
    exact (Support.certOkBOf_iff env.registry backend digest
      (renameCoreCertRef ρg certificate)
      (premises.map (renameResidualAtom ρg))
      (renameResidualAtom ρg conclusion)).mpr accepted
  · intro accepted
    apply (Support.certOkBOf_iff env.registry backend digest
      (renameCoreCertRef ρg certificate)
      (premises.map (renameResidualAtom ρg))
      (renameResidualAtom ρg conclusion)).mp
    rw [envSound.registryReplay backend digest certificate premises conclusion]
    exact (Support.certOkBOf_iff env.registry backend digest certificate
      premises conclusion).mpr accepted

private theorem assuranceOk_rename_iff
    (envSound : EnvRenamingSound env ρg)
    (rule : Support.Rule) (premises : List Atom) (conclusion : Atom)
    (assurance : Support.Assurance) :
    Support.AssuranceOk (Support.certOkOf env.registry)
        (renameCoreRule ρg rule)
        (premises.map (renameResidualAtom ρg))
        (renameResidualAtom ρg conclusion)
        (renameCoreAssurance ρg assurance) ↔
      Support.AssuranceOk (Support.certOkOf env.registry)
        rule premises conclusion assurance := by
  constructor
  · intro accepted
    cases assurance with
    | none =>
        cases accepted with
        | defeasible mode => exact .defeasible mode
    | trusted =>
        cases accepted with
        | trusted mode allowed => exact .trusted mode allowed
    | cert backend digest certificate =>
        cases accepted with
        | cert mode allowed replay =>
            exact .cert mode allowed
              ((certOkOf_rename_iff envSound backend digest certificate
                premises conclusion).mp replay)
  · intro accepted
    cases accepted with
    | defeasible mode => exact .defeasible mode
    | trusted mode allowed => exact .trusted mode allowed
    | cert mode allowed replay =>
        exact .cert mode allowed
          ((certOkOf_rename_iff envSound _ _ _ premises conclusion).mpr replay)

private theorem instSide_rename
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    (envSound : EnvRenamingSound env ρg)
    {ruleId : Support.RuleId} {subst : Support.Subst}
    {rule : Support.Rule} {premises : List Support.SupportTerm}
    {discharges : List (Support.QuestionId × Support.SupportTerm)}
    {holes : List Support.QuestionId} {assurance : Support.Assurance}
    {patternAtoms premiseConclusions : List Atom}
    {premiseObligations : List (List Support.QuestionId)}
    {dischargeConclusions : List Atom}
    {dischargeObligations : List (List Support.QuestionId)}
    {conclusion : Atom}
    (side : Support.InstSide canon policy.ruleLookup
      (Support.certOkOf env.registry) ruleId subst rule premises discharges
      holes assurance patternAtoms premiseConclusions premiseObligations
      dischargeConclusions dischargeObligations conclusion) :
    Support.InstSide canon (renameCorePolicy ρg policy).ruleLookup
      (Support.certOkOf env.registry)
      (renameCoreRuleId ρg ruleId)
      (subst.map fun entry => (entry.1, renameResidualTerm ρg entry.2))
      (renameCoreRule ρg rule)
      (premises.map (renameCoreSupportTerm ρg))
      (discharges.map fun entry =>
        (renameCoreQuestionId ρg entry.1,
          renameCoreSupportTerm ρg entry.2))
      (holes.map (renameCoreQuestionId ρg))
      (renameCoreAssurance ρg assurance)
      (patternAtoms.map (renameResidualAtom ρg))
      (premiseConclusions.map (renameResidualAtom ρg))
      (premiseObligations.map (List.map (renameCoreQuestionId ρg)))
      (dischargeConclusions.map (renameResidualAtom ρg))
      (dischargeObligations.map (List.map (renameCoreQuestionId ρg)))
      (renameResidualAtom ρg conclusion) := by
  have ruleSound := coreRuleRenamingSound_of_lookup sigmaSound policySorted
    side.rule
  refine
    { rule := ?_
      θNodup := ?_
      θDom := ?_
      prems := ?_
      concl := ?_
      lenAs := by simp [side.lenAs]
      lenCs := by simp [side.lenCs]
      lenOs := by simp [side.lenOs]
      premEq := ?_
      lenDCs := by simp [side.lenDCs]
      lenDOs := by simp [side.lenDOs]
      ans := ?_
      qNodup := ?_
      dNodup := ?_
      hNodup := (nodup_map_iff_of_injective
        (renameCoreQuestionId_injective_support ρg)).mpr side.hNodup
      cover := ?_
      disj := ?_
      keysD := ?_
      keysH := ?_
      strictNoQ := ?_
      assur := (assuranceOk_rename_iff envSound rule patternAtoms
        conclusion assurance).mpr side.assur }
  · simp [ruleLookup_rename, side.rule]
  · simpa only [List.map_map, Function.comp_def] using side.θNodup
  · intro varId
    simpa only [renameCoreRule, List.map_map, Function.comp_def] using
      side.θDom varId
  · simpa [renameCoreRule] using
      (instAPats_rename ρg subst rule.premises ruleSound.premises).trans
        (congrArg (Option.map (List.map (renameResidualAtom ρg)))
          side.prems)
  · simpa [renameCoreRule] using
      (instAPat_rename ρg subst rule.concl ruleSound.conclusion).trans
        (congrArg (Option.map (renameResidualAtom ρg)) side.concl)
  · intro i renamedConclusion renamedPattern hConclusion hPattern
    rw [List.getElem?_map, Option.map_eq_some_iff] at hConclusion hPattern
    obtain ⟨sourceConclusion, sourceConclusionAt, conclusionEq⟩ := hConclusion
    obtain ⟨sourcePattern, sourcePatternAt, patternEq⟩ := hPattern
    subst renamedConclusion
    subst renamedPattern
    exact (admission_equiv_renameResidual canon ρg _ _).mpr
      (side.premEq i sourceConclusion sourcePattern sourceConclusionAt
        sourcePatternAt)
  · intro j renamedQuestion renamedTerm renamedConclusion hDischarge hConclusion
    rw [List.getElem?_map, Option.map_eq_some_iff] at hDischarge hConclusion
    obtain ⟨sourceDischarge, sourceDischargeAt, dischargeEq⟩ := hDischarge
    obtain ⟨sourceConclusion, sourceConclusionAt, conclusionEq⟩ := hConclusion
    rcases sourceDischarge with ⟨sourceQuestion, sourceTerm⟩
    simp only [Prod.mk.injEq] at dischargeEq
    rw [← dischargeEq.1, ← conclusionEq]
    obtain ⟨question, questionMember, questionName, answer,
      answerInstantiated, equivalent⟩ :=
        side.ans j sourceQuestion sourceTerm sourceConclusion sourceDischargeAt
          sourceConclusionAt
    refine ⟨{ question with
        name := renameCoreQuestionId ρg question.name }, ?_, ?_,
      renameResidualAtom ρg answer, ?_, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨question, questionMember, rfl⟩
    · simpa [questionName]
    · simpa using
        (instAPat_rename ρg subst question.answer
          (ruleSound.answers question questionMember)).trans
          (congrArg (Option.map (renameResidualAtom ρg)) answerInstantiated)
    · exact (admission_equiv_renameResidual canon ρg _ _).mpr equivalent
  · rw [questionNames_renameCoreRule]
    exact (nodup_map_iff_of_injective
      (renameCoreQuestionId_injective_support ρg)).mpr side.qNodup
  · rw [renameCoreSupportDischargeKeys]
    exact (nodup_map_iff_of_injective
      (renameCoreQuestionId_injective_support ρg)).mpr side.dNodup
  · rw [renameCoreSupportDischargeKeys]
    intro renamedQuestion renamedMember
    simp only [renameCoreRule, List.mem_map] at renamedMember
    obtain ⟨question, questionMember, questionEq⟩ := renamedMember
    subst renamedQuestion
    rcases side.cover question questionMember with discharged | opened
    · exact Or.inl (List.mem_map.mpr
        ⟨question.name, discharged, rfl⟩)
    · exact Or.inr (List.mem_map.mpr
        ⟨question.name, opened, rfl⟩)
  · intro renamedQuestion discharged opened
    rw [renameCoreSupportDischargeKeys] at discharged
    obtain ⟨sourceQuestion, sourceDischarged, questionEq⟩ :=
      List.mem_map.mp discharged
    obtain ⟨sourceOpen, sourceOpenMember, openEq⟩ := List.mem_map.mp opened
    have same : sourceQuestion = sourceOpen :=
      renameCoreQuestionId_injective_support ρg (questionEq.trans openEq.symm)
    exact side.disj sourceQuestion sourceDischarged (same ▸ sourceOpenMember)
  · intro renamedQuestion discharged
    rw [renameCoreSupportDischargeKeys] at discharged
    obtain ⟨sourceQuestion, sourceDischarged, questionEq⟩ :=
      List.mem_map.mp discharged
    subst renamedQuestion
    rw [questionNames_renameCoreRule]
    exact List.mem_map.mpr ⟨sourceQuestion,
      side.keysD sourceQuestion sourceDischarged, rfl⟩
  · intro renamedQuestion opened
    obtain ⟨sourceQuestion, sourceOpen, questionEq⟩ := List.mem_map.mp opened
    subst renamedQuestion
    rw [questionNames_renameCoreRule]
    exact List.mem_map.mpr ⟨sourceQuestion,
      side.keysH sourceQuestion sourceOpen, rfl⟩
  · intro strict
    obtain ⟨dischargesEmpty, holesEmpty⟩ := side.strictNoQ strict
    simp [dischargesEmpty, holesEmpty]

private theorem hasSupport_rename
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    (envSound : EnvRenamingSound env ρg)
    {gamma : Support.LeafId → Option Atom}
    {term : Support.SupportTerm} {conclusion : Atom}
    {obligations : List Support.QuestionId}
    (derivation : Support.HasSupport canon policy.ruleLookup gamma
      (Support.certOkOf env.registry) term conclusion obligations) :
    Support.HasSupport canon (renameCorePolicy ρg policy).ruleLookup
      (renameGamma ρg gamma) (Support.certOkOf env.registry)
      (renameCoreSupportTerm ρg term) (renameResidualAtom ρg conclusion)
      (obligations.map (renameCoreQuestionId ρg)) := by
  induction derivation with
  | leaf declared =>
      apply Support.HasSupport.leaf
      rw [renameGamma_image, declared]
      rfl
  | @inst ruleId subst premises discharges holes assurance rule patternAtoms
      premiseConclusions premiseObligations dischargeConclusions
      dischargeObligations conclusion side premiseDerivations
      dischargeDerivations premiseIhs dischargeIhs =>
      have renamedSide := instSide_rename sigmaSound policySorted envSound side
      have built := Support.HasSupport.inst
        (Gamma := renameGamma ρg gamma) renamedSide (by
        intro i renamedTerm renamedConclusion renamedObligations termAt
          conclusionAt obligationsAt
        rw [List.getElem?_map, Option.map_eq_some_iff] at termAt
        rw [List.getElem?_map, Option.map_eq_some_iff] at conclusionAt
        rw [List.getElem?_map, Option.map_eq_some_iff] at obligationsAt
        obtain ⟨sourceTerm, sourceTermAt, termEq⟩ := termAt
        obtain ⟨sourceConclusion, sourceConclusionAt, conclusionEq⟩ :=
          conclusionAt
        obtain ⟨sourceObligations, sourceObligationsAt, obligationsEq⟩ :=
          obligationsAt
        subst renamedTerm
        subst renamedConclusion
        subst renamedObligations
        exact premiseIhs i sourceTerm sourceConclusion sourceObligations
          sourceTermAt sourceConclusionAt sourceObligationsAt) (by
        intro j renamedQuestion renamedTerm renamedConclusion
          renamedObligations dischargeAt conclusionAt obligationsAt
        rw [List.getElem?_map, Option.map_eq_some_iff] at dischargeAt
        rw [List.getElem?_map, Option.map_eq_some_iff] at conclusionAt
        rw [List.getElem?_map, Option.map_eq_some_iff] at obligationsAt
        obtain ⟨sourceDischarge, sourceDischargeAt, dischargeEq⟩ := dischargeAt
        obtain ⟨sourceConclusion, sourceConclusionAt, conclusionEq⟩ :=
          conclusionAt
        obtain ⟨sourceObligations, sourceObligationsAt, obligationsEq⟩ :=
          obligationsAt
        rcases sourceDischarge with ⟨sourceQuestion, sourceTerm⟩
        simp only [Prod.mk.injEq] at dischargeEq
        rw [← dischargeEq.2, ← conclusionEq,
          ← obligationsEq]
        exact dischargeIhs j sourceQuestion sourceTerm sourceConclusion
          sourceObligations sourceDischargeAt sourceConclusionAt
          sourceObligationsAt)
      simpa [renameCoreSupportTerm, collectObligations_rename] using built

private theorem instSide_reflect
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    (envSound : EnvRenamingSound env ρg)
    {ruleId : Support.RuleId} {subst : Support.Subst}
    {rule : Support.Rule} {premises : List Support.SupportTerm}
    {discharges : List (Support.QuestionId × Support.SupportTerm)}
    {holes : List Support.QuestionId} {assurance : Support.Assurance}
    {patternAtoms premiseConclusions : List Atom}
    {premiseObligations : List (List Support.QuestionId)}
    {dischargeConclusions : List Atom}
    {dischargeObligations : List (List Support.QuestionId)}
    {conclusion : Atom}
    (side : Support.InstSide canon (renameCorePolicy ρg policy).ruleLookup
      (Support.certOkOf env.registry)
      (renameCoreRuleId ρg ruleId)
      (subst.map fun entry => (entry.1, renameResidualTerm ρg entry.2))
      (renameCoreRule ρg rule)
      (premises.map (renameCoreSupportTerm ρg))
      (discharges.map fun entry =>
        (renameCoreQuestionId ρg entry.1,
          renameCoreSupportTerm ρg entry.2))
      (holes.map (renameCoreQuestionId ρg))
      (renameCoreAssurance ρg assurance)
      (patternAtoms.map (renameResidualAtom ρg))
      (premiseConclusions.map (renameResidualAtom ρg))
      (premiseObligations.map (List.map (renameCoreQuestionId ρg)))
      (dischargeConclusions.map (renameResidualAtom ρg))
      (dischargeObligations.map (List.map (renameCoreQuestionId ρg)))
      (renameResidualAtom ρg conclusion)) :
    Support.InstSide canon policy.ruleLookup
      (Support.certOkOf env.registry) ruleId subst rule premises discharges
      holes assurance patternAtoms premiseConclusions premiseObligations
      dischargeConclusions dischargeObligations conclusion := by
  have sourceRule : policy.ruleLookup ruleId = some rule := by
    have mappedRule := side.rule
    rw [ruleLookup_rename] at mappedRule
    cases found : policy.ruleLookup ruleId with
    | none => simp [found] at mappedRule
    | some foundRule =>
        simp only [found, Option.map_some, Option.some.injEq] at mappedRule
        have same := renameCoreRule_injective ρg mappedRule
        simpa [same] using found
  have ruleSound := coreRuleRenamingSound_of_lookup sigmaSound policySorted
    sourceRule
  refine
    { rule := sourceRule
      θNodup := ?_
      θDom := ?_
      prems := ?_
      concl := ?_
      lenAs := by simpa using side.lenAs
      lenCs := by simpa using side.lenCs
      lenOs := by simpa using side.lenOs
      premEq := ?_
      lenDCs := by simpa using side.lenDCs
      lenDOs := by simpa using side.lenDOs
      ans := ?_
      qNodup := ?_
      dNodup := ?_
      hNodup := ?_
      cover := ?_
      disj := ?_
      keysD := ?_
      keysH := ?_
      strictNoQ := ?_
      assur := (assuranceOk_rename_iff envSound rule patternAtoms
        conclusion assurance).mp side.assur }
  · simpa only [List.map_map, Function.comp_def] using side.θNodup
  · intro varId
    simpa only [renameCoreRule, List.map_map, Function.comp_def] using
      side.θDom varId
  · apply optionMap_injective_support
      (listMap_injective_support (admission_residualAtom_injective ρg))
    calc
      Option.map (List.map (renameResidualAtom ρg))
          (Support.instAPats subst rule.premises) =
          Support.instAPats
            (subst.map fun entry =>
              (entry.1, renameResidualTerm ρg entry.2)) rule.premises :=
        (instAPats_rename ρg subst rule.premises ruleSound.premises).symm
      _ = some (patternAtoms.map (renameResidualAtom ρg)) := by
        simpa [renameCoreRule] using side.prems
      _ = Option.map (List.map (renameResidualAtom ρg))
          (some patternAtoms) := rfl
  · apply optionMap_injective_support (admission_residualAtom_injective ρg)
    calc
      Option.map (renameResidualAtom ρg)
          (Support.instAPat subst rule.concl) =
          Support.instAPat
            (subst.map fun entry =>
              (entry.1, renameResidualTerm ρg entry.2)) rule.concl :=
        (instAPat_rename ρg subst rule.concl ruleSound.conclusion).symm
      _ = some (renameResidualAtom ρg conclusion) := by
        simpa [renameCoreRule] using side.concl
      _ = Option.map (renameResidualAtom ρg) (some conclusion) := rfl
  · intro i sourceConclusion sourcePattern conclusionAt patternAt
    have renamedConclusionAt :
        (premiseConclusions.map (renameResidualAtom ρg))[i]? =
          some (renameResidualAtom ρg sourceConclusion) := by
      rw [List.getElem?_map, conclusionAt]
      rfl
    have renamedPatternAt :
        (patternAtoms.map (renameResidualAtom ρg))[i]? =
          some (renameResidualAtom ρg sourcePattern) := by
      rw [List.getElem?_map, patternAt]
      rfl
    exact (admission_equiv_renameResidual canon ρg _ _).mp
      (side.premEq i _ _ renamedConclusionAt renamedPatternAt)
  · intro j sourceQuestion sourceTerm sourceConclusion dischargeAt conclusionAt
    have renamedDischargeAt :
        (discharges.map fun entry =>
          (renameCoreQuestionId ρg entry.1,
            renameCoreSupportTerm ρg entry.2))[j]? =
          some (renameCoreQuestionId ρg sourceQuestion,
            renameCoreSupportTerm ρg sourceTerm) := by
      rw [List.getElem?_map, dischargeAt]
      rfl
    have renamedConclusionAt :
        (dischargeConclusions.map (renameResidualAtom ρg))[j]? =
          some (renameResidualAtom ρg sourceConclusion) := by
      rw [List.getElem?_map, conclusionAt]
      rfl
    obtain ⟨renamedQuestion, renamedQuestionMember, renamedQuestionName,
      renamedAnswer, renamedAnswerInstantiated, renamedEquivalent⟩ :=
        side.ans j (renameCoreQuestionId ρg sourceQuestion)
          (renameCoreSupportTerm ρg sourceTerm)
          (renameResidualAtom ρg sourceConclusion) renamedDischargeAt
          renamedConclusionAt
    simp only [renameCoreRule, List.mem_map] at renamedQuestionMember
    obtain ⟨question, questionMember, questionEq⟩ := renamedQuestionMember
    subst renamedQuestion
    have questionName : question.name = sourceQuestion :=
      renameCoreQuestionId_injective_support ρg renamedQuestionName
    cases answerFound : Support.instAPat subst question.answer with
    | none =>
        have impossible := instAPat_rename ρg subst question.answer
          (ruleSound.answers question questionMember)
        rw [answerFound] at impossible
        simp [impossible] at renamedAnswerInstantiated
    | some answer =>
        have answerEq : renameResidualAtom ρg answer = renamedAnswer := by
          have commutes := instAPat_rename ρg subst question.answer
            (ruleSound.answers question questionMember)
          rw [answerFound] at commutes
          simpa [commutes] using renamedAnswerInstantiated
        refine ⟨question, questionMember, questionName, answer, answerFound, ?_⟩
        rw [← answerEq] at renamedEquivalent
        exact (admission_equiv_renameResidual canon ρg _ _).mp
          renamedEquivalent
  · have targetNodup := side.qNodup
    rw [questionNames_renameCoreRule] at targetNodup
    exact (nodup_map_iff_of_injective
      (renameCoreQuestionId_injective_support ρg)).mp targetNodup
  · have targetNodup := side.dNodup
    rw [renameCoreSupportDischargeKeys] at targetNodup
    exact (nodup_map_iff_of_injective
      (renameCoreQuestionId_injective_support ρg)).mp targetNodup
  · exact (nodup_map_iff_of_injective
      (renameCoreQuestionId_injective_support ρg)).mp side.hNodup
  · intro question questionMember
    have renamedMember :
        { question with name := renameCoreQuestionId ρg question.name } ∈
          (renameCoreRule ρg rule).questions := by
      apply List.mem_map.mpr
      exact ⟨question, questionMember, rfl⟩
    have targetCover := side.cover _ renamedMember
    rw [renameCoreSupportDischargeKeys] at targetCover
    rcases targetCover with discharged | opened
    · obtain ⟨sourceQuestion, sourceMember, equal⟩ := List.mem_map.mp discharged
      have same : sourceQuestion = question.name :=
        renameCoreQuestionId_injective_support ρg equal
      exact Or.inl (same ▸ sourceMember)
    · obtain ⟨sourceQuestion, sourceMember, equal⟩ := List.mem_map.mp opened
      have same : sourceQuestion = question.name :=
        renameCoreQuestionId_injective_support ρg equal
      exact Or.inr (same ▸ sourceMember)
  · intro question discharged opened
    have targetDischarged : renameCoreQuestionId ρg question ∈
        (discharges.map fun entry =>
          (renameCoreQuestionId ρg entry.1,
            renameCoreSupportTerm ρg entry.2)).map Prod.fst := by
      rw [renameCoreSupportDischargeKeys]
      exact List.mem_map.mpr ⟨question, discharged, rfl⟩
    exact side.disj (renameCoreQuestionId ρg question) targetDischarged
      (List.mem_map.mpr ⟨question, opened, rfl⟩)
  · intro question discharged
    have targetDischarged : renameCoreQuestionId ρg question ∈
        (discharges.map fun entry =>
          (renameCoreQuestionId ρg entry.1,
            renameCoreSupportTerm ρg entry.2)).map Prod.fst := by
      rw [renameCoreSupportDischargeKeys]
      exact List.mem_map.mpr ⟨question, discharged, rfl⟩
    have target := side.keysD (renameCoreQuestionId ρg question)
      targetDischarged
    rw [questionNames_renameCoreRule] at target
    obtain ⟨sourceQuestion, sourceMember, equal⟩ := List.mem_map.mp target
    exact (renameCoreQuestionId_injective_support ρg equal) ▸ sourceMember
  · intro question opened
    have target := side.keysH (renameCoreQuestionId ρg question)
      (List.mem_map.mpr ⟨question, opened, rfl⟩)
    rw [questionNames_renameCoreRule] at target
    obtain ⟨sourceQuestion, sourceMember, equal⟩ := List.mem_map.mp target
    exact (renameCoreQuestionId_injective_support ρg equal) ▸ sourceMember
  · intro strict
    have targetStrict : (renameCoreRule ρg rule).mode = .strict := by
      simpa [renameCoreRule] using strict
    obtain ⟨dischargesEmpty, holesEmpty⟩ := side.strictNoQ targetStrict
    have sourceDischargesEmpty : discharges = [] := by
      cases discharges <;> simp_all
    have sourceHolesEmpty : holes = [] := by
      cases holes <;> simp_all
    exact ⟨sourceDischargesEmpty, sourceHolesEmpty⟩

private theorem reflectSupportData
    (ρg : Binding.GlobalRenaming)
    {policy : Lara.Policy.Policy}
    {gamma : Support.LeafId → Option Atom}
    {certOk : Support.BackendId → Support.Digest → Support.CertRef →
      List Atom → Atom → Prop}
    {sourceEntries : List α} (termOf : α → Support.SupportTerm)
    {targetConclusions : List Atom}
    {targetObligations : List (List Support.QuestionId)}
    (conclusionLength : targetConclusions.length = sourceEntries.length)
    (obligationLength : targetObligations.length = sourceEntries.length)
    (children : ∀ (i : Nat) (entry : α) (targetConclusion : Atom)
      (targetObligation : List Support.QuestionId),
      sourceEntries[i]? = some entry →
      targetConclusions[i]? = some targetConclusion →
      targetObligations[i]? = some targetObligation →
      ∃ sourceConclusion : Atom,
      ∃ sourceObligation : List Support.QuestionId,
        targetConclusion = renameResidualAtom ρg sourceConclusion ∧
        targetObligation =
          sourceObligation.map (renameCoreQuestionId ρg) ∧
        Support.HasSupport canon policy.ruleLookup gamma certOk
          (termOf entry) sourceConclusion sourceObligation) :
    ∃ sourceConclusions : List Atom,
    ∃ sourceObligations : List (List Support.QuestionId),
      targetConclusions =
        sourceConclusions.map (renameResidualAtom ρg) ∧
      targetObligations =
        sourceObligations.map (List.map (renameCoreQuestionId ρg)) ∧
      sourceConclusions.length = sourceEntries.length ∧
      sourceObligations.length = sourceEntries.length ∧
      ∀ (i : Nat) (entry : α) (sourceConclusion : Atom)
        (sourceObligation : List Support.QuestionId),
        sourceEntries[i]? = some entry →
        sourceConclusions[i]? = some sourceConclusion →
        sourceObligations[i]? = some sourceObligation →
        Support.HasSupport canon policy.ruleLookup gamma certOk
          (termOf entry) sourceConclusion sourceObligation := by
  induction sourceEntries generalizing targetConclusions targetObligations with
  | nil =>
      have conclusionsEmpty : targetConclusions = [] := by
        cases targetConclusions <;> simp_all
      have obligationsEmpty : targetObligations = [] := by
        cases targetObligations <;> simp_all
      subst targetConclusions
      subst targetObligations
      exact ⟨[], [], rfl, rfl, rfl, rfl, by simp⟩
  | cons entry rest ih =>
      cases targetConclusions with
      | nil => simp at conclusionLength
      | cons targetConclusion targetConclusionRest =>
          cases targetObligations with
          | nil => simp at obligationLength
          | cons targetObligation targetObligationRest =>
              have head := children 0 entry targetConclusion targetObligation
                (by simp) (by simp) (by simp)
              obtain ⟨sourceConclusion, sourceObligation, conclusionEq,
                obligationEq, sourceDerivation⟩ := head
              have tailChildren : ∀ (i : Nat) (tailEntry : α)
                  (tailConclusion : Atom)
                  (tailObligation : List Support.QuestionId),
                  rest[i]? = some tailEntry →
                  targetConclusionRest[i]? = some tailConclusion →
                  targetObligationRest[i]? = some tailObligation →
                  ∃ sourceConclusion : Atom,
                  ∃ sourceObligation : List Support.QuestionId,
                    tailConclusion =
                      renameResidualAtom ρg sourceConclusion ∧
                    tailObligation = sourceObligation.map
                      (renameCoreQuestionId ρg) ∧
                    Support.HasSupport canon policy.ruleLookup gamma certOk
                      (termOf tailEntry) sourceConclusion
                      sourceObligation := by
                intro i tailEntry tailConclusion tailObligation entryAt
                  conclusionAt obligationAt
                exact children (i + 1) tailEntry tailConclusion tailObligation
                  (by simpa using entryAt) (by simpa using conclusionAt)
                  (by simpa using obligationAt)
              obtain ⟨sourceConclusionRest, sourceObligationRest,
                conclusionsEq, obligationsEq, sourceConclusionLength,
                sourceObligationLength, tailDerivations⟩ :=
                  ih (by simpa using conclusionLength)
                    (by simpa using obligationLength) tailChildren
              refine ⟨sourceConclusion :: sourceConclusionRest,
                sourceObligation :: sourceObligationRest, ?_, ?_, ?_, ?_, ?_⟩
              · simp [conclusionEq, conclusionsEq]
              · simp [obligationEq, obligationsEq]
              · simp [sourceConclusionLength]
              · simp [sourceObligationLength]
              · intro i foundEntry foundConclusion foundObligation entryAt
                  conclusionAt obligationAt
                cases i with
                | zero =>
                    simp only [List.getElem?_cons_zero,
                      Option.some.injEq] at entryAt conclusionAt obligationAt
                    subst foundEntry
                    subst foundConclusion
                    subst foundObligation
                    exact sourceDerivation
                | succ i =>
                    simp only [List.getElem?_cons_succ] at entryAt
                    simp only [List.getElem?_cons_succ] at conclusionAt
                    simp only [List.getElem?_cons_succ] at obligationAt
                    exact tailDerivations i foundEntry foundConclusion
                      foundObligation entryAt conclusionAt obligationAt

private theorem hasSupport_reflect_exists
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    (envSound : EnvRenamingSound env ρg)
    {gamma : Support.LeafId → Option Atom}
    {targetTerm : Support.SupportTerm} {targetConclusion : Atom}
    {targetObligations : List Support.QuestionId}
    (derivation : Support.HasSupport canon
      (renameCorePolicy ρg policy).ruleLookup (renameGamma ρg gamma)
      (Support.certOkOf env.registry) targetTerm targetConclusion
      targetObligations) :
    ∀ sourceTerm, renameCoreSupportTerm ρg sourceTerm = targetTerm →
      ∃ sourceConclusion sourceObligations,
        targetConclusion = renameResidualAtom ρg sourceConclusion ∧
        targetObligations =
          sourceObligations.map (renameCoreQuestionId ρg) ∧
        Support.HasSupport canon policy.ruleLookup gamma
          (Support.certOkOf env.registry) sourceTerm sourceConclusion
          sourceObligations := by
  induction derivation with
  | leaf declared =>
      intro sourceTerm termEq
      cases sourceTerm with
      | leaf sourceLeaf =>
          simp only [renameCoreSupportTerm,
            Support.SupportTerm.leaf.injEq] at termEq
          rw [← termEq, renameGamma_image] at declared
          cases sourceFound : gamma sourceLeaf with
          | none => simp [sourceFound] at declared
          | some sourceConclusion =>
              simp only [sourceFound, Option.map_some,
                Option.some.injEq] at declared
              refine ⟨sourceConclusion, [], declared.symm, rfl, ?_⟩
              exact .leaf sourceFound
      | inst ruleId subst premises discharges holes assurance =>
          simp [renameCoreSupportTerm] at termEq
  | @inst ruleId subst premises discharges holes assurance rule patternAtoms
      premiseConclusions premiseObligations dischargeConclusions
      dischargeObligations conclusion side premiseDerivations
      dischargeDerivations premiseIhs dischargeIhs =>
      intro sourceTerm termEq
      cases sourceTerm with
      | leaf sourceLeaf => simp [renameCoreSupportTerm] at termEq
      | inst sourceRuleId sourceSubst sourcePremises sourceDischarges
          sourceHoles sourceAssurance =>
          simp only [renameCoreSupportTerm,
            Support.SupportTerm.inst.injEq] at termEq
          rcases termEq with ⟨ruleIdEq, substEq, premisesEq, dischargesEq,
            holesEq, assuranceEq⟩
          subst ruleId
          subst subst
          subst premises
          subst discharges
          subst holes
          subst assurance
          have sourceRuleExists : ∃ sourceRule,
              policy.ruleLookup sourceRuleId = some sourceRule := by
            have targetFound := side.rule
            rw [ruleLookup_rename] at targetFound
            cases sourceFound : policy.ruleLookup sourceRuleId with
            | none => simp [sourceFound] at targetFound
            | some sourceRule => exact ⟨sourceRule, rfl⟩
          let sourceRule := Classical.choose sourceRuleExists
          have sourceRuleFound :
              policy.ruleLookup sourceRuleId = some sourceRule :=
            Classical.choose_spec sourceRuleExists
          have targetRuleEq : rule = renameCoreRule ρg sourceRule := by
            have targetFound := side.rule
            rw [ruleLookup_rename, sourceRuleFound] at targetFound
            exact Option.some.inj targetFound.symm
          subst rule
          have sourceRuleSound := coreRuleRenamingSound_of_lookup sigmaSound
            policySorted sourceRuleFound
          cases sourcePatternsFound :
              Support.instAPats sourceSubst sourceRule.premises with
          | none =>
              have commutes := instAPats_rename ρg sourceSubst
                sourceRule.premises sourceRuleSound.premises
              rw [sourcePatternsFound] at commutes
              have impossible := side.prems
              simp [renameCoreRule, commutes] at impossible
          | some sourcePatternAtoms =>
              have patternAtomsEq : patternAtoms =
                  sourcePatternAtoms.map (renameResidualAtom ρg) := by
                have commutes := instAPats_rename ρg sourceSubst
                  sourceRule.premises sourceRuleSound.premises
                rw [sourcePatternsFound] at commutes
                have target := side.prems
                have equal : sourcePatternAtoms.map
                    (renameResidualAtom ρg) = patternAtoms := by
                  simpa [renameCoreRule, commutes] using target
                exact equal.symm
              subst patternAtoms
              cases sourceConclusionFound :
                  Support.instAPat sourceSubst sourceRule.concl with
              | none =>
                  have commutes := instAPat_rename ρg sourceSubst
                    sourceRule.concl sourceRuleSound.conclusion
                  rw [sourceConclusionFound] at commutes
                  have impossible := side.concl
                  simp [renameCoreRule, commutes] at impossible
              | some sourceConclusion =>
                  have conclusionEq : conclusion =
                      renameResidualAtom ρg sourceConclusion := by
                    have commutes := instAPat_rename ρg sourceSubst
                      sourceRule.concl sourceRuleSound.conclusion
                    rw [sourceConclusionFound] at commutes
                    have target := side.concl
                    have equal : renameResidualAtom ρg sourceConclusion =
                        conclusion := by
                      simpa [renameCoreRule, commutes] using target
                    exact equal.symm
                  subst conclusion
                  have premiseConclusionLength :
                      premiseConclusions.length = sourcePremises.length := by
                    simpa [renameCoreSupportTerms_eq_map_support] using
                      side.lenCs
                  have premiseObligationLength :
                      premiseObligations.length = sourcePremises.length := by
                    simpa [renameCoreSupportTerms_eq_map_support] using
                      side.lenOs
                  obtain ⟨sourcePremiseConclusions,
                    sourcePremiseObligations, premiseConclusionsEq,
                    premiseObligationsEq, sourcePremiseConclusionLength,
                    sourcePremiseObligationLength,
                    sourcePremiseDerivations⟩ :=
                      reflectSupportData ρg (policy := policy)
                        (gamma := gamma)
                        (certOk := Support.certOkOf env.registry)
                        (sourceEntries := sourcePremises) id
                        premiseConclusionLength premiseObligationLength (by
                          intro i sourceTerm targetConclusion targetObligation
                            sourceTermAt targetConclusionAt targetObligationAt
                          have targetTermAt :
                              (renameCoreSupportTerms ρg sourcePremises)[i]? =
                                some (renameCoreSupportTerm ρg sourceTerm) := by
                            rw [renameCoreSupportTerms_eq_map_support,
                              List.getElem?_map, sourceTermAt]
                            rfl
                          exact premiseIhs i
                            (renameCoreSupportTerm ρg sourceTerm)
                            targetConclusion targetObligation targetTermAt
                            targetConclusionAt targetObligationAt sourceTerm
                            rfl)
                  have dischargeConclusionLength :
                      dischargeConclusions.length = sourceDischarges.length := by
                    simpa [renameCoreSupportDischarges_eq_map_support] using
                      side.lenDCs
                  have dischargeObligationLength :
                      dischargeObligations.length = sourceDischarges.length := by
                    simpa [renameCoreSupportDischarges_eq_map_support] using
                      side.lenDOs
                  obtain ⟨sourceDischargeConclusions,
                    sourceDischargeObligations, dischargeConclusionsEq,
                    dischargeObligationsEq, sourceDischargeConclusionLength,
                    sourceDischargeObligationLength,
                    sourceDischargeDerivations⟩ :=
                      reflectSupportData ρg (policy := policy)
                        (gamma := gamma)
                        (certOk := Support.certOkOf env.registry)
                        (sourceEntries := sourceDischarges) Prod.snd
                        dischargeConclusionLength dischargeObligationLength (by
                          intro i sourceDischarge targetConclusion
                            targetObligation sourceDischargeAt
                            targetConclusionAt targetObligationAt
                          rcases sourceDischarge with ⟨sourceQuestion, sourceTerm⟩
                          have targetDischargeAt :
                              (renameCoreSupportDischarges ρg
                                sourceDischarges)[i]? =
                                some (renameCoreQuestionId ρg sourceQuestion,
                                  renameCoreSupportTerm ρg sourceTerm) := by
                            rw [renameCoreSupportDischarges_eq_map_support,
                              List.getElem?_map, sourceDischargeAt]
                            rfl
                          exact dischargeIhs i
                            (renameCoreQuestionId ρg sourceQuestion)
                            (renameCoreSupportTerm ρg sourceTerm)
                            targetConclusion targetObligation targetDischargeAt
                            targetConclusionAt targetObligationAt sourceTerm
                            rfl)
                  subst premiseConclusions
                  subst premiseObligations
                  subst dischargeConclusions
                  subst dischargeObligations
                  have sourceSide : Support.InstSide canon policy.ruleLookup
                      (Support.certOkOf env.registry) sourceRuleId sourceSubst
                      sourceRule sourcePremises sourceDischarges sourceHoles
                      sourceAssurance sourcePatternAtoms
                      sourcePremiseConclusions sourcePremiseObligations
                      sourceDischargeConclusions sourceDischargeObligations
                      sourceConclusion := by
                    apply instSide_reflect sigmaSound policySorted envSound
                    simpa [renameCoreSupportTerms_eq_map_support,
                      renameCoreSupportDischarges_eq_map_support] using side
                  have sourceDerivation := Support.HasSupport.inst sourceSide
                    sourcePremiseDerivations (by
                      intro j question term resultConclusion resultObligations
                        dischargeAt conclusionAt obligationsAt
                      exact sourceDischargeDerivations j (question, term)
                        resultConclusion resultObligations dischargeAt
                        conclusionAt obligationsAt)
                  refine ⟨sourceConclusion,
                    Support.collectObligations sourcePremiseObligations
                      sourceDischargeObligations sourceRule sourceHoles,
                    rfl, ?_, sourceDerivation⟩
                  exact collectObligations_rename ρg sourcePremiseObligations
                    sourceDischargeObligations sourceRule sourceHoles

private theorem hasSupport_reflect
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    (envSound : EnvRenamingSound env ρg)
    {gamma : Support.LeafId → Option Atom}
    {term : Support.SupportTerm} {conclusion : Atom}
    {obligations : List Support.QuestionId}
    (derivation : Support.HasSupport canon
      (renameCorePolicy ρg policy).ruleLookup (renameGamma ρg gamma)
      (Support.certOkOf env.registry) (renameCoreSupportTerm ρg term)
      (renameResidualAtom ρg conclusion)
      (obligations.map (renameCoreQuestionId ρg))) :
    Support.HasSupport canon policy.ruleLookup gamma
      (Support.certOkOf env.registry) term conclusion obligations := by
  obtain ⟨sourceConclusion, sourceObligations, conclusionEq, obligationsEq,
    sourceDerivation⟩ :=
      hasSupport_reflect_exists sigmaSound policySorted envSound derivation
        term rfl
  have sourceConclusionEq : conclusion = sourceConclusion :=
    admission_residualAtom_injective ρg conclusionEq
  have sourceObligationsEq : obligations = sourceObligations :=
    listMap_injective_support (renameCoreQuestionId_injective_support ρg)
      obligationsEq
  simpa [sourceConclusionEq, sourceObligationsEq] using sourceDerivation

/-- Core support derivations transport forward and reflect through a typed
global renaming.  Policy well-sortedness makes every nullary constructor left
in a rule pattern a declared (therefore fixed) signature symbol; replay
coherence transports the only environment-sensitive side condition. -/
theorem hasSupport_rename_iff
    {sigma : Lara.Sigma.Sigma} {policy : Lara.Policy.Policy}
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    (envSound : EnvRenamingSound env ρg)
    (gamma : Support.LeafId → Option Atom)
    (term : Support.SupportTerm) (conclusion : Atom)
    (obligations : List Support.QuestionId) :
    Support.HasSupport canon (renameCorePolicy ρg policy).ruleLookup
        (renameGamma ρg gamma) (Support.certOkOf env.registry)
        (renameCoreSupportTerm ρg term) (renameResidualAtom ρg conclusion)
        (obligations.map (renameCoreQuestionId ρg)) ↔
      Support.HasSupport canon policy.ruleLookup gamma
        (Support.certOkOf env.registry) term conclusion obligations :=
  ⟨hasSupport_reflect sigmaSound policySorted envSound,
    hasSupport_rename sigmaSound policySorted envSound⟩

private def renameCoreSubst (ρg : Binding.GlobalRenaming)
    (substitution : Support.Subst) : Support.Subst :=
  substitution.map fun entry =>
    (entry.1, renameResidualTerm ρg entry.2)

private theorem exceptionPatternRenamingSound_of_sorted
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    {ruleId : Support.RuleId} {pattern : Support.APat}
    (member : (ruleId, pattern) ∈ policy.defeat.exceptions) :
    CoreAPatRenamingSound ρg pattern := by
  simp only [Lara.policyWellSorted, Bool.and_eq_true] at policySorted
  have checkedSome := List.all_eq_true.mp policySorted.1.2
    (ruleId, pattern) member
  cases checked : Lara.Sigma.checkAPat sigma
      (Lara.exceptionEnv sigma policy ruleId) pattern with
  | none => simp [checked] at checkedSome
  | some next => exact coreAPatRenamingSound_of_check sigmaSound checked

private theorem contraryPatternsRenamingSound_of_sorted
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    {patterns : Support.APat × Support.APat}
    (member : patterns ∈ policy.defeat.contraries) :
    CoreAPatRenamingSound ρg patterns.1 ∧
      CoreAPatRenamingSound ρg patterns.2 := by
  simp only [Lara.policyWellSorted, Bool.and_eq_true] at policySorted
  have checkedSome := List.all_eq_true.mp policySorted.2 patterns member
  cases checked : Lara.Sigma.checkAPats sigma [] [patterns.1, patterns.2] with
  | none => simp [checked] at checkedSome
  | some next =>
      have fixed := coreAPatsRenamingSound_of_check sigmaSound checked
      exact ⟨fixed patterns.1 (by simp), fixed patterns.2 (by simp)⟩

mutual
  private theorem attackMatchPat_rename
      (canon : String → String) (ρg : Binding.GlobalRenaming)
      (substitution : Support.Subst) (term : Lara.Term) :
      ∀ (pattern : Support.Pat), CorePatRenamingSound ρg pattern →
        Lara.Attack.matchPat canon (renameCoreSubst ρg substitution) pattern
            (renameResidualTerm ρg term) =
          (Lara.Attack.matchPat canon substitution pattern term).map
            (renameCoreSubst ρg) := by
    intro pattern fixed
    cases pattern with
    | var varId =>
        simp only [Lara.Attack.matchPat, renameCoreSubst,
          lookupSubst_rename]
        cases found : Support.lookupSubst substitution varId with
        | none => simp [found, renameCoreSubst]
        | some prior =>
            simp only [found, Option.map_some]
            rw [admission_nfTerm_renameResidual,
              admission_nfTerm_renameResidual]
            by_cases equal : Lara.nfTerm canon prior = Lara.nfTerm canon term
            · have renamedEqual :=
                (renameResidualTerm_eq_iff ρg).mpr equal
              simp [equal, renamedEqual, renameCoreSubst]
            · have renamedDifferent :
                  renameResidualTerm ρg (Lara.nfTerm canon prior) ≠
                    renameResidualTerm ρg (Lara.nfTerm canon term) :=
                fun h => equal ((renameResidualTerm_eq_iff ρg).mp h)
              simp [equal, renamedDifferent]
    | num source =>
        simp only [Lara.Attack.matchPat]
        rw [admission_nfTerm_renameResidual]
        by_cases equal : Lara.nfTerm canon (.num source) =
            Lara.nfTerm canon term
        · have renamedEqual := congrArg (renameResidualTerm ρg) equal
          have targetEqual :
              Lara.nfTerm canon (.num source) =
                renameResidualTerm ρg (Lara.nfTerm canon term) := by
            simpa [Lara.nfTerm, renameResidualTerm] using renamedEqual
          rw [if_pos targetEqual, if_pos equal]
          rfl
        · have renamedDifferent :
              Lara.nfTerm canon (.num source) ≠
                renameResidualTerm ρg (Lara.nfTerm canon term) := by
            intro renamedEqual
            apply equal
            apply (renameResidualTerm_eq_iff ρg).mp
            simpa [Lara.nfTerm, renameResidualTerm] using renamedEqual
          simp [equal, renamedDifferent]
    | str source =>
        simp only [Lara.Attack.matchPat]
        rw [admission_nfTerm_renameResidual]
        by_cases equal : Lara.nfTerm canon (.str source) =
            Lara.nfTerm canon term
        · have renamedEqual := congrArg (renameResidualTerm ρg) equal
          have targetEqual :
              Lara.nfTerm canon (.str source) =
                renameResidualTerm ρg (Lara.nfTerm canon term) := by
            simpa [Lara.nfTerm, renameResidualTerm] using renamedEqual
          rw [if_pos targetEqual, if_pos equal]
          rfl
        · have renamedDifferent :
              Lara.nfTerm canon (.str source) ≠
                renameResidualTerm ρg (Lara.nfTerm canon term) := by
            intro renamedEqual
            apply equal
            apply (renameResidualTerm_eq_iff ρg).mp
            simpa [Lara.nfTerm, renameResidualTerm] using renamedEqual
          simp [equal, renamedDifferent]
    | con constructor patterns =>
        cases term with
        | num source => simp [Lara.Attack.matchPat, renameResidualTerm]
        | str source => simp [Lara.Attack.matchPat, renameResidualTerm]
        | con termConstructor terms =>
            cases patterns with
            | nil =>
                cases terms with
                | nil =>
                    have equalIff :
                        constructor.name =
                            Binding.renameText ρg termConstructor ↔
                          constructor.name = termConstructor := by
                      constructor
                      · intro equal
                        apply Binding.renameText_injective ρg
                        rw [fixed]
                        exact equal
                      · intro equal
                        rw [← equal]
                        exact fixed.symm
                    by_cases equal : constructor.name = termConstructor
                    · have renamedEqual := equalIff.mpr equal
                      simp only [Lara.Attack.matchPat, renameResidualTerm]
                      rw [if_pos renamedEqual, if_pos equal]
                      rfl
                    · have renamedDifferent := fun h => equal (equalIff.mp h)
                      simp only [Lara.Attack.matchPat, renameResidualTerm]
                      rw [if_neg renamedDifferent, if_neg equal]
                      rfl
                | cons term rest =>
                    by_cases equal : constructor.name = termConstructor <;>
                      simp [Lara.Attack.matchPat, renameResidualTerm,
                        Lara.Attack.matchPats, equal]
            | cons head rest =>
                cases terms with
                | nil =>
                    simp only [Lara.Attack.matchPat, renameResidualTerm]
                    split <;> split <;> rfl
                | cons term termRest =>
                    simp only [CorePatRenamingSound] at fixed
                    simp only [renameResidualTerm, Lara.Attack.matchPat]
                    by_cases equal : constructor.name = termConstructor
                    · simp only [equal, if_pos]
                      exact attackMatchPats_rename canon ρg substitution
                        (.cons term termRest) (.cons head rest) fixed
                    · simp [equal]
  private theorem attackMatchPats_rename
      (canon : String → String) (ρg : Binding.GlobalRenaming)
      (substitution : Support.Subst) (terms : Lara.Terms) :
      ∀ (patterns : Support.Pats), CorePatsRenamingSound ρg patterns →
        Lara.Attack.matchPats canon (renameCoreSubst ρg substitution) patterns
            (renameResidualTerms ρg terms) =
          (Lara.Attack.matchPats canon substitution patterns terms).map
            (renameCoreSubst ρg) := by
    intro patterns fixed
    cases patterns with
    | nil => cases terms <;> simp [Lara.Attack.matchPats,
        renameResidualTerms, renameCoreSubst]
    | cons pattern rest =>
        cases terms with
        | nil => simp [Lara.Attack.matchPats, renameResidualTerms]
        | cons term termRest =>
            simp only [CorePatsRenamingSound] at fixed
            simp only [renameResidualTerms, Lara.Attack.matchPats]
            rw [attackMatchPat_rename canon ρg substitution term pattern
              fixed.1]
            cases found : Lara.Attack.matchPat canon substitution pattern term
            with
            | none => rfl
            | some next =>
                simp only [Option.map_some]
                exact attackMatchPats_rename canon ρg next termRest rest fixed.2
end

private theorem attackMatchAPat_rename
    (canon : String → String) (ρg : Binding.GlobalRenaming)
    (substitution : Support.Subst) (pattern : Support.APat)
    (atom : Atom) (fixed : CoreAPatRenamingSound ρg pattern) :
    Lara.Attack.matchAPat canon (renameCoreSubst ρg substitution) pattern
        (renameResidualAtom ρg atom) =
      (Lara.Attack.matchAPat canon substitution pattern atom).map
        (renameCoreSubst ρg) := by
  cases pattern with
  | mk patternPredicate patterns =>
      cases atom with
      | atom atomPredicate terms =>
          simp only [Lara.Attack.matchAPat, renameResidualAtom]
          by_cases equal : patternPredicate.name = atomPredicate
          · simp only [equal, if_pos]
            exact attackMatchPats_rename canon ρg substitution terms patterns
              fixed
          · simp [equal]

private theorem contraryMatchDecl_rename
    (canon : String → String) (ρg : Binding.GlobalRenaming)
    (left right : Support.APat) (source target : Atom)
    (leftFixed : CoreAPatRenamingSound ρg left)
    (rightFixed : CoreAPatRenamingSound ρg right) :
    Lara.Attack.contraryMatchDecl canon
        (renameResidualAtom ρg source) (renameResidualAtom ρg target)
        (left, right) =
      Lara.Attack.contraryMatchDecl canon source target (left, right) := by
  unfold Lara.Attack.contraryMatchDecl
  change (match Lara.Attack.matchAPat canon (renameCoreSubst ρg []) left
        (renameResidualAtom ρg source) with
      | none => false
      | some substitution =>
          match Lara.Attack.matchAPat canon substitution right
              (renameResidualAtom ρg target) with
          | none => false
          | some _ => true) = _
  rw [attackMatchAPat_rename canon ρg [] left source leftFixed]
  cases first : Lara.Attack.matchAPat canon [] left source with
  | none => rfl
  | some next =>
      simp only [Option.map_some]
      rw [attackMatchAPat_rename canon ρg next right target rightFixed]
      cases Lara.Attack.matchAPat canon next right target <;> rfl

private theorem contraryMatchBList_rename
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    (patterns : List (Support.APat × Support.APat))
    (contained : ∀ candidate ∈ patterns,
      candidate ∈ policy.defeat.contraries)
    (source target : Atom) :
    patterns.any (Lara.Attack.contraryMatchDecl canon
        (renameResidualAtom ρg source) (renameResidualAtom ρg target)) =
      patterns.any (Lara.Attack.contraryMatchDecl canon source target) := by
  induction patterns with
  | nil => rfl
  | cons pair rest ih =>
      have fixed := contraryPatternsRenamingSound_of_sorted sigmaSound
        policySorted (contained pair (by simp))
      rw [List.any_cons, List.any_cons,
        contraryMatchDecl_rename canon ρg pair.1 pair.2 source target
          fixed.1 fixed.2]
      exact congrArg (Bool.or
        (Lara.Attack.contraryMatchDecl canon source target pair))
        (ih (fun candidate member => contained candidate (by simp [member])))

private theorem contraryMatchB_rename
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    (source target : Atom) :
    Lara.Attack.contraryMatchB canon (renameCorePolicy ρg policy).defeat
        (renameResidualAtom ρg source) (renameResidualAtom ρg target) =
      Lara.Attack.contraryMatchB canon policy.defeat source target := by
  simp only [Lara.Attack.contraryMatchB, renameCorePolicy]
  exact contraryMatchBList_rename sigmaSound policySorted
    policy.defeat.contraries (fun _ member => member) source target

private theorem contraryMatch_rename_iff
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    (source target : Atom) :
    Lara.Attack.ContraryMatch canon (renameCorePolicy ρg policy).defeat
        (renameResidualAtom ρg source) (renameResidualAtom ρg target) ↔
      Lara.Attack.ContraryMatch canon policy.defeat source target := by
  rw [← Lara.Attack.contraryMatchB_iff,
    ← Lara.Attack.contraryMatchB_iff,
    contraryMatchB_rename sigmaSound policySorted]

private theorem lookupDis_rename_attack
    (discharges : List (Support.QuestionId × Support.SupportTerm))
    (question : Support.QuestionId) :
    Lara.Attack.lookupDis
        (discharges.map fun entry =>
          (renameCoreQuestionId ρg entry.1,
            renameCoreSupportTerm ρg entry.2))
        (renameCoreQuestionId ρg question) =
      (Lara.Attack.lookupDis discharges question).map
        (renameCoreSupportTerm ρg) := by
  induction discharges with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨entryQuestion, entryTerm⟩ := entry
      simp only [List.map_cons, Lara.Attack.lookupDis]
      by_cases equal : entryQuestion = question
      · have renamedEqual := congrArg (renameCoreQuestionId ρg) equal
        simp [equal, renamedEqual]
      · have renamedDifferent :
            renameCoreQuestionId ρg entryQuestion ≠
              renameCoreQuestionId ρg question :=
          fun h => equal (renameCoreQuestionId_injective_support ρg h)
        simp [equal, renamedDifferent, ih]

private theorem subterm_rename
    (term : Support.SupportTerm) (position : Lara.Attack.Pos) :
    Lara.Attack.subterm (renameCoreSupportTerm ρg term)
        (renameCorePos ρg position) =
      (Lara.Attack.subterm term position).map
        (renameCoreSupportTerm ρg) := by
  induction position generalizing term with
  | nil => rfl
  | cons step rest ih =>
      cases step with
      | prem index =>
          cases term with
          | leaf leaf => rfl
          | inst rule substitution premises discharges holes assurance =>
              simp only [renameCoreSupportTerm, renameCorePos, List.map_cons,
                Lara.Attack.subterm, renameCoreSupportTerms_eq_map_support,
                List.getElem?_map]
              cases found : premises[index]? with
              | none => rfl
              | some child =>
                  simp only [Option.map_some]
                  exact ih child
      | ques question =>
          cases term with
          | leaf leaf => rfl
          | inst rule substitution premises discharges holes assurance =>
              simp only [renameCoreSupportTerm, renameCorePos, List.map_cons,
                Lara.Attack.subterm,
                renameCoreSupportDischarges_eq_map_support]
              rw [lookupDis_rename_attack]
              cases found : Lara.Attack.lookupDis discharges question with
              | none => rfl
              | some child =>
                  simp only [Option.map_some]
                  exact ih child

private theorem exception_mem_rename_iff
    (ruleId : Support.RuleId) (pattern : Support.APat) :
    (renameCoreRuleId ρg ruleId, pattern) ∈
        (renameCorePolicy ρg policy).defeat.exceptions ↔
      (ruleId, pattern) ∈ policy.defeat.exceptions := by
  simp only [renameCorePolicy, List.mem_map]
  constructor
  · rintro ⟨source, member, equal⟩
    obtain ⟨sourceRule, sourcePattern⟩ := source
    simp only [Prod.mk.injEq] at equal
    have ruleEq := renameCoreRuleId_injective_support ρg equal.1
    simpa [ruleEq, equal.2] using member
  · intro member
    exact ⟨(ruleId, pattern), member, rfl⟩

private theorem hasAttack_rename
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    (envSound : EnvRenamingSound env ρg)
    {gamma : Support.LeafId → Option Atom} {attack : Lara.Attack.Attack}
    (derivation : Lara.Attack.HasAttack canon policy.ruleLookup gamma
      (Support.certOkOf env.registry) policy.defeat attack) :
    Lara.Attack.HasAttack canon
      (renameCorePolicy ρg policy).ruleLookup (renameGamma ρg gamma)
      (Support.certOkOf env.registry) (renameCorePolicy ρg policy).defeat
      (renameCoreAttack ρg attack) := by
  cases derivation with
  | @rebut source ruleId substitution premises discharges holes assurance rule
      sourceConclusion targetConclusion sourceObligations sourceSupport
      ruleFound defeasible conclusionFound contrary =>
      have ruleSound := coreRuleRenamingSound_of_lookup sigmaSound policySorted
        ruleFound
      have targetSupport :=
        (hasSupport_rename_iff sigmaSound policySorted envSound gamma source
          sourceConclusion sourceObligations).mpr sourceSupport
      have targetRuleFound : (renameCorePolicy ρg policy).ruleLookup
          (renameCoreRuleId ρg ruleId) =
            some (renameCoreRule ρg rule) := by
        simpa [ruleLookup_rename, ruleFound]
      have targetConclusionFound : Support.instAPat
          (renameCoreSubst ρg substitution) (renameCoreRule ρg rule).concl =
            some (renameResidualAtom ρg targetConclusion) := by
        have commutes := instAPat_rename ρg substitution rule.concl
          ruleSound.conclusion
        simpa [renameCoreRule, renameCoreSubst, conclusionFound] using commutes
      exact Lara.Attack.HasAttack.rebut
        (Cw := renameResidualAtom ρg sourceConclusion)
        (Cu := renameResidualAtom ρg targetConclusion)
        (Ow := sourceObligations.map (renameCoreQuestionId ρg))
        targetSupport targetRuleFound defeasible targetConclusionFound
        ((contraryMatch_rename_iff sigmaSound policySorted
          sourceConclusion targetConclusion).mpr contrary)
  | @undercut source target position ruleId substitution premises discharges
      holes assurance rule exception targetConclusion sourceConclusion
      sourceObligations sourceSupport occurrence ruleFound defeasible
      exceptionMember exceptionFound equivalent =>
      have exceptionFixed := exceptionPatternRenamingSound_of_sorted sigmaSound
        policySorted exceptionMember
      have targetSupport :=
        (hasSupport_rename_iff sigmaSound policySorted envSound gamma source
          sourceConclusion sourceObligations).mpr sourceSupport
      have targetOccurrence : Lara.Attack.subterm
          (renameCoreSupportTerm ρg target) (renameCorePos ρg position) =
            some (renameCoreSupportTerm ρg
              (.inst ruleId substitution premises discharges holes assurance)) := by
        simpa [occurrence] using subterm_rename
          (ρg := ρg) target position
      have targetRuleFound : (renameCorePolicy ρg policy).ruleLookup
          (renameCoreRuleId ρg ruleId) =
            some (renameCoreRule ρg rule) := by
        simpa [ruleLookup_rename, ruleFound]
      have targetExceptionMember := (exception_mem_rename_iff (ρg := ρg)
          (policy := policy) ruleId exception).mpr exceptionMember
      have targetExceptionFound : Support.instAPat
          (renameCoreSubst ρg substitution) exception =
            some (renameResidualAtom ρg targetConclusion) := by
        have commutes := instAPat_rename ρg substitution exception
          exceptionFixed
        simpa [renameCoreSubst, exceptionFound] using commutes
      exact Lara.Attack.HasAttack.undercut
        (Cw := renameResidualAtom ρg sourceConclusion)
        (e := renameResidualAtom ρg targetConclusion)
        (Ow := sourceObligations.map (renameCoreQuestionId ρg))
        targetSupport targetOccurrence targetRuleFound defeasible
        targetExceptionMember targetExceptionFound
        ((admission_equiv_renameResidual canon ρg
          sourceConclusion targetConclusion).mpr equivalent)
  | @undermine source target position leaf leafConclusion sourceConclusion
      sourceObligations sourceSupport occurrence leafFound contrary =>
      have targetSupport :=
        (hasSupport_rename_iff sigmaSound policySorted envSound gamma source
          sourceConclusion sourceObligations).mpr sourceSupport
      have targetOccurrence : Lara.Attack.subterm
          (renameCoreSupportTerm ρg target) (renameCorePos ρg position) =
            some (.leaf (renameCoreLeafId ρg leaf)) := by
        simpa [occurrence, renameCoreSupportTerm] using subterm_rename
          (ρg := ρg) target position
      have targetLeafFound : renameGamma ρg gamma
          (renameCoreLeafId ρg leaf) =
            some (renameResidualAtom ρg leafConclusion) := by
        simpa [renameGamma_image, leafFound]
      exact Lara.Attack.HasAttack.undermine
        (Cw := renameResidualAtom ρg sourceConclusion)
        (pl := renameResidualAtom ρg leafConclusion)
        (Ow := sourceObligations.map (renameCoreQuestionId ρg))
        targetSupport targetOccurrence targetLeafFound
        ((contraryMatch_rename_iff sigmaSound policySorted
          sourceConclusion leafConclusion).mpr contrary)

private theorem hasAttack_reflect
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    (envSound : EnvRenamingSound env ρg)
    {gamma : Support.LeafId → Option Atom} {attack : Lara.Attack.Attack}
    (derivation : Lara.Attack.HasAttack canon
      (renameCorePolicy ρg policy).ruleLookup (renameGamma ρg gamma)
      (Support.certOkOf env.registry) (renameCorePolicy ρg policy).defeat
      (renameCoreAttack ρg attack)) :
    Lara.Attack.HasAttack canon policy.ruleLookup gamma
      (Support.certOkOf env.registry) policy.defeat attack := by
  cases attack with
  | rebut source target =>
      cases target with
      | leaf leaf => cases derivation
      | inst ruleId substitution premises discharges holes assurance =>
          cases derivation with
          | @rebut _ _ _ _ _ _ _ targetRule sourceConclusion
              targetConclusion targetObligations sourceSupport ruleFound
              defeasible conclusionFound contrary =>
              rw [ruleLookup_rename] at ruleFound
              cases sourceRuleFound : policy.ruleLookup ruleId with
              | none => simp [sourceRuleFound] at ruleFound
              | some sourceRule =>
                  have targetRuleEq : targetRule =
                      renameCoreRule ρg sourceRule := by
                    simpa [sourceRuleFound] using ruleFound.symm
                  subst targetRule
                  have ruleSound := coreRuleRenamingSound_of_lookup sigmaSound
                    policySorted sourceRuleFound
                  obtain ⟨sourceConclusion', sourceObligations,
                    sourceConclusionEq, sourceObligationsEq, sourceSupport'⟩ :=
                      hasSupport_reflect_exists sigmaSound policySorted envSound
                        sourceSupport source rfl
                  subst sourceConclusion
                  subst targetObligations
                  cases sourceConclusionFound :
                      Support.instAPat substitution sourceRule.concl with
                  | none =>
                      have conclusionFound' : Support.instAPat
                          (renameCoreSubst ρg substitution) sourceRule.concl =
                            some targetConclusion := by
                        simpa [renameCoreRule, renameCoreSubst] using
                          conclusionFound
                      have commutes := instAPat_rename ρg substitution
                        sourceRule.concl ruleSound.conclusion
                      simp [renameCoreRule, renameCoreSubst,
                        sourceConclusionFound] at commutes
                      change Support.instAPat (renameCoreSubst ρg substitution)
                          sourceRule.concl = none at commutes
                      rw [commutes] at conclusionFound'
                      cases conclusionFound'
                  | some sourceTargetConclusion =>
                      have targetConclusionEq : targetConclusion =
                          renameResidualAtom ρg sourceTargetConclusion := by
                        have commutes := instAPat_rename ρg substitution
                          sourceRule.concl ruleSound.conclusion
                        rw [sourceConclusionFound] at commutes
                        have conclusionFound' : Support.instAPat
                            (renameCoreSubst ρg substitution)
                              sourceRule.concl = some targetConclusion := by
                          simpa [renameCoreRule, renameCoreSubst] using
                            conclusionFound
                        exact (Option.some.inj
                          (commutes.symm.trans conclusionFound')).symm
                      subst targetConclusion
                      exact Lara.Attack.HasAttack.rebut sourceSupport'
                        sourceRuleFound defeasible sourceConclusionFound
                        ((contraryMatch_rename_iff sigmaSound policySorted
                          sourceConclusion' sourceTargetConclusion).mp contrary)
  | undercut source target position =>
      cases derivation with
      | @undercut _ _ _ targetRuleId targetSubstitution targetPremises
          targetDischarges targetHoles targetAssurance targetRule
          targetException targetConclusion sourceConclusion targetObligations
          sourceSupport occurrence ruleFound defeasible exceptionMember
          exceptionFound equivalent =>
          obtain ⟨sourceConclusion', sourceObligations,
            sourceConclusionEq, sourceObligationsEq, sourceSupport'⟩ :=
              hasSupport_reflect_exists sigmaSound policySorted envSound
                sourceSupport source rfl
          subst sourceConclusion
          subst targetObligations
          cases sourceOccurrence : Lara.Attack.subterm target position with
          | none =>
              have commutes := subterm_rename (ρg := ρg) target position
              rw [sourceOccurrence] at commutes
              rw [commutes] at occurrence
              cases occurrence
          | some sourceSubterm =>
              cases sourceSubterm with
              | leaf sourceLeaf =>
                  have commutes := subterm_rename (ρg := ρg) target position
                  rw [sourceOccurrence] at commutes
                  rw [commutes] at occurrence
                  cases occurrence
              | inst sourceRuleId sourceSubstitution sourcePremises
                  sourceDischarges sourceHoles sourceAssurance =>
                  have commutes := subterm_rename (ρg := ρg) target position
                  rw [sourceOccurrence] at commutes
                  have occurrenceEq := Option.some.inj
                    (commutes.symm.trans occurrence)
                  simp only [renameCoreSupportTerm,
                    Support.SupportTerm.inst.injEq] at occurrenceEq
                  rcases occurrenceEq with ⟨ruleIdEq, substitutionEq,
                    premisesEq, dischargesEq, holesEq, assuranceEq⟩
                  subst targetRuleId
                  subst targetSubstitution
                  subst targetPremises
                  subst targetDischarges
                  subst targetHoles
                  subst targetAssurance
                  rw [ruleLookup_rename] at ruleFound
                  cases sourceRuleFound : policy.ruleLookup sourceRuleId with
                  | none => simp [sourceRuleFound] at ruleFound
                  | some sourceRule =>
                      have targetRuleEq : targetRule =
                          renameCoreRule ρg sourceRule := by
                        simpa [sourceRuleFound] using ruleFound.symm
                      subst targetRule
                      have sourceExceptionMember :=
                        (exception_mem_rename_iff (ρg := ρg)
                          (policy := policy) sourceRuleId targetException).mp
                          exceptionMember
                      have exceptionFixed :=
                        exceptionPatternRenamingSound_of_sorted sigmaSound
                          policySorted sourceExceptionMember
                      cases sourceExceptionFound : Support.instAPat
                          sourceSubstitution targetException with
                      | none =>
                          have instCommutes := instAPat_rename ρg
                            sourceSubstitution targetException exceptionFixed
                          simp [renameCoreSubst, sourceExceptionFound] at instCommutes
                          rw [instCommutes] at exceptionFound
                          cases exceptionFound
                      | some sourceTargetConclusion =>
                          have targetConclusionEq : targetConclusion =
                              renameResidualAtom ρg sourceTargetConclusion := by
                            have instCommutes := instAPat_rename ρg
                              sourceSubstitution targetException exceptionFixed
                            rw [sourceExceptionFound] at instCommutes
                            exact (Option.some.inj
                              (instCommutes.symm.trans exceptionFound)).symm
                          subst targetConclusion
                          exact Lara.Attack.HasAttack.undercut
                            (Cw := sourceConclusion')
                            (Ow := sourceObligations)
                            sourceSupport'
                            sourceOccurrence sourceRuleFound defeasible
                            sourceExceptionMember sourceExceptionFound
                            ((admission_equiv_renameResidual canon ρg
                              sourceConclusion' sourceTargetConclusion).mp
                              equivalent)
  | undermine source target position =>
      cases derivation with
      | @undermine _ _ _ targetLeaf targetLeafConclusion sourceConclusion
          targetObligations sourceSupport occurrence leafFound contrary =>
          obtain ⟨sourceConclusion', sourceObligations,
            sourceConclusionEq, sourceObligationsEq, sourceSupport'⟩ :=
              hasSupport_reflect_exists sigmaSound policySorted envSound
                sourceSupport source rfl
          subst sourceConclusion
          subst targetObligations
          cases sourceOccurrence : Lara.Attack.subterm target position with
          | none =>
              have commutes := subterm_rename (ρg := ρg) target position
              rw [sourceOccurrence] at commutes
              rw [commutes] at occurrence
              cases occurrence
          | some sourceSubterm =>
              cases sourceSubterm with
              | inst sourceRule sourceSubstitution sourcePremises
                  sourceDischarges sourceHoles sourceAssurance =>
                  have commutes := subterm_rename (ρg := ρg) target position
                  rw [sourceOccurrence] at commutes
                  rw [commutes] at occurrence
                  cases occurrence
              | leaf sourceLeaf =>
                  have commutes := subterm_rename (ρg := ρg) target position
                  rw [sourceOccurrence] at commutes
                  have leafEq : targetLeaf = renameCoreLeafId ρg sourceLeaf := by
                    simpa [renameCoreSupportTerm] using
                      (Option.some.inj (commutes.symm.trans occurrence)).symm
                  subst targetLeaf
                  rw [renameGamma_image] at leafFound
                  cases sourceLeafFound : gamma sourceLeaf with
                  | none => simp [sourceLeafFound] at leafFound
                  | some sourceLeafConclusion =>
                      have conclusionEq : targetLeafConclusion =
                          renameResidualAtom ρg sourceLeafConclusion := by
                        simpa [sourceLeafFound] using leafFound.symm
                      subst targetLeafConclusion
                      exact Lara.Attack.HasAttack.undermine
                        (Cw := sourceConclusion')
                        (Ow := sourceObligations)
                        sourceSupport'
                        sourceOccurrence sourceLeafFound
                        ((contraryMatch_rename_iff sigmaSound policySorted
                          sourceConclusion' sourceLeafConclusion).mp contrary)

/-- Typed core attack derivations transport forward and reflect through the
same typed global renaming as their support premise. -/
theorem hasAttack_rename_iff
    {sigma : Lara.Sigma.Sigma} {policy : Lara.Policy.Policy}
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    (envSound : EnvRenamingSound env ρg)
    (gamma : Support.LeafId → Option Atom)
    (attack : Lara.Attack.Attack) :
    Lara.Attack.HasAttack canon
        (renameCorePolicy ρg policy).ruleLookup (renameGamma ρg gamma)
        (Support.certOkOf env.registry) (renameCorePolicy ρg policy).defeat
        (renameCoreAttack ρg attack) ↔
      Lara.Attack.HasAttack canon policy.ruleLookup gamma
        (Support.certOkOf env.registry) policy.defeat attack :=
  ⟨hasAttack_reflect sigmaSound policySorted envSound,
    hasAttack_rename sigmaSound policySorted envSound⟩

private noncomputable def restoreCoreRenameText
    (ρg : Binding.GlobalRenaming) (spelling : String) : String := by
  classical
  exact if witness : ∃ source, Binding.renameText ρg source = spelling then
    Classical.choose witness
  else spelling

private theorem restoreCoreRenameText_rename
    (ρg : Binding.GlobalRenaming) (spelling : String) :
    restoreCoreRenameText ρg (Binding.renameText ρg spelling) = spelling := by
  classical
  unfold restoreCoreRenameText
  split
  · rename_i witness
    apply Binding.renameText_injective ρg
    exact Classical.choose_spec witness
  · rename_i absent
    exact False.elim (absent ⟨spelling, rfl⟩)

private noncomputable def restoreCoreCertPayload
    (ρg : Binding.GlobalRenaming) : Support.SExpr → Support.SExpr
  | .list [.atom "prem", .atom source] =>
      .list [.atom "prem", .atom (restoreCoreRenameText ρg source)]
  | .list [.atom "lam", formula, body] =>
      .list [.atom "lam", formula, restoreCoreCertPayload ρg body]
  | .list [.atom "lam", binder, formula, body] =>
      .list [.atom "lam", binder, formula, restoreCoreCertPayload ρg body]
  | .list [.atom "app", function, argument] =>
      .list [.atom "app", restoreCoreCertPayload ρg function,
        restoreCoreCertPayload ρg argument]
  | .list [.atom "abort", formula, body] =>
      .list [.atom "abort", formula, restoreCoreCertPayload ρg body]
  | expression => expression
termination_by expression => sizeOf expression

private theorem restoreCoreCertPayload_rename
    (ρg : Binding.GlobalRenaming) (payload : Support.SExpr) :
    restoreCoreCertPayload ρg (renameCoreCertPayload ρg payload) = payload := by
  induction payload using renameCoreCertPayload.induct <;>
    simp_all [renameCoreCertPayload, restoreCoreCertPayload,
      restoreCoreRenameText_rename]

private theorem renameCoreCertPayload_eq_iff
    (ρg : Binding.GlobalRenaming) {left right : Support.SExpr} :
    renameCoreCertPayload ρg left = renameCoreCertPayload ρg right ↔
      left = right := by
  constructor
  · intro equal
    have restored := congrArg (restoreCoreCertPayload ρg) equal
    simpa only [restoreCoreCertPayload_rename] using restored
  · intro equal
    subst right
    rfl

private theorem renameCoreAssurance_eq_iff
    (ρg : Binding.GlobalRenaming) {left right : Support.Assurance} :
    renameCoreAssurance ρg left = renameCoreAssurance ρg right ↔
      left = right := by
  constructor
  · intro equal
    cases left <;> cases right <;>
      simp [renameCoreAssurance, renameCoreCertRef] at equal ⊢
    rename_i leftBackend leftDigest leftCertificate rightBackend rightDigest
      rightCertificate
    cases leftCertificate
    cases rightCertificate
    simp only [renameCoreAssurance, Support.Assurance.cert.injEq,
      renameCoreCertRef, Support.CertRef.mk.injEq] at equal ⊢
    exact ⟨equal.1, equal.2.1,
      (renameCoreCertPayload_eq_iff ρg).mp equal.2.2⟩
  · intro equal
    subst right
    rfl

mutual
  private theorem renameCoreSupportTerm_eq_iff
      (ρg : Binding.GlobalRenaming)
      {left right : Support.SupportTerm} :
      renameCoreSupportTerm ρg left = renameCoreSupportTerm ρg right ↔
        left = right := by
    constructor
    · intro equal
      cases left with
      | leaf leftLeaf =>
          cases right with
          | leaf rightLeaf =>
              have leafEq := renameCoreLeafId_injective ρg
                (Support.SupportTerm.leaf.inj equal)
              simpa [leafEq]
          | inst => simp [renameCoreSupportTerm] at equal
      | inst leftRule leftSubstitution leftPremises leftDischarges leftHoles
          leftAssurance =>
          cases right with
          | leaf => simp [renameCoreSupportTerm] at equal
          | inst rightRule rightSubstitution rightPremises rightDischarges
              rightHoles rightAssurance =>
              simp only [renameCoreSupportTerm,
                Support.SupportTerm.inst.injEq] at equal
              have ruleEq := renameCoreRuleId_injective_support ρg equal.1
              have substitutionEntryInjective : Function.Injective
                  (fun entry : Support.VarId × Lara.Term =>
                    (entry.1, renameResidualTerm ρg entry.2)) := by
                rintro ⟨leftVariable, leftTerm⟩ ⟨rightVariable, rightTerm⟩
                  entryEq
                have variableEq : leftVariable = rightVariable := by
                  simpa using congrArg Prod.fst entryEq
                have termEq : leftTerm = rightTerm :=
                  (renameResidualTerm_eq_iff ρg).mp (by
                    simpa using congrArg Prod.snd entryEq)
                exact Prod.ext variableEq termEq
              have substitutionEq : leftSubstitution = rightSubstitution :=
                listMap_injective_support substitutionEntryInjective equal.2.1
              have premisesEq := (renameCoreSupportTerms_eq_iff ρg).mp
                equal.2.2.1
              have dischargesEq := (renameCoreSupportDischarges_eq_iff ρg).mp
                equal.2.2.2.1
              have holesEq : leftHoles = rightHoles :=
                listMap_injective_support
                  (renameCoreQuestionId_injective_support ρg) equal.2.2.2.2.1
              have assuranceEq := (renameCoreAssurance_eq_iff ρg).mp
                equal.2.2.2.2.2
              simp [ruleEq, substitutionEq, premisesEq, dischargesEq,
                holesEq, assuranceEq]
    · intro equal
      subst right
      rfl
  private theorem renameCoreSupportTerms_eq_iff
      (ρg : Binding.GlobalRenaming)
      {left right : List Support.SupportTerm} :
      renameCoreSupportTerms ρg left = renameCoreSupportTerms ρg right ↔
        left = right := by
    constructor
    · intro equal
      cases left with
      | nil => cases right <;> simp [renameCoreSupportTerms] at equal ⊢
      | cons leftTerm leftRest =>
          cases right with
          | nil => simp [renameCoreSupportTerms] at equal
          | cons rightTerm rightRest =>
              simp only [renameCoreSupportTerms] at equal
              have fields := List.cons.inj equal
              have termEq := (renameCoreSupportTerm_eq_iff ρg).mp fields.1
              have restEq := (renameCoreSupportTerms_eq_iff ρg).mp fields.2
              simp [termEq, restEq]
    · intro equal
      subst right
      rfl
  private theorem renameCoreSupportDischarges_eq_iff
      (ρg : Binding.GlobalRenaming)
      {left right : List (Support.QuestionId × Support.SupportTerm)} :
      renameCoreSupportDischarges ρg left =
          renameCoreSupportDischarges ρg right ↔
        left = right := by
    constructor
    · intro equal
      cases left with
      | nil => cases right <;>
          simp [renameCoreSupportDischarges] at equal ⊢
      | cons leftEntry leftRest =>
          cases right with
          | nil => simp [renameCoreSupportDischarges] at equal
          | cons rightEntry rightRest =>
              obtain ⟨leftQuestion, leftTerm⟩ := leftEntry
              obtain ⟨rightQuestion, rightTerm⟩ := rightEntry
              simp only [renameCoreSupportDischarges] at equal
              have fields := List.cons.inj equal
              have headFields := Prod.mk.inj fields.1
              have questionEq := renameCoreQuestionId_injective_support ρg
                headFields.1
              have termEq := (renameCoreSupportTerm_eq_iff ρg).mp headFields.2
              have restEq := (renameCoreSupportDischarges_eq_iff ρg).mp
                fields.2
              simp [questionEq, termEq, restEq]
    · intro equal
      subst right
      rfl
end

mutual
  private theorem containsB_rename
      (ρg : Binding.GlobalRenaming)
      (value query : Support.SupportTerm) :
      Lara.Compile.containsB (renameCoreSupportTerm ρg value)
          (renameCoreSupportTerm ρg query) =
        Lara.Compile.containsB value query := by
    cases value with
    | leaf leaf =>
        simp only [Lara.Compile.containsB, renameCoreSupportTerm]
        apply decide_eq_decide.mpr
        simpa only [renameCoreSupportTerm] using
          (renameCoreSupportTerm_eq_iff ρg
            (left := .leaf leaf) (right := query))
    | inst rule substitution premises discharges holes assurance =>
        simp only [Lara.Compile.containsB, renameCoreSupportTerm]
        rw [containsBList_rename, containsBDis_rename]
        congr 2
        apply decide_eq_decide.mpr
        simpa only [renameCoreSupportTerm] using
          (renameCoreSupportTerm_eq_iff ρg
            (left := .inst rule substitution premises discharges holes assurance)
            (right := query))
  private theorem containsBList_rename
      (ρg : Binding.GlobalRenaming)
      (values : List Support.SupportTerm) (query : Support.SupportTerm) :
      Lara.Compile.containsBList (renameCoreSupportTerms ρg values)
          (renameCoreSupportTerm ρg query) =
        Lara.Compile.containsBList values query := by
    cases values with
    | nil => rfl
    | cons value rest =>
        simp only [renameCoreSupportTerms, Lara.Compile.containsBList]
        rw [containsB_rename, containsBList_rename]
  private theorem containsBDis_rename
      (ρg : Binding.GlobalRenaming)
      (values : List (Support.QuestionId × Support.SupportTerm))
      (query : Support.SupportTerm) :
      Lara.Compile.containsBDis (renameCoreSupportDischarges ρg values)
          (renameCoreSupportTerm ρg query) =
        Lara.Compile.containsBDis values query := by
    cases values with
    | nil => rfl
    | cons value rest =>
        obtain ⟨question, term⟩ := value
        simp only [renameCoreSupportDischarges, Lara.Compile.containsBDis]
        rw [containsB_rename, containsBDis_rename]
end

private theorem attackClosureB_rename
    (attack : Lara.Attack.Attack) (target : Support.SupportTerm) :
    Lara.Compile.attackClosureB (renameCoreAttack ρg attack)
        (renameCoreSupportTerm ρg target) =
      Lara.Compile.attackClosureB attack target := by
  cases attack with
  | rebut source attacked =>
      exact containsB_rename ρg target attacked
  | undercut source attacked position =>
      simp only [Lara.Compile.attackClosureB, renameCoreAttack]
      rw [subterm_rename]
      cases found : Lara.Attack.subterm attacked position with
      | none => rfl
      | some occurrence =>
          simp only [Option.map_some]
          exact containsB_rename ρg target occurrence
  | undermine source attacked position =>
      simp only [Lara.Compile.attackClosureB, renameCoreAttack]
      rw [subterm_rename]
      cases found : Lara.Attack.subterm attacked position with
      | none => rfl
      | some occurrence =>
          simp only [Option.map_some]
          exact containsB_rename ρg target occurrence

@[simp] private theorem attackSource_rename
    (attack : Lara.Attack.Attack) :
    (renameCoreAttack ρg attack).source =
      renameCoreSupportTerm ρg attack.source := by
  cases attack <;> rfl

private theorem coveredB_rename
    (attacks : List Lara.Attack.Attack)
    (source target : Support.SupportTerm) :
    Lara.Compile.coveredB (attacks.map (renameCoreAttack ρg))
        (renameCoreSupportTerm ρg source)
        (renameCoreSupportTerm ρg target) =
      Lara.Compile.coveredB attacks source target := by
  unfold Lara.Compile.coveredB
  induction attacks with
  | nil => rfl
  | cons attack rest ih =>
      simp only [List.map_cons, List.any_cons, attackSource_rename]
      have sourceEq :
          decide (renameCoreSupportTerm ρg attack.source =
              renameCoreSupportTerm ρg source) =
            decide (attack.source = source) := by
        apply decide_eq_decide.mpr
        exact renameCoreSupportTerm_eq_iff ρg
      rw [sourceEq, attackClosureB_rename, ih]

private theorem covered_rename_iff
    {source target : Support.SupportTerm}
    (sourceTargetValid : Support.HasSupport canon policy.ruleLookup gamma certOk
      target targetConclusion [])
    (targetTargetValid : Support.HasSupport canon
      (renameCorePolicy ρg policy).ruleLookup (renameGamma ρg gamma) certOk
      (renameCoreSupportTerm ρg target)
      (renameResidualAtom ρg targetConclusion) [])
    (attacks : List Lara.Attack.Attack) :
    Lara.Compile.Covered (attacks.map (renameCoreAttack ρg))
        (renameCoreSupportTerm ρg source) (renameCoreSupportTerm ρg target) ↔
      Lara.Compile.Covered attacks source target := by
  rw [← Lara.Compile.coveredB_iff
      (Lara.Compile.hasSupport_disNodup targetTargetValid),
    ← Lara.Compile.coveredB_iff
      (Lara.Compile.hasSupport_disNodup sourceTargetValid),
    coveredB_rename]

private theorem conflictAttackable_rename_iff
    (target : Support.SupportTerm) :
    Lara.Compile.ConflictAttackable (renameCorePolicy ρg policy).ruleLookup
        (renameCoreSupportTerm ρg target) ↔
      Lara.Compile.ConflictAttackable policy.ruleLookup target := by
  cases target with
  | leaf leaf => simp [Lara.Compile.ConflictAttackable,
      renameCoreSupportTerm]
  | inst ruleId substitution premises discharges holes assurance =>
      simp only [Lara.Compile.ConflictAttackable, renameCoreSupportTerm]
      rw [ruleLookup_rename]
      constructor
      · rintro ⟨targetRule, targetFound, targetMode⟩
        cases sourceFound : policy.ruleLookup ruleId with
        | none => simp [sourceFound] at targetFound
        | some sourceRule =>
            have ruleEq : targetRule = renameCoreRule ρg sourceRule := by
              simpa [sourceFound] using targetFound.symm
            subst targetRule
            exact ⟨sourceRule, rfl, targetMode⟩
      · rintro ⟨sourceRule, sourceFound, sourceMode⟩
        exact ⟨renameCoreRule ρg sourceRule, by simp [sourceFound], sourceMode⟩

/-- Attack completeness is invariant under the ordered renaming of declared
arguments and typed attacks. -/
theorem attackComplete_rename_iff
    {sigma : Lara.Sigma.Sigma} {policy : Lara.Policy.Policy}
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma policy = true)
    (envSound : EnvRenamingSound env ρg)
    (gamma : Support.LeafId → Option Atom)
    (arguments : List Support.SupportTerm)
    (attacks : List Lara.Attack.Attack) :
    Lara.Compile.AttackComplete canon
        (renameCorePolicy ρg policy).ruleLookup (renameGamma ρg gamma)
        (Support.certOkOf env.registry) (renameCorePolicy ρg policy).defeat
        (arguments.map (renameCoreSupportTerm ρg))
        (attacks.map (renameCoreAttack ρg)) ↔
      Lara.Compile.AttackComplete canon policy.ruleLookup gamma
        (Support.certOkOf env.registry) policy.defeat arguments attacks :=
  by
    constructor
    · intro targetComplete source sourceMember target targetMember
        sourceConclusion targetConclusion sourceValid targetValid contrary
        attackable
      have renamedSourceValid : Support.HasSupport canon
          (renameCorePolicy ρg policy).ruleLookup (renameGamma ρg gamma)
          (Support.certOkOf env.registry)
          (renameCoreSupportTerm ρg source)
          (renameResidualAtom ρg sourceConclusion) [] := by
        simpa using (hasSupport_rename_iff sigmaSound policySorted envSound
          gamma source sourceConclusion []).mpr sourceValid
      have renamedTargetValid : Support.HasSupport canon
          (renameCorePolicy ρg policy).ruleLookup (renameGamma ρg gamma)
          (Support.certOkOf env.registry)
          (renameCoreSupportTerm ρg target)
          (renameResidualAtom ρg targetConclusion) [] := by
        simpa using (hasSupport_rename_iff sigmaSound policySorted envSound
          gamma target targetConclusion []).mpr targetValid
      have renamedCovered := targetComplete
        (renameCoreSupportTerm ρg source)
        (List.mem_map.mpr ⟨source, sourceMember, rfl⟩)
        (renameCoreSupportTerm ρg target)
        (List.mem_map.mpr ⟨target, targetMember, rfl⟩)
        (renameResidualAtom ρg sourceConclusion)
        (renameResidualAtom ρg targetConclusion)
        renamedSourceValid renamedTargetValid
        ((contraryMatch_rename_iff sigmaSound policySorted
          sourceConclusion targetConclusion).mpr contrary)
        ((conflictAttackable_rename_iff (ρg := ρg) (policy := policy)
          target).mpr attackable)
      exact (covered_rename_iff (ρg := ρg) (policy := policy)
        (gamma := gamma) targetValid renamedTargetValid attacks).mp
          renamedCovered
    · intro sourceComplete renamedSource renamedSourceMember renamedTarget
        renamedTargetMember renamedSourceConclusion renamedTargetConclusion
        renamedSourceValid renamedTargetValid renamedContrary renamedAttackable
      obtain ⟨source, sourceMember, sourceEq⟩ :=
        List.mem_map.mp renamedSourceMember
      obtain ⟨target, targetMember, targetEq⟩ :=
        List.mem_map.mp renamedTargetMember
      subst renamedSource
      subst renamedTarget
      obtain ⟨sourceConclusion, sourceObligations, sourceConclusionEq,
        sourceObligationsEq, sourceValid⟩ :=
          hasSupport_reflect_exists sigmaSound policySorted envSound
            renamedSourceValid source rfl
      obtain ⟨targetConclusion, targetObligations, targetConclusionEq,
        targetObligationsEq, targetValid⟩ :=
          hasSupport_reflect_exists sigmaSound policySorted envSound
            renamedTargetValid target rfl
      have sourceObligationsEmpty : sourceObligations = [] := by
        cases sourceObligations with
        | nil => rfl
        | cons question rest => simp at sourceObligationsEq
      have targetObligationsEmpty : targetObligations = [] := by
        cases targetObligations with
        | nil => rfl
        | cons question rest => simp at targetObligationsEq
      subst sourceObligations
      subst targetObligations
      subst renamedSourceConclusion
      subst renamedTargetConclusion
      have sourceCovered := sourceComplete source sourceMember target targetMember
        sourceConclusion targetConclusion sourceValid targetValid
        ((contraryMatch_rename_iff sigmaSound policySorted
          sourceConclusion targetConclusion).mp renamedContrary)
        ((conflictAttackable_rename_iff (ρg := ρg) (policy := policy)
          target).mp renamedAttackable)
      exact (covered_rename_iff (ρg := ρg) (policy := policy)
        (gamma := gamma) targetValid renamedTargetValid attacks).mpr
          sourceCovered

/-! ### Whole-unit structural transport -/

private theorem lookupCon_renameText_aux
    (declarations : List Lara.Sigma.ConSig)
    (sigmaSound : ∀ declaration ∈ declarations,
      Binding.renameText ρg declaration.sym.name = declaration.sym.name)
    (name : String) :
    declarations.find? (fun declaration =>
        decide (declaration.sym = (⟨Binding.renameText ρg name⟩ : Support.ConSym))) =
      declarations.find? (fun declaration =>
        decide (declaration.sym = (⟨name⟩ : Support.ConSym))) := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
      have declarationFixed := sigmaSound declaration (by simp)
      have restFixed : ∀ candidate ∈ rest,
          Binding.renameText ρg candidate.sym.name = candidate.sym.name := by
        intro candidate member
        exact sigmaSound candidate (by simp [member])
      have equalIff :
          declaration.sym = (⟨Binding.renameText ρg name⟩ : Support.ConSym) ↔
            declaration.sym = (⟨name⟩ : Support.ConSym) := by
        constructor
        · intro equal
          have equalName := congrArg Support.ConSym.name equal
          have originalName := Binding.renameText_injective ρg
            (declarationFixed.trans equalName)
          have eta : declaration.sym = ⟨declaration.sym.name⟩ := by
            cases declaration.sym
            rfl
          exact eta.trans (congrArg Support.ConSym.mk originalName)
        · intro equal
          have equalName := congrArg Support.ConSym.name equal
          have renamedName := declarationFixed.symm.trans
            (congrArg (Binding.renameText ρg) equalName)
          have eta : declaration.sym = ⟨declaration.sym.name⟩ := by
            cases declaration.sym
            rfl
          exact eta.trans (congrArg Support.ConSym.mk renamedName)
      simp only [List.find?_cons]
      by_cases equal : declaration.sym = (⟨name⟩ : Support.ConSym)
      · have targetEqual := equalIff.mpr equal
        have sourceDecision : decide
            (declaration.sym = (⟨name⟩ : Support.ConSym)) = true :=
          decide_eq_true equal
        have targetDecision : decide
            (declaration.sym =
              (⟨Binding.renameText ρg name⟩ : Support.ConSym)) = true :=
          decide_eq_true targetEqual
        rw [sourceDecision, targetDecision]
      · have renamedDifferent :
            declaration.sym ≠
              (⟨Binding.renameText ρg name⟩ : Support.ConSym) :=
          fun renamedEqual => equal (equalIff.mp renamedEqual)
        have sourceDecision : decide
            (declaration.sym = (⟨name⟩ : Support.ConSym)) = false :=
          decide_eq_false equal
        have targetDecision : decide
            (declaration.sym =
              (⟨Binding.renameText ρg name⟩ : Support.ConSym)) = false :=
          decide_eq_false renamedDifferent
        rw [sourceDecision, targetDecision]
        exact ih restFixed

private theorem lookupCon_renameText
    (sigmaSound : CoreSigmaRenamingSound ρg sigma) (name : String) :
    sigma.lookupCon ⟨Binding.renameText ρg name⟩ = sigma.lookupCon ⟨name⟩ := by
  unfold Lara.Sigma.Sigma.lookupCon
  exact lookupCon_renameText_aux sigma.cons sigmaSound name

mutual
  private theorem sortOf_renameResidual
      (sigmaSound : CoreSigmaRenamingSound ρg sigma) :
      ∀ term,
        Lara.Sigma.sortOf sigma (renameResidualTerm ρg term) =
          Lara.Sigma.sortOf sigma term := by
    intro term
    cases term with
    | num source => rfl
    | str source => rfl
    | con name terms =>
        cases terms with
        | nil =>
            simp only [renameResidualTerm, Lara.Sigma.sortOf]
            rw [lookupCon_renameText sigmaSound]
        | cons term rest =>
            simp only [renameResidualTerm, Lara.Sigma.sortOf]
            change
              (match sigma.lookupCon ⟨name⟩ with
              | none => none
              | some declaration =>
                  if Lara.Sigma.expectTerms sigma declaration.args
                      (renameResidualTerms ρg (.cons term rest)) then
                    some declaration.result
                  else none) =
                (match sigma.lookupCon ⟨name⟩ with
                | none => none
                | some declaration =>
                    if Lara.Sigma.expectTerms sigma declaration.args
                        (.cons term rest) then
                      some declaration.result
                    else none)
            cases found : sigma.lookupCon ⟨name⟩ with
            | none => simp [found]
            | some declaration =>
                simp only [found]
                have hterms := expectTerms_renameResidual sigmaSound
                  declaration.args (.cons term rest)
                rw [hterms]
  private theorem expectTerms_renameResidual
      (sigmaSound : CoreSigmaRenamingSound ρg sigma) :
      ∀ sorts terms,
        Lara.Sigma.expectTerms sigma sorts (renameResidualTerms ρg terms) =
          Lara.Sigma.expectTerms sigma sorts terms := by
    intro sorts terms
    cases sorts with
    | nil => cases terms <;> rfl
    | cons sort sorts =>
        cases terms with
        | nil => rfl
        | cons term rest =>
            simp only [renameResidualTerms, Lara.Sigma.expectTerms]
            rw [sortOf_renameResidual sigmaSound,
              expectTerms_renameResidual sigmaSound]
end

private theorem wsAtom_renameResidual
    (sigmaSound : CoreSigmaRenamingSound ρg sigma) (atom : Atom) :
    Lara.Sigma.wsAtom sigma (renameResidualAtom ρg atom) =
      Lara.Sigma.wsAtom sigma atom := by
  cases atom with
  | atom predicate terms =>
      simp only [renameResidualAtom, Lara.Sigma.wsAtom]
      change
        (match sigma.lookupPred ⟨predicate⟩ with
        | none => false
        | some declaration =>
            Lara.Sigma.expectTerms sigma declaration.args
              (renameResidualTerms ρg terms)) =
          (match sigma.lookupPred ⟨predicate⟩ with
          | none => false
          | some declaration =>
              Lara.Sigma.expectTerms sigma declaration.args terms)
      cases found : sigma.lookupPred ⟨predicate⟩ with
      | none => simp [found]
      | some declaration =>
          simp only [found]
          exact expectTerms_renameResidual sigmaSound declaration.args terms

private theorem groundWellSorted_rename
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (ground : List Atom) :
    Lara.groundWellSorted sigma (ground.map (renameResidualAtom ρg)) =
      Lara.groundWellSorted sigma ground := by
  unfold Lara.groundWellSorted
  induction ground with
  | nil => rfl
  | cons atom rest ih =>
      simp only [List.map_cons, List.all_cons]
      rw [wsAtom_renameResidual sigmaSound, ih]

private theorem ruleParamSorts_renameCoreRule
    (sigma : Lara.Sigma.Sigma) (rule : Support.Rule) :
    Lara.Sigma.ruleParamSorts sigma (renameCoreRule ρg rule) =
      Lara.Sigma.ruleParamSorts sigma rule := by
  simp [Lara.Sigma.ruleParamSorts, renameCoreRule, List.map_map,
    Function.comp_def]

private theorem exceptionEnv_eq_ruleLookup
    (sigma : Lara.Sigma.Sigma) (policy : Lara.Policy.Policy)
    (ruleId : Support.RuleId) :
    Lara.exceptionEnv sigma policy ruleId =
      match policy.ruleLookup ruleId with
      | some rule => (Lara.Sigma.ruleParamSorts sigma rule).getD []
      | none => [] := by
  unfold Lara.exceptionEnv Lara.Policy.Policy.ruleLookup
  induction policy.rules with
  | nil => rfl
  | cons declaration rest ih =>
      simp only [List.find?_cons, Lara.Policy.lookupRuleDecl]
      by_cases equal : declaration.id = ruleId <;> simp [equal, ih]

private theorem exceptionEnv_rename
    (sigma : Lara.Sigma.Sigma) (policy : Lara.Policy.Policy)
    (ruleId : Support.RuleId) :
    Lara.exceptionEnv sigma (renameCorePolicy ρg policy)
        (renameCoreRuleId ρg ruleId) =
      Lara.exceptionEnv sigma policy ruleId := by
  rw [exceptionEnv_eq_ruleLookup, exceptionEnv_eq_ruleLookup,
    ruleLookup_rename]
  cases policy.ruleLookup ruleId with
  | none => rfl
  | some rule =>
      simp only [Option.map_some]
      rw [ruleParamSorts_renameCoreRule]

private theorem policyWellSorted_rename
    (sigma : Lara.Sigma.Sigma) (policy : Lara.Policy.Policy) :
    Lara.policyWellSorted sigma (renameCorePolicy ρg policy) =
      Lara.policyWellSorted sigma policy := by
  simp only [Lara.policyWellSorted, renameCorePolicy, List.all_map,
    Function.comp_apply]
  have rules :
      policy.rules.all (fun declaration =>
          (Lara.Sigma.ruleParamSorts sigma
            (renameCoreRule ρg declaration.rule)).isSome) =
        policy.rules.all (fun declaration =>
          (Lara.Sigma.ruleParamSorts sigma declaration.rule).isSome) := by
    induction policy.rules with
    | nil => rfl
    | cons declaration rest ih =>
        simp only [List.all_cons]
        rw [ruleParamSorts_renameCoreRule, ih]
  have exceptions :
      policy.defeat.exceptions.all (fun exception =>
          (Lara.Sigma.checkAPat sigma
            (Lara.exceptionEnv sigma (renameCorePolicy ρg policy)
              (renameCoreRuleId ρg exception.1)) exception.2).isSome) =
        policy.defeat.exceptions.all (fun exception =>
          (Lara.Sigma.checkAPat sigma
            (Lara.exceptionEnv sigma policy exception.1)
            exception.2).isSome) := by
    induction policy.defeat.exceptions with
    | nil => rfl
    | cons exception rest ih =>
        simp only [List.all_cons]
        rw [exceptionEnv_rename, ih]
  have rulesComposed :
      policy.rules.all
          ((fun declaration =>
            (Lara.Sigma.ruleParamSorts sigma declaration.rule).isSome) ∘
            fun declaration =>
              ({ id := renameCoreRuleId ρg declaration.id
                 rule := renameCoreRule ρg declaration.rule } :
                Lara.Policy.RuleDecl)) =
        policy.rules.all (fun declaration =>
          (Lara.Sigma.ruleParamSorts sigma declaration.rule).isSome) := by
    simpa [Function.comp_def] using rules
  have exceptionsComposed :
      policy.defeat.exceptions.all
          ((fun exception =>
            (Lara.Sigma.checkAPat sigma
              (Lara.exceptionEnv sigma (renameCorePolicy ρg policy)
                exception.1) exception.2).isSome) ∘
            fun exception =>
              (renameCoreRuleId ρg exception.1, exception.2)) =
        policy.defeat.exceptions.all (fun exception =>
          (Lara.Sigma.checkAPat sigma
            (Lara.exceptionEnv sigma policy exception.1)
            exception.2).isSome) := by
    simpa [Function.comp_def] using exceptions
  have exceptionsExpanded := exceptionsComposed
  simp only [renameCorePolicy] at exceptionsExpanded
  rw [rulesComposed]
  exact congrArg
    (fun exceptionCheck =>
      (policy.rules.all fun declaration =>
          (Lara.Sigma.ruleParamSorts sigma declaration.rule).isSome) &&
        exceptionCheck &&
        policy.defeat.contraries.all (fun contrary =>
          (Lara.Sigma.checkAPats sigma []
            [contrary.1, contrary.2]).isSome))
    exceptionsExpanded

private theorem thetaWellSorted_rename
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (rule : Support.Rule) (env : Lara.Sigma.ParamSorts)
    (substitution : Support.Subst) :
    Lara.thetaWellSorted sigma (renameCoreRule ρg rule) env
        (substitution.map fun entry =>
          (entry.1, renameResidualTerm ρg entry.2)) =
      Lara.thetaWellSorted sigma rule env substitution := by
  unfold Lara.thetaWellSorted
  change
    (substitution.map fun entry =>
      (entry.1, renameResidualTerm ρg entry.2)).all (fun binding =>
        if rule.params.contains binding.1 then
          match Lara.Sigma.sortOf sigma binding.2 with
          | none => false
          | some found =>
              match Lara.Sigma.lookupParam env binding.1 with
              | none => true
              | some expected => decide (found = expected)
        else true) =
      substitution.all (fun binding =>
        if rule.params.contains binding.1 then
          match Lara.Sigma.sortOf sigma binding.2 with
          | none => false
          | some found =>
              match Lara.Sigma.lookupParam env binding.1 with
              | none => true
              | some expected => decide (found = expected)
        else true)
  induction substitution with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨key, term⟩ := entry
      simp only [List.map_cons, List.all_cons]
      by_cases contained : rule.params.contains key = true
      · simp only [contained, if_true]
        rw [sortOf_renameResidual sigmaSound, ih]
      · have containedFalse : rule.params.contains key = false :=
          by
            cases found : rule.params.contains key with
            | false => rfl
            | true => exact False.elim (contained found)
        simp only [containedFalse, Bool.false_eq_true, if_false,
          sortOf_renameResidual sigmaSound, ih]

mutual
  private theorem termWellSorted_rename
      (sigmaSound : CoreSigmaRenamingSound ρg sigma)
      (policy : Lara.Policy.Policy) : ∀ term,
      Lara.termWellSorted sigma (renameCorePolicy ρg policy)
          (renameCoreSupportTerm ρg term) =
        Lara.termWellSorted sigma policy term := by
    intro term
    cases term with
    | leaf leaf => rfl
    | inst ruleId substitution premises discharges holes assurance =>
        simp only [renameCoreSupportTerm, Lara.termWellSorted]
        rw [ruleLookup_rename]
        cases found : policy.ruleLookup ruleId with
        | none =>
            simp only [Option.map_none, Bool.true_and]
            rw [termsWellSorted_rename sigmaSound policy,
              dischargesWellSorted_rename sigmaSound policy]
        | some rule =>
            simp only [Option.map_some]
            rw [ruleParamSorts_renameCoreRule]
            cases sorted : Lara.Sigma.ruleParamSorts sigma rule with
            | none => rfl
            | some env =>
                simp only []
                rw [thetaWellSorted_rename sigmaSound,
                  termsWellSorted_rename sigmaSound policy,
                  dischargesWellSorted_rename sigmaSound policy]
  private theorem termsWellSorted_rename
      (sigmaSound : CoreSigmaRenamingSound ρg sigma)
      (policy : Lara.Policy.Policy) : ∀ terms,
      Lara.termsWellSorted sigma (renameCorePolicy ρg policy)
          (renameCoreSupportTerms ρg terms) =
        Lara.termsWellSorted sigma policy terms := by
    intro terms
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp only [renameCoreSupportTerms, Lara.termsWellSorted]
        rw [termWellSorted_rename sigmaSound policy,
          termsWellSorted_rename sigmaSound policy]
  private theorem dischargesWellSorted_rename
      (sigmaSound : CoreSigmaRenamingSound ρg sigma)
      (policy : Lara.Policy.Policy) : ∀ discharges,
      Lara.dischargesWellSorted sigma (renameCorePolicy ρg policy)
          (renameCoreSupportDischarges ρg discharges) =
        Lara.dischargesWellSorted sigma policy discharges := by
    intro discharges
    cases discharges with
    | nil => rfl
    | cons discharge rest =>
        obtain ⟨question, term⟩ := discharge
        simp only [renameCoreSupportDischarges, Lara.dischargesWellSorted]
        rw [termWellSorted_rename sigmaSound policy,
          dischargesWellSorted_rename sigmaSound policy]
end

private theorem argsWellSorted_rename
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policy : Lara.Policy.Policy) (arguments : List Support.SupportTerm) :
    Lara.argsWellSorted sigma (renameCorePolicy ρg policy)
        (arguments.map (renameCoreSupportTerm ρg)) =
      Lara.argsWellSorted sigma policy arguments := by
  unfold Lara.argsWellSorted
  rw [← renameCoreSupportTerms_eq_map_support,
    termsWellSorted_rename sigmaSound policy]

private def renameScopeViolation (ρg : Binding.GlobalRenaming)
    (violation : Lara.Policy.ScopeViolation) : Lara.Policy.ScopeViolation :=
  { ruleId := renameCoreRuleId ρg violation.ruleId
    param := violation.param }

private def renameCoreRuleDecl (ρg : Binding.GlobalRenaming)
    (declaration : Lara.Policy.RuleDecl) : Lara.Policy.RuleDecl :=
  { id := renameCoreRuleId ρg declaration.id
    rule := renameCoreRule ρg declaration.rule }

private theorem ruleEscapee_renameCoreRule (rule : Support.Rule) :
    Lara.Policy.ruleEscapee? (renameCoreRule ρg rule) =
      Lara.Policy.ruleEscapee? rule := by
  simp [Lara.Policy.ruleEscapee?, renameCoreRule, List.map_map,
    Function.comp_def]

private theorem findRuleDecl_rename
    (rules : List Lara.Policy.RuleDecl) (ruleId : Support.RuleId) :
    (rules.map (renameCoreRuleDecl ρg)).find?
        (fun declaration =>
          decide (declaration.id = renameCoreRuleId ρg ruleId)) =
      (rules.find? fun declaration =>
        decide (declaration.id = ruleId)).map
        (renameCoreRuleDecl ρg) := by
  induction rules with
  | nil => rfl
  | cons declaration rest ih =>
      simp only [List.map_cons, List.find?_cons]
      by_cases equal : declaration.id = ruleId
      · have renamedEqual := congrArg (renameCoreRuleId ρg) equal
        simp [renameCoreRuleDecl, equal, renamedEqual]
      · have renamedDifferent : renameCoreRuleId ρg declaration.id ≠
            renameCoreRuleId ρg ruleId :=
          fun renamed => equal
            (renameCoreRuleId_injective_support ρg renamed)
        simp [renameCoreRuleDecl, equal, renamedDifferent, ih]

private def ruleScopeViolation?
    (declaration : Lara.Policy.RuleDecl) :
    Option Lara.Policy.ScopeViolation :=
  (Lara.Policy.ruleEscapee? declaration.rule).map fun escaped =>
    ⟨declaration.id, escaped⟩

private def exceptionScopeViolation?
    (rules : List Lara.Policy.RuleDecl)
    (exception : Support.RuleId × Support.APat) :
    Option Lara.Policy.ScopeViolation :=
  match rules.find? (fun declaration =>
      decide (declaration.id = exception.1)) with
  | none => none
  | some declaration =>
      (Lara.Policy.aPatEscapee? declaration.rule.params exception.2).map
        fun escaped => ⟨exception.1, escaped⟩

private theorem ruleScopeViolation_rename
    (declaration : Lara.Policy.RuleDecl) :
    ruleScopeViolation? (renameCoreRuleDecl ρg declaration) =
      (ruleScopeViolation? declaration).map (renameScopeViolation ρg) := by
  unfold ruleScopeViolation?
  rw [show (renameCoreRuleDecl ρg declaration).rule =
      renameCoreRule ρg declaration.rule by rfl,
    ruleEscapee_renameCoreRule]
  cases Lara.Policy.ruleEscapee? declaration.rule <;>
    simp [renameCoreRuleDecl, renameScopeViolation]

private theorem exceptionScopeViolation_rename
    (rules : List Lara.Policy.RuleDecl)
    (exception : Support.RuleId × Support.APat) :
    exceptionScopeViolation? (rules.map (renameCoreRuleDecl ρg))
        (renameCoreRuleId ρg exception.1, exception.2) =
      (exceptionScopeViolation? rules exception).map
        (renameScopeViolation ρg) := by
  unfold exceptionScopeViolation?
  rw [findRuleDecl_rename]
  cases rules.find? (fun declaration =>
      decide (declaration.id = exception.1)) with
  | none => rfl
  | some declaration =>
      simp only [Option.map_some]
      cases escaped : Lara.Policy.aPatEscapee?
          declaration.rule.params exception.2 <;>
        simp [escaped, renameCoreRuleDecl, renameCoreRule,
          renameScopeViolation]

private theorem findSomeMap_rename
    (renameInput : α → β) (source : α → Option γ)
    (target : β → Option δ) (renameOutput : γ → δ)
    (commutes : ∀ value,
      target (renameInput value) = (source value).map renameOutput) :
    ∀ values : List α,
      (values.map renameInput).findSome? target =
        (values.findSome? source).map renameOutput := by
  intro values
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.map_cons, List.findSome?_cons]
      rw [commutes]
      cases source value <;> simp [ih]

private theorem ruleScopeScan_rename
    (rules : List Lara.Policy.RuleDecl) :
    (rules.map (renameCoreRuleDecl ρg)).findSome? ruleScopeViolation? =
      (rules.findSome? ruleScopeViolation?).map
        (renameScopeViolation ρg) :=
  findSomeMap_rename (renameCoreRuleDecl ρg) ruleScopeViolation?
    ruleScopeViolation? (renameScopeViolation ρg)
    (ruleScopeViolation_rename (ρg := ρg)) rules

private theorem exceptionScopeScan_rename
    (rules : List Lara.Policy.RuleDecl)
    (exceptions : List (Support.RuleId × Support.APat)) :
    (exceptions.map fun exception =>
        (renameCoreRuleId ρg exception.1, exception.2)).findSome?
        (exceptionScopeViolation? (rules.map (renameCoreRuleDecl ρg))) =
      (exceptions.findSome? (exceptionScopeViolation? rules)).map
        (renameScopeViolation ρg) :=
  findSomeMap_rename
    (fun exception => (renameCoreRuleId ρg exception.1, exception.2))
    (exceptionScopeViolation? rules)
    (exceptionScopeViolation? (rules.map (renameCoreRuleDecl ρg)))
    (renameScopeViolation ρg)
    (exceptionScopeViolation_rename (ρg := ρg) rules) exceptions

private theorem firstOutOfScope_rename
    (policy : Lara.Policy.Policy) :
    Lara.Policy.firstOutOfScope? (renameCorePolicy ρg policy) =
      (Lara.Policy.firstOutOfScope? policy).map
        (renameScopeViolation ρg) := by
  change
    (match
      (policy.rules.map (renameCoreRuleDecl ρg)).findSome?
          ruleScopeViolation? with
    | some violation => some violation
    | none =>
        (policy.defeat.exceptions.map fun exception =>
          (renameCoreRuleId ρg exception.1,
            exception.2)).findSome?
          (exceptionScopeViolation?
            (policy.rules.map (renameCoreRuleDecl ρg)))) =
      (match policy.rules.findSome? ruleScopeViolation? with
      | some violation => some violation
      | none => policy.defeat.exceptions.findSome?
          (exceptionScopeViolation? policy.rules)).map
        (renameScopeViolation ρg)
  rw [ruleScopeScan_rename]
  cases policy.rules.findSome? ruleScopeViolation? with
  | some violation => rfl
  | none =>
      simp only [Option.map_none]
      exact exceptionScopeScan_rename policy.rules policy.defeat.exceptions

private theorem scopesWellFormed_rename_iff
    (policy : Lara.Policy.Policy) :
    Lara.Policy.ScopesWellFormed (renameCorePolicy ρg policy) ↔
      Lara.Policy.ScopesWellFormed policy := by
  unfold Lara.Policy.ScopesWellFormed
  rw [firstOutOfScope_rename]
  cases Lara.Policy.firstOutOfScope? policy <;> simp

private theorem strictReachable_rename_iff
    (policy : Lara.Policy.Policy) (pattern : Support.APat) :
    Lara.Policy.StrictReachable (renameCorePolicy ρg policy) pattern ↔
      Lara.Policy.StrictReachable policy pattern := by
  constructor
  · intro reachable
    cases reachable with
    | @conclusion declaration member strict =>
        obtain ⟨source, sourceMember, sourceEq⟩ := List.mem_map.mp member
        have sourceReachable : Lara.Policy.StrictReachable policy
            source.rule.concl :=
          Lara.Policy.StrictReachable.conclusion sourceMember
            (by
              have strict' := strict
              rw [← sourceEq] at strict'
              simpa [renameCoreRuleDecl, renameCoreRule] using strict')
        have goalEq : declaration.rule.concl = source.rule.concl := by
          rw [← sourceEq]
          rfl
        simpa [goalEq] using sourceReachable
  · intro reachable
    cases reachable with
    | @conclusion declaration member strict =>
        have targetReachable :
            Lara.Policy.StrictReachable (renameCorePolicy ρg policy)
              (renameCoreRule ρg declaration.rule).concl :=
          Lara.Policy.StrictReachable.conclusion
            (d := renameCoreRuleDecl ρg declaration)
            (List.mem_map.mpr ⟨declaration, member, rfl⟩)
            (by simpa [renameCoreRuleDecl, renameCoreRule] using strict)
        simpa [renameCoreRule] using targetReachable

private theorem policyWellFormed_rename_iff
    (canon : String → String) (policy : Lara.Policy.Policy) :
    Lara.Policy.WellFormed canon (renameCorePolicy ρg policy) ↔
      Lara.Policy.WellFormed canon policy := by
  unfold Lara.Policy.WellFormed
  constructor
  · intro target pattern reachable contrary contraryMember
    exact target pattern
      ((strictReachable_rename_iff policy pattern).mpr reachable)
      contrary (by simpa [renameCorePolicy] using contraryMember)
  · intro source pattern reachable contrary contraryMember
    exact source pattern
      ((strictReachable_rename_iff policy pattern).mp reachable)
      contrary (by simpa [renameCorePolicy] using contraryMember)

private theorem ruleIdsNodup_rename_iff
    (policy : Lara.Policy.Policy) :
    ((renameCorePolicy ρg policy).rules.map (·.id)).Nodup ↔
      (policy.rules.map (·.id)).Nodup := by
  have idsEq : (renameCorePolicy ρg policy).rules.map (·.id) =
      (policy.rules.map (·.id)).map (renameCoreRuleId ρg) := by
    simp [renameCorePolicy, List.map_map, Function.comp_def]
  rw [idsEq]
  exact
    (nodup_map_iff_of_injective (renameCoreRuleId_injective_support ρg)
      (xs := policy.rules.map (·.id)))

private theorem argumentsNodup_rename_iff
    (arguments : List Support.SupportTerm) :
    (arguments.map (renameCoreSupportTerm ρg)).Nodup ↔ arguments.Nodup := by
  exact nodup_map_iff_of_injective fun _ _ equal =>
    (renameCoreSupportTerm_eq_iff ρg).mp equal

@[simp] private theorem attackTarget_rename
    (attack : Lara.Attack.Attack) :
    (renameCoreAttack ρg attack).target =
      renameCoreSupportTerm ρg attack.target := by
  cases attack <;> rfl

private theorem signatureStage_rename
    (sigmaSound : CoreSigmaRenamingSound ρg unit.sigma)
    (ground : List Atom) :
    Lara.Check.Unit.signatureStage
        (ground.map (renameResidualAtom ρg)) (renameCoreUnit ρg unit) =
      Lara.Check.Unit.signatureStage ground unit := by
  simp [Lara.Check.Unit.signatureStage, renameCoreUnit,
    policyWellSorted_rename (ρg := ρg),
    groundWellSorted_rename sigmaSound,
    argsWellSorted_rename sigmaSound]

private theorem checkUnit_signatureStage_of_ok
    {canon : String → String} {gamma : Support.LeafId → Option Atom}
    {registry : Support.BackendRegistry canon} {ground : List Atom}
    {unit : Lara.Unit}
    {checked : Lara.Unit.CheckedUnit canon gamma
      (Support.certOkOf registry)}
    (h : Lara.Check.Unit.checkUnit gamma registry ground unit = .ok checked) :
    Lara.Check.Unit.signatureStage ground unit = none := by
  unfold Lara.Check.Unit.checkUnit at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · assumption

/-- Computationally observable fields of two accepted units are related by a
typed global renaming.  Proof fields are deliberately absent: the relation is
stable under proof irrelevance and records the retained node cache in order. -/
structure CheckedUnitRelated (ρg : Binding.GlobalRenaming)
    (source : Lara.Unit.CheckedUnit canon gamma
      (Support.certOkOf registry))
    (target : Lara.Unit.CheckedUnit canon (renameGamma ρg gamma)
      (Support.certOkOf registry)) : Prop where
  sigma : target.sigma = source.sigma
  policy : target.policy = renameCorePolicy ρg source.policy
  arguments : target.program.args =
    source.program.args.map (renameCoreSupportTerm ρg)
  attacks : target.program.atts =
    source.program.atts.map (renameCoreAttack ρg)
  nodeTerms : target.nodes.map (fun node => node.term) =
    source.nodes.map (fun node => renameCoreSupportTerm ρg node.term)
  nodeConclusions : target.nodes.map (fun node => node.conclusion) =
    source.nodes.map (fun node => renameResidualAtom ρg node.conclusion)

private theorem checkedNodeConclusions_rename
    {canon : String → String} {env : Env canon}
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (policySorted : Lara.policyWellSorted sigma sourcePolicy = true)
    (envSound : EnvRenamingSound env ρg)
    (policyEq : targetPolicy = renameCorePolicy ρg sourcePolicy) :
    ∀ (sourceNodes : List (Lara.Compile.CheckedNode canon
          sourcePolicy.ruleLookup gamma (Support.certOkOf env.registry)))
      (targetNodes : List (Lara.Compile.CheckedNode canon
          targetPolicy.ruleLookup (renameGamma ρg gamma)
          (Support.certOkOf env.registry))),
      targetNodes.map (fun node => node.term) =
          sourceNodes.map (fun node => renameCoreSupportTerm ρg node.term) →
        targetNodes.map (fun node => node.conclusion) =
          sourceNodes.map (fun node =>
            renameResidualAtom ρg node.conclusion) := by
  intro sourceNodes
  induction sourceNodes with
  | nil =>
      intro targetNodes terms
      cases targetNodes with
      | nil => rfl
      | cons target rest => simp at terms
  | cons source rest ih =>
      intro targetNodes terms
      cases targetNodes with
      | nil => simp at terms
      | cons target targetRest =>
          simp only [List.map_cons, List.cons.injEq] at terms ⊢
          have transported :=
            (hasSupport_rename_iff sigmaSound policySorted envSound gamma
              source.term source.conclusion []).mpr source.valid
          have targetValid : Support.HasSupport canon
              (renameCorePolicy ρg sourcePolicy).ruleLookup
              (renameGamma ρg gamma) (Support.certOkOf env.registry)
              target.term target.conclusion [] := by
            simpa only [policyEq] using target.valid
          have transportedAtTarget : Support.HasSupport canon
              (renameCorePolicy ρg sourcePolicy).ruleLookup
              (renameGamma ρg gamma) (Support.certOkOf env.registry)
              target.term (renameResidualAtom ρg source.conclusion) [] := by
            simpa only [terms.1, List.map_nil] using transported
          exact ⟨(Support.hasSupport_unique targetValid
              transportedAtTarget).1,
            ih targetRest terms.2⟩

/-- A concrete successful core check transports to a concrete successful
renamed check together with the proof-irrelevance-safe accepted carrier
relation. -/
theorem checkUnit_ok_rename
    {canon : String → String} {env : Env canon}
    {gamma : Support.LeafId → Option Atom} {ground : List Atom}
    {unit : Lara.Unit}
    {checked : Lara.Unit.CheckedUnit canon gamma
      (Support.certOkOf env.registry)}
    (sigmaSound : CoreSigmaRenamingSound ρg unit.sigma)
    (envSound : EnvRenamingSound env ρg)
    (h : Lara.Check.Unit.checkUnit gamma env.registry ground unit =
      .ok checked) :
    ∃ renamedChecked,
      Lara.Check.Unit.checkUnit (renameGamma ρg gamma) env.registry
          (ground.map (renameResidualAtom ρg)) (renameCoreUnit ρg unit) =
        .ok renamedChecked ∧
      CheckedUnitRelated (canon := canon) (gamma := gamma)
        (registry := env.registry) ρg checked renamedChecked := by
  obtain ⟨sourceSigmaEq, _, _, _, _, sourcePolicyEq, sourceRuleIds,
    sourcePolicyWf, sourceArgumentsEq, sourceAttacksEq,
    sourceAttackComplete, sourceNodeTerms⟩ :=
      Lara.Check.Unit.checkUnit_sound h
  have rawPolicySorted :
      Lara.policyWellSorted unit.sigma unit.policy = true := by
    exact Lara.Check.Unit.signatureStage_policy
      (checkUnit_signatureStage_of_ok h)
  have rawScopes : Lara.Policy.ScopesWellFormed unit.policy := by
    simpa only [sourcePolicyEq] using checked.scopes_wf
  have rawRuleIds : (unit.policy.rules.map (·.id)).Nodup := by
    simpa only [sourcePolicyEq] using sourceRuleIds
  have rawPolicyWf : Lara.Policy.WellFormed canon unit.policy := by
    simpa only [sourcePolicyEq] using sourcePolicyWf
  have rawArgumentsNodup : unit.args.Nodup := by
    simpa only [sourceArgumentsEq] using checked.program.nodup
  have rawSupport : ∀ term ∈ unit.args, ∃ conclusion,
      Support.HasSupport canon unit.policy.ruleLookup gamma
        (Support.certOkOf env.registry) term conclusion [] := by
    intro term member
    obtain ⟨conclusion, valid⟩ := checked.program.complete term (by
      simpa only [sourceArgumentsEq] using member)
    exact ⟨conclusion, by simpa only [sourcePolicyEq] using valid⟩
  have rawTyped : ∀ attack ∈ unit.atts,
      Lara.Attack.HasAttack canon unit.policy.ruleLookup gamma
        (Support.certOkOf env.registry) unit.policy.defeat attack := by
    intro attack member
    have valid := checked.program.typed attack (by
      simpa only [sourceAttacksEq] using member)
    simpa only [sourcePolicyEq] using valid
  have rawSourceDeclared : ∀ attack ∈ unit.atts,
      attack.source ∈ unit.args := by
    intro attack member
    have declared := checked.program.source_declared attack (by
      simpa only [sourceAttacksEq] using member)
    simpa only [sourceArgumentsEq] using declared
  have rawTargetDeclared : ∀ attack ∈ unit.atts,
      attack.target ∈ unit.args := by
    intro attack member
    have declared := checked.program.target_declared attack (by
      simpa only [sourceAttacksEq] using member)
    simpa only [sourceArgumentsEq] using declared
  have rawAttackComplete : Lara.Compile.AttackComplete canon
      unit.policy.ruleLookup gamma (Support.certOkOf env.registry)
      unit.policy.defeat unit.args unit.atts := by
    simpa only [sourcePolicyEq, sourceArgumentsEq, sourceAttacksEq] using
      sourceAttackComplete
  have sourceSignature :
      Lara.Check.Unit.signatureStage ground unit = none := by
    exact checkUnit_signatureStage_of_ok h
  have targetSignature :
      Lara.Check.Unit.signatureStage
          (ground.map (renameResidualAtom ρg)) (renameCoreUnit ρg unit) =
        none := by
    rw [signatureStage_rename sigmaSound]
    exact sourceSignature
  have targetScopes :
      Lara.Policy.firstOutOfScope? (renameCorePolicy ρg unit.policy) = none :=
    (scopesWellFormed_rename_iff unit.policy).mpr rawScopes
  have targetRuleIds :
      ((renameCorePolicy ρg unit.policy).rules.map (·.id)).Nodup :=
    (ruleIdsNodup_rename_iff unit.policy).mpr rawRuleIds
  have targetPolicyWf :
      Lara.Policy.WellFormed canon (renameCorePolicy ρg unit.policy) :=
    (policyWellFormed_rename_iff canon unit.policy).mpr rawPolicyWf
  have targetArgumentsNodup :
      (unit.args.map (renameCoreSupportTerm ρg)).Nodup :=
    (argumentsNodup_rename_iff unit.args).mpr rawArgumentsNodup
  have targetSupport : ∀ term ∈ unit.args.map (renameCoreSupportTerm ρg),
      ∃ conclusion, Support.HasSupport canon
        (renameCorePolicy ρg unit.policy).ruleLookup (renameGamma ρg gamma)
        (Support.certOkOf env.registry) term conclusion [] := by
    intro term member
    obtain ⟨sourceTerm, sourceMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨sourceConclusion, sourceValid⟩ :=
      rawSupport sourceTerm sourceMember
    refine ⟨renameResidualAtom ρg sourceConclusion, ?_⟩
    simpa using (hasSupport_rename_iff sigmaSound rawPolicySorted envSound
      gamma sourceTerm sourceConclusion []).mpr sourceValid
  have targetTyped : ∀ attack ∈ unit.atts.map (renameCoreAttack ρg),
      Lara.Attack.HasAttack canon
        (renameCorePolicy ρg unit.policy).ruleLookup (renameGamma ρg gamma)
        (Support.certOkOf env.registry)
        (renameCorePolicy ρg unit.policy).defeat attack := by
    intro attack member
    obtain ⟨sourceAttack, sourceMember, rfl⟩ := List.mem_map.mp member
    exact (hasAttack_rename_iff sigmaSound rawPolicySorted envSound
      gamma sourceAttack).mpr
      (rawTyped sourceAttack sourceMember)
  have targetSourceDeclared :
      ∀ attack ∈ unit.atts.map (renameCoreAttack ρg),
        attack.source ∈ unit.args.map (renameCoreSupportTerm ρg) := by
    intro attack member
    obtain ⟨sourceAttack, sourceMember, rfl⟩ := List.mem_map.mp member
    simpa using List.mem_map.mpr
      ⟨sourceAttack.source, rawSourceDeclared sourceAttack sourceMember, rfl⟩
  have targetTargetDeclared :
      ∀ attack ∈ unit.atts.map (renameCoreAttack ρg),
        attack.target ∈ unit.args.map (renameCoreSupportTerm ρg) := by
    intro attack member
    obtain ⟨sourceAttack, sourceMember, rfl⟩ := List.mem_map.mp member
    simpa using List.mem_map.mpr
      ⟨sourceAttack.target, rawTargetDeclared sourceAttack sourceMember, rfl⟩
  have targetAttackComplete : Lara.Compile.AttackComplete canon
      (renameCorePolicy ρg unit.policy).ruleLookup (renameGamma ρg gamma)
      (Support.certOkOf env.registry) (renameCorePolicy ρg unit.policy).defeat
      (unit.args.map (renameCoreSupportTerm ρg))
      (unit.atts.map (renameCoreAttack ρg)) :=
    (attackComplete_rename_iff sigmaSound rawPolicySorted envSound gamma
      unit.args unit.atts).mpr rawAttackComplete
  obtain ⟨renamedChecked, renamedCheck⟩ :=
    Lara.Check.Unit.checkUnit_complete
      (unit := renameCoreUnit ρg unit) targetSignature targetScopes
      targetRuleIds targetPolicyWf targetArgumentsNodup targetSupport
      targetTyped targetSourceDeclared targetTargetDeclared
      targetAttackComplete
  obtain ⟨targetSigmaEq, _, _, _, _, targetPolicyEq, _, _,
    targetArgumentsEq, targetAttacksEq, _, targetNodeTerms⟩ :=
      Lara.Check.Unit.checkUnit_sound renamedCheck
  have sigmaRelated : renamedChecked.sigma = checked.sigma :=
    targetSigmaEq.trans sourceSigmaEq.symm
  have policyRelated :
      renamedChecked.policy = renameCorePolicy ρg checked.policy := by
    calc
      renamedChecked.policy = (renameCoreUnit ρg unit).policy := targetPolicyEq
      _ = renameCorePolicy ρg unit.policy := rfl
      _ = renameCorePolicy ρg checked.policy :=
        congrArg (renameCorePolicy ρg) sourcePolicyEq.symm
  have argumentsRelated : renamedChecked.program.args =
      checked.program.args.map (renameCoreSupportTerm ρg) := by
    calc
      renamedChecked.program.args = (renameCoreUnit ρg unit).args :=
        targetArgumentsEq
      _ = unit.args.map (renameCoreSupportTerm ρg) := rfl
      _ = checked.program.args.map (renameCoreSupportTerm ρg) :=
        congrArg (List.map (renameCoreSupportTerm ρg)) sourceArgumentsEq.symm
  have attacksRelated : renamedChecked.program.atts =
      checked.program.atts.map (renameCoreAttack ρg) := by
    calc
      renamedChecked.program.atts = (renameCoreUnit ρg unit).atts :=
        targetAttacksEq
      _ = unit.atts.map (renameCoreAttack ρg) := rfl
      _ = checked.program.atts.map (renameCoreAttack ρg) :=
        congrArg (List.map (renameCoreAttack ρg)) sourceAttacksEq.symm
  have nodeTermsRelated : renamedChecked.nodes.map (fun node => node.term) =
      checked.nodes.map (fun node => renameCoreSupportTerm ρg node.term) := by
    calc
      renamedChecked.nodes.map (fun node => node.term) =
          renamedChecked.program.args := targetNodeTerms
      _ = checked.program.args.map (renameCoreSupportTerm ρg) :=
        argumentsRelated
      _ = (checked.nodes.map (fun node => node.term)).map
          (renameCoreSupportTerm ρg) :=
        congrArg (List.map (renameCoreSupportTerm ρg)) sourceNodeTerms.symm
      _ = checked.nodes.map (fun node =>
          renameCoreSupportTerm ρg node.term) := by
        simp [List.map_map, Function.comp_def]
  have checkedSigmaSound : CoreSigmaRenamingSound ρg checked.sigma := by
    rw [sourceSigmaEq]
    exact sigmaSound
  have nodeConclusionsRelated := checkedNodeConclusions_rename
    checkedSigmaSound checked.policy_well_sorted envSound policyRelated
    checked.nodes renamedChecked.nodes nodeTermsRelated
  exact ⟨renamedChecked, renamedCheck,
    { sigma := sigmaRelated
      policy := policyRelated
      arguments := argumentsRelated
      attacks := attacksRelated
      nodeTerms := nodeTermsRelated
      nodeConclusions := nodeConclusionsRelated }⟩

private theorem checkUnit_ok_reflect
    {canon : String → String} {env : Env canon}
    {gamma : Support.LeafId → Option Atom} {ground : List Atom}
    {unit : Lara.Unit}
    {renamedChecked : Lara.Unit.CheckedUnit canon (renameGamma ρg gamma)
      (Support.certOkOf env.registry)}
    (sigmaSound : CoreSigmaRenamingSound ρg unit.sigma)
    (envSound : EnvRenamingSound env ρg)
    (h : Lara.Check.Unit.checkUnit (renameGamma ρg gamma) env.registry
      (ground.map (renameResidualAtom ρg)) (renameCoreUnit ρg unit) =
        .ok renamedChecked) :
    ∃ checked,
      Lara.Check.Unit.checkUnit gamma env.registry ground unit = .ok checked := by
  obtain ⟨targetSigmaEq, _, _, _, _, targetPolicyEq, targetRuleIds,
    targetPolicyWf, targetArgumentsEq, targetAttacksEq,
    targetAttackComplete, _⟩ := Lara.Check.Unit.checkUnit_sound h
  have rawTargetPolicySorted :
      Lara.policyWellSorted unit.sigma (renameCorePolicy ρg unit.policy) = true := by
    exact Lara.Check.Unit.signatureStage_policy
      (checkUnit_signatureStage_of_ok h)
  have targetSignature : Lara.Check.Unit.signatureStage
      (ground.map (renameResidualAtom ρg)) (renameCoreUnit ρg unit) = none := by
    exact checkUnit_signatureStage_of_ok h
  have sourceSignature :
      Lara.Check.Unit.signatureStage ground unit = none := by
    rw [signatureStage_rename sigmaSound] at targetSignature
    exact targetSignature
  have rawSourcePolicySorted :
      Lara.policyWellSorted unit.sigma unit.policy = true :=
    Lara.Check.Unit.signatureStage_policy sourceSignature
  have rawTargetScopes :
      Lara.Policy.ScopesWellFormed (renameCorePolicy ρg unit.policy) := by
    simpa only [targetPolicyEq, renameCoreUnit] using renamedChecked.scopes_wf
  have sourceScopes : Lara.Policy.firstOutOfScope? unit.policy = none :=
    (scopesWellFormed_rename_iff unit.policy).mp rawTargetScopes
  have rawTargetRuleIds :
      ((renameCorePolicy ρg unit.policy).rules.map (·.id)).Nodup := by
    simpa only [targetPolicyEq, renameCoreUnit] using targetRuleIds
  have sourceRuleIds : (unit.policy.rules.map (·.id)).Nodup :=
    (ruleIdsNodup_rename_iff unit.policy).mp rawTargetRuleIds
  have rawTargetPolicyWf :
      Lara.Policy.WellFormed canon (renameCorePolicy ρg unit.policy) := by
    simpa only [targetPolicyEq, renameCoreUnit] using targetPolicyWf
  have sourcePolicyWf : Lara.Policy.WellFormed canon unit.policy :=
    (policyWellFormed_rename_iff canon unit.policy).mp rawTargetPolicyWf
  have rawTargetArgumentsNodup :
      (unit.args.map (renameCoreSupportTerm ρg)).Nodup := by
    simpa only [targetArgumentsEq, renameCoreUnit] using
      renamedChecked.program.nodup
  have sourceArgumentsNodup : unit.args.Nodup :=
    (argumentsNodup_rename_iff unit.args).mp rawTargetArgumentsNodup
  have rawTargetSupport : ∀ term ∈ unit.args.map (renameCoreSupportTerm ρg),
      ∃ conclusion, Support.HasSupport canon
        (renameCorePolicy ρg unit.policy).ruleLookup (renameGamma ρg gamma)
        (Support.certOkOf env.registry) term conclusion [] := by
    intro term member
    obtain ⟨conclusion, valid⟩ := renamedChecked.program.complete term (by
      simpa only [targetArgumentsEq, renameCoreUnit] using member)
    exact ⟨conclusion, by
      simpa only [targetPolicyEq, renameCoreUnit] using valid⟩
  have sourceSupport : ∀ term ∈ unit.args, ∃ conclusion,
      Support.HasSupport canon unit.policy.ruleLookup gamma
        (Support.certOkOf env.registry) term conclusion [] := by
    intro term member
    obtain ⟨targetConclusion, targetValid⟩ := rawTargetSupport
      (renameCoreSupportTerm ρg term) (List.mem_map.mpr ⟨term, member, rfl⟩)
    obtain ⟨sourceConclusion, sourceObligations, _, obligationsEq,
      sourceValid⟩ := hasSupport_reflect_exists sigmaSound
        rawSourcePolicySorted envSound targetValid term rfl
    have obligationsEmpty : sourceObligations = [] := by
      cases sourceObligations with
      | nil => rfl
      | cons question rest => simp at obligationsEq
    subst sourceObligations
    exact ⟨sourceConclusion, sourceValid⟩
  have rawTargetTyped : ∀ attack ∈ unit.atts.map (renameCoreAttack ρg),
      Lara.Attack.HasAttack canon
        (renameCorePolicy ρg unit.policy).ruleLookup (renameGamma ρg gamma)
        (Support.certOkOf env.registry)
        (renameCorePolicy ρg unit.policy).defeat attack := by
    intro attack member
    have valid := renamedChecked.program.typed attack (by
      simpa only [targetAttacksEq, renameCoreUnit] using member)
    simpa only [targetPolicyEq, renameCoreUnit] using valid
  have sourceTyped : ∀ attack ∈ unit.atts,
      Lara.Attack.HasAttack canon unit.policy.ruleLookup gamma
        (Support.certOkOf env.registry) unit.policy.defeat attack := by
    intro attack member
    exact (hasAttack_rename_iff sigmaSound rawSourcePolicySorted envSound
      gamma attack).mp
      (rawTargetTyped (renameCoreAttack ρg attack)
        (List.mem_map.mpr ⟨attack, member, rfl⟩))
  have rawTargetSourceDeclared :
      ∀ attack ∈ unit.atts.map (renameCoreAttack ρg),
        attack.source ∈ unit.args.map (renameCoreSupportTerm ρg) := by
    intro attack member
    have declared := renamedChecked.program.source_declared attack (by
      simpa only [targetAttacksEq, renameCoreUnit] using member)
    simpa only [targetArgumentsEq, renameCoreUnit] using declared
  have rawTargetTargetDeclared :
      ∀ attack ∈ unit.atts.map (renameCoreAttack ρg),
        attack.target ∈ unit.args.map (renameCoreSupportTerm ρg) := by
    intro attack member
    have declared := renamedChecked.program.target_declared attack (by
      simpa only [targetAttacksEq, renameCoreUnit] using member)
    simpa only [targetArgumentsEq, renameCoreUnit] using declared
  have sourceSourceDeclared : ∀ attack ∈ unit.atts,
      attack.source ∈ unit.args := by
    intro attack member
    have renamedMember := rawTargetSourceDeclared (renameCoreAttack ρg attack)
      (List.mem_map.mpr ⟨attack, member, rfl⟩)
    apply (admission_mem_map_injective_iff (renameCoreSupportTerm ρg)
      (fun _ _ equal => (renameCoreSupportTerm_eq_iff ρg).mp equal)
      attack.source unit.args).mp
    simpa using renamedMember
  have sourceTargetDeclared : ∀ attack ∈ unit.atts,
      attack.target ∈ unit.args := by
    intro attack member
    have renamedMember := rawTargetTargetDeclared (renameCoreAttack ρg attack)
      (List.mem_map.mpr ⟨attack, member, rfl⟩)
    apply (admission_mem_map_injective_iff (renameCoreSupportTerm ρg)
      (fun _ _ equal => (renameCoreSupportTerm_eq_iff ρg).mp equal)
      attack.target unit.args).mp
    simpa using renamedMember
  have rawTargetAttackComplete : Lara.Compile.AttackComplete canon
      (renameCorePolicy ρg unit.policy).ruleLookup (renameGamma ρg gamma)
      (Support.certOkOf env.registry) (renameCorePolicy ρg unit.policy).defeat
      (unit.args.map (renameCoreSupportTerm ρg))
      (unit.atts.map (renameCoreAttack ρg)) := by
    simpa only [targetPolicyEq, targetArgumentsEq, targetAttacksEq,
      renameCoreUnit] using targetAttackComplete
  have sourceAttackComplete : Lara.Compile.AttackComplete canon
      unit.policy.ruleLookup gamma (Support.certOkOf env.registry)
      unit.policy.defeat unit.args unit.atts :=
    (attackComplete_rename_iff sigmaSound rawSourcePolicySorted envSound gamma
      unit.args unit.atts).mp rawTargetAttackComplete
  exact Lara.Check.Unit.checkUnit_complete sourceSignature sourceScopes
    sourceRuleIds sourcePolicyWf sourceArgumentsNodup sourceSupport
    sourceTyped sourceSourceDeclared sourceTargetDeclared sourceAttackComplete

/-- Core-check acceptance is preserved and reflected by a structurally sound
typed global renaming.  Rejection payloads need not be literally equal. -/
theorem checkUnit_isOk_rename
    {canon : String → String} {env : Env canon}
    (gamma : Support.LeafId → Option Atom) (ground : List Atom)
    (unit : Lara.Unit)
    (sigmaSound : CoreSigmaRenamingSound ρg unit.sigma)
    (envSound : EnvRenamingSound env ρg) :
    exceptIsOk
        (Lara.Check.Unit.checkUnit (renameGamma ρg gamma) env.registry
          (ground.map (renameResidualAtom ρg)) (renameCoreUnit ρg unit)) =
      exceptIsOk
        (Lara.Check.Unit.checkUnit gamma env.registry ground unit) := by
  cases sourceResult :
      Lara.Check.Unit.checkUnit gamma env.registry ground unit with
  | ok checked =>
      obtain ⟨renamedChecked, renamedResult, _⟩ :=
        checkUnit_ok_rename sigmaSound envSound sourceResult
      simp [sourceResult, renamedResult, exceptIsOk]
  | error sourceError =>
      cases targetResult : Lara.Check.Unit.checkUnit
          (renameGamma ρg gamma) env.registry
          (ground.map (renameResidualAtom ρg)) (renameCoreUnit ρg unit) with
      | error targetError => simp [sourceResult, targetResult, exceptIsOk]
      | ok renamedChecked =>
          obtain ⟨checked, reflected⟩ := checkUnit_ok_reflect
            sigmaSound envSound targetResult
          rw [sourceResult] at reflected
          contradiction

private def DeclarationReconstructionSafe
    (ρg : Binding.GlobalRenaming) : Presentation.Decl → Prop
  | .arg argument =>
      (∀ spelling ∈ argBinderSpellings argument,
        Binding.renameText ρg spelling = spelling) ∧
      (∀ spelling ∈ argOpaqueCertPremiseSpellings argument,
        Binding.renameText ρg spelling = spelling)
  | _ => True

mutual
  private theorem substSupportTerm_binders
      (bindings : List Presentation.ValueBinding)
      (term : Presentation.SupportTerm) :
      supportTermBinderSpellings (substSupportTerm bindings term) =
        supportTermBinderSpellings term := by
    cases term with
    | leaf leaf => rfl
    | rule rule subst premises discharges holes assurance =>
        simp only [substSupportTerm, supportTermBinderSpellings]
        rw [substSupportTerms_binders, substSupportDischarges_binders]

  private theorem substSupportTerms_binders
      (bindings : List Presentation.ValueBinding)
      (terms : Presentation.SupportTerms) :
      supportTermsBinderSpellings (substSupportTerms bindings terms) =
        supportTermsBinderSpellings terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp only [substSupportTerms, supportTermsBinderSpellings]
        rw [substSupportTerm_binders, substSupportTerms_binders]

  private theorem substSupportDischarges_binders
      (bindings : List Presentation.ValueBinding)
      (discharges : Presentation.Discharges) :
      supportDischargesBinderSpellings
          (substSupportDischarges bindings discharges) =
        supportDischargesBinderSpellings discharges := by
    cases discharges with
    | nil => rfl
    | cons question term rest =>
        simp only [substSupportDischarges,
          supportDischargesBinderSpellings]
        rw [substSupportTerm_binders, substSupportDischarges_binders]
end

mutual
  private theorem substSupportTerm_opaque
      (bindings : List Presentation.ValueBinding)
      (term : Presentation.SupportTerm) :
      supportTermOpaqueCertPremiseSpellings
          (substSupportTerm bindings term) =
        supportTermOpaqueCertPremiseSpellings term := by
    cases term with
    | leaf leaf => rfl
    | rule rule subst premises discharges holes assurance =>
        simp only [substSupportTerm,
          supportTermOpaqueCertPremiseSpellings]
        rw [substSupportTerms_opaque, substSupportDischarges_opaque]

  private theorem substSupportTerms_opaque
      (bindings : List Presentation.ValueBinding)
      (terms : Presentation.SupportTerms) :
      supportTermsOpaqueCertPremiseSpellings
          (substSupportTerms bindings terms) =
        supportTermsOpaqueCertPremiseSpellings terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp only [substSupportTerms,
          supportTermsOpaqueCertPremiseSpellings]
        rw [substSupportTerm_opaque, substSupportTerms_opaque]

  private theorem substSupportDischarges_opaque
      (bindings : List Presentation.ValueBinding)
      (discharges : Presentation.Discharges) :
      dischargeOpaqueCertPremiseSpellings
          (substSupportDischarges bindings discharges) =
        dischargeOpaqueCertPremiseSpellings discharges := by
    cases discharges with
    | nil => rfl
    | cons question term rest =>
        simp only [substSupportDischarges,
          dischargeOpaqueCertPremiseSpellings]
        rw [substSupportTerm_opaque, substSupportDischarges_opaque]
end

private theorem substArgInstantiation_binders
    (bindings : List Presentation.ValueBinding)
    (instantiation : Presentation.ArgInstantiation) :
    (match substArgInstantiation bindings instantiation with
      | .explicitTheta term => supportTermBinderSpellings term
      | .inferTheta _ _ _ _ assurance => assuranceBinderSpellings assurance) =
    (match instantiation with
      | .explicitTheta term => supportTermBinderSpellings term
      | .inferTheta _ _ _ _ assurance => assuranceBinderSpellings assurance) := by
  cases instantiation with
  | explicitTheta term => exact substSupportTerm_binders bindings term
  | inferTheta rule references discharges obligations assurance => rfl

private theorem substArgInstantiation_opaque
    (bindings : List Presentation.ValueBinding)
    (instantiation : Presentation.ArgInstantiation) :
    (match substArgInstantiation bindings instantiation with
      | .explicitTheta term =>
          supportTermOpaqueCertPremiseSpellings term
      | .inferTheta _ _ _ _ assurance =>
          assuranceOpaqueCertPremiseSpellings assurance) =
    (match instantiation with
      | .explicitTheta term =>
          supportTermOpaqueCertPremiseSpellings term
      | .inferTheta _ _ _ _ assurance =>
          assuranceOpaqueCertPremiseSpellings assurance) := by
  cases instantiation with
  | explicitTheta term => exact substSupportTerm_opaque bindings term
  | inferTheta rule references discharges obligations assurance => rfl

private theorem DeclsExpand_reconstruction_safe
    (sound : RenamingSound ρg program policy)
    (expanded : DeclsExpand program.valueBindings gamma source target)
    (contained : ∀ declaration ∈ source,
      declaration ∈ program.decls) :
    ∀ declaration ∈ target,
      DeclarationReconstructionSafe ρg declaration := by
  induction expanded with
  | nil => simp
  | @leaf leaf ds ts tail ih =>
      intro declaration member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · trivial
      · exact ih (by
          intro candidate candidateMember
          exact contained candidate (by simp [candidateMember])) _ member
  | @claim claim nl ds ts prose tail ih =>
      intro declaration member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · trivial
      · exact ih (by
          intro candidate candidateMember
          exact contained candidate (by simp [candidateMember])) _ member
  | @arg argument ds ts tail ih =>
      intro declaration member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · have sourceMember : Presentation.Decl.arg argument ∈ program.decls :=
          contained (.arg argument) (by simp)
        constructor
        · intro spelling spellingMember
          apply sound.certBinders spelling
          apply (argumentPayloadsFromProgram sourceMember).1
          change spelling ∈
            (match substArgInstantiation program.valueBindings
                argument.instantiation with
              | .explicitTheta term => supportTermBinderSpellings term
              | .inferTheta _ _ _ _ assurance =>
                  assuranceBinderSpellings assurance) at spellingMember
          rw [substArgInstantiation_binders] at spellingMember
          exact spellingMember
        · intro spelling spellingMember
          apply sound.opaqueCertPremises spelling
          apply (argumentPayloadsFromProgram sourceMember).2
          change spelling ∈
            (match substArgInstantiation program.valueBindings
                argument.instantiation with
              | .explicitTheta term =>
                  supportTermOpaqueCertPremiseSpellings term
              | .inferTheta _ _ _ _ assurance =>
                  assuranceOpaqueCertPremiseSpellings assurance) at spellingMember
          rw [substArgInstantiation_opaque] at spellingMember
          exact spellingMember
      · exact ih (by
          intro candidate candidateMember
          exact contained candidate (by simp [candidateMember])) _ member
  | @comparison comparison nl ds ts prose tail ih =>
      intro declaration member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · trivial
      · exact ih (by
          intro candidate candidateMember
          exact contained candidate (by simp [candidateMember])) _ member
  | @attack attack ds ts tail ih =>
      intro declaration member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · trivial
      · exact ih (by
          intro candidate candidateMember
          exact contained candidate (by simp [candidateMember])) _ member
  | @status proposition ds ts tail ih =>
      intro declaration member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · trivial
      · exact ih (by
          intro candidate candidateMember
          exact contained candidate (by simp [candidateMember])) _ member
  | @group group ds ts tail ih =>
      intro declaration member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · trivial
      · exact ih (by
          intro candidate candidateMember
          exact contained candidate (by simp [candidateMember])) _ member

private theorem DeclsExpand_leafIds
    (expanded : DeclsExpand bindings gamma source target) :
    source.filterMap (fun declaration =>
      match declaration with
      | .leaf leaf => some leaf.id
      | _ => none) =
    target.filterMap (fun declaration =>
      match declaration with
      | .leaf leaf => some leaf.id
      | _ => none) := by
  induction expanded <;> simp_all

private theorem DeclsExpandComparisons_leafIds
    (expanded : DeclsExpandComparisons policy program source target generated) :
    source.filterMap (fun declaration =>
      match declaration with
      | .leaf leaf => some leaf.id
      | _ => none) =
    target.filterMap (fun declaration =>
      match declaration with
      | .leaf leaf => some leaf.id
      | _ => none) := by
  induction expanded with
  | nil => rfl
  | @keep declaration ds ts gs hkeep tail ih =>
      cases declaration with
      | leaf leaf => simp [ih]
      | claim claim => simp [ih]
      | arg argument => simp [ih]
      | attack attack => simp [ih]
      | status proposition => simp [ih]
      | group group => simp [ih]
      | comparison comparison => simp [isComparison] at hkeep
  | @expand comparison data ds ts gs hdata tail ih =>
      simp [generatedDecls, ih]

private theorem programBinderSpellings_eraseProgramNl
    (program : Presentation.Program) :
    programBinderSpellings (eraseProgramNl program) =
      programBinderSpellings program := by
  unfold programBinderSpellings eraseProgramNl
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;>
        simp only [List.map_cons, List.flatMap_cons, eraseDeclNl] <;>
        rw [ih] <;> rfl

private theorem programOpaqueSpellings_eraseProgramNl
    (program : Presentation.Program) :
    programOpaqueCertPremiseSpellings (eraseProgramNl program) =
      programOpaqueCertPremiseSpellings program := by
  unfold programOpaqueCertPremiseSpellings eraseProgramNl
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;>
        simp only [List.map_cons, List.flatMap_cons, eraseDeclNl] <;>
        rw [ih] <;> rfl

private theorem leafIds_eraseProgramNl
    (program : Presentation.Program) :
    leafIds (eraseProgramNl program) = leafIds program := by
  unfold leafIds eraseProgramNl
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp [eraseDeclNl, ih]

private theorem argIds_eraseProgramNl
    (program : Presentation.Program) :
    argIds (eraseProgramNl program) = argIds program := by
  unfold argIds eraseProgramNl
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp [eraseDeclNl, eraseComparisonNl, ih]

private theorem claimFormal?_eraseProgramNl
    (program : Presentation.Program) (claim : Presentation.PropId) :
    claimFormal? (eraseProgramNl program) claim = claimFormal? program claim := by
  unfold claimFormal? claimFormalIn? eraseProgramNl
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration with
      | claim declared =>
          by_cases same : declared.id = claim <;>
            simp [eraseDeclNl, same, ih]
      | leaf leaf => simp [eraseDeclNl, ih]
      | arg argument => simp [eraseDeclNl, ih]
      | attack attack => simp [eraseDeclNl, ih]
      | status status => simp [eraseDeclNl, ih]
      | group group => simp [eraseDeclNl, ih]
      | comparison comparison => simp [eraseDeclNl, eraseComparisonNl, ih]

private theorem checkAuthoredConclusion_eraseProgramNl
    (canon : String → String) (program : Presentation.Program)
    (argument : Presentation.ArgId) (authored : Presentation.ArgConcl)
    (derived : Atom) :
    checkAuthoredConclusion canon (eraseProgramNl program) argument authored derived =
      checkAuthoredConclusion canon program argument authored derived := by
  cases authored with
  | supportsClaim claim =>
      simp [checkAuthoredConclusion, claimFormal?_eraseProgramNl]
  | supportsDerived claim => rfl
  | challenges target =>
      cases target with
      | question question target =>
          simp [checkAuthoredConclusion, argIds_eraseProgramNl]
      | leaf leaf =>
          simp [checkAuthoredConclusion, leafIds_eraseProgramNl]

private theorem programNlDirectiveBodies_eraseProgramNl
    (program : Presentation.Program) :
    programNlDirectiveBodies (eraseProgramNl program) = [] := by
  unfold programNlDirectiveBodies
  apply List.flatMap_eq_nil_iff.mpr
  intro text textMember
  unfold claimNls eraseProgramNl at textMember
  obtain ⟨erased, erasedMember, selected⟩ :=
    List.mem_filterMap.mp textMember
  obtain ⟨declaration, declarationMember, rfl⟩ :=
    List.mem_map.mp erasedMember
  cases declaration <;>
    simp [eraseDeclNl] at selected
  all_goals subst text
  all_goals rfl

private theorem eraseProgramNl_reconstructionSound
    (sound : RenamingSound ρg original policy)
    (comparisonSound : ComparisonRenamingSound ρg current policy)
    (bindingsEmpty : current.valueBindings = [])
    (payloadSafe : ∀ declaration ∈ current.decls,
      DeclarationReconstructionSafe ρg declaration)
    (leavesEq : leafIds current = leafIds original) :
    RenamingSound ρg (eraseProgramNl current) policy := by
  refine
    { rule_spelling := sound.rule_spelling
      leaf_spelling := sound.leaf_spelling
      cell_spelling := sound.cell_spelling
      empty := sound.empty
      numeric := sound.numeric
      integer := sound.integer
      canonicalNat := sound.canonicalNat
      cellCanonNat := sound.cellCanonNat
      identifier := sound.identifier
      sigma := sound.sigma
      atoms := ?_
      patterns := sound.patterns
      certBinders := ?_
      directiveDelimiterFresh := ?_
      opaqueCertPremises := ?_
      directiveInjective := ?_
      noCellValues := ?_ }
  · intro spelling member _
    apply comparisonSound.atoms spelling
    · rw [← programNullaryCons_eraseProgramNl current]
      exact member
    · simp [valueSpellings, programValues, eraseProgramNl, bindingsEmpty]
  · intro spelling member
    rw [programBinderSpellings_eraseProgramNl] at member
    obtain ⟨declaration, declarationMember, spellingMember⟩ :=
      List.mem_flatMap.mp member
    cases declaration with
    | arg argument =>
        exact (payloadSafe (.arg argument) declarationMember).1 spelling
          spellingMember
    | leaf leaf => change spelling ∈ [] at spellingMember; contradiction
    | claim claim => change spelling ∈ [] at spellingMember; contradiction
    | comparison comparison =>
        change spelling ∈ [] at spellingMember
        contradiction
    | attack attack => change spelling ∈ [] at spellingMember; contradiction
    | status proposition =>
        change spelling ∈ [] at spellingMember
        contradiction
    | group group => change spelling ∈ [] at spellingMember; contradiction
  · intro body member
    rw [programNlDirectiveBodies_eraseProgramNl] at member
    contradiction
  · intro spelling member
    rw [programOpaqueSpellings_eraseProgramNl] at member
    obtain ⟨declaration, declarationMember, spellingMember⟩ :=
      List.mem_flatMap.mp member
    cases declaration with
    | arg argument =>
        exact (payloadSafe (.arg argument) declarationMember).2 spelling
          spellingMember
    | leaf leaf => change spelling ∈ [] at spellingMember; contradiction
    | claim claim => change spelling ∈ [] at spellingMember; contradiction
    | comparison comparison =>
        change spelling ∈ [] at spellingMember
        contradiction
    | attack attack => change spelling ∈ [] at spellingMember; contradiction
    | status proposition =>
        change spelling ∈ [] at spellingMember
        contradiction
    | group group => change spelling ∈ [] at spellingMember; contradiction
  · intro left leftMember right rightMember equal
    have erasedValueNames : valueNames (eraseProgramNl current) = [] := by
      simp [valueNames, eraseProgramNl, bindingsEmpty]
    have currentLeft : left ∈
        (leafIds current).map (fun leaf =>
          "cell ".toList ++ leaf.val.toList) := by
      unfold programDirectiveBodies at leftMember
      rw [programNlDirectiveBodies_eraseProgramNl, erasedValueNames,
        leafIds_eraseProgramNl] at leftMember
      simpa using leftMember
    have currentRight : right ∈
        (leafIds current).map (fun leaf =>
          "cell ".toList ++ leaf.val.toList) := by
      unfold programDirectiveBodies at rightMember
      rw [programNlDirectiveBodies_eraseProgramNl, erasedValueNames,
        leafIds_eraseProgramNl] at rightMember
      simpa using rightMember
    have originalLeft : left ∈ programDirectiveBodies original := by
      unfold programDirectiveBodies
      simp only [List.mem_append]
      exact Or.inr (by simpa [← leavesEq] using currentLeft)
    have originalRight : right ∈ programDirectiveBodies original := by
      unfold programDirectiveBodies
      simp only [List.mem_append]
      exact Or.inr (by simpa [← leavesEq] using currentRight)
    exact sound.directiveInjective left originalLeft right originalRight equal
  · simp [valueNames, eraseProgramNl, bindingsEmpty]

private theorem declarationSafe_of_erasedSound
    (sound : RenamingSound ρg (eraseProgramNl program) policy)
    (bindingsEmpty : program.valueBindings = [])
    (declaration : Presentation.Decl)
    (member : declaration ∈ program.decls) :
    (∀ spelling ∈ declNullaryCons declaration,
        Binding.renameText ρg spelling = spelling) ∧
      DeclarationReconstructionSafe ρg declaration := by
  have erasedMember : eraseDeclNl declaration ∈
      (eraseProgramNl program).decls := by
    exact List.mem_map.mpr ⟨declaration, member, rfl⟩
  constructor
  · intro spelling spellingMember
    apply sound.atoms spelling
    · apply List.mem_flatMap.mpr
      refine ⟨eraseDeclNl declaration, erasedMember, ?_⟩
      cases declaration <;> exact spellingMember
    · simp [valueSpellings, programValues, eraseProgramNl, bindingsEmpty]
  · cases declaration with
    | arg argument =>
        have payloads := argumentPayloadsFromProgram
          (program := eraseProgramNl program) erasedMember
        constructor
        · intro spelling spellingMember
          exact sound.certBinders spelling (payloads.1 spellingMember)
        · intro spelling spellingMember
          exact sound.opaqueCertPremises spelling
            (payloads.2 spellingMember)
    | leaf leaf => trivial
    | claim claim => trivial
    | comparison comparison => trivial
    | attack attack => trivial
    | status proposition => trivial
    | group group => trivial

private theorem DeclsExpandComparisons_reconstruction_safe
    (sound : RenamingSound ρg (eraseProgramNl program) policy)
    (bindingsEmpty : program.valueBindings = [])
    (expanded : DeclsExpandComparisons policy program source target generated)
    (contained : ∀ declaration ∈ source,
      declaration ∈ program.decls) :
    ∀ declaration ∈ target,
      (∀ spelling ∈ declNullaryCons declaration,
        Binding.renameText ρg spelling = spelling) ∧
      DeclarationReconstructionSafe ρg declaration := by
  induction expanded with
  | nil => simp
  | @keep d ds ts gs hkeep hrest ih =>
      intro candidate candidateMember
      simp only [List.mem_cons] at candidateMember
      rcases candidateMember with rfl | candidateMember
      · exact declarationSafe_of_erasedSound sound bindingsEmpty candidate
          (contained candidate (by simp))
      · apply ih
        · intro nested nestedMember
          exact contained nested (by simp [nestedMember])
        · exact candidateMember
  | @expand comparison data ds ts gs dataSpec hrest ih =>
      intro declaration declarationMember
      simp only [List.mem_append] at declarationMember
      rcases declarationMember with generatedMember | tailMember
      · have comparisonMember :
            Presentation.Decl.comparison comparison ∈ program.decls :=
          contained (.comparison comparison) (by simp)
        have erasedComparisonMember :
            Presentation.Decl.comparison (eraseComparisonNl comparison) ∈
              (eraseProgramNl program).decls := by
          exact List.mem_map.mpr ⟨.comparison comparison,
            comparisonMember, rfl⟩
        have sourceFound := comparisonExpansion?_complete dataSpec
        have erasedFound : comparisonExpansion?
            (eraseProgramNl program) policy
            (eraseComparisonNl comparison) = some data := by
          rw [comparisonExpansion?_erase]
          exact sourceFound
        have dataFixed := comparisonExpansionData_fixed sound
          (eraseComparisonNl comparison) erasedComparisonMember data erasedFound
        have dataFixedEmpty : AtomFixed ρg [] data.goal ∧
            SubstFixed ρg [] data.thetaRecheck ∧
            SubstFixed ρg [] data.thetaBridge := by
          simpa [programValues, eraseProgramNl, bindingsEmpty] using dataFixed
        have generatedSafe := generatedDecls_reconstruction_safe
          (data := data) (comparison := comparison) sound.numeric
          dataFixedEmpty declaration generatedMember
        cases declaration <;> exact generatedSafe
      · apply ih
        · intro nested nestedMember
          exact contained nested (by simp [nestedMember])
        · exact tailMember

private theorem leafProp?_eraseProgramNl
    (program : Presentation.Program) (leaf : Presentation.LeafId) :
    leafProp? (eraseProgramNl program) leaf = leafProp? program leaf := by
  unfold leafProp?
  rw [declaredLeaves_eraseProgramNl]

private theorem resolveReference_eraseProgramNl
    (program : Presentation.Program) (priors : List PriorArgument)
    (reference : Presentation.ArgRef) :
    resolveReference (eraseProgramNl program) priors reference =
      resolveReference program priors reference := by
  unfold resolveReference
  rw [declaredLeaves_eraseProgramNl]

private theorem conclOfTerm_eraseProgramNl
    (program : Presentation.Program) (policy : Presentation.Policy)
    (term : Presentation.SupportTerm) :
    conclOfTerm (eraseProgramNl program) policy term =
      conclOfTerm program policy term := by
  cases term with
  | leaf leaf => exact leafProp?_eraseProgramNl program leaf
  | rule rule subst premises discharges holes assurance => rfl

private theorem resolveReferences_eraseProgramNl
    (program : Presentation.Program) (priors : List PriorArgument) :
    ∀ references,
      resolveReferences (eraseProgramNl program) priors references =
        resolveReferences program priors references
  | [] => rfl
  | reference :: rest => by
      simp only [resolveReferences]
      rw [resolveReference_eraseProgramNl,
        resolveReferences_eraseProgramNl program priors rest]

private theorem resolveNamedDischarges_eraseProgramNl
    (program : Presentation.Program) (priors : List PriorArgument)
    (rule : Presentation.Rule) :
    ∀ discharges,
      resolveNamedDischarges (eraseProgramNl program) priors rule discharges =
        resolveNamedDischarges program priors rule discharges
  | [] => rfl
  | (question, reference) :: rest => by
      simp only [resolveNamedDischarges]
      rw [resolveReference_eraseProgramNl,
        resolveNamedDischarges_eraseProgramNl program priors rule rest]

private theorem parserPremiseMatches_eraseProgramNl
    (program : Presentation.Program) (priors : List PriorArgument)
    (ground : Atom) :
    parserPremiseMatches (eraseProgramNl program) priors ground =
      parserPremiseMatches program priors ground := by
  unfold parserPremiseMatches
  rw [declaredLeaves_eraseProgramNl]

private theorem parserResolveImplicitPremise_eraseProgramNl
    (program : Presentation.Program) (priors : List PriorArgument)
    (theta : SurfaceSubst) (pattern : Presentation.AtomPat) :
    parserResolveImplicitPremise (eraseProgramNl program) priors theta pattern =
      parserResolveImplicitPremise program priors theta pattern := by
  simp only [parserResolveImplicitPremise,
    parserPremiseMatches_eraseProgramNl]

private theorem parserResolveImplicitPremises_eraseProgramNl
    (program : Presentation.Program) (priors : List PriorArgument)
    (theta : SurfaceSubst) : ∀ patterns,
    parserResolveImplicitPremises (eraseProgramNl program) priors theta patterns =
      parserResolveImplicitPremises program priors theta patterns
  | [] => rfl
  | pattern :: rest => by
      simp only [parserResolveImplicitPremises]
      rw [parserResolveImplicitPremise_eraseProgramNl,
        parserResolveImplicitPremises_eraseProgramNl program priors theta rest]

private theorem parserResolveExplicitDischarges_eraseProgramNl
    (program : Presentation.Program) (priors : List PriorArgument) :
    ∀ discharges,
    parserResolveExplicitDischarges (eraseProgramNl program) priors discharges =
      parserResolveExplicitDischarges program priors discharges
  | .nil => rfl
  | .cons question term rest => by
      cases term with
      | leaf leaf =>
          simp only [parserResolveExplicitDischarges]
          rw [resolveReference_eraseProgramNl,
            parserResolveExplicitDischarges_eraseProgramNl program priors rest]
      | rule rule subst premises nested holes assurance => rfl

private theorem parserReconstructExplicitTerm_eraseProgramNl
    (program : Presentation.Program) (policy : Presentation.Policy)
    (priors : List PriorArgument) (term : Presentation.SupportTerm) :
    parserReconstructExplicitTerm (eraseProgramNl program) policy priors term =
      parserReconstructExplicitTerm program policy priors term := by
  cases term with
  | leaf leaf => rfl
  | rule rule subst premises discharges holes assurance =>
      cases premises with
      | cons premise rest => rfl
      | nil =>
          cases ruleFound : ruleById policy rule with
          | none => simp [parserReconstructExplicitTerm, ruleFound]
          | some selected =>
              cases arity : subst.length != selected.params.length with
              | true =>
                  have lengthNe : subst.length ≠ selected.params.length := by
                    simpa using arity
                  simp [parserReconstructExplicitTerm, ruleFound, lengthNe]
              | false =>
                  have lengthEq : subst.length = selected.params.length := by
                    simpa using arity
                  simp [parserReconstructExplicitTerm, ruleFound, lengthEq,
                    parserResolveImplicitPremises_eraseProgramNl,
                    parserResolveExplicitDischarges_eraseProgramNl]

private theorem buildArgument_eraseProgramNl
    (program : Presentation.Program) (policy : Presentation.Policy)
    (priors : List PriorArgument) (argument : Presentation.Arg) :
    buildArgument (eraseProgramNl program) policy priors argument =
      buildArgument program policy priors argument := by
  cases instantiation : argument.instantiation with
  | explicitTheta term =>
      simp only [buildArgument, instantiation]
      rw [parserReconstructExplicitTerm_eraseProgramNl]
      cases parserReconstructExplicitTerm program policy priors term with
      | none => rfl
      | some rebuilt =>
          simp [conclOfTerm_eraseProgramNl]
  | inferTheta rule references discharges obligations assurance =>
      simp only [buildArgument, instantiation,
        resolveReferences_eraseProgramNl,
        resolveNamedDischarges_eraseProgramNl]

private theorem premiseMatches_eraseProgramNl
    (canon : String → String) (program : Presentation.Program)
    (priors : List PriorArgument) (ground : Atom) :
    premiseMatches canon (eraseProgramNl program) priors ground =
      premiseMatches canon program priors ground := by
  unfold premiseMatches
  rw [declaredLeaves_eraseProgramNl]

private theorem resolveImplicitPremise_eraseProgramNl
    (canon : String → String) (program : Presentation.Program)
    (priors : List PriorArgument) (theta : SurfaceSubst)
    (pattern : Presentation.AtomPat) :
    resolveImplicitPremise canon (eraseProgramNl program) priors theta pattern =
      resolveImplicitPremise canon program priors theta pattern := by
  simp only [resolveImplicitPremise, premiseMatches_eraseProgramNl]

private theorem resolveImplicitPremises_eraseProgramNl
    (canon : String → String) (program : Presentation.Program)
    (priors : List PriorArgument) (theta : SurfaceSubst) :
    ∀ patterns,
      resolveImplicitPremises canon (eraseProgramNl program) priors theta
          patterns =
        resolveImplicitPremises canon program priors theta patterns
  | [] => rfl
  | pattern :: rest => by
      simp only [resolveImplicitPremises]
      rw [resolveImplicitPremise_eraseProgramNl,
        resolveImplicitPremises_eraseProgramNl canon program priors theta rest]

mutual
  private theorem reconstructExplicitTerm_eraseProgramNl
      (canon : String → String) (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument)
      (term : Presentation.SupportTerm) :
      reconstructExplicitTerm canon (eraseProgramNl program) policy priors term =
        reconstructExplicitTerm canon program policy priors term := by
    cases term with
    | leaf leaf => rfl
    | rule rule subst premises discharges holes assurance =>
        cases premises with
        | nil =>
            simp only [reconstructExplicitTerm,
              resolveImplicitPremises_eraseProgramNl,
              reconstructExplicitDischarges_eraseProgramNl]
        | cons premise rest =>
            simp only [reconstructExplicitTerm,
              reconstructExplicitTerms_eraseProgramNl,
              reconstructExplicitDischarges_eraseProgramNl]

  private theorem reconstructExplicitTerms_eraseProgramNl
      (canon : String → String) (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument)
      (terms : Presentation.SupportTerms) :
      reconstructExplicitTerms canon (eraseProgramNl program) policy priors
          terms =
        reconstructExplicitTerms canon program policy priors terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp only [reconstructExplicitTerms]
        rw [reconstructExplicitTerm_eraseProgramNl,
          reconstructExplicitTerms_eraseProgramNl]

  private theorem reconstructExplicitDischarges_eraseProgramNl
      (canon : String → String) (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument)
      (discharges : Presentation.Discharges) :
      reconstructExplicitDischarges canon (eraseProgramNl program) policy
          priors discharges =
        reconstructExplicitDischarges canon program policy priors discharges := by
    cases discharges with
    | nil => rfl
    | cons question term rest =>
        cases term with
        | leaf leaf =>
            simp only [reconstructExplicitDischarges]
            rw [resolveReference_eraseProgramNl,
              reconstructExplicitDischarges_eraseProgramNl]
        | rule rule subst premises nested holes assurance => rfl
end

private theorem reconstructArgument_eraseProgramNl
    (canon : String → String) (program : Presentation.Program)
    (policy : Presentation.Policy) (priors : List PriorArgument)
    (argument : Presentation.Arg) :
    reconstructArgument canon (eraseProgramNl program) policy priors argument =
      reconstructArgument canon program policy priors argument := by
  cases instantiation : argument.instantiation with
  | inferTheta rule references discharges obligations assurance =>
      simp only [reconstructArgument, instantiation]
      exact buildArgument_eraseProgramNl program policy priors argument
  | explicitTheta term =>
      simp only [reconstructArgument, instantiation,
        reconstructExplicitTerm_eraseProgramNl,
        conclOfTerm_eraseProgramNl]

private theorem certificateResolver_eraseProgramNl
    (program : Presentation.Program) (rule : Presentation.Rule)
    (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm) (name : String) :
    certificateResolver (eraseProgramNl program) rule priors premises name =
      certificateResolver program rule priors premises name := by
  unfold certificateResolver
  rw [declaredLeaves_eraseProgramNl]

private theorem lowerAssuranceCertificate_eraseProgramNl
    (env : Env canon) (program : Presentation.Program)
    (rule : Presentation.Rule) (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm)
    (assurance : Presentation.Assurance) :
    lowerAssuranceCertificate env (eraseProgramNl program) rule priors premises
        assurance =
      lowerAssuranceCertificate env program rule priors premises assurance := by
  cases assurance with
  | none => rfl
  | trusted => rfl
  | cert certificate =>
      have resolverEq :
          certificateResolver (eraseProgramNl program) rule priors premises =
            certificateResolver program rule priors premises := by
        funext name
        exact certificateResolver_eraseProgramNl program rule priors premises
          name
      cases version : certificate.version <;>
        simp [lowerAssuranceCertificate, version, resolverEq]

mutual
  private theorem lowerToSupportTerm_eraseProgramNl
      (env : Env canon) (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument)
      (term : Presentation.SupportTerm) :
      lowerToSupportTerm env (eraseProgramNl program) policy priors term =
        lowerToSupportTerm env program policy priors term := by
    cases term with
    | leaf leaf => rfl
    | rule rule subst premises discharges holes assurance =>
        simp only [lowerToSupportTerm,
          lowerAssuranceCertificate_eraseProgramNl,
          lowerToSupportTerms_eraseProgramNl,
          lowerToSupportDischarges_eraseProgramNl]

  private theorem lowerToSupportTerms_eraseProgramNl
      (env : Env canon) (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument)
      (terms : Presentation.SupportTerms) :
      lowerToSupportTerms env (eraseProgramNl program) policy priors terms =
        lowerToSupportTerms env program policy priors terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp only [lowerToSupportTerms]
        rw [lowerToSupportTerm_eraseProgramNl,
          lowerToSupportTerms_eraseProgramNl]

  private theorem lowerToSupportDischarges_eraseProgramNl
      (env : Env canon) (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument)
      (discharges : Presentation.Discharges) :
      lowerToSupportDischarges env (eraseProgramNl program) policy priors
          discharges =
        lowerToSupportDischarges env program policy priors discharges := by
    cases discharges with
    | nil => rfl
    | cons question term rest =>
        simp only [lowerToSupportDischarges]
        rw [lowerToSupportTerm_eraseProgramNl,
          lowerToSupportDischarges_eraseProgramNl]
end

private theorem reconstructArgs_eraseProgramNl
    (env : Env canon) (program : Presentation.Program)
    (policy : Presentation.Policy) :
    ∀ declarations priors,
      reconstructArgs env (eraseProgramNl program) policy
          (declarations.map eraseDeclNl) priors =
        reconstructArgs env program policy declarations priors
  | [], priors => rfl
  | declaration :: rest, priors => by
      cases declaration with
      | leaf leaf =>
          simp only [List.map_cons, eraseDeclNl, reconstructArgs]
          exact reconstructArgs_eraseProgramNl env program policy rest priors
      | claim claim =>
          simp only [List.map_cons, eraseDeclNl, reconstructArgs]
          exact reconstructArgs_eraseProgramNl env program policy rest priors
      | attack attack =>
          simp only [List.map_cons, eraseDeclNl, reconstructArgs]
          exact reconstructArgs_eraseProgramNl env program policy rest priors
      | status proposition =>
          simp only [List.map_cons, eraseDeclNl, reconstructArgs]
          exact reconstructArgs_eraseProgramNl env program policy rest priors
      | group group =>
          simp only [List.map_cons, eraseDeclNl, reconstructArgs]
          exact reconstructArgs_eraseProgramNl env program policy rest priors
      | comparison comparison =>
          simp [List.map_cons, eraseDeclNl, reconstructArgs]
      | arg argument =>
          simp only [List.map_cons, eraseDeclNl, reconstructArgs]
          simp only [reconstructArgument_eraseProgramNl,
            checkAuthoredConclusion_eraseProgramNl,
            lowerToSupportTerm_eraseProgramNl,
            reconstructArgs_eraseProgramNl env program policy]

private theorem renameArg_values_eq_nil
    (values : List Presentation.ValueName)
    (safe : ∀ spelling ∈ declNullaryCons (.arg argument),
      Binding.renameText ρg spelling = spelling) :
    Binding.renameArg ρg values argument =
      Binding.renameArg ρg [] argument := by
  rcases argument with ⟨id, conclusion, instantiation⟩
  cases instantiation with
  | inferTheta rule references discharges obligations assurance =>
      rfl
  | explicitTheta term =>
      have fixedValues : SupportTermFixed ρg values term := by
        intro spelling spellingMember _
        apply safe spelling
        simpa [declNullaryCons, argNullaryCons] using
          spellingMember
      have fixedNil : SupportTermFixed ρg [] term := by
        intro spelling spellingMember _
        apply safe spelling
        simpa [declNullaryCons, argNullaryCons] using
          spellingMember
      have termEq : Binding.renameSupportTerm ρg values term =
          Binding.renameSupportTerm ρg [] term :=
        (renameResidualSupportTerm_eq_renameSupportTerm fixedValues).symm.trans
          (renameResidualSupportTerm_eq_renameSupportTerm fixedNil)
      simp [Binding.renameArg, Binding.renameArgInstantiation,
        termEq]

private theorem ChecksProgram_arguments_mem
    (checks : ChecksProgram env program policy declarations priors rows) :
    ∀ row ∈ rows, Presentation.Decl.arg row.argument ∈ declarations := by
  induction checks with
  | nil => simp
  | cons head tail ih =>
      cases head with
      | leaf =>
          intro row member
          exact List.mem_cons.mpr (Or.inr (ih row (by simpa using member)))
      | claim =>
          intro row member
          exact List.mem_cons.mpr (Or.inr (ih row (by simpa using member)))
      | status =>
          intro row member
          exact List.mem_cons.mpr (Or.inr (ih row (by simpa using member)))
      | group =>
          intro row member
          exact List.mem_cons.mpr (Or.inr (ih row (by simpa using member)))
      | attack =>
          intro row member
          exact List.mem_cons.mpr (Or.inr (ih row (by simpa using member)))
      | @arg argument built core argumentChecks =>
          intro row member
          simp only [List.singleton_append, List.mem_cons] at member
          rcases member with rfl | member
          · simp
          · exact List.mem_cons.mpr (Or.inr (ih row member))

private theorem renameExcept_reconstructed_values_eq_nil
    (env : Env canon) (program : Presentation.Program)
    (policy : Presentation.Policy) (values : List Presentation.ValueName)
    (safe : ∀ declaration ∈ program.decls,
      ∀ spelling ∈ declNullaryCons declaration,
        Binding.renameText ρg spelling = spelling) :
    renameExcept (renameReconstructFailure ρg)
        (List.map (renameReconstructedArgument ρg values))
        (reconstructArgs env program policy program.decls []) =
      renameExcept (renameReconstructFailure ρg)
        (List.map (renameReconstructedArgument ρg []))
        (reconstructArgs env program policy program.decls []) := by
  cases result : reconstructArgs env program policy program.decls [] with
  | error failure => rfl
  | ok rows =>
      have checks := reconstructArgs_sound env program policy result
      simp only [result, renameExcept]
      congr 1
      apply List.map_congr_left
      intro row rowMember
      have argumentMember := ChecksProgram_arguments_mem checks row rowMember
      cases row with
      | mk argument built core =>
          simp only [renameReconstructedArgument]
          congr 1
          exact renameArg_values_eq_nil values
            (safe (.arg argument) argumentMember)

/-- Canonical argument reconstruction commutes with a typed global renaming
after the real executable value and comparison passes.  In particular, this
theorem reconstructs the semantic declarations emitted by `generatedDecls`,
not the pre-validation approximation used by certificate validation. -/
theorem reconstructExpandedArgs_rename
    (sound : RenamingSound ρg program policy)
    (envSound : EnvRenamingSound env ρg)
    (sourceValues : expandValues policy program = .ok valueExpanded)
    (sourceComparisons :
      expandComparisons policy valueExpanded = .ok (semantic, generated))
    (targetValues : expandValues (Binding.renamePolicy ρg policy)
      (Binding.renameProgram ρg program) = .ok renamedValueExpanded)
    (targetComparisons :
      expandComparisons (Binding.renamePolicy ρg policy)
        renamedValueExpanded = .ok (renamedSemantic, renamedGenerated)) :
    reconstructArgs env renamedSemantic (Binding.renamePolicy ρg policy)
        renamedSemantic.decls [] =
      renameExcept (renameReconstructFailure ρg)
        (List.map (renameReconstructedArgument ρg (programValues program)))
        (reconstructArgs env semantic policy semantic.decls []) := by
  have valuesExpansion := expandValues_sound policy sourceValues
  cases valuesExpansion with
  | @intro environment gamma environmentEq gammaEq bindingsEq artifactEq
      digestEq policyEq backendsEq valueDeclarations =>
    rw [environmentEq] at valueDeclarations
    have valuePayloadSafe : ∀ declaration ∈ valueExpanded.decls,
        DeclarationReconstructionSafe ρg declaration :=
      DeclsExpand_reconstruction_safe sound valueDeclarations (by simp)
    have valueLeavesEq : leafIds valueExpanded = leafIds program := by
      have ids := DeclsExpand_leafIds valueDeclarations
      unfold leafIds at ids ⊢
      exact ids.symm
    have valueComparisonSound :=
      comparisonRenamingSound_of_expandValues sound sourceValues
    have valueErasedSound :
        RenamingSound ρg (eraseProgramNl valueExpanded) policy :=
      eraseProgramNl_reconstructionSound sound valueComparisonSound
        bindingsEq valuePayloadSafe valueLeavesEq
    have comparisonsExpansion :=
      expandComparisons_sound policy sourceComparisons
    cases comparisonsExpansion with
    | intro semanticDeclarations semanticArtifactEq semanticDigestEq
        semanticPolicyEq semanticBackendsEq semanticBindingsEq =>
      have semanticBindingsEmpty : semantic.valueBindings = [] :=
        semanticBindingsEq.trans bindingsEq
      have semanticSafe : ∀ declaration ∈ semantic.decls,
          (∀ spelling ∈ declNullaryCons declaration,
            Binding.renameText ρg spelling = spelling) ∧
          DeclarationReconstructionSafe ρg declaration :=
        DeclsExpandComparisons_reconstruction_safe valueErasedSound bindingsEq
          semanticDeclarations (by simp)
      have semanticLeavesEq : leafIds semantic = leafIds program := by
        have ids := DeclsExpandComparisons_leafIds semanticDeclarations
        unfold leafIds at ids ⊢
        exact ids.symm.trans valueLeavesEq
      have semanticComparisonSound :
          ComparisonRenamingSound ρg semantic policy :=
        { atoms := by
            intro spelling spellingMember _
            obtain ⟨declaration, declarationMember, contained⟩ :=
              List.mem_flatMap.mp spellingMember
            exact (semanticSafe declaration declarationMember).1 spelling
              contained
          patterns := sound.patterns }
      have semanticPayloadSafe : ∀ declaration ∈ semantic.decls,
          DeclarationReconstructionSafe ρg declaration := by
        intro declaration declarationMember
        exact (semanticSafe declaration declarationMember).2
      have semanticErasedSound :
          RenamingSound ρg (eraseProgramNl semantic) policy :=
        eraseProgramNl_reconstructionSound sound semanticComparisonSound
          semanticBindingsEmpty semanticPayloadSafe semanticLeavesEq
      have transported := expandValuesThenComparisons_rename_related sound
      rw [sourceValues, targetValues] at transported
      cases transported with
      | ok comparisonsTransported =>
        rw [sourceComparisons, targetComparisons] at comparisonsTransported
        cases comparisonsTransported with
        | ok resultsRelated =>
          have programsRelated :
              eraseProgramNl renamedSemantic =
                Binding.renameProgram ρg (eraseProgramNl semantic) :=
            calc
              eraseProgramNl renamedSemantic =
                  eraseProgramNl (Binding.renameProgram ρg semantic) := by
                simpa [SemanticProgramRelated] using resultsRelated.1
              _ = Binding.renameProgram ρg (eraseProgramNl semantic) :=
                eraseProgramNl_renameProgram ρg semantic
          have declarationsRelated :
              (eraseProgramNl renamedSemantic).decls =
                (eraseProgramNl semantic).decls.map
                  (Binding.renameDecl ρg
                    (programValues (eraseProgramNl semantic))) :=
            congrArg Presentation.Program.decls programsRelated
          have reconstruction := reconstructArgs_rename semanticErasedSound
            envSound (eraseProgramNl semantic).decls [] (by simp)
            (priorPayloadsFromProgram_nil (eraseProgramNl semantic))
          rw [← declarationsRelated, ← programsRelated] at reconstruction
          have sourceErase := reconstructArgs_eraseProgramNl env semantic
            policy semantic.decls []
          have targetErase := reconstructArgs_eraseProgramNl env
            renamedSemantic (Binding.renamePolicy ρg policy)
            renamedSemantic.decls []
          have sourceErase' :
              reconstructArgs env (eraseProgramNl semantic) policy
                  (eraseProgramNl semantic).decls [] =
                reconstructArgs env semantic policy semantic.decls [] := by
            simpa [eraseProgramNl] using sourceErase
          have targetErase' :
              reconstructArgs env (eraseProgramNl renamedSemantic)
                  (Binding.renamePolicy ρg policy)
                  (eraseProgramNl renamedSemantic).decls [] =
                reconstructArgs env renamedSemantic
                  (Binding.renamePolicy ρg policy) renamedSemantic.decls [] := by
            simpa [eraseProgramNl] using targetErase
          simp only [List.map_nil] at reconstruction
          rw [targetErase', sourceErase'] at reconstruction
          have erasedSemanticValues :
              programValues (eraseProgramNl semantic) = [] := by
            simp [programValues, eraseProgramNl, semanticBindingsEmpty]
          rw [erasedSemanticValues] at reconstruction
          have valuesMap := renameExcept_reconstructed_values_eq_nil env
            semantic policy (programValues program) (by
              intro declaration declarationMember spelling spellingMember
              exact (semanticSafe declaration declarationMember).1 spelling
                spellingMember)
          rw [← valuesMap] at reconstruction
          exact reconstruction

/-! ### End-to-end typed global renaming -/

private theorem global_findDuplicate_map_injective
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (rename : α → β) (injective : Function.Injective rename)
    (values : List α) :
    findDuplicate (values.map rename) =
      (findDuplicate values).map rename := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      unfold findDuplicate
      by_cases member : value ∈ rest
      · have sourceSome :
            (rest.find? fun candidate => decide (candidate = value)).isSome :=
          List.find?_isSome.mpr ⟨value, member, by simp⟩
        have renamedSome :
            ((rest.map rename).find? fun candidate =>
              decide (candidate = rename value)).isSome :=
          List.find?_isSome.mpr
            ⟨rename value, List.mem_map.mpr ⟨value, member, rfl⟩, by simp⟩
        cases sourceEq :
            rest.find? (fun candidate => decide (candidate = value)) with
        | none => simp [sourceEq] at sourceSome
        | some sourceFound =>
            cases renamedEq :
                (rest.map rename).find? (fun candidate =>
                  decide (candidate = rename value)) with
            | none => simp [renamedEq] at renamedSome
            | some renamedFound => simp [sourceEq, renamedEq]
      · have sourceNone :
            rest.find? (fun candidate => decide (candidate = value)) = none :=
          List.find?_eq_none.mpr (by
            intro candidate candidateMember predicateTrue
            have equal : candidate = value := of_decide_eq_true predicateTrue
            subst candidate
            exact member candidateMember)
        have renamedNone :
            (rest.map rename).find? (fun candidate =>
              decide (candidate = rename value)) = none :=
          List.find?_eq_none.mpr (by
            intro candidate candidateMember predicateTrue
            obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp candidateMember
            have equal : rename source = rename value :=
              of_decide_eq_true predicateTrue
            have sourceEq : source = value := injective equal
            subst source
            exact member sourceMember)
        simp [sourceNone, renamedNone, ih]

private theorem global_find?_map_eq_map_find?
    (mapValue : α → β) (sourcePredicate : α → Bool)
    (targetPredicate : β → Bool) (values : List α)
    (predicateEq : ∀ value,
      targetPredicate (mapValue value) = sourcePredicate value) :
    (values.map mapValue).find? targetPredicate =
      (values.find? sourcePredicate).map mapValue := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.map_cons, List.find?_cons]
      rw [predicateEq, ih]
      cases sourcePredicate value <;> rfl

private theorem elaborationPrologue_rename_global
    (sound : RenamingSound ρg program policy) :
    elaborationPrologue
        ⟨Binding.renameProgram ρg program, Binding.renamePolicy ρg policy⟩ =
      renameExcept (renameError ρg) id
        (elaborationPrologue ⟨program, policy⟩) := by
  have perRule : ∀ rule,
      canonicalPremiseLabelsForRuleB (Binding.renameRule ρg rule) =
        canonicalPremiseLabelsForRuleB rule := by
    intro rule
    have anyEq :
        (rule.premiseLabels.map (Option.map ρg.premiseLabel)).any
            (fun label => label.isSome) =
          rule.premiseLabels.any (fun label => label.isSome) := by
      induction rule.premiseLabels with
      | nil => rfl
      | cons label rest ih => cases label <;> simp_all
    simp [canonicalPremiseLabelsForRuleB, Binding.renameRule, anyEq]
  have badFind :
      ((Binding.renamePolicy ρg policy).rules.find? fun rule =>
          !canonicalPremiseLabelsForRuleB rule).map (·.id) =
        ((policy.rules.find? fun rule =>
          !canonicalPremiseLabelsForRuleB rule).map (·.id)).map ρg.rule := by
    simp only [Binding.renamePolicy]
    rw [global_find?_map_eq_map_find? (Binding.renameRule ρg)
      (fun rule => !canonicalPremiseLabelsForRuleB rule)
      (fun rule => !canonicalPremiseLabelsForRuleB rule)
      policy.rules (by intro rule; rw [perRule])]
    cases policy.rules.find? (fun rule =>
      !canonicalPremiseLabelsForRuleB rule) <;> simp [Binding.renameRule]
  have leafDuplicate :
      findDuplicate (leafIds (Binding.renameProgram ρg program)) =
        (findDuplicate (leafIds program)).map ρg.leaf := by
    rw [leafIds_renameProgram]
    exact global_findDuplicate_map_injective ρg.leaf ρg.leaf_injective _
  unfold elaborationPrologue
  rw [canonicalPremiseLabelsB_rename, badFind, leafDuplicate]
  by_cases policyMatches : program.policy = policy.id
  · simp only [policyMatches, ↓reduceIte]
    cases canonical : canonicalPremiseLabelsB policy with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have badSome :
            (policy.rules.find? fun rule =>
              !canonicalPremiseLabelsForRuleB rule).isSome := by
          rw [List.find?_isSome]
          simpa [canonicalPremiseLabelsB] using canonical
        cases bad : policy.rules.find? fun rule =>
            !canonicalPremiseLabelsForRuleB rule with
        | none => simp [bad] at badSome
        | some rule =>
            simp [Binding.renameProgram, Binding.renamePolicy,
              policyMatches, renameExcept, renameError]
    | true =>
        cases admissionDuplicate :
            findDuplicate (policy.admission.map Prod.fst) with
        | some key =>
            simp [admissionDuplicate, Binding.renameProgram,
              Binding.renamePolicy, policyMatches, renameExcept, renameError]
        | none =>
            cases leafDuplicateSource : findDuplicate (leafIds program) with
            | none =>
                simp [admissionDuplicate, leafDuplicateSource,
                  Binding.renameProgram, Binding.renamePolicy, policyMatches,
                  renameExcept, renameError]
            | some leaf =>
                simp [admissionDuplicate, leafDuplicateSource,
                  Binding.renameProgram, Binding.renamePolicy, policyMatches,
                  renameExcept, renameError]
  · simp [Binding.renameProgram, Binding.renamePolicy, policyMatches,
      renameExcept, renameError]

private theorem semanticIdentifierChecks_rename_global
    (sound : RenamingSound ρg program policy) :
    semanticIdentifierChecks (Binding.renamePolicy ρg policy)
        (Binding.renameProgram ρg program) =
      renameExcept (renameError ρg) id
        (semanticIdentifierChecks policy program) := by
  have ruleSentinel : ρg.rule (⟨""⟩ : Presentation.RuleId) = ⟨""⟩ := by
    apply congrArg Presentation.RuleId.mk
    simpa using (ρg.rule_coherent ⟨""⟩).trans sound.empty
  have argDuplicate :
      findDuplicate (argIds (Binding.renameProgram ρg program)) =
        (findDuplicate (argIds program)).map ρg.arg := by
    rw [argIds_renameProgram]
    exact global_findDuplicate_map_injective ρg.arg ρg.arg_injective _
  have claimDuplicate :
      findDuplicate (claimIds (Binding.renameProgram ρg program)) =
        (findDuplicate (claimIds program)).map ρg.prop := by
    rw [claimIds_renameProgram]
    exact global_findDuplicate_map_injective ρg.prop ρg.prop_injective _
  unfold semanticIdentifierChecks
  rw [argDuplicate, claimDuplicate, ruleNamespacesWellFormedB_rename sound,
    validateAttackEndpoints_rename sound]
  cases findDuplicate (argIds program) <;>
    cases findDuplicate (claimIds program) <;>
    cases ruleNamespacesWellFormedB policy <;>
    simp [renameExcept, renameError, ruleSentinel]

private structure ExpandedSemanticFacts
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program)
    (policy : Presentation.Policy) (semantic : Presentation.Program) : Prop where
  bindingsEmpty : semantic.valueBindings = []
  declarationsFixed : ∀ declaration ∈ semantic.decls,
    ∀ spelling ∈ declNullaryCons declaration,
      Binding.renameText ρg spelling = spelling
  erasedSound : RenamingSound ρg (eraseProgramNl semantic) policy

private theorem expandedSemanticFacts
    (sound : RenamingSound ρg program policy)
    (sourceValues : expandValues policy program = .ok valueExpanded)
    (sourceComparisons :
      expandComparisons policy valueExpanded = .ok (semantic, generated)) :
    ExpandedSemanticFacts ρg program policy semantic := by
  have valuesExpansion := expandValues_sound policy sourceValues
  cases valuesExpansion with
  | @intro environment gamma environmentEq gammaEq bindingsEq artifactEq
      digestEq policyEq backendsEq valueDeclarations =>
    rw [environmentEq] at valueDeclarations
    have valuePayloadSafe : ∀ declaration ∈ valueExpanded.decls,
        DeclarationReconstructionSafe ρg declaration :=
      DeclsExpand_reconstruction_safe sound valueDeclarations (by simp)
    have valueLeavesEq : leafIds valueExpanded = leafIds program := by
      have ids := DeclsExpand_leafIds valueDeclarations
      unfold leafIds at ids ⊢
      exact ids.symm
    have valueComparisonSound :=
      comparisonRenamingSound_of_expandValues sound sourceValues
    have valueErasedSound :
        RenamingSound ρg (eraseProgramNl valueExpanded) policy :=
      eraseProgramNl_reconstructionSound sound valueComparisonSound
        bindingsEq valuePayloadSafe valueLeavesEq
    have comparisonsExpansion :=
      expandComparisons_sound policy sourceComparisons
    cases comparisonsExpansion with
    | intro semanticDeclarations semanticArtifactEq semanticDigestEq
        semanticPolicyEq semanticBackendsEq semanticBindingsEq =>
      have semanticSafe : ∀ declaration ∈ semantic.decls,
          (∀ spelling ∈ declNullaryCons declaration,
            Binding.renameText ρg spelling = spelling) ∧
          DeclarationReconstructionSafe ρg declaration :=
        DeclsExpandComparisons_reconstruction_safe valueErasedSound bindingsEq
          semanticDeclarations (by simp)
      have semanticBindingsEmpty : semantic.valueBindings = [] :=
        semanticBindingsEq.trans bindingsEq
      have semanticLeavesEq : leafIds semantic = leafIds program := by
        have ids := DeclsExpandComparisons_leafIds semanticDeclarations
        unfold leafIds at ids ⊢
        exact ids.symm.trans valueLeavesEq
      have semanticComparisonSound :
          ComparisonRenamingSound ρg semantic policy :=
        { atoms := by
            intro spelling spellingMember _
            obtain ⟨declaration, declarationMember, contained⟩ :=
              List.mem_flatMap.mp spellingMember
            exact (semanticSafe declaration declarationMember).1 spelling
              contained
          patterns := sound.patterns }
      have semanticPayloadSafe : ∀ declaration ∈ semantic.decls,
          DeclarationReconstructionSafe ρg declaration := by
        intro declaration declarationMember
        exact (semanticSafe declaration declarationMember).2
      exact
        { bindingsEmpty := semanticBindingsEmpty
          declarationsFixed := by
            intro declaration declarationMember
            exact (semanticSafe declaration declarationMember).1
          erasedSound :=
            eraseProgramNl_reconstructionSound sound semanticComparisonSound
              semanticBindingsEmpty semanticPayloadSafe semanticLeavesEq }

mutual
  private theorem residualTerm_eq_self_of_fixed
      (term : Lara.Term)
      (fixed : ∀ spelling ∈ termNullaryCons term,
        Binding.renameText ρg spelling = spelling) :
      renameResidualTerm ρg term = term := by
    cases term with
    | num source => rfl
    | str source => rfl
    | con name terms =>
        cases terms with
        | nil =>
            simp only [renameResidualTerm, termNullaryCons, List.mem_singleton]
            rw [fixed name (List.mem_singleton.mpr rfl)]
        | cons head tail =>
            simp only [renameResidualTerm, termNullaryCons]
            congr 1
            exact residualTerms_eq_self_of_fixed (.cons head tail) (by
              intro spelling member
              exact fixed spelling member)
  private theorem residualTerms_eq_self_of_fixed
      (terms : Lara.Terms)
      (fixed : ∀ spelling ∈ termsNullaryCons terms,
        Binding.renameText ρg spelling = spelling) :
      renameResidualTerms ρg terms = terms := by
    cases terms with
    | nil => rfl
    | cons head tail =>
        simp only [renameResidualTerms, termsNullaryCons]
        rw [residualTerm_eq_self_of_fixed head (by
          intro spelling member
          exact fixed spelling (List.mem_append_left _ member))]
        rw [residualTerms_eq_self_of_fixed tail (by
          intro spelling member
          exact fixed spelling (List.mem_append_right _ member))]
end

private theorem residualAtom_eq_self_of_fixed
    (atom : Lara.Atom)
    (fixed : ∀ spelling ∈ atomNullaryCons atom,
      Binding.renameText ρg spelling = spelling) :
    renameResidualAtom ρg atom = atom := by
  cases atom with
  | atom predicate terms =>
      simp only [renameResidualAtom, atomNullaryCons]
      rw [residualTerms_eq_self_of_fixed terms fixed]

private theorem surfaceAttacksOf_eraseProgramNl_global
    (program : Presentation.Program) :
    surfaceAttacksOf (eraseProgramNl program) = surfaceAttacksOf program := by
  unfold surfaceAttacksOf eraseProgramNl
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp_all [eraseDeclNl]

private theorem surfaceAttacksOf_renameProgram_global
    (program : Presentation.Program) :
    surfaceAttacksOf (Binding.renameProgram ρg program) =
      (surfaceAttacksOf program).map (Binding.renameSurfaceAttack ρg) := by
  unfold surfaceAttacksOf Binding.renameProgram
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp_all [Binding.renameDecl]

private theorem admissionLeafMetas_eraseProgramNl_global
    (program : Presentation.Program) :
    admissionLeafMetas (eraseProgramNl program) = admissionLeafMetas program := by
  unfold admissionLeafMetas leafRecords eraseProgramNl
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp_all [eraseDeclNl]

private theorem admissionLeafMetas_renameProgram_global
    (program : Presentation.Program) :
    admissionLeafMetas (Binding.renameProgram ρg program) =
      (admissionLeafMetas program).map (renameLeafMeta ρg) := by
  unfold admissionLeafMetas leafRecords Binding.renameProgram
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;>
        simp_all [Binding.renameDecl, renameLeafMeta, toSupportLeafId,
          renameCoreLeafId]

private theorem admissionGroups_eraseProgramNl_global
    (program : Presentation.Program) :
    admissionGroups (eraseProgramNl program) = admissionGroups program := by
  unfold admissionGroups eraseProgramNl
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp_all [eraseDeclNl]

private theorem admissionGroups_renameProgram_global
    (program : Presentation.Program) :
    admissionGroups (Binding.renameProgram ρg program) =
      (admissionGroups program).map (renameDupGroup ρg) := by
  unfold admissionGroups Binding.renameProgram
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;>
        simp_all [Binding.renameDecl, renameDupGroup, toSupportLeafId,
          renameCoreLeafId]

private theorem surfaceAttacksOf_semantic_related
    (related : SemanticProgramRelated ρg source target) :
    surfaceAttacksOf target =
      (surfaceAttacksOf source).map (Binding.renameSurfaceAttack ρg) := by
  unfold SemanticProgramRelated at related
  have mapped := congrArg surfaceAttacksOf related
  rw [surfaceAttacksOf_eraseProgramNl_global,
    surfaceAttacksOf_eraseProgramNl_global] at mapped
  exact mapped.trans (surfaceAttacksOf_renameProgram_global source)

private theorem admissionLeafMetas_semantic_related
    (related : SemanticProgramRelated ρg source target) :
    admissionLeafMetas target =
      (admissionLeafMetas source).map (renameLeafMeta ρg) := by
  unfold SemanticProgramRelated at related
  have mapped := congrArg admissionLeafMetas related
  rw [admissionLeafMetas_eraseProgramNl_global,
    admissionLeafMetas_eraseProgramNl_global] at mapped
  exact mapped.trans (admissionLeafMetas_renameProgram_global source)

private theorem admissionGroups_semantic_related
    (related : SemanticProgramRelated ρg source target) :
    admissionGroups target =
      (admissionGroups source).map (renameDupGroup ρg) := by
  unfold SemanticProgramRelated at related
  have mapped := congrArg admissionGroups related
  rw [admissionGroups_eraseProgramNl_global,
    admissionGroups_eraseProgramNl_global] at mapped
  exact mapped.trans (admissionGroups_renameProgram_global source)

private theorem admissionLeafTable_semantic_related
    (facts : ExpandedSemanticFacts ρg program policy source)
    (related : SemanticProgramRelated ρg source target) :
    admissionLeafTable target =
      (admissionLeafTable source).map fun entry =>
        (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2) := by
  have programsRelated :
      eraseProgramNl target =
        Binding.renameProgram ρg (eraseProgramNl source) := by
    calc
      eraseProgramNl target =
          eraseProgramNl (Binding.renameProgram ρg source) := related
      _ = Binding.renameProgram ρg (eraseProgramNl source) :=
        eraseProgramNl_renameProgram ρg source
  have leavesRelated := congrArg declaredLeaves programsRelated
  rw [declaredLeaves_renameResidual facts.erasedSound] at leavesRelated
  rw [declaredLeaves_eraseProgramNl,
    declaredLeaves_eraseProgramNl] at leavesRelated
  unfold admissionLeafTable
  rw [leavesRelated]
  simp [List.map_map, Function.comp_def, toSupportLeafId,
    renameCoreLeafId]

private theorem rawAttackOfResolved_rename_global
    (surface : Presentation.SurfaceAttack) (resolved : Lara.Attack.Attack) :
    rawAttackOfResolved (Binding.renameSurfaceAttack ρg surface)
        (renameCoreAttack ρg resolved) =
      (rawAttackOfResolved surface resolved).map (renameRawAttack ρg) := by
  cases surface <;> cases resolved <;>
    simp [rawAttackOfResolved, Binding.renameSurfaceAttack,
      renameCoreAttack, renameRawAttack]

private theorem rawAttacksOfResolved_rename_global
    (surfaces : List Presentation.SurfaceAttack)
    (resolved : List Lara.Attack.Attack) :
    rawAttacksOfResolved (surfaces.map (Binding.renameSurfaceAttack ρg))
        (resolved.map (renameCoreAttack ρg)) =
      (rawAttacksOfResolved surfaces resolved).map
        (List.map (renameRawAttack ρg)) := by
  induction surfaces generalizing resolved with
  | nil => cases resolved <;> rfl
  | cons surface rest ih =>
      cases resolved with
      | nil => rfl
      | cons head tail =>
          simp only [List.map_cons, rawAttacksOfResolved]
          rw [rawAttackOfResolved_rename_global, ih]
          cases rawAttackOfResolved surface head <;>
            cases rawAttacksOfResolved rest tail <;> simp

private theorem admissionArgs_rename_global
    (source : Input) (pairs : List ReconstructedArgument) :
    admissionArgs
        (pairs.map
          (renameReconstructedArgument ρg (programValues source.program))) =
      (admissionArgs pairs).map fun entry =>
        ((ρg.arg ⟨entry.1⟩).val, renameCoreSupportTerm ρg entry.2) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      simp [admissionArgs, renameReconstructedArgument, ih,
        Binding.renameArg]

private theorem buildGamma_rename_at
    (leaves : List (Support.LeafId × Lara.Atom)) (leaf : Support.LeafId) :
    Lara.Admission.buildGamma
        (leaves.map fun entry =>
          (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2))
        (renameCoreLeafId ρg leaf) =
      (Lara.Admission.buildGamma leaves leaf).map (renameResidualAtom ρg) := by
  unfold Lara.Admission.buildGamma
  rw [admission_find?_map
    (fun entry : Support.LeafId × Lara.Atom =>
      (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2))
    (fun entry => decide (entry.1 = leaf))
    (fun entry => decide (entry.1 = renameCoreLeafId ρg leaf))
    leaves]
  · cases leaves.find? (fun entry => decide (entry.1 = leaf)) <;> rfl
  · intro entry
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (renameCoreLeafId_injective ρg).eq_iff

private theorem buildGamma_rename
    (leaves : List (Support.LeafId × Lara.Atom)) :
    Lara.Admission.buildGamma
        (leaves.map fun entry =>
          (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2)) =
      renameGamma ρg (Lara.Admission.buildGamma leaves) := by
  funext target
  unfold renameGamma
  by_cases witness : ∃ source, renameCoreLeafId ρg source = target
  · rw [dif_pos witness]
    have targetEq :
        renameCoreLeafId ρg (Classical.choose witness) = target :=
      Classical.choose_spec witness
    calc
      Lara.Admission.buildGamma
          (leaves.map fun entry =>
            (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2))
          target =
        Lara.Admission.buildGamma
          (leaves.map fun entry =>
            (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2))
          (renameCoreLeafId ρg (Classical.choose witness)) := by
            rw [targetEq]
      _ = (Lara.Admission.buildGamma leaves
          (Classical.choose witness)).map (renameResidualAtom ρg) :=
        buildGamma_rename_at leaves (Classical.choose witness)
  · rw [dif_neg witness]
    unfold Lara.Admission.buildGamma
    rw [List.find?_eq_none.mpr]
    · rfl
    · intro entry entryMember predicateTrue
      obtain ⟨source, sourceMember, sourceEq⟩ := List.mem_map.mp entryMember
      subst entry
      have equal : renameCoreLeafId ρg source.1 = target :=
        of_decide_eq_true predicateTrue
      exact witness ⟨source.1, equal⟩

private theorem rootHoles_rename (term : Support.SupportTerm) :
    rootHoles (renameCoreSupportTerm ρg term) =
      (rootHoles term).map (renameCoreQuestionId ρg) := by
  cases term <;> rfl

private theorem rootAuthoredHoles_rename
    (values : List Presentation.ValueName)
    (term : Presentation.SupportTerm) :
    rootAuthoredHoles (Binding.renameSupportTerm ρg values term) =
      (rootAuthoredHoles term).map ρg.obligation := by
  cases term <;> rfl

private theorem openQuestionsOf_rename_global
    (sourceInput : Input) (pairs : List ReconstructedArgument) :
    openQuestionsOf
        (pairs.map (renameReconstructedArgument ρg
          (programValues sourceInput.program))) =
      (openQuestionsOf pairs).map fun entry =>
        (ρg.arg entry.1, entry.2.map (renameCoreQuestionId ρg)) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      simp [openQuestionsOf, renameReconstructedArgument, Binding.renameArg,
        rootHoles_rename, ih]

private theorem authoredObligationsOf_rename_global
    (program : Presentation.Program) :
    authoredObligationsOf (Binding.renameProgram ρg program) =
      (authoredObligationsOf program).map fun entry =>
        (ρg.arg entry.1, entry.2.map ρg.obligation) := by
  unfold authoredObligationsOf Binding.renameProgram
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration with
      | leaf leaf => simpa [Binding.renameDecl] using ih
      | claim claim => simpa [Binding.renameDecl] using ih
      | attack attack => simpa [Binding.renameDecl] using ih
      | status status => simpa [Binding.renameDecl] using ih
      | group group => simpa [Binding.renameDecl] using ih
      | comparison comparison => simpa [Binding.renameDecl] using ih
      | arg argument =>
          cases argument with
          | mk id conclusion instantiation =>
              cases instantiation with
              | explicitTheta term =>
                  simp only [List.map_cons, Binding.renameDecl,
                    Binding.renameArg, Binding.renameArgInstantiation,
                    List.filterMap_cons, Option.toList_some]
                  rw [rootAuthoredHoles_rename]
                  simpa using ih
              | inferTheta rule refs discharges obligations assurance =>
                  simp only [List.map_cons, Binding.renameDecl,
                    Binding.renameArg, Binding.renameArgInstantiation,
                    List.filterMap_cons, List.map_cons]
                  rw [ih]

private theorem admissionKeptPairs_rename_global
    (sourceInput : Input) (pairs : List ReconstructedArgument)
    (admission : Lara.Admission.AdmissionResult)
    (keepEq : admission.prune.keep = fun argument =>
      !Lara.Groups.usesLeaf admission.prune.removedSeed argument.2) :
    admissionKeptPairs
        (pairs.map (renameReconstructedArgument ρg
          (programValues sourceInput.program)))
        (renameAdmissionResult ρg admission) =
      (admissionKeptPairs pairs admission).map
        (renameReconstructedArgument ρg
          (programValues sourceInput.program)) := by
  unfold admissionKeptPairs renameAdmissionResult renameAdmissionPrune
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      simp only [List.map_cons, List.filter_cons]
      simp only [renameReconstructedArgument]
      rw [usesLeaf_rename (ρg := ρg) admission.prune.removedSeed pair.core]
      rw [keepEq]
      split <;>
        simp_all [renameReconstructedArgument, Binding.renameArg]

private def semanticClaimIds (program : Presentation.Program) :
    List Presentation.PropId :=
  program.decls.filterMap fun
    | .claim claim => some claim.id
    | _ => none

private theorem semanticClaimIds_eraseProgramNl
    (program : Presentation.Program) :
    semanticClaimIds (eraseProgramNl program) = semanticClaimIds program := by
  unfold semanticClaimIds eraseProgramNl
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih => cases declaration <;> simp_all [eraseDeclNl]

private theorem semanticClaimIds_renameProgram
    (program : Presentation.Program) :
    semanticClaimIds (Binding.renameProgram ρg program) =
      (semanticClaimIds program).map ρg.prop := by
  unfold semanticClaimIds Binding.renameProgram
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih => cases declaration <;>
      simp_all [Binding.renameDecl]

private theorem semanticClaimIds_semantic_related
    (related : SemanticProgramRelated ρg source target) :
    semanticClaimIds target = (semanticClaimIds source).map ρg.prop := by
  unfold SemanticProgramRelated at related
  have mapped := congrArg semanticClaimIds related
  rw [semanticClaimIds_eraseProgramNl,
    semanticClaimIds_eraseProgramNl] at mapped
  exact mapped.trans (semanticClaimIds_renameProgram source)

private def claimFor (pairs : List ReconstructedArgument)
    (claim : Presentation.PropId) : Lara.Grounded.Claim :=
  let supporting := pairs.zipIdx.filter fun (pair, _) =>
    argSupportsClaim claim pair.argument.concl
  { support := (supporting.filter fun (pair, _) =>
      rootHoles pair.core = []).map (·.2)
    holes := (supporting.filter fun (pair, _) =>
      rootHoles pair.core != []).map (·.2) }

private theorem claimsOf_eq_claimFor
    (pairs : List ReconstructedArgument) (program : Presentation.Program) :
    claimsOf pairs program = (semanticClaimIds program).map fun claim =>
      (claim, claimFor pairs claim) := by
  unfold claimsOf semanticClaimIds claimFor
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih => cases declaration <;> simp_all

private theorem argSupportsClaim_rename_global
    (claim : Presentation.PropId) (conclusion : Presentation.ArgConcl) :
    argSupportsClaim (ρg.prop claim)
        (Binding.renameArgConcl ρg conclusion) =
      argSupportsClaim claim conclusion := by
  cases conclusion <;>
    simp [argSupportsClaim, Binding.renameArgConcl,
      ρg.prop_injective.eq_iff]
  rename_i challenge
  cases challenge <;> rfl

private theorem claimFor_rename_global
    (sourceInput : Input) (pairs : List ReconstructedArgument)
    (claim : Presentation.PropId) :
    claimFor
        (pairs.map (renameReconstructedArgument ρg
          (programValues sourceInput.program)))
        (ρg.prop claim) = claimFor pairs claim := by
  have holesNonempty : ∀ holes : List Support.QuestionId,
      (holes.map (renameCoreQuestionId ρg) != []) = (holes != []) := by
    intro holes
    cases holes <;> rfl
  unfold claimFor
  simp only [List.zipIdx_map, List.filter_map, List.map_map,
    Function.comp_def, Prod.map]
  simp [renameReconstructedArgument, Binding.renameArg,
    argSupportsClaim_rename_global, rootHoles_rename, holesNonempty]

private theorem claimsOf_rename_global
    (sourceInput : Input) (pairs : List ReconstructedArgument)
    (related : SemanticProgramRelated ρg source target) :
    claimsOf
        (pairs.map (renameReconstructedArgument ρg
          (programValues sourceInput.program))) target =
      (claimsOf pairs source).map fun claim => (ρg.prop claim.1, claim.2) := by
  rw [claimsOf_eq_claimFor, claimsOf_eq_claimFor,
    semanticClaimIds_semantic_related related]
  simp [List.map_map, Function.comp_def, claimFor_rename_global]

mutual
  private theorem renameValueTerm_nil
      (term : Lara.Term) :
      Binding.renameValueTerm ρg [] term = term := by
    cases term with
    | num source => rfl
    | str source => rfl
    | con name terms =>
        cases terms with
        | nil => simp [Binding.renameValueTerm]
        | cons head tail =>
            simp [Binding.renameValueTerm,
              renameValueTerms_nil (.cons head tail)]
  private theorem renameValueTerms_nil
      (terms : Lara.Terms) :
      Binding.renameValueTerms ρg [] terms = terms := by
    cases terms with
    | nil => rfl
    | cons head tail =>
        simp [Binding.renameValueTerms, renameValueTerm_nil head,
          renameValueTerms_nil tail]
end

private theorem renameValueAtom_nil (atom : Lara.Atom) :
    Binding.renameValueAtom ρg [] atom = atom := by
  cases atom
  simp [Binding.renameValueAtom, renameValueTerms_nil]

private def semanticFormalClaims (program : Presentation.Program) :
    List Lara.Atom :=
  program.decls.filterMap fun
    | .claim claim => some claim.formal
    | _ => none

private theorem semanticFormalClaims_eraseProgramNl
    (program : Presentation.Program) :
    semanticFormalClaims (eraseProgramNl program) =
      semanticFormalClaims program := by
  unfold semanticFormalClaims eraseProgramNl
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih => cases declaration <;> simp_all [eraseDeclNl]

private theorem semanticFormalClaimsDecls_rename
    (declarations : List Presentation.Decl)
    (fixed : ∀ declaration ∈ declarations,
      ∀ spelling ∈ declNullaryCons declaration,
        Binding.renameText ρg spelling = spelling) :
    (declarations.map (Binding.renameDecl ρg [])).filterMap (fun
        | .claim claim => some claim.formal
        | _ => none) =
      (declarations.filterMap fun
        | .claim claim => some claim.formal
        | _ => none).map (renameResidualAtom ρg) := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
      have tailFixed : ∀ candidate ∈ rest,
          ∀ spelling ∈ declNullaryCons candidate,
            Binding.renameText ρg spelling = spelling := by
        intro candidate candidateMember
        exact fixed candidate (by simp [candidateMember])
      have tail := ih tailFixed
      cases declaration with
      | claim claim =>
          have formalFixed : renameResidualAtom ρg claim.formal =
              claim.formal :=
            residualAtom_eq_self_of_fixed claim.formal (by
              intro spelling spellingMember
              exact fixed (.claim claim) (by simp) spelling (by
                simpa [declNullaryCons] using spellingMember))
          simp [Binding.renameDecl, renameValueAtom_nil, formalFixed, tail]
      | leaf leaf => simpa [Binding.renameDecl] using tail
      | arg argument => simpa [Binding.renameDecl] using tail
      | attack attack => simpa [Binding.renameDecl] using tail
      | status status => simpa [Binding.renameDecl] using tail
      | group group => simpa [Binding.renameDecl] using tail
      | comparison comparison => simpa [Binding.renameDecl] using tail

private theorem semanticFormalClaims_renameProgram
    (facts : ExpandedSemanticFacts ρg program policy source) :
    semanticFormalClaims (Binding.renameProgram ρg source) =
      (semanticFormalClaims source).map (renameResidualAtom ρg) := by
  unfold semanticFormalClaims Binding.renameProgram
  have valuesEmpty : programValues source = [] := by
    simp [programValues, facts.bindingsEmpty]
  change
    (source.decls.map
      (Binding.renameDecl ρg (programValues source))).filterMap (fun
        | .claim claim => some claim.formal
        | _ => none) = _
  rw [valuesEmpty]
  exact semanticFormalClaimsDecls_rename source.decls facts.declarationsFixed

private theorem semanticFormalClaims_semantic_related
    (facts : ExpandedSemanticFacts ρg program policy source)
    (related : SemanticProgramRelated ρg source target) :
    semanticFormalClaims target =
      (semanticFormalClaims source).map (renameResidualAtom ρg) := by
  unfold SemanticProgramRelated at related
  have mapped := congrArg semanticFormalClaims related
  rw [semanticFormalClaims_eraseProgramNl,
    semanticFormalClaims_eraseProgramNl] at mapped
  exact mapped.trans (semanticFormalClaims_renameProgram facts)

private theorem statusIds_eraseProgramNl
    (program : Presentation.Program) :
    statusIds (eraseProgramNl program) = statusIds program := by
  unfold statusIds eraseProgramNl
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp [eraseDeclNl, eraseComparisonNl, ih]

private theorem claimIds_eraseProgramNl
    (program : Presentation.Program) :
    claimIds (eraseProgramNl program) = claimIds program := by
  unfold claimIds eraseProgramNl
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp [eraseDeclNl, eraseComparisonNl, ih]

private theorem groupDecls_eraseProgramNl
    (program : Presentation.Program) :
    groupDecls (eraseProgramNl program) = groupDecls program := by
  unfold groupDecls eraseProgramNl
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp [eraseDeclNl, eraseComparisonNl, ih]

private theorem statusesWellFormed_eraseProgramNl_iff
    (program : Presentation.Program) :
    StatusesWellFormed (eraseProgramNl program) ↔ StatusesWellFormed program := by
  unfold StatusesWellFormed
  rw [statusIds_eraseProgramNl, claimIds_eraseProgramNl]

private theorem groupsWellFormed_eraseProgramNl_iff
    (program : Presentation.Program) :
    GroupsWellFormed (eraseProgramNl program) ↔ GroupsWellFormed program := by
  unfold GroupsWellFormed
  rw [groupDecls_eraseProgramNl, leafIds_eraseProgramNl]

private theorem statusesWellFormed_renameProgram_iff
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program) :
    StatusesWellFormed (Binding.renameProgram ρg program) ↔
      StatusesWellFormed program := by
  rw [← statusesWellFormedB_iff, ← statusesWellFormedB_iff,
    Renaming.statusesWellFormedB_rename]

private theorem groupsWellFormed_renameProgram_iff
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program) :
    GroupsWellFormed (Binding.renameProgram ρg program) ↔
      GroupsWellFormed program := by
  rw [← groupsWellFormedB_iff, ← groupsWellFormedB_iff,
    Renaming.groupsWellFormedB_rename]

private theorem statusesWellFormed_semantic_related
    (related : SemanticProgramRelated ρg source target) :
    StatusesWellFormed target ↔ StatusesWellFormed source := by
  unfold SemanticProgramRelated at related
  calc
    StatusesWellFormed target ↔ StatusesWellFormed (eraseProgramNl target) :=
      (statusesWellFormed_eraseProgramNl_iff target).symm
    _ ↔ StatusesWellFormed
        (eraseProgramNl (Binding.renameProgram ρg source)) := by rw [related]
    _ ↔ StatusesWellFormed (Binding.renameProgram ρg source) :=
      statusesWellFormed_eraseProgramNl_iff _
    _ ↔ StatusesWellFormed source :=
      statusesWellFormed_renameProgram_iff ρg source

private theorem groupsWellFormed_semantic_related
    (related : SemanticProgramRelated ρg source target) :
    GroupsWellFormed target ↔ GroupsWellFormed source := by
  unfold SemanticProgramRelated at related
  calc
    GroupsWellFormed target ↔ GroupsWellFormed (eraseProgramNl target) :=
      (groupsWellFormed_eraseProgramNl_iff target).symm
    _ ↔ GroupsWellFormed
        (eraseProgramNl (Binding.renameProgram ρg source)) := by rw [related]
    _ ↔ GroupsWellFormed (Binding.renameProgram ρg source) :=
      groupsWellFormed_eraseProgramNl_iff _
    _ ↔ GroupsWellFormed source :=
      groupsWellFormed_renameProgram_iff ρg source

private theorem requestedStatusAtoms_eraseProgramNl
    (program : Presentation.Program) :
    requestedStatusAtoms (eraseProgramNl program) =
      requestedStatusAtoms program := by
  unfold requestedStatusAtoms
  rw [statusIds_eraseProgramNl]
  have lookupEq : claimFormal? (eraseProgramNl program) = claimFormal? program := by
    funext claim
    exact claimFormal?_eraseProgramNl program claim
  rw [lookupEq]

private theorem claimFormalIn?_rename_expanded
    (declarations : List Presentation.Decl)
    (fixed : ∀ declaration ∈ declarations,
      ∀ spelling ∈ declNullaryCons declaration,
        Binding.renameText ρg spelling = spelling)
    (claimId : Presentation.PropId) :
    claimFormalIn? (declarations.map (Binding.renameDecl ρg []))
        (ρg.prop claimId) =
      (claimFormalIn? declarations claimId).map (renameResidualAtom ρg) := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
      have tailFixed : ∀ candidate ∈ rest,
          ∀ spelling ∈ declNullaryCons candidate,
            Binding.renameText ρg spelling = spelling := by
        intro candidate candidateMember
        exact fixed candidate (by simp [candidateMember])
      cases declaration with
      | claim claim =>
          have formalFixed : renameResidualAtom ρg claim.formal = claim.formal :=
            residualAtom_eq_self_of_fixed claim.formal (by
              intro spelling spellingMember
              exact fixed (.claim claim) (by simp) spelling (by
                simpa [declNullaryCons] using spellingMember))
          by_cases same : claim.id = claimId
          · have renamedSame : ρg.prop claim.id = ρg.prop claimId :=
              congrArg ρg.prop same
            simp only [claimFormalIn?, List.map_cons, Binding.renameDecl,
              List.findSome?_cons, renamedSame, ↓reduceIte, same,
              Option.map_some]
            rw [renameValueAtom_nil]
            exact congrArg some formalFixed.symm
          · have renamedNe : ρg.prop claim.id ≠ ρg.prop claimId := fun equal =>
              same (ρg.prop_injective equal)
            simp only [claimFormalIn?, List.map_cons, Binding.renameDecl,
              List.findSome?_cons, renamedNe, ↓reduceIte, same]
            simpa only [claimFormalIn?] using ih tailFixed
      | leaf leaf =>
          simpa [claimFormalIn?, Binding.renameDecl] using ih tailFixed
      | arg argument =>
          simpa [claimFormalIn?, Binding.renameDecl] using ih tailFixed
      | attack attack =>
          simpa [claimFormalIn?, Binding.renameDecl] using ih tailFixed
      | status status =>
          simpa [claimFormalIn?, Binding.renameDecl] using ih tailFixed
      | group group =>
          simpa [claimFormalIn?, Binding.renameDecl] using ih tailFixed
      | comparison comparison =>
          simpa [claimFormalIn?, Binding.renameDecl] using ih tailFixed

private theorem claimFormal?_renameProgram_expanded
    (facts : ExpandedSemanticFacts ρg program policy source)
    (claimId : Presentation.PropId) :
    claimFormal? (Binding.renameProgram ρg source) (ρg.prop claimId) =
      (claimFormal? source claimId).map (renameResidualAtom ρg) := by
  have valuesEmpty : programValues source = [] := by
    simp [programValues, facts.bindingsEmpty]
  change
    claimFormalIn?
        (source.decls.map (Binding.renameDecl ρg (programValues source)))
        (ρg.prop claimId) =
      (claimFormalIn? source.decls claimId).map (renameResidualAtom ρg)
  rw [valuesEmpty]
  exact claimFormalIn?_rename_expanded source.decls facts.declarationsFixed claimId

private theorem requestedStatusAtoms_renameProgram
    (facts : ExpandedSemanticFacts ρg program policy source) :
    requestedStatusAtoms (Binding.renameProgram ρg source) =
      (requestedStatusAtoms source).map (renameResidualAtom ρg) := by
  unfold requestedStatusAtoms
  rw [statusIds_renameProgram]
  induction statusIds source with
  | nil => rfl
  | cons claim rest ih =>
      simp only [List.map_cons, List.filterMap_cons]
      rw [claimFormal?_renameProgram_expanded facts claim]
      cases found : claimFormal? source claim <;> simp [found, ih]

private theorem requestedStatusAtoms_semantic_related
    (facts : ExpandedSemanticFacts ρg program policy source)
    (related : SemanticProgramRelated ρg source target) :
    requestedStatusAtoms target =
      (requestedStatusAtoms source).map (renameResidualAtom ρg) := by
  unfold SemanticProgramRelated at related
  have mapped := congrArg requestedStatusAtoms related
  rw [requestedStatusAtoms_eraseProgramNl,
    requestedStatusAtoms_eraseProgramNl] at mapped
  exact mapped.trans (requestedStatusAtoms_renameProgram facts)

private theorem toCorePolicy_rename_global
    (policy : Presentation.Policy) :
    toCorePolicy (Binding.renamePolicy ρg policy) =
      renameCorePolicy ρg (toCorePolicy policy) := by
  unfold toCorePolicy renameCorePolicy
  simp [Binding.renamePolicy, Binding.renameRule, Binding.renamePolicyException,
    toCoreRule, renameCoreRule, toSupportRuleId, renameCoreRuleId,
    toSupportQuestionId, renameCoreQuestionId, List.map_map,
    Function.comp_def]

@[simp] private theorem wrapRenamedArgId
    (ρg : Binding.GlobalRenaming) (value : String) :
    (⟨(ρg.arg (⟨value⟩ : Presentation.ArgId)).val⟩ :
      Presentation.ArgId) = ρg.arg ⟨value⟩ := by
  cases ρg.arg (⟨value⟩ : Presentation.ArgId)
  rfl

@[simp] private theorem wrapRenamedPropAsArgId
    (ρg : Binding.GlobalRenaming) (value : String) :
    (⟨(ρg.prop (⟨value⟩ : Presentation.PropId)).val⟩ :
      Presentation.ArgId) = ρg.arg ⟨value⟩ := by
  apply congrArg Presentation.ArgId.mk
  exact (ρg.arg_coherent ⟨value⟩).symm

/-- Ground data is renamed on elaborated leaves and claims, while the policy's
theory/formula table remains a replay-significant literal suffix. -/
def GroundRelated (ρg : Binding.GlobalRenaming) (sourceInput : Input)
    (source target : List Lara.Atom) : Prop :=
  ∃ executableGround,
    source = executableGround ++ sourceInput.policy.theories.flatMap (·.2) ∧
    target = executableGround.map (renameResidualAtom ρg) ++
      sourceInput.policy.theories.flatMap (·.2)

/-- Every public retained-output field commutes with global renaming.  The
semantic program uses the prose-erased executable relation because expanded
natural-language text is not literally equivariant. -/
structure ElaboratedRelated (ρg : Binding.GlobalRenaming)
    (sourceInput : Input) (source target : Elaborated canon) : Prop where
  gamma : target.gamma = renameGamma ρg source.gamma
  ground : GroundRelated ρg sourceInput source.ground target.ground
  unit : target.unit = renameCoreUnit ρg source.unit
  claims : target.claims = source.claims.map fun claim =>
    (ρg.prop claim.1, claim.2)
  argIds : target.argIds = source.argIds.map ρg.arg
  authoredObligations : target.authoredObligations =
    source.authoredObligations.map fun entry =>
      (ρg.arg entry.1, entry.2.map ρg.obligation)
  openQuestions : target.openQuestions = source.openQuestions.map fun entry =>
    (ρg.arg entry.1, entry.2.map (renameCoreQuestionId ρg))
  resolvedAttacks : target.resolvedAttacks =
    source.resolvedAttacks.map (renameCoreAttack ρg)
  semanticProgram : SemanticProgramRelated ρg
    source.semanticProgram target.semanticProgram

private theorem outputFromAdmission_related
    {canon : String → String}
    (sourceInput : Input)
    (facts : ExpandedSemanticFacts ρg sourceInput.program
      sourceInput.policy sourceSemantic)
    (semanticRelated :
      SemanticProgramRelated ρg sourceSemantic targetSemantic)
    (sourcePairs : List ReconstructedArgument)
    (sourceAdmission : Lara.Admission.AdmissionResult)
    (keepEq : sourceAdmission.prune.keep = fun argument =>
      !Lara.Groups.usesLeaf sourceAdmission.prune.removedSeed argument.2) :
    ElaboratedRelated (canon := canon) ρg sourceInput
      (outputFromAdmission (canon := canon) sourceInput sourceSemantic
        sourcePairs sourceAdmission)
      (outputFromAdmission (canon := canon)
        ⟨Binding.renameProgram ρg sourceInput.program,
          Binding.renamePolicy ρg sourceInput.policy⟩
        targetSemantic
        (sourcePairs.map (renameReconstructedArgument ρg
          (programValues sourceInput.program)))
        (renameAdmissionResult ρg sourceAdmission)) := by
  have keptPairs := admissionKeptPairs_rename_global (ρg := ρg)
    sourceInput sourcePairs sourceAdmission keepEq
  have claims := claimsOf_rename_global (ρg := ρg) sourceInput
    (admissionKeptPairs sourcePairs sourceAdmission) semanticRelated
  have questions := openQuestionsOf_rename_global (ρg := ρg) sourceInput
    (admissionKeptPairs sourcePairs sourceAdmission)
  have requestedStatuses := requestedStatusAtoms_semantic_related
    (ρg := ρg) facts semanticRelated
  constructor
  · simp [outputFromAdmission, renameAdmissionResult, renameAdmissionPrune,
      buildGamma_rename]
  · refine ⟨sourceAdmission.prune.checkedLeaves.map (·.2) ++
        requestedStatusAtoms sourceSemantic, ?_, ?_⟩
    · rfl
    · simp only [outputFromAdmission]
      change
        (renameAdmissionResult ρg sourceAdmission).prune.checkedLeaves.map
              (·.2) ++
            requestedStatusAtoms targetSemantic ++
          (Binding.renamePolicy ρg sourceInput.policy).theories.flatMap
            (·.2) = _
      rw [requestedStatuses]
      simp [renameAdmissionResult,
        renameAdmissionPrune, Binding.renamePolicy, List.map_append,
        List.map_map, Function.comp_def, List.append_assoc]
  · simp only [outputFromAdmission]
    rw [toCorePolicy_rename_global]
    simp [renameAdmissionResult, renameAdmissionPrune, renameCoreUnit,
      Binding.renamePolicy]
  · simp [outputFromAdmission, keptPairs, claims]
  · simp [outputFromAdmission, renameAdmissionResult, renameAdmissionPrune,
      wrapRenamedArgId ρg, wrapRenamedPropAsArgId ρg]
  · simp [outputFromAdmission, authoredObligationsOf_rename_global]
  · simp [outputFromAdmission, keptPairs, questions]
  · simp [outputFromAdmission, renameAdmissionResult, renameAdmissionPrune]
  · exact semanticRelated

private theorem groundWellSorted_of_GroundRelated
    (sigmaSound : CoreSigmaRenamingSound ρg sigma)
    (related : GroundRelated ρg sourceInput sourceGround targetGround) :
    Lara.groundWellSorted sigma targetGround =
      Lara.groundWellSorted sigma sourceGround := by
  rcases related with ⟨executable, sourceEq, targetEq⟩
  rw [sourceEq, targetEq]
  unfold Lara.groundWellSorted
  simp only [List.all_append, Bool.and_eq_true]
  have prefixSorted := groundWellSorted_rename sigmaSound executable
  unfold Lara.groundWellSorted at prefixSorted
  rw [prefixSorted]

private def checkUnitIsOkModel
    {canon : String → String}
    (gamma : Support.LeafId → Option Lara.Atom)
    (registry : Support.BackendRegistry canon)
    (ground : List Lara.Atom) (unit : Lara.Unit) : Bool :=
  match Lara.Policy.firstDuplicateRuleId? unit.policy.rules with
  | some _ => false
  | none =>
      match Lara.Check.Unit.signatureStage ground unit with
      | some _ => false
      | none =>
          match Lara.Policy.firstOutOfScope? unit.policy with
          | some _ => false
          | none =>
              match Lara.Policy.firstViolation? canon unit.policy with
              | some _ => false
              | none =>
                  exceptIsOk (Lara.Check.checkProgramDetailed
                    unit.policy.ruleLookup gamma registry unit.policy.defeat
                    unit.args unit.atts)

private theorem exceptIsOk_checkUnit_eq_model
    {canon : String → String}
    (gamma : Support.LeafId → Option Lara.Atom)
    (registry : Support.BackendRegistry canon)
    (ground : List Lara.Atom) (unit : Lara.Unit) :
    exceptIsOk (Lara.Check.Unit.checkUnit gamma registry ground unit) =
      checkUnitIsOkModel gamma registry ground unit := by
  unfold Lara.Check.Unit.checkUnit checkUnitIsOkModel
  split
  · simp_all [exceptIsOk]
  · split
    · simp_all [exceptIsOk]
    · split
      · simp_all [exceptIsOk]
      · split
        · simp_all [exceptIsOk]
        · split <;> simp_all [exceptIsOk]

private theorem checkUnit_isOk_of_groundWellSorted_eq
    {canon : String → String}
    (gamma : Support.LeafId → Option Lara.Atom)
    (registry : Support.BackendRegistry canon)
    (left right : List Lara.Atom) (unit : Lara.Unit)
    (sortedEq : Lara.groundWellSorted unit.sigma left =
      Lara.groundWellSorted unit.sigma right) :
    exceptIsOk (Lara.Check.Unit.checkUnit gamma registry left unit) =
      exceptIsOk (Lara.Check.Unit.checkUnit gamma registry right unit) := by
  have signatureEq :
      Lara.Check.Unit.signatureStage left unit =
        Lara.Check.Unit.signatureStage right unit := by
    unfold Lara.Check.Unit.signatureStage
    rw [sortedEq]
  rw [exceptIsOk_checkUnit_eq_model,
    exceptIsOk_checkUnit_eq_model]
  unfold checkUnitIsOkModel
  rw [signatureEq]

private theorem checkUnit_isOk_mixed_rename
    {canon : String → String} {env : Env canon}
    (sourceInput : Input)
    (gamma : Support.LeafId → Option Lara.Atom)
    (sourceGround targetGround : List Lara.Atom) (unit : Lara.Unit)
    (sigmaSound : CoreSigmaRenamingSound ρg unit.sigma)
    (envSound : EnvRenamingSound env ρg)
    (groundRelated : GroundRelated ρg sourceInput sourceGround targetGround) :
    exceptIsOk
        (Lara.Check.Unit.checkUnit (renameGamma ρg gamma) env.registry
          targetGround (renameCoreUnit ρg unit)) =
      exceptIsOk
        (Lara.Check.Unit.checkUnit gamma env.registry sourceGround unit) := by
  have mixedSorted : Lara.groundWellSorted unit.sigma targetGround =
      Lara.groundWellSorted unit.sigma sourceGround :=
    groundWellSorted_of_GroundRelated sigmaSound groundRelated
  have mappedSorted :
      Lara.groundWellSorted unit.sigma
          (sourceGround.map (renameResidualAtom ρg)) =
        Lara.groundWellSorted unit.sigma sourceGround :=
    groundWellSorted_rename sigmaSound sourceGround
  have targetToMapped := checkUnit_isOk_of_groundWellSorted_eq
    (renameGamma ρg gamma) env.registry targetGround
    (sourceGround.map (renameResidualAtom ρg)) (renameCoreUnit ρg unit)
    (by simpa [renameCoreUnit] using mixedSorted.trans mappedSorted.symm)
  exact targetToMapped.trans
    (checkUnit_isOk_rename gamma sourceGround unit sigmaSound envSound)

/-- The pre-admission carrier commutes field-for-field; only semantic prose is
related extensionally. -/
structure DeclaredElaborationRelated (ρg : Binding.GlobalRenaming)
    (sourceInput : Input) (source target : DeclaredElaboration) : Prop where
  semanticProgram : SemanticProgramRelated ρg
    source.semanticProgram target.semanticProgram
  pairs : target.pairs = source.pairs.map
    (renameReconstructedArgument ρg (programValues sourceInput.program))
  rawAttacks : target.rawAttacks = source.rawAttacks.map (renameRawAttack ρg)
  resolvedAttacks : target.resolvedAttacks =
    source.resolvedAttacks.map (renameCoreAttack ρg)
  unit : target.unit = renameCoreUnit ρg source.unit
  admission : target.admission = renameAdmissionResult ρg source.admission

/-- The complete audited result relation used by the headline theorem. -/
structure ElaboratedWithAuditRelated (ρg : Binding.GlobalRenaming)
    (sourceInput : Input) (source target : ElaboratedWithAudit canon) : Prop where
  declared : DeclaredElaborationRelated ρg sourceInput
    source.declared target.declared
  output : ElaboratedRelated ρg sourceInput source.output target.output

/-- The executable transports available for a genuine typed global renaming.
This is deliberately distinct from `alpha_elaboration_invariant`: alpha
equivalence changes only certificate binders, whereas this contract renames
every typed global namespace and transports the executable surface passes. -/
structure GlobalRenamingStageTransports (env : Env canon)
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program)
    (policy : Presentation.Policy) : Prop where
  supported :
    Supported
        ⟨Binding.renameProgram ρg program,
          Binding.renamePolicy ρg policy⟩ ↔
      Supported ⟨program, policy⟩
  valueExpansion :
    RenamedExcept (ExpandValuesErrorRelated ρg)
      (SemanticProgramRelated ρg)
      (expandValues policy program)
      (expandValues (Binding.renamePolicy ρg policy)
        (Binding.renameProgram ρg program))
  comparisonExpansion :
    RenamedExcept (ExpandValuesErrorRelated ρg)
      (fun source target =>
        RenamedExcept (ExpandComparisonsErrorRelated ρg)
          (GeneratedResultsRelated ρg)
          (expandComparisons policy source)
          (expandComparisons (Binding.renamePolicy ρg policy) target))
      (expandValues policy program)
      (expandValues (Binding.renamePolicy ρg policy)
        (Binding.renameProgram ρg program))
  reconstruction : ∀
      (declarations : List Presentation.Decl)
      (priors : List PriorArgument),
      (∀ declaration ∈ declarations, declaration ∈ program.decls) →
      PriorPayloadsFromProgram program priors →
      reconstructArgs env (Binding.renameProgram ρg program)
          (Binding.renamePolicy ρg policy)
          (declarations.map (Binding.renameDecl ρg (programValues program)))
          (priors.map (renamePriorArgument ρg)) =
        renameExcept (renameReconstructFailure ρg)
          (List.map
            (renameReconstructedArgument ρg (programValues program)))
          (reconstructArgs env program policy declarations priors)
  attackResolution : ∀
      (arguments : List
        (Presentation.ArgId × Lara.Support.SupportTerm))
      (attacks : List Presentation.SurfaceAttack),
      resolveSurfaceAttacks (Binding.renamePolicy ρg policy)
          (arguments.map fun entry =>
            (ρg.arg entry.1, renameCoreSupportTerm ρg entry.2))
          (attacks.map (Binding.renameSurfaceAttack ρg)) =
        renameExcept
          (fun failure => (ρg.arg failure.1, ρg.arg failure.2))
          (List.map (renameCoreAttack ρg))
          (resolveSurfaceAttacks policy arguments attacks)
  admissionEvaluation : ∀
      (table : List Lara.Admission.AdmissionRow)
      (metas : List Lara.Admission.LeafMeta)
      (leaves : List (Lara.Support.LeafId × Lara.Atom))
      (argsRaw : List (String × Lara.Support.SupportTerm))
      (rawAtts : List Lara.RawAttack.RawAttack)
      (groups : List Lara.Groups.DupGroup)
      (declared : Lara.Admission.AlignedAttacks argsRaw rawAtts),
      Lara.Admission.evaluateAdmission canon table
          (metas.map (renameLeafMeta ρg))
          (leaves.map fun entry =>
            (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2))
          (argsRaw.map fun entry =>
            ((ρg.arg ⟨entry.1⟩).val, renameCoreSupportTerm ρg entry.2))
          (rawAtts.map (renameRawAttack ρg))
          (groups.map (renameDupGroup ρg))
          (renameAlignedAttacks ρg declared) =
        renameSourceAdmission ρg
          (Lara.Admission.evaluateAdmission canon table metas leaves argsRaw
            rawAtts groups declared)
  coreChecking : ∀
      (gamma : Support.LeafId → Option Atom)
      (ground : List Atom) (unit : Lara.Unit),
      unit.sigma = policy.sigma →
      exceptIsOk
          (Lara.Check.Unit.checkUnit (renameGamma ρg gamma) env.registry
            (ground.map (renameResidualAtom ρg)) (renameCoreUnit ρg unit)) =
        exceptIsOk
          (Lara.Check.Unit.checkUnit gamma env.registry ground unit)

/-- Typed global renaming preserves the supported fragment and commutes with
the executable value, reconstruction/certificate, attack-resolution, and
admission/pruning passes. Unlike binder alpha-equivalence, this theorem
requires both structural renaming soundness and environment replay soundness. -/
theorem global_renaming_stage_transports
    (sound : RenamingSound ρg program policy)
    (envSound : EnvRenamingSound env ρg) :
    GlobalRenamingStageTransports env ρg program policy :=
  { supported :=
      Binding.supported_rename_iff ρg program policy sound
    valueExpansion := expandValues_rename_related sound
    comparisonExpansion :=
      expandValuesThenComparisons_rename_related sound
    reconstruction := by
      intro declarations priors contained safe
      exact reconstructArgs_rename sound envSound declarations priors
        contained safe
    attackResolution := by
      intro arguments attacks
      exact resolveSurfaceAttacks_rename sound arguments attacks
    admissionEvaluation := by
      intro table metas leaves argsRaw rawAtts groups declared
      exact evaluateAdmission_rename _ table metas leaves argsRaw rawAtts
        groups declared
    coreChecking := by
      intro gamma ground unit sigmaEq
      exact checkUnit_isOk_rename gamma ground unit
        (by
          simpa [sigmaEq] using
            Lara.Surface.Renaming.RenamingSound.coreSigma sound)
        envSound }

/-- A genuine all-namespace renaming transports the canonical audited
elaboration to the renamed input, hence also transports `elaborate`; actual
core-check acceptance agrees, and every concrete source accepted carrier has
a proof-irrelevance-safe related renamed carrier. -/
theorem global_renaming_equivariant
    {canon : String → String} {env : Env canon}
    {ρg : Binding.GlobalRenaming} {program : Presentation.Program}
    {policy : Presentation.Policy} {source : ElaboratedWithAudit canon}
    (sound : RenamingSound ρg program policy)
    (envSound : EnvRenamingSound env ρg)
    (sourceAudit : elaborateWithAudit env ⟨program, policy⟩ = .ok source) :
    ∃ target : ElaboratedWithAudit canon,
      elaborateWithAudit env
          ⟨Binding.renameProgram ρg program,
            Binding.renamePolicy ρg policy⟩ = .ok target ∧
      elaborate env ⟨program, policy⟩ = .ok source.output ∧
      elaborate env
          ⟨Binding.renameProgram ρg program,
            Binding.renamePolicy ρg policy⟩ = .ok target.output ∧
      ElaboratedWithAuditRelated ρg ⟨program, policy⟩ source target ∧
      exceptIsOk
          (Lara.Check.Unit.checkUnit target.output.gamma env.registry
            target.output.ground target.output.unit) =
        exceptIsOk
          (Lara.Check.Unit.checkUnit source.output.gamma env.registry
            source.output.ground source.output.unit) ∧
      ∀ checked : Lara.Unit.CheckedUnit canon source.output.gamma
          (Support.certOkOf env.registry),
        Lara.Check.Unit.checkUnit source.output.gamma env.registry
            source.output.ground source.output.unit = .ok checked →
        ∃ renamedChecked,
          Lara.Check.Unit.checkUnit
              (renameGamma ρg source.output.gamma) env.registry
              (source.output.ground.map (renameResidualAtom ρg))
              (renameCoreUnit ρg source.output.unit) = .ok renamedChecked ∧
          CheckedUnitRelated (canon := canon) (gamma := source.output.gamma)
            (registry := env.registry) ρg checked renamedChecked :=
  by
    obtain ⟨valueExpanded, generated, sourcePrologue, sourceValues,
      sourceComparisons, sourceIdentifiers⟩ := pass_inv sourceAudit
    have alignment := elaborateWithAudit_alignment sourceAudit
    have passTransport := expandValuesThenComparisons_rename_related sound
    cases targetValues :
        expandValues (Binding.renamePolicy ρg policy)
          (Binding.renameProgram ρg program) with
    | error targetValueError =>
        rw [sourceValues, targetValues] at passTransport
        cases passTransport
    | ok renamedValueExpanded =>
      rw [sourceValues, targetValues] at passTransport
      cases passTransport with
      | ok comparisonsTransport =>
        cases targetComparisons :
            expandComparisons (Binding.renamePolicy ρg policy)
              renamedValueExpanded with
        | error targetComparisonError =>
            rw [sourceComparisons, targetComparisons] at comparisonsTransport
            cases comparisonsTransport
        | ok targetComparisonResult =>
          obtain ⟨renamedSemantic, renamedGenerated⟩ := targetComparisonResult
          rw [sourceComparisons, targetComparisons] at comparisonsTransport
          cases comparisonsTransport with
          | ok resultsRelated =>
            have semanticRelated : SemanticProgramRelated ρg
                source.declared.semanticProgram renamedSemantic :=
              resultsRelated.1
            have facts := expandedSemanticFacts sound sourceValues
              sourceComparisons
            let renamedPairs := source.declared.pairs.map
              (renameReconstructedArgument ρg (programValues program))
            let renamedRawAttacks := source.declared.rawAttacks.map
              (renameRawAttack ρg)
            let renamedResolvedAttacks := source.declared.resolvedAttacks.map
              (renameCoreAttack ρg)
            let renamedAdmission :=
              renameAdmissionResult ρg source.declared.admission
            have targetPrologue : elaborationPrologue
                ⟨Binding.renameProgram ρg program,
                  Binding.renamePolicy ρg policy⟩ = .ok () := by
              have transported := elaborationPrologue_rename_global sound
              rw [sourcePrologue] at transported
              simpa [renameExcept] using transported
            have targetIdentifiers :
                semanticIdentifierChecks (Binding.renamePolicy ρg policy)
                    (Binding.renameProgram ρg program) = .ok () := by
              have transported := semanticIdentifierChecks_rename_global sound
              rw [sourceIdentifiers] at transported
              simpa [renameExcept] using transported
            have reconstructionTransport := reconstructExpandedArgs_rename
              sound envSound sourceValues sourceComparisons targetValues
              targetComparisons
            have targetReconstruction :
                reconstructArgs env renamedSemantic
                    (Binding.renamePolicy ρg policy)
                    renamedSemantic.decls [] = .ok renamedPairs := by
              rw [alignment.reconstruction] at reconstructionTransport
              simpa [renamedPairs, renameExcept] using reconstructionTransport
            let sourceArguments := source.declared.pairs.map fun pair =>
              (pair.argument.id, pair.core)
            have targetArgumentsEq :
                renamedPairs.map (fun pair =>
                  (pair.argument.id, pair.core)) =
                sourceArguments.map fun entry =>
                  (ρg.arg entry.1, renameCoreSupportTerm ρg entry.2) := by
              simp [renamedPairs, sourceArguments,
                renameReconstructedArgument, Binding.renameArg,
                List.map_map, Function.comp_def]
            have targetSurfaceAttacks :=
              surfaceAttacksOf_semantic_related semanticRelated
            have targetSurfaceResolution :
                resolveSurfaceAttacks (Binding.renamePolicy ρg policy)
                    (renamedPairs.map fun pair =>
                      (pair.argument.id, pair.core))
                    (surfaceAttacksOf renamedSemantic) =
                  .ok renamedResolvedAttacks := by
              rw [targetArgumentsEq, targetSurfaceAttacks]
              have transported := resolveSurfaceAttacks_rename sound
                sourceArguments
                (surfaceAttacksOf source.declared.semanticProgram)
              rw [alignment.surfaceResolution] at transported
              simpa [renamedResolvedAttacks, renameExcept] using transported
            have targetRawOrder :
                rawAttacksOfResolved (surfaceAttacksOf renamedSemantic)
                    renamedResolvedAttacks = some renamedRawAttacks := by
              rw [targetSurfaceAttacks]
              calc
                rawAttacksOfResolved
                    ((surfaceAttacksOf source.declared.semanticProgram).map
                      (Binding.renameSurfaceAttack ρg))
                    renamedResolvedAttacks =
                  (rawAttacksOfResolved
                    (surfaceAttacksOf source.declared.semanticProgram)
                    source.declared.resolvedAttacks).map
                      (List.map (renameRawAttack ρg)) := by
                    simpa [renamedResolvedAttacks] using
                      rawAttacksOfResolved_rename_global
                        (ρg := ρg)
                        (surfaceAttacksOf source.declared.semanticProgram)
                        source.declared.resolvedAttacks
                _ = some renamedRawAttacks := by
                  rw [alignment.rawOrder]
                  rfl
            have admissionArgsEq : admissionArgs renamedPairs =
                (admissionArgs source.declared.pairs).map fun entry =>
                  ((ρg.arg ⟨entry.1⟩).val,
                    renameCoreSupportTerm ρg entry.2) := by
              exact admissionArgs_rename_global (ρg := ρg)
                ⟨program, policy⟩ source.declared.pairs
            have mappedIdsNodup :
                (((admissionArgs source.declared.pairs).map fun entry =>
                    ((ρg.arg ⟨entry.1⟩).val,
                      renameCoreSupportTerm ρg entry.2)).map (·.1)).Nodup := by
              simpa [List.map_map, Function.comp_def] using
                (nodup_map_iff_of_injective
                  (renameCoreArgString_injective ρg)).2 alignment.idsNodup
            have targetIdsNodup :
                ((admissionArgs renamedPairs).map (·.1)).Nodup := by
              rw [admissionArgsEq]
              exact mappedIdsNodup
            let sourceAligned : Lara.Admission.AlignedAttacks
                (admissionArgs source.declared.pairs)
                source.declared.rawAttacks :=
              { resolved := source.declared.resolvedAttacks
                resolve_eq := alignment.rawResolution
                ids_nodup := alignment.idsNodup }
            have targetRawResolution : Lara.RawAttack.resolveAttacks
                (admissionArgs renamedPairs) renamedRawAttacks =
                  .ok renamedResolvedAttacks := by
              have transported := rawResolveAttacks_rename
                (ρg := ρg) (admissionArgs source.declared.pairs)
                source.declared.rawAttacks
              rw [alignment.rawResolution] at transported
              simpa [admissionArgsEq, renamedRawAttacks,
                renamedResolvedAttacks, renameExcept] using transported
            let targetAligned : Lara.Admission.AlignedAttacks
                (admissionArgs renamedPairs) renamedRawAttacks :=
              { resolved := renamedResolvedAttacks
                resolve_eq := targetRawResolution
                ids_nodup := targetIdsNodup }
            have targetResolveAligned :
                resolveAligned (admissionArgs renamedPairs) renamedRawAttacks
                    targetIdsNodup = .ok targetAligned := by
              unfold resolveAligned
              split
              · rename_i error found
                rw [targetRawResolution] at found
                contradiction
              · rename_i resolved found
                have same : resolved = renamedResolvedAttacks :=
                  Except.ok.inj (found.symm.trans targetRawResolution)
                subst resolved
                rfl
            have targetMetas :=
              admissionLeafMetas_semantic_related semanticRelated
            have targetLeaves :=
              admissionLeafTable_semantic_related facts semanticRelated
            have targetGroups :=
              admissionGroups_semantic_related semanticRelated
            have sourceAdmissionEvaluation :
                Lara.Admission.evaluateAdmission canon (admissionRows policy)
                    (admissionLeafMetas source.declared.semanticProgram)
                    (admissionLeafTable source.declared.semanticProgram)
                    (admissionArgs source.declared.pairs)
                    source.declared.rawAttacks
                    (admissionGroups source.declared.semanticProgram)
                    sourceAligned =
                  .accepted source.declared.admission := by
              simpa [sourceAligned] using alignment.admissionEvaluation
            have admissionTransport := evaluateAdmission_rename (ρg := ρg) canon
              (admissionRows policy)
              (admissionLeafMetas source.declared.semanticProgram)
              (admissionLeafTable source.declared.semanticProgram)
              (admissionArgs source.declared.pairs)
              source.declared.rawAttacks
              (admissionGroups source.declared.semanticProgram)
              sourceAligned
            rw [sourceAdmissionEvaluation] at admissionTransport
            have targetAdmissionEvaluation :
                Lara.Admission.evaluateAdmission canon
                    (admissionRows (Binding.renamePolicy ρg policy))
                    (admissionLeafMetas renamedSemantic)
                    (admissionLeafTable renamedSemantic)
                    (admissionArgs renamedPairs) renamedRawAttacks
                    (admissionGroups renamedSemantic) targetAligned =
                  .accepted renamedAdmission := by
              simpa [Binding.renamePolicy, admissionRows,
                Binding.rename_arg_val, targetMetas, targetLeaves,
                admissionArgsEq, renamedRawAttacks, targetGroups,
                targetAligned, sourceAligned, renameAlignedAttacks,
                Lara.Admission.evaluateAdmission, renamedAdmission,
                renamedResolvedAttacks, renameSourceAdmission]
                using admissionTransport
            let targetDeclaredUnit : Lara.Unit :=
              { sigma := (Binding.renamePolicy ρg policy).sigma
                policy := toCorePolicy (Binding.renamePolicy ρg policy)
                args := renamedPairs.map (·.core)
                atts := targetAligned.resolved }
            let target : ElaboratedWithAudit canon :=
              { declared :=
                  { semanticProgram := renamedSemantic
                    pairs := renamedPairs
                    rawAttacks := renamedRawAttacks
                    resolvedAttacks := targetAligned.resolved
                    unit := targetDeclaredUnit
                    admission := renamedAdmission }
                output := outputFromAdmission
                  ⟨Binding.renameProgram ρg program,
                    Binding.renamePolicy ρg policy⟩
                  renamedSemantic renamedPairs renamedAdmission }
            have targetGroupsWellFormed : GroupsWellFormed renamedSemantic :=
              (groupsWellFormed_semantic_related semanticRelated).mpr
                alignment.groupsWellFormed
            have targetStatusesWellFormed : StatusesWellFormed renamedSemantic :=
              (statusesWellFormed_semantic_related semanticRelated).mpr
                alignment.statusesWellFormed
            have targetAudit : elaborateWithAudit env
                ⟨Binding.renameProgram ρg program,
                  Binding.renamePolicy ρg policy⟩ = .ok target := by
              unfold elaborateWithAudit
              rw [targetPrologue]
              simp only [bind_ok_reduce]
              rw [targetValues]
              simp only [bind_ok_reduce]
              rw [targetComparisons]
              simp only [bind_ok_reduce]
              rw [targetIdentifiers]
              simp only [bind_ok_reduce]
              rw [validateGroups_complete targetGroupsWellFormed]
              simp only [bind_ok_reduce]
              rw [targetReconstruction]
              simp only [bind_ok_reduce]
              rw [targetSurfaceResolution]
              simp only [bind_ok_reduce]
              rw [targetRawOrder]
              simp only [bind_ok_reduce]
              rw [resolveStatuses_complete targetStatusesWellFormed]
              simp only [bind_ok_reduce]
              rw [dif_pos targetIdsNodup]
              rw [targetResolveAligned]
              simp only
              rw [targetAdmissionEvaluation]
            have keepEq : source.declared.admission.prune.keep =
                fun argument => !Lara.Groups.usesLeaf
                  source.declared.admission.prune.removedSeed argument.2 := by
              rw [alignment.prune]
              rfl
            have outputRelated : ElaboratedRelated ρg ⟨program, policy⟩
                source.output target.output := by
              rw [alignment.retainedOutput]
              exact outputFromAdmission_related
                (canon := canon) ⟨program, policy⟩ facts semanticRelated
                source.declared.pairs source.declared.admission keepEq
            have declaredUnitRelated : target.declared.unit =
                renameCoreUnit ρg source.declared.unit := by
              rw [alignment.declaredUnit]
              simp [target, targetDeclaredUnit, targetAligned, renamedPairs,
                renameCoreUnit, Binding.renamePolicy,
                renameReconstructedArgument, List.map_map,
                Function.comp_def]
              exact ⟨toCorePolicy_rename_global policy, rfl⟩
            have declaredRelated : DeclaredElaborationRelated ρg
                ⟨program, policy⟩ source.declared target.declared :=
              { semanticProgram := semanticRelated
                pairs := by rfl
                rawAttacks := by rfl
                resolvedAttacks := by rfl
                unit := declaredUnitRelated
                admission := by rfl }
            have auditRelated : ElaboratedWithAuditRelated ρg
                ⟨program, policy⟩ source target :=
              { declared := declaredRelated
                output := outputRelated }
            have sourceElaborate : elaborate env ⟨program, policy⟩ =
                .ok source.output := by
              unfold elaborate
              rw [sourceAudit]
              rfl
            have targetElaborate : elaborate env
                ⟨Binding.renameProgram ρg program,
                  Binding.renamePolicy ρg policy⟩ = .ok target.output := by
              unfold elaborate
              rw [targetAudit]
              rfl
            have sourceSigma : source.output.unit.sigma = policy.sigma := by
              rw [alignment.outputUnit]
            have sigmaSound : CoreSigmaRenamingSound ρg
                source.output.unit.sigma := by
              rw [sourceSigma]
              exact RenamingSound.coreSigma sound
            have coreRelated : exceptIsOk
                (Lara.Check.Unit.checkUnit target.output.gamma env.registry
                  target.output.ground target.output.unit) =
                exceptIsOk
                  (Lara.Check.Unit.checkUnit source.output.gamma env.registry
                    source.output.ground source.output.unit) := by
              rw [outputRelated.gamma, outputRelated.unit]
              exact checkUnit_isOk_mixed_rename ⟨program, policy⟩
                source.output.gamma source.output.ground target.output.ground
                source.output.unit sigmaSound envSound outputRelated.ground
            refine ⟨target, targetAudit, sourceElaborate, targetElaborate,
              auditRelated, coreRelated, ?_⟩
            intro checked checkedEq
            exact checkUnit_ok_rename sigmaSound envSound checkedEq

end Renaming
end Lara.Surface
