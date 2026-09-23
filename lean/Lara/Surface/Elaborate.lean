/-
Production-ordered pure presentation elaboration (M5 Task 5).

The executable order is the source boundary prologue, value expansion,
comparison expansion, semantic identifier checks, the left-to-right argument
fold (including certificate lowering), attack resolution, declared-unit
assembly, and the one policy/group admission prune. Core checking is not part
of this module.
-/

import Lara.Surface.Check
import Lara.Admission

namespace Lara.Surface

open Lara

/-! ### Declared attack and admission carriers -/

/-- One resolved surface attack with its authored argument ids retained. -/
def rawAttackOfResolved : Presentation.SurfaceAttack → Lara.Attack.Attack →
    Option Lara.RawAttack.RawAttack
  | .rebut source target, .rebut _ _ =>
      some (.rebut source.val target.val)
  | .undercut source target _, .undercut _ _ position =>
      some (.undercut source.val target.val position)
  | .undermine source target _, .undermine _ _ position =>
      some (.undermine source.val target.val position)
  | _, _ => none

/-- Preserve authored ids while pairing the declaration-ordered semantic
attack list with its declaration-ordered surface list. -/
def rawAttacksOfResolved : List Presentation.SurfaceAttack →
    List Lara.Attack.Attack → Option (List Lara.RawAttack.RawAttack)
  | [], [] => some []
  | attack :: attacks, resolved :: resolvedRest => do
      let raw ← rawAttackOfResolved attack resolved
      let tail ← rawAttacksOfResolved attacks resolvedRest
      some (raw :: tail)
  | _, _ => none

private theorem rawLookup_of_findArgTerm
    {args : List (Presentation.ArgId × Lara.Support.SupportTerm)}
    {id : Presentation.ArgId} {term : Lara.Support.SupportTerm}
    (hids : (args.map fun row => row.1.val).Nodup)
    (h : findArgTerm args id = some term) :
    Lara.RawAttack.lookupArg (args.map fun row => (row.1.val, row.2)) id.val =
      some term := by
  unfold findArgTerm at h
  obtain ⟨row, hfind, hterm⟩ := Option.map_eq_some_iff.mp h
  have hmem : row ∈ args := List.mem_of_find?_eq_some hfind
  have hp : decide (row.1 = id) = true :=
    List.find?_some
      (p := fun entry : Presentation.ArgId × Lara.Support.SupportTerm =>
        decide (entry.1 = id)) hfind
  have hid : row.1 = id := of_decide_eq_true hp
  have hrow : (row.1.val, row.2) = (id.val, term) := by
    cases row
    simp_all
  have hids' :
      ((args.map fun row => (row.1.val, row.2)).map (·.1)).Nodup := by
    simpa [List.map_map, Function.comp_def] using hids
  exact Lara.RawAttack.lookupArg_of_mem_nodup hids'
    (List.mem_map.mpr ⟨row, hmem, hrow⟩)

/-- The raw endpoint carrier reconstructed from a declared attack derivation
resolves to the same semantic attacks in the same order. -/
theorem checksAttacks_raw_alignment
    {args : List (Presentation.ArgId × Lara.Support.SupportTerm)}
    {attacks : List Presentation.SurfaceAttack}
    {resolved : List Lara.Attack.Attack}
    (hids : (args.map fun row => row.1.val).Nodup)
    (h : ChecksAttacks policy args attacks resolved) :
    ∃ raw,
      rawAttacksOfResolved attacks resolved = some raw ∧
      Lara.RawAttack.resolveAttacks
        (args.map fun row => (row.1.val, row.2)) raw = .ok resolved := by
  induction h with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons head tail ih =>
      obtain ⟨rawTail, hrawTail, hresolveTail⟩ := ih
      cases head with
      | @rebut source sourceTerm target targetTerm hsource htarget =>
          refine ⟨.rebut source.val target.val :: rawTail, ?_, ?_⟩
          · simp [rawAttacksOfResolved, rawAttackOfResolved, hrawTail]
          · simp only [Lara.RawAttack.resolveAttacks,
              Lara.RawAttack.RawAttack.endpoints]
            rw [rawLookup_of_findArgTerm hids hsource,
              rawLookup_of_findArgTerm hids htarget]
            rw [hresolveTail]
            rfl
      | @undercut source sourceTerm target targetTerm path position
          hsource htarget hpath =>
          refine ⟨.undercut source.val target.val position :: rawTail, ?_, ?_⟩
          · simp [rawAttacksOfResolved, rawAttackOfResolved, hrawTail]
          · simp only [Lara.RawAttack.resolveAttacks,
              Lara.RawAttack.RawAttack.endpoints]
            rw [rawLookup_of_findArgTerm hids hsource,
              rawLookup_of_findArgTerm hids htarget]
            rw [hresolveTail]
            rfl
      | @undermine source sourceTerm target targetTerm path position
          hsource htarget hpath =>
          refine ⟨.undermine source.val target.val position :: rawTail, ?_, ?_⟩
          · simp [rawAttacksOfResolved, rawAttackOfResolved, hrawTail]
          · simp only [Lara.RawAttack.resolveAttacks,
              Lara.RawAttack.RawAttack.endpoints]
            rw [rawLookup_of_findArgTerm hids hsource,
              rawLookup_of_findArgTerm hids htarget]
            rw [hresolveTail]
            rfl

private theorem memberOf_argId_val (id : Presentation.ArgId)
    (ids : List Presentation.ArgId) :
    memberOf id ids = decide (id.val ∈ ids.map (·.val)) := by
  apply Bool.eq_iff_iff.mpr
  rw [memberOf_iff, decide_eq_true_iff]
  constructor
  · intro h
    exact List.mem_map.mpr ⟨id, h, rfl⟩
  · intro h
    obtain ⟨other, hmem, hval⟩ := List.mem_map.mp h
    have : other = id := by
      cases other
      cases id
      simp_all
    simpa [this] using hmem

/-- Authored-endpoint selection on the surface/semantic alignment is exactly
the raw-endpoint selection consumed by admission. -/
theorem checksAttacks_raw_selection_alignment
    {args : List (Presentation.ArgId × Lara.Support.SupportTerm)}
    {attacks : List Presentation.SurfaceAttack}
    {resolved : List Lara.Attack.Attack}
    (h : ChecksAttacks policy args attacks resolved) :
    ∀ {raw},
      rawAttacksOfResolved attacks resolved = some raw →
      ∀ kept : List Presentation.ArgId,
        selectResolvedAttacks kept attacks resolved =
          Lara.RawAttack.selectAligned
            (fun attack =>
              decide (attack.endpoints.1 ∈ kept.map (·.val)) &&
                decide (attack.endpoints.2 ∈ kept.map (·.val)))
            raw resolved := by
  induction h with
  | nil =>
      intro raw hraw kept
      simp [rawAttacksOfResolved] at hraw
      subst raw
      rfl
  | @cons attack resolved rest resolvedRest head tail ih =>
      intro raw hraw kept
      cases head with
      | @rebut source sourceTerm target targetTerm hsource htarget =>
          cases htail : rawAttacksOfResolved rest resolvedRest with
          | none =>
              simp [rawAttacksOfResolved, rawAttackOfResolved, htail] at hraw
          | some rawTail =>
              simp [rawAttacksOfResolved, rawAttackOfResolved, htail] at hraw
              subst raw
              simp [selectResolvedAttacks, Lara.RawAttack.selectAligned,
                attackEndpoints, Lara.RawAttack.RawAttack.endpoints,
                memberOf_argId_val, ih htail]
      | @undercut source sourceTerm target targetTerm path position
          hsource htarget hpath =>
          cases htail : rawAttacksOfResolved rest resolvedRest with
          | none =>
              simp [rawAttacksOfResolved, rawAttackOfResolved, htail] at hraw
          | some rawTail =>
              simp [rawAttacksOfResolved, rawAttackOfResolved, htail] at hraw
              subst raw
              simp [selectResolvedAttacks, Lara.RawAttack.selectAligned,
                attackEndpoints, Lara.RawAttack.RawAttack.endpoints,
                memberOf_argId_val, ih htail]
      | @undermine source sourceTerm target targetTerm path position
          hsource htarget hpath =>
          cases htail : rawAttacksOfResolved rest resolvedRest with
          | none =>
              simp [rawAttacksOfResolved, rawAttackOfResolved, htail] at hraw
          | some rawTail =>
              simp [rawAttacksOfResolved, rawAttackOfResolved, htail] at hraw
              subst raw
              simp [selectResolvedAttacks, Lara.RawAttack.selectAligned,
                attackEndpoints, Lara.RawAttack.RawAttack.endpoints,
                memberOf_argId_val, ih htail]


private def admissionLeafMetasOfDecls (decls : List Presentation.Decl) :
    List Lara.Admission.LeafMeta :=
  decls.filterMap fun
    | .leaf leaf =>
        some ⟨toSupportLeafId leaf.id, leaf.kind, leaf.provenance⟩
    | _ => none

private theorem DeclsExpand_admissionLeafMetas
    {env gamma source target}
    (h : DeclsExpand env gamma source target) :
    admissionLeafMetasOfDecls source = admissionLeafMetasOfDecls target := by
  induction h <;> simp_all [admissionLeafMetasOfDecls]
private theorem admissionLeafMetasOfDecls_cons_congr
    (declaration : Presentation.Decl) {left right : List Presentation.Decl}
    (h : admissionLeafMetasOfDecls left = admissionLeafMetasOfDecls right) :
    admissionLeafMetasOfDecls (declaration :: left) =
      admissionLeafMetasOfDecls (declaration :: right) := by
  cases declaration <;> simpa [admissionLeafMetasOfDecls] using h


private theorem DeclsExpandComparisons_admissionLeafMetas
    {policy program source target generated}
    (h : DeclsExpandComparisons policy program source target generated) :
    admissionLeafMetasOfDecls source = admissionLeafMetasOfDecls target := by
  induction h with
  | nil => rfl
  | keep hkeep tail ih =>
      exact admissionLeafMetasOfDecls_cons_congr _ ih
  | expand hdata tail ih =>
      simpa [admissionLeafMetasOfDecls, generatedDecls] using ih
private theorem admissionLeafMetas_eq_ofDecls (program : Presentation.Program) :
    admissionLeafMetas program = admissionLeafMetasOfDecls program.decls := by
  unfold admissionLeafMetas leafRecords
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp_all [admissionLeafMetasOfDecls]

private theorem expansions_admissionLeafMetas
    {source mid target generated}
    (hvalues : ExpandsValues source mid)
    (hcomparisons : ExpandsComparisons policy mid target generated) :
    admissionLeafMetas source = admissionLeafMetas target := by
  cases hvalues with
  | intro henv hgamma hbindings hartifact hdigest hpolicy hbackends hdecls =>
      cases hcomparisons with
      | intro hcomparisons hartifact' hdigest' hpolicy' hbackends' hbindings' =>
          rw [admissionLeafMetas_eq_ofDecls source,
            admissionLeafMetas_eq_ofDecls target]
          exact (DeclsExpand_admissionLeafMetas hdecls).trans
            (DeclsExpandComparisons_admissionLeafMetas hcomparisons)

private theorem admission_metadata_aligned (program : Presentation.Program) :
    Lara.Admission.metadataLeafAligned
      (admissionLeafMetas program) (admissionLeafTable program) := by
  unfold Lara.Admission.metadataLeafAligned
  unfold admissionLeafMetas admissionLeafTable leafRecords declaredLeaves
  simp only [List.map_map, Function.comp_apply]
  generalize program.decls = decls
  induction decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp_all

private theorem decisionFor_admissionRows (policy : Presentation.Policy)
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

private theorem admissionLeafMetas_ids_nodup
    (program : Presentation.Program) (h : (leafIds program).Nodup) :
    ((admissionLeafMetas program).map (·.id)).Nodup := by
  have heq :
      (admissionLeafMetas program).map (·.id) =
        (leafIds program).map toSupportLeafId := by
    unfold admissionLeafMetas leafRecords leafIds
    induction program.decls with
    | nil => rfl
    | cons declaration rest ih =>
        cases declaration <;> simp_all
  rw [heq]
  apply h.map
  intro left right heq
  cases left
  cases right
  simp_all [toSupportLeafId]

private theorem firstDuplicateKey_none_of_nodup
    {table : List Lara.Admission.AdmissionRow}
    (h : (table.map (·.key)).Nodup) :
    Lara.Admission.firstDuplicateKey table = none := by
  unfold Lara.Admission.firstDuplicateKey
  have go :
      ∀ {keys seen :
          List (Presentation.LeafKind × Presentation.Provenance)},
        keys.Nodup → (∀ key ∈ keys, key ∉ seen) →
        Lara.Admission.firstDuplicateKeyAux keys seen = none := by
    intro keys
    induction keys with
    | nil => intro seen _ _; rfl
    | cons key rest ih =>
        intro seen hnodup hdisjoint
        have hkey : key ∉ seen := hdisjoint key (by simp)
        have hrestNodup := (List.nodup_cons.mp hnodup).2
        have hrestDisjoint : ∀ x ∈ rest, x ∉ key :: seen := by
          intro x hx hmem
          rcases List.mem_cons.mp hmem with rfl | hseen
          · exact (List.nodup_cons.mp hnodup).1 hx
          · exact hdisjoint x (by simp [hx]) hseen
        simp [Lara.Admission.firstDuplicateKeyAux, hkey,
          ih hrestNodup hrestDisjoint]
  exact go h (by simp)

private theorem firstAdmissionRejection_none
    {table : List Lara.Admission.AdmissionRow}
    {metas : List Lara.Admission.LeafMeta}
    (h : ∀ m ∈ metas,
      Lara.Admission.decisionFor table m.kind m.provenance ≠ .reject) :
    Lara.Admission.firstAdmissionRejection table metas = none := by
  induction metas with
  | nil => rfl
  | cons m rest ih =>
      have hhead := h m (by simp)
      have htail : ∀ entry ∈ rest,
          Lara.Admission.decisionFor table entry.kind entry.provenance ≠ .reject := by
        intro entry hentry
        exact h entry (by simp [hentry])
      simp only [Lara.Admission.firstAdmissionRejection,
        Lara.Admission.firstAdmissionRejection.go, if_neg hhead]
      simpa [Lara.Admission.firstAdmissionRejection] using ih htail

private theorem admissionArgs_filter_alignment
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

private theorem wrap_argId_vals (ids : List Presentation.ArgId) :
    (ids.map (·.val)).map (fun id => (⟨id⟩ : Presentation.ArgId)) = ids := by
  induction ids with
  | nil => rfl
  | cons id rest ih =>
      cases id
      simp [ih]

/-- The full pre-admission result. The `unit` is deliberately assembled before
`admission`; this field order mirrors the production data dependency. -/
structure DeclaredElaboration where
  semanticProgram : Presentation.Program
  pairs : List ReconstructedArgument
  rawAttacks : List Lara.RawAttack.RawAttack
  resolvedAttacks : List Lara.Attack.Attack
  unit : Lara.Unit
  admission : Lara.Admission.AdmissionResult

/-- The audit remains a separate typed result because the reviewed public
`Elaborated` carrier does not include diagnostics. -/
structure ElaboratedWithAudit (canon : String → String) where
  declared : DeclaredElaboration
  output : Elaborated canon

/-- Reconstructed rows selected by the exact keep predicate carried by the
accepted admission result. -/
def admissionKeptPairs (pairs : List ReconstructedArgument)
    (admission : Lara.Admission.AdmissionResult) : List ReconstructedArgument :=
  pairs.filter fun pair =>
    admission.prune.keep (pair.argument.id.val, pair.core)

/-- Construct the public carrier solely from the accepted evaluator result.
No pruning or attack resolution is repeated here. -/
def outputFromAdmission (input : Input) (semantic : Presentation.Program)
    (pairs : List ReconstructedArgument)
    (admission : Lara.Admission.AdmissionResult) : Elaborated canon :=
  let keptPairs := admissionKeptPairs pairs admission
  { gamma := Lara.Admission.buildGamma admission.prune.checkedLeaves
    ground :=
      admission.prune.checkedLeaves.map (·.2) ++
        requestedStatusAtoms semantic ++
        input.policy.theories.flatMap (·.2)
    unit :=
      { sigma := input.policy.sigma
        policy := toCorePolicy input.policy
        args := admission.prune.keptArgs.map (·.2)
        atts := admission.prune.keptAttacks }
    claims := claimsOf keptPairs semantic
    argIds := admission.prune.keptIds.map fun id => ⟨id⟩
    authoredObligations := authoredObligationsOf input.program
    openQuestions := openQuestionsOf keptPairs
    resolvedAttacks := admission.prune.keptAttacks
    semanticProgram := semantic }

/-- Package declared attack resolution behind a fixed result type so the D4
pipeline consumes one aligned carrier rather than reopening its proof. -/
def resolveAligned (args : List (String × Lara.Support.SupportTerm))
    (rawAttacks : List Lara.RawAttack.RawAttack)
    (hids : (args.map (·.1)).Nodup) :
    Except String (Lara.Admission.AlignedAttacks args rawAttacks) :=
  match hresolve : Lara.RawAttack.resolveAttacks args rawAttacks with
  | .error error => .error error
  | .ok resolved =>
      .ok
        { resolved := resolved
          resolve_eq := hresolve
          ids_nodup := hids }

/-- The one canonical D4 pipeline. It resolves every declared attack before
constructing the declared unit, then evaluates admission exactly once and
derives the retained output from that evaluator result. -/
def elaborateWithAudit (env : Env canon) (input : Input) :
    Except Error (ElaboratedWithAudit canon) := do
  elaborationPrologue input
  let valueExpanded ← expandValues input.policy input.program
  let (semantic, _) ← expandComparisons input.policy valueExpanded
  semanticIdentifierChecks input.policy input.program
  validateGroups semantic
  let pairs ← match reconstructArgs env semantic input.policy semantic.decls [] with
    | .error (.build id) => .error (.invalidInferredArgument id)
    | .error (.lower id) => .error (.invalidNamedCertificate id)
    | .error (.conclusionMismatch id claim) => .error (.conclusionMismatch id claim)
    | .error (.challengeTargetUndeclared id) =>
        .error (.challengeTargetUndeclared id)
    | .ok pairs => .ok pairs
  let surfaceAttacks := surfaceAttacksOf semantic
  let surfaceResolved ← match resolveSurfaceAttacks input.policy
      (pairs.map fun pair => (pair.argument.id, pair.core)) surfaceAttacks with
    | .error (source, target) => .error (.invalidSurfaceAttack source target)
    | .ok resolved => .ok resolved
  let rawAttacks ← match rawAttacksOfResolved surfaceAttacks surfaceResolved with
    | none =>
        let endpoints := (surfaceAttacks.head?.map attackEndpoints).getD
          (⟨""⟩, ⟨""⟩)
        .error (.invalidSurfaceAttack endpoints.1 endpoints.2)
    | some raw => .ok raw
  let _ ← resolveStatuses semantic
  let argsRaw := admissionArgs pairs
  if hids : (argsRaw.map (·.1)).Nodup then
    match resolveAligned argsRaw rawAttacks hids with
    | .error _ =>
        let endpoints := (surfaceAttacks.head?.map attackEndpoints).getD
          (⟨""⟩, ⟨""⟩)
        .error (.invalidSurfaceAttack endpoints.1 endpoints.2)
    | .ok aligned =>
        let declaredUnit : Lara.Unit :=
          { sigma := input.policy.sigma
            policy := toCorePolicy input.policy
            args := pairs.map (·.core)
            atts := aligned.resolved }
        match Lara.Admission.evaluateAdmission canon (admissionRows input.policy)
            (admissionLeafMetas semantic) (admissionLeafTable semantic) argsRaw
            rawAttacks (admissionGroups semantic) aligned with
        | .invalid (.duplicateAdmissionKey key) =>
            .error (.duplicateAdmissionKey key.1 key.2)
        | .invalid (.duplicateLeafId leaf) =>
            .error (.duplicateLeafId ⟨leaf.name⟩)
        | .invalid .metadataLeafMisalignment =>
            .error (.duplicateLeafId ⟨""⟩)
        | .rejected rejection =>
            .error (.admissionRejected ⟨rejection.leaf.name⟩)
        | .accepted admission =>
            .ok
              { declared :=
                  { semanticProgram := semantic
                    pairs := pairs
                    rawAttacks := rawAttacks
                    resolvedAttacks := aligned.resolved
                    unit := declaredUnit
                    admission := admission }
                output := outputFromAdmission input semantic pairs admission }
  else .error (.duplicateArgId ⟨""⟩)

/-- Pure lowering only. It intentionally does not call `checkUnit`,
`Surface.check`, or validate the entire `Supported` predicate. It omits core
signature and ground sorting, support typing, typed attack/conflict checking,
certificate-backend acceptance, replay identity, and parser/printing
validation. It does perform source guards, both expansions, identifier checks,
left-to-right argument and certificate lowering, declared attack resolution,
declared-unit construction, one admission evaluation, the policy/group prune,
and construction of the semantic provenance and diagnostic maps. -/
def elaborate (env : Env canon) (input : Input) : Except Error (Elaborated canon) :=
  (elaborateWithAudit env input).map (·.output)


/-! ### Executable renaming transport -/

namespace Renaming

noncomputable def renameElaborated (ρg : Binding.GlobalRenaming) (source : Input)
    (output : Elaborated canon) : Elaborated canon :=
  { gamma := renameGamma ρg output.gamma
    ground := output.ground.map (renameResidualAtom ρg)
    unit := renameCoreUnit ρg output.unit
    claims := output.claims.map fun claim => (ρg.prop claim.1, claim.2)
    argIds := output.argIds.map ρg.arg
    authoredObligations := output.authoredObligations.map fun entry =>
      (ρg.arg entry.1, entry.2.map ρg.obligation)
    openQuestions := output.openQuestions.map fun entry =>
      (ρg.arg entry.1, entry.2.map (renameCoreQuestionId ρg))
    resolvedAttacks := output.resolvedAttacks.map (renameCoreAttack ρg)
    semanticProgram := renameSemanticProgram ρg output.semanticProgram }

def renameDeclaredElaboration (ρg : Binding.GlobalRenaming)
    (source : Input) (declared : DeclaredElaboration) :
    DeclaredElaboration :=
  { semanticProgram := renameSemanticProgram ρg declared.semanticProgram
    pairs := declared.pairs.map
      (renameReconstructedArgument ρg (programValues source.program))
    rawAttacks := declared.rawAttacks.map (renameRawAttack ρg)
    resolvedAttacks := declared.resolvedAttacks.map (renameCoreAttack ρg)
    unit := renameCoreUnit ρg declared.unit
    admission := renameAdmissionResult ρg declared.admission }

noncomputable def renameElaboratedWithAudit (ρg : Binding.GlobalRenaming)
    (source : Input) (result : ElaboratedWithAudit canon) :
    ElaboratedWithAudit canon :=
  { declared := renameDeclaredElaboration ρg source result.declared
    output := renameElaborated ρg source result.output }


def renameLeafMeta (ρg : Binding.GlobalRenaming)
    (leafMeta : Lara.Admission.LeafMeta) : Lara.Admission.LeafMeta :=
  { leafMeta with id := renameCoreLeafId ρg leafMeta.id }

def renameDupGroup (ρg : Binding.GlobalRenaming)
    (group : Lara.Groups.DupGroup) : Lara.Groups.DupGroup :=
  { id := (ρg.group ⟨group.id⟩).val
    members := group.members.map (renameCoreLeafId ρg) }

private theorem rawAttackOfResolved_rename
    (surface : Presentation.SurfaceAttack) (resolved : Lara.Attack.Attack) :
    rawAttackOfResolved (Binding.renameSurfaceAttack ρg surface)
        (renameCoreAttack ρg resolved) =
      (rawAttackOfResolved surface resolved).map (renameRawAttack ρg) := by
  cases surface <;> cases resolved <;>
    simp [rawAttackOfResolved, Binding.renameSurfaceAttack,
      renameCoreAttack, renameRawAttack, Binding.renameText]

private theorem rawAttacksOfResolved_rename
    (surfaces : List Presentation.SurfaceAttack)
    (resolved : List Lara.Attack.Attack) :
    rawAttacksOfResolved (surfaces.map (Binding.renameSurfaceAttack ρg))
        (resolved.map (renameCoreAttack ρg)) =
      (rawAttacksOfResolved surfaces resolved).map
        (List.map (renameRawAttack ρg)) := by
  induction surfaces generalizing resolved with
  | nil =>
      cases resolved <;> rfl
  | cons surface rest ih =>
      cases resolved with
      | nil => rfl
      | cons head tail =>
          simp only [List.map_cons, rawAttacksOfResolved]
          rw [rawAttackOfResolved_rename, ih]
          cases rawAttackOfResolved surface head <;>
            cases rawAttacksOfResolved rest tail <;>
            simp

private theorem admissionArgs_rename
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
private theorem findDuplicate_map_injective
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
      · have renamedMember : rename value ∈ rest.map rename :=
          List.mem_map.mpr ⟨value, member, rfl⟩
        have sourceSome :
            (rest.find? fun candidate => decide (candidate = value)).isSome :=
          List.find?_isSome.mpr ⟨value, member, by simp⟩
        have renamedSome :
            ((rest.map rename).find? fun candidate =>
              decide (candidate = rename value)).isSome :=
          List.find?_isSome.mpr ⟨rename value, renamedMember, by simp⟩
        cases sourceEq :
            rest.find? (fun candidate => decide (candidate = value)) with
        | none =>
            simp [sourceEq] at sourceSome
        | some sourceFound =>
            cases renamedEq :
                (rest.map rename).find? (fun candidate =>
                  decide (candidate = rename value)) with
            | none =>
                simp [renamedEq] at renamedSome
            | some renamedFound =>
                simp [sourceEq, renamedEq]
      · have sourceNone :
            rest.find? (fun candidate => decide (candidate = value)) = none :=
          List.find?_eq_none.mpr (by
            intro candidate candidateMember
            intro predicateTrue
            have equal : candidate = value :=
              of_decide_eq_true predicateTrue
            subst candidate
            exact member candidateMember)
        have renamedNone :
            (rest.map rename).find? (fun candidate =>
              decide (candidate = rename value)) = none :=
          List.find?_eq_none.mpr (by
            intro candidate candidateMember
            intro predicateTrue
            obtain ⟨source, sourceMember, sourceEq⟩ :=
              List.mem_map.mp candidateMember
            subst candidate
            have renamedEqual : rename source = rename value :=
              of_decide_eq_true predicateTrue
            have sourceEqual := injective renamedEqual
            subst source
            exact member sourceMember)
        simp [sourceNone, renamedNone, ih]
private theorem find?_map_eq_map_find?
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

private theorem rawLookupArg_rename
    (args : List (String × Lara.Support.SupportTerm)) (id : String) :
    Lara.RawAttack.lookupArg
        (args.map fun entry =>
          ((ρg.arg ⟨entry.1⟩).val, renameCoreSupportTerm ρg entry.2))
        (ρg.arg ⟨id⟩).val =
      (Lara.RawAttack.lookupArg args id).map (renameCoreSupportTerm ρg) := by
  unfold Lara.RawAttack.lookupArg
  rw [find?_map_eq_map_find?
    (fun entry : String × Lara.Support.SupportTerm =>
      ((ρg.arg ⟨entry.1⟩).val, renameCoreSupportTerm ρg entry.2))
    (fun entry => entry.1 == id)
    (fun entry => entry.1 == (ρg.arg ⟨id⟩).val) args]
  · simp [Option.map_map, Function.comp_def]
  · intro entry
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro equal
      have typed :
          ρg.arg (⟨entry.1⟩ : Presentation.ArgId) =
            ρg.arg (⟨id⟩ : Presentation.ArgId) := by
        apply congrArg Presentation.ArgId.mk
        exact equal
      exact congrArg Presentation.ArgId.val (ρg.arg_injective typed)
    · intro equal
      subst id
      rfl

theorem rawResolveAttacks_rename
    (args : List (String × Lara.Support.SupportTerm))
    (raw : List Lara.RawAttack.RawAttack) :
    Lara.RawAttack.resolveAttacks
        (args.map fun entry =>
          ((ρg.arg ⟨entry.1⟩).val, renameCoreSupportTerm ρg entry.2))
        (raw.map (renameRawAttack ρg)) =
      renameExcept id (List.map (renameCoreAttack ρg))
        (Lara.RawAttack.resolveAttacks args raw) := by
  induction raw with
  | nil => rfl
  | cons attack rest ih =>
      cases attack with
      | rebut source target =>
          simp only [List.map_cons, renameRawAttack,
            Lara.RawAttack.resolveAttacks_rebut]
          rw [rawLookupArg_rename, rawLookupArg_rename]
          cases Lara.RawAttack.lookupArg args source with
          | none => simp [renameExcept]
          | some sourceTerm =>
            cases Lara.RawAttack.lookupArg args target with
            | none => simp [renameExcept]
            | some targetTerm =>
              simp only [Option.map_some]
              rw [ih]
              cases Lara.RawAttack.resolveAttacks args rest <;>
                simp [Except.bind, renameExcept, renameCoreAttack]
      | undercut source target position =>
          simp only [List.map_cons, renameRawAttack,
            Lara.RawAttack.resolveAttacks_undercut]
          rw [rawLookupArg_rename, rawLookupArg_rename]
          cases Lara.RawAttack.lookupArg args source with
          | none => simp [renameExcept]
          | some sourceTerm =>
            cases Lara.RawAttack.lookupArg args target with
            | none => simp [renameExcept]
            | some targetTerm =>
              simp only [Option.map_some]
              rw [ih]
              cases Lara.RawAttack.resolveAttacks args rest <;>
                simp [Except.bind, renameExcept, renameCoreAttack]
      | undermine source target position =>
          simp only [List.map_cons, renameRawAttack,
            Lara.RawAttack.resolveAttacks_undermine]
          rw [rawLookupArg_rename, rawLookupArg_rename]
          cases Lara.RawAttack.lookupArg args source with
          | none => simp [renameExcept]
          | some sourceTerm =>
            cases Lara.RawAttack.lookupArg args target with
            | none => simp [renameExcept]
            | some targetTerm =>
              simp only [Option.map_some]
              rw [ih]
              cases Lara.RawAttack.resolveAttacks args rest <;>
                simp [Except.bind, renameExcept, renameCoreAttack]

def renameAlignedAttacks (ρg : Binding.GlobalRenaming)
    {args : List (String × Lara.Support.SupportTerm)}
    {raw : List Lara.RawAttack.RawAttack}
    (aligned : Lara.Admission.AlignedAttacks args raw) :
    Lara.Admission.AlignedAttacks
      (args.map fun entry =>
        ((ρg.arg ⟨entry.1⟩).val, renameCoreSupportTerm ρg entry.2))
      (raw.map (renameRawAttack ρg)) :=
  { resolved := aligned.resolved.map (renameCoreAttack ρg)
    resolve_eq := by
      rw [rawResolveAttacks_rename, aligned.resolve_eq]
      rfl
    ids_nodup := by
      have stringInjective :
          Function.Injective (fun value : String => (ρg.arg ⟨value⟩).val) := by
        intro left right equal
        have typed :
            ρg.arg (⟨left⟩ : Presentation.ArgId) =
              ρg.arg (⟨right⟩ : Presentation.ArgId) := by
          apply congrArg Presentation.ArgId.mk
          exact equal
        exact congrArg Presentation.ArgId.val (ρg.arg_injective typed)
      simpa [List.map_map, Function.comp_def] using
        (nodup_map_iff_of_injective stringInjective).2 aligned.ids_nodup }

private theorem resolveAligned_error
    (args : List (String × Lara.Support.SupportTerm))
    (raw : List Lara.RawAttack.RawAttack)
    (hids : (args.map (·.1)).Nodup)
    (failure : String)
    (hresolve :
      Lara.RawAttack.resolveAttacks args raw = .error failure) :
    resolveAligned args raw hids = .error failure := by
  unfold resolveAligned
  split
  · rename_i error heq
    rw [hresolve] at heq
    cases heq
    rfl
  · rename_i resolved heq
    rw [hresolve] at heq
    contradiction

private theorem resolveAligned_ok
    (args : List (String × Lara.Support.SupportTerm))
    (raw : List Lara.RawAttack.RawAttack)
    (hids : (args.map (·.1)).Nodup)
    (resolved : List Lara.Attack.Attack)
    (hresolve :
      Lara.RawAttack.resolveAttacks args raw = .ok resolved) :
    resolveAligned args raw hids =
      .ok
        { resolved := resolved
          resolve_eq := hresolve
          ids_nodup := hids } := by
  unfold resolveAligned
  split
  · rename_i error heq
    rw [hresolve] at heq
    contradiction
  · rename_i targetResolved heq
    rw [hresolve] at heq
    cases heq
    rfl

theorem resolveAligned_rename
    (args : List (String × Lara.Support.SupportTerm))
    (raw : List Lara.RawAttack.RawAttack)
    (hids : (args.map (·.1)).Nodup)
    (renamedHids :
      ((args.map fun entry =>
        ((ρg.arg ⟨entry.1⟩).val, renameCoreSupportTerm ρg entry.2)).map
          (·.1)).Nodup) :
    resolveAligned
        (args.map fun entry =>
          ((ρg.arg ⟨entry.1⟩).val, renameCoreSupportTerm ρg entry.2))
        (raw.map (renameRawAttack ρg)) renamedHids =
      renameExcept id (renameAlignedAttacks ρg)
        (resolveAligned args raw hids) := by
  have transport := rawResolveAttacks_rename (ρg := ρg) args raw
  cases sourceResult : Lara.RawAttack.resolveAttacks args raw with
  | error sourceFailure =>
      rw [sourceResult] at transport
      simp only [renameExcept] at transport
      cases targetResult : Lara.RawAttack.resolveAttacks
          (args.map fun entry =>
            ((ρg.arg ⟨entry.1⟩).val, renameCoreSupportTerm ρg entry.2))
          (raw.map (renameRawAttack ρg)) with
      | error targetFailure =>
          rw [targetResult] at transport
          cases transport
          rw [resolveAligned_error args raw hids sourceFailure sourceResult]
          rw [resolveAligned_error _ _ renamedHids sourceFailure targetResult]
          rfl
      | ok targetResolved =>
          rw [targetResult] at transport
          contradiction
  | ok sourceResolved =>
      rw [sourceResult] at transport
      simp only [renameExcept] at transport
      cases targetResult : Lara.RawAttack.resolveAttacks
          (args.map fun entry =>
            ((ρg.arg ⟨entry.1⟩).val, renameCoreSupportTerm ρg entry.2))
          (raw.map (renameRawAttack ρg)) with
      | error targetFailure =>
          rw [targetResult] at transport
          contradiction
      | ok targetResolved =>
          rw [targetResult] at transport
          cases transport
          rw [resolveAligned_ok args raw hids sourceResolved sourceResult]
          rw [resolveAligned_ok _ _ renamedHids
            (sourceResolved.map (renameCoreAttack ρg)) targetResult]
          simp [renameExcept, renameAlignedAttacks]


private theorem elaborationPrologue_rename
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
      | cons label rest ih =>
          cases label <;> simp_all
    simp [canonicalPremiseLabelsForRuleB, Binding.renameRule, anyEq]
  have badFind :
      ((Binding.renamePolicy ρg policy).rules.find? fun rule =>
          !canonicalPremiseLabelsForRuleB rule).map (·.id) =
        ((policy.rules.find? fun rule =>
          !canonicalPremiseLabelsForRuleB rule).map (·.id)).map ρg.rule := by
    simp only [Binding.renamePolicy]
    rw [find?_map_eq_map_find? (Binding.renameRule ρg)
      (fun rule => !canonicalPremiseLabelsForRuleB rule)
      (fun rule => !canonicalPremiseLabelsForRuleB rule)
      policy.rules (by intro rule; rw [perRule])]
    cases policy.rules.find? (fun rule =>
      !canonicalPremiseLabelsForRuleB rule) <;>
      simp [Binding.renameRule]
  have leafDuplicate :
      findDuplicate (leafIds (Binding.renameProgram ρg program)) =
        (findDuplicate (leafIds program)).map ρg.leaf := by
    rw [leafIds_renameProgram]
    exact findDuplicate_map_injective ρg.leaf ρg.leaf_injective _
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
        cases bad :
            policy.rules.find? fun rule =>
              !canonicalPremiseLabelsForRuleB rule with
        | none =>
            simp [bad] at badSome
        | some rule =>
            simp [bad, Binding.renameProgram, Binding.renamePolicy,
              policyMatches, renameExcept, renameError]
    | true =>
        cases admissionDuplicate :
            findDuplicate (policy.admission.map Prod.fst) with
        | some key =>
            simp [admissionDuplicate, Binding.renameProgram,
              Binding.renamePolicy, policyMatches, renameExcept, renameError]
        | none =>
            cases leafDuplicateSource :
                findDuplicate (leafIds program) with
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

private theorem contains_arg_map (ρg : Binding.GlobalRenaming)
    (ids : List Presentation.ArgId) (id : Presentation.ArgId) :
    (ids.map ρg.arg).contains (ρg.arg id) = ids.contains id := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem]
  constructor
  · intro member
    obtain ⟨source, sourceMember, equal⟩ := List.mem_map.mp member
    exact (ρg.arg_injective equal).symm ▸ sourceMember
  · exact fun member => List.mem_map.mpr ⟨id, member, rfl⟩

private theorem attackEndpointDeclaredB_rename
    (ρg : Binding.GlobalRenaming) (values : List Presentation.ValueName)
    (ids : List Presentation.ArgId) (declaration : Presentation.Decl) :
    attackEndpointDeclaredB (ids.map ρg.arg)
        (Binding.renameDecl ρg values declaration) =
      attackEndpointDeclaredB ids declaration := by
  cases declaration with
  | attack attack =>
      cases attack <;>
        simp only [Binding.renameDecl, Binding.renameSurfaceAttack,
          attackEndpointDeclaredB, attackEndpoints]
      all_goals rw [contains_arg_map, contains_arg_map]
  | leaf leaf => rfl
  | claim claim => rfl
  | arg argument => rfl
  | status status => rfl
  | group group => rfl
  | comparison comparison => rfl

private theorem attackEndpointsDeclaredB_rename
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program) :
    attackEndpointsDeclaredB (Binding.renameProgram ρg program) =
      attackEndpointsDeclaredB program := by
  unfold attackEndpointsDeclaredB
  rw [argIds_renameProgram]
  change (program.decls.map
      (Binding.renameDecl ρg (programValues program))).all _ = _
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      simp only [List.map_cons, List.all_cons]
      rw [attackEndpointDeclaredB_rename, ih]

private theorem firstBadEndpointAttackIn?_rename
    (ρg : Binding.GlobalRenaming) (values : List Presentation.ValueName)
    (ids : List Presentation.ArgId) :
    ∀ declarations,
      firstBadEndpointAttackIn? (ids.map ρg.arg)
          (declarations.map (Binding.renameDecl ρg values)) =
        (firstBadEndpointAttackIn? ids declarations).map
          (Binding.renameSurfaceAttack ρg)
  | [] => rfl
  | declaration :: rest => by
      cases declaration with
      | attack attack =>
          simp only [List.map_cons, Binding.renameDecl,
            firstBadEndpointAttackIn?]
          have head := attackEndpointDeclaredB_rename ρg values ids
            (.attack attack)
          simp only [Binding.renameDecl] at head
          rw [head]
          by_cases valid : attackEndpointDeclaredB ids (.attack attack)
          · simp [valid,
              firstBadEndpointAttackIn?_rename ρg values ids rest]
          · simp [valid, Binding.renameSurfaceAttack]
      | leaf leaf =>
          simp [firstBadEndpointAttackIn?, Binding.renameDecl,
            firstBadEndpointAttackIn?_rename ρg values ids rest]
      | claim claim =>
          simp [firstBadEndpointAttackIn?, Binding.renameDecl,
            firstBadEndpointAttackIn?_rename ρg values ids rest]
      | arg argument =>
          simp [firstBadEndpointAttackIn?, Binding.renameDecl,
            firstBadEndpointAttackIn?_rename ρg values ids rest]
      | status status =>
          simp [firstBadEndpointAttackIn?, Binding.renameDecl,
            firstBadEndpointAttackIn?_rename ρg values ids rest]
      | group group =>
          simp [firstBadEndpointAttackIn?, Binding.renameDecl,
            firstBadEndpointAttackIn?_rename ρg values ids rest]
      | comparison comparison =>
          simp [firstBadEndpointAttackIn?, Binding.renameDecl,
            firstBadEndpointAttackIn?_rename ρg values ids rest]

private theorem firstBadEndpointAttack?_rename
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program) :
    firstBadEndpointAttack? (Binding.renameProgram ρg program) =
      (firstBadEndpointAttack? program).map
        (Binding.renameSurfaceAttack ρg) := by
  unfold firstBadEndpointAttack?
  rw [argIds_renameProgram]
  change firstBadEndpointAttackIn? _
      (program.decls.map (Binding.renameDecl ρg (programValues program))) = _
  exact firstBadEndpointAttackIn?_rename ρg (programValues program)
    (argIds program) program.decls

theorem validateAttackEndpoints_rename
    (sound : RenamingSound ρg program policy) :
    validateAttackEndpoints (Binding.renameProgram ρg program) =
      renameExcept (renameError ρg) id (validateAttackEndpoints program) := by
  have argSentinel : ρg.arg (⟨""⟩ : Presentation.ArgId) = ⟨""⟩ := by
    apply congrArg Presentation.ArgId.mk
    simpa using (ρg.arg_coherent ⟨""⟩).trans sound.empty
  unfold validateAttackEndpoints
  rw [attackEndpointsDeclaredB_rename, firstBadEndpointAttack?_rename]
  cases valid : attackEndpointsDeclaredB program with
  | true => simp [valid, renameExcept]
  | false =>
      cases bad : firstBadEndpointAttack? program with
      | none =>
          simp [valid, bad, renameExcept, renameError, argSentinel,
            Binding.renameSurfaceAttack, attackEndpoints]
      | some attack =>
          cases attack <;>
            simp [valid, bad, renameExcept, renameError,
              Binding.renameSurfaceAttack, attackEndpoints]

private theorem semanticIdentifierChecks_rename
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
    exact findDuplicate_map_injective ρg.arg ρg.arg_injective _
  have claimDuplicate :
      findDuplicate (claimIds (Binding.renameProgram ρg program)) =
        (findDuplicate (claimIds program)).map ρg.prop := by
    rw [claimIds_renameProgram]
    exact findDuplicate_map_injective ρg.prop ρg.prop_injective _
  unfold semanticIdentifierChecks
  rw [argDuplicate, claimDuplicate, ruleNamespacesWellFormedB_rename sound,
    validateAttackEndpoints_rename sound]
  cases findDuplicate (argIds program) <;>
    cases findDuplicate (claimIds program) <;>
    cases ruleNamespacesWellFormedB policy <;>
    simp [renameExcept, renameError, ruleSentinel]


end Renaming

/-! ### Successful-execution alignment -/

private theorem elaboration_bind_error_reduce {α β} (error : Error)
    (next : α → Except Error β) :
    (do let value ← (Except.error error : Except Error α); next value) =
      Except.error error := rfl

private theorem accepted_audit_eq
    {table : List Lara.Admission.AdmissionRow}
    {metas : List Lara.Admission.LeafMeta}
    {leaves : List (Lara.Support.LeafId × Lara.Atom)}
    {argsRaw : List (String × Lara.Support.SupportTerm)}
    {rawAttacks : List Lara.RawAttack.RawAttack}
    {groups : List Lara.Groups.DupGroup}
    {aligned : Lara.Admission.AlignedAttacks argsRaw rawAttacks}
    {admission : Lara.Admission.AdmissionResult}
    (haccepted :
      Lara.Admission.evaluateAdmission canon table metas leaves argsRaw rawAttacks
          groups aligned = .accepted admission) :
    admission.audit =
      Lara.Admission.buildAdmissionAudit canon table metas leaves argsRaw rawAttacks
        groups aligned.resolved := by
  cases hkey : Lara.Admission.firstDuplicateKey table with
  | some key =>
      simp [Lara.Admission.evaluateAdmission, hkey] at haccepted
  | none =>
      cases hleaf : Lara.Admission.firstDuplicateLeafId metas with
      | some leaf =>
          simp [Lara.Admission.evaluateAdmission, hkey, hleaf] at haccepted
      | none =>
          by_cases hmeta : Lara.Admission.metadataLeafAligned metas leaves
          · cases hrejection :
              Lara.Admission.firstAdmissionRejection table metas with
            | some rejection =>
                simp [Lara.Admission.evaluateAdmission, hkey, hleaf, hmeta,
                  hrejection] at haccepted
            | none =>
                simp [Lara.Admission.evaluateAdmission, hkey, hleaf, hmeta,
                  hrejection] at haccepted
                rw [← haccepted]
          · simp [Lara.Admission.evaluateAdmission, hkey, hleaf, hmeta] at haccepted

private theorem accepted_declaredResolved_eq
    {table : List Lara.Admission.AdmissionRow}
    {metas : List Lara.Admission.LeafMeta}
    {leaves : List (Lara.Support.LeafId × Lara.Atom)}
    {argsRaw : List (String × Lara.Support.SupportTerm)}
    {rawAttacks : List Lara.RawAttack.RawAttack}
    {groups : List Lara.Groups.DupGroup}
    {aligned : Lara.Admission.AlignedAttacks argsRaw rawAttacks}
    {admission : Lara.Admission.AdmissionResult}
    (haccepted :
      Lara.Admission.evaluateAdmission canon table metas leaves argsRaw rawAttacks
          groups aligned = .accepted admission) :
    admission.declaredResolved = aligned.resolved := by
  have hresolved := Lara.Admission.accepted_resolved_aligned
    canon table metas leaves argsRaw rawAttacks groups aligned haccepted
  rw [aligned.resolve_eq] at hresolved
  exact (Except.ok.inj hresolved).symm

/-- The complete correspondence carried by one successful canonical execution.
Every field is tied to the successful `elaborateWithAudit` call and the one
accepted admission result that call produced. -/
structure ElaborationAlignment (env : Env canon) (input : Input)
    (result : ElaboratedWithAudit canon) : Prop where
  groupsWellFormed : GroupsWellFormed result.declared.semanticProgram
  statusesWellFormed : StatusesWellFormed result.declared.semanticProgram
  reconstruction :
    reconstructArgs env result.declared.semanticProgram input.policy
        result.declared.semanticProgram.decls [] =
      .ok result.declared.pairs
  surfaceResolution :
    resolveSurfaceAttacks input.policy
        (result.declared.pairs.map fun pair => (pair.argument.id, pair.core))
        (surfaceAttacksOf result.declared.semanticProgram) =
      .ok result.declared.resolvedAttacks
  rawOrder :
    rawAttacksOfResolved (surfaceAttacksOf result.declared.semanticProgram)
        result.declared.resolvedAttacks =
      some result.declared.rawAttacks
  rawResolution :
    Lara.RawAttack.resolveAttacks (admissionArgs result.declared.pairs)
        result.declared.rawAttacks =
      .ok result.declared.resolvedAttacks
  idsNodup :
    ((admissionArgs result.declared.pairs).map (·.1)).Nodup
  admissionEvaluation :
    Lara.Admission.evaluateAdmission canon (admissionRows input.policy)
        (admissionLeafMetas result.declared.semanticProgram)
        (admissionLeafTable result.declared.semanticProgram)
        (admissionArgs result.declared.pairs) result.declared.rawAttacks
        (admissionGroups result.declared.semanticProgram)
        { resolved := result.declared.resolvedAttacks
          resolve_eq := rawResolution
          ids_nodup := idsNodup } =
      .accepted result.declared.admission
  declaredSigma : result.declared.unit.sigma = input.policy.sigma
  declaredPolicy :
    result.declared.unit.policy = toCorePolicy input.policy
  declaredArgs :
    result.declared.unit.args = result.declared.pairs.map (·.core)
  declaredAttacks :
    result.declared.unit.atts = result.declared.resolvedAttacks
  declaredUnit :
    result.declared.unit =
      { sigma := input.policy.sigma
        policy := toCorePolicy input.policy
        args := result.declared.pairs.map (·.core)
        atts := result.declared.resolvedAttacks }
  admissionDeclaredResolved :
    result.declared.admission.declaredResolved =
      result.declared.resolvedAttacks
  prune :
    result.declared.admission.prune =
      Lara.Admission.buildPrune canon (admissionRows input.policy)
        (admissionLeafMetas result.declared.semanticProgram)
        (admissionLeafTable result.declared.semanticProgram)
        (admissionArgs result.declared.pairs) result.declared.rawAttacks
        (admissionGroups result.declared.semanticProgram)
        result.declared.resolvedAttacks
  audit :
    result.declared.admission.audit =
      Lara.Admission.buildAdmissionAudit canon (admissionRows input.policy)
        (admissionLeafMetas result.declared.semanticProgram)
        (admissionLeafTable result.declared.semanticProgram)
        (admissionArgs result.declared.pairs) result.declared.rawAttacks
        (admissionGroups result.declared.semanticProgram)
        result.declared.resolvedAttacks
  keptIds :
    result.declared.admission.prune.keptIds =
      (Lara.Admission.buildPrune canon (admissionRows input.policy)
        (admissionLeafMetas result.declared.semanticProgram)
        (admissionLeafTable result.declared.semanticProgram)
        (admissionArgs result.declared.pairs) result.declared.rawAttacks
        (admissionGroups result.declared.semanticProgram)
        result.declared.resolvedAttacks).keptIds
  keptArgs :
    result.declared.admission.prune.keptArgs =
      (Lara.Admission.buildPrune canon (admissionRows input.policy)
        (admissionLeafMetas result.declared.semanticProgram)
        (admissionLeafTable result.declared.semanticProgram)
        (admissionArgs result.declared.pairs) result.declared.rawAttacks
        (admissionGroups result.declared.semanticProgram)
        result.declared.resolvedAttacks).keptArgs
  keptAttacks :
    result.declared.admission.prune.keptAttacks =
      (Lara.Admission.buildPrune canon (admissionRows input.policy)
        (admissionLeafMetas result.declared.semanticProgram)
        (admissionLeafTable result.declared.semanticProgram)
        (admissionArgs result.declared.pairs) result.declared.rawAttacks
        (admissionGroups result.declared.semanticProgram)
        result.declared.resolvedAttacks).keptAttacks
  checkedLeaves :
    result.declared.admission.prune.checkedLeaves =
      (Lara.Admission.buildPrune canon (admissionRows input.policy)
        (admissionLeafMetas result.declared.semanticProgram)
        (admissionLeafTable result.declared.semanticProgram)
        (admissionArgs result.declared.pairs) result.declared.rawAttacks
        (admissionGroups result.declared.semanticProgram)
        result.declared.resolvedAttacks).checkedLeaves
  outputGamma :
    result.output.gamma =
      Lara.Admission.buildGamma result.declared.admission.prune.checkedLeaves
  outputGround :
    result.output.ground =
      result.declared.admission.prune.checkedLeaves.map (·.2) ++
        requestedStatusAtoms result.declared.semanticProgram ++
        input.policy.theories.flatMap (·.2)
  outputUnit :
    result.output.unit =
      { sigma := input.policy.sigma
        policy := toCorePolicy input.policy
        args := result.declared.admission.prune.keptArgs.map (·.2)
        atts := result.declared.admission.prune.keptAttacks }
  outputArgIds :
    result.output.argIds =
      result.declared.admission.prune.keptIds.map fun id => ⟨id⟩
  outputClaims :
    result.output.claims =
      claimsOf
        (admissionKeptPairs result.declared.pairs result.declared.admission)
        result.declared.semanticProgram
  outputAuthoredObligations :
    result.output.authoredObligations = authoredObligationsOf input.program
  outputOpenQuestions :
    result.output.openQuestions =
      openQuestionsOf
        (admissionKeptPairs result.declared.pairs result.declared.admission)
  outputResolvedAttacks :
    result.output.resolvedAttacks =
      result.declared.admission.prune.keptAttacks
  outputSemanticProgram :
    result.output.semanticProgram = result.declared.semanticProgram
  retainedOutput :
    result.output =
      outputFromAdmission input result.declared.semanticProgram
        result.declared.pairs result.declared.admission

/-- A successful canonical run exposes its complete declared/admission/retained
alignment contract. -/
theorem elaborateWithAudit_alignment {env : Env canon} {input : Input}
    {result : ElaboratedWithAudit canon}
    (hsuccess : elaborateWithAudit env input = .ok result) :
    ElaborationAlignment env input result := by
  unfold elaborateWithAudit at hsuccess
  cases hprologue : elaborationPrologue input with
  | error error =>
      rw [hprologue] at hsuccess
      simp only [elaboration_bind_error_reduce] at hsuccess
      cases hsuccess
  | ok ignored =>
      rw [hprologue] at hsuccess
      simp only [bind_ok_reduce] at hsuccess
      cases hvalues : expandValues input.policy input.program with
      | error error =>
          rw [hvalues] at hsuccess
          simp only [elaboration_bind_error_reduce] at hsuccess
          cases hsuccess
      | ok valueExpanded =>
          rw [hvalues] at hsuccess
          simp only [bind_ok_reduce] at hsuccess
          cases hcomparisons :
              expandComparisons input.policy valueExpanded with
          | error error =>
              rw [hcomparisons] at hsuccess
              simp only [elaboration_bind_error_reduce] at hsuccess
              cases hsuccess
          | ok comparisonResult =>
              rcases comparisonResult with ⟨semantic, generated⟩
              rw [hcomparisons] at hsuccess
              simp only [bind_ok_reduce] at hsuccess
              cases hsemantic :
                  semanticIdentifierChecks input.policy input.program with
              | error error =>
                  rw [hsemantic] at hsuccess
                  simp only [elaboration_bind_error_reduce] at hsuccess
                  cases hsuccess
              | ok ignored =>
                  rw [hsemantic] at hsuccess
                  simp only [bind_ok_reduce] at hsuccess
                  cases hgroups : validateGroups semantic with
                  | error error =>
                      rw [hgroups] at hsuccess
                      simp only [elaboration_bind_error_reduce] at hsuccess
                      cases hsuccess
                  | ok ignoredGroups =>
                    rw [hgroups] at hsuccess
                    simp only [bind_ok_reduce] at hsuccess
                    cases hreconstruct :
                        reconstructArgs env semantic input.policy semantic.decls [] with
                    | error error =>
                        cases error <;>
                          rw [hreconstruct] at hsuccess <;>
                          simp only [elaboration_bind_error_reduce] at hsuccess <;>
                          cases hsuccess
                    | ok pairs =>
                        rw [hreconstruct] at hsuccess
                        simp only [bind_ok_reduce] at hsuccess
                        cases hsurface :
                            resolveSurfaceAttacks input.policy
                              (pairs.map fun pair =>
                                (pair.argument.id, pair.core))
                              (surfaceAttacksOf semantic) with
                        | error endpoints =>
                            rcases endpoints with ⟨source, target⟩
                            rw [hsurface] at hsuccess
                            simp only [elaboration_bind_error_reduce] at hsuccess
                            cases hsuccess
                        | ok surfaceResolved =>
                            rw [hsurface] at hsuccess
                            simp only [bind_ok_reduce] at hsuccess
                            cases hraw :
                                rawAttacksOfResolved
                                  (surfaceAttacksOf semantic) surfaceResolved with
                            | none =>
                                rw [hraw] at hsuccess
                                simp only [elaboration_bind_error_reduce] at hsuccess
                                cases hsuccess
                            | some rawAttacks =>
                                rw [hraw] at hsuccess
                                simp only [bind_ok_reduce] at hsuccess
                                cases hstatuses : resolveStatuses semantic with
                                | error error =>
                                    rw [hstatuses] at hsuccess
                                    simp only [elaboration_bind_error_reduce] at hsuccess
                                    cases hsuccess
                                | ok statusAtoms =>
                                  rw [hstatuses] at hsuccess
                                  simp only [bind_ok_reduce] at hsuccess
                                  by_cases hids :
                                      ((admissionArgs pairs).map (·.1)).Nodup
                                  · rw [dif_pos hids] at hsuccess
                                    cases haligned :
                                        resolveAligned (admissionArgs pairs)
                                          rawAttacks hids with
                                    | error error =>
                                        rw [haligned] at hsuccess
                                        simp only at hsuccess
                                        cases hsuccess
                                    | ok aligned =>
                                        rw [haligned] at hsuccess
                                        simp only at hsuccess
                                        cases hadmission :
                                            Lara.Admission.evaluateAdmission canon
                                              (admissionRows input.policy)
                                              (admissionLeafMetas semantic)
                                              (admissionLeafTable semantic)
                                              (admissionArgs pairs) rawAttacks
                                              (admissionGroups semantic) aligned with
                                        | invalid invalid =>
                                            cases invalid <;>
                                              rw [hadmission] at hsuccess <;>
                                              simp only at hsuccess <;>
                                              cases hsuccess
                                        | rejected rejection =>
                                            rw [hadmission] at hsuccess
                                            simp only at hsuccess
                                            cases hsuccess
                                        | accepted admission =>
                                            rw [hadmission] at hsuccess
                                            simp only [Except.ok.injEq] at hsuccess
                                            subst result
                                            have hprune :=
                                              Lara.Admission.accepted_prune_eq canon
                                                (admissionRows input.policy)
                                                (admissionLeafMetas semantic)
                                                (admissionLeafTable semantic)
                                                (admissionArgs pairs) rawAttacks
                                                (admissionGroups semantic) aligned
                                                hadmission
                                            have haudit :=
                                              accepted_audit_eq hadmission
                                            have hdeclared :=
                                              accepted_declaredResolved_eq hadmission
                                            have hpairIds :
                                                ((pairs.map fun pair =>
                                                  (pair.argument.id, pair.core)).map
                                                    fun row => row.1.val).Nodup := by
                                              simpa [admissionArgs, List.map_map,
                                                Function.comp_def] using hids
                                            obtain ⟨rawAligned, hrawAligned,
                                                hrawResolve⟩ :=
                                              checksAttacks_raw_alignment hpairIds
                                                (resolveSurfaceAttacks_sound
                                                  input.policy hsurface)
                                            have hrawAlignedEq :
                                                rawAligned = rawAttacks := by
                                              rw [hraw] at hrawAligned
                                              exact (Option.some.inj hrawAligned).symm
                                            subst rawAligned
                                            have hrawResolve' :
                                                Lara.RawAttack.resolveAttacks
                                                    (admissionArgs pairs) rawAttacks =
                                                  .ok surfaceResolved := by
                                              simpa [admissionArgs, List.map_map,
                                                Function.comp_def] using hrawResolve
                                            have hresolved :
                                                surfaceResolved = aligned.resolved := by
                                              rw [aligned.resolve_eq] at hrawResolve'
                                              exact (Except.ok.inj hrawResolve').symm
                                            refine
                                              { groupsWellFormed :=
                                                  validateGroups_sound (by
                                                    simpa using hgroups)
                                                statusesWellFormed :=
                                                  (resolveStatuses_sound hstatuses).1
                                                reconstruction := hreconstruct
                                                surfaceResolution := by
                                                  simpa [hresolved] using hsurface
                                                rawOrder := by
                                                  simpa [hresolved] using hraw
                                                rawResolution := aligned.resolve_eq
                                                idsNodup := hids
                                                admissionEvaluation := by
                                                  simpa using hadmission
                                                declaredSigma := rfl
                                                declaredPolicy := rfl
                                                declaredArgs := rfl
                                                declaredAttacks := rfl
                                                declaredUnit := rfl
                                                admissionDeclaredResolved := hdeclared
                                                prune := ?_
                                                audit := ?_
                                                keptIds := ?_
                                                keptArgs := ?_
                                                keptAttacks := ?_
                                                checkedLeaves := ?_
                                                outputGamma := rfl
                                                outputGround := rfl
                                                outputUnit := rfl
                                                outputArgIds := rfl
                                                outputClaims := rfl
                                                outputAuthoredObligations := rfl
                                                outputOpenQuestions := rfl
                                                outputResolvedAttacks := rfl
                                                outputSemanticProgram := rfl
                                                retainedOutput := rfl }
                                            · simpa using hprune
                                            · simpa using haudit
                                            · exact congrArg
                                                Lara.Admission.AdmissionPrune.keptIds
                                                hprune
                                            · exact congrArg
                                                Lara.Admission.AdmissionPrune.keptArgs
                                                hprune
                                            · exact congrArg
                                                Lara.Admission.AdmissionPrune.keptAttacks
                                                hprune
                                            · exact congrArg
                                                Lara.Admission.AdmissionPrune.checkedLeaves
                                                hprune
                                  · rw [dif_neg hids] at hsuccess
                                    cases hsuccess
/-- Adjacent boundary: semantic reconstruction feeds the declared attack pass. -/
theorem elaborateWithAudit_reconstruction_boundary
    {env : Env canon} {input : Input} {result : ElaboratedWithAudit canon}
    (hsuccess : elaborateWithAudit env input = .ok result) :
    reconstructArgs env result.declared.semanticProgram input.policy
        result.declared.semanticProgram.decls [] =
      .ok result.declared.pairs :=
  (elaborateWithAudit_alignment hsuccess).reconstruction

/-- Adjacent boundary: declared surface attacks preserve order through raw and
semantic resolution. -/
theorem elaborateWithAudit_attack_boundary
    {env : Env canon} {input : Input} {result : ElaboratedWithAudit canon}
    (hsuccess : elaborateWithAudit env input = .ok result) :
    resolveSurfaceAttacks input.policy
        (result.declared.pairs.map fun pair => (pair.argument.id, pair.core))
        (surfaceAttacksOf result.declared.semanticProgram) =
        .ok result.declared.resolvedAttacks ∧
      rawAttacksOfResolved (surfaceAttacksOf result.declared.semanticProgram)
          result.declared.resolvedAttacks =
        some result.declared.rawAttacks ∧
      Lara.RawAttack.resolveAttacks (admissionArgs result.declared.pairs)
          result.declared.rawAttacks =
        .ok result.declared.resolvedAttacks := by
  have h := elaborateWithAudit_alignment hsuccess
  exact ⟨h.surfaceResolution, h.rawOrder, h.rawResolution⟩

/-- Adjacent boundary: declared resolution constructs the exact declared unit. -/
theorem elaborateWithAudit_unit_boundary
    {env : Env canon} {input : Input} {result : ElaboratedWithAudit canon}
    (hsuccess : elaborateWithAudit env input = .ok result) :
    result.declared.unit =
      { sigma := input.policy.sigma
        policy := toCorePolicy input.policy
        args := result.declared.pairs.map (·.core)
        atts := result.declared.resolvedAttacks } :=
  (elaborateWithAudit_alignment hsuccess).declaredUnit

/-- Adjacent boundary: the declared unit's aligned attacks feed the one
accepted admission evaluation. -/
theorem elaborateWithAudit_admission_boundary
    {env : Env canon} {input : Input} {result : ElaboratedWithAudit canon}
    (hsuccess : elaborateWithAudit env input = .ok result) :
    ∃ aligned : Lara.Admission.AlignedAttacks
        (admissionArgs result.declared.pairs) result.declared.rawAttacks,
      aligned.resolved = result.declared.resolvedAttacks ∧
      Lara.Admission.evaluateAdmission canon (admissionRows input.policy)
          (admissionLeafMetas result.declared.semanticProgram)
          (admissionLeafTable result.declared.semanticProgram)
          (admissionArgs result.declared.pairs) result.declared.rawAttacks
          (admissionGroups result.declared.semanticProgram) aligned =
        .accepted result.declared.admission := by
  have h := elaborateWithAudit_alignment hsuccess
  let aligned : Lara.Admission.AlignedAttacks
      (admissionArgs result.declared.pairs) result.declared.rawAttacks :=
    { resolved := result.declared.resolvedAttacks
      resolve_eq := h.rawResolution
      ids_nodup := h.idsNodup }
  exact ⟨aligned, rfl, h.admissionEvaluation⟩

/-- Adjacent boundary: the accepted admission result is the sole source of the
retained public output. -/
theorem elaborateWithAudit_output_boundary
    {env : Env canon} {input : Input} {result : ElaboratedWithAudit canon}
    (hsuccess : elaborateWithAudit env input = .ok result) :
    result.output =
      outputFromAdmission input result.declared.semanticProgram
        result.declared.pairs result.declared.admission :=
  (elaborateWithAudit_alignment hsuccess).retainedOutput

/-! ### Argument and certificate laws -/

/-- Reconstruction records the conclusion of exactly the rebuilt term. The
certificate premise keeps the theorem on the actual per-argument production
fold rather than a second reconstruction model. -/
theorem reconstructArgument_preserves_conclusion
    (env : Env canon) (program : Presentation.Program)
    (policy : Presentation.Policy) (priors : List PriorArgument)
    (argument : Presentation.Arg) (built : PriorArgument)
    (core : Lara.Support.SupportTerm)
    (hbuild : reconstructArgument canon program policy priors argument = some built)
    (hlower : lowerToSupportTerm env program policy priors built.term = some core) :
    conclOfTerm program policy built.term = some built.conclusion := by
  have hconclusion := reconstructArgument_conclusion_sound hbuild
  exact conclOfTerm_complete hconclusion

/-- Certificate lowering preserves the reconstructed root obligation list
exactly, modulo the sole presentation-to-core question-id conversion. -/
theorem reconstructArgument_preserves_obligations
    (env : Env canon) (program : Presentation.Program)
    (policy : Presentation.Policy) (priors : List PriorArgument)
    (argument : Presentation.Arg) (built : PriorArgument)
    (core : Lara.Support.SupportTerm)
    (hbuild : reconstructArgument canon program policy priors argument = some built)
    (hlower : lowerToSupportTerm env program policy priors built.term = some core) :
    rootHoles core = (rootAuthoredHoles built.term).map toSupportObligationId := by
  have hcertificate := lowerToSupportTerm_sound env hlower
  generalize hterm : built.term = term at hcertificate ⊢
  cases hcertificate <;> rfl

/-- Successful assurance lowering constructs the independent assurance
judgment. -/
theorem lowerCertificate_sound (env : Env canon) (program : Presentation.Program)
    (rule : Presentation.Rule) (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm) (authored : Presentation.Assurance)
    (core : Lara.Support.Assurance)
    (h : lowerAssuranceCertificate env program rule priors premises authored = some core) :
    ChecksAssurance env program rule priors premises authored core := by
  cases authored with
  | none => simp [lowerAssuranceCertificate] at h; cases h; exact .none
  | trusted => simp [lowerAssuranceCertificate] at h; cases h; exact .trusted
  | cert certificate => exact .cert h

/-- Both certificate lowering branches are identity on canonical kernel data. -/
theorem lowerCertificate_kernel_identity
    (startsIdent : String → Bool) (resolver : String → Option Nat)
    (encodeProp : String → Option String) (nPrem : Nat)
    (hNat : ∀ n, startsIdent (Nat.repr n) = false)
    (cert : Lara.ND.Cert) (binders : List (Option String))
    (backend : String) (version : Nat) (payload : Lara.Support.SExpr)
    (hslots : Lara.CertSlots.NoSymbolicRef backend version payload) :
    Lara.NDNamed.lowerNamed startsIdent resolver encodeProp nPrem binders
        (Lara.NDNamed.encodeCert cert) = some (Lara.NDNamed.encodeCert cert) ∧
      Lara.CertSlots.lowerPayload sourceStartsIdentifier resolver backend version payload =
        some payload := by
  exact ⟨Lara.NDNamed.lowerNamed_id_of_kernel startsIdent resolver encodeProp nPrem hNat
      cert binders,
    Lara.CertSlots.lower_id_of_no_symbolic sourceStartsIdentifier resolver backend version
      payload hslots⟩

/-- Named-certificate lowering is invariant under genuine binder alpha-renaming. -/
theorem lowerCertificate_alpha_invariant
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
  Lara.NDNamed.lowerNamed_eq_of_alpha startsIdent resolver encodeProp nPrem hNat
    leftWF rightWF halpha

/-! ### Attack, admission, and pass alignment -/

/-- Successful ordered resolution preserves the number of authored attacks. -/
theorem resolveSurfaceAttacks_order_alignment (policy : Presentation.Policy)
    (args : List (Presentation.ArgId × Lara.Support.SupportTerm)) :
    ∀ {attacks resolved}, resolveSurfaceAttacks policy args attacks = .ok resolved →
      attacks.length = resolved.length := by
  intro attacks resolved h
  induction attacks generalizing resolved with
  | nil => simp [resolveSurfaceAttacks] at h; cases h; rfl
  | cons attack rest ih =>
      simp only [resolveSurfaceAttacks] at h
      cases hhead : resolveSurfaceAttack policy args attack with
      | none => simp [hhead] at h
      | some head =>
          cases hrest : resolveSurfaceAttacks policy args rest with
          | error failure => simp [hhead, hrest] at h
          | ok tail =>
              simp [hhead, hrest] at h
              cases h
              simp [ih hrest]

/-- A successful endpoint lookup witnesses membership in the authored argument
table. -/
private theorem findArgTerm_id_mem
    {args : List (Presentation.ArgId × Lara.Support.SupportTerm)}
    {id : Presentation.ArgId} {term : Lara.Support.SupportTerm}
    (h : findArgTerm args id = some term) : id ∈ args.map (·.1) := by
  unfold findArgTerm at h
  obtain ⟨row, hfind, _⟩ := Option.map_eq_some_iff.mp h
  refine List.mem_map.mpr ⟨row, List.mem_of_find?_eq_some hfind, ?_⟩
  have hp : decide (row.1 = id) = true :=
    List.find?_some
      (p := fun entry : Presentation.ArgId × Lara.Support.SupportTerm =>
        decide (entry.1 = id)) hfind
  exact of_decide_eq_true hp

private theorem checksAttack_endpoint_membership
    {policy : Presentation.Policy}
    {args : List (Presentation.ArgId × Lara.Support.SupportTerm)}
    {attack : Presentation.SurfaceAttack} {resolved : Lara.Attack.Attack}
    (h : ChecksAttack policy args attack resolved) :
    (attackEndpoints attack).1 ∈ args.map (·.1) ∧
      (attackEndpoints attack).2 ∈ args.map (·.1) := by
  cases h <;> constructor <;> apply findArgTerm_id_mem <;> assumption

/-- Every successfully resolved surface attack looked up both authored endpoint
ids in the declaration-ordered argument table. -/
theorem resolveSurfaceAttacks_endpoint_membership (policy : Presentation.Policy)
    (args : List (Presentation.ArgId × Lara.Support.SupportTerm))
    {attacks resolved}
    (h : resolveSurfaceAttacks policy args attacks = .ok resolved) :
    ∀ attack ∈ attacks,
      (attackEndpoints attack).1 ∈ args.map (·.1) ∧
        (attackEndpoints attack).2 ∈ args.map (·.1) := by
  have hchecks := resolveSurfaceAttacks_sound policy h
  induction hchecks with
  | nil => simp
  | cons head tail ih =>
      intro attack hmem
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact checksAttack_endpoint_membership head
      · exact ih (resolveSurfaceAttacks_complete tail) attack htail

/-- The accepted evaluator result is the sole source of every retained carrier
component. This records the exact argument, attack, checker-context, claim, and
obligation alignments consumed downstream. -/
theorem outputFromAdmission_alignment (input : Input)
    (semantic : Presentation.Program) (pairs : List ReconstructedArgument)
    (admission : Lara.Admission.AdmissionResult) :
    let output := outputFromAdmission (canon := canon) input semantic pairs admission
    output.argIds = admission.prune.keptIds.map (fun id => ⟨id⟩) ∧
    output.unit.args = admission.prune.keptArgs.map (·.2) ∧
    output.unit.atts = admission.prune.keptAttacks ∧
    output.resolvedAttacks = admission.prune.keptAttacks ∧
    output.gamma = Lara.Admission.buildGamma admission.prune.checkedLeaves ∧
    output.claims = claimsOf (admissionKeptPairs pairs admission) semantic ∧
    output.openQuestions = openQuestionsOf (admissionKeptPairs pairs admission) ∧
    output.authoredObligations = authoredObligationsOf input.program := by
  simp [outputFromAdmission]

/-- The declared unit is constructed at the boundary immediately before
admission and carries the evaluator's exact resolved attack sequence. -/
def DeclaredAdmissionOutputAligned (input : Input)
    (result : ElaboratedWithAudit canon) : Prop :=
  result.declared.admission.declaredResolved = result.declared.resolvedAttacks ∧
  result.output.argIds =
    result.declared.admission.prune.keptIds.map (fun id => ⟨id⟩) ∧
  result.output.unit.args = result.declared.admission.prune.keptArgs.map (·.2) ∧
  result.output.unit.atts = result.declared.admission.prune.keptAttacks ∧
  result.output.resolvedAttacks = result.declared.admission.prune.keptAttacks ∧
  result.output.gamma =
    Lara.Admission.buildGamma result.declared.admission.prune.checkedLeaves ∧
  result.output.claims =
    claimsOf (admissionKeptPairs result.declared.pairs result.declared.admission)
      result.declared.semanticProgram ∧
  result.output.openQuestions =
    openQuestionsOf
      (admissionKeptPairs result.declared.pairs result.declared.admission) ∧
  result.output.authoredObligations = authoredObligationsOf input.program

/-- The adjacent expansion boundary is exactly the verified value pass. -/
theorem value_pass_complete {env : Env canon} {input : Input}
    {output : Elaborated canon} (h : Checks env input output) :
    ∃ mid, expandValues input.policy input.program = .ok mid := by
  rcases h.expansions with ⟨mid, target, generated, hvalues, rest⟩
  exact ⟨mid, expandValues_complete input.policy h.supported.value_bindings_wf hvalues⟩

/-- The adjacent comparison boundary is exactly the verified shallow pass. -/
theorem comparison_pass_complete {env : Env canon} {input : Input}
    {output : Elaborated canon} (h : Checks env input output) :
    ∃ mid generated,
      expandValues input.policy input.program = .ok mid ∧
        expandComparisons input.policy mid = .ok (output.semanticProgram, generated) := by
  rcases h.expansions with
    ⟨mid, target, generated, hvalues, hfresh, hkeys, hcomparisons, rfl⟩
  exact ⟨mid, generated,
    expandValues_complete input.policy h.supported.value_bindings_wf hvalues,
    expandComparisons_complete_independent input.policy hfresh hkeys hcomparisons⟩

/-- Independent derivations reconstruct the exact production lowering. The
proof uses no core checker call: the `Checks.core` field is intentionally not
referenced. -/
theorem elaborate_complete (env : Env canon) (input : Input) (output : Elaborated canon)
    (h : Checks env input output) : elaborate env input = .ok output := by
  have hprologue := elaborationPrologue_complete h
  rcases h.expansions with
    ⟨mid, target, generated, hvalues, hmidFresh, hkeys, hcomparisons, htarget⟩
  have hvalues' := expandValues_complete input.policy h.supported.value_bindings_wf hvalues
  have hcomparisons' := expandComparisons_complete_independent input.policy
    hmidFresh hkeys hcomparisons
  subst target
  rcases h.program with
    ⟨pairs, declaredResolved, hprogram, hpairIds, hdeclaredRelation,
      hselected, hids, hargs, hclaims, hquestions⟩
  have hfold := reconstructArgs_complete hprogram
  have hsurface := resolveSurfaceAttacks_complete hdeclaredRelation
  have hpairRows :
      ((pairs.map fun pair => (pair.argument.id, pair.core)).map
        fun row => row.1.val).Nodup := by
    simpa [List.map_map, Function.comp_def] using hpairIds
  obtain ⟨rawAttacks, hrawAttacks, hrawResolve⟩ :=
    checksAttacks_raw_alignment hpairRows hdeclaredRelation
  have hrawSelected :=
    checksAttacks_raw_selection_alignment hdeclaredRelation hrawAttacks
      ((keptReconstructed canon input.policy output.semanticProgram pairs).map
        (·.argument.id))
  let keepArgument : String × Lara.Support.SupportTerm → Bool :=
    fun row =>
      !Lara.Groups.usesLeaf
        (Lara.Admission.policyQuarantineSeed (admissionRows input.policy)
            (admissionLeafMetas output.semanticProgram) ++
          Lara.Groups.quarantined canon
            (admissionLeafTable output.semanticProgram)
            (admissionGroups output.semanticProgram))
        row.2
  have hkeptRows := admissionArgs_filter_alignment pairs keepArgument
  have hkeptRawIds :
      ((keptReconstructed canon input.policy output.semanticProgram pairs).map
          (·.argument.id)).map (·.val) =
        ((admissionArgs pairs).filter keepArgument).map (·.1) := by
    have hmapped := congrArg (List.map Prod.fst) hkeptRows
    simpa [keepArgument, keptReconstructed, List.map_map,
      Function.comp_def] using hmapped.symm
  have hkeptRawArgs :
      ((admissionArgs pairs).filter keepArgument).map (·.2) =
        (keptReconstructed canon input.policy output.semanticProgram pairs).map
          (·.core) := by
    have hmapped := congrArg (List.map Prod.snd) hkeptRows
    simpa [keepArgument, keptReconstructed, List.map_map,
      Function.comp_def] using hmapped
  have hselectedRaw :
      Lara.RawAttack.selectAligned
          (fun attack =>
            decide
                (attack.endpoints.1 ∈
                  ((admissionArgs pairs).filter keepArgument).map (·.1)) &&
              decide
                (attack.endpoints.2 ∈
                  ((admissionArgs pairs).filter keepArgument).map (·.1)))
          rawAttacks declaredResolved =
        output.resolvedAttacks := by
    rw [← hkeptRawIds, ← hrawSelected]
    exact hselected
  have hsemantic := semanticIdentifierChecks_complete h
  have hmetaEq := expansions_admissionLeafMetas hvalues hcomparisons
  have hkeyNodup : ((admissionRows input.policy).map (·.key)).Nodup := by
    simpa [admissionRows, List.map_map, Function.comp_def] using h.admission.1
  have hkeyNone := firstDuplicateKey_none_of_nodup hkeyNodup
  rcases h.supported.declaration_ids_nodup with
    ⟨⟨⟨hleafIds, _⟩, _⟩, _⟩
  have hsourceMetaIds := admissionLeafMetas_ids_nodup input.program hleafIds
  have hsemanticMetaIds :
      ((admissionLeafMetas output.semanticProgram).map (·.id)).Nodup := by
    rw [← hmetaEq]
    exact hsourceMetaIds
  have hleafNone :=
    (Lara.Admission.firstDuplicateLeafId_none_iff_nodup
      (admissionLeafMetas output.semanticProgram)).2 hsemanticMetaIds
  have haligned := admission_metadata_aligned output.semanticProgram
  have hrejection :
      Lara.Admission.firstAdmissionRejection (admissionRows input.policy)
        (admissionLeafMetas output.semanticProgram) = none := by
    apply firstAdmissionRejection_none
    intro leafMeta hmem
    have hmemSource : leafMeta ∈ admissionLeafMetas input.program := by
      rw [hmetaEq]
      exact hmem
    unfold admissionLeafMetas at hmemSource
    obtain ⟨leaf, hleafmem, hleaf⟩ := List.mem_map.mp hmemSource
    subst leafMeta
    rw [decisionFor_admissionRows]
    exact h.admission.2 leaf hleafmem
  have hrawResolve' :
      Lara.RawAttack.resolveAttacks (admissionArgs pairs) rawAttacks =
        .ok declaredResolved := by
    simpa [admissionArgs, List.map_map, Function.comp_def] using hrawResolve
  have hpairIds' : ((admissionArgs pairs).map (·.1)).Nodup := by
    simpa [admissionArgs, List.map_map, Function.comp_def] using hpairIds
  let aligned :
      Lara.Admission.AlignedAttacks (admissionArgs pairs) rawAttacks :=
    { resolved := declaredResolved
      resolve_eq := hrawResolve'
      ids_nodup := hpairIds' }
  let admission : Lara.Admission.AdmissionResult :=
    { prune :=
        Lara.Admission.buildPrune canon (admissionRows input.policy)
          (admissionLeafMetas output.semanticProgram)
          (admissionLeafTable output.semanticProgram) (admissionArgs pairs)
          rawAttacks (admissionGroups output.semanticProgram) declaredResolved
      declaredResolved := declaredResolved
      audit :=
        Lara.Admission.buildAdmissionAudit canon (admissionRows input.policy)
          (admissionLeafMetas output.semanticProgram)
          (admissionLeafTable output.semanticProgram) (admissionArgs pairs)
          rawAttacks (admissionGroups output.semanticProgram) declaredResolved }
  have hevaluate :
      Lara.Admission.evaluateAdmission canon (admissionRows input.policy)
          (admissionLeafMetas output.semanticProgram)
          (admissionLeafTable output.semanticProgram) (admissionArgs pairs)
          rawAttacks (admissionGroups output.semanticProgram) aligned =
        .accepted admission := by
    simp [Lara.Admission.evaluateAdmission, hkeyNone, hleafNone, haligned,
      hrejection, admission, aligned]
  have hresolveAligned :
      resolveAligned (admissionArgs pairs) rawAttacks hpairIds' = .ok aligned := by
    unfold resolveAligned
    split
    · rename_i he
      rw [hrawResolve'] at he
      contradiction
    · rename_i resolved he
      have hresolved : resolved = declaredResolved := by
        rw [hrawResolve'] at he
        exact (Except.ok.inj he).symm
      subst resolved
      congr
  have hgammaOut :
      Lara.Admission.buildGamma admission.prune.checkedLeaves = output.gamma := by
    simpa [admission, Lara.Admission.buildPrune, surfaceGamma] using h.gamma
  have hgroundOut :
      admission.prune.checkedLeaves.map (·.2) ++
          requestedStatusAtoms output.semanticProgram ++
        input.policy.theories.flatMap (·.2) =
      output.ground := by
    rw [show admission.prune.checkedLeaves =
      Lara.Admission.checkedLeafTable canon (admissionRows input.policy)
        (admissionLeafMetas output.semanticProgram)
        (admissionLeafTable output.semanticProgram)
        (admissionGroups output.semanticProgram) by rfl]
    exact h.ground
  have hargsOut :
      ((admissionArgs pairs).filter keepArgument).map (·.2) =
        output.unit.args :=
    hkeptRawArgs.trans hargs
  have hidsOut :
      ((admissionArgs pairs).filter keepArgument).map
          (fun row => (⟨row.1⟩ : Presentation.ArgId)) =
        output.argIds := by
    calc
      ((admissionArgs pairs).filter keepArgument).map
            (fun row => (⟨row.1⟩ : Presentation.ArgId)) =
          (((keptReconstructed canon input.policy output.semanticProgram pairs).map
              (·.argument.id)).map (·.val)).map
                (fun id => (⟨id⟩ : Presentation.ArgId)) := by
                  simpa [List.map_map, Function.comp_def] using
                    congrArg (List.map fun id : String =>
                      (⟨id⟩ : Presentation.ArgId)) hkeptRawIds.symm
      _ = (keptReconstructed canon input.policy output.semanticProgram pairs).map
            (·.argument.id) :=
        wrap_argId_vals _
      _ = output.argIds := hids
  have hpruneArgs :
      admission.prune.keptArgs.map (·.2) = output.unit.args := by
    simpa [admission, Lara.Admission.buildPrune, keepArgument] using hargsOut
  have hpruneIds :
      admission.prune.keptIds.map
          (fun id => (⟨id⟩ : Presentation.ArgId)) =
        output.argIds := by
    simpa [admission, Lara.Admission.buildPrune, keepArgument,
      Function.comp_def] using hidsOut
  have hpruneAttacks :
      admission.prune.keptAttacks = output.resolvedAttacks := by
    simpa [admission, Lara.Admission.buildPrune, keepArgument] using hselectedRaw
  have hpruneUnitAttacks :
      admission.prune.keptAttacks = output.unit.atts :=
    hpruneAttacks.trans h.unitAttacks
  have hkeptPairsCanonical :
      admissionKeptPairs pairs admission =
        keptReconstructed canon input.policy output.semanticProgram pairs := by
    rfl
  have hclaimsCanonical :
      claimsOf (admissionKeptPairs pairs admission) output.semanticProgram =
        output.claims := by
    rw [hkeptPairsCanonical]
    exact hclaims
  have hquestionsCanonical :
      openQuestionsOf (admissionKeptPairs pairs admission) =
        output.openQuestions := by
    rw [hkeptPairsCanonical]
    exact hquestions
  unfold elaborate elaborateWithAudit
  rw [hprologue]
  simp only [bind_ok_reduce]
  rw [hvalues']
  simp only [bind_ok_reduce]
  rw [hcomparisons']
  simp only [bind_ok_reduce]
  rw [hsemantic]
  simp only [bind_ok_reduce]
  rw [validateGroups_complete h.groups]
  simp only [bind_ok_reduce]
  rw [hfold]
  simp only [bind_ok_reduce]
  rw [hsurface]
  simp only [bind_ok_reduce]
  rw [hrawAttacks]
  simp only [bind_ok_reduce]
  rw [resolveStatuses_complete h.statuses]
  simp only [bind_ok_reduce]
  rw [dif_pos hpairIds']
  rw [hresolveAligned]
  simp only
  rw [hevaluate]
  simp only [Except.map, bind_ok_reduce]
  apply congrArg Except.ok
  cases output with
  | mk gamma ground unit claims argIds authoredObligations openQuestions
      resolvedAttacks semanticProgram =>
    cases unit with
    | mk sigma policy args atts =>
      simp only [outputFromAdmission]
      simp only [hgammaOut, hgroundOut, hpruneArgs, hpruneUnitAttacks,
        hclaimsCanonical, hpruneIds, h.authoredObligations,
        hquestionsCanonical, h.sigma, h.unitPolicy]
      congr
      exact h.unitAttacks.symm

end Lara.Surface
