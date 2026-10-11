import Lara.Process.Source

set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

namespace Lara.Examples.ProcessSourceReplay

open Lara.Process.Source

def wrap (surface : Surface.Input) : SourceInput :=
  { surface
    replay :=
      { core := ⟨Driver.coreVersionText⟩
        policy := surface.policy.id
        backends := surface.program.backends.map fun pair => ⟨pair.1, ⟨pair.2⟩⟩
        theories := surface.policy.theories.map Prod.fst
        artifact := surface.program.digest }
    capture := none }

def accepted (surface : Surface.Input) : Bool :=
  match checkSource (wrap surface) with
  | .ok _ => true
  | .error _ => false

def rejection (surface : Surface.Input) : Option SourceRejection :=
  match checkSource (wrap surface) with
  | .ok _ => none
  | .error error => some error

def withoutSelection (surface : Surface.Input) : Surface.Input :=
  { surface with program := { surface.program with backends := [] } }

theorem withoutSelection_clears_both (surface : Surface.Input) :
    (wrap (withoutSelection surface)).surface.program.backends = [] ∧
      (wrap (withoutSelection surface)).replay.backends = [] := ⟨rfl, rfl⟩

/-- The shipped `ord@1` checker admits proof-producing normalization without
ND's classical formula equality. Both slots cite the same numeric cell. -/
def certificate : Presentation.Assurance :=
  .cert ⟨⟨"ord"⟩, 1, ⟨"sha256:replay"⟩, Surface.ordcmpPayload 0 0⟩

def leafId : Presentation.LeafId := ⟨"l-cell"⟩
def argCertId : Presentation.ArgId := ⟨"a-cert"⟩

def cellPattern : Presentation.AtomPat :=
  ⟨"cell", .cons (.lit (.num "1")) .nil⟩

def comparisonPattern : Presentation.AtomPat :=
  ⟨"num_le", .cons (.lit (.num "1")) (.cons (.lit (.num "1")) .nil)⟩

def leaf : Presentation.Leaf :=
  ⟨leafId, .atom "cell" (.cons (.num "1") .nil), .observed, .user, [], none⟩

def certificateRule : Presentation.Rule :=
  { id := ⟨"compare-self"⟩
    params := []
    mode := .strict
    premises := [cellPattern]
    premiseLabels := []
    conclusion := comparisonPattern
    allowTrusted := false
    certifiers := [⟨⟨"ord"⟩, 1, ⟨"sha256:replay"⟩⟩]
    questions := [] }

def policy : Presentation.Policy :=
  { id := ⟨"replay-policy"⟩
    sigma := ⟨[], [], [⟨⟨"cell"⟩, [.num]⟩, ⟨⟨"num_le"⟩, [.num, .num]⟩]⟩
    rules := [certificateRule]
    contraries := []
    exceptions := []
    admission := [((.observed, .user), .admit)]
    theories := [(⟨"sha256:replay"⟩, [])]
    groupMode := .quarantineOnConflict
    measurands := []
    comparisonSchemes := [] }

def certifiedTerm : Presentation.SupportTerm :=
  .rule certificateRule.id [] (.cons (.leaf leafId) .nil) .nil [] certificate

def certificateInput : Surface.Input :=
  { program :=
      { artifact := "source-replay"
        digest := ⟨"sha256:source-replay"⟩
        policy := policy.id
        backends := [(⟨"ord"⟩, "1")]
        valueBindings := []
        decls := [.leaf leaf,
          .arg ⟨argCertId, .supportsDerived ⟨"c-comparison"⟩,
            .explicitTheta certifiedTerm⟩] }
    policy }

def outerRule : Presentation.Rule :=
  { certificateRule with
    id := ⟨"outer"⟩
    premises := [comparisonPattern]
    allowTrusted := true
    certifiers := [] }

def nestedInput : Surface.Input :=
  { program := { certificateInput.program with decls := [.leaf leaf,
      .arg ⟨⟨"nested"⟩, .supportsDerived ⟨"c-comparison"⟩,
        .explicitTheta (.rule outerRule.id [] (.cons certifiedTerm .nil) .nil [] .trusted)⟩] }
    policy := { policy with rules := [certificateRule, outerRule] } }

/-- A discharged mandatory question belongs to a defeasible step with no
assurance. Strict steps prohibit discharges, even when their answers check. -/
def dischargeRule : Presentation.Rule :=
  { outerRule with
    mode := .defeasible
    premises := [cellPattern]
    allowTrusted := false
    questions := [⟨⟨"required"⟩, comparisonPattern, .mandatory⟩] }

def dischargedInput : Surface.Input :=
  { program := { certificateInput.program with decls := certificateInput.program.decls ++ [
      .arg ⟨⟨"discharged"⟩, .supportsDerived ⟨"c-comparison"⟩,
        .explicitTheta (.rule dischargeRule.id [] (.cons (.leaf leafId) .nil)
          (.cons ⟨"required"⟩ (.leaf ⟨argCertId.val⟩) .nil) [] .none)⟩] }
    policy := { policy with rules := [certificateRule, dischargeRule] } }

def quarantinedInput : Surface.Input :=
  { certificateInput with policy := { policy with
      admission := [((.observed, .user), .quarantine)] } }

/-- Compute only proof-free checker outputs. Completeness below turns these
checks into actual source acceptance, avoiding reduction through dependent records. -/
private def ready (surface : Surface.Input) : Bool :=
  let env := sourceEnv (wrap surface)
  match Surface.assemble env surface with
  | .error _ => false
  | .ok out =>
    decide (surface.policy.evidenceCheckers.Nodup ∧
      Check.Unit.signatureStage out.ground out.unit = none ∧
      Policy.firstOutOfScope? out.unit.policy = none ∧
      (out.unit.policy.rules.map (·.id)).Nodup ∧ out.unit.args.Nodup ∧
      out.unit.policy.defeat.contraries = [] ∧ out.unit.atts = []) &&
    out.unit.args.all (fun term =>
      (Check.inferSupport out.unit.policy.ruleLookup out.gamma env.registry
        Check.CheckLoc.root term).isOk) &&
    (Surface.checkSourceGroups canonNum surface.policy out.semanticProgram).isOk &&
    (Evidence.admit [] surface.policy.evidenceCheckers [] Evidence.extract
      (Surface.leafRecords out.semanticProgram)).isOk &&
    decide ((Surface.leafRecords out.semanticProgram).find? Surface.needsEvidence = none)

private theorem ready_source (surface : Surface.Input) (h : ready surface = true) :
    ∃ result : Surface.SourceWithEvidenceAudit (sourceEnv (wrap surface)) surface [] [],
      Surface.sourceWithEvidenceAudit (sourceEnv (wrap surface)) surface [] [] = .ok result ∧
      (Surface.leafRecords result.output.semanticProgram).find? Surface.needsEvidence = none := by
  cases ha : Surface.assemble (sourceEnv (wrap surface)) surface with
  | error error => simp [ready, ha] at h
  | ok out =>
    simp only [ready, ha, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨⟨hn, hsig, hscope, hids, hargs, hcontra, hatts⟩, hsupport⟩,
      hgroups⟩, hevidence⟩, hneeds⟩
    have supports : ∀ term ∈ out.unit.args, ∃ C O,
        Support.HasSupport canonNum out.unit.policy.ruleLookup out.gamma
          (Support.certOkOf (sourceEnv (wrap surface)).registry) term C O := by
      intro term hterm
      obtain ⟨result, hresult⟩ := Check.Unit.exists_ok_of_isOk
        (List.all_eq_true.mp hsupport term hterm)
      exact ⟨result.conclusion, result.obligations, Check.inferSupport_sound hresult⟩
    obtain ⟨checked, hchecked⟩ := Check.Unit.checkUnit_complete_holes
      (reg := (sourceEnv (wrap surface)).registry) hsig hscope hids
      (by intro p hp ab hab; rw [hcontra] at hab; cases hab)
      hargs supports
      (by intro k hk; rw [hatts] at hk; cases hk)
      (by intro k hk; rw [hatts] at hk; cases hk)
      (by intro k hk; rw [hatts] at hk; cases hk)
      (by
        intro source hs target ht C D hC hD hmatch
        obtain ⟨ab, hab, _⟩ := hmatch
        rw [hcontra] at hab
        cases hab)
    obtain ⟨groups, hg⟩ := Check.Unit.exists_ok_of_isOk hgroups
    obtain ⟨judgments, he⟩ := Check.Unit.exists_ok_of_isOk hevidence
    have legacy : Surface.sourceWithEvidence (sourceEnv (wrap surface)) surface [] []
        Evidence.extract = .ok (out, judgments) := by
      simp [Surface.sourceWithEvidence, hn, ha, hg, he,
        Surface.finishAssembled, hchecked, Except.mapError]
    have erase := Surface.sourceWithEvidenceAudit_erasure
      (sourceEnv (wrap surface)) surface [] []
    cases hs : Surface.sourceWithEvidenceAudit (sourceEnv (wrap surface)) surface [] [] with
    | error error => simp [hs, legacy, Except.map, Except.mapError] at erase
    | ok result =>
      have equal : result.output = out := by
        have pair : (result.output, result.judgments) = (out, judgments) := by
          simpa [hs, legacy, Except.map, Except.mapError] using erase
        exact congrArg Prod.fst pair
      exact ⟨result, rfl, by simpa [equal] using hneeds⟩

private def selection (surface : Surface.Input) :=
  (Surface.elaborateWithAudit (sourceEnv (wrap surface)) surface).map fun audit =>
    firstUnselectedDeclared (selectedBackends (wrap surface)) audit.declared.pairs 0

private theorem accepted_of_ready (surface : Surface.Input)
    (hready : ready surface = true)
    (hr : replayCompatible (wrap surface) = .ok ())
    (hsel : selection surface = .ok none) : accepted surface = true := by
  obtain ⟨result, hs, hn⟩ := ready_source surface hready
  have select : firstUnselectedDeclared (selectedBackends (wrap surface))
      result.audit.declared.pairs 0 = none := by
    simpa [selection, result.audit_eq, Except.map] using hsel
  have audited : Surface.sourceWithEvidenceAudit (sourceEnv (wrap surface))
      (wrap surface).surface (wrap surface).snapshot (wrap surface).manifest = .ok result := hs
  have success : ∃ observation, checkSource (wrap surface) = .ok observation := by
    unfold checkSource
    split
    · rename_i error he
      rw [hr] at he
      contradiction
    · split
      · rename_i error he
        rw [audited] at he
        contradiction
      · rename_i found hf
        have equal : found = result := Except.ok.inj (hf.symm.trans audited)
        subst found
        split
        · rename_i value hv
          rw [select] at hv
          contradiction
        · split
          · exact ⟨_, rfl⟩
          · split
            · rename_i value hv
              have impossible := hn.symm.trans hv
              cases impossible
            · exact ⟨_, rfl⟩
  obtain ⟨observation, ho⟩ := success
  unfold accepted
  rw [ho]

private theorem rejected_of_ready (surface : Surface.Input)
    (index : Nat) (argument : Presentation.ArgId) (backend : Support.BackendId)
    (hready : ready surface = true)
    (hr : replayCompatible (wrap surface) = .ok ())
    (hsel : selection surface = .ok (some (index, argument, backend))) :
    rejection surface = some (.unselectedCertificate index argument backend) := by
  obtain ⟨result, hs, _⟩ := ready_source surface hready
  have select : firstUnselectedDeclared (selectedBackends (wrap surface))
      result.audit.declared.pairs 0 = some (index, argument, backend) := by
    simpa [selection, result.audit_eq, Except.map] using hsel
  have audited : Surface.sourceWithEvidenceAudit (sourceEnv (wrap surface))
      (wrap surface).surface (wrap surface).snapshot (wrap surface).manifest = .ok result := hs
  have rejected : checkSource (wrap surface) =
      .error (.unselectedCertificate index argument backend) := by
    unfold checkSource
    split
    · rename_i error he
      rw [hr] at he
      contradiction
    · split
      · rename_i error he
        rw [audited] at he
        contradiction
      · rename_i found hf
        have equal : found = result := Except.ok.inj (hf.symm.trans audited)
        subst found
        split
        · rename_i i a b hv
          have equal := Option.some.inj (hv.symm.trans select)
          cases equal
          rfl
        · rename_i hv
          rw [select] at hv
          contradiction
  unfold rejection
  rw [rejected]

theorem selected_certificate_accepted : accepted certificateInput = true :=
  accepted_of_ready certificateInput (by cbv) (by decide +kernel) (by cbv)

theorem unselected_certificate_rejected :
    rejection (withoutSelection certificateInput) =
      some (.unselectedCertificate 0 argCertId Driver.ordBackendId) :=
  rejected_of_ready _ _ _ _ (by cbv) (by decide +kernel) (by cbv)

theorem selected_nested_certificate_accepted : accepted nestedInput = true :=
  accepted_of_ready nestedInput (by cbv) (by decide +kernel) (by cbv)

theorem nested_certificate_not_hidden :
    rejection (withoutSelection nestedInput) =
      some (.unselectedCertificate 0 ⟨"nested"⟩ Driver.ordBackendId) :=
  rejected_of_ready _ _ _ _ (by cbv) (by decide +kernel) (by cbv)

theorem selected_discharged_certificate_accepted : accepted dischargedInput = true :=
  accepted_of_ready dischargedInput (by cbv) (by decide +kernel) (by cbv)

/-- The prior certificate is the first authoritative declaration; the discharged
copy is checked separately below without changing first-rejection priority. -/
theorem discharged_certificate_not_hidden :
    rejection (withoutSelection dischargedInput) =
      some (.unselectedCertificate 0 argCertId Driver.ordBackendId) :=
  rejected_of_ready _ _ _ _ (by cbv) (by decide +kernel) (by cbv)

theorem quarantined_certificate_not_hidden :
    rejection (withoutSelection quarantinedInput) =
      some (.unselectedCertificate 0 argCertId Driver.ordBackendId) :=
  rejected_of_ready _ _ _ _ (by cbv) (by decide +kernel) (by cbv)

theorem quarantined_certificate_is_declared_not_retained :
    (Surface.elaborateWithAudit (sourceEnv (wrap quarantinedInput)) quarantinedInput).map
      (fun audit => (audit.declared.pairs.length, audit.output.unit.args.length)) =
      .ok (1, 0) := by cbv

/-- Production reconstruction expands the prior-argument reference inside the
mandatory discharge. This is the real declared audit row, not a visitor mock. -/
def dischargedCore : Option Support.SupportTerm :=
  (Surface.elaborateWithAudit (sourceEnv (wrap dischargedInput))
    dischargedInput).toOption.bind fun audit => audit.declared.pairs[1]?.map (·.core)

theorem discharged_core_exact :
    dischargedCore = some (Surface.toSupportTerm
      (.rule dischargeRule.id [] (.cons (.leaf leafId) .nil)
        (.cons ⟨"required"⟩ certifiedTerm .nil) [] .none)) := by cbv

theorem discharged_core_requires_selection :
    dischargedCore.map (Driver.firstUnselectedCertificate []) =
      some (some Driver.ordBackendId) := by
  rw [discharged_core_exact]
  decide +kernel

theorem accepted_discharge_retains_core
    (observation : AcceptedObservation (wrap dischargedInput)) :
    observation.accepted.audit.declared.pairs[1]?.map (·.core) = dischargedCore := by
  have auditEq : Surface.elaborateWithAudit (sourceEnv (wrap dischargedInput))
      dischargedInput = .ok observation.accepted.audit := observation.accepted.audit_eq
  unfold dischargedCore
  rw [auditEq]
  rfl

theorem accepted_discharge_requires_selection
    (observation : AcceptedObservation (wrap dischargedInput)) :
    observation.accepted.audit.declared.pairs[1]?.map
      (fun row => Driver.firstUnselectedCertificate [] row.core) =
      some (some Driver.ordBackendId) := by
  have required := discharged_core_requires_selection
  rw [← accepted_discharge_retains_core observation] at required
  simp only [Option.map_map] at required
  exact required

end Lara.Examples.ProcessSourceReplay
