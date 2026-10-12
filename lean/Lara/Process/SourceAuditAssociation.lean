import Lara.Process.SourceAuditSupport

namespace Lara.Process.Source

inductive AssociationFault where
  | inputClaim
  | semanticClaim
  | missingDeclaration
  | wrongArgument
  | notAlternative
  deriving DecidableEq

structure SourceAssociation {input : SourceInput} (observation : AcceptedObservation input)
    (claim : ClaimBinding) (argument : Presentation.ArgId)
    (selected : ResolvedSupport observation ⟨argument, claim.query⟩) : Type where
  inputClaim : Surface.claimFormal? input.surface.program claim.declaration = some claim.query
  semanticClaim : Surface.claimFormal? observation.accepted.audit.declared.semanticProgram
    claim.declaration = some claim.query
  selectedPair : ∃ pair,
    observation.accepted.audit.declared.pairs[selected.ref.rawIndex]? = some pair ∧
      pair.argument.id = argument ∧ pair.core = selected.ref.row.2 ∧
        Surface.argSupportsClaim claim.declaration pair.argument.concl = true
  alternative : ∃ indices,
    (claim.declaration, indices) ∈ Surface.claimAlternativesOf observation.accepted.audit.declared.pairs
      observation.accepted.audit.declared.semanticProgram ∧ selected.ref.rawIndex ∈ indices

def associateSource {input : SourceInput} (observation : AcceptedObservation input)
    (claim : ClaimBinding) (argument : Presentation.ArgId)
    (selected : ResolvedSupport observation ⟨argument, claim.query⟩) :
    Except AssociationFault (SourceAssociation observation claim argument selected) :=
  if inputClaim : Surface.claimFormal? input.surface.program claim.declaration = some claim.query then
    if semanticClaim : Surface.claimFormal? observation.accepted.audit.declared.semanticProgram
        claim.declaration = some claim.query then
      match pairAt : observation.accepted.audit.declared.pairs[selected.ref.rawIndex]? with
      | none => .error .missingDeclaration
      | some pair =>
        if pairExact : pair.argument.id = argument ∧ pair.core = selected.ref.row.2 ∧
            Surface.argSupportsClaim claim.declaration pair.argument.concl = true then
          let alternatives := Surface.claimAlternativesOf observation.accepted.audit.declared.pairs
            observation.accepted.audit.declared.semanticProgram
          match alternativeAt : alternatives.find? (fun entry =>
              decide (entry.1 = claim.declaration ∧ selected.ref.rawIndex ∈ entry.2)) with
          | none => .error .notAlternative
          | some entry =>
            .ok
              { inputClaim := inputClaim
                semanticClaim := semanticClaim
                selectedPair := ⟨pair, pairAt, pairExact⟩
                alternative := by
                  have found : decide (entry.1 = claim.declaration ∧ selected.ref.rawIndex ∈ entry.2) = true :=
                    List.find?_some (p := fun candidate : Presentation.PropId × List Nat =>
                      decide (candidate.1 = claim.declaration ∧ selected.ref.rawIndex ∈ candidate.2)) alternativeAt
                  have matching := of_decide_eq_true found
                  have member := List.mem_of_find?_eq_some alternativeAt
                  have entryEq : entry = (claim.declaration, entry.2) := Prod.ext matching.1 rfl
                  exact ⟨entry.2, entryEq ▸ member, matching.2⟩ }
        else .error .wrongArgument
    else .error .semanticClaim
  else .error .inputClaim

structure ResolvedSupports {input : SourceInput} (observation : AcceptedObservation input)
    (bindings : List SupportBinding) where
  refs : List BHL.SupportRef
  raw : ∀ ref ∈ refs, BHL.RawSupport (sourceEnv input).registry observation.state ref
  exact : refs.map (fun ref => (⟨⟨ref.row.1⟩, ref.query⟩ : SupportBinding)) = bindings

def resolveSupports {input : SourceInput} (observation : AcceptedObservation input) :
    (bindings : List SupportBinding) → Except (Presentation.ArgId × SupportFault)
      (ResolvedSupports observation bindings)
  | [] => .ok ⟨[], by simp, rfl⟩
  | binding :: rest =>
    match resolveSupport observation binding with
    | .error error => .error (binding.argument, error)
    | .ok head =>
      match resolveSupports observation rest with
      | .error error => .error error
      | .ok tail =>
        .ok
          { refs := head.ref :: tail.refs
            raw := by
              intro ref member
              rcases List.mem_cons.mp member with same | member
              · subst ref; exact head.raw
              · exact tail.raw ref member
            exact := by
              simp only [List.map_cons, head.name, head.query, tail.exact] }

structure MethodBinding where
  method : BHL.CheckedMethods.Method
  mode : BHL.PayloadMode
  parameter : Int
  first : Bool
  second : Bool
  residual : List BHL.ResidualAssumption
  deriving DecidableEq

/-- The method binding contains no supplied canonical program, checker result,
source association, or successful application flag. -/
def artifactBinding {input : SourceInput} (observation : AcceptedObservation input)
    (claim : ClaimBinding) (argument : Presentation.ArgId)
    (selected : ResolvedSupport observation ⟨argument, claim.query⟩)
    {dependencies : List SupportBinding} (resolved : ResolvedSupports observation dependencies)
    (method : MethodBinding) : BHL.ArtifactBinding :=
  { source := observation.state
    claim := claim.declaration
    origin := .declared argument
    query := claim.query
    interpretation := .ofMode method.mode method.method
    selected := selected.ref
    dependencies := resolved.refs
    method := method.method
    canonical := method.method.binding
    request := method.method.request method.parameter method.first method.second
    residual := method.residual
    coverage := .completeModeled
    mode := method.mode
    evidence := some ⟨input.surface, input.snapshot, input.manifest, observation.accepted.output.ground⟩ }

@[macro_inline]
def bridgeCertificate {input : SourceInput} (observation : AcceptedObservation input)
    (claim : ClaimBinding) (argument : Presentation.ArgId)
    (selected : ResolvedSupport observation ⟨argument, claim.query⟩)
    (association : SourceAssociation observation claim argument selected)
    {dependencies : List SupportBinding} (resolved : ResolvedSupports observation dependencies)
    (method : MethodBinding) : BHL.BridgeCertificate (sourceEnv input).registry Evidence.extract :=
  { binding := artifactBinding observation claim argument selected resolved method
    run := observation.run
    raw := by
      intro ref member
      rcases List.mem_cons.mp member with same | member
      · subst ref; exact selected.raw
      · exact resolved.raw ref member
    evidence := .certified observation.certified
    association := by
      rw [observation.run_eq]
      apply BHL.ClaimAssociation.declared argument rfl rfl
        (BHL.certifiedSourceOfSource observation.accepted.audit observation.accepted.source_eq
          observation.accepted.audit_eq rfl)
      · exact selected.raw.occurrence
      · exact association.inputClaim
      · exact association.semanticClaim
      · exact association.selectedPair
      · exact selected.name
      · exact association.alternative
      · exact selected.query }

@[macro_inline]
def checkMethod {input : SourceInput} (observation : AcceptedObservation input)
    (claim : ClaimBinding) (argument : Presentation.ArgId)
    (selected : ResolvedSupport observation ⟨argument, claim.query⟩)
    (association : SourceAssociation observation claim argument selected)
    {dependencies : List SupportBinding} (resolved : ResolvedSupports observation dependencies)
    (method : MethodBinding) : Except BHL.BridgeError _root_.Unit :=
  BHL.checkBridgeNative (artifactBinding observation claim argument selected resolved method)
    (bridgeCertificate observation claim argument selected association resolved method)

theorem checkMethod_sound {input : SourceInput} (observation : AcceptedObservation input)
    (claim : ClaimBinding) (argument : Presentation.ArgId)
    (selected : ResolvedSupport observation ⟨argument, claim.query⟩)
    (association : SourceAssociation observation claim argument selected)
    {dependencies : List SupportBinding} (resolved : ResolvedSupports observation dependencies)
    (method : MethodBinding)
    (checked : checkMethod observation claim argument selected association resolved method = .ok ()) :
    BHL.ArtifactMeaning (artifactBinding observation claim argument selected resolved method)
      observation.run := by
  unfold checkMethod BHL.checkBridgeNative at checked
  cases result : BHL.checkBridge (artifactBinding observation claim argument selected resolved method)
      (bridgeCertificate observation claim argument selected association resolved method) with
  | error error => simp [result, Except.map] at checked
  | ok certificate => exact certificate.checked.meaning

structure InterpretationId where
  index : Nat
  deriving DecidableEq, Repr

inductive ArtifactInterpretation where
  | declared : InterpretationId → ArtifactInterpretation
  | checkedMethod : MethodBinding → ArtifactInterpretation
  deriving DecidableEq

structure ArtifactSpec where
  argument : Presentation.ArgId
  dependencies : List SupportBinding
  interpretation : ArtifactInterpretation
  deriving DecidableEq

inductive ArtifactFault where
  | support : Presentation.ArgId → SupportFault → ArtifactFault
  | association : AssociationFault → ArtifactFault
  | method : BHL.BridgeError → ArtifactFault
  deriving DecidableEq

structure SourceArtifact {input : SourceInput} (observation : AcceptedObservation input)
    (claim : ClaimBinding) (spec : ArtifactSpec) where
  selected : ResolvedSupport observation ⟨spec.argument, claim.query⟩
  association : SourceAssociation observation claim spec.argument selected
  dependencies : ResolvedSupports observation spec.dependencies
  method_ok : ∀ method, spec.interpretation = .checkedMethod method →
    checkMethod observation claim spec.argument selected association dependencies method = .ok ()

def checkArtifact {input : SourceInput} (observation : AcceptedObservation input)
    (claim : ClaimBinding) (spec : ArtifactSpec) :
    Except ArtifactFault (SourceArtifact observation claim spec) :=
  match resolveSupport observation ⟨spec.argument, claim.query⟩ with
  | .error error => .error (.support spec.argument error)
  | .ok selected =>
    match associateSource observation claim spec.argument selected with
    | .error error => .error (.association error)
    | .ok association =>
      match resolveSupports observation spec.dependencies with
      | .error (argument, error) => .error (.support argument error)
      | .ok dependencies =>
        match interpretation : spec.interpretation with
        | .declared _ =>
          .ok ⟨selected, association, dependencies, by
            intro method named
            rw [interpretation] at named
            cases named⟩
        | .checkedMethod method =>
          match checked : checkMethod observation claim spec.argument selected association dependencies method with
          | .error error => .error (.method error)
          | .ok () =>
            .ok ⟨selected, association, dependencies, by
              intro requested named
              rw [interpretation] at named
              cases named
              exact checked⟩

theorem SourceArtifact.method_sound {input : SourceInput}
    {observation : AcceptedObservation input} {claim : ClaimBinding} {spec : ArtifactSpec}
    (artifact : SourceArtifact observation claim spec) (method : MethodBinding)
    (named : spec.interpretation = .checkedMethod method) :
    BHL.ArtifactMeaning
      (artifactBinding observation claim spec.argument artifact.selected artifact.dependencies method)
      observation.run :=
  checkMethod_sound observation claim spec.argument artifact.selected artifact.association
    artifact.dependencies method (artifact.method_ok method named)

end Lara.Process.Source
