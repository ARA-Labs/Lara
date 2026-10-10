import Lara.Process.Revision
import Lara.BHL.LaraBridge

/-!
R5: the update/revision distinction over core source edits.

Katsuno–Mendelzon's distinction is drawn on `Lara.Update.SourceUpdate`. A
`tighten` quarantines a leaf kind/provenance: it is a *revision*, and
`tighten_revision` restates `Lara.BHL.tighten_artifact_warrant_loss` as the
withdrawal of every artifact warrant that depends on the quarantined material.
Every other constructor adds material: it is an *update*, after which warrant
must be re-established by recomputation (an added attack can still defeat).
-/

namespace Lara.Process

open Lara Lara.BHL Lara.Support

/-- The class of a core source edit. -/
inductive EditClass where
  | update
  | revision
  deriving DecidableEq, Repr

/-- `tighten` revises; every other source edit updates. -/
def editClass : Update.SourceUpdate → EditClass
  | .tighten _ => .revision
  | _ => .update

/-- A revision withdraws dependent warrants: an actual `tighten` of material a
selected or dependency support uses leaves no artifact warrant for the binding
at the target source. -/
theorem tighten_revision {canon : String → String} {reg : BackendRegistry canon}
    {source target : Update.SourceState}
    (sourceRun : Update.AcceptedRun reg source) (targetRun : Update.AcceptedRun reg target)
    {key : Presentation.LeafKind × Presentation.Provenance}
    (update : Update.applyUpdate reg source (.tighten key) = .ok target)
    (binding : ArtifactBinding) (sameTarget : binding.source = target)
    (ref : SupportRef) (member : ref ∈ binding.supports) (raw : RawSupport reg source ref)
    (metadata : Admission.LeafMeta) (declared : metadata ∈ source.metas)
    (keyExact : (metadata.kind, metadata.provenance) = key)
    (used : metadata.id ∈ Support.leaves ref.row.2) :
    editClass (.tighten key) = .revision ∧ ¬ ArtifactWarrant binding (sameTarget.symm ▸ targetRun) :=
  ⟨rfl, tighten_artifact_warrant_loss sourceRun targetRun update binding sameTarget ref member raw
    metadata declared keyExact used⟩

/-- An update keeps old warrants for the old version. This records how warrant
is indexed rather than proving anything about the edit: an artifact warrant is
a property of its binding's source snapshot, and applying an update produces a
new snapshot without changing the old one. -/
theorem update_keeps_old {canon : String → String} {reg : BackendRegistry canon}
    {source target : Update.SourceState} {u : Update.SourceUpdate}
    (_isUpdate : editClass u = .update)
    (_applied : Update.applyUpdate reg source u = .ok target)
    (binding : ArtifactBinding) (run : Update.AcceptedRun reg binding.source)
    (_old : binding.source = source) (warrant : ArtifactWarrant binding run) :
    ArtifactWarrant binding run :=
  warrant

/-- At the updated snapshot, warrant must be re-established. The rebinding
contract `RebindConditions` (injective raw and checked index maps, preserved
material and a sink embedding) suffices; `warranted_natural` and
`corroboration_preserved_iff` show injectivity is needed only where a profile
counts sources, which refines that sufficient contract toward a
characterization on the support-only fragment. -/
theorem update_reestablish {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} (certificate : BridgeCertificate reg registry)
    {target : Update.SourceState} (targetRun : Update.AcceptedRun reg target)
    (rawMap checkedMap : Nat → Nat) (sinks : List Nat) (evidence : Option EvidenceMaterial)
    (transport : RebindConditions certificate targetRun rawMap checkedMap sinks evidence)
    (oldWarrant : ArtifactWarrant certificate.binding certificate.run) :
    ArtifactWarrant (reboundBinding certificate.binding target rawMap checkedMap evidence)
      targetRun :=
  rebind_warrant certificate targetRun rawMap checkedMap sinks evidence transport oldWarrant

end Lara.Process
