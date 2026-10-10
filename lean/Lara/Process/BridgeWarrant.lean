import Lara.Process.Conservative
import Lara.Process.Entitlement

/-!
R2: warrant over BHL bridge histories.

`WarrantModel.withArtifact` binds the external artifact check of a warrant
model over bridge histories to BHL's `ArtifactWarrant`, so `Warranted` is then
exactly `ArtifactWarrant` plus the profile checks (`bridge_warranted_iff`), and
an audited submitted argument certifies `ArtifactWarrant` in every compatible
bridge history (`bridge_argument_audit`).

`payloadKind` reads BHL's payload modes into the evidence-kind
lattice: a conditional payload is `conditional`, an applied one `observed`.
`conditional_not_applied` is the non-collapse witness: BHL's conditional-false
method is a valid conditional triple with no modeled application, and its
conditional kind is not admissible under `Profile.strict`.
-/

namespace Lara.Process

open Lara.BHL Lara.Support

variable {canon : String → String} {reg : BackendRegistry canon} {Claim Wit : Type}

/-- Bind a warrant model's artifact check to BHL's `ArtifactWarrant`. -/
def WarrantModel.withArtifact (M : WarrantModel (BridgeHistory reg) Claim Wit) :
    WarrantModel (BridgeHistory reg) Claim Wit :=
  { M with artifact := fun h _ => ArtifactWarrant h.binding h.run }

theorem bridge_warranted_iff {Policy : Type} (M : WarrantModel (BridgeHistory reg) Claim Wit)
    (P : Profile Policy) (h : BridgeHistory reg) (c : Claim) (w : Wit) :
    Warranted M.withArtifact P h c w ↔
      ArtifactWarrant h.binding h.run ∧ ProfileChecks M P h c w :=
  Iff.rfl

/-- An audited submitted argument certifies the BHL artifact warrant in every
compatible bridge history. -/
theorem bridge_argument_audit {Policy Rho R : Type}
    {M : WarrantModel (BridgeHistory reg) Claim Wit} {P : Profile Policy}
    {S : ProcessModel (BridgeHistory reg) Rho R} {A : Admitted (BridgeHistory reg) Rho Policy}
    {r : R} {c : Claim} {w : Wit} (audited : ArgumentEntitled M.withArtifact P S A r c w) :
    ∀ x, Compatible S A.assumptions r x → ArtifactWarrant x.1.binding x.1.run :=
  fun x hx => (audited.2.2 x hx).1

/-- BHL payload modes read as evidence kinds. -/
def payloadKind : PayloadMode → EvidenceKind
  | .conditional => .conditional
  | .applied => .observed

/-- Conditional but not applied: the conditional-false method is a valid
conditional triple without a modeled application, and a conditional payload is
not admissible under the strict profile. -/
theorem conditional_not_applied {Policy : Type} (binding : ArtifactBinding)
    (canonical : binding.canonical = CheckedMethods.Method.conditionalFalse.binding) (α : ℚ) :
    ConditionalMethod binding ∧ ¬ ModeledApplication binding ∧
      payloadKind .conditional ∉ (Profile.strict (Policy := Policy) α).admissible := by
  refine ⟨?_, conditional_false_no_application binding canonical, by simp [payloadKind, Profile.strict]⟩
  unfold ConditionalMethod
  rw [canonical]
  exact CheckedMethods.method_valid .conditionalFalse

end Lara.Process
