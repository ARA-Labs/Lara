import Lara.Process.Entitlement
import Lara.Process.Bridge
import Lara.Process.SourceInput

namespace Lara.Process.Source

structure AssumptionId where
  index : Nat
  deriving DecidableEq, Repr

inductive KindKey where
  | leaf : Presentation.LeafId → KindKey
  | method : Support.RuleId → KindKey
  | argument : Presentation.ArgId → KindKey
  deriving DecidableEq

/-- Reader admission binds a fidelity assumption to exact source and process
material. It is not a certificate that the physical event occurred. -/
structure CaptureAssumption where
  id : AssumptionId
  source : SourceInput
  key : KindKey
  event : Stamped
  run : RunId
  basis : AdmissionBasis
  deriving DecidableEq

structure KindSpec where
  source : SourceInput
  key : KindKey
  upper : EvidenceKind
  assumption : Option AssumptionId
  deriving DecidableEq

mutual
/-- Every support dependency, including rule methods and discharge subterms. -/
  def supportKeys : Support.SupportTerm → List KindKey
    | .leaf leaf => [.leaf ⟨leaf.name⟩]
    | .inst rule _ premises discharges _ _ =>
        .method rule :: (premiseKeys premises ++ dischargeKeys discharges)
  def premiseKeys : List Support.SupportTerm → List KindKey
    | [] => []
    | term :: rest => supportKeys term ++ premiseKeys rest
  def dischargeKeys : List (Support.QuestionId × Support.SupportTerm) → List KindKey
    | [] => []
    | entry :: rest => supportKeys entry.2 ++ dischargeKeys rest
end

def CaptureAssumption.matches (assumption : CaptureAssumption) (source : SourceInput)
    (key : KindKey) (history : ProcessHistory) (admitted : List AdmissionBasis) : Bool :=
  decide (assumption.source = source ∧ assumption.key = key ∧
    assumption.event ∈ history ∧ assumption.basis ∈ admitted) &&
    match assumption.event.event with
    | .run run _ _ _ _ | .result run _ => decide (run = assumption.run)
    | _ => false

def kindFromSpec (source : SourceInput) (history : ProcessHistory)
    (assumptions : List CaptureAssumption) (admitted : List AdmissionBasis)
    (hypothetical : List KindKey) (key : KindKey) (spec : KindSpec) :
    EvidenceKind × Bool :=
  let cap := if key ∈ hypothetical then EvidenceKind.hypothetical
    else if assumptions.any (fun assumption =>
      spec.assumption == some assumption.id &&
        assumption.matches source key history admitted) then .observed
    else .conditional
  (spec.upper ⊓ cap, true)

/-- Slot provenance is supplied by materialization, not by producer kind labels.
Missing metadata gets the least kind and is separately reported incomplete. -/
def inputKind (source : SourceInput) (history : ProcessHistory)
    (specs : List KindSpec) (assumptions : List CaptureAssumption)
    (admitted : List AdmissionBasis) (hypothetical : List KindKey) (key : KindKey) :
    EvidenceKind × Bool :=
  match specs.find? (fun spec => decide (spec.source = source ∧ spec.key = key)) with
  | none => (.hypothetical, false)
  | some spec => kindFromSpec source history assumptions admitted hypothetical key spec

def meetKinds : List (EvidenceKind × Bool) → EvidenceKind × Bool
  | [] => (.observed, true)
  | value :: rest =>
      let tail := meetKinds rest
      (value.1 ⊓ tail.1, value.2 && tail.2)

def nodeKind (source : SourceInput) (history : ProcessHistory)
    (specs : List KindSpec) (assumptions : List CaptureAssumption)
    (admitted : List AdmissionBasis) (hypothetical : List KindKey)
    (argument : Presentation.ArgId) (term : Support.SupportTerm) : EvidenceKind × Bool :=
  meetKinds ((.argument argument :: supportKeys term).map
    (inputKind source history specs assumptions admitted hypothetical))

theorem meetKinds_complete (inputs : List (EvidenceKind × Bool)) :
    (meetKinds inputs).2 = true ↔ ∀ input ∈ inputs, input.2 = true := by
  induction inputs with
  | nil => simp [meetKinds]
  | cons value rest ih => simp [meetKinds, ih]

theorem meetKinds_le_input {inputs : List (EvidenceKind × Bool)} {input : EvidenceKind × Bool}
    (member : input ∈ inputs) : (meetKinds inputs).1 ≤ input.1 := by
  induction inputs with
  | nil => simp at member
  | cons value rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst input
      exact inf_le_left
    · exact le_trans inf_le_right (ih member)

theorem inputKind_hypothetical (source : SourceInput) (history : ProcessHistory)
    (specs : List KindSpec) (assumptions : List CaptureAssumption)
    (admitted : List AdmissionBasis) (hypothetical : List KindKey) (key : KindKey)
    (member : key ∈ hypothetical) :
    (inputKind source history specs assumptions admitted hypothetical key).1 = .hypothetical := by
  unfold inputKind
  split
  · rfl
  · simp only [kindFromSpec, if_pos member]
    exact le_antisymm inf_le_right bot_le

theorem nodeKind_no_promotion (source : SourceInput) (history : ProcessHistory)
    (specs : List KindSpec) (assumptions : List CaptureAssumption)
    (admitted : List AdmissionBasis) (hypothetical : List KindKey)
    (argument : Presentation.ArgId) (term : Support.SupportTerm) (key : KindKey)
    (used : key ∈ .argument argument :: supportKeys term) (slot : key ∈ hypothetical) :
    (nodeKind source history specs assumptions admitted hypothetical argument term).1 =
      .hypothetical := by
  apply le_antisymm _ bot_le
  have bound := meetKinds_le_input (List.mem_map_of_mem
    (f := inputKind source history specs assumptions admitted hypothetical) used)
  rw [inputKind_hypothetical source history specs assumptions admitted hypothetical key slot] at bound
  exact bound

theorem nodeKind_missing_metadata (source : SourceInput) (history : ProcessHistory)
    (specs : List KindSpec) (assumptions : List CaptureAssumption)
    (admitted : List AdmissionBasis) (hypothetical : List KindKey)
    (argument : Presentation.ArgId) (term : Support.SupportTerm) (key : KindKey)
    (used : key ∈ .argument argument :: supportKeys term)
    (missing : specs.find? (fun spec => decide (spec.source = source ∧ spec.key = key)) = none) :
    (nodeKind source history specs assumptions admitted hypothetical argument term).2 = false := by
  apply Bool.eq_false_iff.mpr
  intro complete
  have all := (meetKinds_complete _).mp complete
  have one := all _ (List.mem_map_of_mem
    (f := inputKind source history specs assumptions admitted hypothetical) used)
  unfold inputKind at one
  rw [missing] at one
  cases one

end Lara.Process.Source
