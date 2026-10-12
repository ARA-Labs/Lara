import Lara.Process.SourceKinds

namespace Lara.Process.Source.KindTable

structure Row where
  key : KindKey
  value : EvidenceKind × Bool

abbrev Table := List Row

/-- Materialize source-local metadata in list order, retaining first-match semantics. -/
def build (source : SourceInput) (history : ProcessHistory)
    (specs : List KindSpec) (assumptions : List CaptureAssumption)
    (admitted : List AdmissionBasis) (hypothetical conditional : List KindKey) : Table :=
  match specs with
  | [] => []
  | spec :: rest =>
      let tail := build source history rest assumptions admitted hypothetical conditional
      if spec.source = source then
        let raw := kindFromSpec source history assumptions admitted hypothetical spec.key spec
        let value := (if spec.key ∈ conditional then raw.1 ⊓ EvidenceKind.conditional
          else raw.1, raw.2)
        ⟨spec.key, value⟩ :: tail
      else tail

def lookup : Table → KindKey → EvidenceKind × Bool
  | [], _ => (.hypothetical, false)
  | row :: rest, key => if row.key = key then row.value else lookup rest key

/-- The uncached source semantics, with the materialized conditional-slot cap. -/
def reference (source : SourceInput) (history : ProcessHistory)
    (specs : List KindSpec) (assumptions : List CaptureAssumption)
    (admitted : List AdmissionBasis) (hypothetical conditional : List KindKey)
    (key : KindKey) : EvidenceKind × Bool :=
  let raw := inputKind source history specs assumptions admitted hypothetical key
  (if key ∈ conditional then raw.1 ⊓ EvidenceKind.conditional else raw.1, raw.2)

/-- Equality holds even for duplicate metadata: both sides choose the first match. -/
theorem lookup_build (source : SourceInput) (history : ProcessHistory)
    (specs : List KindSpec) (assumptions : List CaptureAssumption)
    (admitted : List AdmissionBasis) (hypothetical conditional : List KindKey)
    (key : KindKey) :
    lookup (build source history specs assumptions admitted hypothetical conditional) key =
      reference source history specs assumptions admitted hypothetical conditional key := by
  induction specs with
  | nil =>
      simp [build, lookup, reference, inputKind]
      exact fun _ => bot_le
  | cons spec rest ih =>
      by_cases sourceMatch : spec.source = source
      · by_cases keyMatch : spec.key = key
        · simp [build, lookup, reference, inputKind, sourceMatch, keyMatch]
        · simpa [build, lookup, reference, inputKind, sourceMatch, keyMatch] using ih
      · simpa [build, reference, inputKind, sourceMatch] using ih

theorem lookup_build_no_promotion (source : SourceInput) (history : ProcessHistory)
    (specs : List KindSpec) (assumptions : List CaptureAssumption)
    (admitted : List AdmissionBasis) (hypothetical conditional : List KindKey)
    (key : KindKey) (slot : key ∈ hypothetical) :
    (lookup (build source history specs assumptions admitted hypothetical conditional) key).1 =
      .hypothetical := by
  rw [lookup_build]
  simp only [reference, inputKind_hypothetical source history specs assumptions admitted
    hypothetical key slot]
  split
  · exact le_antisymm inf_le_left bot_le
  · rfl

theorem lookup_build_conditional_cap (source : SourceInput) (history : ProcessHistory)
    (specs : List KindSpec) (assumptions : List CaptureAssumption)
    (admitted : List AdmissionBasis) (hypothetical conditional : List KindKey)
    (key : KindKey) (slot : key ∈ conditional) :
    (lookup (build source history specs assumptions admitted hypothetical conditional) key).1 ≤
      EvidenceKind.conditional := by
  rw [lookup_build]
  simp only [reference, if_pos slot]
  exact inf_le_right

theorem lookup_build_complete (source : SourceInput) (history : ProcessHistory)
    (specs : List KindSpec) (assumptions : List CaptureAssumption)
    (admitted : List AdmissionBasis) (hypothetical conditional : List KindKey)
    (key : KindKey) :
    (lookup (build source history specs assumptions admitted hypothetical conditional) key).2 =
      (inputKind source history specs assumptions admitted hypothetical key).2 := by
  rw [lookup_build]
  rfl

end Lara.Process.Source.KindTable
