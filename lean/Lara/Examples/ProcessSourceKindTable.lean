import Lara.Process.SourceKindTable

namespace Lara.Examples.ProcessSourceKindTable

open Lara.Process Lara.Process.Source

/-- A later duplicate cannot replace the first source-local metadata row. -/
example (source : SourceInput) (history : ProcessHistory) (key : KindKey)
    (assumptions : List CaptureAssumption) (admitted : List AdmissionBasis) :
    KindTable.lookup (KindTable.build source history
      [⟨source, key, .hypothetical, none⟩, ⟨source, key, .observed, none⟩]
      assumptions admitted [] []) key = (.hypothetical, true) := by
  simp [KindTable.build, KindTable.lookup, kindFromSpec]
  exact bot_le

/-- Foreign metadata is discarded before the matching local row is cached. -/
example (source foreign : SourceInput) (different : foreign ≠ source)
    (history : ProcessHistory) (key : KindKey) :
    KindTable.lookup (KindTable.build source history
      [⟨foreign, key, .hypothetical, none⟩, ⟨source, key, .observed, none⟩]
      [] [] [] []) key = (.conditional, true) := by
  simp [KindTable.build, KindTable.lookup, kindFromSpec, different]
  exact le_top

/-- Missing metadata remains incomplete even when the key is conditional. -/
example (source : SourceInput) (history : ProcessHistory) (key : KindKey) :
    KindTable.lookup (KindTable.build source history [] [] [] [] [key]) key =
      (.hypothetical, false) := by
  rfl

end Lara.Examples.ProcessSourceKindTable
