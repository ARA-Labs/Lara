import Lara.Process.SourceLedger

/-! Exact-rational source ledger checks over modeled histories. The outcome label
is held fixed while the supplied statistic metadata changes; it is not a statistic. -/

namespace Lara.Process.Source.LedgerExamples

private def runEvent : Stamped := ⟨⟨0⟩, .run ⟨0⟩ ⟨0⟩ ⟨0⟩ [] ⟨0⟩⟩
private def resultEvent : Stamped := ⟨⟨1⟩, .result ⟨0⟩ 7⟩
private def history : ProcessHistory := [runEvent, resultEvent]
private def pBinding : LedgerBinding :=
  ⟨⟨0⟩, ⟨0⟩, 7, ⟨some .pValue, some (1 / 40), some 2, some .fwer⟩⟩
private def eBinding : LedgerBinding :=
  { pBinding with ledger := ⟨some .eValue, some 60, some 2, some .fwer⟩ }

 theorem pValue_exact_level : observeLedger history pBinding = .ok (.fwer, 1 / 20) := by
  decide +kernel

 theorem eValue_exact_level : observeLedger history eBinding = .ok (.fwer, 1 / 30) := by
  decide +kernel

 theorem missing_kind : observeLedger history
    { pBinding with ledger := { pBinding.ledger with kind := none } } = .error .missingKind := by
  decide +kernel

 theorem missing_value : observeLedger history
    { pBinding with ledger := { pBinding.ledger with value := none } } = .error .missingValue := by
  decide +kernel

 theorem missing_guarantee : observeLedger history
    { pBinding with ledger := { pBinding.ledger with guarantee := none } } =
      .error .missingGuarantee := by
  decide +kernel

 theorem missing_bound : observeLedger history
    { pBinding with ledger := { pBinding.ledger with countBound := none } } =
      .error .missingBound := by
  decide +kernel

 theorem zero_bound : observeLedger history
    { pBinding with ledger := { pBinding.ledger with countBound := some 0 } } =
      .error .zeroBound := by
  decide +kernel

 theorem fdr_not_fwer : observeLedger history
    { pBinding with ledger := { pBinding.ledger with guarantee := some .fdr } } =
      .error .unsupportedGuarantee := by
  decide +kernel

 theorem mfdr_not_fwer : observeLedger history
    { pBinding with ledger := { pBinding.ledger with guarantee := some .mfdr } } =
      .error .unsupportedGuarantee := by
  decide +kernel

 theorem absent_run : observeLedger [resultEvent] pBinding = .error .absentRun := by
  decide +kernel

 theorem absent_result : observeLedger [runEvent] pBinding = .error .absentResult := by
  decide +kernel

 theorem wrong_family : observeLedger history { pBinding with family := ⟨1⟩ } =
    .error .familyMismatch := by
  decide +kernel

 theorem wrong_outcome : observeLedger history { pBinding with outcome := 8 } =
    .error .absentResult := by
  decide +kernel

 theorem zero_statistic : observeLedger history
    { eBinding with ledger := { eBinding.ledger with value := some 0 } } =
      .error .nonFiniteLevel := by
  decide +kernel

 theorem negative_statistic : observeLedger history
    { pBinding with ledger := { pBinding.ledger with value := some (-1) } } =
      .error .nonFiniteLevel := by
  decide +kernel

private def tightBinding : LedgerBinding :=
  { pBinding with ledger := { pBinding.ledger with countBound := some 1 } }
private def failedSibling : Stamped := ⟨⟨2⟩, .run ⟨1⟩ ⟨0⟩ ⟨0⟩ [] ⟨0⟩⟩
private def extended : ProcessHistory := history ++ [failedSibling]

/-- A hidden sibling with no result consumes the same bound without changing
any supplied statistic or the selected run's exact result event. -/
 theorem hidden_failed_sibling_invalidates :
    observeLedger history tightBinding = .ok (.fwer, 1 / 40) ∧
      familyCount history tightBinding.family = 1 ∧
      familyCount extended tightBinding.family = 2 ∧
      observeLedger extended tightBinding = .error .exceededBound ∧
      resultEvent ∈ extended := by
  decide +kernel

 theorem failed_result_still_counts :
    familyCount (extended ++ [⟨⟨3⟩, .result ⟨1⟩ 0⟩]) tightBinding.family = 2 ∧
      observeLedger (extended ++ [⟨⟨3⟩, .result ⟨1⟩ 0⟩]) tightBinding =
        .error .exceededBound := by
  decide +kernel

 theorem other_family_does_not_consume_bound :
    observeLedger (history ++ [⟨⟨2⟩, .run ⟨1⟩ ⟨0⟩ ⟨0⟩ [] ⟨1⟩⟩]) tightBinding =
      .ok (.fwer, 1 / 40) := by
  decide +kernel

end Lara.Process.Source.LedgerExamples
