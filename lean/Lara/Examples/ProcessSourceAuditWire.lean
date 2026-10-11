import Lara.Process.SourceAuditWire
import Lara.Examples.ProcessSourceKinds

namespace Lara.Examples.ProcessSourceAuditWire
open Lara Lara.Process Lara.Process.Source Lara.Process.Source.AuditWire

example (q : ℚ) : AuditWire.decodeRat (AuditWire.encodeRat q) = some q :=
  AuditWire.decode_encodeRat q

example (fault : WitnessFault) :
    AuditWire.decodeWitnessFault (AuditWire.encodeWitnessFault fault) = some fault :=
  AuditWire.decode_encodeWitnessFault fault

def names : Process.Wire.Names :=
  ⟨["event"], ["actor"], ["plan"], ["run"], ["claim"], ["source"], ["data"],
    ["family"], ["witness"]⟩

theorem names_unique : InquiryProcessWire.UniqueNames names := by
  simp [InquiryProcessWire.UniqueNames, names]

def claim : ClaimBinding := ⟨⟨0⟩, ⟨"claim"⟩, .atom "query" (.cons (.num "1") .nil)⟩
def dependency : SupportBinding := ⟨⟨"argument"⟩, claim.query⟩
def method : MethodBinding :=
  ⟨.conditionalFalse, .applied, -7, true, false,
    [.runtimeRefinement, .captureAdequacy, .physicalSampling, .interpretationFidelity,
      .runtimeRefinement]⟩
def ledger : Statistics.Ledger := ⟨some .eValue, some (-3 / 7), some 0, some .fdr⟩
def emptyLedger : Statistics.Ledger := ⟨none, none, none, none⟩
def binding : LedgerBinding := ⟨⟨0⟩, ⟨0⟩, 23, ledger⟩
def witness : WitnessSpec :=
  ⟨⟨0⟩, ⟨0⟩, ProcessSourceKinds.source,
    ⟨⟨"argument"⟩, [dependency, dependency], .checkedMethod method⟩,
    [.sampling, .selection, .sampling], .ledger binding⟩
def conditionalWitness : WitnessSpec :=
  { witness with
    artifact := ⟨⟨"argument"⟩, [], .declared ⟨123⟩⟩
    guarantee := .conditional .fwer (-5 / 2) }
def assumption : CaptureAssumption :=
  ⟨⟨19⟩, ProcessSourceKinds.source, .method ⟨"method"⟩,
    ProcessSourceKinds.runEvent, ⟨0⟩, .signedAttestation⟩

/-- Duplicate metadata and invalid statistical inputs are deliberately retained. -/
def config : AuditConfig :=
  ⟨[claim, claim], [witness, conditionalWitness, witness],
    [⟨ProcessSourceKinds.source, .leaf ⟨"leaf"⟩, .observed, some ⟨19⟩⟩,
      ⟨ProcessSourceKinds.source, .argument ⟨"argument"⟩, .hypothetical, none⟩],
    [assumption, assumption]⟩

theorem config_named : ConfigWellNamed names config := by
  simp [ConfigWellNamed, ClaimBindingWellNamed, WitnessSpecWellNamed,
    GuaranteeBindingWellNamed, LedgerBindingWellNamed, CaptureAssumptionWellNamed,
    InquiryProcessWire.StampedWellNamed, InquiryProcessWire.EventWellNamed,
    config, claim, witness, conditionalWitness, binding, assumption,
    ProcessSourceKinds.runEvent, names]

theorem full_config_roundtrip : decodeConfig names (encodeConfig names config) = some config :=
  decode_encodeConfig names names_unique config config_named

theorem invalid_config_preserved :
    decodeConfig names (encodeConfig names config) = some config ∧
      config.wellFormed = false := by
  exact ⟨full_config_roundtrip, by simp [AuditConfig.wellFormed, config]⟩

theorem negative_conditional_preserved :
    decodeGuaranteeBinding names (encodeGuaranteeBinding names (.conditional .fwer (-5 / 2))) =
      some (.conditional .fwer (-5 / 2)) :=
  decode_encodeGuaranteeBinding names names_unique _ trivial

theorem negative_conditional_rejected :
    (checkGuarantee [] (.conditional .fwer (-5 / 2))).isOk = false := by
  norm_num [checkGuarantee, Except.isOk]
  rfl

theorem every_optional_ledger_field (kind : Option Statistics.StatKind) (value : Option ℚ)
    (count : Option Nat) (guarantee : Option GuaranteeClass) :
    decodeLedger (encodeLedger ⟨kind, value, count, guarantee⟩) =
      some ⟨kind, value, count, guarantee⟩ := decode_encodeLedger _

theorem absent_present_distinct :
    encodeLedger emptyLedger ≠ encodeLedger { emptyLedger with value := some 0 } := by
  intro h
  have equal := encodeLedger_injective h
  cases equal

theorem same_digest_stale_pin_distinct :
    ProcessSourceKinds.source.surface.program.digest =
      ProcessSourceKinds.staleSource.surface.program.digest ∧
    encodeWitnessSpec names witness ≠
      encodeWitnessSpec names { witness with source := ProcessSourceKinds.staleSource } := by
  constructor
  · rfl
  · intro h
    have equal := encodeWitnessSpec_injective names names_unique
      (a := witness) (b := { witness with source := ProcessSourceKinds.staleSource })
      (by simp [WitnessSpecWellNamed, GuaranteeBindingWellNamed,
        LedgerBindingWellNamed, witness, binding, names])
      (by simp [WitnessSpecWellNamed, GuaranteeBindingWellNamed,
        LedgerBindingWellNamed, witness, binding, names]) h
    have pin := congrArg (fun w => w.source.surface.program.artifact) equal
    have : ProcessSourceKinds.source.surface.program.artifact = "different-source" := pin
    contradiction

def nestedError : WitnessFault := .artifact (.support ⟨"argument"⟩
  (.inference (.R1 (.premise (.question .root ⟨"why"⟩) 7) (.missingLeaf ⟨"leaf"⟩))))
theorem nested_error_roundtrip :
    decodeWitnessFault (encodeWitnessFault nestedError) = some nestedError :=
  decode_encodeWitnessFault _

theorem nested_application_error_roundtrip :
    decodeWitnessFault (encodeWitnessFault
      (.artifact (.method (.application .failedPrecondition)))) =
      some (.artifact (.method (.application .failedPrecondition))) :=
  decode_encodeWitnessFault _

theorem malformed_config_arity :
    decodeConfig names (tagged .auditConfig []) = none := rfl
theorem malformed_fault_arity :
    decodeWitnessFault (tagged .artifact []) = none := rfl
theorem noncanonical_assumption_id :
    decodeAssumptionId (tagged .assumptionId [.atom "01"]) = none := by
  simp [decodeAssumptionId, Wire.canonical, decodeAssumptionIdRaw, tagged,
    ResultWire.decodeNat, ND.decodeNat_leading_zero_01]

def allMethods : List BHL.CheckedMethods.Method :=
  [.two, .low, .up, .disjunction, .conjunction, .conditionalFalse]
def allLedgers : List Statistics.Ledger := do
  let kind ← [none, some .pValue, some .eValue]
  let value ← [none, some (-3 / 7), some 0, some (5 / 2)]
  let count ← [none, some 0, some 3]
  let guarantee ← [none, some .fwer, some .fdr, some .mfdr]
  pure ⟨kind, value, count, guarantee⟩
def malformed : List Driver.Sx :=
  [tagged .rational [encodeInt 1, .atom "0"],
    tagged .rational [encodeInt 1, .atom "01"],
    tagged .rational [encodeInt 2, .atom "4"],
    tagged .rational [encodeInt 0, .atom "2"],
    tagged .rational [.atom "-0", .atom "1"],
    tagged .rational [encodeInt 1],
    tagged .rational [encodeInt 1, .atom "-1"],
    tagged .rational [encodeInt 1, .atom "1", .atom "extra"]]

def smoke : IO _root_.Unit := do
  let checks : List (String × Bool) :=
    [("full-config", decide (decodeConfig names (encodeConfig names config) = some config)),
      ("duplicate-metadata-retained", !config.wellFormed),
      ("stale-pin-same-digest",
        decide (ProcessSourceKinds.source.surface.program.digest =
          ProcessSourceKinds.staleSource.surface.program.digest) &&
        decide (encodeWitnessSpec names witness ≠
          encodeWitnessSpec names { witness with source := ProcessSourceKinds.staleSource })),
      ("all-optional-ledger-fields", allLedgers.all fun l =>
        decide (decodeLedger (encodeLedger l) = some l)),
      ("negative-and-out-of-range-rationals", ([-5 / 2, 0, 1 / 3, 5 / 2] : List ℚ).all
        fun q => decide (decodeRat (encodeRat q) = some q)),
      ("all-methods-and-modes", allMethods.all fun m =>
        [BHL.PayloadMode.conditional, .applied].all fun mode =>
          let b := { method with method := m, mode }
          decide (decodeMethodBinding (encodeMethodBinding b) = some b)),
      ("nested-errors", decide
        (decodeWitnessFault (encodeWitnessFault nestedError) = some nestedError)),
      ("provenance-reference", decide (decodeProvenanceError
        (encodeProvenanceError (.unresolvedReference ⟨"reference"⟩)) =
          some (.unresolvedReference ⟨"reference"⟩))),
      ("malformed-noncanonical", malformed.all fun sx => (decodeRat sx).isNone),
      ("invalid-conditional-semantic-rejection",
        !(checkGuarantee [] conditionalWitness.guarantee).isOk)]
  for (label, passed) in checks do
    if !passed then throw (IO.userError s!"source-audit-wire: FAIL {label}")
    IO.println s!"source-audit-wire: PASS {label}"

#eval smoke

end Lara.Examples.ProcessSourceAuditWire
