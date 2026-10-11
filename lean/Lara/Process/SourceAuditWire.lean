import Lara.Process.SourceAudit
import Lara.Process.SourceProvenance
import Lara.Process.SourceResultWire
import Lara.Process.InquiryProcessWire

/-! Typed checked-source audit payloads. Decoding checks framing, never semantic
validity: duplicate rows, stale pins, negative levels and missing ledger fields
remain available to the semantic validators. Process identities reuse P0 names. -/
namespace Lara.Process.Source.AuditWire
open Lara.Driver (Sx)
open InquiryProcessWire (UniqueNames StampedWellNamed)
set_option maxRecDepth 4096

inductive Tag where
  | rational | none | some | two | low | up | disjunction | conjunction | conditionalFalse | conditional | applied | interpretationFidelity | physicalSampling | captureAdequacy | runtimeRefinement | pValue | eValue | inputClaim | semanticClaim | missingDeclaration | wrongArgument | notAlternative | absentRun | familyMismatch | absentResult | missingKind | missingValue | missingGuarantee | missingBound | zeroBound | unsupportedGuarantee | exceededBound | nonFiniteLevel | modelMismatch | premiseMismatch | programMismatch | postconditionMismatch | runMismatch | failedPrecondition | staleSnapshot | incompatibleInterpretation | incompatibleMethod | incompatibleClaim | incompatibleDependencies | incompatibleEvidence | incompatibleBinding | missingSupport | blockedSupport | defeatedSupport | failedDerivation | falsePrecondition | application | absent | differentConclusion | notRetained | absentNode | nodeMismatch | blocked | inference | incomplete | support | association | method | invalidConditionalLevel | ledger | missingClaim | missingWitness | ambiguousMetadata | wrongClaim | staleSource | artifact | guarantee | shape | implicitMatch | missingRule | unresolvedReference | missingArgument | duplicateArgument | missingNode | assumptionId | interpretationId | leaf | argument | supportBinding | methodBinding | declared | checkedMethod | artifactSpec | ledgerFields | kindSpec | claimBinding | ledgerBinding | witnessSpec | captureAssumption | auditConfig
  deriving DecidableEq, Repr

def Tag.text : Tag → String
  | .rational => "rational"
  | .none => Driver.tagToString .nonE
  | .some => "some"
  | .two => "two"
  | .low => "low"
  | .up => "up"
  | .disjunction => "disjunction"
  | .conjunction => "conjunction"
  | .conditionalFalse => "conditional-false"
  | .conditional => EvidenceKind.label .conditional
  | .applied => "applied"
  | .interpretationFidelity => "interpretation-fidelity"
  | .physicalSampling => "physical-sampling"
  | .captureAdequacy => "capture-adequacy"
  | .runtimeRefinement => "runtime-refinement"
  | .pValue => "p-value"
  | .eValue => "e-value"
  | .inputClaim => "input-claim"
  | .semanticClaim => "semantic-claim"
  | .missingDeclaration => "missing-declaration"
  | .wrongArgument => "wrong-argument"
  | .notAlternative => "not-alternative"
  | .absentRun => "absent-run"
  | .familyMismatch => "family-mismatch"
  | .absentResult => "absent-result"
  | .missingKind => "missing-kind"
  | .missingValue => "missing-value"
  | .missingGuarantee => "missing-guarantee"
  | .missingBound => "missing-bound"
  | .zeroBound => "zero-bound"
  | .unsupportedGuarantee => "unsupported-guarantee"
  | .exceededBound => "exceeded-bound"
  | .nonFiniteLevel => "non-finite-level"
  | .modelMismatch => "model-mismatch"
  | .premiseMismatch => "premise-mismatch"
  | .programMismatch => "program-mismatch"
  | .postconditionMismatch => "postcondition-mismatch"
  | .runMismatch => "run-mismatch"
  | .failedPrecondition => "failed-precondition"
  | .staleSnapshot => "stale-snapshot"
  | .incompatibleInterpretation => "incompatible-interpretation"
  | .incompatibleMethod => "incompatible-method"
  | .incompatibleClaim => "incompatible-claim"
  | .incompatibleDependencies => "incompatible-dependencies"
  | .incompatibleEvidence => "incompatible-evidence"
  | .incompatibleBinding => "incompatible-binding"
  | .missingSupport => "missing-support"
  | .blockedSupport => "blocked-support"
  | .defeatedSupport => "defeated-support"
  | .failedDerivation => "failed-derivation"
  | .falsePrecondition => "false-precondition"
  | .application => "application"
  | .absent => Wire.Tag.absent.text
  | .differentConclusion => "different-conclusion"
  | .notRetained => "not-retained"
  | .absentNode => "absent-node"
  | .nodeMismatch => "node-mismatch"
  | .blocked => "blocked"
  | .inference => "inference"
  | .incomplete => "incomplete"
  | .support => "support"
  | .association => "association"
  | .method => "method"
  | .invalidConditionalLevel => "invalid-conditional-level"
  | .ledger => "ledger"
  | .missingClaim => "missing-claim"
  | .missingWitness => "missing-witness"
  | .ambiguousMetadata => "ambiguous-metadata"
  | .wrongClaim => "wrong-claim"
  | .staleSource => "stale-source"
  | .artifact => "artifact"
  | .guarantee => Process.Wire.Tag.guarantee.text
  | .shape => "shape"
  | .implicitMatch => "implicit-match"
  | .missingRule => ResultWire.Tag.missingRule.text
  | .unresolvedReference => "unresolved-reference"
  | .missingArgument => "missing-argument"
  | .duplicateArgument => ResultWire.Tag.duplicateArgument.text
  | .missingNode => "missing-node"
  | .assumptionId => "assumption-id"
  | .interpretationId => "interpretation-id"
  | .leaf => Driver.tagToString .leaf
  | .argument => ResultWire.Tag.argument.text
  | .supportBinding => "support-binding"
  | .methodBinding => "method-binding"
  | .declared => "declared"
  | .checkedMethod => "checked-method"
  | .artifactSpec => "artifact-spec"
  | .ledgerFields => "ledger-fields"
  | .kindSpec => "kind-spec"
  | .claimBinding => "claim-binding"
  | .ledgerBinding => "ledger-binding"
  | .witnessSpec => "witness-spec"
  | .captureAssumption => "capture-assumption"
  | .auditConfig => "audit-config"
def Tag.all : List Tag := [.rational, .none, .some, .two, .low, .up, .disjunction, .conjunction, .conditionalFalse, .conditional, .applied, .interpretationFidelity, .physicalSampling, .captureAdequacy, .runtimeRefinement, .pValue, .eValue, .inputClaim, .semanticClaim, .missingDeclaration, .wrongArgument, .notAlternative, .absentRun, .familyMismatch, .absentResult, .missingKind, .missingValue, .missingGuarantee, .missingBound, .zeroBound, .unsupportedGuarantee, .exceededBound, .nonFiniteLevel, .modelMismatch, .premiseMismatch, .programMismatch, .postconditionMismatch, .runMismatch, .failedPrecondition, .staleSnapshot, .incompatibleInterpretation, .incompatibleMethod, .incompatibleClaim, .incompatibleDependencies, .incompatibleEvidence, .incompatibleBinding, .missingSupport, .blockedSupport, .defeatedSupport, .failedDerivation, .falsePrecondition, .application, .absent, .differentConclusion, .notRetained, .absentNode, .nodeMismatch, .blocked, .inference, .incomplete, .support, .association, .method, .invalidConditionalLevel, .ledger, .missingClaim, .missingWitness, .ambiguousMetadata, .wrongClaim, .staleSource, .artifact, .guarantee, .shape, .implicitMatch, .missingRule, .unresolvedReference, .missingArgument, .duplicateArgument, .missingNode, .assumptionId, .interpretationId, .leaf, .argument, .supportBinding, .methodBinding, .declared, .checkedMethod, .artifactSpec, .ledgerFields, .kindSpec, .claimBinding, .ledgerBinding, .witnessSpec, .captureAssumption, .auditConfig]
def Tag.spelling : Process.Wire.Spelling Tag := ⟨Tag.all, Tag.text⟩
def Tag.parse := Tag.spelling.parse
theorem Tag.spelling_complete (tag : Tag) : tag ∈ Tag.all := by
  cases tag <;> decide
theorem Tag.spelling_nodup : (Tag.all.map Tag.text).Nodup := by decide
@[simp] theorem Tag.parse_text (tag : Tag) : Tag.parse tag.text = Option.some tag :=
  Tag.spelling.parse_text Tag.spelling_complete Tag.spelling_nodup tag
theorem Tag.parse_some {text : String} {tag : Tag} (h : Tag.parse text = Option.some tag) :
    tag.text = text := Tag.spelling.parse_some h
theorem Tag.text_injective : Function.Injective Tag.text :=
  Tag.spelling.text_injective Tag.spelling_complete Tag.spelling_nodup

def tagged (tag : Tag) (xs : List Sx) : Sx := .list (.atom tag.text :: xs)

@[simp] theorem toOption_ok (a : α) : (Except.ok a : Except ε α).toOption = some a := rfl

def encodeOption (encode : α → Sx) : Option α → Sx
  | none => tagged .none []
  | some a => tagged .some [encode a]
def decodeOption (decode : Sx → Option α) : Sx → Option (Option α)
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .none, [] => some none
    | some .some, [a] => do return some (← decode a)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeOption (e : α → Sx) (d : Sx → Option α)
    (h : ∀ a, d (e a) = some a) (a : Option α) :
    decodeOption d (encodeOption e a) = some a := by
  cases a <;> simp [decodeOption, encodeOption, tagged, h]

abbrev encodeSource := Wire.encode
abbrev decodeSource := Wire.decode

def encodeInt (value : Int) : Sx := Wire.encodePresentation (.int value)
def decodeInt (wire : Sx) : Option Int := do
  match ← Wire.decodePresentationStrict wire with
  | .int value => some value
  | _ => none
@[simp] theorem decode_encodeInt (value : Int) : decodeInt (encodeInt value) = some value := by
  simp [encodeInt, decodeInt]
theorem decodeInt_canonical {wire : Sx} {value : Int}
    (h : decodeInt wire = some value) : encodeInt value = wire := by
  unfold decodeInt at h
  cases parsed : Wire.decodePresentationStrict wire with
  | none => simp [parsed] at h
  | some sx =>
    cases sx with
    | str text => simp [parsed] at h
    | node tag children => simp [parsed] at h
    | int i =>
      have equal : i = value := by simpa [parsed] using h
      subst i
      exact Wire.decodePresentationStrict_canonical parsed
theorem encodeInt_injective : Function.Injective encodeInt :=
  Wire.injective_of_roundtrip _ _ decode_encodeInt

def encodeRat (value : ℚ) : Sx := tagged .rational
  [encodeInt value.num, ResultWire.encodeNat value.den]
def decodeRatRaw : Sx → Option ℚ
  | .list [.atom t, num, den] => match Tag.parse t with
    | some .rational => do
      let num ← decodeInt num
      let den ← ResultWire.decodeNat den
      if den = 0 then none else some (num / (den : ℚ))
    | _ => none
  | _ => none
def decodeRat := Wire.canonical encodeRat decodeRatRaw
@[simp] theorem decode_encodeRat (value : ℚ) : decodeRat (encodeRat value) = some value := by
  apply Wire.canonical_roundtrip
  intro q
  simp [decodeRatRaw, encodeRat, tagged, Rat.den_ne_zero, Rat.num_div_den]
theorem decodeRat_canonical {wire : Sx} {value : ℚ}
    (h : decodeRat wire = some value) : encodeRat value = wire := Wire.canonical_sound _ _ h
theorem encodeRat_injective : Function.Injective encodeRat :=
  Wire.injective_of_roundtrip _ _ decode_encodeRat

def encodeBool : Bool → Sx
  | false => .atom (Driver.tagToString .falsE)
  | true => .atom (Driver.tagToString .truE)
def decodeBool : Sx → Option Bool
  | .atom s => if s = Driver.tagToString .falsE then some false else
      if s = Driver.tagToString .truE then some true else none
  | _ => none
@[simp] theorem decode_encodeBool (b : Bool) : decodeBool (encodeBool b) = some b := by
  cases b <;> rfl

def encodeArgRef (value : Presentation.ArgRef) : Sx := .atom value.val
def decodeArgRef : Sx → Option Presentation.ArgRef
  | .atom s => some ⟨s⟩
  | _ => none
@[simp] theorem decode_encodeArgRef (value : Presentation.ArgRef) :
    decodeArgRef (encodeArgRef value) = some value := rfl

def encodeGuaranteeClass (value : GuaranteeClass) : Sx := .atom (Process.Wire.GuaranteeClass.spelling.text value)
def decodeGuaranteeClass (wire : Sx) : Option GuaranteeClass :=
  (Process.Wire.decodeWord Process.Wire.GuaranteeClass.spelling "-guarantee-class" wire).toOption
@[simp] theorem decode_encodeGuaranteeClass (value : GuaranteeClass) :
    decodeGuaranteeClass (encodeGuaranteeClass value) = some value := by
  simp [encodeGuaranteeClass, decodeGuaranteeClass, InquiryProcessWire.decode_encodeWord _
    Process.Wire.GuaranteeClass.spelling_complete Process.Wire.GuaranteeClass.spelling_nodup]

def encodeEvidenceKind (value : EvidenceKind) : Sx := .atom (Process.Wire.EvidenceKind.spelling.text value)
def decodeEvidenceKind (wire : Sx) : Option EvidenceKind :=
  (Process.Wire.decodeWord Process.Wire.EvidenceKind.spelling "-evidence-kind" wire).toOption
@[simp] theorem decode_encodeEvidenceKind (value : EvidenceKind) :
    decodeEvidenceKind (encodeEvidenceKind value) = some value := by
  simp [encodeEvidenceKind, decodeEvidenceKind, InquiryProcessWire.decode_encodeWord _
    Process.Wire.EvidenceKind.spelling_complete Process.Wire.EvidenceKind.spelling_nodup]

def encodeErrorKind (value : ErrorKind) : Sx := .atom (Process.Wire.ErrorKind.spelling.text value)
def decodeErrorKind (wire : Sx) : Option ErrorKind :=
  (Process.Wire.decodeWord Process.Wire.ErrorKind.spelling "-error-kind" wire).toOption
@[simp] theorem decode_encodeErrorKind (value : ErrorKind) :
    decodeErrorKind (encodeErrorKind value) = some value := by
  simp [encodeErrorKind, decodeErrorKind, InquiryProcessWire.decode_encodeWord _
    Process.Wire.ErrorKind.spelling_complete Process.Wire.ErrorKind.spelling_nodup]

def encodeAdmissionBasis (value : AdmissionBasis) : Sx := .atom (Process.Wire.AdmissionBasis.spelling.text value)
def decodeAdmissionBasis (wire : Sx) : Option AdmissionBasis :=
  (Process.Wire.decodeWord Process.Wire.AdmissionBasis.spelling "-admission-basis" wire).toOption
@[simp] theorem decode_encodeAdmissionBasis (value : AdmissionBasis) :
    decodeAdmissionBasis (encodeAdmissionBasis value) = some value := by
  simp [encodeAdmissionBasis, decodeAdmissionBasis, InquiryProcessWire.decode_encodeWord _
    Process.Wire.AdmissionBasis.spelling_complete Process.Wire.AdmissionBasis.spelling_nodup]

def encodeClaimId (n : Process.Wire.Names) (value : ClaimId) : Sx :=
  Process.Wire.encodeIdx n.claim value.index
def decodeClaimId (n : Process.Wire.Names) (wire : Sx) : Option ClaimId :=
  (Process.Wire.decodeIdx n.claim "claim" wire).toOption.map ClaimId.mk
def encodeWitnessId (n : Process.Wire.Names) (value : WitnessId) : Sx :=
  Process.Wire.encodeIdx n.witness value.index
def decodeWitnessId (n : Process.Wire.Names) (wire : Sx) : Option WitnessId :=
  (Process.Wire.decodeIdx n.witness "witness" wire).toOption.map WitnessId.mk
def encodeRunId (n : Process.Wire.Names) (value : RunId) : Sx :=
  Process.Wire.encodeIdx n.run value.index
def decodeRunId (n : Process.Wire.Names) (wire : Sx) : Option RunId :=
  (Process.Wire.decodeIdx n.run "run" wire).toOption.map RunId.mk
def encodeFamilyId (n : Process.Wire.Names) (value : FamilyId) : Sx :=
  Process.Wire.encodeIdx n.family value.index
def decodeFamilyId (n : Process.Wire.Names) (wire : Sx) : Option FamilyId :=
  (Process.Wire.decodeIdx n.family "family" wire).toOption.map FamilyId.mk
abbrev encodeStamped := Process.Wire.encodeStamped
def decodeStamped (n : Process.Wire.Names) (wire : Sx) : Option Stamped :=
  (Process.Wire.decodeStamped n wire).toOption

def encodeMethod : BHL.CheckedMethods.Method → Sx
  | .two => tagged .two []
  | .low => tagged .low []
  | .up => tagged .up []
  | .disjunction => tagged .disjunction []
  | .conjunction => tagged .conjunction []
  | .conditionalFalse => tagged .conditionalFalse []
def decodeMethodRaw : Sx → Option BHL.CheckedMethods.Method
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .two, [] => some .two
    | some .low, [] => some .low
    | some .up, [] => some .up
    | some .disjunction, [] => some .disjunction
    | some .conjunction, [] => some .conjunction
    | some .conditionalFalse, [] => some .conditionalFalse
    | _, _ => none
  | _ => none
def decodeMethod := Wire.canonical (encodeMethod) (decodeMethodRaw)
@[simp] theorem decode_encodeMethod (value : BHL.CheckedMethods.Method) :
    decodeMethod (encodeMethod value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x <;> simp [encodeMethod, decodeMethodRaw, tagged]
theorem encodeMethod_injective : Function.Injective encodeMethod :=
  Wire.injective_of_roundtrip _ _ decode_encodeMethod
theorem decodeMethod_canonical {wire : Sx} {value : BHL.CheckedMethods.Method}
    (h : decodeMethod wire = some value) : encodeMethod value = wire :=
  Wire.canonical_sound _ _ h

def encodePayloadMode : BHL.PayloadMode → Sx
  | .conditional => tagged .conditional []
  | .applied => tagged .applied []
def decodePayloadModeRaw : Sx → Option BHL.PayloadMode
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .conditional, [] => some .conditional
    | some .applied, [] => some .applied
    | _, _ => none
  | _ => none
def decodePayloadMode := Wire.canonical (encodePayloadMode) (decodePayloadModeRaw)
@[simp] theorem decode_encodePayloadMode (value : BHL.PayloadMode) :
    decodePayloadMode (encodePayloadMode value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x <;> simp [encodePayloadMode, decodePayloadModeRaw, tagged]
theorem encodePayloadMode_injective : Function.Injective encodePayloadMode :=
  Wire.injective_of_roundtrip _ _ decode_encodePayloadMode
theorem decodePayloadMode_canonical {wire : Sx} {value : BHL.PayloadMode}
    (h : decodePayloadMode wire = some value) : encodePayloadMode value = wire :=
  Wire.canonical_sound _ _ h

def encodeResidualAssumption : BHL.ResidualAssumption → Sx
  | .interpretationFidelity => tagged .interpretationFidelity []
  | .physicalSampling => tagged .physicalSampling []
  | .captureAdequacy => tagged .captureAdequacy []
  | .runtimeRefinement => tagged .runtimeRefinement []
def decodeResidualAssumptionRaw : Sx → Option BHL.ResidualAssumption
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .interpretationFidelity, [] => some .interpretationFidelity
    | some .physicalSampling, [] => some .physicalSampling
    | some .captureAdequacy, [] => some .captureAdequacy
    | some .runtimeRefinement, [] => some .runtimeRefinement
    | _, _ => none
  | _ => none
def decodeResidualAssumption := Wire.canonical (encodeResidualAssumption) (decodeResidualAssumptionRaw)
@[simp] theorem decode_encodeResidualAssumption (value : BHL.ResidualAssumption) :
    decodeResidualAssumption (encodeResidualAssumption value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x <;> simp [encodeResidualAssumption, decodeResidualAssumptionRaw, tagged]
theorem encodeResidualAssumption_injective : Function.Injective encodeResidualAssumption :=
  Wire.injective_of_roundtrip _ _ decode_encodeResidualAssumption
theorem decodeResidualAssumption_canonical {wire : Sx} {value : BHL.ResidualAssumption}
    (h : decodeResidualAssumption wire = some value) : encodeResidualAssumption value = wire :=
  Wire.canonical_sound _ _ h

def encodeStatKind : Statistics.StatKind → Sx
  | .pValue => tagged .pValue []
  | .eValue => tagged .eValue []
def decodeStatKindRaw : Sx → Option Statistics.StatKind
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .pValue, [] => some .pValue
    | some .eValue, [] => some .eValue
    | _, _ => none
  | _ => none
def decodeStatKind := Wire.canonical (encodeStatKind) (decodeStatKindRaw)
@[simp] theorem decode_encodeStatKind (value : Statistics.StatKind) :
    decodeStatKind (encodeStatKind value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x <;> simp [encodeStatKind, decodeStatKindRaw, tagged]
theorem encodeStatKind_injective : Function.Injective encodeStatKind :=
  Wire.injective_of_roundtrip _ _ decode_encodeStatKind
theorem decodeStatKind_canonical {wire : Sx} {value : Statistics.StatKind}
    (h : decodeStatKind wire = some value) : encodeStatKind value = wire :=
  Wire.canonical_sound _ _ h

def encodeAssociationFault : AssociationFault → Sx
  | .inputClaim => tagged .inputClaim []
  | .semanticClaim => tagged .semanticClaim []
  | .missingDeclaration => tagged .missingDeclaration []
  | .wrongArgument => tagged .wrongArgument []
  | .notAlternative => tagged .notAlternative []
def decodeAssociationFaultRaw : Sx → Option AssociationFault
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .inputClaim, [] => some .inputClaim
    | some .semanticClaim, [] => some .semanticClaim
    | some .missingDeclaration, [] => some .missingDeclaration
    | some .wrongArgument, [] => some .wrongArgument
    | some .notAlternative, [] => some .notAlternative
    | _, _ => none
  | _ => none
def decodeAssociationFault := Wire.canonical (encodeAssociationFault) (decodeAssociationFaultRaw)
@[simp] theorem decode_encodeAssociationFault (value : AssociationFault) :
    decodeAssociationFault (encodeAssociationFault value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x <;> simp [encodeAssociationFault, decodeAssociationFaultRaw, tagged]
theorem encodeAssociationFault_injective : Function.Injective encodeAssociationFault :=
  Wire.injective_of_roundtrip _ _ decode_encodeAssociationFault
theorem decodeAssociationFault_canonical {wire : Sx} {value : AssociationFault}
    (h : decodeAssociationFault wire = some value) : encodeAssociationFault value = wire :=
  Wire.canonical_sound _ _ h

def encodeLedgerFault : LedgerFault → Sx
  | .absentRun => tagged .absentRun []
  | .familyMismatch => tagged .familyMismatch []
  | .absentResult => tagged .absentResult []
  | .missingKind => tagged .missingKind []
  | .missingValue => tagged .missingValue []
  | .missingGuarantee => tagged .missingGuarantee []
  | .missingBound => tagged .missingBound []
  | .zeroBound => tagged .zeroBound []
  | .unsupportedGuarantee => tagged .unsupportedGuarantee []
  | .exceededBound => tagged .exceededBound []
  | .nonFiniteLevel => tagged .nonFiniteLevel []
def decodeLedgerFaultRaw : Sx → Option LedgerFault
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .absentRun, [] => some .absentRun
    | some .familyMismatch, [] => some .familyMismatch
    | some .absentResult, [] => some .absentResult
    | some .missingKind, [] => some .missingKind
    | some .missingValue, [] => some .missingValue
    | some .missingGuarantee, [] => some .missingGuarantee
    | some .missingBound, [] => some .missingBound
    | some .zeroBound, [] => some .zeroBound
    | some .unsupportedGuarantee, [] => some .unsupportedGuarantee
    | some .exceededBound, [] => some .exceededBound
    | some .nonFiniteLevel, [] => some .nonFiniteLevel
    | _, _ => none
  | _ => none
def decodeLedgerFault := Wire.canonical (encodeLedgerFault) (decodeLedgerFaultRaw)
@[simp] theorem decode_encodeLedgerFault (value : LedgerFault) :
    decodeLedgerFault (encodeLedgerFault value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x <;> simp [encodeLedgerFault, decodeLedgerFaultRaw, tagged]
theorem encodeLedgerFault_injective : Function.Injective encodeLedgerFault :=
  Wire.injective_of_roundtrip _ _ decode_encodeLedgerFault
theorem decodeLedgerFault_canonical {wire : Sx} {value : LedgerFault}
    (h : decodeLedgerFault wire = some value) : encodeLedgerFault value = wire :=
  Wire.canonical_sound _ _ h

def encodeApplicationError : BHL.CheckedMethods.ApplicationError → Sx
  | .modelMismatch => tagged .modelMismatch []
  | .premiseMismatch => tagged .premiseMismatch []
  | .programMismatch => tagged .programMismatch []
  | .postconditionMismatch => tagged .postconditionMismatch []
  | .runMismatch => tagged .runMismatch []
  | .failedPrecondition => tagged .failedPrecondition []
def decodeApplicationErrorRaw : Sx → Option BHL.CheckedMethods.ApplicationError
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .modelMismatch, [] => some .modelMismatch
    | some .premiseMismatch, [] => some .premiseMismatch
    | some .programMismatch, [] => some .programMismatch
    | some .postconditionMismatch, [] => some .postconditionMismatch
    | some .runMismatch, [] => some .runMismatch
    | some .failedPrecondition, [] => some .failedPrecondition
    | _, _ => none
  | _ => none
def decodeApplicationError := Wire.canonical (encodeApplicationError) (decodeApplicationErrorRaw)
@[simp] theorem decode_encodeApplicationError (value : BHL.CheckedMethods.ApplicationError) :
    decodeApplicationError (encodeApplicationError value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x <;> simp [encodeApplicationError, decodeApplicationErrorRaw, tagged]
theorem encodeApplicationError_injective : Function.Injective encodeApplicationError :=
  Wire.injective_of_roundtrip _ _ decode_encodeApplicationError
theorem decodeApplicationError_canonical {wire : Sx} {value : BHL.CheckedMethods.ApplicationError}
    (h : decodeApplicationError wire = some value) : encodeApplicationError value = wire :=
  Wire.canonical_sound _ _ h

def encodeBridgeError : BHL.BridgeError → Sx
  | .staleSnapshot => tagged .staleSnapshot []
  | .incompatibleInterpretation => tagged .incompatibleInterpretation []
  | .incompatibleMethod => tagged .incompatibleMethod []
  | .incompatibleClaim => tagged .incompatibleClaim []
  | .incompatibleDependencies => tagged .incompatibleDependencies []
  | .incompatibleEvidence => tagged .incompatibleEvidence []
  | .incompatibleBinding => tagged .incompatibleBinding []
  | .missingSupport => tagged .missingSupport []
  | .blockedSupport => tagged .blockedSupport []
  | .defeatedSupport => tagged .defeatedSupport []
  | .failedDerivation => tagged .failedDerivation []
  | .falsePrecondition => tagged .falsePrecondition []
  | .application error => tagged .application [encodeApplicationError error]
def decodeBridgeErrorRaw : Sx → Option BHL.BridgeError
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .staleSnapshot, [] => some .staleSnapshot
    | some .incompatibleInterpretation, [] => some .incompatibleInterpretation
    | some .incompatibleMethod, [] => some .incompatibleMethod
    | some .incompatibleClaim, [] => some .incompatibleClaim
    | some .incompatibleDependencies, [] => some .incompatibleDependencies
    | some .incompatibleEvidence, [] => some .incompatibleEvidence
    | some .incompatibleBinding, [] => some .incompatibleBinding
    | some .missingSupport, [] => some .missingSupport
    | some .blockedSupport, [] => some .blockedSupport
    | some .defeatedSupport, [] => some .defeatedSupport
    | some .failedDerivation, [] => some .failedDerivation
    | some .falsePrecondition, [] => some .falsePrecondition
    | some .application, [error] => do return .application (← decodeApplicationError error)
    | _, _ => none
  | _ => none
def decodeBridgeError := Wire.canonical (encodeBridgeError) (decodeBridgeErrorRaw)
@[simp] theorem decode_encodeBridgeError (value : BHL.BridgeError) :
    decodeBridgeError (encodeBridgeError value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x <;> simp [encodeBridgeError, decodeBridgeErrorRaw, tagged]
theorem encodeBridgeError_injective : Function.Injective encodeBridgeError :=
  Wire.injective_of_roundtrip _ _ decode_encodeBridgeError
theorem decodeBridgeError_canonical {wire : Sx} {value : BHL.BridgeError}
    (h : decodeBridgeError wire = some value) : encodeBridgeError value = wire :=
  Wire.canonical_sound _ _ h

def encodeSupportFault : SupportFault → Sx
  | .absent => tagged .absent []
  | .differentConclusion => tagged .differentConclusion []
  | .notRetained => tagged .notRetained []
  | .absentNode => tagged .absentNode []
  | .nodeMismatch => tagged .nodeMismatch []
  | .blocked => tagged .blocked []
  | .inference error => tagged .inference [ResultWire.encodeCheckError error]
  | .incomplete questions => tagged .incomplete [ResultWire.encodeQuestions questions]
def decodeSupportFaultRaw : Sx → Option SupportFault
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .absent, [] => some .absent
    | some .differentConclusion, [] => some .differentConclusion
    | some .notRetained, [] => some .notRetained
    | some .absentNode, [] => some .absentNode
    | some .nodeMismatch, [] => some .nodeMismatch
    | some .blocked, [] => some .blocked
    | some .inference, [error] => do return .inference (← ResultWire.decodeCheckError error)
    | some .incomplete, [questions] => do return .incomplete (← ResultWire.decodeQuestions questions)
    | _, _ => none
  | _ => none
def decodeSupportFault := Wire.canonical (encodeSupportFault) (decodeSupportFaultRaw)
@[simp] theorem decode_encodeSupportFault (value : SupportFault) :
    decodeSupportFault (encodeSupportFault value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x <;> simp [encodeSupportFault, decodeSupportFaultRaw, tagged]
theorem encodeSupportFault_injective : Function.Injective encodeSupportFault :=
  Wire.injective_of_roundtrip _ _ decode_encodeSupportFault
theorem decodeSupportFault_canonical {wire : Sx} {value : SupportFault}
    (h : decodeSupportFault wire = some value) : encodeSupportFault value = wire :=
  Wire.canonical_sound _ _ h

def encodeArtifactFault : ArtifactFault → Sx
  | .support argument fault => tagged .support [ResultWire.encodeArgId argument, encodeSupportFault fault]
  | .association fault => tagged .association [encodeAssociationFault fault]
  | .method fault => tagged .method [encodeBridgeError fault]
def decodeArtifactFaultRaw : Sx → Option ArtifactFault
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .support, [argument, fault] => do return .support (← ResultWire.decodeArgId argument) (← decodeSupportFault fault)
    | some .association, [fault] => do return .association (← decodeAssociationFault fault)
    | some .method, [fault] => do return .method (← decodeBridgeError fault)
    | _, _ => none
  | _ => none
def decodeArtifactFault := Wire.canonical (encodeArtifactFault) (decodeArtifactFaultRaw)
@[simp] theorem decode_encodeArtifactFault (value : ArtifactFault) :
    decodeArtifactFault (encodeArtifactFault value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x <;> simp [encodeArtifactFault, decodeArtifactFaultRaw, tagged]
theorem encodeArtifactFault_injective : Function.Injective encodeArtifactFault :=
  Wire.injective_of_roundtrip _ _ decode_encodeArtifactFault
theorem decodeArtifactFault_canonical {wire : Sx} {value : ArtifactFault}
    (h : decodeArtifactFault wire = some value) : encodeArtifactFault value = wire :=
  Wire.canonical_sound _ _ h

def encodeGuaranteeFault : GuaranteeFault → Sx
  | .invalidConditionalLevel => tagged .invalidConditionalLevel []
  | .ledger fault => tagged .ledger [encodeLedgerFault fault]
def decodeGuaranteeFaultRaw : Sx → Option GuaranteeFault
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .invalidConditionalLevel, [] => some .invalidConditionalLevel
    | some .ledger, [fault] => do return .ledger (← decodeLedgerFault fault)
    | _, _ => none
  | _ => none
def decodeGuaranteeFault := Wire.canonical (encodeGuaranteeFault) (decodeGuaranteeFaultRaw)
@[simp] theorem decode_encodeGuaranteeFault (value : GuaranteeFault) :
    decodeGuaranteeFault (encodeGuaranteeFault value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x <;> simp [encodeGuaranteeFault, decodeGuaranteeFaultRaw, tagged]
theorem encodeGuaranteeFault_injective : Function.Injective encodeGuaranteeFault :=
  Wire.injective_of_roundtrip _ _ decode_encodeGuaranteeFault
theorem decodeGuaranteeFault_canonical {wire : Sx} {value : GuaranteeFault}
    (h : decodeGuaranteeFault wire = some value) : encodeGuaranteeFault value = wire :=
  Wire.canonical_sound _ _ h

def encodeWitnessFault : WitnessFault → Sx
  | .missingClaim => tagged .missingClaim []
  | .missingWitness => tagged .missingWitness []
  | .ambiguousMetadata => tagged .ambiguousMetadata []
  | .wrongClaim => tagged .wrongClaim []
  | .staleSource => tagged .staleSource []
  | .artifact fault => tagged .artifact [encodeArtifactFault fault]
  | .guarantee fault => tagged .guarantee [encodeGuaranteeFault fault]
def decodeWitnessFaultRaw : Sx → Option WitnessFault
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .missingClaim, [] => some .missingClaim
    | some .missingWitness, [] => some .missingWitness
    | some .ambiguousMetadata, [] => some .ambiguousMetadata
    | some .wrongClaim, [] => some .wrongClaim
    | some .staleSource, [] => some .staleSource
    | some .artifact, [fault] => do return .artifact (← decodeArtifactFault fault)
    | some .guarantee, [fault] => do return .guarantee (← decodeGuaranteeFault fault)
    | _, _ => none
  | _ => none
def decodeWitnessFault := Wire.canonical (encodeWitnessFault) (decodeWitnessFaultRaw)
@[simp] theorem decode_encodeWitnessFault (value : WitnessFault) :
    decodeWitnessFault (encodeWitnessFault value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x <;> simp [encodeWitnessFault, decodeWitnessFaultRaw, tagged]
theorem encodeWitnessFault_injective : Function.Injective encodeWitnessFault :=
  Wire.injective_of_roundtrip _ _ decode_encodeWitnessFault
theorem decodeWitnessFault_canonical {wire : Sx} {value : WitnessFault}
    (h : decodeWitnessFault wire = some value) : encodeWitnessFault value = wire :=
  Wire.canonical_sound _ _ h

def encodeProvenanceError : Provenance.Error → Sx
  | .shape => tagged .shape []
  | .implicitMatch => tagged .implicitMatch []
  | .missingRule rule => tagged .missingRule [ResultWire.encodeRuleId rule]
  | .unresolvedReference reference => tagged .unresolvedReference [encodeArgRef reference]
  | .missingArgument argument => tagged .missingArgument [ResultWire.encodeArgId argument]
  | .duplicateArgument argument => tagged .duplicateArgument [ResultWire.encodeArgId argument]
  | .missingNode node => tagged .missingNode [ResultWire.encodeNat node]
def decodeProvenanceErrorRaw : Sx → Option Provenance.Error
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .shape, [] => some .shape
    | some .implicitMatch, [] => some .implicitMatch
    | some .missingRule, [rule] => do return .missingRule (← ResultWire.decodeRuleId rule)
    | some .unresolvedReference, [reference] => do return .unresolvedReference (← decodeArgRef reference)
    | some .missingArgument, [argument] => do return .missingArgument (← ResultWire.decodeArgId argument)
    | some .duplicateArgument, [argument] => do return .duplicateArgument (← ResultWire.decodeArgId argument)
    | some .missingNode, [node] => do return .missingNode (← ResultWire.decodeNat node)
    | _, _ => none
  | _ => none
def decodeProvenanceError := Wire.canonical (encodeProvenanceError) (decodeProvenanceErrorRaw)
@[simp] theorem decode_encodeProvenanceError (value : Provenance.Error) :
    decodeProvenanceError (encodeProvenanceError value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x <;> simp [encodeProvenanceError, decodeProvenanceErrorRaw, tagged]
theorem encodeProvenanceError_injective : Function.Injective encodeProvenanceError :=
  Wire.injective_of_roundtrip _ _ decode_encodeProvenanceError
theorem decodeProvenanceError_canonical {wire : Sx} {value : Provenance.Error}
    (h : decodeProvenanceError wire = some value) : encodeProvenanceError value = wire :=
  Wire.canonical_sound _ _ h

def encodeAssumptionId : AssumptionId → Sx
  | ⟨index⟩ => tagged .assumptionId [ResultWire.encodeNat index]
def decodeAssumptionIdRaw : Sx → Option AssumptionId
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .assumptionId, [index] => do return ⟨(← ResultWire.decodeNat index)⟩
    | _, _ => none
  | _ => none
def decodeAssumptionId := Wire.canonical (encodeAssumptionId) (decodeAssumptionIdRaw)
@[simp] theorem decode_encodeAssumptionId (value : AssumptionId) :
    decodeAssumptionId (encodeAssumptionId value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x; simp [encodeAssumptionId, decodeAssumptionIdRaw, tagged]
theorem encodeAssumptionId_injective : Function.Injective encodeAssumptionId :=
  Wire.injective_of_roundtrip _ _ decode_encodeAssumptionId
theorem decodeAssumptionId_canonical {wire : Sx} {value : AssumptionId}
    (h : decodeAssumptionId wire = some value) : encodeAssumptionId value = wire :=
  Wire.canonical_sound _ _ h

def encodeInterpretationId : InterpretationId → Sx
  | ⟨index⟩ => tagged .interpretationId [ResultWire.encodeNat index]
def decodeInterpretationIdRaw : Sx → Option InterpretationId
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .interpretationId, [index] => do return ⟨(← ResultWire.decodeNat index)⟩
    | _, _ => none
  | _ => none
def decodeInterpretationId := Wire.canonical (encodeInterpretationId) (decodeInterpretationIdRaw)
@[simp] theorem decode_encodeInterpretationId (value : InterpretationId) :
    decodeInterpretationId (encodeInterpretationId value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x; simp [encodeInterpretationId, decodeInterpretationIdRaw, tagged]
theorem encodeInterpretationId_injective : Function.Injective encodeInterpretationId :=
  Wire.injective_of_roundtrip _ _ decode_encodeInterpretationId
theorem decodeInterpretationId_canonical {wire : Sx} {value : InterpretationId}
    (h : decodeInterpretationId wire = some value) : encodeInterpretationId value = wire :=
  Wire.canonical_sound _ _ h

def encodeKindKey : KindKey → Sx
  | .leaf leaf => tagged .leaf [ResultWire.encodeLeafId leaf]
  | .method rule => tagged .method [ResultWire.encodeRule rule]
  | .argument argument => tagged .argument [ResultWire.encodeArgId argument]
def decodeKindKeyRaw : Sx → Option KindKey
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .leaf, [leaf] => do return .leaf (← ResultWire.decodeLeafId leaf)
    | some .method, [rule] => do return .method (← ResultWire.decodeRule rule)
    | some .argument, [argument] => do return .argument (← ResultWire.decodeArgId argument)
    | _, _ => none
  | _ => none
def decodeKindKey := Wire.canonical (encodeKindKey) (decodeKindKeyRaw)
@[simp] theorem decode_encodeKindKey (value : KindKey) :
    decodeKindKey (encodeKindKey value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x <;> simp [encodeKindKey, decodeKindKeyRaw, tagged]
theorem encodeKindKey_injective : Function.Injective encodeKindKey :=
  Wire.injective_of_roundtrip _ _ decode_encodeKindKey
theorem decodeKindKey_canonical {wire : Sx} {value : KindKey}
    (h : decodeKindKey wire = some value) : encodeKindKey value = wire :=
  Wire.canonical_sound _ _ h

def encodeSupportBinding : SupportBinding → Sx
  | ⟨argument, query⟩ => tagged .supportBinding [ResultWire.encodeArgId argument, ResultWire.encodeAtom query]
def decodeSupportBindingRaw : Sx → Option SupportBinding
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .supportBinding, [argument, query] => do return ⟨(← ResultWire.decodeArgId argument), (← ResultWire.decodeAtom query)⟩
    | _, _ => none
  | _ => none
def decodeSupportBinding := Wire.canonical (encodeSupportBinding) (decodeSupportBindingRaw)
@[simp] theorem decode_encodeSupportBinding (value : SupportBinding) :
    decodeSupportBinding (encodeSupportBinding value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x; simp [encodeSupportBinding, decodeSupportBindingRaw, tagged]
theorem encodeSupportBinding_injective : Function.Injective encodeSupportBinding :=
  Wire.injective_of_roundtrip _ _ decode_encodeSupportBinding
theorem decodeSupportBinding_canonical {wire : Sx} {value : SupportBinding}
    (h : decodeSupportBinding wire = some value) : encodeSupportBinding value = wire :=
  Wire.canonical_sound _ _ h

def encodeMethodBinding : MethodBinding → Sx
  | ⟨method, mode, parameter, first, second, residual⟩ => tagged .methodBinding [encodeMethod method, encodePayloadMode mode, encodeInt parameter, encodeBool first, encodeBool second, (ResultWire.encodeList encodeResidualAssumption) residual]
def decodeMethodBindingRaw : Sx → Option MethodBinding
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .methodBinding, [method, mode, parameter, first, second, residual] => do return ⟨(← decodeMethod method), (← decodePayloadMode mode), (← decodeInt parameter), (← decodeBool first), (← decodeBool second), (← (ResultWire.decodeList decodeResidualAssumption) residual)⟩
    | _, _ => none
  | _ => none
def decodeMethodBinding := Wire.canonical (encodeMethodBinding) (decodeMethodBindingRaw)
@[simp] theorem decode_encodeMethodBinding (value : MethodBinding) :
    decodeMethodBinding (encodeMethodBinding value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x; simp [encodeMethodBinding, decodeMethodBindingRaw, tagged]
theorem encodeMethodBinding_injective : Function.Injective encodeMethodBinding :=
  Wire.injective_of_roundtrip _ _ decode_encodeMethodBinding
theorem decodeMethodBinding_canonical {wire : Sx} {value : MethodBinding}
    (h : decodeMethodBinding wire = some value) : encodeMethodBinding value = wire :=
  Wire.canonical_sound _ _ h

def encodeArtifactInterpretation : ArtifactInterpretation → Sx
  | .declared id => tagged .declared [encodeInterpretationId id]
  | .checkedMethod method => tagged .checkedMethod [encodeMethodBinding method]
def decodeArtifactInterpretationRaw : Sx → Option ArtifactInterpretation
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .declared, [id] => do return .declared (← decodeInterpretationId id)
    | some .checkedMethod, [method] => do return .checkedMethod (← decodeMethodBinding method)
    | _, _ => none
  | _ => none
def decodeArtifactInterpretation := Wire.canonical (encodeArtifactInterpretation) (decodeArtifactInterpretationRaw)
@[simp] theorem decode_encodeArtifactInterpretation (value : ArtifactInterpretation) :
    decodeArtifactInterpretation (encodeArtifactInterpretation value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x <;> simp [encodeArtifactInterpretation, decodeArtifactInterpretationRaw, tagged]
theorem encodeArtifactInterpretation_injective : Function.Injective encodeArtifactInterpretation :=
  Wire.injective_of_roundtrip _ _ decode_encodeArtifactInterpretation
theorem decodeArtifactInterpretation_canonical {wire : Sx} {value : ArtifactInterpretation}
    (h : decodeArtifactInterpretation wire = some value) : encodeArtifactInterpretation value = wire :=
  Wire.canonical_sound _ _ h

def encodeArtifactSpec : ArtifactSpec → Sx
  | ⟨argument, dependencies, interpretation⟩ => tagged .artifactSpec [ResultWire.encodeArgId argument, (ResultWire.encodeList encodeSupportBinding) dependencies, encodeArtifactInterpretation interpretation]
def decodeArtifactSpecRaw : Sx → Option ArtifactSpec
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .artifactSpec, [argument, dependencies, interpretation] => do return ⟨(← ResultWire.decodeArgId argument), (← (ResultWire.decodeList decodeSupportBinding) dependencies), (← decodeArtifactInterpretation interpretation)⟩
    | _, _ => none
  | _ => none
def decodeArtifactSpec := Wire.canonical (encodeArtifactSpec) (decodeArtifactSpecRaw)
@[simp] theorem decode_encodeArtifactSpec (value : ArtifactSpec) :
    decodeArtifactSpec (encodeArtifactSpec value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x; simp [encodeArtifactSpec, decodeArtifactSpecRaw, tagged]
theorem encodeArtifactSpec_injective : Function.Injective encodeArtifactSpec :=
  Wire.injective_of_roundtrip _ _ decode_encodeArtifactSpec
theorem decodeArtifactSpec_canonical {wire : Sx} {value : ArtifactSpec}
    (h : decodeArtifactSpec wire = some value) : encodeArtifactSpec value = wire :=
  Wire.canonical_sound _ _ h

def encodeLedger : Statistics.Ledger → Sx
  | ⟨kind, value, countBound, guarantee⟩ => tagged .ledgerFields [(encodeOption encodeStatKind) kind, (encodeOption encodeRat) value, (encodeOption ResultWire.encodeNat) countBound, (encodeOption encodeGuaranteeClass) guarantee]
def decodeLedgerRaw : Sx → Option Statistics.Ledger
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .ledgerFields, [kind, value, countBound, guarantee] => do return ⟨(← (decodeOption decodeStatKind) kind), (← (decodeOption decodeRat) value), (← (decodeOption ResultWire.decodeNat) countBound), (← (decodeOption decodeGuaranteeClass) guarantee)⟩
    | _, _ => none
  | _ => none
def decodeLedger := Wire.canonical (encodeLedger) (decodeLedgerRaw)
@[simp] theorem decode_encodeLedger (value : Statistics.Ledger) :
    decodeLedger (encodeLedger value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x; simp [encodeLedger, decodeLedgerRaw, tagged]
theorem encodeLedger_injective : Function.Injective encodeLedger :=
  Wire.injective_of_roundtrip _ _ decode_encodeLedger
theorem decodeLedger_canonical {wire : Sx} {value : Statistics.Ledger}
    (h : decodeLedger wire = some value) : encodeLedger value = wire :=
  Wire.canonical_sound _ _ h

def encodeKindSpec : KindSpec → Sx
  | ⟨source, key, upper, assumption⟩ => tagged .kindSpec [encodeSource source, encodeKindKey key, encodeEvidenceKind upper, (encodeOption encodeAssumptionId) assumption]
def decodeKindSpecRaw : Sx → Option KindSpec
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .kindSpec, [source, key, upper, assumption] => do return ⟨(← decodeSource source), (← decodeKindKey key), (← decodeEvidenceKind upper), (← (decodeOption decodeAssumptionId) assumption)⟩
    | _, _ => none
  | _ => none
def decodeKindSpec := Wire.canonical (encodeKindSpec) (decodeKindSpecRaw)
@[simp] theorem decode_encodeKindSpec (value : KindSpec) :
    decodeKindSpec (encodeKindSpec value) = some value := by
  apply Wire.canonical_roundtrip
  intro x
  cases x; simp [encodeKindSpec, decodeKindSpecRaw, tagged, encodeSource, decodeSource]
theorem encodeKindSpec_injective : Function.Injective encodeKindSpec :=
  Wire.injective_of_roundtrip _ _ decode_encodeKindSpec
theorem decodeKindSpec_canonical {wire : Sx} {value : KindSpec}
    (h : decodeKindSpec wire = some value) : encodeKindSpec value = wire :=
  Wire.canonical_sound _ _ h

def encodeClaimBinding (n : Process.Wire.Names) : ClaimBinding → Sx
  | ⟨claim, declaration, query⟩ => tagged .claimBinding [(encodeClaimId n) claim, ResultWire.encodePropId declaration, ResultWire.encodeAtom query]
def decodeClaimBindingRaw (n : Process.Wire.Names) : Sx → Option ClaimBinding
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .claimBinding, [claim, declaration, query] => do return ⟨(← (decodeClaimId n) claim), (← ResultWire.decodePropId declaration), (← ResultWire.decodeAtom query)⟩
    | _, _ => none
  | _ => none
def decodeClaimBinding (n : Process.Wire.Names) := Wire.canonical (encodeClaimBinding n) (decodeClaimBindingRaw n)
theorem decodeClaimBinding_canonical (n : Process.Wire.Names) {wire : Sx} {value : ClaimBinding}
    (h : decodeClaimBinding n wire = some value) : encodeClaimBinding n value = wire :=
  Wire.canonical_sound _ _ h

def encodeLedgerBinding (n : Process.Wire.Names) : LedgerBinding → Sx
  | ⟨run, family, outcome, ledger⟩ => tagged .ledgerBinding [(encodeRunId n) run, (encodeFamilyId n) family, ResultWire.encodeNat outcome, encodeLedger ledger]
def decodeLedgerBindingRaw (n : Process.Wire.Names) : Sx → Option LedgerBinding
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .ledgerBinding, [run, family, outcome, ledger] => do return ⟨(← (decodeRunId n) run), (← (decodeFamilyId n) family), (← ResultWire.decodeNat outcome), (← decodeLedger ledger)⟩
    | _, _ => none
  | _ => none
def decodeLedgerBinding (n : Process.Wire.Names) := Wire.canonical (encodeLedgerBinding n) (decodeLedgerBindingRaw n)
theorem decodeLedgerBinding_canonical (n : Process.Wire.Names) {wire : Sx} {value : LedgerBinding}
    (h : decodeLedgerBinding n wire = some value) : encodeLedgerBinding n value = wire :=
  Wire.canonical_sound _ _ h

def encodeGuaranteeBinding (n : Process.Wire.Names) : GuaranteeBinding → Sx
  | .conditional kind level => tagged .conditional [encodeGuaranteeClass kind, encodeRat level]
  | .ledger binding => tagged .ledger [(encodeLedgerBinding n) binding]
def decodeGuaranteeBindingRaw (n : Process.Wire.Names) : Sx → Option GuaranteeBinding
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .conditional, [kind, level] => do return .conditional (← decodeGuaranteeClass kind) (← decodeRat level)
    | some .ledger, [binding] => do return .ledger (← (decodeLedgerBinding n) binding)
    | _, _ => none
  | _ => none
def decodeGuaranteeBinding (n : Process.Wire.Names) := Wire.canonical (encodeGuaranteeBinding n) (decodeGuaranteeBindingRaw n)
theorem decodeGuaranteeBinding_canonical (n : Process.Wire.Names) {wire : Sx} {value : GuaranteeBinding}
    (h : decodeGuaranteeBinding n wire = some value) : encodeGuaranteeBinding n value = wire :=
  Wire.canonical_sound _ _ h

def encodeWitnessSpec (n : Process.Wire.Names) : WitnessSpec → Sx
  | ⟨witness, claim, source, artifact, probed, guarantee⟩ => tagged .witnessSpec [(encodeWitnessId n) witness, (encodeClaimId n) claim, encodeSource source, encodeArtifactSpec artifact, (ResultWire.encodeList encodeErrorKind) probed, (encodeGuaranteeBinding n) guarantee]
def decodeWitnessSpecRaw (n : Process.Wire.Names) : Sx → Option WitnessSpec
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .witnessSpec, [witness, claim, source, artifact, probed, guarantee] => do return ⟨(← (decodeWitnessId n) witness), (← (decodeClaimId n) claim), (← decodeSource source), (← decodeArtifactSpec artifact), (← (ResultWire.decodeList decodeErrorKind) probed), (← (decodeGuaranteeBinding n) guarantee)⟩
    | _, _ => none
  | _ => none
def decodeWitnessSpec (n : Process.Wire.Names) := Wire.canonical (encodeWitnessSpec n) (decodeWitnessSpecRaw n)
theorem decodeWitnessSpec_canonical (n : Process.Wire.Names) {wire : Sx} {value : WitnessSpec}
    (h : decodeWitnessSpec n wire = some value) : encodeWitnessSpec n value = wire :=
  Wire.canonical_sound _ _ h

def encodeCaptureAssumption (n : Process.Wire.Names) : CaptureAssumption → Sx
  | ⟨id, source, key, event, run, basis⟩ => tagged .captureAssumption [encodeAssumptionId id, encodeSource source, encodeKindKey key, (encodeStamped n) event, (encodeRunId n) run, encodeAdmissionBasis basis]
def decodeCaptureAssumptionRaw (n : Process.Wire.Names) : Sx → Option CaptureAssumption
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .captureAssumption, [id, source, key, event, run, basis] => do return ⟨(← decodeAssumptionId id), (← decodeSource source), (← decodeKindKey key), (← (decodeStamped n) event), (← (decodeRunId n) run), (← decodeAdmissionBasis basis)⟩
    | _, _ => none
  | _ => none
def decodeCaptureAssumption (n : Process.Wire.Names) := Wire.canonical (encodeCaptureAssumption n) (decodeCaptureAssumptionRaw n)
theorem decodeCaptureAssumption_canonical (n : Process.Wire.Names) {wire : Sx} {value : CaptureAssumption}
    (h : decodeCaptureAssumption n wire = some value) : encodeCaptureAssumption n value = wire :=
  Wire.canonical_sound _ _ h

def encodeConfig (n : Process.Wire.Names) : AuditConfig → Sx
  | ⟨claims, witnesses, kinds, assumptions⟩ => tagged .auditConfig [(ResultWire.encodeList (encodeClaimBinding n)) claims, (ResultWire.encodeList (encodeWitnessSpec n)) witnesses, (ResultWire.encodeList encodeKindSpec) kinds, (ResultWire.encodeList (encodeCaptureAssumption n)) assumptions]
def decodeConfigRaw (n : Process.Wire.Names) : Sx → Option AuditConfig
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .auditConfig, [claims, witnesses, kinds, assumptions] => do return ⟨(← (ResultWire.decodeList (decodeClaimBinding n)) claims), (← (ResultWire.decodeList (decodeWitnessSpec n)) witnesses), (← (ResultWire.decodeList decodeKindSpec) kinds), (← (ResultWire.decodeList (decodeCaptureAssumption n)) assumptions)⟩
    | _, _ => none
  | _ => none
def decodeConfig (n : Process.Wire.Names) := Wire.canonical (encodeConfig n) (decodeConfigRaw n)
theorem decodeConfig_canonical (n : Process.Wire.Names) {wire : Sx} {value : AuditConfig}
    (h : decodeConfig n wire = some value) : encodeConfig n value = wire :=
  Wire.canonical_sound _ _ h

/-- Structural bounds only; these predicates do not mention decoding. -/
def ClaimBindingWellNamed (n : Process.Wire.Names) (v : ClaimBinding) : Prop :=
  v.claim.index < n.claim.length
def LedgerBindingWellNamed (n : Process.Wire.Names) (v : LedgerBinding) : Prop :=
  v.run.index < n.run.length ∧ v.family.index < n.family.length
def GuaranteeBindingWellNamed (n : Process.Wire.Names) : GuaranteeBinding → Prop
  | .conditional _ _ => True
  | .ledger v => LedgerBindingWellNamed n v
def WitnessSpecWellNamed (n : Process.Wire.Names) (v : WitnessSpec) : Prop :=
  v.witness.index < n.witness.length ∧ v.claim.index < n.claim.length ∧
    GuaranteeBindingWellNamed n v.guarantee
def CaptureAssumptionWellNamed (n : Process.Wire.Names) (v : CaptureAssumption) : Prop :=
  StampedWellNamed n v.event ∧ v.run.index < n.run.length
def ConfigWellNamed (n : Process.Wire.Names) (v : AuditConfig) : Prop :=
  (∀ c ∈ v.claims, ClaimBindingWellNamed n c) ∧
  (∀ w ∈ v.witnesses, WitnessSpecWellNamed n w) ∧
  (∀ a ∈ v.assumptions, CaptureAssumptionWellNamed n a)

theorem decode_encodeClaimId (n : Process.Wire.Names) (unique : UniqueNames n)
    (value : ClaimId) (bound : value.index < n.claim.length) :
    decodeClaimId n (encodeClaimId n value) = some value := by
  cases value
  simp [decodeClaimId, encodeClaimId, InquiryProcessWire.decode_encodeIdx _ unique.2.2.2.2.1 _ _ bound]

theorem decode_encodeWitnessId (n : Process.Wire.Names) (unique : UniqueNames n)
    (value : WitnessId) (bound : value.index < n.witness.length) :
    decodeWitnessId n (encodeWitnessId n value) = some value := by
  cases value
  simp [decodeWitnessId, encodeWitnessId, InquiryProcessWire.decode_encodeIdx _ unique.2.2.2.2.2.2.2.2 _ _ bound]

theorem decode_encodeRunId (n : Process.Wire.Names) (unique : UniqueNames n)
    (value : RunId) (bound : value.index < n.run.length) :
    decodeRunId n (encodeRunId n value) = some value := by
  cases value
  simp [decodeRunId, encodeRunId, InquiryProcessWire.decode_encodeIdx _ unique.2.2.2.1 _ _ bound]

theorem decode_encodeFamilyId (n : Process.Wire.Names) (unique : UniqueNames n)
    (value : FamilyId) (bound : value.index < n.family.length) :
    decodeFamilyId n (encodeFamilyId n value) = some value := by
  cases value
  simp [decodeFamilyId, encodeFamilyId, InquiryProcessWire.decode_encodeIdx _ unique.2.2.2.2.2.2.2.1 _ _ bound]

theorem decode_encodeStamped (n : Process.Wire.Names) (unique : UniqueNames n)
    (value : Stamped) (bound : StampedWellNamed n value) :
    decodeStamped n (encodeStamped n value) = some value := by
  simp [decodeStamped, InquiryProcessWire.decode_encodeStamped n unique value bound]

theorem decode_encodeClaimBinding (n : Process.Wire.Names) (unique : UniqueNames n)
    (value : ClaimBinding) (valid : ClaimBindingWellNamed n value) :
    decodeClaimBinding n (encodeClaimBinding n value) = some value := by
  have hc := decode_encodeClaimId n unique value.claim valid
  cases value
  simp_all [decodeClaimBinding, Wire.canonical, decodeClaimBindingRaw, encodeClaimBinding, tagged]

theorem decode_encodeLedgerBinding (n : Process.Wire.Names) (unique : UniqueNames n)
    (value : LedgerBinding) (valid : LedgerBindingWellNamed n value) :
    decodeLedgerBinding n (encodeLedgerBinding n value) = some value := by
  have hr := decode_encodeRunId n unique value.run valid.1
  have hf := decode_encodeFamilyId n unique value.family valid.2
  cases value
  simp_all [decodeLedgerBinding, Wire.canonical, decodeLedgerBindingRaw, encodeLedgerBinding, tagged]

theorem decode_encodeGuaranteeBinding (n : Process.Wire.Names) (unique : UniqueNames n)
    (value : GuaranteeBinding) (valid : GuaranteeBindingWellNamed n value) :
    decodeGuaranteeBinding n (encodeGuaranteeBinding n value) = some value := by
  cases value with
  | conditional kind level => simp [decodeGuaranteeBinding, Wire.canonical, decodeGuaranteeBindingRaw, encodeGuaranteeBinding, tagged]
  | ledger binding =>
      have h := decode_encodeLedgerBinding n unique binding valid
      simp [decodeGuaranteeBinding, Wire.canonical, decodeGuaranteeBindingRaw, encodeGuaranteeBinding, tagged, h]

theorem decode_encodeWitnessSpec (n : Process.Wire.Names) (unique : UniqueNames n)
    (value : WitnessSpec) (valid : WitnessSpecWellNamed n value) :
    decodeWitnessSpec n (encodeWitnessSpec n value) = some value := by
  have hw := decode_encodeWitnessId n unique value.witness valid.1
  have hc := decode_encodeClaimId n unique value.claim valid.2.1
  have hg := decode_encodeGuaranteeBinding n unique value.guarantee valid.2.2
  cases value
  simp_all [decodeWitnessSpec, Wire.canonical, decodeWitnessSpecRaw, encodeWitnessSpec, tagged, encodeSource, decodeSource]

theorem decode_encodeCaptureAssumption (n : Process.Wire.Names) (unique : UniqueNames n)
    (value : CaptureAssumption) (valid : CaptureAssumptionWellNamed n value) :
    decodeCaptureAssumption n (encodeCaptureAssumption n value) = some value := by
  have he := decode_encodeStamped n unique value.event valid.1
  have hr := decode_encodeRunId n unique value.run valid.2
  cases value
  simp_all [decodeCaptureAssumption, Wire.canonical, decodeCaptureAssumptionRaw, encodeCaptureAssumption, tagged, encodeSource, decodeSource]

theorem decode_encodeList_of (e : α → Sx) (d : Sx → Option α)
    (p : α → Prop) (roundtrip : ∀ a, p a → d (e a) = some a)
    (values : List α) (valid : ∀ a ∈ values, p a) :
    ResultWire.decodeList d (ResultWire.encodeList e values) = some values := by
  simp only [ResultWire.decodeList, ResultWire.encodeList]
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at valid
    simp [Wire.decodeList, roundtrip a valid.1, ih valid.2]

theorem decode_encodeConfig (n : Process.Wire.Names) (unique : UniqueNames n)
    (value : AuditConfig) (valid : ConfigWellNamed n value) :
    decodeConfig n (encodeConfig n value) = some value := by
  have hc := decode_encodeList_of _ _ _ (decode_encodeClaimBinding n unique) value.claims valid.1
  have hw := decode_encodeList_of _ _ _ (decode_encodeWitnessSpec n unique) value.witnesses valid.2.1
  have ha := decode_encodeList_of _ _ _ (decode_encodeCaptureAssumption n unique) value.assumptions valid.2.2
  cases value
  simp_all [decodeConfig, Wire.canonical, decodeConfigRaw, encodeConfig, tagged]

theorem encodeClaimBinding_injective (n : Process.Wire.Names) (unique : UniqueNames n)
    {a b : ClaimBinding} (ha : ClaimBindingWellNamed n a) (hb : ClaimBindingWellNamed n b)
    (equal : encodeClaimBinding n a = encodeClaimBinding n b) : a = b := by
  have h := congrArg (decodeClaimBinding n) equal
  simpa only [decode_encodeClaimBinding n unique a ha, decode_encodeClaimBinding n unique b hb,
    Option.some.injEq] using h

theorem encodeLedgerBinding_injective (n : Process.Wire.Names) (unique : UniqueNames n)
    {a b : LedgerBinding} (ha : LedgerBindingWellNamed n a) (hb : LedgerBindingWellNamed n b)
    (equal : encodeLedgerBinding n a = encodeLedgerBinding n b) : a = b := by
  have h := congrArg (decodeLedgerBinding n) equal
  simpa only [decode_encodeLedgerBinding n unique a ha, decode_encodeLedgerBinding n unique b hb,
    Option.some.injEq] using h

theorem encodeGuaranteeBinding_injective (n : Process.Wire.Names) (unique : UniqueNames n)
    {a b : GuaranteeBinding} (ha : GuaranteeBindingWellNamed n a) (hb : GuaranteeBindingWellNamed n b)
    (equal : encodeGuaranteeBinding n a = encodeGuaranteeBinding n b) : a = b := by
  have h := congrArg (decodeGuaranteeBinding n) equal
  simpa only [decode_encodeGuaranteeBinding n unique a ha, decode_encodeGuaranteeBinding n unique b hb,
    Option.some.injEq] using h

theorem encodeWitnessSpec_injective (n : Process.Wire.Names) (unique : UniqueNames n)
    {a b : WitnessSpec} (ha : WitnessSpecWellNamed n a) (hb : WitnessSpecWellNamed n b)
    (equal : encodeWitnessSpec n a = encodeWitnessSpec n b) : a = b := by
  have h := congrArg (decodeWitnessSpec n) equal
  simpa only [decode_encodeWitnessSpec n unique a ha, decode_encodeWitnessSpec n unique b hb,
    Option.some.injEq] using h

theorem encodeCaptureAssumption_injective (n : Process.Wire.Names) (unique : UniqueNames n)
    {a b : CaptureAssumption} (ha : CaptureAssumptionWellNamed n a) (hb : CaptureAssumptionWellNamed n b)
    (equal : encodeCaptureAssumption n a = encodeCaptureAssumption n b) : a = b := by
  have h := congrArg (decodeCaptureAssumption n) equal
  simpa only [decode_encodeCaptureAssumption n unique a ha, decode_encodeCaptureAssumption n unique b hb,
    Option.some.injEq] using h

theorem encodeConfig_injective (n : Process.Wire.Names) (unique : UniqueNames n)
    {a b : AuditConfig} (ha : ConfigWellNamed n a) (hb : ConfigWellNamed n b)
    (equal : encodeConfig n a = encodeConfig n b) : a = b := by
  have h := congrArg (decodeConfig n) equal
  simpa only [decode_encodeConfig n unique a ha, decode_encodeConfig n unique b hb,
    Option.some.injEq] using h

end Lara.Process.Source.AuditWire
