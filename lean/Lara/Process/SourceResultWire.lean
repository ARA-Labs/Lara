import Lara.Process.Source
import Lara.Process.SourceDiagnosticWire

namespace Lara.Process.Source.ResultWire

set_option maxRecDepth 4096

/-- Closed result vocabulary. Reason strings and identifiers remain payload atoms. -/
inductive Tag where
  | backend | strict | defeasible | prem | ques
  | root | premise | question | missingLeaf | missingRule
  | undeclaredAttackSource | undeclaredAttackTarget | duplicateKeys | domainMismatch | premiseInstantiation
  | conclusionInstantiation | count | mismatch | duplicateDeclarations | duplicateDischarges
  | duplicateHoles | uncovered | overlap | undeclaredDischarge | undeclaredHole
  | answerInstantiation | conclusionMismatch | questionsPresent | wrongMode | trustedDisallowed
  | certifierUnallowlisted | backendMissing | digestMissing | replayRejected | rebut
  | undercut | undermine | rule | leaf | undefinedPosition
  | wrongOccurrenceKind | missingTargetRule | targetConclusionInstantiation | missingTargetLeaf | strictTarget
  | missingContrary | missingException | exceptionInstantiation | exceptionMismatch | R1
  | R3 | R4 | R5 | R6 | R7
  | R10 | R11 | R13 | argument | attack
  | missingConflict | rejection | duplicateArgument | duplicateRule | scopeViolation
  | policyViolation | malformedSigma | policyIllSorted | groundIllSorted | argsIllSorted
  | signature | program | unsupported | policyMismatch | duplicateLeafId
  | duplicateArgId | duplicateClaimId | duplicateValueName | malformedRuleNamespace | invalidValueBinding
  | invalidComparison | invalidInferredArgument | invalidNamedCertificate | challengeTargetUndeclared | invalidSurfaceAttack
  | unknownStatusClaim | duplicateGroupId | groupRepeatedMember | groupTooFewMembers | groupMemberUndeclared
  | noncanonicalPremiseLabels | duplicateAdmissionKey | admissionRejected | structural | evidence
  | evidenceSyntax | groupConflict | binding | capture | extraction
  | admissionError | source | core | unsupportedCore | backendMismatch
  | duplicateBackend | unsupportedBackend | duplicateTheory | theoryMismatch | artifactMismatch
  | replay | missingEvidence | unselectedCertificate | published | evidenceBlocked
  | rejected | accepted | absent | present
  deriving DecidableEq

def Tag.text : Tag → String
  | .backend => "backend"
  | .strict => Driver.tagToString .strict
  | .defeasible => Driver.tagToString .defeasible
  | .prem => Driver.tagToString .prem
  | .ques => Driver.tagToString .ques
  | .root => "root"
  | .premise => "premise"
  | .question => "question"
  | .missingLeaf => "missing-leaf"
  | .missingRule => "missing-rule"
  | .undeclaredAttackSource => "undeclared-attack-source"
  | .undeclaredAttackTarget => "undeclared-attack-target"
  | .duplicateKeys => "duplicate-keys"
  | .domainMismatch => "domain-mismatch"
  | .premiseInstantiation => "premise-instantiation"
  | .conclusionInstantiation => "conclusion-instantiation"
  | .count => "count"
  | .mismatch => "mismatch"
  | .duplicateDeclarations => "duplicate-declarations"
  | .duplicateDischarges => "duplicate-discharges"
  | .duplicateHoles => "duplicate-holes"
  | .uncovered => "uncovered"
  | .overlap => "overlap"
  | .undeclaredDischarge => "undeclared-discharge"
  | .undeclaredHole => "undeclared-hole"
  | .answerInstantiation => "answer-instantiation"
  | .conclusionMismatch => "conclusion-mismatch"
  | .questionsPresent => "questions-present"
  | .wrongMode => "wrong-mode"
  | .trustedDisallowed => "trusted-disallowed"
  | .certifierUnallowlisted => "certifier-unallowlisted"
  | .backendMissing => "backend-missing"
  | .digestMissing => "digest-missing"
  | .replayRejected => "replay-rejected"
  | .rebut => "rebut"
  | .undercut => "undercut"
  | .undermine => "undermine"
  | .rule => "rule"
  | .leaf => "leaf"
  | .undefinedPosition => "undefined-position"
  | .wrongOccurrenceKind => "wrong-occurrence-kind"
  | .missingTargetRule => "missing-target-rule"
  | .targetConclusionInstantiation => "target-conclusion-instantiation"
  | .missingTargetLeaf => "missing-target-leaf"
  | .strictTarget => "strict-target"
  | .missingContrary => "missing-contrary"
  | .missingException => "missing-exception"
  | .exceptionInstantiation => "exception-instantiation"
  | .exceptionMismatch => "exception-mismatch"
  | .R1 => "r1"
  | .R3 => "r3"
  | .R4 => "r4"
  | .R5 => "r5"
  | .R6 => "r6"
  | .R7 => "r7"
  | .R10 => "r10"
  | .R11 => "r11"
  | .R13 => "r13"
  | .argument => "argument"
  | .attack => "attack"
  | .missingConflict => "missing-conflict"
  | .rejection => "rejection"
  | .duplicateArgument => "duplicate-argument"
  | .duplicateRule => "duplicate-rule"
  | .scopeViolation => "scope-violation"
  | .policyViolation => "policy-violation"
  | .malformedSigma => "malformed-sigma"
  | .policyIllSorted => "policy-ill-sorted"
  | .groundIllSorted => "ground-ill-sorted"
  | .argsIllSorted => "args-ill-sorted"
  | .signature => "signature"
  | .program => "program"
  | .unsupported => "unsupported"
  | .policyMismatch => "policy-mismatch"
  | .duplicateLeafId => "duplicate-leaf-id"
  | .duplicateArgId => "duplicate-arg-id"
  | .duplicateClaimId => "duplicate-claim-id"
  | .duplicateValueName => "duplicate-value-name"
  | .malformedRuleNamespace => "malformed-rule-namespace"
  | .invalidValueBinding => "invalid-value-binding"
  | .invalidComparison => "invalid-comparison"
  | .invalidInferredArgument => "invalid-inferred-argument"
  | .invalidNamedCertificate => "invalid-named-certificate"
  | .challengeTargetUndeclared => "challenge-target-undeclared"
  | .invalidSurfaceAttack => "invalid-surface-attack"
  | .unknownStatusClaim => "unknown-status-claim"
  | .duplicateGroupId => "duplicate-group-id"
  | .groupRepeatedMember => "group-repeated-member"
  | .groupTooFewMembers => "group-too-few-members"
  | .groupMemberUndeclared => "group-member-undeclared"
  | .noncanonicalPremiseLabels => "noncanonical-premise-labels"
  | .duplicateAdmissionKey => "duplicate-admission-key"
  | .admissionRejected => "admission-rejected"
  | .structural => "structural"
  | .evidence => "evidence"
  | .evidenceSyntax => "evidence-syntax"
  | .groupConflict => "group-conflict"
  | .binding => "binding"
  | .capture => "capture"
  | .extraction => "extraction"
  | .admissionError => "admission-error"
  | .source => "source"
  | .core => "core"
  | .unsupportedCore => "unsupported-core"
  | .backendMismatch => "backend-mismatch"
  | .duplicateBackend => "duplicate-backend"
  | .unsupportedBackend => "unsupported-backend"
  | .duplicateTheory => "duplicate-theory"
  | .theoryMismatch => "theory-mismatch"
  | .artifactMismatch => "artifact-mismatch"
  | .replay => "replay"
  | .missingEvidence => "missing-evidence"
  | .unselectedCertificate => "unselected-certificate"
  | .published => "published"
  | .evidenceBlocked => "evidence-blocked"
  | .rejected => "rejected"
  | .accepted => "accepted"
  | .absent => "absent"
  | .present => "present"

def Tag.spelling : Process.Wire.Spelling Tag where
  all := [.backend, .strict, .defeasible, .prem, .ques, .root, .premise, .question, .missingLeaf, .missingRule, .undeclaredAttackSource, .undeclaredAttackTarget, .duplicateKeys, .domainMismatch, .premiseInstantiation, .conclusionInstantiation, .count, .mismatch, .duplicateDeclarations, .duplicateDischarges, .duplicateHoles, .uncovered, .overlap, .undeclaredDischarge, .undeclaredHole, .answerInstantiation, .conclusionMismatch, .questionsPresent, .wrongMode, .trustedDisallowed, .certifierUnallowlisted, .backendMissing, .digestMissing, .replayRejected, .rebut, .undercut, .undermine, .rule, .leaf, .undefinedPosition, .wrongOccurrenceKind, .missingTargetRule, .targetConclusionInstantiation, .missingTargetLeaf, .strictTarget, .missingContrary, .missingException, .exceptionInstantiation, .exceptionMismatch, .R1, .R3, .R4, .R5, .R6, .R7, .R10, .R11, .R13, .argument, .attack, .missingConflict, .rejection, .duplicateArgument, .duplicateRule, .scopeViolation, .policyViolation, .malformedSigma, .policyIllSorted, .groundIllSorted, .argsIllSorted, .signature, .program, .unsupported, .policyMismatch, .duplicateLeafId, .duplicateArgId, .duplicateClaimId, .duplicateValueName, .malformedRuleNamespace, .invalidValueBinding, .invalidComparison, .invalidInferredArgument, .invalidNamedCertificate, .challengeTargetUndeclared, .invalidSurfaceAttack, .unknownStatusClaim, .duplicateGroupId, .groupRepeatedMember, .groupTooFewMembers, .groupMemberUndeclared, .noncanonicalPremiseLabels, .duplicateAdmissionKey, .admissionRejected, .structural, .evidence, .evidenceSyntax, .groupConflict, .binding, .capture, .extraction, .admissionError, .source, .core, .unsupportedCore, .backendMismatch, .duplicateBackend, .unsupportedBackend, .duplicateTheory, .theoryMismatch, .artifactMismatch, .replay, .missingEvidence, .unselectedCertificate, .published, .evidenceBlocked, .rejected, .accepted, .absent, .present]
  text := Tag.text

def Tag.parse : String → Option Tag := Tag.spelling.parse

theorem Tag.spelling_complete (t : Tag) : t ∈ Tag.spelling.all := by
  cases t <;> decide
theorem Tag.spelling_nodup : (Tag.spelling.all.map Tag.spelling.text).Nodup := by decide
@[simp] theorem Tag.parse_text (t : Tag) : Tag.parse t.text = some t :=
  Tag.spelling.parse_text Tag.spelling_complete Tag.spelling_nodup t
theorem Tag.parse_some {text : String} {tag : Tag} (h : Tag.parse text = some tag) :
    tag.text = text := Tag.spelling.parse_some h
theorem Tag.text_injective : Function.Injective Tag.text :=
  Tag.spelling.text_injective Tag.spelling_complete Tag.spelling_nodup

def tagged (tag : Tag) (xs : List Sx) : Sx := .list (.atom tag.text :: xs)

def encodeCoreLeaf (x : Support.LeafId) : Sx := .atom x.name
def decodeCoreLeaf : Sx → Option Support.LeafId
  | .atom s => some ⟨s⟩
  | _ => none
@[simp] theorem decode_encodeCoreLeaf (x : Support.LeafId) : decodeCoreLeaf (encodeCoreLeaf x) = some x := rfl

def encodeRule (x : Support.RuleId) : Sx := .atom x.name
def decodeRule : Sx → Option Support.RuleId
  | .atom s => some ⟨s⟩
  | _ => none
@[simp] theorem decode_encodeRule (x : Support.RuleId) : decodeRule (encodeRule x) = some x := rfl

def encodeDigest (x : Support.Digest) : Sx := .atom x.hash
def decodeDigest : Sx → Option Support.Digest
  | .atom s => some ⟨s⟩
  | _ => none
@[simp] theorem decode_encodeDigest (x : Support.Digest) : decodeDigest (encodeDigest x) = some x := rfl

def encodePolicyId (x : Presentation.PolicyId) : Sx := .atom x.val
def decodePolicyId : Sx → Option Presentation.PolicyId
  | .atom s => some ⟨s⟩
  | _ => none
@[simp] theorem decode_encodePolicyId (x : Presentation.PolicyId) : decodePolicyId (encodePolicyId x) = some x := rfl

def encodeLeafId (x : Presentation.LeafId) : Sx := .atom x.val
def decodeLeafId : Sx → Option Presentation.LeafId
  | .atom s => some ⟨s⟩
  | _ => none
@[simp] theorem decode_encodeLeafId (x : Presentation.LeafId) : decodeLeafId (encodeLeafId x) = some x := rfl

def encodeArgId (x : Presentation.ArgId) : Sx := .atom x.val
def decodeArgId : Sx → Option Presentation.ArgId
  | .atom s => some ⟨s⟩
  | _ => none
@[simp] theorem decode_encodeArgId (x : Presentation.ArgId) : decodeArgId (encodeArgId x) = some x := rfl

def encodePropId (x : Presentation.PropId) : Sx := .atom x.val
def decodePropId : Sx → Option Presentation.PropId
  | .atom s => some ⟨s⟩
  | _ => none
@[simp] theorem decode_encodePropId (x : Presentation.PropId) : decodePropId (encodePropId x) = some x := rfl

def encodeValueName (x : Presentation.ValueName) : Sx := .atom x.val
def decodeValueName : Sx → Option Presentation.ValueName
  | .atom s => some ⟨s⟩
  | _ => none
@[simp] theorem decode_encodeValueName (x : Presentation.ValueName) : decodeValueName (encodeValueName x) = some x := rfl

def encodeRuleId (x : Presentation.RuleId) : Sx := .atom x.val
def decodeRuleId : Sx → Option Presentation.RuleId
  | .atom s => some ⟨s⟩
  | _ => none
@[simp] theorem decode_encodeRuleId (x : Presentation.RuleId) : decodeRuleId (encodeRuleId x) = some x := rfl

def encodeGroupId (x : Presentation.GroupId) : Sx := .atom x.val
def decodeGroupId : Sx → Option Presentation.GroupId
  | .atom s => some ⟨s⟩
  | _ => none
@[simp] theorem decode_encodeGroupId (x : Presentation.GroupId) : decodeGroupId (encodeGroupId x) = some x := rfl

def encodeObject (x : Evidence.ObjectId) : Sx := .atom x.val
def decodeObject : Sx → Option Evidence.ObjectId
  | .atom s => some ⟨s⟩
  | _ => none
@[simp] theorem decode_encodeObject (x : Evidence.ObjectId) : decodeObject (encodeObject x) = some x := rfl

def encodeLeafKind (x : Presentation.LeafKind) : Sx := Wire.encodePresentation x.sx
def decodeLeafKind (s : Sx) : Option Presentation.LeafKind := do
  Presentation.unLeafKind (← Wire.decodePresentation s)
@[simp] theorem decode_encodeLeafKind (x : Presentation.LeafKind) : decodeLeafKind (encodeLeafKind x) = some x := by
  simp [decodeLeafKind, encodeLeafKind]

def encodeProvenance (x : Presentation.Provenance) : Sx := Wire.encodePresentation x.sx
def decodeProvenance (s : Sx) : Option Presentation.Provenance := do
  Presentation.unProvenance (← Wire.decodePresentation s)
@[simp] theorem decode_encodeProvenance (x : Presentation.Provenance) : decodeProvenance (encodeProvenance x) = some x := by
  simp [decodeProvenance, encodeProvenance]

abbrev encodeCoreVersion := Wire.encodeCoreVersion
abbrev decodeCoreVersion := Wire.decodeCoreVersion

abbrev encodeBackendIdentity := Wire.encodeBackend
abbrev decodeBackendIdentity := Wire.decodeBackend
@[simp] theorem decode_encodeCoreVersion (v : CoreVersion) :
    decodeCoreVersion (encodeCoreVersion v) = some v := Wire.decode_encodeCoreVersion v
@[simp] theorem decode_encodeBackendIdentity (v : BackendIdentity) :
    decodeBackendIdentity (encodeBackendIdentity v) = some v := Wire.decode_encodeBackend v

def encodeObjectOption : Option Evidence.ObjectId → Sx
  | none => tagged .absent []
  | some o => tagged .present [encodeObject o]
def decodeObjectOption : Sx → Option (Option Evidence.ObjectId)
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .absent, [] => some none
    | some .present, [o] => do return some (← decodeObject o)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeObjectOption (o : Option Evidence.ObjectId) :
    decodeObjectOption (encodeObjectOption o) = some o := by
  cases o <;> simp [encodeObjectOption, decodeObjectOption, tagged]

def encodeVars : List Support.VarId → Sx := encodeList encodeVar
def decodeVars : Sx → Option (List Support.VarId) := decodeList decodeVar
@[simp] theorem decode_encodeVars (x : List Support.VarId) : decodeVars (encodeVars x) = some x := by
  simp [encodeVars, decodeVars]

def encodeQuestions : List Support.QuestionId → Sx := encodeList encodeQuestion
def decodeQuestions : Sx → Option (List Support.QuestionId) := decodeList decodeQuestion
@[simp] theorem decode_encodeQuestions (x : List Support.QuestionId) : decodeQuestions (encodeQuestions x) = some x := by
  simp [encodeQuestions, decodeQuestions]

def encodeAPats : List Support.APat → Sx := encodeList encodeAPat
def decodeAPats : Sx → Option (List Support.APat) := decodeList decodeAPat
@[simp] theorem decode_encodeAPats (x : List Support.APat) : decodeAPats (encodeAPats x) = some x := by
  simp [encodeAPats, decodeAPats]

def encodeAPatPair : Support.APat × Support.APat → Sx := encodePair encodeAPat encodeAPat
def decodeAPatPair : Sx → Option (Support.APat × Support.APat) := decodePair decodeAPat decodeAPat
@[simp] theorem decode_encodeAPatPair (x : Support.APat × Support.APat) : decodeAPatPair (encodeAPatPair x) = some x := by
  simp [encodeAPatPair, decodeAPatPair]

def encodeBackend : Support.BackendId → Sx
  | .mk a0 a1 => tagged .backend [encodeText a0, encodeNat a1]
def decodeBackend : Sx → Option Support.BackendId
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .backend, [a0, a1] => do return .mk (← decodeText a0) (← decodeNat a1)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeBackend (x : Support.BackendId) : decodeBackend (encodeBackend x) = some x := by
  cases x; simp [encodeBackend, decodeBackend, tagged]

def encodeMode : Support.Mode → Sx
  | .strict => .atom Tag.strict.text
  | .defeasible => .atom Tag.defeasible.text
def decodeMode : Sx → Option Support.Mode
  | .atom t => match Tag.parse t with
    | some .strict => some .strict
    | some .defeasible => some .defeasible
    | _ => none
  | _ => none
@[simp] theorem decode_encodeMode (x : Support.Mode) : decodeMode (encodeMode x) = some x := by
  cases x <;> simp [encodeMode, decodeMode]

def encodePosElem : Attack.PosElem → Sx
  | .prem a0 => tagged .prem [encodeNat a0]
  | .ques a0 => tagged .ques [encodeQuestion a0]
def decodePosElem : Sx → Option Attack.PosElem
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .prem, [a0] => do return .prem (← decodeNat a0)
    | some .ques, [a0] => do return .ques (← decodeQuestion a0)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodePosElem (x : Attack.PosElem) : decodePosElem (encodePosElem x) = some x := by
  cases x <;> simp [encodePosElem, decodePosElem, tagged]

abbrev encodePosition := Driver.encodePos
def decodePosition : Sx → Option Attack.Pos
  | .list (.atom t :: xs) => if t = Driver.tagToString .pos then Wire.decodeList decodePosElem xs else none
  | _ => none
@[simp] theorem decode_encodePosition (p : Attack.Pos) : decodePosition (encodePosition p) = some p := by
  change decodePosition (coreNode .pos (p.map encodePosElem)) = some p
  simp [decodePosition, coreNode, Wire.decodeList_map]

def encodeLocation : Check.CheckLoc → Sx
  | .root => tagged .root []
  | .premise a0 a1 => tagged .premise [encodeLocation a0, encodeNat a1]
  | .question a0 a1 => tagged .question [encodeLocation a0, encodeQuestion a1]
def decodeLocation : Sx → Option Check.CheckLoc
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .root, [] => some .root
    | some .premise, [a0, a1] => do return .premise (← decodeLocation a0) (← decodeNat a1)
    | some .question, [a0, a1] => do return .question (← decodeLocation a0) (← decodeQuestion a1)
    | _, _ => none
  | _ => none
termination_by wire => sizeOf wire
@[simp] theorem decode_encodeLocation (x : Check.CheckLoc) : decodeLocation (encodeLocation x) = some x := by
  induction x <;> simp_all [encodeLocation, decodeLocation, tagged]

def encodeReferenceReason : Check.ReferenceReason → Sx
  | .missingLeaf a0 => tagged .missingLeaf [encodeCoreLeaf a0]
  | .missingRule a0 => tagged .missingRule [encodeRule a0]
  | .undeclaredAttackSource a0 => tagged .undeclaredAttackSource [encodeSupport a0]
  | .undeclaredAttackTarget a0 => tagged .undeclaredAttackTarget [encodeSupport a0]
def decodeReferenceReason : Sx → Option Check.ReferenceReason
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .missingLeaf, [a0] => do return .missingLeaf (← decodeCoreLeaf a0)
    | some .missingRule, [a0] => do return .missingRule (← decodeRule a0)
    | some .undeclaredAttackSource, [a0] => do return .undeclaredAttackSource (← decodeSupport a0)
    | some .undeclaredAttackTarget, [a0] => do return .undeclaredAttackTarget (← decodeSupport a0)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeReferenceReason (x : Check.ReferenceReason) : decodeReferenceReason (encodeReferenceReason x) = some x := by
  cases x <;> simp [encodeReferenceReason, decodeReferenceReason, tagged]

def encodeSubstitutionReason : Check.SubstitutionReason → Sx
  | .duplicateKeys a0 => tagged .duplicateKeys [encodeVars a0]
  | .domainMismatch a0 a1 => tagged .domainMismatch [encodeVars a0, encodeVars a1]
  | .premiseInstantiation a0 => tagged .premiseInstantiation [encodeAPats a0]
  | .conclusionInstantiation a0 => tagged .conclusionInstantiation [encodeAPat a0]
def decodeSubstitutionReason : Sx → Option Check.SubstitutionReason
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .duplicateKeys, [a0] => do return .duplicateKeys (← decodeVars a0)
    | some .domainMismatch, [a0, a1] => do return .domainMismatch (← decodeVars a0) (← decodeVars a1)
    | some .premiseInstantiation, [a0] => do return .premiseInstantiation (← decodeAPats a0)
    | some .conclusionInstantiation, [a0] => do return .conclusionInstantiation (← decodeAPat a0)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeSubstitutionReason (x : Check.SubstitutionReason) : decodeSubstitutionReason (encodeSubstitutionReason x) = some x := by
  cases x <;> simp [encodeSubstitutionReason, decodeSubstitutionReason, tagged]

def encodePremiseReason : Check.PremiseReason → Sx
  | .count a0 a1 => tagged .count [encodeNat a0, encodeNat a1]
  | .mismatch a0 a1 => tagged .mismatch [encodeAtom a0, encodeAtom a1]
def decodePremiseReason : Sx → Option Check.PremiseReason
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .count, [a0, a1] => do return .count (← decodeNat a0) (← decodeNat a1)
    | some .mismatch, [a0, a1] => do return .mismatch (← decodeAtom a0) (← decodeAtom a1)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodePremiseReason (x : Check.PremiseReason) : decodePremiseReason (encodePremiseReason x) = some x := by
  cases x <;> simp [encodePremiseReason, decodePremiseReason, tagged]

def encodeQuestionReason : Check.QuestionReason → Sx
  | .duplicateDeclarations a0 => tagged .duplicateDeclarations [encodeQuestions a0]
  | .duplicateDischarges a0 => tagged .duplicateDischarges [encodeQuestions a0]
  | .duplicateHoles a0 => tagged .duplicateHoles [encodeQuestions a0]
  | .uncovered a0 a1 a2 => tagged .uncovered [encodeQuestions a0, encodeQuestions a1, encodeQuestions a2]
  | .overlap a0 a1 => tagged .overlap [encodeQuestions a0, encodeQuestions a1]
  | .undeclaredDischarge a0 a1 => tagged .undeclaredDischarge [encodeQuestions a0, encodeQuestions a1]
  | .undeclaredHole a0 a1 => tagged .undeclaredHole [encodeQuestions a0, encodeQuestions a1]
def decodeQuestionReason : Sx → Option Check.QuestionReason
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .duplicateDeclarations, [a0] => do return .duplicateDeclarations (← decodeQuestions a0)
    | some .duplicateDischarges, [a0] => do return .duplicateDischarges (← decodeQuestions a0)
    | some .duplicateHoles, [a0] => do return .duplicateHoles (← decodeQuestions a0)
    | some .uncovered, [a0, a1, a2] => do return .uncovered (← decodeQuestions a0) (← decodeQuestions a1) (← decodeQuestions a2)
    | some .overlap, [a0, a1] => do return .overlap (← decodeQuestions a0) (← decodeQuestions a1)
    | some .undeclaredDischarge, [a0, a1] => do return .undeclaredDischarge (← decodeQuestions a0) (← decodeQuestions a1)
    | some .undeclaredHole, [a0, a1] => do return .undeclaredHole (← decodeQuestions a0) (← decodeQuestions a1)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeQuestionReason (x : Check.QuestionReason) : decodeQuestionReason (encodeQuestionReason x) = some x := by
  cases x <;> simp [encodeQuestionReason, decodeQuestionReason, tagged]

def encodeDischargeReason : Check.DischargeReason → Sx
  | .answerInstantiation a0 a1 => tagged .answerInstantiation [encodeQuestion a0, encodeAPat a1]
  | .conclusionMismatch a0 a1 a2 => tagged .conclusionMismatch [encodeQuestion a0, encodeAtom a1, encodeAtom a2]
def decodeDischargeReason : Sx → Option Check.DischargeReason
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .answerInstantiation, [a0, a1] => do return .answerInstantiation (← decodeQuestion a0) (← decodeAPat a1)
    | some .conclusionMismatch, [a0, a1, a2] => do return .conclusionMismatch (← decodeQuestion a0) (← decodeAtom a1) (← decodeAtom a2)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeDischargeReason (x : Check.DischargeReason) : decodeDischargeReason (encodeDischargeReason x) = some x := by
  cases x <;> simp [encodeDischargeReason, decodeDischargeReason, tagged]

def encodeAssuranceReason : Check.AssuranceReason → Sx
  | .questionsPresent a0 a1 => tagged .questionsPresent [encodeQuestions a0, encodeQuestions a1]
  | .wrongMode a0 a1 => tagged .wrongMode [encodeMode a0, encodeAssurance a1]
  | .trustedDisallowed => tagged .trustedDisallowed []
  | .certifierUnallowlisted a0 a1 => tagged .certifierUnallowlisted [encodeBackend a0, encodeDigest a1]
def decodeAssuranceReason : Sx → Option Check.AssuranceReason
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .questionsPresent, [a0, a1] => do return .questionsPresent (← decodeQuestions a0) (← decodeQuestions a1)
    | some .wrongMode, [a0, a1] => do return .wrongMode (← decodeMode a0) (← decodeAssurance a1)
    | some .trustedDisallowed, [] => some .trustedDisallowed
    | some .certifierUnallowlisted, [a0, a1] => do return .certifierUnallowlisted (← decodeBackend a0) (← decodeDigest a1)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeAssuranceReason (x : Check.AssuranceReason) : decodeAssuranceReason (encodeAssuranceReason x) = some x := by
  cases x <;> simp [encodeAssuranceReason, decodeAssuranceReason, tagged]

def encodeBackendReason : Check.BackendReason → Sx
  | .backendMissing a0 => tagged .backendMissing [encodeBackend a0]
  | .digestMissing a0 a1 => tagged .digestMissing [encodeBackend a0, encodeDigest a1]
  | .replayRejected a0 a1 a2 => tagged .replayRejected [encodeBackend a0, encodeDigest a1, encodeCertRef a2]
def decodeBackendReason : Sx → Option Check.BackendReason
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .backendMissing, [a0] => do return .backendMissing (← decodeBackend a0)
    | some .digestMissing, [a0, a1] => do return .digestMissing (← decodeBackend a0) (← decodeDigest a1)
    | some .replayRejected, [a0, a1, a2] => do return .replayRejected (← decodeBackend a0) (← decodeDigest a1) (← decodeCertRef a2)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeBackendReason (x : Check.BackendReason) : decodeBackendReason (encodeBackendReason x) = some x := by
  cases x <;> simp [encodeBackendReason, decodeBackendReason, tagged]

def encodeAttackKind : Check.AttackKind → Sx
  | .rebut => tagged .rebut []
  | .undercut => tagged .undercut []
  | .undermine => tagged .undermine []
def decodeAttackKind : Sx → Option Check.AttackKind
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .rebut, [] => some .rebut
    | some .undercut, [] => some .undercut
    | some .undermine, [] => some .undermine
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeAttackKind (x : Check.AttackKind) : decodeAttackKind (encodeAttackKind x) = some x := by
  cases x <;> simp [encodeAttackKind, decodeAttackKind, tagged]

def encodeOccurrenceKind : Check.AttackOccurrenceKind → Sx
  | .rule => tagged .rule []
  | .leaf => tagged .leaf []
def decodeOccurrenceKind : Sx → Option Check.AttackOccurrenceKind
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .rule, [] => some .rule
    | some .leaf, [] => some .leaf
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeOccurrenceKind (x : Check.AttackOccurrenceKind) : decodeOccurrenceKind (encodeOccurrenceKind x) = some x := by
  cases x <;> simp [encodeOccurrenceKind, decodeOccurrenceKind, tagged]

def encodePositionReason : Check.AttackPositionReason → Sx
  | .undefinedPosition => tagged .undefinedPosition []
  | .wrongOccurrenceKind a0 a1 => tagged .wrongOccurrenceKind [encodeOccurrenceKind a0, encodeOccurrenceKind a1]
def decodePositionReason : Sx → Option Check.AttackPositionReason
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .undefinedPosition, [] => some .undefinedPosition
    | some .wrongOccurrenceKind, [a0, a1] => do return .wrongOccurrenceKind (← decodeOccurrenceKind a0) (← decodeOccurrenceKind a1)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodePositionReason (x : Check.AttackPositionReason) : decodePositionReason (encodePositionReason x) = some x := by
  cases x <;> simp [encodePositionReason, decodePositionReason, tagged]

def encodeRelationReason : Check.AttackRelationReason → Sx
  | .missingTargetRule a0 => tagged .missingTargetRule [encodeRule a0]
  | .targetConclusionInstantiation a0 a1 => tagged .targetConclusionInstantiation [encodeRule a0, encodeAPat a1]
  | .missingTargetLeaf a0 => tagged .missingTargetLeaf [encodeCoreLeaf a0]
  | .strictTarget a0 => tagged .strictTarget [encodeRule a0]
  | .missingContrary a0 a1 => tagged .missingContrary [encodeAtom a0, encodeAtom a1]
  | .missingException a0 => tagged .missingException [encodeRule a0]
  | .exceptionInstantiation a0 a1 => tagged .exceptionInstantiation [encodeRule a0, encodeAPat a1]
  | .exceptionMismatch a0 a1 a2 => tagged .exceptionMismatch [encodeRule a0, encodeAtom a1, encodeAtom a2]
def decodeRelationReason : Sx → Option Check.AttackRelationReason
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .missingTargetRule, [a0] => do return .missingTargetRule (← decodeRule a0)
    | some .targetConclusionInstantiation, [a0, a1] => do return .targetConclusionInstantiation (← decodeRule a0) (← decodeAPat a1)
    | some .missingTargetLeaf, [a0] => do return .missingTargetLeaf (← decodeCoreLeaf a0)
    | some .strictTarget, [a0] => do return .strictTarget (← decodeRule a0)
    | some .missingContrary, [a0, a1] => do return .missingContrary (← decodeAtom a0) (← decodeAtom a1)
    | some .missingException, [a0] => do return .missingException (← decodeRule a0)
    | some .exceptionInstantiation, [a0, a1] => do return .exceptionInstantiation (← decodeRule a0) (← decodeAPat a1)
    | some .exceptionMismatch, [a0, a1, a2] => do return .exceptionMismatch (← decodeRule a0) (← decodeAtom a1) (← decodeAtom a2)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeRelationReason (x : Check.AttackRelationReason) : decodeRelationReason (encodeRelationReason x) = some x := by
  cases x <;> simp [encodeRelationReason, decodeRelationReason, tagged]

def encodeCheckError : Check.CheckError → Sx
  | .R1 a0 a1 => tagged .R1 [encodeLocation a0, encodeReferenceReason a1]
  | .R3 a0 a1 => tagged .R3 [encodeLocation a0, encodeSubstitutionReason a1]
  | .R4 a0 a1 => tagged .R4 [encodeLocation a0, encodePremiseReason a1]
  | .R5 a0 a1 => tagged .R5 [encodeLocation a0, encodeQuestionReason a1]
  | .R6 a0 a1 => tagged .R6 [encodeLocation a0, encodeDischargeReason a1]
  | .R7 a0 a1 => tagged .R7 [encodeLocation a0, encodeAssuranceReason a1]
  | .R10 a0 a1 a2 a3 => tagged .R10 [encodeLocation a0, encodePosition a1, encodeAttackKind a2, encodePositionReason a3]
  | .R11 a0 a1 a2 a3 => tagged .R11 [encodeLocation a0, encodePosition a1, encodeAttackKind a2, encodeRelationReason a3]
  | .R13 a0 a1 => tagged .R13 [encodeLocation a0, encodeBackendReason a1]
def decodeCheckError : Sx → Option Check.CheckError
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .R1, [a0, a1] => do return .R1 (← decodeLocation a0) (← decodeReferenceReason a1)
    | some .R3, [a0, a1] => do return .R3 (← decodeLocation a0) (← decodeSubstitutionReason a1)
    | some .R4, [a0, a1] => do return .R4 (← decodeLocation a0) (← decodePremiseReason a1)
    | some .R5, [a0, a1] => do return .R5 (← decodeLocation a0) (← decodeQuestionReason a1)
    | some .R6, [a0, a1] => do return .R6 (← decodeLocation a0) (← decodeDischargeReason a1)
    | some .R7, [a0, a1] => do return .R7 (← decodeLocation a0) (← decodeAssuranceReason a1)
    | some .R10, [a0, a1, a2, a3] => do return .R10 (← decodeLocation a0) (← decodePosition a1) (← decodeAttackKind a2) (← decodePositionReason a3)
    | some .R11, [a0, a1, a2, a3] => do return .R11 (← decodeLocation a0) (← decodePosition a1) (← decodeAttackKind a2) (← decodeRelationReason a3)
    | some .R13, [a0, a1] => do return .R13 (← decodeLocation a0) (← decodeBackendReason a1)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeCheckError (x : Check.CheckError) : decodeCheckError (encodeCheckError x) = some x := by
  cases x <;> simp [encodeCheckError, decodeCheckError, tagged]

def encodeDeclLoc : Check.DeclLoc → Sx
  | .argument a0 => tagged .argument [encodeNat a0]
  | .attack a0 => tagged .attack [encodeNat a0]
def decodeDeclLoc : Sx → Option Check.DeclLoc
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .argument, [a0] => do return .argument (← decodeNat a0)
    | some .attack, [a0] => do return .attack (← decodeNat a0)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeDeclLoc (x : Check.DeclLoc) : decodeDeclLoc (encodeDeclLoc x) = some x := by
  cases x <;> simp [encodeDeclLoc, decodeDeclLoc, tagged]

def encodeMissingConflict : Check.MissingConflict → Sx
  | .mk a0 a1 a2 a3 => tagged .missingConflict [encodeNat a0, encodeNat a1, encodeAtom a2, encodeAtom a3]
def decodeMissingConflict : Sx → Option Check.MissingConflict
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .missingConflict, [a0, a1, a2, a3] => do return .mk (← decodeNat a0) (← decodeNat a1) (← decodeAtom a2) (← decodeAtom a3)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeMissingConflict (x : Check.MissingConflict) : decodeMissingConflict (encodeMissingConflict x) = some x := by
  cases x; simp [encodeMissingConflict, decodeMissingConflict, tagged]

def encodeProgramError : Check.ProgramError → Sx
  | .rejection a0 a1 => tagged .rejection [encodeDeclLoc a0, encodeCheckError a1]
  | .duplicateArgument a0 a1 => tagged .duplicateArgument [encodeNat a0, encodeNat a1]
  | .missingConflict a0 => tagged .missingConflict [encodeMissingConflict a0]
def decodeProgramError : Sx → Option Check.ProgramError
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .rejection, [a0, a1] => do return .rejection (← decodeDeclLoc a0) (← decodeCheckError a1)
    | some .duplicateArgument, [a0, a1] => do return .duplicateArgument (← decodeNat a0) (← decodeNat a1)
    | some .missingConflict, [a0] => do return .missingConflict (← decodeMissingConflict a0)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeProgramError (x : Check.ProgramError) : decodeProgramError (encodeProgramError x) = some x := by
  cases x <;> simp [encodeProgramError, decodeProgramError, tagged]

def encodeDuplicateRule : Policy.DuplicateRule → Sx
  | .mk a0 a1 a2 => tagged .duplicateRule [encodeRule a0, encodeNat a1, encodeNat a2]
def decodeDuplicateRule : Sx → Option Policy.DuplicateRule
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .duplicateRule, [a0, a1, a2] => do return .mk (← decodeRule a0) (← decodeNat a1) (← decodeNat a2)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeDuplicateRule (x : Policy.DuplicateRule) : decodeDuplicateRule (encodeDuplicateRule x) = some x := by
  cases x; simp [encodeDuplicateRule, decodeDuplicateRule, tagged]

def encodeScopeViolation : Policy.ScopeViolation → Sx
  | .mk a0 a1 => tagged .scopeViolation [encodeRule a0, encodeVar a1]
def decodeScopeViolation : Sx → Option Policy.ScopeViolation
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .scopeViolation, [a0, a1] => do return .mk (← decodeRule a0) (← decodeVar a1)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeScopeViolation (x : Policy.ScopeViolation) : decodeScopeViolation (encodeScopeViolation x) = some x := by
  cases x; simp [encodeScopeViolation, decodeScopeViolation, tagged]

def encodeViolation : Policy.Violation → Sx
  | .mk a0 a1 a2 => tagged .policyViolation [encodeRule a0, encodeAPat a1, encodeAPatPair a2]
def decodeViolation : Sx → Option Policy.Violation
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .policyViolation, [a0, a1, a2] => do return .mk (← decodeRule a0) (← decodeAPat a1) (← decodeAPatPair a2)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeViolation (x : Policy.Violation) : decodeViolation (encodeViolation x) = some x := by
  cases x; simp [encodeViolation, decodeViolation, tagged]

def encodeSignatureFault : Check.Unit.SignatureFault → Sx
  | .malformedSigma => tagged .malformedSigma []
  | .policyIllSorted => tagged .policyIllSorted []
  | .groundIllSorted => tagged .groundIllSorted []
  | .argsIllSorted => tagged .argsIllSorted []
def decodeSignatureFault : Sx → Option Check.Unit.SignatureFault
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .malformedSigma, [] => some .malformedSigma
    | some .policyIllSorted, [] => some .policyIllSorted
    | some .groundIllSorted, [] => some .groundIllSorted
    | some .argsIllSorted, [] => some .argsIllSorted
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeSignatureFault (x : Check.Unit.SignatureFault) : decodeSignatureFault (encodeSignatureFault x) = some x := by
  cases x <;> simp [encodeSignatureFault, decodeSignatureFault, tagged]

def encodeUnitError : Check.Unit.UnitError → Sx
  | .duplicateRule a0 => tagged .duplicateRule [encodeDuplicateRule a0]
  | .signature a0 => tagged .signature [encodeSignatureFault a0]
  | .scopeViolation a0 => tagged .scopeViolation [encodeScopeViolation a0]
  | .policyViolation a0 => tagged .policyViolation [encodeViolation a0]
  | .program a0 => tagged .program [encodeProgramError a0]
def decodeUnitError : Sx → Option Check.Unit.UnitError
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .duplicateRule, [a0] => do return .duplicateRule (← decodeDuplicateRule a0)
    | some .signature, [a0] => do return .signature (← decodeSignatureFault a0)
    | some .scopeViolation, [a0] => do return .scopeViolation (← decodeScopeViolation a0)
    | some .policyViolation, [a0] => do return .policyViolation (← decodeViolation a0)
    | some .program, [a0] => do return .program (← decodeProgramError a0)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeUnitError (x : Check.Unit.UnitError) : decodeUnitError (encodeUnitError x) = some x := by
  cases x <;> simp [encodeUnitError, decodeUnitError, tagged]

def encodeSurfaceError : Surface.Error → Sx
  | .unsupported => tagged .unsupported []
  | .policyMismatch a0 a1 => tagged .policyMismatch [encodePolicyId a0, encodePolicyId a1]
  | .duplicateLeafId a0 => tagged .duplicateLeafId [encodeLeafId a0]
  | .duplicateArgId a0 => tagged .duplicateArgId [encodeArgId a0]
  | .duplicateClaimId a0 => tagged .duplicateClaimId [encodePropId a0]
  | .duplicateValueName a0 => tagged .duplicateValueName [encodeValueName a0]
  | .malformedRuleNamespace a0 => tagged .malformedRuleNamespace [encodeRuleId a0]
  | .invalidValueBinding a0 => tagged .invalidValueBinding [encodeValueName a0]
  | .invalidComparison a0 => tagged .invalidComparison [encodePropId a0]
  | .invalidInferredArgument a0 => tagged .invalidInferredArgument [encodeArgId a0]
  | .invalidNamedCertificate a0 => tagged .invalidNamedCertificate [encodeArgId a0]
  | .conclusionMismatch a0 a1 => tagged .conclusionMismatch [encodeArgId a0, encodePropId a1]
  | .challengeTargetUndeclared a0 => tagged .challengeTargetUndeclared [encodeArgId a0]
  | .invalidSurfaceAttack a0 a1 => tagged .invalidSurfaceAttack [encodeArgId a0, encodeArgId a1]
  | .unknownStatusClaim a0 => tagged .unknownStatusClaim [encodePropId a0]
  | .duplicateGroupId a0 => tagged .duplicateGroupId [encodeGroupId a0]
  | .groupRepeatedMember a0 a1 => tagged .groupRepeatedMember [encodeGroupId a0, encodeLeafId a1]
  | .groupTooFewMembers a0 => tagged .groupTooFewMembers [encodeGroupId a0]
  | .groupMemberUndeclared a0 a1 => tagged .groupMemberUndeclared [encodeGroupId a0, encodeLeafId a1]
  | .noncanonicalPremiseLabels a0 => tagged .noncanonicalPremiseLabels [encodeRuleId a0]
  | .duplicateAdmissionKey a0 a1 => tagged .duplicateAdmissionKey [encodeLeafKind a0, encodeProvenance a1]
  | .admissionRejected a0 => tagged .admissionRejected [encodeLeafId a0]
def decodeSurfaceError : Sx → Option Surface.Error
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .unsupported, [] => some .unsupported
    | some .policyMismatch, [a0, a1] => do return .policyMismatch (← decodePolicyId a0) (← decodePolicyId a1)
    | some .duplicateLeafId, [a0] => do return .duplicateLeafId (← decodeLeafId a0)
    | some .duplicateArgId, [a0] => do return .duplicateArgId (← decodeArgId a0)
    | some .duplicateClaimId, [a0] => do return .duplicateClaimId (← decodePropId a0)
    | some .duplicateValueName, [a0] => do return .duplicateValueName (← decodeValueName a0)
    | some .malformedRuleNamespace, [a0] => do return .malformedRuleNamespace (← decodeRuleId a0)
    | some .invalidValueBinding, [a0] => do return .invalidValueBinding (← decodeValueName a0)
    | some .invalidComparison, [a0] => do return .invalidComparison (← decodePropId a0)
    | some .invalidInferredArgument, [a0] => do return .invalidInferredArgument (← decodeArgId a0)
    | some .invalidNamedCertificate, [a0] => do return .invalidNamedCertificate (← decodeArgId a0)
    | some .conclusionMismatch, [a0, a1] => do return .conclusionMismatch (← decodeArgId a0) (← decodePropId a1)
    | some .challengeTargetUndeclared, [a0] => do return .challengeTargetUndeclared (← decodeArgId a0)
    | some .invalidSurfaceAttack, [a0, a1] => do return .invalidSurfaceAttack (← decodeArgId a0) (← decodeArgId a1)
    | some .unknownStatusClaim, [a0] => do return .unknownStatusClaim (← decodePropId a0)
    | some .duplicateGroupId, [a0] => do return .duplicateGroupId (← decodeGroupId a0)
    | some .groupRepeatedMember, [a0, a1] => do return .groupRepeatedMember (← decodeGroupId a0) (← decodeLeafId a1)
    | some .groupTooFewMembers, [a0] => do return .groupTooFewMembers (← decodeGroupId a0)
    | some .groupMemberUndeclared, [a0, a1] => do return .groupMemberUndeclared (← decodeGroupId a0) (← decodeLeafId a1)
    | some .noncanonicalPremiseLabels, [a0] => do return .noncanonicalPremiseLabels (← decodeRuleId a0)
    | some .duplicateAdmissionKey, [a0, a1] => do return .duplicateAdmissionKey (← decodeLeafKind a0) (← decodeProvenance a1)
    | some .admissionRejected, [a0] => do return .admissionRejected (← decodeLeafId a0)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeSurfaceError (x : Surface.Error) : decodeSurfaceError (encodeSurfaceError x) = some x := by
  cases x <;> simp [encodeSurfaceError, decodeSurfaceError, tagged]

def encodeSourceError : Surface.SourceError → Sx
  | .structural a0 => tagged .structural [encodeSurfaceError a0]
  | .evidence a0 => tagged .evidence [encodeLeafId a0]
  | .evidenceSyntax => tagged .evidenceSyntax []
  | .groupConflict a0 => tagged .groupConflict [encodeGroupId a0]
def decodeSourceError : Sx → Option Surface.SourceError
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .structural, [a0] => do return .structural (← decodeSurfaceError a0)
    | some .evidence, [a0] => do return .evidence (← decodeLeafId a0)
    | some .evidenceSyntax, [] => some .evidenceSyntax
    | some .groupConflict, [a0] => do return .groupConflict (← decodeGroupId a0)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeSourceError (x : Surface.SourceError) : decodeSourceError (encodeSourceError x) = some x := by
  cases x <;> simp [encodeSourceError, decodeSourceError, tagged]

def encodeStage : Evidence.Stage → Sx
  | .binding => tagged .binding []
  | .capture => tagged .capture []
  | .extraction => tagged .extraction []
def decodeStage : Sx → Option Evidence.Stage
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .binding, [] => some .binding
    | some .capture, [] => some .capture
    | some .extraction, [] => some .extraction
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeStage (x : Evidence.Stage) : decodeStage (encodeStage x) = some x := by
  cases x <;> simp [encodeStage, decodeStage, tagged]

def encodeAdmissionError : Evidence.AdmissionError → Sx
  | .mk a0 a1 a2 a3 => tagged .admissionError [encodeStage a0, encodeText a1, encodeObjectOption a2, encodeText a3]
def decodeAdmissionError : Sx → Option Evidence.AdmissionError
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .admissionError, [a0, a1, a2, a3] => do return .mk (← decodeStage a0) (← decodeText a1) (← decodeObjectOption a2) (← decodeText a3)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeAdmissionError (x : Evidence.AdmissionError) : decodeAdmissionError (encodeAdmissionError x) = some x := by
  cases x; simp [encodeAdmissionError, decodeAdmissionError, tagged]

def encodeSourceDiagnostic : Surface.SourceDiagnostic → Sx
  | .source a0 => tagged .source [encodeSourceError a0]
  | .evidence a0 => tagged .evidence [encodeAdmissionError a0]
  | .core a0 => tagged .core [encodeUnitError a0]
def decodeSourceDiagnostic : Sx → Option Surface.SourceDiagnostic
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .source, [a0] => do return .source (← decodeSourceError a0)
    | some .evidence, [a0] => do return .evidence (← decodeAdmissionError a0)
    | some .core, [a0] => do return .core (← decodeUnitError a0)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeSourceDiagnostic (x : Surface.SourceDiagnostic) : decodeSourceDiagnostic (encodeSourceDiagnostic x) = some x := by
  cases x <;> simp [encodeSourceDiagnostic, decodeSourceDiagnostic, tagged]

def encodeReplayError : ReplayError → Sx
  | .unsupportedCore a0 => tagged .unsupportedCore [encodeCoreVersion a0]
  | .policyMismatch => tagged .policyMismatch []
  | .backendMismatch => tagged .backendMismatch []
  | .duplicateBackend => tagged .duplicateBackend []
  | .unsupportedBackend a0 => tagged .unsupportedBackend [encodeBackendIdentity a0]
  | .duplicateTheory => tagged .duplicateTheory []
  | .theoryMismatch => tagged .theoryMismatch []
  | .artifactMismatch => tagged .artifactMismatch []
def decodeReplayError : Sx → Option ReplayError
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .unsupportedCore, [a0] => do return .unsupportedCore (← decodeCoreVersion a0)
    | some .policyMismatch, [] => some .policyMismatch
    | some .backendMismatch, [] => some .backendMismatch
    | some .duplicateBackend, [] => some .duplicateBackend
    | some .unsupportedBackend, [a0] => do return .unsupportedBackend (← decodeBackendIdentity a0)
    | some .duplicateTheory, [] => some .duplicateTheory
    | some .theoryMismatch, [] => some .theoryMismatch
    | some .artifactMismatch, [] => some .artifactMismatch
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeReplayError (x : ReplayError) : decodeReplayError (encodeReplayError x) = some x := by
  cases x <;> simp [encodeReplayError, decodeReplayError, tagged]

def encodeRejection : SourceRejection → Sx
  | .replay a0 => tagged .replay [encodeReplayError a0]
  | .source a0 => tagged .source [encodeSourceDiagnostic a0]
  | .missingEvidence a0 => tagged .missingEvidence [encodeLeafId a0]
  | .unselectedCertificate a0 a1 a2 => tagged .unselectedCertificate [encodeNat a0, encodeArgId a1, encodeBackend a2]
def decodeRejectionRaw : Sx → Option SourceRejection
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .replay, [a0] => do return .replay (← decodeReplayError a0)
    | some .source, [a0] => do return .source (← decodeSourceDiagnostic a0)
    | some .missingEvidence, [a0] => do return .missingEvidence (← decodeLeafId a0)
    | some .unselectedCertificate, [a0, a1, a2] => do return .unselectedCertificate (← decodeNat a0) (← decodeArgId a1) (← decodeBackend a2)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeRejectionRaw (x : SourceRejection) : decodeRejectionRaw (encodeRejection x) = some x := by
  cases x <;> simp [encodeRejection, decodeRejectionRaw, tagged]

def decodeRejection := Wire.canonical encodeRejection decodeRejectionRaw
@[simp] theorem decode_encodeRejection (x : SourceRejection) : decodeRejection (encodeRejection x) = some x :=
  Wire.canonical_roundtrip _ _ decode_encodeRejectionRaw x
theorem encodeRejection_injective : Function.Injective encodeRejection :=
  Wire.injective_of_roundtrip _ _ decode_encodeRejection
theorem decodeRejection_canonical {wire : Sx} {value : SourceRejection}
    (h : decodeRejection wire = some value) : encodeRejection value = wire :=
  Wire.canonical_sound _ _ h

def encodePublicStatus : Driver.PublicStatus → Sx
  | .published a0 => tagged .published [encodeStatus a0]
  | .evidenceBlocked a0 => tagged .evidenceBlocked [encodeStatus a0]
def decodePublicStatusRaw : Sx → Option Driver.PublicStatus
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .published, [a0] => do return .published (← decodeStatus a0)
    | some .evidenceBlocked, [a0] => do return .evidenceBlocked (← decodeStatus a0)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodePublicStatusRaw (x : Driver.PublicStatus) : decodePublicStatusRaw (encodePublicStatus x) = some x := by
  cases x <;> simp [encodePublicStatus, decodePublicStatusRaw, tagged]

def decodePublicStatus := Wire.canonical encodePublicStatus decodePublicStatusRaw
@[simp] theorem decode_encodePublicStatus (x : Driver.PublicStatus) : decodePublicStatus (encodePublicStatus x) = some x :=
  Wire.canonical_roundtrip _ _ decode_encodePublicStatusRaw x
theorem encodePublicStatus_injective : Function.Injective encodePublicStatus :=
  Wire.injective_of_roundtrip _ _ decode_encodePublicStatus
theorem decodePublicStatus_canonical {wire : Sx} {value : Driver.PublicStatus}
    (h : decodePublicStatus wire = some value) : encodePublicStatus value = wire :=
  Wire.canonical_sound _ _ h

def encodeQueryOutcome : QueryOutcome → Sx
  | .rejected a0 => tagged .rejected [encodeRejection a0]
  | .accepted a0 => tagged .accepted [encodePublicStatus a0]
def decodeQueryOutcomeRaw : Sx → Option QueryOutcome
  | .list (.atom t :: xs) => match Tag.parse t, xs with
    | some .rejected, [a0] => do return .rejected (← decodeRejectionRaw a0)
    | some .accepted, [a0] => do return .accepted (← decodePublicStatusRaw a0)
    | _, _ => none
  | _ => none
@[simp] theorem decode_encodeQueryOutcomeRaw (x : QueryOutcome) : decodeQueryOutcomeRaw (encodeQueryOutcome x) = some x := by
  cases x <;> simp [encodeQueryOutcome, decodeQueryOutcomeRaw, tagged]

def decodeQueryOutcome := Wire.canonical encodeQueryOutcome decodeQueryOutcomeRaw
@[simp] theorem decode_encodeQueryOutcome (x : QueryOutcome) : decodeQueryOutcome (encodeQueryOutcome x) = some x :=
  Wire.canonical_roundtrip _ _ decode_encodeQueryOutcomeRaw x
theorem encodeQueryOutcome_injective : Function.Injective encodeQueryOutcome :=
  Wire.injective_of_roundtrip _ _ decode_encodeQueryOutcome
theorem decodeQueryOutcome_canonical {wire : Sx} {value : QueryOutcome}
    (h : decodeQueryOutcome wire = some value) : encodeQueryOutcome value = wire :=
  Wire.canonical_sound _ _ h

theorem decodeRejection_unknown {tag : String} (xs : List Sx)
    (unknown : Tag.parse tag = none) :
    decodeRejection (.list (.atom tag :: xs)) = none := by
  simp [decodeRejection, Wire.canonical, decodeRejectionRaw, unknown]

theorem decodePublicStatus_unknown {tag : String} (xs : List Sx)
    (unknown : Tag.parse tag = none) :
    decodePublicStatus (.list (.atom tag :: xs)) = none := by
  simp [decodePublicStatus, Wire.canonical, decodePublicStatusRaw, unknown]

theorem decodeQueryOutcome_unknown {tag : String} (xs : List Sx)
    (unknown : Tag.parse tag = none) :
    decodeQueryOutcome (.list (.atom tag :: xs)) = none := by
  simp [decodeQueryOutcome, Wire.canonical, decodeQueryOutcomeRaw, unknown]

theorem encodeSourceDiagnostic_injective : Function.Injective encodeSourceDiagnostic :=
  Wire.injective_of_roundtrip _ _ decode_encodeSourceDiagnostic
theorem encodeSourceError_injective : Function.Injective encodeSourceError :=
  Wire.injective_of_roundtrip _ _ decode_encodeSourceError
theorem encodeSurfaceError_injective : Function.Injective encodeSurfaceError :=
  Wire.injective_of_roundtrip _ _ decode_encodeSurfaceError
theorem encodeAdmissionError_injective : Function.Injective encodeAdmissionError :=
  Wire.injective_of_roundtrip _ _ decode_encodeAdmissionError
theorem encodeUnitError_injective : Function.Injective encodeUnitError :=
  Wire.injective_of_roundtrip _ _ decode_encodeUnitError
theorem encodeCheckError_injective : Function.Injective encodeCheckError :=
  Wire.injective_of_roundtrip _ _ decode_encodeCheckError
theorem encodeReplayError_injective : Function.Injective encodeReplayError :=
  Wire.injective_of_roundtrip _ _ decode_encodeReplayError

end Lara.Process.Source.ResultWire
