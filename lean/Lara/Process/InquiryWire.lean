import Lara.Process.AnalysisWire
import Lara.Process.Impact
import Lara.Process.Run

/-!
The `inquiry-input 1` / `inquiry-result 1` / `inquiry-error 1` wrapper codecs
(issue #22, shared protocol).

The wrapper embeds an unchanged `process-input 1` document and a finite typed
source-choice family, so the five landed semantic stages (P1 source observer,
P2 bounded enumeration, P3 analyses, P4 locality, P5 impact) become reachable
from the file boundary. Nothing here interprets a document: decoding preserves
validity, never validates semantics and never invents defaults. Every field is a
typed record built from the stage codecs; names are interned by the same tables
the embedded `Process.Wire` document already declares.

This module owns the wrapper's own closed tag table and the codec surface for
the records the stages left unwired (`RunRefusal`, the inquiry limits, the
reference form, the request forms, the wrapped result envelope and the P5 impact
certificate/result and verification result). It restates no stage encoding: the
embedded document reuses `Process.Wire`, the source snapshots reuse
`Source.Wire`, slots/choices/guards/fragments reuse `Family.Wire`, the audit
configuration reuses `Source.AuditWire`, observables/targets/literals and the P3
result records reuse `Analysis.AnalysisWire`, and statuses/diagnostics reuse
`Source.ResultWire`.
-/

namespace Lara.Process.InquiryWire

open Lara.Driver (Sx)

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

abbrev Names := Process.Wire.Names
abbrev UniqueNames := Process.InquiryProcessWire.UniqueNames

/-- The public entry points of the composed sub-codecs, named once. -/
abbrev encodeDocument := Process.Wire.encodeDocument
abbrev decodeDocument := Process.Wire.decodeDocument
abbrev encodeSource := Source.Wire.encode
abbrev decodeSource := Source.Wire.decode
abbrev encodeSlot := Family.Wire.encodeSlot
abbrev decodeSlot := Family.Wire.decodeSlot
abbrev encodeChoice := Family.Wire.encodeChoice
abbrev decodeChoice := Family.Wire.decodeChoice
abbrev encodeGuard := Family.Wire.encodeGuard
abbrev decodeGuard := Family.Wire.decodeGuard
abbrev encodeFragment := Source.Wire.encodeFragment
abbrev decodeFragment := Source.Wire.decodeFragment
abbrev encodeStamped := Source.AuditWire.encodeStamped
abbrev decodeStamped := Source.AuditWire.decodeStamped
abbrev encodeClaimId := Source.AuditWire.encodeClaimId
abbrev decodeClaimId := Source.AuditWire.decodeClaimId
abbrev encodeWitnessId := Source.AuditWire.encodeWitnessId
abbrev decodeWitnessId := Source.AuditWire.decodeWitnessId
abbrev encodeProfileSpec := Analysis.AnalysisWire.encodeProfileSpec
abbrev decodeProfileSpec := Analysis.AnalysisWire.decodeProfileSpec
abbrev encodeObservableSpec := Analysis.AnalysisWire.encodeObservableSpec
abbrev decodeObservableSpec := Analysis.AnalysisWire.decodeObservableSpec
abbrev encodeTargetSpec := Analysis.AnalysisWire.encodeTargetSpec
abbrev decodeTargetSpec := Analysis.AnalysisWire.decodeTargetSpec
abbrev encodeLiteral := Analysis.AnalysisWire.encodeLiteral
abbrev decodeLiteral := Analysis.AnalysisWire.decodeLiteral
abbrev encodeStabilityResult := Analysis.AnalysisWire.encodeStabilityResult
abbrev decodeStabilityResult := Analysis.AnalysisWire.decodeStabilityResult
abbrev encodeSensitivityResult := Analysis.AnalysisWire.encodeSensitivityResult
abbrev decodeSensitivityResult := Analysis.AnalysisWire.decodeSensitivityResult
abbrev encodeAssumptionResult := Analysis.AnalysisWire.encodeAssumptionResult
abbrev decodeAssumptionResult := Analysis.AnalysisWire.decodeAssumptionResult
abbrev encodeRejection := Source.ResultWire.encodeRejection
abbrev decodeRejection := Source.ResultWire.decodeRejection
abbrev encodePublicStatus := Source.ResultWire.encodePublicStatus
abbrev decodePublicStatus := Source.ResultWire.decodePublicStatus
abbrev encodeAtom := Source.ResultWire.encodeAtom
abbrev decodeAtom := Source.ResultWire.decodeAtom
abbrev encodeArgId := Source.ResultWire.encodeArgId
abbrev decodeArgId := Source.ResultWire.decodeArgId
abbrev encodeCoreLeaf := Source.ResultWire.encodeCoreLeaf
abbrev decodeCoreLeaf := Source.ResultWire.decodeCoreLeaf
abbrev encodeBackend := Source.ResultWire.encodeBackend
abbrev decodeBackend := Source.ResultWire.decodeBackend
abbrev encodeObject := Source.ResultWire.encodeObject
abbrev decodeObject := Source.ResultWire.decodeObject
abbrev encodeCapture := Source.Wire.encodeCapture
abbrev decodeCapture := Source.Wire.decodeCapture
abbrev encodeReplay := Source.Wire.encodeReplay
abbrev decodeReplay := Source.Wire.decodeReplay

/-! ### One closed tag table -/

/-- The wrapper's own spelling vocabulary. Every tag spelled here heads a list
this module encodes; nested records keep the tag tables of the modules that own
them (`Process.Wire`, `Source.Wire`, `Family.Wire`, `Source.AuditWire`,
`Analysis.AnalysisWire`, `Source.ResultWire`). -/
inductive Tag where
  -- envelopes and input layout
  | inquiryInput | inquiryResult | inquiryError
  | process | baseSource | slots | slotTable | choiceTable | bindings | kindMetadata
  | admittedAssumptions | assumptionCatalog | inquiryLimits | requests
  | histories | sources | sourceBytes | declarations | searchSteps | pairs | subsets
  -- requests
  | reqStatus | reqAudit | reqStable | reqSensitivity | reqSlotsSensitive
  | reqMinimalAssumptions | reqImpact | reqVerifyImpact | queries
  -- references
  | reference | refHistory | refChoices | refEntry
  -- result envelope
  | bodyAnswer | bodyStatus | bodyAudit | bodyStability | bodySensitivity
  | bodySlotsSensitive | bodyAssumptions | bodyImpact | bodyVerification
  | familyStatusResult | familyAuditResult | familyRow | familyAuditRow
  | historyCount | verdict | rowStatus | rowAudit
  -- refusals
  | malformed | syntax | unsupported | version | usage | io | limit
  | counter | actual | cap
  -- impact / verification
  | side | before | after | transition | rejectedToRejected | rejectedToAccepted
  | acceptedToRejected | acceptedToAccepted
  | endpointReport | queryImpact | impactResult | impactCertificate
  | acceptedFlag | rejectionField | referenceCarrier | checkedCarrier | compiledCarrier
  | blockedQueries | supports | compiledNodes | queryAtom | beforeStatus | afterStatus
  | changedFlag | localityFlag | changed | unchanged | blockedBefore | blockedAfter
  | carrier | nodeDiff | edgeDiff | locality | reads
  | beforeInput | afterInput | beforeSnapshot | afterSnapshot | beforeIdentity | afterIdentity
  | beforeReport | afterReport
  | verified | invalidCertificate
  -- verification faults
  | mismatchedSnapshots | mismatchedIdentities | outcomeMismatch | statusMismatch
  | invalidSupports | invalidGraph | falseLocality | falseReadEvidence
  -- read keys and values
  | valAbsent | valAtom | valAtoms | valNat | valNats | valBool | valName | valNames
  | valText | valTexts | valSource
  | keyLeafContent | keyLeafMeta | keyRuleLookup | keyAdmissionLookup | keyAbsentLookup
  | keyGroupMember | keyGroupConflict | keyRawEndpoint | keyRetention | keySignature
  | keyPolicyContrary | keySubstitution | keyBackendTheory | keyBackendDigest
  | keyCertificateInput | keyPremiseSubterm | keyDischargeSubterm | keyConclusionEquiv
  | keySupportMember | keyHoleMember | keyReferenceCarrier | keyCheckedCarrier
  | keyCompiledCarrier | keyBlockedClosure | keyBlockedQuery | keySupportNodes
  | keyHoleNodes | keyAttackEdge | keyWholeInput
  deriving DecidableEq, Repr

def Tag.text : Tag → String
  | .inquiryInput => "inquiry-input" | .inquiryResult => "inquiry-result"
  | .inquiryError => "inquiry-error" | .process => "process" | .baseSource => "base"
  | .slots => "slots" | .slotTable => "slot" | .choiceTable => "choice"
  | .bindings => "bindings" | .kindMetadata => "kind-metadata"
  | .admittedAssumptions => "admitted-assumptions" | .assumptionCatalog => "assumption-catalog"
  | .inquiryLimits => "inquiry-limits" | .requests => "requests"
  | .histories => "histories" | .sources => "sources" | .sourceBytes => "source-bytes"
  | .declarations => "declarations" | .searchSteps => "search-steps" | .pairs => "pairs"
  | .subsets => "subsets"
  | .reqStatus => "status" | .reqAudit => "audit" | .reqStable => "stable"
  | .reqSensitivity => "sensitivity" | .reqSlotsSensitive => "slots-sensitive"
  | .reqMinimalAssumptions => "minimal-assumptions" | .reqImpact => "impact"
  | .reqVerifyImpact => "verify-impact" | .queries => "queries"
  | .reference => "reference" | .refHistory => "ref-history" | .refChoices => "ref-choices"
  | .refEntry => "ref-entry"
  | .bodyAnswer => "history-verdict" | .bodyStatus => "status-body"
  | .bodyAudit => "audit-body" | .bodyStability => "stability-body"
  | .bodySensitivity => "sensitivity-body" | .bodySlotsSensitive => "slots-sensitive-body"
  | .bodyAssumptions => "assumptions-body" | .bodyImpact => "impact-body"
  | .bodyVerification => "verification-body"
  | .familyStatusResult => "family-status-result" | .familyAuditResult => "family-audit-result"
  | .familyRow => "family-row" | .familyAuditRow => "family-audit-row"
  | .historyCount => "history-count" | .verdict => "verdict" | .rowStatus => "row-status"
  | .rowAudit => "row-audit"
  | .malformed => "malformed" | .syntax => "syntax" | .unsupported => "unsupported"
  | .version => "version" | .usage => "usage" | .io => "io" | .limit => "limit"
  | .counter => "counter" | .actual => "actual" | .cap => "cap"
  | .side => "side" | .before => "before" | .after => "after" | .transition => "transition"
  | .rejectedToRejected => "rejected-to-rejected"
  | .rejectedToAccepted => "rejected-to-accepted"
  | .acceptedToRejected => "accepted-to-rejected"
  | .acceptedToAccepted => "accepted-to-accepted"
  | .endpointReport => "endpoint-report" | .queryImpact => "query-impact"
  | .impactResult => "impact-result" | .impactCertificate => "impact-certificate"
  | .acceptedFlag => "accepted" | .rejectionField => "rejection"
  | .referenceCarrier => "reference-carrier" | .checkedCarrier => "checked-carrier"
  | .compiledCarrier => "compiled-carrier" | .blockedQueries => "blocked-queries"
  | .supports => "supports" | .compiledNodes => "compiled-nodes" | .queryAtom => "query"
  | .beforeStatus => "before-status" | .afterStatus => "after-status"
  | .changedFlag => "changed-flag" | .localityFlag => "locality-flag"
  | .changed => "changed-set" | .unchanged => "unchanged-set"
  | .blockedBefore => "blocked-before" | .blockedAfter => "blocked-after"
  | .carrier => "carrier" | .nodeDiff => "node-diff" | .edgeDiff => "edge-diff"
  | .locality => "locality-checks" | .reads => "reads"
  | .beforeInput => "before-input" | .afterInput => "after-input"
  | .beforeSnapshot => "before-snapshot" | .afterSnapshot => "after-snapshot"
  | .beforeIdentity => "before-identity" | .afterIdentity => "after-identity"
  | .beforeReport => "before-report" | .afterReport => "after-report"
  | .verified => "verified" | .invalidCertificate => "invalid-certificate"
  | .mismatchedSnapshots => "mismatched-snapshots"
  | .mismatchedIdentities => "mismatched-identities" | .outcomeMismatch => "outcome-mismatch"
  | .statusMismatch => "status-mismatch" | .invalidSupports => "invalid-supports"
  | .invalidGraph => "invalid-graph" | .falseLocality => "false-locality"
  | .falseReadEvidence => "false-read-evidence"
  | .valAbsent => "v-absent" | .valAtom => "v-atom" | .valAtoms => "v-atoms"
  | .valNat => "v-nat" | .valNats => "v-nats" | .valBool => "v-bool"
  | .valName => "v-name" | .valNames => "v-names" | .valText => "v-text"
  | .valTexts => "v-texts" | .valSource => "v-source"
  | .keyLeafContent => "k-leaf-content" | .keyLeafMeta => "k-leaf-meta"
  | .keyRuleLookup => "k-rule-lookup" | .keyAdmissionLookup => "k-admission-lookup"
  | .keyAbsentLookup => "k-absent-lookup" | .keyGroupMember => "k-group-member"
  | .keyGroupConflict => "k-group-conflict" | .keyRawEndpoint => "k-raw-endpoint"
  | .keyRetention => "k-retention" | .keySignature => "k-signature"
  | .keyPolicyContrary => "k-policy-contrary" | .keySubstitution => "k-substitution"
  | .keyBackendTheory => "k-backend-theory" | .keyBackendDigest => "k-backend-digest"
  | .keyCertificateInput => "k-certificate-input" | .keyPremiseSubterm => "k-premise-subterm"
  | .keyDischargeSubterm => "k-discharge-subterm" | .keyConclusionEquiv => "k-conclusion-equiv"
  | .keySupportMember => "k-support-member" | .keyHoleMember => "k-hole-member"
  | .keyReferenceCarrier => "k-reference-carrier" | .keyCheckedCarrier => "k-checked-carrier"
  | .keyCompiledCarrier => "k-compiled-carrier" | .keyBlockedClosure => "k-blocked-closure"
  | .keyBlockedQuery => "k-blocked-query" | .keySupportNodes => "k-support-nodes"
  | .keyHoleNodes => "k-hole-nodes" | .keyAttackEdge => "k-attack-edge"
  | .keyWholeInput => "k-whole-input"

def Tag.all : List Tag :=
  [.inquiryInput, .inquiryResult, .inquiryError, .process, .baseSource, .slots, .slotTable,
   .choiceTable, .bindings, .kindMetadata, .admittedAssumptions, .assumptionCatalog,
   .inquiryLimits, .requests, .histories, .sources, .sourceBytes, .declarations, .searchSteps,
   .pairs, .subsets, .reqStatus, .reqAudit, .reqStable, .reqSensitivity, .reqSlotsSensitive,
   .reqMinimalAssumptions, .reqImpact, .reqVerifyImpact, .queries, .reference, .refHistory,
   .refChoices, .refEntry, .bodyAnswer, .bodyStatus, .bodyAudit, .bodyStability, .bodySensitivity,
   .bodySlotsSensitive, .bodyAssumptions, .bodyImpact, .bodyVerification, .familyStatusResult,
   .familyAuditResult, .familyRow, .familyAuditRow, .historyCount, .verdict, .rowStatus, .rowAudit,
   .malformed, .syntax, .unsupported, .version, .usage, .io, .limit, .counter, .actual, .cap,
   .side, .before, .after, .transition, .rejectedToRejected, .rejectedToAccepted,
   .acceptedToRejected, .acceptedToAccepted, .endpointReport, .queryImpact, .impactResult,
   .impactCertificate, .acceptedFlag, .rejectionField, .referenceCarrier, .checkedCarrier,
   .compiledCarrier, .blockedQueries, .supports, .compiledNodes, .queryAtom, .beforeStatus,
   .afterStatus, .changedFlag, .localityFlag, .changed, .unchanged, .blockedBefore, .blockedAfter,
   .carrier, .nodeDiff, .edgeDiff, .locality, .reads, .beforeInput, .afterInput, .beforeSnapshot,
   .afterSnapshot, .beforeIdentity, .afterIdentity, .beforeReport, .afterReport, .verified,
   .invalidCertificate, .mismatchedSnapshots, .mismatchedIdentities, .outcomeMismatch,
   .statusMismatch, .invalidSupports, .invalidGraph, .falseLocality, .falseReadEvidence,
   .valAbsent, .valAtom, .valAtoms, .valNat, .valNats, .valBool, .valName, .valNames, .valText,
   .valTexts, .valSource, .keyLeafContent, .keyLeafMeta, .keyRuleLookup, .keyAdmissionLookup,
   .keyAbsentLookup, .keyGroupMember, .keyGroupConflict, .keyRawEndpoint, .keyRetention,
   .keySignature, .keyPolicyContrary, .keySubstitution, .keyBackendTheory, .keyBackendDigest,
   .keyCertificateInput, .keyPremiseSubterm, .keyDischargeSubterm, .keyConclusionEquiv,
   .keySupportMember, .keyHoleMember, .keyReferenceCarrier, .keyCheckedCarrier,
   .keyCompiledCarrier, .keyBlockedClosure, .keyBlockedQuery, .keySupportNodes, .keyHoleNodes,
   .keyAttackEdge, .keyWholeInput]

def Tag.spelling : Process.Wire.Spelling Tag := ⟨Tag.all, Tag.text⟩

def Tag.parse (s : String) : Option Tag := Tag.spelling.parse s

theorem Tag.spelling_complete (tag : Tag) : tag ∈ Tag.spelling.all := by cases tag <;> decide

theorem Tag.spelling_nodup : (Tag.spelling.all.map Tag.spelling.text).Nodup := by decide

@[simp] theorem Tag.parse_text (tag : Tag) : Tag.parse tag.text = some tag :=
  Tag.spelling.parse_text Tag.spelling_complete Tag.spelling_nodup tag

theorem Tag.parse_some {text : String} {tag : Tag} (h : Tag.parse text = some tag) :
    tag.text = text := Tag.spelling.parse_some h

theorem Tag.text_injective : Function.Injective Tag.text :=
  Tag.spelling.text_injective Tag.spelling_complete Tag.spelling_nodup

/-- A tagged list in this module's own closed vocabulary. -/
def tagged (tag : Tag) (args : List Sx) : Sx := .list (.atom tag.text :: args)

/-- The arity of every form this module emits: a tagged list must carry exactly
the listed arguments. -/
def head (e : Sx) : Option (Tag × List Sx) :=
  match e with
  | .list (.atom s :: args) => (Tag.parse s).map (·, args)
  | _ => none

@[simp] theorem head_tagged (tag : Tag) (args : List Sx) :
    head (.list (.atom tag.text :: args)) = some (tag, args) := by
  simp [head, Tag.parse_text]

theorem head_eq_some {e : Sx} {tag : Tag} {args : List Sx} (h : head e = some (tag, args)) :
    e = tagged tag args := by
  unfold head at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨t', ht, rfl, rfl⟩ := h
    rw [← Tag.parse_some ht]; rfl
  · cases h

/-! ### Option-level helpers (mirroring the landed codec style) -/

private theorem except_toOption_some {e : Except ε α} {a : α} :
    e.toOption = some a ↔ e = .ok a := by
  cases e <;> simp [Except.toOption]

private theorem bind_some_iff {x : Option α} {f : α → Option β} {b : β} :
    (x >>= f) = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp

private theorem pure_some_iff {a b : α} : (pure a : Option α) = some b ↔ a = b := by
  constructor
  · exact Option.some.inj
  · intro h; cases h; rfl

/-- The canonical natural spelling and its strict decoder, owned by the P0
result codec. -/
abbrev encodeNat := Source.ResultWire.encodeNat
abbrev decodeNat := Source.ResultWire.decodeNat

def encodeList (encode : α → Sx) (xs : List α) : Sx := .list (xs.map encode)

def decodeList (decode : Sx → Option α) : Sx → Option (List α)
  | .list xs => Source.Wire.decodeList decode xs
  | _ => none

@[simp] theorem decode_encodeList (encode : α → Sx) (decode : Sx → Option α)
    (h : ∀ a, decode (encode a) = some a) (xs : List α) :
    decodeList decode (encodeList encode xs) = some xs := by
  simp [decodeList, encodeList, Source.Wire.decodeList_map, h]

theorem decodeList_canonical (encode : α → Sx) (decode : Sx → Option α)
    (canonical : ∀ {wire a}, decode wire = some a → encode a = wire)
    {wires : List Sx} {values : List α}
    (h : Source.Wire.decodeList decode wires = some values) : values.map encode = wires := by
  induction wires generalizing values with
  | nil => simp only [Source.Wire.decodeList, Option.some.injEq] at h; subst h; rfl
  | cons wire wires ih =>
      simp only [Source.Wire.decodeList, bind_some_iff, pure_some_iff] at h
      obtain ⟨a, ha, rest, hr, rfl⟩ := h
      simp [canonical ha, ih hr]

theorem decodeList_map_of (encode : α → Sx) (decode : Sx → Option α) (p : α → Prop)
    (roundtrip : ∀ a, p a → decode (encode a) = some a) (values : List α)
    (valid : ∀ a ∈ values, p a) :
    Source.Wire.decodeList decode (values.map encode) = some values := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
      have ha := roundtrip a (valid a (by simp))
      have hrest := ih (fun x hx => valid x (by simp [hx]))
      simp [Source.Wire.decodeList, ha, hrest]

/-- The canonical decoder: only the unique canonical spelling is retained. -/
def canonical (encode : α → Sx) (decode : Sx → Option α) (wire : Sx) : Option α := do
  let value ← decode wire
  if encode value = wire then some value else none

theorem canonical_roundtrip (encode : α → Sx) (decode : Sx → Option α)
    (roundtrip : ∀ a, decode (encode a) = some a) (a : α) :
    canonical encode decode (encode a) = some a := by
  simp [canonical, roundtrip]

theorem canonical_roundtrip_of (encode : α → Sx) (decode : Sx → Option α) (p : α → Prop)
    (roundtrip : ∀ a, p a → decode (encode a) = some a) (a : α) (ha : p a) :
    canonical encode decode (encode a) = some a := by
  simp [canonical, roundtrip a ha]

theorem canonical_sound (encode : α → Sx) (decode : Sx → Option α)
    {wire : Sx} {a : α} (h : canonical encode decode wire = some a) : encode a = wire := by
  cases decoded : decode wire with
  | none => simp [canonical, decoded] at h
  | some value =>
      by_cases equal : encode value = wire
      · have value_eq : value = a := by simpa [canonical, decoded, equal] using h
        exact value_eq ▸ equal
      · simp [canonical, decoded, equal] at h

theorem injective_of_roundtrip (encode : α → Sx) (decode : Sx → Option α)
    (roundtrip : ∀ a, decode (encode a) = some a) : Function.Injective encode := by
  intro a b h
  have equality := congrArg decode h
  simpa only [roundtrip, Option.some.injEq] using equality

theorem injective_on_of_roundtrip (encode : α → Sx) (decode : Sx → Option α)
    (p : α → Prop) (roundtrip : ∀ a, p a → decode (encode a) = some a)
    {a b : α} (ha : p a) (hb : p b) (equal : encode a = encode b) : a = b := by
  have h := congrArg decode equal
  simpa only [roundtrip a ha, roundtrip b hb, Option.some.injEq] using h

/-- Exact arity: `tagged` never accepts a short or long argument list for a
form whose expected argument count is fixed. -/
def decodeArity (tag : Tag) (arity : Nat) (e : Sx) : Option (List Sx) :=
  match head e with
  | some (t, args) => if t = tag ∧ args.length = arity then some args else none
  | none => none

/-! ### The inquiry limits -/

/-- The whole-document inquiry budget. Every counter is the declared bound; the
checker ceiling is applied by the runner, not at decode. -/
structure InquiryLimits where
  histories : Nat
  sources : Nat
  sourceBytes : Nat
  declarations : Nat
  searchSteps : Nat
  pairs : Nat
  subsets : Nat
  deriving DecidableEq, Repr

def encodeLimitsField (tag : Tag) (n : Nat) : Sx := tagged tag [encodeNat n]

def decodeLimitsField (tag : Tag) : Sx → Option Nat
  | .list [.atom t, value] =>
      match Tag.parse t with
      | some t' => if t' = tag then decodeNat value else none
      | none => none
  | _ => none

theorem decode_encodeLimitsField (tag : Tag) (n : Nat) :
    decodeLimitsField tag (encodeLimitsField tag n) = some n := by
  simp [encodeLimitsField, decodeLimitsField, tagged, Tag.parse_text]

def encodeInquiryLimits (l : InquiryLimits) : Sx :=
  tagged .inquiryLimits [encodeLimitsField .histories l.histories,
    encodeLimitsField .sources l.sources, encodeLimitsField .sourceBytes l.sourceBytes,
    encodeLimitsField .declarations l.declarations, encodeLimitsField .searchSteps l.searchSteps,
    encodeLimitsField .pairs l.pairs, encodeLimitsField .subsets l.subsets]

def decodeInquiryLimitsRaw : Sx → Option InquiryLimits
  | .list [.atom t, h, s, sb, d, ss, p, sub] =>
      match Tag.parse t with
      | some t' => if t' = Tag.inquiryLimits then do
          return ⟨← decodeLimitsField .histories h, ← decodeLimitsField .sources s,
            ← decodeLimitsField .sourceBytes sb, ← decodeLimitsField .declarations d,
            ← decodeLimitsField .searchSteps ss, ← decodeLimitsField .pairs p,
            ← decodeLimitsField .subsets sub⟩
        else none
      | none => none
  | _ => none

def decodeInquiryLimits := canonical encodeInquiryLimits decodeInquiryLimitsRaw

theorem decode_encodeInquiryLimitsRaw (l : InquiryLimits) :
    decodeInquiryLimitsRaw (encodeInquiryLimits l) = some l := by
  obtain ⟨h, s, sb, d, ss, p, sub⟩ := l
  have hh := decode_encodeLimitsField .histories h
  have hs := decode_encodeLimitsField .sources s
  have hsb := decode_encodeLimitsField .sourceBytes sb
  have hd := decode_encodeLimitsField .declarations d
  have hss := decode_encodeLimitsField .searchSteps ss
  have hp := decode_encodeLimitsField .pairs p
  have hsub := decode_encodeLimitsField .subsets sub
  simp [encodeInquiryLimits, decodeInquiryLimitsRaw, tagged, Tag.parse_text, hh, hs, hsb, hd,
    hss, hp, hsub]

@[simp] theorem decode_encodeInquiryLimits (l : InquiryLimits) :
    decodeInquiryLimits (encodeInquiryLimits l) = some l :=
  canonical_roundtrip _ _ decode_encodeInquiryLimitsRaw l

theorem decodeInquiryLimits_canonical {wire : Sx} {l : InquiryLimits}
    (h : decodeInquiryLimits wire = some l) : encodeInquiryLimits l = wire :=
  canonical_sound _ _ h

theorem encodeInquiryLimits_injective : Function.Injective encodeInquiryLimits :=
  injective_of_roundtrip _ _ decode_encodeInquiryLimits

/-! ### Closed refusals -/

/-- The seven inquiry counters, spelled by the same tags as the limits record. -/
inductive LimitCounter where
  | histories | sources | sourceBytes | declarations | searchSteps | pairs | subsets
  deriving DecidableEq, Repr

def LimitCounter.text : LimitCounter → String
  | .histories => "histories" | .sources => "sources" | .sourceBytes => "source-bytes"
  | .declarations => "declarations" | .searchSteps => "search-steps" | .pairs => "pairs"
  | .subsets => "subsets"

def LimitCounter.spelling : Process.Wire.Spelling LimitCounter where
  all := [.histories, .sources, .sourceBytes, .declarations, .searchSteps, .pairs, .subsets]
  text := LimitCounter.text

theorem LimitCounter.spelling_complete (c : LimitCounter) : c ∈ LimitCounter.spelling.all := by
  cases c <;> decide

theorem LimitCounter.spelling_nodup :
    (LimitCounter.spelling.all.map LimitCounter.spelling.text).Nodup := by decide

@[simp] theorem LimitCounter.parse_text (c : LimitCounter) :
    LimitCounter.spelling.parse c.text = some c :=
  LimitCounter.spelling.parse_text LimitCounter.spelling_complete LimitCounter.spelling_nodup c

/-- A closed reason a whole inquiry run is refused. Text cases carry a diagnostic
string only; the structured `limit` case carries the counter and both numbers. -/
inductive RunRefusal where
  | malformed (detail : String)
  | syntaxError (detail : String)
  | unsupported (detail : String)
  | version (detail : String)
  | usage (detail : String)
  | io (detail : String)
  | limit (counter : LimitCounter) (actual cap : Nat)
  deriving DecidableEq, Repr

def encodeRunRefusal : RunRefusal → Sx
  | .malformed d => tagged .malformed [.atom d]
  | .syntaxError d => tagged .syntax [.atom d]
  | .unsupported d => tagged .unsupported [.atom d]
  | .version d => tagged .version [.atom d]
  | .usage d => tagged .usage [.atom d]
  | .io d => tagged .io [.atom d]
  | .limit c actual cap => tagged .limit [tagged .counter [.atom c.text],
      tagged .actual [encodeNat actual], tagged .cap [encodeNat cap]]

def decodeRunRefusalRaw : Sx → Option RunRefusal
  | .list [.atom t, .atom d] =>
      match Tag.parse t with
      | some .malformed => some (.malformed d)
      | some .syntax => some (.syntaxError d)
      | some .unsupported => some (.unsupported d)
      | some .version => some (.version d)
      | some .usage => some (.usage d)
      | some .io => some (.io d)
      | _ => none
  | .list [.atom t, .list [.atom ct, .atom cs], .list [.atom atg, actual], .list [.atom pt, cap]] =>
      match Tag.parse t, Tag.parse ct, Tag.parse atg, Tag.parse pt with
      | some .limit, some .counter, some .actual, some .cap =>
          (LimitCounter.spelling.parse cs).map fun c =>
            RunRefusal.limit c ((decodeNat actual).getD 0) ((decodeNat cap).getD 0)
      | _, _, _, _ => none
  | _ => none

def decodeRunRefusal := canonical encodeRunRefusal decodeRunRefusalRaw

theorem decode_encodeRunRefusalRaw (r : RunRefusal) :
    decodeRunRefusalRaw (encodeRunRefusal r) = some r := by
  cases r with
  | malformed d => simp [encodeRunRefusal, decodeRunRefusalRaw, tagged, Tag.parse_text]
  | syntaxError d => simp [encodeRunRefusal, decodeRunRefusalRaw, tagged, Tag.parse_text]
  | unsupported d => simp [encodeRunRefusal, decodeRunRefusalRaw, tagged, Tag.parse_text]
  | version d => simp [encodeRunRefusal, decodeRunRefusalRaw, tagged, Tag.parse_text]
  | usage d => simp [encodeRunRefusal, decodeRunRefusalRaw, tagged, Tag.parse_text]
  | io d => simp [encodeRunRefusal, decodeRunRefusalRaw, tagged, Tag.parse_text]
  | limit c actual cap =>
      have hc := LimitCounter.parse_text c
      simp [encodeRunRefusal, decodeRunRefusalRaw, tagged, Tag.parse_text, hc,
        Source.ResultWire.decode_encodeNat]

@[simp] theorem decode_encodeRunRefusal (r : RunRefusal) :
    decodeRunRefusal (encodeRunRefusal r) = some r :=
  canonical_roundtrip _ _ decode_encodeRunRefusalRaw r

theorem decodeRunRefusal_canonical {wire : Sx} {r : RunRefusal}
    (h : decodeRunRefusal wire = some r) : encodeRunRefusal r = wire :=
  canonical_sound _ _ h

theorem encodeRunRefusal_injective : Function.Injective encodeRunRefusal :=
  injective_of_roundtrip _ _ decode_encodeRunRefusal

/-! ### P5 impact, read keys and verification (type-level data) -/

abbrev encodeBool := Source.AuditWire.encodeBool
abbrev decodeBool := Source.AuditWire.decodeBool
abbrev encodeOpt {α : Type} : (α → Sx) → Option α → Sx := Analysis.AnalysisWire.encodeOpt
abbrev decodeOpt {α : Type} : (Sx → Option α) → Sx → Option (Option α) := Analysis.AnalysisWire.decodeOpt
abbrev encodePair {α β : Type} : (α → Sx) → (β → Sx) → α × β → Sx := Analysis.AnalysisWire.encodePair
abbrev decodePair {α β : Type} : (Sx → Option α) → (Sx → Option β) → Sx → Option (α × β) :=
  Analysis.AnalysisWire.decodePair
abbrev encodeText := Source.ResultWire.encodeText
abbrev decodeText := Source.ResultWire.decodeText

def encodeSide : Impact.Side → Sx
  | .before => tagged .side [.atom "before"]
  | .after => tagged .side [.atom "after"]

def decodeSideRaw : Sx → Option Impact.Side
  | .list [.atom t, .atom s] =>
      match Tag.parse t with
      | some .side => if s = "before" then some .before else if s = "after" then some .after else none
      | _ => none
  | _ => none

def decodeSide := canonical encodeSide decodeSideRaw

@[simp] theorem decode_encodeSide (s : Impact.Side) : decodeSide (encodeSide s) = some s := by
  cases s <;>
    simp [encodeSide, decodeSide, canonical, decodeSideRaw, tagged, Tag.parse_text]

theorem decodeSide_canonical {wire : Sx} {s : Impact.Side}
    (h : decodeSide wire = some s) : encodeSide s = wire := canonical_sound _ _ h

theorem encodeSide_injective : Function.Injective encodeSide :=
  injective_of_roundtrip _ _ decode_encodeSide

def encodeImpactTransition : Impact.ImpactTransition → Sx
  | .rejectedToRejected => tagged .transition [.atom "rejected-to-rejected"]
  | .rejectedToAccepted => tagged .transition [.atom "rejected-to-accepted"]
  | .acceptedToRejected => tagged .transition [.atom "accepted-to-rejected"]
  | .acceptedToAccepted => tagged .transition [.atom "accepted-to-accepted"]

def decodeImpactTransitionRaw : Sx → Option Impact.ImpactTransition
  | .list [.atom t, .atom s] =>
      match Tag.parse t with
      | some .transition =>
          if s = "rejected-to-rejected" then some .rejectedToRejected
          else if s = "rejected-to-accepted" then some .rejectedToAccepted
          else if s = "accepted-to-rejected" then some .acceptedToRejected
          else if s = "accepted-to-accepted" then some .acceptedToAccepted
          else none
      | _ => none
  | _ => none

def decodeImpactTransition := canonical encodeImpactTransition decodeImpactTransitionRaw

@[simp] theorem decode_encodeImpactTransition (t : Impact.ImpactTransition) :
    decodeImpactTransition (encodeImpactTransition t) = some t := by
  cases t <;> simp [encodeImpactTransition, decodeImpactTransition, canonical, decodeImpactTransitionRaw,
    tagged, Tag.parse_text]

theorem decodeImpactTransition_canonical {wire : Sx} {t : Impact.ImpactTransition}
    (h : decodeImpactTransition wire = some t) : encodeImpactTransition t = wire :=
  canonical_sound _ _ h

theorem encodeImpactTransition_injective : Function.Injective encodeImpactTransition :=
  injective_of_roundtrip _ _ decode_encodeImpactTransition

def encodeVerificationFault : Impact.VerificationFault → Sx
  | .mismatchedSnapshots => tagged .mismatchedSnapshots []
  | .mismatchedIdentities => tagged .mismatchedIdentities []
  | .outcomeMismatch => tagged .outcomeMismatch []
  | .statusMismatch => tagged .statusMismatch []
  | .invalidSupports => tagged .invalidSupports []
  | .invalidGraph => tagged .invalidGraph []
  | .falseLocality => tagged .falseLocality []
  | .falseReadEvidence => tagged .falseReadEvidence []

def decodeVerificationFaultRaw : Sx → Option Impact.VerificationFault
  | .list [.atom t] =>
      match Tag.parse t with
      | some .mismatchedSnapshots => some .mismatchedSnapshots
      | some .mismatchedIdentities => some .mismatchedIdentities
      | some .outcomeMismatch => some .outcomeMismatch
      | some .statusMismatch => some .statusMismatch
      | some .invalidSupports => some .invalidSupports
      | some .invalidGraph => some .invalidGraph
      | some .falseLocality => some .falseLocality
      | some .falseReadEvidence => some .falseReadEvidence
      | _ => none
  | _ => none

def decodeVerificationFault := canonical encodeVerificationFault decodeVerificationFaultRaw

@[simp] theorem decode_encodeVerificationFault (f : Impact.VerificationFault) :
    decodeVerificationFault (encodeVerificationFault f) = some f := by
  cases f <;>
    simp [encodeVerificationFault, decodeVerificationFault, canonical, decodeVerificationFaultRaw,
      tagged, Tag.parse_text]

theorem decodeVerificationFault_canonical {wire : Sx} {f : Impact.VerificationFault}
    (h : decodeVerificationFault wire = some f) : encodeVerificationFault f = wire :=
  canonical_sound _ _ h

theorem encodeVerificationFault_injective : Function.Injective encodeVerificationFault :=
  injective_of_roundtrip _ _ decode_encodeVerificationFault

def encodeVerificationResult : Impact.VerificationResult → Sx
  | .verified => tagged .verified []
  | .invalidCertificate f => tagged .invalidCertificate [encodeVerificationFault f]

def decodeVerificationResultRaw : Sx → Option Impact.VerificationResult
  | .list [.atom t] =>
      match Tag.parse t with
      | some .verified => some .verified
      | _ => none
  | .list [.atom t, fault] =>
      match Tag.parse t with
      | some .invalidCertificate => (decodeVerificationFault fault).map Impact.VerificationResult.invalidCertificate
      | _ => none
  | _ => none

def decodeVerificationResult := canonical encodeVerificationResult decodeVerificationResultRaw

@[simp] theorem decode_encodeVerificationResult (r : Impact.VerificationResult) :
    decodeVerificationResult (encodeVerificationResult r) = some r := by
  cases r with
  | verified => simp [encodeVerificationResult, decodeVerificationResult, canonical,
      decodeVerificationResultRaw, tagged, Tag.parse_text]
  | invalidCertificate f =>
      simp [encodeVerificationResult, decodeVerificationResult, canonical,
        decodeVerificationResultRaw, tagged, Tag.parse_text, decode_encodeVerificationFault]

theorem decodeVerificationResult_canonical {wire : Sx} {r : Impact.VerificationResult}
    (h : decodeVerificationResult wire = some r) : encodeVerificationResult r = wire :=
  canonical_sound _ _ h

theorem encodeVerificationResult_injective : Function.Injective encodeVerificationResult :=
  injective_of_roundtrip _ _ decode_encodeVerificationResult

/-- `(side S) (read-key ...) (read-val ...)` triples. -/
def encodeReadKey : Impact.ReadKey → Sx
  | .leafContent l => tagged .keyLeafContent [encodeCoreLeaf l]
  | .leafMeta l => tagged .keyLeafMeta [encodeCoreLeaf l]
  | .ruleLookup a => tagged .keyRuleLookup [encodeArgId a]
  | .admissionLookup a => tagged .keyAdmissionLookup [encodeArgId a]
  | .absentLookup a => tagged .keyAbsentLookup [encodeArgId a]
  | .groupMember a => tagged .keyGroupMember [encodeArgId a]
  | .groupConflict a => tagged .keyGroupConflict [encodeArgId a]
  | .rawEndpoint n => tagged .keyRawEndpoint [encodeNat n]
  | .retention n => tagged .keyRetention [encodeNat n]
  | .signature a => tagged .keySignature [encodeArgId a]
  | .policyContrary a => tagged .keyPolicyContrary [encodeArgId a]
  | .substitution a => tagged .keySubstitution [encodeArgId a]
  | .backendTheory b => tagged .keyBackendTheory [encodeBackend b]
  | .backendDigest b => tagged .keyBackendDigest [encodeBackend b]
  | .certificateInput b => tagged .keyCertificateInput [encodeBackend b]
  | .premiseSubterm n => tagged .keyPremiseSubterm [encodeNat n]
  | .dischargeSubterm n => tagged .keyDischargeSubterm [encodeNat n]
  | .conclusionEquiv a => tagged .keyConclusionEquiv [encodeArgId a]
  | .supportMember q n => tagged .keySupportMember [encodeAtom q, encodeNat n]
  | .holeMember q n => tagged .keyHoleMember [encodeAtom q, encodeNat n]
  | .referenceCarrier => tagged .keyReferenceCarrier []
  | .checkedCarrier => tagged .keyCheckedCarrier []
  | .compiledCarrier => tagged .keyCompiledCarrier []
  | .blockedClosure => tagged .keyBlockedClosure []
  | .blockedQuery q => tagged .keyBlockedQuery [encodeAtom q]
  | .supportNodes q => tagged .keySupportNodes [encodeAtom q]
  | .holeNodes q => tagged .keyHoleNodes [encodeAtom q]
  | .attackEdge a b => tagged .keyAttackEdge [encodeNat a, encodeNat b]
  | .wholeInput => tagged .keyWholeInput []

def encodeReadVal : Impact.ReadVal → Sx
  | .absent => tagged .valAbsent []
  | .atom a => tagged .valAtom [encodeAtom a]
  | .atoms l => tagged .valAtoms [encodeList encodeAtom l]
  | .nat n => tagged .valNat [encodeNat n]
  | .nats l => tagged .valNats [encodeList encodeNat l]
  | .bool b => tagged .valBool [encodeBool b]
  | .name a => tagged .valName [encodeArgId a]
  | .names l => tagged .valNames [encodeList encodeArgId l]
  | .text s => tagged .valText [.atom s]
  | .texts l => tagged .valTexts [encodeList encodeText l]
  | .source i => tagged .valSource [encodeSource i]

def decodeReadKeyRaw : Sx → Option Impact.ReadKey
  | .list (.atom t :: args) =>
      match Tag.parse t, args with
      | some .keyLeafContent, [l] => (decodeCoreLeaf l).map Impact.ReadKey.leafContent
      | some .keyLeafMeta, [l] => (decodeCoreLeaf l).map Impact.ReadKey.leafMeta
      | some .keyRuleLookup, [a] => (decodeArgId a).map Impact.ReadKey.ruleLookup
      | some .keyAdmissionLookup, [a] => (decodeArgId a).map Impact.ReadKey.admissionLookup
      | some .keyAbsentLookup, [a] => (decodeArgId a).map Impact.ReadKey.absentLookup
      | some .keyGroupMember, [a] => (decodeArgId a).map Impact.ReadKey.groupMember
      | some .keyGroupConflict, [a] => (decodeArgId a).map Impact.ReadKey.groupConflict
      | some .keyRawEndpoint, [n] => (decodeNat n).map Impact.ReadKey.rawEndpoint
      | some .keyRetention, [n] => (decodeNat n).map Impact.ReadKey.retention
      | some .keySignature, [a] => (decodeArgId a).map Impact.ReadKey.signature
      | some .keyPolicyContrary, [a] => (decodeArgId a).map Impact.ReadKey.policyContrary
      | some .keySubstitution, [a] => (decodeArgId a).map Impact.ReadKey.substitution
      | some .keyBackendTheory, [b] => (decodeBackend b).map Impact.ReadKey.backendTheory
      | some .keyBackendDigest, [b] => (decodeBackend b).map Impact.ReadKey.backendDigest
      | some .keyCertificateInput, [b] => (decodeBackend b).map Impact.ReadKey.certificateInput
      | some .keyPremiseSubterm, [n] => (decodeNat n).map Impact.ReadKey.premiseSubterm
      | some .keyDischargeSubterm, [n] => (decodeNat n).map Impact.ReadKey.dischargeSubterm
      | some .keyConclusionEquiv, [a] => (decodeArgId a).map Impact.ReadKey.conclusionEquiv
      | some .keySupportMember, [q, n] =>
          (match decodeAtom q, decodeNat n with
           | some a, some k => some (Impact.ReadKey.supportMember a k) | _, _ => none)
      | some .keyHoleMember, [q, n] =>
          (match decodeAtom q, decodeNat n with
           | some a, some k => some (Impact.ReadKey.holeMember a k) | _, _ => none)
      | some .keyReferenceCarrier, [] => some .referenceCarrier
      | some .keyCheckedCarrier, [] => some .checkedCarrier
      | some .keyCompiledCarrier, [] => some .compiledCarrier
      | some .keyBlockedClosure, [] => some .blockedClosure
      | some .keyBlockedQuery, [q] => (decodeAtom q).map Impact.ReadKey.blockedQuery
      | some .keySupportNodes, [q] => (decodeAtom q).map Impact.ReadKey.supportNodes
      | some .keyHoleNodes, [q] => (decodeAtom q).map Impact.ReadKey.holeNodes
      | some .keyAttackEdge, [a, b] =>
          (match decodeNat a, decodeNat b with
           | some x, some y => some (Impact.ReadKey.attackEdge x y) | _, _ => none)
      | some .keyWholeInput, [] => some .wholeInput
      | _, _ => none
  | _ => none

def decodeReadValRaw : Sx → Option Impact.ReadVal
  | .list (.atom t :: args) =>
      match Tag.parse t, args with
      | some .valAbsent, [] => some .absent
      | some .valAtom, [a] => (decodeAtom a).map Impact.ReadVal.atom
      | some .valAtoms, [l] => (decodeList decodeAtom l).map Impact.ReadVal.atoms
      | some .valNat, [n] => (decodeNat n).map Impact.ReadVal.nat
      | some .valNats, [l] => (decodeList decodeNat l).map Impact.ReadVal.nats
      | some .valBool, [b] => (decodeBool b).map Impact.ReadVal.bool
      | some .valName, [a] => (decodeArgId a).map Impact.ReadVal.name
      | some .valNames, [l] => (decodeList decodeArgId l).map Impact.ReadVal.names
      | some .valText, [s] => (decodeText s).map Impact.ReadVal.text
      | some .valTexts, [l] => (decodeList decodeText l).map Impact.ReadVal.texts
      | some .valSource, [i] => (decodeSource i).map Impact.ReadVal.source
      | _, _ => none
  | _ => none

def decodeReadKey := canonical encodeReadKey decodeReadKeyRaw
def decodeReadVal := canonical encodeReadVal decodeReadValRaw

@[simp] theorem decode_encodeReadKey (k : Impact.ReadKey) :
    decodeReadKey (encodeReadKey k) = some k := by
  cases k <;>
    simp [encodeReadKey, decodeReadKey, canonical, decodeReadKeyRaw, tagged, Tag.parse_text,
      Source.ResultWire.decode_encodeCoreLeaf, Source.ResultWire.decode_encodeArgId,
      Source.ResultWire.decode_encodeBackend, Source.ResultWire.decode_encodeAtom,
      Source.ResultWire.decode_encodeNat]

@[simp] theorem decode_encodeReadVal (v : Impact.ReadVal) :
    decodeReadVal (encodeReadVal v) = some v := by
  cases v with
  | absent => simp [encodeReadVal, decodeReadVal, canonical, decodeReadValRaw, tagged, Tag.parse_text]
  | atom a => simp [encodeReadVal, decodeReadVal, canonical, decodeReadValRaw, tagged, Tag.parse_text,
      Source.ResultWire.decode_encodeAtom]
  | atoms l => simp [encodeReadVal, decodeReadVal, canonical, decodeReadValRaw, tagged, Tag.parse_text,
      decode_encodeList, Source.ResultWire.decode_encodeAtom]
  | nat n => simp [encodeReadVal, decodeReadVal, canonical, decodeReadValRaw, tagged, Tag.parse_text,
      Source.ResultWire.decode_encodeNat]
  | nats l => simp [encodeReadVal, decodeReadVal, canonical, decodeReadValRaw, tagged, Tag.parse_text,
      decode_encodeList, Source.ResultWire.decode_encodeNat]
  | bool b => simp [encodeReadVal, decodeReadVal, canonical, decodeReadValRaw, tagged, Tag.parse_text,
      Source.AuditWire.decode_encodeBool]
  | name a => simp [encodeReadVal, decodeReadVal, canonical, decodeReadValRaw, tagged, Tag.parse_text,
      Source.ResultWire.decode_encodeArgId]
  | names l => simp [encodeReadVal, decodeReadVal, canonical, decodeReadValRaw, tagged, Tag.parse_text,
      decode_encodeList, Source.ResultWire.decode_encodeArgId]
  | text s => simp [encodeReadVal, decodeReadVal, canonical, decodeReadValRaw, tagged, Tag.parse_text,
      Source.ResultWire.decodeText, Source.ResultWire.encodeText]
  | texts l => simp [encodeReadVal, decodeReadVal, canonical, decodeReadValRaw, tagged, Tag.parse_text,
      decode_encodeList, Source.ResultWire.decodeText, Source.ResultWire.encodeText,
      Source.ResultWire.decode_encodeText]
  | source i => simp [encodeReadVal, decodeReadVal, canonical, decodeReadValRaw, tagged, Tag.parse_text,
      Source.Wire.decode_encode]

theorem decodeReadKey_canonical {wire : Sx} {k : Impact.ReadKey}
    (h : decodeReadKey wire = some k) : encodeReadKey k = wire := canonical_sound _ _ h

theorem decodeReadVal_canonical {wire : Sx} {v : Impact.ReadVal}
    (h : decodeReadVal wire = some v) : encodeReadVal v = wire := canonical_sound _ _ h

theorem encodeReadKey_injective : Function.Injective encodeReadKey :=
  injective_of_roundtrip _ _ decode_encodeReadKey

theorem encodeReadVal_injective : Function.Injective encodeReadVal :=
  injective_of_roundtrip _ _ decode_encodeReadVal

def encodeReadEntry (e : Impact.Side × Impact.ReadKey × Impact.ReadVal) : Sx :=
  match e with
  | ⟨side, key, value⟩ => tagged .reads [encodeSide side, encodeReadKey key, encodeReadVal value]

def decodeReadEntryRaw : Sx → Option (Impact.Side × Impact.ReadKey × Impact.ReadVal)
  | .list [.atom t, side, key, value] =>
      match Tag.parse t with
      | some .reads =>
          (match decodeSide side, decodeReadKey key, decodeReadVal value with
           | some s, some k, some v => some (s, k, v)
           | _, _, _ => none)
      | _ => none
  | _ => none

def decodeReadEntry := canonical encodeReadEntry decodeReadEntryRaw

@[simp] theorem decode_encodeReadEntryRaw (e : Impact.Side × Impact.ReadKey × Impact.ReadVal) :
    decodeReadEntryRaw (encodeReadEntry e) = some e := by
  obtain ⟨s, k, v⟩ := e
  simp [encodeReadEntry, decodeReadEntryRaw, tagged, Tag.parse_text, decode_encodeSide,
    decode_encodeReadKey, decode_encodeReadVal]

@[simp] theorem decode_encodeReadEntry (e : Impact.Side × Impact.ReadKey × Impact.ReadVal) :
    decodeReadEntry (encodeReadEntry e) = some e :=
  canonical_roundtrip _ _ decode_encodeReadEntryRaw e

theorem decodeReadEntry_canonical {wire : Sx} {e : Impact.Side × Impact.ReadKey × Impact.ReadVal}
    (h : decodeReadEntry wire = some e) : encodeReadEntry e = wire := canonical_sound _ _ h

/-- The read log is a set: the encoder enumerates it (`Finset.toList`), and the
decoder rebuilds the same set from any enumeration. -/
noncomputable def encodeReads (s : Finset (Impact.Side × Impact.ReadKey × Impact.ReadVal)) : Sx :=
  encodeList encodeReadEntry s.toList

def decodeReads : Sx → Option (Finset (Impact.Side × Impact.ReadKey × Impact.ReadVal))
  | .list xs => (Source.Wire.decodeList decodeReadEntry xs).map List.toFinset
  | _ => none

theorem decode_encodeReads (s : Finset (Impact.Side × Impact.ReadKey × Impact.ReadVal)) :
    decodeReads (encodeReads s) = some s := by
  have h := Source.Wire.decodeList_map encodeReadEntry decodeReadEntry
    (fun e => decode_encodeReadEntry e) s.toList
  show (Source.Wire.decodeList decodeReadEntry (s.toList.map encodeReadEntry)).map
    List.toFinset = some s
  rw [h]
  exact congrArg some (Finset.toList_toFinset s)

def encodeSnapshot (s : Evidence.Snapshot) : Sx :=
  encodeList Source.Wire.encodeSnapshotEntry s

def decodeSnapshot : Sx → Option Evidence.Snapshot :=
  decodeList Source.Wire.decodeSnapshotEntry

@[simp] theorem decode_encodeSnapshot (s : Evidence.Snapshot) :
    decodeSnapshot (encodeSnapshot s) = some s := by
  show Source.Wire.decodeList Source.Wire.decodeSnapshotEntry
    (s.map Source.Wire.encodeSnapshotEntry) = some s
  exact Source.Wire.decodeList_map _ _ Source.Wire.decode_encodeSnapshotEntry s

def encodeArgIds (l : List Presentation.ArgId) : Sx := encodeList encodeArgId l
def decodeArgIds : Sx → Option (List Presentation.ArgId) := decodeList decodeArgId

@[simp] theorem decode_encodeArgIds (l : List Presentation.ArgId) :
    decodeArgIds (encodeArgIds l) = some l := by
  unfold encodeArgIds decodeArgIds
  exact decode_encodeList encodeArgId decodeArgId
    (fun a => Source.ResultWire.decode_encodeArgId a) l

def encodeAtoms (l : List Atom) : Sx := encodeList encodeAtom l
def decodeAtoms : Sx → Option (List Atom) := decodeList decodeAtom

@[simp] theorem decode_encodeAtoms (l : List Atom) : decodeAtoms (encodeAtoms l) = some l := by
  unfold encodeAtoms decodeAtoms
  exact decode_encodeList encodeAtom decodeAtom (fun a => Source.ResultWire.decode_encodeAtom a) l

def encodeNats (l : List Nat) : Sx := encodeList encodeNat l
def decodeNats : Sx → Option (List Nat) := decodeList decodeNat

@[simp] theorem decode_encodeNats (l : List Nat) : decodeNats (encodeNats l) = some l := by
  unfold encodeNats decodeNats
  exact decode_encodeList encodeNat decodeNat (fun a => Source.ResultWire.decode_encodeNat a) l

def encodeEndpointReport (r : Impact.EndpointReport) : Sx :=
  tagged .endpointReport [encodeBool r.accepted, encodeOpt encodeRejection r.rejection,
    encodeNats r.referenceCarrier, encodeNats r.checkedCarrier, encodeNats r.compiledCarrier,
    encodeAtoms r.blocked, encodeList (encodePair encodeAtom encodeArgIds) r.supports]

def decodeEndpointReportRaw : Sx → Option Impact.EndpointReport
  | .list [.atom t, accepted, rejection, refc, chkc, compc, blocked, supports] =>
      match Tag.parse t with
      | some .endpointReport => do
          return ⟨← decodeBool accepted, ← decodeOpt decodeRejection rejection,
            ← decodeNats refc, ← decodeNats chkc, ← decodeNats compc,
            ← decodeAtoms blocked, ← decodeList (decodePair decodeAtom decodeArgIds) supports⟩
      | _ => none
  | _ => none

def decodeEndpointReport := canonical encodeEndpointReport decodeEndpointReportRaw

@[simp] theorem decode_encodeEndpointReportRaw (r : Impact.EndpointReport) :
    decodeEndpointReportRaw (encodeEndpointReport r) = some r := by
  obtain ⟨accepted, rejection, refc, chkc, compc, blocked, supports⟩ := r
  simp [encodeEndpointReport, decodeEndpointReportRaw, tagged, Tag.parse_text,
    Source.AuditWire.decode_encodeBool, Analysis.AnalysisWire.decode_encodeOpt,
    Source.ResultWire.decode_encodeRejection, decode_encodeNats, decode_encodeAtoms,
    decode_encodeList, Analysis.AnalysisWire.decode_encodePair, Source.ResultWire.decode_encodeAtom,
    decode_encodeArgIds]

@[simp] theorem decode_encodeEndpointReport (r : Impact.EndpointReport) :
    decodeEndpointReport (encodeEndpointReport r) = some r :=
  canonical_roundtrip _ _ decode_encodeEndpointReportRaw r

theorem decodeEndpointReport_canonical {wire : Sx} {r : Impact.EndpointReport}
    (h : decodeEndpointReport wire = some r) : encodeEndpointReport r = wire :=
  canonical_sound _ _ h

theorem encodeEndpointReport_injective : Function.Injective encodeEndpointReport :=
  injective_of_roundtrip _ _ decode_encodeEndpointReport

def encodeQueryImpact (q : Impact.QueryImpact) : Sx :=
  tagged .queryImpact [encodeAtom q.query, encodeOpt encodePublicStatus q.beforeStatus,
    encodeOpt encodePublicStatus q.afterStatus, encodeBool q.changed, encodeBool q.localityAccepted]

def decodeQueryImpactRaw : Sx → Option Impact.QueryImpact
  | .list [.atom t, query, before, after, changed, locality] =>
      match Tag.parse t with
      | some .queryImpact => do
          return ⟨← decodeAtom query, ← decodeOpt decodePublicStatus before,
            ← decodeOpt decodePublicStatus after, ← decodeBool changed, ← decodeBool locality⟩
      | _ => none
  | _ => none

def decodeQueryImpact := canonical encodeQueryImpact decodeQueryImpactRaw

@[simp] theorem decode_encodeQueryImpactRaw (q : Impact.QueryImpact) :
    decodeQueryImpactRaw (encodeQueryImpact q) = some q := by
  obtain ⟨query, before, after, changed, locality⟩ := q
  simp [encodeQueryImpact, decodeQueryImpactRaw, tagged, Tag.parse_text,
    Source.ResultWire.decode_encodeAtom, Analysis.AnalysisWire.decode_encodeOpt,
    Source.ResultWire.decode_encodePublicStatus, Source.AuditWire.decode_encodeBool]

@[simp] theorem decode_encodeQueryImpact (q : Impact.QueryImpact) :
    decodeQueryImpact (encodeQueryImpact q) = some q :=
  canonical_roundtrip _ _ decode_encodeQueryImpactRaw q

theorem decodeQueryImpact_canonical {wire : Sx} {q : Impact.QueryImpact}
    (h : decodeQueryImpact wire = some q) : encodeQueryImpact q = wire :=
  canonical_sound _ _ h

theorem encodeQueryImpact_injective : Function.Injective encodeQueryImpact :=
  injective_of_roundtrip _ _ decode_encodeQueryImpact

def encodeImpactResult (r : Impact.ImpactResult) : Sx :=
  tagged .impactResult [encodeImpactTransition r.transition,
    encodeList encodeQueryImpact r.rows, encodeAtoms r.changed, encodeAtoms r.unchanged]

def decodeImpactResultRaw : Sx → Option Impact.ImpactResult
  | .list [.atom t, transition, rows, changed, unchanged] =>
      match Tag.parse t with
      | some .impactResult => do
          return ⟨← decodeImpactTransition transition, ← decodeList decodeQueryImpact rows,
            ← decodeAtoms changed, ← decodeAtoms unchanged⟩
      | _ => none
  | _ => none

def decodeImpactResult := canonical encodeImpactResult decodeImpactResultRaw

@[simp] theorem decode_encodeImpactResultRaw (r : Impact.ImpactResult) :
    decodeImpactResultRaw (encodeImpactResult r) = some r := by
  obtain ⟨transition, rows, changed, unchanged⟩ := r
  simp [encodeImpactResult, decodeImpactResultRaw, tagged, Tag.parse_text,
    decode_encodeImpactTransition, decode_encodeList, decode_encodeQueryImpact,
    decode_encodeAtoms]

@[simp] theorem decode_encodeImpactResult (r : Impact.ImpactResult) :
    decodeImpactResult (encodeImpactResult r) = some r :=
  canonical_roundtrip _ _ decode_encodeImpactResultRaw r

theorem decodeImpactResult_canonical {wire : Sx} {r : Impact.ImpactResult}
    (h : decodeImpactResult wire = some r) : encodeImpactResult r = wire :=
  canonical_sound _ _ h

theorem encodeImpactResult_injective : Function.Injective encodeImpactResult :=
  injective_of_roundtrip _ _ decode_encodeImpactResult

/-- The wire form of `Impact.ImpactCertificate`: the same typed data, with the
read log carried as its ordered enumeration (a certificate is pure data with no
names table, so this codec round-trips unconditionally). The runner calls
`toCertificate` to recover the set-valued semantic record. -/
structure ImpactCertificateWire where
  beforeInput : Source.SourceInput
  afterInput : Source.SourceInput
  queries : List Atom
  beforeSnapshot : Evidence.Snapshot
  afterSnapshot : Evidence.Snapshot
  beforeIdentity : Source.ReplayIdentity
  afterIdentity : Source.ReplayIdentity
  beforeReport : Impact.EndpointReport
  afterReport : Impact.EndpointReport
  transition : Impact.ImpactTransition
  rows : List Impact.QueryImpact
  changed : List Atom
  unchanged : List Atom
  blockedBefore : List Atom
  blockedAfter : List Atom
  carrier : List Presentation.ArgId
  nodeDiff : List Grounded.Arg
  edgeDiff : List (Grounded.Arg × Grounded.Arg)
  locality : List (Atom × Bool)
  reads : List (Impact.Side × Impact.ReadKey × Impact.ReadVal)
  deriving DecidableEq

def ImpactCertificateWire.toCertificate (c : ImpactCertificateWire) : Impact.ImpactCertificate :=
  { beforeInput := c.beforeInput, afterInput := c.afterInput, queries := c.queries,
    beforeSnapshot := c.beforeSnapshot, afterSnapshot := c.afterSnapshot,
    beforeIdentity := c.beforeIdentity, afterIdentity := c.afterIdentity,
    beforeReport := c.beforeReport, afterReport := c.afterReport, transition := c.transition,
    rows := c.rows, changed := c.changed, unchanged := c.unchanged,
    blockedBefore := c.blockedBefore, blockedAfter := c.blockedAfter, carrier := c.carrier,
    nodeDiff := c.nodeDiff, edgeDiff := c.edgeDiff, locality := c.locality,
    reads := c.reads.toFinset }

def encodeImpactCertificate (c : ImpactCertificateWire) : Sx :=
  tagged .impactCertificate [encodeSource c.beforeInput, encodeSource c.afterInput,
    encodeAtoms c.queries, encodeSnapshot c.beforeSnapshot, encodeSnapshot c.afterSnapshot,
    encodeReplay c.beforeIdentity, encodeReplay c.afterIdentity,
    encodeEndpointReport c.beforeReport, encodeEndpointReport c.afterReport,
    encodeImpactTransition c.transition, encodeList encodeQueryImpact c.rows,
    encodeAtoms c.changed, encodeAtoms c.unchanged, encodeAtoms c.blockedBefore,
    encodeAtoms c.blockedAfter, encodeArgIds c.carrier, encodeNats c.nodeDiff,
    encodeList (encodePair encodeNat encodeNat) c.edgeDiff,
    encodeList (encodePair encodeAtom encodeBool) c.locality, encodeList encodeReadEntry c.reads]

def decodeImpactCertificateRaw : Sx → Option ImpactCertificateWire
  | .list [.atom t, beforeInput, afterInput, queries, beforeSnap, afterSnap, beforeId, afterId,
      beforeRep, afterRep, transition, rows, changed, unchanged, blockedBefore, blockedAfter,
      carrier, nodeDiff, edgeDiff, locality, reads] =>
      match Tag.parse t with
      | some .impactCertificate => do
          return {
            beforeInput := ← decodeSource beforeInput, afterInput := ← decodeSource afterInput,
            queries := ← decodeAtoms queries, beforeSnapshot := ← decodeSnapshot beforeSnap,
            afterSnapshot := ← decodeSnapshot afterSnap, beforeIdentity := ← decodeReplay beforeId,
            afterIdentity := ← decodeReplay afterId, beforeReport := ← decodeEndpointReport beforeRep,
            afterReport := ← decodeEndpointReport afterRep,
            transition := ← decodeImpactTransition transition, rows := ← decodeList decodeQueryImpact rows,
            changed := ← decodeAtoms changed, unchanged := ← decodeAtoms unchanged,
            blockedBefore := ← decodeAtoms blockedBefore, blockedAfter := ← decodeAtoms blockedAfter,
            carrier := ← decodeArgIds carrier, nodeDiff := ← decodeNats nodeDiff,
            edgeDiff := ← decodeList (decodePair decodeNat decodeNat) edgeDiff,
            locality := ← decodeList (decodePair decodeAtom decodeBool) locality,
            reads := ← decodeList decodeReadEntry reads }
      | _ => none
  | _ => none

def decodeImpactCertificate := canonical encodeImpactCertificate decodeImpactCertificateRaw

theorem decode_encodeImpactCertificateRaw (c : ImpactCertificateWire) :
    decodeImpactCertificateRaw (encodeImpactCertificate c) = some c := by
  obtain ⟨bi, ai, queries, bsnap, asnap, bid, aid, brep, arep, transition, rows, changed,
    unchanged, blockedBefore, blockedAfter, carrier, nodeDiff, edgeDiff, locality, reads⟩ := c
  simp [encodeImpactCertificate, decodeImpactCertificateRaw, tagged, Tag.parse_text,
    Source.Wire.decode_encode, decode_encodeAtoms, decode_encodeSnapshot,
    Source.Wire.decode_encodeReplay, decode_encodeEndpointReport, decode_encodeImpactTransition,
    decode_encodeList, decode_encodeQueryImpact, decode_encodeArgIds, decode_encodeNats,
    Analysis.AnalysisWire.decode_encodePair, Source.ResultWire.decode_encodeNat, Source.ResultWire.decode_encodeAtom,
    Source.AuditWire.decode_encodeBool, decode_encodeReadEntry]

@[simp] theorem decode_encodeImpactCertificate (c : ImpactCertificateWire) :
    decodeImpactCertificate (encodeImpactCertificate c) = some c :=
  canonical_roundtrip _ _ decode_encodeImpactCertificateRaw c

theorem decodeImpactCertificate_canonical {wire : Sx} {c : ImpactCertificateWire}
    (h : decodeImpactCertificate wire = some c) : encodeImpactCertificate c = wire :=
  canonical_sound _ _ h

theorem encodeImpactCertificate_injective : Function.Injective encodeImpactCertificate :=
  injective_of_roundtrip _ _ decode_encodeImpactCertificate


/-! ### The embedded P0 verdict answer -/

/-- The P0 verdict answer as the `process-result` spelling determines it: a
verdict, a completion count, and the held/failed histories as their event
identities (the P0 spelling records no bodies). The encoder is byte-for-byte
`Process.Wire.encodeAnswer` after projecting a semantic `Answer`. -/
structure OutcomeAnswer where
  verdict : Verdict
  count : Nat
  holds : Option (List EventId)
  fails : Option (List EventId)
  deriving DecidableEq, Repr

def OutcomeAnswer.ofAnswer (a : Universe.Answer) : OutcomeAnswer :=
  { verdict := a.verdict, count := a.count,
    holds := a.holds.map (List.map Stamped.id), fails := a.fails.map (List.map Stamped.id) }

/-- The structural bound the P0 answer's identity histories need. -/
def HistoriesWellNamed (n : Names) (h : Option (List EventId)) : Prop :=
  ∀ hs, h = some hs → ∀ e ∈ hs, e.index < n.event.length

def OutcomeAnswerWellNamed (n : Names) (a : OutcomeAnswer) : Prop :=
  HistoriesWellNamed n a.holds ∧ HistoriesWellNamed n a.fails

def encodeIdentities (n : Names) (h : List EventId) : Sx :=
  Process.Wire.tagged Process.Wire.Tag.history (h.map fun e => Process.Wire.encodeIdx n.event e.index)

def decodeIdentities (n : Names) : Sx → Option (List EventId)
  | e =>
    match Process.Wire.head e with
    | some (Process.Wire.Tag.history, args) =>
        decodeList (fun x => (Process.Wire.decodeIdx n.event "event" x).toOption.map EventId.mk) (Sx.list args)
    | _ => none

@[simp] theorem decode_encodeIdentities (n : Names) (unique : UniqueNames n) (h : List EventId)
    (bound : ∀ e ∈ h, e.index < n.event.length) :
    decodeIdentities n (encodeIdentities n h) = some h := by
  simp only [encodeIdentities, decodeIdentities, Process.InquiryProcessWire.head_tagged]
  exact decodeList_map_of (fun e : EventId => Process.Wire.encodeIdx n.event e.index)
    (fun x => (Process.Wire.decodeIdx n.event "event" x).toOption.map EventId.mk)
    (fun e => e.index < n.event.length)
    (fun e he => by
      cases e
      simp [Process.InquiryProcessWire.decode_encodeIdx _ unique.1 "event" _ he, Except.toOption])
    h bound

def encodeOptTagged (n : Names) (tag : Process.Wire.Tag) : Option (List EventId) → List Sx
  | none => []
  | some hs => [Process.Wire.tagged tag [encodeIdentities n hs]]

theorem encodeOptTagged_eq (n : Names) (tag : Process.Wire.Tag) (h : Option (List EventId)) :
    encodeOptTagged n tag h =
      (h.map fun hs => Process.Wire.tagged tag [encodeIdentities n hs]).toList := by
  cases h <;> rfl

def encodeOutcomeAnswer (n : Names) (label : String) (a : OutcomeAnswer) : Sx :=
  Process.Wire.tagged Process.Wire.Tag.answer
    ([.atom label, .atom (Process.Wire.Verdict.spelling.text a.verdict),
      Process.Wire.encodeField Process.Wire.Tag.completions a.count] ++
     encodeOptTagged n Process.Wire.Tag.holds a.holds ++
     encodeOptTagged n Process.Wire.Tag.fails a.fails)

def decodeOptTagged (n : Names) (tag : Process.Wire.Tag) :
    List Sx → Option (Option (List EventId) × List Sx)
  | [] => some (none, [])
  | e :: rest =>
    match Process.Wire.head e with
    | some (t, [arg]) =>
        if t = tag then (decodeIdentities n arg).map (fun h => (some h, rest))
        else some (none, e :: rest)
    | _ => some (none, e :: rest)

def decodeOutcomeAnswerRaw (n : Names) : Sx → Option OutcomeAnswer
  | e =>
    match Process.Wire.head e with
    | some (Process.Wire.Tag.answer, _ :: verdict :: completions :: rest) =>
        (match (Process.Wire.decodeWord Process.Wire.Verdict.spelling "verdict" verdict).toOption with
         | some v =>
           (match (Process.Wire.decodeField Process.Wire.Tag.completions completions).toOption with
            | some count =>
              (match decodeOptTagged n Process.Wire.Tag.holds rest with
               | some (h, rest1) =>
                 (match decodeOptTagged n Process.Wire.Tag.fails rest1 with
                  | some (f, rest2) => if rest2 = [] then some ⟨v, count, h, f⟩ else none
                  | none => none)
               | none => none)
            | none => none)
         | none => none)
    | _ => none

theorem decode_encodeOutcomeAnswerRaw (n : Names) (unique : UniqueNames n) (label : String)
    (a : OutcomeAnswer) (valid : OutcomeAnswerWellNamed n a) :
    decodeOutcomeAnswerRaw n (encodeOutcomeAnswer n label a) = some a := by
  obtain ⟨v, count, holds, fails⟩ := a
  obtain ⟨hh, hf⟩ := valid
  have hv : (Process.Wire.decodeWord Process.Wire.Verdict.spelling "verdict"
      (.atom (Process.Wire.Verdict.spelling.text v))).toOption = some v := by
    simp [InquiryProcessWire.decode_encodeWord Process.Wire.Verdict.spelling
      Process.Wire.Verdict.spelling_complete Process.Wire.Verdict.spelling_nodup "verdict"]
  have hc : (Process.Wire.decodeField Process.Wire.Tag.completions
      (Process.Wire.encodeField Process.Wire.Tag.completions count)).toOption = some count := by
    simp [Process.Wire.decodeField, Process.Wire.encodeField]
  cases holds with
  | none =>
      cases fails with
      | none => simp [encodeOutcomeAnswer, encodeOptTagged, decodeOutcomeAnswerRaw, decodeOptTagged,
          Process.InquiryProcessWire.head_tagged, hv, hc]
      | some fs => simp [encodeOutcomeAnswer, encodeOptTagged, decodeOutcomeAnswerRaw, decodeOptTagged,
          Process.InquiryProcessWire.head_tagged, hv, hc,
          decode_encodeIdentities n unique fs (hf fs rfl)]
  | some hs =>
      cases fails with
      | none => simp [encodeOutcomeAnswer, encodeOptTagged, decodeOutcomeAnswerRaw, decodeOptTagged,
          Process.InquiryProcessWire.head_tagged, hv, hc,
          decode_encodeIdentities n unique hs (hh hs rfl)]
      | some fs => simp [encodeOutcomeAnswer, encodeOptTagged, decodeOutcomeAnswerRaw, decodeOptTagged,
          Process.InquiryProcessWire.head_tagged, hv, hc,
          decode_encodeIdentities n unique hs (hh hs rfl),
          decode_encodeIdentities n unique fs (hf fs rfl)]

/-- The wire answer for a projected semantic `Answer` is exactly the P0
`process-result` answer bytes. -/
theorem encodeOutcomeAnswer_ofAnswer (n : Names) (label : String) (a : Universe.Answer) :
    encodeOutcomeAnswer n label (OutcomeAnswer.ofAnswer a) =
      Process.Wire.encodeAnswer n (label, a) := by
  obtain ⟨verdict, count, holds, fails⟩ := a
  cases holds <;> cases fails <;>
    simp [encodeOutcomeAnswer, OutcomeAnswer.ofAnswer, Process.Wire.encodeAnswer, encodeOptTagged,
      Process.Wire.encodeHistory, encodeIdentities, List.map_map, Function.comp_def, Stamped.id]

/-! ### References, requests and the wrapper input -/

def version : String := "1"

/-- `(reference (ref-history STAMPED...) (ref-choices (SLOT CHOICE)...))`. -/
structure ReferenceSpec where
  history : List Stamped
  assignment : List (Family.SlotId × Family.ChoiceId)
  deriving DecidableEq, Repr

def ReferenceWellNamed (n : Names) (r : ReferenceSpec) : Prop :=
  ∀ e ∈ r.history, InquiryProcessWire.StampedWellNamed n e

def encodeAssignment (a : List (Family.SlotId × Family.ChoiceId)) : Sx :=
  encodeList (encodePair Family.Wire.encodeSlotId Family.Wire.encodeChoiceId) a

def decodeAssignment : Sx → Option (List (Family.SlotId × Family.ChoiceId)) :=
  decodeList (decodePair Family.Wire.decodeSlotId Family.Wire.decodeChoiceId)

@[simp] theorem decode_encodeAssignment (a : List (Family.SlotId × Family.ChoiceId)) :
    decodeAssignment (encodeAssignment a) = some a := by
  unfold encodeAssignment decodeAssignment
  exact decode_encodeList _ _ (fun p => by
    obtain ⟨x, y⟩ := p
    simp [Analysis.AnalysisWire.decode_encodePair, Family.Wire.decode_encodeSlotId,
      Family.Wire.decode_encodeChoiceId]) a

def encodeReference (n : Names) (r : ReferenceSpec) : Sx :=
  tagged .reference [tagged .refHistory [encodeList (Source.AuditWire.encodeStamped n) r.history],
    tagged .refChoices [encodeAssignment r.assignment]]

def decodeReferenceRaw (n : Names) : Sx → Option ReferenceSpec
  | .list [.atom t, .list [.atom ht, history], .list [.atom ct, choices]] =>
      match Tag.parse t, Tag.parse ht, Tag.parse ct with
      | some .reference, some .refHistory, some .refChoices => do
          return ⟨← decodeList (Source.AuditWire.decodeStamped n) history,
            ← decodeAssignment choices⟩
      | _, _, _ => none
  | _ => none

def decodeReference (n : Names) := canonical (encodeReference n) (decodeReferenceRaw n)

theorem decode_encodeReferenceRaw (n : Names) (unique : UniqueNames n) (r : ReferenceSpec)
    (valid : ReferenceWellNamed n r) : decodeReferenceRaw n (encodeReference n r) = some r := by
  obtain ⟨history, assignment⟩ := r
  have h := decodeList_map_of _ _ _ (Source.AuditWire.decode_encodeStamped n unique) history valid
  simp only [encodeReference, decodeReferenceRaw, tagged, Tag.parse_text, decodeList, encodeList,
    h, decode_encodeAssignment]
  rfl

@[simp] theorem decode_encodeReference (n : Names) (unique : UniqueNames n) (r : ReferenceSpec)
    (valid : ReferenceWellNamed n r) : decodeReference n (encodeReference n r) = some r :=
  canonical_roundtrip_of _ _ _ (decode_encodeReferenceRaw n unique) r valid

theorem decodeReference_canonical {n : Names} {wire : Sx} {r : ReferenceSpec}
    (h : decodeReference n wire = some r) : encodeReference n r = wire :=
  canonical_sound _ _ h

theorem encodeReference_injective (n : Names) (unique : UniqueNames n)
    {a b : ReferenceSpec} (ha : ReferenceWellNamed n a) (hb : ReferenceWellNamed n b)
    (h : encodeReference n a = encodeReference n b) : a = b :=
  injective_on_of_roundtrip _ _ _ (decode_encodeReference n unique) ha hb h

inductive RequestSpec where
  | status (label : String) (claim : ClaimId)
  | audit (label : String) (claim : ClaimId) (witness : WitnessId) (profile : Process.Wire.ProfileSpec)
  | stable (label : String) (observable : Analysis.AnalysisWire.ObservableSpec)
  | sensitivity (label : String) (reference : ReferenceSpec)
      (observable : Analysis.AnalysisWire.ObservableSpec)
  | slotsSensitive (label : String) (reference : ReferenceSpec)
      (observable : Analysis.AnalysisWire.ObservableSpec)
  | minimalAssumptions (label : String) (target : Analysis.AnalysisWire.TargetSpec)
  | impact (label : String) (before after : Source.SourceInput) (queries : List ClaimId)
  | verifyImpact (label : String) (before after : Source.SourceInput)
      (certificate : ImpactCertificateWire)
  deriving DecidableEq

def RequestWellNamed (n : Names) : RequestSpec → Prop
  | .status _ c => c.index < n.claim.length
  | .audit _ c w _ => c.index < n.claim.length ∧ w.index < n.witness.length
  | .stable _ o => Analysis.AnalysisWire.ObservableWellNamed n o
  | .sensitivity _ r o => ReferenceWellNamed n r ∧ Analysis.AnalysisWire.ObservableWellNamed n o
  | .slotsSensitive _ r o => ReferenceWellNamed n r ∧ Analysis.AnalysisWire.ObservableWellNamed n o
  | .minimalAssumptions _ t => Analysis.AnalysisWire.TargetWellNamed n t
  | .impact _ _ _ qs => ∀ c ∈ qs, c.index < n.claim.length
  | .verifyImpact _ _ _ _ => True

def encodeRequest (n : Names) : RequestSpec → Sx
  | .status label c => tagged .reqStatus [.atom label, Source.AuditWire.encodeClaimId n c]
  | .audit label c w p => tagged .reqAudit [.atom label, Source.AuditWire.encodeClaimId n c,
      Source.AuditWire.encodeWitnessId n w, encodeProfileSpec p]
  | .stable label o => tagged .reqStable [.atom label, encodeObservableSpec n o]
  | .sensitivity label r o => tagged .reqSensitivity [.atom label, encodeReference n r,
      encodeObservableSpec n o]
  | .slotsSensitive label r o => tagged .reqSlotsSensitive [.atom label, encodeReference n r,
      encodeObservableSpec n o]
  | .minimalAssumptions label t => tagged .reqMinimalAssumptions [.atom label, encodeTargetSpec n t]
  | .impact label b a qs => tagged .reqImpact [.atom label, encodeSource b, encodeSource a,
      tagged .queries (qs.map (Source.AuditWire.encodeClaimId n))]
  | .verifyImpact label b a c => tagged .reqVerifyImpact [.atom label, encodeSource b, encodeSource a,
      encodeImpactCertificate c]

def decodeRequestRaw (n : Names) : Sx → Option RequestSpec
  | .list [.atom t, .atom label, x] =>
      match Tag.parse t with
      | some .reqStatus => (Source.AuditWire.decodeClaimId n x).map (RequestSpec.status label)
      | some .reqStable => (decodeObservableSpec n x).map (RequestSpec.stable label)
      | some .reqMinimalAssumptions => (decodeTargetSpec n x).map (RequestSpec.minimalAssumptions label)
      | _ => none
  | .list [.atom t, .atom label, r, o] =>
      match Tag.parse t with
      | some .reqSensitivity =>
          (match decodeReference n r, decodeObservableSpec n o with
           | some reference, some observable => some (.sensitivity label reference observable)
           | _, _ => none)
      | some .reqSlotsSensitive =>
          (match decodeReference n r, decodeObservableSpec n o with
           | some reference, some observable => some (.slotsSensitive label reference observable)
           | _, _ => none)
      | _ => none
  | .list [.atom t, .atom label, x, y, z] =>
      match Tag.parse t with
      | some .reqAudit =>
          (match Source.AuditWire.decodeClaimId n x, Source.AuditWire.decodeWitnessId n y,
                 decodeProfileSpec z with
           | some claim, some witness, some profile => some (.audit label claim witness profile)
           | _, _, _ => none)
      | some .reqImpact =>
          (match decodeSource x, decodeSource y, head z with
           | some before, some after, some (.queries, args) =>
               (Source.Wire.decodeList (Source.AuditWire.decodeClaimId n) args).map
                 (RequestSpec.impact label before after)
           | _, _, _ => none)
      | some .reqVerifyImpact =>
          (match decodeSource x, decodeSource y, decodeImpactCertificate z with
           | some before, some after, some certificate => some (.verifyImpact label before after certificate)
           | _, _, _ => none)
      | _ => none
  | _ => none

def decodeRequest (n : Names) := canonical (encodeRequest n) (decodeRequestRaw n)

theorem decode_encodeRequestRaw (n : Names) (unique : UniqueNames n) (r : RequestSpec)
    (valid : RequestWellNamed n r) : decodeRequestRaw n (encodeRequest n r) = some r := by
  cases r with
  | status label c =>
      simp [encodeRequest, decodeRequestRaw, tagged, Tag.parse_text,
        Source.AuditWire.decode_encodeClaimId n unique c valid]
  | audit label c w p =>
      obtain ⟨hc, hw⟩ := valid
      simp [encodeRequest, decodeRequestRaw, tagged, Tag.parse_text,
        Source.AuditWire.decode_encodeClaimId n unique c hc,
        Source.AuditWire.decode_encodeWitnessId n unique w hw,
        Analysis.AnalysisWire.decode_encodeProfileSpec]
  | stable label o =>
      simp only [RequestWellNamed] at valid
      simp [encodeRequest, decodeRequestRaw, tagged, Tag.parse_text,
        Analysis.AnalysisWire.decode_encodeObservableSpec n unique o valid]
  | sensitivity label ref obs =>
      obtain ⟨hr, ho⟩ := valid
      simp [encodeRequest, decodeRequestRaw, tagged, Tag.parse_text,
        decode_encodeReference n unique ref hr,
        Analysis.AnalysisWire.decode_encodeObservableSpec n unique obs ho]
  | slotsSensitive label ref obs =>
      obtain ⟨hr, ho⟩ := valid
      simp [encodeRequest, decodeRequestRaw, tagged, Tag.parse_text,
        decode_encodeReference n unique ref hr,
        Analysis.AnalysisWire.decode_encodeObservableSpec n unique obs ho]
  | minimalAssumptions label tgt =>
      simp only [RequestWellNamed] at valid
      simp [encodeRequest, decodeRequestRaw, tagged, Tag.parse_text,
        Analysis.AnalysisWire.decode_encodeTargetSpec n unique tgt valid]
  | impact label before after qs =>
      simp [encodeRequest, decodeRequestRaw, tagged, Tag.parse_text, Source.Wire.decode_encode,
        Process.InquiryProcessWire.head_tagged, Source.Wire.decodeList,
        decodeList_map_of _ _ _ (Source.AuditWire.decode_encodeClaimId n unique) qs valid]
  | verifyImpact label before after cert =>
      simp [encodeRequest, decodeRequestRaw, tagged, Tag.parse_text, Source.Wire.decode_encode,
        decode_encodeImpactCertificate]

@[simp] theorem decode_encodeRequest (n : Names) (unique : UniqueNames n) (r : RequestSpec)
    (valid : RequestWellNamed n r) : decodeRequest n (encodeRequest n r) = some r :=
  canonical_roundtrip_of _ _ _ (decode_encodeRequestRaw n unique) r valid

theorem decodeRequest_canonical {n : Names} {wire : Sx} {r : RequestSpec}
    (h : decodeRequest n wire = some r) : encodeRequest n r = wire := canonical_sound _ _ h

theorem encodeRequest_injective (n : Names) (unique : UniqueNames n)
    {a b : RequestSpec} (ha : RequestWellNamed n a) (hb : RequestWellNamed n b)
    (h : encodeRequest n a = encodeRequest n b) : a = b :=
  injective_on_of_roundtrip _ _ _ (decode_encodeRequest n unique) ha hb h

structure InquiryInput where
  process : Process.Wire.Document
  base : Source.SourceInput
  slots : List Family.Slot
  claims : List Source.ClaimBinding
  witnesses : List Source.WitnessSpec
  kinds : List Source.KindSpec
  assumptions : List Source.CaptureAssumption
  catalog : List Analysis.Literal
  limits : InquiryLimits
  requests : List RequestSpec
  deriving DecidableEq

/-- The embedded `process-input 1` document is one the P0 codec round-trips: its
names tables are duplicate-free and every interned index is in range. This is the
embedded codec's own law, not the wrapper's decode success. -/
def ProcessCodecRounds (d : Process.Wire.Document) : Prop :=
  Process.Wire.decodeDocument (Process.Wire.encodeDocument d) = .ok d

def InquiryInputWellNamed (input : InquiryInput) : Prop :=
  ProcessCodecRounds input.process ∧ UniqueNames input.process.names ∧
    (∀ s ∈ input.slots, Family.Wire.SlotWellNamed input.process.names s) ∧
    (∀ c ∈ input.claims, Source.AuditWire.ClaimBindingWellNamed input.process.names c) ∧
    (∀ w ∈ input.witnesses, Source.AuditWire.WitnessSpecWellNamed input.process.names w) ∧
    (∀ a ∈ input.assumptions, Source.AuditWire.CaptureAssumptionWellNamed input.process.names a) ∧
    (∀ l ∈ input.catalog, Analysis.AnalysisWire.LiteralWellNamed input.process.names l) ∧
    (∀ r ∈ input.requests, RequestWellNamed input.process.names r)

def encodeInquiryInput (input : InquiryInput) : Sx :=
  let n := input.process.names
  tagged .inquiryInput [.atom version, Process.Wire.encodeDocument input.process,
    encodeSource input.base, tagged .slots (input.slots.map (encodeSlot n)),
    tagged .bindings [.list (input.claims.map (Source.AuditWire.encodeClaimBinding n)),
      .list (input.witnesses.map (Source.AuditWire.encodeWitnessSpec n))],
    tagged .kindMetadata (input.kinds.map Source.AuditWire.encodeKindSpec),
    tagged .admittedAssumptions (input.assumptions.map (Source.AuditWire.encodeCaptureAssumption n)),
    tagged .assumptionCatalog (input.catalog.map (encodeLiteral n)),
    encodeInquiryLimits input.limits, tagged .requests (input.requests.map (encodeRequest n))]

def decodeBindings (n : Names) (e : Sx) :
    Option (List Source.ClaimBinding × List Source.WitnessSpec) :=
  match head e with
  | some (.bindings, [cbs, wss]) =>
      (match decodeList (Source.AuditWire.decodeClaimBinding n) cbs with
       | some claims =>
           (match decodeList (Source.AuditWire.decodeWitnessSpec n) wss with
            | some witnesses => some (claims, witnesses)
            | none => none)
       | none => none)
  | _ => none

def decodeBlock {α : Type} (t : Tag) (d : Sx → Option α) (e : Sx) : Option (List α) :=
  match head e with
  | some (t', args) => if t' = t then Source.Wire.decodeList d args else none
  | none => none

def decodeInquiryInputRaw : Sx → Option InquiryInput
  | .list [.atom t, .atom ver, proc, base,
      slotsBlock, bindingsBlock, kindsBlock, assumBlock, catBlock, lim, reqBlock] =>
      match Tag.parse t with
      | some .inquiryInput =>
          if ver = version then
            match Process.Wire.decodeDocument proc with
            | .ok d => do
                let base' ← decodeSource base
                let slots ← decodeBlock .slots (Family.Wire.decodeSlot d.names) slotsBlock
                let bd ← decodeBindings d.names bindingsBlock
                let kinds ← decodeBlock .kindMetadata Source.AuditWire.decodeKindSpec kindsBlock
                let assumptions ← decodeBlock .admittedAssumptions
                  (Source.AuditWire.decodeCaptureAssumption d.names) assumBlock
                let catalog ← decodeBlock .assumptionCatalog (decodeLiteral d.names) catBlock
                let limits ← decodeInquiryLimits lim
                let requests ← decodeBlock .requests (decodeRequest d.names) reqBlock
                return ⟨d, base', slots, bd.1, bd.2, kinds, assumptions, catalog, limits, requests⟩
            | .error _ => none
          else none
      | _ => none
  | _ => none

def decodeInquiryInput := canonical encodeInquiryInput decodeInquiryInputRaw

theorem decodeBindings_encode (n : Names) (unique : UniqueNames n)
    (claims : List Source.ClaimBinding) (witnesses : List Source.WitnessSpec)
    (hc : ∀ c ∈ claims, Source.AuditWire.ClaimBindingWellNamed n c)
    (hw : ∀ w ∈ witnesses, Source.AuditWire.WitnessSpecWellNamed n w) :
    decodeBindings n (.list (.atom Tag.bindings.text ::
      [.list (claims.map (Source.AuditWire.encodeClaimBinding n)),
        .list (witnesses.map (Source.AuditWire.encodeWitnessSpec n))])) = some (claims, witnesses) := by
  simp only [decodeBindings, tagged, Tag.parse_text, decodeList, head_tagged]
  rw [decodeList_map_of _ _ _ (Source.AuditWire.decode_encodeClaimBinding n unique) claims hc,
    decodeList_map_of _ _ _ (Source.AuditWire.decode_encodeWitnessSpec n unique) witnesses hw]

theorem decodeBlock_eq {α : Type} (t : Tag) (d : Sx → Option α) (args : List Sx) :
    decodeBlock t d (.list (.atom t.text :: args)) = Source.Wire.decodeList d args := by
  simp [decodeBlock, Tag.parse_text, head_tagged]

theorem decodeInquiryInputRaw_encode (input : InquiryInput) (valid : InquiryInputWellNamed input) :
    decodeInquiryInputRaw (encodeInquiryInput input) = some input := by
  obtain ⟨hproc, hunique, hslots, hclaims, hwitnesses, hassumptions, hcatalog, hrequests⟩ := valid
  have hproc' : Process.Wire.decodeDocument (Process.Wire.encodeDocument input.process) = .ok input.process := hproc
  have hsl := decodeList_map_of _ _ _ (Family.Wire.decode_encodeSlot input.process.names hunique)
    input.slots hslots
  have hbd := decodeBindings_encode input.process.names hunique input.claims input.witnesses
    hclaims hwitnesses
  have hkd := decodeList_map_of _ _ _ (fun k _ => Source.AuditWire.decode_encodeKindSpec k)
    input.kinds (fun _ _ => trivial)
  have had := decodeList_map_of _ _ _
    (Source.AuditWire.decode_encodeCaptureAssumption input.process.names hunique)
    input.assumptions hassumptions
  have hcd := decodeList_map_of _ _ _
    (Analysis.AnalysisWire.decode_encodeLiteral input.process.names hunique)
    input.catalog hcatalog
  have hrd := decodeList_map_of _ _ _
    (decode_encodeRequest input.process.names hunique) input.requests hrequests
  simp [encodeInquiryInput, decodeInquiryInputRaw, tagged, Tag.parse_text, if_true, hproc',
    Source.Wire.decode_encode, decodeBlock_eq, hsl, hbd, hkd, had, hcd, hrd,
    decode_encodeInquiryLimits]

@[simp] theorem decode_encodeInquiryInput (input : InquiryInput) (valid : InquiryInputWellNamed input) :
    decodeInquiryInput (encodeInquiryInput input) = some input :=
  canonical_roundtrip_of _ _ _ decodeInquiryInputRaw_encode input valid

theorem decodeInquiryInput_canonical {wire : Sx} {v : InquiryInput}
    (h : decodeInquiryInput wire = some v) : encodeInquiryInput v = wire := canonical_sound _ _ h

theorem encodeInquiryInput_injective {a b : InquiryInput} (ha : InquiryInputWellNamed a)
    (hb : InquiryInputWellNamed b) (h : encodeInquiryInput a = encodeInquiryInput b) : a = b :=
  injective_on_of_roundtrip _ _ _ decode_encodeInquiryInput ha hb h

/-- The strict version check: a decoded envelope whose version is not `1` is
refused with the version case, never silently accepted. -/
def parseInquiryInput (e : Sx) : Except RunRefusal InquiryInput :=
  match head e with
  | some (.inquiryInput, .atom ver :: _) =>
      if ver = version then
        match decodeInquiryInput e with
        | some v => .ok v
        | none => .error (.malformed "malformed inquiry-input")
      else .error (.version s!"inquiry-input supports version 1 only, found {ver}")
  | _ => .error (.malformed "expected an inquiry-input document")

/-! ### Family result rows -/

structure FamilyStatusRow where
  history : List Stamped
  assignment : List (Family.SlotId × Family.ChoiceId)
  rejection : Option Source.SourceRejection
  status : Option Driver.PublicStatus
  deriving DecidableEq

structure FamilyAuditRow where
  history : List Stamped
  assignment : List (Family.SlotId × Family.ChoiceId)
  rejection : Option Source.SourceRejection
  audit : Option Bool
  deriving DecidableEq

structure FamilyStatusResult where
  rows : List FamilyStatusRow
  total : Nat
  accepted : Nat
  rejected : Nat
  verdict : Bool
  deriving DecidableEq

structure FamilyAuditResult where
  rows : List FamilyAuditRow
  total : Nat
  accepted : Nat
  rejected : Nat
  verdict : Bool
  deriving DecidableEq

def FamilyRowWellNamed (n : Names) (row : FamilyStatusRow) : Prop :=
  ∀ e ∈ row.history, InquiryProcessWire.StampedWellNamed n e
def FamilyAuditRowWellNamed (n : Names) (row : FamilyAuditRow) : Prop :=
  ∀ e ∈ row.history, InquiryProcessWire.StampedWellNamed n e
def FamilyStatusResultWellNamed (n : Names) (r : FamilyStatusResult) : Prop :=
  ∀ row ∈ r.rows, FamilyRowWellNamed n row
def FamilyAuditResultWellNamed (n : Names) (r : FamilyAuditResult) : Prop :=
  ∀ row ∈ r.rows, FamilyAuditRowWellNamed n row

def encodeFamilyStatusRow (n : Names) (r : FamilyStatusRow) : Sx :=
  tagged .familyRow [encodeList (Source.AuditWire.encodeStamped n) r.history,
    encodeAssignment r.assignment, encodeOpt encodeRejection r.rejection,
    encodeOpt encodePublicStatus r.status]

def decodeFamilyStatusRowRaw (n : Names) : Sx → Option FamilyStatusRow
  | .list [.atom t, history, assignment, rejection, status] =>
      match Tag.parse t with
      | some .familyRow => do
          return ⟨← decodeList (Source.AuditWire.decodeStamped n) history,
            ← decodeAssignment assignment, ← decodeOpt decodeRejection rejection,
            ← decodeOpt decodePublicStatus status⟩
      | _ => none
  | _ => none

def decodeFamilyStatusRow (n : Names) :=
  canonical (encodeFamilyStatusRow n) (decodeFamilyStatusRowRaw n)

theorem decode_encodeFamilyStatusRowRaw (n : Names) (unique : UniqueNames n) (r : FamilyStatusRow)
    (valid : FamilyRowWellNamed n r) : decodeFamilyStatusRowRaw n (encodeFamilyStatusRow n r) = some r := by
  obtain ⟨history, assignment, rejection, status⟩ := r
  simp [encodeFamilyStatusRow, decodeFamilyStatusRowRaw, tagged, Tag.parse_text, decodeList, encodeList,
    decodeList_map_of _ _ _ (Source.AuditWire.decode_encodeStamped n unique) history valid,
    decode_encodeAssignment, Analysis.AnalysisWire.decode_encodeOpt,
    Source.ResultWire.decode_encodeRejection, Source.ResultWire.decode_encodePublicStatus]

@[simp] theorem decode_encodeFamilyStatusRow (n : Names) (unique : UniqueNames n) (r : FamilyStatusRow)
    (valid : FamilyRowWellNamed n r) : decodeFamilyStatusRow n (encodeFamilyStatusRow n r) = some r :=
  canonical_roundtrip_of _ _ _ (decode_encodeFamilyStatusRowRaw n unique) r valid

def encodeFamilyAuditRow (n : Names) (r : FamilyAuditRow) : Sx :=
  tagged .familyAuditRow [encodeList (Source.AuditWire.encodeStamped n) r.history,
    encodeAssignment r.assignment, encodeOpt encodeRejection r.rejection, encodeOpt encodeBool r.audit]

def decodeFamilyAuditRowRaw (n : Names) : Sx → Option FamilyAuditRow
  | .list [.atom t, history, assignment, rejection, audit] =>
      match Tag.parse t with
      | some .familyAuditRow => do
          return ⟨← decodeList (Source.AuditWire.decodeStamped n) history,
            ← decodeAssignment assignment, ← decodeOpt decodeRejection rejection,
            ← decodeOpt decodeBool audit⟩
      | _ => none
  | _ => none

def decodeFamilyAuditRow (n : Names) := canonical (encodeFamilyAuditRow n) (decodeFamilyAuditRowRaw n)

theorem decode_encodeFamilyAuditRowRaw (n : Names) (unique : UniqueNames n) (r : FamilyAuditRow)
    (valid : FamilyAuditRowWellNamed n r) : decodeFamilyAuditRowRaw n (encodeFamilyAuditRow n r) = some r := by
  obtain ⟨history, assignment, rejection, audit⟩ := r
  simp [encodeFamilyAuditRow, decodeFamilyAuditRowRaw, tagged, Tag.parse_text, decodeList, encodeList,
    decodeList_map_of _ _ _ (Source.AuditWire.decode_encodeStamped n unique) history valid,
    decode_encodeAssignment, Analysis.AnalysisWire.decode_encodeOpt,
    Source.ResultWire.decode_encodeRejection, Source.AuditWire.decode_encodeBool]

@[simp] theorem decode_encodeFamilyAuditRow (n : Names) (unique : UniqueNames n) (r : FamilyAuditRow)
    (valid : FamilyAuditRowWellNamed n r) : decodeFamilyAuditRow n (encodeFamilyAuditRow n r) = some r :=
  canonical_roundtrip_of _ _ _ (decode_encodeFamilyAuditRowRaw n unique) r valid

def encodeFamilyStatusResult (n : Names) (r : FamilyStatusResult) : Sx :=
  tagged .familyStatusResult [encodeList (encodeFamilyStatusRow n) r.rows, encodeNat r.total,
    encodeNat r.accepted, encodeNat r.rejected, encodeBool r.verdict]

def decodeFamilyStatusResultRaw (n : Names) : Sx → Option FamilyStatusResult
  | .list [.atom t, rows, total, accepted, rejected, verdict] =>
      match Tag.parse t with
      | some .familyStatusResult => do
          return ⟨← decodeList (decodeFamilyStatusRow n) rows, ← decodeNat total,
            ← decodeNat accepted, ← decodeNat rejected, ← decodeBool verdict⟩
      | _ => none
  | _ => none

def decodeFamilyStatusResult (n : Names) :=
  canonical (encodeFamilyStatusResult n) (decodeFamilyStatusResultRaw n)

theorem decode_encodeFamilyStatusResultRaw (n : Names) (unique : UniqueNames n)
    (r : FamilyStatusResult) (valid : FamilyStatusResultWellNamed n r) :
    decodeFamilyStatusResultRaw n (encodeFamilyStatusResult n r) = some r := by
  obtain ⟨rows, total, accepted, rejected, verdict⟩ := r
  simp [encodeFamilyStatusResult, decodeFamilyStatusResultRaw, tagged, Tag.parse_text, decodeList, encodeList,
    decodeList_map_of _ _ _ (decode_encodeFamilyStatusRow n unique) rows valid,
    Source.ResultWire.decode_encodeNat, Source.AuditWire.decode_encodeBool]

@[simp] theorem decode_encodeFamilyStatusResult (n : Names) (unique : UniqueNames n)
    (r : FamilyStatusResult) (valid : FamilyStatusResultWellNamed n r) :
    decodeFamilyStatusResult n (encodeFamilyStatusResult n r) = some r :=
  canonical_roundtrip_of _ _ _ (decode_encodeFamilyStatusResultRaw n unique) r valid

def encodeFamilyAuditResult (n : Names) (r : FamilyAuditResult) : Sx :=
  tagged .familyAuditResult [encodeList (encodeFamilyAuditRow n) r.rows, encodeNat r.total,
    encodeNat r.accepted, encodeNat r.rejected, encodeBool r.verdict]

def decodeFamilyAuditResultRaw (n : Names) : Sx → Option FamilyAuditResult
  | .list [.atom t, rows, total, accepted, rejected, verdict] =>
      match Tag.parse t with
      | some .familyAuditResult => do
          return ⟨← decodeList (decodeFamilyAuditRow n) rows, ← decodeNat total,
            ← decodeNat accepted, ← decodeNat rejected, ← decodeBool verdict⟩
      | _ => none
  | _ => none

def decodeFamilyAuditResult (n : Names) :=
  canonical (encodeFamilyAuditResult n) (decodeFamilyAuditResultRaw n)

theorem decode_encodeFamilyAuditResultRaw (n : Names) (unique : UniqueNames n)
    (r : FamilyAuditResult) (valid : FamilyAuditResultWellNamed n r) :
    decodeFamilyAuditResultRaw n (encodeFamilyAuditResult n r) = some r := by
  obtain ⟨rows, total, accepted, rejected, verdict⟩ := r
  simp [encodeFamilyAuditResult, decodeFamilyAuditResultRaw, tagged, Tag.parse_text, decodeList, encodeList,
    decodeList_map_of _ _ _ (decode_encodeFamilyAuditRow n unique) rows valid,
    Source.ResultWire.decode_encodeNat, Source.AuditWire.decode_encodeBool]

@[simp] theorem decode_encodeFamilyAuditResult (n : Names) (unique : UniqueNames n)
    (r : FamilyAuditResult) (valid : FamilyAuditResultWellNamed n r) :
    decodeFamilyAuditResult n (encodeFamilyAuditResult n r) = some r :=
  canonical_roundtrip_of _ _ _ (decode_encodeFamilyAuditResultRaw n unique) r valid

/-! ### The result and error envelopes -/

inductive ResultBody where
  | histories (historyCount : Nat) (answer : OutcomeAnswer)
  | status (result : FamilyStatusResult)
  | audit (result : FamilyAuditResult)
  | stability (result : Analysis.StabilityResult Analysis.AnalysisWire.ObservableSpec)
  | sensitivity (result : Analysis.SensitivityResult Analysis.AnalysisWire.ObservableSpec)
  | slotsSensitive (result : Analysis.SensitivityResult Analysis.AnalysisWire.ObservableSpec)
  | minimalAssumptions (result : Analysis.AssumptionResult Analysis.AnalysisWire.TargetSpec)
  | impact (result : Impact.ImpactResult)
  | verification (result : Impact.VerificationResult)

structure InquiryResult where
  label : String
  body : ResultBody

structure InquiryError where
  label : Option String
  refusal : RunRefusal
  deriving DecidableEq

def ResultBodyWellNamed (n : Names) : ResultBody → Prop
  | .histories _ ans => OutcomeAnswerWellNamed n ans
  | .status r => FamilyStatusResultWellNamed n r
  | .audit r => FamilyAuditResultWellNamed n r
  | .stability r => Analysis.AnalysisWire.StabilityResultWellNamed n r
  | .sensitivity r => Analysis.AnalysisWire.SensitivityResultWellNamed n r
  | .slotsSensitive r => Analysis.AnalysisWire.SensitivityResultWellNamed n r
  | .minimalAssumptions r => Analysis.AnalysisWire.AssumptionResultWellNamed n r
  | .impact _ => True
  | .verification _ => True

def InquiryResultWellNamed (n : Names) (r : InquiryResult) : Prop := ResultBodyWellNamed n r.body

def encodeResultBody (n : Names) (label : String) : ResultBody → Sx
  | .histories count answer =>
      tagged .bodyAnswer [tagged .historyCount [encodeNat count], encodeOutcomeAnswer n label answer]
  | .status result => tagged .bodyStatus [encodeFamilyStatusResult n result]
  | .audit result => tagged .bodyAudit [encodeFamilyAuditResult n result]
  | .stability result => tagged .bodyStability [encodeStabilityResult n result]
  | .sensitivity result => tagged .bodySensitivity [encodeSensitivityResult n result]
  | .slotsSensitive result => tagged .bodySlotsSensitive [encodeSensitivityResult n result]
  | .minimalAssumptions result => tagged .bodyAssumptions [encodeAssumptionResult n result]
  | .impact result => tagged .bodyImpact [encodeImpactResult result]
  | .verification result => tagged .bodyVerification [encodeVerificationResult result]

def decodeResultBodyRaw (n : Names) : Sx → Option ResultBody
  | .list [.atom t, count, answer] =>
      match Tag.parse t with
      | some .bodyAnswer =>
          (match head count with
           | some (.historyCount, [c]) =>
               (match decodeNat c, decodeOutcomeAnswerRaw n answer with
                | some k, some a => some (.histories k a)
                | _, _ => none)
           | _ => none)
      | _ => none
  | .list [.atom t, x] =>
      match Tag.parse t with
      | some .bodyStatus => (decodeFamilyStatusResult n x).map ResultBody.status
      | some .bodyAudit => (decodeFamilyAuditResult n x).map ResultBody.audit
      | some .bodyStability => (decodeStabilityResult n x).map ResultBody.stability
      | some .bodySensitivity => (decodeSensitivityResult n x).map ResultBody.sensitivity
      | some .bodySlotsSensitive => (decodeSensitivityResult n x).map ResultBody.slotsSensitive
      | some .bodyAssumptions => (decodeAssumptionResult n x).map ResultBody.minimalAssumptions
      | some .bodyImpact => (decodeImpactResult x).map ResultBody.impact
      | some .bodyVerification => (decodeVerificationResult x).map ResultBody.verification
      | _ => none
  | _ => none

def encodeInquiryResult (n : Names) (r : InquiryResult) : Sx :=
  tagged .inquiryResult [.atom version, .atom r.label, encodeResultBody n r.label r.body]

def decodeInquiryResultRaw (n : Names) : Sx → Option InquiryResult
  | .list [.atom t, .atom ver, .atom label, body] =>
      match Tag.parse t with
      | some .inquiryResult =>
          if ver = version then (decodeResultBodyRaw n body).map (fun b => ⟨label, b⟩) else none
      | _ => none
  | _ => none

def decodeInquiryResult (n : Names) := canonical (encodeInquiryResult n) (decodeInquiryResultRaw n)

theorem decode_encodeInquiryResultRaw (n : Names) (unique : UniqueNames n) (r : InquiryResult)
    (valid : InquiryResultWellNamed n r) :
    decodeInquiryResultRaw n (encodeInquiryResult n r) = some r := by
  obtain ⟨label, body⟩ := r
  cases body with
  | histories count ans =>
      simp [encodeInquiryResult, encodeResultBody, decodeInquiryResultRaw, decodeResultBodyRaw,
        tagged, Tag.parse_text, if_true, Source.ResultWire.decode_encodeNat,
        decode_encodeOutcomeAnswerRaw n unique label ans valid]
  | status res =>
      simp [encodeInquiryResult, encodeResultBody, decodeInquiryResultRaw, decodeResultBodyRaw,
        tagged, Tag.parse_text, if_true, decode_encodeFamilyStatusResult n unique res valid]
  | audit res =>
      simp [encodeInquiryResult, encodeResultBody, decodeInquiryResultRaw, decodeResultBodyRaw,
        tagged, Tag.parse_text, if_true, decode_encodeFamilyAuditResult n unique res valid]
  | stability res =>
      simp [encodeInquiryResult, encodeResultBody, decodeInquiryResultRaw, decodeResultBodyRaw,
        tagged, Tag.parse_text, if_true, Analysis.AnalysisWire.decode_encodeStabilityResult n unique res valid]
  | sensitivity res =>
      simp [encodeInquiryResult, encodeResultBody, decodeInquiryResultRaw, decodeResultBodyRaw,
        tagged, Tag.parse_text, if_true, Analysis.AnalysisWire.decode_encodeSensitivityResult n unique res valid]
  | slotsSensitive res =>
      simp [encodeInquiryResult, encodeResultBody, decodeInquiryResultRaw, decodeResultBodyRaw,
        tagged, Tag.parse_text, if_true, Analysis.AnalysisWire.decode_encodeSensitivityResult n unique res valid]
  | minimalAssumptions res =>
      simp [encodeInquiryResult, encodeResultBody, decodeInquiryResultRaw, decodeResultBodyRaw,
        tagged, Tag.parse_text, if_true, Analysis.AnalysisWire.decode_encodeAssumptionResult n unique res valid]
  | impact res =>
      simp [encodeInquiryResult, encodeResultBody, decodeInquiryResultRaw, decodeResultBodyRaw,
        tagged, Tag.parse_text, if_true, decode_encodeImpactResult]
  | verification res =>
      simp [encodeInquiryResult, encodeResultBody, decodeInquiryResultRaw, decodeResultBodyRaw,
        tagged, Tag.parse_text, if_true, decode_encodeVerificationResult]

@[simp] theorem decode_encodeInquiryResult (n : Names) (unique : UniqueNames n) (r : InquiryResult)
    (valid : InquiryResultWellNamed n r) : decodeInquiryResult n (encodeInquiryResult n r) = some r :=
  canonical_roundtrip_of _ _ _ (decode_encodeInquiryResultRaw n unique) r valid

theorem decodeInquiryResult_canonical {n : Names} {wire : Sx} {r : InquiryResult}
    (h : decodeInquiryResult n wire = some r) : encodeInquiryResult n r = wire :=
  canonical_sound _ _ h

theorem encodeInquiryResult_injective (n : Names) (unique : UniqueNames n)
    {a b : InquiryResult} (ha : InquiryResultWellNamed n a) (hb : InquiryResultWellNamed n b)
    (h : encodeInquiryResult n a = encodeInquiryResult n b) : a = b :=
  injective_on_of_roundtrip _ _ _ (decode_encodeInquiryResult n unique) ha hb h

def encodeInquiryError (e : InquiryError) : Sx :=
  tagged .inquiryError [.atom version, encodeOpt (fun s => Sx.atom s) e.label,
    encodeRunRefusal e.refusal]

def decodeInquiryErrorRaw : Sx → Option InquiryError
  | .list [.atom t, .atom ver, label, refusal] =>
      match Tag.parse t with
      | some .inquiryError =>
          if ver = version then
            (match decodeOpt decodeText label, decodeRunRefusal refusal with
             | some l, some r => some ⟨l, r⟩
             | _, _ => none)
          else none
      | _ => none
  | _ => none

def decodeInquiryError := canonical encodeInquiryError decodeInquiryErrorRaw

theorem decode_encodeInquiryErrorRaw (e : InquiryError) :
    decodeInquiryErrorRaw (encodeInquiryError e) = some e := by
  obtain ⟨label, refusal⟩ := e
  have hl : decodeOpt decodeText (encodeOpt (fun s => Sx.atom s) label) = some label := by
    cases label with
    | none => rfl
    | some s =>
        simp [Analysis.AnalysisWire.encodeOpt, Analysis.AnalysisWire.decodeOpt,
          Source.ResultWire.decodeText, Source.ResultWire.encodeText]
  have hr := decode_encodeRunRefusal refusal
  simp [encodeInquiryError, decodeInquiryErrorRaw, tagged, Tag.parse_text, if_true, hl, hr]

@[simp] theorem decode_encodeInquiryError (e : InquiryError) :
    decodeInquiryError (encodeInquiryError e) = some e :=
  canonical_roundtrip _ _ decode_encodeInquiryErrorRaw e

theorem decodeInquiryError_canonical {wire : Sx} {e : InquiryError}
    (h : decodeInquiryError wire = some e) : encodeInquiryError e = wire := canonical_sound _ _ h

theorem encodeInquiryError_injective : Function.Injective encodeInquiryError :=
  injective_of_roundtrip _ _ decode_encodeInquiryError

def parseInquiryResult (n : Names) (e : Sx) : Except RunRefusal InquiryResult :=
  match head e with
  | some (.inquiryResult, .atom ver :: _) =>
      if ver = version then
        match decodeInquiryResult n e with
        | some v => .ok v
        | none => .error (.malformed "malformed inquiry-result")
      else .error (.version s!"inquiry-result supports version 1 only, found {ver}")
  | _ => .error (.malformed "expected an inquiry-result envelope")

def parseInquiryError (e : Sx) : Except RunRefusal InquiryError :=
  match head e with
  | some (.inquiryError, .atom ver :: _) =>
      if ver = version then
        match decodeInquiryError e with
        | some v => .ok v
        | none => .error (.malformed "malformed inquiry-error")
      else .error (.version s!"inquiry-error supports version 1 only, found {ver}")
  | _ => .error (.malformed "expected an inquiry-error envelope")

/-! ### Renaming the wrapper's own identities -/

/-- Rename a slot identity by an injection on its interned position. -/
def SlotId.rename (f : Nat → Nat) (i : Family.SlotId) : Family.SlotId := ⟨f i.index⟩

/-- Rename a choice identity by an injection on its interned position. -/
def ChoiceId.rename (f : Nat → Nat) (i : Family.ChoiceId) : Family.ChoiceId := ⟨f i.index⟩

theorem SlotId.rename_injective {f : Nat → Nat} (hf : Function.Injective f) :
    Function.Injective (SlotId.rename f) := by
  intro a b h
  cases a with
  | mk ai => cases b with
    | mk bi =>
        simp only [SlotId.rename, Family.SlotId.mk.injEq] at h ⊢
        exact hf h

theorem ChoiceId.rename_injective {f : Nat → Nat} (hf : Function.Injective f) :
    Function.Injective (ChoiceId.rename f) := by
  intro a b h
  cases a with
  | mk ai => cases b with
    | mk bi =>
        simp only [ChoiceId.rename, Family.ChoiceId.mk.injEq] at h ⊢
        exact hf h

/-- Slot identities are interned in their own namespace: renaming the identity
renames exactly the canonical natural it is interned as, and the embedded
process `Names` table is not consulted. -/
theorem encodeSlotId_rename (f : Nat → Nat) (i : Family.SlotId) :
    Family.Wire.encodeSlotId (SlotId.rename f i) =
      .list [.atom Family.Wire.Tag.slotId.text, encodeNat (f i.index)] := by
  cases i; rfl

/-- Choice identities commute with the same renaming. -/
theorem encodeChoiceId_rename (f : Nat → Nat) (i : Family.ChoiceId) :
    Family.Wire.encodeChoiceId (ChoiceId.rename f i) =
      .list [.atom Family.Wire.Tag.choiceId.text, encodeNat (f i.index)] := by
  cases i; rfl

/-- Core argument identities stay in their own string namespace. -/
def ArgId.rename (g : String → String) (a : Presentation.ArgId) : Presentation.ArgId := ⟨g a.val⟩

theorem encodeArgId_rename (g : String → String) (a : Presentation.ArgId) :
    Source.ResultWire.encodeArgId (ArgId.rename g a) = .atom (g a.val) := rfl

end Lara.Process.InquiryWire
