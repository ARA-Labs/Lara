import Lara.Process.SourceInput
import Lara.EvidenceDriver
import Lara.Process.Wire

namespace Lara.Process.Source.Wire

open Lara.Evidence
open Lara.Presentation (SxList)

-- Driver's nested tree needs a mutually recursive equality decision.
mutual
  def sxDecEq (a b : Driver.Sx) : Decidable (a = b) :=
    match a, b with
    | .atom x, .atom y =>
        if h : x = y then .isTrue (by cases h; rfl)
        else .isFalse (fun eq => h (Driver.Sx.atom.inj eq))
    | .list xs, .list ys =>
        match sxListDecEq xs ys with
        | .isTrue h => .isTrue (by cases h; rfl)
        | .isFalse h => .isFalse (fun eq => h (Driver.Sx.list.inj eq))
    | .atom _, .list _ => .isFalse (by intro h; cases h)
    | .list _, .atom _ => .isFalse (by intro h; cases h)
  termination_by sizeOf a
  def sxListDecEq (xs ys : List Driver.Sx) : Decidable (xs = ys) :=
    match xs, ys with
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse (by intro h; cases h)
    | _ :: _, [] => .isFalse (by intro h; cases h)
    | x :: xs, y :: ys =>
        match sxDecEq x y, sxListDecEq xs ys with
        | .isTrue hx, .isTrue hs => .isTrue (by cases hx; cases hs; rfl)
        | .isFalse hx, _ => .isFalse (fun h => hx (List.cons.inj h).1)
        | _, .isFalse hs => .isFalse (fun h => hs (List.cons.inj h).2)
  termination_by sizeOf xs
end

instance : DecidableEq Driver.Sx := sxDecEq

abbrev Sx := Driver.Sx

/-- Fixed source-wire vocabulary. Authored payload strings are never parsed as tags. -/
inductive Tag where
  | string | integerNatural | integerNegativeSuccessor | node | nil | cons
  | backend | replay | object | array | number | true | false | null
  | csv | json | failed | captured | evidence | absent | present
  | source | fragment | versionOne
  deriving DecidableEq

def Tag.text : Tag → String
  | .string => "string"
  | .integerNatural => "integer-natural"
  | .integerNegativeSuccessor => "integer-negative-successor"
  | .node => "node" | .nil => "nil" | .cons => "cons"
  | .backend => "backend" | .replay => "replay"
  | .object => "object" | .array => "array" | .number => "number"
  | .true => "true" | .false => "false" | .null => "null"
  | .csv => "csv" | .json => "json"
  | .failed => "failed" | .captured => "captured" | .evidence => "evidence"
  | .absent => "absent" | .present => "present"
  | .source => "checked-source" | .fragment => "checked-fragment"
  | .versionOne => "1"

def Tag.spelling : Lara.Process.Wire.Spelling Tag where
  all := [.string, .integerNatural, .integerNegativeSuccessor, .node, .nil, .cons,
    .backend, .replay, .object, .array, .number, .true, .false, .null,
    .csv, .json, .failed, .captured, .evidence, .absent, .present,
    .source, .fragment, .versionOne]
  text := Tag.text

def Tag.parse : String → Option Tag := Tag.spelling.parse

theorem Tag.spelling_complete (tag : Tag) : tag ∈ Tag.spelling.all := by
  cases tag <;> decide

theorem Tag.spelling_nodup : (Tag.spelling.all.map Tag.spelling.text).Nodup := by decide

@[simp] theorem Tag.parse_text (tag : Tag) : Tag.parse tag.text = some tag :=
  Tag.spelling.parse_text Tag.spelling_complete Tag.spelling_nodup tag

theorem Tag.parse_some {text : String} {tag : Tag} (h : Tag.parse text = some tag) :
    tag.text = text := Tag.spelling.parse_some h

theorem Tag.text_injective : Function.Injective Tag.text :=
  Tag.spelling.text_injective Tag.spelling_complete Tag.spelling_nodup

def decodeList (decode : Sx → Option α) : List Sx → Option (List α)
  | [] => some []
  | x :: xs => do return (← decode x) :: (← decodeList decode xs)

@[simp] theorem decodeList_map (encode : α → Sx) (decode : Sx → Option α)
    (roundtrip : ∀ a, decode (encode a) = some a) (xs : List α) :
    decodeList decode (xs.map encode) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [decodeList, roundtrip, ih]

/-- Retain only the unique canonical spelling of a successfully decoded value. -/
def canonical (encode : α → Sx) (decode : Sx → Option α) (wire : Sx) : Option α := do
  let value ← decode wire
  if encode value = wire then some value else none

 theorem canonical_roundtrip (encode : α → Sx) (decode : Sx → Option α)
    (roundtrip : ∀ a, decode (encode a) = some a) (a : α) :
    canonical encode decode (encode a) = some a := by
  simp [canonical, roundtrip]

 theorem canonical_sound (encode : α → Sx) (decode : Sx → Option α)
    {wire : Sx} {a : α} (h : canonical encode decode wire = some a) :
    encode a = wire := by
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

mutual
  /-- Strings and integers have disjoint tags. Signed integers use the two Int
  constructors with canonical decimal natural magnitudes, including negative zero's
  absence. Children use a cons spine so decoding is total structural recursion. -/
  def encodePresentation : Presentation.Sx → Sx
    | .str text => .list [.atom Tag.string.text, .atom text]
    | .int (.ofNat n) => .list [.atom Tag.integerNatural.text, .atom (Nat.repr n)]
    | .int (.negSucc n) =>
        .list [.atom Tag.integerNegativeSuccessor.text, .atom (Nat.repr n)]
    | .node tag children => .list [.atom Tag.node.text, .atom tag, encodeChildren children]
  def encodeChildren : SxList → Sx
    | .nil => .list [.atom Tag.nil.text]
    | .cons value rest => .list [.atom Tag.cons.text, encodePresentation value, encodeChildren rest]
end

mutual
  def decodePresentation : Sx → Option Presentation.Sx
    | .list [.atom raw, .atom text] =>
        match Tag.parse raw with
        | some .string => some (.str text)
        | some .integerNatural => (ND.decodeNat text).map (fun n => .int (.ofNat n))
        | some .integerNegativeSuccessor => (ND.decodeNat text).map (fun n => .int (.negSucc n))
        | _ => none
    | .list [.atom raw, .atom tag, children] =>
        match Tag.parse raw with
        | some .node => do return .node tag (← decodeChildren children)
        | _ => none
    | _ => none
  termination_by wire => sizeOf wire
  def decodeChildren : Sx → Option SxList
    | .list [.atom raw] =>
        match Tag.parse raw with
        | some .nil => some .nil
        | _ => none
    | .list [.atom raw, value, rest] =>
        match Tag.parse raw with
        | some .cons => do return .cons (← decodePresentation value) (← decodeChildren rest)
        | _ => none
    | _ => none
  termination_by wire => sizeOf wire
end

mutual
  @[simp] theorem decode_encodePresentation (value : Presentation.Sx) :
      decodePresentation (encodePresentation value) = some value := by
    cases value with
    | str text => simp [encodePresentation, decodePresentation]
    | int n => cases n <;> simp [encodePresentation, decodePresentation]
    | node tag children =>
        simp [encodePresentation, decodePresentation, decode_encodeChildren children]
  @[simp] theorem decode_encodeChildren (values : SxList) :
      decodeChildren (encodeChildren values) = some values := by
    cases values with
    | nil => simp [encodeChildren, decodeChildren]
    | cons value rest => simp [encodeChildren, decodeChildren,
        decode_encodePresentation value, decode_encodeChildren rest]
end

 theorem encodePresentation_injective : Function.Injective encodePresentation :=
  injective_of_roundtrip _ _ decode_encodePresentation

def decodePresentationStrict := canonical encodePresentation decodePresentation
@[simp] theorem decode_encodePresentationStrict (value : Presentation.Sx) :
    decodePresentationStrict (encodePresentation value) = some value :=
  canonical_roundtrip _ _ decode_encodePresentation value
 theorem decodePresentationStrict_canonical {wire : Sx} {value : Presentation.Sx}
    (h : decodePresentationStrict wire = some value) : encodePresentation value = wire :=
  canonical_sound _ _ h

def encodeCoreVersion (version : CoreVersion) : Sx := .atom version.val
def decodeCoreVersion : Sx → Option CoreVersion
  | .atom value => some ⟨value⟩
  | _ => none
@[simp] theorem decode_encodeCoreVersion (version : CoreVersion) :
    decodeCoreVersion (encodeCoreVersion version) = some version := rfl

def encodeBackendVersion (version : BackendVersion) : Sx := .atom version.val
def decodeBackendVersion : Sx → Option BackendVersion
  | .atom value => some ⟨value⟩
  | _ => none
@[simp] theorem decode_encodeBackendVersion (version : BackendVersion) :
    decodeBackendVersion (encodeBackendVersion version) = some version := rfl

def encodeBackend (backend : BackendIdentity) : Sx :=
  .list [.atom Tag.backend.text, .atom backend.name.val, encodeBackendVersion backend.version]
def decodeBackend : Sx → Option BackendIdentity
  | .list [.atom raw, .atom name, version] =>
      match Tag.parse raw with
      | some .backend => do return ⟨⟨name⟩, ← decodeBackendVersion version⟩
      | _ => none
  | _ => none
@[simp] theorem decode_encodeBackend (backend : BackendIdentity) :
    decodeBackend (encodeBackend backend) = some backend := by
  cases backend; simp [encodeBackend, decodeBackend]

def encodeTheory (theory : Presentation.TheoryDigest) : Sx := .atom theory.val
def decodeTheory : Sx → Option Presentation.TheoryDigest
  | .atom digest => some ⟨digest⟩
  | _ => none
@[simp] theorem decode_encodeTheory (theory : Presentation.TheoryDigest) :
    decodeTheory (encodeTheory theory) = some theory := rfl

def encodeReplay (replay : ReplayIdentity) : Sx :=
  .list [.atom Tag.replay.text, encodeCoreVersion replay.core, .atom replay.policy.val,
    .list (replay.backends.map encodeBackend), .list (replay.theories.map encodeTheory),
    .atom replay.artifact.val]
def decodeReplay : Sx → Option ReplayIdentity
  | .list [.atom raw, core, .atom policy, .list backends, .list theories,
      .atom artifact] =>
      match Tag.parse raw with
      | some .replay => do
          return ⟨← decodeCoreVersion core, ⟨policy⟩, ← decodeList decodeBackend backends,
            ← decodeList decodeTheory theories, ⟨artifact⟩⟩
      | _ => none
  | _ => none
@[simp] theorem decode_encodeReplay (replay : ReplayIdentity) :
    decodeReplay (encodeReplay replay) = some replay := by
  cases replay
  simp [encodeReplay, decodeReplay, decodeList_map _ _ decode_encodeBackend,
    decodeList_map _ _ decode_encodeTheory]

/-- Reuse the production metadata spelling. Its fixture decoder imposes OS/path
admission restrictions, which are not restrictions on immutable typed captures;
this decoder preserves every ObjectMeta, including rejected source evidence. -/
def encodeMeta := EvidenceDriver.encodeMeta

def decodeMeta : Sx → Option ObjectMeta
  | .list [.atom raw, .atom id, .atom path, .atom length, .atom digest] =>
      match Tag.parse raw with
      | some .object => do return ⟨⟨id⟩, ⟨path⟩, ← ND.decodeNat length, ⟨digest⟩⟩
      | _ => none
  | _ => none
@[simp] theorem decode_encodeMeta (metadata : ObjectMeta) :
    decodeMeta (encodeMeta metadata) = some metadata := by
  cases metadata
  simp [encodeMeta, EvidenceDriver.encodeMeta, decodeMeta, Tag.parse, Tag.spelling,
    Lara.Process.Wire.Spelling.parse, Tag.text]

mutual
  /-- Total typed JSON codecs preserve member order, duplicate keys, and number
  lexemes. No opaque JSON text or partial fixture parser enters the source model. -/
  def encodeJson : JsonValue → Sx
    | .object entries => .list [.atom Tag.object.text, encodeJsonEntries entries]
    | .array values => .list [.atom Tag.array.text, encodeJsonValues values]
    | .string text => .list [.atom Tag.string.text, .atom text]
    | .number text => .list [.atom Tag.number.text, .atom text]
    | .bool true => .atom Tag.true.text
    | .bool false => .atom Tag.false.text
    | .null => .atom Tag.null.text
  def encodeJsonEntries : JsonEntries → Sx
    | .nil => .list []
    | .cons key value rest =>
        .list [.atom key.val, encodeJson value, encodeJsonEntries rest]
  def encodeJsonValues : JsonValues → Sx
    | .nil => .list []
    | .cons value rest => .list [encodeJson value, encodeJsonValues rest]
end

def encodeText (text : String) : Sx := .atom text
def decodeText : Sx → Option String
  | .atom text => some text
  | _ => none
@[simp] theorem decode_encodeText (text : String) :
    decodeText (encodeText text) = some text := rfl

mutual
  def decodeJson : Sx → Option JsonValue
    | .list [.atom raw, value] =>
        match Tag.parse raw with
        | some .object => (decodeJsonEntries value).map .object
        | some .array => (decodeJsonValues value).map .array
        | some .string => (decodeText value).map .string
        | some .number => (decodeText value).map .number
        | _ => none
    | .atom raw =>
        match Tag.parse raw with
        | some .true => some (.bool true)
        | some .false => some (.bool false)
        | some .null => some .null
        | _ => none
    | _ => none
  termination_by wire => sizeOf wire
  def decodeJsonEntries : Sx → Option JsonEntries
    | .list [] => some .nil
    | .list [.atom key, value, rest] => do
        return .cons ⟨key⟩ (← decodeJson value) (← decodeJsonEntries rest)
    | _ => none
  termination_by wire => sizeOf wire
  def decodeJsonValues : Sx → Option JsonValues
    | .list [] => some .nil
    | .list [value, rest] => do
        return .cons (← decodeJson value) (← decodeJsonValues rest)
    | _ => none
  termination_by wire => sizeOf wire
end

mutual
  @[simp] theorem decode_encodeJson (value : JsonValue) :
      decodeJson (encodeJson value) = some value := by
    cases value with
    | object entries => simp [encodeJson, decodeJson, decode_encodeJsonEntries entries]
    | array values => simp [encodeJson, decodeJson, decode_encodeJsonValues values]
    | string text => simp [encodeJson, decodeJson, decodeText]
    | number text => simp [encodeJson, decodeJson, decodeText]
    | bool value => cases value <;> simp [encodeJson, decodeJson]
    | null => simp [encodeJson, decodeJson]
  @[simp] theorem decode_encodeJsonEntries (entries : JsonEntries) :
      decodeJsonEntries (encodeJsonEntries entries) = some entries := by
    cases entries with
    | nil => simp [encodeJsonEntries, decodeJsonEntries]
    | cons key value rest => simp [encodeJsonEntries, decodeJsonEntries,
        decode_encodeJson value, decode_encodeJsonEntries rest]
  @[simp] theorem decode_encodeJsonValues (values : JsonValues) :
      decodeJsonValues (encodeJsonValues values) = some values := by
    cases values with
    | nil => simp [encodeJsonValues, decodeJsonValues]
    | cons value rest => simp [encodeJsonValues, decodeJsonValues,
        decode_encodeJson value, decode_encodeJsonValues rest]
end

def encodeColumn (column : ColumnName) : Sx := .atom column.val
def decodeColumn : Sx → Option ColumnName
  | .atom text => some ⟨text⟩
  | _ => none
@[simp] theorem decode_encodeColumn (column : ColumnName) :
    decodeColumn (encodeColumn column) = some column := rfl

def encodeRow (row : List String) : Sx := .list (row.map encodeText)
def decodeRow : Sx → Option (List String)
  | .list cells => decodeList decodeText cells
  | _ => none
@[simp] theorem decode_encodeRow (row : List String) :
    decodeRow (encodeRow row) = some row :=
  decodeList_map _ _ decode_encodeText row

def encodeCsv (table : CsvTable) : Sx :=
  .list [.list (table.header.map encodeColumn), .list (table.rows.map encodeRow)]
def decodeCsv : Sx → Option CsvTable
  | .list [.list header, .list rows] => do
      return ⟨← decodeList decodeColumn header, ← decodeList decodeRow rows⟩
  | _ => none
@[simp] theorem decode_encodeCsv (table : CsvTable) :
    decodeCsv (encodeCsv table) = some table := by
  cases table
  simp [encodeCsv, decodeCsv, decodeList_map _ _ decode_encodeColumn,
    decodeList_map _ _ decode_encodeRow]

def encodePayload : Payload → Sx
  | .csv table => .list [.atom Tag.csv.text, encodeCsv table]
  | .json value => .list [.atom Tag.json.text, encodeJson value]
def decodePayload : Sx → Option Payload
  | .list [.atom raw, value] =>
      match Tag.parse raw with
      | some .csv => (decodeCsv value).map .csv
      | some .json => (decodeJson value).map .json
      | _ => none
  | _ => none
@[simp] theorem decode_encodePayload (payload : Payload) :
    decodePayload (encodePayload payload) = some payload := by
  cases payload <;> simp [encodePayload, decodePayload]

def encodeCaptured (captured : CapturedObject) : Sx :=
  .list [encodeMeta captured.metadata, encodePayload captured.payload]
def decodeCaptured : Sx → Option CapturedObject
  | .list [metadata, payload] => do
      return ⟨← decodeMeta metadata, ← decodePayload payload⟩
  | _ => none
@[simp] theorem decode_encodeCaptured (captured : CapturedObject) :
    decodeCaptured (encodeCaptured captured) = some captured := by
  cases captured; simp [encodeCaptured, decodeCaptured]

def encodeCaptureResult : Except String CapturedObject → Sx
  | .error reason => .list [.atom Tag.failed.text, .atom reason]
  | .ok captured => .list [.atom Tag.captured.text, encodeCaptured captured]
def decodeCaptureResult : Sx → Option (Except String CapturedObject)
  | .list [.atom raw, value] =>
      match Tag.parse raw with
      | some .failed => match value with | .atom reason => some (.error reason) | _ => none
      | some .captured => (decodeCaptured value).map .ok
      | _ => none
  | _ => none
@[simp] theorem decode_encodeCaptureResult (result : Except String CapturedObject) :
    decodeCaptureResult (encodeCaptureResult result) = some result := by
  cases result <;> simp [encodeCaptureResult, decodeCaptureResult]

def encodeSnapshotEntry (entry : ObjectId × Except String CapturedObject) : Sx :=
  .list [.atom entry.1.val, encodeCaptureResult entry.2]
def decodeSnapshotEntry : Sx → Option (ObjectId × Except String CapturedObject)
  | .list [.atom id, result] => do return (⟨id⟩, ← decodeCaptureResult result)
  | _ => none
@[simp] theorem decode_encodeSnapshotEntry (entry : ObjectId × Except String CapturedObject) :
    decodeSnapshotEntry (encodeSnapshotEntry entry) = some entry := by
  rcases entry with ⟨⟨id⟩, result⟩
  simp [encodeSnapshotEntry, decodeSnapshotEntry]

def encodeCapture (capture : EvidenceCapture) : Sx :=
  .list [.atom Tag.evidence.text, .list (capture.snapshot.map encodeSnapshotEntry),
    .list (capture.manifest.map encodeMeta)]
def decodeCapture : Sx → Option EvidenceCapture
  | .list [.atom raw, .list snapshot, .list manifest] =>
      match Tag.parse raw with
      | some .evidence => do
          return ⟨← decodeList decodeSnapshotEntry snapshot, ← decodeList decodeMeta manifest⟩
      | _ => none
  | _ => none
@[simp] theorem decode_encodeCapture (capture : EvidenceCapture) :
    decodeCapture (encodeCapture capture) = some capture := by
  cases capture
  simp [encodeCapture, decodeCapture, decodeList_map _ _ decode_encodeSnapshotEntry,
    decodeList_map _ _ decode_encodeMeta]

def encodeOptionalCapture : Option EvidenceCapture → Sx
  | none => .list [.atom Tag.absent.text]
  | some capture => .list [.atom Tag.present.text, encodeCapture capture]
def decodeOptionalCapture : Sx → Option (Option EvidenceCapture)
  | .list [.atom raw] =>
      match Tag.parse raw with
      | some .absent => some none
      | _ => none
  | .list [.atom raw, capture] =>
      match Tag.parse raw with
      | some .present => (decodeCapture capture).map some
      | _ => none
  | _ => none
@[simp] theorem decode_encodeOptionalCapture (capture : Option EvidenceCapture) :
    decodeOptionalCapture (encodeOptionalCapture capture) = some capture := by
  cases capture <;> simp [encodeOptionalCapture, decodeOptionalCapture]

/-- Authoritative source ASTs are exactly the existing Presentation serializers. -/
def encodeSurface (surface : Surface.Input) : Sx :=
  .list [encodePresentation (Presentation.printProgram surface.program),
    encodePresentation (Presentation.printPolicy surface.policy)]
def decodeSurfaceRaw : Sx → Option Surface.Input
  | .list [program, policy] => do
      return ⟨← Presentation.parseProgram (← decodePresentation program),
        ← Presentation.parsePolicy (← decodePresentation policy)⟩
  | _ => none
@[simp] theorem decode_encodeSurfaceRaw (surface : Surface.Input) :
    decodeSurfaceRaw (encodeSurface surface) = some surface := by
  cases surface
  simp [encodeSurface, decodeSurfaceRaw, Presentation.parse_printProgram,
    Presentation.parse_printPolicy]

def decodeSurface := canonical encodeSurface decodeSurfaceRaw
@[simp] theorem decode_encodeSurface (surface : Surface.Input) :
    decodeSurface (encodeSurface surface) = some surface :=
  canonical_roundtrip _ _ decode_encodeSurfaceRaw surface
 theorem decodeSurface_canonical {wire : Sx} {surface : Surface.Input}
    (h : decodeSurface wire = some surface) : encodeSurface surface = wire :=
  canonical_sound _ _ h

def encode (input : SourceInput) : Sx :=
  .list [.atom Tag.source.text, .atom Tag.versionOne.text, encodeSurface input.surface,
    encodeReplay input.replay, encodeOptionalCapture input.capture]
def decodeRaw : Sx → Option SourceInput
  | .list [.atom raw, .atom version, surface, replay, capture] =>
      match Tag.parse raw, Tag.parse version with
      | some .source, some .versionOne => do
          return ⟨← decodeSurface surface, ← decodeReplay replay, ← decodeOptionalCapture capture⟩
      | _, _ => none
  | _ => none
@[simp] theorem decode_encodeRaw (input : SourceInput) :
    decodeRaw (encode input) = some input := by
  cases input; simp [encode, decodeRaw]

/-- Decoding does not claim compatibility or evidence admissibility. Those are
closed semantic checks on the retained source, not wire normalization. -/
def decode := canonical encode decodeRaw
@[simp] theorem decode_encode (input : SourceInput) : decode (encode input) = some input :=
  canonical_roundtrip _ _ decode_encodeRaw input
 theorem decode_canonical {wire : Sx} {input : SourceInput}
    (h : decode wire = some input) : encode input = wire := canonical_sound _ _ h
 theorem encode_injective : Function.Injective encode :=
  injective_of_roundtrip _ _ decode_encode

/-- Declaration fragments reuse sxDecl/unDecl without expanding source sugar. -/
def encodeFragment (decls : List Presentation.Decl) : Sx :=
  .list [.atom Tag.fragment.text, .atom Tag.versionOne.text,
    encodePresentation (Presentation.sxList Presentation.sxDecl decls)]
def decodeFragmentRaw : Sx → Option (List Presentation.Decl)
  | .list [.atom raw, .atom version, decls] =>
      match Tag.parse raw, Tag.parse version with
      | some .fragment, some .versionOne => do
          Presentation.unSxList Presentation.unDecl (← decodePresentation decls)
      | _, _ => none
  | _ => none
@[simp] theorem decode_encodeFragmentRaw (decls : List Presentation.Decl) :
    decodeFragmentRaw (encodeFragment decls) = some decls := by
  simp [encodeFragment, decodeFragmentRaw]
def decodeFragment := canonical encodeFragment decodeFragmentRaw
@[simp] theorem decode_encodeFragment (decls : List Presentation.Decl) :
    decodeFragment (encodeFragment decls) = some decls :=
  canonical_roundtrip _ _ decode_encodeFragmentRaw decls
 theorem decodeFragment_canonical {wire : Sx} {decls : List Presentation.Decl}
    (h : decodeFragment wire = some decls) : encodeFragment decls = wire :=
  canonical_sound _ _ h
 theorem encodeFragment_injective : Function.Injective encodeFragment :=
  injective_of_roundtrip _ _ decode_encodeFragment

end Lara.Process.Source.Wire
