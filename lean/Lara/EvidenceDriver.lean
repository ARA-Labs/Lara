import Lara.Evidence.Admission
import Lara.AdmissionDriver
import Lara.Surface.Check

namespace Lara.EvidenceDriver
open Lara Lara.Evidence Lara.Driver

private def nat (s : String) : Except String Nat :=
  match s.toNat? with | some n => .ok n | none => .error "expected natural"
private def version (s : String) : Except String CheckerVersion :=
  match s.toNat? with
  | some n => if toString n = s then .ok ⟨Int.ofNat n⟩ else .error "noncanonical checker version"
  | none => .error "expected checker version"
def decodeChecker : Sx → Except String (LeafCheckerId × CheckerVersion)
  | .list [.atom "csv-row", .atom v] => do pure (.csvRow, ← version v)
  | .list [.atom "json-pointer", .atom v] => do pure (.jsonPointer, ← version v)
  | _ => .error "checker entry"
def decodeEncoding : Sx → Except String TermEncoding
  | .atom "decimal" => .ok .decimal
  | .atom "text" => .ok .text
  | .atom "decimal-line" => .ok .decimalLine
  | _ => .error "term encoding"
private def pointerToken : List Char → Except String (List Char)
  | [] => .ok []
  | '~' :: '0' :: rest => do pure ('~' :: (← pointerToken rest))
  | '~' :: '1' :: rest => do pure ('/' :: (← pointerToken rest))
  | '~' :: _ => .error "pointer escape"
  | c :: rest => do pure (c :: (← pointerToken rest))
def decodePath (path : String) : Except String JsonPath :=
  if path = "" then .ok [] else
  if path.startsWith "/" then
    ((path.drop 1).toString.splitOn "/").mapM fun token => do
      pure ⟨String.ofList (← pointerToken token.toList)⟩
  else .error "pointer must begin with slash"
def decodeCsvSelector : Sx → Except String CsvSelector
  | .list [.atom column, encoding] => do pure ⟨⟨column⟩, ← decodeEncoding encoding⟩
  | _ => .error "csv selector"
def decodeJsonSelector : Sx → Except String JsonSelector
  | .list [.atom path, encoding] => do pure ⟨← decodePath path, ← decodeEncoding encoding⟩
  | _ => .error "json selector"
def decodeRequest : Sx → Except String ExtractionRequest
  | .list [.atom "csv-row", .atom v, .atom id,
      .list [.atom "key", .atom column, .atom raw],
      .list (.atom "select" :: sels), .list [.atom "predicate", .atom pred]] => do
    pure (.csvRowRequest (← version v) ⟨id⟩ ⟨column⟩ raw (← sels.mapM decodeCsvSelector) pred)
  | .list [.atom "json-pointer", .atom v, .atom id,
      .list (.atom "select" :: sels), .list [.atom "predicate", .atom pred]] => do
    pure (.jsonPointerRequest (← version v) ⟨id⟩ (← sels.mapM decodeJsonSelector) pred)
  | _ => .error "extraction request"
def decodeMeta : Sx → Except String ObjectMeta
  | .list [.atom "object", .atom id, .atom path, .atom length, .atom digest] => do
    let n ← nat length
    let components := path.splitOn "/"
    let hex := (digest.drop 7).toString
    if id == "" || path == "" || path.startsWith "/" ||
        path.toList.any (fun c => c.toNat == 0) ||
        components.any (fun c => c == "" || c == "." || c == "..") ||
        !digest.startsWith "sha256:" || hex.length != 64 ||
        !hex.toList.all (fun c => decide (('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f'))) ||
        decide (n > 8388608) || toString n != length then
      .error "invalid object metadata"
    else pure ⟨⟨id⟩, ⟨path⟩, n, ⟨digest⟩⟩
  | _ => .error "object metadata"
private def strings : List Sx → Except String (List String) :=
  List.mapM fun | .atom s => .ok s | _ => .error "string atom"
mutual
  partial def decodeJson : Sx → Except String JsonValue
    | .list (.atom "object" :: entries) => do pure (.object (← decodeEntries entries))
    | .list (.atom "array" :: values) => do pure (.array (← decodeValues values))
    | .list [.atom "string", .atom s] => .ok (.string s)
    | .list [.atom "number", .atom s] => .ok (.number s)
    | .atom "true" => .ok (.bool true)
    | .atom "false" => .ok (.bool false)
    | .atom "null" => .ok .null
    | _ => .error "typed JSON value"
  partial def decodeEntries : List Sx → Except String JsonEntries
    | [] => .ok .nil
    | .list [.atom "entry", .atom key, value] :: rest => do
      pure (.cons ⟨key⟩ (← decodeJson value) (← decodeEntries rest))
    | _ => .error "typed JSON entry"
  partial def decodeValues : List Sx → Except String JsonValues
    | [] => .ok .nil
    | value :: rest => do pure (.cons (← decodeJson value) (← decodeValues rest))
end
def decodePayload : Sx → Except String Payload
  | .list [.atom "csv", .list (.atom "header" :: header), .list (.atom "rows" :: rows)] => do
    let header ← strings header
    let rows ← rows.mapM fun
      | .list (.atom "row" :: cells) => strings cells
      | _ => .error "CSV row"
    pure (.csv ⟨header.map (fun s => ⟨s⟩), rows⟩)
  | .list [.atom "json", value] => do pure (.json (← decodeJson value))
  | _ => .error "typed object"
def decodeSnapshotEntry (manifest : List ObjectMeta) : Sx → Except String (ObjectId × Except String CapturedObject)
  | .list [.atom "failed", .atom id, .atom reason] => .ok (⟨id⟩, .error reason)
  | .list [.atom "captured", .atom id, payload] => do
    let metadata ← match manifestObject manifest ⟨id⟩ with
      | none => .error "captured ID absent from manifest"
      | some metadata => .ok metadata
    pure (⟨id⟩, .ok ⟨metadata, ← decodePayload payload⟩)
  | _ => .error "snapshot entry"
def decodeLeaf : Sx → Except String Presentation.Leaf
  | .list [.atom "leaf", .atom id, kind, provenance,
      .list (.atom "refs" :: refs), request, proposition] => do
    let extraction ← match request with
      | .atom "none" => .ok none
      | request => do pure (some (← decodeRequest request))
    pure ⟨⟨id⟩, ← decodeAtom proposition, ← AdmissionDriver.decodeKind kind,
      ← AdmissionDriver.decodeProvenance provenance,
      (← strings refs).map (fun ref => ⟨ref⟩), extraction⟩
  | _ => .error "evidence leaf"

structure Fixture where
  policy : EvidencePolicy
  manifest : List ObjectMeta
  snapshot : Snapshot
  leaves : List Presentation.Leaf
  table : List Lara.Admission.AdmissionRow
  unit : Sx

def decodeFixture : Sx → Except String Fixture
  | .list [.atom "evidence-model", .atom "1", .list (.atom "allowlist" :: allowlist),
      .list (.atom "manifest" :: objects), .list (.atom "snapshot" :: snapshot),
      .list (.atom "leaves" :: leaves), .list [.atom "ordinary", table, unit]] => do
    let policy ← allowlist.mapM decodeChecker
    let manifest ← objects.mapM decodeMeta
    let snapshot ← snapshot.mapM (decodeSnapshotEntry manifest)
    let leaves ← leaves.mapM decodeLeaf
    if !(decide policy.Nodup) || !(decide (manifest.map (·.id)).Nodup) ||
        !(decide (manifest.map (·.path)).Nodup) || decide (manifest.length > 256) ||
        !(decide (snapshot.map (·.1)).Nodup) || !(decide (leaves.map (·.id)).Nodup) then
      .error "duplicate declaration"
    else pure ⟨policy, manifest, snapshot, leaves, ← AdmissionDriver.decodeTable table, unit⟩
  | _ => .error "expected evidence-model@1 envelope"

def encodeMeta (m : ObjectMeta) : Sx :=
  .list [.atom "object", .atom m.id.val, .atom m.path.val, .atom (toString m.length), .atom m.digest.val]
def stageName : Stage → String
  | .binding => "binding"
  | .capture => "capture"
  | .extraction => "extraction"
def encodeError (e : AdmissionError) : Sx :=
  .list [.atom "rejected", .atom (stageName e.stage), .atom e.leaf,
    .atom (e.object.map (·.val) |>.getD "none"), .atom e.reason]
def encodeJudgment (j : Judgment) : Sx :=
  .list [.atom "leaf", .atom j.leaf, encodeAtom j.normalized,
    .list (.atom "deps" :: j.dependencies.map encodeMeta)]

/-- No supplied expected propositions enter the registry. The expected source
atoms are compared only by `admit`, after actual typed extraction. -/
def evaluate (fx : Fixture) : Except String Sx := do
  let decoded ← decodeUnit fx.unit
  let metas := fx.leaves.map fun leaf =>
    (⟨⟨leaf.id.val⟩, leaf.kind, leaf.provenance⟩ : Lara.Admission.LeafMeta)
  if decoded.leaves != fx.leaves.map (fun leaf => (⟨leaf.id.val⟩, leaf.prop)) then
    .error "ordinary/evidence leaf table mismatch"
  else
    let aligned : Lara.Admission.AlignedAttacks decoded.argsRaw decoded.attacksRaw :=
      ⟨decoded.atts, decoded.attacksAligned, decoded.argIdsNodup⟩
    let ordinary := Lara.Admission.evaluateAdmission canonNum fx.table metas decoded.leaves
      decoded.argsRaw decoded.attacksRaw decoded.groups aligned
    let result ← match ordinary with
      | .invalid _ => pure (AdmissionDriver.encodeOutcome ordinary)
      | .rejected _ => pure (.list [.atom "rejected", .atom "policy", AdmissionDriver.encodeOutcome ordinary])
      | .accepted retained =>
        match admit fx.snapshot fx.policy fx.manifest extract fx.leaves with
        | .error error => pure (encodeError error)
        | .ok judgments => do
          let keptIds := retained.prune.checkedLeaves.map (fun l => l.1.name)
          let keptArgs := retained.prune.keptArgs.map (·.1)
          let declared := fx.leaves.filter (fun leaf => leaf.kind != .certified)
          let registry := buildRegistry decoded.theories
          let unit : Lara.Unit :=
            { sigma := decoded.sigma, policy := decoded.policy,
              args := retained.prune.keptArgs.map (·.2), atts := retained.prune.keptAttacks }
          let holes ← match Check.Unit.checkUnit (Lara.Admission.buildGamma retained.prune.checkedLeaves)
              registry (retained.prune.checkedLeaves.map (·.2) ++
                decoded.theories.flatMap (·.2) ++ decoded.queries) unit with
            | .error _ => pure (.list [.atom "core-rejected"])
            | .ok checked => pure (.list (.atom "holes" :: checked.holes.map (fun hole =>
                .list [.atom "hole", .atom (keptArgs[hole.index]?.getD ""),
                  encodeAtom hole.conclusion,
                  .list (.atom "obligations" :: hole.obligations.map (fun q => .atom q.name))])))
          pure (.list [.atom "accepted", .list (.atom "checked" :: judgments.map encodeJudgment),
            .list (.atom "declared" :: declared.map (fun l => .atom l.id.val)),
            .list (.atom "retained-checked" ::
              (judgments.filter (fun j => decide (j.leaf ∈ keptIds))).map (fun j => .atom j.leaf)),
            .list [.atom "ordinary", AdmissionDriver.encodeOutcome ordinary],
            .list [.atom "retained", .list (.atom "leaves" :: keptIds.map .atom),
              .list (.atom "args" :: keptArgs.map .atom),
              .list (.atom "attacks" :: (decoded.attacksRaw.filter retained.prune.keepAttack).map AdmissionDriver.encodeRawAttack), holes]])
    pure (.list [.atom "evidence-result", .atom "1", result])

def main (args : List String) : IO _root_.Unit := do
  match args with
  | [path] =>
    let contents ← IO.FS.readFile (⟨path⟩ : System.FilePath)
    match parseWire contents >>= decodeFixture >>= evaluate with
    | .error message => IO.eprintln ("evidence-driver: " ++ message); IO.Process.exit 2
    | .ok output => IO.println (printSx output)
  | _ => IO.eprintln "usage: evidence-driver <fixture.sexp>"; IO.Process.exit 2

end Lara.EvidenceDriver

/-- Executable entry point for `evidence-driver`: the driver's `main` lives in
the `Lara.EvidenceDriver` namespace so that importing the module never collides
with another executable's entry point. -/
def main (args : List String) : IO _root_.Unit :=
  Lara.EvidenceDriver.main args
