/-
The executable admission differential driver (metatheory plan Task 3): the
Lean side of `scripts/admission-differential.sh`.

Reads one test-only fixture under `fixtures/admission/` — leaf metadata, the
admission table, a wire-shaped declared unit, and the committed expected
outcome — runs the proved `Lara.Admission.evaluateAdmission` judgment over
it, and prints the canonical outcome S-expression on stdout.  The fixture's
`expected` section must reproduce the computed encoding byte-for-byte; a
mismatch is an error (exit 1), a malformed fixture is a codec error (exit 2,
empty stdout), matching the Haskell twin `scripts/check-admission.hs`.

The fixture schema is test-only: it is NOT a production wire format and never
enters `lara-core@0.1` or replay identity.
-/
import Lara.Driver
import Lara.Admission

namespace Lara.AdmissionDriver

open Lara Lara.Support
open Lara.Presentation (LeafKind Provenance Admission)
open Lara.Attack
open Lara.RawAttack Lara.Admission Lara.Driver

/-- The production numeric-literal canonicalizer (group consistency). -/
def dcanon : String → String := Lara.canonNum

/-! ### Fixture decoding (test-only schema) -/

structure Fixture where
  metas : List LeafMeta
  table : List AdmissionRow
  unit : Sx
  expected : Sx

def decodeKind : Sx → Except String LeafKind
  | .atom "observed" => .ok .observed
  | .atom "attested" => .ok .attested
  | .atom "assumed" => .ok .assumed
  | .atom "certified" => .ok .certified
  | _ => .error "fixture: unknown leaf kind"

def decodeProvenance : Sx → Except String Provenance
  | .atom "user" => .ok .user
  | .atom "ai" => .ok .aiExecuted
  | .list [.atom "checker", .atom n, .atom v] => .ok (.checker n v)
  | _ => .error "fixture: unknown provenance"

def decodeDecision : Sx → Except String Admission
  | .atom "admit" => .ok .admit
  | .atom "quarantine" => .ok .quarantine
  | .atom "reject" => .ok .reject
  | _ => .error "fixture: unknown admission decision"

/-- `(meta "id" (kind K) (provenance P))` -/
def decodeMetaRow : Sx → Except String LeafMeta
  | .list [.atom "meta", .atom lid, kindE, provE] => do
      let k ← (match kindE with
        | .list [.atom "kind", kE] => decodeKind kE
        | _ => .error "fixture: malformed meta kind")
      let p ← (match provE with
        | .list [.atom "provenance", pE] => decodeProvenance pE
        | _ => .error "fixture: malformed meta provenance")
      .ok ⟨⟨lid⟩, k, p⟩
  | _ => .error "fixture: malformed meta"

/-- `(metas (meta …)*)` -/
def decodeMetas : Sx → Except String (List LeafMeta)
  | .list (.atom "metas" :: rows) => rows.mapM decodeMetaRow
  | _ => .error "fixture: malformed metas section"

/-- `(row (kind K) (provenance P) (decision D))` -/
def decodeTableRow : Sx → Except String AdmissionRow
  | .list [.atom "row", .list [.atom "kind", kindE], .list [.atom "provenance", provE],
      .list [.atom "decision", decE]] => do
      let k ← decodeKind kindE
      let p ← decodeProvenance provE
      let d ← decodeDecision decE
      .ok { key := (k, p), decision := d }
  | _ => .error "fixture: malformed admission row"

/-- `(table (row …)*)` -/
def decodeTable : Sx → Except String (List AdmissionRow)
  | .list (.atom "table" :: rows) => rows.mapM decodeTableRow
  | _ => .error "fixture: malformed table section"

/-- Validate one canonical audit cause. Expected bytes are part of the
differential oracle, so malformed nested payloads are codec errors rather than
ordinary oracle mismatches. -/
def validateExpectedCause : Sx → Except String _root_.Unit
  | .list [.atom "cause", .atom "policy"] => .ok ()
  | .list [.atom "cause", .list [.atom "group", .atom _]] => .ok ()
  | _ => .error "fixture: malformed expected outcome"

def validateExpectedLeafRow : Sx → Except String _root_.Unit
  | .list (.atom "leaf-row" :: .atom _ :: causes) => do
      if causes.isEmpty then
        .error "fixture: malformed expected outcome"
      else
        let _ ← causes.mapM validateExpectedCause
        .ok ()
  | _ => .error "fixture: malformed expected outcome"

def validateExpectedAtom : Sx → Except String _root_.Unit
  | .atom _ => .ok ()
  | _ => .error "fixture: malformed expected outcome"

def validateExpectedAttack (e : Sx) : Except String _root_.Unit := do
  let _ ← decodeAttack e
  .ok ()

def validateExpectedAudit : Sx → Except String _root_.Unit
  | .list [.atom "audit", .list (.atom "leaves" :: rows),
      .list (.atom "args" :: args), .list (.atom "attacks" :: attacks)] => do
      let _ ← rows.mapM validateExpectedLeafRow
      let _ ← args.mapM validateExpectedAtom
      let _ ← attacks.mapM validateExpectedAttack
      .ok ()
  | _ => .error "fixture: malformed expected outcome"

/-- Exact grammar of `encodeOutcome`. Shape-valid but semantically unrelated
S-expressions are rejected before evaluation, on both differential sides. -/
def validateExpectedOutcome : Sx → Except String _root_.Unit
  | .list [.atom "invalid",
      .list [.atom "duplicate-key", kindE, provenanceE]] => do
      let _ ← decodeKind kindE
      let _ ← decodeProvenance provenanceE
      .ok ()
  | .list [.atom "invalid",
      .list [.atom "duplicate-leaf-id", .atom _]] => .ok ()
  | .list [.atom "invalid", .atom "metadata-leaf-misalignment"] => .ok ()
  | .list [.atom "rejected", .list [.atom "leaf", .atom _],
      .list [.atom "kind", kindE], .list [.atom "provenance", provenanceE],
      .list [.atom "decision", .atom "reject"]] => do
      let _ ← decodeKind kindE
      let _ ← decodeProvenance provenanceE
      .ok ()
  | .list [.atom "accepted", auditE] => validateExpectedAudit auditE
  | _ => .error "fixture: malformed expected outcome"

/-- `(admission (metas …) (table …) (unit …) (expected …))` — exactly four
sections, in order; the expected section carries the committed outcome. -/
def decodeFixture (e : Sx) : Except String Fixture :=
  match e with
  | .list [.atom "admission", metasE, tableE, unitE, expectedE] => do
      let metas ← decodeMetas metasE
      let table ← decodeTable tableE
      let expected ← (match expectedE with
        | .list [.atom "expected", expectedX] => .ok expectedX
        | _ => .error "fixture: malformed expected section")
      let _ ← validateExpectedOutcome expected
      .ok { metas := metas, table := table, unit := unitE, expected := expected }
  | _ => .error "fixture: expected exact (admission (metas …) (table …) (unit …) (expected …))"


/-! ### Outcome encoding (canonical test encoding, mirrors the Haskell twin) -/

def encodeKind : LeafKind → Sx
  | .observed => .atom "observed"
  | .attested => .atom "attested"
  | .assumed => .atom "assumed"
  | .certified => .atom "certified"

def encodeProvenance : Provenance → Sx
  | .user => .atom "user"
  | .aiExecuted => .atom "ai"
  | .checker n v => .list [.atom "checker", .atom n, .atom v]

def encodeDecision : Admission → Sx
  | .admit => .atom "admit"
  | .quarantine => .atom "quarantine"
  | .reject => .atom "reject"

def encodePosElem : PosElem → Sx
  | .prem n => .list [.atom "prem", .atom (toString n)]
  | .ques q => .list [.atom "ques", .atom q.name]

def encodeRawAttack : RawAttack → Sx
  | .rebut w u => .list [.atom "rebut", .atom w, .atom u]
  | .undercut w u π => .list [.atom "undercut", .atom w, .atom u, .list (.atom "pos" :: π.map encodePosElem)]
  | .undermine w u π => .list [.atom "undermine", .atom w, .atom u, .list (.atom "pos" :: π.map encodePosElem)]

def encodeCause : AdmissionCause → Sx
  | .policy => .list [.atom "cause", .atom "policy"]
  | .group g => .list [.atom "cause", .list [.atom "group", .atom g]]

def encodeAudit (a : AdmissionAudit) : Sx :=
  .list
    [ .atom "audit"
    , .list (.atom "leaves" :: a.leaves.map (fun row =>
        .list (.atom "leaf-row" :: .atom row.1.name :: row.2.map encodeCause)))
    , .list (.atom "args" :: a.args.map .atom)
    , .list (.atom "attacks" :: a.attacks.map encodeRawAttack)
    ]

def encodeOutcome : SourceAdmission → Sx
  | .invalid (.duplicateAdmissionKey (k, p)) =>
      .list [.atom "invalid", .list [.atom "duplicate-key", encodeKind k, encodeProvenance p]]
  | .invalid (.duplicateLeafId l) =>
      .list [.atom "invalid", .list [.atom "duplicate-leaf-id", .atom l.name]]
  | .invalid .metadataLeafMisalignment =>
      .list [.atom "invalid", .atom "metadata-leaf-misalignment"]
  | .rejected r =>
      .list [.atom "rejected"
      , .list [.atom "leaf", .atom r.leaf.name]
      , .list [.atom "kind", encodeKind r.kind]
      , .list [.atom "provenance", encodeProvenance r.provenance]
      , .list [.atom "decision", encodeDecision r.matched.decision]]
  | .accepted res => .list [.atom "accepted", encodeAudit res.audit]

/-! ### The driver -/

/-- One fixture: decode, evaluate, verify against the committed expected
encoding, and print. Exit 0 with the canonical outcome on stdout when the
oracle matches; exit 1 on an oracle mismatch; exit 2 on a codec error. -/
def runOnContents (contents : String) : IO _root_.Unit := do  match parseWire contents with
  | .error msg =>
      IO.eprintln ("admission-driver: codec error at " ++ msg)
      IO.Process.exit 2
  | .ok e =>
    match decodeFixture e with
    | .error msg =>
        IO.eprintln ("admission-driver: codec error at " ++ msg)
        IO.Process.exit 2
    | .ok fx =>
      match decodeUnit fx.unit with
      | .error msg =>
          IO.eprintln ("admission-driver: codec error at " ++ msg)
          IO.Process.exit 2
      | .ok decoded =>
        let declared : AlignedAttacks decoded.argsRaw decoded.attacksRaw :=
          { resolved := decoded.atts
          , resolve_eq := decoded.attacksAligned
          , ids_nodup := decoded.argIdsNodup }
        let outcome :=
          evaluateAdmission dcanon fx.table fx.metas decoded.leaves
            decoded.argsRaw decoded.attacksRaw decoded.groups declared
        let encoded := encodeOutcome outcome
        let printed := printSx encoded
        if printed == printSx fx.expected then
          IO.println printed
        else do
          IO.eprintln "admission-driver: computed outcome differs from the fixture's expected section"
          IO.Process.exit 1

/-- Executable entry point: `admission-driver <fixture.sexp>`. -/
def main (args : List String) : IO _root_.Unit := do
  match args with
  | [path] => do
      let contents ← (do
        try
          IO.FS.readFile (⟨path⟩ : System.FilePath)
        catch _ =>
          IO.eprintln ("admission-driver: cannot read " ++ path)
          IO.Process.exit 2)
      runOnContents contents
  | _ =>
      IO.eprintln "usage: admission-driver <fixture.sexp>"
      IO.Process.exit 2

end Lara.AdmissionDriver
