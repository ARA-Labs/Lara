/-
File-driven PW example. Host contexts/worlds are documented in PWFileHost;
file-authored declarations and modal queries travel through the actual codec,
loader and elaborator. Each bridge additionally compares the explicit source
probe q(), showing that translation uses the file's map. No hidden translation
is applied to modal operands. This example protocol is separate from the
versioned authoring codec and from the frozen local checker wire contract.
-/
import Lara.Examples.PWFileHost
import Lara.PW.Wire

namespace Lara.PW.Example
open Lara.Driver (Sx)
open Lara.PW.Surface Lara.PW.Surface.Declared Lara.Examples.PWFileHost

inductive Error where
  | wire (fault : Wire.Error)
  | load (fault : LoadError)
  | form (fault : FormError)
  | io (detail : String)
  | usage

private def node (tag : String) (args : List Sx := []) : Sx :=
  .list (.atom tag :: args)

private def queryFault : Sorted.QueryFault → Sx
  | .undeclaredPredicate p => node "undeclared-predicate" [.atom p.name]
  | .illSortedArguments p => node "ill-sorted-arguments" [.atom p.name]

private def bridgeFault : BridgeError → Sx
  | .nameMismatch a b => node "name-mismatch" [.atom a.name, .atom b.name]
  | .sourceMismatch a b => node "source-mismatch" [.atom a.name, .atom b.name]
  | .targetMismatch a b => node "target-mismatch" [.atom a.name, .atom b.name]
  | .missingClause c => node "missing-clause" [.atom c.text]
  | .ruleClauseFails => node "rule-clause-fails"

/-- Stable categories and structured names; free text never controls execution. -/
def encodeError : Error → Sx
  | .wire e => node "pw-example-error" [.atom "1", .atom "wire", .atom e.tag.text, .atom e.detail]
  | .load e => node "pw-example-error" [.atom "1", .atom "load", match e with
      | .duplicateBridge n => node "duplicate-bridge" [.atom n.name]
      | .unknownSource b n => node "unknown-source" [.atom b.name, .atom n.name]
      | .unknownTarget b n => node "unknown-target" [.atom b.name, .atom n.name]
      | .invalidBridge b f => node "invalid-bridge" [.atom b.name, bridgeFault f]]
  | .form e => node "pw-example-error" [.atom "1", .atom "form", match e with
      | .unknownContext n => node "unknown-context" [.atom n.name]
      | .unknownBridge n => node "unknown-bridge" [.atom n.name]
      | .bridgeSourceMismatch b a c =>
        node "bridge-source-mismatch" [.atom b.name, .atom a.name, .atom c.name]
      | .notAQuery n f => node "not-a-query" [.atom n.name, queryFault f]]
  | .io detail => node "pw-example-error" [.atom "1", .atom "io", .atom detail]
  | .usage => node "pw-example-error" [.atom "1", .atom "usage",
      .atom "pw-example <file.sexp>"]

private def posingFault : Sorted.PosingFault → Sx
  | .sourceQuery f => node "source-query" [queryFault f]
  | .targetQuery f => node "target-query" [queryFault f]
  | .bridgeVocabulary f => node "bridge-vocabulary" [match f with
      | .pred p => node "pred" [.atom p.name]
      | .con c => node "con" [.atom c.name]]

/-- Preserve the distinction between unposable claims, incomparable worlds,
and a nonempty profile of local statuses. -/
def encodeComparison : Sorted.SortedResult → Sx
  | .notPosable f => node "not-posable" [posingFault f]
  | .compared (.incomparable r) => node "incomparable" [.atom (match r with
      | .translationUndefined => "translation-undefined"
      | .noCandidateWorld => "no-candidate-world"
      | .allCandidateBridgesRejected => "all-candidate-bridges-rejected")]
  | .compared (.comparable s ss) => node "comparable" ((s :: ss).map Wire.encodeStatus)

/-- Evaluate a posed formula only after the declaration-derived naming checks it. -/
def runQuery (E : Registry host) (p : Posed) : Except Error Bool := do
  let ⟨k, φ⟩ ← (elabPosed (naming E) p).mapError Error.form
  pure (evalFinite (finite E) (observation E) φ (worldAt k))

/-- This fixed source probe is printed with each result, so the example never
suggests that a modal target operand was implicitly translated. -/
def probe : Atom := .atom "q" .nil

/-- Parse-independent execution of a complete authored document. Comparisons
follow the registry's bridges, which `load_declarations` and `bridges_names` pin
to the file's declaration order. -/
def run (d : Wire.Document) : Except Error Sx := do
  let E ← (load host d.bridges).mapError Error.load
  let answers ← d.queries.mapM (runQuery E)
  let profiles := E.bridges.map fun b =>
    node "comparison" [.atom b.val.name, Wire.encodeAtom probe,
      encodeComparison (compareProbe E b probe)]
  pure (node "pw-example-result" [.atom "1",
    node "queries" (answers.map fun b => .atom (if b then "true" else "false")),
    node "comparisons" profiles])

def runText (text : String) : Except Error Sx := do
  run (← (Wire.parse text).mapError Error.wire)

/-- Exit 0 means the document ran, including false modal answers and tagged
incomparability results; exit 1 means input/host validation failed. -/
def main (args : List String) : IO UInt32 := do
  let result ← match args with
    | [file] =>
      try pure (runText (← IO.FS.readFile file))
      catch e => pure (.error (.io e.toString))
    | _ => pure (.error .usage)
  let out ← IO.getStdout
  match result with
  | .ok value => out.putStrLn (Lara.Driver.printSx value); pure 0
  | .error e => out.putStrLn (Lara.Driver.printSx (encodeError e)); pure 1

end Lara.PW.Example

def main (args : List String) : IO UInt32 := Lara.PW.Example.main args
