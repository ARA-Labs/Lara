/-
The Lean reference executable for `pw-run 1`: `pw-run <file.sexp>`.

It reads the run file, reads every `(file PATH)` world source relative to the
run file's directory, and hands the pure `Lara.PW.Run.run` the parsed inputs.
A `(lara PATH)` source is reported as a `world-input` fault: the reference has
no surface parser, and the gate runs it on the document `lara pw-input` derives.
Output is one S-expression on stdout either way — `pw-result 1` or
`pw-error 1` — with the exit code `Error.exitCode` fixes. The Haskell
`lara pw` door implements the same contract; `scripts/check-pw-conformance.py`
compares the two.
-/
import Lara.PW.Run

namespace Lara.PW.RunMain
open Lara.Driver (Sx)
open Lara.PW.Run

/-- Read and parse a world source; failures stay per-world, so the pure loader
reports them in declaration order. A `lara` source is a presentation program,
and this reference has no surface parser: it is reported as unreadable, and
`lara pw-input` is the door that derives a run document with the envelope
inline. -/
def readSource (dir : System.FilePath) : WorldSource → IO (Except String Sx)
  | .inline e => pure (.ok e)
  | .lara p => pure (.error (p ++ ": lara sources have no Lean reader; derive an inline envelope with lara pw-input"))
  | .file p => do
    let rel : System.FilePath := p
    let path := if rel.isAbsolute then rel else dir / rel
    try
      let text ← IO.FS.readFile path
      pure (Lara.Driver.parseWire text)
    catch e => pure (.error e.toString)

def inputsOf (dir : System.FilePath) (doc : RunDoc) : IO (List WorldInput) :=
  doc.worlds.mapM fun d => do
    let input ← readSource dir d.source
    pure ⟨d.id, d.context, input⟩

def runFile (file : String) : IO (Except Error Outcome) := do
  let text ← try pure (Except.ok (← IO.FS.readFile file))
    catch e => pure (Except.error e.toString)
  match text with
  | .error detail => pure (.error (.io detail))
  | .ok text =>
    match parse text with
    | .error e => pure (.error (.wire e))
    | .ok doc =>
      let dir := (System.FilePath.mk file).parent.getD "."
      let inputs ← inputsOf dir doc
      pure (run doc inputs)

def main (args : List String) : IO UInt32 := do
  let result ← match args with
    | [file] => runFile file
    | _ => pure (.error .usage)
  let out ← IO.getStdout
  match result with
  | .ok o => out.putStrLn (Lara.Driver.printSx (encodeOutcome o)); pure 0
  | .error e => out.putStrLn (Lara.Driver.printSx (encodeError e)); pure e.exitCode

end Lara.PW.RunMain

def main (args : List String) : IO UInt32 := Lara.PW.RunMain.main args
