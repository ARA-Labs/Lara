/-
The Lean reference executable for `inquiry-input 1`: `inquiry-run <file.sexp>`.

It reads one document, decodes it with the strict wrapper codec, runs the
bounded runner and prints one canonical S-expression per emitted result on
stdout, or a single `inquiry-error 1` envelope. Exit codes match the plan: 0 for
a result, 1 for `unsupported`/`limit` (limit-exceeded), 2 for every other
refusal. Stderr stays empty; the executable performs no IO at library load.

The Haskell door that implements the same contract is later work (issue #22,
P6); until then this runner and `process-run` are the two Lean entry points.
-/
import Lara.Process.InquiryRun

namespace Lara.Process.InquiryRunMain

open Lara.Process
open Lara.Process.InquiryWire
open Lara.Process.InquiryRun

/-- Render a decoded document, charging the original wire input's UTF-8 bytes. -/
def render (input : InquiryInput) (sourceBytes : Nat) : List String × UInt32 :=
  match runBounded input sourceBytes with
  | .error refusal => ([Lara.Driver.printSx (encodeInquiryError ⟨none, refusal⟩)],
      exitCodeOf refusal)
  | .ok results =>
      (results.map fun result =>
        Lara.Driver.printSx (encodeInquiryResult input.process.names result), 0)

/-- Render a decode refusal: no document was produced, so no label is known. -/
def refusal (r : RunRefusal) : List String × UInt32 :=
  ([Lara.Driver.printSx (encodeInquiryError ⟨none, r⟩)], exitCodeOf r)

def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let (lines, code) ← match args with
    | [file] =>
      match (← (try (pure (some (← IO.FS.readFile file))) catch _ => pure none)) with
      | none => pure (refusal (.io s!"cannot read {file}"))
      | some text =>
        match Lara.Driver.parseWire text with
        | .error e => pure (refusal (.syntaxError e))
        | .ok sx =>
          match parseInquiryInput sx with
          | .error r => pure (refusal r)
          | .ok input => pure (render input text.utf8ByteSize)
    | _ => pure (refusal (.usage "usage: inquiry-run FILE"))
  for line in lines do out.putStrLn line
  pure code

end Lara.Process.InquiryRunMain

def main (args : List String) : IO UInt32 := Lara.Process.InquiryRunMain.main args
