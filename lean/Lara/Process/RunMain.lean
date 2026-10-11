/-
The Lean reference executable for `process-input 1`: `process-run <file.sexp>`.

It reads one document and prints one S-expression on stdout: a
`process-result 1` exits 0, and a `process-error 1` exits with the code
`Error.exitCode` fixes (1 for `unsupported` and `limit-exceeded`, 2 for every
other refusal). Stderr stays empty. The Haskell door that implements the same contract
is later work (issue #22, P6); until then `make process-theory` checks this
runner against the committed goldens in `fixtures/process/run/`.
-/
import Lara.Process.Run

namespace Lara.Process.RunMain
open Lara.Process.Wire

def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let (sx, code) ← match args with
    | [file] =>
      try pure (process (← IO.FS.readFile file))
      catch e => let err : Error := ⟨.io, e.toString⟩; pure (encodeError err, err.exitCode)
    | _ =>
      let err : Error := ⟨.usage, "usage: process-run FILE"⟩
      pure (encodeError err, err.exitCode)
  out.putStrLn (Lara.Driver.printSx sx)
  pure code

end Lara.Process.RunMain

def main (args : List String) : IO UInt32 := Lara.Process.RunMain.main args
