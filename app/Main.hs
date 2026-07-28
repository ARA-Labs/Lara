-- | The @lara@ command-line driver — a thin shell over "Lara.Driver".
--
-- Contract (M3 plan, review D16 — identical to the Lean driver
-- @lean/Lara/Driver.lean@):
--
-- * @lara check \<file.sexp\>@ reads one wire unit ("Lara.Wire", the N11
--   differential anchor), runs the real six-stage pipeline
--   ('Lara.Driver.runUnit'), and prints an S-expression verdict on @stdout@
--   through the same codec the Lean driver uses, byte-identical.
-- * Exit codes: @0@ = accept, @1@ = checker rejection, @2@ = codec or usage
--   error (with a located message on @stderr@).
--
-- The verdict is printed with a single trailing newline via 'putStrLn' —
-- 'printSExpr' emits no newline, so both drivers' stdout is @printSExpr
-- (encodeVerdict v)@ plus one @\\n@ and differential comparison is byte equality.
module Main (main) where

import Control.Exception (IOException, evaluate, try)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)
import System.IO (hPutStrLn, stderr)

import Lara.Driver (runUnit)
import Lara.Wire
  ( Verdict (..)
  , WireError (..)
  , decodeUnitFile
  , encodeVerdict
  , printSExpr
  )

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["check", file] -> check file
    _ -> usage >> exitWith (ExitFailure 2)

usage :: IO ()
usage = hPutStrLn stderr "usage: lara check <file.sexp>"

check :: FilePath -> IO ()
check file = do
  contentsOrError <- try $ do
    contents <- readFile file
    _ <- evaluate (length contents) -- force the read inside 'try'
    pure contents
  case contentsOrError of
    Left err -> do
      hPutStrLn stderr ("lara: cannot read " ++ file ++ ": " ++ show (err :: IOException))
      exitWith (ExitFailure 2)
    Right contents ->
      case decodeUnitFile contents of
        Left (WireError ctx msg) -> do
          hPutStrLn stderr ("lara: codec error at " ++ ctx ++ ": " ++ msg)
          exitWith (ExitFailure 2)
        Right unit -> do
          let verdict = runUnit unit
          putStrLn (printSExpr (encodeVerdict verdict))
          case verdict of
            VAccept{} -> pure ()
            VReject{} -> exitWith (ExitFailure 1)
