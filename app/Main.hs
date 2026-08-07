-- | The @lara@ command-line driver — a thin shell over "Lara.Driver".
--
-- Contract (M3 plan, review D16 — identical to the Lean driver
-- @lean/Lara/Driver.lean@):
--
-- * @lara check \<file.sexp\>@ reads one wire check-input envelope
--   ("Lara.Wire", the N11 differential anchor), runs the real replay preflight
--   and six-stage pipeline ('Lara.Driver.runCheck'), and prints an
--   identity-bearing S-expression verdict on @stdout@.
-- * @lara check \<file.lara\>@ (M4a Task A1) parses the presentation program,
--   resolves its co-located policy file, elaborates to the checker 'Unit',
--   validates a 'CheckInput' from the real source metadata, then runs the same
--   'Lara.Driver.runCheck' path. The CLI is a thin shell, so the @.lara@
--   verdict bytes equal the in-process source construction + checker bytes.
-- * Exit codes (shared by both paths): @0@ = accept, @1@ = checker rejection
--   (a rejection whose class alone cannot say what went wrong additionally
--   explains itself with one 'Lara.Driver.runCheckLocatedReported' line on @stderr@: a
--   replay-preflight R13 'Lara.Replay.replayFailureMessage', an escalated
--   group-conflict R9 'Lara.Driver.groupConflictMessage', or a checker-side R13
--   'Lara.Driver.backendRejectionMessage' carrying the backend's own reason),
--   @2@ =
--   decode/elaborate-boundary or usage error (with a located message on
--   @stderr@ and nothing on @stdout@). For @.lara@, a program\/policy parse
--   error, a missing\/unreadable policy file, and an 'ElabError' are all
--   decode-boundary failures and share the codec error's exit @2@.
--
-- The verdict is printed with a single trailing newline via 'putStrLn' —
-- 'printSExpr' emits no newline, so both drivers' stdout is @printSExpr
-- (encodeVerdict v)@ plus one @\\n@ and differential comparison is byte equality.
module Main (main) where

import Control.Exception (IOException, evaluate, try)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)
import System.FilePath (takeDirectory, takeExtension, (</>), (<.>))
import System.IO (hPutStrLn, stderr)

import Lara.AST (PolicyId (..), programPolicy)
import Lara.Admission
  ( admissionAuditIsEmpty
  , renderAdmissionAudit
  , renderAdmissionRejection
  )
import Lara.Check (fullConfig)
import Lara.Driver (runCheckLocatedReported)
import Lara.Elaborate
  ( PreparedSource (..)
  , defeasibleSuiteSigma
  , prepareSource
  , renderSourceInvalid
  , runSourceCheck
  , sourceResultAudit
  , sourceResultDiagnostics
  , sourceResultVerdict
  )
import qualified Lara.Syntax as Syntax
import Lara.Wire
  ( Outcome (..)
  , Verdict (..)
  , WireError (..)
  , decodeCheckInputFile
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
usage = hPutStrLn stderr "usage: lara check <file.sexp|file.lara>"

-- | Dispatch on the artifact extension: a @.lara@ path runs the presentation
-- pipeline (parse + co-located policy + elaborate); everything else (including
-- @.sexp@) runs the frozen wire check-input path.
check :: FilePath -> IO ()
check file
  | takeExtension file == ".lara" = checkLara file
  | otherwise = checkSexp file

-- ---------------------------------------------------------------------------
-- The frozen @.sexp@ check-input path
-- ---------------------------------------------------------------------------

checkSexp :: FilePath -> IO ()
checkSexp file = do
  contentsOrError <- readFileEither file
  case contentsOrError of
    Left err -> do
      hPutStrLn stderr ("lara: cannot read " ++ file ++ ": " ++ show err)
      exitWith (ExitFailure 2)
    Right contents ->
      case decodeCheckInputFile contents of
        Left (WireError ctx msg) -> do
          hPutStrLn stderr ("lara: codec error at " ++ ctx ++ ": " ++ msg)
          exitWith (ExitFailure 2)
        Right input -> do
          -- One pass: the verdict and the lines explaining it come from the
          -- same decision, so stderr can never describe a different rejection
          -- than the one on stdout.
          let (verdict, _, diagnostics) = runCheckLocatedReported fullConfig input
          mapM_ (hPutStrLn stderr) diagnostics
          emitVerdict verdict

-- ---------------------------------------------------------------------------
-- The @.lara@ presentation path (M4a Task A1)
-- ---------------------------------------------------------------------------

-- | Parse a @.lara@ program, resolve + parse its co-located policy, elaborate to
-- a 'Unit', then run the shared pipeline. Every decode\/elaborate-boundary
-- failure exits @2@ with a located message on @stderr@ and nothing on @stdout@,
-- mirroring the @.sexp@ codec error; accept\/reject follow the shared verdict
-- convention.
checkLara :: FilePath -> IO ()
checkLara file = do
  progTextOrError <- readFileEither file
  case progTextOrError of
    Left err -> die2 ("lara: cannot read " ++ file ++ ": " ++ show err)
    Right progText ->
      case Syntax.parseProgram progText of
        Left pe -> die2 (locatedParseError file pe)
        Right prog -> do
          let policyPath = resolvePolicyPath file (programPolicy prog)
          polTextOrError <- readFileEither policyPath
          case polTextOrError of
            Left err -> die2 ("lara: cannot read policy " ++ policyPath ++ ": " ++ show err)
            Right polText ->
              case Syntax.parsePolicy polText of
                Left pe -> die2 (locatedParseError policyPath pe)
                Right pol ->
                  case prepareSource defeasibleSuiteSigma prog pol of
                    Left invalid -> die2 ("lara: source invalid: " ++ renderSourceInvalid invalid)
                    Right (SourceRejected rejection) -> do
                      hPutStrLn stderr ("lara: " ++ renderAdmissionRejection rejection)
                      exitWith (ExitFailure 1)
                    Right (SourceAccepted input) -> do
                      let result = runSourceCheck input
                          audit = sourceResultAudit result
                          verdict = sourceResultVerdict result
                      mapM_ (hPutStrLn stderr) (sourceResultDiagnostics result)
                      case verdictOutcome verdict of
                        Accept{}
                          | not (admissionAuditIsEmpty audit) ->
                              hPutStrLn stderr ("lara: " ++ renderAdmissionAudit audit)
                        _ -> pure ()
                      emitVerdict verdict

-- | Co-located policy resolution (D-Arch-2): read @\<policyId\>.policy.lara@ from
-- the /same directory/ as the artifact. E.g. @examples\/A-…​.lara@ declaring
-- @policy empirical-v1@ resolves to @examples\/empirical-v1.policy.lara@.
resolvePolicyPath :: FilePath -> PolicyId -> FilePath
resolvePolicyPath artifact (PolicyId pid) =
  takeDirectory artifact </> pid <.> "policy" <.> "lara"

-- | Render a "Lara.Syntax".'Syntax.ParseError' as one located @stderr@ line.
locatedParseError :: FilePath -> Syntax.ParseError -> String
locatedParseError path pe =
  "lara: parse error at "
    ++ path
    ++ ":"
    ++ show (Syntax.peLine pe)
    ++ ":"
    ++ show (Syntax.peCol pe)
    ++ ": "
    ++ Syntax.peReason pe

-- ---------------------------------------------------------------------------
-- Shared helpers
-- ---------------------------------------------------------------------------

-- | Print the verdict on @stdout@ (one trailing newline) and set the exit code:
-- accept ⇒ @0@ (fall through), reject ⇒ @1@.
emitVerdict :: Verdict -> IO ()
emitVerdict verdict = do
  putStrLn (printSExpr (encodeVerdict verdict))
  case verdictOutcome verdict of
    Accept{} -> pure ()
    Reject{} -> exitWith (ExitFailure 1)

-- | Read a file, forcing the read inside 'try' so an IO failure is caught here.
readFileEither :: FilePath -> IO (Either IOException String)
readFileEither file = try $ do
  contents <- readFile file
  _ <- evaluate (length contents)
  pure contents

-- | Emit a located message on @stderr@ and exit @2@ (the decode\/boundary code).
die2 :: String -> IO ()
die2 msg = hPutStrLn stderr msg >> exitWith (ExitFailure 2)
