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
-- * @lara deps \<file.sexp|file.lara\>@ (\#204) runs the same two doors and
--   prints the /accepted/ unit's certificate dependency report on @stdout@
--   instead of its verdict: one @argument \<id\>@ header per checked argument,
--   then that argument's dependency lines in
--   "Lara.Strict.Deps".@encodeCertDeps@ canonical order. This is the shipped
--   consumer of the accounting Lean's @cert_steps_accounted@ and
--   @certDeps_eq_union@ prove. It is a __separate subcommand precisely so that
--   @lara check@'s @stdout@ does not move__: those bytes are the N11
--   differential anchor against @lean\/Lara\/Driver.lean@ and are pinned by the
--   corpus goldens, and the Lean driver has no report encoder. A rejected input
--   prints nothing on @stdout@, one line on @stderr@, and exits @1@.
--
-- * Exit codes (shared by both paths): @0@ = accept, @1@ = checker rejection
--   (a rejection whose class alone cannot say what went wrong additionally
--   explains itself with one 'Lara.Driver.runCheckLocatedReported' line on @stderr@: a
--   replay-preflight R13 'Lara.Replay.replayFailureMessage', an escalated
--   group-conflict R9 'Lara.Driver.groupConflictMessage', or a checker-side R13
--   'Lara.Driver.backendRejectionMessage' carrying the backend's own reason;
--   on the @.lara@ door only, a checker-side R13 against an argument a
--   @comparison@ block generated additionally gets one surface-context line
--   /above/ that kernel line, naming the block and its @result@\/@baseline@\/
--   measurand — 'Lara.Elaborate.sourceResultAuthorDiagnostics'),
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
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)
import System.FilePath (takeDirectory, takeExtension, (</>), (<.>))
import System.IO (hPutStrLn, stderr)

import Lara.AST (ArgId, PolicyId (..), programPolicy)
import Lara.Admission
  ( admissionAuditIsEmpty
  , renderAdmissionAudit
  , renderAdmissionRejection
  )
import Lara.Check (fullConfig)
import Lara.Driver (renderCertDeps, runCheckDeps, runCheckLocatedReported)
import Lara.Elaborate
  ( PreparedSource (..)
  , prepareSource
  , renderSourceInvalid
  , runSourceCheck
  , sourceResultAudit
  , sourceResultAuthorDiagnostics
  , sourceResultCertDeps
  , sourceResultVerdict
  )
import Lara.Strict.Deps (CertDep)
import qualified Lara.Syntax as Syntax
import Lara.Wire
  ( Outcome (..)
  , Verdict (..)
  , WireError (..)
  , decodeCheckInputFileBS
  , encodeVerdict
  , printSExpr
  )

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["check", file] -> check file
    ["deps", file] -> deps file
    _ -> usage >> exitWith (ExitFailure 2)

usage :: IO ()
usage = hPutStrLn stderr "usage: lara (check|deps) <file.sexp|file.lara>"

-- | Dispatch on the artifact extension: a @.lara@ path runs the presentation
-- pipeline (parse + co-located policy + elaborate); everything else (including
-- @.sexp@) runs the frozen wire check-input path.
check :: FilePath -> IO ()
check file
  | takeExtension file == ".lara" = checkLara file
  | otherwise = checkSexp file

-- | @lara deps@ (#204): the same two doors, reporting the accepted unit's
-- certificate dependencies instead of its verdict.
deps :: FilePath -> IO ()
deps file
  | takeExtension file == ".lara" = depsLara file
  | otherwise = depsSexp file

-- ---------------------------------------------------------------------------
-- The frozen @.sexp@ check-input path
-- ---------------------------------------------------------------------------

checkSexp :: FilePath -> IO ()
checkSexp file = do
  contentsOrError <- readFileBytesEither file
  case contentsOrError of
    Left err -> do
      hPutStrLn stderr ("lara: cannot read " ++ file ++ ": " ++ show err)
      exitWith (ExitFailure 2)
    Right contents ->
      case decodeCheckInputFileBS contents of
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
  prepared <- loadSource file
  case prepared of
    SourceRejected rejection -> do
      hPutStrLn stderr ("lara: " ++ renderAdmissionRejection rejection)
      exitWith (ExitFailure 1)
    SourceAccepted input -> do
      let result = runSourceCheck input
          audit = sourceResultAudit result
          verdict = sourceResultVerdict result
      -- The author-facing layer (plan D5): the same kernel lines the raw door
      -- prints, with a surface-context line prepended when the rejected
      -- argument is one a @comparison@ block generated. Additive only — the
      -- kernel line, the verdict, and the exit code are unchanged, and the raw
      -- @.sexp@ door above does not go through here.
      mapM_ (hPutStrLn stderr) (sourceResultAuthorDiagnostics result)
      case verdictOutcome verdict of
        Accept{}
          | not (admissionAuditIsEmpty audit) ->
              hPutStrLn stderr ("lara: " ++ renderAdmissionAudit audit)
        _ -> pure ()
      emitVerdict verdict

-- | Parse a @.lara@ program and its co-located policy and validate the source,
-- or exit @2@ with one located @stderr@ line. Shared by @lara check@ and
-- @lara deps@ so the two doors cannot drift on which inputs are
-- decode-boundary failures: a program\/policy parse error, a missing or
-- unreadable policy file, and a 'Lara.Elaborate.SourceInvalid' are all exit
-- @2@, in this order.
loadSource :: FilePath -> IO PreparedSource
loadSource file = do
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
                  case prepareSource prog pol of
                    Left invalid -> die2 ("lara: source invalid: " ++ renderSourceInvalid invalid)
                    Right prepared -> pure prepared

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
-- The @lara deps@ report path (#204)
-- ---------------------------------------------------------------------------

-- | The raw @.sexp@ door's report: decode, run the pipeline, and print the
-- accepted unit's certificate dependency report on @stdout@.
depsSexp :: FilePath -> IO ()
depsSexp file = do
  contentsOrError <- readFileBytesEither file
  case contentsOrError of
    Left err -> die2 ("lara: cannot read " ++ file ++ ": " ++ show err)
    Right contents ->
      case decodeCheckInputFileBS contents of
        Left (WireError ctx msg) -> die2 ("lara: codec error at " ++ ctx ++ ": " ++ msg)
        Right input -> do
          let (verdict, report) = runCheckDeps fullConfig input
          emitReport file (acceptedReport (verdictOutcome verdict) report)

-- | The @.lara@ door's report, over the source-boundary prune. A source stopped
-- by policy admission never reaches the checker, so it has no report and is
-- reported as a rejection here — the same exit @1@ 'checkLara' gives it.
depsLara :: FilePath -> IO ()
depsLara file = do
  prepared <- loadSource file
  case prepared of
    SourceRejected _ -> emitReport file Nothing
    SourceAccepted input -> do
      let result = runSourceCheck input
      emitReport
        file
        ( acceptedReport
            (verdictOutcome (sourceResultVerdict result))
            (sourceResultCertDeps result)
        )

-- | Print a report and set the exit code, on the shared @lara@ convention: an
-- accepted unit prints its report on @stdout@ and exits @0@ (an accepted unit
-- whose arguments cite nothing prints nothing, which is a report, not an
-- error); a rejected one prints /nothing/ on @stdout@, one line on @stderr@,
-- and exits @1@.
--
-- __Why a rejection prints no report rather than a partial one.__ The
-- accounting @certDeps@ mechanizes ranges over checked terms; on a term the
-- checker refused, the collector would still walk past the refused node and
-- emit whatever the accepted steps beneath it cited. That output would look
-- like an audit of evidence the verdict does not rest on. The reason lives with
-- @lara check@, which is the command that decides and explains rejections, so
-- this door points at it instead of duplicating its diagnostic precedence.
emitReport :: FilePath -> Maybe [(ArgId, [CertDep])] -> IO ()
emitReport file report = case report of
  Just deps -> putStr (renderCertDeps deps)
  Nothing -> do
    hPutStrLn
      stderr
      ("lara: " ++ file ++ " was rejected; no dependency report (run 'lara check' for the reason)")
    exitWith (ExitFailure 1)

-- | A report exists exactly when the verdict accepts: 'Nothing' pairs a
-- rejection with the absence of a report, so no caller can pass a rejecting
-- outcome and a non-empty report together.
acceptedReport :: Outcome -> [(ArgId, [CertDep])] -> Maybe [(ArgId, [CertDep])]
acceptedReport outcome report = case outcome of
  Accept{} -> Just report
  Reject{} -> Nothing

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

-- | Read a file as raw bytes, for the @.sexp@ codec path. Unlike
-- 'readFileEither' this does no locale decoding, so invalid UTF-8 reaches the
-- wire parser and becomes a located R14 codec error (exit @2@) instead of an
-- IO-level read failure — the same outcome class, through the codec channel.
readFileBytesEither :: FilePath -> IO (Either IOException ByteString)
readFileBytesEither file = try $ do
  contents <- B.readFile file
  _ <- evaluate (B.length contents)
  pure contents

-- | Emit a located message on @stderr@ and exit @2@ (the decode\/boundary code).
--
-- The return type is @IO a@, not @IO ()@: this never returns, so it is usable
-- as an arm of a @case@ whose other arms produce a value ('loadSource').
die2 :: String -> IO a
die2 msg = hPutStrLn stderr msg >> exitWith (ExitFailure 2)
