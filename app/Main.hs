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
-- * @lara check \<file.laramap\>@ (\#303) reads a multi-artifact /map/
--   manifest, rereads and rechecks every member it names, links them into one
--   unit, checks that unit, evaluates the declared alignments, and prints one
--   @map-verdict\@1@ composite S-expression on @stdout@
--   ('Lara.Map.Driver.runMap'). The @(scope map)@ marker leads those bytes, so
--   no consumer can mistake them for a solo @(verdict …)@. A map failure
--   prints /nothing/ on @stdout@ and exactly one line on @stderr@
--   ('Lara.Map.Types.renderMapError'), and its exit code is the same 2-or-1
--   split the other doors use, decided in one place
--   ('Lara.Map.Types.mapErrorExitCode'): an ill-formed map exits @2@, a map
--   that was understood and rejected exits @1@.
-- * @lara map-input \<file.laramap\>@ (\#303) prints the map's
--   @map-check-input\@1@ __cross-driver parity envelope__ on @stdout@ instead
--   of its verdict: the same checked-boundary members the verdict was computed
--   from, spelled so that @lean\/Lara\/Map\/Driver.lean@ can reconstruct the
--   linking itself and its verdict can be byte-compared against this driver's
--   ('Lara.Map.Driver.mapCheckInput', @scripts\/check-map-conformance.sh@).
--   It is a __separate subcommand precisely so that @lara check@'s @stdout@
--   does not move__, for the same reason @lara deps@ is one. It stops at the
--   same stage @lara check@ does for every /boundary/ failure — the manifest,
--   the members, and the coordinate resolution — so every envelope it prints
--   is one that decodes; what it does not do is link, check, or evaluate an
--   alignment, because those are exactly the decisions the envelope exists to
--   have made twice.
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
-- * @lara pw \<run.sexp\>@ (\#322) runs a @pw-run 1@ possible-world document:
--   it loads the declared worlds through the same checker, the bridge
--   registry, and the candidate edges, then answers the modal queries and
--   source-claim comparisons ("Lara.PW.Run"). It prints one @pw-result 1@ or
--   @pw-error 1@ S-expression on @stdout@ and nothing on @stderr@, which is the
--   contract the Lean @pw-run@ reference shares byte for byte. Its exit codes
--   are listed at 'pwRun'.
-- * @lara pw-input \<run.sexp\>@ (\#327) prints the run's __derived document__
--   on @stdout@ instead of its result: the same @pw-run 1@ document with every
--   world source replaced by the envelope it yielded, inline. It exists for
--   the same reason @lara map-input@ does: a @(lara PATH)@ world is a
--   presentation program only this driver can elaborate, and the derived
--   document is what the Lean @pw-run@ reference is handed so that the two
--   can be byte-compared ('pwInput').
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
-- * Every text boundary is UTF-8 whatever the locale ('textBoundary'): the
--   command line, the paths this driver opens, the @.lara@\/@.laramap@ text it
--   reads, and the @stdout@\/@stderr@ it writes. One @.lara@ file therefore
--   names one unit under every @LC_ALL@ and on every door (\#334).
--
-- The verdict is printed with a single trailing newline via 'putStrLn' —
-- 'printSExpr' emits no newline, so both drivers' stdout is @printSExpr
-- (encodeVerdict v)@ plus one @\\n@ and differential comparison is byte equality.
--
-- * @lara check \<file\> --out \<path\>@ (\#303) sends those same bytes to
--   @path@ instead of @stdout@, through 'Lara.AtomicWrite.atomicWriteFile', so
--   a @Makefile@ rule can name a verdict file as its output ('Sink'). It is a
--   __product file, not a stdout redirect__: @path@ is replaced when and only
--   when the check __accepts__, and every nonzero exit /of the check/ leaves
--   the previous @path@ exactly as it was and behaves precisely as it does
--   without the flag — a rejected solo unit still prints its
--   @(verdict … reject …)@ on @stdout@, a refused map still prints its one
--   @stderr@ line and no verdict. A caller that wants a rejection's bytes in a
--   file uses the default form and redirects.
--
--   A failed /write/ is the one exit the flag adds, and the one case where the
--   two forms differ in more than destination: without @--out@ that same run
--   would have exited @0@ with a verdict on @stdout@. It exits @2@ instead,
--   and 'emitAccepted' has its exit code, its effect on the destination's
--   permissions, and its behaviour at a symlink.
module Main (main) where

import Control.Exception (IOException, evaluate, try)
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)
import System.FilePath (takeExtension)
import qualified GHC.Foreign
import GHC.IO.Encoding (getFileSystemEncoding, setFileSystemEncoding, setLocaleEncoding, utf8)
import System.IO (hPutStrLn, hSetEncoding, mkTextEncoding, stderr, stdout)

import Lara.AST (ArgId)
import Lara.AtomicWrite (atomicWriteFile)
import Lara.Admission
  ( admissionAuditIsEmpty
  , renderAdmissionAudit
  , renderAdmissionRejection
  )
import Lara.Check (fullConfig)
import Lara.Driver (renderCertDeps, runCheckDeps, runCheckLocatedReported)
import Lara.Elaborate
  ( PreparedSource (..)
  , runSourceCheck
  , sourceResultAudit
  , sourceResultAuthorDiagnostics
  , sourceResultCertDeps
  , sourceResultVerdict
  )
import Lara.Map.Driver
  ( encodeMapCheckInput
  , mapCheckInput
  , resolveReferences
  , runMap
  )
import Lara.Map.Load (loadMap)
import Lara.Map.Types
  ( MapBoundaryError (MBWire)
  , MapError (MapBoundary)
  , mapErrorExitCode
  , renderMapError
  )
import Lara.Map.Wire (encodeMapVerdict)
import Lara.PW.Run (PWError, deriveRunFile, encodeError, encodeOutcome, pwErrorExitCode, runPWFile)
import Lara.PW.Wire (printRun)
import Lara.Source.Load
  ( loadSource
  , loadedPrepared
  , renderSourceLoadError
  )
import Lara.Strict.Deps (CertDep)
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
  args <- textBoundary =<< getArgs
  case args of
    ["check", file] -> check file ToStdout
    ["check", file, "--out", out] -> check file (ToFile out)
    ["deps", file] -> deps file
    ["map-input", file] -> mapInput file
    ["pw", file] -> pwRun file
    ["pw-input", file] -> pwInput file
    _ -> usage >> exitWith (ExitFailure 2)

usage :: IO ()
usage = do
  hPutStrLn
    stderr
    "usage: lara (check|deps|map-input) <file.sexp|file.lara|file.laramap>"
  hPutStrLn
    stderr
    "       lara check <file> --out <path>   (write the accepted verdict to <path>)"
  hPutStrLn
    stderr
    "       lara pw <run.sexp>               (run a pw-run 1 possible-world document)"
  hPutStrLn
    stderr
    "       lara pw-input <run.sexp>         (print the run with every world source inline)"

-- | Dispatch on the artifact extension: a @.laramap@ path runs the map
-- pipeline (#303), a @.lara@ path the presentation pipeline (parse +
-- co-located policy + elaborate); everything else (including @.sexp@) runs the
-- frozen wire check-input path.
--
-- The @.laramap@ arm is /explicit/ and sits first, but the fall-through arm is
-- unchanged and is what keeps every legacy and unknown extension on the wire
-- door: a @.json@, a @.txt@ or an extensionless file still reaches 'checkSexp'
-- and is decided there — an unreadable path as a read failure, readable bytes
-- as a located codec error, exit @2@ either way — exactly as it did before the
-- map door existed.
check :: FilePath -> Sink -> IO ()
check file sink
  | takeExtension file == ".laramap" = checkMapFile file sink
  | takeExtension file == ".lara" = checkLara file sink
  | otherwise = checkSexp file sink

-- | A @.laramap@ has __no dependency report__, and gets a named refusal rather
-- than the wire door's codec error.
--
-- The refusal is not a new outcome: a map manifest is not a check-input
-- envelope, so this path already exited @2@ with nothing on @stdout@ — what
-- changes is only that the line names the map door instead of blaming the
-- manifest for failing to be a @check-input\@1@. The report itself is defined
-- per /accepted unit/ and a map is a set of them, so what a map's report would
-- even mean is an open question this increment deliberately does not answer.
depsMap :: FilePath -> IO ()
depsMap file =
  die2
    ( "lara: "
        ++ file
        ++ " is a map manifest; there is no dependency report for a map"
        ++ " (run 'lara check' on it, or 'lara deps' on one of its members)"
    )

-- | @lara deps@ (#204): the same two doors, reporting the accepted unit's
-- certificate dependencies instead of its verdict — plus a third arm that
-- declines, because a map has no such report ('depsMap').
deps :: FilePath -> IO ()
deps file
  | takeExtension file == ".laramap" = depsMap file
  | takeExtension file == ".lara" = depsLara file
  | otherwise = depsSexp file

-- ---------------------------------------------------------------------------
-- The frozen @.sexp@ check-input path
-- ---------------------------------------------------------------------------

checkSexp :: FilePath -> Sink -> IO ()
checkSexp file sink = do
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
          emitVerdict sink verdict

-- ---------------------------------------------------------------------------
-- The @.lara@ presentation path (M4a Task A1)
-- ---------------------------------------------------------------------------

-- | Parse a @.lara@ program, resolve + parse its co-located policy, elaborate to
-- a 'Unit', then run the shared pipeline. Every decode\/elaborate-boundary
-- failure exits @2@ with a located message on @stderr@ and nothing on @stdout@,
-- mirroring the @.sexp@ codec error; accept\/reject follow the shared verdict
-- convention.
checkLara :: FilePath -> Sink -> IO ()
checkLara file sink = do
  prepared <- loadPrepared file
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
      emitVerdict sink verdict

-- | Parse a @.lara@ program and its co-located policy and validate the source,
-- or exit @2@ with one located @stderr@ line. Shared by @lara check@ and
-- @lara deps@ so the two doors cannot drift on which inputs are
-- decode-boundary failures: a program\/policy parse error, a missing or
-- unreadable policy file, and a 'Lara.Elaborate.SourceInvalid' are all exit
-- @2@, in this order.
--
-- The four steps themselves live in "Lara.Source.Load", which the map loader
-- shares; what stays here is the CLI shell around them — the @lara: @ prefix,
-- the @stderr@ channel, and the exit code. 'renderSourceLoadError' carries no
-- prefix of its own, so these bytes are exactly what they were when the steps
-- lived in this file.
loadPrepared :: FilePath -> IO PreparedSource
loadPrepared file = do
  loaded <- loadSource file
  case loaded of
    Left err -> die2 ("lara: " ++ renderSourceLoadError err)
    Right source -> pure (loadedPrepared source)

-- ---------------------------------------------------------------------------
-- The @.laramap@ multi-artifact map path (#303)
-- ---------------------------------------------------------------------------

-- | Run a map and print its composite verdict.
--
-- The whole operation lives in 'Lara.Map.Driver.runMap'; what stays here is
-- the CLI shell around it, exactly as 'loadPrepared' is the shell around the
-- @.lara@ source seam: the @stderr@ channel, the single line, and the exit
-- code. The 2-or-1 split is not decided here either — 'mapErrorExitCode' is
-- the one place it lives, so this door cannot disagree with an in-process
-- caller about whether a given map was ill-formed or rejected.
--
-- One 'hPutStrLn' is the whole diagnostic and @stdout@ stays empty:
-- 'renderMapError' is the single place a map's lines live, and it folds the
-- newlines out of the free-text payloads it carries from outside (a codec
-- context and message, a filesystem error, a member's own exit-2 text, an
-- admission-audit summary, a link-boundary reason).
checkMapFile :: FilePath -> Sink -> IO ()
checkMapFile file sink = do
  outcome <- runMap file
  case outcome of
    Left err -> do
      hPutStrLn stderr ("lara: " ++ renderMapError err)
      exitWith (ExitFailure (mapErrorExitCode err))
    Right verdict -> emitAccepted sink (printSExpr (encodeMapVerdict verdict))

-- | @lara map-input@ (#303): print the map's cross-driver parity envelope.
--
-- Stops where the /boundary/ stages stop and no later: the manifest, the
-- members, and coordinate resolution all run, so an envelope that is printed
-- is one that decodes, while linking, checking and alignment evaluation are
-- left undone because those are the decisions the envelope exists to have made
-- independently by a second implementation. A map that fails a boundary stage
-- therefore exits @2@ here with the same line @lara check@ would print, and a
-- map whose /link/ or /alignment/ is what fails still prints its envelope and
-- exits @0@ — which is the case that matters, since it is exactly the input
-- the Lean driver must be given in order to refuse it too.
mapInput :: FilePath -> IO ()
mapInput file = do
  loaded <- loadMap file
  case loaded >>= envelopeOf of
    Left err -> do
      hPutStrLn stderr ("lara: " ++ renderMapError err)
      exitWith (ExitFailure (mapErrorExitCode err))
    Right input -> putStrLn (printSExpr (encodeMapCheckInput input))
  where
    -- Resolve first, so an unresolvable alignment gets its own located map
    -- diagnostic (MBUnknownAlias, MBUnknownClaim, MBCoordinateOutOfRange)
    -- rather than the envelope constructor's flatter codec message. The
    -- constructor re-checks the same conditions, which is what makes this
    -- ordering a preference about the message rather than a load-bearing
    -- convention.
    envelopeOf members = do
      _ <- resolveReferences members
      case mapCheckInput members of
        Left err -> Left (MapBoundary (MBWire err))
        Right input -> Right input

-- ---------------------------------------------------------------------------
-- The @lara pw@ possible-world path (#322)
-- ---------------------------------------------------------------------------

-- | @lara pw \<run.sexp\>@: load a @pw-run 1@ document's worlds, bridges and
-- edges, answer its modal queries and comparisons, and print one
-- S-expression on @stdout@ — @pw-result 1@ or @pw-error 1@ — with nothing on
-- @stderr@. That is the contract the Lean reference @pw-run@ executable
-- implements byte for byte (@scripts\/check-pw-conformance.py@), which is why
-- a refusal is a structured envelope on @stdout@ rather than this CLI's usual
-- @stderr@ line.
--
-- Exit codes keep the shared 2-or-1 split: @0@ for a completed run (a false
-- modal answer or an incomparable comparison is a result), @2@ when the run
-- file cannot be read or decoded, @1@ when a decoded run is refused — a world
-- the checker rejects, a bridge that does not load, an edge or comparison
-- that does not resolve, or a query that does not elaborate.
--
-- Every text boundary was switched to UTF-8 before this ran ('textBoundary'),
-- which is what lets the Lean reference use UTF-8 for all of them whatever the
-- locale. That boundary is now the whole CLI's rather than these two doors'
-- (\#334); the PW gate's locale reruns are still the case that exercises it
-- against a second implementation.
pwRun :: FilePath -> IO ()
pwRun arg = do
  result <- runPWFile arg
  case result of
    Right outcome -> putStrLn (printSExpr (encodeOutcome outcome))
    Left err -> pwRefuse err

-- | @lara pw-input \<run.sexp\>@ (#327): print the derived document.
--
-- Stops where the __sources__ stop and no later: every world's source is read
-- — a @lara@ source elaborated — and the first world without an envelope is
-- reported exactly as @lara pw@ would report it, a @world-input@ envelope on
-- @stdout@ at exit @1@; an unreadable or undecodable run file is the same
-- @io@ or @wire@ envelope at exit @2@. Worlds are not checked and nothing
-- after them runs, because those are the decisions the derived document exists
-- to have made twice. A document this prints is therefore one both runtimes
-- read, and @scripts\/check-pw-conformance.py@ requires @pw-run@ on it and
-- @lara pw@ on the original to agree.
--
-- One run file makes the two doors report different faults, and it is one
-- @lara pw@ refuses either way: a world whose ID repeats an earlier one and
-- whose source cannot be read is @duplicate-world@ from @lara pw@, which tests
-- the ID first, and @world-input@ from here, which reads every source before
-- it stops. See 'Lara.PW.Run.deriveRunFile'.
pwInput :: FilePath -> IO ()
pwInput arg = do
  result <- deriveRunFile arg
  case result of
    Right doc -> putStrLn (printRun doc)
    Left err -> pwRefuse err

-- | A PW door's refusal: the structured envelope on @stdout@, and the shared
-- 2-or-1 exit code.
pwRefuse :: PWError -> IO ()
pwRefuse err = do
  putStrLn (printSExpr (encodeError err))
  exitWith (ExitFailure (pwErrorExitCode err))

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
  prepared <- loadPrepared file
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
  Just certDeps -> putStr (renderCertDeps certDeps)
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

-- | Switch every text boundary of the CLI to UTF-8, and return the command
-- line re-decoded as UTF-8.
--
-- __Lara source text is UTF-8 by definition__ (#334): a @.lara@ file means one
-- thing, and what it means does not depend on @LC_ALL@. Nothing below this
-- line consults the environment's encoding again, so @check@, @deps@,
-- @map-input@ and the two PW doors all read the same bytes as the same
-- program. This ran only on the PW doors until #334 ('pwRun'), which is what
-- left @lara check@ refusing — or, under an 8-bit locale, silently
-- mis-decoding — a non-ASCII program those doors accepted.
--
-- Five boundaries, and __two encodings, deliberately__: @\/\/ROUNDTRIP@ where
-- bytes must survive a round trip through 'String', and __strict__ 'utf8' for
-- the one boundary where a permissive decode would change what a file means.
--
-- * @stdout@: a verdict, a report and a PW result all echo author-chosen
--   names, so under a non-UTF-8 locale the default encoder would fail on the
--   first non-ASCII identifier. The @\/\/ROUNDTRIP@ variant also writes back a
--   path byte that is not UTF-8, where a strict encoder would stop
--   mid-envelope.
-- * @stderr@: the same, for the door that explains itself there.
--   'Lara.Elaborate.sourceResultAuthorDiagnostics' names the author's own
--   claim, argument and leaf ids, and 'renderSourceLoadError' names a path, so
--   once the program is /readable/ under @LC_ALL=C@ its diagnostic must be
--   /printable/ too — otherwise a rejection that used to be a verdict becomes
--   an encoding exception. Neither handle can be left to 'setLocaleEncoding'
--   below: it does not retarget a handle that is already open, and both want
--   the @\/\/ROUNDTRIP@ variant rather than the strict encoding the locale is
--   being set to. Setting each explicitly also removes any dependence on
--   /when/ GHC first forces the handle.
-- * The command line: 'getArgs' has already decoded it with the locale's
--   encoding. Each argument is turned back into its original bytes with that
--   same encoding, which round-trips, and those bytes are decoded as UTF-8.
--   Merely switching encodings afterwards is not enough: under an 8-bit locale
--   such as ISO-8859-1, @café@ would be decoded byte by byte and then looked
--   up as @cafÃ©@.
-- * File paths: a path this driver reads out of a document — a PW world's
--   @(file PATH)@ or @(lara PATH)@, a map member, a co-located policy — is
--   decoded text, and GHC encodes a path with the file-system encoding, which
--   is ASCII under @LC_ALL=C@. It is switched to UTF-8, so every file is
--   opened by its UTF-8 bytes.
-- * @.lara@ and @.laramap@ text: "Lara.Source.Load" reads both through the
--   locale encoding. That encoding is switched to __strict__ UTF-8 — not the
--   @\/\/ROUNDTRIP@ variant the four boundaries above use — so a non-ASCII
--   program elaborates to the same unit under every locale /and/ program text
--   that is not UTF-8 is a read failure rather than a surrogate-escaped
--   decode. Strictness is the half that carries meaning: a permissive decoder
--   would silently accept a file as a program no reader could reproduce. The
--   loader's own read forces the contents inside a @try@, so the failure
--   arrives as its ordinary \"cannot read\" boundary line at exit @2@.
--
-- The @.sexp@ door is unaffected by the last point and always was: it reads
-- raw bytes ('readFileBytesEither') and decodes them itself.
textBoundary :: [String] -> IO [String]
textBoundary args = do
  utf8Roundtrip <- mkTextEncoding "UTF-8//ROUNDTRIP"
  hSetEncoding stdout utf8Roundtrip
  hSetEncoding stderr utf8Roundtrip
  localeFs <- getFileSystemEncoding
  decoded <-
    mapM
      (\arg -> GHC.Foreign.withCStringLen localeFs arg (GHC.Foreign.peekCStringLen utf8Roundtrip))
      args
  setFileSystemEncoding utf8Roundtrip
  setLocaleEncoding utf8
  pure decoded

-- | Where an /accepted/ verdict goes: @stdout@ by default, or the file named by
-- @lara check … --out \<path\>@.
--
-- Only an accepted verdict is ever routed, which is what makes this a closed
-- two-constructor choice rather than a general output redirection: no failing
-- path in this module consults a 'Sink' at all. A rejection prints its verdict
-- on @stdout@ and a boundary failure prints one line on @stderr@, each exactly
-- as it does without the flag.
data Sink = ToStdout | ToFile FilePath

-- | Emit accepted verdict bytes — one trailing newline either way, so a file
-- written here holds exactly the bytes the default form prints.
--
-- The file replacement is 'Lara.AtomicWrite.atomicWriteFile': a same-directory
-- temporary is populated and renamed over the destination, so a reader either
-- sees the old bytes or the new ones and never a partial write. A write that
-- fails — an unwritable directory, a destination that is a directory — exits
-- @2@ with one located @stderr@ line, and the previous destination is left
-- intact: this is a filesystem-boundary failure of the /command/, not a
-- statement about the artifact, so it takes the same exit code an unreadable
-- input does rather than @1@'s "understood and rejected" meaning. Nothing is
-- printed on @stdout@ in that case, because the verdict's one destination was
-- the file that could not be written.
--
-- __Two consequences of that helper that a @--out@ caller does not choose.__
-- 'Lara.AtomicWrite.atomicWriteWith' was written for /generated repository
-- artifacts/ and is reused here unchanged against an arbitrary user-named
-- path, so:
--
-- * __the destination's permissions become @0644@__, whatever they were. The
--   helper sets that mode on its temporary before the rename, so a @0600@
--   destination comes back @0644@ — a widening — and a restrictive @umask@ is
--   ignored for a freshly created one. Do not point @--out@ at a path whose
--   mode matters.
-- * __a symlink destination is replaced, not followed__. @rename(2)@ acts on
--   the link itself, so @--out@ at a symlink leaves it a regular file and the
--   link's former target untouched. This is ordinary POSIX behaviour, and it
--   is worth stating because it silently breaks a link a @make map-check
--   OUT=@ user set up on purpose.
--
-- Neither is a bug in the helper and neither is changed here: narrowing them
-- would mean either a second write path or altering a function
-- "Lara.BindingAudit" and @scripts\/claim-support.hs@ already depend on for
-- exactly the generated-artifact behaviour it has. They are recorded so the
-- contract is the whole contract.
emitAccepted :: Sink -> String -> IO ()
emitAccepted ToStdout bytes = putStrLn bytes
emitAccepted (ToFile path) bytes = do
  written <- try (atomicWriteFile path (bytes ++ "\n"))
  case written of
    Left err -> die2 ("lara: cannot write " ++ path ++ ": " ++ show (err :: IOException))
    Right () -> pure ()

-- | Emit the verdict and set the exit code: accept ⇒ @0@ (fall through, through
-- the 'Sink'), reject ⇒ @1@.
--
-- A rejection goes to @stdout@ whatever the 'Sink' says, and no file is
-- touched. That is the whole of @--out@'s "only on success" rule on this door:
-- an @--out@ file keeps its previous contents across a failed run, and the
-- rejecting bytes are still where they have always been.
emitVerdict :: Sink -> Verdict -> IO ()
emitVerdict sink verdict =
  case verdictOutcome verdict of
    Accept{} -> emitAccepted sink bytes
    Reject{} -> putStrLn bytes >> exitWith (ExitFailure 1)
  where
    bytes = printSExpr (encodeVerdict verdict)

-- | Read a file as raw bytes, for the @.sexp@ codec path. Unlike the text read
-- "Lara.Source.Load" performs on the @.lara@ door, this does no locale
-- decoding, so invalid UTF-8 reaches the wire parser and becomes a located R14
-- codec error (exit @2@) instead of an IO-level read failure — the same outcome
-- class, through the codec channel.
readFileBytesEither :: FilePath -> IO (Either IOException ByteString)
readFileBytesEither file = try $ do
  contents <- B.readFile file
  _ <- evaluate (B.length contents)
  pure contents

-- | Emit a located message on @stderr@ and exit @2@ (the decode\/boundary code).
--
-- The return type is @IO a@, not @IO ()@: this never returns, so it is usable
-- as an arm of a @case@ whose other arms produce a value ('loadPrepared').
die2 :: String -> IO a
die2 msg = hPutStrLn stderr msg >> exitWith (ExitFailure 2)
