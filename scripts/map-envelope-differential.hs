-- | Haskell half of the envelope's __cross-decoder differential__.
--
-- The committed malformed corpus asserts, on each side separately, that a
-- hand-written envelope is refused: @test\/MapSpec.hs@ runs the Haskell decoder
-- in process, and @scripts\/check-map-conformance.sh@ requires the Lean driver
-- to exit 2. Nothing ran the __same bytes through both decoders and compared
-- the decision__. That is exactly the divergence class the corpus exists to
-- catch — one decoder accepting what the other refuses — and a hand-curated
-- refusal list cannot catch it, because a divergence in the middle of the
-- language stays invisible until someone happens to write that fixture. This
-- PR's own empty-member-path bug was found by hand for that reason, and
-- fuzzing did not find it either.
--
-- So this program mechanically derives mutants of the committed envelopes,
-- decides each with the Haskell decoder, and writes the bytes and the decision
-- to a directory. @check-map-conformance.sh@ then runs the Lean driver over the
-- same files and fails on any disagreement.
--
-- __Deterministic, with no RNG.__ The mutation set is a fixed function of the
-- input bytes, so two runs on one tree produce the same corpus and a
-- disagreement is reproducible from the file the script names.
--
-- __The corpus must contain accepted envelopes, not only refused ones.__ A
-- differential over refusals alone is satisfied by two decoders that refuse
-- everything. The unmutated envelopes are included for that reason, and the
-- run fails if the accepted count is zero.
--
-- Usage:  map-envelope-differential OUTDIR ENVELOPE...
-- Output: @OUTDIR\/NNNN.sexp@ per case, and @OUTDIR\/decisions.tsv@ carrying one
--         @NNNN.sexp \<TAB\> accept|reject \<TAB\> label@ row per case.
-- Exit:   0 on success; 2 on a usage error, an unreadable envelope, or a corpus
--         that has silently shrunk.
module Main (main) where

import Control.Monad (unless)
import Data.Char (isDigit)
import qualified Data.Set as Set
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.Exit (exitWith, ExitCode (..))
import System.FilePath ((</>))
import System.IO (hPutStrLn, stderr)
import Text.Printf (printf)

import Lara.Map.Driver (decodeMapCheckInputText)

-- | The smallest corpus this program is allowed to produce.
--
-- A guard against silent shrinkage: if the tokenizer or the mutation set
-- regresses, the differential would keep exiting 0 over a handful of cases
-- while reading like full coverage. The committed envelopes yield thousands, so
-- this bound is far below the real figure and only fires on a real regression.
minimumCases :: Int
minimumCases = 200

main :: IO ()
main = do
  args <- getArgs
  case args of
    (outDir : envelopes@(_ : _)) -> run outDir envelopes
    _ -> die "usage: map-envelope-differential OUTDIR ENVELOPE..."

die :: String -> IO a
die message = do
  hPutStrLn stderr ("map-envelope-differential: " ++ message)
  exitWith (ExitFailure 2)

run :: FilePath -> [FilePath] -> IO ()
run outDir envelopes = do
  createDirectoryIfMissing True outDir
  sources <- mapM readFile envelopes
  let cases = dedupeByText (concat (zipWith mutantsOf envelopes sources))
      decided = [(label, text, decide text) | (label, text) <- cases]
      accepted = length [() | (_, _, Accept) <- decided]
  unless (length decided >= minimumCases) $
    die
      ( "only " ++ show (length decided) ++ " cases (want at least "
          ++ show minimumCases ++ "); the mutation set has shrunk and this"
          ++ " differential is weaker than it reads"
      )
  unless (accepted > 0) $
    die
      ( "no case is ACCEPTED by the Haskell decoder; a differential over"
          ++ " refusals alone is satisfied by two decoders that refuse everything"
      )
  rows <- mapM (emit outDir) (zip [0 :: Int ..] decided)
  writeFile (outDir </> "decisions.tsv") (unlines rows)
  printf
    "%d differential cases (%d accepted, %d refused)\n"
    (length rows)
    accepted
    (length rows - accepted)

data Decision = Accept | Reject
  deriving (Eq)

decisionText :: Decision -> String
decisionText Accept = "accept"
decisionText Reject = "reject"

decide :: String -> Decision
decide = either (const Reject) (const Accept) . decodeMapCheckInputText

-- | Distinct bytes only, first label wins. Different edits often coincide
-- (dropping the token after a repeat, say), and a duplicate case is a duplicate
-- Lean invocation for no extra evidence.
--
-- Through a 'Set', not @nub@: these are tens of kilobytes each, and the
-- quadratic version spent longer deduplicating than both decoders spend
-- deciding.
dedupeByText :: [(String, String)] -> [(String, String)]
dedupeByText = go Set.empty
  where
    go _ [] = []
    go seen ((label, text) : rest)
      | Set.member text seen = go seen rest
      | otherwise = (label, text) : go (Set.insert text seen) rest

emit :: FilePath -> (Int, (String, String, Decision)) -> IO String
emit outDir (index, (label, text, decision)) = do
  let name = printf "%04d.sexp" index :: String
  writeFile (outDir </> name) text
  pure (name ++ "\t" ++ decisionText decision ++ "\t" ++ label)

-- ---------------------------------------------------------------------------
-- Mutation
-- ---------------------------------------------------------------------------

-- | What can be done to one token.
--
-- Chosen so the corpus reaches the __structural__ boundaries where two
-- independently written decoders are most likely to part company: arity (a
-- dropped or repeated token), vocabulary (a keyword swapped for another of the
-- same shape), numeric syntax (a leading zero, a sign, a value past any
-- plausible arity), and emptiness.
data Edit
  = -- | delete the token: every enclosing form loses one field
    DropToken
  | -- | repeat it: every enclosing form gains one
    RepeatToken
  | -- | replace an atom with the empty quoted string
    EmptyToken
  | -- | @0@ becomes @00@, exercising leading-zero handling
    LeadingZero
  | -- | @0@ becomes @-0@, exercising sign handling
    SignedNumber
  | -- | @0@ becomes @999999@, past any real arity
    LargeNumber
  deriving (Eq, Show)

editName :: Edit -> String
editName edit = case edit of
  DropToken -> "drop"
  RepeatToken -> "repeat"
  EmptyToken -> "empty"
  LeadingZero -> "leading-zero"
  SignedNumber -> "signed"
  LargeNumber -> "large"

-- | The edits worth applying to a given token.
-- | A bare decimal token, the population the numeric edits apply to.
isNumericToken :: String -> Bool
isNumericToken token = not (null token) && all isDigit token

editsFor :: String -> [Edit]
editsFor token =
  [DropToken, RepeatToken]
    ++ [EmptyToken | not (isParen token)]
    ++ (if isNumber token then [LeadingZero, SignedNumber, LargeNumber] else [])
  where
    isParen t = t == "(" || t == ")"
    isNumber = isNumericToken

applyEdit :: Edit -> String -> [String]
applyEdit edit token = case edit of
  DropToken -> []
  RepeatToken -> [token, token]
  EmptyToken -> ["\"\""]
  LeadingZero -> ["0" ++ token]
  SignedNumber -> ["-" ++ token]
  LargeNumber -> ["999999"]

-- | How many token positions of each envelope to mutate.
--
-- A committed envelope is several thousand tokens, and mutating every one gives
-- tens of thousands of multi-kilobyte files — minutes of wall clock and a Lean
-- process per case, for a corpus whose marginal case says nothing new. The
-- positions are taken by an even __stride__ rather than from a prefix, so the
-- sample still reaches every section of the envelope: the policy and backends
-- near the front, the units in the middle, the alignments at the end. A prefix
-- would have tested the manifest header a thousand times and the alignment
-- grammar never.
positionsPerEnvelope :: Int
positionsPerEnvelope = 120

-- | Mutants of one envelope, labelled by where and how each was made.
--
-- The label is what a disagreement report names, so it identifies the edit
-- rather than merely numbering it.
mutantsOf :: FilePath -> String -> [(String, String)]
mutantsOf source text =
  (source ++ ":unmutated", text)
    : [ (source ++ ":" ++ show position ++ ":" ++ editName edit, rebuilt)
      | position <- sampled
      , let token = tokens !! position
      , edit <- editsFor token
      , let rebuilt = rebuild position edit token
      , rebuilt /= text
      ]
  where
    tokens = tokenize text
    count = length tokens
    stride = max 1 (count `div` positionsPerEnvelope)
    -- Every NUMERIC position, plus an even stride over the rest.
    --
    -- The stride alone is a blind sample, and the numbers are exactly where two
    -- hand-written decoders most easily part company: leading zeros, signs, and
    -- out-of-range indices are each a separate decision that a second
    -- implementation can spell differently. There are few enough numeric tokens
    -- in an envelope to take all of them, and taking them is what makes this
    -- corpus catch a relaxed natural-number parser. (Checked: with the leading
    -- zero rejection removed from mapNatText, the stride-only sample still
    -- passed and this sample fails.)
    numeric = [position | (position, token) <- zip [0 ..] tokens, isNumericToken token]
    sampled = Set.toAscList (Set.fromList (numeric ++ [0, stride .. count - 1]))
    rebuild position edit token =
      untokenize
        (take position tokens ++ applyEdit edit token ++ drop (position + 1) tokens)

-- | S-expression tokens: parens, quoted strings (which may contain spaces and
-- escapes), and bare atoms.
--
-- Splitting on whitespace would tear the @rationale@ strings apart and produce
-- mutants that are only ever parse errors, which is the one failure mode both
-- decoders agree on trivially and so the least informative corpus available.
tokenize :: String -> [String]
tokenize = go
  where
    go [] = []
    go (c : cs)
      | c `elem` " \t\n\r" = go cs
      | c == '(' || c == ')' = [c] : go cs
      | c == '"' = let (literal, rest) = quoted cs in ('"' : literal) : go rest
      | otherwise = let (atom, rest) = break isBoundary (c : cs) in atom : go rest

    isBoundary c = c `elem` " \t\n\r()\""

    -- Consume through the closing quote, honouring backslash escapes.
    quoted [] = ("", [])
    quoted ('\\' : e : rest) = let (more, out) = quoted rest in ('\\' : e : more, out)
    quoted ('"' : rest) = ("\"", rest)
    quoted (c : rest) = let (more, out) = quoted rest in (c : more, out)

-- | Print tokens back with a single space between them.
--
-- The result is not byte-identical to the input — the committed envelopes have
-- their own spacing — which is fine and deliberate: what this corpus compares
-- is the two decoders' /decisions/, and a decoder that disagreed about
-- whitespace would be a divergence worth reporting rather than one to hide.
untokenize :: [String] -> String
untokenize = unwords
