-- | Ground-truth tests for the S-expression wire codec ("Lara.Wire", the N11
-- differential anchor; M3 plan review D11).
--
-- Three layers, mirroring the "StrictSpec" atom-key pattern:
--
--   * __hand-verified golden vectors__ — exact text ↔ value pairs for the
--     textual codec (bare/quoted atoms, escapes, comments), one full unit,
--     and verdicts;
--   * __round-trip properties__ — @parse ∘ print = id@ on 'SExpr' trees, and
--     @decode ∘ encode = Right id@ on units, checker inputs, and verdicts
--     (generators respect the documented AST invariants: 'PLit' literals
--     only, non-negative versions and indices, unique argument ids, declared
--     attack endpoints; checker inputs and verdicts carry varied canonical
--     replay identities — 0-3 sorted theory digests, occasionally non-ASCII
--     to exercise the quoted-atom path, and varied backend selections —
--     PR #44 review C10);
--   * __malformed-input rejection matrix__ — text-level errors, then one
--     field short / one field long per grammar construct, unknown tags, bad
--     naturals, and the two wire-well-formedness invariants (duplicate
--     argument ids, undeclared attack endpoints).
--
-- The two 'prop_leanDriver*' goldens are hand-authored pins of the wire
-- bytes the Lean driver (@lean/Lara/Driver.lean@) must print for the
-- corresponding fixtures; the differential harness confirms the actual Lean
-- output against them.
module WireSpec (wireSpecProps) where

import Control.Monad (forM)
import qualified Data.ByteString as B
import Data.Char (ord)
import Data.List (isPrefixOf, isSuffixOf, nub, sortBy)
import Data.Ord (comparing)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import System.Directory (doesDirectoryExist, listDirectory)
import Test.QuickCheck

import Lara.AST hiding (Reject)
import Lara.Replay
import Lara.Prop (Prop (..), Term (..))
import Lara.Sigma
  ( ConSig (..)
  , PredSig (..)
  , Sigma (..)
  , Sort (..)
  , SortName (..)
  , emptySigma
  )
import Lara.Strict (SExpr (..))
import Lara.Wire

-- ---------------------------------------------------------------------------
-- Generators
-- ---------------------------------------------------------------------------

-- | Identifiers: short bare-safe names (quoting paths are exercised by the
-- atom-payload generator below).
genIdent :: Gen String
genIdent = do
  n <- choose (1, 6)
  vectorOf n (elements (['a' .. 'z'] ++ ['0' .. '9'] ++ "-_"))

-- | Lists in recursive generator positions: a small bounded length, keeping
-- the expected branching factor below one so tree sizes stay linear in the
-- QuickCheck size parameter (an unbounded 'listOf' here is supercritical —
-- it made the suite generate multi-gigabyte units).
smallListOf :: Gen a -> Gen [a]
smallListOf g = do
  k <- choose (0, 3 :: Int)
  vectorOf k g

-- | Arbitrary atom payloads, including strings that force quoting and every
-- escaped character.
genAtomString :: Gen String
genAtomString =
  oneof
    [ genIdent
    , pure ""
    , listOf (elements (['a' .. 'd'] ++ " \t\"\\\nπ雪:;()"))
    ]

genNumString :: Gen String
genNumString =
  oneof
    [ show <$> (arbitrary :: Gen (NonNegative Int))
    , do
        sign <- elements ["", "+", "-"]
        digits <- listOf1 (elements ['0' .. '9'])
        frac <-
          oneof
            [ pure ""
            , do
                f <- listOf1 (elements ['0' .. '9'])
                pure ("." ++ f)
            ]
        pure (sign ++ digits ++ frac)
    ]

genCanonicalNat :: Gen Int
genCanonicalNat = choose (0, 9999)

genSExpr :: Gen SExpr
genSExpr = sized go
  where
    go n
      | n <= 0 = SAtom <$> genAtomString
      | otherwise =
          frequency
            [ (3, SAtom <$> genAtomString)
            , (2, SList <$> smallListOf (go (n `div` 2)))
            ]

genTerm :: Gen Term
genTerm = sized go
  where
    go n
      | n <= 0 =
          oneof
            [ TNum <$> genNumString
            , TStr <$> genAtomString
            , TCon <$> (FunSym <$> genIdent) <*> pure []
            ]
      | otherwise =
          frequency
            [ (3, go 0)
            , (1, TCon <$> (FunSym <$> genIdent) <*> smallListOf (go (n `div` 2)))
            ]

genProp :: Gen Prop
genProp = Prop <$> (Pred <$> genIdent) <*> smallListOf genTerm

genPat :: Gen Pat
genPat = sized go
  where
    go n
      | n <= 0 =
          oneof
            [ PVar . Param <$> genIdent
            , PLit . TNum <$> genNumString
            , PLit . TStr <$> genAtomString
            , PCon <$> (FunSym <$> genIdent) <*> pure []
            ]
      | otherwise =
          frequency
            [ (3, go 0)
            , (1, PCon <$> (FunSym <$> genIdent) <*> smallListOf (go (n `div` 2)))
            ]

genAtomPat :: Gen AtomPat
genAtomPat = AtomPat <$> (Pred <$> genIdent) <*> smallListOf genPat

genQuestion :: Gen Question
genQuestion =
  Question
    <$> (QuestionId <$> genIdent)
    <*> genAtomPat
    <*> elements [Mandatory, Optional]

genCertifier :: Gen CertRef
genCertifier =
  CertRef
    <$> (BackendId <$> genIdent)
    <*> genCanonicalNat
    <*> (TheoryDigest <$> genAtomString)

genRule :: Gen Rule
genRule = do
  rid <- RuleId <$> genIdent
  params <- smallListOf (Param <$> genIdent)
  mode <- elements [Strict, Defeasible]
  prems <- smallListOf genAtomPat
  concl <- genAtomPat
  at <- arbitrary
  certs <- smallListOf genCertifier
  qs <- smallListOf genQuestion
  pure
    Rule
      { ruleId = rid
      , ruleParams = params
      , ruleMode = mode
      , rulePremises = prems
      , rulePremiseLabels = []
      , ruleConclusion = concl
      , ruleAllowTrusted = at
      , ruleCertifiers = certs
      , ruleQuestions = qs
      }

genAssurance :: Gen Assurance
genAssurance =
  oneof
    [ pure AssuranceNone
    , pure AssuranceTrusted
    , AssuranceCert
        <$> ( Cert
                <$> (BackendId <$> genIdent)
                <*> genCanonicalNat
                <*> (TheoryDigest <$> genAtomString)
                <*> genSExpr
            )
    ]

genSupportTerm :: Gen SupportTerm
genSupportTerm = sized go
  where
    go n
      | n <= 0 = SLeaf . LeafId <$> genIdent
      | otherwise =
          frequency
            [ (2, SLeaf . LeafId <$> genIdent)
            , ( 3
              , SRule
                  <$> (RuleId <$> genIdent)
                  <*> smallListOf ((,) <$> (Param <$> genIdent) <*> genTerm)
                  <*> smallListOf (go (n `div` 2))
                  <*> smallListOf
                    ((,) <$> (QuestionId <$> genIdent) <*> go (n `div` 2))
                  <*> smallListOf (ObligationId <$> genIdent)
                  <*> genAssurance
              )
            ]

genPosition :: Gen Position
genPosition =
  listOf
    ( oneof
        [ StepPremise <$> genCanonicalNat
        , StepQuestion . QuestionId <$> genIdent
        ]
    )

genAttackFrom :: [ArgId] -> Gen Attack
genAttackFrom aids =
  oneof
    [ Rebut <$> elements aids <*> elements aids
    , Undercut <$> elements aids <*> elements aids <*> genPosition
    , Undermine <$> elements aids <*> elements aids <*> genPosition
    ]

-- | A signature over the same identifier pool as the rest of the generator.
-- Round-tripping does __not__ require well-sortedness (the codec never checks
-- it), so this deliberately generates arbitrary — often ill-sorted — signatures:
-- the property under test is @decode ∘ encode = id@, and restricting the
-- generator to well-sorted signatures would leave the interesting decode paths
-- unexercised.
genSigma :: Gen Sigma
genSigma = do
  sorts <- nub <$> smallListOf (SortName <$> genIdent)
  let genSort =
        if null sorts
          then elements [SortNum, SortStr]
          else oneof [elements [SortNum, SortStr], SortDecl <$> elements sorts]
  cons <-
    smallListOf
      (ConSig <$> (FunSym <$> genIdent) <*> smallListOf genSort <*> genSort)
  preds <- smallListOf (PredSig <$> (Pred <$> genIdent) <*> smallListOf genSort)
  pure (Sigma sorts cons preds)

genUnit :: Gen Unit
genUnit = do
  sigma <- genSigma
  rules <- smallListOf genRule
  contraries <- smallListOf (Contrary <$> genAtomPat <*> genAtomPat)
  exceptions <-
    smallListOf (Exception <$> (RuleId <$> genIdent) <*> genAtomPat)
  theories <-
    smallListOf ((,) <$> (TheoryDigest <$> genAtomString) <*> smallListOf genProp)
  leaves <- smallListOf ((,) <$> (LeafId <$> genIdent) <*> genProp)
  nArgs <- choose (0, 4)
  argTerms <- vectorOf nArgs (scale (`div` 2) genSupportTerm)
  let args = zip [ArgId ("a" ++ show i) | i <- [0 ..]] argTerms
  attacks <-
    if null args
      then pure []
      else smallListOf (genAttackFrom (map fst args))
  queries <- smallListOf genProp
  let leafIds = nub (map fst leaves)
  groupMembers <-
    if length leafIds < 2
      then pure []
      else choose (0, 2) >>= \n -> vectorOf n (sublistOf leafIds)
  let groups =
        [ DupGroup (GroupId ("g" ++ show i)) (nub ms)
        | (i, ms) <- zip [0 :: Int ..] groupMembers
        , length (nub ms) >= 2
        ]
  -- The conflict mode is only wire-carried when groups exist, so keep it at the
  -- canonical default otherwise (else @decode ∘ encode@ would not be identity).
  groupMode <-
    if null groups
      then pure QuarantineOnConflict
      else elements [QuarantineOnConflict, RejectOnConflict]
  pure
    Unit
      { unitSigma = sigma
      , unitRules = rules
      , unitContraries = contraries
      , unitExceptions = exceptions
      , unitTheories = theories
      , unitLeaves = leaves
      , unitArgs = args
      , unitAttacks = attacks
      , unitQueries = queries
      , unitGroups = groups
      , unitGroupMode = groupMode
      }

-- ---------------------------------------------------------------------------
-- Varied replay identities (PR #44 review C10)
-- ---------------------------------------------------------------------------

-- | Theory-digest text: mostly bare @sha256:@ digests, occasionally carrying
-- non-ASCII characters (@é@, @λ@, @π@, @雪@) to exercise the quoted-atom
-- codec path and make Unicode code-point order observable.
genTheoryDigestText :: Gen String
genTheoryDigestText =
  oneof
    [ ("sha256:" ++) <$> genIdent
    , ("sha256:" ++) <$> listOf1 (elements (['a' .. 'f'] ++ ['0' .. '9'] ++ "éλπ雪"))
    ]

-- | 0-3 distinct theory digests in canonical (strictly increasing Unicode
-- code-point) order, as 'mkReplayId' requires.
genCanonicalTheories :: Gen [TheoryDigest]
genCanonicalTheories = do
  k <- choose (0, 3)
  texts <- vectorOf k genTheoryDigestText
  pure (map TheoryDigest (sortBy (comparing (map ord)) (nub texts)))

-- | A backend selection: 0-3 (name, version) pairs with arbitrary atom
-- payloads, occasionally forcing quoted output. 'mkReplayId' does not
-- validate the selection (that is the runtime preflight's job), so any
-- strings are wire-valid here.
genBackendSelection :: Gen [(BackendId, String)]
genBackendSelection = do
  k <- choose (0, 3)
  vectorOf k ((,) <$> (BackendId <$> genBackendText) <*> genBackendText)
  where
    genBackendText = oneof [genIdent, show <$> genCanonicalNat, genAtomString]

-- | A valid replay identity with varied policy, backend selection, canonical
-- theories, and artifact digest — never the fixed golden identity.
genReplayId :: Gen ReplayId
genReplayId = do
  policy <- PolicyId <$> genAtomString
  backends <- genBackendSelection
  theories <- genCanonicalTheories
  artifact <- Digest <$> genAtomString
  case mkReplayId LaraCoreV02 policy backends theories artifact of
    Right replayId -> pure replayId
    Left _ -> discard -- unreachable: the theories are canonical by construction

-- | A full checker input with a varied replay identity (C10), built directly
-- via 'mkReplayId' / 'mkCheckInput' (not 'testCheckInput''s fixed
-- constants). The unit's theory table carries exactly the identity's digests
-- as @(digest, [])@ pairs — the 'mkCheckInput' consistency gate compares the
-- sorted theory keys only, and the generated digests are distinct and
-- canonical, so construction always succeeds.
genCheckInput :: Gen CheckInput
genCheckInput = do
  generatedUnit <- genUnit
  replayId <- genReplayId
  let unit =
        generatedUnit
          { unitTheories = [(digest, []) | digest <- replayTheories replayId]
          }
  case mkCheckInput replayId unit of
    Right input -> pure input
    Left _ -> discard -- unreachable: unit theory keys are the identity's

genLabel :: Gen Label
genLabel = elements [LIn, LOut, LUndec]

genStatus :: Gen Status
genStatus = elements [Gap, Justified, Contested, Defeated]

-- | A public status: ordinary, or @evidence-blocked@ over a conditional label
-- (spec §4.3, issue #76). Blocked entries are generated at roughly one in three
-- so the conditional section is exercised on most multi-query verdicts.
genPublicStatus :: Gen PublicStatus
genPublicStatus =
  frequency [(2, Published <$> genStatus), (1, EvidenceBlocked <$> genStatus)]

genRejection :: Gen Rejection
genRejection =
  oneof
    [ RejectClass <$> elements [minBound .. maxBound]
    , pure DuplicateRule
    , pure DuplicateArgument
    , pure IncompleteArgument
    , pure MissingConflict
    ]

genVerdict :: Gen Verdict
genVerdict = do
  replayId <- genReplayId
  oneof
    [ do
        n <- choose (0, 5)
        lbls <- zip [0 ..] <$> vectorOf n genLabel
        edges <-
          if n == 0
            then pure []
            else
              listOf
                ((,) <$> choose (0, n - 1) <*> choose (0, n - 1))
        -- Some queries are @evidence-blocked@ (spec §4.3, issue #76), so the
        -- round-trip covers the conditional section. Blockedness lives inside
        -- the status, so the generator cannot construct an inconsistent
        -- statuses/blocked pairing even by accident.
        statuses <- listOf ((,) <$> genProp <*> genPublicStatus)
        pure (Verdict replayId (Accept lbls edges statuses))
    , Verdict replayId . Reject <$> genRejection
    ]

-- ---------------------------------------------------------------------------
-- Text-codec golden vectors (hand-verified)
-- ---------------------------------------------------------------------------

-- | (input text, parsed value, canonical reprint). The reprint is the exact
-- byte string both drivers must emit for the value.
textGoldens :: [(String, SExpr, String)]
textGoldens =
  [ ("a", SAtom "a", "a")
  , ("()", SList [], "()")
  , ("(a b (c))", SList [SAtom "a", SAtom "b", SList [SAtom "c"]], "(a b (c))")
  , -- every bare-set punctuation character stays bare
    ( barePunct
    , SAtom barePunct
    , barePunct
    )
  , -- quoting is forced exactly by space, delimiters, non-ASCII, and emptiness
    ("\"sp ace\"", SAtom "sp ace", "\"sp ace\"")
  , ("\"\"", SAtom "", "\"\"")
  , ("\"uniπ雪\"", SAtom "uniπ雪", "\"uniπ雪\"")
  , ("\"(paren)\"", SAtom "(paren)", "\"(paren)\"")
  , ("\"semi;colon\"", SAtom "semi;colon", "\"semi;colon\"")
  , -- the three escapes, round-tripping exactly
    ("\"quote\\\"x\"", SAtom "quote\"x", "\"quote\\\"x\"")
  , ("\"bs\\\\x\"", SAtom "bs\\x", "\"bs\\\\x\"")
  , ("\"nl\\nx\"", SAtom "nl\nx", "\"nl\\nx\"")
  , -- comments and layout are skipped on parse, canonical on print
    ( "; leading comment\n  (a ; inner\n b)\n; trailing"
    , SList [SAtom "a", SAtom "b"]
    , "(a b)"
    )
  , ("  spaced  ", SAtom "spaced", "spaced")
  ]
  where
    barePunct = "!#$%&'*+,-./:<=>?@[]^_{|}~"

prop_textGoldenVectors :: Bool
prop_textGoldenVectors =
  and
    [ parseSExpr input == Right value
        && printSExpr value == canonical
    | (input, value, canonical) <- textGoldens
    ]

prop_textMalformedRejected :: Bool
prop_textMalformedRejected =
  and
    [ isLeft (parseSExpr "(a b") -- unclosed list
    , isLeft (parseSExpr ")") -- stray close
    , isLeft (parseSExpr "\"\\q\"") -- unknown escape
    , isLeft (parseSExpr "\"abc") -- unterminated string
    , isLeft (parseSExpr "abc\\") -- trailing backslash outside a string
    , isLeft (parseSExpr "(a) (b)") -- second top-level form
    , isLeft (parseSExpr "a b") -- second bare form
    , isLeft (parseSExpr "") -- no form at all
    , isLeft (parseSExpr " ; only a comment\n") -- no form at all
    ]
  where
    isLeft (Left _) = True
    isLeft _ = False

-- | The textual round trip on arbitrary trees (quoting included).
prop_sexprTextRoundTrip :: Property
prop_sexprTextRoundTrip =
  forAll genSExpr $ \s -> parseSExpr (printSExpr s) == Right s

-- | Reprinting is idempotent: print ∘ parse ∘ print = print.
prop_printParsePrintIdempotent :: Property
prop_printParsePrintIdempotent =
  forAll genSExpr $ \s ->
    let text = printSExpr s
     in fmap printSExpr (parseSExpr text) == Right text

-- ---------------------------------------------------------------------------
-- The reference-parser differential (#115)
-- ---------------------------------------------------------------------------
--
-- 'parseSExprBS' replaced a @String@ ([Char]) reader with one over strict
-- 'B.ByteString'. Comparing it against 'parseSExpr' would prove nothing —
-- 'parseSExpr' is now a thin wrapper over 'parseSExprBS', so the two agree by
-- construction. The oracle is therefore the /previous/ implementation, copied
-- verbatim below (only the top-level names are prefixed @ref@) from
-- @src\/Lara\/Wire.hs@ at @f7b043e@. Every accepted input, every rejected
-- input, and every error line\/column\/message must be identical.
--
-- Columns count code points in both, which is the point: the Lean reference
-- driver (@lean\/Lara\/Driver.lean@) parses a @List Char@, so a byte-counting
-- parser would silently relocate any error that follows a multi-byte character
-- on the same line.

refIsBareChar :: Char -> Bool
refIsBareChar c =
  ord c >= 0x21 && ord c <= 0x7e && c `notElem` "();\"\\"

data RefP = RefP
  { refInput :: String
  , refLine :: !Int
  , refCol :: !Int
  }

refPerr :: RefP -> String -> Either ParseError a
refPerr p msg = Left (ParseError (refLine p) (refCol p) msg)

refStep :: RefP -> RefP
refStep p = case refInput p of
  '\n' : rest -> p {refInput = rest, refLine = refLine p + 1, refCol = 1}
  _ : rest -> p {refInput = rest, refCol = refCol p + 1}
  "" -> p

refSkipSpace :: RefP -> RefP
refSkipSpace p = case refInput p of
  c : rest
    | c `elem` " \t\n\r" -> refSkipSpace (refStep p)
    | c == ';' -> refSkipSpace (refSkipComment p {refInput = rest})
  _ -> p
  where
    refSkipComment q = case refInput q of
      '\n' : _ -> q
      "" -> q
      _ -> refSkipComment (refStep q)

-- | The bound the reader enforces; kept as a literal here so the copy is
-- self-contained and a silent change to 'Lara.Wire' shows up as a divergence.
refMaxDepth :: Int
refMaxDepth = 10000

referenceParseSExpr :: String -> Either ParseError SExpr
referenceParseSExpr input = do
  let start = refSkipSpace (RefP input 1 1)
  (e, rest) <- refParseForm 0 start
  let rest' = refSkipSpace rest
  if null (refInput rest')
    then Right e
    else refPerr rest' "expected a single S-expression, found more input"

refParseForm :: Int -> RefP -> Either ParseError (SExpr, RefP)
refParseForm depth p
  | depth > refMaxDepth =
      refPerr p ("maximum S-expression nesting depth exceeded (" ++ show refMaxDepth ++ ")")
  | otherwise = case refInput p of
      '(' : _ -> parseList (refStep p) []
      '"' : _ -> parseQuoted (refStep p) []
      c : _
        | refIsBareChar c ->
            let (tok, rest) = span refIsBareChar (refInput p)
                p' = p {refInput = rest, refCol = refCol p + length tok}
             in Right (SAtom tok, p')
        | otherwise -> refPerr p ("unexpected character " ++ show c)
      "" -> refPerr p "unexpected end of input"
  where
    parseList q acc =
      let q' = refSkipSpace q
       in case refInput q' of
            ')' : _ -> Right (SList (reverse acc), refStep q')
            "" -> refPerr q' "unclosed list"
            _ -> do
              (e, q'') <- refParseForm (depth + 1) q'
              parseList q'' (e : acc)
    parseQuoted q acc = case refInput q of
      '"' : _ -> Right (SAtom (reverse acc), refStep q)
      '\\' : "" -> refPerr q "unterminated escape sequence"
      '\\' : c : rest
        | c == '"' -> parseQuoted (drop2 q rest) ('"' : acc)
        | c == '\\' -> parseQuoted (drop2 q rest) ('\\' : acc)
        | c == 'n' -> parseQuoted (drop2 q rest) ('\n' : acc)
        | otherwise -> refPerr q ("invalid escape sequence \\" ++ [c])
        where
          drop2 r s = (refStep (refStep r)){refInput = s}
      "" -> refPerr q "unterminated string literal"
      c : _ -> parseQuoted (refStep q) (c : acc)

-- | One differential comparison, on the @Right@ tree and — when it fails — on
-- the exact 'ParseError' line, column, and message.
agreesWithReference :: String -> String -> Property
agreesWithReference what txt =
  counterexample (what ++ ": input " ++ show txt) $
    parseSExprBS (TE.encodeUtf8 (T.pack txt)) === referenceParseSExpr txt

-- | (a) Every committed @.sexp@ input, read as bytes and parsed both ways.
-- This is the set the differential harness and the corpus freeze actually
-- depend on, malformed envelopes and generated codec mutants included.
prop_referenceParserCommittedInputs :: Property
prop_referenceParserCommittedInputs = once (ioProperty check)
  where
    check = do
      paths <- concat <$> mapM sexpFilesUnder ["fixtures", "corpus-units", "bundles", "examples"]
      comparisons <- forM paths $ \path -> do
        bytes <- B.readFile path
        pure $ counterexample path $ case TE.decodeUtf8' bytes of
          Left e -> counterexample ("not UTF-8: " ++ show e) (property False)
          Right txt -> parseSExprBS bytes === referenceParseSExpr (T.unpack txt)
      pure $
        counterexample
          "no committed .sexp inputs discovered"
          (length paths > 100)
          .&&. conjoin comparisons

sexpFilesUnder :: FilePath -> IO [FilePath]
sexpFilesUnder dir = do
  entries <- listDirectory dir
  fmap concat $ forM entries $ \entry -> do
    let path = dir ++ "/" ++ entry
    isDir <- doesDirectoryExist path
    if isDir
      then sexpFilesUnder path
      else pure [path | ".sexp" `isSuffixOf` path]

-- | (b) Canonical printer output for arbitrary trees.
prop_referenceParserPrinted :: Property
prop_referenceParserPrinted =
  forAll genSExpr $ \s -> agreesWithReference "printed" (printSExpr s)

-- | Corruptions of canonical wire text, so the /error/ paths are differentially
-- covered too — not just the happy path. Injected characters include the
-- delimiters, the escape character, and multi-byte code points, which is where
-- a byte-counting column would drift.
genMutatedWire :: Gen String
genMutatedWire = do
  text <- printSExpr <$> genSExpr
  let n = length text
  oneof
    [ do
        k <- choose (0, n)
        pure (take k text) -- truncation
    , do
        k <- choose (0, n)
        c <- elements "()\";\\ \n\t\rπé雪\0abc"
        pure (take k text ++ [c] ++ drop k text) -- injection
    , do
        k <- choose (0, max 0 (n - 1))
        pure (take k text ++ drop (k + 1) text) -- deletion
    , pure (text ++ " " ++ text) -- a second top-level form
    , pure ("; é\n" ++ text) -- a multi-byte comment before the form
    , do
        k <- choose (refMaxDepth - 2, refMaxDepth + 3)
        pure (replicate k '(' ++ replicate k ')') -- the depth bound, both sides
    ]

-- | (c) The mutated-input differential.
prop_referenceParserMutated :: Property
prop_referenceParserMutated =
  forAll genMutatedWire (agreesWithReference "mutated")

-- ---------------------------------------------------------------------------
-- Targeted error positions (#115 T5)
-- ---------------------------------------------------------------------------

-- | Exact @(line, column, message)@ pins. The generic differential above only
-- covers well-formed committed inputs and randomly corrupted trees; these
-- fix the cases the 'B.ByteString' rewrite could plausibly get wrong, above
-- all the multi-byte ones — a byte-counting column is off by one per
-- continuation byte, which no round-trip property would notice.
prop_parserErrorPositions :: Property
prop_parserErrorPositions =
  conjoin
    [ -- After a multi-byte character on the same line: byte columns would say 9.
      located "(a \"\233\" \\)" 1 8 ("unexpected character " ++ show '\\')
    , -- Inside a quoted atom that carries a multi-byte character.
      located "(a \"\233\\q\")" 1 6 "invalid escape sequence \\q"
    , -- End of input inside a comment carrying a multi-byte character; the
      -- ';' itself is not counted, matching the reader this replaced.
      located "; \233" 1 3 "unexpected end of input"
    , -- A raw newline inside a quoted atom advances the line and resets the
      -- column, exactly as the character-at-a-time reader did.
      located "(\"a\nb\" \\)" 2 4 ("unexpected character " ++ show '\\')
    , -- A non-ASCII code point in bare position renders as a code point, not
      -- as its leading byte (D3).
      located "\233" 1 1 ("unexpected character " ++ show '\233')
    , located "(a b" 1 5 "unclosed list"
    , located "(\"ab" 1 5 "unterminated string literal"
    , located "(\"ab\\" 1 5 "unterminated escape sequence"
    , located "(\"a\\q\")" 1 4 "invalid escape sequence \\q"
    , located "(a) (b)" 1 5 "expected a single S-expression, found more input"
    , -- The depth bound fires as a located codec error, not a stack overflow.
      located
        (replicate (refMaxDepth + 2) '(')
        1
        (refMaxDepth + 2)
        ("maximum S-expression nesting depth exceeded (" ++ show refMaxDepth ++ ")")
    ]
  where
    located txt line col msg =
      counterexample (show txt) $
        parseSExprBS (TE.encodeUtf8 (T.pack txt)) === Left (ParseError line col msg)

-- | The over-deep input reaches the R14 codec channel as a located error
-- (CLI exit 2), which is the contract @scripts\/differential.sh@ relies on to
-- tell a codec fault apart from a checker rejection.
prop_depthBoundIsCodecError :: Property
prop_depthBoundIsCodecError =
  once $
    decodeCheckInputFileBS (TE.encodeUtf8 (T.pack (replicate (refMaxDepth + 2) '(')))
      === Left
        ( WireError
            ("line 1, column " ++ show (refMaxDepth + 2))
            ("maximum S-expression nesting depth exceeded (" ++ show refMaxDepth ++ ")")
        )

-- | The bound counts nesting DEPTH, not forms seen.
--
-- Every other depth case in this repository — here, in @test\/MapSpec.hs@, and
-- in the three reader gates — is built from @(((...)))@, one element per list,
-- where depth and total-forms-seen are numerically equal. Writing the tail
-- recursion as @parseList (depth + 1)@ rather than @parseList depth@ (the slip
-- the mutual threading invites) would leave every one of those cases passing
-- while the reader refused a wide, shallow document. @docs\/spec.md@ §10.1
-- asserts the bound "bounds no expressible program"; a list with more siblings
-- than the bound, nested one level, is the case that says so. Both the shipped
-- reader and 'referenceParseSExpr' — an independent hand-copy of the same
-- threading — must admit it.
prop_depthBoundCountsDepthNotForms :: Property
prop_depthBoundCountsDepthNotForms =
  once $
    counterexample "a one-level list of more than maxDepth siblings must parse" $
      conjoin
        [ counterexample "parseSExprBS" $
            parseSExprBS (TE.encodeUtf8 (T.pack wide)) === Right expected
        , counterexample "referenceParseSExpr" $
            referenceParseSExpr wide === Right expected
        ]
  where
    n = refMaxDepth + 2
    wide = "(" ++ concat (replicate n "a ") ++ ")"
    expected = SList (replicate n (SAtom "a"))

-- | Invalid UTF-8 now reaches the parser (the @.sexp@ reader is
-- 'B.readFile'-based) and becomes a located codec error rather than an
-- IO-level read failure. Both drivers already exited 2 with empty stdout on
-- such input; this pins the Haskell side's new, better-located route to the
-- same outcome class, and pins that it fails /closed/ — no U+FFFD
-- substitution, which would accept malformed input with mangled content.
prop_invalidUtf8Rejected :: Property
prop_invalidUtf8Rejected =
  conjoin
    [ counterexample "in a quoted atom" $
        parseSExprBS (B.pack [0x28, 0x22, 0xff, 0x22, 0x29])
          === Left (ParseError 1 4 "invalid UTF-8 in string literal")
    , counterexample "in bare position" $
        parseSExprBS (B.pack [0xff])
          === Left (ParseError 1 1 "invalid UTF-8 byte sequence")
    , -- Located at the offending byte (column 3), not at the backslash that
      -- precedes it: the escape marker itself is well formed.
      counterexample "after an escape" $
        parseSExprBS (B.pack [0x22, 0x5c, 0xff])
          === Left (ParseError 1 3 "invalid UTF-8 in string literal")
    ]

-- ---------------------------------------------------------------------------
-- Unit golden vectors (hand-verified)
-- ---------------------------------------------------------------------------

-- | One full unit exercising every section, as a hand-verified text/AST pair.
goldenUnitText :: String
goldenUnitText =
  "(unit \
  \(sigma (sorts Item) (cons (con k (args Item) Item) (con c0 (args) Item)) \
  \(preds (pred p (args)) (pred q (args)))) \
  \(policy \
  \(rules \
  \(rule rmix (mode defeasible) (params) (premises) \
  \(conclusion (apat p)) \
  \(questions (question q1 (apat q) mandatory) \
  \(question q2 (apat q) optional)) \
  \(allow-trusted false) (certifiers)) \
  \(rule rcert (mode strict) (params) (premises (apat p)) \
  \(conclusion (apat q)) (questions) (allow-trusted false) \
  \(certifiers (certifier nd 1 sha256:theory-a)))) \
  \(contraries (contrary (apat p) (apat q))) \
  \(exceptions (exception rmix (apat q)))) \
  \(theories (theory sha256:theory-a (atom q))) \
  \(leaves (leaf l1 (atom p)) (leaf l2 (atom q))) \
  \(args (arg a0 (leaf l1)) \
  \(arg a1 (inst rcert (subst) (premises (leaf l1)) (discharges) (holes) \
  \(assurance (cert nd 1 sha256:theory-a (hyp 1)))))) \
  \(attacks (rebut a0 a1) (undermine a0 a1 (pos (prem 0)))) \
  \(queries (atom p) (atom q)))"

goldenUnit :: Unit
goldenUnit =
  Unit
    { unitSigma =
        Sigma
          [SortName "Item"]
          [ ConSig (FunSym "k") [SortDecl (SortName "Item")] (SortDecl (SortName "Item"))
          , ConSig (FunSym "c0") [] (SortDecl (SortName "Item"))
          ]
          [PredSig (Pred "p") [], PredSig (Pred "q") []]
    , unitRules =
        [ Rule
            { ruleId = RuleId "rmix"
            , ruleParams = []
            , ruleMode = Defeasible
            , rulePremises = []
            , rulePremiseLabels = []
            , ruleConclusion = AtomPat (Pred "p") []
            , ruleAllowTrusted = False
            , ruleCertifiers = []
            , ruleQuestions =
                [ Question (QuestionId "q1") (AtomPat (Pred "q") []) Mandatory
                , Question (QuestionId "q2") (AtomPat (Pred "q") []) Optional
                ]
            }
        , Rule
            { ruleId = RuleId "rcert"
            , ruleParams = []
            , ruleMode = Strict
            , rulePremises = [AtomPat (Pred "p") []]
            , rulePremiseLabels = []
            , ruleConclusion = AtomPat (Pred "q") []
            , ruleAllowTrusted = False
            , ruleCertifiers =
                [CertRef (BackendId "nd") 1 (TheoryDigest "sha256:theory-a")]
            , ruleQuestions = []
            }
        ]
    , unitContraries =
        [Contrary (AtomPat (Pred "p") []) (AtomPat (Pred "q") [])]
    , unitExceptions =
        [Exception (RuleId "rmix") (AtomPat (Pred "q") [])]
    , unitTheories =
        [(TheoryDigest "sha256:theory-a", [Prop (Pred "q") []])]
    , unitLeaves =
        [ (LeafId "l1", Prop (Pred "p") [])
        , (LeafId "l2", Prop (Pred "q") [])
        ]
    , unitArgs =
        [ (ArgId "a0", SLeaf (LeafId "l1"))
        ,
          ( ArgId "a1"
          , SRule
              (RuleId "rcert")
              []
              [SLeaf (LeafId "l1")]
              []
              []
              ( AssuranceCert
                  ( Cert
                      (BackendId "nd")
                      1
                      (TheoryDigest "sha256:theory-a")
                      (SList [SAtom "hyp", SAtom "1"])
                  )
              )
          )
        ]
    , unitAttacks =
        [ Rebut (ArgId "a0") (ArgId "a1")
        , Undermine (ArgId "a0") (ArgId "a1") [StepPremise 0]
        ]
    , unitQueries = [Prop (Pred "p") [], Prop (Pred "q") []]
    , unitGroups = []
    , unitGroupMode = QuarantineOnConflict
    }

goldenReplayText :: String
goldenReplayText =
  "(replay-id (core lara-core@0.2) (policy empirical-v1) "
    ++ "(backends (backend nd 1)) "
    ++ "(theories sha256:theory-a) "
    ++ "(artifact sha256:artifact-0))"

goldenReplayId :: ReplayId
goldenReplayId =
  either (error . replayErrorMessage) id $
    mkReplayId
      LaraCoreV02
      (PolicyId "empirical-v1")
      [(BackendId "nd", "1")]
      [TheoryDigest "sha256:theory-a"]
      (Digest "sha256:artifact-0")

goldenCheckInputText :: String
goldenCheckInputText =
  "(check-input " ++ goldenReplayText ++ " " ++ goldenUnitText ++ ")"

goldenCheckInput :: CheckInput
goldenCheckInput =
  either (error . replayErrorMessage) id (mkCheckInput goldenReplayId goldenUnit)

goldenAcceptText :: String
goldenAcceptText =
  "(verdict " ++ goldenReplayText
    ++ " accept (labels (0 in)) (edges) "
    ++ "(statuses (status (atom p) justified)))"

goldenRejectText :: String
goldenRejectText =
  "(verdict " ++ goldenReplayText ++ " reject R13)"

prop_replayEnvelopeGoldenVectors :: Bool
prop_replayEnvelopeGoldenVectors =
  and
    [ printSExpr (encodeReplayId goldenReplayId) == goldenReplayText
    , decodeText decodeReplayId goldenReplayText == Right goldenReplayId
    , printSExpr (encodeCheckInput goldenCheckInput) == goldenCheckInputText
    , decodeText decodeCheckInput goldenCheckInputText == Right goldenCheckInput
    , decodeCheckInputFile goldenCheckInputText == Right goldenCheckInput
    , printSExpr (encodeVerdict acceptVerdict) == goldenAcceptText
    , decodeText decodeVerdict goldenAcceptText == Right acceptVerdict
    , printSExpr (encodeVerdict rejectVerdict) == goldenRejectText
    , decodeText decodeVerdict goldenRejectText == Right rejectVerdict
    ]
  where
    acceptVerdict =
      Verdict
        goldenReplayId
        (Accept [(0, LIn)] [] [(Prop (Pred "p") [], Published Justified)])
    rejectVerdict = Verdict goldenReplayId (Reject (RejectClass R13))

prop_replayEnvelopeMalformedMatrix :: Bool
prop_replayEnvelopeMalformedMatrix =
  all (isLeft . decodeText decodeReplayId) malformedReplay
    && all (isLeft . decodeText decodeCheckInput) malformedInput
    && isLeft (decodeCheckInputFile "(unit)")
    && isLeft (decodeText decodeVerdict "(verdict reject R1)")
  where
    malformedReplay =
      [ "(replay-id (core lara-core@0.2) (policy empirical-v1) (backends) (theories))"
      , "(replay-id (core lara-core@0.2) (policy empirical-v1) (backends) (theories) (artifact sha256:a) extra)"
      , "(replay-id (core) (policy empirical-v1) (backends) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.2 extra) (policy empirical-v1) (backends) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.2) (policy) (backends) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.2) (policy empirical-v1 extra) (backends) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.2) (policy empirical-v1) (backends (backend nd)) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.2) (policy empirical-v1) (backends (backend nd 1 extra)) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.2) (policy empirical-v1) (backends) (theories (x)) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.2) (policy empirical-v1) (backends) (theories) (artifact))"
      , "(replay-id (core lara-core@0.2) (policy empirical-v1) (backends) (theories) (artifact sha256:a extra))"
      , "(replay-id (policy empirical-v1) (core lara-core@0.2) (backends) (theories) (artifact sha256:a))"
        -- The retired version (hard cutover, #91 decision 5): a @0.1 envelope is
        -- an unsupported core version, not a compatibility path.
      , "(replay-id (core lara-core@0.1) (policy empirical-v1) (backends) (theories) (artifact sha256:a))"
      , "(replay-id (core (lara-core@0.2)) (policy empirical-v1) (backends) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.2) (policy (empirical-v1)) (backends) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.2) (policy empirical-v1) (backends (backend (nd) 1)) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.2) (policy empirical-v1) (backends (backend nd (1))) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.2) (policy empirical-v1) (backends) (theories (sha256:a)) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.2) (policy empirical-v1) (backends) (theories) (artifact (sha256:a)))"
      , "(replay-id (core lara-core@0.2) (policy empirical-v1) (backends) (theories sha256:z sha256:a) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.2) (policy empirical-v1) (backends) (theories sha256:a sha256:a) (artifact sha256:a))"
      ]
    malformedInput =
      [ "(check-input " ++ goldenReplayText ++ ")"
      , "(check-input " ++ goldenReplayText ++ " " ++ goldenUnitText ++ " extra)"
      , "(check-input "
          ++ goldenReplayText
          ++ " (unit (theories (theory sha256:theory-a) (theory sha256:theory-a))))"
      , "(check-input "
          ++ goldenReplayText
          ++ " (unit (theories (theory sha256:other))))"
      ]
    isLeft (Left _) = True
    isLeft _ = False

decodeText :: (SExpr -> Either WireError a) -> String -> Either WireError a
decodeText decoder text =
  case parseSExpr text of
    Left err -> Left (WireError "text" (show err))
    Right value -> decoder value

prop_unitGoldenVector :: Bool
prop_unitGoldenVector =
  decodeText decodeUnit goldenUnitText == Right goldenUnit
    && printSExpr (encodeUnit goldenUnit) == goldenUnitText
    && decodeText decodeUnit (printSExpr (encodeUnit goldenUnit)) == Right goldenUnit

-- | The same unit decodes identically with noisy layout and comments, and
-- with empty sections spelled out or omitted.
prop_unitGoldenLayoutVariants :: Bool
prop_unitGoldenLayoutVariants =
  decodeText decodeUnit commented == Right goldenUnit
    && decodeText decodeUnit minimal == Right minimalUnit
    && decodeText decodeUnit spelled == Right minimalUnit
  where
    commented = "; header\n" ++ goldenUnitText ++ "\n; footer\n"
    minimal = "(unit)"
    spelled =
      "(unit (policy (rules) (contraries) (exceptions)) (theories) \
      \(leaves) (args) (attacks) (queries))"
    minimalUnit = Unit emptySigma [] [] [] [] [] [] [] [] [] QuarantineOnConflict

-- | The unit round trip: decode ∘ encode = Right id, through the text layer.
prop_unitRoundTrip :: Property
prop_unitRoundTrip =
  forAll genUnit $ \u ->
    decodeUnit (encodeUnit u) == Right u
      && decodeText decodeUnit (printSExpr (encodeUnit u)) == Right u


-- | The checker-input round trip over varied replay identities (C10):
-- @decode ∘ encode = Right id@ at both the tree and the text layer, with
-- 0-3 canonical theory digests (occasionally non-ASCII, exercising the
-- quoted-atom path) and a varied backend selection in the replay-id.
prop_checkInputRoundTrip :: Property
prop_checkInputRoundTrip =
  forAll genCheckInput $ \input ->
    let encoded = encodeCheckInput input
     in decodeCheckInput encoded == Right input
          && decodeCheckInputFile (printSExpr encoded) == Right input
-- | The wire tag table is self-consistent.
prop_tagRoundTrip :: Property
prop_tagRoundTrip =
  forAll (elements [minBound .. maxBound]) $ \t ->
    parseTag (tagToString t) == Just t

-- | The complete wire tag table round-trips and has unique spellings.
prop_tagTableTotal :: Property
prop_tagTableTotal =
  conjoin
    [ counterexample "some bounded tag does not round-trip" $
        property (all (\t -> parseTag (tagToString t) == Just t) tags)
    , counterexample ("colliding tag spelling(s): " ++ show collisions) $
        length spellings == length (nub spellings)
    ]
  where
    tags = [minBound .. maxBound]
    spellings = map tagToString tags
    collisions =
      [ spelling
      | spelling <- nub spellings
      , length (filter (== spelling) spellings) > 1
      ]

-- ---------------------------------------------------------------------------
-- Verdict golden vectors (hand-verified)
-- ---------------------------------------------------------------------------

prop_verdictGoldenVectors :: Bool
prop_verdictGoldenVectors =
  and
    [ printSExpr (encodeVerdict acceptV) == acceptText
    , decodeVerdict (encodeVerdict acceptV) == Right acceptV
    , parseSExpr acceptText == Right (encodeVerdict acceptV)
    , printSExpr (encodeVerdict rejectR5) == rejectText (RejectClass R5)
    , decodeVerdict (encodeVerdict rejectR5) == Right rejectR5
    , printSExpr (encodeVerdict rejectDup) == rejectText DuplicateRule
    , decodeVerdict (encodeVerdict rejectDup) == Right rejectDup
    , printSExpr (encodeVerdict rejectIncomplete)
        == rejectText IncompleteArgument
    , decodeVerdict (encodeVerdict rejectIncomplete) == Right rejectIncomplete
    , printSExpr (encodeVerdict rejectMissing)
        == rejectText MissingConflict
    , decodeVerdict (encodeVerdict rejectMissing) == Right rejectMissing
    , printSExpr (encodeVerdict blockedV) == blockedText
    , decodeVerdict (encodeVerdict blockedV) == Right blockedV
    , parseSExpr blockedText == Right (encodeVerdict blockedV)
    , printSExpr (encodeVerdict twoBlockedV) == twoBlockedText
    , decodeVerdict (encodeVerdict twoBlockedV) == Right twoBlockedV
    , parseSExpr twoBlockedText == Right (encodeVerdict twoBlockedV)
    ]
  where
    acceptV =
      Verdict goldenReplayId $
        Accept
          [(0, LIn), (1, LOut), (2, LUndec)]
          [(0, 1), (0, 2)]
          [ (Prop (Pred "p") [], Published Justified)
          , (Prop (Pred "q") [TNum "2"], Published Defeated)
          ]
    -- Spec §4.3 / issue #76: @p@'s support could have been affected by
    -- quarantine, so its public status is @evidence-blocked@ and the four-state
    -- label it would have had moves to the @conditional@ section. @q@ is out of
    -- reach of the edit and keeps its ordinary status.
    blockedV =
      Verdict goldenReplayId $
        Accept
          [(0, LIn), (1, LOut), (2, LUndec)]
          [(0, 1), (0, 2)]
          [ (Prop (Pred "p") [], EvidenceBlocked Justified)
          , (Prop (Pred "q") [TNum "2"], Published Defeated)
          ]
    blockedText =
      "(verdict " ++ goldenReplayText
        ++ " accept (labels (0 in) (1 out) (2 undec)) "
        ++ "(edges (0 1) (0 2)) "
        ++ "(statuses (status (atom p) evidence-blocked) "
        ++ "(status (atom q (num 2)) defeated)) "
        ++ "(conditional (status (atom p) justified)))"
    -- Two blocked queries pin the positional invariant: the conditional
    -- projection is in query order, including when an ordinary status sits
    -- between the blocked entries.
    twoBlockedV =
      Verdict goldenReplayId $
        Accept
          [(0, LIn), (1, LOut), (2, LUndec)]
          [(0, 1), (0, 2)]
          [ (Prop (Pred "p") [], EvidenceBlocked Justified)
          , (Prop (Pred "q") [TNum "2"], Published Defeated)
          , (Prop (Pred "r") [], EvidenceBlocked Contested)
          ]
    twoBlockedText =
      "(verdict " ++ goldenReplayText
        ++ " accept (labels (0 in) (1 out) (2 undec)) "
        ++ "(edges (0 1) (0 2)) "
        ++ "(statuses (status (atom p) evidence-blocked) "
        ++ "(status (atom q (num 2)) defeated) "
        ++ "(status (atom r) evidence-blocked)) "
        ++ "(conditional (status (atom p) justified) "
        ++ "(status (atom r) contested)))"
    acceptText =
      "(verdict " ++ goldenReplayText
        ++ " accept (labels (0 in) (1 out) (2 undec)) "
        ++ "(edges (0 1) (0 2)) "
        ++ "(statuses (status (atom p) justified) "
        ++ "(status (atom q (num 2)) defeated)))"
    rejectText rejection =
      "(verdict " ++ goldenReplayText ++ " reject " ++ rejectionText rejection ++ ")"
    rejectionText rejection = case rejection of
      RejectClass R5 -> "R5"
      DuplicateRule -> "duplicate-rule"
      IncompleteArgument -> "incomplete-argument"
      MissingConflict -> "missing-conflict"
      _ -> error "unexpected rejection fixture"
    rejectR5 = Verdict goldenReplayId (Reject (RejectClass R5))
    rejectDup = Verdict goldenReplayId (Reject DuplicateRule)
    rejectIncomplete = Verdict goldenReplayId (Reject IncompleteArgument)
    rejectMissing = Verdict goldenReplayId (Reject MissingConflict)

prop_verdictRoundTrip :: Property
prop_verdictRoundTrip =
  forAll genVerdict $ \v ->
    decodeVerdict (encodeVerdict v) == Right v
      && fmap printSExpr (parseSExpr (printSExpr (encodeVerdict v)))
        == Right (printSExpr (encodeVerdict v))

-- ---------------------------------------------------------------------------
-- Malformed-input rejection matrix (R14)
-- ---------------------------------------------------------------------------

-- | Grammar-level rejections: one field short / one field long per construct,
-- unknown tags, bad naturals, and the two wire-well-formedness invariants.
prop_unitMalformedMatrix :: Bool
prop_unitMalformedMatrix = all isLeft (map decodeUnit malformed)
  where
    isLeft (Left _) = True
    isLeft _ = False
    malformed =
      -- top-level shape and sections
      [ SAtom "unit" -- not a list
      , SList [SAtom "bogus"] -- unknown head tag
      , SList [SAtom "unit", SList [SAtom "bogus"]] -- unknown section
      , SList [SAtom "unit", leavesSec, leavesSec] -- duplicate section
      , SList [SAtom "unit", leavesSec, policySec] -- out-of-order section
      -- sigma section
      , SList [SAtom "unit", SList [SAtom "sigma", sigmaSortsSec, sigmaConsSec]] -- sigma short
      , SList [SAtom "unit", SList [SAtom "sigma", sigmaSortsSec, sigmaConsSec, sigmaPredsSec, SList []]] -- sigma long
      , sigmaWith (SList [SAtom "sorts", SList []]) sigmaConsSec sigmaPredsSec -- sort not an atom
      , sigmaWith sigmaSortsSec (SList [SAtom "cons", SList [SAtom "bogus", SAtom "k", SList [SAtom "args"], SAtom "Num"]]) sigmaPredsSec -- constructor tag
      , sigmaWith sigmaSortsSec (SList [SAtom "cons", SList [SAtom "con", SAtom "k", SList [SAtom "args"]]]) sigmaPredsSec -- constructor short
      , sigmaWith sigmaSortsSec (SList [SAtom "cons", SList [SAtom "con", SAtom "k", SList [SAtom "bogus"], SAtom "Num"]]) sigmaPredsSec -- constructor args tag
      , sigmaWith sigmaSortsSec sigmaConsSec (SList [SAtom "preds", SList [SAtom "bogus", SAtom "p", SList [SAtom "args"]]]) -- predicate tag
      , sigmaWith sigmaSortsSec sigmaConsSec (SList [SAtom "preds", SList [SAtom "pred", SAtom "p"]]) -- predicate short
      , sigmaWith sigmaSortsSec sigmaConsSec (SList [SAtom "preds", SList [SAtom "pred", SAtom "p", SList [SAtom "bogus"]]]) -- predicate args tag
      , SList [SAtom "unit", SList [SAtom "policy", rulesSec]] -- policy short
      , SList
          [ SAtom "unit"
          , SList [SAtom "policy", rulesSec, contrariesSec, exceptionsSec, SList []]
          ] -- policy long
      , SList [SAtom "unit", SList [SAtom "policy", SList [SAtom "bogus"], contrariesSec, exceptionsSec]] -- policy subsection tag
      -- rules
      , SList [SAtom "unit", policyWith (SList (SAtom "rule" : take 7 ruleBody))] -- rule short
      , SList [SAtom "unit", policyWith (SList (SAtom "rule" : ruleBody ++ [SAtom "extra"]))] -- rule long
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", SList [SAtom "mode", SAtom "bogus"], paramsSec, premisesSec, conclusionSec, questionsSec, allowTrustedSec, certifiersSec])] -- bad mode
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, premisesSec, conclusionSec, questionsSec, SList [SAtom "allow-trusted", SAtom "bogus"], certifiersSec])] -- bad bool
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, premisesSec, conclusionSec, SList [SAtom "questions", SList [SAtom "question", SAtom "q", apatP, SAtom "bogus"]], allowTrustedSec, certifiersSec])] -- bad necessity
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, premisesSec, conclusionSec, SList [SAtom "questions", SList [SAtom "question", SAtom "q", apatP]], allowTrustedSec, certifiersSec])] -- question short
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, premisesSec, conclusionSec, SList [SAtom "questions", SList [SAtom "question", SAtom "q", apatP, SAtom "mandatory", SAtom "x"]], allowTrustedSec, certifiersSec])] -- question long
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, premisesSec, conclusionSec, questionsSec, allowTrustedSec, SList [SAtom "certifiers", SList [SAtom "certifier", SAtom "nd", SAtom "01", SAtom "h"]]])] -- certifier bad nat
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, premisesSec, conclusionSec, questionsSec, allowTrustedSec, SList [SAtom "certifiers", SList [SAtom "certifier", SAtom "nd", SAtom "1"]]])] -- certifier short
      -- contraries / exceptions
      , SList [SAtom "unit", policyParts (SList [SAtom "contraries", SList [SAtom "contrary", apatP]]) exceptionsSec] -- contrary short
      , SList [SAtom "unit", policyParts (SList [SAtom "contraries", SList [SAtom "contrary", apatP, apatP, apatP]]) exceptionsSec] -- contrary long
      , SList [SAtom "unit", policyParts contrariesSec (SList [SAtom "exceptions", SList [SAtom "exception", SAtom "r"]])] -- exception short
      , SList [SAtom "unit", policyParts contrariesSec (SList [SAtom "exceptions", SList [SAtom "bogus", SAtom "r", apatP]])] -- exception tag
      -- atoms, patterns, terms
      , SList [SAtom "unit", SList [SAtom "queries", SList [SAtom "atom"]]] -- atom without head
      , SList [SAtom "unit", SList [SAtom "queries", SList [SAtom "atom", SAtom "p", SAtom "notalist"]]] -- term not a list
      , SList [SAtom "unit", SList [SAtom "queries", SList [SAtom "atom", SAtom "p", SList [SAtom "num", SAtom "1", SAtom "2"]]]] -- num long
      , SList [SAtom "unit", SList [SAtom "queries", SList [SAtom "atom", SAtom "p", SList [SAtom "con"]]]] -- con without head
      , SList [SAtom "unit", SList [SAtom "queries", SList [SAtom "atom", SAtom "p", SList [SAtom "bogus", SAtom "1"]]]] -- term unknown tag
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, SList [SAtom "premises", SList [SAtom "apat"]], conclusionSec, questionsSec, allowTrustedSec, certifiersSec])] -- apat without head
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, SList [SAtom "premises", SList [SAtom "apat", SAtom "p", SList [SAtom "var", SAtom "X", SAtom "Y"]]], conclusionSec, questionsSec, allowTrustedSec, certifiersSec])] -- var long
      -- support terms
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", substSec, premisesSec, dischargesSec, holesSec])] -- inst short
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", substSec, premisesSec, dischargesSec, holesSec, assuranceSec, SAtom "extra"])] -- inst long
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", SList [SAtom "subst", SList [SAtom "X"]], premisesSec, dischargesSec, holesSec, assuranceSec])] -- binding short
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", SList [SAtom "subst", SList [SAtom "X", SList [SAtom "num", SAtom "1"], SAtom "e"]], premisesSec, dischargesSec, holesSec, assuranceSec])] -- binding long
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", substSec, premisesSec, SList [SAtom "discharges", SList [SAtom "q"]], holesSec, assuranceSec])] -- discharge short
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", substSec, premisesSec, dischargesSec, SList [SAtom "holes", SList [SAtom "notatom"]], assuranceSec])] -- hole not an atom
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", substSec, premisesSec, dischargesSec, holesSec, SList [SAtom "assurance", SAtom "bogus"]])] -- assurance unknown
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", substSec, premisesSec, dischargesSec, holesSec, SList [SAtom "assurance", SList [SAtom "cert", SAtom "nd", SAtom "-1", SAtom "h", SList []]]])] -- cert bad nat
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", substSec, premisesSec, dischargesSec, holesSec, SList [SAtom "assurance", SList [SAtom "cert", SAtom "nd", SAtom "1", SAtom "h"]]])] -- cert short
      , SList [SAtom "unit", argsWith (SList [SAtom "leaf", SAtom "l", SAtom "extra"])] -- leaf long
      , SList [SAtom "unit", argsWith (SAtom "notalist")] -- sterm not a list
      -- attacks and positions
      , SList [SAtom "unit", argsPairSec, SList [SAtom "attacks", SList [SAtom "rebut", SAtom "a0"]]] -- rebut short
      , SList [SAtom "unit", argsPairSec, SList [SAtom "attacks", SList [SAtom "rebut", SAtom "a0", SAtom "a1", SAtom "e"]]] -- rebut long
      , SList [SAtom "unit", argsPairSec, SList [SAtom "attacks", SList [SAtom "undercut", SAtom "a0", SAtom "a1"]]] -- undercut short
      , SList [SAtom "unit", argsPairSec, SList [SAtom "attacks", SList [SAtom "bogus", SAtom "a0", SAtom "a1"]]] -- attack kind
      , SList [SAtom "unit", argsPairSec, SList [SAtom "attacks", SList [SAtom "undermine", SAtom "a0", SAtom "a1", SList [SAtom "pos", SList [SAtom "prem", SAtom "01"]]]]] -- pos bad nat
      , SList [SAtom "unit", argsPairSec, SList [SAtom "attacks", SList [SAtom "undermine", SAtom "a0", SAtom "a1", SList [SAtom "pos", SList [SAtom "bogus", SAtom "0"]]]]] -- pos step tag
      , SList [SAtom "unit", argsPairSec, SList [SAtom "attacks", SList [SAtom "undermine", SAtom "a0", SAtom "a1", SAtom "notalist"]]] -- pos not a list
      -- wire well-formedness (R14 invariants)
      , SList [SAtom "unit", SList [SAtom "args", argA0, argA0']] -- duplicate arg ids
      , SList [SAtom "unit", SList [SAtom "attacks", SList [SAtom "rebut", SAtom "a0", SAtom "a1"]]] -- undeclared endpoint
      -- duplicate-report groups (spec §4.3): decode shape + R14 well-formedness
      , SList [SAtom "unit", SList [SAtom "groups"]] -- groups section missing its conflict mode
      , SList [SAtom "unit", groupLeaves, SList [SAtom "groups", SAtom "bogus", groupG12]] -- unknown conflict mode
      , SList [SAtom "unit", SList [SAtom "groups", SAtom "reject", SList [SAtom "group", SAtom "g"]]] -- group bad arity (no members list)
      , SList [SAtom "unit", SList [SAtom "groups", SAtom "reject", SList [SAtom "group", SAtom "g", SAtom "notalist"]]] -- members not a list
      , SList [SAtom "unit", groupLeaves, SList [SAtom "groups", SAtom "reject", groupG12, groupG12]] -- duplicate group id
      , SList [SAtom "unit", groupLeaves, SList [SAtom "groups", SAtom "reject", SList [SAtom "group", SAtom "g", SList [SAtom "l1", SAtom "l1"]]]] -- repeated member
      , SList [SAtom "unit", groupLeaves, SList [SAtom "groups", SAtom "reject", SList [SAtom "group", SAtom "g", SList [SAtom "l1"]]]] -- fewer than two members
      , SList [SAtom "unit", groupLeaves, SList [SAtom "groups", SAtom "reject", SList [SAtom "group", SAtom "g", SList [SAtom "l1", SAtom "lX"]]]] -- dangling member (not a declared leaf)
      ]
    leavesSec = SList [SAtom "leaves", SList [SAtom "leaf", SAtom "l", apatAtomP]]
    policySec = SList [SAtom "policy", rulesSec, contrariesSec, exceptionsSec]
    rulesSec = SList [SAtom "rules"]
    contrariesSec = SList [SAtom "contraries"]
    exceptionsSec = SList [SAtom "exceptions"]
    sigmaSortsSec = SList [SAtom "sorts"]
    sigmaConsSec = SList [SAtom "cons"]
    sigmaPredsSec = SList [SAtom "preds"]
    sigmaWith ss cs ps = SList [SAtom "unit", SList [SAtom "sigma", ss, cs, ps]]
    policyWith rule = SList [SAtom "policy", SList [SAtom "rules", rule], contrariesSec, exceptionsSec]
    policyParts cs es = SList [SAtom "policy", rulesSec, cs, es]
    ruleBody =
      [ SAtom "r"
      , modeSec
      , paramsSec
      , premisesSec
      , conclusionSec
      , questionsSec
      , allowTrustedSec
      , certifiersSec
      ]
    modeSec = SList [SAtom "mode", SAtom "defeasible"]
    paramsSec = SList [SAtom "params"]
    premisesSec = SList [SAtom "premises"]
    conclusionSec = SList [SAtom "conclusion", apatP]
    questionsSec = SList [SAtom "questions"]
    allowTrustedSec = SList [SAtom "allow-trusted", SAtom "false"]
    certifiersSec = SList [SAtom "certifiers"]
    apatP = SList [SAtom "apat", SAtom "p"]
    apatAtomP = SList [SAtom "atom", SAtom "p"]
    substSec = SList [SAtom "subst"]
    dischargesSec = SList [SAtom "discharges"]
    holesSec = SList [SAtom "holes"]
    assuranceSec = SList [SAtom "assurance", SAtom "none"]
    argsWith sterm = SList [SAtom "args", SList [SAtom "arg", SAtom "a0", sterm]]
    argA0 = SList [SAtom "arg", SAtom "a0", SList [SAtom "leaf", SAtom "l"]]
    argA0' = SList [SAtom "arg", SAtom "a0", SList [SAtom "leaf", SAtom "m"]]
    argsPairSec =
      SList
        [ SAtom "args"
        , SList [SAtom "arg", SAtom "a0", SList [SAtom "leaf", SAtom "l"]]
        , SList [SAtom "arg", SAtom "a1", SList [SAtom "leaf", SAtom "l"]]
        ]
    groupLeaves =
      SList
        [ SAtom "leaves"
        , SList [SAtom "leaf", SAtom "l1", apatAtomP]
        , SList [SAtom "leaf", SAtom "l2", apatAtomP]
        ]
    groupG12 = SList [SAtom "group", SAtom "g", SList [SAtom "l1", SAtom "l2"]]

-- | Malformed verdicts are rejected at the decode boundary.
prop_verdictMalformedMatrix :: Bool
prop_verdictMalformedMatrix = all isLeft (map decodeVerdict malformed)
  where
    isLeft (Left _) = True
    isLeft _ = False
    malformed =
      [ SAtom "verdict" -- not a list
      , SList [SAtom "bogus", SAtom "reject", SAtom "R5"] -- head tag
      , SList [SAtom "verdict", SAtom "bogus", SAtom "R5"] -- accept|reject tag
      , SList [SAtom "verdict", SAtom "reject"] -- reject short
      , SList [SAtom "verdict", SAtom "reject", SAtom "R5", SAtom "x"] -- reject long
      , SList [SAtom "verdict", SAtom "reject", SAtom "R2"] -- class outside the core
      , SList [SAtom "verdict", SAtom "reject", SAtom "bogus"] -- unknown rejection
      , SList [SAtom "verdict", SAtom "reject", SList []] -- rejection not an atom
      , SList [SAtom "verdict", SAtom "accept", labelsSec, edgesSec] -- accept short
      , SList [SAtom "verdict", SAtom "accept", labelsSec, edgesSec, statusesSec, SList []] -- accept long
      , SList [SAtom "verdict", SAtom "accept", SList [SAtom "labels", SList [SAtom "0", SAtom "bogus"]], edgesSec, statusesSec] -- bad label
      , SList [SAtom "verdict", SAtom "accept", SList [SAtom "labels", SList [SAtom "01", SAtom "in"]], edgesSec, statusesSec] -- label bad nat
      , SList [SAtom "verdict", SAtom "accept", SList [SAtom "labels", SList [SAtom "0"]], edgesSec, statusesSec] -- label short
      , SList [SAtom "verdict", SAtom "accept", labelsSec, SList [SAtom "edges", SList [SAtom "0"]], statusesSec] -- edge short
      , SList [SAtom "verdict", SAtom "accept", labelsSec, edgesSec, SList [SAtom "statuses", SList [SAtom "status", apatAtomP, SAtom "bogus"]]] -- bad status
      , SList [SAtom "verdict", SAtom "accept", labelsSec, edgesSec, SList [SAtom "statuses", SList [SAtom "status", apatAtomP]]] -- status short
      , SList [SAtom "verdict", SAtom "accept", labelsSec, edgesSec, SList [SAtom "statuses", SList [SAtom "bogus", apatAtomP, SAtom "gap"]]] -- status entry tag
      -- The rows above omit the replay-id, so they die on the outer shape and
      -- never reach the section decoders. These carry a well-formed replay-id so
      -- the section checks are the thing under test — including the four
      -- rejection paths the conditional section adds (spec §4.3, issue #76).
      , accept [labelsSec, edgesSec] -- accept short
      , accept [labelsSec, edgesSec, statusesSec, conditionalSec, conditionalSec] -- accept long
      , accept [labelsSec, edgesSec, blockedStatusesSec] -- evidence-blocked, no conditional section
      , accept [labelsSec, edgesSec, statusesSec, conditionalSec] -- conditional entry, nothing blocked
      , accept [labelsSec, edgesSec, blockedStatusesSec, SList [SAtom "conditional"]] -- present but empty
      , accept [labelsSec, edgesSec, blockedStatusesSec, otherConditionalSec] -- conditional names another query
      , accept [labelsSec, edgesSec, blockedStatusesSec, SList [SAtom "bogus", statusEntry "p" "gap"]] -- section tag
      , accept [labelsSec, edgesSec, blockedStatusesSec, SList [SAtom "conditional", SList [SAtom "status", apatAtomP, SAtom "evidence-blocked"]]] -- conditional label not four-state
      -- With multiple blocked queries the conditional projection is positional,
      -- not a lookup table: reversal, truncation, and a duplicate\/extra suffix
      -- are all non-canonical.
      , accept [labelsSec, edgesSec, twoBlockedStatusesSec, SList [SAtom "conditional", statusEntry "q" "defeated", statusEntry "p" "gap"]]
      , accept [labelsSec, edgesSec, twoBlockedStatusesSec, SList [SAtom "conditional", statusEntry "p" "gap"]]
      , accept [labelsSec, edgesSec, twoBlockedStatusesSec, SList [SAtom "conditional", statusEntry "p" "gap", statusEntry "q" "defeated", statusEntry "q" "defeated"]]
      ]
    accept sections =
      SList ([SAtom "verdict", encodeReplayId goldenReplayId, SAtom "accept"] ++ sections)
    labelsSec = SList [SAtom "labels"]
    edgesSec = SList [SAtom "edges"]
    statusesSec = SList [SAtom "statuses", statusEntry "p" "gap"]
    blockedStatusesSec = SList [SAtom "statuses", statusEntry "p" "evidence-blocked"]
    twoBlockedStatusesSec =
      SList
        [ SAtom "statuses"
        , statusEntry "p" "evidence-blocked"
        , statusEntry "q" "evidence-blocked"
        ]
    conditionalSec = SList [SAtom "conditional", statusEntry "p" "gap"]
    otherConditionalSec = SList [SAtom "conditional", statusEntry "q" "gap"]
    statusEntry name value =
      SList [SAtom "status", SList [SAtom "atom", SAtom name], SAtom value]
    apatAtomP = SList [SAtom "atom", SAtom "p"]

-- | Whole-file text and low-level Unit grammar rejections.
prop_fileMalformedRejected :: Bool
prop_fileMalformedRejected =
  and
    [ isLeft (decodeText decodeUnit "(unit") -- truncated text
    , isLeft (decodeText decodeUnit "(unit) (unit)") -- two units
    , isLeft (decodeText decodeUnit "bogus") -- not a unit
    ]
  where
    isLeft (Left _) = True
    isLeft _ = False

-- | Codec errors are located: the failure carries a context path.
prop_errorIsLocated :: Bool
prop_errorIsLocated =
  case decodeText decodeUnit "(unit (leaves (leaf l1 (atom))))" of
    Left (WireError ctx _) -> "leaf" `isPrefixOf` ctx || ctx == "atom"
    Right _ -> False

-- ---------------------------------------------------------------------------
-- Cross-checked Lean-driver goldens
-- ---------------------------------------------------------------------------

-- | Fixture: the self-conflict unit of @lean/Lara/Examples/GroundedConsistency@
-- ('coveredSelfEdgeUnit') over the empty policy — one self-undermining leaf
-- argument. This assertion pins the intended Lean wire output: the bytes the
-- Lean driver must print for this fixture, here checked to decode to exactly
-- this verdict and to be reproduced by 'encodeVerdict'. The differential
-- harness confirms the actual Lean output.
prop_leanDriverAcceptGolden :: Bool
prop_leanDriverAcceptGolden =
  decodeVerdict leanBytes == Right expected
    && printSExpr (encodeVerdict expected) == leanText
  where
    leanText =
      "(verdict " ++ goldenReplayText
        ++ " accept (labels (0 undec)) (edges (0 0)) "
        ++ "(statuses (status (atom p) contested)))"
    Right leanBytes = parseSExpr leanText
    expected =
      Verdict
        goldenReplayId
        (Accept [(0, LUndec)] [(0, 0)] [(Prop (Pred "p") [], Published Contested)])

-- | Fixture: the missing-self-edge unit of the same file
-- ('missingSelfEdgeUnit') — no attack covers the declared contrary. Pins the
-- missing-conflict rejection bytes the Lean driver must print.
prop_leanDriverRejectGolden :: Bool
prop_leanDriverRejectGolden =
  decodeVerdict leanBytes == Right expected
    && printSExpr (encodeVerdict expected) == leanText
  where
    leanText = "(verdict " ++ goldenReplayText ++ " reject missing-conflict)"
    Right leanBytes = parseSExpr leanText
    expected = Verdict goldenReplayId (Reject MissingConflict)

-- ---------------------------------------------------------------------------
-- Exported runner
-- ---------------------------------------------------------------------------

wireSpecProps :: [(String, IO Result)]
wireSpecProps =
  [ ("wire text golden vectors", quickCheckResult prop_textGoldenVectors)
  , ("wire text malformed rejected", quickCheckResult prop_textMalformedRejected)
  , ("wire S-expr text round-trip", quickCheckResult prop_sexprTextRoundTrip)
  , ("wire print∘parse∘print idempotent", quickCheckResult prop_printParsePrintIdempotent)
  , ("wire ByteString parser matches the reference reader on committed inputs", quickCheckResult prop_referenceParserCommittedInputs)
  , ("wire ByteString parser matches the reference reader on printed trees", quickCheckResult prop_referenceParserPrinted)
  , ("wire ByteString parser matches the reference reader on corrupted input", quickCheckResult prop_referenceParserMutated)
  , ("wire parse error positions", quickCheckResult prop_parserErrorPositions)
  , ("wire depth bound is a located codec error", quickCheckResult prop_depthBoundIsCodecError)
  , ("wire depth bound counts depth, not forms", quickCheckResult prop_depthBoundCountsDepthNotForms)
  , ("wire invalid UTF-8 rejected closed", quickCheckResult prop_invalidUtf8Rejected)
  , ("wire unit golden vector", quickCheckResult prop_unitGoldenVector)
  , ("wire unit golden layout variants", quickCheckResult prop_unitGoldenLayoutVariants)
  , ("wire unit round-trip", quickCheckResult prop_unitRoundTrip)
  , ("wire check-input round-trip", quickCheckResult prop_checkInputRoundTrip)
  , ("wire tag round-trip", quickCheckResult prop_tagRoundTrip)
  , ("wire tag table total", quickCheckResult prop_tagTableTotal)
  , ("wire replay/envelope golden vectors", quickCheckResult prop_replayEnvelopeGoldenVectors)
  , ("wire replay/envelope malformed matrix", quickCheckResult prop_replayEnvelopeMalformedMatrix)
  , ("wire verdict golden vectors", quickCheckResult prop_verdictGoldenVectors)
  , ("wire verdict round-trip", quickCheckResult prop_verdictRoundTrip)
  , ("wire unit malformed matrix", quickCheckResult prop_unitMalformedMatrix)
  , ("wire verdict malformed matrix", quickCheckResult prop_verdictMalformedMatrix)
  , ("wire file malformed rejected", quickCheckResult prop_fileMalformedRejected)
  , ("wire codec error is located", quickCheckResult prop_errorIsLocated)
  , ("wire Lean-driver accept golden", quickCheckResult prop_leanDriverAcceptGolden)
  , ("wire Lean-driver reject golden", quickCheckResult prop_leanDriverRejectGolden)
  ]
