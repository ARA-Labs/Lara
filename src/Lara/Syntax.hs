-- | The concrete @.lara@ surface syntax: parser and label-preserving printer
-- (@lara-syntax\@0.7@, over the frozen @0.1@ grammar in
-- @docs/lara-surface-grammar.md@).
--
-- == Live surface versions
--
-- @\@0.3@ introduced the six Appendix B forms below. They remain
-- presentation-only, are parsed and printed here, and are expanded by
-- @Lara.Elaborate@ /before the checker anchor exists/:
--
--   * B.1 @measurand m : Num where higher-is-better@ — a policy-level table;
--   * B.2 @comparison-scheme@ blocks keyed by @(relation, polarity)@;
--   * B.3 the program-level @comparison@ declaration;
--   * B.4 optional @label:@ prefixes on rule premises;
--   * B.5 attack-path segments that name a premise label, and
--   * B.6 the @nl@ brace contract (@{cell l}@ directives, @{{@\/@}}@ escapes).
--
-- @\@0.4@ adds Appendix C's ordered @let name = term@ table and @{name}@
-- interpolation. Bindings round-trip as authored and are consumed once, before
-- the @\@0.3@ comparison pass; neither surface reaches 'Unit'.
--
-- @\@0.7@ is a /surface strictness/ release: it removes surface, it does not
-- add any. Its one invariant is that every authored token must change the
-- semantic object or be rejected with a located error. Two parser-side
-- consequences live in this module:
--
--   * @\@0.7@ — @discharge@ and @open@ under a bare @leaf(…)@ are parse errors,
--     not silently dropped lines. This extends App. A.1's existing ruling on
--     @assurance@ to its two siblings, for the same reason: the checker has no
--     rule to attach them to, and dropping them would mislead the author.
--   * @\@0.7@ — a hole is spelled @open q@. The retired @open q as o@ form named
--     the same thing twice (§6.1 reads a hole's 'ObligationId' /as/ the
--     question it leaves open), so the second slot could only ever be
--     redundant or misleading; a trailing @as …@ is now a located error
--     carrying its repair.
--
-- Nothing here touches @lara-core@, 'Lara.AST', or the wire: the surface
-- version never reaches the kernel, so every derived byte is unchanged.
--
-- Expansion deliberately does __not__ happen here: spec result 12
-- (@parse ∘ print = id@) is stated on the presentation AST, so bindings and a
-- @comparison@ must round-trip as authored and never as their expansions. For
-- the same reason B.5 positions and brace-bearing @nl@ bodies are recorded
-- __in the spelling they were authored in__ ('SurfaceStep', and a raw
-- unexpanded @nl@ string).
--
-- == Position in the pipeline
--
-- "Lara.Syntax" is the /presentation/ front end (spec §1): it decodes concrete
-- @.lara@\/@.policy.lara@ text into the presentation-layer abstract syntax of
-- "Lara.AST" ('Program' \/ 'Policy'), and prints those values back to a single
-- __canonical__ concrete spelling. It is __inside the TCB__: like "Lara.Wire"
-- it is a decode boundary, so a malformed source is a /located/ parse error
-- (spec §10.1 R14), never a checker verdict.
--
-- This module does __not__ elaborate. Resolving a surface argument's implicit
-- premises, its θ against a rule's declared parameters, its discharge targets
-- (leaf vs. prior argument), and whether a @supports(c)@ names a declared claim
-- are all the job of the @Program → Unit@ elaborator (@Lara.Elaborate@, Task
-- A1b). The parser therefore records the surface /faithfully but shallowly/ (see
-- "Surface support terms" below), and the printer inverts exactly that shallow
-- record so that @parse ∘ print = id@ holds on the presentation AST (spec
-- result 12).
--
-- == Canonical printing
--
-- LARA is not layout-sensitive (grammar §1.1); the printer emits fields in the
-- fixed order of grammar §3–§4 and the one canonical position spelling of §7,
-- so that reparsing a printed value returns it unchanged. The parser is more
-- permissive than the printer (it accepts any whitespace\/comments and the
-- documented optional fields); the printer commits to one spelling.
--
-- == Surface support terms (the A1a → A1b contract)
--
-- The surface @by r(g1,…,gn)@ form plus its
-- @discharge@\/@open@\/@assurance@ lines carries strictly less than the frozen
-- 'SupportTerm' (spec §5): premises are implicit, θ is positional with the
-- parameter /names/ living in the policy, and a discharge target is a bare
-- identifier whose leaf-vs-argument nature is a scoping question. The parser
-- records one complete 'ArgInstantiation' and leaves the rest for the
-- elaborator:
--
--   * @leaf(l)@                         ↦ @'ExplicitTheta' ('SLeaf' (LeafId l))@.
--   * @r(g1,…,gn)@                      ↦ @'ExplicitTheta' ('SRule'@ with
--     @srSubst = [(Param \"1\", g1), …, (Param \"n\", gn)]@ (positional,
--     1-based — §5's \"i-th parameter ↦ gi\"), empty premises, and the
--     optional assurance supplied by the arg block.
--   * @r from [ref1,…,refn]@             ↦ @'InferTheta'@ carrying the rule,
--     source references, shallow discharges, holes, and assurance.
--   * @discharge q with ref@            ↦ a shallow leaf target in an explicit
--     rule or an 'ArgRef' target in an inferred rule.
--
-- On a rule application — explicit or inferred — a hole is authored and
-- printed as @open q@ (@\@0.7@): one identifier, stored as its
-- 'ObligationId'. §6.1 reads that id /as/ the question the hole leaves open
-- (@holeNames@ in "Lara.SupportTerm"), so the single name is the whole
-- content of the line and there is no second identity to record. The retired
-- @open q as o@ form is rejected with the repair, whether or not @q@ and @o@
-- agree. The printer is total on every 'ArgInstantiation'.
--
-- On a bare @leaf(…)@ support term there is nowhere to attach a body line, so
-- @argBody@ rejects all three (@\@0.7@): 'addArgDischarge', 'addArgHole'
-- and 'setArgAssurance' return a @Left@ that @argBody@ turns into a located
-- 'ParseError' at the keyword — extending to the first two what App. A.1
-- already required for @assurance@. None of the three has a silent
-- fall-through equation, so the wart cannot be re-created by a caller that
-- skips the parser's check.
module Lara.Syntax
  ( -- * Located parse errors (spec §10.1 R14)
    ParseError (..)
    -- * Parsing
  , Source (..)
  , parseSource
  , parseProgram
  , parsePolicy
  , parseProp
  , isIdentStart
    -- * Canonical printing
  , printSource
  , printProgram
  , printPolicy
  , printArg
  , printArgConcl
  , printProp
    -- * Surface spellings of the @lara-syntax\@0.3@ closed vocabularies
    --
    -- | The @toString@ half of the single table each closed tag has here
    -- (grammar App. B.7). Exported so a diagnostic elsewhere — notably
    -- "Lara.Elaborate.Error" naming the (relation, polarity) pair a policy has
    -- no @comparison-scheme@ for — spells the surface keyword from this table
    -- and never from a second copy of the string literal.
  , polarityStr
  , relationStr
  , nlCellDirective
  , attackPathTerminalMarkers
  ) where

import Data.Char (isAlpha, isDigit)
import Data.List (intercalate)
import qualified Data.Set as Set

import Lara.AST
import Lara.Sigma
  ( ConSig (..)
  , PredSig (..)
  , Sigma (..)
  , Sort (..)
  , SortName (..)
  , emptySigma
  , sortFromText
  , sortText
  )
import Lara.Prop (Prop (..), Term (..))
import Lara.Strict (SExpr)
import Lara.Wire (parseSExpr, printSExpr)

-- ---------------------------------------------------------------------------
-- Located parse errors
-- ---------------------------------------------------------------------------

-- | A located surface parse failure (line and column are 1-based), mirroring
-- "Lara.Wire"'s @ParseError@\/@WireError@ shape at the decode boundary.
data ParseError = ParseError
  { peLine :: Int
  , peCol :: Int
  , peReason :: String
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Parser state and monad (hand-rolled; no external combinator library)
-- ---------------------------------------------------------------------------

data TriviaMode
  = NormalTrivia
  | WhitespaceOnlyTrivia

data PState = PState
  { psInput :: String
  , psLine :: !Int
  , psCol :: !Int
  , psTriviaMode :: !TriviaMode
  }

-- | A backtracking parser threading source position, the same shape as the
-- hand-rolled S-expression reader in "Lara.Wire" lifted into a monad.
newtype P a = P {runP :: PState -> Either ParseError (a, PState)}

instance Functor P where
  fmap f (P g) = P $ \s -> case g s of
    Left e -> Left e
    Right (a, s') -> Right (f a, s')

instance Applicative P where
  pure a = P $ \s -> Right (a, s)
  P f <*> P g = P $ \s -> case f s of
    Left e -> Left e
    Right (h, s') -> case g s' of
      Left e -> Left e
      Right (a, s'') -> Right (h a, s'')

instance Monad P where
  P g >>= k = P $ \s -> case g s of
    Left e -> Left e
    Right (a, s') -> runP (k a) s'

-- | Fail at the current cursor.
failP :: String -> P a
failP msg = P $ \s -> Left (ParseError (psLine s) (psCol s) msg)

-- | Read the current 1-based source position without consuming input.
getPosition :: P (Int, Int)
getPosition = P $ \s -> Right ((psLine s, psCol s), s)

-- | Fail at a previously captured source position.
failAtP :: (Int, Int) -> String -> P a
failAtP (line, col) msg = P $ \_ -> Left (ParseError line col msg)

getInput :: P String
getInput = P $ \s -> Right (psInput s, s)

-- | Advance one character, maintaining line/column.
advance1 :: PState -> PState
advance1 st = case psInput st of
  '\n' : r -> st {psInput = r, psLine = psLine st + 1, psCol = 1}
  _ : r -> st {psInput = r, psCol = psCol st + 1}
  [] -> st

advanceP :: P ()
advanceP = P $ \st -> Right ((), advance1 st)

-- | Consume the maximal prefix of characters satisfying the predicate.
takeWhileP :: (Char -> Bool) -> P String
takeWhileP p = P $ \s -> Right (go s)
  where
    go st = case psInput st of
      c : _ | p c -> let (rest, st') = go (advance1 st) in (c : rest, st')
      _ -> ("", st)

-- ---------------------------------------------------------------------------
-- Lexical layer (normal and whitespace-only trivia; grammar §1.2)
-- ---------------------------------------------------------------------------

-- | Whether a character may begin a source identifier. Exported so
-- presentation lowering uses the lexer’s exact Unicode-aware boundary rather
-- than maintaining a second classifier.
isIdentStart :: Char -> Bool
isIdentStart c = isAlpha c || c == '_'

isIdentChar :: Char -> Bool
isIdentChar c = isAlpha c || isDigit c || c == '_' || c == '-'

isDigestChar :: Char -> Bool
isDigestChar c = isAlpha c || isDigit c || c `elem` ("._-" :: String)

-- | A source reference in ref-list mode: any run that is not a comma, a closing
-- bracket, or whitespace. @\'#\'@ is an ordinary character here (grammar §1.2).
isSourceRefChar :: Char -> Bool
isSourceRefChar c =
  c /= ',' && c /= ']' && c /= ' ' && c /= '\t' && c /= '\n' && c /= '\r'

-- | Consume trivia according to the parser's current lexical mode.
skipTrivia :: P ()
skipTrivia = do
  mode <- P $ \s -> Right (psTriviaMode s, s)
  _ <- takeWhileP isSpaceChar
  s <- getInput
  case (mode, s) of
    (NormalTrivia, '#' : _) -> do
      _ <- takeWhileP (/= '\n')
      skipTrivia
    _ -> pure ()
  where
    isSpaceChar c = c == ' ' || c == '\t' || c == '\n' || c == '\r'

-- | Ref-list-mode trivia: whitespace only, so @\'#\'@ stays literal.
skipWs :: P ()
skipWs = () <$ takeWhileP (\c -> c == ' ' || c == '\t' || c == '\n' || c == '\r')

-- | Pure lookahead for an identifier (does not consume).
scanIdent :: String -> Maybe String
scanIdent (c : cs)
  | isIdentStart c = Just (c : takeWhile isIdentChar cs)
scanIdent _ = Nothing

-- | Peek the next identifier without consuming payload (trivia is skipped).
peekIdent :: P (Maybe String)
peekIdent = do
  skipTrivia
  scanIdent <$> getInput

-- | Peek the next non-trivia character.
peekChar :: P (Maybe Char)
peekChar = do
  skipTrivia
  s <- getInput
  pure $ case s of
    c : _ -> Just c
    [] -> Nothing

identifier :: P String
identifier = do
  skipTrivia
  s <- getInput
  case s of
    c : _ | isIdentStart c -> takeWhileP isIdentChar
    _ -> failP "expected an identifier"

-- | An identifier that must equal the given keyword.
keyword :: String -> P ()
keyword kw = do
  mw <- peekIdent
  case mw of
    Just w | w == kw -> () <$ identifier
    _ -> failP ("expected keyword '" ++ kw ++ "'")

-- | Consume a single punctuation character.
symbol :: Char -> P ()
symbol c = do
  skipTrivia
  s <- getInput
  case s of
    x : _ | x == c -> advanceP
    _ -> failP ("expected '" ++ [c] ++ "'")

-- | A double-quoted single-line string (grammar §1.3; no escapes).
stringLit :: P String
stringLit = do
  skipTrivia
  s <- getInput
  case s of
    '"' : _ -> do
      advanceP
      body <- takeWhileP (\c -> c /= '"' && c /= '\n')
      s' <- getInput
      case s' of
        '"' : _ -> body <$ advanceP
        _ -> failP "unterminated string literal"
    _ -> failP "expected a string literal"

-- | The directive head reserved for premise-cell interpolation.
nlCellDirective :: String
nlCellDirective = "cell"

-- | §7 terminal position markers, reserved from premise-label namespaces.
attackPathTerminalMarkers :: [String]
attackPathTerminalMarkers = ["rule", "leaf"]

-- | An @nl@ string with @lara-syntax\@0.5@'s brace contract (grammar Apps. B.6 and C.5):
--
-- > igap      ::= { " " | "\t" }
-- > hgap      ::= ( " " | "\t" ) igap
-- > directive ::= "{" igap "cell" hgap leafId igap "}"
-- >             | "{" igap valueName igap "}"
--
-- Inside an @nl@ string @{{@ and @}}@ denote literal braces (the f-string
-- convention this surface's audience already knows) and __any other @{@ must
-- open a recognized directive__: either @{cell \<leafId\>}@ or a one-token
-- value reference. Inline spaces and tabs around either form are retained in
-- the raw body. An unknown multi-token directive, a bare @}@, or an
-- unterminated brace is a /located/ parse error. This is strict rather than
-- lenient on purpose: if @{cel e2}@ (a typo) silently stayed literal text, a
-- number the author believed was auto-synced would be frozen prose — the exact
-- prose↔formal staleness the feature exists to kill.
--
-- The result is the __raw__ body: directives are not expanded and @{{@\/@}}@
-- are not converted, so the printer emits the authored bytes back and
-- @parse ∘ print = id@ holds on the spelling. Interpolation is the elaborator's
-- job, which is also where names are resolved and premise cells are checked.
--
-- Every claim-form @nl@ field uses this contract: both §3's ordinary
-- @claim@ declaration and App. B.3's nested @claims@ block. Binding
-- @rationale@ remains the escape-free 'stringLit' of grammar §1.3.
nlStringLit :: P String
nlStringLit = do
  skipTrivia
  s0 <- getInput
  case s0 of
    '"' : _ -> do
      advanceP
      go ""
    _ -> failP "expected a string literal"
  where
    go acc = do
      s <- getInput
      case s of
        [] -> failP "unterminated string literal"
        '\n' : _ -> failP "unterminated string literal"
        '"' : _ -> reverse acc <$ advanceP
        '{' : '{' : _ -> do advanceP; advanceP; go ('{' : '{' : acc)
        '}' : '}' : _ -> do advanceP; advanceP; go ('}' : '}' : acc)
        '}' : _ ->
          failP "unmatched '}' in nl string (write '}}' for a literal brace)"
        '{' : _ -> do
          raw <- directive
          go (reverse raw ++ acc)
        c : _ -> do advanceP; go (c : acc)
    directive = do
      advanceP -- the opening '{'
      leadingGap <- takeWhileP isInlineSpace
      s <- getInput
      name <- case s of
        c : _ | isIdentStart c -> takeWhileP isIdentChar
        _ ->
          failP
            "expected a directive after '{' in nl string (write '{{' for a literal brace)"
      gap <- takeWhileP isInlineSpace
      if name == nlCellDirective
        then do
          s' <- getInput
          arg <- case s' of
            c : _ | isIdentStart c -> takeWhileP isIdentChar
            _ -> failP "expected a leaf id in a '{cell …}' nl directive"
          trailingGap <- takeWhileP isInlineSpace
          s'' <- getInput
          case s'' of
            '}' : _ -> ("{" ++ leadingGap ++ name ++ gap ++ arg ++ trailingGap ++ "}") <$ advanceP
            _ -> failP "unterminated '{cell …}' nl directive (expected '}')"
        else do
          s' <- getInput
          case s' of
            '}' : _ -> ("{" ++ leadingGap ++ name ++ gap ++ "}") <$ advanceP
            _ -> failP ("unknown nl directive '" ++ name ++ "' (expected a one-token value reference or '{" ++ nlCellDirective ++ " <leaf>}')")
    isInlineSpace c = c == ' ' || c == '\t'

-- | A numeric literal @[+|-] digit+ [ . digit+ ]@ (grammar §1.3).
numberLit :: P String
numberLit = do
  skipTrivia
  sgn <- signPart
  ds <- takeWhileP isDigit
  if null ds
    then failP "expected a number"
    else do
      fr <- fracPart
      pure (sgn ++ ds ++ fr)
  where
    signPart = do
      s <- getInput
      case s of
        c : _ | c == '+' || c == '-' -> (: []) c <$ advanceP
        _ -> pure ""
    fracPart = do
      s <- getInput
      case s of
        '.' : d : _ | isDigit d -> do
          advanceP
          ds <- takeWhileP isDigit
          pure ('.' : ds)
        _ -> pure ""

-- | A digest @ident : digestBody@ (grammar §1.3), e.g. @sha256:aaaa...@.
digestLit :: P Digest
digestLit = do
  h <- identifier
  symbol ':'
  body <- takeWhileP isDigestChar
  if null body
    then failP "expected a digest body"
    else pure (Digest (h ++ ":" ++ body))

-- | Bracketed comma-separated list (normal mode): @[ p , … ]@, possibly empty.
brackets :: P a -> P [a]
brackets p = do
  symbol '['
  c <- peekChar
  case c of
    Just ']' -> [] <$ symbol ']'
    _ -> do
      xs <- commaSep1 p
      symbol ']'
      pure xs

-- | Parenthesised comma-separated list: @( p , … )@, possibly empty.
parenList :: P a -> P [a]
parenList p = do
  symbol '('
  c <- peekChar
  case c of
    Just ')' -> [] <$ symbol ')'
    _ -> do
      xs <- commaSep1 p
      symbol ')'
      pure xs

commaSep1 :: P a -> P [a]
commaSep1 p = do
  x <- p
  go [x]
  where
    go acc = do
      c <- peekChar
      case c of
        Just ',' -> do
          symbol ','
          y <- p
          go (acc ++ [y])
        _ -> pure acc -- already in source order

eof :: P ()
eof = do
  skipTrivia
  s <- getInput
  case s of
    [] -> pure ()
    _ -> failP "expected end of input"

-- ---------------------------------------------------------------------------
-- Fixed vocabulary tables (one spelling per constructor; grammar §1.4)
-- ---------------------------------------------------------------------------

-- | Parse one of a table of @ident@ spellings; fail with the field name.
enumFromTable :: String -> [(String, a)] -> P a
enumFromTable what tbl = do
  w <- identifier
  case lookup w tbl of
    Just a -> pure a
    Nothing -> failP ("expected " ++ what)

modeTable :: [(String, Mode)]
modeTable = [("strict", Strict), ("defeasible", Defeasible)]

leafKindTable :: [(String, LeafKind)]
leafKindTable =
  [ ("observed", Observed)
  , ("attested", Attested)
  , ("assumed", Assumed)
  , ("certified", Certified)
  ]

auditStatusTable :: [(String, AuditStatus)]
auditStatusTable =
  [("unreviewed", Unreviewed), ("reviewed", Reviewed), ("disputed", Disputed)]

necessityTable :: [(String, Necessity)]
necessityTable = [("mandatory", Mandatory), ("optional", Optional)]

admissionTable :: [(String, Admission)]
admissionTable =
  [("admit", Admit), ("quarantine", Quarantine), ("reject", Reject)]

boolTable :: [(String, Bool)]
boolTable = [("true", True), ("false", False)]

-- | Duplicate-report-group conflict outcome (spec §4.3): the @duplicate-reports@
-- policy setting.
groupModeTable :: [(String, GroupConflictMode)]
groupModeTable =
  [("quarantine", QuarantineOnConflict), ("reject", RejectOnConflict)]

-- | Measurand polarity (grammar App. B.1, B.7).
polarityTable :: [(String, Polarity)]
polarityTable =
  [("higher-is-better", HigherIsBetter), ("lower-is-better", LowerIsBetter)]

-- | Comparison relation (grammar App. B.2, B.3, B.7).
relationTable :: [(String, Relation)]
relationTable =
  [("strictly-better", StrictlyBetter), ("at-least-as-good", AtLeastAsGood)]


-- | Reverse table lookup for canonical printing (constructors are unique).
tableToString :: (Eq a) => [(String, a)] -> a -> String
tableToString tbl a = case [s | (s, b) <- tbl, b == a] of
  (s : _) -> s
  [] -> "" -- unreachable: every constructor is in its table

modeStr :: Mode -> String
modeStr = tableToString modeTable

leafKindStr :: LeafKind -> String
leafKindStr = tableToString leafKindTable

auditStatusStr :: AuditStatus -> String
auditStatusStr = tableToString auditStatusTable

necessityStr :: Necessity -> String
necessityStr = tableToString necessityTable

admissionStr :: Admission -> String
admissionStr = tableToString admissionTable

boolStr :: Bool -> String
boolStr = tableToString boolTable

groupModeStr :: GroupConflictMode -> String
groupModeStr = tableToString groupModeTable

polarityStr :: Polarity -> String
polarityStr = tableToString polarityTable

relationStr :: Relation -> String
relationStr = tableToString relationTable

-- | @sort ::= \"Num\" | \"Str\" | ident@ (grammar §4.0). An identifier that is
-- not a base-sort spelling is a declared sort; whether it was declared is
-- Σ-well-formedness, decided by the checker, not by the parser.
sortP :: P Sort
sortP = sortFromText <$> identifier

-- | Provenance is a small closed vocabulary with one compound form,
-- @checker(name, version)@ (grammar §1.4).
provenanceP :: P Provenance
provenanceP = do
  w <- identifier
  case w of
    "user" -> pure User
    "ai-executed" -> pure AiExecuted
    "checker" -> do
      symbol '('
      name <- identifier
      symbol ','
      ver <- identifier
      symbol ')'
      pure (Checker name ver)
    _ -> failP "expected provenance (user | ai-executed | checker(name, version))"

provenanceStr :: Provenance -> String
provenanceStr p = case p of
  User -> "user"
  AiExecuted -> "ai-executed"
  Checker name ver -> "checker(" ++ name ++ ", " ++ ver ++ ")"

-- ---------------------------------------------------------------------------
-- Shared sub-grammars: terms, propositions, patterns (grammar §2)
-- ---------------------------------------------------------------------------

-- | @term ::= number | ident | ident \"(\" term,… \")\"@.
termP :: P Term
termP = do
  c <- peekChar
  case c of
    Just ch
      | ch == '+' || ch == '-' || isDigit ch -> TNum <$> numberLit
      | isIdentStart ch -> do
          h <- identifier
          next <- peekChar
          case next of
            Just '(' -> TCon (FunSym h) <$> parenList termP
            _ -> pure (TCon (FunSym h) [])
    _ -> failP "expected a term"

-- | @prop ::= pred [ \"(\" term,… \")\" ]@.
propP :: P Prop
propP = do
  h <- identifier
  next <- peekChar
  case next of
    Just '(' -> Prop (Pred h) <$> parenList termP
    _ -> pure (Prop (Pred h) [])

-- | Parse one complete surface proposition (the same @prop@ production used by
-- @formal@\/@leaf@\/@theory@ lines), for callers that receive a proposition
-- spelling outside a source file — notably the @nd\@1@ named formula
-- annotation @(prop TEXT)@ (grammar App. I), whose carrier atom decodes to
-- exactly this production. Surrounding whitespace is tolerated, while @\#@
-- remains literal and therefore fails as trailing input rather than silently
-- truncating the authored proposition.
parseProp :: String -> Either ParseError Prop
parseProp = runCompleteWith WhitespaceOnlyTrivia (propP <* eof)

-- | @pat ::= number | ident | ident \"(\" pat,… \")\"@. A bare identifier is
-- recorded as 'PVar'; the elaborator reclassifies it to a ground literal when
-- it is not one of the enclosing rule's parameters (grammar §2).
patP :: P Pat
patP = do
  c <- peekChar
  case c of
    Just ch
      | ch == '+' || ch == '-' || isDigit ch -> PLit . TNum <$> numberLit
      | isIdentStart ch -> do
          h <- identifier
          next <- peekChar
          case next of
            Just '(' -> PCon (FunSym h) <$> parenList patP
            _ -> pure (PVar (Param h))
    _ -> failP "expected a pattern"

-- | @apat ::= pred [ \"(\" pat,… \")\" ]@.
apatP :: P AtomPat
apatP = do
  h <- identifier
  next <- peekChar
  case next of
    Just '(' -> AtomPat (Pred h) <$> parenList patP
    _ -> pure (AtomPat (Pred h) [])

-- ---------------------------------------------------------------------------
-- Artifact program (grammar §3)
-- ---------------------------------------------------------------------------

-- | Parse an artifact @Program@ from @.lara@ source text.
parseProgram :: String -> Either ParseError Program
parseProgram = runComplete (programP <* eof)

programP :: P Program
programP = do
  keyword "artifact"
  name <- identifier
  keyword "at"
  dig <- digestLit
  keyword "policy"
  pid <- identifier
  keyword "use"
  keyword "backends"
  bes <- brackets backendRefP
  vbs <- valueBindingsP
  ds <- declsP
  pure
    Program
      { programArtifact = name
      , programDigest = dig
      , programPolicy = PolicyId pid
      , programBackends = bes
      , programValueBindings = vbs
      , programDecls = ds
      }

-- | Parse the ordered @let@ table between the fixed header and declarations
-- (grammar App. C.1). Duplicate names are rejected at their second declaration.
valueBindingsP :: P [ValueBinding]
valueBindingsP = go Set.empty []
  where
    go seen acc = do
      mw <- peekIdent
      case mw of
        Just "let" -> do
          bindingPos <- getPosition
          binding <- valueBindingP
          let name = valueName binding
          if name `Set.member` seen
            then
              failAtP bindingPos
                ( "duplicate value binding: "
                    ++ let ValueName raw = name in raw
                )
            else go (Set.insert name seen) (binding : acc)
        _ -> pure (reverse acc)

-- | @valueBinding ::= "let" valueName "=" term@ (grammar App. C.1).
valueBindingP :: P ValueBinding
valueBindingP = do
  keyword "let"
  rawName <- identifier
  if rawName == nlCellDirective
    then failP "'cell' is reserved and cannot be used as a value binding name"
    else do
      symbol '='
      ValueBinding (ValueName rawName) <$> termP

-- | @backendRef ::= ident \"@\" (number | ident)@ → @(BackendId, version)@,
-- version kept as a surface string (grammar §1.3).
backendRefP :: P (BackendId, String)
backendRefP = do
  b <- identifier
  symbol '@'
  ver <- versionToken
  pure (BackendId b, ver)

-- | The version half of a backend reference: a number or a bare identifier.
versionToken :: P String
versionToken = do
  c <- peekChar
  case c of
    Just ch
      | ch == '+' || ch == '-' || isDigit ch -> numberLit
      | isIdentStart ch -> identifier
    _ -> failP "expected a backend version"

-- | The leading keywords that open a top-level @decl@ (grammar §3).
declKeywords :: [String]
declKeywords =
  [ "claim", "leaf", "arg", "rebut", "undercut", "undermine", "status", "group"
  , "comparison" -- lara-syntax@0.3, grammar App. B.3
  ]

-- | Zero-or-more @decl@s in declaration order, stopping at the first token that
-- is not a declaration keyword. Once a keyword is seen the declaration is parsed
-- committed, so a malformed declaration reports its own located error rather
-- than being silently backtracked past.
declsP :: P [Decl]
declsP = go []
  where
    go acc = do
      mw <- peekIdent
      case mw of
        Just k | k `elem` declKeywords -> do d <- declP; go (acc ++ [d])
        Just "let" ->
          failP "value binding declarations must precede all program declarations"
        _ -> pure acc

declP :: P Decl
declP = do
  mw <- peekIdent
  case mw of
    Just "claim" -> DeclClaim <$> claimP
    Just "leaf" -> DeclLeaf <$> leafP
    Just "arg" -> DeclArg <$> argP
    Just "rebut" -> DeclAttack <$> attackP
    Just "undercut" -> DeclAttack <$> attackP
    Just "undermine" -> DeclAttack <$> attackP
    Just "status" -> do
      keyword "status"
      DeclStatus . PropId <$> identifier
    Just "group" -> DeclGroup <$> groupP
    Just "comparison" -> DeclComparison <$> comparisonP
    _ -> failP "expected a declaration (claim | leaf | arg | rebut | undercut | undermine | status | group | comparison)"

claimP :: P Claim
claimP = do
  keyword "claim"
  cid <- identifier
  keyword "nl"
  symbol '='
  nl <- nlStringLit
  keyword "formal"
  symbol '='
  formal <- propP
  keyword "binding"
  symbol '='
  b <- bindingP
  pure
    Claim
      { claimId = PropId cid
      , claimNl = nl
      , claimFormal = formal
      , claimBinding = b
      }

-- | @binding ::= \"{\" bindingField,… \"}\"@ — order-free; @author@ and
-- @audit-status@ required, @rationale@ optional (grammar §3).
bindingP :: P Binding
bindingP = do
  symbol '{'
  fields <- commaSep1 bindingFieldP
  symbol '}'
  author <- required "author" [a | BFAuthor a <- fields]
  audit <- required "audit-status" [a | BFAudit a <- fields]
  let rat = case [r | BFRationale r <- fields] of
        (r : _) -> r
        [] -> ""
  pure
    Binding
      { bindingAuthor = author
      , bindingRationale = rat
      , bindingAuditStatus = audit
      }
  where
    required nm xs = case xs of
      (x : _) -> pure x
      [] -> failP ("binding is missing required field '" ++ nm ++ "'")

data BindingField
  = BFAuthor String
  | BFRationale String
  | BFAudit AuditStatus

bindingFieldP :: P BindingField
bindingFieldP = do
  mw <- peekIdent
  case mw of
    Just "author" -> do
      keyword "author"; symbol '='; BFAuthor <$> identifier
    Just "rationale" -> do
      keyword "rationale"; symbol '='; BFRationale <$> stringLit
    Just "audit-status" -> do
      keyword "audit-status"
      symbol '='
      BFAudit <$> enumFromTable "an audit status" auditStatusTable
    _ -> failP "expected a binding field (author | rationale | audit-status)"

leafP :: P Leaf
leafP = do
  keyword "leaf"
  lid <- identifier
  symbol ':'
  p <- propP
  keyword "kind"
  symbol '='
  k <- enumFromTable "a leaf kind" leafKindTable
  keyword "provenance"
  symbol '='
  prov <- provenanceP
  keyword "refs"
  symbol '='
  refs <- refsListP
  pure
    Leaf
      { leafId = LeafId lid
      , leafProp = p
      , leafKind = k
      , leafProvenance = prov
      , leafRefs = refs
      }

-- | @group ident = [ leafId,… ]@ (grammar §3): a duplicate-report group over
-- declared leaf ids (spec §4.3). The named id lets an R9 data-integrity
-- diagnostic locate the group declaration.
groupP :: P DupGroup
groupP = do
  keyword "group"
  gid <- identifier
  symbol '='
  members <- brackets (LeafId <$> identifier)
  pure (DupGroup (GroupId gid) members)

-- | @comparisonBlock@ (grammar App. B.3), the @lara-syntax\@0.3@ comparative
-- declaration:
--
-- > comparison ":" prop "on" ident "@" ident
-- >   "relation" "=" relation
-- >   "recheck"  "=" argId      "bridge"   "=" argId
-- >   "result"   "=" leafId     "baseline" "=" leafId
-- >   "binding"  "=" leafId
-- >   "claims" propId  "nl" "=" nlString  "binding" "=" binding
-- >   [ "supports" propId ]
--
-- Field order is fixed by the grammar, which is what keeps the two @binding@
-- lines — the evidence leaf and the sub-claim's attestation block —
-- unambiguous. This parser is /shallow/ in the same sense as the rest of the
-- module: it records the surface and leaves scheme lookup, goal generation, and
-- every B.3 well-formedness check to the elaborator.
comparisonP :: P Comparison
comparisonP = do
  keyword "comparison"
  symbol ':'
  concl <- propP
  keyword "on"
  m <- identifier
  symbol '@'
  d <- identifier
  keyword "relation"
  symbol '='
  rel <- enumFromTable "a relation (strictly-better | at-least-as-good)" relationTable
  recheckArg <- field "recheck"
  bridgeArg <- field "bridge"
  result <- field "result"
  baseline <- field "baseline"
  bindingLeaf <- field "binding"
  keyword "claims"
  cid <- identifier
  keyword "nl"
  symbol '='
  nl <- nlStringLit
  keyword "binding"
  symbol '='
  b <- bindingP
  sup <- optSupports
  pure
    Comparison
      { cmpConclusion = concl
      , cmpMeasurand = MeasurandId m
      , cmpDataset = DatasetId d
      , cmpRelation = rel
      , cmpRecheckArg = ArgId recheckArg
      , cmpBridgeArg = ArgId bridgeArg
      , cmpResult = LeafId result
      , cmpBaseline = LeafId baseline
      , cmpBinding = LeafId bindingLeaf
      , cmpClaim =
          ComparisonClaim {ccId = PropId cid, ccNlRaw = nl, ccBinding = b}
      , cmpSupports = sup
      }
  where
    field kw = do keyword kw; symbol '='; identifier
    optSupports = do
      mw <- peekIdent
      case mw of
        Just "supports" -> do
          keyword "supports"
          Just . PropId <$> identifier
        _ -> pure Nothing

-- | @refs = [ sourceRef,… ]@, lexed in ref-list mode: @\'#\'@ is literal and
-- comment recognition is suspended inside the brackets (grammar §1.2).
refsListP :: P [SourceRef]
refsListP = do
  symbol '['
  refs <- go []
  pure refs
  where
    go acc = do
      skipWs
      s <- getInput
      case s of
        ']' : _ -> reverse acc <$ advanceP
        [] -> failP "unterminated refs list (missing ']')"
        ',' : _ -> do advanceP; go acc
        _ -> do
          ref <- takeWhileP isSourceRefChar
          if null ref
            then failP "malformed source reference in refs list"
            else go (SourceRef ref : acc)

-- | @arg ::= \"arg\" ident \":\" argConcl \"by\" supportTerm { dischargeLine |
-- openLine }@ (grammar §3, §5), where
-- @supportTerm ::= \"leaf\" \"(\" leafId \")\" | ruleId \"(\" termList? \")\" |
-- ruleId \"from\" \"[\" argRefList? \"]\"@. Discharges\/open lines fold into the
-- complete 'ArgInstantiation'.
argP :: P Arg
argP = do
  keyword "arg"
  aid <- identifier
  symbol ':'
  concl <- argConclP
  keyword "by"
  instantiation <- supportTermP
  instantiation' <- argBody instantiation
  pure
    Arg
      { argId = ArgId aid
      , argConcl = concl
      , argInstantiation = instantiation'
      }

argConclP :: P ArgConcl
argConclP = do
  mw <- peekIdent
  case mw of
    Just "supports" -> do
      keyword "supports"
      symbol '('
      c <- identifier
      symbol ')'
      -- The parser cannot know whether @c@ is a declared claim; it records the
      -- surface form as 'SupportsClaim' and the elaborator downgrades an
      -- undeclared target to 'SupportsDerived' (grammar §6).
      pure (SupportsClaim (PropId c))
    Just "challenges" -> do
      keyword "challenges"
      symbol '('
      t <- challengeTargetP
      symbol ')'
      pure (Challenges t)
    _ -> failP "expected an argument conclusion (supports(…) | challenges(…))"

challengeTargetP :: P ChallengeTarget
challengeTargetP = do
  x <- identifier
  next <- peekChar
  case next of
    Just '(' -> do
      symbol '('
      u <- identifier
      symbol ')'
      pure (ChallengesQuestion (QuestionId x) (ArgId u))
    _ -> pure (ChallengesLeaf (LeafId x))

-- | The support payload of a @by@ clause (grammar §3, §5):
-- @leaf(l)@, @ruleId (termList?)@, or
-- @ruleId \"from\" \"[\" argRefList? \"]\"@. Discharges\/holes are folded into
-- the complete 'ArgInstantiation'.
supportTermP :: P ArgInstantiation
supportTermP = do
  h <- identifier
  if h == "leaf"
    then do
      symbol '('
      l <- identifier
      symbol ')'
      pure (ExplicitTheta (SLeaf (LeafId l)))
    else do
      next <- peekIdent
      case next of
        Just "from" -> inferredRuleP (RuleId h)
        _ -> explicitRuleP (RuleId h)

explicitRuleP :: RuleId -> P ArgInstantiation
explicitRuleP rid = do
  terms <- parenList termP
  let theta = zipWith (\i t -> (Param (show i), t)) [1 :: Int ..] terms
  pure
    ( ExplicitTheta
        SRule
          { srRule = rid
          , srSubst = theta
          , srPremises = []
          , srDischarge = []
          , srHoles = []
          , srAssurance = AssuranceNone
          }
    )

inferredRuleP :: RuleId -> P ArgInstantiation
inferredRuleP rid = do
  keyword "from"
  refs <- brackets (ArgRef <$> identifier)
  pure (InferTheta rid refs [] [] AssuranceNone)

-- | Fold @discharge@\/@open@\/@assurance@ lines into the support payload.
--
-- @\@0.7@: every body line must reach the AST or be rejected. A
-- @discharge@ or @open@ line under a bare @leaf(…)@ has nothing to attach to,
-- so it is a /located/ parse error at the keyword — the same ruling App. A.1
-- already makes for @assurance@. 'peekIdent' has consumed the preceding
-- trivia, so 'getPosition' here is the keyword's own line\/column.
--
-- @\@0.7@: a hole is spelled @open q@ and nothing else. A trailing
-- @as …@ is the retired @\@0.6@ spelling and is reported with its repair.
argBody :: ArgInstantiation -> P ArgInstantiation
argBody base = go base False
  where
    go acc seenAssurance = do
      mw <- peekIdent
      pos <- getPosition
      case mw of
        Just "discharge" -> do
          keyword "discharge"
          q <- identifier
          keyword "with"
          ref <- identifier
          case addArgDischarge acc (QuestionId q) (ArgRef ref) of
            Left msg -> failAtP pos msg
            Right acc' -> go acc' seenAssurance
        Just "open" -> do
          keyword "open"
          o <- identifier
          suffix <- peekIdent
          case suffix of
            Just "as" -> failP "lara-syntax@0.7 uses 'open q'; remove 'as …'"
            _ -> case addArgHole acc (ObligationId o) of
              Left msg -> failAtP pos msg
              Right acc' -> go acc' seenAssurance
        Just "assurance" ->
          if seenAssurance
            then failP "duplicate assurance line in arg block"
            else case acc of
              -- Rejected before 'assuranceP' runs, so a bare leaf reports its
              -- own ruling rather than a malformed-value error underneath it.
              ExplicitTheta (SLeaf _) ->
                failAtP pos "assurance requires a rule application, not a bare leaf"
              _ -> do
                assurance <- assuranceP
                case setArgAssurance acc assurance of
                  Left msg -> failAtP pos msg
                  Right acc' -> go acc' True
        _ -> pure acc

-- | Attach a @discharge@ line, or say why it cannot attach. The three
-- equations are the three 'ArgInstantiation' shapes, so the function is total
-- without a catch-all: a caller cannot re-create the dropped-line bug by
-- falling through.
addArgDischarge
  :: ArgInstantiation -> QuestionId -> ArgRef -> Either String ArgInstantiation
addArgDischarge (ExplicitTheta (SRule r th pr ds hs as)) q (ArgRef ref) =
  Right (ExplicitTheta (SRule r th pr (ds ++ [(q, SLeaf (LeafId ref))]) hs as))
addArgDischarge (InferTheta r refs ds hs as) q ref =
  Right (InferTheta r refs (ds ++ [(q, ref)]) hs as)
addArgDischarge (ExplicitTheta (SLeaf _)) _ _ =
  Left "discharge requires a rule application, not a bare leaf"

-- | Attach an @open@ hole, or say why it cannot attach (see 'addArgDischarge'
-- for why there is no catch-all equation).
addArgHole :: ArgInstantiation -> ObligationId -> Either String ArgInstantiation
addArgHole (ExplicitTheta (SRule r th pr ds hs as)) o =
  Right (ExplicitTheta (SRule r th pr ds (hs ++ [o]) as))
addArgHole (InferTheta r refs ds hs as) o =
  Right (InferTheta r refs ds (hs ++ [o]) as)
addArgHole (ExplicitTheta (SLeaf _)) _ =
  Left "open requires a rule application, not a bare leaf"

-- | Attach an @assurance@ value, or say why it cannot attach (see
-- 'addArgDischarge' for why there is no catch-all equation).
--
-- @argBody@ rejects the bare-leaf shape before parsing the value, so this
-- @Left@ is not the reporting path in practice. It is here because App. A.1's
-- ruling must not depend on a parser-side convention any more than the
-- dropped-line ruling's does: with a silent @inst@ fall-through, a future
-- caller reaching this helper directly would drop the author's @assurance@
-- exactly the way
-- 'addArgDischarge' used to drop a @discharge@.
setArgAssurance
  :: ArgInstantiation -> Assurance -> Either String ArgInstantiation
setArgAssurance (ExplicitTheta (SRule r th pr ds hs _)) assurance =
  Right (ExplicitTheta (SRule r th pr ds hs assurance))
setArgAssurance (InferTheta r refs ds hs _) assurance =
  Right (InferTheta r refs ds hs assurance)
setArgAssurance (ExplicitTheta (SLeaf _)) _ =
  Left "assurance requires a rule application, not a bare leaf"

-- | @attackDecl@ / @posTarget@ (grammar §3, §7), producing the /presentation/
-- 'SurfaceAttack': positions keep the spelling they were authored in (grammar
-- §7 AMENDMENT, App. B.5) and the elaborator resolves them to the frozen
-- 'Attack' once the policy — and hence the target rule's premise labels — is in
-- hand.
attackP :: P SurfaceAttack
attackP = do
  mw <- peekIdent
  case mw of
    Just "rebut" -> do
      keyword "rebut"
      w <- identifier
      u <- identifier
      pure (SRebut (ArgId w) (ArgId u))
    Just "undercut" -> do
      keyword "undercut"
      w <- identifier
      (u, steps) <- posTargetP "rule"
      pure (SUndercut (ArgId w) u steps)
    Just "undermine" -> do
      keyword "undermine"
      w <- identifier
      (u, steps) <- posTargetP "leaf"
      pure (SUndermine (ArgId w) u steps)
    _ -> failP "expected an attack (rebut | undercut | undermine)"

-- | @posTarget ::= ident { \".\" step } \".\" marker@ where @marker@ is the
-- fixed terminal for the attack kind (@rule@ for undercut, @leaf@ for
-- undermine). Returns the base argument and the authored @['SurfaceStep']@
-- (grammar §7, App. B.5).
--
-- Segment classification is purely lexical and unchanged from @\@0.2@ in
-- effect: an all-digits segment is a 'StepIndex' (which lowers to
-- 'StepPremise'), anything else a 'StepName' (which @\@0.2@ could only resolve
-- to a 'QuestionId', and @\@0.3@ resolves to a premise label /or/ a question
-- id). The terminal-marker rule is untouched.
posTargetP :: String -> P (ArgId, [SurfaceStep])
posTargetP marker = do
  u <- identifier
  segs <- dotSegments
  case reverse segs of
    (lastSeg : revSteps)
      | lastSeg == marker -> pure (ArgId u, map toStep (reverse revSteps))
      | otherwise ->
          failP ("expected terminal '." ++ marker ++ "' on attack position, found '." ++ lastSeg ++ "'")
    [] -> failP ("expected a '." ++ marker ++ "' marker on the attack position")
  where
    toStep s
      | not (null s) && all isDigit s = StepIndex (read s)
      | otherwise = StepName s

-- | One-or-more @\".\" segment@ groups (each segment an integer or an ident).
dotSegments :: P [String]
dotSegments = do
  skipTrivia
  s <- getInput
  case s of
    '.' : _ -> do
      advanceP
      seg <- segmentTok
      rest <- moreSegments
      pure (seg : rest)
    _ -> failP "expected a '.'-delimited attack position"
  where
    moreSegments = do
      skipTrivia
      s <- getInput
      case s of
        '.' : _ -> do
          advanceP
          seg <- segmentTok
          rest <- moreSegments
          pure (seg : rest)
        _ -> pure []
    segmentTok = do
      s <- getInput
      case s of
        c : _ | isDigit c -> takeWhileP isDigit
        c : _ | isIdentStart c -> takeWhileP isIdentChar
        _ -> failP "expected a premise index or question id in the attack position"

-- ---------------------------------------------------------------------------
-- Policy (grammar §4)
-- ---------------------------------------------------------------------------

-- | Parse a @Policy@ from @.policy.lara@ source text.
parsePolicy :: String -> Either ParseError Policy
parsePolicy = runComplete (policyP <* eof)

-- | Accumulator for policy declarations, which the grammar allows in any order
-- but which the AST partitions by kind (grammar §4).
data PolicyAcc
  = PolicyAcc Sigma [Rule] [Contrary] [Exception]
      [((LeafKind, Provenance), Admission)] [(TheoryDigest, [Prop])]
      GroupConflictMode [Measurand] [ComparisonScheme]

policyP :: P Policy
policyP = do
  keyword "policy"
  pid <- identifier
  PolicyAcc sg rs cs es adm ts gm ms schs <-
    policyDecls (PolicyAcc emptySigma [] [] [] [] [] QuarantineOnConflict [] [])
  pure
    Policy
      { policyId = PolicyId pid
      , policySigma = sg
      , policyRules = rs
      , policyContraries = cs
      , policyExceptions = es
      , policyAdmission = adm
      , policyTheories = ts
      , policyGroupMode = gm
      , policyMeasurands = ms
      , policyComparisonSchemes = schs
      }

policyDecls :: PolicyAcc -> P PolicyAcc
policyDecls acc@(PolicyAcc sg rs cs es adm ts gm ms schs) = do
  mw <- peekIdent
  case mw of
    -- The signature blocks (grammar §4.0). Duplicate detection is Σ
    -- well-formedness, decided by the checker as R2 — the parser is a decode
    -- boundary and records what was written, exactly as it does for a rule id
    -- declared twice.
    Just "sort" -> do
      ns <- sortLineP
      policyDecls (PolicyAcc sg{sigmaSorts = sigmaSorts sg ++ ns} rs cs es adm ts gm ms schs)
    Just "con" -> do
      c <- conLineP
      policyDecls (PolicyAcc sg{sigmaCons = sigmaCons sg ++ [c]} rs cs es adm ts gm ms schs)
    Just "pred" -> do
      pr <- predLineP
      policyDecls (PolicyAcc sg{sigmaPreds = sigmaPreds sg ++ [pr]} rs cs es adm ts gm ms schs)
    Just "rule" -> do r <- ruleP; policyDecls (PolicyAcc sg (rs ++ [r]) cs es adm ts gm ms schs)
    Just "contrary" -> do c <- contraryP; policyDecls (PolicyAcc sg rs (cs ++ [c]) es adm ts gm ms schs)
    Just "exception" -> do e <- exceptionP; policyDecls (PolicyAcc sg rs cs (es ++ [e]) adm ts gm ms schs)
    Just "admission" -> do a <- admissionP; policyDecls (PolicyAcc sg rs cs es (adm ++ a) ts gm ms schs)
    Just "duplicate-reports" -> do
      keyword "duplicate-reports"
      symbol '='
      gm' <- enumFromTable "a group conflict mode (quarantine | reject)" groupModeTable
      policyDecls (PolicyAcc sg rs cs es adm ts gm' ms schs)
    Just "theory" -> do
      t@(TheoryDigest d, _) <- theoryLineP
      if any (\(TheoryDigest d', _) -> d' == d) ts
        then failP ("duplicate theory digest: " ++ d)
        else policyDecls (PolicyAcc sg rs cs es adm (ts ++ [t]) gm ms schs)
    -- A duplicate measurand is rejected inline, like a duplicate theory digest
    -- and for the same reason (grammar App. B.1): a silent first-wins lookup
    -- would pick a polarity the author did not intend, flipping the generated
    -- goal of every comparison on that measurand.
    Just "measurand" -> do
      m <- measurandLineP
      if any ((== measurandId m) . measurandId) ms
        then failP ("duplicate measurand: " ++ let MeasurandId n = measurandId m in n)
        else policyDecls (PolicyAcc sg rs cs es adm ts gm (ms ++ [m]) schs)
    -- Schemes are keyed by the (relation, polarity) __pair__, so that is the
    -- duplicate key (grammar App. B.2); there are at most four entries.
    Just "comparison-scheme" -> do
      sch <- comparisonSchemeP
      if any (\s -> (csRelation s, csPolarity s) == (csRelation sch, csPolarity sch)) schs
        then
          failP
            ( "duplicate comparison-scheme for "
                ++ relationStr (csRelation sch)
                ++ " "
                ++ polarityStr (csPolarity sch)
            )
        else policyDecls (PolicyAcc sg rs cs es adm ts gm ms (schs ++ [sch]))
    _ -> pure acc

-- | @sortLine ::= \"sort\" ident { \",\" ident }@ (grammar §4.0).
sortLineP :: P [SortName]
sortLineP = do
  keyword "sort"
  commaSep1 (SortName <$> identifier)

-- | @conLine ::= \"con\" ident [ \"(\" sort { \",\" sort } \")\" ] \":\" sort@
-- (grammar §4.0). A nullary constant is spelled without parentheses — the one
-- canonical spelling, so @parse ∘ print = id@ holds.
conLineP :: P ConSig
conLineP = do
  keyword "con"
  k <- identifier
  args <- optionalSortArgs
  symbol ':'
  res <- sortP
  pure (ConSig (FunSym k) args res)

-- | @predLine ::= \"pred\" ident [ \"(\" sort { \",\" sort } \")\" ]@
-- (grammar §4.0).
predLineP :: P PredSig
predLineP = do
  keyword "pred"
  p <- identifier
  args <- optionalSortArgs
  pure (PredSig (Pred p) args)

-- | An argument-sort vector, absent for a nullary symbol. @()@ parses (the
-- parser is the permissive half) but never prints: the canonical nullary
-- spelling omits the parentheses.
optionalSortArgs :: P [Sort]
optionalSortArgs = do
  c <- peekChar
  if c == Just '(' then parenList sortP else pure []

-- | @measurandLine ::= \"measurand\" ident \":\" sort [ \"where\" polarity ]@
-- (grammar App. B.1).
--
-- The sort slot is open (D-1) — it is a sort position over the same
-- vocabulary the policy's signature declares. The @where@ clause is optional
-- and __@Num@-gated__: it presupposes an ordered domain, and only @Num@ is
-- ordered, so a polarity on a non-@Num@ measurand is rejected here.
measurandLineP :: P Measurand
measurandLineP = do
  keyword "measurand"
  m <- identifier
  symbol ':'
  srt <- sortP
  mw <- peekIdent
  pol <- case mw of
    Just "where" -> do
      keyword "where"
      p <- enumFromTable "a polarity (higher-is-better | lower-is-better)" polarityTable
      pure (Just p)
    _ -> pure Nothing
  case pol of
    Just _
      | srt /= SortNum ->
          failP
            ( "measurand " ++ m ++ " : " ++ sortText srt
                ++ " cannot carry a polarity clause (only Num is ordered)"
            )
    _ -> pure ()
  pure
    Measurand
      {measurandId = MeasurandId m, measurandSort = srt, measurandPolarity = pol}

-- | @schemeBlock ::= \"comparison-scheme\" relation polarity \"recheck\" \"=\"
-- ruleId \"bridge\" \"=\" ruleId@ (grammar App. B.2).
comparisonSchemeP :: P ComparisonScheme
comparisonSchemeP = do
  keyword "comparison-scheme"
  rel <- enumFromTable "a relation (strictly-better | at-least-as-good)" relationTable
  pol <- enumFromTable "a polarity (higher-is-better | lower-is-better)" polarityTable
  keyword "recheck"
  symbol '='
  rec' <- identifier
  keyword "bridge"
  symbol '='
  br <- identifier
  pure
    ComparisonScheme
      { csRelation = rel
      , csPolarity = pol
      , csRecheck = RuleId rec'
      , csBridge = RuleId br
      }

-- | @theoryLine ::= "theory" digest "=" "[" [ prop { "," prop } ] "]"@
-- (grammar App. A.2).
theoryLineP :: P (TheoryDigest, [Prop])
theoryLineP = do
  keyword "theory"
  Digest d <- digestLit
  symbol '='
  ps <- brackets propP
  pure (TheoryDigest d, ps)

ruleP :: P Rule
ruleP = do
  keyword "rule"
  rid <- identifier
  params <- parenList (Param <$> identifier)
  keyword "mode"
  symbol '='
  mode <- enumFromTable "a mode (strict | defeasible)" modeTable
  keyword "premises"
  symbol '='
  labelled <- brackets labelledPremiseP
  let prems = map snd labelled
      rawLabels = map fst labelled
      -- Canonical: @[]@ when no premise is labelled, else one entry per
      -- premise (grammar App. B.4 — labels are optional /per premise/).
      labels = if all (== Nothing) rawLabels then [] else rawLabels
      names = [n | Just (PremiseLabel n) <- rawLabels]
  case firstDupStr names of
    Just n -> failP ("duplicate premise label '" ++ n ++ "' in rule '" ++ rid ++ "'")
    Nothing -> pure ()
  -- @rule@\/@leaf@ are the §7 terminal markers, so a premise label spelling
  -- either of them would make @a2.leaf.leaf@ parse two ways (grammar App. B.4).
  case filter (`elem` attackPathTerminalMarkers) names of
    (n : _) ->
      failP ("premise label '" ++ n ++ "' is reserved (the §7 terminal markers)")
    [] -> pure ()
  keyword "conclusion"
  symbol '='
  concl <- apatP
  at <- optAllowTrusted
  certs <- optCertifiers
  qs <- questionLines
  -- B.4 policy well-formedness, rejected at declaration time rather than
  -- discovered at an attack site: both namespaces are declared right here, so a
  -- label that also names a critical question makes an attack path ambiguous.
  case filter (`elem` [q | Question (QuestionId q) _ _ <- qs]) names of
    (n : _) ->
      failP
        ( "premise label '" ++ n ++ "' in rule '" ++ rid
            ++ "' also names a critical question"
        )
    [] -> pure ()
  pure
    Rule
      { ruleId = RuleId rid
      , ruleParams = params
      , ruleMode = mode
      , rulePremises = prems
      , rulePremiseLabels = labels
      , ruleConclusion = concl
      , ruleAllowTrusted = at
      , ruleCertifiers = certs
      , ruleQuestions = qs
      }
  where
    optAllowTrusted = do
      mw <- peekIdent
      case mw of
        Just "allow-trusted" -> do
          keyword "allow-trusted"
          symbol '='
          enumFromTable "a boolean (true | false)" boolTable
        _ -> pure False
    optCertifiers = do
      mw <- peekIdent
      case mw of
        Just "certifiers" -> do
          keyword "certifiers"
          symbol '='
          brackets certRefP
        _ -> pure []
    questionLines = go []
    go acc = do
      mw <- peekIdent
      case mw of
        Just "question" -> do q <- questionP; go (acc ++ [q])
        _ -> pure acc

-- | @labelledPremise ::= [ ident \":\" ] apat@ (grammar App. B.4). The label is
-- optional per premise; an unlabelled premise behaves exactly as it does in
-- @\@0.2@.
--
-- Disambiguation is a bounded lookahead and cannot be ambiguous: an @apat@'s
-- head ident is followed by @(@, @,@, or @]@ — never by @:@ — so a @:@ after
-- the first ident marks a label. (Like 'peekNecessityParen' the scan skips only
-- whitespace, not comments; a comment between a label and its colon is not
-- accepted.)
labelledPremiseP :: P (Maybe PremiseLabel, AtomPat)
labelledPremiseP = do
  lbl <- optLabel
  a <- apatP
  pure (lbl, a)
  where
    optLabel = do
      skipTrivia
      s <- getInput
      case scanIdent s of
        Just w
          | colonFollows (drop (length w) s) -> do
              _ <- identifier
              symbol ':'
              pure (Just (PremiseLabel w))
        _ -> pure Nothing
    colonFollows r = case dropWhile isWs r of
      ':' : _ -> True
      _ -> False
    isWs c = c == ' ' || c == '\t' || c == '\n' || c == '\r'

-- | The first value occurring twice, in first-duplicate order.
firstDupStr :: [String] -> Maybe String
firstDupStr = go []
  where
    go _ [] = Nothing
    go seen (x : xs) | x `elem` seen = Just x
                     | otherwise = go (x : seen) xs

-- | @questionLine ::= \"question\" ident \":\" apat [ \"(\" necessity \")\" ]@
-- (default @mandatory@; grammar §4).
questionP :: P Question
questionP = do
  keyword "question"
  q <- identifier
  symbol ':'
  a <- questionAnswerP
  nec <- optNecessity
  pure Question {questionId = QuestionId q, questionAnswer = a, questionNecessity = nec}
  where
    optNecessity = do
      c <- peekChar
      case c of
        Just '(' -> do
          symbol '('
          n <- enumFromTable "a necessity (mandatory | optional)" necessityTable
          symbol ')'
          pure n
        _ -> pure Mandatory

-- | The question answer @apat@. Grammar §4's @question q : apat [ \"(\"
-- necessity \")\" ]@ is locally ambiguous when @apat@ is /nullary/: @p
-- (mandatory)@ could read @mandatory@ as @p@'s sole argument. Since @mandatory@
-- \/ @optional@ are the necessity vocabulary, a trailing @( necessity )@ is
-- taken as the necessity suffix, never as the atom's argument list. (Applied
-- answers such as @randomized(Exp)@ — every answer in the reference policy — are
-- unaffected: they carry their own parentheses.)
questionAnswerP :: P AtomPat
questionAnswerP = do
  h <- identifier
  next <- peekChar
  case next of
    Just '(' -> do
      isNec <- peekNecessityParen
      if isNec
        then pure (AtomPat (Pred h) [])
        else AtomPat (Pred h) <$> parenList patP
    _ -> pure (AtomPat (Pred h) [])

-- | Pure lookahead: does the input begin with @( necessity )@?
peekNecessityParen :: P Bool
peekNecessityParen = do
  skipTrivia
  s <- getInput
  pure (scan s)
  where
    isWs c = c == ' ' || c == '\t' || c == '\n' || c == '\r'
    necWords = map fst necessityTable
    scan ('(' : rest0) =
      let rest1 = dropWhile isWs rest0
       in case scanIdent rest1 of
            Just w
              | w `elem` necWords ->
                  case dropWhile isWs (drop (length w) rest1) of
                    ')' : _ -> True
                    _ -> False
            _ -> False
    scan _ = False

-- | @backendRef ::= ident "@" nat@ — shared by 'certRefP' and 'assuranceP'.
backendVersionP :: P (BackendId, Int)
backendVersionP = do
  b <- identifier
  symbol '@'
  v <- natLit
  pure (BackendId b, v)

-- | @certRef ::= \"(\" backendRef \",\" digest \")\"@ (grammar §4). The backend
-- version is a checker-facing NAT here (@CertRef.certRefVersion :: Int@).
certRefP :: P CertRef
certRefP = do
  symbol '('
  (b, v) <- backendVersionP
  symbol ','
  Digest dig <- digestLit
  symbol ')'
  pure (CertRef b v (TheoryDigest dig))

-- | @assuranceLine@ (grammar App. A.1). The cert payload is a raw
-- S-expression captured by 'sexpLitP' and decoded by the wire codec.
assuranceP :: P Assurance
assuranceP = do
  keyword "assurance"
  symbol '='
  mw <- peekIdent
  case mw of
    Just "none" -> AssuranceNone <$ keyword "none"
    Just "trusted" -> AssuranceTrusted <$ keyword "trusted"
    Just "cert" -> do
      keyword "cert"
      symbol '('
      (b, v) <- backendVersionP
      symbol ','
      Digest dig <- digestLit
      symbol ','
      payload <- sexpLitP
      symbol ')'
      pure (AssuranceCert (Cert b v (TheoryDigest dig) payload))
    _ -> failP "expected an assurance (none | trusted | cert(…))"

-- | Consume one character without skipping trivia.
char1 :: P Char
char1 = do
  s <- getInput
  case s of
    c : _ -> c <$ advanceP
    [] -> failP "unexpected end of input"

-- | A raw S-expression literal, captured by a quote-aware balanced-paren scan
-- and decoded by 'Lara.Wire.parseSExpr' (the canonical wire parser). The
-- payload must be a parenthesised form — every nd@1 certificate is a list.
sexpLitP :: P SExpr
sexpLitP = do
  skipTrivia
  s <- getInput
  case s of
    '(' : _ -> do
      raw <- scan (0 :: Int) False False False ""
      case parseSExpr raw of
        Right e -> pure e
        Left _ -> failP "malformed certificate payload S-expression"
    _ -> failP "certificate payload must be a parenthesised S-expression"
  where
    scan depth inStr esc inComment acc = do
      s <- getInput
      case s of
        [] -> failP "unterminated certificate payload"
        c : _
          | inComment && c == '\n' -> consume depth inStr False False
          | inComment -> consume depth inStr False True
          | esc -> consume depth inStr False False
          | inStr && c == '\\' -> consume depth inStr True False
          | inStr && c == '"' -> consume depth False False False
          | inStr -> consume depth True False False
          | c == ';' -> consume depth False False True
          | c == '"' -> consume depth True False False
          | c == '(' -> consume (depth + 1) False False False
          | c == ')' && depth > 1 -> consume (depth - 1) False False False
          | c == ')' && depth == 1 -> do
              ch <- char1
              pure (acc ++ [ch])
          | otherwise -> consume depth False False False
      where
        consume nextDepth nextInStr nextEsc nextInComment = do
          ch <- char1
          scan nextDepth nextInStr nextEsc nextInComment (acc ++ [ch])

-- | A canonical natural (no sign, no leading zeros beyond a lone @0@).
natLit :: P Int
natLit = do
  skipTrivia
  ds <- takeWhileP isDigit
  case ds of
    [] -> failP "expected a natural number"
    (d0 : _)
      | ds == "0" || d0 /= '0' -> pure (read ds)
      | otherwise -> failP "natural number has a leading zero"

contraryP :: P Contrary
contraryP = do
  keyword "contrary"
  a <- apatP
  b <- apatP
  pure (Contrary a b)

exceptionP :: P Exception
exceptionP = do
  keyword "exception"
  r <- identifier
  symbol ':'
  a <- apatP
  pure (Exception (RuleId r) a)

-- | @admission ::= \"admission\" \"{\" admitRow,… \"}\"@ (grammar §4, optional).
admissionP :: P [((LeafKind, Provenance), Admission)]
admissionP = do
  keyword "admission"
  symbol '{'
  c <- peekChar
  rows <- case c of
    Just '}' -> pure []
    _ -> commaSep1 admitRowP
  symbol '}'
  pure rows

admitRowP :: P ((LeafKind, Provenance), Admission)
admitRowP = do
  symbol '('
  k <- enumFromTable "a leaf kind" leafKindTable
  symbol ','
  prov <- provenanceP
  symbol ')'
  symbol '='
  a <- enumFromTable "an admission (admit | quarantine | reject)" admissionTable
  pure ((k, prov), a)

-- ---------------------------------------------------------------------------
-- Top-level dispatch (grammar §0)
-- ---------------------------------------------------------------------------

-- | A parsed source file: an artifact program or a policy, disambiguated by the
-- leading keyword (grammar §0).
data Source
  = SourceProgram Program
  | SourcePolicy Policy
  deriving (Eq, Show)

-- | Parse a source file, dispatching on the first significant token
-- (@artifact@ → 'Program', @policy@ → 'Policy'; grammar §0).
parseSource :: String -> Either ParseError Source
parseSource input = runComplete p input
  where
    p = do
      mw <- peekIdent
      case mw of
        Just "artifact" -> SourceProgram <$> (programP <* eof)
        Just "policy" -> SourcePolicy <$> (policyP <* eof)
        _ -> failP "expected a source file beginning with 'artifact' or 'policy'"

-- | Run a parser over whole input with normal source-file trivia.
runComplete :: P a -> String -> Either ParseError a
runComplete = runCompleteWith NormalTrivia

runCompleteWith :: TriviaMode -> P a -> String -> Either ParseError a
runCompleteWith mode p input = fst <$> runP p (PState input 1 1 mode)

-- ===========================================================================
-- Canonical printer (grammar §3–§4 field order; §7 position spelling)
-- ===========================================================================

-- | Print a source file in its one canonical spelling.
printSource :: Source -> String
printSource (SourceProgram p) = printProgram p
printSource (SourcePolicy p) = printPolicy p

-- | Canonically print an artifact @Program@ (grammar §3). @parseProgram
-- (printProgram p) == Right p@ (spec result 12).
printProgram :: Program -> String
printProgram p =
  unlines $
    [ "artifact " ++ programArtifact p ++ " at " ++ digestStr (programDigest p)
    , "policy " ++ let PolicyId pid = programPolicy p in pid
    , "use backends [" ++ intercalate ", " (map backendRefStr (programBackends p)) ++ "]"
    ]
      ++ map printValueBinding (programValueBindings p)
      ++ concatMap (("" :) . printDecl) (programDecls p)

printValueBinding :: ValueBinding -> String
printValueBinding (ValueBinding (ValueName name) term) =
  "let " ++ name ++ " = " ++ printTerm term

digestStr :: Digest -> String
digestStr (Digest d) = d

backendRefStr :: (BackendId, String) -> String
backendRefStr (BackendId b, v) = b ++ "@" ++ v

printDecl :: Decl -> [String]
printDecl d = case d of
  DeclClaim c -> printClaim c
  DeclLeaf l -> printLeaf l
  DeclArg a -> printArg a
  DeclAttack k -> [printAttack k]
  DeclStatus (PropId c) -> ["status " ++ c]
  DeclGroup g -> [printGroup g]
  DeclComparison c -> printComparison c

-- | @comparison@ in the fixed field order of grammar App. B.3. The @nl@ string
-- is emitted __raw__ (directives unexpanded, @{{@\/@}}@ unconverted, B.6), which
-- is what makes @parse ∘ print = id@ hold on the authored spelling.
printComparison :: Comparison -> [String]
printComparison c =
  [ "comparison : " ++ printProp (cmpConclusion c)
      ++ " on " ++ (let MeasurandId m = cmpMeasurand c in m)
      ++ " @ " ++ (let DatasetId d = cmpDataset c in d)
  , "  relation = " ++ relationStr (cmpRelation c)
  , "  recheck = " ++ (let ArgId a = cmpRecheckArg c in a)
  , "  bridge = " ++ (let ArgId a = cmpBridgeArg c in a)
  , "  result = " ++ (let LeafId l = cmpResult c in l)
  , "  baseline = " ++ (let LeafId l = cmpBaseline c in l)
  , "  binding = " ++ (let LeafId l = cmpBinding c in l)
  , "  claims " ++ (let PropId p = ccId (cmpClaim c) in p)
  , "    nl = " ++ quote (ccNlRaw (cmpClaim c))
  , "    binding = " ++ printBinding (ccBinding (cmpClaim c))
  ]
    ++ [ "  supports " ++ p | Just (PropId p) <- [cmpSupports c] ]

-- | @group ident = [ leafId,… ]@ (grammar §3, spec §4.3).
printGroup :: DupGroup -> String
printGroup (DupGroup (GroupId g) members) =
  "group " ++ g ++ " = [" ++ intercalate ", " [l | LeafId l <- members] ++ "]"

printClaim :: Claim -> [String]
printClaim c =
  [ "claim " ++ let PropId cid = claimId c in cid
  , "  nl = " ++ quote (claimNl c)
  , "  formal = " ++ printProp (claimFormal c)
  , "  binding = " ++ printBinding (claimBinding c)
  ]

printBinding :: Binding -> String
printBinding b =
  "{ author = "
    ++ bindingAuthor b
    ++ ", rationale = "
    ++ quote (bindingRationale b)
    ++ ", audit-status = "
    ++ auditStatusStr (bindingAuditStatus b)
    ++ " }"

printLeaf :: Leaf -> [String]
printLeaf l =
  [ "leaf " ++ (let LeafId lid = leafId l in lid) ++ " : " ++ printProp (leafProp l)
  , "  kind = " ++ leafKindStr (leafKind l)
  , "  provenance = " ++ provenanceStr (leafProvenance l)
  , "  refs = [" ++ intercalate ", " [r | SourceRef r <- leafRefs l] ++ "]"
  ]

printArg :: Arg -> [String]
printArg a =
  ("arg " ++ (let ArgId aid = argId a in aid) ++ " : " ++ printArgConcl (argConcl a) ++ " by " ++ headTerm)
    : dischargeLines
  where
    (headTerm, dischargeLines) =
      case argInstantiation a of
        ExplicitTheta term -> printSupportTerm term
        InferTheta rule refs disch holes assurance ->
          printInferredSupportTerm rule refs disch holes assurance

-- Inferred payloads retain obligation ids for elaboration, but not the
-- critical-question id discarded by the surface parser. Re-emitting the
-- obligation id in both slots is exact, not invented: §6.1 reads a hole's
-- 'ObligationId' as the question name (module header).
printInferredSupportTerm
  :: RuleId -> [ArgRef] -> ArgDischarge -> [ObligationId] -> Assurance -> (String, [String])
printInferredSupportTerm (RuleId r) refs disch holes assurance =
  ( r ++ " from [" ++ intercalate ", " [name | ArgRef name <- refs] ++ "]"
  , [ "  discharge " ++ q ++ " with " ++ ref
    | (QuestionId q, ArgRef ref) <- disch
    ]
      ++ openLines holes
      ++ assuranceLine assurance
  )

printArgConcl :: ArgConcl -> String
printArgConcl ac = case ac of
  SupportsClaim (PropId c) -> "supports(" ++ c ++ ")"
  SupportsDerived (PropId c) -> "supports(" ++ c ++ ")"
  Challenges (ChallengesQuestion (QuestionId q) (ArgId u)) ->
    "challenges(" ++ q ++ "(" ++ u ++ "))"
  Challenges (ChallengesLeaf (LeafId l)) -> "challenges(" ++ l ++ ")"

-- | Print a support term's head form and its indented discharge, @open@, and
-- assurance lines. Total on every 'SupportTerm'; faithful (round-tripping) on
-- the surface subset the parser produces (module header).
printSupportTerm :: SupportTerm -> (String, [String])
printSupportTerm t = case t of
  SLeaf (LeafId l) -> ("leaf(" ++ l ++ ")", [])
  SRule (RuleId r) theta _prems disch holes assurance ->
    ( r ++ "(" ++ intercalate ", " (map printTerm (map snd theta)) ++ ")"
    , printRuleBody disch holes assurance
    )

-- | Body lines in the canonical printer's fixed order: the §3
-- @{ dischargeLine | openLine }@ repetition emitted as discharges then opens,
-- then the optional App. A.1 assurance line. §3 and A.1 both leave the source
-- order free; this is the normalization, not a grammar constraint.
printRuleBody :: [(QuestionId, SupportTerm)] -> [ObligationId] -> Assurance -> [String]
printRuleBody disch holes assurance =
  [ "  discharge " ++ q ++ " with " ++ dischargeRef w
  | (QuestionId q, w) <- disch
  ]
    ++ openLines holes
    ++ assuranceLine assurance

-- | @open q@ per hole (@lara-syntax\@0.7@). A hole has exactly one
-- identity: §6.1 reads its 'ObligationId' /as/ the question it leaves open
-- (@holeNames@ in "Lara.SupportTerm"), so one identifier is the whole content
-- of the line and the retired @as o@ slot had nothing left to say.
openLines :: [ObligationId] -> [String]
openLines holes = ["  open " ++ o | ObligationId o <- holes]

dischargeRef :: SupportTerm -> String
dischargeRef (SLeaf (LeafId l)) = l
dischargeRef (SRule (RuleId r) _ _ _ _ _) = r -- totality fallback only

assuranceLine :: Assurance -> [String]
assuranceLine assurance = case assurance of
  AssuranceNone -> []
  AssuranceTrusted -> ["  assurance = trusted"]
  AssuranceCert (Cert (BackendId b) v (TheoryDigest h) payload) ->
    [ "  assurance = cert(" ++ b ++ "@" ++ show v ++ ", " ++ h ++ ", "
        ++ printSExpr payload ++ ")"
    ]

-- | Print an authored attack (grammar §7, App. B.5). Each 'SurfaceStep' is
-- emitted in the spelling it was written in — 'StepIndex' as its integer,
-- 'StepName' as its bare name — so both round-trip; the terminal
-- @rule@\/@leaf@ marker is regenerated canonically from the attack kind.
printAttack :: SurfaceAttack -> String
printAttack k = case k of
  SRebut (ArgId w) (ArgId u) -> "rebut " ++ w ++ " " ++ u
  SUndercut (ArgId w) (ArgId u) steps ->
    "undercut " ++ w ++ " " ++ u ++ printPath steps ++ ".rule"
  SUndermine (ArgId w) (ArgId u) steps ->
    "undermine " ++ w ++ " " ++ u ++ printPath steps ++ ".leaf"
  where
    printPath = concatMap (\s -> "." ++ printStep s)
    printStep (StepIndex i) = show i
    printStep (StepName s) = s

-- ---------------------------------------------------------------------------
-- Policy printer
-- ---------------------------------------------------------------------------

-- | Canonically print a @Policy@ (grammar §4). @parsePolicy (printPolicy p) ==
-- Right p@ (spec result 12).
--
-- __Canonical section order__ (the grammar is order-insensitive, so the printer
-- picks one): @policy@ header, @rule@s, @contrary@, @exception@, @admission@,
-- @duplicate-reports@, @theory@ — the frozen @\@0.2@ block — then the
-- @lara-syntax\@0.3@ additions @measurand@ and @comparison-scheme@, appended in
-- that order. Every optional section is elided when empty, so a policy written
-- before @\@0.3@ prints byte-identically to before.
printPolicy :: Policy -> String
printPolicy p =
  unlines $
    ["policy " ++ let PolicyId pid = policyId p in pid]
      ++ printSigma (policySigma p)
      ++ concatMap (("" :) . printRule) (policyRules p)
      ++ prependBlank (map printContrary (policyContraries p))
      ++ prependBlank (map printException (policyExceptions p))
      ++ printAdmission (policyAdmission p)
      ++ printGroupMode (policyGroupMode p)
      ++ printTheories (policyTheories p)
      ++ printMeasurands (policyMeasurands p)
      ++ printSchemes (policyComparisonSchemes p)
  where
    prependBlank [] = []
    prependBlank xs = "" : xs
    -- The default is omitted, mirroring the optional admission block, so
    -- group-free policies print byte-identically to the pre-groups grammar.
    printGroupMode QuarantineOnConflict = []
    printGroupMode m = ["", "duplicate-reports = " ++ groupModeStr m]

-- | The policy signature blocks (grammar §4.0), immediately after the @policy@
-- header: one @sort@ line carrying every declared sort in declaration order,
-- then one @con@ line per constructor and one @pred@ line per predicate. Each
-- block is elided when empty, so a signature-free policy prints byte-identically
-- to the pre-@0.2@ grammar.
printSigma :: Sigma -> [String]
printSigma sg = sortsBlock ++ block (map printCon (sigmaCons sg)) ++ block (map printPred (sigmaPreds sg))
  where
    sortsBlock
      | null (sigmaSorts sg) = []
      | otherwise = ["", "sort " ++ intercalate ", " [n | SortName n <- sigmaSorts sg]]
    block [] = []
    block ls = "" : ls
    printCon c =
      "con " ++ (let FunSym k = conSym c in k)
        ++ argVector (conArgs c)
        ++ " : "
        ++ sortText (conResult c)
    printPred s =
      "pred " ++ (let Pred h = predSym s in h) ++ argVector (predArgs s)
    argVector [] = ""
    argVector ss = "(" ++ intercalate ", " (map sortText ss) ++ ")"

printRule :: Rule -> [String]
printRule r =
  [ "rule " ++ (let RuleId rid = ruleId r in rid) ++ "(" ++ intercalate ", " [x | Param x <- ruleParams r] ++ ")"
  , "  mode = " ++ modeStr (ruleMode r)
  , "  premises = [" ++ intercalate ", " (zipWith printPremise labels (rulePremises r)) ++ "]"
  , "  conclusion = " ++ printAPat (ruleConclusion r)
  ]
    ++ strictFields
    ++ [ "  question " ++ q ++ " : " ++ printAPat a ++ " (" ++ necessityStr n ++ ")"
       | Question (QuestionId q) a n <- ruleQuestions r
       ]
  where
    -- Premise labels are optional and positional (grammar App. B.4). A short or
    -- absent label list pads with 'Nothing', so an unlabelled rule prints
    -- byte-identically to @\@0.2@.
    labels = rulePremiseLabels r ++ repeat Nothing
    printPremise Nothing a = printAPat a
    printPremise (Just (PremiseLabel l)) a = l ++ ": " ++ printAPat a
    -- allow-trusted / certifiers are a strict-rule surface (grammar §4).
    strictFields
      | ruleMode r == Strict =
          [ "  allow-trusted = " ++ boolStr (ruleAllowTrusted r)
          , "  certifiers = [" ++ intercalate ", " (map printCertRef (ruleCertifiers r)) ++ "]"
          ]
      | otherwise = []

printCertRef :: CertRef -> String
printCertRef (CertRef (BackendId b) v (TheoryDigest d)) =
  "(" ++ b ++ "@" ++ show v ++ ", " ++ d ++ ")"

printContrary :: Contrary -> String
printContrary (Contrary a b) = "contrary " ++ printAPat a ++ " " ++ printAPat b

printException :: Exception -> String
printException (Exception (RuleId r) a) = "exception " ++ r ++ " : " ++ printAPat a

printAdmission :: [((LeafKind, Provenance), Admission)] -> [String]
printAdmission [] = []
printAdmission rows =
  ["", "admission { " ++ intercalate ", " (map printRow rows) ++ " }"]
  where
    printRow ((k, prov), a) =
      "(" ++ leafKindStr k ++ ", " ++ provenanceStr prov ++ ") = " ++ admissionStr a

printTheories :: [(TheoryDigest, [Prop])] -> [String]
printTheories [] = []
printTheories ts =
  "" :
    [ "theory " ++ d ++ " = [" ++ intercalate ", " (map printProp ps) ++ "]"
    | (TheoryDigest d, ps) <- ts
    ]

-- | The measurand table (grammar App. B.1), one line each; elided when empty.
printMeasurands :: [Measurand] -> [String]
printMeasurands [] = []
printMeasurands ms =
  "" :
    [ "measurand " ++ m ++ " : " ++ sortText (measurandSort x)
        ++ maybe "" ((" where " ++) . polarityStr) (measurandPolarity x)
    | x <- ms
    , let MeasurandId m = measurandId x
    ]

-- | The comparison-scheme blocks (grammar App. B.2); elided when empty.
printSchemes :: [ComparisonScheme] -> [String]
printSchemes = concatMap (("" :) . one)
  where
    one s =
      [ "comparison-scheme " ++ relationStr (csRelation s) ++ " " ++ polarityStr (csPolarity s)
      , "  recheck = " ++ (let RuleId r = csRecheck s in r)
      , "  bridge = " ++ (let RuleId r = csBridge s in r)
      ]

-- ---------------------------------------------------------------------------
-- Shared value printers
-- ---------------------------------------------------------------------------

printProp :: Prop -> String
printProp (Prop (Pred h) []) = h
printProp (Prop (Pred h) ts) = h ++ "(" ++ intercalate ", " (map printTerm ts) ++ ")"

printTerm :: Term -> String
printTerm t = case t of
  TNum s -> s
  TStr s -> quote s -- not surface-representable in a term; totality only
  TCon (FunSym k) [] -> k
  TCon (FunSym k) ts -> k ++ "(" ++ intercalate ", " (map printTerm ts) ++ ")"

printAPat :: AtomPat -> String
printAPat (AtomPat (Pred h) []) = h
printAPat (AtomPat (Pred h) ps) = h ++ "(" ++ intercalate ", " (map printPat ps) ++ ")"

printPat :: Pat -> String
printPat p = case p of
  PVar (Param x) -> x
  PLit (TNum s) -> s
  PLit (TStr s) -> quote s -- not surface-representable; totality only
  PLit (TCon (FunSym k) []) -> k
  PLit (TCon (FunSym k) ts) -> k ++ "(" ++ intercalate ", " (map printTerm ts) ++ ")"
  PCon (FunSym k) ps -> k ++ "(" ++ intercalate ", " (map printPat ps) ++ ")"

-- | Emit a single-line double-quoted string (grammar §1.3).
quote :: String -> String
quote s = '"' : s ++ "\""
