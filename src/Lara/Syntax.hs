-- | The concrete @.lara@ surface syntax: parser and label-preserving printer
-- (@lara-syntax\@0.2@, additive over the frozen @0.1@ grammar in
-- @docs/lara-surface-grammar.md@).
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
-- records what the surface states, using these conventions, and leaves the rest
-- for the elaborator:
--
--   * @leaf(l)@                         ↦ @'SLeaf' (LeafId l)@.
--   * @r(g1,…,gn)@                      ↦ @'SRule'@ with @srSubst =
--     [(Param \"1\", g1), …, (Param \"n\", gn)]@ (positional, 1-based — §5's
--     \"i-th parameter ↦ gi\"), @srPremises = []@, with optional assurance
--     supplied by the arg block (default 'AssuranceNone').
--   * @discharge q with ref@            ↦ appends @(QuestionId q, 'SLeaf'
--     (LeafId ref))@ to @srDischarge@ (the elaborator re-points a target that is
--     actually a prior argument).
--
-- @open@ lines and non-'SLeaf' discharge subterms are __not emitted__ by the
-- printer and are excluded from the round-trip generators: 'SupportTerm' has no
-- field for an @open@ line's critical-question id, so that surface form is not
-- losslessly representable here and belongs to the elaborator's hole accounting
-- (spec §4.2). The printer is nonetheless __total__ on every 'SupportTerm'.
module Lara.Syntax
  ( -- * Located parse errors (spec §10.1 R14)
    ParseError (..)
    -- * Parsing
  , Source (..)
  , parseSource
  , parseProgram
  , parsePolicy
    -- * Canonical printing
  , printSource
  , printProgram
  , printPolicy
  ) where

import Data.Char (isAlpha, isDigit)
import Data.List (intercalate)

import Lara.AST
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

data PState = PState
  { psInput :: String
  , psLine :: !Int
  , psCol :: !Int
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
-- Lexical layer (two modes: normal, and ref-list — grammar §1.2)
-- ---------------------------------------------------------------------------

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

-- | Normal-mode trivia: whitespace and @\'#\'@ line comments.
skipTrivia :: P ()
skipTrivia = do
  _ <- takeWhileP isSpaceChar
  s <- getInput
  case s of
    '#' : _ -> do
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
  ds <- declsP
  pure
    Program
      { programArtifact = name
      , programDigest = dig
      , programPolicy = PolicyId pid
      , programBackends = bes
      , programDecls = ds
      }

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
  ["claim", "leaf", "arg", "rebut", "undercut", "undermine", "status", "group"]

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
    _ -> failP "expected a declaration (claim | leaf | arg | rebut | undercut | undermine | status | group)"

claimP :: P Claim
claimP = do
  keyword "claim"
  cid <- identifier
  keyword "nl"
  symbol '='
  nl <- stringLit
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
-- openLine }@ (grammar §3, §5). Discharge\/open lines fold into the support
-- term; see the module header for the surface-support-term contract.
argP :: P Arg
argP = do
  keyword "arg"
  aid <- identifier
  symbol ':'
  concl <- argConclP
  keyword "by"
  base <- supportTermP
  term <- argBody base
  pure Arg {argId = ArgId aid, argConcl = concl, argTerm = term}

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

-- | The bare support term of a @by@ clause (grammar §3): @leaf(l)@ or a rule
-- instance @r(g1,…,gn)@. Discharges\/holes are attached by 'argBody'.
supportTermP :: P SupportTerm
supportTermP = do
  h <- identifier
  if h == "leaf"
    then do
      symbol '('
      l <- identifier
      symbol ')'
      pure (SLeaf (LeafId l))
    else do
      terms <- parenList termP
      let theta = zipWith (\i t -> (Param (show i), t)) [1 :: Int ..] terms
      pure
        SRule
          { srRule = RuleId h
          , srSubst = theta
          , srPremises = []
          , srDischarge = []
          , srHoles = []
          , srAssurance = AssuranceNone
          }

-- | Fold @discharge@\/@open@\/@assurance@ lines into the base support term.
argBody :: SupportTerm -> P SupportTerm
argBody base = go base False
  where
    go acc seenAssurance = do
      mw <- peekIdent
      case mw of
        Just "discharge" -> do
          keyword "discharge"
          q <- identifier
          keyword "with"
          ref <- identifier
          go (addDischarge acc (QuestionId q) (SLeaf (LeafId ref))) seenAssurance
        Just "open" -> do
          keyword "open"
          _q <- identifier
          keyword "as"
          o <- identifier
          go (addHole acc (ObligationId o)) seenAssurance
        Just "assurance" ->
          if seenAssurance
            then failP "duplicate assurance line in arg block"
            else case acc of
              SRule {} -> do
                assurance <- assuranceP
                go (setAssurance acc assurance) True
              _ -> failP "assurance requires a rule application, not a bare leaf"
        _ -> pure acc

addDischarge :: SupportTerm -> QuestionId -> SupportTerm -> SupportTerm
addDischarge (SRule r th pr ds hs as) q w = SRule r th pr (ds ++ [(q, w)]) hs as
addDischarge t _ _ = t -- a discharge on a bare leaf is elaborator-rejected

addHole :: SupportTerm -> ObligationId -> SupportTerm
addHole (SRule r th pr ds hs as) o = SRule r th pr ds (hs ++ [o]) as
addHole t _ = t

setAssurance :: SupportTerm -> Assurance -> SupportTerm
setAssurance (SRule r th pr ds hs _) assurance = SRule r th pr ds hs assurance
setAssurance t _ = t -- unreachable: 'argBody' rejects a non-rule base

-- | @attackDecl@ / @posTarget@ (grammar §3, §7).
attackP :: P Attack
attackP = do
  mw <- peekIdent
  case mw of
    Just "rebut" -> do
      keyword "rebut"
      w <- identifier
      u <- identifier
      pure (Rebut (ArgId w) (ArgId u))
    Just "undercut" -> do
      keyword "undercut"
      w <- identifier
      (u, steps) <- posTargetP "rule"
      pure (Undercut (ArgId w) u steps)
    Just "undermine" -> do
      keyword "undermine"
      w <- identifier
      (u, steps) <- posTargetP "leaf"
      pure (Undermine (ArgId w) u steps)
    _ -> failP "expected an attack (rebut | undercut | undermine)"

-- | @posTarget ::= ident { \".\" step } \".\" marker@ where @marker@ is the
-- fixed terminal for the attack kind (@rule@ for undercut, @leaf@ for
-- undermine). Returns the base argument and the decoded @[Step]@ (grammar §7).
posTargetP :: String -> P (ArgId, Position)
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
      | not (null s) && all isDigit s = StepPremise (read s)
      | otherwise = StepQuestion (QuestionId s)

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
  = PolicyAcc [Rule] [Contrary] [Exception]
      [((LeafKind, Provenance), Admission)] [(TheoryDigest, [Prop])]
      GroupConflictMode

policyP :: P Policy
policyP = do
  keyword "policy"
  pid <- identifier
  PolicyAcc rs cs es adm ts gm <- policyDecls (PolicyAcc [] [] [] [] [] QuarantineOnConflict)
  pure
    Policy
      { policyId = PolicyId pid
      , policyRules = rs
      , policyContraries = cs
      , policyExceptions = es
      , policyAdmission = adm
      , policyTheories = ts
      , policyGroupMode = gm
      }

policyDecls :: PolicyAcc -> P PolicyAcc
policyDecls acc@(PolicyAcc rs cs es adm ts gm) = do
  mw <- peekIdent
  case mw of
    Just "rule" -> do r <- ruleP; policyDecls (PolicyAcc (rs ++ [r]) cs es adm ts gm)
    Just "contrary" -> do c <- contraryP; policyDecls (PolicyAcc rs (cs ++ [c]) es adm ts gm)
    Just "exception" -> do e <- exceptionP; policyDecls (PolicyAcc rs cs (es ++ [e]) adm ts gm)
    Just "admission" -> do a <- admissionP; policyDecls (PolicyAcc rs cs es (adm ++ a) ts gm)
    Just "duplicate-reports" -> do
      keyword "duplicate-reports"
      symbol '='
      gm' <- enumFromTable "a group conflict mode (quarantine | reject)" groupModeTable
      policyDecls (PolicyAcc rs cs es adm ts gm')
    Just "theory" -> do
      t@(TheoryDigest d, _) <- theoryLineP
      if any (\(TheoryDigest d', _) -> d' == d) ts
        then failP ("duplicate theory digest: " ++ d)
        else policyDecls (PolicyAcc rs cs es adm (ts ++ [t]) gm)
    _ -> pure acc

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
  prems <- brackets apatP
  keyword "conclusion"
  symbol '='
  concl <- apatP
  at <- optAllowTrusted
  certs <- optCertifiers
  qs <- questionLines
  pure
    Rule
      { ruleId = RuleId rid
      , ruleParams = params
      , ruleMode = mode
      , rulePremises = prems
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

-- | Run a parser over whole input, returning the value or the located error.
runComplete :: P a -> String -> Either ParseError a
runComplete p input = fst <$> runP p (PState input 1 1)

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
      ++ concatMap (("" :) . printDecl) (programDecls p)

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
    (headTerm, dischargeLines) = printSupportTerm (argTerm a)

printArgConcl :: ArgConcl -> String
printArgConcl ac = case ac of
  SupportsClaim (PropId c) -> "supports(" ++ c ++ ")"
  SupportsDerived (PropId c) -> "supports(" ++ c ++ ")"
  Challenges (ChallengesQuestion (QuestionId q) (ArgId u)) ->
    "challenges(" ++ q ++ "(" ++ u ++ "))"
  Challenges (ChallengesLeaf (LeafId l)) -> "challenges(" ++ l ++ ")"

-- | Print a support term's head form and its indented discharge lines. Total on
-- every 'SupportTerm'; faithful (round-tripping) on the surface subset the
-- parser produces (module header).
printSupportTerm :: SupportTerm -> (String, [String])
printSupportTerm t = case t of
  SLeaf (LeafId l) -> ("leaf(" ++ l ++ ")", [])
  SRule (RuleId r) theta _prems disch _holes assurance ->
    ( r ++ "(" ++ intercalate ", " (map printTerm (map snd theta)) ++ ")"
    , [ "  discharge " ++ q ++ " with " ++ dischargeRef w
      | (QuestionId q, w) <- disch
      ]
        ++ assuranceLine assurance
    )
  where
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

printAttack :: Attack -> String
printAttack k = case k of
  Rebut (ArgId w) (ArgId u) -> "rebut " ++ w ++ " " ++ u
  Undercut (ArgId w) (ArgId u) steps ->
    "undercut " ++ w ++ " " ++ u ++ printPath steps ++ ".rule"
  Undermine (ArgId w) (ArgId u) steps ->
    "undermine " ++ w ++ " " ++ u ++ printPath steps ++ ".leaf"
  where
    printPath = concatMap (\s -> "." ++ printStep s)
    printStep (StepPremise i) = show i
    printStep (StepQuestion (QuestionId q)) = q

-- ---------------------------------------------------------------------------
-- Policy printer
-- ---------------------------------------------------------------------------

-- | Canonically print a @Policy@ (grammar §4). @parsePolicy (printPolicy p) ==
-- Right p@ (spec result 12).
printPolicy :: Policy -> String
printPolicy p =
  unlines $
    ["policy " ++ let PolicyId pid = policyId p in pid]
      ++ concatMap (("" :) . printRule) (policyRules p)
      ++ prependBlank (map printContrary (policyContraries p))
      ++ prependBlank (map printException (policyExceptions p))
      ++ printAdmission (policyAdmission p)
      ++ printGroupMode (policyGroupMode p)
      ++ printTheories (policyTheories p)
  where
    prependBlank [] = []
    prependBlank xs = "" : xs
    -- The default is omitted, mirroring the optional admission block, so
    -- group-free policies print byte-identically to the pre-groups grammar.
    printGroupMode QuarantineOnConflict = []
    printGroupMode m = ["", "duplicate-reports = " ++ groupModeStr m]

printRule :: Rule -> [String]
printRule r =
  [ "rule " ++ (let RuleId rid = ruleId r in rid) ++ "(" ++ intercalate ", " [x | Param x <- ruleParams r] ++ ")"
  , "  mode = " ++ modeStr (ruleMode r)
  , "  premises = [" ++ intercalate ", " (map printAPat (rulePremises r)) ++ "]"
  , "  conclusion = " ++ printAPat (ruleConclusion r)
  ]
    ++ strictFields
    ++ [ "  question " ++ q ++ " : " ++ printAPat a ++ " (" ++ necessityStr n ++ ")"
       | Question (QuestionId q) a n <- ruleQuestions r
       ]
  where
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
