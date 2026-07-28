{-# LANGUAGE DerivingVia #-}

-- | The S-expression wire codec (the N11 differential anchor).
--
-- One textual S-expression format carries checker-boundary 'Unit's and checker
-- 'Verdict's between the Haskell production runtime and the Lean executable
-- semantics (@lean/Lara/Driver.lean@). Both drivers print verdicts through this
-- exact codec, so differential testing is byte comparison (plan D16). This is
-- the /only/ wire front end: there is deliberately no JSON codec (plan, global
-- constraints).
--
-- == Canonical text format
--
-- The printer is /canonical/: one S-expression per value, single-line, so two
-- implementations agree byte-for-byte.
--
-- * A list prints as @(e1 e2 … en)@ — one space between elements, none after
--   @(@ or before @)@; the empty list is @()@.
-- * An atom prints /bare/ when every character is in the bare set — printable
--   ASCII (0x21–0x7E) except @(@, @)@, @;@, @\"@, and @\\@ — and it is
--   nonempty. Every other atom prints quoted: @"…"@ with exactly three
--   escapes (@\"@, @\\@, @\n@); all other characters (including non-ASCII)
--   print verbatim inside the quotes.
-- * The reader additionally skips whitespace and @;@-to-end-of-line comments;
--   it accepts any of the three escapes and rejects all others.
-- * A file holds __exactly one__ top-level form; trailing whitespace or
--   comments are allowed, a second form is a codec error.
--
-- == Unit grammar (input)
--
-- @
-- \<unit\>     ::= (unit \<policy-sec\>? \<theories-sec\>? \<leaves-sec\>?
--                        \<args-sec\>? \<attacks-sec\>? \<queries-sec\>?)
-- \<policy-sec\>   ::= (policy (rules \<rule\>*) (contraries \<contrary\>*)
--                             (exceptions \<exception\>*))
-- \<rule\>         ::= (rule ID (mode strict | defeasible) (params ID*)
--                       (premises \<apat\>*) (conclusion \<apat\>)
--                       (questions \<question\>*) (allow-trusted true | false)
--                       (certifiers \<certifier\>*))
-- \<question\>     ::= (question ID \<apat\> mandatory | optional)
-- \<certifier\>    ::= (certifier ID NAT STRING)
-- \<contrary\>     ::= (contrary \<apat\> \<apat\>)
-- \<exception\>    ::= (exception ID \<apat\>)
-- \<theories-sec\> ::= (theories (theory STRING \<atom\>*)*)
-- \<leaves-sec\>   ::= (leaves (leaf ID \<atom\>)*)
-- \<args-sec\>     ::= (args (arg ID \<sterm\>)*)
-- \<attacks-sec\>  ::= (attacks \<attack\>*)
-- \<queries-sec\>  ::= (queries \<atom\>*)
-- \<apat\>         ::= (apat ID \<pat\>*)
-- \<pat\>          ::= (var ID) | (num STRING) | (str STRING) | (con ID \<pat\>*)
-- \<atom\>         ::= (atom ID \<term\>*)
-- \<term\>         ::= (num STRING) | (str STRING) | (con ID \<term\>*)
-- \<sterm\>        ::= (leaf ID)
--                    | (inst ID (subst (ID \<term\>)*) (premises \<sterm\>*)
--                             (discharges (ID \<sterm\>)*) (holes ID*)
--                             (assurance \<assurance\>))
-- \<assurance\>    ::= none | trusted | (cert ID NAT STRING SEXPR)
-- \<attack\>       ::= (rebut ID ID) | (undercut ID ID \<pos\>)
--                    | (undermine ID ID \<pos\>)
-- \<pos\>          ::= (pos ((prem NAT) | (ques ID))*)
-- @
--
-- @ID@ is any atom (its text becomes the corresponding newtype payload),
-- @NAT@ is a canonical decimal (no sign, no leading zeros), @STRING@ any atom,
-- and @SEXPR@ an opaque sub-expression (the backend certificate grammar, e.g.
-- the ND grammar of "Lara.Strict.ND" — this codec never inspects it).
--
-- Section order is fixed and each section occurs at most once; the policy
-- subsections are all required, in order. Two further invariants are checked
-- at the decode boundary in __both__ drivers (they are wire well-formedness,
-- R14 — not checker rejections): argument identifiers are unique, and every
-- attack endpoint names a declared argument.
--
-- AST invariants the encoder relies on (the decoder produces only these):
-- 'PLit' carries literals ('TNum'\/'TStr') only — constructor patterns are
-- 'PCon'; 'Cert' versions and 'CertRef' versions are canonical decimals.
--
-- == Verdict grammar (output)
--
-- @
-- \<verdict\> ::= (verdict accept (labels (NAT in | out | undec)*)
--                               (edges (NAT NAT)*)
--                               (statuses (status \<atom\> STATUS)*))
--               | (verdict reject REJECTION)
-- STATUS    ::= gap | justified | contested | defeated
-- REJECTION ::= duplicate-rule | duplicate-argument | incomplete-argument
--             | missing-conflict | R1 | R3 | R4 | R5 | R6 | R7
--             | R10 | R11 | R12 | R13
-- @
--
-- Labels cover every compiled argument in declaration order; edges are the
-- compiled closure edges in ascending @(i, j)@ order; statuses follow the
-- query order of the unit. The rejection payload is the class atom only —
-- located diagnostics live in the checker's result type ("Lara.Check",
-- Task 1), not on the wire.
module Lara.Wire
  ( -- * Textual S-expression codec
    ParseError (..)
  , parseSExpr
  , printSExpr
    -- * The closed tag vocabulary
  , Tag (..)
  , tagToString
  , parseTag
    -- * Unit codec
  , WireError (..)
  , decodeUnit
  , encodeUnit
  , decodeUnitFile
    -- * Verdict codec
  , Verdict (..)
  , decodeVerdict
  , encodeVerdict
  ) where

import Data.Char (ord)
import Data.List (intercalate)

import Lara.AST
import Lara.Prop (Prop (..), Term (..))
import Lara.Strict (SExpr (..))

-- ---------------------------------------------------------------------------
-- Textual S-expression codec
-- ---------------------------------------------------------------------------

-- | A located text parse failure (line and column are 1-based).
data ParseError = ParseError
  { peLine :: Int
  , peCol :: Int
  , peMessage :: String
  }
  deriving (Eq, Show)

-- | Characters allowed in a bare (unquoted) atom: printable ASCII except the
-- delimiters @(@, @)@, @;@, @\"@, and @\\@. Non-ASCII characters are always
-- quoted, keeping the bare set free of any Unicode-classification drift
-- between the two runtimes.
isBareChar :: Char -> Bool
isBareChar c =
  ord c >= 0x21 && ord c <= 0x7e && c `notElem` "();\"\\"

-- | Parser state: remaining input and the 1-based cursor.
data P = P
  { pInput :: String
  , pLine :: !Int
  , pCol :: !Int
  }

perr :: P -> String -> Either ParseError a
perr p msg = Left (ParseError (pLine p) (pCol p) msg)

step :: P -> P
step p = case pInput p of
  '\n' : rest -> p {pInput = rest, pLine = pLine p + 1, pCol = 1}
  _ : rest -> p {pInput = rest, pCol = pCol p + 1}
  "" -> p

-- | Skip whitespace and @;@ comments.
skipSpace :: P -> P
skipSpace p = case pInput p of
  c : rest
    | c `elem` " \t\n\r" -> skipSpace (step p)
    | c == ';' -> skipSpace (skipComment p {pInput = rest})
  _ -> p
  where
    skipComment q = case pInput q of
      '\n' : _ -> q
      "" -> q
      _ -> skipComment (step q)

-- | Maximum S-expression nesting depth. Bounds parser recursion so a
-- pathologically nested input (@(((… )))@) is a located R14 codec error (CLI
-- exit 2) rather than a GHC stack overflow — which the CLI cannot map to an exit
-- code, and which @scripts/differential.sh@ would otherwise misread as a checker
-- rejection (exit 1). Comfortably above any real artifact's structural depth.
maxDepth :: Int
maxDepth = 10000

-- | Parse exactly one top-level form; a second form is an error.
parseSExpr :: String -> Either ParseError SExpr
parseSExpr input = do
  let start = skipSpace (P input 1 1)
  (e, rest) <- parseForm 0 start
  let rest' = skipSpace rest
  if null (pInput rest')
    then Right e
    else perr rest' "expected a single S-expression, found more input"

parseForm :: Int -> P -> Either ParseError (SExpr, P)
parseForm depth p
  | depth > maxDepth =
      perr p ("maximum S-expression nesting depth exceeded (" ++ show maxDepth ++ ")")
  | otherwise = case pInput p of
      '(' : _ -> parseList (step p) []
      '"' : _ -> parseQuoted (step p) []
      c : _
        | isBareChar c ->
            let (tok, rest) = span isBareChar (pInput p)
                p' = p {pInput = rest, pCol = pCol p + length tok}
             in Right (SAtom tok, p')
        | otherwise -> perr p ("unexpected character " ++ show c)
      "" -> perr p "unexpected end of input"
  where
    parseList q acc =
      let q' = skipSpace q
       in case pInput q' of
            ')' : _ -> Right (SList (reverse acc), step q')
            "" -> perr q' "unclosed list"
            _ -> do
              (e, q'') <- parseForm (depth + 1) q'
              parseList q'' (e : acc)
    parseQuoted q acc = case pInput q of
      '"' : _ -> Right (SAtom (reverse acc), step q)
      '\\' : "" -> perr q "unterminated escape sequence"
      '\\' : c : rest
        | c == '"' -> parseQuoted (drop2 q rest) ('"' : acc)
        | c == '\\' -> parseQuoted (drop2 q rest) ('\\' : acc)
        | c == 'n' -> parseQuoted (drop2 q rest) ('\n' : acc)
        | otherwise -> perr q ("invalid escape sequence \\" ++ [c])
        where
          drop2 r s = (step (step r)){pInput = s}
      "" -> perr q "unterminated string literal"
      c : _ -> parseQuoted (step q) (c : acc)

-- | Canonical printing of one S-expression (single line; see module docs).
printSExpr :: SExpr -> String
printSExpr (SAtom s) = printAtom s
printSExpr (SList xs) = "(" ++ intercalate " " (map printSExpr xs) ++ ")"

printAtom :: String -> String
printAtom s
  | not (null s) && all isBareChar s = s
  | otherwise = '"' : concatMap esc s ++ "\""
  where
    esc '"' = "\\\""
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc c = [c]

-- ---------------------------------------------------------------------------
-- The closed tag vocabulary
-- ---------------------------------------------------------------------------

-- | Every keyword of the wire grammar, as a closed sum type. The concrete
-- spellings live in exactly one place ('tagToString' \/ 'parseTag'), textually
-- mirrored by the Lean driver's table. (The conformance tests intentionally
-- spell raw string literals as independent ground truth — do not \"fix\" them
-- to consume this table.)
data Tag
  = -- unit structure
    TUnit | TPolicy | TRules | TRule | TMode | TParams | TPremises
  | TConclusion | TQuestions | TQuestion | TAllowTrusted | TCertifiers
  | TCertifier | TContraries | TContrary | TExceptions | TException
  | TTheories | TTheory | TLeaves | TLeaf | TArgs | TArg | TAttacks
  | TQueries | TSubst | TDischarges | THoles | TAssurance | TCert
  | TPos | TPrem | TQues | TInst
    -- modes, necessity, booleans, assurance
  | TStrict | TDefeasible | TMandatory | TOptional | TTrue | TFalse
  | TNone | TTrusted
    -- patterns, terms, atoms
  | TVar | TNumLit | TStrLit | TConApp | TAtom | TApat
    -- attacks
  | TRebut | TUndercut | TUndermine
    -- verdicts
  | TVerdict | TAccept | TReject | TLabels | TEdges | TStatuses | TStatus
  | TIn | TOut | TUndec | TGap | TJustified | TContested | TDefeated
    -- rejection outcomes
  | TDupRule | TDupArgument | TIncompleteArgument | TMissingConflict
  | TR1 | TR3 | TR4 | TR5 | TR6 | TR7 | TR10 | TR11 | TR12 | TR13
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The on-the-wire spelling of a keyword.
tagToString :: Tag -> String
tagToString t = case t of
  TUnit -> "unit"; TPolicy -> "policy"; TRules -> "rules"; TRule -> "rule"
  TMode -> "mode"; TParams -> "params"; TPremises -> "premises"
  TConclusion -> "conclusion"; TQuestions -> "questions"
  TQuestion -> "question"; TAllowTrusted -> "allow-trusted"
  TCertifiers -> "certifiers"; TCertifier -> "certifier"
  TContraries -> "contraries"; TContrary -> "contrary"
  TExceptions -> "exceptions"; TException -> "exception"
  TTheories -> "theories"; TTheory -> "theory"; TLeaves -> "leaves"
  TLeaf -> "leaf"; TArgs -> "args"; TArg -> "arg"; TAttacks -> "attacks"
  TQueries -> "queries"; TSubst -> "subst"; TDischarges -> "discharges"
  THoles -> "holes"; TAssurance -> "assurance"; TCert -> "cert"
  TPos -> "pos"; TPrem -> "prem"; TQues -> "ques"; TInst -> "inst"
  TStrict -> "strict"; TDefeasible -> "defeasible"
  TMandatory -> "mandatory"; TOptional -> "optional"
  TTrue -> "true"; TFalse -> "false"; TNone -> "none"; TTrusted -> "trusted"
  TVar -> "var"; TNumLit -> "num"; TStrLit -> "str"; TConApp -> "con"
  TAtom -> "atom"; TApat -> "apat"
  TRebut -> "rebut"; TUndercut -> "undercut"; TUndermine -> "undermine"
  TVerdict -> "verdict"; TAccept -> "accept"; TReject -> "reject"
  TLabels -> "labels"; TEdges -> "edges"; TStatuses -> "statuses"
  TStatus -> "status"
  TIn -> "in"; TOut -> "out"; TUndec -> "undec"
  TGap -> "gap"; TJustified -> "justified"; TContested -> "contested"
  TDefeated -> "defeated"
  TDupRule -> "duplicate-rule"; TDupArgument -> "duplicate-argument"
  TIncompleteArgument -> "incomplete-argument"
  TMissingConflict -> "missing-conflict"
  TR1 -> "R1"; TR3 -> "R3"; TR4 -> "R4"; TR5 -> "R5"; TR6 -> "R6"
  TR7 -> "R7"; TR10 -> "R10"; TR11 -> "R11"; TR12 -> "R12"; TR13 -> "R13"

-- | Parse a wire keyword, inverse to 'tagToString'. Derived from the same
-- table by enumerating 'Tag', so it cannot drift out of sync.
parseTag :: String -> Maybe Tag
parseTag s = lookup s [(tagToString t, t) | t <- [minBound .. maxBound]]

-- ---------------------------------------------------------------------------
-- Decode helpers
-- ---------------------------------------------------------------------------

-- | A wire decode failure (R14): the offending grammar position and reason.
data WireError = WireError
  { weContext :: String
  , weMessage :: String
  }
  deriving (Eq, Show)

-- | The decoder monad: 'Either WireError' with a 'MonadFail' instance, so
-- arity-checked field lists can be destructured directly in @do@ blocks (the
-- failure path is unreachable — 'matchTagged' verifies arity first).
newtype Decode a = Decode {runDecode :: Either WireError a}
  deriving (Functor, Applicative, Monad) via Either WireError

instance MonadFail Decode where
  fail = werr "decode"

werr :: String -> String -> Decode a
werr ctx msg = Decode (Left (WireError ctx msg))

ok :: a -> Decode a
ok = Decode . Right

-- | Build a tagged list: @(tag e1 … en)@.
tagged :: Tag -> [SExpr] -> SExpr
tagged t es = SList (SAtom (tagToString t) : es)

-- | Match a tagged list with exactly @n@ payload fields.
matchTagged :: String -> Tag -> Int -> SExpr -> Decode [SExpr]
matchTagged ctx t arity e = case e of
  SList (SAtom k : fields)
    | parseTag k == Just t ->
        if length fields == arity
          then ok fields
          else werr ctx
            ( "wrong number of fields for " ++ tagToString t
                ++ ": expected " ++ show arity ++ ", got "
                ++ show (length fields)
            )
  _ -> werr ctx ("expected (" ++ tagToString t ++ " …), got " ++ show e)

atomText :: String -> SExpr -> Decode String
atomText _ (SAtom s) = ok s
atomText ctx e = werr ctx ("expected an atom, got " ++ show e)

-- | Canonical decimal: no sign, no leading zeros.
parseNatText :: String -> SExpr -> Decode Int
parseNatText ctx e = do
  s <- atomText ctx e
  case reads s :: [(Int, String)] of
    [(n, "")]
      | n >= 0
      , show n == s -> ok n
    _ -> werr ctx ("malformed natural number: " ++ show s)

-- ---------------------------------------------------------------------------
-- Terms, patterns, atoms
-- ---------------------------------------------------------------------------

encodeTerm :: Term -> SExpr
encodeTerm t = case t of
  TNum s -> tagged TNumLit [SAtom s]
  TStr s -> tagged TStrLit [SAtom s]
  TCon (FunSym k) ts -> tagged TConApp (SAtom k : map encodeTerm ts)

decodeTerm :: SExpr -> Decode Term
decodeTerm e = do
  let ctx = "term"
  case e of
    SList (SAtom k : _)
      | parseTag k == Just TNumLit -> do
          [s] <- matchTagged ctx TNumLit 1 e
          TNum <$> atomText ctx s
      | parseTag k == Just TStrLit -> do
          [s] <- matchTagged ctx TStrLit 1 e
          TStr <$> atomText ctx s
      | parseTag k == Just TConApp -> do
          (h, ts) <- headedFields ctx "constructor term" TConApp e
          TCon (FunSym h) <$> mapM decodeTerm ts
    _ -> werr ctx ("malformed term: " ++ show e)

-- | Patterns share the @num@\/@str@\/@con@ tags with terms. A literal pattern
-- is 'PLit'; a constructor pattern is 'PCon' (never 'PLit' of a 'TCon' — the
-- decoder is canonical, so the round-trip property holds on decoded values).
encodePat :: Pat -> SExpr
encodePat p = case p of
  PVar (Param x) -> tagged TVar [SAtom x]
  PLit t -> encodeTerm t
  PCon (FunSym k) ps -> tagged TConApp (SAtom k : map encodePat ps)

decodePat :: SExpr -> Decode Pat
decodePat e = case e of
  SList (SAtom k : _)
    | parseTag k == Just TVar -> do
        [x] <- matchTagged "pattern" TVar 1 e
        PVar . Param <$> atomText "pattern" x
    | parseTag k == Just TConApp -> do
        (h, ps) <- headedFields "pattern" "constructor pattern" TConApp e
        PCon (FunSym h) <$> mapM decodePat ps
    | parseTag k == Just TNumLit -> PLit <$> decodeTerm e
    | parseTag k == Just TStrLit -> PLit <$> decodeTerm e
  _ -> werr "pattern" ("malformed pattern: " ++ show e)

-- | Match @(tag head fields\*)@ where @head@ is an atom; return the head text
-- and the fields.
headedFields :: String -> String -> Tag -> SExpr -> Decode (String, [SExpr])
headedFields ctx what t e = case e of
  SList (SAtom k : h : fs) | parseTag k == Just t -> do
    name <- atomText ctx h
    ok (name, fs)
  _ -> werr ctx ("malformed " ++ what ++ ": " ++ show e)

encodeAtom :: Prop -> SExpr
encodeAtom (Prop (Pred p) ts) = tagged TAtom (SAtom p : map encodeTerm ts)

decodeAtom :: SExpr -> Decode Prop
decodeAtom e = do
  fields <- sectionFields "atom" TAtom e
  case fields of
    h : ts -> do
      p <- atomText "atom" h
      Prop (Pred p) <$> mapM decodeTerm ts
    [] -> werr "atom" ("malformed atom: " ++ show e)

encodeAPat :: AtomPat -> SExpr
encodeAPat (AtomPat (Pred p) ps) = tagged TApat (SAtom p : map encodePat ps)

decodeAPat :: SExpr -> Decode AtomPat
decodeAPat e = case e of
  SList (SAtom k : h : ps) | parseTag k == Just TApat -> do
    p <- atomText "atom pattern" h
    AtomPat (Pred p) <$> mapM decodePat ps
  _ -> werr "atom pattern" ("malformed atom pattern: " ++ show e)

-- ---------------------------------------------------------------------------
-- Policy
-- ---------------------------------------------------------------------------

encodeBool :: Bool -> SExpr
encodeBool b = SAtom (tagToString (if b then TTrue else TFalse))

decodeBool :: String -> SExpr -> Decode Bool
decodeBool _ (SAtom s)
  | parseTag s == Just TTrue = ok True
  | parseTag s == Just TFalse = ok False
decodeBool ctx e = werr ctx ("expected true|false, got " ++ show e)

encodeQuestion :: Question -> SExpr
encodeQuestion (Question (QuestionId q) ap n) =
  tagged
    TQuestion
    [ SAtom q
    , encodeAPat ap
    , SAtom (tagToString (case n of Mandatory -> TMandatory; Optional -> TOptional))
    ]

decodeQuestion :: SExpr -> Decode Question
decodeQuestion e = do
  [qid, ap, nec] <- matchTagged "question" TQuestion 3 e
  q <- atomText "question" qid
  a <- decodeAPat ap
  n <- case nec of
    SAtom s
      | parseTag s == Just TMandatory -> ok Mandatory
      | parseTag s == Just TOptional -> ok Optional
    _ -> werr "question" ("expected mandatory|optional, got " ++ show nec)
  ok (Question (QuestionId q) a n)

encodeCertifier :: CertRef -> SExpr
encodeCertifier (CertRef (BackendId b) v (TheoryDigest h)) =
  tagged TCertifier [SAtom b, SAtom (show v), SAtom h]

decodeCertifier :: SExpr -> Decode CertRef
decodeCertifier e = do
  [b, v, h] <- matchTagged "certifier" TCertifier 3 e
  name <- atomText "certifier" b
  version <- parseNatText "certifier" v
  digest <- atomText "certifier" h
  ok (CertRef (BackendId name) version (TheoryDigest digest))

encodeRule :: Rule -> SExpr
encodeRule r =
  tagged
    TRule
    [ SAtom (let RuleId rid = ruleId r in rid)
    , tagged TMode
        [ SAtom
            ( tagToString
                (case ruleMode r of Strict -> TStrict; Defeasible -> TDefeasible)
            )
        ]
    , tagged TParams [SAtom x | Param x <- ruleParams r]
    , tagged TPremises (map encodeAPat (rulePremises r))
    , tagged TConclusion [encodeAPat (ruleConclusion r)]
    , tagged TQuestions (map encodeQuestion (ruleQuestions r))
    , tagged TAllowTrusted [encodeBool (ruleAllowTrusted r)]
    , tagged TCertifiers (map encodeCertifier (ruleCertifiers r))
    ]

decodeRule :: SExpr -> Decode Rule
decodeRule e = do
  [rid, modeS, paramsS, premsS, conclS, qsS, atS, certsS] <-
    matchTagged "rule" TRule 8 e
  rid' <- RuleId <$> atomText "rule" rid
  mode' <- do
    [m] <- matchTagged "rule mode" TMode 1 modeS
    case m of
      SAtom s
        | parseTag s == Just TStrict -> ok Strict
        | parseTag s == Just TDefeasible -> ok Defeasible
      _ -> werr "rule mode" ("expected strict|defeasible, got " ++ show m)
  params' <- do
    ps <- sectionFields "rule params" TParams paramsS
    mapM (fmap Param . atomText "rule params") ps
  prems' <- do
    ps <- sectionFields "rule premises" TPremises premsS
    mapM decodeAPat ps
  concl' <- do
    [c] <- matchTagged "rule conclusion" TConclusion 1 conclS
    decodeAPat c
  qs' <- do
    qs <- sectionFields "rule questions" TQuestions qsS
    mapM decodeQuestion qs
  at' <- do
    [b] <- matchTagged "rule allow-trusted" TAllowTrusted 1 atS
    decodeBool "rule allow-trusted" b
  certs' <- do
    cs <- sectionFields "rule certifiers" TCertifiers certsS
    mapM decodeCertifier cs
  ok
    Rule
      { ruleId = rid'
      , ruleParams = params'
      , ruleMode = mode'
      , rulePremises = prems'
      , ruleConclusion = concl'
      , ruleAllowTrusted = at'
      , ruleCertifiers = certs'
      , ruleQuestions = qs'
      }

-- | Match @(tag fields\*)@ and return the fields.
sectionFields :: String -> Tag -> SExpr -> Decode [SExpr]
sectionFields ctx t e = case e of
  SList (SAtom k : fs) | parseTag k == Just t -> ok fs
  _ -> werr ctx ("expected (" ++ tagToString t ++ " …), got " ++ show e)

encodeContrary :: Contrary -> SExpr
encodeContrary (Contrary a b) = tagged TContrary [encodeAPat a, encodeAPat b]

decodeContrary :: SExpr -> Decode Contrary
decodeContrary e = do
  [a, b] <- matchTagged "contrary" TContrary 2 e
  Contrary <$> decodeAPat a <*> decodeAPat b

encodeException :: Exception -> SExpr
encodeException (Exception (RuleId r) ap) =
  tagged TException [SAtom r, encodeAPat ap]

decodeException :: SExpr -> Decode Exception
decodeException e = do
  [r, ap] <- matchTagged "exception" TException 2 e
  Exception . RuleId <$> atomText "exception" r <*> decodeAPat ap

-- ---------------------------------------------------------------------------
-- Support terms and attacks
-- ---------------------------------------------------------------------------

encodeAssurance :: Assurance -> SExpr
encodeAssurance a = case a of
  AssuranceNone -> SAtom (tagToString TNone)
  AssuranceTrusted -> SAtom (tagToString TTrusted)
  AssuranceCert (Cert (BackendId b) v (TheoryDigest h) payload) ->
    tagged TCert [SAtom b, SAtom (show v), SAtom h, payload]

decodeAssurance :: SExpr -> Decode Assurance
decodeAssurance e = case e of
  SAtom s
    | parseTag s == Just TNone -> ok AssuranceNone
    | parseTag s == Just TTrusted -> ok AssuranceTrusted
  SList (SAtom k : _)
    | parseTag k == Just TCert -> do
        [b, v, h, payload] <- matchTagged "assurance" TCert 4 e
        name <- atomText "assurance" b
        version <- parseNatText "assurance" v
        digest <- atomText "assurance" h
        ok
          ( AssuranceCert
              (Cert (BackendId name) version (TheoryDigest digest) payload)
          )
  _ -> werr "assurance" ("malformed assurance: " ++ show e)

encodeSupportTerm :: SupportTerm -> SExpr
encodeSupportTerm t = case t of
  SLeaf (LeafId l) -> tagged TLeaf [SAtom l]
  SRule (RuleId r) theta prems disch holes assurance ->
    tagged
      TInst
      [ SAtom r
      , tagged TSubst [SList [SAtom x, encodeTerm tm] | (Param x, tm) <- theta]
      , tagged TPremises (map encodeSupportTerm prems)
      , tagged
          TDischarges
          [ SList [SAtom q, encodeSupportTerm w]
          | (QuestionId q, w) <- disch
          ]
      , tagged THoles [SAtom o | ObligationId o <- holes]
      , tagged TAssurance [encodeAssurance assurance]
      ]

decodeSupportTerm :: SExpr -> Decode SupportTerm
decodeSupportTerm e = case e of
  SList (SAtom k : _)
    | parseTag k == Just TLeaf -> do
        [l] <- matchTagged "support term" TLeaf 1 e
        SLeaf . LeafId <$> atomText "support term" l
    | parseTag k == Just TInst -> do
        [r, substS, premsS, dischS, holesS, assuranceS] <-
          matchTagged "support term" TInst 6 e
        r' <- RuleId <$> atomText "support term" r
        theta <- do
          fs <- sectionFields "substitution" TSubst substS
          mapM decodeBinding fs
        prems <- do
          fs <- sectionFields "premises" TPremises premsS
          mapM decodeSupportTerm fs
        disch <- do
          fs <- sectionFields "discharges" TDischarges dischS
          mapM decodeDischarge fs
        holes <- do
          fs <- sectionFields "holes" THoles holesS
          mapM (fmap ObligationId . atomText "holes") fs
        assurance <- do
          [a] <- matchTagged "assurance" TAssurance 1 assuranceS
          decodeAssurance a
        ok (SRule r' theta prems disch holes assurance)
  _ -> werr "support term" ("malformed support term: " ++ show e)
  where
    decodeBinding b = case b of
      SList [x, tm] -> do
        x' <- Param <$> atomText "substitution" x
        tm' <- decodeTerm tm
        ok (x', tm')
      _ -> werr "substitution" ("malformed binding: " ++ show b)
    decodeDischarge d = case d of
      SList [q, w] -> do
        q' <- QuestionId <$> atomText "discharges" q
        w' <- decodeSupportTerm w
        ok (q', w')
      _ -> werr "discharges" ("malformed discharge: " ++ show d)

encodePosition :: Position -> SExpr
encodePosition steps = tagged TPos (map encodeStep steps)
  where
    encodeStep (StepPremise i) = tagged TPrem [SAtom (show i)]
    encodeStep (StepQuestion (QuestionId q)) = tagged TQues [SAtom q]

decodePosition :: SExpr -> Decode Position
decodePosition e = do
  fs <- sectionFields "position" TPos e
  mapM decodeStep fs
  where
    decodeStep s = case s of
      SList (SAtom k : _)
        | parseTag k == Just TPrem -> do
            [i] <- matchTagged "position" TPrem 1 s
            StepPremise <$> parseNatText "position" i
        | parseTag k == Just TQues -> do
            [q] <- matchTagged "position" TQues 1 s
            StepQuestion . QuestionId <$> atomText "position" q
      _ -> werr "position" ("malformed position step: " ++ show s)

encodeAttack :: Attack -> SExpr
encodeAttack k = case k of
  Rebut (ArgId w) (ArgId u) -> tagged TRebut [SAtom w, SAtom u]
  Undercut (ArgId w) (ArgId u) pos ->
    tagged TUndercut [SAtom w, SAtom u, encodePosition pos]
  Undermine (ArgId w) (ArgId u) pos ->
    tagged TUndermine [SAtom w, SAtom u, encodePosition pos]

decodeAttack :: SExpr -> Decode Attack
decodeAttack e = case e of
  SList (SAtom k : _)
    | parseTag k == Just TRebut -> do
        [w, u] <- matchTagged "attack" TRebut 2 e
        Rebut <$> fmap ArgId (atomText "attack" w) <*> fmap ArgId (atomText "attack" u)
    | parseTag k == Just TUndercut -> do
        [w, u, pos] <- matchTagged "attack" TUndercut 3 e
        Undercut
          <$> fmap ArgId (atomText "attack" w)
          <*> fmap ArgId (atomText "attack" u)
          <*> decodePosition pos
    | parseTag k == Just TUndermine -> do
        [w, u, pos] <- matchTagged "attack" TUndermine 3 e
        Undermine
          <$> fmap ArgId (atomText "attack" w)
          <*> fmap ArgId (atomText "attack" u)
          <*> decodePosition pos
  _ -> werr "attack" ("malformed attack: " ++ show e)

-- ---------------------------------------------------------------------------
-- Units
-- ---------------------------------------------------------------------------

encodeUnit :: Unit -> SExpr
encodeUnit u =
  tagged TUnit . concat $
    [ [ tagged
          TPolicy
          [ tagged TRules (map encodeRule (unitRules u))
          , tagged TContraries (map encodeContrary (unitContraries u))
          , tagged TExceptions (map encodeException (unitExceptions u))
          ]
      ]
    , [ tagged
          TTheories
          [ tagged TTheory (SAtom h : map encodeAtom ps)
          | (TheoryDigest h, ps) <- unitTheories u
          ]
      | not (null (unitTheories u))
      ]
    , [ tagged
          TLeaves
          [ tagged TLeaf [SAtom l, encodeAtom p]
          | (LeafId l, p) <- unitLeaves u
          ]
      | not (null (unitLeaves u))
      ]
    , [ tagged
          TArgs
          [ tagged TArg [SAtom a, encodeSupportTerm t]
          | (ArgId a, t) <- unitArgs u
          ]
      | not (null (unitArgs u))
      ]
    , [tagged TAttacks (map encodeAttack (unitAttacks u)) | not (null (unitAttacks u))]
    , [tagged TQueries (map encodeAtom (unitQueries u)) | not (null (unitQueries u))]
    ]

decodeUnitM :: SExpr -> Decode Unit
decodeUnitM e = do
  sections <- sectionFields "unit" TUnit e
  (policyS, rest1) <- takeSection TPolicy sections
  (theoriesS, rest2) <- takeSection TTheories rest1
  (leavesS, rest3) <- takeSection TLeaves rest2
  (argsS, rest4) <- takeSection TArgs rest3
  (attacksS, rest5) <- takeSection TAttacks rest4
  (queriesS, rest6) <- takeSection TQueries rest5
  case rest6 of
    s : _ -> werr "unit" ("unexpected section: " ++ show s)
    [] -> ok ()
  (rules, contraries, exceptions) <- decodePolicy policyS
  theories <- decodeTheories theoriesS
  leaves <- decodeLeaves leavesS
  args <- decodeArgs argsS
  attacks <- decodeAttacks attacksS
  queries <- decodeQueries queriesS
  checkArgInvariants args attacks
  ok
    Unit
      { unitRules = rules
      , unitContraries = contraries
      , unitExceptions = exceptions
      , unitTheories = theories
      , unitLeaves = leaves
      , unitArgs = args
      , unitAttacks = attacks
      , unitQueries = queries
      }
  where
    -- Peel one optional section; sections are ordered and occur at most once.
    takeSection t ss = case ss of
      s : rest
        | SList (SAtom k : _) <- s
        , parseTag k == Just t -> ok (Just s, rest)
      _ -> ok (Nothing, ss)

    decodePolicy Nothing = ok ([], [], [])
    decodePolicy (Just s) = do
      [rulesS, contrariesS, exceptionsS] <- matchTagged "policy" TPolicy 3 s
      rules <- sectionFields "policy rules" TRules rulesS >>= mapM decodeRule
      contraries <-
        sectionFields "policy contraries" TContraries contrariesS
          >>= mapM decodeContrary
      exceptions <-
        sectionFields "policy exceptions" TExceptions exceptionsS
          >>= mapM decodeException
      ok (rules, contraries, exceptions)

    decodeTheories Nothing = ok []
    decodeTheories (Just s) = do
      fs <- sectionFields "theories" TTheories s
      mapM decodeTheory fs
      where
        decodeTheory t = do
          fields <- sectionFields "theory" TTheory t
          case fields of
            h : atoms -> do
              digest <- TheoryDigest <$> atomText "theory" h
              props <- mapM decodeAtom atoms
              ok (digest, props)
            [] -> werr "theory" ("malformed theory: " ++ show t)

    decodeLeaves Nothing = ok []
    decodeLeaves (Just s) = do
      fs <- sectionFields "leaves" TLeaves s
      mapM decodeLeaf fs
      where
        decodeLeaf l = do
          [lid, atom] <- matchTagged "leaf" TLeaf 2 l
          l' <- LeafId <$> atomText "leaf" lid
          p <- decodeAtom atom
          ok (l', p)

    decodeArgs Nothing = ok []
    decodeArgs (Just s) = do
      fs <- sectionFields "args" TArgs s
      mapM decodeArg fs
      where
        decodeArg a = do
          [aid, sterm] <- matchTagged "arg" TArg 2 a
          a' <- ArgId <$> atomText "arg" aid
          t <- decodeSupportTerm sterm
          ok (a', t)

    decodeAttacks Nothing = ok []
    decodeAttacks (Just s) =
      sectionFields "attacks" TAttacks s >>= mapM decodeAttack

    decodeQueries Nothing = ok []
    decodeQueries (Just s) =
      sectionFields "queries" TQueries s >>= mapM decodeAtom

    -- Wire well-formedness (R14), identical in both drivers: argument
    -- identifiers are unique and every attack endpoint is declared.
    checkArgInvariants args attacks = do
      let ids = map fst args
      case firstDuplicate ids of
        Just (ArgId a) -> werr "args" ("duplicate argument id: " ++ show a)
        Nothing -> ok ()
      mapM_ checkEndpoint (concatMap endpoints attacks)
      where
        firstDuplicate xs = go xs []
          where
            go [] _ = Nothing
            go (x : rest) seen
              | x `elem` seen = Just x
              | otherwise = go rest (x : seen)
        endpoints k = case k of
          Rebut w u -> [w, u]
          Undercut w u _ -> [w, u]
          Undermine w u _ -> [w, u]
        checkEndpoint (ArgId a)
          | ArgId a `elem` map fst args = ok ()
          | otherwise =
              werr "attacks" ("attack endpoint is not a declared argument: " ++ show a)

-- | Decode a unit from its S-expression form (the whole grammar; see module
-- docs). This is 'decodeUnitM' unwrapped for callers.
decodeUnit :: SExpr -> Either WireError Unit
decodeUnit = runDecode . decodeUnitM

-- | Decode a whole wire file: exactly one top-level form, then the unit
-- grammar. Text parse errors and grammar errors are both R14 codec failures.
decodeUnitFile :: String -> Either WireError Unit
decodeUnitFile = runDecode . decodeUnitFileM

decodeUnitFileM :: String -> Decode Unit
decodeUnitFileM input =
  case parseSExpr input of
    Left (ParseError ln col msg) ->
      werr
        ("line " ++ show ln ++ ", column " ++ show col)
        msg
    Right e -> decodeUnitM e

-- ---------------------------------------------------------------------------
-- Verdicts
-- ---------------------------------------------------------------------------

-- | The checker output both drivers print (plan D16 contract).
data Verdict
  = -- | accepted: grounded labels for every argument (declaration order),
    -- the compiled closure edges (ascending), and one status per query atom
    VAccept
      { verdictLabels :: [(Int, Label)]
      , verdictEdges :: [(Int, Int)]
      , verdictStatuses :: [(Prop, Status)]
      }
  | -- | rejected: the rejection class atom only (located diagnostics live in
    -- the checker's result type, not on the wire)
    VReject Rejection
  deriving (Eq, Show)

encodeVerdict :: Verdict -> SExpr
encodeVerdict v = case v of
  VReject r -> tagged TVerdict [SAtom (tagToString TReject), encodeRejection r]
  VAccept lbls edges statuses ->
    tagged
      TVerdict
      [ SAtom (tagToString TAccept)
      , tagged
          TLabels
          [ SList
              [ SAtom (show i)
              , SAtom
                  ( tagToString
                      (case l of LIn -> TIn; LOut -> TOut; LUndec -> TUndec)
                  )
              ]
          | (i, l) <- lbls
          ]
      , tagged TEdges [SList [SAtom (show i), SAtom (show j)] | (i, j) <- edges]
      , tagged
          TStatuses
          [ tagged TStatus [encodeAtom p, encodeStatus s]
          | (p, s) <- statuses
          ]
      ]
  where
    encodeStatus s =
      SAtom
        ( tagToString
            ( case s of
                Gap -> TGap
                Justified -> TJustified
                Contested -> TContested
                Defeated -> TDefeated
            )
        )

encodeRejection :: Rejection -> SExpr
encodeRejection r =
  SAtom
    ( tagToString
        ( case r of
            DuplicateRule -> TDupRule
            DuplicateArgument -> TDupArgument
            IncompleteArgument -> TIncompleteArgument
            MissingConflict -> TMissingConflict
            RejectClass c -> rejectClassTag c
        )
    )

rejectClassTag :: RejectClass -> Tag
rejectClassTag c = case c of
  R1 -> TR1; R3 -> TR3; R4 -> TR4; R5 -> TR5; R6 -> TR6; R7 -> TR7
  R10 -> TR10; R11 -> TR11; R12 -> TR12; R13 -> TR13

-- | Decode a verdict (the dual of 'encodeVerdict'; used by the conformance
-- tests and any consumer of a driver's output).
decodeVerdict :: SExpr -> Either WireError Verdict
decodeVerdict = runDecode . decodeVerdictM

decodeVerdictM :: SExpr -> Decode Verdict
decodeVerdictM e = case e of
  SList (SAtom v : SAtom h : rest)
    | parseTag v == Just TVerdict
    , parseTag h == Just TReject
    , [payload] <- rest -> VReject <$> decodeRejection payload
    | parseTag v == Just TVerdict
    , parseTag h == Just TAccept
    , [labelsS, edgesS, statusesS] <- rest -> do
        lbls <- sectionFields "verdict labels" TLabels labelsS >>= mapM decodeLabel
        edges <- sectionFields "verdict edges" TEdges edgesS >>= mapM decodeEdge
        statuses <-
          sectionFields "verdict statuses" TStatuses statusesS
            >>= mapM decodeStatusEntry
        ok (VAccept lbls edges statuses)
  _ -> werr "verdict" ("malformed verdict: " ++ show e)
  where
    decodeLabel l = case l of
      SList [i, a] -> do
        i' <- parseNatText "verdict label" i
        l' <- case a of
          SAtom s
            | parseTag s == Just TIn -> ok LIn
            | parseTag s == Just TOut -> ok LOut
            | parseTag s == Just TUndec -> ok LUndec
          _ -> werr "verdict label" ("expected in|out|undec, got " ++ show a)
        ok (i', l')
      _ -> werr "verdict label" ("malformed label: " ++ show l)
    decodeEdge ed = case ed of
      SList [i, j] -> do
        i' <- parseNatText "verdict edge" i
        j' <- parseNatText "verdict edge" j
        ok (i', j')
      _ -> werr "verdict edge" ("malformed edge: " ++ show ed)
    decodeStatusEntry se = do
      [atom, statusS] <- matchTagged "verdict status" TStatus 2 se
      p <- decodeAtom atom
      s <- case statusS of
        SAtom x
          | parseTag x == Just TGap -> ok Gap
          | parseTag x == Just TJustified -> ok Justified
          | parseTag x == Just TContested -> ok Contested
          | parseTag x == Just TDefeated -> ok Defeated
        _ ->
          werr
            "verdict status"
            ("expected gap|justified|contested|defeated, got " ++ show statusS)
      ok (p, s)
    decodeRejection r = case r of
      SAtom s -> case parseTag s of
        Just TDupRule -> ok DuplicateRule
        Just TDupArgument -> ok DuplicateArgument
        Just TIncompleteArgument -> ok IncompleteArgument
        Just TMissingConflict -> ok MissingConflict
        Just t
          | Just c <- tagRejectClass t -> ok (RejectClass c)
        _ -> werr "verdict reject" ("unknown rejection: " ++ show s)
      _ -> werr "verdict reject" ("malformed rejection: " ++ show r)
    tagRejectClass t = lookup t [(rejectClassTag c, c) | c <- [minBound .. maxBound]]
