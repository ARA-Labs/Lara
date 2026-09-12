{-# LANGUAGE DerivingVia #-}

-- | The S-expression wire codec (the N11 differential anchor).
--
-- One textual S-expression format carries validated checker-boundary
-- 'CheckInput's and identity-bearing 'Verdict's between the Haskell production
-- runtime and the Lean executable semantics (@lean/Lara/Driver.lean@).
-- Both drivers print verdicts through this exact codec, so differential testing
-- is byte comparison (plan D16). This is the /only/ wire front end: there is
-- deliberately no JSON checker-input codec.
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
-- == Check-input grammar (input)
--
-- @
-- \<check-input\> ::= (check-input \<replay-id\> \<unit\>)
-- \<replay-id\>   ::= (replay-id (core lara-core\@0.2) (policy ID)
--                       (backends (backend ID STRING)*) (theories STRING*)
--                       (artifact STRING))
-- \<unit\>     ::= (unit \<sigma-sec\>? \<policy-sec\>? \<theories-sec\>? \<leaves-sec\>?
--                        \<args-sec\>? \<attacks-sec\>? \<queries-sec\>?)
-- \<sigma-sec\>    ::= (sigma (sorts ID*) (cons \<con-sig\>*) (preds \<pred-sig\>*))
-- \<con-sig\>      ::= (con ID (args SORT*) SORT)
-- \<pred-sig\>     ::= (pred ID (args SORT*))
-- SORT           ::= Num | Str | ID
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
-- \<verdict\> ::= (verdict \<replay-id\> accept
--                    (labels (NAT in | out | undec)*) (edges (NAT NAT)*)
--                    (statuses (status \<atom\> STATUS)*)
--                    \<conditional-sec\>?)
--               | (verdict \<replay-id\> reject REJECTION)
-- \<conditional-sec\> ::= (conditional (status \<atom\> CORE-STATUS)+)
-- STATUS    ::= CORE-STATUS | evidence-blocked
-- CORE-STATUS ::= gap | justified | contested | defeated
-- REJECTION ::= duplicate-rule | duplicate-argument | incomplete-argument
--             | missing-conflict | R1 | R2 | R3 | R4 | R5 | R6 | R7
--             | R9 | R10 | R11 | R12 | R13
-- @
--
-- Labels cover every compiled argument in declaration order; edges are the
-- compiled closure edges in ascending @(i, j)@ order; statuses follow the
-- query order of the unit.
--
-- @evidence-blocked@ is the public status of a query whose four-state label
-- could have been changed by §4.3 quarantine deleting material under it
-- (issue #76): the label is not the answer, it is a conditional diagnostic, and
-- it moves to the @conditional@ section. That section is present exactly when
-- some status is @evidence-blocked@, and it lists those queries in query order,
-- so a verdict with nothing blocked is byte-identical to the pre-#76 format. The rejection payload is the class atom only —
-- located diagnostics live in the checker's result type ("Lara.Check",
-- Task 1), not on the wire.
module Lara.Wire
  ( -- * Textual S-expression codec
    ParseError (..)
  , parseSExpr
  , parseSExprBS
  , printSExpr
  , maxDepth
    -- * The closed tag vocabulary
  , Tag (..)
  , tagToString
  , parseTag
  , rejectClassTag
    -- * Unit and checker-input codecs
  , WireError (..)
  , decodeUnit
  , encodeUnit
  , decodeReplayId
  , encodeReplayId
  , coreVersionText
  , decodeCheckInput
  , encodeCheckInput
  , decodeCheckInputFile
  , decodeCheckInputFileBS
    -- * The shared @\<atom\>@ production
    --
    -- | Additive exports (issue #303): the multi-artifact map's composite verdict
    -- ("Lara.Map.Wire") reports statuses against propositions, and there must
    -- be exactly one @\<atom\>@ syntax for a 'Prop' across every LARA grammar
    -- — a second spelling would be a second thing to keep in step with
    -- @lean/Lara/Driver.lean@. Nothing else about this codec changes: the
    -- production was already here, and no existing byte moves.
  , encodeAtom
  , decodeAtomSExpr
    -- * Verdict codec
  , PublicStatus (..)
  , conditionalStatus
  , isPublished
  , Outcome (..)
  , Verdict (..)
  , decodeVerdict
  , encodeVerdict
  ) where

import Data.Bits ((.&.))
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import Data.Char (ord)
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Word (Word8)

import Lara.AST hiding (Reject)
import Lara.Replay
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

-- | Bytes allowed in a bare (unquoted) atom. This mirrors 'isBareChar'
-- exactly: the bare set is a subset of printable ASCII, so a byte is bare iff
-- the 'Char' it denotes is, and every byte @>= 0x80@ is non-bare just as every
-- non-ASCII 'Char' is.
isBareByte :: Word8 -> Bool
isBareByte b =
  b >= 0x21
    && b <= 0x7e
    && b /= 0x28 -- '('
    && b /= 0x29 -- ')'
    && b /= 0x3b -- ';'
    && b /= 0x22 -- '"'
    && b /= 0x5c -- '\\'

-- | Bytes the reader skips between forms.
isSpaceByte :: Word8 -> Bool
isSpaceByte b = b == 0x20 || b == 0x09 || b == 0x0a || b == 0x0d

-- | Number of code points in a UTF-8 span: bytes @b@ with
-- @b .&. 0xC0 /= 0x80@ start a code point, continuation bytes do not.
cpLen :: ByteString -> Int
cpLen = B.foldl' (\n b -> if b .&. 0xC0 /= 0x80 then n + 1 else n) 0

-- | Decode the single UTF-8 code point at the cursor, for the error messages
-- that render the offending character ('show' of a 'Char'). Off the hot path,
-- so it may be as slow as it likes. 'Nothing' means the bytes at the cursor
-- are not valid UTF-8.
peekCodePoint :: ByteString -> Maybe Char
peekCodePoint bs = case B.uncons bs of
  Nothing -> Nothing
  Just (b0, _) ->
    let width
          | b0 >= 0xf0 = 4
          | b0 >= 0xe0 = 3
          | b0 >= 0xc0 = 2
          | otherwise = 1
     in case TE.decodeUtf8' (B.take width bs) of
          Right t | [c] <- T.unpack t -> Just c
          _ -> Nothing

-- | Parser state: remaining input and the 1-based cursor.
--
-- __Column invariant.__ @pCol@ counts /code points/, not bytes, because the
-- Lean reference driver (@lean\/Lara\/Driver.lean@) parses a @List Char@ and
-- both drivers must locate the same codec error. The input is UTF-8; bare
-- atoms are ASCII by construction ('isBareByte'), so there byte length and
-- code-point length coincide and 'B.length' is used directly. Only quoted-atom
-- payloads and @;@ comments can carry multi-byte sequences, and those spans go
-- through 'bump'.
data P = P
  { pInput :: !ByteString
  , pLine :: !Int
  , pCol :: !Int
  }

perr :: P -> String -> Either ParseError a
perr p msg = Left (ParseError (pLine p) (pCol p) msg)

-- | Advance the cursor over a consumed span, counting lines and code points.
-- Does not touch 'pInput' — the caller sets the remaining slice.
bump :: ByteString -> P -> P
bump span_ p = case B.elemIndexEnd 0x0a span_ of
  Nothing -> p {pCol = pCol p + cpLen span_}
  Just i ->
    p
      { pLine = pLine p + B.count 0x0a span_
      , pCol = 1 + cpLen (B.drop (i + 1) span_)
      }

-- | Advance the cursor over one ASCII byte that is not a newline.
step1 :: ByteString -> P -> P
step1 rest p = p {pInput = rest, pCol = pCol p + 1}

-- | Skip whitespace and @;@ comments.
skipSpace :: P -> P
skipSpace p =
  let (ws, rest) = B.span isSpaceByte (pInput p)
      p' = if B.null ws then p else (bump ws p) {pInput = rest}
   in case B.uncons (pInput p') of
        -- The @;@ itself is dropped without a column bump, matching the reader
        -- this replaced (and the Lean driver) character for character.
        Just (0x3b, afterSemi) -> skipSpace (skipComment p' {pInput = afterSemi})
        _ -> p'
  where
    skipComment q =
      let (cmt, rest) = B.break (== 0x0a) (pInput q)
       in (bump cmt q) {pInput = rest}

-- | Maximum S-expression nesting depth. Bounds parser recursion so a
-- pathologically nested input (@(((… )))@) is a located R14 codec error (CLI
-- exit 2) rather than a GHC stack overflow — which the CLI cannot map to an exit
-- code, and which @scripts/differential.sh@ would otherwise misread as a checker
-- rejection (exit 1). Comfortably above any real artifact's structural depth:
-- @scripts\/differential.sh@ measures the deepest committed @.sexp@\/@.laramap@\/
-- @.lara@ tree on every run and fails if the margin ever narrows.
--
-- Part of the shared reader contract, not a Haskell-only boundary: Lean's
-- @Lara.Driver.maxDepth@ carries the same value and its reader refuses at the
-- same depth with the same message and column, so both runtimes reject an
-- over-deep input identically (#331). Exported so the gates that pin that
-- agreement name one constant rather than a second copy of the literal.
maxDepth :: Int
maxDepth = 10000

-- | Parse exactly one top-level form from UTF-8 bytes; a second form is an
-- error. This is the primitive; 'parseSExpr' is the 'String' wrapper.
parseSExprBS :: ByteString -> Either ParseError SExpr
parseSExprBS input = do
  let start = skipSpace (P input 1 1)
  (e, rest) <- parseForm 0 start
  let rest' = skipSpace rest
  if B.null (pInput rest')
    then Right e
    else perr rest' "expected a single S-expression, found more input"

-- | Parse exactly one top-level form; a second form is an error.
--
-- A thin wrapper over 'parseSExprBS'. The round trip through UTF-8 is exact,
-- and the code-point column discipline of 'P' makes the two agree on error
-- positions as well as on results.
parseSExpr :: String -> Either ParseError SExpr
parseSExpr = parseSExprBS . TE.encodeUtf8 . T.pack

parseForm :: Int -> P -> Either ParseError (SExpr, P)
parseForm depth p
  | depth > maxDepth =
      perr p ("maximum S-expression nesting depth exceeded (" ++ show maxDepth ++ ")")
  | otherwise = case B.uncons (pInput p) of
      Just (0x28, rest) -> parseList (step1 rest p) []
      Just (0x22, rest) -> parseQuoted (step1 rest p) []
      Just (b, _)
        | isBareByte b ->
            let (tok, rest) = B.span isBareByte (pInput p)
                -- Bare atoms are ASCII, so the byte length is the column delta
                -- and 'BC.unpack' is an exact decode.
                p' = p {pInput = rest, pCol = pCol p + B.length tok}
             in Right (SAtom (BC.unpack tok), p')
        | otherwise -> case peekCodePoint (pInput p) of
            Just c -> perr p ("unexpected character " ++ show c)
            Nothing -> perr p "invalid UTF-8 byte sequence"
      Nothing -> perr p "unexpected end of input"
  where
    parseList q acc =
      let q' = skipSpace q
       in case B.uncons (pInput q') of
            Just (0x29, rest) -> Right (SList (reverse acc), step1 rest q')
            Nothing -> perr q' "unclosed list"
            _ -> do
              (e, q'') <- parseForm (depth + 1) q'
              parseList q'' (e : acc)
    -- Quoted payloads accumulate raw byte slices and are UTF-8 decoded once at
    -- the closing quote. Escape scanning on bytes is safe because @"@, @\\@ and
    -- @n@ are ASCII and UTF-8 is self-synchronizing, so none of them can occur
    -- inside a multi-byte sequence.
    parseQuoted q acc =
      let (chunk, rest) = B.break isQuoteStop (pInput q)
          q' = (bump chunk q) {pInput = rest}
       in case B.uncons rest of
            Nothing -> perr q' "unterminated string literal"
            Just (0x22, rest') -> case decodeQuotedPayload (chunk : acc) of
              Just s -> Right (SAtom s, step1 rest' q')
              Nothing -> perr q' "invalid UTF-8 in string literal"
            Just (_, rest') -> escape (chunk : acc) q' rest'
    -- @q@ is positioned at the backslash; @rest@ is what follows it.
    escape acc q rest = case B.uncons rest of
      Nothing -> perr q "unterminated escape sequence"
      Just (c, rest')
        | c == 0x22 -> parseQuoted (adv2 rest') (B.singleton 0x22 : acc)
        | c == 0x5c -> parseQuoted (adv2 rest') (B.singleton 0x5c : acc)
        | c == 0x6e -> parseQuoted (adv2 rest') (B.singleton 0x0a : acc)
        | otherwise -> case peekCodePoint rest of
            Just ch -> perr q ("invalid escape sequence \\" ++ [ch])
            -- The escape marker is well formed and the bad byte is exactly the
            -- one after it, so locate the codec fault there rather than at the
            -- backslash. (A payload that only fails to decode at the closing
            -- quote is still reported there: 'decodeQuotedPayload' decodes the
            -- accumulated chunks in one batch and has no source offset to
            -- report.)
            Nothing -> perr q {pCol = pCol q + 1} "invalid UTF-8 in string literal"
        where
          adv2 s = q {pInput = s, pCol = pCol q + 2}
    isQuoteStop b = b == 0x22 || b == 0x5c

-- | Decode an accumulated quoted payload (chunks in reverse order).
-- 'Nothing' is invalid UTF-8. The common case is one all-ASCII slice.
decodeQuotedPayload :: [ByteString] -> Maybe String
decodeQuotedPayload chunks
  | B.all (< 0x80) bs = Just (BC.unpack bs)
  | otherwise = case TE.decodeUtf8' bs of
      Right t -> Just (T.unpack t)
      Left _ -> Nothing
  where
    bs = case chunks of
      [one] -> one
      _ -> B.concat (reverse chunks)

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
-- spellings live in exactly one place ('tagToString'); @tagTable@ derives the
-- reverse lookup from that function. The Lean driver textually mirrors the
-- 'tagToString' table.
-- (The conformance tests intentionally spell raw string literals as independent
-- ground truth — do not \"fix\" them to consume this table.)
data Tag
  = -- checker input and replay identity
    TCheckInput | TReplayId | TCore | TBackends | TBackend | TArtifact
    -- unit structure
  | TUnit | TPolicy | TRules | TRule | TMode | TParams | TPremises
  | TConclusion | TQuestions | TQuestion | TAllowTrusted | TCertifiers
  | TCertifier | TContraries | TContrary | TExceptions | TException
  | TTheories | TTheory | TLeaves | TLeaf | TArgs | TArg | TAttacks
  | TQueries | TSubst | TDischarges | THoles | TAssurance | TCert
  | TPos | TPrem | TQues | TInst
    -- duplicate-report groups (spec §4.3)
  | TGroups | TGroup | TQuarantine
    -- the many-sorted signature Sigma (spec §2, §3.4; lara-core@0.2)
  | TSigma | TSorts | TCons | TPreds | TPred
    -- modes, necessity, booleans, assurance
  | TStrict | TDefeasible | TMandatory | TOptional | TTrue | TFalse
  | TNone | TTrusted
    -- patterns, terms, atoms
  | TVar | TNumLit | TStrLit | TConApp | TAtom | TApat
    -- attacks
  | TRebut | TUndercut | TUndermine
    -- verdicts
  | TVerdict | TAccept | TReject | TLabels | TEdges | TStatuses | TStatus
  | TConditional
  | TIn | TOut | TUndec | TGap | TJustified | TContested | TDefeated
  | TEvidenceBlocked
    -- rejection outcomes
  | TDupRule | TDupArgument | TIncompleteArgument | TMissingConflict
  | TR1 | TR2 | TR3 | TR4 | TR5 | TR6 | TR7 | TR9 | TR10 | TR11 | TR12 | TR13
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The on-the-wire spelling of a keyword.
tagToString :: Tag -> String
tagToString t = case t of
  TCheckInput -> "check-input"; TReplayId -> "replay-id"
  TCore -> "core"; TBackends -> "backends"; TBackend -> "backend"
  TArtifact -> "artifact"
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
  TGroups -> "groups"; TGroup -> "group"; TQuarantine -> "quarantine"
  TSigma -> "sigma"; TSorts -> "sorts"; TCons -> "cons"; TPreds -> "preds"
  TPred -> "pred"
  TStrict -> "strict"; TDefeasible -> "defeasible"
  TMandatory -> "mandatory"; TOptional -> "optional"
  TTrue -> "true"; TFalse -> "false"; TNone -> "none"; TTrusted -> "trusted"
  TVar -> "var"; TNumLit -> "num"; TStrLit -> "str"; TConApp -> "con"
  TAtom -> "atom"; TApat -> "apat"
  TRebut -> "rebut"; TUndercut -> "undercut"; TUndermine -> "undermine"
  TVerdict -> "verdict"; TAccept -> "accept"; TReject -> "reject"
  TLabels -> "labels"; TEdges -> "edges"; TStatuses -> "statuses"
  TStatus -> "status"; TConditional -> "conditional"
  TIn -> "in"; TOut -> "out"; TUndec -> "undec"
  TGap -> "gap"; TJustified -> "justified"; TContested -> "contested"
  TDefeated -> "defeated"; TEvidenceBlocked -> "evidence-blocked"
  TDupRule -> "duplicate-rule"; TDupArgument -> "duplicate-argument"
  TIncompleteArgument -> "incomplete-argument"
  TMissingConflict -> "missing-conflict"
  TR1 -> "R1"; TR2 -> "R2"; TR3 -> "R3"; TR4 -> "R4"; TR5 -> "R5"; TR6 -> "R6"
  TR7 -> "R7"; TR9 -> "R9"; TR10 -> "R10"; TR11 -> "R11"; TR12 -> "R12"
  TR13 -> "R13"

{-# NOINLINE tagTable #-}
tagTable :: Map.Map String Tag
tagTable = Map.fromList [(tagToString t, t) | t <- [minBound .. maxBound]]

-- | Parse a wire keyword, inverse to 'tagToString'. @tagTable@ is derived from
-- 'tagToString' by enumerating 'Tag'. A spelling collision would break that
-- inverse because 'Map.fromList' keeps one value per key. @prop_tagTableTotal@
-- (WireSpec) rejects collisions, and @Lara.Driver.tagToString_injective@ proves
-- the same invariant for the mirrored Lean vocabulary.
parseTag :: String -> Maybe Tag
parseTag s = Map.lookup s tagTable

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

-- | A proposition in the @\<atom\>@ form: @(atom PRED \<term\>*)@.
--
-- Exported so that a grammar layered above @lara-core\@0.2@ — the
-- @map-verdict\@1@ composite verdict of "Lara.Map.Wire" — can carry
-- propositions in /this/ syntax instead of inventing a second one. The bytes
-- are unchanged; only the visibility is new.
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

-- | 'decodeAtom' at the public boundary: the dual of 'encodeAtom' for a caller
-- outside this module, which cannot name the internal 'Decode' monad. A thin
-- @runDecode@ wrapper, so the located 'WireError' a nested atom produces is
-- exactly the one the core decoder would have produced.
decodeAtomSExpr :: SExpr -> Either WireError Prop
decodeAtomSExpr = runDecode . decodeAtom

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
      , -- Presentation-only (grammar App. B.4) and deliberately not on the
        -- wire: 'encodeRule' names its eight encoded fields explicitly, so a
        -- decoded rule has no labels. See 'Lara.AST.rulePremiseLabels'.
        rulePremiseLabels = []
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

-- | The wire spelling of a sort __reference__: the two base sorts print as
-- their reserved names, a declared sort as its name. Sort /declarations/ are
-- bare 'SortName' atoms, so @(sort Num)@ is representable and rejected by the
-- checker as base-sort shadowing rather than being unspellable.
encodeSort :: Sort -> SExpr
encodeSort = SAtom . sortText

decodeSort :: SExpr -> Decode Sort
decodeSort e = sortFromText <$> atomText "sort" e

encodeSigma :: Sigma -> SExpr
encodeSigma sg =
  tagged
    TSigma
    [ tagged TSorts [SAtom n | SortName n <- sigmaSorts sg]
    , tagged
        TCons
        [ tagged
            TConApp
            [ SAtom k
            , tagged TArgs (map encodeSort (conArgs c))
            , encodeSort (conResult c)
            ]
        | c <- sigmaCons sg
        , let FunSym k = conSym c
        ]
    , tagged
        TPreds
        [ tagged TPred [SAtom h, tagged TArgs (map encodeSort (predArgs p))]
        | p <- sigmaPreds sg
        , let Pred h = predSym p
        ]
    ]

decodeSigma :: SExpr -> Decode Sigma
decodeSigma e = do
  [sortsS, consS, predsS] <- matchTagged "sigma" TSigma 3 e
  sorts <-
    sectionFields "sigma sorts" TSorts sortsS
      >>= mapM (fmap SortName . atomText "sigma sorts")
  cons <- sectionFields "sigma cons" TCons consS >>= mapM decodeConSig
  preds <- sectionFields "sigma preds" TPreds predsS >>= mapM decodePredSig
  ok (Sigma sorts cons preds)
  where
    decodeConSig c = do
      [nameV, argsV, resV] <- matchTagged "sigma con" TConApp 3 c
      k <- FunSym <$> atomText "sigma con" nameV
      args <- sectionFields "sigma con args" TArgs argsV >>= mapM decodeSort
      res <- decodeSort resV
      ok (ConSig k args res)
    decodePredSig p = do
      [nameV, argsV] <- matchTagged "sigma pred" TPred 2 p
      h <- Pred <$> atomText "sigma pred" nameV
      args <- sectionFields "sigma pred args" TArgs argsV >>= mapM decodeSort
      ok (PredSig h args)

encodeUnit :: Unit -> SExpr
encodeUnit u =
  tagged TUnit . concat $
    [ -- The signature (lara-core@0.2). Emitted only when non-empty, so a
      -- symbol-free unit is unaffected; a real unit always carries one, since
      -- strict mode makes an empty Σ accept nothing that mentions a symbol.
      [encodeSigma (unitSigma u) | unitSigma u /= emptySigma]
    , [ tagged
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
    , -- Duplicate-report groups (spec §4.3). Emitted only when non-empty, so
      -- group-free units are byte-identical to the pre-groups wire; the
      -- conflict mode rides as the section's first field (the default
      -- 'QuarantineOnConflict' is spelled @quarantine@, never omitted here).
      [ tagged
          TGroups
          ( SAtom (tagToString (groupModeTag (unitGroupMode u)))
              : [ tagged TGroup [SAtom g, SList [SAtom l | LeafId l <- ms]]
                | DupGroup (GroupId g) ms <- unitGroups u
                ]
          )
      | not (null (unitGroups u))
      ]
    ]

-- | The wire spelling of a duplicate-report-group conflict mode (spec §4.3),
-- kept in one place per the closed-vocabulary discipline.
groupModeTag :: GroupConflictMode -> Tag
groupModeTag m = case m of
  QuarantineOnConflict -> TQuarantine
  RejectOnConflict -> TReject

decodeUnitM :: SExpr -> Decode Unit
decodeUnitM e = do
  sections <- sectionFields "unit" TUnit e
  (sigmaS, rest0) <- takeSection TSigma sections
  (policyS, rest1) <- takeSection TPolicy rest0
  (theoriesS, rest2) <- takeSection TTheories rest1
  (leavesS, rest3) <- takeSection TLeaves rest2
  (argsS, rest4) <- takeSection TArgs rest3
  (attacksS, rest5) <- takeSection TAttacks rest4
  (queriesS, rest6) <- takeSection TQueries rest5
  (groupsS, rest7) <- takeSection TGroups rest6
  case rest7 of
    s : _ -> werr "unit" ("unexpected section: " ++ show s)
    [] -> ok ()
  sigma <- maybe (ok emptySigma) decodeSigma sigmaS
  (rules, contraries, exceptions) <- decodePolicy policyS
  theories <- decodeTheories theoriesS
  leaves <- decodeLeaves leavesS
  args <- decodeArgs argsS
  attacks <- decodeAttacks attacksS
  queries <- decodeQueries queriesS
  (groups, groupMode) <- decodeGroups groupsS
  checkArgInvariants args attacks
  checkGroupInvariants groups leaves
  ok
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

    -- The groups section (spec §4.3): first field is the conflict mode, then
    -- one @(group id (member*))@ per declared duplicate-report group. Absent
    -- section ⇒ no groups and the default quarantine mode.
    decodeGroups Nothing = ok ([], QuarantineOnConflict)
    decodeGroups (Just s) = do
      fs <- sectionFields "groups" TGroups s
      case fs of
        modeE : groupEs -> do
          mode <- decodeGroupMode modeE
          groups <- mapM decodeGroup groupEs
          ok (groups, mode)
        [] -> werr "groups" "groups section missing its conflict mode"
      where
        decodeGroupMode (SAtom t)
          | parseTag t == Just TQuarantine = ok QuarantineOnConflict
          | parseTag t == Just TReject = ok RejectOnConflict
        decodeGroupMode other =
          werr "groups mode" ("unknown group conflict mode: " ++ show other)
        decodeGroup g = do
          [gid, membersE] <- matchTagged "group" TGroup 2 g
          g' <- GroupId <$> atomText "group" gid
          members <- decodeMembers membersE
          ok (DupGroup g' members)
        decodeMembers (SList ms) = mapM (fmap LeafId . atomText "group member") ms
        decodeMembers other =
          werr "group members" ("malformed member list: " ++ show other)

    -- Wire well-formedness (R14) for groups, identical in both drivers: at
    -- least two distinct members, all declared leaves, and unique group ids.
    -- A one-member "group" or a member without a leaf is malformed elaborator
    -- output, not a data conflict.
    checkGroupInvariants groups leaves = do
      case firstDup [g | DupGroup g _ <- groups] of
        Just (GroupId g) -> werr "groups" ("duplicate group id: " ++ show g)
        Nothing -> ok ()
      mapM_ checkGroup groups
      where
        declared = map fst leaves
        checkGroup (DupGroup (GroupId g) members) = do
          case firstDup members of
            Just (LeafId l) ->
              werr "group" ("group " ++ show g ++ " repeats member: " ++ show l)
            Nothing -> ok ()
          if length members < 2
            then werr "group" ("group " ++ show g ++ " has fewer than two members")
            else ok ()
          mapM_ checkMember members
          where
            checkMember l
              | l `elem` declared = ok ()
              | otherwise =
                  werr
                    "group"
                    ("group " ++ show g ++ " member is not a declared leaf: " ++ show l)

    firstDup :: Eq a => [a] -> Maybe a
    firstDup = go []
      where
        go _ [] = Nothing
        go seen (x : rest)
          | x `elem` seen = Just x
          | otherwise = go (x : seen) rest

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

encodeReplayId :: ReplayId -> SExpr
encodeReplayId replayId =
  tagged
    TReplayId
    [ tagged TCore [SAtom (coreVersionText (replayCore replayId))]
    , tagged TPolicy [SAtom policy]
    , tagged
        TBackends
        [tagged TBackend [SAtom backend, SAtom version] | (BackendId backend, version) <- replayBackends replayId]
    , tagged TTheories [SAtom theory | TheoryDigest theory <- replayTheories replayId]
    , tagged TArtifact [SAtom artifact]
    ]
  where
    PolicyId policy = replayPolicy replayId
    Digest artifact = replayArtifact replayId

decodeReplayId :: SExpr -> Either WireError ReplayId
decodeReplayId = runDecode . decodeReplayIdM

decodeReplayIdM :: SExpr -> Decode ReplayId
decodeReplayIdM value = do
  [coreSection, policySection, backendsSection, theoriesSection, artifactSection] <-
    matchTagged "replay-id" TReplayId 5 value
  [coreValue] <- matchTagged "replay-id core" TCore 1 coreSection
  coreText <- atomText "replay-id core" coreValue
  core <-
    if coreText == coreVersionText LaraCoreV02
      then ok LaraCoreV02
      else werr "replay-id" ("unsupported core version: " ++ show coreText)
  [policyValue] <- matchTagged "replay-id policy" TPolicy 1 policySection
  policy <- PolicyId <$> atomText "replay-id policy" policyValue
  backendValues <- sectionFields "replay-id backends" TBackends backendsSection
  backends <- mapM decodeBackend backendValues
  theoryValues <- sectionFields "replay-id theories" TTheories theoriesSection
  theories <- mapM (fmap TheoryDigest . atomText "replay-id theories") theoryValues
  [artifactValue] <- matchTagged "replay-id artifact" TArtifact 1 artifactSection
  artifact <- Digest <$> atomText "replay-id artifact" artifactValue
  replayResult "replay-id" (mkReplayId core policy backends theories artifact)
  where
    decodeBackend backendValue = do
      [backendName, backendVersion] <-
        matchTagged "replay-id backend" TBackend 2 backendValue
      (,)
        <$> fmap BackendId (atomText "replay-id backend" backendName)
        <*> atomText "replay-id backend" backendVersion

encodeCheckInput :: CheckInput -> SExpr
encodeCheckInput input =
  tagged TCheckInput [encodeReplayId (inputReplayId input), encodeUnit (inputUnit input)]

decodeCheckInput :: SExpr -> Either WireError CheckInput
decodeCheckInput = runDecode . decodeCheckInputM

decodeCheckInputM :: SExpr -> Decode CheckInput
decodeCheckInputM value = do
  [replayValue, unitValue] <- matchTagged "check-input" TCheckInput 2 value
  replayId <- decodeReplayIdM replayValue
  unit <- decodeUnitM unitValue
  case mkCheckInput replayId unit of
    Left err@(DuplicateUnitTheory _) -> replayResult "unit theories" (Left err)
    result -> replayResult "check-input" result

-- | Decode a whole check-input file from its UTF-8 bytes. This is the
-- primitive; 'decodeCheckInputFile' is the 'String' wrapper.
decodeCheckInputFileBS :: ByteString -> Either WireError CheckInput
decodeCheckInputFileBS = runDecode . decodeCheckInputFileM

-- | Decode a whole check-input file. A thin wrapper over
-- 'decodeCheckInputFileBS'.
decodeCheckInputFile :: String -> Either WireError CheckInput
decodeCheckInputFile = decodeCheckInputFileBS . TE.encodeUtf8 . T.pack

decodeCheckInputFileM :: ByteString -> Decode CheckInput
decodeCheckInputFileM input =
  case parseSExprBS input of
    Left (ParseError line column message) ->
      werr
        ("line " ++ show line ++ ", column " ++ show column)
        message
    Right value -> decodeCheckInputM value

replayResult :: String -> Either ReplayError a -> Decode a
replayResult context = either (werr context . replayErrorMessage) ok

coreVersionText :: CoreVersion -> String
coreVersionText LaraCoreV02 = "lara-core@0.2"

-- ---------------------------------------------------------------------------
-- Verdicts
-- ---------------------------------------------------------------------------

-- | The public status of a queried claim.
--
-- 'Published' is the ordinary four-state answer. 'EvidenceBlocked' carries the
-- four-state label the checker computed on the program it actually saw, which —
-- because §4.3 quarantine removed material under the claim — is a __conditional
-- diagnostic and not the answer__ (spec §4.3, issue #76; the rule is
-- "Lara.Blocked", the metatheory @lean\/Lara\/Blocked.lean@).
--
-- Blockedness lives /inside/ the status rather than in a parallel list of
-- blocked propositions, so a blocked query with no status entry, a blocked list
-- permuted against the statuses, and a duplicated blocked entry are all
-- unrepresentable — the @conditional@ wire section is then a pure projection of
-- 'verdictStatuses' and consumers pattern-match instead of cross-referencing.
data PublicStatus
  = Published Status
  | EvidenceBlocked Status
  deriving (Eq, Show)

-- | The four-state label under a public status: the answer for 'Published', the
-- conditional diagnostic for 'EvidenceBlocked'. Callers that need the /public/
-- reading must match on the constructor — this projection deliberately forgets
-- the distinction, so it is only for consumers rendering the diagnostic.
conditionalStatus :: PublicStatus -> Status
conditionalStatus ps = case ps of
  Published status -> status
  EvidenceBlocked status -> status

-- | Whether a public status is the ordinary four-state answer.
isPublished :: PublicStatus -> Bool
isPublished ps = case ps of
  Published _ -> True
  EvidenceBlocked _ -> False

-- | The checker outcome, nested under its replay identity.
--
-- On the wire the honest value is the headline: the @statuses@ section prints
-- @evidence-blocked@ for a blocked query and the conditional label moves to a
-- trailing @conditional@ section, which is emitted exactly when some query is
-- blocked. A verdict with nothing blocked is byte-identical to the pre-#76
-- format, and a consumer that has never heard of @evidence-blocked@ fails to
-- decode rather than silently reading a status that deletion inflated.
data Outcome
  = Accept
      { verdictLabels :: [(Int, Label)]
      , verdictEdges :: [(Int, Int)]
      , verdictStatuses :: [(Prop, PublicStatus)]
      }
  | Reject Rejection
  deriving (Eq, Show)

-- | The checker output both drivers print, carrying the input replay identity.
data Verdict = Verdict
  { verdictReplayId :: ReplayId
  , verdictOutcome :: Outcome
  }
  deriving (Eq, Show)

encodeVerdict :: Verdict -> SExpr
encodeVerdict (Verdict replayId outcome) =
  case outcome of
    Reject rejection ->
      tagged TVerdict [encodeReplayId replayId, SAtom (tagToString TReject), encodeRejection rejection]
    Accept labels edges statuses ->
      tagged TVerdict $
        [ encodeReplayId replayId
        , SAtom (tagToString TAccept)
        , tagged
            TLabels
            [SList [SAtom (show index), encodeLabel label] | (index, label) <- labels]
        , tagged
            TEdges
            [SList [SAtom (show source), SAtom (show target)] | (source, target) <- edges]
        , tagged
            TStatuses
            [ tagged TStatus [encodeAtom proposition, encodePublicStatusValue status]
            | (proposition, status) <- statuses
            ]
        ]
          -- The conditional section is a projection of the statuses, emitted
          -- exactly when some query is blocked (spec §4.3, issue #76).
          ++ [ tagged
                 TConditional
                 [ tagged TStatus [encodeAtom proposition, encodeStatusValue status]
                 | (proposition, EvidenceBlocked status) <- statuses
                 ]
             | any (not . isPublished . snd) statuses
             ]

encodeLabel :: Label -> SExpr
encodeLabel label =
  SAtom . tagToString $ case label of
    LIn -> TIn
    LOut -> TOut
    LUndec -> TUndec

-- | The public status token: @evidence-blocked@ hides the conditional label of a
-- quarantine-affected query (spec §4.3, issue #76).
encodePublicStatusValue :: PublicStatus -> SExpr
encodePublicStatusValue ps = case ps of
  Published status -> encodeStatusValue status
  EvidenceBlocked _ -> SAtom (tagToString TEvidenceBlocked)

encodeStatusValue :: Status -> SExpr
encodeStatusValue status =
  SAtom . tagToString $ case status of
    Gap -> TGap
    Justified -> TJustified
    Contested -> TContested
    Defeated -> TDefeated

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
  R1 -> TR1; R2 -> TR2; R3 -> TR3; R4 -> TR4; R5 -> TR5; R6 -> TR6; R7 -> TR7
  R9 -> TR9; R10 -> TR10; R11 -> TR11; R12 -> TR12; R13 -> TR13

-- | Decode a verdict (the dual of 'encodeVerdict'; used by the conformance
-- tests and any consumer of a driver's output).
decodeVerdict :: SExpr -> Either WireError Verdict
decodeVerdict = runDecode . decodeVerdictM

decodeVerdictM :: SExpr -> Decode Verdict
decodeVerdictM value = case value of
  SList [SAtom verdictTag, replayValue, SAtom outcomeTag, rejectionValue]
    | parseTag verdictTag == Just TVerdict
    , parseTag outcomeTag == Just TReject -> do
        replayId <- decodeReplayIdM replayValue
        rejection <- decodeRejection rejectionValue
        ok (Verdict replayId (Reject rejection))
  SList (SAtom verdictTag : replayValue : SAtom outcomeTag : sections)
    | parseTag verdictTag == Just TVerdict
    , parseTag outcomeTag == Just TAccept
    , Just (labelsSection, edgesSection, statusesSection, conditionalSection) <-
        acceptSections sections -> do
        replayId <- decodeReplayIdM replayValue
        labels <- sectionFields "verdict labels" TLabels labelsSection >>= mapM decodeLabel
        edges <- sectionFields "verdict edges" TEdges edgesSection >>= mapM decodeEdge
        publicStatuses <-
          sectionFields "verdict statuses" TStatuses statusesSection
            >>= mapM decodePublicStatusEntry
        conditional <- case conditionalSection of
          Nothing -> ok []
          Just section -> do
            entries <-
              sectionFields "verdict conditional" TConditional section
                >>= mapM decodeStatusEntry
            -- The encoder emits the section exactly when something is blocked,
            -- so a present-but-empty one is non-canonical wire text (R14) — not
            -- an accept with nothing blocked.
            if null entries
              then
                werr
                  "verdict conditional"
                  "conditional section is present but empty"
              else ok entries
        -- The two sections must line up entry for entry: a conditional entry
        -- with no @evidence-blocked@ status (or the reverse) is a malformed
        -- verdict (R14), never a silently-dropped diagnostic.
        (statuses, leftover) <- resolveStatuses conditional publicStatuses
        if null leftover
          then ok (Verdict replayId (Accept labels edges statuses))
          else
            werr
              "verdict conditional"
              ("conditional entries with no evidence-blocked query: " ++ show (map fst leftover))
  _ -> werr "verdict" ("malformed verdict: " ++ show value)
  where
    decodeLabel labelValue = case labelValue of
      SList [indexValue, encodedLabel] -> do
        index <- parseNatText "verdict label" indexValue
        label <- case encodedLabel of
          SAtom text
            | parseTag text == Just TIn -> ok LIn
            | parseTag text == Just TOut -> ok LOut
            | parseTag text == Just TUndec -> ok LUndec
          _ ->
            werr
              "verdict label"
              ("expected in|out|undec, got " ++ show encodedLabel)
        ok (index, label)
      _ -> werr "verdict label" ("malformed label: " ++ show labelValue)

    decodeEdge edgeValue = case edgeValue of
      SList [sourceValue, targetValue] -> do
        source <- parseNatText "verdict edge" sourceValue
        target <- parseNatText "verdict edge" targetValue
        ok (source, target)
      _ -> werr "verdict edge" ("malformed edge: " ++ show edgeValue)

    decodeStatusEntry statusValue = do
      [atomValue, encodedStatus] <-
        matchTagged "verdict status" TStatus 2 statusValue
      proposition <- decodeAtom atomValue
      status <- case encodedStatus of
        SAtom text
          | parseTag text == Just TGap -> ok Gap
          | parseTag text == Just TJustified -> ok Justified
          | parseTag text == Just TContested -> ok Contested
          | parseTag text == Just TDefeated -> ok Defeated
        _ ->
          werr
            "verdict status"
            ("expected gap|justified|contested|defeated, got " ++ show encodedStatus)
      ok (proposition, status)

    -- The accept sections: the pre-#76 three, plus the @conditional@ section
    -- that appears exactly when a query is @evidence-blocked@ (spec §4.3).
    acceptSections sections = case sections of
      [labelsSection, edgesSection, statusesSection] ->
        Just (labelsSection, edgesSection, statusesSection, Nothing)
      [labelsSection, edgesSection, statusesSection, conditionalSection] ->
        Just (labelsSection, edgesSection, statusesSection, Just conditionalSection)
      _ -> Nothing

    -- A status entry as printed: @Nothing@ for @evidence-blocked@, whose
    -- conditional label lives in the @conditional@ section.
    decodePublicStatusEntry statusValue = do
      [atomValue, encodedStatus] <-
        matchTagged "verdict status" TStatus 2 statusValue
      proposition <- decodeAtom atomValue
      status <- case encodedStatus of
        SAtom text
          | parseTag text == Just TEvidenceBlocked -> ok Nothing
          | parseTag text == Just TGap -> ok (Just Gap)
          | parseTag text == Just TJustified -> ok (Just Justified)
          | parseTag text == Just TContested -> ok (Just Contested)
          | parseTag text == Just TDefeated -> ok (Just Defeated)
        _ ->
          werr
            "verdict status"
            ( "expected gap|justified|contested|defeated|evidence-blocked, got "
                ++ show encodedStatus
            )
      ok (proposition, status)

    -- Walk both sections in step, so the pairing is positional rather than by
    -- lookup: a repeated query keeps its own conditional entry.
    resolveStatuses conditional [] = ok ([], conditional)
    resolveStatuses conditional ((proposition, status) : rest) = case status of
      Just s -> do
        (resolved, leftover) <- resolveStatuses conditional rest
        ok ((proposition, Published s) : resolved, leftover)
      Nothing -> case conditional of
        (conditionalProposition, s) : conditionalRest
          | conditionalProposition == proposition -> do
              (resolved, leftover) <- resolveStatuses conditionalRest rest
              ok ((proposition, EvidenceBlocked s) : resolved, leftover)
        _ ->
          werr
            "verdict status"
            ("evidence-blocked query has no matching conditional entry: " ++ show proposition)

    decodeRejection rejectionValue = case rejectionValue of
      SAtom text -> case parseTag text of
        Just TDupRule -> ok DuplicateRule
        Just TDupArgument -> ok DuplicateArgument
        Just TIncompleteArgument -> ok IncompleteArgument
        Just TMissingConflict -> ok MissingConflict
        Just tag
          | Just rejectionClass <- tagRejectClass tag ->
              ok (RejectClass rejectionClass)
        _ -> werr "verdict reject" ("unknown rejection: " ++ show text)
      _ ->
        werr
          "verdict reject"
          ("malformed rejection: " ++ show rejectionValue)

    tagRejectClass tag =
      lookup tag [(rejectClassTag rejectionClass, rejectionClass) | rejectionClass <- [minBound .. maxBound]]
