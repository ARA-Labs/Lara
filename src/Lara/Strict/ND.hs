-- | The required v0.1 reference strict backend: intuitionistic natural
-- deduction for implication and falsum (@docs/strict-backend-decision.md@ §4.1;
-- spec §5).
--
-- This adapter is deliberately __modest__: it certifies only the propositional
-- consequences visible in its own encoding. Domain laws (arithmetic, temporal,
-- code behavior) are __not__ hidden axioms here — they remain explicit theory
-- dependencies or trusted policy rules. Keeping a real reference adapter (not
-- just the abstract seam) is what makes the backend interface concrete rather
-- than hypothetical.
--
-- == Formulas and certificates
--
-- > phi ::= a | false | phi -> phi                       -- backend formulas
-- > e   ::= hyp i | lam phi e | app e e | abort phi e     -- de Bruijn certificates
--
-- Certificates use __de Bruijn indices__, so binding and dependency checking
-- are syntactic. An index counts the enclosing @lam@ binders outward; an index
-- that overshoots the binders refers into the __free context__, which is the
-- source premises followed by the selected theory entries.
--
-- == Encoding and the obligations it discharges
--
-- > encode_ND(p) = atom(canonicalSerialize(nf p))
--
-- Here the canonical serialization is the shared tagged, UTF-8 byte-length
-- framed atom key. Its closed decoder is a left inverse, so
--
-- > p ≡ q   iff   nf p == nf q   iff   encodeND p == encodeND q,
--
-- which is exactly __normalization fidelity__ (decision doc §2 obligation 2):
-- the forward direction preserves source identity, the reverse prevents the
-- encoder from collapsing distinct propositions.
--
-- The type checker discharges the remaining obligations:
--
--   * __decidable replay__ (obligation 1) — 'inferType' is a total structural
--     recursion;
--   * __certificate soundness__ (obligation 3) — Theorem 4: a well-typed
--     certificate is Boolean-valid, proved by induction on the typing
--     derivation (the property suite exercises this by construction);
--   * __dependency accountability + exactness__ (obligation 4 / Lemma 5) — the
--     free de Bruijn indices of an accepted certificate are /exactly/ the
--     premise/theory slots its derivation depends on; 'inferType' returns that
--     set and the seam maps it to 'Dependency' values.
module Lara.Strict.ND
  ( -- * Backend formulas and certificates
    Formula (..)
  , AtomId -- ^ opaque: constructor hidden; see "Lara.Strict.ND.Internal"
  , atomIdString
  , Cert (..)
    -- * Wire grammar
  , Tag (..)
  , tagToString
  , parseTag
  , decodeFormula
  , decodeCert
    -- * Encoding
  , FrameTag (..)
  , frameTagToString
  , parseFrameTag
  , encodeND
  , encodeAtomKey
  , decodeAtomKey
    -- * Type checking (the replay)
  , inferType
    -- * The registered adapter
  , ndBackendId
  , mkNDBackend
  ) where

import Data.Char (ord)
import Data.Set (Set)
import qualified Data.Set as Set

import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..), nf)
import Lara.Strict.ND.Internal (AtomId (..))
import Lara.Strict
  ( Backend (..)
  , BackendId (..)
  , Dependency (..)
  , SExpr (..)
  , TheoryDigest
  )

-- ---------------------------------------------------------------------------
-- Backend formulas and certificates
-- ---------------------------------------------------------------------------

-- | A backend formula. Atoms are the injective serialization of a normalized
-- source proposition (see 'encodeND'); the producer references a source
-- proposition by that same string.
data Formula
  = FAtom AtomId
  | FFalse
  | FImp Formula Formula
  deriving (Eq, Ord, Show)

-- | Project the underlying serialization out of an 'AtomId'. This is the only
-- public way to observe an atom's payload; there is no public way to construct
-- one except through 'encodeND' or the closed wire decoder.
atomIdString :: AtomId -> String
atomIdString (AtomId s) = s

-- | A natural-deduction certificate in de Bruijn form.
data Cert
  = -- | @hyp i@: the assumption at de Bruijn index @i@
    Hyp Integer
  | -- | @lam phi e@: implication introduction; @phi@ is the (annotated) antecedent
    Lam Formula Cert
  | -- | @app f x@: implication elimination
    App Cert Cert
  | -- | @abort phi e@: falsum elimination to @phi@; @e@ must conclude @false@
    Abort Formula Cert
  deriving (Eq, Ord, Show)

-- ---------------------------------------------------------------------------
-- Encoding
-- ---------------------------------------------------------------------------

-- | The closed vocabulary of the framed source-atom key.
data FrameTag = FTAtom | FTNum | FTStr | FTCon | FTLen
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The single source of truth for frame-tag wire spellings.
frameTagToString :: FrameTag -> String
frameTagToString FTAtom = "A"
frameTagToString FTNum = "N"
frameTagToString FTStr = "S"
frameTagToString FTCon = "C"
frameTagToString FTLen = "L"

-- | Parse a frame tag, inverse to 'frameTagToString'.
parseFrameTag :: String -> Maybe FrameTag
parseFrameTag s =
  lookup s [(frameTagToString t, t) | t <- [minBound .. maxBound]]

utf8Length :: String -> Int
utf8Length = sum . map width
  where
    width c
      | ord c <= 0x7f = 1
      | ord c <= 0x7ff = 2
      | ord c <= 0xffff = 3
      | otherwise = 4

frame :: String -> String
frame s = show (utf8Length s) ++ ":" ++ s

renderFrames :: [String] -> String
renderFrames = concatMap frame

encodeTermKey :: Term -> String
encodeTermKey (TNum n) = renderFrames [frameTagToString FTNum, n]
encodeTermKey (TStr s) = renderFrames [frameTagToString FTStr, s]
encodeTermKey (TCon (FunSym k) ts) =
  renderFrames
    ( [frameTagToString FTCon, k, frameTagToString FTLen, show (length ts)]
        ++ map encodeTermKey ts
    )

-- | Exact, prefix-free source-atom wire key shared with the Lean adapter.
encodeAtomKey :: Prop -> String
encodeAtomKey (Prop (Pred p) ts) =
  renderFrames
    ( [frameTagToString FTAtom, p, frameTagToString FTLen, show (length ts)]
        ++ map encodeTermKey ts
    )

takeUtf8 :: Int -> String -> Maybe (String, String)
takeUtf8 n
  | n < 0 = const Nothing
  | otherwise = go n []
  where
    go 0 acc rest = Just (reverse acc, rest)
    go _ _ [] = Nothing
    go left acc (c : cs)
      | width c <= left = go (left - width c) (c : acc) cs
      | otherwise = Nothing
    width c
      | ord c <= 0x7f = 1
      | ord c <= 0x7ff = 2
      | ord c <= 0xffff = 3
      | otherwise = 4

parseCanonicalNat :: String -> Maybe Integer
parseCanonicalNat s =
  case reads s :: [(Integer, String)] of
    [(n, "")]
      | n >= 0
      , show n == s -> Just n
    _ -> Nothing

parseFrame :: String -> Maybe (String, String)
parseFrame input = do
  let (digits, colonRest) = break (== ':') input
  rest <- case colonRest of
    ':' : xs -> Just xs
    _ -> Nothing
  n <- parseCanonicalNat digits
  if n <= toInteger (maxBound :: Int)
    then takeUtf8 (fromInteger n) rest
    else Nothing

decodeFrames :: String -> Maybe [String]
decodeFrames "" = Just []
decodeFrames input = do
  (field, rest) <- parseFrame input
  (field :) <$> decodeFrames rest

decodeTermKey :: String -> Maybe Term
decodeTermKey key = do
  fields <- decodeFrames key
  case fields of
    [tag, payload] ->
      case parseFrameTag tag of
        Just FTNum -> Just (TNum payload)
        Just FTStr -> Just (TStr payload)
        _ -> Nothing
    conTag : k : lenTag : count : children
      | parseFrameTag conTag == Just FTCon
      , parseFrameTag lenTag == Just FTLen -> do
          n <- parseCanonicalNat count
          if toInteger (length children) == n
            then TCon (FunSym k) <$> mapM decodeTermKey children
            else Nothing
    _ -> Nothing

-- | Inverse of 'encodeAtomKey'; rejects non-canonical lengths/counts, unknown
-- tags, truncation, trailing bytes, and child-count mismatches.
decodeAtomKey :: String -> Maybe Prop
decodeAtomKey key = do
  fields <- decodeFrames key
  case fields of
    atomTag : p : lenTag : count : children
      | parseFrameTag atomTag == Just FTAtom
      , parseFrameTag lenTag == Just FTLen -> do
          n <- parseCanonicalNat count
          if toInteger (length children) == n
            then Prop (Pred p) <$> mapM decodeTermKey children
            else Nothing
    _ -> Nothing

-- | @encode_ND(p) = atom(encodeAtomKey(nf p))@.
encodeND :: Prop -> Formula
encodeND = FAtom . AtomId . encodeAtomKey . nf

-- ---------------------------------------------------------------------------
-- Type checking (the replay)
-- ---------------------------------------------------------------------------

-- | Infer the formula of a certificate and the set of __free context slots__ it
-- depends on.
--
-- @'inferType' locals free e@ checks @e@ where @locals@ are the formulas bound
-- by enclosing @lam@s (innermost first) and @free@ is the fixed free context
-- (premise encodings followed by theory encodings). It returns the derived
-- formula and the set of indices /into @free@/ actually consulted — a locally
-- bound assumption contributes nothing (Lemma 5).
--
-- Total and deterministic: every constructor has one rule and every lookup is
-- range-checked, so it is a decidable replay (obligation 1).
inferType :: [Formula] -> [Formula] -> Cert -> Either String (Formula, Set Int)
inferType locals free = go locals
  where
    nFree = length free
    nFreeInteger = toInteger nFree

    go :: [Formula] -> Cert -> Either String (Formula, Set Int)
    go ls (Hyp i)
      | i < 0 = Left ("negative de Bruijn index " ++ show i)
      | i < nLoc =
          let localIndex = fromInteger i
           in Right (ls !! localIndex, Set.empty) -- locally bound: not a dependency
      | otherwise =
          let j = i - nLoc -- into the free context
           in if j < nFreeInteger
                then
                  let freeIndex = fromInteger j
                   in Right (free !! freeIndex, Set.singleton freeIndex)
                else
                  Left
                    ( "free de Bruijn index out of range: hyp "
                        ++ show i
                        ++ " with "
                        ++ show (length ls)
                        ++ " binder(s) and "
                        ++ show nFree
                        ++ " free slot(s)"
                    )
      where
        nLoc = toInteger (length ls)
    go ls (Lam phi e) = do
      (psi, deps) <- go (phi : ls) e
      Right (FImp phi psi, deps)
    go ls (App f x) = do
      (ft, fdeps) <- go ls f
      (xt, xdeps) <- go ls x
      case ft of
        FImp a b
          | a == xt -> Right (b, Set.union fdeps xdeps)
          | otherwise ->
              Left ("application mismatch: expected " ++ show a ++ ", got " ++ show xt)
        other -> Left ("application of a non-implication: " ++ show other)
    go ls (Abort phi e) = do
      (et, deps) <- go ls e
      case et of
        FFalse -> Right (phi, deps)
        other -> Left ("abort of a non-false proof: " ++ show other)

-- ---------------------------------------------------------------------------
-- SExpr wire decoding (the closed decoder)
-- ---------------------------------------------------------------------------

-- The certificate reaches the adapter as an opaque 'SExpr'; only this module
-- decodes it (closed registration). Wire grammar:
--
-- > formula := (atom STRING) | false | (imp FORMULA FORMULA)
-- > cert    := (hyp N) | (lam FORMULA CERT) | (app CERT CERT) | (abort FORMULA CERT)

-- | The closed set of wire keywords. Every grammar keyword is a constructor,
-- so the tag vocabulary is symbolic: the concrete on-the-wire strings live in
-- exactly one place ('tagToString' \/ 'parseTag'), and any producer that needs
-- to emit the same grammar (e.g. the conformance tests) shares this table
-- rather than duplicating string literals. 'tagToString' and 'parseTag' are
-- mutually inverse.
data Tag = TAtom | TFalse | TImp | THyp | TLam | TApp | TAbort
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The on-the-wire spelling of a keyword. The single source of truth for the
-- grammar's concrete syntax.
tagToString :: Tag -> String
tagToString TAtom = "atom"
tagToString TFalse = "false"
tagToString TImp = "imp"
tagToString THyp = "hyp"
tagToString TLam = "lam"
tagToString TApp = "app"
tagToString TAbort = "abort"

-- | Parse a wire keyword, inverse to 'tagToString'. Derived from the same table
-- by enumerating 'Tag', so it cannot drift out of sync.
parseTag :: String -> Maybe Tag
parseTag s = lookup s [(tagToString t, t) | t <- [minBound .. maxBound]]

decodeFormula :: SExpr -> Either String Formula
decodeFormula (SAtom s) | parseTag s == Just TFalse = Right FFalse
decodeFormula (SList [SAtom k, SAtom s]) | parseTag k == Just TAtom = Right (FAtom (AtomId s))
decodeFormula (SList [SAtom k, a, b]) | parseTag k == Just TImp =
  FImp <$> decodeFormula a <*> decodeFormula b
decodeFormula e = Left ("malformed ND formula: " ++ show e)

decodeCert :: SExpr -> Either String Cert
decodeCert (SList [SAtom k, SAtom n]) | parseTag k == Just THyp =
  case parseCanonicalNat n of
    Just i -> Right (Hyp i)
    _ -> Left ("malformed de Bruijn index: " ++ show n)
decodeCert (SList [SAtom k, phi, e]) | parseTag k == Just TLam =
  Lam <$> decodeFormula phi <*> decodeCert e
decodeCert (SList [SAtom k, f, x]) | parseTag k == Just TApp =
  App <$> decodeCert f <*> decodeCert x
decodeCert (SList [SAtom k, phi, e]) | parseTag k == Just TAbort =
  Abort <$> decodeFormula phi <*> decodeCert e
decodeCert e = Left ("malformed ND certificate: " ++ show e)

-- ---------------------------------------------------------------------------
-- The registered adapter
-- ---------------------------------------------------------------------------

-- | The reference natural-deduction backend identifier: @nd\@1@.
ndBackendId :: BackendId
ndBackendId = BackendId {backendName = "nd", backendVersion = 1}

-- | Build the reference adapter with a __fixed__ theory table mapping each
-- admissible 'TheoryDigest' to its finite list of source propositions (the
-- theory entries, encoded on demand). Closed registration: the table is fixed
-- at construction; an artifact selects a digest but cannot change or extend it.
--
-- On a strict step the adapter encodes the premises and goal, resolves the
-- theory digest to its entry encodings, decodes and replays the certificate,
-- checks that it concludes @encode_ND(goal)@, and returns the consulted
-- 'Dependency' set: a free slot below @length premises@ is a 'PremiseSlot', at
-- or above it a 'TheoryEntry'.
mkNDBackend :: [(TheoryDigest, [Prop])] -> Backend
mkNDBackend theories =
  Backend
    { backendId = ndBackendId
    , runBackend = run
    }
  where
    run :: TheoryDigest -> [Prop] -> Prop -> SExpr -> Either String (Set Dependency)
    run digest premises goal certSExpr =
      case lookup digest theories of
        Nothing -> Left ("unknown theory digest: " ++ show digest)
        Just theoryProps -> do
          cert <- decodeCert certSExpr
          let nPrem = length premises
              free = map encodeND premises ++ map encodeND theoryProps
          (concl, slots) <- inferType [] free cert
          let goalF = encodeND goal
          if concl == goalF
            then Right (Set.map (toDependency nPrem) slots)
            else
              Left
                ( "certificate concludes "
                    ++ show concl
                    ++ " but the goal encodes to "
                    ++ show goalF
                )

    toDependency :: Int -> Int -> Dependency
    toDependency nPrem slot
      | slot < nPrem = PremiseSlot slot
      | otherwise = TheoryEntry (slot - nPrem)
