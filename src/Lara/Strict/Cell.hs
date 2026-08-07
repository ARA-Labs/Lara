-- | Shared cell helpers for the rational-arithmetic strict backends: the
-- canonical numeral grammars, the premise-cell convention, and the premise
-- slot-reference wire sub-grammar @(prem N)@.
--
-- @ra\@1@ ("Lara.Strict.RA") and the ordered-comparison backend @ord\@1@
-- certify goals over measured cells and share the same three sub-problems:
-- decoding a slot reference from the opaque certificate, parsing canonical
-- numerals (the 'Lara.Prop.canonNum' image), and extracting the one numeric
-- literal a consulted premise carries. One definition, two importers — each
-- backend keeps its own closed top-level certificate tag (@radrop@ in
-- "Lara.Strict.RA"; @ordcmp@ in the ordered-comparison backend), while the
-- slot-reference sub-grammar has exactly one home: the @\"prem\"@ spelling
-- lives in this module's 'Tag' table and nowhere else.
--
-- == Where the shared stages sit: the @ord\@1@ rejection funnel
--
-- The funnel of the ordered-comparison backend that consumes these helpers,
-- marking which stages are shared Cell code:
--
-- >         (digest, premises, goal, cert)
-- >                     │
-- >    ┌────────────────▼─────────────────┐
-- >    │ 1 digest registered?             │──no──▶ reject: unknown digest
-- >    ├──────────────────────────────────┤
-- >    │ 2 decode (ordcmp (prem N)(prem M)│──no──▶ reject: malformed cert     ┐ shared:
-- >    │   [Cell: decodeSlot, canonical   │                                   │ decodeSlot,
-- >    │    naturals]                     │                                   │ parseCanonicalNat
-- >    ├──────────────────────────────────┤                                   │
-- >    │ 3 goal = num_lt/num_le over two  │──no──▶ reject: bad goal           │ shared:
-- >    │   canonical decimals             │                                   │ parseDecimal
-- >    │   [Cell: parseDecimal]           │                                   │
-- >    ├──────────────────────────────────┤                                   │
-- >    │ 4 slots < nPrem? premiseCell on  │──no──▶ reject: slot out of range, │ shared:
-- >    │   each (exactly one literal)     │        slot names a theory entry, │ premiseCell
-- >    │   [Cell: premiseCell]            │        or 0-or-2+ literals        ┘
-- >    ├──────────────────────────────────┤
-- >    │ 5 cells == goal numerals?        │──no──▶ reject: wrong cell (L or R)  ord-only
-- >    ├──────────────────────────────────┤
-- >    │ 6 relation holds (exact ℚ)?      │──no──▶ reject: relation fails       ord-only
-- >    └────────────────┬─────────────────┘
-- >                     ▼
-- >       accept, deps = {PremiseSlot N, PremiseSlot M}
module Lara.Strict.Cell
  ( -- * Wire sub-grammar: premise slot references
    Tag (..)
  , tagToString
  , parseTag
  , decodeSlot
    -- * Canonical numeral grammars
  , parseCanonicalNat
  , parseCanonicalInt
  , parseDecimal
    -- * The premise-cell convention
  , premiseCell
  ) where

import Data.Ratio ((%))

import Lara.Prop (Prop (..), Term (..), nf)
import Lara.Strict (SExpr (..))

-- ---------------------------------------------------------------------------
-- Wire sub-grammar: premise slot references
-- ---------------------------------------------------------------------------

-- | The closed set of shared wire keywords ('Lara.Strict.ND.Tag' discipline:
-- the concrete spellings live in exactly one table). Only the slot-reference
-- keyword is shared; each backend's own keywords stay in that backend's table.
data Tag = TPrem
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The on-the-wire spelling of a keyword.
tagToString :: Tag -> String
tagToString TPrem = "prem"

-- | Parse a wire keyword, inverse to 'tagToString'.
parseTag :: String -> Maybe Tag
parseTag s = lookup s [(tagToString t, t) | t <- [minBound .. maxBound]]

-- | Decode a slot reference @(prem N)@ with @N@ a canonical natural bounded
-- by the host 'Int'. The first argument labels the calling backend in the
-- malformed-reference message — @ra\@1@ passes @\"RA\"@, keeping its
-- rejection strings byte-identical to the pre-factoring adapter.
decodeSlot :: String -> SExpr -> Either String Int
decodeSlot _ (SList [SAtom k, SAtom n])
  | parseTag k == Just TPrem =
      case parseCanonicalNat n of
        Just i
          | i <= toInteger (maxBound :: Int) -> Right (fromInteger i)
        _ -> Left ("malformed premise slot: " ++ show n)
decodeSlot backend e =
  Left ("malformed " ++ backend ++ " premise reference: " ++ show e)

-- ---------------------------------------------------------------------------
-- Canonical numeral grammars
-- ---------------------------------------------------------------------------

-- | A canonical natural: digits only, no sign, no leading zeros.
parseCanonicalNat :: String -> Maybe Integer
parseCanonicalNat s =
  case reads s :: [(Integer, String)] of
    [(n, "")]
      | n >= 0
      , show n == s -> Just n
    _ -> Nothing

-- | A canonical integer: an optional @-@ on a nonzero canonical natural.
parseCanonicalInt :: String -> Maybe Integer
parseCanonicalInt ('-' : rest) = do
  n <- parseCanonicalNat rest
  if n == 0 then Nothing else Just (negate n)
parseCanonicalInt s = parseCanonicalNat s

-- | Parse a canonical decimal numeral (the 'Lara.Prop.canonNum' image:
-- optional @-@, no leading zeros, no trailing fraction zeros) into an exact
-- rational. Anything else — including empty fraction parts and scientific
-- notation — is rejected.
parseDecimal :: String -> Maybe Rational
parseDecimal ('-' : rest) = negate <$> parseUnsigned rest
parseDecimal s = parseUnsigned s

parseUnsigned :: String -> Maybe Rational
parseUnsigned s =
  case break (== '.') s of
    (intPart, "") -> fromInteger <$> parseCanonicalNat intPart
    (intPart, '.' : fracPart)
      | not (null fracPart)
      , all (`elem` ['0' .. '9']) fracPart
      , last fracPart /= '0' -> do
          n <- parseCanonicalNat intPart
          let scale = 10 ^ length fracPart :: Integer
              fracDigits = read fracPart :: Integer
          Just (fromInteger n + fracDigits % scale)
    _ -> Nothing

-- ---------------------------------------------------------------------------
-- The premise-cell convention
-- ---------------------------------------------------------------------------

collectNums :: Term -> [String]
collectNums (TNum n) = [n]
collectNums (TStr _) = []
collectNums (TCon _ ts) = concatMap collectNums ts

-- | The premise-cell convention: the normalized premise proposition must
-- contain exactly one numeric literal anywhere in its argument terms.
premiseCell :: Prop -> Either String Rational
premiseCell p =
  case nf p of
    normalized@(Prop _ ts) ->
      case concatMap collectNums ts of
        [n] ->
          maybe
            (Left ("premise cell is not a canonical decimal: " ++ n))
            Right
            (parseDecimal n)
        ns ->
          Left
            ( "premise must carry exactly one numeric literal, found "
                ++ show (length ns)
                ++ " in "
                ++ show normalized
            )
