-- | The rational-arithmetic domain-checker backend: @ra\@1@ (issue #57;
-- @docs/strict-backend-decision.md@ §2 obligations).
--
-- This adapter certifies exactly one goal shape — a relative-drop inequality
--
-- > rel_drop_ge(F, A, C, T)   -- full cell, ablated cell, claimed drop, threshold
--
-- read off the normalized goal proposition, where all four arguments are
-- numeric literals. Replay recomputes @(F - A) \/ F@ in exact rational
-- arithmetic (no floats) and accepts iff the certificate's witness fraction
-- equals both the recomputation and the claimed @C@, and @C >= T@.
--
-- == Certificates
--
-- > cert ::= (radrop (prem N) (prem M) (frac P Q))
--
-- @N@ and @M@ name the premise slots supplying the full and ablated cells
-- (dependency accountability, obligation 4: @uses@ is a function of the
-- certificate alone). @P\/Q@ is the claimed drop as an exact fraction in
-- __lowest terms__ with @Q > 0@ — one wire form per value, so a well-formed
-- payload carrying a different value is a replay rejection (R13), not a decode
-- error.
--
-- == The premise-cell convention
--
-- A consulted premise must contain __exactly one__ numeric literal anywhere in
-- its argument terms; that literal is the cell. Zero or several literals is a
-- rejection: the adapter refuses to guess which number the evidence reports.
--
-- == What this discharges — and what it does not
--
-- Like @nd\@1@ this adapter is modest: an accepted certificate discharges the
-- /arithmetic identity/ relative to the premise conclusions — it does not
-- assert that any premise cell is true (the factivity firewall). The truth of
-- the cells stays with the defeasible leaves feeding the premise slots.
module Lara.Strict.RA
  ( -- * Backend formulas and certificates
    RAGoal (..)
  , RACert (..)
    -- * Wire grammar
  , Tag (..)
  , tagToString
  , parseTag
  , decodeCert
    -- * Parsing and evaluation (the replay)
  , raGoalPred
  , parseDecimal
  , premiseCell
  , parseGoal
  , checkDrop
    -- * The registered adapter
  , raBackendId
  , mkRABackend
  ) where

import Data.Ratio (denominator, numerator, (%))
import qualified Data.Set as Set

import Lara.Prop (Pred (..), Prop (..), Term (..), nf)
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

-- | The one goal shape this backend certifies, parsed from the normalized
-- goal proposition: @rel_drop_ge(F, A, C, T)@ with every argument a numeric
-- literal.
data RAGoal = RAGoal
  { raFull :: Rational -- ^ @F@, the full-configuration cell
  , raAblated :: Rational -- ^ @A@, the ablated-configuration cell
  , raClaimed :: Rational -- ^ @C@, the claimed relative drop
  , raThreshold :: Rational -- ^ @T@, the falsification threshold
  }
  deriving (Eq, Show)

-- | A rational-arithmetic certificate: which free-context slots carry the two
-- cells, and the claimed drop as an exact fraction in lowest terms. Slots
-- index the full consulted context — premises followed by theory entries —
-- exactly like @nd\@1@'s de Bruijn free variables.
data RACert = RACert
  { raFullSlot :: Int -- ^ free-context slot of the full cell
  , raAblatedSlot :: Int -- ^ free-context slot of the ablated cell
  , raWitness :: Rational -- ^ the claimed drop, @P \/ Q@ in lowest terms
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Wire grammar (the closed decoder)
-- ---------------------------------------------------------------------------

-- The certificate reaches the adapter as an opaque 'SExpr'; only this module
-- decodes it (closed registration). Wire grammar:
--
-- > cert := (radrop (prem N) (prem M) (frac P Q))

-- | The closed set of wire keywords ('Lara.Strict.ND.Tag' discipline: the
-- concrete spellings live in exactly one table).
data Tag = TRadrop | TPrem | TFrac
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The on-the-wire spelling of a keyword.
tagToString :: Tag -> String
tagToString TRadrop = "radrop"
tagToString TPrem = "prem"
tagToString TFrac = "frac"

-- | Parse a wire keyword, inverse to 'tagToString'.
parseTag :: String -> Maybe Tag
parseTag s = lookup s [(tagToString t, t) | t <- [minBound .. maxBound]]

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

decodeSlot :: SExpr -> Either String Int
decodeSlot (SList [SAtom k, SAtom n])
  | parseTag k == Just TPrem =
      case parseCanonicalNat n of
        Just i
          | i <= toInteger (maxBound :: Int) -> Right (fromInteger i)
        _ -> Left ("malformed premise slot: " ++ show n)
decodeSlot e = Left ("malformed RA premise reference: " ++ show e)

decodeFrac :: SExpr -> Either String Rational
decodeFrac (SList [SAtom k, SAtom p, SAtom q])
  | parseTag k == Just TFrac = do
      pn <- maybe (Left ("malformed numerator: " ++ show p)) Right (parseCanonicalInt p)
      qn <- maybe (Left ("malformed denominator: " ++ show q)) Right (parseCanonicalNat q)
      if qn <= 0
        then Left "fraction denominator must be positive"
        else
          let r = pn % qn
           in if numerator r == pn && denominator r == qn
                then Right r
                else Left ("fraction not in lowest terms: " ++ p ++ "/" ++ q)
decodeFrac e = Left ("malformed RA fraction: " ++ show e)

-- | Decode the opaque wire certificate; rejects unknown tags, non-canonical
-- numerals, and fractions not in lowest terms.
decodeCert :: SExpr -> Either String RACert
decodeCert (SList [SAtom k, slotF, slotA, frac])
  | parseTag k == Just TRadrop =
      RACert <$> decodeSlot slotF <*> decodeSlot slotA <*> decodeFrac frac
decodeCert e = Left ("malformed RA certificate: " ++ show e)

-- ---------------------------------------------------------------------------
-- Parsing and evaluation (the replay)
-- ---------------------------------------------------------------------------

-- | The single spelling of the goal predicate this backend recognizes.
raGoalPred :: Pred
raGoalPred = Pred "rel_drop_ge"

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

-- | Parse the normalized goal into an 'RAGoal'.
parseGoal :: Prop -> Either String RAGoal
parseGoal g =
  case nf g of
    Prop p [TNum f, TNum a, TNum c, TNum t]
      | p == raGoalPred ->
          RAGoal
            <$> dec "full cell" f
            <*> dec "ablated cell" a
            <*> dec "claimed drop" c
            <*> dec "threshold" t
    other -> Left ("goal is not a rel_drop_ge atom over numerals: " ++ show other)
  where
    dec what n =
      maybe (Left (what ++ " is not a canonical decimal: " ++ n)) Right (parseDecimal n)

-- | The arithmetic identity replay checks: the witness equals the exact
-- recomputation @(F - A) \/ F@, equals the claimed @C@, and clears @T@.
checkDrop :: RAGoal -> Rational -> Either String ()
checkDrop goal witness
  | raFull goal == 0 = Left "full cell is zero: relative drop undefined"
  | recomputed /= witness =
      Left "witness fraction does not equal the recomputed relative drop"
  | witness /= raClaimed goal =
      Left "witness fraction does not equal the claimed drop in the goal"
  | raClaimed goal < raThreshold goal =
      Left "claimed drop does not clear the threshold"
  | otherwise = Right ()
  where
    recomputed = (raFull goal - raAblated goal) / raFull goal

-- ---------------------------------------------------------------------------
-- The registered adapter
-- ---------------------------------------------------------------------------

-- | The rational-arithmetic backend identifier: @ra\@1@.
raBackendId :: BackendId
raBackendId = BackendId {backendName = "ra", backendVersion = 1}

-- | Build the adapter with a __fixed__ theory table ('Lara.Strict.ND.mkNDBackend'
-- discipline: closed registration, digest selection only). The theory entries
-- are never consulted — the certified identity is pure arithmetic — so an
-- accepted certificate reports only 'PremiseSlot' dependencies; an unknown
-- digest is still a rejection, mirroring @nd\@1@.
mkRABackend :: [(TheoryDigest, [Prop])] -> Backend
mkRABackend theories =
  Backend
    { backendId = raBackendId
    , runBackend = run
    }
  where
    run :: TheoryDigest -> [Prop] -> Prop -> SExpr -> Either String (Set.Set Dependency)
    run digest premises goal certSExpr =
      case lookup digest theories of
        Nothing -> Left ("unknown theory digest: " ++ show digest)
        Just theoryProps -> do
          cert <- decodeCert certSExpr
          goalR <- parseGoal goal
          let free = premises ++ theoryProps
              nPrem = length premises
              slot i =
                if i >= 0 && i < length free
                  then Right (free !! i)
                  else Left ("free-context slot out of range: " ++ show i)
          fullP <- slot (raFullSlot cert)
          ablatedP <- slot (raAblatedSlot cert)
          fullCell <- premiseCell fullP
          ablatedCell <- premiseCell ablatedP
          assert
            (fullCell == raFull goalR)
            "full-cell premise does not match the goal's full cell"
          assert
            (ablatedCell == raAblated goalR)
            "ablated-cell premise does not match the goal's ablated cell"
          checkDrop goalR (raWitness cert)
          Right
            ( Set.fromList
                [ toDependency nPrem (raFullSlot cert)
                , toDependency nPrem (raAblatedSlot cert)
                ]
            )
      where
        assert cond msg = if cond then Right () else Left msg

    toDependency :: Int -> Int -> Dependency
    toDependency nPrem i
      | i < nPrem = PremiseSlot i
      | otherwise = TheoryEntry (i - nPrem)
