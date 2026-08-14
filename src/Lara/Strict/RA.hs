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
-- == Premise-only slots
--
-- Slots name premises and nothing else: a slot at or beyond the premise count
-- is rejected, exactly as in @ord\@1@. Both rational-arithmetic backends
-- therefore share one trusted-base sentence — every certificate-consulted cell
-- traces to a consulted premise, hence to a leaf, hence to the attack and
-- admission layers. The Lean counterpart reaches the same acceptance set from
-- the other side: @Lara.Driver.buildRegistry@ resolves any /known/ @ra\@1@ or
-- @ord\@1@ digest to @[]@, so there the consulted context genuinely is the
-- premises alone.
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
  , parseGoal
  , checkDrop
    -- * The registered adapter
  , raBackendId
  , slotSchema
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
import Lara.Strict.Cell
  ( SlotSchema (..)
  , decodeSlot
  , parseCanonicalInt
  , parseCanonicalNat
  , parseDecimal
  , premiseCell
  , renderDecimal
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

-- | A rational-arithmetic certificate: which __premise__ slots carry the two
-- cells, and the claimed drop as an exact fraction in lowest terms.
data RACert = RACert
  { raFullSlot :: Int -- ^ premise slot of the full cell
  , raAblatedSlot :: Int -- ^ premise slot of the ablated cell
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
--
-- The @(prem N)@ slot-reference sub-grammar is shared with the other
-- rational-arithmetic backends and lives in "Lara.Strict.Cell"
-- ('decodeSlot'); this table keeps only the RA-specific keywords.

-- | The closed set of RA-specific wire keywords ('Lara.Strict.ND.Tag'
-- discipline: the concrete spellings live in exactly one table). The shared
-- slot keyword @prem@ lives in 'Lara.Strict.Cell.Tag'.
data Tag = TRadrop | TFrac
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The on-the-wire spelling of a keyword.
tagToString :: Tag -> String
tagToString TRadrop = "radrop"
tagToString TFrac = "frac"

-- | Parse a wire keyword, inverse to 'tagToString'.
parseTag :: String -> Maybe Tag
parseTag s = lookup s [(tagToString t, t) | t <- [minBound .. maxBound]]

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
      RACert <$> decodeSlot "RA" slotF <*> decodeSlot "RA" slotA <*> decodeFrac frac
decodeCert e = Left ("malformed RA certificate: " ++ show e)

-- ---------------------------------------------------------------------------
-- Parsing and evaluation (the replay)
-- ---------------------------------------------------------------------------

-- | The single spelling of the goal predicate this backend recognizes.
raGoalPred :: Pred
raGoalPred = Pred "rel_drop_ge"

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
      Left
        ( "witness fraction does not equal the recomputed relative drop: witness "
            ++ renderDecimal witness
            ++ " vs recomputed "
            ++ renderDecimal recomputed
        )
  | witness /= raClaimed goal =
      Left
        ( "witness fraction does not equal the claimed drop in the goal: witness "
            ++ renderDecimal witness
            ++ " vs goal "
            ++ renderDecimal (raClaimed goal)
        )
  | raClaimed goal < raThreshold goal =
      Left
        ( "claimed drop does not clear the threshold: claimed "
            ++ renderDecimal (raClaimed goal)
            ++ " < threshold "
            ++ renderDecimal (raThreshold goal)
        )
  | otherwise = Right ()
  where
    recomputed = (raFull goal - raAblated goal) / raFull goal

-- ---------------------------------------------------------------------------
-- The registered adapter
-- ---------------------------------------------------------------------------

-- | The rational-arithmetic backend identifier: @ra\@1@.
raBackendId :: BackendId
raBackendId = BackendId {backendName = "ra", backendVersion = 1}

-- | The @ra\@1@ premise-reference schema:
-- @(radrop (prem N) (prem M) (frac P Q))@ — the first two positions premise
-- references, the witness fraction untouched. Spellings come from this
-- module's own tag table and identity — the schema introduces no new strings.
slotSchema :: SlotSchema
slotSchema =
  SlotSchema
    { ssBackend = raBackendId
    , ssHead = tagToString TRadrop
    , ssArity = 3
    , ssRefSlots = [0, 1]
    }

-- | Build the adapter with a __fixed__ theory table ('Lara.Strict.ND.mkNDBackend'
-- discipline: closed registration, digest selection only). The theory entries
-- are never consulted — the certified identity is pure arithmetic, and since
-- the premise-only guard below refuses to cite them they are not reachable as
-- cells either — so an accepted certificate reports only 'PremiseSlot'
-- dependencies; an unknown digest is still a rejection, mirroring @nd\@1@.
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
          fullP <- resolve theoryProps (raFullSlot cert)
          ablatedP <- resolve theoryProps (raAblatedSlot cert)
          fullCell <- premiseCell fullP
          ablatedCell <- premiseCell ablatedP
          assert
            (fullCell == raFull goalR)
            ( "full-cell premise does not match the goal's full cell: premise "
                ++ renderDecimal fullCell
                ++ " vs goal "
                ++ renderDecimal (raFull goalR)
            )
          assert
            (ablatedCell == raAblated goalR)
            ( "ablated-cell premise does not match the goal's ablated cell: premise "
                ++ renderDecimal ablatedCell
                ++ " vs goal "
                ++ renderDecimal (raAblated goalR)
            )
          checkDrop goalR (raWitness cert)
          Right
            ( Set.fromList
                [ PremiseSlot (raFullSlot cert)
                , PremiseSlot (raAblatedSlot cert)
                ]
            )
      where
        nPrem = length premises

        -- Premise-only slot resolution, identical in shape and message to
        -- @ord\@1@'s (see "Lara.Strict.Ord" §"Premise-only slots"): a slot
        -- naming a theory entry is rejected outright, so every compared cell
        -- traces to a consulted premise.
        --
        -- Until the seam-wide decision this backend indexed the /free context/
        -- @premises ++ theory@, so on the raw @.sexp@ door — where the wire
        -- @theories@ section is passed straight through and preflight never
        -- validates its content — an artifact could self-supply the cell it
        -- then certified against. That was not a soundness bug (@ra\@1@ never
        -- claimed premise-backing) but it was the one path by which a
        -- certificate-consulted value bypassed the leaf\/admission layer, and
        -- it made the trusted-base story differ between two sibling
        -- rational-arithmetic backends. It is now uniform.
        resolve theoryProps i
          | i >= 0 && i < nPrem = Right (premises !! i)
          | i >= nPrem && i < nPrem + length theoryProps =
              Left
                ( "RA cites premise slots only; slot names theory entry "
                    ++ show (i - nPrem)
                )
          | otherwise = Left ("premise slot out of range: " ++ show i)

        assert cond msg = if cond then Right () else Left msg
