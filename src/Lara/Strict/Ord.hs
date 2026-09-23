-- | The ordered-comparison domain-checker backend: @ord\@1@
-- (@plans\/2026-08-06-ord1-comparison-backend.md@;
-- @docs\/strict-backend-decision.md@ §2 obligations).
--
-- This adapter certifies the most common claim shape in ML methodology papers
-- — "this number beats that number" — as a closed two-predicate family over
-- exactly two canonical decimal numerals:
--
-- > num_lt(A, B)   -- A <  B
-- > num_le(A, B)   -- A <= B
--
-- There is no @num_gt@\/@num_ge@: \"A > B\" is authored as @num_lt(B, A)@, and
-- a frontend that wants @>@ swaps the arguments at elaboration. There is no
-- @num_eq@ either: canonical decimal form is injective on representable
-- rationals, so @num_eq(A, B)@ could only ever accept when @A@ and @B@ are the
-- /same/ numeral. The kernel stays minimal; the family is @{lt, le}@.
--
-- == Certificates
--
-- > cert ::= (ordcmp (prem N) (prem M))
--
-- @N@ and @M@ name the premise slots supplying the left and right cells
-- (dependency accountability, obligation 4: @uses@ is a function of the
-- certificate alone). The relation is read off the goal predicate, not the
-- certificate. There is __no witness value__: unlike @ra\@1@'s recomputed
-- fraction, a comparison over ground literals has nothing to recompute — the
-- replay decides it directly.
--
-- == Premise-only slots
--
-- This backend rejects any slot @>= nPrem@. On the raw @.sexp@ door the backend
-- theory table is built from the unit's own wire @theories@ section and replay
-- preflight never validates its content, so a theory-entry slot would let an
-- artifact cite a self-supplied, unattackable, non-leaf value.
--
-- @ra\@1@ originally indexed the whole free context (premises then theory
-- entries) and has since been brought to the same rule, so the two
-- rational-arithmetic backends share one trusted-base sentence. @nd\@1@ keeps
-- free-context indexing, because its de Bruijn free variables are /meant/ to
-- reach theory axioms.
--
-- That is precisely why the guard is load-bearing rather than free. A
-- well-formed unit's @ord\@1@ theory is empty __by convention__ — the @.lara@
-- policy door pins theory content through the elaborator's @registryOf@ — but
-- on the raw door nothing prevents an artifact from supplying entries, and
-- this adapter is handed whatever it supplied. The guard does not enforce
-- that the theory is empty; a unit may declare entries and still be accepted.
-- What it enforces is that theory entries are __uncitable__, which is what
-- makes "every compared value traces to a consulted premise" true by
-- construction. A threshold or public baseline is likewise not a bare goal
-- constant: it enters as a leaf feeding a premise slot.
--
-- The Lean counterpart reaches the same acceptance set from the other side:
-- @Lara.Driver.buildRegistry@ resolves any /known/ @ord\@1@ digest to @[]@, so
-- there the consulted context genuinely is the premises alone.
--
-- == What this discharges — and what it does not
--
-- Since both numerals appear in the goal, the relation itself is decidable
-- from the goal alone; what the premises add is __provenance anchoring__. An
-- accepted certificate certifies that each cited premise's unique numeric
-- literal equals the corresponding goal numeral, and that the goal's relation
-- holds of those numerals. It does __not__ assert that any premise cell is
-- true — the factivity firewall. You cannot argue with the arithmetic; you
-- argue with the measurements, which stay defeasible: attackable,
-- quarantinable, admission-governed.
--
-- Note also that @num_lt@\/@num_le@ head __no__ declared contrary pair. That
-- is a theorem, not a workaround: comparison goals are decidable against a
-- shared ground truth, so a sound backend can never accept two conflicting
-- members of the family over the same literals (the exclusivity lemmas in
-- @lean\/Lara\/Ord.lean@). Intra-family consistency is enforced at acceptance
-- time by arithmetic, not by attack structure.
module Lara.Strict.Ord
  ( -- * Backend formulas and certificates
    OrdRel (..)
  , OrdGoal (..)
  , OrdCert (..)
    -- * Wire grammar
  , Tag (..)
  , tagToString
  , parseTag
  , decodeCert
    -- * Parsing and evaluation (the replay)
  , ordPred
  , parseOrdPred
  , parseGoal
  , holdsRel
    -- * The registered adapter
  , ordBackendId
  , slotSchema
  , mkOrdBackend
  ) where

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
  , parseDecimal
  , premiseCell
  , renderDecimal
  )

-- ---------------------------------------------------------------------------
-- Backend formulas and certificates
-- ---------------------------------------------------------------------------

-- | The closed comparison family. One internal relation per goal predicate;
-- the concrete spellings live in exactly one table ('ordPred').
data OrdRel
  = -- | @num_lt(A, B)@: @A < B@
    OLt
  | -- | @num_le(A, B)@: @A <= B@
    OLe
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The goal shape this backend certifies, parsed from the normalized goal
-- proposition: a family member over two numeric literals.
data OrdGoal = OrdGoal
  { ordRel :: OrdRel -- ^ which comparison, read off the predicate
  , ordLeft :: Rational -- ^ @A@, the left cell
  , ordRight :: Rational -- ^ @B@, the right cell
  }
  deriving (Eq, Show)

-- | An ordered-comparison certificate: which __premise__ slots carry the two
-- compared cells. No witness value — the relation is decided by replay.
data OrdCert = OrdCert
  { ordLeftSlot :: Int -- ^ premise slot of the left cell
  , ordRightSlot :: Int -- ^ premise slot of the right cell
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Wire grammar (the closed decoder)
-- ---------------------------------------------------------------------------

-- The certificate reaches the adapter as an opaque 'SExpr'; only this module
-- decodes it (closed registration). Wire grammar:
--
-- > cert := (ordcmp (prem N) (prem M))
--
-- The @(prem N)@ slot-reference sub-grammar is shared with the other
-- rational-arithmetic backends and lives in "Lara.Strict.Cell"
-- ('decodeSlot'); this table keeps only the @ord\@1@-specific keyword.

-- | The closed set of @ord\@1@-specific wire keywords
-- ('Lara.Strict.ND.Tag' discipline).
data Tag = TOrdcmp
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The on-the-wire spelling of a keyword.
tagToString :: Tag -> String
tagToString TOrdcmp = "ordcmp"

-- | Parse a wire keyword, inverse to 'tagToString'.
parseTag :: String -> Maybe Tag
parseTag s = lookup s [(tagToString t, t) | t <- [minBound .. maxBound]]

-- | Decode the opaque wire certificate; rejects unknown tags, wrong arity, and
-- non-canonical slot naturals.
decodeCert :: SExpr -> Either String OrdCert
decodeCert (SList [SAtom k, slotL, slotR])
  | parseTag k == Just TOrdcmp =
      OrdCert <$> decodeSlot "ord" slotL <*> decodeSlot "ord" slotR
decodeCert e = Left ("malformed ord certificate: " ++ show e)

-- ---------------------------------------------------------------------------
-- Parsing and evaluation (the replay)
-- ---------------------------------------------------------------------------

-- | The goal predicate spelling each family member is authored with. This is
-- the one table where the concrete spellings live.
ordPred :: OrdRel -> Pred
ordPred OLt = Pred "num_lt"
ordPred OLe = Pred "num_le"

-- | Recognize a family predicate, inverse to 'ordPred'. Any other predicate is
-- not this backend's goal shape.
parseOrdPred :: Pred -> Maybe OrdRel
parseOrdPred p = lookup p [(ordPred r, r) | r <- [minBound .. maxBound]]

-- | Parse the normalized goal into an 'OrdGoal': one of the two family
-- predicates over exactly two canonical decimal numerals.
parseGoal :: Prop -> Either String OrdGoal
parseGoal g =
  case nf g of
    Prop p [TNum a, TNum b]
      | Just rel <- parseOrdPred p ->
          OrdGoal rel <$> dec "left cell" a <*> dec "right cell" b
    other ->
      Left ("goal is not a num_lt/num_le atom over two numerals: " ++ show other)
  where
    dec what n =
      maybe (Left (what ++ " is not a canonical decimal: " ++ n)) Right (parseDecimal n)

-- | The comparison replay decides, in exact rational arithmetic (no floats).
holdsRel :: OrdRel -> Rational -> Rational -> Bool
holdsRel OLt a b = a < b
holdsRel OLe a b = a <= b

-- | The mathematical symbol for a family member, for rejection messages only.
-- The authored spelling stays 'ordPred'; this is prose, not wire syntax.
relSymbol :: OrdRel -> String
relSymbol OLt = "<"
relSymbol OLe = "<="

-- ---------------------------------------------------------------------------
-- The registered adapter
-- ---------------------------------------------------------------------------

-- | The ordered-comparison backend identifier: @ord\@1@.
ordBackendId :: BackendId
ordBackendId = BackendId {backendName = "ord", backendVersion = 1}

-- | The @ord\@1@ premise-reference schema: @(ordcmp (prem N) (prem M))@,
-- both positions premise references. Spellings come from this module's own
-- tag table and identity — the schema introduces no new strings.
slotSchema :: SlotSchema
slotSchema =
  SlotSchema
    { ssBackend = ordBackendId
    , ssHead = tagToString TOrdcmp
    , ssArity = 2
    , ssRefSlots = [0, 1]
    }

-- | Build the adapter with a __fixed__ theory table ('Lara.Strict.RA.mkRABackend'
-- discipline: closed registration, digest selection only). The theory is empty
-- by design and its entries are never consulted — comparison is pure
-- arithmetic over premise cells — so an accepted certificate reports only
-- 'PremiseSlot' dependencies; an unknown digest is still a rejection.
mkOrdBackend :: [(TheoryDigest, [Prop])] -> Backend
mkOrdBackend theories =
  Backend
    { backendId = ordBackendId
    , runBackend = run
    }
  where
    run :: TheoryDigest -> [Prop] -> Prop -> SExpr -> Either String (Set.Set Dependency)
    run digest premises goal certSExpr =
      case lookup digest theories of
        Nothing -> Left ("unknown theory digest: " ++ show digest)
        Just theoryProps -> do
          cert <- decodeCert certSExpr
          goalO <- parseGoal goal
          leftP <- resolve theoryProps (ordLeftSlot cert)
          rightP <- resolve theoryProps (ordRightSlot cert)
          leftCell <- premiseCell leftP
          rightCell <- premiseCell rightP
          assert
            (leftCell == ordLeft goalO)
            ( "left-cell premise does not match the goal's left numeral: premise "
                ++ renderDecimal leftCell
                ++ " vs goal "
                ++ renderDecimal (ordLeft goalO)
            )
          assert
            (rightCell == ordRight goalO)
            ( "right-cell premise does not match the goal's right numeral: premise "
                ++ renderDecimal rightCell
                ++ " vs goal "
                ++ renderDecimal (ordRight goalO)
            )
          assert
            (holdsRel (ordRel goalO) (ordLeft goalO) (ordRight goalO))
            ( "the claimed comparison does not hold: "
                ++ renderDecimal (ordLeft goalO)
                ++ " "
                ++ relSymbol (ordRel goalO)
                ++ " "
                ++ renderDecimal (ordRight goalO)
                ++ " is false"
            )
          -- A same-slot certificate dedups to a single dependency.
          Right
            ( Set.fromList
                [ PremiseSlot (ordLeftSlot cert)
                , PremiseSlot (ordRightSlot cert)
                ]
            )
      where
        nPrem = length premises

        -- Premise-only slot resolution: a slot naming a theory entry is
        -- rejected outright, so every compared value traces to a consulted
        -- premise.
        --
        -- The middle branch is live, not defensive. It is reached whenever the
        -- unit declares a non-empty theory for this digest — the raw @.sexp@
        -- door passes the wire @theories@ section straight through — and this
        -- repository reaches it from two directions:
        -- @fixtures\/corpus\/ord-premise-only-reject.sexp@ (two premises, a
        -- one-entry theory, a certificate citing @(prem 2)@) and
        -- @prop_ordTheorySlotRejected@ in @test\/OrdSpec.hs@, whose generator
        -- deliberately builds a non-empty theory and asserts this arm's
        -- message. Collapsing it into @otherwise@ would change a string both
        -- of those pin.
        --
        -- The @i >= 0@ conjunct looks dead — 'decodeSlot' parses a canonical
        -- natural, so a negative index never reaches here — but it is what
        -- keeps this function total. Drop it and @i < nPrem@ holds for @-1@,
        -- turning a rejection into a @premises !! (-1)@ exception. Slots stay
        -- 'Int' (not 'Numeric.Natural.Natural') because the seam's
        -- 'Dependency' is @PremiseSlot Int@; a narrower type here would only
        -- move the conversion, and 'Lara.Strict.RA' has the same shape.
        resolve theoryProps i
          | i >= 0 && i < nPrem = Right (premises !! i)
          | i >= nPrem && i < nPrem + length theoryProps =
              Left
                ( "ord cites premise slots only; slot names theory entry "
                    ++ show (i - nPrem)
                )
          | otherwise = Left ("premise slot out of range: " ++ show i)

        assert cond msg = if cond then Right () else Left msg
