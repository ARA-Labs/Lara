-- | Conformance tests for the rational-arithmetic adapter ("Lara.Strict.RA"),
-- mirroring the ND suite in "StrictSpec" (conformance evidence, not soundness —
-- the Lean mechanization in @lean/Lara/RA.lean@ carries soundness):
--
--   * __closed wire grammar__ — the 'Tag' table is coherent; literal wire
--     vectors pin the certificate grammar independently of 'tagToString'; the
--     decoder rejects unknown tags, non-canonical numerals, and fractions not
--     in lowest terms.
--   * __canonical decimal grammar__ — 'parseDecimal' accepts exactly the
--     'Lara.Prop.canonNum' image and rejects everything else.
--   * __the premise-cell convention__ — exactly one numeric literal anywhere
--     in the argument terms; zero or several is a rejection.
--   * __decidable replay + dependency exactness__ — a generated well-formed
--     drop scenario replays to acceptance with exactly the two consulted
--     slots as dependencies (premise or theory, per the slot layout), and
--     every single-field mutation of it (witness, threshold, slots, digest)
--     is a rejection.
--   * __closed registration + seam__ — the adapter drives end-to-end through
--     'strictCheck' on the opaque 'SExpr' wire form.
module RASpec (raSpecProps) where

import Data.Ratio (denominator, numerator, (%))
import qualified Data.Set as Set
import Test.QuickCheck

import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..))
import Lara.Strict
  ( Backend (..)
  , Dependency (..)
  , SExpr (..)
  , TheoryDigest (..)
  , mkRegistry
  , sjConclusion
  , sjDependencies
  , strictCheck
  )
import Lara.Strict.RA
  ( RACert (..)
  , Tag (..)
  , checkDrop
  , decodeCert
  , mkRABackend
  , parseDecimal
  , parseTag
  , premiseCell
  , raBackendId
  , tagToString
  , RAGoal (..)
  )

-- ---------------------------------------------------------------------------
-- Wire serialization (mirrors the adapter's grammar)
--
-- Shares the adapter's 'Tag' table via 'tagToString' so the wire keywords are
-- defined in exactly one place ("StrictSpec" discipline).
-- ---------------------------------------------------------------------------

tag :: Tag -> SExpr
tag = SAtom . tagToString

slotToSExpr :: Int -> SExpr
slotToSExpr i = SList [tag TPrem, SAtom (show i)]

fracToSExpr :: Rational -> SExpr
fracToSExpr r =
  SList [tag TFrac, SAtom (show (numerator r)), SAtom (show (denominator r))]

certToSExpr :: RACert -> SExpr
certToSExpr (RACert f a w) =
  SList [tag TRadrop, slotToSExpr f, slotToSExpr a, fracToSExpr w]

-- ---------------------------------------------------------------------------
-- Canonical decimal rendering
-- ---------------------------------------------------------------------------

-- | Render @m / 10^k@ (with @m >= 0@) as a canonical decimal numeral: no
-- leading zeros, no trailing fraction zeros, no dangling point — the
-- 'Lara.Prop.canonNum' image 'parseDecimal' accepts.
renderScaled :: Integer -> Int -> String
renderScaled m k =
  let (q, r) = m `divMod` (10 ^ k)
      padded = pad k (show r)
      frac = reverse (dropWhile (== '0') (reverse padded))
   in if null frac then show q else show q ++ "." ++ frac
  where
    pad n s = replicate (n - length s) '0' ++ s

-- ---------------------------------------------------------------------------
-- Generated accept scenarios
--
-- Pick @F = f@ (a positive integer), a claimed drop @C = c / 10^k@, and a
-- threshold @T = t / 10^k@ with @t <= c@; then @A = F * (1 - C)@ has scale
-- @10^k@ too, so every goal argument renders as a canonical decimal and the
-- recomputed drop @(F - A) / F@ equals @C@ exactly. The two cells sit at
-- generator-chosen slots among padding premises, so the reported dependency
-- set is a genuine differential check, not a restatement.
-- ---------------------------------------------------------------------------

data DropScenario = DropScenario
  { dsPremises :: [Prop]
  , dsTheory :: [Prop]
  , dsGoal :: Prop
  , dsCert :: RACert
  , dsDeps :: Set.Set Dependency
  , dsDistinctCells :: Bool -- ^ F /= A, so swapping the slots must reject
  }
  deriving (Show)

-- | A premise carrying exactly one numeric literal, nested under a
-- constructor to exercise 'premiseCell' recursion.
cellPremise :: String -> String -> Prop
cellPremise name num =
  Prop (Pred "measured") [TCon (FunSym name) [TStr name, TNum num]]

-- | A padding premise with no numeric literal (unconsulted slots are never
-- inspected, but keeping them literal-free makes slot mix-ups loud).
notePremise :: Int -> Prop
notePremise i = Prop (Pred "note") [TStr ("pad" ++ show i)]

genDropScenario :: Gen DropScenario
genDropScenario = do
  f <- choose (1, 9999 :: Integer)
  k <- choose (1, 3 :: Int)
  c <- choose (0, 10 ^ k :: Integer)
  t <- choose (0, c)
  nPad <- choose (0, 3)
  fromTheory <- arbitrary -- ablated cell from a theory entry?
  let denomScale = 10 ^ k :: Integer
      aNum = f * denomScale - f * c -- A * 10^k
      fullStr = show f
      ablatedStr = renderScaled aNum k
      claimedStr = renderScaled c k
      thresholdStr = renderScaled t k
      goal =
        Prop
          (Pred "rel_drop_ge")
          [TNum fullStr, TNum ablatedStr, TNum claimedStr, TNum thresholdStr]
      claimedDrop = c % denomScale
      fullP = cellPremise "full" fullStr
      ablatedP = cellPremise "ablated" ablatedStr
      pads = map notePremise [0 .. nPad - 1]
  fullSlot <- choose (0, nPad)
  let premises
        | fromTheory = insertAt fullSlot fullP pads
        | otherwise = insertAt fullSlot fullP pads ++ [ablatedP]
      theory = [ablatedP | fromTheory]
      ablatedSlot = length premises + (if fromTheory then 0 else -1)
      ablatedDep
        | fromTheory = TheoryEntry 0
        | otherwise = PremiseSlot ablatedSlot
  pure
    DropScenario
      { dsPremises = premises
      , dsTheory = theory
      , dsGoal = goal
      , dsCert = RACert fullSlot ablatedSlot claimedDrop
      , dsDeps = Set.fromList [PremiseSlot fullSlot, ablatedDep]
      , dsDistinctCells = c /= 0
      }
  where
    insertAt i x xs = take i xs ++ [x] ++ drop i xs

instance Arbitrary DropScenario where
  arbitrary = genDropScenario

theoryDigest :: TheoryDigest
theoryDigest = TheoryDigest "ra-spec"

runScenario :: DropScenario -> SExpr -> Either String (Set.Set Dependency)
runScenario ds =
  runBackend
    (mkRABackend [(theoryDigest, dsTheory ds)])
    theoryDigest
    (dsPremises ds)
    (dsGoal ds)

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

-- ---------------------------------------------------------------------------
-- Properties: replay and dependencies
-- ---------------------------------------------------------------------------

-- | Every generated well-formed scenario is accepted with exactly the two
-- consulted slots as dependencies.
prop_raReplayAndDeps :: DropScenario -> Property
prop_raReplayAndDeps ds =
  counterexample (show (runScenario ds wire)) $
    runScenario ds wire == Right (dsDeps ds)
  where
    wire = certToSExpr (dsCert ds)

-- | R13: a well-formed witness carrying any other value is a replay
-- rejection, not a decode error.
prop_raWrongWitnessRejected :: DropScenario -> Bool
prop_raWrongWitnessRejected ds =
  isLeft (runScenario ds (certToSExpr (dsCert ds) {raWitness = wrong}))
  where
    wrong = raWitness (dsCert ds) + 2

-- | Swapping the full and ablated slots must reject whenever the cells
-- differ (the full-cell premise no longer matches the goal's full cell).
prop_raSwappedSlotsRejected :: DropScenario -> Property
prop_raSwappedSlotsRejected ds =
  dsDistinctCells ds ==>
    isLeft (runScenario ds (certToSExpr swapped))
  where
    swapped =
      (dsCert ds)
        { raFullSlot = raAblatedSlot (dsCert ds)
        , raAblatedSlot = raFullSlot (dsCert ds)
        }

-- | A slot past the consulted context (premises ++ theory) is a rejection.
prop_raSlotOutOfRangeRejected :: DropScenario -> Bool
prop_raSlotOutOfRangeRejected ds =
  isLeft (runScenario ds (certToSExpr oob))
  where
    oob = (dsCert ds) {raFullSlot = length (dsPremises ds) + length (dsTheory ds)}

-- | An unknown theory digest is rejected before any certificate work.
prop_raUnknownDigestRejected :: DropScenario -> Bool
prop_raUnknownDigestRejected ds =
  isLeft
    ( runBackend
        (mkRABackend [(theoryDigest, dsTheory ds)])
        (TheoryDigest "other")
        (dsPremises ds)
        (dsGoal ds)
        (certToSExpr (dsCert ds))
    )

-- | End-to-end through the opaque wire form and the closed registry
-- (obligation 5 composed): 'strictCheck' seals a judgment with the goal as
-- conclusion and the two consulted slots as dependencies.
prop_raStrictCheckSeals :: DropScenario -> Bool
prop_raStrictCheckSeals ds =
  let reg = mkRegistry [mkRABackend [(theoryDigest, dsTheory ds)]]
   in case strictCheck reg raBackendId theoryDigest (dsPremises ds) (dsGoal ds) (certToSExpr (dsCert ds)) of
        Right j ->
          sjConclusion j == dsGoal ds
            && sjDependencies j == dsDeps ds
        Left _ -> False

-- ---------------------------------------------------------------------------
-- Properties: the closed wire grammar
-- ---------------------------------------------------------------------------

-- | The wire keyword table is coherent and exhaustive over the closed set.
prop_raTagRoundTrip :: Bool
prop_raTagRoundTrip =
  all (\t -> parseTag (tagToString t) == Just t) [minBound .. maxBound]

-- | Literal wire vectors pin the certificate grammar independently of
-- 'tagToString' (production-independent fixtures), including the corpus-v1
-- Family-10 witness @119/500@.
prop_raWireGoldenVectors :: Bool
prop_raWireGoldenVectors =
  and
    [ decodeCert
        (SList
           [ SAtom "radrop"
           , SList [SAtom "prem", SAtom "0"]
           , SList [SAtom "prem", SAtom "1"]
           , SList [SAtom "frac", SAtom "119", SAtom "500"]
           ])
        == Right (RACert 0 1 (119 % 500))
    , decodeCert
        (SList
           [ SAtom "radrop"
           , SList [SAtom "prem", SAtom "2"]
           , SList [SAtom "prem", SAtom "0"]
           , SList [SAtom "frac", SAtom "-1", SAtom "2"]
           ])
        == Right (RACert 2 0 ((-1) % 2))
    , decodeCert
        (SList
           [ SAtom "radrop"
           , SList [SAtom "prem", SAtom "0"]
           , SList [SAtom "prem", SAtom "1"]
           , SList [SAtom "frac", SAtom "0", SAtom "1"]
           ])
        == Right (RACert 0 1 0)
    ]

-- | The decoder rejects everything outside the closed grammar: wrong arity,
-- unknown tags, non-canonical slot and fraction numerals, fractions not in
-- lowest terms, and non-positive denominators.
prop_raDecodeRejectionMatrix :: Bool
prop_raDecodeRejectionMatrix =
  all
    (isLeft . decodeCert)
    [ SAtom "radrop"
    , SList []
    , SList [SAtom "unknown", slot "0", slot "1", frac "1" "2"]
    , SList [SAtom "radrop", slot "0", slot "1"]
    , SList [SAtom "radrop", slot "0", slot "1", frac "1" "2", SAtom "extra"]
    , SList [SAtom "radrop", SAtom "0", slot "1", frac "1" "2"]
    , SList [SAtom "radrop", SList [SAtom "frac", SAtom "0"], slot "1", frac "1" "2"]
    , SList [SAtom "radrop", slot "01", slot "1", frac "1" "2"]
    , SList [SAtom "radrop", slot "-1", slot "1", frac "1" "2"]
    , SList [SAtom "radrop", slot "+1", slot "1", frac "1" "2"]
    , SList [SAtom "radrop", slot "x", slot "1", frac "1" "2"]
    , SList [SAtom "radrop", slot "", slot "1", frac "1" "2"]
    , SList [SAtom "radrop", slot "0", slot "1", frac "2" "4"] -- not lowest terms
    , SList [SAtom "radrop", slot "0", slot "1", frac "238" "1000"] -- not lowest terms
    , SList [SAtom "radrop", slot "0", slot "1", frac "1" "0"] -- zero denominator
    , SList [SAtom "radrop", slot "0", slot "1", frac "1" "-2"] -- signed denominator
    , SList [SAtom "radrop", slot "0", slot "1", frac "-0" "1"] -- negative zero
    , SList [SAtom "radrop", slot "0", slot "1", frac "01" "2"] -- leading zero
    , SList [SAtom "radrop", slot "0", slot "1", SList [SAtom "frac", SAtom "1"]]
    , SList [SAtom "radrop", slot "0", slot "1", SList [SAtom "prem", SAtom "1", SAtom "2"]]
    ]
  where
    slot n = SList [SAtom "prem", SAtom n]
    frac p q = SList [SAtom "frac", SAtom p, SAtom q]

-- | The Lean wire grammar uses unbounded 'Nat' slots; the Haskell decoder
-- bounds them by host 'Int'. Both sides reject a slot past @maxBound :: Int@
-- (Haskell at decode, Lean at replay), so the asymmetry is unobservable at
-- the seam — this pins the Haskell half of that agreement.
prop_raHugeSlotRejected :: Bool
prop_raHugeSlotRejected =
  isLeft
    ( decodeCert
        (SList
           [ SAtom "radrop"
           , SList [SAtom "prem", SAtom "9223372036854775808"]
           , SList [SAtom "prem", SAtom "0"]
           , SList [SAtom "frac", SAtom "1", SAtom "2"]
           ])
    )

-- ---------------------------------------------------------------------------
-- Properties: the canonical decimal grammar
-- ---------------------------------------------------------------------------

-- | 'parseDecimal' accepts canonical decimals at their exact rational values.
prop_parseDecimalGoldenVectors :: Bool
prop_parseDecimalGoldenVectors =
  and
    [ parseDecimal "0" == Just 0
    , parseDecimal "50" == Just 50
    , parseDecimal "38.1" == Just (381 % 10)
    , parseDecimal "0.238" == Just (119 % 500)
    , parseDecimal "-0.5" == Just ((-1) % 2)
    , parseDecimal "-3" == Just (-3)
    ]

-- | 'parseDecimal' rejects everything outside the 'canonNum' image.
prop_parseDecimalRejectsNonCanonical :: Bool
prop_parseDecimalRejectsNonCanonical =
  all
    ((== Nothing) . parseDecimal)
    [ ""
    , "+1" -- explicit plus
    , "01" -- leading zero
    , "1." -- dangling point
    , ".5" -- missing integer part
    , "1.50" -- trailing fraction zero
    , "1.0" -- trailing fraction zero
    , "1e3" -- scientific notation
    , " 1" -- whitespace
    , "--1"
    , "-"
    , "1.2.3"
    ]

-- | Generated coverage: every canonically rendered @m / 10^k@ parses back to
-- exactly that rational.
prop_parseDecimalRoundTrip :: Property
prop_parseDecimalRoundTrip =
  forAll ((,) <$> choose (0, 10 ^ (6 :: Int)) <*> choose (0, 6)) $ \(m, k) ->
    parseDecimal (renderScaled m k) == Just (m % (10 ^ k))

-- ---------------------------------------------------------------------------
-- Properties: the premise-cell convention
-- ---------------------------------------------------------------------------

prop_premiseCellConvention :: Bool
prop_premiseCellConvention =
  and
    [ premiseCell (cellPremise "full" "38.1") == Right (381 % 10)
    , -- normalization runs first: a noisy numeral canonicalizes, then parses
      premiseCell (Prop (Pred "p") [TNum "+050"]) == Right 50
    , -- zero literals: refuse to guess
      isLeft (premiseCell (notePremise 0))
    , -- two literals: refuse to guess, even across nesting
      isLeft
        (premiseCell
           (Prop (Pred "p") [TNum "1", TCon (FunSym "f") [TNum "2"]]))
    ]

-- ---------------------------------------------------------------------------
-- Properties: the arithmetic identity
-- ---------------------------------------------------------------------------

prop_checkDropMatrix :: Bool
prop_checkDropMatrix =
  and
    [ -- the corpus-v1 identity: (50 - 38.1) / 50 = 119/500 = 0.238 >= 0.05
      checkDrop (RAGoal 50 (381 % 10) (119 % 500) (1 % 20)) (119 % 500) == Right ()
    , -- threshold met with equality
      checkDrop (RAGoal 50 (381 % 10) (119 % 500) (119 % 500)) (119 % 500) == Right ()
    , -- a zero full cell leaves the drop undefined
      isLeft (checkDrop (RAGoal 0 0 0 0) 0)
    , -- witness disagrees with the recomputation
      isLeft (checkDrop (RAGoal 50 (381 % 10) (119 % 500) (1 % 20)) (1 % 4))
    , -- witness agrees with the recomputation but not the claimed drop
      isLeft (checkDrop (RAGoal 50 (381 % 10) (1 % 4) (1 % 20)) (119 % 500))
    , -- claimed drop below the threshold
      isLeft (checkDrop (RAGoal 50 (381 % 10) (119 % 500) (1 % 2)) (119 % 500))
    ]

-- ---------------------------------------------------------------------------
-- Exported runner
-- ---------------------------------------------------------------------------

raSpecProps :: [(String, IO Result)]
raSpecProps =
  [ ("RA replay + dependency exactness", quickCheckResult prop_raReplayAndDeps)
  , ("RA wrong witness rejected (R13)", quickCheckResult prop_raWrongWitnessRejected)
  , ("RA swapped cells rejected", quickCheckResult prop_raSwappedSlotsRejected)
  , ("RA slot out of range rejected", quickCheckResult prop_raSlotOutOfRangeRejected)
  , ("RA unknown digest rejected", quickCheckResult prop_raUnknownDigestRejected)
  , ("RA strictCheck seals a judgment", quickCheckResult prop_raStrictCheckSeals)
  , ("RA wire tag round-trip", quickCheckResult prop_raTagRoundTrip)
  , ("RA literal wire golden vectors", quickCheckResult prop_raWireGoldenVectors)
  , ("RA closed decoder rejection matrix", quickCheckResult prop_raDecodeRejectionMatrix)
  , ("RA huge slot rejected at decode", quickCheckResult prop_raHugeSlotRejected)
  , ("RA decimal golden vectors", quickCheckResult prop_parseDecimalGoldenVectors)
  , ("RA non-canonical decimals rejected", quickCheckResult prop_parseDecimalRejectsNonCanonical)
  , ("RA rendered decimal round-trip", quickCheckResult prop_parseDecimalRoundTrip)
  , ("RA premise-cell convention", quickCheckResult prop_premiseCellConvention)
  , ("RA checkDrop identity matrix", quickCheckResult prop_checkDropMatrix)
  ]
