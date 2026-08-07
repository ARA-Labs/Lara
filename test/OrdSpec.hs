-- | Conformance tests for the ordered-comparison adapter
-- ("Lara.Strict.Ord"), mirroring the @ra\@1@ suite in "RASpec" (conformance
-- evidence, not soundness — the Lean mechanization in @lean/Lara/Ord.lean@
-- carries soundness):
--
--   * __closed wire grammar__ — the 'Tag' table is coherent; literal wire
--     vectors pin the certificate grammar independently of 'tagToString'; the
--     decoder rejects unknown tags, wrong arity, and non-canonical slot
--     numerals.
--   * __the closed goal family__ — exactly @num_lt@ and @num_le@ over exactly
--     two canonical decimal numerals; every other predicate, arity, or
--     argument shape is a rejection (no @num_gt@\/@num_ge@\/@num_eq@).
--   * __premise-only slots__ — a slot naming a theory entry is rejected even
--     when the theory entry would have supplied a matching cell (§2.2: the
--     guard that makes "every compared value traces to a consulted premise"
--     true by construction).
--   * __decidable replay + dependency exactness__ — a generated well-formed
--     comparison replays to acceptance with exactly the two consulted premise
--     slots as dependencies, and a same-slot certificate dedups to one.
--     Single-field mutations reject: goal numerals, certificate slots (each
--     side independently), and the digest are perturbed over /generated/
--     scenarios; the relation arm is hand-built instead, because a relation
--     flip only rejects when the two cells are equal — a draw too rare to
--     generate without discarding nearly everything.
--   * __the boundary arms__ — @num_lt(A, A)@ rejects, @num_le(A, A)@ accepts.
--   * __closed registration + seam__ — the adapter drives end-to-end through
--     'strictCheck' on the opaque 'SExpr' wire form.
module OrdSpec (ordSpecProps) where

import Data.List (isInfixOf)
import Data.Ratio ((%))
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
import qualified Lara.Strict.Cell as Cell
import Lara.Strict.Ord
  ( OrdCert (..)
  , OrdGoal (..)
  , OrdRel (..)
  , Tag (..)
  , decodeCert
  , holdsRel
  , mkOrdBackend
  , ordBackendId
  , ordPred
  , parseGoal
  , parseOrdPred
  , parseTag
  , tagToString
  )

-- ---------------------------------------------------------------------------
-- Wire serialization (mirrors the adapter's grammar)
--
-- Shares the adapter's 'Tag' table via 'tagToString' — and the shared slot
-- keyword via 'Cell.tagToString' — so the wire keywords are defined in
-- exactly one place ("StrictSpec" discipline).
-- ---------------------------------------------------------------------------

tag :: Tag -> SExpr
tag = SAtom . tagToString

slotToSExpr :: Int -> SExpr
slotToSExpr i = SList [SAtom (Cell.tagToString Cell.TPrem), SAtom (show i)]

certToSExpr :: OrdCert -> SExpr
certToSExpr (OrdCert l r) = SList [tag TOrdcmp, slotToSExpr l, slotToSExpr r]

-- ---------------------------------------------------------------------------
-- Canonical decimal rendering
-- ---------------------------------------------------------------------------

-- | Render @m / 10^k@ (with @m >= 0@) as a canonical decimal numeral.
renderScaled :: Integer -> Int -> String
renderScaled m k =
  let (q, r) = m `divMod` (10 ^ k)
      padded = pad k (show r)
      frac = reverse (dropWhile (== '0') (reverse padded))
   in if null frac then show q else show q ++ "." ++ frac
  where
    pad n s = replicate (n - length s) '0' ++ s

-- | Render a possibly negative @m / 10^k@ canonically (no negative zero).
renderSigned :: Integer -> Int -> String
renderSigned m k
  | m < 0 = '-' : renderScaled (negate m) k
  | otherwise = renderScaled m k

-- ---------------------------------------------------------------------------
-- Fixture propositions
-- ---------------------------------------------------------------------------

-- | A premise carrying exactly one numeric literal, nested under a
-- constructor to exercise 'Lara.Strict.Cell.premiseCell' recursion.
cellPremise :: String -> String -> Prop
cellPremise name num =
  Prop (Pred "measured") [TCon (FunSym name) [TStr name, TNum num]]

-- | A padding premise with no numeric literal (unconsulted slots are never
-- inspected, but keeping them literal-free makes slot mix-ups loud).
notePremise :: Int -> Prop
notePremise i = Prop (Pred "note") [TStr ("pad" ++ show i)]

goalProp :: OrdRel -> String -> String -> Prop
goalProp rel a b = Prop (ordPred rel) [TNum a, TNum b]

-- ---------------------------------------------------------------------------
-- Generated accept scenarios
--
-- Pick two cells @A <= B@ at scale @10^k@ (both possibly negative), a family
-- member the pair satisfies, and place the two cell premises at
-- generator-chosen slots among padding premises — so the reported dependency
-- set is a genuine differential check, not a restatement. The theory is
-- deliberately non-empty and its single entry carries the /left/ cell, so the
-- premise-only guard (§2.2) is tested against a slot that would otherwise
-- have resolved to a matching value.
-- ---------------------------------------------------------------------------

data OrdScenario = OrdScenario
  { osPremises :: [Prop]
  , osTheory :: [Prop]
  , osGoal :: Prop
  , osCert :: OrdCert
  , osDeps :: Set.Set Dependency
  , osLeftStr :: String
  , osRightStr :: String
  , osRel :: OrdRel
  , osDistinctCells :: Bool -- ^ A /= B, so swapping the slots must reject
  }
  deriving (Show)

genOrdScenario :: Gen OrdScenario
genOrdScenario = do
  k <- choose (0, 3 :: Int)
  m1 <- choose (-9999, 9999 :: Integer)
  m2 <- choose (-9999, 9999 :: Integer)
  rel <- elements [minBound .. maxBound]
  let lo = min m1 m2
      -- @num_lt@ needs a strict pair; @num_le@ takes the generated one as is,
      -- so the equal-cells boundary stays inside the generated coverage.
      hi = case rel of
        OLt | m1 == m2 -> lo + 1
        _ -> max m1 m2
      leftStr = renderSigned lo k
      rightStr = renderSigned hi k
  nPad <- choose (0, 3 :: Int)
  let total = nPad + 2
  leftSlot <- choose (0, total - 1)
  rightSlot <- elements [i | i <- [0 .. total - 1], i /= leftSlot]
  let mk i
        | i == leftSlot = cellPremise "left" leftStr
        | i == rightSlot = cellPremise "right" rightStr
        | otherwise = notePremise i
  pure
    OrdScenario
      { osPremises = map mk [0 .. total - 1]
      , osTheory = [cellPremise "theory" leftStr]
      , osGoal = goalProp rel leftStr rightStr
      , osCert = OrdCert leftSlot rightSlot
      , osDeps = Set.fromList [PremiseSlot leftSlot, PremiseSlot rightSlot]
      , osLeftStr = leftStr
      , osRightStr = rightStr
      , osRel = rel
      , osDistinctCells = lo /= hi
      }

instance Arbitrary OrdScenario where
  arbitrary = genOrdScenario

theoryDigest :: TheoryDigest
theoryDigest = TheoryDigest "ord-spec"

runScenario :: OrdScenario -> SExpr -> Either String (Set.Set Dependency)
runScenario os =
  runBackend
    (mkOrdBackend [(theoryDigest, osTheory os)])
    theoryDigest
    (osPremises os)
    (osGoal os)

-- | Replay a generated scenario against a substituted goal, so a single goal
-- field can be perturbed while everything else is held fixed.
runScenarioGoal :: OrdScenario -> Prop -> SExpr -> Either String (Set.Set Dependency)
runScenarioGoal os goal =
  runBackend
    (mkOrdBackend [(theoryDigest, osTheory os)])
    theoryDigest
    (osPremises os)
    goal

-- | Replay a hand-built case with an empty theory (the registered shape).
runCase :: [Prop] -> Prop -> OrdCert -> Either String (Set.Set Dependency)
runCase premises goal cert =
  runBackend
    (mkOrdBackend [(theoryDigest, [])])
    theoryDigest
    premises
    goal
    (certToSExpr cert)

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

rejectsWith :: String -> Either String a -> Bool
rejectsWith needle (Left msg) = needle `isInfixOf` msg
rejectsWith _ _ = False

-- ---------------------------------------------------------------------------
-- Properties: replay and dependencies
-- ---------------------------------------------------------------------------

-- | Every generated well-formed comparison is accepted with exactly the two
-- consulted premise slots as dependencies.
prop_ordReplayAndDeps :: OrdScenario -> Property
prop_ordReplayAndDeps os =
  counterexample (show (runScenario os wire)) $
    runScenario os wire == Right (osDeps os)
  where
    wire = certToSExpr (osCert os)

-- | Swapping the slots must reject whenever the cells differ: the left-cell
-- premise no longer matches the goal's left numeral.
prop_ordSwappedSlotsRejected :: OrdScenario -> Property
prop_ordSwappedSlotsRejected os =
  osDistinctCells os ==>
    isLeft (runScenario os (certToSExpr swapped))
  where
    swapped = OrdCert (ordRightSlot (osCert os)) (ordLeftSlot (osCert os))

-- | Perturbing either goal numeral, one at a time, is a rejection: the cited
-- premise's cell no longer matches that side of the goal.
prop_ordGoalNumeralMutationsRejected :: OrdScenario -> Bool
prop_ordGoalNumeralMutationsRejected os =
  and
    [ rejectsWith
        "left-cell premise"
        (runScenarioGoal os (goalProp rel (bump (osLeftStr os)) (osRightStr os)) wire)
    , rejectsWith
        "right-cell premise"
        (runScenarioGoal os (goalProp rel (osLeftStr os) (bump (osRightStr os))) wire)
    ]
  where
    rel = osRel os
    wire = certToSExpr (osCert os)
    -- A different canonical numeral. Appending a digit keeps the canonical
    -- form (no leading zero introduced, no trailing fraction zero) for every
    -- numeral except "0", whose successor must be spelled outright.
    bump "0" = "1"
    bump n = n ++ "1"

-- | A slot past the whole consulted context is a rejection — driven on each
-- side of the certificate independently, so neither slot can silently stop
-- being range-checked.
prop_ordSlotOutOfRangeRejected :: OrdScenario -> Bool
prop_ordSlotOutOfRangeRejected os =
  and
    [ rejectsWith "out of range" (runScenario os (certToSExpr oobLeft))
    , rejectsWith "out of range" (runScenario os (certToSExpr oobRight))
    ]
  where
    oob = length (osPremises os) + length (osTheory os)
    oobLeft = (osCert os) {ordLeftSlot = oob}
    oobRight = (osCert os) {ordRightSlot = oob}

-- | §2.2, the premise-only guard: a slot naming a theory entry is rejected —
-- even though this scenario's theory entry carries exactly the left cell, so
-- free-context indexing would have resolved it and accepted. @ra\@1@ now
-- enforces the same rule (@prop_raTheorySlotRejected@); @nd\@1@ deliberately
-- does not.
prop_ordTheorySlotRejected :: OrdScenario -> Bool
prop_ordTheorySlotRejected os =
  and
    [ rejectsWith "premise slots only" (runScenario os (certToSExpr theoryLeft))
    , rejectsWith "premise slots only" (runScenario os (certToSExpr theoryRight))
    ]
  where
    nPrem = length (osPremises os)
    theoryLeft = (osCert os) {ordLeftSlot = nPrem}
    theoryRight = (osCert os) {ordRightSlot = nPrem}

-- | An unknown theory digest is rejected before any certificate work.
prop_ordUnknownDigestRejected :: OrdScenario -> Bool
prop_ordUnknownDigestRejected os =
  rejectsWith
    "unknown theory digest"
    ( runBackend
        (mkOrdBackend [(theoryDigest, osTheory os)])
        (TheoryDigest "other")
        (osPremises os)
        (osGoal os)
        (certToSExpr (osCert os))
    )

-- | End-to-end through the opaque wire form and the closed registry
-- (obligation 5 composed): 'strictCheck' seals a judgment with the goal as
-- conclusion and the two consulted slots as dependencies.
prop_ordStrictCheckSeals :: OrdScenario -> Bool
prop_ordStrictCheckSeals os =
  let reg = mkRegistry [mkOrdBackend [(theoryDigest, osTheory os)]]
   in case strictCheck reg ordBackendId theoryDigest (osPremises os) (osGoal os) wire of
        Right j -> sjConclusion j == osGoal os && sjDependencies j == osDeps os
        Left _ -> False
  where
    wire = certToSExpr (osCert os)

-- ---------------------------------------------------------------------------
-- Properties: the accept matrix, the boundary arms, and the same-slot cert
-- ---------------------------------------------------------------------------

-- | Per-relation accepts, including negative and fractional cells.
prop_ordAcceptMatrix :: Bool
prop_ordAcceptMatrix =
  and
    [ accepts OLt "0.71" "0.74"
    , accepts OLe "0.71" "0.74"
    , -- integral cells
      accepts OLt "1" "2"
    , -- negative cells, and a sign-crossing pair
      accepts OLt "-0.5" "-0.25"
    , accepts OLt "-1" "0"
    , accepts OLe "-3" "-3"
    , -- differing scales compare exactly, not lexicographically
      accepts OLt "0.9" "10"
    , accepts OLt "0.0001" "0.001"
    ]
  where
    accepts rel a b =
      runCase [cellPremise "l" a, cellPremise "r" b] (goalProp rel a b) (OrdCert 0 1)
        == Right (Set.fromList [PremiseSlot 0, PremiseSlot 1])

-- | The boundary arms: @num_lt(A, A)@ rejects, @num_le(A, A)@ accepts. With a
-- single premise carrying @A@ the certificate cites the same slot twice, so
-- the dependency set dedups to exactly one slot.
prop_ordBoundaryAndSameSlotDedup :: Bool
prop_ordBoundaryAndSameSlotDedup =
  and
    [ sameSlot OLe "0.71" == Right (Set.fromList [PremiseSlot 0])
    , rejectsWith "comparison does not hold" (sameSlot OLt "0.71")
    , -- the same boundary through two distinct premises reporting one value
      runCase [cellPremise "l" "5", cellPremise "r" "5"] (goalProp OLe "5" "5") (OrdCert 0 1)
        == Right (Set.fromList [PremiseSlot 0, PremiseSlot 1])
    , rejectsWith
        "comparison does not hold"
        (runCase [cellPremise "l" "5", cellPremise "r" "5"] (goalProp OLt "5" "5") (OrdCert 0 1))
    ]
  where
    sameSlot rel a = runCase [cellPremise "c" a] (goalProp rel a a) (OrdCert 0 0)

-- | The replay's own rejection arms, each isolated from the others.
prop_ordRejectionMatrix :: Bool
prop_ordRejectionMatrix =
  and
    [ -- wrong LEFT cell: the relation still holds, so only the cell check fires
      rejectsWith "left-cell premise" (runCase cells (goalProp OLt "0.70" "0.74") (OrdCert 0 1))
    , -- wrong RIGHT cell: likewise
      rejectsWith "right-cell premise" (runCase cells (goalProp OLt "0.71" "0.75") (OrdCert 0 1))
    , -- cells match, relation fails — per arm
      rejectsWith
        "comparison does not hold"
        (runCase [cellPremise "l" "0.74", cellPremise "r" "0.71"] (goalProp OLt "0.74" "0.71") (OrdCert 0 1))
    , rejectsWith
        "comparison does not hold"
        (runCase [cellPremise "l" "0.74", cellPremise "r" "0.71"] (goalProp OLe "0.74" "0.71") (OrdCert 0 1))
    , -- a premise with no numeric literal: refuse to guess
      rejectsWith
        "exactly one numeric literal"
        (runCase [notePremise 0, cellPremise "r" "0.74"] (goalProp OLt "0.71" "0.74") (OrdCert 0 1))
    , -- an ambiguous premise carrying two literals: refuse to guess
      rejectsWith
        "exactly one numeric literal"
        (runCase [ambiguous, cellPremise "r" "0.74"] (goalProp OLt "0.71" "0.74") (OrdCert 0 1))
    , -- a slot past the (empty-theory) premise list never resolves
      rejectsWith "out of range" (runCase cells (goalProp OLt "0.71" "0.74") (OrdCert 5 1))
    , -- the ord-side half of the Cell extraction's label invariant: a non-slot
      -- sub-expression names THIS backend, not the shared module
      rejectsWith
        "malformed ord premise reference"
        (decodeCert (SList [tag TOrdcmp, SAtom "0", slotToSExpr 1]))
    , -- a premise whose single literal survives nf but is not a decimal: the
      -- cell parser's own rejection arm, distinct from the 0-or-2+ count
      rejectsWith
        "not a canonical decimal"
        (runCase
           [Prop (Pred "p") [TNum "1e3"], cellPremise "r" "0.74"]
           (goalProp OLt "0.71" "0.74")
           (OrdCert 0 1))
    , -- a negative slot is rejected earlier still, at decode: the wire
      -- sub-grammar admits canonical naturals only, so it never reaches
      -- slot resolution
      rejectsWith
        "malformed premise slot"
        (runCase cells (goalProp OLt "0.71" "0.74") (OrdCert (-1) 1))
    ]
  where
    cells = [cellPremise "l" "0.71", cellPremise "r" "0.74"]
    ambiguous = Prop (Pred "p") [TNum "0.71", TCon (FunSym "f") [TNum "0.9"]]

-- ---------------------------------------------------------------------------
-- Properties: the closed goal family
-- ---------------------------------------------------------------------------

-- | The predicate table is coherent and exhaustive over the closed family,
-- and the family is exactly @{lt, le}@ — the rejected spellings do not parse.
prop_ordPredTable :: Bool
prop_ordPredTable =
  and
    [ all (\r -> parseOrdPred (ordPred r) == Just r) [minBound .. maxBound]
    , map ordPred [minBound .. maxBound] == [Pred "num_lt", Pred "num_le"]
    , all
        ((== Nothing) . parseOrdPred)
        [Pred "num_gt", Pred "num_ge", Pred "num_eq", Pred "rel_drop_ge", Pred ""]
    ]

-- | 'parseGoal' accepts the family over canonical decimals and nothing else:
-- unknown predicates, wrong arity, non-numeral arguments, and literals outside
-- the 'Lara.Prop.canonNum' image are all rejections.
--
-- Normalization runs __first__, so surface variants that 'canonNum' maps into
-- the canonical image (a leading @+@, trailing fraction zeros, a dangling
-- point, a missing integer part, negative zero) are accepted at their
-- normalized value — the same discipline @ra\@1@ applies to its goal. What
-- rejects is a literal whose /normal form/ is still not a decimal.
prop_ordGoalMatrix :: Bool
prop_ordGoalMatrix =
  and
    [ parseGoal (goalProp OLt "0.71" "0.74") == Right (OrdGoal OLt (71 % 100) (37 % 50))
    , parseGoal (goalProp OLe "-3" "50") == Right (OrdGoal OLe (-3) 50)
    , -- normalized into the canonical image, then parsed
      parseGoal (Prop (Pred "num_lt") [TNum "+0.50", TNum "1"])
        == Right (OrdGoal OLt (1 % 2) 1)
    , parseGoal (Prop (Pred "num_lt") [TNum ".5", TNum "2."])
        == Right (OrdGoal OLt (1 % 2) 2)
    , parseGoal (Prop (Pred "num_lt") [TNum "-0.0", TNum "1"])
        == Right (OrdGoal OLt 0 1)
    , all
        (isLeft . parseGoal)
        [ Prop (Pred "num_gt") [TNum "1", TNum "2"] -- outside the family
        , Prop (Pred "num_ge") [TNum "1", TNum "2"]
        , Prop (Pred "num_eq") [TNum "1", TNum "2"]
        , Prop (Pred "num_lt") [TNum "1"] -- arity
        , Prop (Pred "num_lt") [TNum "1", TNum "2", TNum "3"]
        , Prop (Pred "num_lt") [] -- arity
        , Prop (Pred "num_lt") [TStr "1", TNum "2"] -- not a numeral
        , Prop (Pred "num_lt") [TNum "1", TCon (FunSym "f") [TNum "2"]]
        , -- normal forms that are still not decimals
          Prop (Pred "num_lt") [TNum "1e3", TNum "2"] -- scientific notation
        , Prop (Pred "num_lt") [TNum "1", TNum "1.2.3"]
        , Prop (Pred "num_lt") [TNum "NaN", TNum "2"]
        , Prop (Pred "num_lt") [TNum "1", TNum "1/2"]
        ]
    ]

-- | Exact rational comparison, not float and not lexicographic.
prop_ordHoldsRelMatrix :: Bool
prop_ordHoldsRelMatrix =
  and
    [ holdsRel OLt (71 % 100) (37 % 50)
    , not (holdsRel OLt (37 % 50) (71 % 100))
    , not (holdsRel OLt (71 % 100) (71 % 100)) -- the strict boundary
    , holdsRel OLe (71 % 100) (71 % 100) -- the non-strict boundary
    , holdsRel OLe (71 % 100) (37 % 50)
    , not (holdsRel OLe (37 % 50) (71 % 100))
    , holdsRel OLt (-1) 0
    , holdsRel OLt (1 % 10000) (1 % 1000) -- "0.0001" < "0.001"
    ]

-- | Generated agreement between the two arms: @le@ is @lt@ or equality, and
-- exactly one of @lt(a,b)@, @lt(b,a)@, @a == b@ holds (the trichotomy the
-- §3.2 exclusivity lemmas mechanize).
prop_ordRelTrichotomy :: Property
prop_ordRelTrichotomy =
  forAll ((,) <$> gen <*> gen) $ \(a, b) ->
    (holdsRel OLe a b == (holdsRel OLt a b || a == b))
      && (length (filter id [holdsRel OLt a b, holdsRel OLt b a, a == b]) == 1)
      && not (holdsRel OLt a b && holdsRel OLe b a)
  where
    gen = (%) <$> choose (-50, 50) <*> choose (1, 20)

-- ---------------------------------------------------------------------------
-- Properties: the closed wire grammar
-- ---------------------------------------------------------------------------

-- | The wire keyword tables (the adapter's own and the shared slot table in
-- "Lara.Strict.Cell") are coherent and exhaustive over their closed sets.
prop_ordTagRoundTrip :: Bool
prop_ordTagRoundTrip =
  all (\t -> parseTag (tagToString t) == Just t) [minBound .. maxBound]
    && all (\t -> Cell.parseTag (Cell.tagToString t) == Just t) [minBound .. maxBound]

-- | Literal wire vectors pin the certificate grammar independently of
-- 'tagToString' (production-independent fixtures).
prop_ordWireGoldenVectors :: Bool
prop_ordWireGoldenVectors =
  and
    [ decodeCert
        (SList
           [ SAtom "ordcmp"
           , SList [SAtom "prem", SAtom "0"]
           , SList [SAtom "prem", SAtom "1"]
           ])
        == Right (OrdCert 0 1)
    , decodeCert
        (SList
           [ SAtom "ordcmp"
           , SList [SAtom "prem", SAtom "3"]
           , SList [SAtom "prem", SAtom "3"]
           ])
        == Right (OrdCert 3 3)
    ]

-- | The decoder rejects everything outside the closed grammar: wrong arity,
-- unknown tags (including the sibling backend's), and non-canonical slot
-- numerals.
prop_ordDecodeRejectionMatrix :: Bool
prop_ordDecodeRejectionMatrix =
  all
    (isLeft . decodeCert)
    [ SAtom "ordcmp"
    , SList []
    , SList [SAtom "unknown", slot "0", slot "1"]
    , SList [SAtom "radrop", slot "0", slot "1"] -- the sibling backend's tag
    , SList [SAtom "ordcmp", slot "0"] -- arity
    , SList [SAtom "ordcmp", slot "0", slot "1", slot "2"] -- arity
    , SList [SAtom "ordcmp", SAtom "0", slot "1"] -- bare slot
    , SList [SAtom "ordcmp", SList [SAtom "frac", SAtom "0"], slot "1"]
    , SList [SAtom "ordcmp", slot "01", slot "1"] -- leading zero
    , SList [SAtom "ordcmp", slot "-1", slot "1"] -- signed
    , SList [SAtom "ordcmp", slot "+1", slot "1"]
    , SList [SAtom "ordcmp", slot "x", slot "1"]
    , SList [SAtom "ordcmp", slot "", slot "1"]
    , SList [SAtom "ordcmp", slot "0", slot "1.0"] -- not a natural
    , SList [SAtom "ordcmp", SList [SAtom "prem", SAtom "1", SAtom "2"], slot "1"]
    ]
  where
    slot n = SList [SAtom "prem", SAtom n]

-- | The Lean wire grammar uses unbounded 'Nat' slots; the Haskell decoder
-- bounds them by host 'Int'. Both sides reject a slot past @maxBound :: Int@
-- (Haskell at decode, Lean at replay), so the asymmetry is unobservable at
-- the seam — this pins the Haskell half of that agreement.
prop_ordHugeSlotRejected :: Bool
prop_ordHugeSlotRejected =
  isLeft
    ( decodeCert
        (SList
           [ SAtom "ordcmp"
           , SList [SAtom "prem", SAtom "9223372036854775808"]
           , SList [SAtom "prem", SAtom "0"]
           ])
    )

-- ---------------------------------------------------------------------------
-- Exported runner
-- ---------------------------------------------------------------------------

ordSpecProps :: [(String, IO Result)]
ordSpecProps =
  [ ("ord replay + dependency exactness", quickCheckResult prop_ordReplayAndDeps)
  , ("ord swapped cells rejected", quickCheckResult prop_ordSwappedSlotsRejected)
  , ("ord goal numeral mutations rejected", quickCheckResult prop_ordGoalNumeralMutationsRejected)
  , ("ord slot out of range rejected", quickCheckResult prop_ordSlotOutOfRangeRejected)
  , ("ord theory-entry slot rejected (premise-only)", quickCheckResult prop_ordTheorySlotRejected)
  , ("ord unknown digest rejected", quickCheckResult prop_ordUnknownDigestRejected)
  , ("ord strictCheck seals a judgment", quickCheckResult prop_ordStrictCheckSeals)
  , ("ord accept matrix (both arms, signs, scales)", quickCheckResult prop_ordAcceptMatrix)
  , ("ord boundary arms + same-slot dedup", quickCheckResult prop_ordBoundaryAndSameSlotDedup)
  , ("ord replay rejection matrix", quickCheckResult prop_ordRejectionMatrix)
  , ("ord closed predicate family", quickCheckResult prop_ordPredTable)
  , ("ord goal grammar matrix", quickCheckResult prop_ordGoalMatrix)
  , ("ord exact rational comparison", quickCheckResult prop_ordHoldsRelMatrix)
  , ("ord relation trichotomy", quickCheckResult prop_ordRelTrichotomy)
  , ("ord wire tag round-trip", quickCheckResult prop_ordTagRoundTrip)
  , ("ord literal wire golden vectors", quickCheckResult prop_ordWireGoldenVectors)
  , ("ord closed decoder rejection matrix", quickCheckResult prop_ordDecodeRejectionMatrix)
  , ("ord huge slot rejected at decode", quickCheckResult prop_ordHugeSlotRejected)
  ]
