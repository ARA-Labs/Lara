-- | Conformance tests for the static code-inspection adapter
-- ("Lara.Strict.Insp"), mirroring the @ord\@1@ suite in "OrdSpec" (conformance
-- evidence, not soundness — the Lean mechanization in @lean\/Lara\/Insp.lean@
-- carries soundness):
--
--   * __closed wire grammar__ — the 'Tag' table is coherent; literal wire
--     vectors pin both certificate shapes independently of 'tagToString'; the
--     decoder rejects unknown tags, wrong arity, and non-canonical slot
--     numerals.
--   * __the closed goal family__ — exactly @code_absent@, @code_present@,
--     @code_unique@ at arity 2 and @code_planned_not_shipped@ at arity 3;
--     every other predicate or arity is a rejection.
--   * __the inventory convention__ — exactly one @inv(Src, Findings)@ node,
--     with a well-formed @finding@\/@no_findings@ spine. Zero nodes, two
--     nodes, a nested @inv@ inside a finding, a wrong-arity @inv@, and a
--     truncated spine are each their own rejection arm.
--   * __arity is part of the family__ — an @(inspect …)@ payload under a diff
--     goal, and an @(inspectdiff …)@ payload under a one-inventory goal, are
--     rejections rather than re-interpretations.
--   * __premise-only slots__ — a slot naming a theory entry is rejected even
--     when the theory entry would have supplied a matching inventory. This is
--     the guard that keeps the closed-world premise out of the artifact's own
--     hands.
--   * __decidable replay + dependency exactness__ — a generated well-formed
--     inspection replays to acceptance with exactly the consulted premise
--     slots as dependencies, and single-field mutations (the goal's source
--     unit, the goal's feature, the certificate's slots, the digest) reject.
--   * __the closed-world arm__ — an exhaustive inspection that found nothing
--     certifies every absence, which is the whole reason the backend is a
--     strict step rather than a measurement.
--   * __co-acceptability of the contrary pair__ — the Haskell mirror of
--     @Lara.Insp.inspModels_absent_present_sat@: two /different/ inventories
--     make @code_absent@ and @code_present@ both accept, which is why the
--     policy must declare them contrary (unlike the @ord\@1@ family, whose
--     exclusivity is a theorem).
--   * __closed registration + seam__ — the adapter drives end-to-end through
--     'strictCheck' on the opaque 'SExpr' wire form.
module InspSpec (inspSpecProps) where

import Data.List (isInfixOf)
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
import Lara.Strict.Cell (SlotSchema (..))
import qualified Lara.Strict.Cell as Cell
import Lara.Strict.Insp
  ( Con (..)
  , InspCert (..)
  , InspGoal (..)
  , InspRel (..)
  , Inventory (..)
  , Tag (..)
  , conToString
  , decodeCert
  , diffPred
  , holdsRel
  , inspBackendId
  , inspPred
  , mkInspBackend
  , parseCon
  , parseGoal
  , parseInspPred
  , parseTag
  , premiseInventory
  , slotSchemaDiff
  , slotSchemaOne
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

certToSExpr :: InspCert -> SExpr
certToSExpr (CertOne n) = SList [tag TInspect, slotToSExpr n]
certToSExpr (CertDiff n m) = SList [tag TInspectDiff, slotToSExpr n, slotToSExpr m]

-- ---------------------------------------------------------------------------
-- Source-level inventory terms (mirrors the adapter's 'Con' table)
-- ---------------------------------------------------------------------------

-- | A nullary feature or source-unit symbol.
sym :: String -> Term
sym n = TCon (FunSym n) []

con :: Con -> [Term] -> Term
con c = TCon (FunSym (conToString c))

-- | The @finding@\/@no_findings@ spine over an enumeration.
spine :: [Term] -> Term
spine = foldr (\f rest -> con CFinding [f, rest]) (con CNoFindings [])

-- | @inv(Src, Findings)@.
invTerm :: Term -> [Term] -> Term
invTerm src fs = con CInv [src, spine fs]

-- | An inspection-result premise. The inventory sits __nested__ under an
-- ordinary constructor, so the adapter's whole-term scan is exercised rather
-- than a top-level argument match.
invPremise :: String -> Term -> [Term] -> Prop
invPremise tag_ src fs =
  Prop (Pred "inspects") [TCon (FunSym "report") [TStr tag_, invTerm src fs]]

-- | A padding premise with no inventory (unconsulted slots are never
-- inspected, but keeping them inventory-free makes slot mix-ups loud).
notePremise :: Int -> Prop
notePremise i = Prop (Pred "note") [TStr ("pad" ++ show i)]

goalOne :: InspRel -> Term -> Term -> Prop
goalOne rel src f = Prop (inspPred rel) [src, f]

goalDiff :: Term -> Term -> Term -> Prop
goalDiff plan src f = Prop diffPred [plan, src, f]

-- ---------------------------------------------------------------------------
-- Generated accept scenarios
--
-- Two shapes, generated together so every slot-, digest-, and goal-level
-- property runs against both certificate arities. Cited inventories are
-- placed at generator-chosen slots among padding premises, so the reported
-- dependency set is a genuine differential check rather than a restatement.
-- The theory is deliberately non-empty and its single entry carries an
-- inventory that would have satisfied the goal, so the premise-only guard is
-- tested against a slot that would otherwise have resolved.
-- ---------------------------------------------------------------------------

data InspScenario = InspScenario
  { isPremises :: [Prop]
  , isTheory :: [Prop]
  , isGoal :: Prop
  , isCert :: InspCert
  , isDeps :: Set.Set Dependency
  , isSource :: Term -- ^ the goal's (source-side) unit
  , isFeature :: Term -- ^ the goal's feature
  , isOtherFeature :: Term -- ^ a feature the goal does not name
  }
  deriving (Show)

features :: [Term]
features = [sym ("f" ++ show i) | i <- [0 .. 5 :: Int]]

-- | A feature no generated inventory ever enumerates. Substituting it into a
-- presence-shaped goal must reject: it is in nothing, so @code_present@,
-- @code_unique@, and the diff's plan half all fail. (Substituting it into an
-- absence goal would /succeed/, which is why 'prop_inspFeatureMutationRejected'
-- excludes that arm rather than expecting it to reject.)
unenumerated :: Term
unenumerated = sym "never_enumerated"

-- | Place the cited premises at generator-chosen slots among @nPad@ padding
-- premises, returning the premise list and the chosen slots.
placeAt :: [Prop] -> Gen ([Prop], [Int])
placeAt cited = do
  nPad <- choose (0, 3 :: Int)
  let width = nPad + length cited
  slots <- distinct (length cited) [0 .. width - 1]
  let table = zip slots cited
      mk i = maybe (notePremise i) id (lookup i table)
  pure (map mk [0 .. width - 1], slots)
  where
    distinct 0 _ = pure []
    distinct k pool = do
      i <- elements pool
      rest <- distinct (k - 1) [j | j <- pool, j /= i]
      pure (i : rest)

genOneScenario :: Gen InspScenario
genOneScenario = do
  rel <- elements [minBound .. maxBound]
  src <- elements [sym "solver_module", sym "kernel_module"]
  f <- elements features
  let others = [g | g <- features, g /= f]
  found <- case rel of
    IAbsent -> sublistOf others
    IPresent -> do
      extra <- sublistOf others
      pure (f : extra)
    IUnique -> do
      k <- choose (1, 3 :: Int)
      pure (replicate k f)
  (premises, slots) <- placeAt [invPremise "src" src found]
  let n = head slots
  pure
    InspScenario
      { isPremises = premises
      , isTheory = [invPremise "theory" src found]
      , isGoal = goalOne rel src f
      , isCert = CertOne n
      , isDeps = Set.fromList [PremiseSlot n]
      , isSource = src
      , isFeature = f
      , isOtherFeature = unenumerated
      }

genDiffScenario :: Gen InspScenario
genDiffScenario = do
  plan <- elements [sym "plan_notes", sym "design_doc"]
  src <- elements [sym "solver_module", sym "kernel_module"]
  f <- elements features
  let others = [g | g <- features, g /= f]
  planExtra <- sublistOf others
  shipped <- sublistOf others
  (premises, slots) <-
    placeAt [invPremise "plan" plan (f : planExtra), invPremise "src" src shipped]
  -- 'placeAt' returns one slot per cited premise, so this pair is total;
  -- spelled defensively so an incomplete-pattern warning cannot hide a
  -- generator change.
  let (n, m) = case slots of
        (a : b : _) -> (a, b)
        _ -> (0, 1)
  pure
    InspScenario
      { isPremises = premises
      , isTheory = [invPremise "theory" plan (f : planExtra)]
      , isGoal = goalDiff plan src f
      , isCert = CertDiff n m
      , isDeps = Set.fromList [PremiseSlot n, PremiseSlot m]
      , isSource = src
      , isFeature = f
      , isOtherFeature = unenumerated
      }

instance Arbitrary InspScenario where
  arbitrary = oneof [genOneScenario, genDiffScenario]

theoryDigest :: TheoryDigest
theoryDigest = TheoryDigest "insp-spec"

runScenario :: InspScenario -> SExpr -> Either String (Set.Set Dependency)
runScenario is =
  runBackend
    (mkInspBackend [(theoryDigest, isTheory is)])
    theoryDigest
    (isPremises is)
    (isGoal is)

-- | Replay a generated scenario against a substituted goal, so a single goal
-- field can be perturbed while everything else is held fixed.
runScenarioGoal :: InspScenario -> Prop -> SExpr -> Either String (Set.Set Dependency)
runScenarioGoal is goal =
  runBackend
    (mkInspBackend [(theoryDigest, isTheory is)])
    theoryDigest
    (isPremises is)
    goal

-- | Replay a hand-built case with an empty theory (the registered shape).
runCase :: [Prop] -> Prop -> InspCert -> Either String (Set.Set Dependency)
runCase premises goal cert =
  runBackend
    (mkInspBackend [(theoryDigest, [])])
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

-- | The slots a certificate names, in wire order.
certSlots :: InspCert -> [Int]
certSlots (CertOne n) = [n]
certSlots (CertDiff n m) = [n, m]

-- | Rebuild a certificate of the same shape over new slots.
withSlots :: InspCert -> [Int] -> InspCert
withSlots CertOne{} [n] = CertOne n
withSlots CertDiff{} [n, m] = CertDiff n m
withSlots c _ = c

-- ---------------------------------------------------------------------------
-- Properties: replay and dependencies
-- ---------------------------------------------------------------------------

-- | Every generated well-formed inspection is accepted with exactly the
-- consulted premise slots as dependencies.
prop_inspReplayAndDeps :: InspScenario -> Property
prop_inspReplayAndDeps is =
  counterexample (show (runScenario is wire)) $
    runScenario is wire == Right (isDeps is)
  where
    wire = certToSExpr (isCert is)

-- | Naming a different source unit in the goal is a rejection: the cited
-- inventory inspects the unit it inspects, and no certificate re-points it.
prop_inspSourceMismatchRejected :: InspScenario -> Bool
prop_inspSourceMismatchRejected is =
  rejectsWith "inspects a different unit" mutated
    || rejectsWith "inspects a different source unit" mutated
  where
    wire = certToSExpr (isCert is)
    elsewhere = sym "unrelated_module"
    mutated = runScenarioGoal is (repoint (isGoal is)) wire
    repoint (Prop p args) = Prop p (map swap args)
      where
        swap t = if t == isSource is then elsewhere else t

-- | Naming a feature the cited inventory does not settle the way the goal
-- claims is a rejection. The substituted feature is drawn from the same
-- catalogue, so nothing but the claim itself changes.
prop_inspFeatureMutationRejected :: InspScenario -> Property
prop_inspFeatureMutationRejected is =
  isPresenceShaped ==> isLeft (runScenarioGoal is mutated wire)
  where
    wire = certToSExpr (isCert is)
    mutated = case isGoal is of
      Prop p args -> Prop p (map swap args)
      where
        swap t = if t == isFeature is then isOtherFeature is else t
    -- A presence-shaped goal (`code_present`, `code_unique`, or the diff's
    -- plan half) pins the feature down: swapping it must fail. An absence
    -- goal does not — some other feature may also be absent — so it is
    -- excluded rather than expected to reject.
    isPresenceShaped = case isGoal is of
      Prop p _ ->
        p == diffPred
          || p `elem` map inspPred [IPresent, IUnique]

-- | A slot past the whole consulted context is a rejection — driven on each
-- certificate position independently, so no slot can silently stop being
-- range-checked.
prop_inspSlotOutOfRangeRejected :: InspScenario -> Bool
prop_inspSlotOutOfRangeRejected is =
  and
    [ rejectsWith "out of range" (runScenario is (certToSExpr (bump k)))
    | k <- [0 .. length slots - 1]
    ]
  where
    slots = certSlots (isCert is)
    oob = length (isPremises is) + length (isTheory is)
    bump k = withSlots (isCert is) [if j == k then oob else s | (j, s) <- zip [0 ..] slots]

-- | The premise-only guard: a slot naming a theory entry is rejected — even
-- though this scenario's theory entry carries an inventory that would have
-- satisfied the goal, so free-context indexing would have resolved it.
prop_inspTheorySlotRejected :: InspScenario -> Bool
prop_inspTheorySlotRejected is =
  and
    [ rejectsWith "premise slots only" (runScenario is (certToSExpr (point k)))
    | k <- [0 .. length slots - 1]
    ]
  where
    slots = certSlots (isCert is)
    nPrem = length (isPremises is)
    point k = withSlots (isCert is) [if j == k then nPrem else s | (j, s) <- zip [0 ..] slots]

-- | An unknown theory digest is rejected before any certificate work.
prop_inspUnknownDigestRejected :: InspScenario -> Bool
prop_inspUnknownDigestRejected is =
  rejectsWith
    "unknown theory digest"
    ( runBackend
        (mkInspBackend [(theoryDigest, isTheory is)])
        (TheoryDigest "other")
        (isPremises is)
        (isGoal is)
        (certToSExpr (isCert is))
    )

-- | Arity is part of the family: a one-inventory certificate under a diff
-- goal, and a diff certificate under a one-inventory goal, are rejections.
prop_inspArityMismatchRejected :: InspScenario -> Bool
prop_inspArityMismatchRejected is =
  isLeft (runScenario is (certToSExpr crossed))
  where
    crossed = case isCert is of
      CertOne n -> CertDiff n n
      CertDiff n _ -> CertOne n

-- | End-to-end through the opaque wire form and the closed registry
-- (obligation 5 composed): 'strictCheck' seals a judgment with the goal as
-- conclusion and the consulted slots as dependencies.
prop_inspStrictCheckSeals :: InspScenario -> Bool
prop_inspStrictCheckSeals is =
  let reg = mkRegistry [mkInspBackend [(theoryDigest, isTheory is)]]
   in case strictCheck reg inspBackendId theoryDigest (isPremises is) (isGoal is) wire of
        Right j -> sjConclusion j == isGoal is && sjDependencies j == isDeps is
        Left _ -> False
  where
    wire = certToSExpr (isCert is)

-- ---------------------------------------------------------------------------
-- Properties: the accept matrix and the closed-world arm
-- ---------------------------------------------------------------------------

-- | Per-member accepts, including the empty-inventory absence — the closed
-- world step itself — and the same-slot diff's dependency dedup.
prop_inspAcceptMatrix :: Bool
prop_inspAcceptMatrix =
  and
    [ -- absence against a nonempty enumeration
      one IAbsent shipped (sym "repair_pass") == Right dep0
    , -- absence against an EXHAUSTIVE EMPTY enumeration: inspected, found
      -- nothing, so every absence follows
      one IAbsent [] (sym "repair_pass") == Right dep0
    , one IPresent shipped (sym "vote_call") == Right dep0
    , -- uniqueness: a single active configuration, and its duplicate-tolerant
      -- form (the same finding enumerated twice)
      one IUnique [sym "cfg_block16384"] (sym "cfg_block16384") == Right dep0
    , one IUnique [sym "cfg_block16384", sym "cfg_block16384"] (sym "cfg_block16384")
        == Right dep0
    , -- the plan-vs-shipped diff
      diff == Right (Set.fromList [PremiseSlot 0, PremiseSlot 1])
    ]
  where
    dep0 = Set.fromList [PremiseSlot 0]
    src = sym "solver_module"
    plan = sym "plan_notes"
    shipped = [sym "generation_call", sym "vote_call"]
    one rel found f =
      runCase [invPremise "src" src found] (goalOne rel src f) (CertOne 0)
    diff =
      runCase
        [ invPremise "plan" plan [sym "repair_pass", sym "python_translate"]
        , invPremise "src" src shipped
        ]
        (goalDiff plan src (sym "repair_pass"))
        (CertDiff 0 1)

-- | The Haskell mirror of @Lara.Insp.inspModels_absent_present_sat@: two
-- /different/ inventories of the same source make @code_absent@ and
-- @code_present@ over the same feature both accept.
--
-- This is not a defect — an inspection goal is settled against a declared
-- enumeration, not against a shared ground truth the way @ord\@1@'s numerals
-- are — but it is exactly why a policy shipping this backend must declare
-- @code_absent@ / @code_present@ a contrary pair, so the conflict surfaces as
-- an attack instead of two quietly justified claims.
prop_inspContraryCoAcceptable :: Bool
prop_inspContraryCoAcceptable =
  and
    [ runCase [invPremise "a" src []] (goalOne IAbsent src f) (CertOne 0) == Right dep0
    , runCase [invPremise "b" src [f]] (goalOne IPresent src f) (CertOne 0) == Right dep0
    ]
  where
    dep0 = Set.fromList [PremiseSlot 0]
    src = sym "solver_module"
    f = sym "repair_pass"

-- | A same-slot diff certificate dedups to one dependency — and can never be
-- accepted, since one enumeration cannot both hold and miss the feature.
prop_inspSameSlotDiffRejected :: Bool
prop_inspSameSlotDiffRejected =
  rejectsWith
    "not-shipped half fails"
    (runCase [invPremise "p" src [f]] (goalDiff src src f) (CertDiff 0 0))
  where
    src = sym "solver_module"
    f = sym "repair_pass"

-- | The replay's own rejection arms, each isolated from the others.
prop_inspRejectionMatrix :: Bool
prop_inspRejectionMatrix =
  and
    [ -- the structural claim fails, per member
      rejectsWith
        "does not hold"
        (runCase [invPremise "s" src [f]] (goalOne IAbsent src f) (CertOne 0))
    , rejectsWith
        "does not hold"
        (runCase [invPremise "s" src []] (goalOne IPresent src f) (CertOne 0))
    , -- uniqueness fails on an empty inventory, and on a mixed one
      rejectsWith
        "does not hold"
        (runCase [invPremise "s" src []] (goalOne IUnique src f) (CertOne 0))
    , rejectsWith
        "does not hold"
        (runCase [invPremise "s" src [f, g]] (goalOne IUnique src f) (CertOne 0))
    , -- the goal names a unit the cited inventory did not inspect
      rejectsWith
        "different source unit"
        (runCase [invPremise "s" other [f]] (goalOne IPresent src f) (CertOne 0))
    , -- each half of the diff, isolated
      rejectsWith
        "planned half fails"
        (runCase
           [invPremise "p" plan [g], invPremise "s" src []]
           (goalDiff plan src f)
           (CertDiff 0 1))
    , rejectsWith
        "not-shipped half fails"
        (runCase
           [invPremise "p" plan [f], invPremise "s" src [f]]
           (goalDiff plan src f)
           (CertDiff 0 1))
    , -- the diff's plan-side and source-side unit checks, isolated
      rejectsWith
        "plan-side inventory premise"
        (runCase
           [invPremise "p" other [f], invPremise "s" src []]
           (goalDiff plan src f)
           (CertDiff 0 1))
    , rejectsWith
        "source-side inventory premise"
        (runCase
           [invPremise "p" plan [f], invPremise "s" other []]
           (goalDiff plan src f)
           (CertDiff 0 1))
    , -- arity crossings, both directions
      rejectsWith
        "cites one inventory"
        (runCase [invPremise "p" plan [f]] (goalDiff plan src f) (CertOne 0))
    , rejectsWith
        "cites two inventories"
        (runCase
           [invPremise "s" src [f], invPremise "s" src [f]]
           (goalOne IPresent src f)
           (CertDiff 0 1))
    , -- a premise carrying no inventory: refuse to guess
      rejectsWith
        "exactly one inventory"
        (runCase [notePremise 0] (goalOne IPresent src f) (CertOne 0))
    , -- a slot past the (empty-theory) premise list never resolves
      rejectsWith
        "out of range"
        (runCase [invPremise "s" src [f]] (goalOne IPresent src f) (CertOne 5))
    , -- the insp-side half of the Cell extraction's label invariant: a
      -- non-slot sub-expression names THIS backend, not the shared module
      rejectsWith
        "malformed insp premise reference"
        (decodeCert (SList [tag TInspect, SAtom "0"]))
    , -- a negative slot is rejected earlier still, at decode: the wire
      -- sub-grammar admits canonical naturals only
      rejectsWith
        "malformed premise slot"
        (runCase [invPremise "s" src [f]] (goalOne IPresent src f) (CertOne (-1)))
    ]
  where
    src = sym "solver_module"
    other = sym "kernel_module"
    plan = sym "plan_notes"
    f = sym "repair_pass"
    g = sym "vote_call"

-- ---------------------------------------------------------------------------
-- Properties: the closed goal family
-- ---------------------------------------------------------------------------

-- | The predicate table is coherent and exhaustive over the closed
-- one-inventory family, and the rejected spellings do not parse.
prop_inspPredTable :: Bool
prop_inspPredTable =
  and
    [ all (\r -> parseInspPred (inspPred r) == Just r) [minBound .. maxBound]
    , map inspPred [minBound .. maxBound]
        == [Pred "code_absent", Pred "code_present", Pred "code_unique"]
    , diffPred == Pred "code_planned_not_shipped"
    , -- the diff predicate is not a member of the one-inventory table
      parseInspPred diffPred == Nothing
    , all
        ((== Nothing) . parseInspPred)
        [Pred "code_property", Pred "code_diff", Pred "num_lt", Pred ""]
    ]

-- | The reserved source constructor table is coherent and exhaustive.
prop_inspConTable :: Bool
prop_inspConTable =
  and
    [ all (\c -> parseCon (FunSym (conToString c)) == Just c) [minBound .. maxBound]
    , map conToString [minBound .. maxBound] == ["inv", "finding", "no_findings"]
    , all
        ((== Nothing) . parseCon)
        [FunSym "inventory", FunSym "findings", FunSym "none", FunSym ""]
    ]

-- | 'parseGoal' accepts the family at its declared arities and nothing else.
prop_inspGoalMatrix :: Bool
prop_inspGoalMatrix =
  and
    [ parseGoal (goalOne IAbsent src f) == Right (GoalOne IAbsent src f)
    , parseGoal (goalOne IPresent src f) == Right (GoalOne IPresent src f)
    , parseGoal (goalOne IUnique src f) == Right (GoalOne IUnique src f)
    , parseGoal (goalDiff plan src f) == Right (GoalDiff plan src f)
    , -- arity is part of the family, in both directions
      all
        (isLeft . parseGoal)
        [ Prop (Pred "code_absent") [src] -- arity
        , Prop (Pred "code_absent") [plan, src, f]
        , Prop (Pred "code_planned_not_shipped") [src, f]
        , Prop (Pred "code_planned_not_shipped") []
        , Prop (Pred "code_property") [src, f] -- outside the family
        , Prop (Pred "code_diff") [plan, src, f]
        , Prop (Pred "num_lt") [TNum "1", TNum "2"] -- a sibling backend's goal
        ]
    ]
  where
    src = sym "solver_module"
    plan = sym "plan_notes"
    f = sym "repair_pass"

-- | The inventory convention's own arms: exactly one @inv@ node, arity 2, and
-- a well-formed spine.
prop_inspInventoryMatrix :: Bool
prop_inspInventoryMatrix =
  and
    [ premiseInventory (invPremise "s" src [f, g]) == Right (Inventory src [f, g])
    , premiseInventory (invPremise "s" src []) == Right (Inventory src [])
    , -- zero inventories
      rejectsWith "exactly one inventory" (premiseInventory (notePremise 0))
    , -- two inventories, side by side
      rejectsWith
        "exactly one inventory"
        (premiseInventory
           (Prop (Pred "p") [invTerm src [f], invTerm src [g]]))
    , -- an inventory nested inside a finding is still a second node
      rejectsWith
        "exactly one inventory"
        (premiseInventory (Prop (Pred "p") [invTerm src [invTerm src [f]]]))
    , -- wrong inv arity
      rejectsWith
        "not inv(Src, Findings)"
        (premiseInventory (Prop (Pred "p") [con CInv [src]]))
    , rejectsWith
        "not inv(Src, Findings)"
        (premiseInventory (Prop (Pred "p") [con CInv [src, spine [f], f]]))
    , -- a truncated spine: the enumeration does not say where it ended
      rejectsWith
        "malformed inventory finding list"
        (premiseInventory
           (Prop (Pred "p") [con CInv [src, con CFinding [f, f]]]))
    , -- a foreign constructor in tail position
      rejectsWith
        "malformed inventory finding list"
        (premiseInventory (Prop (Pred "p") [con CInv [src, sym "whatever"]]))
    , -- a literal in tail position
      rejectsWith
        "malformed inventory finding list"
        (premiseInventory (Prop (Pred "p") [con CInv [src, TStr "none"]]))
    , -- wrong arity on the spine constructors
      rejectsWith
        "malformed inventory finding list"
        (premiseInventory (Prop (Pred "p") [con CInv [src, con CNoFindings [f]]]))
    ]
  where
    src = sym "solver_module"
    f = sym "repair_pass"
    g = sym "vote_call"

-- | The structural decision itself, over enumerations rather than atoms.
prop_inspHoldsRelMatrix :: Bool
prop_inspHoldsRelMatrix =
  and
    [ -- the closed-world step: an exhaustive empty enumeration settles every
      -- absence
      holdsRel IAbsent [] f
    , holdsRel IAbsent [g] f
    , not (holdsRel IAbsent [f, g] f)
    , holdsRel IPresent [f, g] f
    , not (holdsRel IPresent [] f)
    , not (holdsRel IPresent [g] f)
    , holdsRel IUnique [f] f
    , holdsRel IUnique [f, f] f -- duplicate-tolerant
    , not (holdsRel IUnique [] f) -- nothing found is not uniqueness
    , not (holdsRel IUnique [f, g] f)
    ]
  where
    f = sym "repair_pass"
    g = sym "vote_call"

-- | Generated agreement with the mechanized relation laws: the two polarities
-- are exclusive of one enumeration, and uniqueness implies presence
-- (@Lara.Insp.relHolds_polarity_excl@ / @relHolds_present_of_unique@).
prop_inspRelLaws :: Property
prop_inspRelLaws =
  forAll ((,) <$> sublistOf features <*> elements features) $ \(fs, f) ->
    not (holdsRel IAbsent fs f && holdsRel IPresent fs f)
      && (holdsRel IAbsent fs f /= holdsRel IPresent fs f)
      && (not (holdsRel IUnique fs f) || holdsRel IPresent fs f)

-- ---------------------------------------------------------------------------
-- Properties: the closed wire grammar and the flat schemas
-- ---------------------------------------------------------------------------

-- | The wire keyword tables (the adapter's own and the shared slot table in
-- "Lara.Strict.Cell") are coherent and exhaustive over their closed sets.
prop_inspTagRoundTrip :: Bool
prop_inspTagRoundTrip =
  all (\t -> parseTag (tagToString t) == Just t) [minBound .. maxBound]
    && map tagToString [minBound .. maxBound] == ["inspect", "inspectdiff"]
    && all (\t -> Cell.parseTag (Cell.tagToString t) == Just t) [minBound .. maxBound]

-- | The two flat schemas share a backend but differ in head keyword __and__
-- arity, which is what makes "Lara.Elaborate.CertSlots"'s unique-match
-- selection well defined for this backend.
prop_inspSchemasDistinct :: Bool
prop_inspSchemasDistinct =
  and
    [ ssBackend slotSchemaOne == inspBackendId
    , ssBackend slotSchemaDiff == inspBackendId
    , ssHead slotSchemaOne /= ssHead slotSchemaDiff
    , ssArity slotSchemaOne /= ssArity slotSchemaDiff
    , ssRefSlots slotSchemaOne == [0]
    , ssRefSlots slotSchemaDiff == [0, 1]
    , ssArity slotSchemaOne == length (ssRefSlots slotSchemaOne)
    , ssArity slotSchemaDiff == length (ssRefSlots slotSchemaDiff)
    ]

-- | Literal wire vectors pin both certificate shapes independently of
-- 'tagToString' (production-independent fixtures).
prop_inspWireGoldenVectors :: Bool
prop_inspWireGoldenVectors =
  and
    [ decodeCert (SList [SAtom "inspect", SList [SAtom "prem", SAtom "0"]])
        == Right (CertOne 0)
    , decodeCert
        (SList
           [ SAtom "inspectdiff"
           , SList [SAtom "prem", SAtom "0"]
           , SList [SAtom "prem", SAtom "1"]
           ])
        == Right (CertDiff 0 1)
    , decodeCert
        (SList
           [ SAtom "inspectdiff"
           , SList [SAtom "prem", SAtom "3"]
           , SList [SAtom "prem", SAtom "3"]
           ])
        == Right (CertDiff 3 3)
    ]

-- | The decoder rejects everything outside the closed grammar: wrong arity
-- for each keyword, unknown tags (including the sibling backends'), and
-- non-canonical slot numerals.
prop_inspDecodeRejectionMatrix :: Bool
prop_inspDecodeRejectionMatrix =
  all
    (isLeft . decodeCert)
    [ SAtom "inspect"
    , SList []
    , SList [SAtom "unknown", slot "0"]
    , SList [SAtom "ordcmp", slot "0", slot "1"] -- a sibling backend's tag
    , SList [SAtom "radrop", slot "0", slot "1"]
    , SList [SAtom "inspect", slot "0", slot "1"] -- one-inventory arity
    , SList [SAtom "inspectdiff", slot "0"] -- diff arity
    , SList [SAtom "inspectdiff", slot "0", slot "1", slot "2"]
    , SList [SAtom "inspect", SAtom "0"] -- bare slot
    , SList [SAtom "inspect", slot "01"] -- leading zero
    , SList [SAtom "inspect", slot "-1"] -- signed
    , SList [SAtom "inspect", slot "+1"]
    , SList [SAtom "inspect", slot "x"]
    , SList [SAtom "inspect", slot ""]
    , SList [SAtom "inspect", slot "1.0"] -- not a natural
    , SList [SAtom "inspectdiff", slot "0", slot "1.0"]
    , SList [SAtom "inspect", SList [SAtom "prem", SAtom "1", SAtom "2"]]
    ]
  where
    slot n = SList [SAtom "prem", SAtom n]

-- | The Lean wire grammar uses unbounded 'Nat' slots; the Haskell decoder
-- bounds them by host 'Int'. Both sides reject a slot past @maxBound :: Int@
-- (Haskell at decode, Lean at replay), so the asymmetry is unobservable at
-- the seam — this pins the Haskell half of that agreement.
prop_inspHugeSlotRejected :: Bool
prop_inspHugeSlotRejected =
  isLeft
    (decodeCert
       (SList [SAtom "inspect", SList [SAtom "prem", SAtom "9223372036854775808"]]))

-- ---------------------------------------------------------------------------
-- Exported runner
-- ---------------------------------------------------------------------------

inspSpecProps :: [(String, IO Result)]
inspSpecProps =
  [ ("insp replay + dependency exactness", quickCheckResult prop_inspReplayAndDeps)
  , ("insp source-unit mismatch rejected", quickCheckResult prop_inspSourceMismatchRejected)
  , ("insp feature mutation rejected", quickCheckResult prop_inspFeatureMutationRejected)
  , ("insp slot out of range rejected", quickCheckResult prop_inspSlotOutOfRangeRejected)
  , ("insp theory-entry slot rejected (premise-only)", quickCheckResult prop_inspTheorySlotRejected)
  , ("insp unknown digest rejected", quickCheckResult prop_inspUnknownDigestRejected)
  , ("insp certificate/goal arity mismatch rejected", quickCheckResult prop_inspArityMismatchRejected)
  , ("insp strictCheck seals a judgment", quickCheckResult prop_inspStrictCheckSeals)
  , ("insp accept matrix (all four members)", quickCheckResult prop_inspAcceptMatrix)
  , ("insp contrary pair is co-acceptable", quickCheckResult prop_inspContraryCoAcceptable)
  , ("insp same-slot diff rejected", quickCheckResult prop_inspSameSlotDiffRejected)
  , ("insp replay rejection matrix", quickCheckResult prop_inspRejectionMatrix)
  , ("insp closed predicate family", quickCheckResult prop_inspPredTable)
  , ("insp reserved constructor table", quickCheckResult prop_inspConTable)
  , ("insp goal grammar matrix", quickCheckResult prop_inspGoalMatrix)
  , ("insp inventory convention matrix", quickCheckResult prop_inspInventoryMatrix)
  , ("insp structural decision matrix", quickCheckResult prop_inspHoldsRelMatrix)
  , ("insp relation laws", quickCheckResult prop_inspRelLaws)
  , ("insp wire tag round-trip", quickCheckResult prop_inspTagRoundTrip)
  , ("insp flat schemas distinct", quickCheckResult prop_inspSchemasDistinct)
  , ("insp literal wire golden vectors", quickCheckResult prop_inspWireGoldenVectors)
  , ("insp closed decoder rejection matrix", quickCheckResult prop_inspDecodeRejectionMatrix)
  , ("insp huge slot rejected at decode", quickCheckResult prop_inspHugeSlotRejected)
  ]
