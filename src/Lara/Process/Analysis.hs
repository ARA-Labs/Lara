-- | Finite analyses consume the retained checked rows; they never check sources.
module Lara.Process.Analysis where

import Data.Either (isRight)
import Data.List (find, sortOn, subsequences)
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import Numeric.Natural (Natural)
import Lara.Process.Audit.Types
import qualified Lara.Process.Family as Family
import Lara.Process.History (dedupLast, naturalLength, queryHolds)
import Lara.Process.Projection
import Lara.Process.Source.Diagnostic (SourceRejection)
import Lara.Process.Types
import Lara.Wire (PublicStatus)

data Observable = StatusObservable ClaimId | AuditObservable ClaimId WitnessId ProfileSpec deriving (Eq, Show)
data Target = StatusTarget ClaimId PublicStatus | AuditTarget ClaimId WitnessId ProfileSpec deriving (Eq, Show)
data Literal = SlotEq SlotId ChoiceId | SlotNe SlotId ChoiceId | Present Stamped | Absent Stamped
  | Before Stamped Stamped | Formula Query | NotFormula Query deriving (Eq, Ord, Show)
data ObservationValue = StatusValue (Maybe PublicStatus) | AuditValue Bool deriving (Eq, Show)
type Observation = Either SourceRejection ObservationValue

statusRead :: Row -> ClaimId -> Either SourceRejection (Maybe PublicStatus)
statusRead row claim = case rowView row of
  Left rejection -> Left rejection
  Right prepared -> Right (queryStatus <$> find ((== claim) . queryClaim) (preparedQueries prepared))
auditRead :: Row -> ClaimId -> WitnessId -> ProfileSpec -> Either SourceRejection Bool
auditRead row claim witness profile = case rowView row of
  Left rejection -> Left rejection
  Right _ -> Right (warranted row profile claim witness)
statusObservations :: CheckedFamily -> ClaimId -> [(Completion, Either SourceRejection (Maybe PublicStatus))]
statusObservations checked claim = [(snapshotCompletion (rowSnapshot row),statusRead row claim) | row <- checkedRows checked]
auditObservations :: CheckedFamily -> ClaimId -> WitnessId -> ProfileSpec -> [(Completion, Either SourceRejection Bool)]
auditObservations checked claim witness profile =
  [(snapshotCompletion (rowSnapshot row),auditRead row claim witness profile) | row <- checkedRows checked]
observations :: CheckedFamily -> Observable -> [(Completion,Observation)]
observations checked observable = case observable of
  StatusObservable claim -> [(completion,StatusValue <$> value) | (completion,value) <- statusObservations checked claim]
  AuditObservable claim witness profile -> [(completion,AuditValue <$> value) | (completion,value) <- auditObservations checked claim witness profile]
targetObservable :: Target -> Observable
targetObservable (StatusTarget claim _) = StatusObservable claim
targetObservable (AuditTarget claim witness profile) = AuditObservable claim witness profile
targetValue :: Target -> ObservationValue
targetValue (StatusTarget _ status) = StatusValue (Just status)
targetValue AuditTarget{} = AuditValue True

wholeStable :: Eq a => [a] -> Bool
wholeStable [] = False
wholeStable (value:rest) = all (== value) rest
acceptedStable :: Eq a => [Either SourceRejection a] -> Bool
acceptedStable = wholeStable . filter isRight

data StabilityResult = StabilityResult
  { stabilityObservable :: Observable, stabilityTotal :: Natural, stabilityAccepted :: Natural
  , stabilityRejected :: Natural, stabilityWhole :: Bool, stabilityAcceptedDomain :: Bool
  } deriving (Eq, Show)
stability :: CheckedFamily -> Observable -> StabilityResult
stability checked observable = stabilityFrom observable (map snd (observations checked observable))
conditionalStability :: CheckedFamily -> Observable -> [Literal] -> StabilityResult
conditionalStability checked observable literals = stabilityFrom observable
  [value | (completion,value) <- observations checked observable,all (`literalHolds` completion) literals]
stabilityFrom :: Observable -> [Observation] -> StabilityResult
stabilityFrom observable values = StabilityResult observable total accepted
  (total-accepted) (wholeStable values) (wholeStable acceptedValues)
  where
    total = naturalLength values
    acceptedValues = filter isRight values
    accepted = naturalLength acceptedValues

selectionFor :: Completion -> SlotId -> Maybe Choice
selectionFor completion slot = selectionChoice <$> find ((== slot) . selectionSlot) (completionAssignment completion)
changedSlots :: FamilySpec -> Completion -> Completion -> [SlotId]
changedSlots spec reference completion = [slotId slot | slot <- familySlots spec,
  selectionFor reference (slotId slot) /= selectionFor completion (slotId slot)]
-- One-position deletions retain prefixes and avoid machine-sized indexes.
immediateDeletions :: [a] -> [[a]]
immediateDeletions [] = []
immediateDeletions (value:rest) = rest : map (value:) (immediateDeletions rest)

data SensitivityRow = SensitivityRow { sensitivityCompletion :: Completion, sensitivityChanged :: [SlotId] } deriving (Eq, Show)
data SensitivityResult = SensitivityResult
  { sensitivityObservable :: Observable, sensitivityReference :: Completion, sensitivityTotal :: Natural
  , sensitivityCount :: Natural, sensitivityDiffering :: [SensitivityRow], sensitivityMinimal :: [[SlotId]]
  , sensitivityRealizing :: [([SlotId],Completion)]
  } deriving (Eq, Show)
sensitivity :: CheckedFamily -> Observable -> Completion -> Maybe SensitivityResult
sensitivity checked observable reference = do
  referenceValue <- lookup reference table
  let different = [(completion,value) | (completion,value) <- table,value /= referenceValue]
      sameHistory = [SensitivityRow completion (changedSlots spec reference completion) |
        (completion,_) <- different,completionHistory completion == completionHistory reference]
      universe = zip (dedupLast (map slotId (familySlots spec))) [0 :: Natural ..]
      changes = dedupLast (map (Set.fromList . sensitivityChanged) sameHistory)
      -- A nonempty minimal flip set must be one of the differing rows' changed
      -- sets; a proper superset still admits that row after deleting an extra
      -- slot. An empty changed set instead makes every singleton minimal.
      minimal change = not (any (`Set.isProperSubsetOf` change) changes)
      candidates = [[(position,slot) | (slot,position) <- universe,Set.member slot change]
        | change <- changes,minimal change]
      -- Reversed universe positions have the same colex order as subsequences,
      -- without constructing the slot universe's unbudgeted powerset.
      sets = if any Set.null changes then [[slot] | (slot,_) <- universe]
        else map (map snd) (sortOn (reverse . map fst) candidates)
      realizing slots = (slots,) . sensitivityCompletion <$> find (all (`elem` slots) . sensitivityChanged) sameHistory
  pure (SensitivityResult observable reference (naturalLength table) (naturalLength different) sameHistory sets (mapMaybe realizing sets))
  where
    spec = checkedSpec checked
    table = observations checked observable

literalHolds :: Literal -> Completion -> Bool
literalHolds literal completion = case literal of
  SlotEq slot choice -> (choiceId <$> selectionFor completion slot) == Just choice
  SlotNe slot choice -> (choiceId <$> selectionFor completion slot) /= Just choice
  Present event -> Family.guardHolds (GuardPresent event) history
  Absent event -> not (Family.guardHolds (GuardPresent event) history)
  Before first second -> Family.guardHolds (GuardBefore first second) history
  Formula query -> queryHolds query history
  NotFormula query -> not (queryHolds query history)
  where history = completionHistory completion
restrict :: [Completion] -> [Literal] -> [Completion]
restrict completions literals = filter (\completion -> all (`literalHolds` completion) literals) completions
removeLiteral :: [Literal] -> Literal -> [Literal]
removeLiteral literals literal = filter (/= literal) literals

data Deletion = Deletion { deletionLiteral :: Literal, deletionSurviving :: [Completion], deletionCounter :: Maybe Completion } deriving (Eq, Show)
data MinimalSet = MinimalSet { minimalLiterals :: [Literal], minimalSurviving :: [Completion], minimalDeletions :: [Deletion] } deriving (Eq, Show)
data AssumptionResult = AssumptionResult
  { assumptionTarget :: Target, assumptionCatalog :: [Literal], assumptionTotal :: Natural, assumptionMinimal :: [MinimalSet] } deriving (Eq, Show)
assumptions :: CheckedFamily -> Target -> [Literal] -> AssumptionResult
assumptions checked target catalog = AssumptionResult target catalog (naturalLength table) (map result minimal)
  where
    table = observations checked (targetObservable target)
    expected = Right (targetValue target)
    restricted literals = filter (\(completion,_) -> all (`literalHolds` completion) literals) table
    satisfies literals = case restricted literals of
      [] -> False
      values -> all ((== expected) . snd) values
    isMinimal literals = satisfies literals && all (not . satisfies) (immediateDeletions literals)
    minimal = filter isMinimal (subsequences (dedupLast catalog))
    deletion literals literal = let remaining = restricted (removeLiteral literals literal)
      in Deletion literal (map fst remaining) (fst <$> find ((/= expected) . snd) remaining)
    result literals = MinimalSet literals (map fst (restricted literals)) (map (deletion literals) literals)

data FamilyStatusRow = FamilyStatusRow
  { familyStatusHistory :: ProcessHistory, familyStatusAssignment :: [(SlotId,ChoiceId)]
  , familyStatusRejection :: Maybe SourceRejection, familyStatusValue :: Maybe PublicStatus } deriving (Eq, Show)
data FamilyAuditRow = FamilyAuditRow
  { familyAuditHistory :: ProcessHistory, familyAuditAssignment :: [(SlotId,ChoiceId)]
  , familyAuditRejection :: Maybe SourceRejection, familyAuditValue :: Maybe Bool } deriving (Eq, Show)
data FamilyStatusResult = FamilyStatusResult
  { familyStatusRows :: [FamilyStatusRow], familyStatusTotal :: Natural, familyStatusAccepted :: Natural
  , familyStatusRejected :: Natural, familyStatusVerdict :: Bool } deriving (Eq, Show)
data FamilyAuditResult = FamilyAuditResult
  { familyAuditRows :: [FamilyAuditRow], familyAuditTotal :: Natural, familyAuditAccepted :: Natural
  , familyAuditRejected :: Natural, familyAuditVerdict :: Bool } deriving (Eq, Show)
assignmentIds :: Completion -> [(SlotId,ChoiceId)]
assignmentIds = map (\selection -> (selectionSlot selection,choiceId (selectionChoice selection))) . completionAssignment
familyStatus :: CheckedFamily -> ClaimId -> FamilyStatusResult
familyStatus checked claim = FamilyStatusResult rows total accepted (total-accepted) (wholeStable (map snd table))
  where
    table = statusObservations checked claim
    total = naturalLength table
    accepted = naturalLength (filter (isRight . snd) table)
    rows = [FamilyStatusRow (completionHistory completion) (assignmentIds completion)
      (either Just (const Nothing) value) (either (const Nothing) id value) | (completion,value) <- table]
familyAudit :: CheckedFamily -> ClaimId -> WitnessId -> ProfileSpec -> FamilyAuditResult
familyAudit checked claim witness profile = FamilyAuditResult rows total accepted (total-accepted) (audit checked profile claim witness)
  where
    table = auditObservations checked claim witness profile
    total = naturalLength table
    accepted = naturalLength (filter (isRight . snd) table)
    rows = [FamilyAuditRow (completionHistory completion) (assignmentIds completion)
      (either Just (const Nothing) value) (either (const Nothing) Just value) | (completion,value) <- table]
