-- | Closed executable binary methods. Successful applications cannot be forged.
module Lara.Process.CheckedMethods
  ( Prior(..), ModelRef(..), PreRef(..), ProgramRef(..), PostRef(..)
  , Binding(..), Point(..), Request(..), Evidence, DerivationError(..)
  , ImplicationSide(..), DerivationPremise(..)
  , methodBinding, methodRequest, methodEvidence, requestFromBinding
  , checkDerivation, checkBinding, checkApplication, allowed
  , Application, applicationMethod, applicationRequest, applicationOutcome
  , ReportCell(..), Dataset(..), Command(..), Snapshot(..), ExecutionEvent(..), Status(..), Outcome(..)
  , methodBefore, methodAfter, methodCommand, pointSnapshot, run, scheduledRun
  ) where

import Data.Ratio ((%))
import Numeric.Natural (Natural)
import Lara.Process.Audit.Types (Method(..), MethodBinding(..), ApplicationError(..))

data Prior = TwoPrior | LowPrior | UpPrior deriving (Eq, Ord, Show)
data ModelRef = Binary Prior | Dirac deriving (Eq, Show)
data PreRef = SinglePre Prior | MultiplePre | FalsePre deriving (Eq, Show)
data ProgramRef = SingleProgram Natural | SecondProgram | SkipProgram deriving (Eq, Show)
data PostRef = SinglePost Prior Natural | DisjunctionPost | ConjunctionPost | FalsePost deriving (Eq, Show)
data Binding = Binding
  { bindingModel :: ModelRef, bindingPre :: PreRef
  , bindingProgram :: ProgramRef, bindingPost :: PostRef
  } deriving (Eq, Show)
data Point = Sampled | Single Natural | Pair | Hidden | Skipped deriving (Eq, Show)
data Request = Request
  { requestBinding :: Binding, requestBefore :: Point, requestAfter :: Point
  , requestParameter :: Integer, requestFirst :: Bool, requestSecond :: Bool
  } deriving (Eq, Show)

methodBinding :: Method -> Binding
methodBinding Two = Binding (Binary TwoPrior) (SinglePre TwoPrior) (SingleProgram 0) (SinglePost TwoPrior 0)
methodBinding Low = Binding (Binary LowPrior) (SinglePre LowPrior) (SingleProgram 2) (SinglePost LowPrior 2)
methodBinding Up = Binding (Binary UpPrior) (SinglePre UpPrior) (SingleProgram 3) (SinglePost UpPrior 3)
methodBinding Disjunction = Binding (Binary TwoPrior) MultiplePre SecondProgram DisjunctionPost
methodBinding Conjunction = Binding (Binary TwoPrior) MultiplePre SecondProgram ConjunctionPost
methodBinding ConditionalFalse = Binding (Binary TwoPrior) FalsePre SkipProgram FalsePost

methodBefore :: Method -> Point
methodBefore Disjunction = Single 0
methodBefore Conjunction = Single 0
methodBefore _ = Sampled
methodAfter :: Method -> Point
methodAfter Two = Single 0
methodAfter Low = Single 2
methodAfter Up = Single 3
methodAfter Disjunction = Pair
methodAfter Conjunction = Pair
methodAfter ConditionalFalse = Skipped
methodRequest :: Method -> Integer -> Bool -> Bool -> Request
methodRequest m = Request (methodBinding m) (methodBefore m) (methodAfter m)
requestFromBinding :: MethodBinding -> Request
requestFromBinding b = methodRequest (bindingMethod b) (bindingParameter b) (bindingFirst b) (bindingSecond b)

-- These constructors are private: proved implications come only from the frozen
-- kernel-bound built-ins, never from caller verdict flags. Code validation is
-- context-free; the method supplies its independently fixed P/C/Q binding.
data EntailmentCode = Proved deriving (Eq, Show)
-- Only skip, test and consequence are used by the six executable methods.
data Evidence = SkipCode | TestCode | ConsequenceCode EntailmentCode (Maybe Evidence) EntailmentCode
  deriving (Eq, Show)
data ImplicationSide = Initial | Final deriving (Eq, Show)
data DerivationPremise = ConsequenceBody deriving (Eq, Show)
data DerivationError = MissingImplication ImplicationSide | InvalidImplication ImplicationSide
  | MissingPremise DerivationPremise | InPremise DerivationPremise DerivationError
  deriving (Eq, Show)
methodEvidence :: Method -> Evidence
methodEvidence ConditionalFalse = SkipCode
methodEvidence _ = ConsequenceCode Proved (Just TestCode) Proved
checkEntailment :: ImplicationSide -> EntailmentCode -> Either DerivationError ()
checkEntailment _ Proved = Right ()
checkDerivation :: Evidence -> Either DerivationError ()
checkDerivation SkipCode = Right ()
checkDerivation TestCode = Right ()
checkDerivation (ConsequenceCode initial body final) = do
  checkEntailment Initial initial
  case body of
    Nothing -> Left (MissingPremise ConsequenceBody)
    Just code -> case checkDerivation code of
      Left fault -> Left (InPremise ConsequenceBody fault)
      Right () -> Right ()
  checkEntailment Final final

checkBinding :: Binding -> Binding -> Either ApplicationError ()
checkBinding expected actual
  | bindingModel actual /= bindingModel expected = Left ApplicationModelMismatch
  | bindingPre actual /= bindingPre expected = Left ApplicationPremiseMismatch
  | bindingProgram actual /= bindingProgram expected = Left ApplicationProgramMismatch
  | bindingPost actual /= bindingPost expected = Left ApplicationPostconditionMismatch
  | otherwise = Right ()
allowed :: Prior -> Integer -> Bool
allowed TwoPrior n = n == -1 || n == 0 || n == 1
allowed LowPrior n = n == -1 || n == 0
allowed UpPrior n = n == 0 || n == 1
methodPrior :: Method -> Prior
methodPrior Low = LowPrior
methodPrior Up = UpPrior
methodPrior _ = TwoPrior

data ReportCell = FirstReport | SecondReport deriving (Eq, Show)
data Dataset = FirstDataset | SecondDataset deriving (Eq, Show)
data Command = SkipCommand | TestCommand ReportCell Dataset Natural deriving (Eq, Show)
-- Finite coordinates of the canonical snapshots. The protected old report and
-- integer cells are retained even though none of these commands modifies them.
data Snapshot = Snapshot
  { snapshotFirst :: Bool, snapshotSecond :: Bool
  , snapshotX :: Integer, snapshotY :: Integer, snapshotOldReport :: Rational
  , snapshotReport :: Maybe Rational, snapshotSecondReport :: Maybe Rational
  , snapshotLedger :: [(Bool,Natural)]
  } deriving (Eq, Show)
data ExecutionEvent = ExecutionEvent { eventCommand :: Command, eventState :: Snapshot } deriving (Eq, Show)
data Status = Completed | Incomplete | ScheduleChoice Natural deriving (Eq, Show)
data Outcome = Outcome
  { outcomeStatus :: Status, outcomeResidual :: Maybe Command
  , outcomeState :: Snapshot, outcomeEvents :: [ExecutionEvent]
  } deriving (Eq, Show)
initialSnapshot :: Bool -> Bool -> Snapshot
initialSnapshot a b = Snapshot a b 0 0 (7 % 11) Nothing Nothing []
pvalue :: Bool -> Rational
pvalue True = 1 % 4
pvalue False = 1
execute :: Command -> Snapshot -> Snapshot
execute SkipCommand s = s
execute (TestCommand target dataset name) s =
  let sample = case dataset of FirstDataset -> snapshotFirst s; SecondDataset -> snapshotSecond s
      recorded = s { snapshotLedger = snapshotLedger s ++ [(sample,name)] }
  in case target of
    FirstReport -> recorded { snapshotReport = Just (pvalue sample) }
    SecondReport -> recorded { snapshotSecondReport = Just (pvalue sample) }
pointSnapshot :: Point -> Bool -> Bool -> Snapshot
pointSnapshot point a b = case point of
  Sampled -> initial
  Skipped -> initial
  Single name -> execute (TestCommand FirstReport FirstDataset name) initial
  Pair -> execute (TestCommand SecondReport SecondDataset 1) (execute (TestCommand FirstReport FirstDataset 0) initial)
  Hidden -> execute (TestCommand FirstReport FirstDataset 0) (execute (TestCommand FirstReport FirstDataset 4) initial)
  where initial = initialSnapshot a b
methodCommand :: Method -> Command
methodCommand m = case bindingProgram (methodBinding m) of
  SingleProgram name -> TestCommand FirstReport FirstDataset name
  SecondProgram -> TestCommand SecondReport SecondDataset 1
  SkipProgram -> SkipCommand
-- Canonical sources are single commands, hence their nextAll list has exactly
-- one element. Terminal replay ignores surplus schedule entries, as in Lean.
scheduledRun :: [Natural] -> Command -> Snapshot -> Outcome
scheduledRun [] command state = Outcome Incomplete (Just command) state []
scheduledRun (choice:_) command state
  | choice /= 0 = Outcome (ScheduleChoice choice) (Just command) state []
  | otherwise = let after = execute command state
                in Outcome Completed Nothing after [ExecutionEvent command after]
run :: Method -> Integer -> Bool -> Bool -> Outcome
run m _ a b = scheduledRun [0] (methodCommand m) (pointSnapshot (methodBefore m) a b)

data Application = Application Method Request Outcome deriving (Eq, Show)
applicationMethod :: Application -> Method
applicationMethod (Application m _ _) = m
applicationRequest :: Application -> Request
applicationRequest (Application _ r _) = r
applicationOutcome :: Application -> Outcome
applicationOutcome (Application _ _ out) = out
checkApplication :: Method -> Request -> Either ApplicationError Application
checkApplication m r = do
  checkBinding (methodBinding m) (requestBinding r)
  if requestBefore r /= methodBefore m || requestAfter r /= methodAfter m
    then Left ApplicationRunMismatch
    else if not (allowed (methodPrior m) (requestParameter r)) || m == ConditionalFalse
      then Left ApplicationFailedPrecondition
      else Right (Application m r (run m (requestParameter r) (requestFirst r) (requestSecond r)))
