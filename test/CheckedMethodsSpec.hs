module CheckedMethodsSpec (checkedMethodsSpecProps) where

import Data.Either (isRight)
import Data.Ratio ((%))
import Test.QuickCheck
import Lara.Process.Audit.Types
import Lara.Process.CheckedMethods

checkedMethodsSpecProps :: [(String, IO Result)]
checkedMethodsSpecProps = [(name,quickCheckResult test) | (name,test) <-
  [ ("checked methods parameter and Boolean domain", property domain)
  , ("checked methods canonical distinct bindings", property canonical)
  , ("checked methods exact binding fault precedence", property precedence)
  , ("checked methods finite outcomes and occurrences", property outcomes)
  , ("checked methods conditional derivations independent of applicability", property modes)
  , ("checked methods unbounded integers", property huge)
  , ("checked methods scheduled replay", property schedule)
  ]]
  where
    methods = [minBound .. maxBound]
    bits = [(a,b) | a <- [False,True], b <- [False,True]]
    permitted Low n = n == -1 || n == 0
    permitted Up n = n == 0 || n == 1
    permitted ConditionalFalse _ = False
    permitted _ n = n >= -1 && n <= 1
    domain = and [isRight (checkApplication m (methodRequest m n a b)) == permitted m n
                 | m <- methods, n <- [-2..2], (a,b) <- bits]
    canonical = and [methodBinding a /= methodBinding b | a <- methods, b <- methods, a /= b]
      && methodBinding Two == Binding (Binary TwoPrior) (SinglePre TwoPrior) (SingleProgram 0) (SinglePost TwoPrior 0)
      && methodBinding Low == Binding (Binary LowPrior) (SinglePre LowPrior) (SingleProgram 2) (SinglePost LowPrior 2)
      && methodBinding Up == Binding (Binary UpPrior) (SinglePre UpPrior) (SingleProgram 3) (SinglePost UpPrior 3)
      && methodBinding Disjunction == Binding (Binary TwoPrior) MultiplePre SecondProgram DisjunctionPost
      && methodBinding Conjunction == Binding (Binary TwoPrior) MultiplePre SecondProgram ConjunctionPost
      && methodBinding ConditionalFalse == Binding (Binary TwoPrior) FalsePre SkipProgram FalsePost
    rejects fault r = case checkApplication Two r of Left e -> e == fault; Right _ -> False
    base = methodRequest Two 99 False True
    wrong = Binding Dirac FalsePre SkipProgram FalsePost
    precedence = and
      [ rejects ApplicationModelMismatch (base { requestBinding = wrong, requestBefore = Hidden })
      , rejects ApplicationPremiseMismatch (base { requestBinding = wrong { bindingModel = Binary TwoPrior } })
      , rejects ApplicationProgramMismatch (base { requestBinding = wrong { bindingModel = Binary TwoPrior, bindingPre = SinglePre TwoPrior } })
      , rejects ApplicationPostconditionMismatch (base { requestBinding = (methodBinding Two) { bindingPost = FalsePost } })
      , rejects ApplicationRunMismatch (base { requestBefore = Hidden })
      , rejects ApplicationRunMismatch (base { requestAfter = Hidden })
      , rejects ApplicationFailedPrecondition base
      ]
    p True = 1 % 4
    p False = 1
    outcomes = and
      [ let out = run m 0 a b
            state = outcomeState out
            paired = m == Disjunction || m == Conjunction
            name = case m of Low -> 2; Up -> 3; _ -> 0
            expected = if m == ConditionalFalse then [] else if paired then [(a,0),(b,1)] else [(a,name)]
        in outcomeStatus out == Completed && outcomeResidual out == Nothing
          && snapshotLedger state == expected
          && snapshotOldReport state == 7 % 11
          && snapshotFirst state == a && snapshotSecond state == b
          && snapshotReport state == (if m == ConditionalFalse then Nothing else Just (p a))
          && snapshotSecondReport state == (if paired then Just (p b) else Nothing)
          && outcomeEvents out == [ExecutionEvent (methodCommand m) state]
          && case checkApplication m (methodRequest m 0 a b) of
               Left _ -> m == ConditionalFalse
               Right app -> applicationMethod app == m
                 && applicationRequest app == methodRequest m 0 a b
                 && applicationOutcome app == out
      | m <- methods, (a,b) <- bits]
    modes = and [checkDerivation (methodEvidence m) == Right ()
                  && requestFromBinding (MethodBinding m mode 999 a b []) == methodRequest m 999 a b
                | m <- methods, mode <- [ConditionalPayload,AppliedPayload], (a,b) <- bits]
    huge = and [case checkApplication m (methodRequest m n False False) of
                  Left ApplicationFailedPrecondition -> True
                  _ -> False
               | m <- methods, n <- [10^(100 :: Int), negate (10^(100 :: Int))]]
    schedule = and
      [ let state = pointSnapshot Sampled False True
            command = methodCommand Two
        in scheduledRun [] command state == Outcome Incomplete (Just command) state []
          && scheduledRun [1] command state == Outcome (ScheduleChoice 1) (Just command) state []
          && scheduledRun [0,999] command state == run Two 0 False True
      , snapshotLedger (pointSnapshot (Single 1) False True) == [(False,1)]
      , snapshotReport (pointSnapshot (Single 1) False True) == Just 1
      , snapshotSecondReport (pointSnapshot (Single 1) False True) == Nothing
      ]
