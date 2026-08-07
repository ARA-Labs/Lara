-- | Property tests for the trusted kernel.
--
-- Axis (a) of the eval plan lives here: deterministic correctness of the
-- checker itself, independent of any LLM. We test the algebraic laws of the
-- LP rules by generating derivations that check /by construction/ and a few
-- that must be rejected.
module Main (main) where

import Control.Monad (unless)
import System.Exit (exitFailure)
import Test.QuickCheck

import Lara.ConstantSpec
  (Context, ConstantSpec, emptyContext, emptySpec, insertSpec)
import Lara.Formula (Atom (..), Formula (..))
import Lara.Kernel
  ( CheckError (..)
  , Derivation (..)
  , check
  , judgmentFormula
  , judgmentTerm
  )
import Lara.Term (Con (..), Term (..), Var (..))

import AblationSpec (ablationSpecProps)
import AdmissionSpec (admissionSpecProps)
import BlockedSpec (blockedSpecProps)
import CheckSpec (checkSpecProps)
import CliSpec (cliSpecProps)
import CorpusUnitsSpec (corpusUnitsSpecProps)
import DifferentialSpec (differentialSpecProps)
import ElaborateSpec (elaborateSpecProps)
import ClaimSupportSpec (claimSupportSpecProps)
import MechReviewSpec (mechReviewSpecProps)
import MeasureSpec (measureSpecProps)
import MutationSpec (mutationSpecProps)
import PropSpec (propSpecProps)
import OrdSpec (ordSpecProps)
import RASpec (raSpecProps)
import ReportingSpec (reportingSpecProps)
import ReplaySpec (replaySpecProps)
import RunningExampleSpec (runningExampleSpecProps)
import RuntimeSpec (runtimeSpecProps)
import StrictSpec (strictSpecProps)
import SyntaxSpec (syntaxSpecProps)
import WireSpec (wireSpecProps)
import WorkedExamplesSpec (workedExamplesSpecProps)

-- ---------------------------------------------------------------------------
-- Generators
-- ---------------------------------------------------------------------------

genAtom :: Gen Formula
genAtom = FAtom . Atom . (: []) <$> elements ['P' .. 'T']

genFormula :: Gen Formula
genFormula = sized go
  where
    go n
      | n <= 0 = oneof [genAtom, pure Bot]
      | otherwise =
          frequency
            [ (3, genAtom)
            , (1, pure Bot)
            , (2, Imp <$> go (n `div` 2) <*> go (n `div` 2))
            ]

genTerm :: Gen Term
genTerm = sized go
  where
    go n
      | n <= 0 = oneof [TVar . Var . (: []) <$> elements ['u' .. 'z']
                       , TCon . Con . (: []) <$> elements ['a' .. 'e']]
      | otherwise =
          frequency
            [ (3, go 0)
            , (1, Sum <$> go (n `div` 2) <*> go (n `div` 2))
            , (1, Bang <$> go (n - 1))
            ]

-- | A constant specification, a context, and a derivation that is guaranteed
-- to check — built by only ever composing valid pieces.
data Valid = Valid ConstantSpec Context Derivation

instance Show Valid where
  show (Valid spec ctx d) =
    "Valid " ++ show spec ++ " " ++ show ctx ++ " " ++ show d

genValid :: Gen Valid
genValid = sized build
  where
    build n
      | n <= 0 = do
          -- a leaf: a constant pinned to a fresh formula
          c <- Con . (: []) <$> elements ['a' .. 'e']
          f <- genFormula
          pure (Valid (insertSpec c f emptySpec) emptyContext (DConst c f))
      | otherwise =
          oneof
            [ build 0
            , do
                Valid spec ctx d <- build (n - 1)
                t <- genTerm
                elements [Valid spec ctx (DSumL d t), Valid spec ctx (DSumR t d)]
            , do
                Valid spec ctx d <- build (n - 1)
                pure (Valid spec ctx (DCheck d))
            ]

instance Arbitrary Valid where
  arbitrary = genValid

-- ---------------------------------------------------------------------------
-- Properties
-- ---------------------------------------------------------------------------

-- | Every generated valid derivation checks.
prop_validChecks :: Valid -> Bool
prop_validChecks (Valid spec ctx d) =
  case check spec ctx d of
    Right _ -> True
    Left _ -> False

-- | Sum-monotonicity: if @d@ checks to @s : A@, then @s + t@ still checks to
-- @A@ on either side. Adding evidence never invalidates and never changes the
-- formula.
prop_sumMonotone :: Valid -> Property
prop_sumMonotone (Valid spec ctx d) =
  forAll genTerm $ \t ->
    case check spec ctx d of
      Left _ -> True -- vacuous (generator guarantees Right, but stay total)
      Right j ->
        let f = judgmentFormula j
            okL = fmap judgmentFormula (check spec ctx (DSumL d t)) == Right f
            okR = fmap judgmentFormula (check spec ctx (DSumR t d)) == Right f
         in okL && okR

-- | Check (positive introspection) wraps @t : A@ into @(!t) : (t : A)@.
prop_checkIntrospection :: Valid -> Bool
prop_checkIntrospection (Valid spec ctx d) =
  case check spec ctx d of
    Left _ -> True
    Right j ->
      case check spec ctx (DCheck d) of
        Right j' ->
          judgmentTerm j' == Bang (judgmentTerm j)
            && judgmentFormula j' == Col (judgmentTerm j) (judgmentFormula j)
        Left _ -> False

-- | A constant not declared for the claimed formula is rejected.
prop_unknownConstantRejected :: Bool
prop_unknownConstantRejected =
  check emptySpec emptyContext (DConst (Con "c") (FAtom (Atom "P")))
    == Left (UnknownConstant (Con "c") (FAtom (Atom "P")))

-- | Applying a non-implication is rejected.
prop_appNonImplicationRejected :: Bool
prop_appNonImplicationRejected =
  let p = FAtom (Atom "P")
      spec = insertSpec (Con "c") p emptySpec
      d = DApp (DConst (Con "c") p) (DConst (Con "c") p)
   in case check spec emptyContext d of
        Left (NotAnImplication _) -> True
        _ -> False

-- | Application with a domain/argument mismatch is rejected.
prop_appMismatchRejected :: Bool
prop_appMismatchRejected =
  let p = FAtom (Atom "P")
      q = FAtom (Atom "Q")
      r = FAtom (Atom "R")
      spec = insertSpec (Con "f") (Imp p q) (insertSpec (Con "a") r emptySpec)
      d = DApp (DConst (Con "f") (Imp p q)) (DConst (Con "a") r)
   in case check spec emptyContext d of
        Left (ApplicationMismatch _ _) -> True
        _ -> False

-- ---------------------------------------------------------------------------
-- Runner
-- ---------------------------------------------------------------------------

main :: IO ()
main = do
  results <-
    sequence $
      [ run "valid derivations check" (quickCheckResult prop_validChecks)
      , run "sum monotonicity" (quickCheckResult prop_sumMonotone)
      , run "check introspection" (quickCheckResult prop_checkIntrospection)
      , run "unknown constant rejected" (quickCheckResult prop_unknownConstantRejected)
      , run "apply non-implication rejected" (quickCheckResult prop_appNonImplicationRejected)
      , run "apply mismatch rejected" (quickCheckResult prop_appMismatchRejected)
      ]
        ++ [run name act | (name, act) <- propSpecProps]
        ++ [run name act | (name, act) <- strictSpecProps]
        ++ [run name act | (name, act) <- raSpecProps]
        ++ [run name act | (name, act) <- ordSpecProps]
        ++ [run name act | (name, act) <- replaySpecProps]
        ++ [run name act | (name, act) <- wireSpecProps]
        ++ [run name act | (name, act) <- syntaxSpecProps]
        ++ [run name act | (name, act) <- elaborateSpecProps]
        ++ [run name act | (name, act) <- workedExamplesSpecProps]
        ++ [run name act | (name, act) <- corpusUnitsSpecProps]
        ++ [run name act | (name, act) <- checkSpecProps]
        ++ [run name act | (name, act) <- blockedSpecProps]
        ++ [run name act | (name, act) <- differentialSpecProps]
        ++ [run name act | (name, act) <- mutationSpecProps]
        ++ [run name act | (name, act) <- measureSpecProps]
        ++ [run name act | (name, act) <- claimSupportSpecProps]
        ++ [run name act | (name, act) <- mechReviewSpecProps]
        ++ [run name act | (name, act) <- runningExampleSpecProps]
        ++ [run name act | (name, act) <- ablationSpecProps]
        ++ [run name act | (name, act) <- admissionSpecProps]
        ++ [run name act | (name, act) <- runtimeSpecProps]
        ++ [run name act | (name, act) <- reportingSpecProps]
        ++ [run name act | (name, act) <- cliSpecProps]
  unless (and results) exitFailure
  where
    run name act = do
      putStrLn ("== " ++ name)
      r <- act
      pure (isSuccess r)
