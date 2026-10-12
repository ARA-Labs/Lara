{-# LANGUAGE BangPatterns #-}

-- | Deterministic prefix DFS and preflight-bounded guarded source products.
-- The legacy P0 completion and witness order in History is not used or changed.
module Lara.Process.Enumerate
  ( EnumeratedFamily, enumerateFamily, clampedLimits
  , enumeratedSpec, enumeratedHistories, enumeratedCompletions
  , enumeratedHistorySteps, enumeratedLogicalExtensions, enumeratedProductCount
  ) where

import Data.List (delete)
import Numeric.Natural (Natural)
import Lara.Process.Audit.Types
import Lara.Process.Family (guardHolds)
import qualified Lara.Process.History as History
import Lara.Process.Types (Problem (..), ProcessHistory)

-- Positional fields and an unexported constructor keep bounded results read-only:
-- callers cannot update the counts or insert histories that bypassed the caps.
data EnumeratedFamily = EnumeratedFamily
  FamilySpec [ProcessHistory] [Completion] Natural Natural Natural
  deriving (Eq, Show)

enumeratedSpec :: EnumeratedFamily -> FamilySpec
enumeratedSpec (EnumeratedFamily spec _ _ _ _ _) = spec

enumeratedHistories :: EnumeratedFamily -> [ProcessHistory]
enumeratedHistories (EnumeratedFamily _ histories _ _ _ _) = histories

enumeratedCompletions :: EnumeratedFamily -> [Completion]
enumeratedCompletions (EnumeratedFamily _ _ rows _ _ _) = rows

enumeratedHistorySteps :: EnumeratedFamily -> Natural
enumeratedHistorySteps (EnumeratedFamily _ _ _ steps _ _) = steps

enumeratedLogicalExtensions :: EnumeratedFamily -> Natural
enumeratedLogicalExtensions (EnumeratedFamily _ _ _ _ extensions _) = extensions

enumeratedProductCount :: EnumeratedFamily -> Natural
enumeratedProductCount (EnumeratedFamily _ _ _ _ _ products) = products

clampedLimits :: EnumerationLimits -> EnumerationLimits
clampedLimits limits = EnumerationLimits
  (min 10000 (limitHistories limits))
  (min 200000 (limitSteps limits))
  (min 10000 (limitProducts limits))

-- Count every executable prefix, including root and leaves, in the same native
-- traversal that emits histories. Compatibility only controls the stop output.
-- Reverse prefixes avoid copying the prefix on each extension; each forward
-- history is shared by its stop test and, when compatible, the output carrier.
historySearch :: Problem -> (Natural, [ProcessHistory])
historySearch problem =
  let (steps, reversed) = go History.initialState [] pool 0 []
   in (steps, History.dedupLast (reverse reversed))
  where
    pool = History.dedupLast (History.base problem ++ problemUnrecorded problem)
    go state reversedPrefix remaining !visited output =
      let !nextVisited = visited + 1
          history = reverse reversedPrefix
          !nextOutput = if History.problemCompatible problem history then history : output else output
       in foldl' (extend state reversedPrefix remaining) (nextVisited, nextOutput) remaining
    extend state reversedPrefix remaining (visited, output) event = case History.step state event of
      Nothing -> (visited, output)
      Just nextState -> go nextState (event : reversedPrefix) (delete event remaining) visited output

-- The suffix must be counted before saturating its multiplication: a late empty
-- guard annihilates completed products, even after a very large earlier slot.
-- The second component counts logical traversal nodes, not physically shared
-- suffix evaluations. A zero ends deeper reachability without erasing prefixes.
slotCounts :: Natural -> ProcessHistory -> [Slot] -> (Natural, Natural)
slotCounts _ _ [] = (1, 1)
slotCounts cap history (slot : rest)
  | choices == 0 = (0, 1)
  | otherwise =
      let (suffixProducts, suffixNodes) = slotCounts cap history rest
          !products = min (cap + 1) (choices * suffixProducts)
          nodes = 1 + choices * suffixNodes
       in (products, nodes)
  where
    choices = foldl' (\count choice -> if guardHolds (choiceGuard choice) history then count + 1 else count) 0 (slotChoices slot)

-- Saturated addition stops at the first excess, before any selections or rows
-- exist. Logical extensions are exact on every successful bounded enumeration.
productPreflight :: Natural -> [Slot] -> [ProcessHistory] -> (Natural, Natural)
productPreflight cap slots = go 0 0
  where
    go !products !extensions [] = (products, extensions)
    go !products !extensions (history : rest) =
      let (blockProducts, blockNodes) = slotCounts cap history slots
          !nextProducts = min (cap + 1) (products + blockProducts)
          nextExtensions = extensions + blockNodes - 1
       in if nextProducts > cap then (nextProducts, nextExtensions)
          else go nextProducts nextExtensions rest

-- Filter at one fixed history. The suffix is shared once, with earlier choices
-- outermost. Empty choices do not touch the suffix; an empty suffix creates no
-- partial selections, but its logical prefixes remain charged by slotCounts.
guardedAssignments :: ProcessHistory -> [Slot] -> [[Selection]]
guardedAssignments _ [] = [[]]
guardedAssignments history (slot : rest) = case filter survives (slotChoices slot) of
  [] -> []
  choices -> case guardedAssignments history rest of
    [] -> []
    suffixes -> concatMap (\choice -> map (Selection (slotId slot) choice :) suffixes) choices
  where survives choice = guardHolds (choiceGuard choice) history

enumerateFamily :: FamilySpec -> EnumerationLimits -> Either EnumerationRefusal EnumeratedFamily
enumerateFamily spec limits
  | steps > limitSteps cap = Left (StepsRefusal steps (limitSteps cap))
  | historyCount > limitHistories cap = Left (HistoriesRefusal historyCount (limitHistories cap))
  | products > limitProducts cap = Left (ProductsRefusal products (limitProducts cap))
  | otherwise = Right (EnumeratedFamily spec histories rows steps extensions products)
  where
    cap = clampedLimits limits
    (steps, histories) = historySearch (familyProblem spec)
    historyCount = History.naturalLength histories
    (products, extensions) = productPreflight (limitProducts cap) (familySlots spec) histories
    rows = concatMap (\history -> map (Completion history) (guardedAssignments history (familySlots spec))) histories
