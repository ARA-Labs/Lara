-- | Executable process transitions, scoped compatibility and the P0 reference carrier.
module Lara.Process.History where

import Control.Monad (foldM)
import Data.List (find, subsequences)
import Data.Maybe (mapMaybe, isJust)
import qualified Data.Set as Set
import Data.Void (Void, absurd)
import Numeric.Natural (Natural)
import Lara.Process.Types

data ProcessState = ProcessState
  { stateCommitted :: [(PlanId, VersionId)], stateRuns :: [RunId], stateUsed :: [EventId]
  , stateVersions :: [(DataId, VersionId)], stateRetracted :: [SourceId]
  } deriving (Eq, Show)

initialState :: ProcessState
initialState = ProcessState [] [] [] [] []

stateVersion :: ProcessState -> DataId -> VersionId
stateVersion state dataset = maybe (VersionId 0) snd (find ((== dataset) . fst) (stateVersions state))

step :: ProcessState -> Stamped -> Maybe ProcessState
step state stamped
  | stampedId stamped `elem` stateUsed state = Nothing
  | otherwise = transition state { stateUsed = stampedId stamped : stateUsed state }
  where
    transition s = case stampedEvent stamped of
      CommitPlan _ plan version -> Just s { stateCommitted = (plan, version) : stateCommitted s }
      Run run plan version inputs _
        | run `notElem` stateRuns s && (plan, version) `elem` stateCommitted s
          && all (\(dataset, inputVersion) -> stateVersion s dataset == inputVersion) inputs -> Just s { stateRuns = run : stateRuns s }
        | otherwise -> Nothing
      Result run _ | run `notElem` stateRuns s -> Nothing
      UpdateData dataset version -> Just s { stateVersions = (dataset, version) : stateVersions s }
      Retract source
        | source `elem` stateRetracted s -> Nothing
        | otherwise -> Just s { stateRetracted = source : stateRetracted s }
      _ -> Just s

runHistory :: ProcessState -> ProcessHistory -> Maybe ProcessState
runHistory = foldM step

validHistory :: ProcessHistory -> Bool
validHistory = isJust . runHistory initialState

naturalLength :: [a] -> Natural
naturalLength = foldr (\_ n -> n + 1) 0

validThrough :: Natural -> ProcessHistory -> Bool
validThrough cutoff history = naturalLength history <= cutoff && validHistory history

position :: ProcessHistory -> EventId -> Maybe Natural
position history event = go 0 history
  where
    go _ [] = Nothing
    go index (e : rest)
      | stampedId e == event = Just index
      | otherwise = go (index + 1) rest

precedes :: ProcessHistory -> EventId -> EventId -> Bool
precedes history first second = case (position history first, position history second) of
  (Just a, Just b) -> a < b
  _ -> False

planCommittedBefore :: ProcessHistory -> PlanId -> VersionId -> [DataId] -> Bool
planCommittedBefore history plan version datasets = any committed (zip [0 :: Natural ..] history)
  where
    committed (index, e) = commits (stampedEvent e) == Just (plan, version)
      && all (later index) (zip [0 :: Natural ..] history)
    later index (other, e) = case access (stampedEvent e) of
      Just (dataset, Evaluation) | dataset `elem` datasets -> index < other
      _ -> True

runPrecommitted :: ProcessHistory -> RunId -> Bool
runPrecommitted history run = all holds (mapMaybe (runSpec . stampedEvent) history)
  where holds spec = specRun spec /= run || planCommittedBefore history (specPlan spec) (specVersion spec) (map fst (specInputs spec))

predictable :: ProcessHistory -> Bool
predictable history = all (\spec -> planCommittedBefore history (specPlan spec) (specVersion spec) (map fst (specInputs spec))) (mapMaybe (runSpec . stampedEvent) history)

splitSelection :: ProcessHistory -> [DataId] -> [DataId] -> Bool
splitSelection history selection test = all (`notElem` test) selection && all separated (mapMaybe (access . stampedEvent) history)
  where
    separated (dataset, Selection) = dataset `elem` selection
    separated (dataset, Evaluation) = dataset `elem` test

familyCount :: ProcessHistory -> FamilyId -> Natural
familyCount history family = naturalLength (filter ((== Just family) . eventFamily . stampedEvent) history)

successfulRuns :: ProcessHistory -> [RunId]
successfulRuns = mapMaybe successful
  where successful (Stamped _ (Result run outcome)) | outcome > 0 = Just run
        successful _ = Nothing

orderCompatible :: OrderRecord -> ProcessHistory -> Bool
orderCompatible record history = validThrough (orderCutoff record) history
  && all (`elem` history) (orderEvents record)
  && all (uncurry (precedes history)) (orderBefore record)

scopeContains :: CoverageScope -> Natural -> Stamped -> Bool
scopeContains scope index stamped = index < scopeCutoff scope && eventKind event `elem` scopeKinds scope
  && maybe True (\family -> eventFamily event == Just family) (scopeFamily scope)
  && maybe True (\actors -> maybe False (`elem` actors) (eventActor event)) (scopeActors scope)
  && maybe True (\datasets -> not (null touched) && all (`elem` datasets) touched) (scopeData scope)
  where event = stampedEvent stamped
        touched = eventData event

scopeEvents :: CoverageScope -> ProcessHistory -> [Stamped]
scopeEvents scope history = [event | (index, event) <- zip [0 ..] history, scopeContains scope index event]

coverageAllowed :: (policy -> ProcessHistory -> [Stamped] -> Bool) -> RecordCoverage policy -> ProcessHistory -> [Stamped] -> Bool
coverageAllowed policy coverage history reported = case coverage of
  Complete scope -> all (`elem` reported) (scopeEvents scope history)
  CountBounded scope bound -> naturalLength (scopeEvents scope history) <= bound
  DeclaredPolicy _ p -> policy p history reported
  OpenWorld _ -> True

noPolicy :: Void -> ProcessHistory -> [Stamped] -> Bool
noPolicy = absurd

toOrderRecord :: DecodedRecord policy -> OrderRecord
toOrderRecord record = OrderRecord (map decodedEvent (recordEvents record)) (map (\o -> (orderFirst o, orderSecond o)) (recordOrder record)) (recordCutoff record)

compatible :: (policy -> ProcessHistory -> [Stamped] -> Bool) -> DecodedRecord policy -> ProcessHistory -> Bool
compatible policy record history = orderCompatible (toOrderRecord record) history
  && all (\assertion -> coverageAllowed policy (assertionCoverage assertion) history reported) (recordCoverage record)
  where reported = map decodedEvent (recordEvents record)

extract :: (AdmissionBasis -> Bool) -> AraSource policy -> DecodedRecord policy
extract admitted source = DecodedRecord
  [DecodedEvent event ref | EventEntry event ref <- entries]
  [DecodedOrder a b ref | OrderingEntry a b ref <- entries]
  [assertion | CoverageEntry assertion <- entries, admitted (assertionBasis assertion)]
  [(claim, witness) | SubmissionEntry claim witness <- entries]
  (sourceCutoff source)
  where entries = sourceEntries source

encodeSource :: DecodedRecord policy -> AraSource policy
encodeSource record = AraSource
  (map (\e -> EventEntry (decodedEvent e) (decodedSource e)) (recordEvents record)
  ++ map (\o -> OrderingEntry (orderFirst o) (orderSecond o) (orderSource o)) (recordOrder record)
  ++ map CoverageEntry (recordCoverage record)
  ++ map (uncurry SubmissionEntry) (recordSubmitted record)) (recordCutoff record)

sourceRel :: (policy -> ProcessHistory -> [Stamped] -> Bool) -> (AdmissionBasis -> Bool) -> AraSource policy -> ProcessHistory -> Bool
sourceRel policy admitted source = compatible policy (extract admitted source)

-- Lean List.dedup keeps the last occurrence, unlike Data.List.nub.
dedupLast :: Ord a => [a] -> [a]
dedupLast = snd . foldr keep (Set.empty, [])
  where keep value (seen, values)
          | Set.member value seen = (seen, values)
          | otherwise = (Set.insert value seen, value : values)

base :: Problem -> [Stamped]
base = dedupLast . map decodedEvent . recordEvents . problemRecord

problemCompatible :: Problem -> ProcessHistory -> Bool
problemCompatible problem history = naturalLength history == fromIntegral (Set.size (Set.fromList history))
  && compatible noPolicy (problemRecord problem) history

interleave :: a -> [a] -> [[a]]
interleave x [] = [[x]]
interleave x (y : ys) = (x : y : ys) : map (y :) (interleave x ys)

perms :: [a] -> [[a]]
perms [] = [[]]
perms (x : xs) = concatMap (interleave x) (perms xs)

-- This ordering is P0's observable unknown-witness ordering. Source-family
-- guarded enumeration is a separate algorithm, not a replacement for this one.
candidates :: Problem -> [ProcessHistory]
candidates problem = concatMap (perms . (base problem ++)) (subsequences (dedupLast (problemUnrecorded problem)))

completions :: Problem -> [ProcessHistory]
completions problem = dedupLast (filter (problemCompatible problem) possible)
  where
    recorded = base problem
    optional = filter (`notElem` recorded) (dedupLast (problemUnrecorded problem))
    possible = concatMap (perms . (recorded ++)) (subsequences optional)

atomHolds :: Atom -> ProcessHistory -> Bool
atomHolds atom history = case atom of
  RunPrecommitted run -> runPrecommitted history run
  Predictable -> predictable history
  SplitSelection selection test -> splitSelection history selection test
  FamilyCountAtMost family bound -> familyCount history family <= bound

formulaHolds :: (atom -> h -> Bool) -> Formula atom -> h -> Bool
formulaHolds holds formula history = case formula of
  QueryAtom atom -> holds atom history
  QueryNot q -> not (formulaHolds holds q history)
  QueryAnd a b -> formulaHolds holds a history && formulaHolds holds b history
  QueryOr a b -> formulaHolds holds a history || formulaHolds holds b history

queryHolds :: Query -> ProcessHistory -> Bool
queryHolds = formulaHolds atomHolds

listVerdict :: [a] -> (a -> Bool) -> Verdict
listVerdict [] _ = Inconsistent
listVerdict values holds
  | all holds values = CertainTrue
  | all (not . holds) values = CertainFalse
  | otherwise = Unknown

answerOf :: [ProcessHistory] -> Query -> Answer
answerOf histories query = Answer verdict (naturalLength histories) yes no
  where verdict = listVerdict histories (queryHolds query)
        yes = if verdict == Unknown then find (queryHolds query) histories else Nothing
        no = if verdict == Unknown then find (not . queryHolds query) histories else Nothing

answer :: Problem -> Query -> Answer
answer problem = answerOf (completions problem)

coverageKind :: RecordCoverage Void -> CoverageKind
coverageKind (Complete _) = CompleteKind
coverageKind (CountBounded _ _) = CountBoundedKind
coverageKind (OpenWorld _) = OpenWorldKind
coverageKind (DeclaredPolicy _ p) = absurd p

toProfile :: ProfileSpec -> Profile Void
toProfile spec = Profile (`elem` profileAdmissible spec) ((`elem` profileAccepts spec) . coverageKind)
  (profileGuarantee spec, if profileDen spec == 0 then 0 else fromIntegral (profileNum spec) / fromIntegral (profileDen spec))
  (`elem` profileProbes spec) (profileAcceptance spec)

admittedCoverage :: Problem -> [RecordCoverage Void]
admittedCoverage problem = case map assertionCoverage (recordCoverage (problemRecord problem)) of
  [] -> [OpenWorld (CoverageScope [] Nothing Nothing Nothing 0)]
  values -> values

entitledBy :: [h] -> [w] -> (h -> w -> Bool) -> Bool
entitledBy histories witnesses warranted = not (null histories) && all (\h -> any (warranted h) witnesses) histories

argumentEntitledBy :: [h] -> (h -> w -> Bool) -> w -> Bool
argumentEntitledBy histories warranted witness = not (null histories) && all (\h -> warranted h witness) histories
