-- | Stable-identity graph comparisons and the sufficient grounded-locality test.
module Lara.Process.Locality
  ( Graph, graph, graphCarrier, graphEdges, attacks, incoming, ancestors, nodeDiff, edgeDiff
  , supportCorresponds, correlates, regionsCorrespond, localityHolds, LocalityCheck (..), checkLocality
  , sharedCarrier, observationGraph, LiftedGraph, liftObservation, liftedGraph, liftedSupport, liftedRegion
  ) where

import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import Numeric.Natural (Natural)
import qualified Lara.AST as A
import qualified Lara.Grounded as Grounded
import Lara.Prop (Prop)
import Lara.Process.History (dedupLast, naturalLength)
import Lara.Process.Source

-- The relation is total; the separate bounded index represents graphEdges.
data Graph = Graph [Natural] [(Natural,Natural)] (Set.Set (Natural,Natural)) (Set.Set (Natural,Natural))
graph :: [Natural] -> [(Natural,Natural)] -> Graph
graph carrier edges = Graph carrier ordered bounded relation
  where
    relation = Set.fromList edges
    domain = Set.fromList carrier
    bounded = Set.filter (\(source,target) -> Set.member source domain && Set.member target domain) relation
    ordered = [(source,target) | source <- carrier,target <- carrier,Set.member (source,target) bounded]
graphCarrier :: Graph -> [Natural]
graphCarrier (Graph carrier _ _ _) = carrier
graphEdges :: Graph -> [(Natural,Natural)]
graphEdges (Graph _ edges _ _) = edges
attacks :: Graph -> Natural -> Natural -> Bool
attacks (Graph _ _ _ relation) source target = Set.member (source,target) relation
graphEdgeIndex :: Graph -> Set.Set (Natural,Natural)
graphEdgeIndex (Graph _ _ bounded _) = bounded
incoming :: Graph -> Natural -> [Natural]
incoming framework target = filter (\source -> attacks framework source target) (graphCarrier framework)
ancestors :: Graph -> [Natural] -> [Natural]
ancestors framework support = rounds (naturalLength carrier) (filter (`elem` support) carrier)
  where
    carrier = graphCarrier framework
    rounds 0 region = region
    rounds _ [] = []
    rounds count region
      | region == carrier = region
      | otherwise =
          let expanded = filter (\source -> source `elem` region || any (attacks framework source) region) carrier
          in if expanded == region then region else rounds (count-1) expanded
nodeDiff :: Graph -> Graph -> [Natural]
nodeDiff before after = filter (`notElem` graphCarrier after) (graphCarrier before)
  ++ filter (`notElem` graphCarrier before) (graphCarrier after)
edgeDiff :: Graph -> Graph -> [(Natural,Natural)]
edgeDiff before after = filter (`Set.notMember` graphEdgeIndex after) (graphEdges before)
  ++ filter (`Set.notMember` graphEdgeIndex before) (graphEdges after)
supportCorresponds :: [Natural] -> [Natural] -> Bool
supportCorresponds before after = all (`elem` after) before && all (`elem` before) after
correlates :: Graph -> Graph -> [Natural] -> Bool
correlates before after = all (\node -> node `elem` graphCarrier before && node `elem` graphCarrier after
  && incoming before node == incoming after node)
validSupports :: Graph -> Graph -> [Natural] -> [Natural] -> Bool
validSupports before after supportBefore supportAfter =
  all (`elem` graphCarrier before) supportBefore && all (`elem` graphCarrier after) supportAfter
    && supportCorresponds supportBefore supportAfter
localityHolds :: Graph -> Graph -> [Natural] -> [Natural] -> Bool
localityHolds before after supportBefore supportAfter = regionsCorrespond before after supportBefore supportAfter
  (ancestors before supportBefore) (ancestors after supportAfter)
-- Region correspondence alone does not compute ancestry. Callers supply the
-- actual regions, allowing impact locality and read footprints to share them.
regionsCorrespond :: Graph -> Graph -> [Natural] -> [Natural] -> [Natural] -> [Natural] -> Bool
regionsCorrespond before after supportBefore supportAfter regionBefore regionAfter =
  validSupports before after supportBefore supportAfter
    && correlates before after regionBefore && correlates before after regionAfter
data LocalityCheck = LocalityCheck
  { localitySupportBefore :: [Natural], localitySupportAfter :: [Natural]
  , localityNodeDiff :: [Natural], localityEdgeDiff :: [(Natural,Natural)]
  , localityRegionBefore :: [Natural], localityRegionAfter :: [Natural], localityAccepted :: Bool
  } deriving (Eq, Show)
checkLocality :: Graph -> Graph -> [Natural] -> [Natural] -> LocalityCheck
checkLocality before after supportBefore supportAfter = LocalityCheck supportBefore supportAfter
  (nodeDiff before after) (edgeDiff before after) regionBefore regionAfter accepted
  where
    regionBefore = ancestors before supportBefore
    regionAfter = ancestors after supportAfter
    accepted = regionsCorrespond before after supportBefore supportAfter regionBefore regionAfter
sharedCarrier :: [A.ArgId] -> [A.ArgId] -> [A.ArgId]
sharedCarrier before after = dedupLast (before ++ after)
-- The source cache already stores edges in its own carrier order.
observationGraph :: AcceptedObservation -> Graph
observationGraph observation = Graph
  (map fromIntegral (Grounded.afArgs (observationAF observation))) edges index index
  where
    edges = observationEdges observation
    index = Set.fromList edges
-- Compact nodes name their own endpoint, then lift into shared serialization
-- positions. The retained map is reused by every query on this graph.
-- Transporting compact ancestry requires the supplied carrier to cover every
-- checked name; native comparisons satisfy this with the full name union.
data LiftedGraph = LiftedGraph Graph AcceptedObservation (Map.Map Natural Natural)
liftObservation :: [A.ArgId] -> AcceptedObservation -> LiftedGraph
liftObservation carrier observation = LiftedGraph framework observation identities
  where
    positions = Map.fromList (zip carrier [0..])
    identities = Map.fromDistinctAscList [(index,position) |
      (index,name) <- zip [0..] (observationNames observation),Just position <- [Map.lookup name positions]]
    nodes = map snd (Map.toAscList identities)
    edges = [(left,right) | (source,target) <- observationEdges observation,
      Just left <- [Map.lookup source identities],Just right <- [Map.lookup target identities]]
    edgeIndex = Set.fromList edges
    framework = Graph nodes edges edgeIndex edgeIndex
liftedGraph :: LiftedGraph -> Graph
liftedGraph (LiftedGraph framework _ _) = framework
liftedSupport :: LiftedGraph -> Prop -> [Natural]
liftedSupport lifted@(LiftedGraph _ observation _) query = liftedRegion lifted (observationSupport observation query)
liftedRegion :: LiftedGraph -> [Natural] -> [Natural]
liftedRegion (LiftedGraph _ _ identities) = mapMaybe (`Map.lookup` identities)
