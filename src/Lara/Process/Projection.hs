module Lara.Process.Projection
  ( Snapshot, snapshotCompletion, snapshotInput, snapshotOutcome, snapshotNames
  , ModelContext, contextBase, contextConfig, contextCarrier, contextCarrierCount, contextValid, contextWitnessCoordinates
  , Prepared, preparedGraph, preparedProvenance, preparedGrades, preparedComplete
  , preparedWitnesses, preparedWitnessCertificates, preparedQueries
  , Row, rowSnapshot, rowView, rowContext, rowWitness, rowKind, rowArgument, rowArtifact, rowConcludes
  , CheckedFamily, checkFamily, checkedSpec, checkedConfig, checkedEnumeration, checkedSnapshots, checkedContext, checkedRows
  , rowAt, snapshotAt, warranted, audit, auditRows
  ) where

import Data.Either (isRight)
import Data.List (find)
import Data.Maybe (mapMaybe)
import qualified Data.Map.Lazy as Map
import qualified Data.Set as Set
import Numeric.Natural (Natural)
import qualified Lara.AST as A
import qualified Lara.Grounded as G
import qualified Lara.Process.Audit as Audit
import Lara.Process.Audit.Types
import Lara.Process.Enumerate (EnumeratedFamily, enumeratedSpec, enumeratedCompletions)
import qualified Lara.Process.Family as Family
import Lara.Process.History (dedupLast, admittedCoverage, toProfile)
import Lara.Process.Source
import Lara.Process.Source.Diagnostic (SourceRejection)
import qualified Lara.Process.Source.Provenance as Provenance
import Lara.Process.Source.Types
import Lara.Process.Types

data Snapshot = Snapshot Completion SourceInput (Either SourceRejection AcceptedObservation) [A.ArgId]
snapshotCompletion :: Snapshot -> Completion
snapshotCompletion (Snapshot completion _ _ _) = completion
snapshotInput :: Snapshot -> SourceInput
snapshotInput (Snapshot _ input _ _) = input
snapshotOutcome :: Snapshot -> Either SourceRejection AcceptedObservation
snapshotOutcome (Snapshot _ _ outcome _) = outcome
snapshotNames :: Snapshot -> [A.ArgId]
snapshotNames (Snapshot _ _ _ names) = names

takeSnapshot :: FamilySpec -> Completion -> Snapshot
takeSnapshot family completion = Snapshot completion input outcome names
  where
    input = Family.materialize family completion
    outcome = checkSource input
    names = either (const []) observationNames outcome

data ModelContext = ModelContext Audit.AuditMetadata [A.ArgId] Bool [(WitnessId,Natural)] (Map.Map A.ArgId Int)
contextMetadata :: ModelContext -> Audit.AuditMetadata
contextMetadata (ModelContext metadata _ _ _ _) = metadata
contextBase :: ModelContext -> SourceInput
contextBase = Audit.metadataBase . contextMetadata
contextConfig :: ModelContext -> AuditConfig
contextConfig = Audit.metadataConfig . contextMetadata
contextCarrier :: ModelContext -> [A.ArgId]
contextCarrier (ModelContext _ carrier _ _ _) = carrier
contextPositions :: ModelContext -> Map.Map A.ArgId Int
contextPositions (ModelContext _ _ _ _ positions) = positions
contextCarrierCount :: ModelContext -> Natural
contextCarrierCount = fromIntegral . Map.size . contextPositions
contextValid :: ModelContext -> Bool
contextValid (ModelContext _ _ valid _ _) = valid
contextWitnessCoordinates :: ModelContext -> [(WitnessId,Natural)]
contextWitnessCoordinates (ModelContext _ _ _ coordinates _) = coordinates

modelContext :: FamilySpec -> AuditConfig -> [Snapshot] -> ModelContext
modelContext family config snapshots = ModelContext metadata carrier valid coordinates positions
  where
    metadata = Audit.auditMetadata (familyBase family) config
    carrier = dedupLast (concatMap snapshotNames snapshots ++ map (artifactArgument . witnessArtifact) (auditWitnesses config))
    valid = Audit.metadataWellFormed metadata && Family.fixedClaims family config
    positions = Map.fromList (zip carrier [0..])
    coordinates = [(witnessId spec,maybe (fromIntegral (Map.size positions)) fromIntegral
      (Map.lookup (artifactArgument (witnessArtifact spec)) positions)) | spec <- auditWitnesses config]

data Prepared = Prepared G.AF (Either ProvenanceError Provenance.ProvenanceTable) [NodeGrade] Bool
  [(WitnessId,Either WitnessFault WitnessFields)] [(WitnessId,Either WitnessFault Audit.WitnessCertificate)] [QueryFields] (Map.Map Natural EvidenceKind)
preparedGraph :: Prepared -> G.AF
preparedGraph (Prepared graph _ _ _ _ _ _ _) = graph
preparedProvenance :: Prepared -> Either ProvenanceError Provenance.ProvenanceTable
preparedProvenance (Prepared _ provenance _ _ _ _ _ _) = provenance
preparedGrades :: Prepared -> [NodeGrade]
preparedGrades (Prepared _ _ grades _ _ _ _ _) = grades
preparedComplete :: Prepared -> Bool
preparedComplete (Prepared _ _ _ complete _ _ _ _) = complete
preparedWitnesses :: Prepared -> [(WitnessId,Either WitnessFault WitnessFields)]
preparedWitnesses (Prepared _ _ _ _ witnesses _ _ _) = witnesses
preparedWitnessCertificates :: Prepared -> [(WitnessId,Either WitnessFault Audit.WitnessCertificate)]
preparedWitnessCertificates (Prepared _ _ _ _ _ certificates _ _) = certificates
preparedQueries :: Prepared -> [QueryFields]
preparedQueries (Prepared _ _ _ _ _ _ queries _) = queries
preparedNativeKinds :: Prepared -> Map.Map Natural EvidenceKind
preparedNativeKinds (Prepared _ _ _ _ _ _ _ kinds) = kinds

prepare :: ModelContext -> Snapshot -> Either SourceRejection Prepared
prepare context snapshot = do
  observation <- snapshotOutcome snapshot
  let names = snapshotNames snapshot
      positions = contextPositions context
      nodePositions = mapMaybe (`Map.lookup` positions) names
      nameAt index = Map.lookup index sourceNames
      sourceNames = Map.fromDistinctAscList (zip [0..] names)
      edges = Set.fromList [(left,right) | (source,target) <- observationEdges observation,
        Just sourceName <- [nameAt source],Just targetName <- [nameAt target],
        Just left <- [Map.lookup sourceName positions],Just right <- [Map.lookup targetName positions]]
      graph = G.AF nodePositions (\source target -> Set.member (source,target) edges)
      provenance = Provenance.buildProvenance observation
      kinds = fmap (\table -> Provenance.buildKindTable (contextBase context) table
        (completionHistory (snapshotCompletion snapshot)) (auditKinds config) (auditAssumptions config)
        (Audit.metadataAdmittedBases (contextMetadata context)) (Family.hypotheticalKeys (snapshotCompletion snapshot))
        (Audit.metadataConditionalKeys (contextMetadata context))) provenance
      grade index name = case (provenance,kinds) of
        (Right table,Right kindTable) ->
          let keys = Provenance.checkedKeys table index
              value = either (const (Hypothetical,False)) (Provenance.meetKinds . map (Provenance.lookupKind kindTable)) keys
          in NodeGrade name keys value
        (Left fault,_) -> NodeGrade name (Left fault) (Hypothetical,False)
        (_,Left fault) -> NodeGrade name (Left fault) (Hypothetical,False)
      grades = zipWith grade [0..] names
      nativeKinds = Map.fromList [(fromIntegral position,fst (gradeValue entry)) |
        entry <- grades,Just position <- [Map.lookup (gradeArgument entry) positions]]
      complete = contextValid context && isRight provenance && all (snd . gradeValue) grades
      certificates = Audit.checkWitnesses (contextMetadata context) observation (completionHistory (snapshotCompletion snapshot))
      witnesses = [(ident,Audit.witnessCertificateFields <$> certificate) | (ident,certificate) <- certificates]
      queries = [QueryFields (bindingClaim claim) (bindingQuery claim) (publicStatus observation (bindingQuery claim))
        (mapMaybe nameAt (observationSupport observation (bindingQuery claim))) | claim <- auditClaims config]
  pure (Prepared graph provenance grades complete witnesses certificates queries nativeKinds)
  where config = contextConfig context

data Row = Row ModelContext Snapshot (Either SourceRejection Prepared)
rowSnapshot :: Row -> Snapshot
rowSnapshot (Row _ snapshot _) = snapshot
rowView :: Row -> Either SourceRejection Prepared
rowView (Row _ _ view) = view
rowContext :: Row -> ModelContext
rowContext (Row context _ _) = context
rowWitness :: Row -> WitnessId -> Maybe WitnessFields
rowWitness row witness = case rowView row of
  Left _ -> Nothing
  Right view -> case lookup witness (preparedWitnesses view) of
    Just (Right fields) -> Just fields
    _ -> Nothing
rowArgument :: Row -> WitnessId -> Natural
rowArgument row witness = maybe (contextCarrierCount context) id (lookup witness (contextWitnessCoordinates context))
  where context = rowContext row
rowKind :: Row -> Natural -> EvidenceKind
rowKind row argument = case rowView row of
  Right view -> Map.findWithDefault Hypothetical argument (preparedNativeKinds view)
  Left _ -> Hypothetical
rowArtifact :: Row -> WitnessId -> Bool
rowArtifact row witness = case rowView row of
  Left _ -> False
  Right view -> preparedComplete view && maybe False (const True) (rowWitness row witness)
rowConcludes :: Row -> WitnessId -> ClaimId -> Bool
rowConcludes row witness claim = case rowWitness row witness of
  Nothing -> False
  Just fields -> fieldsClaim fields == claim && any (\spec -> witnessId spec == witness &&
    artifactArgument (witnessArtifact spec) == fieldsArgument fields) (auditWitnesses (contextConfig (rowContext row)))

data CheckedFamily = CheckedFamily FamilySpec AuditConfig EnumeratedFamily [Snapshot] ModelContext [Row]
checkedSpec :: CheckedFamily -> FamilySpec
checkedSpec (CheckedFamily family _ _ _ _ _) = family
checkedConfig :: CheckedFamily -> AuditConfig
checkedConfig (CheckedFamily _ config _ _ _ _) = config
checkedEnumeration :: CheckedFamily -> EnumeratedFamily
checkedEnumeration (CheckedFamily _ _ enumeration _ _ _) = enumeration
checkedSnapshots :: CheckedFamily -> [Snapshot]
checkedSnapshots (CheckedFamily _ _ _ snapshots _ _) = snapshots
checkedContext :: CheckedFamily -> ModelContext
checkedContext (CheckedFamily _ _ _ _ context _) = context
checkedRows :: CheckedFamily -> [Row]
checkedRows (CheckedFamily _ _ _ _ _ rows) = rows
checkFamily :: AuditConfig -> EnumeratedFamily -> CheckedFamily
checkFamily config enumerated = CheckedFamily family config enumerated snapshots context rows
  where
    family = enumeratedSpec enumerated
    snapshots = map (takeSnapshot family) (enumeratedCompletions enumerated)
    context = modelContext family config snapshots
    rows = [Row context snapshot (prepare context snapshot) | snapshot <- snapshots]
rowAt :: CheckedFamily -> Completion -> Maybe Row
rowAt checked completion = find ((== completion) . snapshotCompletion . rowSnapshot) (checkedRows checked)
snapshotAt :: CheckedFamily -> Completion -> Maybe Snapshot
snapshotAt checked completion = find ((== completion) . snapshotCompletion) (checkedSnapshots checked)

warranted :: Row -> ProfileSpec -> ClaimId -> WitnessId -> Bool
warranted row specification claim witness = case (rowView row,rowWitness row witness) of
  (Right view,Just fields) -> preparedComplete view && rowConcludes row witness claim
    && admissibleEvidence profile (rowKind row coordinate)
    && all (\probe -> not (requiredProbe profile probe) || probe `elem` fieldsProbed fields) [minBound..maxBound]
    && fst (fieldsAchieved fields) == fst (guaranteeLevel profile)
    && snd (fieldsAchieved fields) <= snd (guaranteeLevel profile)
    && case find ((== coordinate) . fromIntegral) (G.afArgs graph) of
      Nothing -> False
      Just argument -> G.labelC graph argument == A.LIn
    where
      graph = (preparedGraph view){G.afArgs = filter (admissibleEvidence profile . rowKind row . fromIntegral) (G.afArgs (preparedGraph view))}
  _ -> False
  where
    coordinate = rowArgument row witness
    profile = toProfile specification

auditRows :: Problem -> [Row] -> ProfileSpec -> ClaimId -> WitnessId -> Bool
auditRows problem rows specification claim witness = all (acceptsCoverage profile) (admittedCoverage problem)
  && not (null rows) && all (\row -> warranted row specification claim witness) rows
  where profile = toProfile specification

audit :: CheckedFamily -> ProfileSpec -> ClaimId -> WitnessId -> Bool
audit checked = auditRows (familyProblem (checkedSpec checked)) (checkedRows checked)

