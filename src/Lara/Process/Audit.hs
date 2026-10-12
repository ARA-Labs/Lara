module Lara.Process.Audit
  ( ResolvedSupport, resolveSupport, resolvedObservation, resolvedRawIndex, resolvedRow
  , resolvedConclusion, resolvedQuery, resolvedCheckedIndex, associateSource
  , CheckedArtifact, checkArtifact, artifactSelected, artifactResolvedDependencies, artifactMethodResult
  , BoundMethod, boundMethodBinding, boundMethodApplication
  , LedgerCertificate, checkLedger, warrantedLevel, ledgerCertificateCount, ledgerCertificateLevel
  , GuaranteeCertificate, checkGuarantee, guaranteeCertificateAttained
  , WitnessCertificate, checkWitness, witnessCertificateFields, witnessCertificateArtifact
  , AuditMetadata, auditMetadata, metadataBase, metadataConfig, metadataWellFormed, metadataAdmittedBases, metadataConditionalKeys
  , observeWitness, observeWitnesses, checkWitnesses, configWellFormed, admittedBases, conditionalKeys
  , claimFormal, supportsClaim
  ) where

import Control.Monad (unless)
import Data.List (find)
import Numeric.Natural (Natural)
import qualified Lara.AST as A
import Lara.Blocked (pruneChecked)
import Lara.Check (cuNodes)
import Lara.Driver.Internal (buildGamma, buildCertOk)
import Lara.Elaborate (acceptedSourceDeclared, acceptedSourceChecked, acceptedSourcePrune, acceptedSourceSemantic)
import qualified Lara.Grounded as G
import Lara.Policy (lookupRule)
import Lara.Prop (Prop, equiv)
import Lara.SupportTerm (inferSupport, CheckLoc (LocRoot), srConclusion, srObligations, cnTerm, cnConclusion)
import Lara.Process.Audit.Types
import qualified Lara.Process.CheckedMethods as Methods
import Lara.Process.History (familyCount)
import Lara.Process.Source
import Lara.Process.Source.CoreDiagnostic (coreCheckFault)
import Lara.Process.Source.Types
import Lara.Process.Types

-- The opaque reference owns its accepted source; a fresh compact node index
-- cannot be transplanted to a different source or mistaken for a raw occurrence.
data ResolvedSupport = ResolvedSupport AcceptedObservation Natural (A.ArgId,A.SupportTerm) Prop Prop Natural
resolvedObservation :: ResolvedSupport -> AcceptedObservation
resolvedObservation (ResolvedSupport observation _ _ _ _ _) = observation
resolvedRawIndex :: ResolvedSupport -> Natural
resolvedRawIndex (ResolvedSupport _ index _ _ _ _) = index
resolvedRow :: ResolvedSupport -> (A.ArgId,A.SupportTerm)
resolvedRow (ResolvedSupport _ _ row _ _ _) = row
resolvedConclusion :: ResolvedSupport -> Prop
resolvedConclusion (ResolvedSupport _ _ _ conclusion _ _) = conclusion
resolvedQuery :: ResolvedSupport -> Prop
resolvedQuery (ResolvedSupport _ _ _ _ query _) = query
resolvedCheckedIndex :: ResolvedSupport -> Natural
resolvedCheckedIndex (ResolvedSupport _ _ _ _ _ index) = index

atNatural :: [a] -> Natural -> Maybe a
atNatural [] _ = Nothing
atNatural (value:_) 0 = Just value
atNatural (_:rest) index = atNatural rest (index-1)
firstIndex :: (a -> Bool) -> [a] -> Maybe Natural
firstIndex predicate = go 0
  where
    go _ [] = Nothing
    go index (value:rest) | predicate value = Just index
                          | otherwise = go (index+1) rest

resolveSupport :: AcceptedObservation -> SupportBinding -> Either SupportFault ResolvedSupport
resolveSupport observation binding = do
  rawIndex <- maybe (Left SupportAbsent) Right (firstIndex ((== supportArgument binding) . fst) (A.unitArgs declared))
  row <- maybe (Left SupportAbsent) Right (atNatural (A.unitArgs declared) rawIndex)
  inferred <- either (Left . SupportInference . coreCheckFault) Right
    (inferSupport (lookupRule (A.unitRules declared)) (buildGamma (A.unitLeaves declared))
      (buildCertOk (A.unitTheories declared)) LocRoot (snd row))
  unless (null (srObligations inferred)) (Left (SupportIncomplete (srObligations inferred)))
  unless (equiv (srConclusion inferred) (supportQuery binding)) (Left SupportDifferentConclusion)
  unless (row `elem` A.unitArgs retained) (Left SupportNotRetained)
  nodeIndex <- maybe (Left SupportAbsentNode) Right (firstIndex (== supportArgument binding) (observationNames observation))
  node <- maybe (Left SupportAbsentNode) Right (atNatural (cuNodes checked) nodeIndex)
  unless (cnTerm node == snd row && cnConclusion node == srConclusion inferred) (Left SupportNodeMismatch)
  unless (null (blockedClosure observation [supportQuery binding])) (Left SupportBlocked)
  pure (ResolvedSupport observation rawIndex row (srConclusion inferred) (supportQuery binding) nodeIndex)
  where
    accepted = observationAcceptedSource observation
    declared = acceptedSourceDeclared accepted
    checked = acceptedSourceChecked accepted
    retained = pruneChecked (acceptedSourcePrune accepted)

claimFormal :: A.Program -> A.PropId -> Maybe Prop
claimFormal program declaration = A.claimFormal <$> find ((== declaration) . A.claimId)
  [claim | A.DeclClaim claim <- A.programDecls program]
supportsClaim :: A.PropId -> A.ArgConcl -> Bool
supportsClaim declaration conclusion = case conclusion of
  A.SupportsClaim named -> named == declaration
  A.SupportsDerived named -> named == declaration
  A.Challenges _ -> False

associateSource :: ClaimBinding -> A.ArgId -> ResolvedSupport -> Either AssociationFault ()
associateSource claim argument selected = do
  unless (claimFormal (sourceProgram (observationInput observation)) declaration == Just query) (Left AssociationInputClaim)
  unless (claimFormal semantic declaration == Just query) (Left AssociationSemanticClaim)
  (authored,reconstructed) <- maybe (Left AssociationMissingDeclaration) Right (atNatural pairs (resolvedRawIndex selected))
  unless (A.argId authored == argument && reconstructed == resolvedRow selected && supportsClaim declaration (A.argConcl authored))
    (Left AssociationWrongArgument)
  unless (any (\(named,indices) -> named == declaration && resolvedRawIndex selected `elem` indices) alternatives)
    (Left AssociationNotAlternative)
  where
    observation = resolvedObservation selected
    accepted = observationAcceptedSource observation
    semantic = acceptedSourceSemantic accepted
    declaration = bindingDeclaration claim
    query = bindingQuery claim
    pairs = zip [arg | A.DeclArg arg <- A.programDecls semantic] (A.unitArgs (acceptedSourceDeclared accepted))
    alternatives = [(A.claimId declaredClaim,[index | (index,(arg,_)) <- zip [0..] pairs,
      supportsClaim (A.claimId declaredClaim) (A.argConcl arg)]) | A.DeclClaim declaredClaim <- A.programDecls semantic]

data BoundMethod = BoundMethod AcceptedObservation ClaimBinding MethodBinding ResolvedSupport [ResolvedSupport] (Maybe Methods.Application)
boundMethodBinding :: BoundMethod -> MethodBinding
boundMethodBinding (BoundMethod _ _ method _ _ _) = method
boundMethodApplication :: BoundMethod -> Maybe Methods.Application
boundMethodApplication (BoundMethod _ _ _ _ _ application) = application

-- Source-bound methods derive the canonical/request/evidence binding internally.
-- The original observation, authored association, and exact support references
-- are retained together, rather than accepting caller-supplied approval flags.
checkMethod :: AcceptedObservation -> ClaimBinding -> ResolvedSupport -> [ResolvedSupport] -> MethodBinding
  -> Either BridgeError BoundMethod
checkMethod observation claim selected dependencies method = do
  unless (resolvedQuery selected == bindingQuery claim) (Left IncompatibleClaim)
  either (const (Left FailedDerivation)) Right (Methods.checkDerivation (Methods.methodEvidence (bindingMethod method)))
  mapM_ checkSupport (selected:dependencies)
  application <- case bindingMode method of
    ConditionalPayload -> Right Nothing
    AppliedPayload -> case Methods.checkApplication (bindingMethod method)
        (Methods.methodRequest (bindingMethod method) (bindingParameter method) (bindingFirst method) (bindingSecond method)) of
      Left ApplicationFailedPrecondition -> Left FalsePrecondition
      Left fault -> Left (BridgeApplication fault)
      Right value -> Right (Just value)
  pure (BoundMethod observation claim method selected dependencies application)
  where
    accepted = observationAcceptedSource observation
    retained = A.unitArgs (pruneChecked (acceptedSourcePrune accepted))
    checked = acceptedSourceChecked accepted
    graph = observationAF observation
    checkSupport reference = do
      unless (resolvedRow reference `elem` retained) (Left MissingSupport)
      node <- maybe (Left MissingSupport) Right (atNatural (cuNodes checked) (resolvedCheckedIndex reference))
      unless (cnTerm node == snd (resolvedRow reference) && cnConclusion node == resolvedConclusion reference) (Left MissingSupport)
      unless (any ((== resolvedCheckedIndex reference) . fromIntegral) (G.afArgs graph)) (Left MissingSupport)
      unless (null (blockedClosure observation [resolvedQuery reference])) (Left BlockedSupport)
      unless (observationNodeLabel observation (resolvedCheckedIndex reference) == Just A.LIn) (Left DefeatedSupport)

data CheckedArtifact = CheckedArtifact ResolvedSupport [ResolvedSupport] (Maybe BoundMethod)
artifactSelected :: CheckedArtifact -> ResolvedSupport
artifactSelected (CheckedArtifact selected _ _) = selected
artifactResolvedDependencies :: CheckedArtifact -> [ResolvedSupport]
artifactResolvedDependencies (CheckedArtifact _ dependencies _) = dependencies
artifactMethodResult :: CheckedArtifact -> Maybe BoundMethod
artifactMethodResult (CheckedArtifact _ _ method) = method
checkArtifact :: AcceptedObservation -> ClaimBinding -> ArtifactSpec -> Either ArtifactFault CheckedArtifact
checkArtifact observation claim spec = do
  selected <- support (SupportBinding (artifactArgument spec) (bindingQuery claim))
  either (Left . ArtifactAssociation) Right (associateSource claim (artifactArgument spec) selected)
  dependencies <- traverse support (artifactDependencies spec)
  method <- case artifactInterpretation spec of
    DeclaredInterpretation _ -> Right Nothing
    CheckedMethod binding -> Just <$> either (Left . ArtifactMethod) Right (checkMethod observation claim selected dependencies binding)
  pure (CheckedArtifact selected dependencies method)
  where support binding = either (Left . ArtifactSupport (supportArgument binding)) Right (resolveSupport observation binding)

data LedgerCertificate = LedgerCertificate Natural Rational deriving (Eq, Show)
ledgerCertificateCount :: LedgerCertificate -> Natural
ledgerCertificateCount (LedgerCertificate count _) = count
ledgerCertificateLevel :: LedgerCertificate -> Rational
ledgerCertificateLevel (LedgerCertificate _ level) = level
warrantedLevel :: Ledger -> Maybe Rational
warrantedLevel metadata = case (ledgerKind metadata,ledgerValue metadata,ledgerCountBound metadata,ledgerGuarantee metadata) of
  (Just kind,Just value,Just bound,Just FWER) | value > 0 && bound > 0 ->
    Just (case kind of PValue -> fromIntegral bound * value; EValue -> fromIntegral bound / value)
  _ -> Nothing
checkLedger :: ProcessHistory -> LedgerBinding -> Either LedgerFault LedgerCertificate
checkLedger history binding = do
  unless (any exactRun events) (Left (if any sameRun events then FamilyMismatch else AbsentRun))
  unless (Result (ledgerRun binding) (ledgerOutcome binding) `elem` events) (Left AbsentResult)
  maybe (Left MissingKind) (const (Right ())) (ledgerKind metadata)
  maybe (Left MissingValue) (const (Right ())) (ledgerValue metadata)
  unless (ledgerGuarantee metadata == Just FWER)
    (Left (if ledgerGuarantee metadata == Nothing then MissingGuarantee else UnsupportedGuarantee))
  bound <- maybe (Left MissingBound) Right (ledgerCountBound metadata)
  unless (bound > 0) (Left ZeroBound)
  unless (count <= bound) (Left ExceededBound)
  level <- maybe (Left NonFiniteLevel) Right (warrantedLevel metadata)
  pure (LedgerCertificate count level)
  where
    events = map stampedEvent history
    metadata = ledger binding
    count = familyCount history (ledgerFamily binding)
    exactRun (Run run _ _ _ family) = run == ledgerRun binding && family == ledgerFamily binding
    exactRun _ = False
    sameRun (Run run _ _ _ _) = run == ledgerRun binding
    sameRun _ = False

data GuaranteeCertificate = GuaranteeCertificate GuaranteeBinding (GuaranteeClass,Rational) (Maybe LedgerCertificate) deriving (Eq, Show)
guaranteeCertificateAttained :: GuaranteeCertificate -> (GuaranteeClass,Rational)
guaranteeCertificateAttained (GuaranteeCertificate _ attained _) = attained
checkGuarantee :: ProcessHistory -> GuaranteeBinding -> Either GuaranteeFault GuaranteeCertificate
checkGuarantee _ binding@(ConditionalGuarantee kind level)
  | 0 <= level && level <= 1 = Right (GuaranteeCertificate binding (kind,level) Nothing)
  | otherwise = Left InvalidConditionalLevel
checkGuarantee history binding@(LedgerGuarantee metadata) = do
  certificate <- either (Left . GuaranteeLedger) Right (checkLedger history metadata)
  pure (GuaranteeCertificate binding (FWER,ledgerCertificateLevel certificate) (Just certificate))

data WitnessCertificate = WitnessCertificate WitnessSpec ClaimBinding CheckedArtifact GuaranteeCertificate
witnessCertificateArtifact :: WitnessCertificate -> CheckedArtifact
witnessCertificateArtifact (WitnessCertificate _ _ artifact _) = artifact
witnessCertificateFields :: WitnessCertificate -> WitnessFields
witnessCertificateFields (WitnessCertificate spec claim _ guarantee) =
  WitnessFields (bindingClaim claim) (artifactArgument (witnessArtifact spec)) (witnessProbed spec) (guaranteeCertificateAttained guarantee)
checkWitness :: SourceInput -> AcceptedObservation -> ProcessHistory -> ClaimBinding -> WitnessSpec -> Either WitnessFault WitnessCertificate
checkWitness base observation history claim spec = do
  unless (witnessSource spec == base) (Left StaleSource)
  unless (witnessClaim spec == bindingClaim claim) (Left WrongClaim)
  artifact <- either (Left . WitnessArtifact) Right (checkArtifact observation claim (witnessArtifact spec))
  guarantee <- either (Left . WitnessGuarantee) Right (checkGuarantee history (witnessGuarantee spec))
  pure (WitnessCertificate spec claim artifact guarantee)
observeWitness :: SourceInput -> AcceptedObservation -> ProcessHistory -> ClaimBinding -> WitnessSpec -> Either WitnessFault WitnessFields
observeWitness base observation history claim spec = witnessCertificateFields <$> checkWitness base observation history claim spec

configWellFormed :: AuditConfig -> Bool
configWellFormed config = distinct (map bindingClaim (auditClaims config))
  && distinct (map witnessId (auditWitnesses config))
  && distinct [(kindSource spec,kindKey spec) | spec <- auditKinds config]
  && distinct (map captureId (auditAssumptions config))
  where
    distinct [] = True
    distinct (value:rest) = value `notElem` rest && distinct rest
admittedBases :: AuditConfig -> [AdmissionBasis]
admittedBases = map captureBasis . auditAssumptions
conditionalKeys :: AuditConfig -> SourceInput -> [KindKey]
conditionalKeys config base = [ArgumentKey (artifactArgument (witnessArtifact spec)) |
  spec <- auditWitnesses config,witnessSource spec == base,conditional spec]
  where conditional spec = case witnessGuarantee spec of
          ConditionalGuarantee _ _ -> True
          LedgerGuarantee _ -> case artifactInterpretation (witnessArtifact spec) of
            CheckedMethod binding -> bindingMode binding == ConditionalPayload
            DeclaredInterpretation _ -> False
data AuditMetadata = AuditMetadata SourceInput AuditConfig Bool [AdmissionBasis] [KindKey]
auditMetadata :: SourceInput -> AuditConfig -> AuditMetadata
auditMetadata base config = AuditMetadata base config (configWellFormed config) (admittedBases config) (conditionalKeys config base)
metadataBase :: AuditMetadata -> SourceInput
metadataBase (AuditMetadata base _ _ _ _) = base
metadataConfig :: AuditMetadata -> AuditConfig
metadataConfig (AuditMetadata _ config _ _ _) = config
metadataWellFormed :: AuditMetadata -> Bool
metadataWellFormed (AuditMetadata _ _ valid _ _) = valid
metadataAdmittedBases :: AuditMetadata -> [AdmissionBasis]
metadataAdmittedBases (AuditMetadata _ _ _ bases _) = bases
metadataConditionalKeys :: AuditMetadata -> [KindKey]
metadataConditionalKeys (AuditMetadata _ _ _ _ keys) = keys

checkWitnesses :: AuditMetadata -> AcceptedObservation -> ProcessHistory -> [(WitnessId,Either WitnessFault WitnessCertificate)]
checkWitnesses metadata observation history = [(witnessId spec,observe spec) | spec <- auditWitnesses config]
  where
    config = metadataConfig metadata
    observe spec | not (metadataWellFormed metadata) = Left AmbiguousMetadata
                 | otherwise = case find ((== witnessClaim spec) . bindingClaim) (auditClaims config) of
                     Nothing -> Left MissingClaim
                     Just claim -> checkWitness (metadataBase metadata) observation history claim spec
observeWitnesses :: AuditConfig -> SourceInput -> AcceptedObservation -> ProcessHistory -> [(WitnessId,Either WitnessFault WitnessFields)]
observeWitnesses config base observation history =
  [(ident,witnessCertificateFields <$> certificate) | (ident,certificate) <- checkWitnesses (auditMetadata base config) observation history]
