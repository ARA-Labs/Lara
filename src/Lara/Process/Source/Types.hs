module Lara.Process.Source.Types
  ( CoreVersion (..), BackendVersion (..), BackendIdentity (..), ReplayIdentity (..)
  , ObjectPath (..), ObjectMeta (..), EvidenceCapture (..), EvidenceJudgment (..)
  , SourceHole (..), SourceHoleObligation (..)
  , EvidenceStage (..), EvidenceError (..)
  , CertificatePayload (..), CertificateStep (..), CertificateCoordinate (..)
  , SourceInput, sourceProgram, sourcePolicy, sourceReplay, sourceCapture, sourceCertificatePayloads
  , Fragment, fragmentDecls, fragmentCertificatePayloads
  , mkSourceInput, mkSourceInputWithPayloads, mkFragment, mkFragmentWithPayloads
  , appendFragment, replaceSourceProgram, certificatePayloadCore, coreCertificatePayload
  , inquiryCorePolicy
  ) where

import Control.Monad (unless)
import Numeric.Natural (Natural)
import Lara.AST
import Lara.Evidence.Types (ObjectId, ExtractionRequest)
import Lara.Evidence.Registry (TypedObject)
import Lara.Prop (Prop)
import Lara.Strict (SExpr (..))
import Lara.Process.Source.CoreDiagnostic (CorePosition)

newtype CoreVersion = CoreVersion String deriving (Eq, Ord, Show)
newtype BackendVersion = BackendVersion String deriving (Eq, Ord, Show)
data BackendIdentity = BackendIdentity BackendId BackendVersion deriving (Eq, Ord, Show)
data ReplayIdentity = ReplayIdentity
  { replayCore :: CoreVersion, replayPolicy :: PolicyId, replayBackends :: [BackendIdentity]
  , replayTheories :: [TheoryDigest], replayArtifact :: Digest
  } deriving (Eq, Show)
newtype ObjectPath = ObjectPath String deriving (Eq, Ord, Show)
data ObjectMeta = ObjectMeta
  { objectId :: ObjectId, objectPath :: ObjectPath, objectLength :: Natural, objectDigest :: Digest
  } deriving (Eq, Ord, Show)
data EvidenceCapture = EvidenceCapture
  { captureSnapshot :: [(ObjectId, Either String (ObjectMeta, TypedObject))]
  , captureManifest :: [ObjectMeta]
  } deriving (Eq, Show)

-- Opaque backend payloads alone retain authored string/integer constructor
-- distinctions. No presentation node is a semantic runtime value.
data CertificatePayload
  = CertificateString String | CertificateInteger Integer | CertificateNode String [CertificatePayload]
  deriving (Eq, Show)
data CertificateStep = CertificatePremise Natural | CertificateDischarge Natural deriving (Eq, Ord, Show)
data CertificateCoordinate = DeclarationCertificate Natural [CertificateStep] deriving (Eq, Ord, Show)

-- Positional opaque carriers prevent independent updates of AST and payloads.
data SourceInput = SourceInput Program Policy ReplayIdentity (Maybe EvidenceCapture)
  [(CertificateCoordinate,CertificatePayload)] deriving (Eq, Show)
sourceProgram :: SourceInput -> Program
sourceProgram (SourceInput p _ _ _ _) = p
sourcePolicy :: SourceInput -> Policy
sourcePolicy (SourceInput _ p _ _ _) = p
sourceReplay :: SourceInput -> ReplayIdentity
sourceReplay (SourceInput _ _ r _ _) = r
sourceCapture :: SourceInput -> Maybe EvidenceCapture
sourceCapture (SourceInput _ _ _ c _) = c
sourceCertificatePayloads :: SourceInput -> [(CertificateCoordinate,CertificatePayload)]
sourceCertificatePayloads (SourceInput _ _ _ _ ps) = ps

data Fragment = Fragment [Decl] [(CertificateCoordinate,CertificatePayload)] deriving (Eq, Show)
fragmentDecls :: Fragment -> [Decl]
fragmentDecls (Fragment ds _) = ds
fragmentCertificatePayloads :: Fragment -> [(CertificateCoordinate,CertificatePayload)]
fragmentCertificatePayloads (Fragment _ ps) = ps

certificatePayloadCore :: CertificatePayload -> SExpr
certificatePayloadCore (CertificateString s) = SAtom s
certificatePayloadCore (CertificateInteger n) = SAtom (show n)
certificatePayloadCore (CertificateNode tag children) = SList (SAtom tag : map certificatePayloadCore children)
coreCertificatePayload :: SExpr -> Either String CertificatePayload
coreCertificatePayload (SAtom s) = Right (CertificateString s)
coreCertificatePayload (SList (SAtom tag : children)) = CertificateNode tag <$> traverse coreCertificatePayload children
coreCertificatePayload _ = Left "opaque payload is outside the presentation constructor domain"

certificates :: [Decl] -> [(CertificateCoordinate,SExpr)]
certificates ds = concat [argument index arg | (index,DeclArg arg) <- zip [0..] ds]
  where
    argument index arg = case argInstantiation arg of
      ExplicitTheta term -> termPayloads index [] term
      InferTheta _ _ _ _ assurance -> assurancePayload index [] assurance
    termPayloads _ _ SLeaf{} = []
    termPayloads index path (SRule _ _ ps ds' _ assurance) =
      assurancePayload index path assurance
      ++ concat [termPayloads index (path ++ [CertificatePremise n]) term | (n,term) <- zip [0..] ps]
      ++ concat [termPayloads index (path ++ [CertificateDischarge n]) term | (n,(_,term)) <- zip [0..] ds']
    assurancePayload index path (AssuranceCert cert) = [(DeclarationCertificate index path,certPayload cert)]
    assurancePayload _ _ _ = []

validatePayloads :: [Decl] -> [(CertificateCoordinate,CertificatePayload)] -> Either String ()
validatePayloads ds payloads = unless
  ([(coordinate,certificatePayloadCore payload) | (coordinate,payload) <- payloads] == certificates ds)
  (Left "certificate presentation coordinates do not match the declared payloads")
defaultPayloads :: [Decl] -> Either String [(CertificateCoordinate,CertificatePayload)]
defaultPayloads = traverse (\(coordinate,core) -> (coordinate,) <$> coreCertificatePayload core) . certificates

mkSourceInput :: Program -> Policy -> ReplayIdentity -> Maybe EvidenceCapture -> Either String SourceInput
mkSourceInput p policy replay capture = do
  payloads <- defaultPayloads (programDecls p)
  pure (SourceInput p policy replay capture payloads)
mkSourceInputWithPayloads :: Program -> Policy -> ReplayIdentity -> Maybe EvidenceCapture -> [(CertificateCoordinate,CertificatePayload)] -> Either String SourceInput
mkSourceInputWithPayloads p policy replay capture payloads = do
  validatePayloads (programDecls p) payloads
  pure (SourceInput p policy replay capture payloads)
mkFragment :: [Decl] -> Either String Fragment
mkFragment ds = Fragment ds <$> defaultPayloads ds
mkFragmentWithPayloads :: [Decl] -> [(CertificateCoordinate,CertificatePayload)] -> Either String Fragment
mkFragmentWithPayloads ds payloads = do
  validatePayloads ds payloads
  pure (Fragment ds payloads)
appendFragment :: SourceInput -> Fragment -> SourceInput
appendFragment (SourceInput program policy replay capture payloads) (Fragment ds extra) =
  SourceInput program{programDecls = programDecls program ++ ds} policy replay capture
    (payloads ++ [(DeclarationCertificate (index + offset) path,payload) | (DeclarationCertificate index path,payload) <- extra])
  where offset = fromIntegral (length (programDecls program))
replaceSourceProgram :: SourceInput -> Program -> Either String SourceInput
replaceSourceProgram (SourceInput _ policy replay capture old) program = do
  payloads <- traverse keep (certificates (programDecls program))
  pure (SourceInput program policy replay capture payloads)
  where
    keep (coordinate,core) = case lookup coordinate old of
      Just payload | certificatePayloadCore payload == core -> Right (coordinate,payload)
      _ -> (coordinate,) <$> coreCertificatePayload core

data EvidenceJudgment = EvidenceJudgment
  { evidenceLeaf :: LeafId, evidenceRequest :: ExtractionRequest, evidenceProp :: Prop
  , evidenceDependencies :: [ObjectMeta]
  } deriving (Eq, Show)
data EvidenceStage = EvidenceBindingStage | EvidenceCaptureStage | EvidenceExtractionStage
  deriving (Eq, Ord, Show, Enum, Bounded)
data EvidenceError = EvidenceError EvidenceStage LeafId (Maybe ObjectId) String
  deriving (Eq, Show)

data SourceHole = SourceHole
  { holeIndex :: Natural, holeArgument :: ArgId
  , holeObligations :: [SourceHoleObligation], holeAttacks :: [Natural]
  } deriving (Eq, Show)
data SourceHoleObligation = SourceHoleObligation
  { holeQuestion :: QuestionId, holeSites :: [CorePosition]
  } deriving (Eq, Show)

inquiryCorePolicy :: Policy -> Policy
inquiryCorePolicy policy = policy{policyRules = map rule (policyRules policy)}
  where
    rule scheme = scheme{ruleCertifiers =
      [certifier{certRefVersion = max 0 (certRefVersion certifier)} | certifier <- ruleCertifiers scheme]}
