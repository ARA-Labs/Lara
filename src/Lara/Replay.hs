module Lara.Replay
  ( CoreVersion (..)
  , ReplayId
  , replayCore
  , replayPolicy
  , replayBackends
  , replayTheories
  , replayArtifact
  , CheckInput
  , inputReplayId
  , inputUnit
  , ReplayError (..)
  , ReplayFailure (..)
  , mkReplayId
  , mkCheckInput
  , sourceCheckInput
  , runtimeReplayFailure
  , replayFailureMessage
  , replayErrorMessage
  ) where

import Data.Char (ord)
import Data.List (find, sortBy)

import Lara.AST
import qualified Lara.Strict as Strict
import qualified Lara.Strict.ND as ND

data CoreVersion = LaraCoreV01
  deriving (Eq, Show)

data ReplayId = ReplayId
  { replayCore :: CoreVersion
  , replayPolicy :: PolicyId
  , replayBackends :: [(BackendId, String)]
  , replayTheories :: [TheoryDigest]
  , replayArtifact :: Digest
  }
  deriving (Eq, Show)

data CheckInput = CheckInput
  { inputReplayId :: ReplayId
  , inputUnit :: Unit
  }
  deriving (Eq, Show)

data ReplayError
  = NonCanonicalTheoryDigests [TheoryDigest]
  | DuplicateUnitTheory TheoryDigest
  | TheoryIdentityMismatch [TheoryDigest] [TheoryDigest]
  | ReplayPolicyMismatch PolicyId PolicyId
  deriving (Eq, Show)

data ReplayFailure
  = DuplicateSelectedBackend BackendId String
  | UnknownSelectedBackend BackendId String
  | CertificateBackendNotSelected Int ArgId BackendId Int
  deriving (Eq, Show)

mkReplayId
  :: CoreVersion
  -> PolicyId
  -> [(BackendId, String)]
  -> [TheoryDigest]
  -> Digest
  -> Either ReplayError ReplayId
mkReplayId core policy backends theories artifact
  | canonicalTheories theories =
      Right
        ReplayId
          { replayCore = core
          , replayPolicy = policy
          , replayBackends = backends
          , replayTheories = theories
          , replayArtifact = artifact
          }
  | otherwise = Left (NonCanonicalTheoryDigests theories)

mkCheckInput :: ReplayId -> Unit -> Either ReplayError CheckInput
mkCheckInput replayId unit =
  case firstDuplicate theoryKeys of
    Just duplicate -> Left (DuplicateUnitTheory duplicate)
    Nothing
      | canonicalUnitTheories /= replayTheories replayId ->
          Left (TheoryIdentityMismatch (replayTheories replayId) canonicalUnitTheories)
      | otherwise -> Right (CheckInput replayId unit)
  where
    theoryKeys = map fst (unitTheories unit)
    canonicalUnitTheories = sortBy compareTheoryDigest theoryKeys

sourceCheckInput :: Program -> Policy -> Unit -> Either ReplayError CheckInput
sourceCheckInput program policy unit
  | programPolicy program /= policyId policy =
      Left (ReplayPolicyMismatch (programPolicy program) (policyId policy))
  | otherwise = do
      replayId <-
        mkReplayId
          LaraCoreV01
          (policyId policy)
          (programBackends program)
          (sortBy compareTheoryDigest (map fst (policyTheories policy)))
          (programDigest program)
      mkCheckInput replayId unit

runtimeReplayFailure :: CheckInput -> Maybe ReplayFailure
runtimeReplayFailure input =
  case firstDuplicate selectedBackends of
    Just (backend, version) -> Just (DuplicateSelectedBackend backend version)
    Nothing ->
      case find (/= supportedBackend) selectedBackends of
        Just (backend, version) -> Just (UnknownSelectedBackend backend version)
        Nothing -> firstUnselectedCertificate selectedBackends (unitArgs (inputUnit input))
  where
    selectedBackends = replayBackends (inputReplayId input)

-- | One @stderr@ line explaining a replay-preflight rejection (the same
-- preflight 'runtimeReplayFailure' runs; the wire verdict carries only the
-- R13 class). Both drivers print this exact template so their diagnostics are
-- comparable.
replayFailureMessage :: ReplayFailure -> String
replayFailureMessage failure = case failure of
  DuplicateSelectedBackend (BackendId backend) version ->
    "replay preflight: duplicate selected backend " ++ backend ++ "@" ++ version
  UnknownSelectedBackend (BackendId backend) version ->
    "replay preflight: unknown selected backend " ++ backend ++ "@" ++ version
  CertificateBackendNotSelected index (ArgId argumentId) (BackendId backend) version ->
    "replay preflight: certificate backend not selected: argument "
      ++ argumentId
      ++ " (index "
      ++ show index
      ++ ") uses "
      ++ backend
      ++ "@"
      ++ show version

replayErrorMessage :: ReplayError -> String
replayErrorMessage replayError = case replayError of
  NonCanonicalTheoryDigests theories ->
    "replay theory digests are not in strictly increasing Unicode-scalar order: " ++ show theories
  DuplicateUnitTheory theory ->
    "checker Unit contains duplicate theory digest: " ++ show theory
  TheoryIdentityMismatch expected actual ->
    "checker Unit theory identity does not match replay identity: expected "
      ++ show expected
      ++ ", got "
      ++ show actual
  ReplayPolicyMismatch expected actual ->
    "program policy does not match supplied policy: expected "
      ++ show expected
      ++ ", got "
      ++ show actual

compareCodePointString :: String -> String -> Ordering
compareCodePointString a b = compare (map ord a) (map ord b)

compareTheoryDigest :: TheoryDigest -> TheoryDigest -> Ordering
compareTheoryDigest (TheoryDigest a) (TheoryDigest b) = compareCodePointString a b

canonicalTheories :: [TheoryDigest] -> Bool
canonicalTheories theories =
  and (zipWith (\a b -> compareTheoryDigest a b == LT) theories (drop 1 theories))

firstDuplicate :: Eq a => [a] -> Maybe a
firstDuplicate = go []
  where
    go _ [] = Nothing
    go seen (item : rest)
      | item `elem` seen = Just item
      | otherwise = go (item : seen) rest

supportedBackend :: (BackendId, String)
supportedBackend =
  ( BackendId (Strict.backendName ND.ndBackendId)
  , show (Strict.backendVersion ND.ndBackendId)
  )

firstUnselectedCertificate
  :: [(BackendId, String)]
  -> [(ArgId, SupportTerm)]
  -> Maybe ReplayFailure
firstUnselectedCertificate selected =
  firstJust . zipWith visitArgument [0 ..]
  where
    visitArgument index (argumentId, term) = visitTerm index argumentId term

    visitTerm _ _ (SLeaf _) = Nothing
    visitTerm index argumentId (SRule _ _ premises discharges _ assurance) =
      firstJust
        ( visitAssurance index argumentId assurance
            : map (visitTerm index argumentId) premises
              ++ map (visitTerm index argumentId . snd) discharges
        )

    visitAssurance _ _ AssuranceNone = Nothing
    visitAssurance _ _ AssuranceTrusted = Nothing
    visitAssurance index argumentId (AssuranceCert certificate)
      | certificatePair certificate `elem` selected = Nothing
      | otherwise =
          Just
            ( CertificateBackendNotSelected
                index
                argumentId
                (certBackend certificate)
                (certVersion certificate)
            )

    certificatePair certificate =
      (certBackend certificate, show (certVersion certificate))

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (Just value : _) = Just value
firstJust (Nothing : rest) = firstJust rest
