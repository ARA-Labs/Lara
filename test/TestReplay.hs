module TestReplay
  ( testReplayId
  , testCheckInput
  ) where

import Lara.AST
import Lara.Replay

testReplayId :: Unit -> ReplayId
testReplayId = inputReplayId . testCheckInput

testCheckInput :: Unit -> CheckInput
testCheckInput unit =
  case sourceCheckInput program policy unit of
    Right input -> input
    Left err -> error ("invalid conformance replay fixture: " ++ replayErrorMessage err)
  where
    program =
      Program
        { programArtifact = "conformance-corpus"
        , programDigest = Digest "sha256:conformance-corpus-v1"
        , programPolicy = PolicyId "conformance-v1"
        , programBackends = [(BackendId "nd", "1")]
        , programDecls = []
        }
    policy =
      Policy
        { policyId = PolicyId "conformance-v1"
        , policyRules = []
        , policyContraries = []
        , policyExceptions = []
        , policyAdmission = []
        , policyTheories = unitTheories unit
        , policyGroupMode = QuarantineOnConflict
        }
