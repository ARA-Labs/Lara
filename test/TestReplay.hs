module TestReplay
  ( testReplayId
  , testCheckInput
  ) where

import Lara.AST
import Lara.Replay
import Data.List (sort)

testReplayId :: Unit -> ReplayId
testReplayId = inputReplayId . testCheckInput

testCheckInput :: Unit -> CheckInput
testCheckInput unit =
  case build of
    Right input -> input
    Left err -> error ("invalid conformance replay fixture: " ++ replayErrorMessage err)
  where
    build = do
      replayId <-
        mkReplayId
          LaraCoreV02
          (PolicyId "conformance-v1")
          [(BackendId "nd", "1")]
          (sort (map fst (unitTheories unit)))
          (Digest "sha256:conformance-corpus-v1")
      mkCheckInput replayId unit
