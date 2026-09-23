-- | Prepare, validate, or summarize a blinded binding-audit packet.
--
-- > argv -> load fixed corpus records -> prepare: detached three-file write
-- >                                \-> validate: status-free read-only checks
-- >                                \-> summarize: validate + identify + atomically write
--
-- Every mode shares the fixed manifest and policy and normalizes failures only
-- at this CLI boundary.
module Main (main) where

import Control.Exception
  ( IOException
  , SomeException
  , displayException
  , fromException
  , try
  )
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStr, stderr)
import System.IO.Error (ioeGetErrorString, isUserError)

import Lara.BindingAudit
  ( prepareAuditPacket
  , summarizeAuditFiles
  , validateAuditPacket
  )
import Lara.ClaimSupport.Load (loadRecords)

manifestPath :: FilePath
manifestPath = "corpus-units/MANIFEST.tsv"

policyPath :: FilePath
policyPath = "corpus-units/corpus-v1.policy.lara"

usage :: String
usage =
  unlines
    [ "binding-audit.hs prepare <output-dir>"
    , "binding-audit.hs validate <packet-dir>"
    , "binding-audit.hs summarize"
    ]

main :: IO ()
main = do
  arguments <- getArgs
  case arguments of
    ["prepare", outputDirectory] ->
      runMode $ do
        records <- loadRecords manifestPath policyPath
        prepareAuditPacket outputDirectory records
    ["validate", packetDirectory] ->
      runMode $ do
        records <- loadRecords manifestPath policyPath
        validateAuditPacket packetDirectory records
    ["summarize"] ->
      runMode $ do
        records <- loadRecords manifestPath policyPath
        summarizeAuditFiles records
    _ -> die usage

runMode :: IO () -> IO ()
runMode action = do
  result <- try action
  case result of
    Left exception -> die (exceptionMessage exception)
    Right () -> pure ()

exceptionMessage :: SomeException -> String
exceptionMessage exception =
  case fromException exception of
    Just ioException
      | isUserError ioException -> ioeGetErrorString ioException
      | otherwise -> displayException ioException
    Nothing -> displayException exception

die :: String -> IO a
die message = do
  hPutStr stderr ("binding-audit: " ++ ensureFinalLf message)
  exitFailure

ensureFinalLf :: String -> String
ensureFinalLf message
  | null message = "\n"
  | last message == '\n' = message
  | otherwise = message ++ "\n"
