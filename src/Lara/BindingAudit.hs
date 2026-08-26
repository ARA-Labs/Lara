module Lara.BindingAudit
  ( AuditCommandResult (..)
  , AuditIO (..)
  , productionAuditIO
  , validatePacketDestination
  , prepareAuditPacket
  , prepareAuditPacketWith
  , validateAuditPacket
  , validateAuditPacketWith
  , AuditClassification (..)
  , AuditFileRole (..)
  , LeafJudgment (..)
  , ObjectJudgment (..)
  , AuditCounts (..)
  , AuditSummary (..)
  , GitObjectFormat (..)
  , InputIdentity (..)
  , AuditError (..)
  , auditErrorMessage
  , decodeAuditUtf8
  , validateObjectDenominator
  , validateWorklist
  , renderLeafTemplate
  , renderObjectTemplate
  , parseLeafJudgments
  , parseObjectJudgments
  , validateLeafJudgments
  , validateObjectJudgments
  , summarizeAudit
  , renderAuditSummary
  , summarizeAuditFiles
  , summarizeAuditFilesWith
  , leafResultsPath
  , objectResultsPath
  , summaryPath
  ) where

import Control.Applicative ((<|>))
import Control.Exception
  ( IOException
  , SomeException
  , catch
  , displayException
  , evaluate
  , mask
  , onException
  , try
  )
import Control.Monad (unless, void, when)
import qualified Data.ByteString as BS
import Data.Char (isSpace)
import Data.List (dropWhileEnd, find, isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.Text.Encoding.Error (lenientDecode)
import System.Directory
  ( canonicalizePath
  , createDirectory
  , doesPathExist
  , removePathForcibly
  )
import System.FilePath
  ( (</>)
  , dropTrailingPathSeparator
  , normalise
  , splitDirectories
  , takeDirectory
  , takeFileName
  )
import System.Exit (ExitCode (..))
import System.IO (Handle, hClose)
import System.Process
  ( CreateProcess (..)
  , ProcessHandle
  , StdStream (CreatePipe)
  , createProcess
  , proc
  , terminateProcess
  , waitForProcess
  )

import Lara.AST (LeafId (..), LeafKind (..), SourceRef, Status (..))
import Lara.BindingAudit.Tsv
import Lara.BindingAudit.Types
import Lara.AtomicWrite (atomicWriteWith)
import Lara.ClaimSupport
  ( BindingAuditRow (..)
  , LeafFact (..)
  , UnitRecord (..)
  , bindingAuditPath
  , bindingAuditTsv
  , kindStr
  , statusStr
  )
import Lara.ExpectedJson (JValue (..), renderJson)

-- | Every effect needed by packet orchestration.  Named fields keep tests on
-- the real path and transaction logic while allowing deterministic read,
-- write, and filesystem failures without changing the process working
-- directory.
data AuditCommandResult = AuditCommandResult
  { auditCommandExitCode :: ExitCode
  , auditCommandStdout :: BS.ByteString
  , auditCommandStderr :: BS.ByteString
  }
  deriving (Eq, Show)

data AuditIO = AuditIO
  { readAuditBytes :: FilePath -> IO BS.ByteString
  , writeAuditBytes :: FilePath -> BS.ByteString -> IO ()
  , atomicWriteAuditBytes :: FilePath -> BS.ByteString -> IO ()
  , discoverObjectFormat :: IO AuditCommandResult
  , hashAuditBytes :: BS.ByteString -> IO AuditCommandResult
  , canonicalizeAuditPath :: FilePath -> IO FilePath
  , auditPathExists :: FilePath -> IO Bool
  , createAuditDirectory :: FilePath -> IO ()
  , removeAuditDirectory :: FilePath -> IO ()
  }

productionAuditIO :: AuditIO
productionAuditIO =
  AuditIO
    { readAuditBytes = BS.readFile
    , writeAuditBytes = BS.writeFile
    , atomicWriteAuditBytes = \destination bytes ->
        atomicWriteWith destination (\handle -> BS.hPut handle bytes)
    , discoverObjectFormat =
        runGitCommand ["rev-parse", "--show-object-format"] BS.empty
    , hashAuditBytes =
        runGitCommand ["hash-object", "--stdin"]
    , canonicalizeAuditPath = canonicalizePath
    , auditPathExists = doesPathExist
    , createAuditDirectory = createDirectory
    , removeAuditDirectory = removePathForcibly
    }

leafResultsPath :: FilePath
leafResultsPath = "measurements/binding-audit/results.tsv"

objectResultsPath :: FilePath
objectResultsPath = "measurements/binding-audit/object-results.tsv"

summaryPath :: FilePath
summaryPath = "measurements/binding-audit/summary.json"

-- | Reject destinations inside the committed audit store, resolving every
-- existing parent first so relative, absolute, @..@, and symlink spellings
-- share one component-wise containment decision.  Existing destinations are
-- rejected independently: detached human packets are never replaced.
validatePacketDestination :: AuditIO -> FilePath -> IO ()
validatePacketDestination auditIO destination = do
  let normalizedDestination = dropTrailingPathSeparator destination
      baseName = takeFileName normalizedDestination
  when (null baseName || baseName == "." || baseName == "..") $
    ioError (userError "packet destination must name a new directory")
  committedRoot <-
    canonicalizeAuditPath auditIO (takeDirectory bindingAuditPath)
  destinationParent <-
    canonicalizeAuditPath auditIO (takeDirectory normalizedDestination)
  let canonicalDestination = normalise (destinationParent </> baseName)
  when (isContainedBy committedRoot canonicalDestination) $
    ioError (userError "packet destination is inside committed binding-audit storage")
  exists <- auditPathExists auditIO normalizedDestination
  when exists $
    ioError (userError "packet destination already exists")

-- Packet mode/data-flow invariants:
--
-- @
-- prepare: records + committed worklist bytes
--              -> validate denominator -> render/UTF-8/force all outputs
--              -> create once -> write exactly {worklist,leaf,object}
-- validate: packet bytes + committed worklist bytes
--              -> strict UTF-8/TSV/order/generated-field checks -> ()
--              (never urStatuses, counts, verdicts, or writes)
-- @
prepareAuditPacket :: FilePath -> [UnitRecord] -> IO ()
prepareAuditPacket = prepareAuditPacketWith productionAuditIO

prepareAuditPacketWith :: AuditIO -> FilePath -> [UnitRecord] -> IO ()
prepareAuditPacketWith auditIO destination records = do
  _ <- either throwAuditError pure (validateObjectDenominator records)
  validatePacketDestination auditIO destination
  worklistBytes <- readAuditInput auditIO "committed worklist" bindingAuditPath
  _ <- either throwAuditError pure (validateWorklist records worklistBytes)
  objectDocument <- either throwAuditError pure (renderObjectTemplate records)
  let leafBytes = encodeAuditUtf8 (renderLeafTemplate records)
      objectBytes = encodeAuditUtf8 objectDocument
  _ <-
    evaluate
      ( BS.length worklistBytes
          + BS.length leafBytes
          + BS.length objectBytes
      )
  mask $ \restore -> do
    createAuditDirectory auditIO destination
    restore
      ( do
          writeAuditBytes auditIO (destination </> "worklist.tsv") worklistBytes
          writeAuditBytes auditIO (destination </> "results.tsv") leafBytes
          writeAuditBytes auditIO (destination </> "object-results.tsv") objectBytes
      )
      `onException` ignoreCleanup (removeAuditDirectory auditIO destination)

validateAuditPacket :: FilePath -> [UnitRecord] -> IO ()
validateAuditPacket = validateAuditPacketWith productionAuditIO

validateAuditPacketWith :: AuditIO -> FilePath -> [UnitRecord] -> IO ()
validateAuditPacketWith auditIO packetDir records = do
  _ <- either throwAuditError pure (validateObjectDenominator records)
  _ <- either throwAuditError pure (validateUniqueUnitNames records)
  submittedWorklist <-
    readAuditInput auditIO "packet worklist" (packetDir </> "worklist.tsv")
  leafInput <-
    readAuditInput auditIO "leaf-results" (packetDir </> "results.tsv")
  objectInput <-
    readAuditInput auditIO "object-results" (packetDir </> "object-results.tsv")
  expectedWorklist <-
    readAuditInput auditIO "committed worklist" bindingAuditPath
  _ <- either throwAuditError pure (validateWorklist records expectedWorklist)
  unless (submittedWorklist == expectedWorklist) $
    ioError (userError "packet worklist differs from committed worklist")
  leafDocument <- either throwAuditError pure (decodeAuditUtf8 leafRole leafInput)
  objectDocument <- either throwAuditError pure (decodeAuditUtf8 objectRole objectInput)
  leafRows <- either throwAuditError pure (parseLeafJudgments leafDocument)
  objectRows <- either throwAuditError pure (parseObjectJudgments objectDocument)
  _ <- either throwAuditError pure (validateLeafJudgments records leafRows)
  _ <- either throwAuditError pure (validateObjectJudgments records objectRows)
  pure ()

encodeAuditUtf8 :: String -> BS.ByteString
encodeAuditUtf8 = Text.encodeUtf8 . Text.pack

throwAuditError :: AuditError -> IO a
throwAuditError = ioError . userError . auditErrorMessage

isContainedBy :: FilePath -> FilePath -> Bool
isContainedBy parent candidate =
  splitDirectories (normalise parent)
    `isPrefixOf` splitDirectories (normalise candidate)

ignoreCleanup :: IO () -> IO ()
ignoreCleanup action =
  void (try action :: IO (Either SomeException ()))

runGitCommand :: [String] -> BS.ByteString -> IO AuditCommandResult
runGitCommand arguments inputBytes =
  mask $ \restore -> do
    (maybeInput, maybeOutput, maybeError, processHandle) <-
      createProcess
        (proc "git" arguments)
          { std_in = CreatePipe
          , std_out = CreatePipe
          , std_err = CreatePipe
          }
    let handles =
          foldr
            (\maybeHandle rest -> maybe rest (: rest) maybeHandle)
            []
            [maybeInput, maybeOutput, maybeError]
        cleanup = cleanupGitProcess handles processHandle
    case (maybeInput, maybeOutput, maybeError) of
      (Just inputHandle, Just outputHandle, Just errorHandle) ->
        restore
          ( do
              BS.hPut inputHandle inputBytes
              hClose inputHandle
              stdoutBytes <- BS.hGetContents outputHandle
              stderrBytes <- BS.hGetContents errorHandle
              ignoreCleanup (hClose outputHandle)
              ignoreCleanup (hClose errorHandle)
              exitCode <- waitForProcess processHandle
              pure
                AuditCommandResult
                  { auditCommandExitCode = exitCode
                  , auditCommandStdout = stdoutBytes
                  , auditCommandStderr = stderrBytes
                  }
          )
          `onException` cleanup
      _ -> do
        cleanup
        ioError (userError "failed to create Git command pipes")

cleanupGitProcess :: [Handle] -> ProcessHandle -> IO ()
cleanupGitProcess handles processHandle = do
  mapM_ (ignoreCleanup . hClose) handles
  ignoreCleanup (terminateProcess processHandle)
  ignoreCleanup (void (waitForProcess processHandle))

data AuditClassification
  = Faithful
  | Unfaithful
  | Underdetermined
  deriving (Eq, Ord, Show)

data AuditFileRole
  = AuditWorklistFile
  | AuditLeafResultsFile
  | AuditObjectResultsFile
  deriving (Eq, Ord, Show)

data LeafJudgment = LeafJudgment
  { leafJudgmentUnit :: String
  , leafJudgmentLeafId :: LeafId
  , leafJudgmentClassification :: AuditClassification
  , leafJudgmentJustification :: String
  , leafJudgmentDivergence :: Maybe String
  }
  deriving (Eq, Show)

data ObjectJudgment = ObjectJudgment
  { objectJudgmentSubject :: AuditSubjectId
  , objectJudgmentUnit :: String
  , objectJudgmentType :: AuditSubjectType
  , objectJudgmentFormalObject :: String
  , objectJudgmentProseContext :: String
  , objectJudgmentRefs :: [SourceRef]
  , objectJudgmentClassification :: AuditClassification
  , objectJudgmentJustification :: String
  , objectJudgmentDivergence :: Maybe String
  }
  deriving (Eq, Show)

data AuditCounts = AuditCounts
  { countAudited :: Int
  , countFaithful :: Int
  , countUnfaithful :: Int
  , countUnderdetermined :: Int
  }
  deriving (Eq, Show)

data AuditSummary = AuditSummary
  { summaryUnits :: Int
  , summaryLeaves :: AuditCounts
  , summaryByKind :: [(LeafKind, AuditCounts)]
  , summaryPaperAnchored :: AuditCounts
  , summaryByStatus :: [(Status, AuditCounts)]
  , summaryObjects :: [(AuditSubjectType, AuditCounts)]
  }
  deriving (Eq, Show)

data GitObjectFormat
  = GitObjectSha1
  | GitObjectSha256
  deriving (Eq, Show)

data InputIdentity = InputIdentity
  { inputObjectFormat :: GitObjectFormat
  , inputWorklistDigest :: String
  , inputLeafResultsDigest :: String
  , inputObjectResultsDigest :: String
  }
  deriving (Eq, Show)

data AuditError
  = AuditInvalidUtf8 AuditFileRole
  | AuditDocumentError AuditFileRole TsvError
  | AuditHeaderMismatch AuditFileRole [String] [String]
  | AuditRowProblem AuditFileRole Int String
  | AuditKeyProblem AuditFileRole Int String String
  | AuditInvalidClassification AuditFileRole Int String String
  | AuditInvalidSubjectType AuditFileRole Int String String
  | AuditBlankHumanField AuditFileRole Int String String
  | AuditGeneratedFieldDrift AuditFileRole Int String String String
  | AuditWorklistDrift Int (Maybe (String, String)) String
  | AuditDivergenceInvariant AuditFileRole Int String String
  | AuditDuplicateUnit String
  | AuditRequestedStatusCount String Int
  | AuditUnsupportedLeafKind String LeafId LeafKind
  | AuditSummaryJoinProblem String
  | AuditGitCommandFailed String ExitCode String
  | AuditGitOutputMalformed String
  | AuditObjectDenominatorMismatch Int Int Int
  deriving (Eq, Show)

auditErrorMessage :: AuditError -> String
auditErrorMessage auditError =
  case auditError of
    AuditInvalidUtf8 role -> renderFileRole role ++ ": invalid UTF-8"
    AuditDocumentError role tsvError -> renderFileRole role ++ ": " ++ tsvErrorMessage tsvError
    AuditHeaderMismatch role expected actual ->
      renderFileRole role ++ ": header mismatch; expected " ++ show expected ++ ", found " ++ show actual
    AuditRowProblem role rowNumber problem ->
      rowContext role rowNumber Nothing ++ problem
    AuditKeyProblem role rowNumber key problem ->
      rowContext role rowNumber (Just key) ++ problem
    AuditInvalidClassification role rowNumber key raw ->
      rowContext role rowNumber (Just key) ++ "invalid classification " ++ show raw
    AuditInvalidSubjectType role rowNumber key raw ->
      rowContext role rowNumber (Just key) ++ "invalid subject_type " ++ show raw
    AuditBlankHumanField role rowNumber key field ->
      rowContext role rowNumber (Just key) ++ field ++ " is blank"
    AuditGeneratedFieldDrift role rowNumber key field expected ->
      rowContext role rowNumber (Just key)
        ++ field ++ " differs from generated value " ++ expected
    AuditWorklistDrift rowNumber maybeKey problem ->
      rowContext worklistRole rowNumber (renderWorklistKey <$> maybeKey) ++ problem
    AuditDivergenceInvariant role rowNumber key problem ->
      rowContext role rowNumber (Just key) ++ problem
    AuditObjectDenominatorMismatch total strictCount attackCount ->
      "object denominator: expected 4 subjects"
        ++ " (1 strict-step, 3 typed-attack); found "
        ++ show total
        ++ " ("
        ++ show strictCount
        ++ " strict-step, "
        ++ show attackCount
        ++ " typed-attack)"
    AuditDuplicateUnit unit ->
      "duplicate unit " ++ show unit
    AuditRequestedStatusCount unit count ->
      "unit " ++ show unit
        ++ " must have exactly one requested status; found "
        ++ show count
    AuditUnsupportedLeafKind unit leafId kind ->
      "unit " ++ show unit ++ ", leaf " ++ show leafId
        ++ ": unsupported binding-audit kind "
        ++ kindStr kind
    AuditSummaryJoinProblem problem ->
      "summary join: " ++ problem
    AuditGitCommandFailed operation exitCode commandStderr ->
      operation ++ " failed with " ++ show exitCode
        ++ if null (trim commandStderr)
          then ""
          else ": " ++ trim commandStderr
    AuditGitOutputMalformed operation ->
      operation ++ ": malformed output"

decodeAuditUtf8 :: AuditFileRole -> BS.ByteString -> Either AuditError String
decodeAuditUtf8 role bytes =
  case Text.decodeUtf8' bytes of
    Left _ -> Left (AuditInvalidUtf8 role)
    Right text -> Right (Text.unpack text)

validateWorklist :: [UnitRecord] -> BS.ByteString -> Either AuditError ()
validateWorklist records bytes
  | bytes == expectedBytes = Right ()
  | otherwise = do
      document <- decodeAuditUtf8 worklistRole bytes
      _ <- parseDocument worklistRole worklistHeader document
      Left (firstWorklistDrift expectedDocument document)
  where
    expectedDocument = bindingAuditTsv records
    expectedBytes = Text.encodeUtf8 (Text.pack expectedDocument)

validateObjectDenominator :: [UnitRecord] -> Either AuditError ()
validateObjectDenominator records
  | total == 4 && strictCount == 1 && attackCount == 3 = Right ()
  | otherwise =
      Left
        ( AuditObjectDenominatorMismatch
            total
            strictCount
            attackCount
        )
  where
    subjects =
      [ subject
      | record <- records
      , subject <- urBindingAuditSubjects record
      ]
    total = length subjects
    strictCount =
      length
        [ ()
        | subject <- subjects
        , auditSubjectType subject == AuditStrictStep
        ]
    attackCount =
      length
        [ ()
        | subject <- subjects
        , auditSubjectType subject == AuditTypedAttack
        ]

renderLeafTemplate :: [UnitRecord] -> String
renderLeafTemplate records =
  renderDocument leafHeader
    [ [unit, rawLeafId, "", "", ""]
    | record <- records
    , row <- urBindingAuditRows record
    , let unit = urName record
          LeafId rawLeafId = lfId (barLeaf row)
    ]

renderObjectTemplate :: [UnitRecord] -> Either AuditError String
renderObjectTemplate records =
  renderDocument objectHeader
    <$> traverse
      renderRow
      (zip [2 ..] (recordSubjects records))
  where
    renderRow (rowNumber, (unit, subject)) = do
      let AuditSubjectId rawSubjectId = auditSubjectId subject
      refs <-
        renderSubjectRefsValue
          rowNumber
          rawSubjectId
          (auditSubjectRefs subject)
      pure
        [ rawSubjectId
        , unit
        , renderSubjectType (auditSubjectType subject)
        , auditSubjectFormalObject subject
        , auditSubjectProseContext subject
        , refs
        , ""
        , ""
        , ""
        ]

parseLeafJudgments :: String -> Either AuditError [LeafJudgment]
parseLeafJudgments document = do
  rows <- parseDocument leafRole leafHeader document
  traverse parseLeafRow (zip [2 ..] rows)

parseObjectJudgments :: String -> Either AuditError [ObjectJudgment]
parseObjectJudgments document = do
  rows <- parseDocument objectRole objectHeader document
  traverse parseObjectRow (zip [2 ..] rows)

validateLeafJudgments
  :: [UnitRecord]
  -> [LeafJudgment]
  -> Either AuditError [LeafJudgment]
validateLeafJudgments records judgments = do
  validateOrderedKeys leafRole expectedKeys actualKeys
  traverse validateHuman (zip [2 ..] judgments)
  where
    expectedKeys =
      [ leafKey (urName record) (lfId (barLeaf row))
      | record <- records
      , row <- urBindingAuditRows record
      ]
    actualKeys =
      [ leafKey (leafJudgmentUnit judgment) (leafJudgmentLeafId judgment)
      | judgment <- judgments
      ]
    validateHuman (rowNumber, judgment) = do
      let key = leafKey (leafJudgmentUnit judgment) (leafJudgmentLeafId judgment)
      (justification, divergence) <-
        validateTypedHumanFields
          leafRole
          rowNumber
          key
          (leafJudgmentClassification judgment)
          (leafJudgmentJustification judgment)
          (leafJudgmentDivergence judgment)
      Right
        judgment
          { leafJudgmentJustification = justification
          , leafJudgmentDivergence = divergence
          }

validateObjectJudgments
  :: [UnitRecord]
  -> [ObjectJudgment]
  -> Either AuditError [ObjectJudgment]
validateObjectJudgments records judgments = do
  validateOrderedKeys objectRole (map expectedObjectKey expected) (map judgmentKey judgments)
  traverseIndexed_ validateGenerated (zip3 [2 ..] expected judgments)
  traverse validateHuman (zip [2 ..] judgments)
  where
    expected =
      [ ExpectedObject unit subject
      | (unit, subject) <- recordSubjects records
      ]

    validateGenerated rowNumber expectedObject judgment = do
      let key = expectedObjectKey expectedObject
          subject = expectedObjectSubject expectedObject
      validateField Right rowNumber key "unit" (expectedObjectUnit expectedObject) (objectJudgmentUnit judgment)
      validateField (Right . renderSubjectType) rowNumber key "subject_type" (auditSubjectType subject) (objectJudgmentType judgment)
      validateField Right rowNumber key "formal_object" (auditSubjectFormalObject subject) (objectJudgmentFormalObject judgment)
      validateField Right rowNumber key "prose_context" (auditSubjectProseContext subject) (objectJudgmentProseContext judgment)
      validateField (renderSubjectRefsValue rowNumber key) rowNumber key "refs" (auditSubjectRefs subject) (objectJudgmentRefs judgment)

    validateHuman (rowNumber, judgment) = do
      let key = judgmentKey judgment
      (justification, divergence) <-
        validateTypedHumanFields
          objectRole
          rowNumber
          key
          (objectJudgmentClassification judgment)
          (objectJudgmentJustification judgment)
          (objectJudgmentDivergence judgment)
      Right
        judgment
          { objectJudgmentJustification = justification
          , objectJudgmentDivergence = divergence
          }

summarizeAudit
  :: [UnitRecord]
  -> BS.ByteString
  -> [LeafJudgment]
  -> [ObjectJudgment]
  -> Either AuditError AuditSummary
summarizeAudit records worklistBytes leafJudgments objectJudgments = do
  validateWorklist records worklistBytes
  validatedLeaves <- validateLeafJudgments records leafJudgments
  validatedObjects <- validateObjectJudgments records objectJudgments
  validateObjectDenominator records
  validateUniqueUnitNames records
  validateRequestedStatuses records
  let recordsByName = Map.fromList [(urName record, record) | record <- records]
      expectedLeaves =
        [ (urName record, barLeaf row)
        | record <- records
        , row <- urBindingAuditRows record
        ]
      initialSummary =
        AuditSummary
          { summaryUnits = length records
          , summaryLeaves = emptyAuditCounts
          , summaryByKind =
              [(Attested, emptyAuditCounts), (Observed, emptyAuditCounts)]
          , summaryPaperAnchored = emptyAuditCounts
          , summaryByStatus =
              [ (Justified, emptyAuditCounts)
              , (Gap, emptyAuditCounts)
              , (Defeated, emptyAuditCounts)
              , (Contested, emptyAuditCounts)
              ]
          , summaryObjects =
              [ (AuditStrictStep, emptyAuditCounts)
              , (AuditTypedAttack, emptyAuditCounts)
              ]
          }
  leafSummary <-
    foldLeafSummaries
      recordsByName
      initialSummary
      expectedLeaves
      validatedLeaves
  foldObjectSummaries leafSummary validatedObjects

validateUniqueUnitNames :: [UnitRecord] -> Either AuditError ()
validateUniqueUnitNames = go Set.empty
  where
    go _ [] = Right ()
    go seen (record : rest)
      | Set.member (urName record) seen =
          Left (AuditDuplicateUnit (urName record))
      | otherwise = go (Set.insert (urName record) seen) rest

validateRequestedStatuses :: [UnitRecord] -> Either AuditError ()
validateRequestedStatuses [] = Right ()
validateRequestedStatuses (record : rest) =
  case urStatuses record of
    [_] -> validateRequestedStatuses rest
    statuses ->
      Left (AuditRequestedStatusCount (urName record) (length statuses))

foldLeafSummaries
  :: Map.Map String UnitRecord
  -> AuditSummary
  -> [(String, LeafFact)]
  -> [LeafJudgment]
  -> Either AuditError AuditSummary
foldLeafSummaries _ auditSummary [] [] = Right auditSummary
foldLeafSummaries recordsByName auditSummary ((unit, leaf) : expectedRest) (judgment : judgmentRest) = do
  status <-
    case Map.lookup unit recordsByName of
      Just record ->
        case urStatuses record of
          [requestedStatus] -> Right requestedStatus
          _ -> Left (AuditSummaryJoinProblem ("non-singleton status for " ++ show unit))
      Nothing -> Left (AuditSummaryJoinProblem ("missing unit " ++ show unit))
  byKind <-
    case lfKind leaf of
      Attested ->
        updateBucket
          Attested
          (leafJudgmentClassification judgment)
          (summaryByKind auditSummary)
      Observed ->
        updateBucket
          Observed
          (leafJudgmentClassification judgment)
          (summaryByKind auditSummary)
      unsupportedKind ->
        Left
          ( AuditUnsupportedLeafKind
              unit
              (lfId leaf)
              unsupportedKind
          )
  byStatus <-
    updateBucket
      status
      (leafJudgmentClassification judgment)
      (summaryByStatus auditSummary)
  let classification = leafJudgmentClassification judgment
      paperAnchored =
        if lfPaperAnchored leaf
          then incrementAuditCount classification (summaryPaperAnchored auditSummary)
          else summaryPaperAnchored auditSummary
      nextSummary =
        auditSummary
          { summaryLeaves =
              incrementAuditCount classification (summaryLeaves auditSummary)
          , summaryByKind = byKind
          , summaryPaperAnchored = paperAnchored
          , summaryByStatus = byStatus
          }
  foldLeafSummaries recordsByName nextSummary expectedRest judgmentRest
foldLeafSummaries _ _ _ _ =
  Left (AuditSummaryJoinProblem "leaf result cardinality changed after validation")

foldObjectSummaries
  :: AuditSummary
  -> [ObjectJudgment]
  -> Either AuditError AuditSummary
foldObjectSummaries auditSummary [] = Right auditSummary
foldObjectSummaries auditSummary (judgment : rest) = do
  objects <-
    updateBucket
      (objectJudgmentType judgment)
      (objectJudgmentClassification judgment)
      (summaryObjects auditSummary)
  foldObjectSummaries auditSummary {summaryObjects = objects} rest

emptyAuditCounts :: AuditCounts
emptyAuditCounts = AuditCounts 0 0 0 0

incrementAuditCount :: AuditClassification -> AuditCounts -> AuditCounts
incrementAuditCount classification counts =
  case classification of
    Faithful ->
      counts
        { countAudited = countAudited counts + 1
        , countFaithful = countFaithful counts + 1
        }
    Unfaithful ->
      counts
        { countAudited = countAudited counts + 1
        , countUnfaithful = countUnfaithful counts + 1
        }
    Underdetermined ->
      counts
        { countAudited = countAudited counts + 1
        , countUnderdetermined = countUnderdetermined counts + 1
        }

updateBucket
  :: Eq key
  => key
  -> AuditClassification
  -> [(key, AuditCounts)]
  -> Either AuditError [(key, AuditCounts)]
updateBucket _ _ [] =
  Left (AuditSummaryJoinProblem "value outside a closed summary bucket")
updateBucket key classification ((candidate, counts) : rest)
  | key == candidate =
      Right ((candidate, incrementAuditCount classification counts) : rest)
  | otherwise =
      ((candidate, counts) :) <$> updateBucket key classification rest

renderAuditSummary :: InputIdentity -> AuditSummary -> String
renderAuditSummary identity auditSummary =
  renderJson $
    JObject
      [ ("schema", JString "lara-binding-audit@0.1")
      , ( "corpus"
        , JObject
            [ ("seed", JNumber 20260801)
            , ("units", JNumber (summaryUnits auditSummary))
            ]
        )
      , ( "inputs"
        , JObject
            [ ("object-format", JString (renderGitObjectFormat (inputObjectFormat identity)))
            , ("worklist", JString (inputWorklistDigest identity))
            , ("leaf-results", JString (inputLeafResultsDigest identity))
            , ("object-results", JString (inputObjectResultsDigest identity))
            ]
        )
      , ("leaves", auditCountsValue (summaryLeaves auditSummary))
      , ( "by-kind"
        , JObject
            [ (kindStr kind, auditCountsValue counts)
            | (kind, counts) <- summaryByKind auditSummary
            ]
        )
      , ( "paper-anchored"
        , auditCountsValue (summaryPaperAnchored auditSummary)
        )
      , ( "by-requested-status"
        , JObject
            [ (statusStr status, auditCountsValue counts)
            | (status, counts) <- summaryByStatus auditSummary
            ]
        )
      , ( "objects"
        , JObject
            [ (renderSubjectType subjectType, auditCountsValue counts)
            | (subjectType, counts) <- summaryObjects auditSummary
            ]
        )
      ]

auditCountsValue :: AuditCounts -> JValue
auditCountsValue counts =
  JObject
    ( ("audited", JNumber (countAudited counts))
        : [ (renderClassification classification, JNumber (classificationCount classification counts))
          | classification <- auditClassifications
          ]
    )

classificationCount :: AuditClassification -> AuditCounts -> Int
classificationCount classification counts =
  case classification of
    Faithful -> countFaithful counts
    Unfaithful -> countUnfaithful counts
    Underdetermined -> countUnderdetermined counts

auditClassifications :: [AuditClassification]
auditClassifications = [Faithful, Unfaithful, Underdetermined]

renderClassification :: AuditClassification -> String
renderClassification classification =
  case classification of
    Faithful -> "faithful"
    Unfaithful -> "unfaithful"
    Underdetermined -> "underdetermined"

summarizeAuditFiles :: [UnitRecord] -> IO ()
summarizeAuditFiles = summarizeAuditFilesWith productionAuditIO

summarizeAuditFilesWith :: AuditIO -> [UnitRecord] -> IO ()
summarizeAuditFilesWith auditIO records = do
  worklistBytes <-
    readAuditInput auditIO "worklist" bindingAuditPath
  leafBytes <-
    readAuditInput auditIO "leaf-results" leafResultsPath
  objectBytes <-
    readAuditInput auditIO "object-results" objectResultsPath
  _ <-
    either throwAuditError pure (validateWorklist records worklistBytes)
  _ <-
    either throwAuditError pure (validateObjectDenominator records)
  leafDocument <-
    either throwAuditError pure (decodeAuditUtf8 leafRole leafBytes)
  objectDocument <-
    either throwAuditError pure (decodeAuditUtf8 objectRole objectBytes)
  leafJudgments <-
    either throwAuditError pure (parseLeafJudgments leafDocument)
  objectJudgments <-
    either throwAuditError pure (parseObjectJudgments objectDocument)
  auditSummary <-
    either
      throwAuditError
      pure
      (summarizeAudit records worklistBytes leafJudgments objectJudgments)
  identity <- inputIdentity auditIO worklistBytes leafBytes objectBytes
  let summaryBytes =
        encodeAuditUtf8 (renderAuditSummary identity auditSummary)
  _ <- evaluate (BS.length summaryBytes)
  withAuditIOContext
    ("write summary " ++ summaryPath)
    (atomicWriteAuditBytes auditIO summaryPath summaryBytes)

readAuditInput :: AuditIO -> String -> FilePath -> IO BS.ByteString
readAuditInput auditIO inputName path =
  withAuditIOContext
    ("read " ++ inputName ++ " " ++ path)
    (readAuditBytes auditIO path)

withAuditIOContext :: String -> IO a -> IO a
withAuditIOContext context action =
  catch action (auditIOException context)

auditIOException :: String -> IOException -> IO a
auditIOException context exception =
  ioError
    ( userError
        (context ++ ": " ++ displayException exception)
    )

inputIdentity
  :: AuditIO
  -> BS.ByteString
  -> BS.ByteString
  -> BS.ByteString
  -> IO InputIdentity
inputIdentity auditIO worklistBytes leafBytes objectBytes = do
  formatResult <-
    withAuditIOContext
      "git rev-parse --show-object-format"
      (discoverObjectFormat auditIO)
  objectFormat <-
    either throwAuditError pure $
      parseObjectFormat
        "git rev-parse --show-object-format"
        formatResult
  worklistDigest <-
    hashInput auditIO objectFormat "worklist" worklistBytes
  leafDigest <-
    hashInput auditIO objectFormat "leaf-results" leafBytes
  objectDigest <-
    hashInput auditIO objectFormat "object-results" objectBytes
  pure
    InputIdentity
      { inputObjectFormat = objectFormat
      , inputWorklistDigest = worklistDigest
      , inputLeafResultsDigest = leafDigest
      , inputObjectResultsDigest = objectDigest
      }

parseObjectFormat
  :: String
  -> AuditCommandResult
  -> Either AuditError GitObjectFormat
parseObjectFormat operation commandResult = do
  objectFormat <- commandOutputLine operation commandResult
  case objectFormat of
    "sha1" -> Right GitObjectSha1
    "sha256" -> Right GitObjectSha256
    _ -> Left (AuditGitOutputMalformed operation)

hashInput
  :: AuditIO
  -> GitObjectFormat
  -> String
  -> BS.ByteString
  -> IO String
hashInput auditIO objectFormat inputName inputBytes = do
  commandResult <-
    withAuditIOContext
      ("git hash-object --stdin for " ++ inputName)
      (hashAuditBytes auditIO inputBytes)
  let operation = "git hash-object --stdin for " ++ inputName
  digest <- either throwAuditError pure (commandOutputLine operation commandResult)
  unless (validDigest objectFormat digest) $
    throwAuditError (AuditGitOutputMalformed operation)
  pure digest

commandOutputLine
  :: String
  -> AuditCommandResult
  -> Either AuditError String
commandOutputLine operation commandResult =
  case auditCommandExitCode commandResult of
    ExitFailure _ ->
      Left
        ( AuditGitCommandFailed
            operation
            (auditCommandExitCode commandResult)
            ( Text.unpack
                (Text.decodeUtf8With lenientDecode (auditCommandStderr commandResult))
            )
        )
    ExitSuccess ->
      case Text.decodeUtf8' (auditCommandStdout commandResult) of
        Left _ -> Left (AuditGitOutputMalformed operation)
        Right output ->
          let rendered = Text.unpack output
           in case reverse rendered of
                '\n' : reversedLine
                  | not (null reversedLine)
                      && all (/= '\n') reversedLine
                      && all (/= '\r') reversedLine ->
                      Right (reverse reversedLine)
                _ -> Left (AuditGitOutputMalformed operation)

validDigest :: GitObjectFormat -> String -> Bool
validDigest objectFormat digest =
  length digest == expectedLength
    && all isLowerHexDigit digest
  where
    expectedLength =
      case objectFormat of
        GitObjectSha1 -> 40
        GitObjectSha256 -> 64
    isLowerHexDigit character =
      character >= '0' && character <= '9'
        || character >= 'a' && character <= 'f'

renderGitObjectFormat :: GitObjectFormat -> String
renderGitObjectFormat objectFormat =
  case objectFormat of
    GitObjectSha1 -> "sha1"
    GitObjectSha256 -> "sha256"

parseLeafRow :: (Int, [String]) -> Either AuditError LeafJudgment
parseLeafRow (rowNumber, [unit, rawLeafId, rawClassification, rawJustification, rawDivergence]) = do
  let key = unit ++ "/" ++ rawLeafId
  requireKeyParts leafRole rowNumber key [unit, rawLeafId]
  classification <- parseClassification leafRole rowNumber key rawClassification
  (justification, divergence) <-
    validateHumanFields leafRole rowNumber key classification rawJustification rawDivergence
  Right
    LeafJudgment
      { leafJudgmentUnit = unit
      , leafJudgmentLeafId = LeafId rawLeafId
      , leafJudgmentClassification = classification
      , leafJudgmentJustification = justification
      , leafJudgmentDivergence = divergence
      }
parseLeafRow (rowNumber, _) = Left (AuditRowProblem leafRole rowNumber "wrong column count")

parseObjectRow :: (Int, [String]) -> Either AuditError ObjectJudgment
parseObjectRow
  ( rowNumber
    , [ rawSubjectId
      , unit
      , rawSubjectType
      , formalObject
      , proseContext
      , rawRefs
      , rawClassification
      , rawJustification
      , rawDivergence
      ]
    ) = do
    let key = rawSubjectId
    requireKeyParts objectRole rowNumber key [rawSubjectId]
    subjectType <- parseSubjectType rowNumber key rawSubjectType
    refs <-
      mapLeft
        (\refError -> AuditRowProblem objectRole rowNumber ("key " ++ show key ++ ": refs: " ++ refCellErrorMessage refError))
        (parseRefsCell rawRefs)
    classification <- parseClassification objectRole rowNumber key rawClassification
    (justification, divergence) <-
      validateHumanFields objectRole rowNumber key classification rawJustification rawDivergence
    Right
      ObjectJudgment
        { objectJudgmentSubject = AuditSubjectId rawSubjectId
        , objectJudgmentUnit = unit
        , objectJudgmentType = subjectType
        , objectJudgmentFormalObject = formalObject
        , objectJudgmentProseContext = proseContext
        , objectJudgmentRefs = refs
        , objectJudgmentClassification = classification
        , objectJudgmentJustification = justification
        , objectJudgmentDivergence = divergence
        }
parseObjectRow (rowNumber, _) = Left (AuditRowProblem objectRole rowNumber "wrong column count")

data ExpectedObject = ExpectedObject
  { expectedObjectUnit :: String
  , expectedObjectSubject :: AuditSubject
  }

expectedObjectKey :: ExpectedObject -> String
expectedObjectKey expectedObject =
  let AuditSubjectId raw = auditSubjectId (expectedObjectSubject expectedObject)
   in raw

judgmentKey :: ObjectJudgment -> String
judgmentKey judgment =
  let AuditSubjectId raw = objectJudgmentSubject judgment
   in raw

validateOrderedKeys :: AuditFileRole -> [String] -> [String] -> Either AuditError ()
validateOrderedKeys role expected actual = go 2 [] expected actual
  where
    go _ _ [] [] = Right ()
    go rowNumber _ (expectedKey : _) [] =
      Left (AuditKeyProblem role rowNumber expectedKey "missing key")
    go rowNumber _ [] (actualKey : _) =
      Left (AuditKeyProblem role rowNumber actualKey "unknown key")
    go rowNumber seen (expectedKey : expectedRest) (actualKey : actualRest)
      | actualKey == expectedKey =
          go (rowNumber + 1) (actualKey : seen) expectedRest actualRest
      | actualKey `elem` seen =
          Left (AuditKeyProblem role rowNumber actualKey "duplicate key")
      | actualKey `notElem` expected =
          Left (AuditKeyProblem role rowNumber actualKey "unknown key")
      | otherwise =
          Left
            ( AuditKeyProblem role rowNumber actualKey
                ("reordered key; expected " ++ show expectedKey)
            )

validateField
  :: Eq value
  => (value -> Either AuditError String)
  -> Int
  -> String
  -> String
  -> value
  -> value
  -> Either AuditError ()
validateField renderValue rowNumber key field expected actual
  | actual == expected = Right ()
  | otherwise = do
      renderedExpected <- renderValue expected
      Left
        ( AuditGeneratedFieldDrift
            objectRole
            rowNumber
            key
            field
            renderedExpected
        )

parseClassification
  :: AuditFileRole
  -> Int
  -> String
  -> String
  -> Either AuditError AuditClassification
parseClassification role rowNumber key raw =
  case find ((== raw) . renderClassification) auditClassifications of
    Just classification -> Right classification
    Nothing -> Left (AuditInvalidClassification role rowNumber key raw)

parseSubjectType :: Int -> String -> String -> Either AuditError AuditSubjectType
parseSubjectType rowNumber key raw =
  case find ((== raw) . renderSubjectType) auditSubjectTypes of
    Just subjectType -> Right subjectType
    Nothing -> Left (AuditInvalidSubjectType objectRole rowNumber key raw)

auditSubjectTypes :: [AuditSubjectType]
auditSubjectTypes = [AuditStrictStep, AuditTypedAttack]

renderSubjectType :: AuditSubjectType -> String
renderSubjectType AuditStrictStep = "strict-step"
renderSubjectType AuditTypedAttack = "typed-attack"

validateHumanFields
  :: AuditFileRole
  -> Int
  -> String
  -> AuditClassification
  -> String
  -> String
  -> Either AuditError (String, Maybe String)
validateHumanFields role rowNumber key classification rawJustification rawDivergence =
  validateHumanFieldValues
    role
    rowNumber
    key
    classification
    rawJustification
    (Just (trim rawDivergence))
    (rawDivergence == "-")
    "faithful and underdetermined classifications require divergence_note exactly '-'"

validateTypedHumanFields
  :: AuditFileRole
  -> Int
  -> String
  -> AuditClassification
  -> String
  -> Maybe String
  -> Either AuditError (String, Maybe String)
validateTypedHumanFields role rowNumber key classification rawJustification maybeDivergence =
  validateHumanFieldValues
    role
    rowNumber
    key
    classification
    rawJustification
    (trim <$> maybeDivergence)
    (maybeDivergence == Nothing)
    "faithful and underdetermined classifications require no divergence_note"

validateHumanFieldValues
  :: AuditFileRole
  -> Int
  -> String
  -> AuditClassification
  -> String
  -> Maybe String
  -> Bool
  -> String
  -> Either AuditError (String, Maybe String)
validateHumanFieldValues
  role
  rowNumber
  key
  classification
  rawJustification
  submittedDivergence
  noDivergenceAccepted
  noDivergenceProblem = do
    let justification = trim rawJustification
    if null justification
      then Left (AuditBlankHumanField role rowNumber key "justification")
      else Right ()
    divergence <-
      case classification of
        Unfaithful ->
          case submittedDivergence of
            Just value
              | not (null value) && value /= "-" -> Right (Just value)
            _ ->
              Left
                ( AuditDivergenceInvariant role rowNumber key
                    "unfaithful classification requires a non-'-' divergence_note"
                )
        Faithful -> requireNoDivergence
        Underdetermined -> requireNoDivergence
    Right (justification, divergence)
  where
    requireNoDivergence
      | noDivergenceAccepted = Right Nothing
      | otherwise =
          Left
            ( AuditDivergenceInvariant
                role
                rowNumber
                key
                noDivergenceProblem
            )
parseDocument :: AuditFileRole -> [String] -> String -> Either AuditError [[String]]
parseDocument role expectedHeader document = do
  rows <- mapLeft (AuditDocumentError role) (parseTsv (length expectedHeader) document)
  case rows of
    [] -> Left (AuditHeaderMismatch role expectedHeader [])
    actualHeader : dataRows
      | actualHeader == expectedHeader -> Right dataRows
      | otherwise -> Left (AuditHeaderMismatch role expectedHeader actualHeader)

renderDocument :: [String] -> [[String]] -> String
renderDocument header rows = unlines (map renderTsvRow (header : rows))

renderSubjectRefsValue
  :: Int
  -> String
  -> [SourceRef]
  -> Either AuditError String
renderSubjectRefsValue rowNumber key =
  mapLeft
    ( \refError ->
        AuditRowProblem objectRole rowNumber
          ("key " ++ show key ++ ": refs: " ++ refCellErrorMessage refError)
    )
    . renderRefsCell


requireKeyParts :: AuditFileRole -> Int -> String -> [String] -> Either AuditError ()
requireKeyParts role rowNumber key parts
  | any null parts = Left (AuditKeyProblem role rowNumber key "blank key")
  | otherwise = Right ()

recordSubjects :: [UnitRecord] -> [(String, AuditSubject)]
recordSubjects records =
  [ (urName record, subject)
  | record <- records
  , subject <- urBindingAuditSubjects record
  ]

leafKey :: String -> LeafId -> String
leafKey unit (LeafId rawLeafId) = unit ++ "/" ++ rawLeafId

renderWorklistKey :: (String, String) -> String
renderWorklistKey (unit, rawLeafId) = unit ++ "/" ++ rawLeafId

firstWorklistDrift :: String -> String -> AuditError
firstWorklistDrift expected actual =
  let expectedRows = parsedRows expected
      actualRows = parsedRows actual
      differing =
        [ candidateRowNumber
        | (candidateRowNumber, expectedRow, actualRow) <- zip3 [1 ..] expectedRows actualRows
        , expectedRow /= actualRow
        ]
      driftRowNumber =
        case differing of
          first : _ -> first
          [] -> min (length expectedRows) (length actualRows) + 1
      maybeKey =
        rowKey =<< (rowAt driftRowNumber actualRows <|> rowAt driftRowNumber expectedRows)
   in AuditWorklistDrift driftRowNumber maybeKey "does not match the generated worklist"
  where
    parsedRows document =
      case parseTsv (length worklistHeader) document of
        Right rows -> rows
        Left _ -> []

    rowAt rowNumber rows =
      case drop (rowNumber - 1) rows of
        row : _ -> Just row
        [] -> Nothing

    rowKey (unit : rawLeafId : _) = Just (unit, rawLeafId)
    rowKey _ = Nothing

rowContext :: AuditFileRole -> Int -> Maybe String -> String
rowContext role rowNumber maybeKey =
  renderFileRole role ++ ": row " ++ show rowNumber
    ++ maybe "" (\key -> ", key " ++ show key) maybeKey
    ++ ": "

renderFileRole :: AuditFileRole -> String
renderFileRole AuditWorklistFile = "worklist"
renderFileRole AuditLeafResultsFile = "leaf results"
renderFileRole AuditObjectResultsFile = "object results"

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace

mapLeft :: (left -> other) -> Either left right -> Either other right
mapLeft f result =
  case result of
    Left value -> Left (f value)
    Right value -> Right value

traverseIndexed_
  :: (Int -> expected -> actual -> Either error ())
  -> [(Int, expected, actual)]
  -> Either error ()
traverseIndexed_ _ [] = Right ()
traverseIndexed_ f ((rowNumber, expected, actual) : rest) = do
  f rowNumber expected actual
  traverseIndexed_ f rest


tsvErrorMessage :: TsvError -> String
tsvErrorMessage tsvError =
  case tsvError of
    TsvMissingFinalNewline -> "document must end in exactly one LF"
    TsvExtraFinalNewline -> "document has an extra final newline"
    TsvCarriageReturn offset -> "raw CR at character " ++ show offset
    TsvBlankRow rowNumber -> "blank row " ++ show rowNumber
    TsvMalformedEscape rowNumber column maybeEscape ->
      "malformed escape at row " ++ show rowNumber ++ ", column " ++ show column
        ++ maybe " (trailing backslash)" (\escape -> " (\\" ++ [escape] ++ ")") maybeEscape
    TsvWrongColumnCount rowNumber expected actual ->
      "row " ++ show rowNumber ++ " has " ++ show actual
        ++ " columns; expected " ++ show expected

leafHeader :: [String]
leafHeader = ["unit", "leaf_id", "classification", "justification", "divergence_note"]

objectHeader :: [String]
objectHeader =
  [ "subject_id"
  , "unit"
  , "subject_type"
  , "formal_object"
  , "prose_context"
  , "refs"
  , "classification"
  , "justification"
  , "divergence_note"
  ]

worklistHeader :: [String]
worklistHeader =
  [ "unit"
  , "leaf_id"
  , "formal_target"
  , "role"
  , "claim_id"
  , "claim_nl"
  , "kind"
  , "provenance"
  , "refs"
  ]

leafRole, objectRole, worklistRole :: AuditFileRole
leafRole = AuditLeafResultsFile
objectRole = AuditObjectResultsFile
worklistRole = AuditWorklistFile
