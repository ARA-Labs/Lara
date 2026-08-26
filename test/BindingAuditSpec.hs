module BindingAuditSpec (bindingAuditSpecProps) where

import Control.Exception (SomeException, bracket, displayException, try)
import Control.Monad (forM)
import qualified Data.ByteString as BS
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.List (isInfixOf, isPrefixOf, sort)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import System.Directory
  ( canonicalizePath
  , createDirectory
  , createDirectoryLink
  , doesPathExist
  , getTemporaryDirectory
  , listDirectory
  , removeFile
  , removePathForcibly
  )
import System.Exit (ExitCode (..))
import System.FilePath ((</>), addTrailingPathSeparator, takeFileName)
import System.IO (hClose, openTempFile)
import System.IO.Error (ioeGetErrorString)
import System.Process (readProcessWithExitCode)
import Test.QuickCheck

import Lara.AST
  ( LeafId (..)
  , LeafKind (Assumed, Attested, Observed)
  , PropId (..)
  , Provenance (AiExecuted)
  , SourceRef (..)
  , Status (Contested, Defeated, Gap, Justified)
  )
import Lara.BindingAudit
import Lara.BindingAudit.Tsv
import Lara.BindingAudit.Types
import Lara.AtomicWrite (atomicWriteWith)
import Lara.ClaimSupport
import Lara.Prop (Pred (..), Prop (..))
import Lara.ClaimSupport.Load (loadRecords)

bindingAuditSpecProps :: [(String, IO Result)]
bindingAuditSpecProps =
  [ ("binding-audit: TSV escaping round-trips", quickCheckResult prop_tsvEscapes)
  , ("binding-audit: malformed TSV is rejected", quickCheckResult prop_tsvRejectsMalformed)
  , ("binding-audit: leaf template preserves worklist key order", quickCheckResult prop_leafTemplate)
  , ("binding-audit: object template preserves subject order", quickCheckResult prop_objectTemplate)
  , ("binding-audit: classifications parse", quickCheckResult prop_classifications)
  , ("binding-audit: invalid classifications are rejected", quickCheckResult prop_invalidClassification)
  , ("binding-audit: key sequence drift is rejected", quickCheckResult prop_keyDrift)
  , ("binding-audit: blank judgment keys have exact diagnostics", quickCheckResult prop_blankJudgmentKeys)
  , ("binding-audit: blank justifications are rejected", quickCheckResult prop_blankJustification)
  , ("binding-audit: divergence invariants are enforced", quickCheckResult prop_divergenceInvariants)
  , ("binding-audit: exact result headers are required", quickCheckResult prop_exactHeaders)
  , ("binding-audit: result documents use one final LF", quickCheckResult prop_strictDocuments)
  , ("binding-audit: whitespace-only human fields are rejected", quickCheckResult prop_whitespaceHumanFields)
  , ("binding-audit: refs cells share one typed codec", quickCheckResult prop_refsCodec)
  , ("binding-audit: unknown object subject types are rejected", quickCheckResult prop_unknownSubjectType)
  , ("binding-audit: every object generated field is sealed", quickCheckResult prop_generatedFieldDrift)
  , ("binding-audit: worklist validation is exact", quickCheckResult prop_worklistValidation)
  , ("binding-audit: invalid UTF-8 is rejected at the boundary", quickCheckResult prop_invalidUtf8)
  , ("binding-audit: errors carry context without the CLI prefix", quickCheckResult prop_errorContext)
  , ("binding-audit: object denominator is exactly one strict plus three attacks", quickCheckResult prop_objectDenominator)
  , ("binding-audit: summary aggregation is closed and exact", quickCheckResult prop_summaryAggregation)
  , ("binding-audit: summary rejects non-singleton statuses and duplicate units", quickCheckResult prop_summaryJoinFailures)
  , ("binding-audit: summary JSON is canonical", quickCheckResult prop_summaryJsonGolden)
  , ("binding-audit: prepare creates one exact detached packet", quickCheckResult prop_prepareExactPacket)
  , ("binding-audit: prepare rejects stale worklists before creation", quickCheckResult prop_prepareRejectsStaleWorklist)
  , ("binding-audit: packet read failures name operation and path", quickCheckResult prop_packetReadErrorsCarryContext)
  , ("binding-audit: production AuditIO preserves strict bytes and Git results", quickCheckResult prop_productionAuditIO)
  , ("binding-audit: packet templates are status-free and complete", quickCheckResult prop_packetTemplateShape)
  , ("binding-audit: prepare accepts trailing destination separators", quickCheckResult prop_prepareTrailingSeparator)
  , ("binding-audit: prepare never clobbers an existing destination", quickCheckResult prop_prepareNoClobber)
  , ("binding-audit: committed-storage aliases are forbidden", quickCheckResult prop_forbiddenDestinations)
  , ("binding-audit: rendering failures precede destination creation", quickCheckResult prop_renderBeforeCreate)
  , ("binding-audit: every write failure removes only the partial packet", quickCheckResult prop_transactionalWriteFailures)
  , ("binding-audit: validate is read-only and status-blind", quickCheckResult prop_validateReadOnlyStatusBlind)
  , ("binding-audit: validate rejects every malformed packet class", quickCheckResult prop_validateMalformedPackets)
  , ("binding-audit: validate rejects duplicate units before reads", quickCheckResult prop_validateRejectsDuplicateUnits)
  , ("binding-audit: validate rejects a stale committed denominator", quickCheckResult prop_validateRejectsStaleDenominator)
  , ("binding-audit: validate rejects invalid UTF-8 without writes", quickCheckResult prop_validateRejectsInvalidUtf8)
  , ("binding-audit: object denominator failures preserve packet and summary boundaries", quickCheckResult prop_objectDenominatorBoundaries)
  , ("binding-audit: summarize replaces only after complete validation", quickCheckResult prop_summarizeValidationBeforeWrite)
  , ("binding-audit: summarize atomic failure preserves the prior file", quickCheckResult prop_summarizeAtomicFailure)
  , ("binding-audit: summarize identities hash exact raw bytes", quickCheckResult prop_summarizeRawIdentities)
  , ("binding-audit: summarize accepts a complete SHA-256 identity", quickCheckResult prop_summarizeSha256Identity)
  , ("binding-audit: summarize rejects malformed Git object format output", quickCheckResult prop_summarizeObjectFormatFailures)
  , ("binding-audit: summarize rejects every named hash failure", quickCheckResult prop_summarizeHashFailures)
  , ("binding-audit: summarize rejects invalid UTF-8 before Git", quickCheckResult prop_summarizeUtf8BeforeIdentity)
  , ("binding-audit: CLI channels, prefix, and usage are exact", quickCheckResult prop_cliContract)
  ]

leafHeader :: String
leafHeader = "unit\tleaf_id\tclassification\tjustification\tdivergence_note\n"

objectHeader :: String
objectHeader = "subject_id\tunit\tsubject_type\tformal_object\tprose_context\trefs\tclassification\tjustification\tdivergence_note\n"

leafDocument :: String -> String -> String -> String
leafDocument classification justification divergence =
  leafHeader ++ "u1\te1\t" ++ classification ++ "\t" ++ justification ++ "\t" ++ divergence ++ "\n"

validLeafDocument :: String
validLeafDocument =
  leafHeader
    ++ "u1\te1\tfaithful\tchecked\t-\n"
    ++ "u1\te2\tunfaithful\tmismatch\tconcrete divergence\n"
    ++ "u2\te3\tunderdetermined\tinsufficient\t-\n"

objectDocument :: String
objectDocument =
  objectHeader
    ++ "s1\tu1\tstrict-step\tformal one\tprose one\tref/one\tfaithful\tchecked\t-\n"
    ++ "s2\tu1\ttyped-attack\tformal two\tprose two\t-\tunfaithful\tmismatch\twrong endpoint\n"
    ++ "s3\tu2\ttyped-attack\tformal three\tprose three\tref/a,ref/b\tunderdetermined\tinsufficient\t-\n"
    ++ "s4\tu2\ttyped-attack\tformal four\tprose four\tref/four\tfaithful\tchecked\t-\n"

prop_tsvEscapes :: Property
prop_tsvEscapes =
  conjoin
    [ once $
        let cells = ["slash\\tail", "has\ttab", "has\rcr", "has\nlf"]
            document = renderTsvRow cells ++ "\n"
         in counterexample document (parseTsv 4 document === Right [cells])
    , forAll (suchThat (listOf1 (listOf arbitrary)) (/= [""])) $ \cells ->
        let document = renderTsvRow cells ++ "\n"
         in counterexample document $
              parseTsv (length cells) document === Right [cells]
    ]

prop_tsvRejectsMalformed :: Property
prop_tsvRejectsMalformed =
  once $
    conjoin
      [ rejected (parseTsv 2 "a\\q\tb\n")
      , rejected (parseTsv 2 "a\tb\tc\n")
      , rejected (parseTsv 2 "a\traw\ttab\n")
      , rejected (parseTsv 2 "a\\\tb\n")
      , parseTsv 1 "a\\\n" === Left (TsvMalformedEscape 1 1 Nothing)
      ]

prop_leafTemplate :: Property
prop_leafTemplate =
  once $
    renderLeafTemplate records
      === leafHeader
        ++ "u1\te1\t\t\t\n"
        ++ "u1\te2\t\t\t\n"
        ++ "u2\te3\t\t\t\n"

prop_objectTemplate :: Property
prop_objectTemplate =
  once $
    renderObjectTemplate records
      === Right
        ( objectHeader
            ++ "s1\tu1\tstrict-step\tformal one\tprose one\tref/one\t\t\t\n"
            ++ "s2\tu1\ttyped-attack\tformal two\tprose two\t-\t\t\t\n"
            ++ "s3\tu2\ttyped-attack\tformal three\tprose three\tref/a,ref/b\t\t\t\n"
            ++ "s4\tu2\ttyped-attack\tformal four\tprose four\tref/four\t\t\t\n"
        )

prop_classifications :: Property
prop_classifications =
  once $
    conjoin
      [ parsedClass "faithful" Faithful "-"
      , parsedClass "unfaithful" Unfaithful "concrete mismatch"
      , parsedClass "underdetermined" Underdetermined "-"
      ]
  where
    parsedClass raw expected divergence =
      case parseLeafJudgments (leafDocument raw "because evidence" divergence) of
        Right [judgment] -> leafJudgmentClassification judgment === expected
        other -> counterexample (show other) False

prop_invalidClassification :: Property
prop_invalidClassification =
  once $ rejected (parseLeafJudgments (leafDocument "Faithful" "because" "-"))

prop_keyDrift :: Property
prop_keyDrift =
  once $
    conjoin
      [ invalidKeys (leafHeader ++ "u1\te1\tfaithful\tok\t-\n" ++ "u1\te2\tfaithful\tok\t-\n")
      , invalidKeys (leafHeader ++ "u1\te1\tfaithful\tok\t-\n" ++ "u1\te1\tfaithful\tok\t-\n" ++ "u2\te3\tfaithful\tok\t-\n")
      , invalidKeys (leafHeader ++ "u1\te1\tfaithful\tok\t-\n" ++ "u1\tunknown\tfaithful\tok\t-\n" ++ "u2\te3\tfaithful\tok\t-\n")
      , invalidKeys (leafHeader ++ "u1\te2\tfaithful\tok\t-\n" ++ "u1\te1\tfaithful\tok\t-\n" ++ "u2\te3\tfaithful\tok\t-\n")
      , invalidObjectOrder
      ]
  where
    invalidKeys document =
      case parseLeafJudgments document of
        Left err -> counterexample (auditErrorMessage err) False
        Right judgments -> rejected (validateLeafJudgments records judgments)

    invalidObjectOrder =
      case parseObjectJudgments objectDocument of
        Left err -> counterexample (auditErrorMessage err) False
        Right (first : second : rest) ->
          rejected (validateObjectJudgments records (second : first : rest))
        Right other -> counterexample (show other) False

prop_blankJustification :: Property
prop_blankJustification =
  once $ rejected (parseLeafJudgments (leafDocument "faithful" "" "-"))

prop_blankJudgmentKeys :: Property
prop_blankJudgmentKeys =
  once $
    conjoin
      [ exactError
          "leaf results: row 2, key \"/e1\": blank key"
          (parseLeafJudgments (leafHeader ++ "\te1\tfaithful\tbecause\t-\n"))
      , exactError
          "leaf results: row 2, key \"u1/\": blank key"
          (parseLeafJudgments (leafHeader ++ "u1\t\tfaithful\tbecause\t-\n"))
      , exactError
          "object results: row 2, key \"\": blank key"
          ( parseObjectJudgments
              ( objectHeader
                  ++ "\tu1\tstrict-step\tformal\tprose\t-\tfaithful\tbecause\t-\n"
              )
          )
      ]
  where
    exactError expected result =
      case result of
        Left auditError -> auditErrorMessage auditError === expected
        Right _ -> counterexample "unexpected blank-key acceptance" False

prop_divergenceInvariants :: Property
prop_divergenceInvariants =
  once $
    conjoin
      [ rejected (parseLeafJudgments (leafDocument "unfaithful" "because" "-"))
      , rejected (parseLeafJudgments (leafDocument "unfaithful" "because" ""))
      , rejected (parseLeafJudgments (leafDocument "faithful" "because" "difference"))
      , rejected (parseLeafJudgments (leafDocument "underdetermined" "because" "difference"))
      , rejected (parseLeafJudgments (leafDocument "faithful" "because" " -"))
      , rejected (parseLeafJudgments (leafDocument "faithful" "because" "-\x2003"))
      , rejected (parseLeafJudgments (leafDocument "underdetermined" "because" "\x2003-\x2003"))
      ]

prop_exactHeaders :: Property
prop_exactHeaders =
  once $
    conjoin
      [ rejected (parseLeafJudgments ("leaf_id\tunit\tclassification\tjustification\tdivergence_note\n" ++ "e1\tu1\tfaithful\tok\t-\n"))
      , rejected (parseObjectJudgments ("unit\tsubject_id\tsubject_type\tformal_object\tprose_context\trefs\tclassification\tjustification\tdivergence_note\n" ++ "u1\ts1\tstrict-step\tf\tp\t-\tfaithful\tok\t-\n"))
      ]

prop_strictDocuments :: Property
prop_strictDocuments =
  once $
    let accepted = leafDocument "faithful" "because" "-"
     in conjoin
          [ acceptedRight (parseLeafJudgments accepted)
          , rejected (parseLeafJudgments (replaceLfWithCrlf accepted))
          , rejected (parseLeafJudgments (init accepted))
          , rejected (parseLeafJudgments (accepted ++ "\n"))
          , rejected (parseLeafJudgments (leafHeader ++ "\n" ++ "u1\te1\tfaithful\tbecause\t-\n"))
          ]

prop_whitespaceHumanFields :: Property
prop_whitespaceHumanFields =
  once $
    conjoin
      [ rejected (parseLeafJudgments (leafDocument "faithful" "\x2003" "-"))
      , rejected (parseLeafJudgments (leafDocument "unfaithful" "because" "\x2003"))
      , validatorRejectsHumanMutation
      ]
  where
    validatorRejectsHumanMutation =
      case parseLeafJudgments validLeafDocument of
        Left err -> counterexample (auditErrorMessage err) False
        Right judgments ->
          conjoin
            [ rejected
                ( validateLeafJudgments records
                    (changeFirst (\judgment -> judgment {leafJudgmentJustification = "\x2003"}) judgments)
                )
            , rejected
                ( validateLeafJudgments records
                    ( changeFirst
                        ( \judgment ->
                            judgment
                              { leafJudgmentClassification = Unfaithful
                              , leafJudgmentDivergence = Nothing
                              }
                        )
                        judgments
                    )
                )
            , rejected
                ( validateLeafJudgments records
                    (changeFirst (\judgment -> judgment {leafJudgmentDivergence = Just "unexpected"}) judgments)
                )
            ]

prop_refsCodec :: Property
prop_refsCodec =
  once $
    conjoin
      [ renderRefsCell [] === Right "-"
      , renderRefsCell [SourceRef "ref/one"] === Right "ref/one"
      , renderRefsCell [SourceRef "ref/a", SourceRef "ref/b"] === Right "ref/a,ref/b"
      , parseRefsCell "-" === Right []
      , parseRefsCell "ref/one" === Right [SourceRef "ref/one"]
      , parseRefsCell "ref/a,ref/b" === Right [SourceRef "ref/a", SourceRef "ref/b"]
      , rejected (renderRefsCell [SourceRef "-"])
      , rejected (renderRefsCell [SourceRef "a,b"])
      , rejected (parseRefsCell "")
      , rejected (parseRefsCell "-,ref")
      , rejected (parseRefsCell "ref,-")
      , rejected (parseRefsCell "ref,,other")
      ]

prop_unknownSubjectType :: Property
prop_unknownSubjectType =
  once $
    rejected
      ( parseObjectJudgments
          ( objectHeader
              ++ "s1\tu1\tattack\tformal\tprose\t-\tfaithful\tbecause\t-\n"
          )
      )

prop_generatedFieldDrift :: Property
prop_generatedFieldDrift =
  once $
    case parseObjectJudgments objectDocument of
      Left err -> counterexample (auditErrorMessage err) False
      Right judgments ->
        conjoin
          [ rejected (validateObjectJudgments records (changeFirst (\j -> j {objectJudgmentUnit = "other"}) judgments))
          , driftContains
              "subject_type differs from generated value strict-step"
              (changeFirst (\j -> j {objectJudgmentType = AuditTypedAttack}) judgments)
          , rejected (validateObjectJudgments records (changeFirst (\j -> j {objectJudgmentFormalObject = "changed"}) judgments))
          , rejected (validateObjectJudgments records (changeFirst (\j -> j {objectJudgmentProseContext = "changed"}) judgments))
          , driftContains
              "refs differs from generated value ref/one"
              (changeFirst (\j -> j {objectJudgmentRefs = []}) judgments)
          , acceptedRight (validateObjectJudgments records judgments)
          ]
  where
    driftContains expected submitted =
      case validateObjectJudgments records submitted of
        Left auditError ->
          counterexample (auditErrorMessage auditError) $
            property (expected `isInfixOf` auditErrorMessage auditError)
        Right validated ->
          counterexample ("unexpected acceptance: " ++ show validated) False

prop_worklistValidation :: Property
prop_worklistValidation =
  once $
    let exact = bindingAuditTsv records
        drifted = replaceOnce "formal-e1" "changed" exact
        dropped = unlines (init (lines exact))
        extra = exact ++ last (lines exact) ++ "\n"
     in conjoin
          [ acceptedRight (validateWorklist records (asciiBytes exact))
          , case validateWorklist records (asciiBytes drifted) of
              Left auditError ->
                counterexample (auditErrorMessage auditError) $
                  property
                    ( "worklist: row 2, key \"u1/e1\":"
                        `isPrefixOf` auditErrorMessage auditError
                    )
              Right () -> counterexample "unexpected worklist acceptance" False
          , driftStartsWith
              "worklist: row 4, key \"u2/e3\":"
              dropped
          , driftStartsWith
              "worklist: row 5, key \"u2/e3\":"
              extra
          , rejected (validateWorklist records (BS.pack [0xff, 0x0a]))
          ]
  where
    driftStartsWith expected document =
      case validateWorklist records (asciiBytes document) of
        Left auditError ->
          counterexample (auditErrorMessage auditError) $
            property (expected `isPrefixOf` auditErrorMessage auditError)
        Right () -> counterexample "unexpected worklist acceptance" False

prop_invalidUtf8 :: Property
prop_invalidUtf8 =
  once $
    conjoin
      [ decodeAuditUtf8 AuditLeafResultsFile (asciiBytes "foo") === Right "foo"
      , invalidUtf8Role AuditLeafResultsFile "leaf results"
      , invalidUtf8Role AuditObjectResultsFile "object results"
      , invalidUtf8Role AuditWorklistFile "worklist"
      ]
  where
    invalidUtf8Role role expectedRole =
      case decodeAuditUtf8 role (BS.pack [0xff, 0x0a]) of
        Left auditError ->
          counterexample (auditErrorMessage auditError) $
            property ((expectedRole ++ ": invalid UTF-8") == auditErrorMessage auditError)
        Right decoded -> counterexample decoded False

prop_errorContext :: Property
prop_errorContext =
  once $
    case parseLeafJudgments (leafDocument "invalid" "because" "-") of
      Left auditError ->
        let message = auditErrorMessage auditError
         in counterexample message $
              property
                ( "leaf results: row 2, key \"u1/e1\":" `isPrefixOf` message
                    && "invalid classification" `isInfixOf` message
                    && not ("binding-audit:" `isPrefixOf` message)
                )
      Right judgments -> counterexample (show judgments) False

prop_objectDenominator :: Property
prop_objectDenominator =
  once $
    conjoin
      ( acceptedRight (validateObjectDenominator summaryRecords)
          : [ case validateObjectDenominator variantRecords of
                Left (AuditObjectDenominatorMismatch totalCount strictCount attackCount) ->
                  counterexample (show (name, totalCount, strictCount, attackCount)) $
                    (totalCount, strictCount, attackCount) === expectedCounts
                Left other ->
                  counterexample
                    ("wrong denominator error for " ++ name ++ ": " ++ show other)
                    False
                Right () ->
                  counterexample
                    ("invalid denominator accepted: " ++ name)
                    False
            | (name, expectedCounts, variantRecords) <- objectDenominatorVariants
            ]
      )

prop_summaryAggregation :: Property
prop_summaryAggregation =
  once $
    case syntheticSummary summaryRecords of
      Left auditError -> counterexample (auditErrorMessage auditError) False
      Right auditSummary ->
        let leaves = summaryLeaves auditSummary
            kinds = summaryByKind auditSummary
            statuses = summaryByStatus auditSummary
            objects = summaryObjects auditSummary
         in counterexample (show auditSummary) $
              conjoin
                [ leaves === AuditCounts 5 2 2 1
                , property (countsClose leaves)
                , map fst kinds === [Attested, Observed]
                , foldCounts (map snd kinds) === leaves
                , lookup Attested kinds === Just (AuditCounts 3 0 2 1)
                , lookup Observed kinds === Just (AuditCounts 2 2 0 0)
                , summaryPaperAnchored auditSummary === AuditCounts 3 1 1 1
                , map fst statuses === [Justified, Gap, Defeated, Contested]
                , lookup Justified statuses === Just (AuditCounts 2 1 1 0)
                , lookup Gap statuses === Just (AuditCounts 2 1 1 0)
                , lookup Defeated statuses === Just (AuditCounts 1 0 0 1)
                , lookup Contested statuses === Just (AuditCounts 0 0 0 0)
                , property (all countsClose (map snd statuses))
                , map fst objects === [AuditStrictStep, AuditTypedAttack]
                , lookup AuditStrictStep objects === Just (AuditCounts 1 1 0 0)
                , lookup AuditTypedAttack objects === Just (AuditCounts 3 1 1 1)
                , foldCounts (map snd objects) === AuditCounts 4 2 1 1
                ]

prop_summaryJoinFailures :: Property
prop_summaryJoinFailures =
  once $
    let zeroStatus =
          changeFirst (\record -> record {urStatuses = []}) summaryRecords
        multipleStatuses =
          changeFirst
            (\record -> record {urStatuses = [Justified, Gap]})
            summaryRecords
        duplicate =
          summaryRecords
            ++ [(emptyRecord "u-contested" [] []) {urStatuses = [Contested]}]
        unsupportedKind =
          changeFirst
            ( \record ->
                record
                  { urBindingAuditRows =
                      changeFirst
                        ( \row ->
                            row
                              { barLeaf =
                                  (barLeaf row) {lfKind = Assumed}
                              }
                        )
                        (urBindingAuditRows record)
                  }
            )
            summaryRecords
     in conjoin
          [ summaryRejected "u-justified" "exactly one requested status" zeroStatus
          , summaryRejected "u-justified" "exactly one requested status" multipleStatuses
          , summaryRejected "u-contested" "duplicate unit" duplicate
          , summaryRejectedParts
              ["u-justified", "e-justified", "assumed"]
              unsupportedKind
          ]

prop_summaryJsonGolden :: Property
prop_summaryJsonGolden =
  once $
    case syntheticSummary summaryRecords of
      Left auditError -> counterexample (auditErrorMessage auditError) False
      Right auditSummary ->
        renderAuditSummary goldenIdentity auditSummary === summaryJsonGolden

countsClose :: AuditCounts -> Bool
countsClose counts =
  countAudited counts
    == countFaithful counts
      + countUnfaithful counts
      + countUnderdetermined counts

foldCounts :: [AuditCounts] -> AuditCounts
foldCounts =
  foldr
    ( \left right ->
        AuditCounts
          { countAudited = countAudited left + countAudited right
          , countFaithful = countFaithful left + countFaithful right
          , countUnfaithful = countUnfaithful left + countUnfaithful right
          , countUnderdetermined =
              countUnderdetermined left + countUnderdetermined right
          }
    )
    (AuditCounts 0 0 0 0)

summaryRejected :: String -> String -> [UnitRecord] -> Property
summaryRejected unit problem inputRecords =
  case syntheticSummary inputRecords of
    Left auditError ->
      let message = auditErrorMessage auditError
       in counterexample message $
            property (unit `isInfixOf` message && problem `isInfixOf` message)
    Right auditSummary ->
      counterexample ("unexpected summary: " ++ show auditSummary) False

summaryRejectedParts :: [String] -> [UnitRecord] -> Property
summaryRejectedParts expectedParts inputRecords =
  case syntheticSummary inputRecords of
    Left auditError ->
      let message = auditErrorMessage auditError
       in counterexample message $
            property (all (`isInfixOf` message) expectedParts)
    Right auditSummary ->
      counterexample ("unexpected summary: " ++ show auditSummary) False

syntheticSummary :: [UnitRecord] -> Either AuditError AuditSummary
syntheticSummary inputRecords = do
  leafJudgments <- parseLeafJudgments summaryLeafDocument
  objectJudgments <- parseObjectJudgments summaryObjectDocument
  summarizeAudit
    inputRecords
    (utf8Bytes (bindingAuditTsv inputRecords))
    leafJudgments
    objectJudgments

summaryRecords :: [UnitRecord]
summaryRecords =
  [ summaryRecord
      "u-justified"
      Justified
      [ leafRowWith "e-justified" Attested True
      , leafRowWith "e-justified-observed" Observed True
      ]
      [ summarySubject "strict-1" AuditStrictStep "strict formal"
      , summarySubject "attack-1" AuditTypedAttack "attack formal 1"
      ]
  , summaryRecord
      "u-gap"
      Gap
      [ leafRowWith "e-gap" Observed False
      , leafRowWith "e-gap-unfaithful" Attested False
      ]
      [summarySubject "attack-2" AuditTypedAttack "attack formal 2"]
  , summaryRecord
      "u-defeated"
      Defeated
      [leafRowWith "e-defeated" Attested True]
      [summarySubject "attack-3" AuditTypedAttack "attack formal 3"]
  , summaryRecord "u-contested" Contested [] []
  ]

objectDenominatorVariants :: [(String, (Int, Int, Int), [UnitRecord])]
objectDenominatorVariants =
  [ ("missing", (3, 1, 2), changeFirst removeAuditSubject summaryRecords)
  , ("extra", (5, 1, 4), changeFirst addAuditSubject summaryRecords)
  , ("wrong-split", (4, 2, 2), changeFirst changeAuditSubjectSplit summaryRecords)
  ]

removeAuditSubject :: UnitRecord -> UnitRecord
removeAuditSubject record =
  case urBindingAuditSubjects record of
    first : _ : rest ->
      record {urBindingAuditSubjects = first : rest}
    _ -> error "denominator fixture needs at least two subjects"

addAuditSubject :: UnitRecord -> UnitRecord
addAuditSubject record =
  record
    { urBindingAuditSubjects =
        urBindingAuditSubjects record
          ++ [summarySubject "attack-extra" AuditTypedAttack "attack formal extra"]
    }

changeAuditSubjectSplit :: UnitRecord -> UnitRecord
changeAuditSubjectSplit record =
  case urBindingAuditSubjects record of
    first : second : rest ->
      record
        { urBindingAuditSubjects =
            first : second {auditSubjectType = AuditStrictStep} : rest
        }
    _ -> error "denominator fixture needs at least two subjects"

summaryRecord
  :: String
  -> Status
  -> [BindingAuditRow]
  -> [AuditSubject]
  -> UnitRecord
summaryRecord unit status rows subjects =
  (emptyRecord unit rows subjects) {urStatuses = [status]}

leafRowWith :: String -> LeafKind -> Bool -> BindingAuditRow
leafRowWith leafId kind paperAnchored =
  let row = leafRow leafId ("formal-" ++ leafId)
      leaf = barLeaf row
   in row
        { barLeaf =
            leaf
              { lfKind = kind
              , lfPaperAnchored = paperAnchored
              }
        }

summarySubject :: String -> AuditSubjectType -> String -> AuditSubject
summarySubject subjectId subjectType formal =
  subject subjectId subjectType formal ("prose " ++ subjectId) []

summaryLeafDocument :: String
summaryLeafDocument =
  leafHeader
    ++ "u-justified\te-justified\tunfaithful\tmismatch\twrong binding\n"
    ++ "u-justified\te-justified-observed\tfaithful\tchecked\t-\n"
    ++ "u-gap\te-gap\tfaithful\tchecked\t-\n"
    ++ "u-gap\te-gap-unfaithful\tunfaithful\tmismatch\twrong binding\n"
    ++ "u-defeated\te-defeated\tunderdetermined\tinsufficient\t-\n"

summaryObjectDocument :: String
summaryObjectDocument =
  objectHeader
    ++ "strict-1\tu-justified\tstrict-step\tstrict formal\tprose strict-1\t-\tfaithful\tchecked\t-\n"
    ++ "attack-1\tu-justified\ttyped-attack\tattack formal 1\tprose attack-1\t-\tunfaithful\tmismatch\twrong binding\n"
    ++ "attack-2\tu-gap\ttyped-attack\tattack formal 2\tprose attack-2\t-\tunderdetermined\tinsufficient\t-\n"
    ++ "attack-3\tu-defeated\ttyped-attack\tattack formal 3\tprose attack-3\t-\tfaithful\tchecked\t-\n"

summaryWorklistBytes, summaryLeafBytes, summaryObjectBytes :: BS.ByteString
summaryWorklistBytes = utf8Bytes (bindingAuditTsv summaryRecords)
summaryLeafBytes = utf8Bytes summaryLeafDocument
summaryObjectBytes = utf8Bytes summaryObjectDocument

goldenIdentity :: InputIdentity
goldenIdentity =
  InputIdentity
    { inputObjectFormat = GitObjectSha256
    , inputWorklistDigest = "worklist-digest"
    , inputLeafResultsDigest = "leaf-digest"
    , inputObjectResultsDigest = "object-digest"
    }

summaryJsonGolden :: String
summaryJsonGolden =
  unlines
    [ "{"
    , "  \"schema\": \"lara-binding-audit@0.1\","
    , "  \"corpus\": {"
    , "    \"seed\": 20260801,"
    , "    \"units\": 4"
    , "  },"
    , "  \"inputs\": {"
    , "    \"object-format\": \"sha256\","
    , "    \"worklist\": \"worklist-digest\","
    , "    \"leaf-results\": \"leaf-digest\","
    , "    \"object-results\": \"object-digest\""
    , "  },"
    , "  \"leaves\": {"
    , "    \"audited\": 5,"
    , "    \"faithful\": 2,"
    , "    \"unfaithful\": 2,"
    , "    \"underdetermined\": 1"
    , "  },"
    , "  \"by-kind\": {"
    , "    \"attested\": {"
    , "      \"audited\": 3,"
    , "      \"faithful\": 0,"
    , "      \"unfaithful\": 2,"
    , "      \"underdetermined\": 1"
    , "    },"
    , "    \"observed\": {"
    , "      \"audited\": 2,"
    , "      \"faithful\": 2,"
    , "      \"unfaithful\": 0,"
    , "      \"underdetermined\": 0"
    , "    }"
    , "  },"
    , "  \"paper-anchored\": {"
    , "    \"audited\": 3,"
    , "    \"faithful\": 1,"
    , "    \"unfaithful\": 1,"
    , "    \"underdetermined\": 1"
    , "  },"
    , "  \"by-requested-status\": {"
    , "    \"justified\": {"
    , "      \"audited\": 2,"
    , "      \"faithful\": 1,"
    , "      \"unfaithful\": 1,"
    , "      \"underdetermined\": 0"
    , "    },"
    , "    \"gap\": {"
    , "      \"audited\": 2,"
    , "      \"faithful\": 1,"
    , "      \"unfaithful\": 1,"
    , "      \"underdetermined\": 0"
    , "    },"
    , "    \"defeated\": {"
    , "      \"audited\": 1,"
    , "      \"faithful\": 0,"
    , "      \"unfaithful\": 0,"
    , "      \"underdetermined\": 1"
    , "    },"
    , "    \"contested\": {"
    , "      \"audited\": 0,"
    , "      \"faithful\": 0,"
    , "      \"unfaithful\": 0,"
    , "      \"underdetermined\": 0"
    , "    }"
    , "  },"
    , "  \"objects\": {"
    , "    \"strict-step\": {"
    , "      \"audited\": 1,"
    , "      \"faithful\": 1,"
    , "      \"unfaithful\": 0,"
    , "      \"underdetermined\": 0"
    , "    },"
    , "    \"typed-attack\": {"
    , "      \"audited\": 3,"
    , "      \"faithful\": 1,"
    , "      \"unfaithful\": 1,"
    , "      \"underdetermined\": 1"
    , "    }"
    , "  }"
    , "}"
    ]

asciiBytes :: String -> BS.ByteString
asciiBytes = BS.pack . map (fromIntegral . fromEnum)

records :: [UnitRecord]
records =
  [ emptyRecord
      "u1"
      [leafRow "e1" "formal-e1", leafRow "e2" "formal-e2"]
      [ subject "s1" AuditStrictStep "formal one" "prose one" [SourceRef "ref/one"]
      , subject "s2" AuditTypedAttack "formal two" "prose two" []
      ]
  , emptyRecord
      "u2"
      [leafRow "e3" "formal-e3"]
      [ subject "s3" AuditTypedAttack "formal three" "prose three" [SourceRef "ref/a", SourceRef "ref/b"]
      , subject "s4" AuditTypedAttack "formal four" "prose four" [SourceRef "ref/four"]
      ]
  ]

emptyRecord :: String -> [BindingAuditRow] -> [AuditSubject] -> UnitRecord
emptyRecord unit rows subjects =
  UnitRecord
    { urName = unit
    , urStatuses = []
    , urBindingAuditRows = rows
    , urBindingAuditSubjects = subjects
    , urAllLeaves = []
    , urTypedAttacks = 0
    , urDeadEndAttacks = 0
    , urStrictSteps = 0
    , urStrictCertified = 0
    , urStrictFlavored = False
    }

leafRow :: String -> String -> BindingAuditRow
leafRow leafId formal =
  BindingAuditRow
    { barLeaf =
        LeafFact
          { lfId = LeafId leafId
          , lfProvenance = AiExecuted
          , lfKind = Observed
          , lfPaperAnchored = False
          , lfRefs = []
          }
    , barFormalTarget = Prop (Pred formal) []
    , barRole = AuditSupport
    , barClaimId = PropId "claim"
    , barClaimNl = "claim prose"
    }

subject :: String -> AuditSubjectType -> String -> String -> [SourceRef] -> AuditSubject
subject sid subjectType formal prose refs =
  AuditSubject
    { auditSubjectId = AuditSubjectId sid
    , auditSubjectType = subjectType
    , auditSubjectFormalObject = formal
    , auditSubjectProseContext = prose
    , auditSubjectRefs = refs
    }

changeFirst :: (a -> a) -> [a] -> [a]
changeFirst _ [] = []
changeFirst f (x : xs) = f x : xs

replaceLfWithCrlf :: String -> String
replaceLfWithCrlf = concatMap (\c -> if c == '\n' then "\r\n" else [c])

replaceOnce :: String -> String -> String -> String
replaceOnce needle replacement haystack = go haystack
  where
    go [] = []
    go rest
      | needle `prefixOf` rest = replacement ++ drop (length needle) rest
    go (c : rest) = c : go rest

    prefixOf [] _ = True
    prefixOf _ [] = False
    prefixOf (a : as) (b : bs) = a == b && prefixOf as bs

rejected :: Show a => Either e a -> Property
rejected (Left _) = property True
rejected (Right value) = counterexample ("unexpected acceptance: " ++ show value) False

acceptedRight :: Show e => Either e a -> Property
acceptedRight (Right _) = property True
acceptedRight (Left err) = counterexample ("unexpected rejection: " ++ show err) False

prop_prepareExactPacket :: Property
prop_prepareExactPacket =
  once $ ioProperty $ withTempDirectory "binding-audit-prepare" $ \parent -> do
    let destination = parent </> "packet"
        worklist = utf8Bytes (bindingAuditTsv records)
        auditIO = productionAuditIO {readAuditBytes = \_ -> pure worklist}
    prepareAuditPacketWith auditIO destination records
    names <- sort <$> listDirectory destination
    copiedWorklist <- BS.readFile (destination </> "worklist.tsv")
    leafTemplate <- BS.readFile (destination </> "results.tsv")
    objectTemplate <- BS.readFile (destination </> "object-results.tsv")
    pure $
      counterexample (show names) $
        conjoin
          [ names === ["object-results.tsv", "results.tsv", "worklist.tsv"]
          , copiedWorklist === worklist
          , leafTemplate === utf8Bytes (renderLeafTemplate records)
          , Right objectTemplate === (utf8Bytes <$> renderObjectTemplate records)
          ]

prop_prepareRejectsStaleWorklist :: Property
prop_prepareRejectsStaleWorklist =
  once $ ioProperty $ withTempDirectory "binding-audit-stale" $ \parent -> do
    let destination = parent </> "packet"
        stale = utf8Bytes (replaceOnce "formal-e1" "stale" (bindingAuditTsv records))
        auditIO = productionAuditIO {readAuditBytes = \_ -> pure stale}
    failed <- actionFails (prepareAuditPacketWith auditIO destination records)
    created <- doesPathExist destination
    pure (counterexample "stale worklist created a packet" (property (failed && not created)))

prop_packetReadErrorsCarryContext :: Property
prop_packetReadErrorsCarryContext =
  once $ ioProperty $ withTempDirectory "binding-audit-read-context" $ \parent -> do
    let packet = parent </> "packet"
        worklistBytes = utf8Bytes (bindingAuditTsv records)
        leafBytes = utf8Bytes (completedLeafDocument records)
        objectBytes = utf8Bytes (completedObjectDocument records)
        packetInputs =
          [ (packet </> "worklist.tsv", worklistBytes, "read packet worklist")
          , (packet </> "results.tsv", leafBytes, "read leaf-results")
          , (packet </> "object-results.tsv", objectBytes, "read object-results")
          , (bindingAuditPath, worklistBytes, "read committed worklist")
          ]
        injectedRead failedPath path
          | path == failedPath =
              ioError (userError ("injected read failure: " ++ path))
          | otherwise =
              case [bytes | (candidate, bytes, _) <- packetInputs, candidate == path] of
                [bytes] -> pure bytes
                _ -> ioError (userError ("unexpected audit read: " ++ path))
    prepareFailure <-
      actionError
        ( prepareAuditPacketWith
            productionAuditIO
              { readAuditBytes =
                  \path -> ioError (userError ("injected read failure: " ++ path))
              }
            (parent </> "prepared")
            records
        )
    validationFailures <-
      forM packetInputs $ \(failedPath, _, expectedContext) -> do
        failure <-
          actionError
            ( validateAuditPacketWith
                productionAuditIO {readAuditBytes = injectedRead failedPath}
                packet
                records
            )
        pure
          ( failedPath
          , maybe
              False
              (\message -> expectedContext `isInfixOf` message && failedPath `isInfixOf` message)
              failure
          )
    pure $
      counterexample (show (prepareFailure, validationFailures)) $
        property
          ( maybe
              False
              (\message -> "read committed worklist" `isInfixOf` message && bindingAuditPath `isInfixOf` message)
              prepareFailure
              && all snd validationFailures
          )

prop_productionAuditIO :: Property
prop_productionAuditIO =
  once $ ioProperty $ withTempDirectory "binding-audit-production-io" $ \parent -> do
    let atomicTarget = parent </> "atomic.bin"
        sourceTarget = parent </> "source.bin"
        payload = BS.pack [0x00, 0xff, 0x80, 0x0a, 0x41]
    atomicWriteAuditBytes productionAuditIO atomicTarget payload
    BS.writeFile sourceTarget payload
    atomicBytes <- BS.readFile atomicTarget
    objectFormatResult <- discoverObjectFormat productionAuditIO
    hashResult <- hashAuditBytes productionAuditIO payload
    (expectedCode, expectedStdout, expectedStderr) <-
      readProcessWithExitCode "git" ["hash-object", sourceTarget] ""
    names <- sort <$> listDirectory parent
    pure $
      counterexample
        (show (objectFormatResult, hashResult, expectedCode, expectedStdout, expectedStderr, names))
        ( conjoin
            [ atomicBytes === payload
            , names === ["atomic.bin", "source.bin"]
            , auditCommandExitCode objectFormatResult === ExitSuccess
            , property (auditCommandStdout objectFormatResult `elem` map asciiBytes ["sha1\n", "sha256\n"])
            , auditCommandStderr objectFormatResult === BS.empty
            , auditCommandExitCode hashResult === expectedCode
            , auditCommandStdout hashResult === asciiBytes expectedStdout
            , auditCommandStderr hashResult === asciiBytes expectedStderr
            ]
        )

prop_packetTemplateShape :: Property
prop_packetTemplateShape =
  once $ ioProperty $ do
    loaded <- loadAuditRecords
    let blind = map statusBlind loaded
        leafRows = parseTsv 5 (renderLeafTemplate blind)
        objectRows =
          either
            (error . auditErrorMessage)
            (parseTsv 9)
            (renderObjectTemplate blind)
        expectedLeafKeys =
          [ [urName record, rawLeafId]
          | record <- blind
          , row <- urBindingAuditRows record
          , let LeafId rawLeafId = lfId (barLeaf row)
          ]
        expectedObjectKeys =
          [ rawSubjectId
          | record <- blind
          , auditSubject <- urBindingAuditSubjects record
          , let AuditSubjectId rawSubjectId = auditSubjectId auditSubject
          ]
    pure $ case (leafRows, objectRows) of
      (Right (leafColumns : leafData), Right (objectColumns : objectData)) ->
        counterexample (show (length leafData, length objectData)) $
          conjoin
            [ length leafData === 38
            , length objectData === 4
            , map (take 2) leafData === expectedLeafKeys
            , map (take 1) objectData === map (: []) expectedObjectKeys
            , property ("status" `notElem` leafColumns)
            , property ("status" `notElem` objectColumns)
            , property (all ((== 5) . length) leafData)
            , property (all ((== 9) . length) objectData)
            ]
      other -> counterexample (show other) False

prop_prepareNoClobber :: Property
prop_prepareNoClobber =
  once $ ioProperty $ withTempDirectory "binding-audit-no-clobber" $ \parent -> do
    let emptyDestination = parent </> "empty"
        fullDestination = parent </> "full"
        marker = fullDestination </> "keep"
        exact = utf8Bytes (bindingAuditTsv records)
        auditIO = productionAuditIO {readAuditBytes = \_ -> pure exact}
    createDirectory emptyDestination
    createDirectory fullDestination
    BS.writeFile marker (asciiBytes "unchanged")
    emptyFailed <- actionFails (prepareAuditPacketWith auditIO emptyDestination records)
    fullFailed <- actionFails (prepareAuditPacketWith auditIO fullDestination records)
    emptyNames <- listDirectory emptyDestination
    fullNames <- listDirectory fullDestination
    markerBytes <- BS.readFile marker
    pure $
      conjoin
        [ property emptyFailed
        , property fullFailed
        , emptyNames === []
        , fullNames === ["keep"]
        , markerBytes === asciiBytes "unchanged"
        ]

prop_prepareTrailingSeparator :: Property
prop_prepareTrailingSeparator =
  once $ ioProperty $ withTempDirectory "binding-audit-trailing-separator" $ \parent -> do
    let destination = parent </> "packet"
        spelledDestination = addTrailingPathSeparator destination
        exact = utf8Bytes (bindingAuditTsv records)
        auditIO = productionAuditIO {readAuditBytes = \_ -> pure exact}
    prepareAuditPacketWith auditIO spelledDestination records
    names <- sort <$> listDirectory destination
    pure $
      counterexample (show names) $
        names === sort packetFileNames

prop_forbiddenDestinations :: Property
prop_forbiddenDestinations =
  once $ ioProperty $ withTempDirectory "binding-audit-alias" $ \parent -> do
    canonicalRoot <- canonicalizePath bindingAuditDirectory
    let relativeDestination = bindingAuditDirectory </> ".task3-relative-forbidden"
        absoluteDestination = canonicalRoot </> ".task3-absolute-forbidden"
        dotDotDestination =
          canonicalRoot </> ".." </> "binding-audit" </> ".task3-dotdot-forbidden"
        link = parent </> "committed-link"
        linkedDestination = link </> ".task3-symlink-forbidden"
        destinations =
          [ relativeDestination
          , absoluteDestination
          , dotDotDestination
          , linkedDestination
          ]
    createDirectoryLink canonicalRoot link
    failures <- mapM (actionFails . validatePacketDestination productionAuditIO) destinations
    created <- mapM doesPathExist destinations
    pure $
      counterexample (show (failures, created)) $
        property (and failures && not (or created))

prop_renderBeforeCreate :: Property
prop_renderBeforeCreate =
  once $ ioProperty $ withTempDirectory "binding-audit-render" $ \parent -> do
    let invalidRefsRecords =
          changeFirst
            ( \record ->
                record
                  { urBindingAuditSubjects =
                      changeFirst
                        (\auditSubject -> auditSubject {auditSubjectRefs = [SourceRef "-"]})
                        (urBindingAuditSubjects record)
                  }
            )
            records
        lateBottomRecords =
          reverse
            ( changeFirst
                ( \record ->
                    record
                      { urBindingAuditSubjects =
                          reverse
                            ( changeFirst
                                ( \auditSubject ->
                                    auditSubject
                                      { auditSubjectProseContext =
                                          error "late object-template render failure"
                                      }
                                )
                                (reverse (urBindingAuditSubjects record))
                            )
                      }
                )
                (reverse records)
            )
        cases =
          [ ("invalid refs", invalidRefsRecords)
          , ("late render bottom", lateBottomRecords)
          ]
    outcomes <-
      forM cases $ \(caseName, badRecords) -> do
        let destination = parent </> caseName
            exact = utf8Bytes (bindingAuditTsv badRecords)
            auditIO = productionAuditIO {readAuditBytes = \_ -> pure exact}
        failed <- actionFails (prepareAuditPacketWith auditIO destination badRecords)
        created <- doesPathExist destination
        pure (caseName, failed && not created)
    pure (counterexample (show (map fst outcomes)) (property (all snd outcomes)))

prop_transactionalWriteFailures :: Property
prop_transactionalWriteFailures =
  once $ ioProperty $ withTempDirectory "binding-audit-writes" $ \parent -> do
    outcomes <-
      forM packetFileNames $ \failedName -> do
        let destination = parent </> ("packet-" ++ failedName)
            originalMessage = "injected write failure: " ++ failedName
            exact = utf8Bytes (bindingAuditTsv records)
            auditIO =
              productionAuditIO
                { readAuditBytes = \_ -> pure exact
                , writeAuditBytes = \path bytes ->
                    if takeFileName path == failedName
                      then ioError (userError originalMessage)
                      else BS.writeFile path bytes
                , removeAuditDirectory = \path -> do
                    removePathForcibly path
                    ioError (userError "injected cleanup failure after removal")
                }
        result <- try (prepareAuditPacketWith auditIO destination records)
        remains <- doesPathExist destination
        pure $ case result of
          Left ioException ->
            ioeGetErrorString ioException == originalMessage && not remains
          Right () -> False
    pure (counterexample (show outcomes) (property (and outcomes)))

prop_validateReadOnlyStatusBlind :: Property
prop_validateReadOnlyStatusBlind =
  once $ ioProperty $ withTempDirectory "binding-audit-validate" $ \parent -> do
    loaded <- loadAuditRecords
    let destination = parent </> "packet"
        blind = map statusBlind loaded
    writeCompletedPacket destination loaded
    before <- packetSnapshot destination
    result <- try (validateAuditPacket destination blind) :: IO (Either SomeException ())
    after <- packetSnapshot destination
    pure $ case result of
      Left exception ->
        counterexample ("validation failed or forced status: " ++ show exception) False
      Right () ->
        counterexample "validation wrote to the packet" (before === after)

prop_validateMalformedPackets :: Property
prop_validateMalformedPackets =
  once $ ioProperty $ withTempDirectory "binding-audit-malformed" $ \parent -> do
    loaded <- loadAuditRecords
    let validLeaf = completedLeafDocument loaded
        validObject = completedObjectDocument loaded
        malformedDocuments =
          [ ("classification", mutateCell 5 1 2 "Faithful" validLeaf, validObject)
          , ("justification", mutateCell 5 1 3 "" validLeaf, validObject)
          , ("divergence_note", mutateCell 5 1 4 "unexpected" validLeaf, validObject)
          , ("generated", validLeaf, mutateCell 9 1 3 "changed formal object" validObject)
          , ("key", mutateCell 5 1 1 "unknown-leaf" validLeaf, validObject)
          , ("header", mutateCell 5 0 0 "other-unit" validLeaf, validObject)
          , ("grammar", init validLeaf, validObject)
          , ("order", swapFirstDataRows 5 validLeaf, validObject)
          ]
    outcomes <-
      forM malformedDocuments $ \(caseName, leafDocumentBytes, objectDocumentBytes) -> do
        let destination = parent </> caseName
        writePacket destination loaded leafDocumentBytes objectDocumentBytes
        actionFails (validateAuditPacket destination loaded)
    pure (counterexample (show (zip (map (\(caseName, _, _) -> caseName) malformedDocuments) outcomes)) (property (and outcomes)))

prop_validateRejectsStaleDenominator :: Property
prop_validateRejectsStaleDenominator =
  once $ ioProperty $ withTempDirectory "binding-audit-denominator" $ \parent -> do
    loaded <- loadAuditRecords
    let destination = parent </> "packet"
        staleRecords = loaded ++ [emptyRecord "stale-extra-unit" [leafRow "stale" "stale"] []]
    writeCompletedPacket destination loaded
    failed <- actionFails (validateAuditPacket destination staleRecords)
    pure (counterexample "stale committed denominator was accepted" (property failed))

prop_validateRejectsInvalidUtf8 :: Property
prop_validateRejectsInvalidUtf8 =
  once $ ioProperty $ withTempDirectory "binding-audit-utf8" $ \parent -> do
    loaded <- loadAuditRecords
    outcomes <-
      forM packetFileNames $ \failedName -> do
        let destination = parent </> failedName
        writeCompletedPacket destination loaded
        BS.writeFile (destination </> failedName) (BS.pack [0xff, 0x0a])
        before <- packetSnapshot destination
        failed <- actionFails (validateAuditPacket destination loaded)
        after <- packetSnapshot destination
        pure (failed && before == after)
    pure (counterexample (show outcomes) (property (and outcomes)))

prop_validateRejectsDuplicateUnits :: Property
prop_validateRejectsDuplicateUnits =
  once $ ioProperty $ do
    readCalls <- newIORef (0 :: Int)
    let duplicateRecords =
          summaryRecords
            ++ [(emptyRecord "u-contested" [] []) {urStatuses = error "status forced during duplicate-unit validation"}]
        auditIO =
          productionAuditIO
            { readAuditBytes = \_ -> do
                modifyIORef' readCalls (+ 1)
                ioError (userError "validation read before duplicate-unit check")
            }
    failure <-
      actionError
        (validateAuditPacketWith auditIO "unused-packet" duplicateRecords)
    calls <- readIORef readCalls
    pure $
      counterexample (show (failure, calls)) $
        property
          ( maybe
              False
              (\message -> "duplicate unit" `isInfixOf` message && "u-contested" `isInfixOf` message)
              failure
              && calls == 0
          )

prop_objectDenominatorBoundaries :: Property
prop_objectDenominatorBoundaries =
  once $ ioProperty $ withTempDirectory "binding-audit-object-denominator" $ \parent -> do
    outcomes <-
      forM objectDenominatorVariants $ \(name, _, variantRecords) -> do
        let packetDestination = parent </> (name ++ "-packet")
            summaryDestination = parent </> (name ++ "-summary.json")
            prior = asciiBytes ("prior " ++ name ++ "\n")
            baseIO = validSummaryAuditIO summaryDestination
        prepareFailure <-
          actionError
            (prepareAuditPacketWith baseIO packetDestination variantRecords)
        packetCreated <- doesPathExist packetDestination
        validateFailure <-
          actionError
            (validateAuditPacket packetDestination (map statusBlind variantRecords))
        summaryEffects <- newIORef (0 :: Int)
        BS.writeFile summaryDestination prior
        let summaryIO =
              baseIO
                { discoverObjectFormat = do
                    modifyIORef' summaryEffects (+ 1)
                    discoverObjectFormat baseIO
                , hashAuditBytes = \bytes -> do
                    modifyIORef' summaryEffects (+ 1)
                    hashAuditBytes baseIO bytes
                , atomicWriteAuditBytes = \path bytes -> do
                    modifyIORef' summaryEffects (+ 1)
                    atomicWriteAuditBytes baseIO path bytes
                }
        summaryFailure <-
          actionError (summarizeAuditFilesWith summaryIO variantRecords)
        after <- BS.readFile summaryDestination
        effects <- readIORef summaryEffects
        let denominatorFailure =
              maybe False ("object denominator" `isInfixOf`)
        pure
          ( name
          , denominatorFailure prepareFailure
              && not packetCreated
              && denominatorFailure validateFailure
              && denominatorFailure summaryFailure
              && after == prior
              && effects == 0
          )
    pure (counterexample (show outcomes) (property (all snd outcomes)))

prop_summarizeValidationBeforeWrite :: Property
prop_summarizeValidationBeforeWrite =
  once $ ioProperty $ withTempDirectory "binding-audit-summary-validate" $ \parent -> do
    let destination = parent </> "summary.json"
        prior = BS.pack [0x70, 0x72, 0x69, 0x6f, 0x72, 0x0a]
        validIO = validSummaryAuditIO destination
        staleWorklistBytes =
          utf8Bytes
            (replaceOnce "formal-e-justified" "stale" (bindingAuditTsv summaryRecords))
        invalidInputs =
          [ ( "stale worklist"
            , staleWorklistBytes
            , summaryLeafBytes
            , summaryObjectBytes
            )
          , ( "malformed leaf results"
            , summaryWorklistBytes
            , utf8Bytes (replaceOnce "unfaithful" "Unfaithful" summaryLeafDocument)
            , summaryObjectBytes
            )
          , ( "malformed object results"
            , summaryWorklistBytes
            , summaryLeafBytes
            , utf8Bytes (replaceOnce "strict-step" "other-step" summaryObjectDocument)
            )
          ]
    BS.writeFile destination prior
    summarizeAuditFilesWith validIO summaryRecords
    exact <- BS.readFile destination
    let expected = utf8Bytes (renderAuditSummary injectedIdentity (summaryOrDie summaryRecords))
    failures <-
      forM invalidInputs $ \(caseName, worklistBytes, leafBytes, objectBytes) -> do
        BS.writeFile destination prior
        let auditIO =
              summaryAuditIO
                destination
                worklistBytes
                leafBytes
                objectBytes
        failed <- actionFails (summarizeAuditFilesWith auditIO summaryRecords)
        after <- BS.readFile destination
        pure (caseName, failed && after == prior)
    BS.writeFile destination prior
    precedenceFailure <-
      actionError
        ( summarizeAuditFilesWith
            ( summaryAuditIO
                destination
                staleWorklistBytes
                (BS.pack [0xff, 0x0a])
                summaryObjectBytes
            )
            summaryRecords
        )
    precedenceAfter <- BS.readFile destination
    pure $
      counterexample (show (exact, expected, failures, precedenceFailure)) $
        conjoin
          [ leafResultsPath === "measurements/binding-audit/results.tsv"
          , objectResultsPath === "measurements/binding-audit/object-results.tsv"
          , summaryPath === "measurements/binding-audit/summary.json"
          , exact === expected
          , property (all snd failures)
          , property
              ( maybe
                  False
                  ( \message ->
                      "worklist:" `isInfixOf` message
                        && not ("invalid UTF-8" `isInfixOf` message)
                  )
                  precedenceFailure
                  && precedenceAfter == prior
              )
          ]

prop_summarizeAtomicFailure :: Property
prop_summarizeAtomicFailure =
  once $ ioProperty $ withTempDirectory "binding-audit-summary-atomic" $ \parent -> do
    let destination = parent </> "summary.json"
        prior = asciiBytes "prior summary\n"
        auditIO =
          (validSummaryAuditIO destination)
            { atomicWriteAuditBytes = \path bytes ->
                if path == summaryPath
                  then
                    atomicWriteWith destination $ \handle -> do
                      BS.hPut handle bytes
                      ioError (userError "injected atomic summary failure")
                  else ioError (userError ("unexpected audit write: " ++ path))
            }
    BS.writeFile destination prior
    failure <- actionError (summarizeAuditFilesWith auditIO summaryRecords)
    after <- BS.readFile destination
    names <- sort <$> listDirectory parent
    pure $
      counterexample (show (failure, after, names)) $
        property
          ( maybe False ("injected atomic summary failure" `isInfixOf`) failure
              && after == prior
              && names == ["summary.json"]
          )

prop_summarizeSha256Identity :: Property
prop_summarizeSha256Identity =
  once $ ioProperty $ withTempDirectory "binding-audit-summary-sha256" $ \parent -> do
    let destination = parent </> "summary.json"
        digest digit = replicate 64 digit
        hashResult digit =
          AuditCommandResult ExitSuccess (asciiBytes (digest digit ++ "\n")) BS.empty
        hashBytes bytes
          | bytes == summaryWorklistBytes = pure (hashResult 'a')
          | bytes == summaryLeafBytes = pure (hashResult 'b')
          | bytes == summaryObjectBytes = pure (hashResult 'c')
          | otherwise = ioError (userError "unexpected SHA-256 hash input")
        auditIO =
          (validSummaryAuditIO destination)
            { discoverObjectFormat =
                pure
                  ( AuditCommandResult
                      ExitSuccess
                      (asciiBytes "sha256\n")
                      BS.empty
                  )
            , hashAuditBytes = hashBytes
            }
        identity =
          InputIdentity
            { inputObjectFormat = GitObjectSha256
            , inputWorklistDigest = digest 'a'
            , inputLeafResultsDigest = digest 'b'
            , inputObjectResultsDigest = digest 'c'
            }
    summarizeAuditFilesWith auditIO summaryRecords
    actual <- BS.readFile destination
    pure $
      actual
        === utf8Bytes (renderAuditSummary identity (summaryOrDie summaryRecords))

prop_summarizeRawIdentities :: Property
prop_summarizeRawIdentities =
  once $ ioProperty $ withTempDirectory "binding-audit-summary-identity" $ \parent -> do
    let destination = parent </> "summary.json"

    hashedInputs <- newIORef []
    objectFormatResult <- discoverObjectFormat productionAuditIO
    worklistHash <- hashAuditBytes productionAuditIO summaryWorklistBytes
    leafHash <- hashAuditBytes productionAuditIO summaryLeafBytes
    objectHash <- hashAuditBytes productionAuditIO summaryObjectBytes
    let auditIO =
          (validSummaryAuditIO destination)
            { discoverObjectFormat = pure objectFormatResult
            , hashAuditBytes = \bytes -> do
                modifyIORef' hashedInputs (++ [bytes])
                hashAuditBytes productionAuditIO bytes
            }
        expectedIdentity =
          InputIdentity
            { inputObjectFormat = objectFormatOrDie objectFormatResult
            , inputWorklistDigest = commandLineOrDie worklistHash
            , inputLeafResultsDigest = commandLineOrDie leafHash
            , inputObjectResultsDigest = commandLineOrDie objectHash
            }
    summarizeAuditFilesWith auditIO summaryRecords
    actual <- BS.readFile destination
    calls <- readIORef hashedInputs
    let expected =
          utf8Bytes
            (renderAuditSummary expectedIdentity (summaryOrDie summaryRecords))
    pure $
      counterexample (show (calls, actual, expected)) $
        conjoin
          [ calls === [summaryWorklistBytes, summaryLeafBytes, summaryObjectBytes]
          , actual === expected
          ]

prop_summarizeObjectFormatFailures :: Property
prop_summarizeObjectFormatFailures =
  once $ ioProperty $ withTempDirectory "binding-audit-summary-format" $ \parent -> do
    let destination = parent </> "summary.json"
        prior = asciiBytes "prior\n"
        failures =
          [ ("nonzero", AuditCommandResult (ExitFailure 7) BS.empty (asciiBytes "git failed\n"))
          , ("malformed", AuditCommandResult ExitSuccess (asciiBytes "sha1\nextra\n") BS.empty)
          ]
    outcomes <-
      forM failures $ \(caseName, commandResult) -> do
        BS.writeFile destination prior
        let auditIO =
              (validSummaryAuditIO destination)
                { discoverObjectFormat = pure commandResult
                }
        failure <- actionError (summarizeAuditFilesWith auditIO summaryRecords)
        after <- BS.readFile destination
        pure
          ( caseName
          , maybe
              False
              ("git rev-parse --show-object-format" `isInfixOf`)
              failure
              && after == prior
          )
    pure (counterexample (show outcomes) (property (all snd outcomes)))

prop_summarizeHashFailures :: Property
prop_summarizeHashFailures =
  once $ ioProperty $ withTempDirectory "binding-audit-summary-hash" $ \parent -> do
    let destination = parent </> "summary.json"
        prior = asciiBytes "prior\n"
        namedInputs =
          [ ("worklist", summaryWorklistBytes)
          , ("leaf-results", summaryLeafBytes)
          , ("object-results", summaryObjectBytes)
          ]
        failureResults =
          [ ( "nonzero"
            , "sha1"
            , AuditCommandResult (ExitFailure 9) BS.empty (asciiBytes "git failed\n")
            )
          , ("sha1-short", "sha1", hashOutput (replicate 39 'a'))
          , ("sha1-wrong-sha256-length", "sha1", hashOutput (replicate 64 'a'))
          , ("sha1-uppercase", "sha1", hashOutput (replicate 40 'A'))
          , ("sha1-nonhex", "sha1", hashOutput (replicate 39 'a' ++ "g"))
          , ("sha256-short", "sha256", hashOutput (replicate 63 'a'))
          , ("sha256-long", "sha256", hashOutput (replicate 65 'a'))
          , ("sha256-uppercase", "sha256", hashOutput (replicate 64 'A'))
          , ("sha256-nonhex", "sha256", hashOutput (replicate 63 'a' ++ "g"))
          ]
    outcomes <-
      forM
        [ (name, bytes, failureName, objectFormat, result)
        | (name, bytes) <- namedInputs
        , (failureName, objectFormat, result) <- failureResults
        ]
        $ \(name, failedBytes, failureName, objectFormat, commandResult) -> do
          BS.writeFile destination prior
          let validLength = if objectFormat == "sha256" then 64 else 40
              auditIO =
                (validSummaryAuditIO destination)
                  { discoverObjectFormat =
                      pure
                        ( AuditCommandResult
                            ExitSuccess
                            (asciiBytes (objectFormat ++ "\n"))
                            BS.empty
                        )
                  , hashAuditBytes = \bytes ->
                      if bytes == failedBytes
                        then pure commandResult
                        else pure (hashOutput (replicate validLength 'a'))
                  }
          failure <- actionError (summarizeAuditFilesWith auditIO summaryRecords)
          after <- BS.readFile destination
          pure
            ( name ++ "/" ++ failureName
            , maybe
                False
                (("git hash-object --stdin for " ++ name) `isInfixOf`)
                failure
                && after == prior
            )
    pure (counterexample (show outcomes) (property (all snd outcomes)))
  where
    hashOutput digest =
      AuditCommandResult ExitSuccess (asciiBytes (digest ++ "\n")) BS.empty

prop_summarizeUtf8BeforeIdentity :: Property
prop_summarizeUtf8BeforeIdentity =
  once $ ioProperty $ withTempDirectory "binding-audit-summary-utf8" $ \parent -> do
    let destination = parent </> "summary.json"
        prior = asciiBytes "prior\n"
        invalid = BS.pack [0xff, 0x0a]
        cases =
          [ ("worklist", invalid, summaryLeafBytes, summaryObjectBytes)
          , ("leaf results", summaryWorklistBytes, invalid, summaryObjectBytes)
          , ("object results", summaryWorklistBytes, summaryLeafBytes, invalid)
          ]
    outcomes <-
      forM cases $ \(role, worklistBytes, leafBytes, objectBytes) -> do
        identityCalls <- newIORef (0 :: Int)
        BS.writeFile destination prior
        let auditIO =
              ( summaryAuditIO
                  destination
                  worklistBytes
                  leafBytes
                  objectBytes
              )
                { discoverObjectFormat = do
                    modifyIORef' identityCalls (+ 1)
                    pure validObjectFormatResult
                , hashAuditBytes = \bytes -> do
                    modifyIORef' identityCalls (+ 1)
                    hashAuditBytes (validSummaryAuditIO destination) bytes
                }
        failure <- actionError (summarizeAuditFilesWith auditIO summaryRecords)
        calls <- readIORef identityCalls
        after <- BS.readFile destination
        pure
          ( role
          , maybe False ((role ++ ": invalid UTF-8") `isInfixOf`) failure
              && calls == 0
              && after == prior
          )
    pure (counterexample (show outcomes) (property (all snd outcomes)))

summaryAuditIO
  :: FilePath
  -> BS.ByteString
  -> BS.ByteString
  -> BS.ByteString
  -> AuditIO
summaryAuditIO destination worklistBytes leafBytes objectBytes =
  productionAuditIO
    { readAuditBytes = \path ->
        if path == bindingAuditPath
          then pure worklistBytes
          else
            if path == leafResultsPath
              then pure leafBytes
              else
                if path == objectResultsPath
                  then pure objectBytes
                  else ioError (userError ("unexpected audit read: " ++ path))
    , atomicWriteAuditBytes = \path bytes ->
        if path == summaryPath
          then BS.writeFile destination bytes
          else ioError (userError ("unexpected audit write: " ++ path))
    , discoverObjectFormat = pure validObjectFormatResult
    , hashAuditBytes = validInjectedHash
    }

validSummaryAuditIO :: FilePath -> AuditIO
validSummaryAuditIO destination =
  summaryAuditIO
    destination
    summaryWorklistBytes
    summaryLeafBytes
    summaryObjectBytes

validObjectFormatResult :: AuditCommandResult
validObjectFormatResult =
  AuditCommandResult ExitSuccess (asciiBytes "sha1\n") BS.empty

validInjectedHash :: BS.ByteString -> IO AuditCommandResult
validInjectedHash bytes
  | bytes == summaryWorklistBytes = pure (injectedHashResult 'a')
  | bytes == summaryLeafBytes = pure (injectedHashResult 'b')
  | bytes == summaryObjectBytes = pure (injectedHashResult 'c')
  | otherwise = ioError (userError "unexpected bytes passed to injected Git hash")

injectedHashResult :: Char -> AuditCommandResult
injectedHashResult digit =
  AuditCommandResult
    ExitSuccess
    (asciiBytes (replicate 40 digit ++ "\n"))
    BS.empty

injectedIdentity :: InputIdentity
injectedIdentity =
  InputIdentity
    { inputObjectFormat = GitObjectSha1
    , inputWorklistDigest = replicate 40 'a'
    , inputLeafResultsDigest = replicate 40 'b'
    , inputObjectResultsDigest = replicate 40 'c'
    }

summaryOrDie :: [UnitRecord] -> AuditSummary
summaryOrDie inputRecords =
  case syntheticSummary inputRecords of
    Left auditError -> error (auditErrorMessage auditError)
    Right auditSummary -> auditSummary

commandLineOrDie :: AuditCommandResult -> String
commandLineOrDie commandResult =
  case Text.decodeUtf8' (auditCommandStdout commandResult) of
    Right text ->
      case Text.lines text of
        [line] -> Text.unpack line
        _ -> error ("unexpected Git output: " ++ show commandResult)
    Left _ -> error ("non-UTF-8 Git output: " ++ show commandResult)

objectFormatOrDie :: AuditCommandResult -> GitObjectFormat
objectFormatOrDie commandResult =
  case commandLineOrDie commandResult of
    "sha1" -> GitObjectSha1
    "sha256" -> GitObjectSha256
    other -> error ("unexpected Git object format: " ++ other)

actionError :: IO a -> IO (Maybe String)
actionError action = do
  result <- try (action >> pure ()) :: IO (Either SomeException ())
  pure $ case result of
    Left exception -> Just (displayException exception)
    Right () -> Nothing

prop_cliContract :: Property
prop_cliContract =
  once $ ioProperty $ withTempDirectory "binding-audit-cli" $ \parent -> do
    canonicalRoot <- canonicalizePath bindingAuditDirectory
    let forbidden = canonicalRoot </> ".task3-cli-forbidden"
        malformed = parent </> "malformed"
        prepared = parent </> "prepared"
    withCleanPath forbidden $ do
      createDirectory malformed
      mapM_
        (\name -> BS.writeFile (malformed </> name) (asciiBytes "invalid\n"))
        packetFileNames
      invalidResult <- runBindingAudit []
      summarizeResult <- runBindingAudit ["summarize"]
      forbiddenResult <- runBindingAudit ["prepare", forbidden]
      malformedResult <- runBindingAudit ["validate", malformed]
      successResult <- runBindingAudit ["prepare", prepared]
      preparedNames <-
        case successResult of
          (ExitSuccess, _, _) -> sort <$> listDirectory prepared
          _ -> pure []
      forbiddenCreated <- doesPathExist forbidden
      let usage =
            "binding-audit: binding-audit.hs prepare <output-dir>\n"
              ++ "binding-audit.hs validate <packet-dir>\n"
              ++ "binding-audit.hs summarize\n"
          exactUsage result =
            case result of
              (ExitFailure _, "", stderrBytes) -> stderrBytes == usage
              _ -> False
          summarizeRecognized =
            failedChannel summarizeResult
              && case summarizeResult of
                (ExitFailure _, "", stderrBytes) ->
                  not ("staged for Task 4" `isInfixOf` stderrBytes)
                    && leafResultsPath `isInfixOf` stderrBytes
                _ -> False
          failedChannel result =
            case result of
              (ExitFailure _, "", stderrBytes) ->
                "binding-audit:" `isPrefixOf` stderrBytes
                  && countOccurrences "binding-audit:" stderrBytes == 1
              _ -> False
          successChannel =
            successResult == (ExitSuccess, "", "")
              && preparedNames == sort packetFileNames
      pure $
        counterexample
          (show (invalidResult, summarizeResult, forbiddenResult, malformedResult, successResult, preparedNames))
          ( property
              ( exactUsage invalidResult
                  && summarizeRecognized
                  && failedChannel forbiddenResult
                  && failedChannel malformedResult
                  && successChannel
                  && not forbiddenCreated
              )
          )

loadAuditRecords :: IO [UnitRecord]
loadAuditRecords =
  loadRecords "corpus-units/MANIFEST.tsv" "corpus-units/corpus-v1.policy.lara"

statusBlind :: UnitRecord -> UnitRecord
statusBlind record =
  record {urStatuses = error "status forced during blind validation"}

bindingAuditDirectory :: FilePath
bindingAuditDirectory = "measurements/binding-audit"

packetFileNames :: [FilePath]
packetFileNames = ["worklist.tsv", "results.tsv", "object-results.tsv"]
utf8Bytes :: String -> BS.ByteString
utf8Bytes = Text.encodeUtf8 . Text.pack

writeCompletedPacket :: FilePath -> [UnitRecord] -> IO ()
writeCompletedPacket destination loaded =
  writePacket destination loaded (completedLeafDocument loaded) (completedObjectDocument loaded)

writePacket :: FilePath -> [UnitRecord] -> String -> String -> IO ()
writePacket destination loaded leafDocumentBytes objectDocumentBytes = do
  createDirectory destination
  BS.writeFile (destination </> "worklist.tsv") (utf8Bytes (bindingAuditTsv loaded))
  BS.writeFile (destination </> "results.tsv") (utf8Bytes leafDocumentBytes)
  BS.writeFile (destination </> "object-results.tsv") (utf8Bytes objectDocumentBytes)

completedLeafDocument :: [UnitRecord] -> String
completedLeafDocument = completeTemplate 5 . renderLeafTemplate

completedObjectDocument :: [UnitRecord] -> String
completedObjectDocument =
  completeTemplate 9
    . either (error . auditErrorMessage) id
    . renderObjectTemplate

completeTemplate :: Int -> String -> String
completeTemplate columns document =
  case parseTsv columns document of
    Left err -> error ("test template parse failed: " ++ show err)
    Right [] -> error "test template has no header"
    Right (header : dataRows) ->
      unlines
        ( renderTsvRow header
            : [ renderTsvRow (take (columns - 3) row ++ ["faithful", "reviewed", "-"])
              | row <- dataRows
              ]
        )

mutateCell :: Int -> Int -> Int -> String -> String -> String
mutateCell columns rowIndex columnIndex replacement document =
  rewriteDocument columns document $ \rows ->
    [ if index == rowIndex
        then
          [if column == columnIndex then replacement else cell | (column, cell) <- zip [0 ..] row]
        else row
    | (index, row) <- zip [0 ..] rows
    ]

swapFirstDataRows :: Int -> String -> String
swapFirstDataRows columns document =
  rewriteDocument columns document $ \rows ->
    case rows of
      header : first : second : rest -> header : second : first : rest
      _ -> error "test document has fewer than two data rows"

rewriteDocument :: Int -> String -> ([[String]] -> [[String]]) -> String
rewriteDocument columns document transform =
  case parseTsv columns document of
    Left err -> error ("test document parse failed: " ++ show err)
    Right rows -> unlines (map renderTsvRow (transform rows))

packetSnapshot :: FilePath -> IO [(FilePath, BS.ByteString)]
packetSnapshot destination = do
  names <- sort <$> listDirectory destination
  mapM (\name -> (,) name <$> BS.readFile (destination </> name)) names

actionFails :: IO a -> IO Bool
actionFails action = do
  result <- try (action >> pure ()) :: IO (Either SomeException ())
  pure $ case result of
    Left _ -> True
    Right () -> False

withTempDirectory :: String -> (FilePath -> IO a) -> IO a
withTempDirectory prefix =
  bracket (makeTempDirectory prefix) removePathForcibly

withCleanPath :: FilePath -> IO a -> IO a
withCleanPath path action =
  bracket
    (removeIfPresent path)
    (\() -> removeIfPresent path)
    (\() -> action)
removeIfPresent :: FilePath -> IO ()
removeIfPresent path = do
  exists <- doesPathExist path
  if exists then removePathForcibly path else pure ()

makeTempDirectory :: String -> IO FilePath
makeTempDirectory prefix = do
  temporaryRoot <- getTemporaryDirectory
  (path, handle) <- openTempFile temporaryRoot prefix
  hClose handle
  removeFile path
  createDirectory path
  pure path

runBindingAudit :: [String] -> IO (ExitCode, String, String)
runBindingAudit arguments =
  readProcessWithExitCode
    "runghc"
    (["-isrc", "scripts/binding-audit.hs"] ++ arguments)
    ""
countOccurrences :: String -> String -> Int
countOccurrences needle = go
  where
    go [] = 0
    go rest
      | needle `isPrefixOf` rest = 1 + go (drop (length needle) rest)
    go (_ : rest) = go rest
