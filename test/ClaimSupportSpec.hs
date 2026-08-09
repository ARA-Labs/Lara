-- | The corpus claim-support aggregation (#56) as a standing test: the pure
-- "Lara.ClaimSupport" classifiers, plus an end-to-end run over the FROZEN 60
-- corpus units that PINS every headline number the paper cites AND re-diffs the
-- committed frozen deliverable byte-for-byte. The integration props are the
-- regression guard — if a corpus edit or a checker change moves any headline
-- number, or the committed @measurements\/frozen\/claim-support.{json,tsv}@
-- drifts from what the pass now computes, this fails loudly (the freeze
-- discipline for the descriptive pass).
--
-- The per-unit IO is loaded through 'Lara.ClaimSupport.Load' — the same loader
-- the harness (@scripts\/claim-support.hs@) uses — so the records under test
-- are exactly the records that produced the shipped artifact, with no room for
-- the flavored\/decode logic to drift between test and harness.
module ClaimSupportSpec (claimSupportSpecProps) where

import Control.Exception (ErrorCall, IOException, bracket, displayException, evaluate, try)
import qualified Data.Bits as Bits
import Data.List (isInfixOf, isPrefixOf, isSuffixOf, nub)
import System.Directory
  ( createDirectory
  , getTemporaryDirectory
  , listDirectory
  , removeFile
  , removePathForcibly
  )
import System.FilePath ((</>))
import System.IO (hClose, hPutStr, openTempFile)
import System.Posix.Files (fileMode, getFileStatus)
import Test.QuickCheck

import Lara.AST
  ( Arg (..)
  , ArgConcl (..)
  , ArgId (..)
  , Attack (..)
  , AuditStatus (Reviewed)
  , Binding (..)
  , ChallengeTarget (..)
  , Claim (..)
  , Decl (..)
  , Digest (..)
  , GroupConflictMode (QuarantineOnConflict)
  , Label (..)
  , Leaf (..)
  , LeafId (..)
  , LeafKind (Attested, Observed)
  , Mode (Defeasible)
  , PolicyId (..)
  , PropId (..)
  , Program (..)
  , Provenance (AiExecuted)
  , SourceRef (..)
  , Status (Defeated, Gap, Justified)
  , SupportTerm (..)
  , Unit (..)
  )
import Lara.AtomicWrite (atomicWriteFile, atomicWriteWith)
import Lara.ClaimSupport
import Lara.ClaimSupport.Load (loadRecords)
import Lara.Measure (EnvBlock (..))
import Lara.Prop (Pred (..), Prop (..))
import Lara.Replay (inputReplayId)
import Lara.Wire (Outcome (..), Verdict (..))
import TestReplay (testCheckInput)

manifestPath, policyPath, frozenJsonPath, frozenTsvPath :: FilePath
manifestPath = "corpus-units/MANIFEST.tsv"
policyPath = "corpus-units/corpus-v1.policy.lara"
frozenJsonPath = "measurements/frozen/claim-support.json"
frozenTsvPath = "measurements/frozen/claim-support.tsv"

claimSupportSpecProps :: [(String, IO Result)]
claimSupportSpecProps =
  [ ("claim-support: paper-anchor ref classifier", quickCheckResult prop_paperAnchor)
  , ("claim-support: frozen corpus numbers (status/leaves/attacks/strict)", quickCheckResult prop_frozenNumbers)
  , ("claim-support: binding-audit rows preserve the frozen 38-leaf denominator", quickCheckResult prop_bindingAuditRows)
  , ("claim-support: binding-audit rows carry role-aware claim context", quickCheckResult prop_bindingAuditContexts)
  , ("claim-support: binding-audit context drift fails loudly", quickCheckResult prop_bindingAuditContextFailures)
  , ("claim-support: binding-audit attack projections cover every constructor", quickCheckResult prop_bindingAuditAttackProjections)
  , ("claim-support: binding-audit TSV is canonical and rectangular", quickCheckResult prop_bindingAuditTsv)
  , ("claim-support: binding-audit worklist is fresh", quickCheckResult prop_bindingAuditFresh)
  , ("claim-support: atomic worklist writes preserve complete destinations", quickCheckResult prop_atomicWriteFile)
  , ("claim-support: recomputed json/tsv re-diff the committed frozen deliverable", quickCheckResult prop_frozenDeliverable)
  ]

-- | Direct paper-document locators are recognised; agent-artifact paths are not.
prop_paperAnchor :: Property
prop_paperAnchor =
  once $
    counterexample "paper locators" (all (isPaperAnchorRef . SourceRef) paperRefs)
      .&&. counterexample "agent paths" (not (any (isPaperAnchorRef . SourceRef) agentRefs))
  where
    paperRefs =
      [ "E01#Table-2"
      , "E04#Table-10"
      , "Table-5"
      , "Table-4-row-total"
      , "Figure-3a"
      , "Appendix-B"
      , "Theorem-2"
      , "section-4"
      , "paper-section-5.1"
      , "PAPER.md#overview"
      ]
    agentRefs =
      [ "logic/claims.md#C03"
      , "trace/exploration_tree.yaml#N15"
      , "evidence/tables/table4_reward_subset_ablation.md"
      , "src/model.py#L10"
      , "rl_finetune_best_of_n.py#118-139"
      ]

-- | The full aggregation over the frozen 60 units, with EVERY headline number
-- (and its by-provenance/by-kind breakdown) pinned — not only the four the plan
-- names but every field the committed @claim-support.json@ reports, so a
-- classifier edit that flips one leaf cannot pass silently.
prop_frozenNumbers :: Property
prop_frozenNumbers = once $ ioProperty $ do
  rep <- aggregate <$> loadRecords manifestPath policyPath
  let has k n = lookup k (csStatus rep) == Just n
  pure $
    conjoin
      [ counterexample "units" (csUnits rep === 60)
      , counterexample "gap" (property (has Gap 48))
      , counterexample "justified" (property (has Justified 9))
      , counterexample "defeated" (property (has Defeated 3))
      , counterexample "load-bearing total" (csLoadBearingTotal rep === 38)
      , counterexample "load-bearing provenance" (csLoadBearingProvenance rep === [(AiExecuted, 38)])
      , counterexample "load-bearing kind" (csLoadBearingKind rep === [(Attested, 20), (Observed, 18)])
      , counterexample "load-bearing paper-anchored" (csLoadBearingPaperAnchored rep === 15)
      , counterexample "all leaves total" (csAllTotal rep === 169)
      , counterexample "all leaves provenance" (csAllProvenance rep === [(AiExecuted, 169)])
      , counterexample "all leaves kind" (csAllKind rep === [(Attested, 106), (Observed, 63)])
      , counterexample "all leaves paper-anchored" (csAllPaperAnchored rep === 51)
      , counterexample "typed attacks" (csTypedAttacks rep === 3)
      , counterexample "dead-end attacks" (csDeadEndAttacks rep === 2)
      , counterexample "strict steps" (csStrictSteps rep === 1)
      , counterexample "strict certified" (csStrictCertified rep === 1)
      , counterexample "documented strict-flavored" (csStrictFlavored rep === 5)
      ]

prop_bindingAuditTsv :: Property
prop_bindingAuditTsv = once $ ioProperty $ do
  records <- loadRecords manifestPath policyPath
  let rendered = bindingAuditTsv records
      renderedLines = lines rendered
      (renderedHeader, renderedDataLines) =
        case renderedLines of
          [] -> ("", [])
          header : dataLines -> (header, dataLines)
      (headerCells, dataCells) =
        case map splitOnTab renderedLines of
          [] -> ([], [])
          header : dataRows -> (header, dataRows)
      syntheticRow =
        BindingAuditRow
          { barLeaf =
              LeafFact
                { lfId = LeafId "e1"
                , lfProvenance = AiExecuted
                , lfKind = Observed
                , lfPaperAnchored = False
                , lfRefs = [SourceRef "trace/a|b", SourceRef "Table-1"]
                }
          , barFormalTarget = Prop (Pred "p") []
          , barRole = AuditSupport
          , barClaimId = PropId "c1"
          , barClaimNl = "line one\nline two\\tail"
          }
      syntheticRecord =
        UnitRecord
          { urName = "unit\tone"
          , urStatuses = []
          , urAllLeaves = []
          , urTypedAttacks = 0
          , urDeadEndAttacks = 0
          , urStrictSteps = 0
          , urStrictCertified = 0
          , urStrictFlavored = False
          , urBindingAuditRows = [syntheticRow]
          }
      syntheticDataLine = last (lines (bindingAuditTsv [syntheticRecord]))
      emptyRefsRow =
        syntheticRow
          { barClaimNl = "carriage\rreturn"
          , barLeaf = (barLeaf syntheticRow) {lfRefs = []}
          }
      emptyRefsDataLine =
        last
          ( lines
              ( bindingAuditTsv
                  [syntheticRecord {urBindingAuditRows = [emptyRefsRow]}]
              )
          )
      invalidRefs = [SourceRef "a,b", SourceRef "-"]
  invalidRefChecks <-
    mapM
      ( \ref -> do
          result <-
            try
              ( evaluate
                  ( length
                      ( bindingAuditTsv
                          [ syntheticRecord
                              { urBindingAuditRows =
                                  [ syntheticRow
                                      { barLeaf = (barLeaf syntheticRow) {lfRefs = [ref]}
                                      }
                                  ]
                              }
                          ]
                      )
                  )
              )
              :: IO (Either ErrorCall Int)
          pure $
            counterexample ("invalid ref " ++ show ref) $
              case result of
                Left err ->
                  counterexample (displayException err) $
                    property
                      ( ( "claim-support: binding-audit ref " ++ show ref
                            ++ " on leaf LeafId \"e1\" in unit unit\tone"
                        )
                          `isPrefixOf` displayException err
                      )
                Right _ ->
                  counterexample "expected binding-audit ref error" (property False)
      )
      invalidRefs
  pure $
    conjoin
      ( [ counterexample
            "exact header"
            ( bindingAuditTsvHeader
                === "unit\tleaf_id\tformal_target\trole\tclaim_id\tclaim_nl\tkind\tprovenance\trefs"
            )
        , counterexample "header" (renderedHeader === bindingAuditTsvHeader)
        , counterexample "header columns" (length headerCells === 9)
        , counterexample "data rows" (length renderedDataLines === 38)
        , counterexample "rectangular rows" (property (all ((== 9) . length) dataCells))
        , counterexample "canonical final newline" (property (not (null rendered) && last rendered == '\n'))
        , counterexample
            "TSV escaping and comma-delimited refs"
            ( syntheticDataLine
                === "unit\\tone\te1\tp\tsupport\tc1\tline one\\nline two\\\\tail\tobserved\tai-executed\ttrace/a|b,Table-1"
            )
        , counterexample
            "carriage return escaping"
            (property ("carriage\\rreturn" `isInfixOf` emptyRefsDataLine))
        , counterexample
            "empty refs sentinel"
            (property ("\t-" `isSuffixOf` emptyRefsDataLine))
        ]
          ++ invalidRefChecks
      )

-- | The committed binding-audit worklist is exactly the current pure renderer
-- output, so corpus or classifier drift cannot leave the review input stale.
prop_bindingAuditFresh :: Property
prop_bindingAuditFresh = once $ ioProperty $ do
  records <- loadRecords manifestPath policyPath
  committed <- readFile bindingAuditPath
  pure $
    counterexample
      (bindingAuditPath ++ " is stale — regenerate with scripts/claim-support.hs")
      (bindingAuditTsv records === committed)

-- | Atomic worklist writes produce exact bytes, replace existing files, retain
-- the old destination on a write failure, remove temporary files, and leave a
-- repository-readable mode.
prop_atomicWriteFile :: Property
prop_atomicWriteFile = once $ ioProperty $ withTemporaryDirectory $ \directory -> do
  let destination = directory </> "worklist.tsv"
  atomicWriteFile destination "fresh\n"
  fresh <- readFileFully destination
  atomicWriteFile destination "replacement\n"
  replacement <- readFileFully destination
  failed <-
    try
      ( atomicWriteWith destination $ \handle -> do
          hPutStr handle "partial"
          ioError (userError "injected write failure")
      )
      :: IO (Either IOException ())
  retained <- readFileFully destination
  entries <- listDirectory directory
  mode <- fileMode <$> getFileStatus destination
  pure $
    conjoin
      [ counterexample "fresh bytes" (fresh === "fresh\n")
      , counterexample "replacement bytes" (replacement === "replacement\n")
      , counterexample "write failure propagated" $
          case failed of
            Left err -> property ("injected write failure" `isInfixOf` displayException err)
            Right () -> counterexample "expected injected write failure" False
      , counterexample "failed write retained destination" (retained === "replacement\n")
      , counterexample "failed write left no temporary file" (entries === ["worklist.tsv"])
      , counterexample "destination mode" ((mode Bits..&. 0o777) === 0o644)
      ]

withTemporaryDirectory :: (FilePath -> IO a) -> IO a
withTemporaryDirectory = bracket acquire removePathForcibly
  where
    acquire = do
      root <- getTemporaryDirectory
      (path, handle) <- openTempFile root "lara-atomic-write"
      hClose handle
      removeFile path
      createDirectory path
      pure path

readFileFully :: FilePath -> IO String
readFileFully path = do
  contents <- readFile path
  _ <- evaluate (length contents)
  pure contents

-- | Render the JSON and TSV from the freshly recomputed records and require
-- them to reproduce the COMMITTED frozen deliverable byte-for-byte (the JSON
-- modulo its environment block, which is reconstructed from the frozen file so
-- the compare is exact). This pins all 60 per-unit rows and the JSON notes, and
-- catches any hand-edit or corpus-vs-artifact staleness of the committed files
-- — the byte-identical re-diff the house freeze discipline applies elsewhere.
prop_frozenDeliverable :: Property
prop_frozenDeliverable = once $ ioProperty $ do
  records <- loadRecords manifestPath policyPath
  let rep = aggregate records
  frozenJson <- readFile frozenJsonPath
  frozenTsv <- readFile frozenTsvPath
  let env = envFromFrozenJson frozenJson
  pure $
    conjoin
      [ counterexample "frozen tsv (all 60 per-unit rows)" (claimSupportTsv records === frozenTsv)
      , counterexample
          "frozen json (aggregate + per-unit + notes, modulo env)"
          (claimSupportJson env rep records === frozenJson)
      ]


prop_bindingAuditRows :: Property
prop_bindingAuditRows = once $ ioProperty $ do
  records <- loadRecords manifestPath policyPath
  let rows =
        [ (urName record, row)
        | record <- records
        , row <- urBindingAuditRows record
        ]
      keys = [(unit, lfId (barLeaf row)) | (unit, row) <- rows]
      countKind k = length [() | (_, row) <- rows, lfKind (barLeaf row) == k]
  pure $
    conjoin
      [ counterexample "worklist rows" (length rows === 38)
      , counterexample "unique unit/leaf keys" (length (nub keys) === 38)
      , counterexample "attested rows" (countKind Attested === 20)
      , counterexample "observed rows" (countKind Observed === 18)
      , counterexample "provenance" (property (all ((== AiExecuted) . lfProvenance . barLeaf . snd) rows))
      ]

prop_bindingAuditContexts :: Property
prop_bindingAuditContexts = once $ ioProperty $ do
  records <- loadRecords manifestPath policyPath
  let rows =
        [ (urName record, auditRow)
        | record <- records
        , auditRow <- urBindingAuditRows record
        ]
      row unit lid =
        case [auditRow | (rowUnit, auditRow) <- rows, rowUnit == unit, lfId (barLeaf auditRow) == LeafId lid] of
          [auditRow] -> auditRow
          matches -> error ("claim-support test: expected one " ++ unit ++ "/" ++ lid ++ " row, got " ++ show (length matches))
      strictCell = row "adaptive-pruning.C04" "e4"
      attackContexts =
        [ (unit, lfId (barLeaf auditRow), barClaimId auditRow)
        | (unit, auditRow) <- rows
        , barRole auditRow == AuditAttack
        ]
      expectedAttackContexts =
        [ ("fre.C04", LeafId "u1", PropId "c04")
        , ("test-time-model-adaptation.C04", LeafId "u1", PropId "c04")
        , ("rebench-triton_cumsum.C09", LeafId "u1", PropId "c09")
        ]
  pure $
    conjoin
      [ counterexample "strict subclaim role" (barRole strictCell === AuditSupport)
      , counterexample "strict subclaim id" (barClaimId strictCell === PropId "c04a")
      , counterexample "all attack contexts" (attackContexts === expectedAttackContexts)
      ]

-- | Every checked attack constructor selects its target argument's claim, and
-- repeated targets for the same claim collapse to one audit context.
prop_bindingAuditAttackProjections :: Property
prop_bindingAuditAttackProjections =
  once $
    conjoin
      [ projection "rebut" (Rebut attackerId targetId)
      , projection "undercut" (Undercut attackerId targetId [])
      , projection "undermine" (Undermine attackerId targetId [])
      , counterexample "same-claim multi-target attack" $
          case urBindingAuditRows sameClaimMultiTargetRecord of
            [row] ->
              conjoin
                [ barRole row === AuditAttack
                , barClaimId row === primaryClaimId
                ]
            rows ->
              counterexample
                ("expected one deduplicated row, got " ++ show (length rows))
                False
      ]
  where
    projection attackName attack =
      counterexample attackName $
        case urBindingAuditRows (singleAttackRecord attack) of
          [row] ->
            conjoin
              [ barRole row === AuditAttack
              , barClaimId row === primaryClaimId
              ]
          rows ->
            counterexample
              ("expected one attack row, got " ++ show (length rows))
              False

    singleAttackRecord attack =
      auditRecord
        [(attackerId, SLeaf primaryLeafId), (targetId, SLeaf secondaryLeafId)]
        [attack]
        [primaryClaim]
        [challengeArg attackerId primaryLeafId, supportArg targetId primaryClaimId secondaryLeafId]
        [(0, LIn), (1, LOut)]

    sameClaimMultiTargetRecord =
      auditRecord
        [ (attackerId, SLeaf primaryLeafId)
        , (targetId, SLeaf secondaryLeafId)
        , (secondTargetId, SLeaf secondaryLeafId)
        ]
        [ Rebut attackerId targetId
        , Rebut attackerId secondTargetId
        ]
        [primaryClaim]
        [ challengeArg attackerId primaryLeafId
        , supportArg targetId primaryClaimId secondaryLeafId
        , supportArg secondTargetId primaryClaimId secondaryLeafId
        ]
        [(0, LIn), (1, LOut), (2, LOut)]

-- | Reachable surface/core drift cases used to derive human-facing claim
-- context must fail loudly. Forcing the rendered row list evaluates every row
-- field without exposing private context helpers from "Lara.ClaimSupport".
prop_bindingAuditContextFailures :: Property
prop_bindingAuditContextFailures = once $ ioProperty $ do
  checks <- mapM checkCase contextFailureCases
  pure (conjoin checks)
  where
    checkCase (caseName, record, expectedPrefix) = do
      result <-
        try (evaluate (length (show (urBindingAuditRows record))))
          :: IO (Either ErrorCall Int)
      pure $
        counterexample caseName $
          case result of
            Left err ->
              counterexample (displayException err) $
                property (expectedPrefix `isPrefixOf` displayException err)
            Right _ -> counterexample "expected claim-support context error" (property False)

contextFailureCases :: [(String, UnitRecord, String)]
contextFailureCases =
  [ ( "missing declared claim"
    , auditRecord [(supportId, SLeaf primaryLeafId)] [] [] [supportArg supportId primaryClaimId primaryLeafId] [(0, LIn)]
    , "claim-support: claim PropId \"c1\" missing from synthetic"
    )
  , ( "duplicate declared claim"
    , auditRecord [(supportId, SLeaf primaryLeafId)] [] [primaryClaim, primaryClaim] [supportArg supportId primaryClaimId primaryLeafId] [(0, LIn)]
    , "claim-support: duplicate claim PropId \"c1\" in synthetic"
    )
  , ( "missing surface argument"
    , auditRecord [(supportId, SLeaf primaryLeafId)] [] [primaryClaim] [] [(0, LIn)]
    , "claim-support: argument ArgId \"a1\" missing from surface decls in unit synthetic"
    )
  , ( "duplicate surface argument"
    , auditRecord [(supportId, SLeaf primaryLeafId)] [] [primaryClaim] [supportArg supportId primaryClaimId primaryLeafId, supportArg supportId primaryClaimId primaryLeafId] [(0, LIn)]
    , "claim-support: duplicate argument ArgId \"a1\" in unit synthetic"
    )
  , ( "load-bearing derived support"
    , auditRecord [(supportId, SLeaf primaryLeafId)] [] [] [derivedArg supportId primaryLeafId] [(0, LIn)]
    , "claim-support: load-bearing derived claim PropId \"derived\" has no nl context in synthetic"
    )
  , ( "load-bearing untyped challenge"
    , auditRecord [(supportId, SLeaf primaryLeafId)] [] [] [challengeArg supportId primaryLeafId] [(0, LIn)]
    , "claim-support: load-bearing challenge ArgId \"a1\" has no typed attack in synthetic"
    )
  , ( "attacked derived support"
    , auditRecord attackArgs [Rebut attackerId targetId] [] [challengeArg attackerId primaryLeafId, derivedArg targetId secondaryLeafId] [(0, LIn), (1, LOut)]
    , "claim-support: attacked derived claim PropId \"derived\" has no nl context in synthetic"
    )
  , ( "attacked challenge"
    , auditRecord attackArgs [Rebut attackerId targetId] [] [challengeArg attackerId primaryLeafId, challengeArg targetId secondaryLeafId] [(0, LIn), (1, LOut)]
    , "claim-support: attack target ArgId \"target\" is not a claim support in synthetic"
    )
  , ( "multi-target attack with distinct claims"
    , auditRecord
        [ (attackerId, SLeaf primaryLeafId)
        , (targetId, SLeaf secondaryLeafId)
        , (secondTargetId, SLeaf secondaryLeafId)
        ]
        [Rebut attackerId targetId, Rebut attackerId secondTargetId]
        [primaryClaim, secondaryClaim]
        [ challengeArg attackerId primaryLeafId
        , supportArg targetId primaryClaimId secondaryLeafId
        , supportArg secondTargetId secondaryClaimId secondaryLeafId
        ]
        [(0, LIn), (1, LOut), (2, LOut)]
    , "claim-support: load-bearing leaf LeafId \"l1\" has ambiguous claim context in synthetic"
    )
  , ( "dual-role support and attack source"
    , auditRecord
        [(attackerId, SLeaf primaryLeafId), (targetId, SLeaf secondaryLeafId)]
        [Rebut attackerId targetId]
        [primaryClaim, secondaryClaim]
        [ supportArg attackerId secondaryClaimId primaryLeafId
        , supportArg targetId primaryClaimId secondaryLeafId
        ]
        [(0, LIn), (1, LOut)]
    , "claim-support: load-bearing leaf LeafId \"l1\" has ambiguous claim context in synthetic"
    )
  , ( "core leaf missing"
    , auditRecordWithCoreLeaves
        [(secondaryLeafId, secondaryProp)]
        [(supportId, SLeaf primaryLeafId)]
        []
        [primaryClaim]
        [supportArg supportId primaryClaimId primaryLeafId]
        [(0, LIn)]
    , "claim-support: core leaf LeafId \"l1\" missing from checked unit synthetic"
    )
  , ( "surface and core formal targets differ"
    , auditRecordWithCoreLeaves
        [(primaryLeafId, secondaryProp), (secondaryLeafId, secondaryProp)]
        [(supportId, SLeaf primaryLeafId)]
        []
        [primaryClaim]
        [supportArg supportId primaryClaimId primaryLeafId]
        [(0, LIn)]
    , "claim-support: leaf LeafId \"l1\" formal target differs between surface and checked unit synthetic"
    )
  , ( "ambiguous leaf context"
    , auditRecord
        [(supportId, SLeaf primaryLeafId), (secondSupportId, SLeaf primaryLeafId)]
        []
        [primaryClaim, secondaryClaim]
        [supportArg supportId primaryClaimId primaryLeafId, supportArg secondSupportId secondaryClaimId primaryLeafId]
        [(0, LIn), (1, LIn)]
    , "claim-support: load-bearing leaf LeafId \"l1\" has ambiguous claim context in synthetic"
    )
  ]
  where
    attackArgs =
      [ (attackerId, SLeaf primaryLeafId)
      , (targetId, SLeaf secondaryLeafId)
      ]

auditRecord
  :: [(ArgId, SupportTerm)]
  -> [Attack]
  -> [Claim]
  -> [Arg]
  -> [(Int, Label)]
  -> UnitRecord
auditRecord coreArgs =
  auditRecordWithCoreLeaves
    [(leafId leaf, leafProp leaf) | leaf <- syntheticLeaves]
    coreArgs

auditRecordWithCoreLeaves
  :: [(LeafId, Prop)]
  -> [(ArgId, SupportTerm)]
  -> [Attack]
  -> [Claim]
  -> [Arg]
  -> [(Int, Label)]
  -> UnitRecord
auditRecordWithCoreLeaves coreLeaves coreArgs coreAttacks claims surfaceArgs labels =
  computeUnit (const Defeasible) False "synthetic" input verdict program
  where
    unit =
      Unit
        { unitRules = []
        , unitContraries = []
        , unitExceptions = []
        , unitTheories = []
        , unitLeaves = coreLeaves
        , unitArgs = coreArgs
        , unitAttacks = coreAttacks
        , unitQueries = []
        , unitGroups = []
        , unitGroupMode = QuarantineOnConflict
        }
    input = testCheckInput unit
    verdict = Verdict (inputReplayId input) (Accept labels [] [])
    program =
      Program
        { programArtifact = "synthetic"
        , programDigest = Digest "sha256:synthetic"
        , programPolicy = PolicyId "synthetic"
        , programBackends = []
        , programDecls =
            map DeclLeaf syntheticLeaves
              ++ map DeclClaim claims
              ++ map DeclArg surfaceArgs
        }

syntheticLeaves :: [Leaf]
syntheticLeaves =
  [ Leaf primaryLeafId primaryProp Observed AiExecuted [SourceRef "synthetic#l1"]
  , Leaf secondaryLeafId secondaryProp Attested AiExecuted [SourceRef "synthetic#l2"]
  ]

primaryClaim, secondaryClaim :: Claim
primaryClaim = Claim primaryClaimId "primary claim" primaryProp syntheticBinding
secondaryClaim = Claim secondaryClaimId "secondary claim" secondaryProp syntheticBinding

syntheticBinding :: Binding
syntheticBinding = Binding "test" "binding-audit fixture" Reviewed

supportArg :: ArgId -> PropId -> LeafId -> Arg
supportArg aid cid lid = Arg aid (SupportsClaim cid) (SLeaf lid)

derivedArg :: ArgId -> LeafId -> Arg
derivedArg aid lid = Arg aid (SupportsDerived (PropId "derived")) (SLeaf lid)

challengeArg :: ArgId -> LeafId -> Arg
challengeArg aid lid = Arg aid (Challenges (ChallengesLeaf lid)) (SLeaf lid)

primaryProp, secondaryProp :: Prop
primaryProp = Prop (Pred "primary") []
secondaryProp = Prop (Pred "secondary") []

primaryLeafId, secondaryLeafId :: LeafId
primaryLeafId = LeafId "l1"
secondaryLeafId = LeafId "l2"

primaryClaimId, secondaryClaimId :: PropId
primaryClaimId = PropId "c1"
secondaryClaimId = PropId "c2"

supportId, secondSupportId, attackerId, targetId, secondTargetId :: ArgId
supportId = ArgId "a1"
secondSupportId = ArgId "a2"
attackerId = ArgId "attacker"
targetId = ArgId "target"
secondTargetId = ArgId "second-target"

splitOnTab :: String -> [String]
splitOnTab [] = [""]
splitOnTab xs =
  case break (== '\t') xs of
    (cell, []) -> [cell]
    (cell, _ : rest) -> cell : splitOnTab rest
-- | Reconstruct the 'EnvBlock' from a frozen @claim-support.json@'s environment
-- object, so the re-diff can be byte-exact rather than env-sensitive. The six
-- keys are unique to that object and it is the first object in the file.
envFromFrozenJson :: String -> EnvBlock
envFromFrozenJson s =
  EnvBlock
    { envGitRev = field "git-rev"
    , envGitDirty = field "git-dirty" == "true"
    , envGhc = field "ghc"
    , envLean = field "lean"
    , envOs = field "os"
    , envCpu = field "cpu"
    }
  where
    field k =
      case [ dropWhile (== ' ') (drop (length prefix) t)
           | l <- lines s
           , let t = dropWhile (== ' ') l
           , prefix `isPrefixOf` t
           ] of
        (v : _) -> stripQuotes (stripComma v)
        [] -> error ("claim-support test: env field " ++ k ++ " not found in frozen json")
      where
        prefix = "\"" ++ k ++ "\":"
    stripComma xs = if not (null xs) && last xs == ',' then init xs else xs
    stripQuotes ('"' : rest) | not (null rest) && last rest == '"' = init rest
    stripQuotes xs = xs
