-- | Test-only codec and pipeline for the source admission fixtures
-- (metatheory plan Task 3): the single shared implementation behind both
-- @scripts\/check-admission.hs@ (the CI-facing driver) and
-- @test\/DifferentialSpec.hs@ (the plain @cabal test@ half).
--
-- The fixture schema is test-only: it is NOT a production wire format and
-- never enters @lara-core\@0.1@ or replay identity.
--
-- A fixture is:
--
-- > (admission
-- >   (metas (meta "id" (kind K) (provenance P)) ...)
-- >   (table (row (kind K) (provenance P) (decision D)) ...)
-- >   (unit ...)          -- a wire-shaped declared unit (Lara.Wire.decodeUnit)
-- >   (expected OUTCOME)) -- the committed canonical outcome encoding
--
-- and @admissionOutcome@ is a test-only adapter over the production
-- admission/prune primitives: "Lara.Admission" validation, rejection, and
-- policy seed, then "Lara.Blocked".@pruneWithPolicySeed@ and
-- @buildAdmissionAudit@. It deliberately does not invoke @prepareSource@,
-- @runSourceCheck@, or final status rendering; @test\/AdmissionSpec.hs@
-- covers that real source/checker seam. Malformed fixture or unit shape is
-- rejected. Ordered metadata/leaf misalignment is a source-invalid admission
-- outcome, never silently repaired or dropped.
module Lara.AdmissionFixture
  ( admissionOutcome
  ) where

import Data.List (find)
import Data.List.NonEmpty (toList)

import Lara.Admission
  ( AdmissionAudit
  , AdmissionCause (..)
  , AdmissionRejection
  , admissionAuditArgs
  , admissionAuditAttacks
  , admissionAuditLeaves
  , admissionRejectionKind
  , admissionRejectionLeaf
  , admissionRejectionMatchedRow
  , admissionRejectionProvenance
  , buildAdmissionAudit
  , firstAdmissionRejection
  , policyQuarantineSeed
  , validateAdmissionKeys
  )
import Lara.AST
  ( Admission (..)
  , ArgId (..)
  , Attack (..)
  , GroupConflictMode (..)
  , GroupId (..)
  , Leaf (..)
  , LeafId (..)
  , LeafKind (..)
  , Provenance (..)
  , QuestionId (..)
  , Step (..)
  , Unit (..)
  )
import Lara.Blocked (pruneWithPolicySeed)
import Lara.Prop (Prop)
import Lara.Strict (SExpr (..))
import Lara.Wire (WireError (..), decodeUnit, parseSExpr, printSExpr)
import SigmaFixture (structuralSigma)

-- ---------------------------------------------------------------------------
-- Identifier unwrappers (the AST newtypes carry no accessors)
-- ---------------------------------------------------------------------------

unLeafId :: LeafId -> String
unLeafId (LeafId s) = s

unArgId :: ArgId -> String
unArgId (ArgId s) = s

unGroupId :: GroupId -> String
unGroupId (GroupId s) = s

unQuestionId :: QuestionId -> String
unQuestionId (QuestionId s) = s

-- ---------------------------------------------------------------------------
-- Fixture decoding (test-only schema)
-- ---------------------------------------------------------------------------

data Fixture = Fixture
  { fxMetas :: [(LeafId, LeafKind, Provenance)]
  , fxTable :: [((LeafKind, Provenance), Admission)]
  , fxUnit :: SExpr
  , fxExpected :: SExpr
  }

decodeKind :: SExpr -> Either String LeafKind
decodeKind (SAtom "observed") = Right Observed
decodeKind (SAtom "attested") = Right Attested
decodeKind (SAtom "assumed") = Right Assumed
decodeKind (SAtom "certified") = Right Certified
decodeKind _ = Left "fixture: unknown leaf kind"

decodeProvenance :: SExpr -> Either String Provenance
decodeProvenance (SAtom "user") = Right User
decodeProvenance (SAtom "ai") = Right AiExecuted
decodeProvenance (SList [SAtom "checker", SAtom n, SAtom v]) = Right (Checker n v)
decodeProvenance _ = Left "fixture: unknown provenance"

decodeDecision :: SExpr -> Either String Admission
decodeDecision (SAtom "admit") = Right Admit
decodeDecision (SAtom "quarantine") = Right Quarantine
decodeDecision (SAtom "reject") = Right Reject
decodeDecision _ = Left "fixture: unknown admission decision"

-- | @(meta "id" (kind K) (provenance P))@ — id, kind, and provenance only;
-- the proposition is bound later from the unit's declared leaf table.
decodeMetaRow :: SExpr -> Either String (LeafId, LeafKind, Provenance)
decodeMetaRow (SList [SAtom "meta", SAtom lid, kindE, provE]) = do
  k <- case kindE of
    SList [SAtom "kind", kE] -> decodeKind kE
    _ -> Left "fixture: malformed meta kind"
  p <- case provE of
    SList [SAtom "provenance", pE] -> decodeProvenance pE
    _ -> Left "fixture: malformed meta provenance"
  Right (LeafId lid, k, p)
decodeMetaRow _ = Left "fixture: malformed meta"

-- | @(metas (meta ...)*)@
decodeMetas :: SExpr -> Either String [(LeafId, LeafKind, Provenance)]
decodeMetas (SList (SAtom "metas" : rows)) = mapM decodeMetaRow rows
decodeMetas _ = Left "fixture: malformed metas section"

-- | @(row (kind K) (provenance P) (decision D))@
decodeTableRow :: SExpr -> Either String ((LeafKind, Provenance), Admission)
decodeTableRow
  ( SList
      [ SAtom "row"
      , SList [SAtom "kind", kindE]
      , SList [SAtom "provenance", provE]
      , SList [SAtom "decision", decE]
      ]
    ) = do
      k <- decodeKind kindE
      p <- decodeProvenance provE
      d <- decodeDecision decE
      Right ((k, p), d)
decodeTableRow _ = Left "fixture: malformed admission row"

-- | @(table (row ...)*)@
decodeTable :: SExpr -> Either String [((LeafKind, Provenance), Admission)]
decodeTable (SList (SAtom "table" : rows)) = mapM decodeTableRow rows
decodeTable _ = Left "fixture: malformed table section"

malformedExpected :: Either String a
malformedExpected = Left "fixture: malformed expected outcome"

validateExpectedCause :: SExpr -> Either String ()
validateExpectedCause (SList [SAtom "cause", SAtom "policy"]) = Right ()
validateExpectedCause (SList [SAtom "cause", SList [SAtom "group", SAtom _]]) = Right ()
validateExpectedCause _ = malformedExpected

validateExpectedLeafRow :: SExpr -> Either String ()
validateExpectedLeafRow (SList (SAtom "leaf-row" : SAtom _ : causes@(_ : _))) =
  mapM_ validateExpectedCause causes
validateExpectedLeafRow _ = malformedExpected

validateExpectedAtom :: SExpr -> Either String ()
validateExpectedAtom (SAtom _) = Right ()
validateExpectedAtom _ = malformedExpected

validateExpectedStep :: SExpr -> Either String ()
validateExpectedStep (SList [SAtom "prem", SAtom n]) =
  case reads n :: [(Integer, String)] of
    [(value, "")]
      | value >= 0
      , value <= 0x7fffffffffffffff
      , show value == n -> Right ()
    _ -> malformedExpected
validateExpectedStep (SList [SAtom "ques", SAtom _]) = Right ()
validateExpectedStep _ = malformedExpected

validateExpectedPosition :: SExpr -> Either String ()
validateExpectedPosition (SList (SAtom "pos" : steps)) =
  mapM_ validateExpectedStep steps
validateExpectedPosition _ = malformedExpected

validateExpectedAttack :: SExpr -> Either String ()
validateExpectedAttack (SList [SAtom "rebut", SAtom _, SAtom _]) = Right ()
validateExpectedAttack
  (SList [SAtom "undercut", SAtom _, SAtom _, position]) =
    validateExpectedPosition position
validateExpectedAttack
  (SList [SAtom "undermine", SAtom _, SAtom _, position]) =
    validateExpectedPosition position
validateExpectedAttack _ = malformedExpected

validateExpectedAudit :: SExpr -> Either String ()
validateExpectedAudit
  ( SList
      [ SAtom "audit"
      , SList (SAtom "leaves" : rows)
      , SList (SAtom "args" : args)
      , SList (SAtom "attacks" : attacks)
      ]
    ) = do
    mapM_ validateExpectedLeafRow rows
    mapM_ validateExpectedAtom args
    mapM_ validateExpectedAttack attacks
validateExpectedAudit _ = malformedExpected

-- | Exact grammar of 'encodeOutcome'. Nested junk is a codec error, not an
-- oracle mismatch after evaluation.
validateExpectedOutcome :: SExpr -> Either String ()
validateExpectedOutcome
  (SList [SAtom "invalid", SList [SAtom "duplicate-key", kindE, provenanceE]]) = do
    _ <- decodeKind kindE
    _ <- decodeProvenance provenanceE
    Right ()
validateExpectedOutcome
  (SList [SAtom "invalid", SList [SAtom "duplicate-leaf-id", SAtom _]]) =
    Right ()
validateExpectedOutcome
  (SList [SAtom "invalid", SAtom "metadata-leaf-misalignment"]) =
    Right ()
validateExpectedOutcome
  ( SList
      [ SAtom "rejected"
      , SList [SAtom "leaf", SAtom _]
      , SList [SAtom "kind", kindE]
      , SList [SAtom "provenance", provenanceE]
      , SList [SAtom "decision", SAtom "reject"]
      ]
    ) = do
    _ <- decodeKind kindE
    _ <- decodeProvenance provenanceE
    Right ()
validateExpectedOutcome (SList [SAtom "accepted", auditE]) =
  validateExpectedAudit auditE
validateExpectedOutcome _ = malformedExpected


-- | Exact @(admission (metas ...) (table ...) (unit ...) (expected ...))@.
decodeFixture :: SExpr -> Either String Fixture
decodeFixture (SList [SAtom "admission", metasE, tableE, unitE, expectedE]) = do
  metas <- decodeMetas metasE
  table <- decodeTable tableE
  expected <- case expectedE of
    SList [SAtom "expected", expectedX] -> Right expectedX
    _ -> Left "fixture: malformed expected section"
  _ <- validateExpectedOutcome expected
  Right (Fixture metas table unitE expected)
decodeFixture _ =
  Left "fixture: expected exact (admission (metas ...) (table ...) (unit ...) (expected ...))"

-- | Metadata is positionally aligned with the declared leaf table. Exact
-- order is part of the fixture contract because the production pipeline
-- derives both views from one declaration-ordered source list.
metadataLeafAligned :: [(LeafId, LeafKind, Provenance)] -> [(LeafId, Prop)] -> Bool
metadataLeafAligned metas leaves =
  map (\(l, _, _) -> l) metas == map fst leaves

-- | The first duplicate leaf id in declaration order (mirrors
-- "Lara.Elaborate".@firstDuplicateLeafId@).
firstDuplicateLeafId :: [LeafId] -> Maybe LeafId
firstDuplicateLeafId = go []
  where
    go _ [] = Nothing
    go seen (l : ls)
      | l `elem` seen = Just l
      | otherwise = go (l : seen) ls

-- | The declared 'Leaf' values: each meta bound to the unit's declared
-- proposition.  Alignment was validated, so the lookup is total.
bindLeaves
  :: [(LeafId, LeafKind, Provenance)]
  -> [(LeafId, Prop)]
  -> Either String [Leaf]
bindLeaves metas leaves = mapM bindOne metas
  where
    bindOne (lid, kind, provenance) =
      case find ((== lid) . fst) leaves of
        Just (_, prop) -> Right (Leaf lid prop kind provenance [])
        Nothing -> Left ("fixture: meta without declared leaf: " ++ unLeafId lid)

-- ---------------------------------------------------------------------------
-- Outcome encoding (canonical test encoding, mirrors the Lean twin)
-- ---------------------------------------------------------------------------

encodeKind :: LeafKind -> SExpr
encodeKind Observed = SAtom "observed"
encodeKind Attested = SAtom "attested"
encodeKind Assumed = SAtom "assumed"
encodeKind Certified = SAtom "certified"

encodeProvenance :: Provenance -> SExpr
encodeProvenance User = SAtom "user"
encodeProvenance AiExecuted = SAtom "ai"
encodeProvenance (Checker n v) = SList [SAtom "checker", SAtom n, SAtom v]

encodeDecision :: Admission -> SExpr
encodeDecision Admit = SAtom "admit"
encodeDecision Quarantine = SAtom "quarantine"
encodeDecision Reject = SAtom "reject"

encodeStep :: Step -> SExpr
encodeStep (StepPremise n) = SList [SAtom "prem", SAtom (show n)]
encodeStep (StepQuestion q) = SList [SAtom "ques", SAtom (unQuestionId q)]

encodeAttack :: Attack -> SExpr
encodeAttack (Rebut w u) = SList [SAtom "rebut", SAtom (unArgId w), SAtom (unArgId u)]
encodeAttack (Undercut w u pos) =
  SList [SAtom "undercut", SAtom (unArgId w), SAtom (unArgId u), SList (SAtom "pos" : map encodeStep pos)]
encodeAttack (Undermine w u pos) =
  SList [SAtom "undermine", SAtom (unArgId w), SAtom (unArgId u), SList (SAtom "pos" : map encodeStep pos)]

encodeCause :: AdmissionCause -> SExpr
encodeCause PolicyQuarantine = SList [SAtom "cause", SAtom "policy"]
encodeCause (GroupQuarantine g) = SList [SAtom "cause", SList [SAtom "group", SAtom (unGroupId g)]]

-- | The canonical audit encoding: leaf rows with non-empty causes (leaf
-- declaration order, policy cause first, then one cause per inconsistent
-- containing group in group declaration order), removed argument ids and
-- removed raw attacks in declaration order.
encodeAudit :: AdmissionAudit -> SExpr
encodeAudit audit =
  SList
    [ SAtom "audit"
    , SList
        ( SAtom "leaves"
            : [ SList
                  ( SAtom "leaf-row"
                      : SAtom (unLeafId leaf)
                      : map encodeCause causesList
                  )
              | (leaf, causes) <- admissionAuditLeaves audit
              , let causesList = toList causes
              ]
        )
    , SList (SAtom "args" : map (SAtom . unArgId) (admissionAuditArgs audit))
    , SList (SAtom "attacks" : map encodeAttack (admissionAuditAttacks audit))
    ]

encodeOutcome :: Either (LeafKind, Provenance) () -> Maybe AdmissionRejection -> AdmissionAudit -> SExpr
encodeOutcome (Left (kind, provenance)) _ _ =
  SList [SAtom "invalid", SList [SAtom "duplicate-key", encodeKind kind, encodeProvenance provenance]]
encodeOutcome (Right ()) (Just rejection) _ =
  SList
    [ SAtom "rejected"
    , SList [SAtom "leaf", SAtom (unLeafId (admissionRejectionLeaf rejection))]
    , SList [SAtom "kind", encodeKind (admissionRejectionKind rejection)]
    , SList [SAtom "provenance", encodeProvenance (admissionRejectionProvenance rejection)]
    , SList [SAtom "decision", encodeDecision (snd (admissionRejectionMatchedRow rejection))]
    ]
encodeOutcome (Right ()) Nothing audit =
  SList [SAtom "accepted", encodeAudit audit]

-- ---------------------------------------------------------------------------
-- The pipeline
-- ---------------------------------------------------------------------------

-- | The unit the admission model prunes: the wire-decoded declared unit with
-- the fixture's metadata bound into its leaves.
admissionUnit :: [Leaf] -> Unit -> Unit
admissionUnit boundLeaves unit =
  unit { unitLeaves = [(leafId leaf, leafProp leaf) | leaf <- boundLeaves] }

-- | The audit for an invalid or rejected source: no prune runs, so no rows
-- exist (the outcome encoding does not include it).
emptyAudit :: AdmissionAudit
emptyAudit =
  buildAdmissionAudit (pruneWithPolicySeed [] (admissionUnit [] emptyUnit))
  where
    emptyUnit =
      Unit
        { unitSigma = structuralSigma
        , unitRules = []
        , unitContraries = []
        , unitExceptions = []
        , unitTheories = []
        , unitLeaves = []
        , unitArgs = []
        , unitAttacks = []
        , unitQueries = []
        , unitGroups = []
        , unitGroupMode = QuarantineOnConflict
        }
-- | Decode one fixture and run the semantic adapter over production
-- admission/prune primitives. Invalidity precedence mirrors @prepareSource@:
-- duplicate admission key, duplicate leaf id, then the fixture-only ordered
-- metadata/leaf alignment check. Malformed fixture or unit syntax remains a
-- codec error.
admissionOutcome :: String -> Either String (String, String)
admissionOutcome contents = do
  e <- either (Left . show) Right (parseSExpr contents)
  fx <- decodeFixture e
  unit <- either (Left . (\(WireError c m) -> c ++ ": " ++ m)) Right (decodeUnit (fxUnit fx))
  let leaves = unitLeaves unit
      metaIds = map (\(l, _, _) -> l) (fxMetas fx)
      finish computed = Right (printSExpr computed, printSExpr (fxExpected fx))
  case validateAdmissionKeys (fxTable fx) of
    invalid@(Left _) ->
      finish (encodeOutcome invalid Nothing emptyAudit)
    Right () ->
      case firstDuplicateLeafId metaIds of
        Just dup ->
          finish (SList [SAtom "invalid", SList [SAtom "duplicate-leaf-id", SAtom (unLeafId dup)]])
        Nothing
          | not (metadataLeafAligned (fxMetas fx) leaves) ->
              finish (SList [SAtom "invalid", SAtom "metadata-leaf-misalignment"])
          | otherwise -> do
              boundLeaves <- bindLeaves (fxMetas fx) leaves
              let declared = admissionUnit boundLeaves unit
                  rejection = firstAdmissionRejection (fxTable fx) boundLeaves
                  audit =
                    case rejection of
                      Just _ -> emptyAudit
                      Nothing ->
                        let policySeed = policyQuarantineSeed (fxTable fx) boundLeaves
                         in buildAdmissionAudit (pruneWithPolicySeed policySeed declared)
              finish (encodeOutcome (Right ()) rejection audit)
