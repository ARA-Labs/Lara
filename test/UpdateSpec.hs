-- | Constructor and side-condition conformance tests for "Lara.Update".
-- Lean remains the soundness oracle; these examples check that the Haskell
-- mirror makes the same syntactic decisions on representative carriers,
-- including the in-place discharge rewrite and the raw stage of an atomic
-- batch. Acceptance of a batch (admission and checking) is Lean-only.
module UpdateSpec (updateSpecProps) where

import Data.List (isPrefixOf)
import Test.QuickCheck

import Lara.AST
  ( Admission (..)
  , ArgId (..)
  , Assurance (..)
  , DupGroup (..)
  , GroupId (..)
  , LeafId (..)
  , LeafKind (..)
  , ObligationId (..)
  , Provenance (..)
  , QuestionId (..)
  , RuleId (..)
  , Step (..)
  , SupportTerm (..)
  )
import Lara.Attack (subterm)
import Lara.Update

blankState :: SourceState
blankState =
  SourceState
    { sourceSigma = error "UpdateSpec: sourceSigma is not inspected by side conditions"
    , sourcePolicy = error "UpdateSpec: sourcePolicy is not inspected by side conditions"
    , sourceTable = []
    , sourceMetas = []
    , sourceLeaves = []
    , sourceArgsRaw = []
    , sourceRawAttacks = []
    , sourceGroups = []
    , sourceGround = []
    }

freshId, existingId, groupedId :: LeafId
freshId = LeafId "fresh"
existingId = LeafId "existing"
groupedId = LeafId "grouped"

meta :: LeafId -> LeafMeta
meta leaf = LeafMeta leaf Observed User

prop_addLeafChecksEveryCarrier :: Property
prop_addLeafChecksEveryCarrier =
  conjoin
    [ addLeafFreshB blankState freshId === True
    , addLeafFreshB
        blankState {sourceLeaves = [(existingId, error "unused proposition")]}
        existingId
        === False
    , addLeafFreshB blankState {sourceMetas = [meta existingId]} existingId
        === False
    , addLeafFreshB
        blankState {sourceGroups = [DupGroup (GroupId "g") [groupedId]]}
        groupedId
        === False
    ]

prop_tightenRequiresAdmit :: Property
prop_tightenRequiresAdmit =
  let key = (Observed, User)
   in conjoin
        [ admittedAtB blankState key === True
        , admittedAtB blankState {sourceTable = [(key, Admit)]} key === True
        , admittedAtB blankState {sourceTable = [(key, Quarantine)]} key === False
        , admittedAtB blankState {sourceTable = [(key, Reject)]} key === False
        ]

prop_admittedAtBFirstAdmitWins :: Property
prop_admittedAtBFirstAdmitWins =
  let key = (Observed, User)
      source = blankState {sourceTable = [(key, Admit), (key, Quarantine)]}
   in admittedAtB source key === True

prop_admittedAtBFirstQuarantineWins :: Property
prop_admittedAtBFirstQuarantineWins =
  let key = (Observed, User)
      source = blankState {sourceTable = [(key, Quarantine), (key, Admit)]}
   in admittedAtB source key === False

prop_addAttackRequiresBothEndpoints :: Property
prop_addAttackRequiresBothEndpoints =
  let termA = SLeaf (LeafId "a-leaf")
      termB = SLeaf (LeafId "b-leaf")
      argA = ArgId "a"
      argB = ArgId "b"
      missing = ArgId "missing"
      declared = blankState {sourceArgsRaw = [(argA, termA), (argB, termB)]}
   in conjoin
        [ endpointDeclaredB declared (RawRebut argA argB) === True
        , endpointDeclaredB declared (RawUndercut missing argB []) === False
        , endpointDeclaredB declared (RawUndermine argA missing []) === False
        ]

prop_addInstanceRequiresNameAndTermFreshness :: Property
prop_addInstanceRequiresNameAndTermFreshness =
  let oldName = ArgId "old"
      newName = ArgId "new"
      oldTerm = SLeaf (LeafId "old")
      newTerm = SLeaf (LeafId "new")
      declared = blankState {sourceArgsRaw = [(oldName, oldTerm)]}
   in conjoin
        [ instanceFreshB declared newName newTerm === True
        , instanceFreshB declared oldName newTerm === False
        , instanceFreshB declared newName oldTerm === False
        ]

prop_updatePreconditionAddLeaf :: Property
prop_updatePreconditionAddLeaf =
  let proposition = error "UpdateSpec: addLeaf proposition is not inspected"
      occupied = blankState {sourceLeaves = [(existingId, proposition)]}
   in conjoin
        [ updatePrecondition blankState (AddLeaf freshId proposition (meta freshId))
            === Nothing
        , updatePrecondition occupied (AddLeaf existingId proposition (meta existingId))
            === Just (LeafNotFresh existingId)
        ]

prop_updatePreconditionTighten :: Property
prop_updatePreconditionTighten =
  let key = (Observed, User)
      rejected = blankState {sourceTable = [(key, Quarantine)]}
   in conjoin
        [ updatePrecondition blankState (Tighten key) === Nothing
        , updatePrecondition rejected (Tighten key)
            === Just (KeyNotAdmitted key)
        ]

prop_updatePreconditionAddAttack :: Property
prop_updatePreconditionAddAttack =
  let argA = ArgId "a"
      argB = ArgId "b"
      missing = ArgId "missing"
      termA = SLeaf (LeafId "a-leaf")
      termB = SLeaf (LeafId "b-leaf")
      declared = blankState {sourceArgsRaw = [(argA, termA), (argB, termB)]}
      acceptedAttack = RawRebut argA argB
      rejectedAttack = RawRebut argA missing
   in conjoin
        [ updatePrecondition declared (AddAttack acceptedAttack) === Nothing
        , updatePrecondition declared (AddAttack rejectedAttack)
            === Just (EndpointNotDeclared rejectedAttack)
        ]

prop_updatePreconditionAddInstance :: Property
prop_updatePreconditionAddInstance =
  let oldName = ArgId "old"
      newName = ArgId "new"
      oldTerm = SLeaf (LeafId "old")
      newTerm = SLeaf (LeafId "new")
      declared = blankState {sourceArgsRaw = [(oldName, oldTerm)]}
   in conjoin
        [ updatePrecondition declared (AddInstance newName newTerm) === Nothing
        , updatePrecondition declared (AddInstance oldName newTerm)
            === Just (InstanceNotFresh oldName newTerm)
        ]

-- In-place discharge and atomic batches -------------------------------------

q1, q2 :: QuestionId
q1 = QuestionId "q1"
q2 = QuestionId "q2"

-- | A rule instance leaving mandatory @q1@ and optional @q2@ open.
holeTerm :: SupportTerm
holeTerm = SRule (RuleId "rmix") [] [] [] [ObligationId "q1", ObligationId "q2"] AssuranceNone

-- | A wrapper whose only premise is the hole.
wrapTerm :: SupportTerm
wrapTerm = SRule (RuleId "rwrap") [] [holeTerm] [] [] AssuranceNone

answer :: SupportTerm
answer = SLeaf (LeafId "l2")

completionBase :: SourceState
completionBase =
  blankState
    { sourceLeaves = [(LeafId "l1", error "unused proposition")]
    , sourceMetas = [meta (LeafId "l1")]
    , sourceArgsRaw = [(ArgId "a", SLeaf (LeafId "l1")), (ArgId "h", wrapTerm)]
    }

prop_dischargeOpenSiteDecider :: Property
prop_dischargeOpenSiteDecider =
  conjoin
    [ dischargeOpenB completionBase (ArgId "h") [StepPremise 0] q1 === True
    , dischargeOpenB completionBase (ArgId "h") [StepPremise 0] q2 === True
    , dischargeOpenB completionBase (ArgId "h") [] q1 === False
    , dischargeOpenB completionBase (ArgId "h") [StepPremise 1] q1 === False
    , dischargeOpenB completionBase (ArgId "a") [] q1 === False
    , dischargeOpenB completionBase (ArgId "missing") [] q1 === False
    , updatePrecondition completionBase (DischargeOpen (ArgId "a") [] q1 answer)
        === Just (NotDischargeable (ArgId "a") [] q1)
    , updatePrecondition completionBase (DischargeOpen (ArgId "h") [StepPremise 0] q1 answer)
        === Nothing
    ]

prop_dischargeAtAppendsAndCloses :: Property
prop_dischargeAtAppendsAndCloses =
  dischargeAt q1 answer [StepPremise 0] wrapTerm
    === Just
      ( SRule
          (RuleId "rwrap")
          []
          [SRule (RuleId "rmix") [] [] [(q1, answer)] [ObligationId "q2"] AssuranceNone]
          []
          []
          AssuranceNone
      )

-- | Every position defined before the discharge stays defined, and the new
-- edge @π.q@ addresses the discharge term.
prop_dischargeAtKeepsPositions :: Property
prop_dischargeAtKeepsPositions =
  case dischargeAt q1 answer [StepPremise 0] wrapTerm of
    Nothing -> counterexample "discharge site rejected" False
    Just rewritten ->
      conjoin
        [ fmap (const ()) (subterm rewritten pos) === fmap (const ()) (subterm wrapTerm pos)
        | pos <- [[], [StepPremise 0], [StepPremise 1]]
        ]
        .&&. subterm rewritten [StepPremise 0, StepQuestion q1] === Just answer

prop_dischargeRowsKeepNamesAndPositions :: Property
prop_dischargeRowsKeepNamesAndPositions =
  let rows = sourceArgsRaw completionBase
      rewritten = dischargeRows rows (ArgId "h") [StepPremise 0] q1 answer
   in conjoin
        [ map fst rewritten === map fst rows
        , take 1 rewritten === take 1 rows
        , lookup (ArgId "h") rewritten =/= lookup (ArgId "h") rows
        ]

coverAttack :: RawAttack
coverAttack = RawUndermine (ArgId "b") (ArgId "a") []

prop_batchEndpointAlignment :: Property
prop_batchEndpointAlignment =
  conjoin
    [ fmap sourceRawAttacks
        (applyBatch completionBase [EditAddInstance (ArgId "b") answer, EditAddAttack coverAttack])
        === Right [coverAttack]
    , applyBatch completionBase [EditAddAttack coverAttack, EditAddInstance (ArgId "b") answer]
        === Left (BatchEdit 0 (EndpointNotDeclared coverAttack))
    , updatePrecondition completionBase (AddAttack coverAttack)
        === Just (EndpointNotDeclared coverAttack)
    , updatePrecondition
        completionBase
        (Atomic [EditAddInstance (ArgId "b") answer, EditAddAttack coverAttack])
        === Nothing
    ]

prop_batchReportsFirstFailingEdit :: Property
prop_batchReportsFirstFailingEdit =
  applyBatch
    completionBase
    [ EditAddInstance (ArgId "b") answer
    , EditDischargeOpen (ArgId "a") [] q1 answer
    , EditAddInstance (ArgId "b") answer
    ]
    === Left (BatchEdit 1 (NotDischargeable (ArgId "a") [] q1))

-- | A small edit alphabet over 'completionBase', including edits that fail.
editAlphabet :: [AtomicEdit]
editAlphabet =
  [ EditAddLeaf (LeafId "n") (error "unused proposition") (meta (LeafId "n"))
  , EditAddLeaf (LeafId "l1") (error "unused proposition") (meta (LeafId "l1"))
  , EditAddInstance (ArgId "b") answer
  , EditAddInstance (ArgId "a") (SLeaf (LeafId "y"))
  , EditAddAttack coverAttack
  , EditAddAttack (RawRebut (ArgId "h") (ArgId "a"))
  , EditDischargeOpen (ArgId "h") [StepPremise 0] q1 answer
  , EditDischargeOpen (ArgId "a") [] q1 answer
  ]

isAdditive :: AtomicEdit -> Bool
isAdditive edit = case edit of
  EditDischargeOpen {} -> False
  _ -> True

-- | Raw identities across any successful batch: attacks and leaves only grow
-- at the end, argument names keep their positions, and an additive batch keeps
-- every argument row (Lean @applyBatchFrom_prefix@).
prop_batchKeepsRawIdentities :: Property
prop_batchKeepsRawIdentities =
  forAll (listOf (elements editAlphabet)) $ \batch ->
    case applyBatch completionBase batch of
      Left _ -> property True
      Right final ->
        conjoin
          [ property (sourceRawAttacks completionBase `isPrefixOf` sourceRawAttacks final)
          , property (map fst (sourceLeaves completionBase) `isPrefixOf` map fst (sourceLeaves final))
          , property (map fst (sourceArgsRaw completionBase) `isPrefixOf` map fst (sourceArgsRaw final))
          , property
              ( not (all isAdditive batch)
                  || sourceArgsRaw completionBase `isPrefixOf` sourceArgsRaw final
              )
          ]

-- | A rejected batch reports exactly the first edit whose side condition
-- fails against the state the earlier edits produced.
prop_batchRejectsAtFirstFailure :: Property
prop_batchRejectsAtFirstFailure =
  forAll (listOf (elements editAlphabet)) $ \batch ->
    case applyBatch completionBase batch of
      Right _ -> property True
      Left (BatchEdit index reason) ->
        let prefix = take index batch
            failing = batch !! index
         in case applyBatch completionBase prefix of
              Left _ -> counterexample "prefix of the failing edit was rejected" False
              Right state -> applyRawEdit state failing === Left reason
      Left other -> counterexample ("unexpected rejection " ++ show other) False

updateSpecProps :: [(String, IO Result)]
updateSpecProps =
  [ ("update dischargeOpen decides the declared open site",
      quickCheckResult prop_dischargeOpenSiteDecider)
  , ("update dischargeAt appends the discharge and closes the question",
      quickCheckResult prop_dischargeAtAppendsAndCloses)
  , ("update dischargeAt keeps every old position",
      quickCheckResult prop_dischargeAtKeepsPositions)
  , ("update dischargeRows keeps argument names and positions",
      quickCheckResult prop_dischargeRowsKeepNamesAndPositions)
  , ("update atomic batch checks endpoints against the intermediate state",
      quickCheckResult prop_batchEndpointAlignment)
  , ("update atomic batch reports its first failing edit",
      quickCheckResult prop_batchReportsFirstFailingEdit)
  , ("update atomic batch keeps raw identities",
      quickCheckResult prop_batchKeepsRawIdentities)
  , ("update atomic batch rejects at the first failure",
      quickCheckResult prop_batchRejectsAtFirstFailure)
  , ("update addLeaf checks leaves, metadata, and group members",
      quickCheckResult prop_addLeafChecksEveryCarrier)
  , ("update tighten requires admit at the key",
      quickCheckResult prop_tightenRequiresAdmit)
  , ("update admittedAtB uses the first duplicate admit row",
      quickCheckResult prop_admittedAtBFirstAdmitWins)
  , ("update admittedAtB uses the first duplicate quarantine row",
      quickCheckResult prop_admittedAtBFirstQuarantineWins)
  , ("update addAttack requires both declared endpoints",
      quickCheckResult prop_addAttackRequiresBothEndpoints)
  , ("update addInstance requires fresh name and support term",
      quickCheckResult prop_addInstanceRequiresNameAndTermFreshness)
  , ("update precondition maps addLeaf failures",
      quickCheckResult prop_updatePreconditionAddLeaf)
  , ("update precondition maps tighten failures",
      quickCheckResult prop_updatePreconditionTighten)
  , ("update precondition maps addAttack failures",
      quickCheckResult prop_updatePreconditionAddAttack)
  , ("update precondition maps addInstance failures",
      quickCheckResult prop_updatePreconditionAddInstance)
  ]
