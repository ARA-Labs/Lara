-- | Constructor and side-condition conformance tests for "Lara.Update".
-- Lean remains the soundness oracle; these examples check that the Haskell
-- mirror makes the same four syntactic decisions on representative carriers.
module UpdateSpec (updateSpecProps) where

import Test.QuickCheck

import Lara.AST
  ( Admission (..)
  , ArgId (..)
  , DupGroup (..)
  , GroupId (..)
  , LeafId (..)
  , LeafKind (..)
  , Provenance (..)
  , SupportTerm (..)
  )
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

updateSpecProps :: [(String, IO Result)]
updateSpecProps =
  [ ("update addLeaf checks leaves, metadata, and group members",
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
