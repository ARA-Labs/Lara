{-# OPTIONS_GHC -Wall -Werror #-}

-- | Exhaustive finite input spaces for the constructor-side deciders in
-- "Lara.Update", the in-place discharge rewrite, and the raw stage of an atomic
-- batch. The Lean emitter prints the same canonical rows.
module Main (main) where

import Data.List (intercalate)

import Lara.AST
  ( Admission (..)
  , ArgId (..)
  , DupGroup (..)
  , GroupId (..)
  , Assurance (..)
  , LeafId (..)
  , LeafKind (..)
  , ObligationId (..)
  , Provenance (..)
  , QuestionId (..)
  , RuleId (..)
  , Step (..)
  , SupportTerm (..)
  )
import Lara.Update

blankState :: SourceState
blankState =
  SourceState
    { sourceSigma = error "update-preconditions: sigma is not inspected"
    , sourcePolicy = error "update-preconditions: policy is not inspected"
    , sourceTable = []
    , sourceMetas = []
    , sourceLeaves = []
    , sourceArgsRaw = []
    , sourceRawAttacks = []
    , sourceGroups = []
    , sourceGround = []
    }

boolText :: Bool -> String
boolText value = if value then "true" else "false"

bit :: Bool -> String
bit value = if value then "1" else "0"

row :: [String] -> String
row = intercalate "\t"

candidateLeaf :: LeafId
candidateLeaf = LeafId "candidate"

leafRows :: [String]
leafRows =
  [ row
      [ "addLeafFreshB"
      , "leaves=" ++ bit inLeaves
      , "metas=" ++ bit inMetas
      , "groups=" ++ bit inGroups
      , boolText (addLeafFreshB source candidateLeaf)
      ]
  | inLeaves <- [False, True]
  , inMetas <- [False, True]
  , inGroups <- [False, True]
  , let source =
          blankState
            { sourceLeaves =
                if inLeaves then [(candidateLeaf, error "proposition is not inspected")] else []
            , sourceMetas =
                if inMetas then [LeafMeta candidateLeaf Observed User] else []
            , sourceGroups =
                if inGroups then [DupGroup (GroupId "g") [candidateLeaf]] else []
            }
  ]

admissionName :: Admission -> String
admissionName decision = case decision of
  Admit -> "admit"
  Quarantine -> "quarantine"
  Reject -> "reject"

admissionTables :: [[Admission]]
admissionTables =
  [[]]
    ++ [[first] | first <- decisions]
    ++ [[first, second] | first <- decisions, second <- decisions]
  where
    decisions = [Admit, Quarantine, Reject]

admissionRows :: [String]
admissionRows =
  [ row
      [ "admittedAtB"
      , "table=" ++ case decisions of
          [] -> "omitted"
          _ -> intercalate "," (map admissionName decisions)
      , boolText (admittedAtB source key)
      ]
  | decisions <- admissionTables
  , let key = (Observed, User)
        source = blankState {sourceTable = [(key, decision) | decision <- decisions]}
  ]

endpointRows :: [String]
endpointRows =
  [ row
      [ "endpointDeclaredB"
      , "kind=" ++ kind
      , "source=" ++ bit sourceDeclared
      , "target=" ++ bit targetDeclared
      , boolText (endpointDeclaredB source attack)
      ]
  | (kind, makeAttack) <- attackKinds
  , sourceDeclared <- [False, True]
  , targetDeclared <- [False, True]
  , let sourceName = ArgId "source"
        targetName = ArgId "target"
        source =
          blankState
            { sourceArgsRaw =
                [(sourceName, SLeaf (LeafId "source-term")) | sourceDeclared]
                  ++ [(targetName, SLeaf (LeafId "target-term")) | targetDeclared]
            }
        attack = makeAttack sourceName targetName
  ]
  where
    attackKinds =
      [ ("rebut", \source target -> RawRebut source target)
      , ("undercut", \source target -> RawUndercut source target [])
      , ("undermine", \source target -> RawUndermine source target [])
      ]

instanceRows :: [String]
instanceRows =
  [ row
      [ "instanceFreshB"
      , "name=" ++ bit nameCollision
      , "term=" ++ bit termCollision
      , boolText (instanceFreshB source candidateName candidateTerm)
      ]
  | nameCollision <- [False, True]
  , termCollision <- [False, True]
  , let candidateName = ArgId "candidate"
        otherName = ArgId "other"
        candidateTerm = SLeaf (LeafId "candidate-term")
        otherTerm = SLeaf (LeafId "other-term")
        source =
          blankState
            { sourceArgsRaw =
                [(candidateName, otherTerm) | nameCollision]
                  ++ [(otherName, candidateTerm) | termCollision]
            }
  ]

openInst, closedInst, wrapInst :: SupportTerm
openInst = SRule (RuleId "r") [] [] [] [ObligationId "q1"] AssuranceNone
closedInst = SRule (RuleId "r") [] [] [] [] AssuranceNone
wrapInst =
  SRule (RuleId "w") [] [openInst] [(QuestionId "q2", SLeaf (LeafId "d"))] [] AssuranceNone

-- | Canonical rendering shared with the Lean emitter:
-- @rule(premises;question=discharge;open)@.
renderTerm :: SupportTerm -> String
renderTerm term = case term of
  SLeaf (LeafId l) -> l
  SRule (RuleId r) _ premises discharges holes _ ->
    r
      ++ "("
      ++ intercalate "," (map renderTerm premises)
      ++ ";"
      ++ intercalate "," [q ++ "=" ++ renderTerm w | (QuestionId q, w) <- discharges]
      ++ ";"
      ++ intercalate "," [o | ObligationId o <- holes]
      ++ ")"

dischargeRowsTsv :: [String]
dischargeRowsTsv =
  [ row
      [ "dischargeOpenB"
      , "declared=" ++ bit declared
      , "term=" ++ shapeName
      , "pos=" ++ posName
      , "q=" ++ qName
      , boolText decided
      , "result=" ++ result
      ]
  | declared <- [False, True]
  , (shapeName, term) <- shapes
  , (posName, pos) <- positions
  , (qName, q) <- questions
  , let source = blankState {sourceArgsRaw = [(ArgId "t", term) | declared]}
        decided = dischargeOpenB source (ArgId "t") pos q
        result
          | decided = case dischargeRows (sourceArgsRaw source) (ArgId "t") pos q (SLeaf (LeafId "v")) of
              [(_, rewritten)] -> renderTerm rewritten
              _ -> "?"
          | otherwise = "-"
  ]
  where
    shapes =
      [ ("leaf", SLeaf (LeafId "x"))
      , ("open", openInst)
      , ("closed", closedInst)
      , ("wrap", wrapInst)
      ]
    positions =
      [ ("eps", [])
      , ("prem0", [StepPremise 0])
      , ("prem1", [StepPremise 1])
      , ("q2", [StepQuestion (QuestionId "q2")])
      ]
    questions = [("q1", QuestionId "q1"), ("q2", QuestionId "q2")]

batchBase :: SourceState
batchBase =
  blankState
    { sourceLeaves = [(LeafId "x", error "proposition is not inspected")]
    , sourceMetas = [LeafMeta (LeafId "x") Observed User]
    , sourceArgsRaw = [(ArgId "a", SLeaf (LeafId "x")), (ArgId "h", openInst)]
    }

edits :: [(String, AtomicEdit)]
edits =
  [ ("leafNew", EditAddLeaf (LeafId "n") unused (LeafMeta (LeafId "n") Observed User))
  , ("leafOld", EditAddLeaf (LeafId "x") unused (LeafMeta (LeafId "x") Observed User))
  , ("instNew", EditAddInstance (ArgId "b") (SLeaf (LeafId "n")))
  , ("instDup", EditAddInstance (ArgId "a") (SLeaf (LeafId "y")))
  , ("attNew", EditAddAttack (RawRebut (ArgId "b") (ArgId "a")))
  , ("attOld", EditAddAttack (RawRebut (ArgId "h") (ArgId "a")))
  , ("disOk", EditDischargeOpen (ArgId "h") [] (QuestionId "q1") (SLeaf (LeafId "n")))
  , ("disBad", EditDischargeOpen (ArgId "a") [] (QuestionId "q1") (SLeaf (LeafId "n")))
  ]
  where
    unused = error "proposition is not inspected"

renderRejection :: UpdateRejection -> String
renderRejection reason = case reason of
  BatchEdit index inner -> "batchEdit " ++ show index ++ " " ++ inner'
    where
      inner' = case inner of
        BatchEdit _ _ -> "other"
        _ -> renderRejection inner
  LeafNotFresh (LeafId l) -> "leafNotFresh " ++ l
  InstanceNotFresh (ArgId name) _ -> "instanceNotFresh " ++ name
  EndpointNotDeclared _ -> "endpointNotDeclared"
  NotDischargeable (ArgId name) _ (QuestionId q) -> "notDischargeable " ++ name ++ " " ++ q
  KeyNotAdmitted _ -> "other"

renderState :: SourceState -> String
renderState state =
  "args="
    ++ intercalate "," [name ++ ":" ++ renderTerm term | (ArgId name, term) <- sourceArgsRaw state]
    ++ " atts="
    ++ show (length (sourceRawAttacks state))
    ++ " leaves="
    ++ intercalate "," [l | (LeafId l, _) <- sourceLeaves state]

batchRows :: [String]
batchRows =
  [ row
      [ "applyBatch"
      , "edits=" ++ if null batch then "none" else intercalate "," (map fst batch)
      , case applyBatch batchBase (map snd batch) of
          Right state -> "ok " ++ renderState state
          Left reason -> "error " ++ renderRejection reason
      ]
  | batch <- [[]] ++ [[e] | e <- edits] ++ [[e, f] | e <- edits, f <- edits]
  ]

main :: IO ()
main =
  putStr
    ( unlines
        ( leafRows
            ++ admissionRows
            ++ endpointRows
            ++ instanceRows
            ++ dischargeRowsTsv
            ++ batchRows
        )
    )
