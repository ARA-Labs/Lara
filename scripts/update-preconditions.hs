{-# OPTIONS_GHC -Wall -Werror #-}

-- | Exhaustive finite input spaces for the four constructor-side deciders in
-- "Lara.Update". The Lean emitter prints the same canonical rows.
module Main (main) where

import Data.List (intercalate)

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

main :: IO ()
main = putStr (unlines (leafRows ++ admissionRows ++ endpointRows ++ instanceRows))
