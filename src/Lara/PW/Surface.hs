-- | The possible-world outer surface (#307, #313, #314): the Haskell mirror of
-- the authoring AST in @lean\/Lara\/PW\/Surface.lean@.
--
-- A 'BridgeDecl' declares a bridge between two named contexts, with its
-- symbol map, evidence-leaf map, and the three structural clauses of T6's
-- contract. An 'SForm' is an /unelaborated/ modal query: claims are raw
-- 'Prop's and modalities name a bridge by identifier. "Lara.PW.Run" types it
-- against a loaded host; "Lara.PW.Wire" reads it from @pw-surface 1@ text.
--
-- Symbolic, per the repository's core discipline: contexts and bridges are
-- distinct newtypes, and the clause vocabulary is a closed sum whose spelling
-- lives only in 'clauseText'.
module Lara.PW.Surface
  ( CtxId (..)
  , BridgeId (..)
  , SymEntry (..)
  , LeafEntry (..)
  , Clause (..)
  , clauseText
  , clauseAll
  , BridgeDecl (..)
  , SForm (..)
  , Posed (..)
  , Document (..)
  ) where

import Lara.AST (LeafId, Status)
import Lara.Prop (FunSym, Pred, Prop)

-- | A scientific-context identifier (Lean @CtxId@).
newtype CtxId = CtxId String
  deriving (Eq, Ord, Show)

-- | A bridge identifier (Lean @BridgeId@).
newtype BridgeId = BridgeId String
  deriving (Eq, Ord, Show)

-- | One entry of a declared symbol map. Predicates and constructors are
-- separate namespaces, as in the core AST.
data SymEntry
  = SymPred Pred Pred
  | SymCon FunSym FunSym
  deriving (Eq, Show)

-- | One entry of a declared evidence-leaf renaming.
data LeafEntry = LeafEntry
  { leafEntrySource :: LeafId
  , leafEntryTarget :: LeafId
  }
  deriving (Eq, Show)

-- | The three structural clauses a bridge declaration states (Lean @Clause@).
data Clause = ClauseLeafOk | ClauseRuleOk | ClauseCertOk
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The one spelling table for 'Clause'.
clauseText :: Clause -> String
clauseText c = case c of
  ClauseLeafOk -> "leaf-ok"
  ClauseRuleOk -> "rule-ok"
  ClauseCertOk -> "cert-ok"

-- | Every clause, in declaration order: the scan order of the loader's
-- completeness check (Lean @Clause.all@). Enumerated from the type, so a new
-- clause cannot silently stop being required.
clauseAll :: [Clause]
clauseAll = [minBound .. maxBound]

-- | A bridge declaration; every list keeps authored order (Lean @BridgeDecl@).
data BridgeDecl = BridgeDecl
  { bdId :: BridgeId
  , bdSource :: CtxId
  , bdTarget :: CtxId
  , bdSymbols :: [SymEntry]
  , bdLeaves :: [LeafEntry]
  , bdClauses :: [Clause]
  }
  deriving (Eq, Show)

-- | A modal query, unelaborated (Lean @SForm@): PW0's grammar and nothing
-- more.
data SForm
  = SStatus Status Prop
  | STop
  | SNeg SForm
  | SConj SForm SForm
  | SBox BridgeId SForm
  | SDia BridgeId SForm
  deriving (Eq, Show)

-- | A query and the context it is posed in (Lean @Posed@).
data Posed = Posed
  { posedContext :: CtxId
  , posedForm :: SForm
  }
  deriving (Eq, Show)

-- | The @pw-surface 1@ unit of authoring (Lean @Wire.Document@).
data Document = Document
  { docBridges :: [BridgeDecl]
  , docQueries :: [Posed]
  }
  deriving (Eq, Show)
