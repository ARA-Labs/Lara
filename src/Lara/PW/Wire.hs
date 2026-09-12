-- | The @pw-surface 1@ authoring codec (#314) and the @pw-run 1@ execution
-- codec (#322): the Haskell mirror of @lean\/Lara\/PW\/Wire.lean@ and the codec
-- half of @lean\/Lara\/PW\/Run.lean@.
--
-- Text reading and printing reuse "Lara.Wire"'s reader and printer, so quoting,
-- escapes and comments are the inner checker wire's. The structured decoders
-- here transcribe Lean's constructor by constructor, including the order in
-- which sections decode and the /what/ each @malformed@ failure names, because
-- the differential gate compares both runtimes' error envelopes. Consumers
-- branch on the 'CodecErrorTag', never on the detail text.
--
-- A world's check-input envelope is carried as an untyped 'SExpr' at this
-- layer and decoded when the world is loaded: the envelope is the frozen local
-- wire, and a malformed one is a world-loading failure, not a run-codec one.
module Lara.PW.Wire
  ( -- * Errors
    CodecErrorTag (..)
  , codecErrorTagText
  , CodecError (..)
    -- * The @pw-surface 1@ document
  , surfaceVersion
  , encodeDocument
  , decodeDocument
  , encodeAtom
  , encodeStatus
    -- * The @pw-run 1@ document
  , WorldId (..)
  , Acceptance (..)
  , acceptanceText
  , WorldSource (..)
  , WorldDecl (..)
  , EdgeDecl (..)
  , CompareDecl (..)
  , RunDoc (..)
  , runVersion
  , encodeRun
  , decodeRun
    -- * Text
  , parseRunBS
  , printRun
  ) where

import Data.ByteString (ByteString)
import qualified Data.Map.Strict as Map

import Lara.AST (LeafId (..), Status (..))
import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term)
import qualified Lara.Prop as P
import Lara.PW.Surface
import Lara.Strict (SExpr (..))
import qualified Lara.Wire as W

-- ---------------------------------------------------------------------------
-- Errors
-- ---------------------------------------------------------------------------

-- | Stable failure categories (Lean @Wire.ErrorTag@).
data CodecErrorTag = CodecSyntax | CodecMalformed | CodecUnsupportedVersion
  deriving (Eq, Show)

codecErrorTagText :: CodecErrorTag -> String
codecErrorTagText t = case t of
  CodecSyntax -> "syntax"
  CodecMalformed -> "malformed"
  CodecUnsupportedVersion -> "unsupported-version"

-- | A category and its boundary detail (Lean @Wire.Error@).
data CodecError = CodecError
  { codecErrorTag :: CodecErrorTag
  , codecErrorDetail :: String
  }
  deriving (Eq, Show)

malformed :: String -> Either CodecError a
malformed = Left . CodecError CodecMalformed

-- ---------------------------------------------------------------------------
-- The surface vocabulary (Lean @Wire.Tag@)
-- ---------------------------------------------------------------------------

data STag
  = TDocument | TBridges | TQueries | TBridge | TSymbols | TLeaves | TClauses
  | TPred | TCon | TLeaf | TPose | TStatusF | TTop | TNeg | TConj | TBox | TDia
  | TAtom | TNum | TStr
  deriving (Eq, Show, Enum, Bounded)

-- | @num@, @str@, @con@ and @atom@ encode the inner checker wire's term and
-- atom shape, so their spellings come from "Lara.Wire"'s table.
sTagText :: STag -> String
sTagText t = case t of
  TDocument -> "pw-surface"
  TBridges -> "bridges"
  TQueries -> "queries"
  TBridge -> "bridge"
  TSymbols -> "symbols"
  TLeaves -> "leaves"
  TClauses -> "clauses"
  TPred -> "pred"
  TCon -> W.tagToString W.TConApp
  TLeaf -> "leaf"
  TPose -> "pose"
  TStatusF -> "status"
  TTop -> "top"
  TNeg -> "not"
  TConj -> "and"
  TBox -> "box"
  TDia -> "dia"
  TAtom -> W.tagToString W.TAtom
  TNum -> W.tagToString W.TNumLit
  TStr -> W.tagToString W.TStrLit

{-# NOINLINE sTagTable #-}
sTagTable :: Map.Map String STag
sTagTable = Map.fromList [(sTagText t, t) | t <- [minBound .. maxBound]]

sTagged :: STag -> [SExpr] -> SExpr
sTagged t args = SList (SAtom (sTagText t) : args)

sHead :: SExpr -> Maybe (STag, [SExpr])
sHead e = case e of
  SList (SAtom s : args) -> (\t -> (t, args)) <$> Map.lookup s sTagTable
  _ -> Nothing

sSection :: STag -> SExpr -> Either CodecError [SExpr]
sSection t e = case sHead e of
  Just (found, xs) | found == t -> Right xs
  _ -> malformed (sTagText t)

-- ---------------------------------------------------------------------------
-- The @pw-surface 1@ document
-- ---------------------------------------------------------------------------

surfaceVersion :: String
surfaceVersion = "1"

encodeTerm :: Term -> SExpr
encodeTerm t = case t of
  P.TNum s -> sTagged TNum [SAtom s]
  P.TStr s -> sTagged TStr [SAtom s]
  P.TCon (FunSym k) ts -> sTagged TCon (SAtom k : map encodeTerm ts)

decodeTerm :: SExpr -> Either CodecError Term
decodeTerm e = case sHead e of
  Just (TNum, [SAtom s]) -> Right (P.TNum s)
  Just (TStr, [SAtom s]) -> Right (P.TStr s)
  Just (TCon, SAtom k : ts) -> P.TCon (FunSym k) <$> mapM decodeTerm ts
  _ -> malformed "term"

encodeAtom :: Prop -> SExpr
encodeAtom (Prop (Pred p) ts) = sTagged TAtom (SAtom p : map encodeTerm ts)

decodeAtom :: SExpr -> Either CodecError Prop
decodeAtom e = case sHead e of
  Just (TAtom, SAtom p : ts) -> Prop (Pred p) <$> mapM decodeTerm ts
  _ -> malformed "atom"

-- | Status spellings are the inner verdict's.
statusTag :: Status -> W.Tag
statusTag s = case s of
  Justified -> W.TJustified
  Contested -> W.TContested
  Defeated -> W.TDefeated
  Gap -> W.TGap

encodeStatus :: Status -> SExpr
encodeStatus = SAtom . W.tagToString . statusTag

decodeStatus :: SExpr -> Either CodecError Status
decodeStatus e = case e of
  SAtom s | Just st <- lookup s [(W.tagToString (statusTag st), st) | st <- statuses] -> Right st
  _ -> malformed "status"
  where
    statuses = [Justified, Contested, Defeated, Gap]

decodeClause :: SExpr -> Either CodecError Clause
decodeClause e = case e of
  SAtom s | Just c <- lookup s [(clauseText c, c) | c <- clauseAll] -> Right c
  _ -> malformed "clause"

encodeSymEntry :: SymEntry -> SExpr
encodeSymEntry entry = case entry of
  SymPred (Pred s) (Pred t) -> sTagged TPred [SAtom s, SAtom t]
  SymCon (FunSym s) (FunSym t) -> sTagged TCon [SAtom s, SAtom t]

decodeSymEntry :: SExpr -> Either CodecError SymEntry
decodeSymEntry e = case sHead e of
  Just (TPred, [SAtom s, SAtom t]) -> Right (SymPred (Pred s) (Pred t))
  Just (TCon, [SAtom s, SAtom t]) -> Right (SymCon (FunSym s) (FunSym t))
  _ -> malformed "symbol-entry"

encodeLeafEntry :: LeafEntry -> SExpr
encodeLeafEntry (LeafEntry (LeafId s) (LeafId t)) = sTagged TLeaf [SAtom s, SAtom t]

decodeLeafEntry :: SExpr -> Either CodecError LeafEntry
decodeLeafEntry e = case sHead e of
  Just (TLeaf, [SAtom s, SAtom t]) -> Right (LeafEntry (LeafId s) (LeafId t))
  _ -> malformed "leaf-entry"

encodeBridgeDecl :: BridgeDecl -> SExpr
encodeBridgeDecl d =
  sTagged
    TBridge
    [ SAtom b
    , SAtom s
    , SAtom t
    , sTagged TSymbols (map encodeSymEntry (bdSymbols d))
    , sTagged TLeaves (map encodeLeafEntry (bdLeaves d))
    , sTagged TClauses (map (SAtom . clauseText) (bdClauses d))
    ]
  where
    BridgeId b = bdId d
    CtxId s = bdSource d
    CtxId t = bdTarget d

-- | Each section is read and fully decoded before the next one's header.
decodeBridgeDecl :: SExpr -> Either CodecError BridgeDecl
decodeBridgeDecl e = case sHead e of
  Just (TBridge, [SAtom b, SAtom s, SAtom t, syms, leaves, clauses]) -> do
    symbols <- sSection TSymbols syms >>= mapM decodeSymEntry
    leafEntries <- sSection TLeaves leaves >>= mapM decodeLeafEntry
    clauseList <- sSection TClauses clauses >>= mapM decodeClause
    pure (BridgeDecl (BridgeId b) (CtxId s) (CtxId t) symbols leafEntries clauseList)
  _ -> malformed "bridge"

encodeForm :: SForm -> SExpr
encodeForm f = case f of
  SStatus s a -> sTagged TStatusF [encodeStatus s, encodeAtom a]
  STop -> sTagged TTop []
  SNeg g -> sTagged TNeg [encodeForm g]
  SConj g h -> sTagged TConj [encodeForm g, encodeForm h]
  SBox (BridgeId b) g -> sTagged TBox [SAtom b, encodeForm g]
  SDia (BridgeId b) g -> sTagged TDia [SAtom b, encodeForm g]

decodeForm :: SExpr -> Either CodecError SForm
decodeForm e = case sHead e of
  Just (TStatusF, [s, a]) -> SStatus <$> decodeStatus s <*> decodeAtom a
  Just (TTop, []) -> Right STop
  Just (TNeg, [f]) -> SNeg <$> decodeForm f
  Just (TConj, [f, g]) -> SConj <$> decodeForm f <*> decodeForm g
  Just (TBox, [SAtom b, f]) -> SBox (BridgeId b) <$> decodeForm f
  Just (TDia, [SAtom b, f]) -> SDia (BridgeId b) <$> decodeForm f
  _ -> malformed "formula"

encodePosed :: Posed -> SExpr
encodePosed (Posed (CtxId c) f) = sTagged TPose [SAtom c, encodeForm f]

decodePosed :: SExpr -> Either CodecError Posed
decodePosed e = case sHead e of
  Just (TPose, [SAtom c, f]) -> Posed (CtxId c) <$> decodeForm f
  _ -> malformed "posed-query"

encodeDocument :: Document -> SExpr
encodeDocument d =
  sTagged
    TDocument
    [ SAtom surfaceVersion
    , sTagged TBridges (map encodeBridgeDecl (docBridges d))
    , sTagged TQueries (map encodePosed (docQueries d))
    ]

-- | The version is read before the layout (Lean @decodeDocument@).
decodeDocument :: SExpr -> Either CodecError Document
decodeDocument e = case sHead e of
  Just (TDocument, SAtom v : rest)
    | v == surfaceVersion -> case rest of
        [bs, qs] -> do
          bridges <- sSection TBridges bs >>= mapM decodeBridgeDecl
          queries <- sSection TQueries qs >>= mapM decodePosed
          pure (Document bridges queries)
        _ -> malformed "document"
    | otherwise -> Left (CodecError CodecUnsupportedVersion v)
  _ -> malformed "document"

-- ---------------------------------------------------------------------------
-- The @pw-run 1@ document (Lean @Run.RunDoc@)
-- ---------------------------------------------------------------------------

-- | A world identifier: its own namespace.
newtype WorldId = WorldId String
  deriving (Eq, Ord, Show)

-- | The declared acceptance of one candidate edge.
data Acceptance = Accepted | Rejected
  deriving (Eq, Show, Enum, Bounded)

acceptanceText :: Acceptance -> String
acceptanceText a = case a of
  Accepted -> "accepted"
  Rejected -> "rejected"

-- | Where a world's check-input envelope comes from; @file@ paths are relative
-- to the run file's directory.
data WorldSource
  = SourceInline SExpr
  | SourceFile String
  deriving (Eq, Show)

data WorldDecl = WorldDecl
  { wdId :: WorldId
  , wdContext :: CtxId
  , wdSource :: WorldSource
  }
  deriving (Eq, Show)

data EdgeDecl = EdgeDecl
  { edBridge :: BridgeId
  , edSource :: WorldId
  , edTarget :: WorldId
  , edAcceptance :: Acceptance
  }
  deriving (Eq, Show)

data CompareDecl = CompareDecl
  { cdBridge :: BridgeId
  , cdWorld :: WorldId
  , cdClaim :: Prop
  }
  deriving (Eq, Show)

data RunDoc = RunDoc
  { rdWorlds :: [WorldDecl]
  , rdEdges :: [EdgeDecl]
  , rdComparisons :: [CompareDecl]
  , rdDocument :: Document
  }
  deriving (Eq, Show)

-- | The run grammar's own keywords (Lean @Run.Tag@).
data RTag
  = RRun | RWorlds | RWorld | RInline | RFile | REdges | REdge | RComparisons | RCompare
  deriving (Eq, Show, Enum, Bounded)

rTagText :: RTag -> String
rTagText t = case t of
  RRun -> "pw-run"
  RWorlds -> "worlds"
  RWorld -> "world"
  RInline -> "inline"
  RFile -> "file"
  REdges -> "edges"
  REdge -> "edge"
  RComparisons -> "comparisons"
  RCompare -> "compare"

{-# NOINLINE rTagTable #-}
rTagTable :: Map.Map String RTag
rTagTable = Map.fromList [(rTagText t, t) | t <- [minBound .. maxBound]]

rTagged :: RTag -> [SExpr] -> SExpr
rTagged t args = SList (SAtom (rTagText t) : args)

rHead :: SExpr -> Maybe (RTag, [SExpr])
rHead e = case e of
  SList (SAtom s : args) -> (\t -> (t, args)) <$> Map.lookup s rTagTable
  _ -> Nothing

rSection :: RTag -> SExpr -> Either CodecError [SExpr]
rSection t e = case rHead e of
  Just (found, xs) | found == t -> Right xs
  _ -> malformed (rTagText t)

runVersion :: String
runVersion = "1"

decodeAcceptance :: SExpr -> Either CodecError Acceptance
decodeAcceptance e = case e of
  SAtom s | Just a <- lookup s [(acceptanceText a, a) | a <- [minBound .. maxBound]] -> Right a
  _ -> malformed "acceptance"

encodeSource :: WorldSource -> SExpr
encodeSource s = case s of
  SourceInline e -> rTagged RInline [e]
  SourceFile p -> rTagged RFile [SAtom p]

decodeSource :: SExpr -> Either CodecError WorldSource
decodeSource e = case rHead e of
  Just (RInline, [x]) -> Right (SourceInline x)
  Just (RFile, [SAtom p]) -> Right (SourceFile p)
  _ -> malformed "world-source"

encodeWorld :: WorldDecl -> SExpr
encodeWorld (WorldDecl (WorldId w) (CtxId c) s) = rTagged RWorld [SAtom w, SAtom c, encodeSource s]

decodeWorld :: SExpr -> Either CodecError WorldDecl
decodeWorld e = case rHead e of
  Just (RWorld, [SAtom w, SAtom c, src]) -> WorldDecl (WorldId w) (CtxId c) <$> decodeSource src
  _ -> malformed "world"

encodeEdge :: EdgeDecl -> SExpr
encodeEdge (EdgeDecl (BridgeId b) (WorldId s) (WorldId t) a) =
  rTagged REdge [SAtom b, SAtom s, SAtom t, SAtom (acceptanceText a)]

decodeEdge :: SExpr -> Either CodecError EdgeDecl
decodeEdge e = case rHead e of
  Just (REdge, [SAtom b, SAtom s, SAtom t, a]) ->
    EdgeDecl (BridgeId b) (WorldId s) (WorldId t) <$> decodeAcceptance a
  _ -> malformed "edge"

encodeCompare :: CompareDecl -> SExpr
encodeCompare (CompareDecl (BridgeId b) (WorldId w) c) = rTagged RCompare [SAtom b, SAtom w, encodeAtom c]

decodeCompare :: SExpr -> Either CodecError CompareDecl
decodeCompare e = case rHead e of
  Just (RCompare, [SAtom b, SAtom w, a]) -> CompareDecl (BridgeId b) (WorldId w) <$> decodeAtom a
  _ -> malformed "comparison"

encodeRun :: RunDoc -> SExpr
encodeRun d =
  rTagged
    RRun
    [ SAtom runVersion
    , rTagged RWorlds (map encodeWorld (rdWorlds d))
    , rTagged REdges (map encodeEdge (rdEdges d))
    , rTagged RComparisons (map encodeCompare (rdComparisons d))
    , encodeDocument (rdDocument d)
    ]

-- | The version first, then each section in order, each fully decoded before
-- the next section header is read (Lean @decodeRun@).
decodeRun :: SExpr -> Either CodecError RunDoc
decodeRun e = case rHead e of
  Just (RRun, SAtom v : rest)
    | v == runVersion -> case rest of
        [ws, es, cs, doc] -> do
          worlds <- rSection RWorlds ws >>= mapM decodeWorld
          edges <- rSection REdges es >>= mapM decodeEdge
          comparisons <- rSection RComparisons cs >>= mapM decodeCompare
          document <- decodeDocument doc
          pure (RunDoc worlds edges comparisons document)
        _ -> malformed "run"
    | otherwise -> Left (CodecError CodecUnsupportedVersion v)
  _ -> malformed "run"

-- | Read exactly one run document with the shared reader; syntax failures keep
-- the reader's line and column.
parseRunBS :: ByteString -> Either CodecError RunDoc
parseRunBS bytes = case W.parseSExprBS bytes of
  Left err -> Left (CodecError CodecSyntax (renderParseError err))
  Right e -> decodeRun e

renderParseError :: W.ParseError -> String
renderParseError (W.ParseError line col msg) =
  "line " ++ show line ++ ", column " ++ show col ++ ": " ++ msg

printRun :: RunDoc -> String
printRun = W.printSExpr . encodeRun
