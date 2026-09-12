-- | The possible-world outer runtime (#322): load declared worlds, check the
-- bridge registry, resolve candidate edges, then answer modal queries and
-- source-claim comparisons. The Haskell side of the @pw-run 1@ contract, whose
-- Lean reference is @lean\/Lara\/PW\/Run.lean@ and whose byte-level agreement
-- with it is gated by @scripts\/check-pw-conformance.py@.
--
-- __The finite model boundary.__ A context contains exactly the worlds the run
-- file declares. A bridge's candidate relation is the declared edge list, and
-- acceptance is each edge's declared flag. A world is a check-input envelope
-- accepted by the unchanged local checker ('checkUnitWith' 'fullConfig'), so
-- every status atom is read from 'statusC' over that world's compiled
-- framework. Lean proves the evaluator agrees with @PW.Sat@ in the frame
-- a run declares (@Model.evaluates_iff@), and that a comparison profile is the
-- model's @⟨b⟩@ reading (@Model.compare_mem_iff_sat@). This module is the
-- conformance implementation of those definitions, not a second source of
-- truth.
--
-- __What stays explicit.__ Every context uses the production canonicalizer,
-- which is how canonicalizer agreement holds. The loader decides T6's
-- @rule-ok@ clause. @leaf-ok@ and @cert-ok@ must be listed but are never
-- proved. A world whose duplicate-report groups all agree is checked as
-- declared, because an empty §4.3 quarantine is the identity (Lean
-- @addWorld_checks_declared@); a world with a conflicting group is refused,
-- because quarantine would make a public status conditional.
--
-- __Sources (#327).__ A world's envelope is inline, in a file, or elaborated
-- from a @.lara@ presentation program through the same steps @lara check@
-- takes on that file alone. The Lean reference has no surface parser, so
-- 'deriveRunFile' produces the equivalent document with every source inline;
-- @lara pw-input@ prints it, and the differential gate compares both runtimes
-- on that.
module Lara.PW.Run
  ( -- * Errors
    WorldError (..)
  , BridgeFault (..)
  , LoadError (..)
  , EdgeError (..)
  , FormError (..)
  , CompareError (..)
  , PWError (..)
  , pwErrorExitCode
    -- * Running
  , WorldInput (..)
  , Outcome (..)
  , runPW
  , runPWFile
  , deriveRunFile
  , inlineSources
    -- * The result protocol
  , ResultTag (..)
  , resultTagText
  , encodeOutcome
  , encodeError
  ) where

import Control.Exception (IOException, try)
import qualified Data.ByteString as B
import Data.List (find, findIndex)
import qualified Data.Text.Encoding as TE
import System.FilePath (takeDirectory, (</>))

import Lara.Admission (AdmissionAudit, renderAdmissionAudit, renderAdmissionRejection)
import Lara.AST
  ( Contrary
  , DupGroup (..)
  , Exception
  , GroupId (..)
  , LeafId
  , RejectClass (..)
  , Rejection (..)
  , Rule
  , Status
  , TheoryDigest
  , Unit (..)
  )
import Lara.Blocked (groupConsistent)
import Lara.Check (CheckedUnit, checkUnitWith, cuNodes, cuProgram, fullConfig)
import Lara.Compile (CheckedProgram)
import Lara.Diagnostics (rejectionOf)
import Lara.Driver (buildCertOk, buildGamma)
import Lara.Elaborate (PreparedSource (..), preparedCheckInput)
import Lara.Grounded (AF, completeClaimFor, statusC)
import Lara.Prop (FunSym (..), Pred (..), Prop)
import Lara.PW.Sorted
import Lara.PW.Surface
import Lara.PW.Wire
import Lara.Replay (inputUnit, runtimeReplayFailure)
import Lara.Runtime (runtimeAF)
import Lara.Sigma (Sigma)
import Lara.Source.Load (loadSource, loadedPrepared, renderSourceLoadError)
import Lara.Strict (SExpr (..))
import qualified Lara.Wire as W

-- ---------------------------------------------------------------------------
-- Errors (Lean @Run.Error@ and the loader's @LoadError@ / @FormError@)
-- ---------------------------------------------------------------------------

-- | Why a declared world is refused (Lean @WorldError@).
data WorldError
  = DuplicateWorld WorldId
  | WorldInputError WorldId String
  | WorldGroups WorldId GroupId
  | WorldRejected WorldId Rejection
  | ContextEnvironment WorldId CtxId
  | DuplicateWorldState WorldId WorldId
  deriving (Eq, Show)

-- | The two reachable 'LoadError' faults of the bridge checker (Lean
-- @BridgeError@; its name and endpoint mismatches cannot arise when the
-- environment is built from the declaration itself).
data BridgeFault
  = MissingClause Clause
  | RuleClauseFails
  deriving (Eq, Show)

-- | Why the bridge registry does not load (Lean @LoadError@).
data LoadError
  = DuplicateBridge BridgeId
  | UnknownSource BridgeId CtxId
  | UnknownTarget BridgeId CtxId
  | InvalidBridge BridgeId BridgeFault
  deriving (Eq, Show)

-- | Why an edge cannot be placed in the declared frame (Lean @EdgeError@).
data EdgeError
  = EdgeUnknownBridge BridgeId
  | EdgeUnknownWorld WorldId
  | EdgeSourceContext BridgeId WorldId
  | EdgeTargetContext BridgeId WorldId
  | DuplicateEdge BridgeId WorldId WorldId
  deriving (Eq, Show)

-- | Why a posed query does not elaborate (Lean @FormError@).
data FormError
  = UnknownContext CtxId
  | UnknownBridge BridgeId
  | BridgeSourceMismatch BridgeId CtxId CtxId
  | NotAQuery CtxId QueryFault
  deriving (Eq, Show)

-- | Why a comparison cannot run (Lean @CompareError@).
data CompareError
  = CompareUnknownBridge BridgeId
  | CompareUnknownWorld WorldId
  | CompareSourceContext BridgeId WorldId
  deriving (Eq, Show)

-- | The stage that refused a run. Incomparability is a result, never here.
data PWError
  = PWWire CodecError
  | PWWorld WorldError
  | PWBridge LoadError
  | PWEdge EdgeError
  | PWQuery FormError
  | PWComparison CompareError
  | PWIO String
  deriving (Eq, Show)

-- | @2@ for a run file that could not be read or decoded, @1@ for a run
-- refused after decoding (Lean @Error.exitCode@).
pwErrorExitCode :: PWError -> Int
pwErrorExitCode e = case e of
  PWWire _ -> 2
  PWIO _ -> 2
  _ -> 1

-- ---------------------------------------------------------------------------
-- Positions
-- ---------------------------------------------------------------------------

-- | A context's position in the loaded list (Lean @Hosted.K@).
newtype CtxIx = CtxIx Int
  deriving (Eq)

-- | A world's position within its context (the @Nat@ of Lean @REdge@).
newtype WorldIx = WorldIx Int
  deriving (Eq)

-- | An entry's position in the checked registry (Lean @Registry.B@).
newtype BridgeIx = BridgeIx Int
  deriving (Eq)

-- ---------------------------------------------------------------------------
-- Worlds
-- ---------------------------------------------------------------------------

-- | The stable part of a check-input envelope: what a context shares (Lean
-- @Env@). The defeat table is only ever compared, never read, hence the
-- underscore selectors.
data Env = Env
  { envSigma :: Sigma
  , envRules :: [Rule]
  , _envContraries :: [Contrary]
  , _envExceptions :: [Exception]
  , envLeaves :: [(LeafId, Prop)]
  , envTheories :: [(TheoryDigest, [Prop])]
  }
  deriving (Eq)

envOf :: Unit -> Env
envOf u =
  Env (unitSigma u) (unitRules u) (unitContraries u) (unitExceptions u) (unitLeaves u) (unitTheories u)

data LoadedWorld = LoadedWorld
  { lwId :: WorldId
  , lwUnit :: CheckedUnit
  , lwAF :: AF
  }

-- | A context and its worlds, in declaration order; no two share a checked
-- program (Lean @LoadedCtx.distinct@).
data LoadedCtx = LoadedCtx
  { lcName :: CtxId
  , lcEnv :: Env
  , lcWorlds :: [LoadedWorld]
  }

-- | A world's source, already read and parsed.
data WorldInput = WorldInput
  { wiId :: WorldId
  , wiContext :: CtxId
  , wiInput :: Either String SExpr
  }

worldProgram :: LoadedWorld -> CheckedProgram
worldProgram = cuProgram . lwUnit

-- | The world-local status of a claim (Lean @Instance.cmpStatus@).
worldStatus :: LoadedWorld -> Prop -> Status
worldStatus w c = statusC (lwAF w) (completeClaimFor (cuNodes (lwUnit w)) c)

-- | Check a world under its context and append it (Lean @extendCtx@).
extendCtx :: LoadedCtx -> WorldId -> Unit -> Either WorldError LoadedCtx
extendCtx c wid unit =
  case checkUnitWith fullConfig (buildGamma (envLeaves env)) (buildCertOk (envTheories env)) unit of
    Left err -> Left (WorldRejected wid (rejectionOf err))
    Right cu -> case find (\w -> worldProgram w == cuProgram cu) (lcWorlds c) of
      Just earlier -> Left (DuplicateWorldState wid (lwId earlier))
      Nothing ->
        Right c {lcWorlds = lcWorlds c ++ [LoadedWorld wid cu (runtimeAF (cuProgram cu))]}
  where
    env = lcEnv c

-- | Place a world in its named context, creating the context at the end when
-- it is new; the environment check precedes checking (Lean @placeWorld@).
placeWorld :: WorldId -> CtxId -> Unit -> [LoadedCtx] -> Either WorldError [LoadedCtx]
placeWorld wid cname unit ctxs = case ctxs of
  [] -> (: []) <$> extendCtx (LoadedCtx cname (envOf unit) []) wid unit
  c : cs
    | lcName c == cname ->
        if lcEnv c == envOf unit
          then (: cs) <$> extendCtx c wid unit
          else Left (ContextEnvironment wid cname)
    | otherwise -> (c :) <$> placeWorld wid cname unit cs

-- | Load one world: decode, refuse a conflicting duplicate-report group, replay
-- preflight, then check (Lean @addWorld@). The group check names the first
-- group, in declaration order, whose members are not pairwise @≡@; whether
-- the policy would quarantine it or escalate to R9 makes no difference here,
-- since either way the world is not an unconditionally checked unit.
addWorld :: [LoadedCtx] -> [WorldId] -> WorldInput -> Either WorldError [LoadedCtx]
addWorld ctxs seen wi
  | wiId wi `elem` seen = Left (DuplicateWorld (wiId wi))
  | otherwise = do
      e <- either (Left . WorldInputError (wiId wi)) Right (wiInput wi)
      input <- case W.decodeCheckInput e of
        Left (W.WireError ctx msg) -> Left (WorldInputError (wiId wi) (ctx ++ ": " ++ msg))
        Right input -> Right input
      let unit = inputUnit input
      case find (not . groupConsistent unit) (unitGroups unit) of
        Just (DupGroup g _) -> Left (WorldGroups (wiId wi) g)
        Nothing -> case runtimeReplayFailure input of
          Just _ -> Left (WorldRejected (wiId wi) (RejectClass R13))
          Nothing -> placeWorld (wiId wi) (wiContext wi) unit ctxs

loadWorlds :: [WorldInput] -> Either WorldError [LoadedCtx]
loadWorlds = go [] []
  where
    go ctxs _ [] = Right ctxs
    go ctxs seen (wi : rest) = do
      ctxs' <- addWorld ctxs seen wi
      go ctxs' (seen ++ [wiId wi]) rest

ctxAt :: [LoadedCtx] -> CtxIx -> LoadedCtx
ctxAt ctxs (CtxIx k) = ctxs !! k

worldsAt :: [LoadedCtx] -> CtxIx -> [LoadedWorld]
worldsAt ctxs = lcWorlds . ctxAt ctxs

worldAt :: [LoadedWorld] -> WorldIx -> LoadedWorld
worldAt ws (WorldIx i) = ws !! i

-- ---------------------------------------------------------------------------
-- The bridge registry (Lean @Declared.load@)
-- ---------------------------------------------------------------------------

-- | A checked declaration at its resolved endpoints (Lean @Resolved@).
data Resolved = Resolved
  { rDecl :: BridgeDecl
  , rSource :: CtxIx
  , rTarget :: CtxIx
  , rSym :: SymMap
  }

ctxIndex :: [LoadedCtx] -> CtxId -> Maybe CtxIx
ctxIndex ctxs n = CtxIx <$> findIndex ((== n) . lcName) ctxs

-- | Resolve both endpoints, then check the clauses and the rule clause.
resolveBridge :: [LoadedCtx] -> BridgeDecl -> Either LoadError Resolved
resolveBridge ctxs d = case (ctxIndex ctxs (bdSource d), ctxIndex ctxs (bdTarget d)) of
  (Nothing, _) -> Left (UnknownSource (bdId d) (bdSource d))
  (_, Nothing) -> Left (UnknownTarget (bdId d) (bdTarget d))
  (Just s, Just t) -> case find (`notElem` bdClauses d) clauseAll of
    Just c -> Left (InvalidBridge (bdId d) (MissingClause c))
    Nothing
      | ruleOk sym (rulesAt s) (rulesAt t) -> Right (Resolved d s t sym)
      | otherwise -> Left (InvalidBridge (bdId d) RuleClauseFails)
  where
    sym = symMapOf (bdSymbols d)
    rulesAt = envRules . lcEnv . ctxAt ctxs

loadBridges :: [LoadedCtx] -> [BridgeDecl] -> Either LoadError [Resolved]
loadBridges ctxs = go []
  where
    go acc [] = Right acc
    go acc (d : ds)
      | any ((== bdId d) . bdId . rDecl) acc = Left (DuplicateBridge (bdId d))
      | otherwise = do
          r <- resolveBridge ctxs d
          go (acc ++ [r]) ds

-- ---------------------------------------------------------------------------
-- Edges
-- ---------------------------------------------------------------------------

-- | A resolved edge: world positions within their contexts (Lean @REdge@).
data REdge = REdge
  { reBridge :: BridgeId
  , reSource :: WorldIx
  , reTarget :: WorldIx
  , reAccepted :: Bool
  }

data Model = Model
  { mCtxs :: [LoadedCtx]
  , mBridges :: [Resolved]
  , mEdges :: [REdge]
  }

lookupBridge :: [Resolved] -> BridgeId -> Maybe (BridgeIx, Resolved)
lookupBridge rs n = find ((== n) . bdId . rDecl . snd) (zip (map BridgeIx [0 ..]) rs)

bridgeAt :: Model -> BridgeIx -> Resolved
bridgeAt m (BridgeIx b) = mBridges m !! b

worldExists :: [LoadedCtx] -> WorldId -> Bool
worldExists ctxs w = any (any ((== w) . lwId) . lcWorlds) ctxs

positionIn :: [LoadedWorld] -> WorldId -> Maybe WorldIx
positionIn ws w = WorldIx <$> findIndex ((== w) . lwId) ws

-- | The bridge, both worlds, both endpoint contexts, then uniqueness of the
-- (bridge, source, target) triple (Lean @resolveEdge@).
resolveEdge :: [LoadedCtx] -> [Resolved] -> [EdgeDecl] -> EdgeDecl -> Either EdgeError REdge
resolveEdge ctxs rs seen d = case lookupBridge rs (edBridge d) of
  Nothing -> Left (EdgeUnknownBridge (edBridge d))
  Just (_, r)
    | not (worldExists ctxs (edSource d)) -> Left (EdgeUnknownWorld (edSource d))
    | not (worldExists ctxs (edTarget d)) -> Left (EdgeUnknownWorld (edTarget d))
    | otherwise -> case ( positionIn (worldsAt ctxs (rSource r)) (edSource d)
                        , positionIn (worldsAt ctxs (rTarget r)) (edTarget d)
                        ) of
        (Nothing, _) -> Left (EdgeSourceContext (edBridge d) (edSource d))
        (_, Nothing) -> Left (EdgeTargetContext (edBridge d) (edTarget d))
        (Just i, Just j)
          | any sameTriple seen -> Left (DuplicateEdge (edBridge d) (edSource d) (edTarget d))
          | otherwise -> Right (REdge (edBridge d) i j (edAcceptance d == Accepted))
  where
    sameTriple x = edBridge x == edBridge d && edSource x == edSource d && edTarget x == edTarget d

resolveEdges :: [LoadedCtx] -> [Resolved] -> [EdgeDecl] -> Either EdgeError [REdge]
resolveEdges ctxs rs = go []
  where
    go _ [] = Right []
    go seen (d : ds) = do
      e <- resolveEdge ctxs rs seen d
      (e :) <$> go (seen ++ [d]) ds

-- ---------------------------------------------------------------------------
-- Queries (Lean @elabForm@ / @elabPosed@ / @evalFinite@)
-- ---------------------------------------------------------------------------

-- | An elaborated query: posed claims, and modalities resolved to registry
-- positions. The context position is carried by elaboration, as Lean's type
-- does.
data Form
  = FStatus Status Prop
  | FTop
  | FNeg Form
  | FConj Form Form
  | FBox BridgeIx Form
  | FDia BridgeIx Form

elabForm :: Model -> CtxIx -> SForm -> Either FormError Form
elabForm m k f = case f of
  SStatus s c -> case queryFault (envSigma (lcEnv (ctxAt (mCtxs m) k))) c of
    Just fault -> Left (NotAQuery (ctxName k) fault)
    Nothing -> Right (FStatus s c)
  STop -> Right FTop
  SNeg g -> FNeg <$> elabForm m k g
  SConj g h -> FConj <$> elabForm m k g <*> elabForm m k h
  SBox n g -> modal FBox n g
  SDia n g -> modal FDia n g
  where
    ctxName = lcName . ctxAt (mCtxs m)
    modal con n g = case lookupBridge (mBridges m) n of
      Nothing -> Left (UnknownBridge n)
      Just (b, r)
        | ctxName (rSource r) == ctxName k -> con b <$> elabForm m (rTarget r) g
        | otherwise -> Left (BridgeSourceMismatch n (ctxName k) (ctxName (rSource r)))

-- | Accepted successors of world @i@ along registry entry @b@.
successors :: Model -> BridgeIx -> WorldIx -> [WorldIx]
successors m b i =
  [ reTarget e
  | e <- mEdges m
  , reBridge e == bdId (rDecl (bridgeAt m b))
  , reSource e == i
  , reAccepted e
  ]

evalForm :: Model -> CtxIx -> Form -> WorldIx -> Bool
evalForm m k f i = case f of
  FStatus s c -> worldStatus (worldAt (worldsAt (mCtxs m) k) i) c == s
  FTop -> True
  FNeg g -> not (evalForm m k g i)
  FConj g h -> evalForm m k g i && evalForm m k h i
  FBox b g -> all (evalForm m (target b) g) (successors m b i)
  FDia b g -> any (evalForm m (target b) g) (successors m b i)
  where
    target = rTarget . bridgeAt m

-- | Elaborate, then answer at every world of the context, in order.
runQuery :: Model -> Posed -> Either FormError [(WorldId, Bool)]
runQuery m p = case ctxIndex (mCtxs m) (posedContext p) of
  Nothing -> Left (UnknownContext (posedContext p))
  Just k -> do
    f <- elabForm m k (posedForm p)
    pure [(lwId w, evalForm m k f i) | (i, w) <- zip (map WorldIx [0 ..]) (worldsAt (mCtxs m) k)]

-- ---------------------------------------------------------------------------
-- Comparisons (Lean @Model.compare@)
-- ---------------------------------------------------------------------------

-- | Resolve the bridge and the source world, then compare over the declared
-- candidates in edge order, accepted and rejected alike.
runCompare :: Model -> CompareDecl -> Either CompareError SortedResult
runCompare m d = case lookupBridge (mBridges m) (cdBridge d) of
  Nothing -> Left (CompareUnknownBridge (cdBridge d))
  Just (_, r)
    | not (worldExists ctxs (cdWorld d)) -> Left (CompareUnknownWorld (cdWorld d))
    | otherwise -> case positionIn (worldsAt ctxs (rSource r)) (cdWorld d) of
        Nothing -> Left (CompareSourceContext (cdBridge d) (cdWorld d))
        Just i ->
          let candidates =
                [ (worldAt (worldsAt ctxs (rTarget r)) (reTarget e), reAccepted e)
                | e <- mEdges m
                , reBridge e == bdId (rDecl r)
                , reSource e == i
                ]
           in Right
                ( crossComparePosed
                    (sigmaAt (rSource r))
                    (sigmaAt (rTarget r))
                    (rSym r)
                    (cdClaim d)
                    candidates
                    snd
                    (worldStatus . fst)
                )
  where
    ctxs = mCtxs m
    sigmaAt = envSigma . lcEnv . ctxAt ctxs

-- ---------------------------------------------------------------------------
-- Running
-- ---------------------------------------------------------------------------

-- | A completed run: answers per query and world, and one result per
-- comparison, both in input order.
data Outcome = Outcome
  { outcomeQueries :: [[(WorldId, Bool)]]
  , outcomeComparisons :: [(CompareDecl, SortedResult)]
  }

-- | Stage order: worlds, bridges, edges, queries, comparisons (Lean @run@).
runPW :: RunDoc -> [WorldInput] -> Either PWError Outcome
runPW doc inputs = do
  ctxs <- mapLeft PWWorld (loadWorlds inputs)
  bridges <- mapLeft PWBridge (loadBridges ctxs (docBridges (rdDocument doc)))
  edges <- mapLeft PWEdge (resolveEdges ctxs bridges (rdEdges doc))
  let m = Model ctxs bridges edges
  answers <- mapM (mapLeft PWQuery . runQuery m) (docQueries (rdDocument doc))
  results <- mapM (\d -> mapLeft PWComparison ((,) d <$> runCompare m d)) (rdComparisons doc)
  pure (Outcome answers results)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

-- | Read bytes as UTF-8 text first, as the Lean reference's @IO.FS.readFile@
-- does, so an undecodable file is a read failure on both sides.
readUtf8 :: FilePath -> IO (Either String B.ByteString)
readUtf8 path = do
  bytes <- try (B.readFile path)
  pure $ case bytes of
    Left err -> Left (show (err :: IOException))
    Right bs -> case TE.decodeUtf8' bs of
      Left err -> Left (show err)
      Right _ -> Right bs

-- | Read one world source to an envelope tree, or say why it could not be.
--
-- A @lara@ source goes through the steps @lara check@ takes on that file alone
-- ("Lara.Source.Load", 'Lara.Elaborate.prepareSource'), and stops where an
-- envelope stops existing: a parse or policy failure, a source the elaborator
-- refuses, a policy admission __stop__, or a policy __quarantine__ (whose
-- pruned unit the frozen envelope cannot express, exactly as
-- 'Lara.Elaborate.sourceResultCheckInput' says). Every one of those is a
-- @world-input@ fault, so the fault set of the loader does not grow. What
-- comes back is the envelope's own encoding, so the loader decodes a @lara@
-- world through the same 'W.decodeCheckInput' as an inline or file one, and
-- so the document 'deriveRunFile' prints means what this run meant.
readSource :: FilePath -> WorldSource -> IO (Either String SExpr)
readSource dir source = case source of
  SourceInline e -> pure (Right e)
  SourceFile p -> do
    bytes <- readUtf8 (dir </> p)
    pure $ case bytes of
      Left err -> Left err
      Right bs -> case W.parseSExprBS bs of
        Left (W.ParseError line col msg) ->
          Left ("line " ++ show line ++ ", column " ++ show col ++ ": " ++ msg)
        Right e -> Right e
  SourceLara p -> do
    loaded <- loadSource (dir </> p)
    pure $ case loaded of
      Left err -> Left (renderSourceLoadError err)
      Right src -> case loadedPrepared src of
        SourceRejected rejection -> Left (renderAdmissionRejection rejection)
        SourceAccepted prepared -> case preparedCheckInput prepared of
          Left audit -> Left (quarantineDetail audit)
          Right input -> Right (W.encodeCheckInput input)

-- | Why a policy __quarantine__ leaves no envelope, then the audit that says
-- what was pruned.
--
-- The audit line alone is not a reason. Beside a @lara check@ accept it is an
-- informational note, and 'Lara.Elaborate.preparedCheckInput' renders nothing
-- — it returns the audit. This site and the map loader's
-- @MRUnsupportedAdmission@ ("Lara.Map.Load") are the places an audit becomes a
-- refusal, and each frames it for its own door, so the sentence that makes it
-- one belongs at the site rather than in the renderer the solo door shares.
quarantineDetail :: AdmissionAudit -> String
quarantineDetail audit =
  "policy quarantine: a check-input envelope cannot express a pruned unit; "
    ++ renderAdmissionAudit audit

-- | Read a run file and every world source relative to its directory.
--
-- Paths go through GHC's file-system encoding, and @.lara@ text through the
-- locale encoding. The Lean reference always uses UTF-8, so a caller that must
-- agree with it on non-ASCII paths and programs under any locale sets both
-- encodings to UTF-8 first — the locale one /strictly/, so that program text
-- which is not UTF-8 is the read failure @lara check@ reports and not a
-- surrogate-escaped decode. The @lara@ CLI does this once for every door
-- (@textBoundary@ in @app\/Main.hs@), which is what makes a @(lara PATH)@
-- world and @lara check@ on the same file agree (\#334). A @(file PATH)@
-- world needs no such setting: 'readUtf8' reads its bytes and decodes them
-- here.
readRunFile :: FilePath -> IO (Either PWError (RunDoc, [WorldInput]))
readRunFile file = do
  bytes <- readUtf8 file
  case bytes of
    Left err -> pure (Left (PWIO err))
    Right bs -> case parseRunBS bs of
      Left err -> pure (Left (PWWire err))
      Right doc -> do
        inputs <-
          mapM
            (\d -> WorldInput (wdId d) (wdContext d) <$> readSource (takeDirectory file) (wdSource d))
            (rdWorlds doc)
        pure (Right (doc, inputs))

-- | Read a run file and its worlds, then run.
runPWFile :: FilePath -> IO (Either PWError Outcome)
runPWFile file = fmap (>>= uncurry runPW) (readRunFile file)

-- | The self-contained run document equivalent to a run file: every world
-- source replaced by the envelope tree it yielded, in place (#327). The
-- derivation door of @lara pw-input@, in the style of @lara map-input@.
--
-- A world whose source yields no envelope is the first fault, in declaration
-- order, as a @world-input@ envelope; 'runPWFile' on the same file reports
-- that world too, with two exceptions. An earlier world may already have
-- refused the run — and 'addWorld' tests @wiId wi \`elem\` seen@ /before/ it
-- looks at 'wiInput', so a world whose ID repeats an earlier one and whose
-- source is unreadable is @duplicate-world@ from 'runPWFile' and
-- @world-input@ from here. Both are the same rule (the run's first refusal
-- wins, and the two doors stop at different stages), and a run file with a
-- repeated world ID is already refused, so no derived document depends on it.
-- Nothing is checked: a document this prints is one both runtimes then read
-- alike.
deriveRunFile :: FilePath -> IO (Either PWError RunDoc)
deriveRunFile file = fmap (>>= inlineSources) (readRunFile file)

-- | Replace each world's source with the tree it was read to.
inlineSources :: (RunDoc, [WorldInput]) -> Either PWError RunDoc
inlineSources (doc, inputs) = do
  worlds <- mapM inlineWorld (zip (rdWorlds doc) inputs)
  pure doc {rdWorlds = worlds}
  where
    inlineWorld (d, wi) = case wiInput wi of
      Left detail -> Left (PWWorld (WorldInputError (wiId wi) detail))
      Right e -> Right d {wdSource = SourceInline e}

-- ---------------------------------------------------------------------------
-- The @pw-result 1@ / @pw-error 1@ protocol (Lean @encodeOutcome@ /
-- @encodeError@)
-- ---------------------------------------------------------------------------

-- | Every keyword the result protocol spells (Lean @ResultTag@): envelope
-- heads, stage names, result nodes, reasons and fault constructors. One
-- constructor per spelling, so the @query@ stage and the @(query …)@ answer
-- node share 'OQuery', and likewise 'OComparison'.
--
-- A separate closed sum from the run grammar's 'RTag' and the surface's
-- 'STag', with its own single table, as 'Lara.Map.Wire.MapTag' is from
-- 'Lara.Wire.Tag'. The output reuses a few input spellings (@queries@,
-- @comparisons@, @world@, @pred@, @con@) on purpose, but it must not be able
-- to perturb the input codec. Lean's table also spells the @usage@ stage and
-- the bridge checker's three name and endpoint mismatches, none of which can
-- arise here (see 'BridgeFault').
data ResultTag
  = OResult | OError
  | OWire | OWorld | OBridge | OEdge | OQuery | OComparison | OIo
  | OQueries | OAt | OTrue | OFalse | OComparisons
  | OComparable | OIncomparable | ONotPosable
  | OTranslationUndefined | ONoCandidateWorld | OAllCandidateBridgesRejected
  | OSourceQuery | OTargetQuery | OBridgeVocabulary | OPred | OCon
  | OUndeclaredPredicate | OIllSortedArguments
  | ODuplicateWorld | OWorldInput | OWorldGroups | OWorldRejected
  | OContextEnvironment | ODuplicateWorldState
  | ODuplicateBridge | OUnknownSource | OUnknownTarget | OInvalidBridge
  | OMissingClause | ORuleClauseFails
  | OUnknownBridge | OUnknownWorld | OSourceContext | OTargetContext | ODuplicateEdge
  | OUnknownContext | OBridgeSourceMismatch | ONotAQuery
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The one spelling table of the result protocol.
resultTagText :: ResultTag -> String
resultTagText t = case t of
  OResult -> "pw-result"
  OError -> "pw-error"
  OWire -> "wire"
  OWorld -> "world"
  OBridge -> "bridge"
  OEdge -> "edge"
  OQuery -> "query"
  OComparison -> "comparison"
  OIo -> "io"
  OQueries -> "queries"
  OAt -> "at"
  OTrue -> "true"
  OFalse -> "false"
  OComparisons -> "comparisons"
  OComparable -> "comparable"
  OIncomparable -> "incomparable"
  ONotPosable -> "not-posable"
  OTranslationUndefined -> "translation-undefined"
  ONoCandidateWorld -> "no-candidate-world"
  OAllCandidateBridgesRejected -> "all-candidate-bridges-rejected"
  OSourceQuery -> "source-query"
  OTargetQuery -> "target-query"
  OBridgeVocabulary -> "bridge-vocabulary"
  OPred -> "pred"
  OCon -> "con"
  OUndeclaredPredicate -> "undeclared-predicate"
  OIllSortedArguments -> "ill-sorted-arguments"
  ODuplicateWorld -> "duplicate-world"
  OWorldInput -> "world-input"
  OWorldGroups -> "world-groups"
  OWorldRejected -> "world-rejected"
  OContextEnvironment -> "context-environment"
  ODuplicateWorldState -> "duplicate-world-state"
  ODuplicateBridge -> "duplicate-bridge"
  OUnknownSource -> "unknown-source"
  OUnknownTarget -> "unknown-target"
  OInvalidBridge -> "invalid-bridge"
  OMissingClause -> "missing-clause"
  ORuleClauseFails -> "rule-clause-fails"
  OUnknownBridge -> "unknown-bridge"
  OUnknownWorld -> "unknown-world"
  OSourceContext -> "source-context"
  OTargetContext -> "target-context"
  ODuplicateEdge -> "duplicate-edge"
  OUnknownContext -> "unknown-context"
  OBridgeSourceMismatch -> "bridge-source-mismatch"
  ONotAQuery -> "not-a-query"

node :: ResultTag -> [SExpr] -> SExpr
node tag args = SList (SAtom (resultTagText tag) : args)

keyword :: ResultTag -> SExpr
keyword = SAtom . resultTagText

name :: String -> SExpr
name = SAtom

bridgeName :: BridgeId -> SExpr
bridgeName (BridgeId b) = name b

ctxNameS :: CtxId -> SExpr
ctxNameS (CtxId c) = name c

worldName :: WorldId -> SExpr
worldName (WorldId w) = name w

groupName :: GroupId -> SExpr
groupName (GroupId g) = name g

encodeQueryFault :: QueryFault -> SExpr
encodeQueryFault f = case f of
  UndeclaredPredicate (Pred p) -> node OUndeclaredPredicate [name p]
  IllSortedArguments (Pred p) -> node OIllSortedArguments [name p]

encodePosingFault :: PosingFault -> SExpr
encodePosingFault f = case f of
  SourceQuery q -> node OSourceQuery [encodeQueryFault q]
  TargetQuery q -> node OTargetQuery [encodeQueryFault q]
  BridgeVocabulary v -> node OBridgeVocabulary [case v of
    OovPred (Pred p) -> node OPred [name p]
    OovCon (FunSym c) -> node OCon [name c]]

encodeReason :: IncomparabilityReason -> SExpr
encodeReason r = keyword $ case r of
  TranslationUndefined -> OTranslationUndefined
  NoCandidateWorld -> ONoCandidateWorld
  AllCandidateBridgesRejected -> OAllCandidateBridgesRejected

encodeComparison :: SortedResult -> SExpr
encodeComparison r = case r of
  NotPosable f -> node ONotPosable [encodePosingFault f]
  Compared (Incomparable reason) -> node OIncomparable [encodeReason reason]
  Compared (Comparable s ss) -> node OComparable (map encodeStatus (s : ss))

encodeOutcome :: Outcome -> SExpr
encodeOutcome o =
  node
    OResult
    [ SAtom runVersion
    , node OQueries [node OQuery [node OAt [worldName w, keyword (if b then OTrue else OFalse)] | (w, b) <- ws] | ws <- outcomeQueries o]
    , node
        OComparisons
        [ node OComparison [bridgeName (cdBridge d), worldName (cdWorld d), encodeAtom (cdClaim d), encodeComparison r]
        | (d, r) <- outcomeComparisons o
        ]
    ]

-- | The wire spelling of a checker rejection, from "Lara.Wire"'s one table.
rejectionText :: Rejection -> String
rejectionText r = W.tagToString $ case r of
  DuplicateRule -> W.TDupRule
  DuplicateArgument -> W.TDupArgument
  IncompleteArgument -> W.TIncompleteArgument
  MissingConflict -> W.TMissingConflict
  RejectClass c -> W.rejectClassTag c

encodeWorldError :: WorldError -> SExpr
encodeWorldError e = case e of
  DuplicateWorld w -> node ODuplicateWorld [worldName w]
  WorldInputError w detail -> node OWorldInput [worldName w, SAtom detail]
  WorldGroups w g -> node OWorldGroups [worldName w, groupName g]
  WorldRejected w r -> node OWorldRejected [worldName w, SAtom (rejectionText r)]
  ContextEnvironment w c -> node OContextEnvironment [worldName w, ctxNameS c]
  DuplicateWorldState w earlier -> node ODuplicateWorldState [worldName w, worldName earlier]

encodeLoadError :: LoadError -> SExpr
encodeLoadError e = case e of
  DuplicateBridge b -> node ODuplicateBridge [bridgeName b]
  UnknownSource b c -> node OUnknownSource [bridgeName b, ctxNameS c]
  UnknownTarget b c -> node OUnknownTarget [bridgeName b, ctxNameS c]
  InvalidBridge b f -> node OInvalidBridge [bridgeName b, case f of
    MissingClause c -> node OMissingClause [SAtom (clauseText c)]
    RuleClauseFails -> node ORuleClauseFails []]

encodeEdgeError :: EdgeError -> SExpr
encodeEdgeError e = case e of
  EdgeUnknownBridge b -> node OUnknownBridge [bridgeName b]
  EdgeUnknownWorld w -> node OUnknownWorld [worldName w]
  EdgeSourceContext b w -> node OSourceContext [bridgeName b, worldName w]
  EdgeTargetContext b w -> node OTargetContext [bridgeName b, worldName w]
  DuplicateEdge b s t -> node ODuplicateEdge [bridgeName b, worldName s, worldName t]

encodeFormError :: FormError -> SExpr
encodeFormError e = case e of
  UnknownContext c -> node OUnknownContext [ctxNameS c]
  UnknownBridge b -> node OUnknownBridge [bridgeName b]
  BridgeSourceMismatch b expected found ->
    node OBridgeSourceMismatch [bridgeName b, ctxNameS expected, ctxNameS found]
  NotAQuery c f -> node ONotAQuery [ctxNameS c, encodeQueryFault f]

encodeCompareError :: CompareError -> SExpr
encodeCompareError e = case e of
  CompareUnknownBridge b -> node OUnknownBridge [bridgeName b]
  CompareUnknownWorld w -> node OUnknownWorld [worldName w]
  CompareSourceContext b w -> node OSourceContext [bridgeName b, worldName w]

-- | Stable stage and fault constructors; only @syntax@, @world-input@ and @io@
-- carry reader- or runtime-specific detail text.
encodeError :: PWError -> SExpr
encodeError e = case e of
  PWWire c -> envelope OWire [SAtom (codecErrorTagText (codecErrorTag c)), SAtom (codecErrorDetail c)]
  PWWorld w -> envelope OWorld [encodeWorldError w]
  PWBridge l -> envelope OBridge [encodeLoadError l]
  PWEdge x -> envelope OEdge [encodeEdgeError x]
  PWQuery f -> envelope OQuery [encodeFormError f]
  PWComparison c -> envelope OComparison [encodeCompareError c]
  PWIO detail -> envelope OIo [SAtom detail]
  where
    envelope stage args = node OError (SAtom runVersion : keyword stage : args)
