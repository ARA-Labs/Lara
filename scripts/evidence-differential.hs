module Main (main) where

import Control.Monad (unless)
import Control.Exception (IOException,try)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.ByteString.Char8 as B
import Data.List (find, nub)
import System.Environment (getArgs)
import System.Exit (exitWith, ExitCode (..))
import System.IO (hPutStrLn, stderr)
import Lara.AST
import qualified Lara.Admission as Admission
import Lara.AdmissionFixture
import Lara.Blocked (pruneWithPolicySeed, pruneChecked)
import Lara.Check (checkUnit,cuHoles)
import Lara.Driver (buildCertOk,buildGamma,groupConflictReject)
import Lara.Evidence.Admission
import Lara.Evidence.CSV
import Lara.Evidence.JSON
import Lara.Evidence.Manifest
import Lara.Evidence.Registry
import Lara.Evidence.Runner
import Lara.Evidence.Syntax
import Lara.Evidence.Types
import Lara.Prop (nf)
import Lara.Strict (SExpr (..))
import Lara.Strict.Cell (parseCanonicalNat)
import Lara.SupportTerm (chIndex,chConclusion,chObligations)
import Lara.Wire (parseSExpr,printSExpr,decodeUnit,decodeAtomSExpr,encodeAtom)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      captured <- try (B.readFile path) :: IO (Either IOException B.ByteString)
      bytes <- either (die . show) pure captured
      text <- either (die . show) (pure . T.unpack) (T.decodeUtf8' bytes)
      case parseSExpr text of
        Left err -> die (show err)
        Right expression -> case execute expression of
          Left reason -> die reason
          Right result -> putStrLn (printSExpr result)
    _ -> die "usage: evidence-differential FIXTURE.sexp"
  where
    die message = hPutStrLn stderr message >> exitWith (ExitFailure 2)

execute :: SExpr -> Either String SExpr
execute (SList [SAtom "evidence-model",SAtom "1",allowExpr,manifestExpr,snapshotExpr,leavesExpr,SList [SAtom "ordinary",tableExpr,unitExpr]]) = do
  allowlist <- case allowExpr of
    SList (SAtom "allowlist":entries) -> decodeCheckers (SList (SAtom "checkers":entries))
    _ -> Left "malformed model allowlist"
  metadata <- case manifestExpr of SList (SAtom "manifest":entries) -> mapM object entries; _ -> Left "malformed model manifest"
  unique "manifest IDs" (map objectId metadata)
  unique "manifest paths" (map objectPath metadata)
  snapshot <- case snapshotExpr of SList (SAtom "snapshot":entries) -> mapM (capture metadata) entries; _ -> Left "malformed model snapshot"
  unique "snapshot IDs" (map fst snapshot)
  leaves <- case leavesExpr of SList (SAtom "leaves":entries) -> mapM leaf entries; _ -> Left "malformed model leaves"
  unique "leaf IDs" (map leafId leaves)
  table <- decodeTable tableExpr
  unit <- either (Left . show) Right (decodeUnit unitExpr)
  let ordinary = admissionTypedOutcome table leaves unit
  pure $ result $ case ordinary of
    SList (SAtom "invalid":_) -> ordinary
    SList (SAtom "rejected":_) -> SList [SAtom "rejected",SAtom "policy",ordinary]
    _ -> case bindEvidenceMetadata metadata allowlist leaves of
      Left err -> rejection [] err
      Right requests -> case replayTypedEvidence metadata snapshot requests of
        Left err -> rejection requests err
        Right observations -> success ordinary table unit leaves observations
  where
    result body = SList [SAtom "evidence-result",SAtom "1",body]
execute _ = Left "malformed evidence-model envelope"

unique :: Ord a => String -> [a] -> Either String ()
unique label xs = unless (length xs == length (nub xs)) (Left ("duplicate " ++ label))
atom :: SExpr -> Either String String
atom (SAtom value) = Right value
atom _ = Left "expected atom"
object :: SExpr -> Either String ObjectMeta
object (SList [SAtom "object",SAtom ident,SAtom path,SAtom len,SAtom hash]) = do
  n <- maybe (Left "invalid object length") Right (parseCanonicalNat len)
  digest <- decodeSha256 hash
  makeObjectMeta (ObjectId ident) path n digest
object _ = Left "malformed object metadata"
capture :: [ObjectMeta] -> SExpr -> Either String (ObjectId,Either String (ObjectMeta,TypedObject))
capture _ (SList [SAtom "failed",SAtom ident,SAtom reason]) = Right (ObjectId ident,Left reason)
capture metadata (SList [SAtom "captured",SAtom ident,payload]) = do
  meta <- maybe (Left "captured object absent from manifest") Right (find ((==ObjectId ident) . objectId) metadata)
  value <- typed payload
  pure (ObjectId ident,Right (meta,value))
capture _ _ = Left "malformed captured object"
typed :: SExpr -> Either String TypedObject
typed (SList [SAtom "csv",SList (SAtom "header":columns),SList (SAtom "rows":rows)]) =
  CsvPayload <$> (CsvTable <$> mapM (fmap ColumnName . atom) columns <*> mapM row rows)
  where row (SList (SAtom "row":cells)) = mapM atom cells; row _ = Left "malformed typed CSV row"
typed (SList [SAtom "json",value]) = JsonPayload <$> json value
typed _ = Left "malformed typed object"
json :: SExpr -> Either String JsonValue
json (SList (SAtom "object":entries)) = JsonObject <$> mapM entry entries
  where entry (SList [SAtom "entry",SAtom key,value]) = (,) (JsonToken key) <$> json value; entry _ = Left "malformed JSON entry"
json (SList (SAtom "array":values)) = JsonArray <$> mapM json values
json (SList [SAtom "string",SAtom value]) = Right (JsonString value)
json (SList [SAtom "number",SAtom value]) = Right (JsonNumber value)
json (SAtom "true") = Right (JsonBool True)
json (SAtom "false") = Right (JsonBool False)
json (SAtom "null") = Right JsonNull
json _ = Left "malformed typed JSON"
leaf :: SExpr -> Either String Leaf
leaf (SList [SAtom "leaf",SAtom ident,kindExpr,provenanceExpr,SList (SAtom "refs":refs),requestExpr,propExpr]) = do
  kind <- decodeKind kindExpr
  provenance <- decodeProvenance provenanceExpr
  references <- mapM (fmap SourceRef . atom) refs
  request <- case requestExpr of SAtom "none" -> Right Nothing; expr -> Just <$> decodeRequest expr
  prop <- either (Left . show) Right (decodeAtomSExpr propExpr)
  pure (Leaf (LeafId ident) prop kind provenance references request)
leaf _ = Left "malformed typed leaf"

rejection :: [BoundRequest] -> EvidenceRejection -> SExpr
rejection requests err = SList [SAtom "rejected",SAtom stage,leafAtom (evidenceLeaf err),objectExpr,SAtom reason]
  where
    stage = case evidenceStage err of BindingStage -> "binding"; CaptureStage -> "capture"; ExtractionStage -> "extraction"
    -- The canonical rejection names an artifact only where the failure is
    -- located at one. A capture failure names the object it could not capture;
    -- an extraction failure is located at its leaf, which is already named, and
    -- the finite model's `replayLeaf` carries no object there, so the encoding
    -- must not invent one: the leaf locates the rejection.
    objectExpr = case evidenceStage err of
      ExtractionStage -> SAtom "none"
      _ -> maybe (SAtom "none") (\(ObjectId ident) -> SAtom ident) (evidenceObject err)
    reason = case evidenceStage err of
      BindingStage -> "binding"
      CaptureStage -> evidenceReason err
      ExtractionStage
        | evidenceReason err == "extracted proposition mismatch" -> "mismatch"
        | evidenceReason err == "wrong checker object type" -> "payload-type"
        | otherwise -> case find ((== evidenceLeaf err) . leafId . boundLeaf) requests of
            Just bound | requestChecker (boundRequest bound) == CsvRow -> "csv-selection"
            _ -> "json-selection"
leafAtom :: LeafId -> SExpr
leafAtom (LeafId name) = SAtom name
argAtom :: ArgId -> SExpr
argAtom (ArgId name) = SAtom name
success :: SExpr -> [((LeafKind,Provenance),Admission)] -> Unit -> [Leaf] -> [EvidenceObservation] -> SExpr
success ordinary table unit leaves observations = SList
  [ SAtom "accepted"
  , SList (SAtom "checked" : [SList [SAtom "leaf",leafAtom ident,encodeAtom (nf prop),SList (SAtom "deps":map objectSExpr deps)] | (ident,_,prop,deps) <- observations])
  , SList (SAtom "declared":map (leafAtom . leafId) (filter ((`notElem` checked) . leafId) leaves))
  , SList (SAtom "retained-checked":map leafAtom (filter (`elem` retainedLeaves) checked))
  , SList [SAtom "ordinary",ordinary]
  , SList (SAtom "retained" :
      [ SList (SAtom "leaves":map leafAtom retainedLeaves)
      , SList (SAtom "args":map (argAtom . fst) (unitArgs retained))
      , SList (SAtom "attacks":map encodeAttack (unitAttacks retained))
      , holes
      ])
  ]
  where
    checked = [ident | (ident,_,_,_) <- observations]
    retained = pruneChecked (pruneWithPolicySeed (Admission.policyQuarantineSeed table leaves) unit)
    retainedLeaves = map fst (unitLeaves retained)
    holes = case groupConflictReject unit of
      True -> SList [SAtom "core-rejected"]
      False -> case checkUnit (buildGamma (unitLeaves retained)) (buildCertOk (unitTheories retained)) retained of
        Left _ -> SList [SAtom "core-rejected"]
        Right checkedUnit -> SList (SAtom "holes" :
          [ SList [SAtom "hole",argAtom ident,encodeAtom (chConclusion hole),SList (SAtom "obligations":[SAtom q | QuestionId q <- chObligations hole])]
          | hole <- cuHoles checkedUnit
          , Just (ident,_) <- [lookup (chIndex hole) (zip [0..] (unitArgs retained))]
          ])
