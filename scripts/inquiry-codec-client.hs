module Main (main) where

import Control.Monad (forM_, unless)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import System.Environment (getArgs)
import System.Exit (die)
import Lara.Strict (SExpr (..))
import qualified Lara.Wire as Raw
import qualified Lara.Process.Wire as Process
import qualified Lara.Process.Types as P
import qualified Lara.Process.Inquiry.Types as I
import qualified Lara.Process.Inquiry.Wire as W
import qualified Lara.Process.Analysis as A
import qualified Lara.Process.Audit.Types as Audit
import qualified Lara.Process.Impact as Impact

require :: Bool -> String -> IO ()
require condition detail = unless condition (die detail)

right :: Show e => Either e a -> IO a
right = either (die . show) pure

-- These are consumer assertions, not driver calls. Input and output are the
-- original file and captured stdout; comparison is on the parsed wire tree.
-- The caller supplies an independent decoder expectation; a consumer refusing
-- a valid original is a failure even when the driver output is a runtime error.
consume :: String -> FilePath -> FilePath -> IO ()
consume mode inputPath outputPath = do
  inputBytes <- BS.readFile inputPath
  output <- BS.readFile outputPath
  let input = W.parseInquiryInputBS inputBytes
  case mode of
    "accepted" -> do
      require (BS.isValidUtf8 inputBytes) "accepted input is not valid UTF-8"
      case input of
        Left refusal -> die ("expected accepted input: " ++ show refusal)
        Right _ -> pure ()
    "rejected" -> do
      require (BS.isValidUtf8 inputBytes) "decoder refusal input is not valid UTF-8"
      case input of
        Left _ -> pure ()
        Right _ -> die "expected input decoder refusal"
    "invalid-utf8" -> require (not (BS.isValidUtf8 inputBytes)) "IO case must contain invalid UTF-8"
    _ -> die ("unknown input expectation: " ++ mode)
  case input of
    Left _ -> pure () -- only explicitly expected decoder/UTF-8 refusals reach here
    Right value -> do
      original <- right (Raw.parseSExprBS inputBytes)
      require (W.encodeInquiryInput value == original) "input consumer changed wire AST"
      require (W.parseInquiryInput (W.encodeInquiryInput value) == Right value) "input typed roundtrip"
  require (BS.null output || BS.last output == 10) "output missing final LF"
  forM_ (BC.lines output) $ \line -> do
    tree <- right (Raw.parseSExprBS line)
    case tree of
      SList (SAtom "inquiry-error" : _) -> do
        value <- right (W.parseInquiryError tree)
        require (W.encodeInquiryError value == tree) "error consumer changed wire AST"
      _ -> case input of
        Left refusal -> die ("result without typed input: " ++ show refusal)
        Right value -> do
          let names = Process.documentNames (I.inquiryProcess value)
          result <- right (W.parseInquiryResult names tree)
          require (W.encodeInquiryResult names result == tree) "result consumer changed wire AST"

-- Fixtures cover every result-body tag. Values below additionally cover absent
-- histories, empty families, all verdicts/faults, optional labels, and naturals
-- beyond machine integers through the public consumer, not only the encoder.
values :: FilePath -> IO ()
values path = do
  input <- BS.readFile path >>= right . W.parseInquiryInputBS
  let names = Process.documentNames (I.inquiryProcess input)
      checkResult body = do
        let result = I.InquiryResult "α\\\"\n" body
            tree = W.encodeInquiryResult names result
        decoded <- right (W.parseInquiryResult names tree)
        require (decoded == result && W.encodeInquiryResult names decoded == tree) "result value roundtrip"
        case tree of
          SList fields -> require
            (W.parseInquiryResult names (SList (fields ++ [SAtom "extra"])) == Left (I.Malformed "malformed inquiry-result"))
            "result constructor arity"
          _ -> die "result encoder did not produce an envelope"
      huge = 2^(128 :: Int)
  forM_ [P.Inconsistent,P.CertainTrue,P.CertainFalse,P.Unknown] $ \verdict ->
    forM_ [Nothing,Just []] $ \holds -> forM_ [Nothing,Just []] $ \fails ->
      checkResult (I.HistoryVerdict huge (I.OutcomeAnswer verdict huge holds fails))
  checkResult (I.StatusBody (A.FamilyStatusResult [] huge 0 huge False))
  checkResult (I.AuditBody (A.FamilyAuditResult [] huge 0 huge False))
  forM_ [minBound..maxBound] $ \fault ->
    checkResult (I.VerificationBody (Impact.InvalidCertificate fault))
  checkResult (I.VerificationBody Impact.Verified)
  forM_ [Impact.RejectedToRejected,Impact.RejectedToAccepted,Impact.AcceptedToRejected,Impact.AcceptedToAccepted] $ \transition ->
    checkResult (I.ImpactBody (Impact.ImpactResult transition [] [] []))
  -- The fixed-witness namespace contains both claim and witness identities.
  let profile = P.ProfileSpec [P.Observed] [P.CompleteKind] P.FWER huge 0 [] P.GroundedJustified
      observable = A.AuditObservable (P.ClaimId 0) (P.WitnessId 0) profile
      completion = Audit.Completion [] []
      sensitivity = A.SensitivityResult observable completion huge 0 [] [[]] [([],completion)]
  checkResult (I.StabilityBody (A.StabilityResult observable huge 0 huge False False))
  checkResult (I.SensitivityBody sensitivity)
  checkResult (I.SlotsSensitiveBody sensitivity)
  let event = P.Stamped (P.EventId 0) (P.Access (P.ActorId 0) (P.DataId 0) P.Evaluation)
      literals = [A.SlotEq (Audit.SlotId huge) (Audit.ChoiceId huge)
        ,A.SlotNe (Audit.SlotId huge) (Audit.ChoiceId huge)
        ,A.Present event,A.Absent event,A.Before event event
        ,A.Formula (P.QueryAtom P.Predictable),A.NotFormula (P.QueryAtom P.Predictable)]
      target = A.AuditTarget (P.ClaimId 0) (P.WitnessId 0) profile
      deletion literal = A.Deletion literal [completion] (Just completion)
      minimal = A.MinimalSet literals [completion] (map deletion literals)
  checkResult (I.AssumptionsBody (A.AssumptionResult target literals huge [minimal]))
  let inputValue = input { I.inquiryCatalog = literals }
      inputTree = W.encodeInquiryInput inputValue
  decodedInput <- right (W.parseInquiryInput inputTree)
  require (decodedInput == inputValue && W.encodeInquiryInput decodedInput == inputTree) "input literal constructor families"
  case inputTree of
    SList fields -> require
      (W.parseInquiryInput (SList (fields ++ [SAtom "extra"])) == Left (I.Malformed "malformed inquiry-input"))
      "input constructor arity"
    _ -> die "input encoder did not produce a document"
  forM_ [Nothing,Just "",Just "α"] $ \label ->
    forM_ ([I.Malformed "detail",I.SyntaxError "line 1",I.Unsupported "feature",I.Version "2",I.Usage "usage",I.IOFailure "path"]
      ++ [I.Limit counter huge (huge-1) | counter <- [minBound..maxBound]]) $ \refusal -> do
        let value = I.InquiryError label refusal
            tree = W.encodeInquiryError value
        decoded <- right (W.parseInquiryError tree)
        require (decoded == value && W.encodeInquiryError decoded == tree) "error value roundtrip"
        case tree of
          SList fields -> require
            (W.parseInquiryError (SList (fields ++ [SAtom "extra"])) == Left (I.Malformed "malformed inquiry-error"))
            "error constructor arity"
          _ -> die "error encoder did not produce an envelope"
  forM_ ["inquiry-result","inquiry-error"] $ \tag -> do
    let parse = if tag == "inquiry-result" then fmap (const ()) . W.parseInquiryResult names else fmap (const ()) . W.parseInquiryError
    require (parse (SList [SAtom tag,SAtom "2"]) == Left (I.Version (tag ++ " supports version 1 only, found 2"))) "consumer version precedence"
    require (parse (SList [SAtom tag,SAtom "1"]) == Left (I.Malformed ("malformed " ++ tag))) "consumer malformed distinction"
  let inconsistentLabels = SList [SAtom "inquiry-result",SAtom "1",SAtom "outer",
        SList [SAtom "history-verdict",SList [SAtom "history-count",SAtom "1"],
          SList [SAtom "answer",SAtom "inner",SAtom "certainTrue",SList [SAtom "completions",SAtom "1"]]]]
  require (W.parseInquiryResult names inconsistentLabels == Left (I.Malformed "malformed inquiry-result")) "result labels must agree"

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["consume",mode,input,output] -> consume mode input output
    ["values",input] -> values input
    _ -> die "usage: inquiry-codec-client consume accepted|rejected|invalid-utf8 INPUT OUTPUT | values INPUT"
