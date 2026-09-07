{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wall -Werror=missing-fields -Werror=incomplete-patterns #-}

-- | Haskell half of the manifest-driven M5 surface conformance table.
--
-- The presentation fingerprint is FNV-1a-64 over UTF-8 bytes of an explicitly
-- framed test-only 'Sx'.  This encoder mirrors 'Lara.Presentation.printProgram'
-- and @printPolicy@ in Lean; it does not read Lean output.  Core fingerprints
-- use a second structured encoding of the semantic Unit (signature, core
-- policy, alpha-normalized support terms, and resolved attacks).  Cross-language
-- Show/Repr output is deliberately absent from the contract.
module Main (main) where

import Control.Monad (forM, unless, when)
import Data.Bits (xor)
import qualified Data.ByteString as B
import Data.List (findIndex, intercalate, nub)
import qualified Data.Text as T
import qualified Data.Text.Encoding as Text
import Data.Word (Word64)
import Numeric (showHex)
import System.Directory (doesFileExist)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath ((</>), takeDirectory)
import System.IO (stderr)

import Lara.AST
import qualified Lara.Admission as Admission
import qualified Lara.Attack as Attack
import qualified Lara.Blocked as Blocked
import qualified Lara.Check as Check
import qualified Lara.Compile as Compile
import Lara.Elaborate
import qualified Lara.Elaborate.Internal as ElabInternal
import Lara.Grounded (AF (..), completeClaimFor)
import qualified Lara.Grounded as Grounded
import qualified Lara.Prop as P
import qualified Lara.Semantics as Semantics
import qualified Lara.Sigma as Sigma
import qualified Lara.Strict as Strict
import qualified Lara.Strict.Insp as Insp
import qualified Lara.Strict.ND as ND
import qualified Lara.Strict.Ord as Ord
import qualified Lara.Strict.RA as RA
import Lara.SupportTerm (CertOutcome (..))
import qualified Lara.SupportTerm as SupportTerm
import Lara.Syntax (parsePolicy, parseProgram)
import qualified Lara.Wire as Wire

-- --------------------------------------------------------------------------
-- Manifest contract
-- --------------------------------------------------------------------------

data ManifestRow = ManifestRow
  { manifestCase :: String
  , manifestProgram :: FilePath
  , manifestPolicy :: FilePath
  , manifestExpected :: String
  , manifestFeatures :: [String]
  }

requiredFeatures :: [String]
requiredFeatures =
  [ "labelled-premise", "named-discharge", "comparison"
  , "value-interpolation", "cell-interpolation", "named-cert-premise"
  , "named-formula", "rule-binder", "nd-binder", "surface-attacks"
  , "capture-rejection", "ambiguous-premise-rejection"
  , "comparison-polarity-rejection", "attack-path-rejection"
  , "conclusion-mismatch-rejection", "challenge-target-rejection"
  , "unknown-status-rejection", "duplicate-group-id-rejection"
  , "group-repeated-member-rejection", "group-too-few-members-rejection"
  , "group-member-undeclared-rejection", "admission-prune", "open-obligation"
  ]

outputHeader :: String
outputHeader =
  "case_id\tast_fingerprint\toutcome\tcore_fingerprint\tobligations\tattacks\tobservations"

splitOn :: Char -> String -> [String]
splitOn _ [] = [""]
splitOn delimiter text =
  let (prefix, suffix) = break (== delimiter) text
   in prefix : case suffix of
        [] -> []
        _ : rest -> splitOn delimiter rest

loadManifest :: FilePath -> IO [ManifestRow]
loadManifest path = do
  bytes <- readUtf8File "manifest file" path
  case lines bytes of
    [] -> failUtf8 "surface conformance: empty manifest"
    header : records -> do
      unless (header == "case_id\tprogram\tpolicy\texpected\tfeatures") $
        failUtf8 "surface conformance: manifest header mismatch"
      when (null records) $ failUtf8 "surface conformance: manifest has no cases"
      rows <- forM (zip [2 :: Int ..] records) $ \(lineNo, line) ->
        case splitOn '\t' line of
          [caseId, program, policy, expected, featuresText]
            | all (not . null) [caseId, program, policy, expected, featuresText] -> do
                let features = splitOn ',' featuresText
                    unknown = filter (`notElem` requiredFeatures) features
                unless (null unknown) $
                  failUtf8 ("surface conformance: unknown feature in " ++ caseId ++ ": " ++ intercalate "," unknown)
                unless (length features == length (nub features)) $
                  failUtf8 ("surface conformance: duplicate feature in " ++ caseId)
                unless (expected == "accept" || "reject:" `prefixOf` expected) $
                  failUtf8 ("surface conformance: invalid expected outcome in " ++ caseId)
                pure (ManifestRow caseId program policy expected features)
          cells -> failUtf8 ("surface conformance: manifest line " ++ show lineNo
                    ++ " has " ++ show (length cells) ++ " columns")
      let covered = nub (concatMap manifestFeatures rows)
      unless (all (`elem` covered) requiredFeatures) $
        failUtf8 ("surface conformance: required feature coverage missing: "
          ++ intercalate "," (filter (`notElem` covered) requiredFeatures))
      unless (length (map manifestCase rows) == length (nub (map manifestCase rows))) $
        failUtf8 "surface conformance: duplicate case_id"
      pure rows
  where
    prefixOf prefix text = take (length prefix) text == prefix

-- --------------------------------------------------------------------------
-- Structured presentation encoding (independent mirror of Lean)
-- --------------------------------------------------------------------------

data Sx = SStr String | SInt Int | SNode String [Sx]

sxList :: (a -> Sx) -> [a] -> Sx
sxList encoder = SNode "l" . map encoder

sxPair :: (a -> Sx) -> (b -> Sx) -> (a, b) -> Sx
sxPair left right (a, b) = SNode "p" [left a, right b]

sxOpt :: (a -> Sx) -> Maybe a -> Sx
sxOpt _ Nothing = SNode "no" []
sxOpt encoder (Just value) = SNode "so" [encoder value]

sxTerm :: P.Term -> Sx
sxTerm = \case
  P.TNum text -> SNode "tn" [SStr text]
  P.TStr text -> SNode "ts" [SStr text]
  P.TCon (P.FunSym name) terms -> SNode "tc" (SStr name : map sxTerm terms)

sxAtom :: P.Prop -> Sx
sxAtom (P.Prop (P.Pred name) terms) = SNode "atom" (SStr name : map sxTerm terms)

sxPat :: Pat -> Sx
sxPat = \case
  PVar (Param name) -> SNode "pv" [SStr name]
  PLit term -> SNode "pl" [sxTerm term]
  PCon (P.FunSym name) pats -> SNode "pc" (SStr name : map sxPat pats)

sxAtomPat :: AtomPat -> Sx
sxAtomPat (AtomPat (P.Pred name) pats) = SNode "apat" (SStr name : map sxPat pats)

sxSort :: Sigma.Sort -> Sx
sxSort = \case
  Sigma.SortNum -> SNode "sort-num" []
  Sigma.SortStr -> SNode "sort-str" []
  Sigma.SortDecl (Sigma.SortName name) -> SNode "sort-decl" [SStr name]

sxSigma :: Sigma.Sigma -> Sx
sxSigma sigma = SNode "sigma"
  [ sxList (\(Sigma.SortName name) -> SStr name) (Sigma.sigmaSorts sigma)
  , sxList sxConSig (Sigma.sigmaCons sigma)
  , sxList sxPredSig (Sigma.sigmaPreds sigma)
  ]
  where
    sxConSig signature = SNode "con-sig"
      [ let P.FunSym name = Sigma.conSym signature in SStr name
      , sxList sxSort (Sigma.conArgs signature)
      , sxSort (Sigma.conResult signature)
      ]
    sxPredSig signature = SNode "pred-sig"
      [ let P.Pred name = Sigma.predSym signature in SStr name
      , sxList sxSort (Sigma.predArgs signature)
      ]

sxLeafKind :: LeafKind -> Sx
sxLeafKind Observed = SNode "observed" []
sxLeafKind Attested = SNode "attested" []
sxLeafKind Assumed = SNode "assumed" []
sxLeafKind Certified = SNode "certified" []

sxProvenance :: Provenance -> Sx
sxProvenance = \case
  User -> SNode "user" []
  AiExecuted -> SNode "ai" []
  Checker name version -> SNode "checker" [SStr name, SStr version]

sxAudit :: AuditStatus -> Sx
sxAudit = \case
  Unreviewed -> SNode "unreviewed" []
  Reviewed -> SNode "reviewed" []
  Disputed -> SNode "disputed" []

sxMode :: Mode -> Sx
sxMode Strict = SNode "strict" []
sxMode Defeasible = SNode "defeasible" []

sxNecessity :: Necessity -> Sx
sxNecessity Mandatory = SNode "mandatory" []
sxNecessity Optional = SNode "optional" []

sxAdmission :: Admission -> Sx
sxAdmission Admit = SNode "admit" []
sxAdmission Quarantine = SNode "quarantine" []
sxAdmission Reject = SNode "reject" []

sxGroupMode :: GroupConflictMode -> Sx
sxGroupMode QuarantineOnConflict = SNode "gq" []
sxGroupMode RejectOnConflict = SNode "gr" []

sxPolarity :: Polarity -> Sx
sxPolarity HigherIsBetter = SNode "hib" []
sxPolarity LowerIsBetter = SNode "lib" []

sxRelation :: Relation -> Sx
sxRelation StrictlyBetter = SNode "sb" []
sxRelation AtLeastAsGood = SNode "alag" []

sxBool :: Bool -> Sx
sxBool True = SNode "true" []
sxBool False = SNode "false" []

sxNative :: Strict.SExpr -> Sx
sxNative = \case
  Strict.SAtom atom -> SStr atom
  Strict.SList (Strict.SAtom tag : children) -> SNode tag (map sxNative children)
  Strict.SList children -> SNode "" (map sxNative children)

sxCert :: Cert -> Sx
sxCert (Cert (BackendId backend) version (TheoryDigest theory) payload) =
  SNode "cert" [SStr backend, SInt version, SStr theory, sxNative payload]

sxAssurance :: Assurance -> Sx
sxAssurance AssuranceNone = SNode "an" []
sxAssurance AssuranceTrusted = SNode "at" []
sxAssurance (AssuranceCert cert) = SNode "ac" [sxCert cert]

sxSupportTerm :: SupportTerm -> Sx
sxSupportTerm = \case
  SLeaf (LeafId leaf) -> SNode "sl" [SStr leaf]
  SRule (RuleId rule) theta premises discharges holes assurance ->
    SNode "sr"
      [ SStr rule
      , sxList (sxPair (\(Param name) -> SStr name) sxTerm) theta
      , SNode "prems" (map sxSupportTerm premises)
      , SNode "dis" [SNode "d" [SStr q, sxSupportTerm term]
                    | (QuestionId q, term) <- discharges]
      , sxList (\(ObligationId obligation) -> SStr obligation) holes
      , sxAssurance assurance
      ]

sxBinding :: Binding -> Sx
sxBinding binding = SNode "bind"
  [ SStr (bindingAuthor binding), SStr (bindingRationale binding)
  , sxAudit (bindingAuditStatus binding)
  ]

sxLeaf :: Leaf -> Sx
sxLeaf leaf = SNode "leaf"
  [ let LeafId name = leafId leaf in SStr name
  , sxAtom (leafProp leaf), sxLeafKind (leafKind leaf)
  , sxProvenance (leafProvenance leaf)
  , sxList (\(SourceRef source) -> SStr source) (leafRefs leaf)
  ]

sxClaim :: Claim -> Sx
sxClaim claim = SNode "claim"
  [ let PropId name = claimId claim in SStr name
  , SStr (claimNl claim), sxAtom (claimFormal claim), sxBinding (claimBinding claim)
  ]

sxQuestion :: Question -> Sx
sxQuestion question = SNode "q"
  [ let QuestionId name = questionId question in SStr name
  , sxAtomPat (questionAnswer question), sxNecessity (questionNecessity question)
  ]

sxCertRef :: CertRef -> Sx
sxCertRef (CertRef (BackendId backend) version (TheoryDigest theory)) =
  SNode "cref" [SStr backend, SInt version, SStr theory]

sxRule :: Rule -> Sx
sxRule rule = SNode "rule"
  [ let RuleId name = ruleId rule in SStr name
  , sxList (\(Param name) -> SStr name) (ruleParams rule)
  , sxMode (ruleMode rule)
  , sxList sxAtomPat (rulePremises rule)
  , sxList (sxOpt (\(PremiseLabel label) -> SStr label)) (rulePremiseLabels rule)
  , sxAtomPat (ruleConclusion rule)
  , sxBool (ruleAllowTrusted rule)
  , sxList sxCertRef (ruleCertifiers rule)
  , sxList sxQuestion (ruleQuestions rule)
  ]

sxContrary :: Contrary -> Sx
sxContrary (Contrary left right) = SNode "contra" [sxAtomPat left, sxAtomPat right]

sxException :: Exception -> Sx
sxException exception = SNode "exc"
  [let RuleId name = exceptionRule exception in SStr name, sxAtomPat (exceptionAtom exception)]

sxAdmissionEntry :: ((LeafKind, Provenance), Admission) -> Sx
sxAdmissionEntry = sxPair (sxPair sxLeafKind sxProvenance) sxAdmission

sxMeasurand :: Measurand -> Sx
sxMeasurand measurand = SNode "meas"
  [ let MeasurandId name = measurandId measurand in SStr name
  , sxSort (measurandSort measurand)
  , sxOpt sxPolarity (measurandPolarity measurand)
  ]

sxScheme :: ComparisonScheme -> Sx
sxScheme scheme = SNode "cscheme"
  [ sxRelation (csRelation scheme), sxPolarity (csPolarity scheme)
  , let RuleId name = csRecheck scheme in SStr name
  , let RuleId name = csBridge scheme in SStr name
  ]

sxPolicy :: Policy -> Sx
sxPolicy policy = SNode "policy"
  [ let PolicyId name = policyId policy in SStr name
  , sxSigma (policySigma policy)
  , sxList sxRule (policyRules policy)
  , sxList sxContrary (policyContraries policy)
  , sxList sxException (policyExceptions policy)
  , sxList sxAdmissionEntry (policyAdmission policy)
  , sxList (sxPair (\(TheoryDigest digest) -> SStr digest) (sxList sxAtom)) (policyTheories policy)
  , sxGroupMode (policyGroupMode policy)
  , sxList sxMeasurand (policyMeasurands policy)
  , sxList sxScheme (policyComparisonSchemes policy)
  ]

sxSurfaceStep :: SurfaceStep -> Sx
sxSurfaceStep (StepIndex index) = SNode "ssi" [SInt index]
sxSurfaceStep (StepName name) = SNode "ssn" [SStr name]

sxSurfaceAttack :: SurfaceAttack -> Sx
sxSurfaceAttack = \case
  SRebut (ArgId source) (ArgId target) -> SNode "sreb" [SStr source, SStr target]
  SUndercut (ArgId source) (ArgId target) path ->
    SNode "sunc" [SStr source, SStr target, sxList sxSurfaceStep path]
  SUndermine (ArgId source) (ArgId target) path ->
    SNode "sunm" [SStr source, SStr target, sxList sxSurfaceStep path]

sxChallenge :: ChallengeTarget -> Sx
sxChallenge (ChallengesQuestion (QuestionId question) (ArgId argument)) =
  SNode "chq" [SStr question, SStr argument]
sxChallenge (ChallengesLeaf (LeafId leaf)) = SNode "chl" [SStr leaf]

sxArgConcl :: ArgConcl -> Sx
sxArgConcl (SupportsClaim (PropId claim)) = SNode "sc" [SStr claim]
sxArgConcl (SupportsDerived (PropId claim)) = SNode "sd" [SStr claim]
sxArgConcl (Challenges target) = SNode "ch" [sxChallenge target]

sxArgInstantiation :: ArgInstantiation -> Sx
sxArgInstantiation (ExplicitTheta term) = SNode "et" [sxSupportTerm term]
sxArgInstantiation (InferTheta (RuleId rule) refs discharges obligations assurance) =
  SNode "it"
    [ SStr rule
    , sxList (\(ArgRef ref) -> SStr ref) refs
    , sxList (sxPair (\(QuestionId question) -> SStr question) (\(ArgRef ref) -> SStr ref)) discharges
    , sxList (\(ObligationId obligation) -> SStr obligation) obligations
    , sxAssurance assurance
    ]

sxArg :: Arg -> Sx
sxArg argument = SNode "arg"
  [ let ArgId name = argId argument in SStr name
  , sxArgConcl (argConcl argument), sxArgInstantiation (argInstantiation argument)
  ]

sxComparisonClaim :: ComparisonClaim -> Sx
sxComparisonClaim claim = SNode "cclaim"
  [let PropId name = ccId claim in SStr name, SStr (ccNlRaw claim), sxBinding (ccBinding claim)]

sxComparison :: Comparison -> Sx
sxComparison comparison = SNode "cmp"
  [ sxAtom (cmpConclusion comparison)
  , let MeasurandId name = cmpMeasurand comparison in SStr name
  , let DatasetId name = cmpDataset comparison in SStr name
  , sxRelation (cmpRelation comparison)
  , let ArgId name = cmpRecheckArg comparison in SStr name
  , let ArgId name = cmpBridgeArg comparison in SStr name
  , let LeafId name = cmpResult comparison in SStr name
  , let LeafId name = cmpBaseline comparison in SStr name
  , let LeafId name = cmpBinding comparison in SStr name
  , sxComparisonClaim (cmpClaim comparison)
  , sxOpt (\(PropId name) -> SStr name) (cmpSupports comparison)
  ]

sxDecl :: Decl -> Sx
sxDecl = \case
  DeclLeaf leaf -> SNode "dl" [sxLeaf leaf]
  DeclClaim claim -> SNode "dc" [sxClaim claim]
  DeclArg argument -> SNode "da" [sxArg argument]
  DeclAttack attack -> SNode "dk" [sxSurfaceAttack attack]
  DeclStatus (PropId claim) -> SNode "ds" [SStr claim]
  DeclGroup (DupGroup (GroupId group) members) -> SNode "dg"
    [SNode "group" [SStr group, sxList (\(LeafId leaf) -> SStr leaf) members]]
  DeclComparison comparison -> SNode "dm" [sxComparison comparison]

sxProgram :: Program -> Sx
sxProgram program = SNode "program"
  [ SStr (programArtifact program)
  , let Digest digest = programDigest program in SStr digest
  , let PolicyId policy = programPolicy program in SStr policy
  , sxList (sxPair (\(BackendId backend) -> SStr backend) SStr) (programBackends program)
  , sxList (\(ValueBinding (ValueName name) term) -> SNode "value-binding" [SStr name, sxTerm term])
      (programValueBindings program)
  , sxList sxDecl (programDecls program)
  ]

sxInput :: Program -> Policy -> Sx
sxInput program policy = SNode "input" [sxProgram program, sxPolicy policy]

-- --------------------------------------------------------------------------
-- Canonical framing and fingerprint
-- --------------------------------------------------------------------------

utf8Length :: String -> Int
utf8Length = B.length . utf8Bytes

-- | The sole String-to-byte boundary for the conformance contract.  Never use
-- Char8/locale truncation here: Lean's peer is exactly `String.toUTF8`.
utf8Bytes :: String -> B.ByteString
utf8Bytes = Text.encodeUtf8 . T.pack

readUtf8File :: String -> FilePath -> IO String
readUtf8File context path = do
  bytes <- B.readFile path
  case Text.decodeUtf8' bytes of
    Left _ -> failUtf8 ("surface conformance: " ++ context ++ " invalid UTF-8: " ++ path)
    Right value -> pure (T.unpack value)

writeUtf8Line :: String -> IO ()
writeUtf8Line value = B.putStr (utf8Bytes (value ++ "\n"))

failUtf8 :: String -> IO a
failUtf8 message = do
  B.hPutStr stderr (utf8Bytes (message ++ "\n"))
  exitFailure

renderSx :: Sx -> String
renderSx (SStr value) = "s" ++ show (utf8Length value) ++ ":" ++ value
renderSx (SInt value) = "i" ++ show value ++ ";"
renderSx (SNode tag children) =
  "n" ++ show (utf8Length tag) ++ ":" ++ tag ++ show (length children)
    ++ "[" ++ concatMap renderSx children ++ "]"

fnv1a64 :: B.ByteString -> Word64
fnv1a64 = B.foldl' step 14695981039346656037
  where step hash byte = (hash `xor` fromIntegral byte) * 1099511628211

fingerprint :: Sx -> String
fingerprint value = replicate (16 - length digits) '0' ++ digits
  where digits = showHex (fnv1a64 (utf8Bytes (renderSx value))) ""

-- --------------------------------------------------------------------------
-- Alpha-normalized semantic core encoding
-- --------------------------------------------------------------------------

type RuleEnv = [(RuleId, [Param])]

ruleEnv :: Unit -> RuleEnv
ruleEnv unit = [(ruleId rule, ruleParams rule) | rule <- unitRules unit]

alphaParam :: [Param] -> Param -> String
alphaParam params parameter = case findIndex (== parameter) params of
  Just index -> "$" ++ show index
  Nothing -> let Param name = parameter in name

sxCorePat :: [Param] -> Pat -> Sx
sxCorePat params = \case
  PVar parameter -> SNode "v" [SStr (alphaParam params parameter)]
  PLit term -> SNode "lit" [sxTerm term]
  PCon (P.FunSym name) pats -> SNode "con" (SStr name : map (sxCorePat params) pats)

sxCoreAtomPat :: [Param] -> AtomPat -> Sx
sxCoreAtomPat params (AtomPat (P.Pred name) pats) =
  SNode "apat" (SStr name : map (sxCorePat params) pats)

sxCoreRule :: Rule -> Sx
sxCoreRule rule =
  let params = ruleParams rule
   in SNode "rule"
      [ let RuleId name = ruleId rule in SStr name
      , sxMode (ruleMode rule)
      , sxList (SStr . alphaParam params) params
      , sxList (sxCoreAtomPat params) (rulePremises rule)
      , sxCoreAtomPat params (ruleConclusion rule)
      , sxList (\question -> SNode "question"
          [ let QuestionId name = questionId question in SStr name
          , sxCoreAtomPat params (questionAnswer question)
          , sxBool (questionNecessity question == Mandatory)
          ]) (ruleQuestions rule)
      , sxBool (ruleAllowTrusted rule)
      , sxList sxCertRef (ruleCertifiers rule)
      ]

paramsFor :: RuleEnv -> RuleId -> [Param]
paramsFor environment rule = maybe [] snd (findFirst ((== rule) . fst) environment)
  where
    findFirst _ [] = Nothing
    findFirst predicate (entry : rest)
      | predicate entry = Just entry
      | otherwise = findFirst predicate rest

sxCoreAssurance :: Assurance -> Sx
sxCoreAssurance AssuranceNone = SNode "none" []
sxCoreAssurance AssuranceTrusted = SNode "trusted" []
sxCoreAssurance (AssuranceCert (Cert (BackendId backend) version (TheoryDigest theory) payload)) =
  SNode "cert" [SStr backend, SInt version, SStr theory, sxNative payload]

sxCoreTerm :: RuleEnv -> SupportTerm -> Sx
sxCoreTerm environment = \case
  SLeaf (LeafId leaf) -> SNode "leaf" [SStr leaf]
  SRule rule theta premises discharges holes assurance ->
    let params = paramsFor environment rule
     in SNode "inst"
        [ let RuleId name = rule in SStr name
        , sxList (sxPair (SStr . alphaParam params) sxTerm) theta
        , sxList (sxCoreTerm environment) premises
        , sxList (sxPair (\(QuestionId question) -> SStr question) (sxCoreTerm environment)) discharges
        , sxList (\(ObligationId hole) -> SStr hole) holes
        , sxCoreAssurance assurance
        ]

sxCoreStep :: Step -> Sx
sxCoreStep (StepPremise index) = SNode "prem" [SInt index]
sxCoreStep (StepQuestion (QuestionId question)) = SNode "ques" [SStr question]

sxCoreAttack :: RuleEnv -> Attack.RAttack -> Sx
sxCoreAttack environment = \case
  Attack.RRebut source target -> SNode "rebut"
    [sxCoreTerm environment source, sxCoreTerm environment target]
  Attack.RUndercut source target path -> SNode "undercut"
    [sxCoreTerm environment source, sxCoreTerm environment target, sxList sxCoreStep path]
  Attack.RUndermine source target path -> SNode "undermine"
    [sxCoreTerm environment source, sxCoreTerm environment target, sxList sxCoreStep path]

sxCoreContrary :: Contrary -> Sx
sxCoreContrary (Contrary left right) = SNode "contrary" [sxCoreAtomPat [] left, sxCoreAtomPat [] right]

sxCoreException :: Exception -> Sx
sxCoreException (Exception (RuleId rule) atom) = SNode "exception" [SStr rule, sxCoreAtomPat [] atom]

sxCoreUnit :: Unit -> Sx
sxCoreUnit unit =
  let environment = ruleEnv unit
      resolved = Check.resolveAttacks (unitArgs unit) (unitAttacks unit)
   in SNode "core"
      [ sxSigma (unitSigma unit)
      , sxList sxCoreRule (unitRules unit)
      , sxList sxCoreContrary (unitContraries unit)
      , sxList sxCoreException (unitExceptions unit)
      , sxList (sxCoreTerm environment . snd) (unitArgs unit)
      , sxList (sxCoreAttack environment) resolved
      ]

-- --------------------------------------------------------------------------
-- Canonical evidence cells
-- --------------------------------------------------------------------------

percentAtom :: String -> String
percentAtom value
  | value == "-" = "%2d"
  | otherwise = concatMap encodeByte (B.unpack (utf8Bytes value))
  where
    encodeByte byte
      | safe byte = [toEnum (fromIntegral byte)]
      | otherwise = '%' : hex byte
    safe byte =
      (0x30 <= byte && byte <= 0x39)
        || (0x41 <= byte && byte <= 0x5a)
        || (0x61 <= byte && byte <= 0x7a)
        || byte `elem` map (fromIntegral . fromEnum) ("._:@/+~-" :: String)
    hex byte = [digits !! fromIntegral (byte `div` 16), digits !! fromIntegral (byte `mod` 16)]
    digits = "0123456789abcdef"

hexBytes :: String -> String
hexBytes = concatMap hex . B.unpack . utf8Bytes
  where
    hex byte = [digits !! fromIntegral (byte `div` 16), digits !! fromIntegral (byte `mod` 16)]
    digits = "0123456789abcdef"

codecVector :: String -> String
codecVector value = intercalate "\t"
  [ "utf8=" ++ hexBytes value
  , "length=" ++ show (utf8Length value)
  , "framed=" ++ renderSx (SStr value)
  , "percent=" ++ percentAtom value
  , "fingerprint=" ++ fingerprint (SStr value)
  ]

renderList :: [String] -> String
renderList [] = "-"
renderList values = intercalate "," (map percentAtom values)

renderAttack :: Attack -> String
renderAttack = \case
  Rebut (ArgId source) (ArgId target) -> "rebut:" ++ source ++ ":" ++ target
  Undercut (ArgId source) (ArgId target) path ->
    "undercut:" ++ source ++ ":" ++ target ++ concatMap renderStep path
  Undermine (ArgId source) (ArgId target) path ->
    "undermine:" ++ source ++ ":" ++ target ++ concatMap renderStep path
  where
    renderStep (StepPremise index) = ":premise:" ++ show index
    renderStep (StepQuestion (QuestionId question)) = ":question:" ++ question

buildGamma :: [(LeafId, P.Prop)] -> LeafId -> Maybe P.Prop
buildGamma leaves leaf = lookup leaf leaves

buildCertOk :: [(TheoryDigest, [P.Prop])] -> SupportTerm.CertOk
buildCertOk theories cert premises conclusion =
  case Strict.lookupBackend registry (Strict.BackendId name version) of
    Nothing -> CertRejected ("no registered backend " ++ name ++ "@" ++ show version)
    Just backend ->
      case Strict.runBackend backend (Strict.TheoryDigest theory) premises conclusion payload of
        Right dependencies -> CertAccepted dependencies
        Left reason -> CertRejected reason
  where
    Cert (BackendId name) version (TheoryDigest theory) payload = cert
    table = [(Strict.TheoryDigest digest, propositions)
            | (TheoryDigest digest, propositions) <- theories]
    registry = Strict.mkRegistry
      [ ND.mkNDBackend table
      , RA.mkRABackend table
      , Ord.mkOrdBackend table
      , Insp.mkInspBackend table
      ]

observeText :: (AF -> [[Int]]) -> AF -> Grounded.Claim -> String
observeText enumerate framework claim
  | null (Grounded.claimSupport claim) = "gap"
  | null extensions = "noExtension"
  | all accepts extensions = "justified"
  | all defeats extensions = "defeated"
  | otherwise = "contested"
  where
    extensions = enumerate framework
    accepts extension = any (`elem` extension) (Grounded.claimSupport claim)
    defeats extension = all (\argument -> any (\attacker -> afAttack framework attacker argument) extension)
      (Grounded.claimSupport claim)

semanticsTable :: [(String, AF -> [[Int]])]
semanticsTable =
  [ ("grounded", Semantics.enumerateGrounded)
  , ("complete", Semantics.enumerateComplete)
  , ("preferred", Semantics.enumeratePreferred)
  , ("stable", Semantics.enumerateStable)
  , ("semi-stable", Semantics.enumerateSemiStable)
  ]

claimIdsInOrder :: Program -> [PropId]
claimIdsInOrder program = [claim | DeclStatus claim <- programDecls program]

renderObservations :: Program -> Unit -> Check.CheckedUnit -> [String]
renderObservations program unit accepted =
  [ semanticsName ++ ":" ++ claimName ++ ":" ++ observeText enumerate framework claim
  | (semanticsName, enumerate) <- semanticsTable
  , (claimIdValue, proposition) <- zip (claimIdsInOrder program) (unitQueries unit)
  , let PropId claimName = claimIdValue
        claim = completeClaimFor (Check.cuNodes accepted) proposition
  ]
  where framework = Compile.checkedAF (Check.cuProgram accepted)

-- --------------------------------------------------------------------------
-- Production evaluation and structural outcomes
-- --------------------------------------------------------------------------

errorTag :: ElabError -> Maybe String
errorTag = \case
  CertNdBinderShadowsPremise {} -> Just "cert-binder-captures-premise"
  AmbiguousPremise {} -> Just "ambiguous-premise"
  CertSlotMultiSlot {} -> Just "ambiguous-premise"
  ComparisonSchemeDirectionMismatch {} -> Just "comparison-polarity"
  AttackStepUnresolved {} -> Just "attack-path"
  ConclusionMismatch {} -> Just "conclusion-mismatch"
  ChallengeTargetUndeclared {} -> Just "challenge-target"
  UnknownStatusClaim {} -> Just "unknown-status"
  DuplicateGroupId {} -> Just "duplicate-group-id"
  GroupRepeatedMember {} -> Just "group-repeated-member"
  GroupTooFewMembers {} -> Just "group-too-few-members"
  GroupMemberUndeclared {} -> Just "group-member-undeclared"
  _ -> Nothing

sourceInvalidTag :: SourceInvalid -> Maybe String
sourceInvalidTag (SourceElaborationError err) = errorTag err
sourceInvalidTag _ = Nothing

data OutputRow = OutputRow String String String String String String String

renderOutputRow :: OutputRow -> String
renderOutputRow (OutputRow caseId ast outcome core obligations attacks observations) =
  intercalate "\t" [caseId, ast, outcome, core, obligations, attacks, observations]

evaluateRow :: FilePath -> ManifestRow -> IO OutputRow
evaluateRow manifestPath row = do
  let root = takeDirectory manifestPath
      programPath = root </> manifestProgram row
      policyPath = root </> manifestPolicy row
  _ <- forM [programPath, policyPath] $ \path -> do
    exists <- doesFileExist path
    unless exists $ failUtf8 ("surface conformance: " ++ manifestCase row ++ ": missing file " ++ path)
  programText <- readUtf8File (manifestCase row ++ ": program file") programPath
  policyText <- readUtf8File (manifestCase row ++ ": policy file") policyPath
  program <- either (failUtf8 . contextual "program parse") pure (parseProgram programText)
  policy <- either (failUtf8 . contextual "policy parse") pure (parsePolicy policyText)
  let ast = fingerprint (sxInput program policy)
  case prepareSource program policy of
    Left invalid -> case sourceInvalidTag invalid of
      Nothing -> failUtf8 (contextual "unexpected source invalidity" invalid)
      Just tag -> do
        let actual = "reject:" ++ tag
        unless (manifestExpected row == actual) $
          failUtf8 (contextual "expected outcome mismatch" (manifestExpected row, actual, invalid))
        rejected ast tag
    Right (SourceRejected rejection) ->
      failUtf8 (contextual "unexpected admission rejection" rejection)
    Right (SourceAccepted sourceInput) -> do
      let sourceResult = runSourceCheck sourceInput
      case Wire.verdictOutcome (sourceResultVerdict sourceResult) of
        Wire.Reject rejection -> failUtf8 (contextual "unexpected checker rejection" rejection)
        Wire.Accept {} -> do
          declared <- either (failUtf8 . contextual "second production lowering") pure
            (ElabInternal.elaborate (ElabInternal.registryOf policy) program policy)
          let leaves = [leaf | DeclLeaf leaf <- programDecls program]
              seed = Admission.policyQuarantineSeed (policyAdmission policy) leaves
              checkedUnit = Blocked.pruneChecked (Blocked.pruneWithPolicySeed seed declared)
          accepted <- either (failUtf8 . contextual "checked pruned Unit") pure
            (Check.checkUnit (buildGamma (unitLeaves checkedUnit))
              (buildCertOk (unitTheories checkedUnit)) checkedUnit)
          let outcome = "accept"
              obligations = renderList
                [argument ++ ":" ++ obligation
                | (ArgId argument, term) <- unitArgs checkedUnit
                , ObligationId obligation <- holesOf term]
              attacks = renderList (map renderAttack (unitAttacks checkedUnit))
              observations = renderList (renderObservations program checkedUnit accepted)
              output = OutputRow (manifestCase row) ast outcome
                (fingerprint (sxCoreUnit checkedUnit)) obligations attacks observations
          unless (manifestExpected row == outcome) $
            failUtf8 (contextual "expected outcome mismatch" (manifestExpected row, outcome))
          pure output
  where
    contextual label detail = manifestCase row ++ ": " ++ label ++ ": " ++ show detail
    rejected ast tag = do
      let outcome = "reject:" ++ tag
      unless (manifestExpected row == outcome) $
        failUtf8 (contextual "expected outcome mismatch" (manifestExpected row, outcome))
      pure (OutputRow (manifestCase row) ast outcome "-" "-" "-" "-")
    holesOf (SLeaf _) = []
    holesOf (SRule _ _ premises discharges holes _) =
      holes ++ concatMap holesOf premises ++ concatMap (holesOf . snd) discharges

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--codec-vector", value] -> writeUtf8Line (codecVector value)
    ["--manifest", manifestPath] -> do
      rows <- loadManifest manifestPath
      outputs <- mapM (evaluateRow manifestPath) rows
      writeUtf8Line outputHeader
      mapM_ (writeUtf8Line . renderOutputRow) outputs
    _ -> failUtf8 "usage: surface-conformance --manifest PATH | --codec-vector TEXT"
