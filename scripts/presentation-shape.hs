{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall -Werror=missing-fields -Werror=incomplete-patterns -Wno-orphans #-}

-- | The __Haskell side__ of the cross-language presentation-shape parity guard.
--
-- The guard does not parse source text. Each runtime contains exact constructor
-- witnesses, exhaustive eliminators, a normalized ordered inventory, and a
-- shape tripwire; the gate script compares the two inventories byte-for-byte.
--
-- @
--  Haskell types ──cabal build──▶ presentation-shape.hs ──┐  witnesses: compile-time
--   (Lara.AST,                    (witnesses + shape      │  tripwire: rows ==
--    Lara.Sigma)                   tripwire + shapeRows)  ▼            real shape
--                                                  haskell.tsv ──┐
--                                                                ├─ diff -u ─▶ PASS/FAIL
--                                                    lean.tsv ───┘
--   Lean types  ──lake build───▶ presentation-shape ──────▲
--    (Lara.Presentation)          (lean_exe: witnesses + shapeRows)
-- @
--
-- Three things hold the guard up, and each fails at __compile__ time, before a
-- row is ever printed:
--
--   1. every record has an exact constructor-signature witness, so a field
--      added, dropped, or retyped stops this file compiling; named record
--      selectors are also normalized and compared with the inventory, so a
--      rename or reorder cannot hide behind an unchanged positional type
--      sequence;
--   2. every payload-carrying sum arm has an exact constructor-signature
--      witness, and every sum has an exhaustive eliminator whose arms bind
--      constructor arguments at __full positional arity__ (@SRule _ _ _ _ _ _@,
--      never a record wildcard or a whole-payload catch-all), so a new
--      constructor, payload retype, or payload-arity change stops this file
--      compiling;
--   3. the shape tripwire below re-derives every row's real part count from the
--      datatype's own @GHC.Generics@ metadata and, for named records, its
--      normalized selector sequence. It refuses to print if the inventory
--      disagrees, so a row cannot be padded or relabeled to fake agreement.
--
-- == Named representation exemptions
--
--   1. __@SortName@ is witnessed but row-erased.__ There is a
--      @String -> SortName@ witness below, but no @SortName@ inventory row:
--      Lean's @Sigma.sorts@ is a @List String@, so the sort-name wrapper
--      normalizes to a bare string on both sides.
--   2. __@Cert@'s @payload@ is exempt from shape comparison.__ It is each
--      language's native S-expression type (Haskell 'SExpr', Lean @Sx@); the
--      @Cert@ row names the field, and nothing compares the two payload types.
--
-- Two further normalization notes, for the same reason:
--
--   * the @FunSym@ / @Pred@ rows are the Haskell @Lara.Prop@ newtypes and the
--     Lean @Lara.Support.ConSym@ / @Lara.Support.PredSym@ structures — the
--     frozen Lean semantic core spells the symbol wrappers there, and
--     @Lara.Presentation@ reuses them through @ConSig@ / @PredSig@ rather than
--     declaring a parallel pair;
--   * the @Prop@ row is Haskell's @Lara.Prop.Prop@ and Lean's @Lara.Atom@
--     (@Prop@ is a Lean keyword), which is why its parts are the two
--     constructor arguments @pred@ / @args@ rather than field names.
--
-- Finally, the @Attack@ / @Step@ / @Position@ rows are modeled by
-- @Lara.Presentation@ even though the __elaborator__, not the surface parser,
-- produces resolved 'Attack' values: @DeclAttack@ carries the surface
-- 'SurfaceAttack', and the frozen trio is kept, codec'd, and proved alongside
-- it. Both are in the guard's scope.
module Main (main) where

import Control.Monad (unless)
import Data.Char (isUpper, toLower)
import Data.List (intercalate, stripPrefix)
import GHC.Generics
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Lara.AST
import Lara.Sigma
import Lara.Strict (SExpr)
import qualified Lara.Prop as P

-- ---------------------------------------------------------------------------
-- Identifier and symbol witnesses
-- ---------------------------------------------------------------------------
--
-- Each is an exact @String -> <newtype>@ ascription: retyping the payload, or
-- widening a newtype into a record, stops this file compiling.

propIdCtor :: String -> PropId
propIdCtor = PropId

questionIdCtor :: String -> QuestionId
questionIdCtor = QuestionId

leafIdCtor :: String -> LeafId
leafIdCtor = LeafId

ruleIdCtor :: String -> RuleId
ruleIdCtor = RuleId

argIdCtor :: String -> ArgId
argIdCtor = ArgId

argRefCtor :: String -> ArgRef
argRefCtor = ArgRef

obligationIdCtor :: String -> ObligationId
obligationIdCtor = ObligationId

backendIdCtor :: String -> BackendId
backendIdCtor = BackendId

policyIdCtor :: String -> PolicyId
policyIdCtor = PolicyId

paramCtor :: String -> Param
paramCtor = Param

sourceRefCtor :: String -> SourceRef
sourceRefCtor = SourceRef

theoryDigestCtor :: String -> TheoryDigest
theoryDigestCtor = TheoryDigest

digestCtor :: String -> Digest
digestCtor = Digest

groupIdCtor :: String -> GroupId
groupIdCtor = GroupId

measurandIdCtor :: String -> MeasurandId
measurandIdCtor = MeasurandId

datasetIdCtor :: String -> DatasetId
datasetIdCtor = DatasetId

premiseLabelCtor :: String -> PremiseLabel
premiseLabelCtor = PremiseLabel

valueNameCtor :: String -> ValueName
valueNameCtor = ValueName

valueNameText :: ValueName -> String
valueNameText value = case value of
  ValueName text -> text

-- | Exemption 1: witnessed, but row-erased (Lean's @Sigma.sorts@ is
-- @List String@).
sortNameCtor :: String -> SortName
sortNameCtor = SortName

funSymCtor :: String -> FunSym
funSymCtor = FunSym

predCtor :: String -> Pred
predCtor = Pred

propCtor :: Pred -> [P.Term] -> P.Prop
propCtor = P.Prop
-- ---------------------------------------------------------------------------
-- Normalized alias/entry witnesses
-- ---------------------------------------------------------------------------

-- These expected shapes are deliberately local to the guard. Constructor
-- witnesses below tie the anonymous tuple entries to the fields that carry
-- them; the two identity witnesses tie the real AST aliases to their expected
-- expansions.
type ExpectedAdmissionEntry = ((LeafKind, Provenance), Admission)
type ExpectedTheoryEntry = (TheoryDigest, [P.Prop])
type ExpectedBackendEntry = (BackendId, String)
type ExpectedSubst = [(Param, P.Term)]
type ExpectedDischargeEntry = (QuestionId, SupportTerm)
type ExpectedArgDischarge = [(QuestionId, ArgRef)]
type ExpectedPosition = [Step]

substWitness :: Subst -> ExpectedSubst
substWitness = id

positionWitness :: Position -> ExpectedPosition
positionWitness = id

argDischargeWitness :: ArgDischarge -> ExpectedArgDischarge
argDischargeWitness = id

-- ---------------------------------------------------------------------------
-- Record constructor witnesses
-- ---------------------------------------------------------------------------

atomPatCtor :: Pred -> [Pat] -> AtomPat
atomPatCtor = AtomPat

leafCtor :: LeafId -> P.Prop -> LeafKind -> Provenance -> [SourceRef] -> Leaf
leafCtor = Leaf

bindingCtor :: String -> String -> AuditStatus -> Binding
bindingCtor = Binding

claimCtor :: PropId -> String -> P.Prop -> Binding -> Claim
claimCtor = Claim

questionCtor :: QuestionId -> AtomPat -> Necessity -> Question
questionCtor = Question

certRefCtor :: BackendId -> Int -> TheoryDigest -> CertRef
certRefCtor = CertRef

ruleCtor ::
  RuleId -> [Param] -> Mode -> [AtomPat] -> [Maybe PremiseLabel] ->
  AtomPat -> Bool -> [CertRef] -> [Question] -> Rule
ruleCtor = Rule

contraryCtor :: AtomPat -> AtomPat -> Contrary
contraryCtor = Contrary

exceptionCtor :: RuleId -> AtomPat -> Exception
exceptionCtor = Exception

dupGroupCtor :: GroupId -> [LeafId] -> DupGroup
dupGroupCtor = DupGroup

conSigCtor :: FunSym -> [Sort] -> Sort -> ConSig
conSigCtor = ConSig

predSigCtor :: Pred -> [Sort] -> PredSig
predSigCtor = PredSig

sigmaCtor :: [SortName] -> [ConSig] -> [PredSig] -> Sigma
sigmaCtor = Sigma

measurandCtor :: MeasurandId -> Sort -> Maybe Polarity -> Measurand
measurandCtor = Measurand

comparisonSchemeCtor :: Relation -> Polarity -> RuleId -> RuleId -> ComparisonScheme
comparisonSchemeCtor = ComparisonScheme

policyCtor ::
  PolicyId -> Sigma -> [Rule] -> [Contrary] -> [Exception] ->
  [ExpectedAdmissionEntry] -> [ExpectedTheoryEntry] ->
  GroupConflictMode -> [Measurand] -> [ComparisonScheme] -> Policy
policyCtor = Policy

-- | Exemption 2: @payload@ is the native S-expression type and is not compared.
certCtor :: BackendId -> Int -> TheoryDigest -> SExpr -> Cert
certCtor = Cert

sruleCtor ::
  RuleId -> Subst -> [SupportTerm] -> [ExpectedDischargeEntry] ->
  [ObligationId] -> Assurance -> SupportTerm
sruleCtor = SRule

argCtor :: ArgId -> ArgConcl -> ArgInstantiation -> Arg
argCtor = Arg

comparisonClaimCtor :: PropId -> String -> Binding -> ComparisonClaim
comparisonClaimCtor = ComparisonClaim

comparisonCtor ::
  P.Prop -> MeasurandId -> DatasetId -> Relation -> ArgId -> ArgId ->
  LeafId -> LeafId -> LeafId -> ComparisonClaim -> Maybe PropId -> Comparison
comparisonCtor = Comparison

valueBindingCtor :: ValueName -> P.Term -> ValueBinding
valueBindingCtor = ValueBinding

programCtor ::
  String -> Digest -> PolicyId -> [ExpectedBackendEntry] ->
  [ValueBinding] -> [Decl] -> Program
programCtor = Program

-- M5 coverage witnesses.  These intentionally repeat the exact production
-- constructors behind the five appended M5 inventory rows: the rows are not
-- labels floating beside the model; each has a compile-time type ascription.
m5RuleCarrier ::
  RuleId -> [Param] -> Mode -> [AtomPat] -> [Maybe PremiseLabel] ->
  AtomPat -> Bool -> [CertRef] -> [Question] -> Rule
m5RuleCarrier = Rule

m5InferThetaCarrier ::
  RuleId -> [ArgRef] -> ArgDischarge -> [ObligationId] -> Assurance ->
  ArgInstantiation
m5InferThetaCarrier = InferTheta

m5ComparisonCarrier ::
  P.Prop -> MeasurandId -> DatasetId -> Relation -> ArgId -> ArgId ->
  LeafId -> LeafId -> LeafId -> ComparisonClaim -> Maybe PropId -> Comparison
m5ComparisonCarrier = Comparison

m5ValueBindingCarrier :: ValueName -> P.Term -> ValueBinding
m5ValueBindingCarrier = ValueBinding

m5CertCarrier :: BackendId -> Int -> TheoryDigest -> SExpr -> Cert
m5CertCarrier = Cert

-- ---------------------------------------------------------------------------
-- Sum-constructor payload witnesses
-- ---------------------------------------------------------------------------
--
-- Exhaustive eliminators pin constructor presence and payload arity. These
-- exact ascriptions additionally pin every payload type.

termNumCtor :: String -> P.Term
termNumCtor = P.TNum

termStrCtor :: String -> P.Term
termStrCtor = P.TStr

termConCtor :: FunSym -> [P.Term] -> P.Term
termConCtor = P.TCon

provenanceCheckerCtor :: String -> String -> Provenance
provenanceCheckerCtor = Checker

sortDeclCtor :: SortName -> Sort
sortDeclCtor = SortDecl

patVarCtor :: Param -> Pat
patVarCtor = PVar

patLitCtor :: P.Term -> Pat
patLitCtor = PLit

patConCtor :: FunSym -> [Pat] -> Pat
patConCtor = PCon

assuranceCertCtor :: Cert -> Assurance
assuranceCertCtor = AssuranceCert

supportLeafCtor :: LeafId -> SupportTerm
supportLeafCtor = SLeaf

stepPremiseCtor :: Int -> Step
stepPremiseCtor = StepPremise

stepQuestionCtor :: QuestionId -> Step
stepQuestionCtor = StepQuestion

rebutCtor :: ArgId -> ArgId -> Attack
rebutCtor = Rebut

undercutCtor :: ArgId -> ArgId -> ExpectedPosition -> Attack
undercutCtor = Undercut

undermineCtor :: ArgId -> ArgId -> ExpectedPosition -> Attack
undermineCtor = Undermine

surfaceStepIndexCtor :: Int -> SurfaceStep
surfaceStepIndexCtor = StepIndex

surfaceStepNameCtor :: String -> SurfaceStep
surfaceStepNameCtor = StepName

surfaceRebutCtor :: ArgId -> ArgId -> SurfaceAttack
surfaceRebutCtor = SRebut

surfaceUndercutCtor :: ArgId -> ArgId -> [SurfaceStep] -> SurfaceAttack
surfaceUndercutCtor = SUndercut

surfaceUndermineCtor :: ArgId -> ArgId -> [SurfaceStep] -> SurfaceAttack
surfaceUndermineCtor = SUndermine

challengeQuestionCtor :: QuestionId -> ArgId -> ChallengeTarget
challengeQuestionCtor = ChallengesQuestion

challengeLeafCtor :: LeafId -> ChallengeTarget
challengeLeafCtor = ChallengesLeaf

supportsClaimCtor :: PropId -> ArgConcl
supportsClaimCtor = SupportsClaim

supportsDerivedCtor :: PropId -> ArgConcl
supportsDerivedCtor = SupportsDerived

challengesCtor :: ChallengeTarget -> ArgConcl
challengesCtor = Challenges

explicitThetaCtor :: SupportTerm -> ArgInstantiation
explicitThetaCtor = ExplicitTheta

inferThetaCtor ::
  RuleId -> [ArgRef] -> ExpectedArgDischarge -> [ObligationId] -> Assurance ->
  ArgInstantiation
inferThetaCtor = InferTheta

declLeafCtor :: Leaf -> Decl
declLeafCtor = DeclLeaf

declClaimCtor :: Claim -> Decl
declClaimCtor = DeclClaim

declArgCtor :: Arg -> Decl
declArgCtor = DeclArg

declAttackCtor :: SurfaceAttack -> Decl
declAttackCtor = DeclAttack

declStatusCtor :: PropId -> Decl
declStatusCtor = DeclStatus

declGroupCtor :: DupGroup -> Decl
declGroupCtor = DeclGroup

declComparisonCtor :: Comparison -> Decl
declComparisonCtor = DeclComparison

-- ---------------------------------------------------------------------------
-- Exhaustive eliminators
-- ---------------------------------------------------------------------------
--
-- One per closed sum. Every arm binds its constructor's arguments at full
-- positional arity, so both a new constructor (-Werror=incomplete-patterns) and
-- a changed payload arity break the build here.

termTag :: P.Term -> String
termTag t = case t of
  P.TNum _ -> "num"
  P.TStr _ -> "str"
  P.TCon _ _ -> "con"

leafKindTag :: LeafKind -> String
leafKindTag k = case k of
  Observed -> "observed"
  Attested -> "attested"
  Assumed -> "assumed"
  Certified -> "certified"

provenanceTag :: Provenance -> String
provenanceTag p = case p of
  User -> "user"
  AiExecuted -> "ai-executed"
  Checker _ _ -> "checker(name,version)"

auditStatusTag :: AuditStatus -> String
auditStatusTag a = case a of
  Unreviewed -> "unreviewed"
  Reviewed -> "reviewed"
  Disputed -> "disputed"

modeTag :: Mode -> String
modeTag m = case m of
  Strict -> "strict"
  Defeasible -> "defeasible"

necessityTag :: Necessity -> String
necessityTag n = case n of
  Mandatory -> "mandatory"
  Optional -> "optional"

admissionTag :: Admission -> String
admissionTag a = case a of
  Admit -> "admit"
  Quarantine -> "quarantine"
  Reject -> "reject"

groupConflictModeTag :: GroupConflictMode -> String
groupConflictModeTag g = case g of
  QuarantineOnConflict -> "quarantine-on-conflict"
  RejectOnConflict -> "reject-on-conflict"

polarityTag :: Polarity -> String
polarityTag p = case p of
  HigherIsBetter -> "higher-is-better"
  LowerIsBetter -> "lower-is-better"

relationTag :: Relation -> String
relationTag r = case r of
  StrictlyBetter -> "strictly-better"
  AtLeastAsGood -> "at-least-as-good"

sortTag :: Sort -> String
sortTag s = case s of
  SortNum -> "num"
  SortStr -> "str"
  SortDecl _ -> "decl"

patTag :: Pat -> String
patTag p = case p of
  PVar _ -> "var"
  PLit _ -> "lit"
  PCon _ _ -> "con"

assuranceTag :: Assurance -> String
assuranceTag a = case a of
  AssuranceNone -> "none"
  AssuranceTrusted -> "trusted"
  AssuranceCert _ -> "cert"

supportTermTag :: SupportTerm -> String
supportTermTag w = case w of
  SLeaf _ -> "leaf"
  SRule _ _ _ _ _ _ -> "rule"

stepTag :: Step -> String
stepTag s = case s of
  StepPremise _ -> "premise"
  StepQuestion _ -> "question"

attackTag :: Attack -> String
attackTag k = case k of
  Rebut _ _ -> "rebut"
  Undercut _ _ _ -> "undercut"
  Undermine _ _ _ -> "undermine"

surfaceStepTag :: SurfaceStep -> String
surfaceStepTag s = case s of
  StepIndex _ -> "index"
  StepName _ -> "name"

surfaceAttackTag :: SurfaceAttack -> String
surfaceAttackTag k = case k of
  SRebut _ _ -> "rebut"
  SUndercut _ _ _ -> "undercut"
  SUndermine _ _ _ -> "undermine"

challengeTargetTag :: ChallengeTarget -> String
challengeTargetTag t = case t of
  ChallengesQuestion _ _ -> "question"
  ChallengesLeaf _ -> "leaf"

argConclTag :: ArgConcl -> String
argConclTag c = case c of
  SupportsClaim _ -> "supports-claim"
  SupportsDerived _ -> "supports-derived"
  Challenges _ -> "challenges"

argInstantiationTag :: ArgInstantiation -> String
argInstantiationTag inst = case inst of
  ExplicitTheta _ -> "explicit-theta"
  InferTheta _ _ _ _ _ -> "infer-theta"

declTag :: Decl -> String
declTag decl = case decl of
  DeclLeaf _ -> "leaf"
  DeclClaim _ -> "claim"
  DeclArg _ -> "arg"
  DeclAttack _ -> "attack"
  DeclStatus _ -> "status"
  DeclGroup _ -> "group"
  DeclComparison _ -> "comparison"

-- | Sink that consumes every witness above, so @-Wall@ stays clean while the
-- type ascriptions and the exhaustive @case@ arms stay load-bearing.
witnesses :: [()]
witnesses =
  [ used propIdCtor, used questionIdCtor, used leafIdCtor, used ruleIdCtor
  , used argIdCtor, used obligationIdCtor, used backendIdCtor, used policyIdCtor
  , used paramCtor, used sourceRefCtor, used theoryDigestCtor, used digestCtor
  , used groupIdCtor, used measurandIdCtor, used datasetIdCtor
  , used premiseLabelCtor, used valueNameCtor, used valueNameText
  , used sortNameCtor, used funSymCtor, used predCtor
  , used argRefCtor, used argDischargeWitness
  , used propCtor, used substWitness, used positionWitness
  , used atomPatCtor, used leafCtor, used bindingCtor, used claimCtor
  , used questionCtor, used certRefCtor, used ruleCtor, used contraryCtor
  , used exceptionCtor, used dupGroupCtor, used conSigCtor, used predSigCtor
  , used sigmaCtor, used measurandCtor, used comparisonSchemeCtor
  , used policyCtor, used certCtor, used sruleCtor, used argCtor
  , used explicitThetaCtor, used inferThetaCtor
  , used comparisonClaimCtor, used comparisonCtor, used valueBindingCtor
  , used programCtor, used termNumCtor, used termStrCtor, used termConCtor
  , used m5RuleCarrier, used m5InferThetaCarrier, used m5ComparisonCarrier
  , used m5ValueBindingCarrier, used m5CertCarrier
  , used provenanceCheckerCtor, used sortDeclCtor
  , used patVarCtor, used patLitCtor, used patConCtor
  , used assuranceCertCtor, used supportLeafCtor
  , used stepPremiseCtor, used stepQuestionCtor
  , used rebutCtor, used undercutCtor, used undermineCtor
  , used surfaceStepIndexCtor, used surfaceStepNameCtor
  , used surfaceRebutCtor, used surfaceUndercutCtor, used surfaceUndermineCtor
  , used challengeQuestionCtor, used challengeLeafCtor
  , used supportsClaimCtor, used supportsDerivedCtor, used challengesCtor
  , used declLeafCtor, used declClaimCtor, used declArgCtor, used declAttackCtor
  , used declStatusCtor, used declGroupCtor, used declComparisonCtor
  , used termTag, used leafKindTag, used provenanceTag, used auditStatusTag
  , used modeTag, used necessityTag, used admissionTag, used groupConflictModeTag
  , used polarityTag, used relationTag, used sortTag, used patTag
  , used assuranceTag, used supportTermTag, used stepTag, used attackTag
  , used surfaceStepTag, used surfaceAttackTag, used challengeTargetTag
  , used argConclTag, used argInstantiationTag, used declTag
  ]
  where
    used :: a -> ()
    used _ = ()

-- ---------------------------------------------------------------------------
-- The normalized inventory
-- ---------------------------------------------------------------------------

-- | The complete surface-reachable shape, in the order both runtimes emit it.
-- Row order is part of the comparison contract. Row labels are __semantic__
-- strings, not identifiers: the @Sort@ row is spelled @Sort@ on both sides even
-- though the Lean identifier is @TermSort@.
shapeRows :: [(String, [String])]
shapeRows =
  [ ("PropId", ["val"])
  , ("QuestionId", ["val"])
  , ("LeafId", ["val"])
  , ("RuleId", ["val"])
  , ("ArgId", ["val"])
  , ("ObligationId", ["val"])
  , ("BackendId", ["val"])
  , ("PolicyId", ["val"])
  , ("Param", ["val"])
  , ("SourceRef", ["val"])
  , ("TheoryDigest", ["val"])
  , ("Digest", ["val"])
  , ("GroupId", ["val"])
  , ("MeasurandId", ["val"])
  , ("DatasetId", ["val"])
  , ("PremiseLabel", ["val"])
  , ("ValueName", ["val"])
  , ("FunSym", ["val"])
  , ("Pred", ["val"])
  , ("Term", ["num", "str", "con"])
  , ("Prop", ["pred", "args"])
  , ("LeafKind", ["observed", "attested", "assumed", "certified"])
  , ("Provenance", ["user", "ai-executed", "checker(name,version)"])
  , ("AuditStatus", ["unreviewed", "reviewed", "disputed"])
  , ("Mode", ["strict", "defeasible"])
  , ("Necessity", ["mandatory", "optional"])
  , ("Admission", ["admit", "quarantine", "reject"])
  , ("GroupConflictMode", ["quarantine-on-conflict", "reject-on-conflict"])
  , ("Polarity", ["higher-is-better", "lower-is-better"])
  , ("Relation", ["strictly-better", "at-least-as-good"])
  , ("Sort", ["num", "str", "decl"])
  , ("Pat", ["var", "lit", "con"])
  , ("Assurance", ["none", "trusted", "cert"])
  , ("SupportTerm", ["leaf", "rule"])
  , ("Step", ["premise", "question"])
  , ("Attack", ["rebut", "undercut", "undermine"])
  , ("SurfaceStep", ["index", "name"])
  , ("SurfaceAttack", ["rebut", "undercut", "undermine"])
  , ("ChallengeTarget", ["question", "leaf"])
  , ("ArgConcl", ["supports-claim", "supports-derived", "challenges"])
  , ("Decl", ["leaf", "claim", "arg", "attack", "status", "group", "comparison"])
  , ("AtomPat", ["pred", "args"])
  , ("Leaf", ["id", "prop", "kind", "provenance", "refs"])
  , ("Binding", ["author", "rationale", "audit-status"])
  , ("Claim", ["id", "nl", "formal", "binding"])
  , ("Question", ["id", "answer", "necessity"])
  , ("CertRef", ["backend", "version", "theory"])
  , ( "Rule"
    , [ "id", "params", "mode", "premises", "premise-labels", "conclusion"
      , "allow-trusted", "certifiers", "questions"
      ]
    )
  , ("Contrary", ["left", "right"])
  , ("Exception", ["rule", "atom"])
  , ("DupGroup", ["id", "members"])
  , ("ConSig", ["sym", "args", "result"])
  , ("PredSig", ["sym", "args"])
  , ("Sigma", ["sorts", "cons", "preds"])
  , ("Measurand", ["id", "sort", "polarity"])
  , ("ComparisonScheme", ["relation", "polarity", "recheck", "bridge"])
  , ( "Policy"
    , [ "id", "sigma", "rules", "contraries", "exceptions", "admission"
      , "theories", "group-mode", "measurands", "comparison-schemes"
      ]
    )
  , ("Cert", ["backend", "version", "theory", "payload"])
  , ("SRule", ["rule", "subst", "premises", "discharge", "holes", "assurance"])
  , ("ArgRef", ["val"])
  , ("ArgDischarge", ["entries:List (QuestionId,ArgRef)"])
  , ("ArgInstantiation", ["explicit-theta", "infer-theta"])
  , ("Arg", ["id", "conclusion", "instantiation"])
  , ("ComparisonClaim", ["id", "nl-raw", "binding"])
  , ( "Comparison"
    , [ "conclusion", "measurand", "dataset", "relation", "recheck-arg"
      , "bridge-arg", "result", "baseline", "binding", "claim", "supports"
      ]
    )
  , ("ValueBinding", ["name", "term"])
  , ("Program", ["artifact", "digest", "policy", "backends", "value-bindings", "decls"])
  , ("AdmissionEntry", ["key:(LeafKind,Provenance)", "value:Admission"])
  , ("TheoryEntry", ["digest:TheoryDigest", "atoms:List Prop"])
  , ("BackendEntry", ["backend:BackendId", "version:String"])
  , ("Subst", ["entries:List (Param,Term)"])
  , ("DischargeEntry", ["question:QuestionId", "term:SupportTerm"])
  , ("Position", ["steps:List Step"])
  , ( "M5.Rule"
    , [ "id", "params", "mode", "premises", "premise-labels", "conclusion"
      , "allow-trusted", "certifiers", "questions" ]
    )
  , ("M5.InferTheta", ["rule", "refs", "discharge", "obligations", "assurance"])
  , ( "M5.Comparison"
    , [ "conclusion", "measurand", "dataset", "relation", "recheck-arg"
      , "bridge-arg", "result", "baseline", "binding", "claim", "supports" ]
    )
  , ("M5.ValueBinding", ["name", "term"])
  , ("M5.Cert", ["backend", "version", "theory", "payload"])
  ]

renderRow :: (String, [String]) -> String
renderRow (name, parts) = intercalate "\t" (name : parts)

-- ---------------------------------------------------------------------------
-- The shape tripwire
-- ---------------------------------------------------------------------------
--
-- Constructor names, positional arities, and named selectors read off a type's
-- own 'Generic' metadata. The inventory above is hand-written; this re-derives
-- counts for every row and selector order for named records. Positional
-- semantic labels and swaps among same-typed fields remain assertions because
-- those constructors expose no selector names.

class GCtors f where
  gCtors :: f p -> [(String, Int)]

instance GCtors V1 where
  gCtors _ = []

instance (GCtors f, GCtors g) => GCtors (f :+: g) where
  gCtors _ = gCtors (undefined :: f p) ++ gCtors (undefined :: g p)

instance GCtors f => GCtors (M1 D d f) where
  gCtors _ = gCtors (undefined :: f p)

instance (Constructor c, GArity f) => GCtors (M1 C c f) where
  gCtors x = [(conName x, gArity (undefined :: f p))]

class GArity f where
  gArity :: f p -> Int

instance GArity U1 where
  gArity _ = 0

instance GArity (K1 i c) where
  gArity _ = 1

instance (GArity f, GArity g) => GArity (f :*: g) where
  gArity _ = gArity (undefined :: f p) + gArity (undefined :: g p)

instance GArity f => GArity (M1 S s f) where
  gArity _ = gArity (undefined :: f p)

class GCtorSelectors f where
  gCtorSelectors :: f p -> [(String, [String])]

instance GCtorSelectors V1 where
  gCtorSelectors _ = []

instance (GCtorSelectors f, GCtorSelectors g) => GCtorSelectors (f :+: g) where
  gCtorSelectors _ =
    gCtorSelectors (undefined :: f p) ++ gCtorSelectors (undefined :: g p)

instance GCtorSelectors f => GCtorSelectors (M1 D d f) where
  gCtorSelectors _ = gCtorSelectors (undefined :: f p)

instance (Constructor c, GSelectors f) => GCtorSelectors (M1 C c f) where
  gCtorSelectors x = [(conName x, gSelectors (undefined :: f p))]

class GSelectors f where
  gSelectors :: f p -> [String]

instance GSelectors U1 where
  gSelectors _ = []

instance Selector s => GSelectors (M1 S s (K1 i c)) where
  gSelectors x = [selName x]

instance (GSelectors f, GSelectors g) => GSelectors (f :*: g) where
  gSelectors _ = gSelectors (undefined :: f p) ++ gSelectors (undefined :: g p)

ctorsOf :: forall a. (Generic a, GCtors (Rep a)) => [(String, Int)]
ctorsOf = gCtors (undefined :: Rep a p)

selectorsOf ::
  forall a. (Generic a, GCtorSelectors (Rep a)) => [(String, [String])]
selectorsOf = gCtorSelectors (undefined :: Rep a p)

-- | How a row's real shape is recovered.
data Shape
  = -- | closed sum: the real count is the constructor count
    SumOf [(String, Int)]
  | -- | single-constructor positional record or newtype
    RecordOf [(String, Int)]
  | -- | named record: arity plus normalized selector sequence
    NamedRecordOf String [(String, Int)] [(String, [String])]
  | -- | one positional constructor of a sum
    CtorOf String [(String, Int)]
  | -- | one named constructor of a sum
    NamedCtorOf String String [(String, Int)] [(String, [String])]
  | -- | normalized alias row, anchored by an exact type-equality witness
    AliasOf Int

namedRecordOf ::
  forall a.
  (Generic a, GCtors (Rep a), GCtorSelectors (Rep a)) =>
  String -> Shape
namedRecordOf prefix =
  NamedRecordOf prefix (ctorsOf @a) (selectorsOf @a)

namedCtorOf ::
  forall a.
  (Generic a, GCtors (Rep a), GCtorSelectors (Rep a)) =>
  String -> String -> Shape
namedCtorOf ctor prefix =
  NamedCtorOf ctor prefix (ctorsOf @a) (selectorsOf @a)

realShape :: Shape -> Either String Int
realShape (SumOf cs) = Right (length cs)
realShape (RecordOf cs) = oneCtorArity cs
realShape (NamedRecordOf _ cs _) = oneCtorArity cs
realShape (CtorOf c cs) = ctorArity c cs
realShape (NamedCtorOf c _ cs _) = ctorArity c cs
realShape (AliasOf n) = Right n

oneCtorArity :: [(String, Int)] -> Either String Int
oneCtorArity cs = case cs of
  [(_, n)] -> Right n
  _ -> Left ("expected exactly one constructor, found " ++ show (length cs))

ctorArity :: String -> [(String, Int)] -> Either String Int
ctorArity c cs = case lookup c cs of
  Just n -> Right n
  Nothing -> Left ("no constructor named " ++ c)

realLabels :: Shape -> Either String (Maybe [String])
realLabels (NamedRecordOf prefix _ css) = Just <$> namedRecordLabels prefix css
realLabels (NamedCtorOf ctor prefix _ css) =
  Just <$> namedCtorLabels ctor prefix css
realLabels _ = Right Nothing

namedRecordLabels :: String -> [(String, [String])] -> Either String [String]
namedRecordLabels prefix css = case css of
  [(_, sels)] -> normalizeSelectors prefix sels
  _ -> Left ("expected exactly one constructor, found " ++ show (length css))

namedCtorLabels ::
  String -> String -> [(String, [String])] -> Either String [String]
namedCtorLabels ctor prefix css = case lookup ctor css of
  Just sels -> normalizeSelectors prefix sels
  Nothing -> Left ("no constructor named " ++ ctor)

normalizeSelectors :: String -> [String] -> Either String [String]
normalizeSelectors prefix = traverse normalize
  where
    normalize selector
      | null selector = Left "expected named record selectors, found a positional field"
      | otherwise = case stripPrefix prefix selector of
          Nothing ->
            Left
              ( "selector " ++ selector ++ " does not start with expected prefix "
                  ++ prefix
              )
          Just field -> Right (semanticField prefix field)

-- The models intentionally use different source identifiers for a few semantic
-- fields. Keep each spelling normalization scoped to its owning record prefix;
-- every other named selector is prefix-stripped and camel-to-kebab converted
-- mechanically.
semanticField :: String -> String -> String
semanticField "arg" "Concl" = "conclusion"
semanticField "value" "Name" = "name"
semanticField "value" "Term" = "term"
semanticField "program" "ValueBindings" = "value-bindings"
semanticField _ field = camelToKebab field
camelToKebab :: String -> String
camelToKebab [] = []
camelToKebab (c : cs) = toLower c : concatMap step cs
  where
    step ch
      | isUpper ch = ['-', toLower ch]
      | otherwise = [ch]

deriving instance Generic PropId
deriving instance Generic QuestionId
deriving instance Generic LeafId
deriving instance Generic RuleId
deriving instance Generic ArgId
deriving instance Generic ObligationId
deriving instance Generic BackendId
deriving instance Generic PolicyId
deriving instance Generic Param
deriving instance Generic SourceRef
deriving instance Generic TheoryDigest
deriving instance Generic Digest
deriving instance Generic GroupId
deriving instance Generic MeasurandId
deriving instance Generic DatasetId
deriving instance Generic PremiseLabel
deriving instance Generic ValueName
deriving instance Generic FunSym
deriving instance Generic Pred
deriving instance Generic P.Term
deriving instance Generic P.Prop
deriving instance Generic LeafKind
deriving instance Generic Provenance
deriving instance Generic AuditStatus
deriving instance Generic Mode
deriving instance Generic Necessity
deriving instance Generic Admission
deriving instance Generic GroupConflictMode
deriving instance Generic Polarity
deriving instance Generic Relation
deriving instance Generic Sort
deriving instance Generic Pat
deriving instance Generic Assurance
deriving instance Generic SupportTerm
deriving instance Generic Step
deriving instance Generic Attack
deriving instance Generic SurfaceStep
deriving instance Generic SurfaceAttack
deriving instance Generic ChallengeTarget
deriving instance Generic ArgRef
deriving instance Generic ArgInstantiation
deriving instance Generic ArgConcl
deriving instance Generic Decl
deriving instance Generic AtomPat
deriving instance Generic Leaf
deriving instance Generic Binding
deriving instance Generic Claim
deriving instance Generic Question
deriving instance Generic CertRef
deriving instance Generic Rule
deriving instance Generic Contrary
deriving instance Generic Exception
deriving instance Generic DupGroup
deriving instance Generic ConSig
deriving instance Generic PredSig
deriving instance Generic Sigma
deriving instance Generic Measurand
deriving instance Generic ComparisonScheme
deriving instance Generic Policy
deriving instance Generic Cert
deriving instance Generic Arg
deriving instance Generic ComparisonClaim
deriving instance Generic Comparison
deriving instance Generic ValueBinding
deriving instance Generic Program

-- | One entry per 'shapeRows' entry, same order and same row name.
--
-- The anonymous association-list entries are anchored through the exact
-- 'Policy', 'Program', and 'SRule' constructor signatures, and their tuple
-- arities come from the tuples' own 'Generic' instances. 'Subst' and 'Position'
-- have no distinct runtime representation, so exact identity witnesses above
-- pin their expansions while 'AliasOf' records the normalized one-part row.
shapeChecks :: [(String, Shape)]
shapeChecks =
  [ ("PropId", RecordOf (ctorsOf @PropId))
  , ("QuestionId", RecordOf (ctorsOf @QuestionId))
  , ("LeafId", RecordOf (ctorsOf @LeafId))
  , ("RuleId", RecordOf (ctorsOf @RuleId))
  , ("ArgId", RecordOf (ctorsOf @ArgId))
  , ("ObligationId", RecordOf (ctorsOf @ObligationId))
  , ("BackendId", RecordOf (ctorsOf @BackendId))
  , ("PolicyId", RecordOf (ctorsOf @PolicyId))
  , ("Param", RecordOf (ctorsOf @Param))
  , ("SourceRef", RecordOf (ctorsOf @SourceRef))
  , ("TheoryDigest", RecordOf (ctorsOf @TheoryDigest))
  , ("Digest", RecordOf (ctorsOf @Digest))
  , ("GroupId", RecordOf (ctorsOf @GroupId))
  , ("MeasurandId", RecordOf (ctorsOf @MeasurandId))
  , ("DatasetId", RecordOf (ctorsOf @DatasetId))
  , ("PremiseLabel", RecordOf (ctorsOf @PremiseLabel))
  , ("ValueName", RecordOf (ctorsOf @ValueName))
  , ("FunSym", RecordOf (ctorsOf @FunSym))
  , ("Pred", RecordOf (ctorsOf @Pred))
  , ("Term", SumOf (ctorsOf @P.Term))
  , ("Prop", RecordOf (ctorsOf @P.Prop))
  , ("LeafKind", SumOf (ctorsOf @LeafKind))
  , ("Provenance", SumOf (ctorsOf @Provenance))
  , ("AuditStatus", SumOf (ctorsOf @AuditStatus))
  , ("Mode", SumOf (ctorsOf @Mode))
  , ("Necessity", SumOf (ctorsOf @Necessity))
  , ("Admission", SumOf (ctorsOf @Admission))
  , ("GroupConflictMode", SumOf (ctorsOf @GroupConflictMode))
  , ("Polarity", SumOf (ctorsOf @Polarity))
  , ("Relation", SumOf (ctorsOf @Relation))
  , ("Sort", SumOf (ctorsOf @Sort))
  , ("Pat", SumOf (ctorsOf @Pat))
  , ("Assurance", SumOf (ctorsOf @Assurance))
  , ("SupportTerm", SumOf (ctorsOf @SupportTerm))
  , ("Step", SumOf (ctorsOf @Step))
  , ("Attack", SumOf (ctorsOf @Attack))
  , ("SurfaceStep", SumOf (ctorsOf @SurfaceStep))
  , ("SurfaceAttack", SumOf (ctorsOf @SurfaceAttack))
  , ("ChallengeTarget", SumOf (ctorsOf @ChallengeTarget))
  , ("ArgConcl", SumOf (ctorsOf @ArgConcl))
  , ("Decl", SumOf (ctorsOf @Decl))
  , ("AtomPat", RecordOf (ctorsOf @AtomPat))
  , ("Leaf", namedRecordOf @Leaf "leaf")
  , ("Binding", namedRecordOf @Binding "binding")
  , ("Claim", namedRecordOf @Claim "claim")
  , ("Question", namedRecordOf @Question "question")
  , ("CertRef", namedRecordOf @CertRef "certRef")
  , ("Rule", namedRecordOf @Rule "rule")
  , ("Contrary", RecordOf (ctorsOf @Contrary))
  , ("Exception", namedRecordOf @Exception "exception")
  , ("DupGroup", namedRecordOf @DupGroup "dg")
  , ("ConSig", namedRecordOf @ConSig "con")
  , ("PredSig", namedRecordOf @PredSig "pred")
  , ("Sigma", namedRecordOf @Sigma "sigma")
  , ("Measurand", namedRecordOf @Measurand "measurand")
  , ("ComparisonScheme", namedRecordOf @ComparisonScheme "cs")
  , ("Policy", namedRecordOf @Policy "policy")
  , ("Cert", namedRecordOf @Cert "cert")
  , ("SRule", namedCtorOf @SupportTerm "SRule" "sr")
  , ("ArgRef", RecordOf (ctorsOf @ArgRef))
  , ("ArgDischarge", AliasOf 1)
  , ("ArgInstantiation", SumOf (ctorsOf @ArgInstantiation))
  , ("Arg", namedRecordOf @Arg "arg")
  , ("ComparisonClaim", namedRecordOf @ComparisonClaim "cc")
  , ("Comparison", namedRecordOf @Comparison "cmp")
  , ("ValueBinding", namedRecordOf @ValueBinding "value")
  , ("Program", namedRecordOf @Program "program")
  , ("AdmissionEntry", RecordOf (ctorsOf @ExpectedAdmissionEntry))
  , ("TheoryEntry", RecordOf (ctorsOf @ExpectedTheoryEntry))
  , ("BackendEntry", RecordOf (ctorsOf @ExpectedBackendEntry))
  , ("Subst", AliasOf 1)
  , ("DischargeEntry", RecordOf (ctorsOf @ExpectedDischargeEntry))
  , ("Position", AliasOf 1)
  , ("M5.Rule", namedRecordOf @Rule "rule")
  , ("M5.InferTheta", CtorOf "InferTheta" (ctorsOf @ArgInstantiation))
  , ("M5.Comparison", namedRecordOf @Comparison "cmp")
  , ("M5.ValueBinding", namedRecordOf @ValueBinding "value")
  , ("M5.Cert", namedRecordOf @Cert "cert")
  ]

-- | Refuse to print unless every row's part count equals the real shape of the
-- type it names. Exits nonzero naming the offending row.
checkShape :: IO ()
checkShape = do
  unless (length shapeRows == length shapeChecks) $
    bail
      ( "inventory has " ++ show (length shapeRows) ++ " rows but the tripwire has "
          ++ show (length shapeChecks)
      )
  mapM_ one (zip shapeRows shapeChecks)
  where
    one ((rowName, parts), (checkName, shape))
      | rowName /= checkName =
          bail (rowName ++ ": tripwire row order disagrees (found " ++ checkName ++ ")")
      | otherwise = case realShape shape of
          Left err -> bail (rowName ++ ": " ++ err)
          Right real
            | real /= length parts ->
                bail
                  ( rowName ++ ": inventory lists " ++ show (length parts)
                      ++ " parts but the type has " ++ show real
                      ++ " (update this row in BOTH inventories)"
                  )
            | otherwise -> case realLabels shape of
                Left err -> bail (rowName ++ ": " ++ err)
                Right Nothing -> pure ()
                Right (Just labels)
                  | labels == parts -> pure ()
                  | otherwise ->
                      bail
                        ( rowName ++ ": inventory labels " ++ show parts
                            ++ " disagree with normalized selectors " ++ show labels
                        )

    bail :: String -> IO ()
    bail msg = do
      hPutStrLn stderr ("presentation parity: shape tripwire: " ++ msg)
      exitFailure

main :: IO ()
main = do
  -- The witness sink exists only to keep -Wunused-top-binds quiet while every
  -- witness above stays load-bearing; forcing it here is what makes it "used".
  witnesses `seq` pure ()
  checkShape
  putStr (unlines (map renderRow shapeRows))
