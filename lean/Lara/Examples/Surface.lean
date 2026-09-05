import Lara.Surface.Syntax
import Lara.Surface.ValueBinding
import Lara.Surface.Comparison
import Lara.Surface.Check
import Lara.Surface.Correctness
import Lara.Surface.Observation
import Lara.Driver

set_option maxHeartbeats 4000000

namespace Lara.Examples.Surface

open Lara
open Lara.Presentation

private def terms (items : List Term) : Terms :=
  items.foldr .cons .nil

private def pats (items : List Pat) : Pats :=
  items.foldr .cons .nil

private def atom (pred : String) (items : List Term) : Atom :=
  .atom pred (terms items)

private def atomPat (pred : String) (items : List Pat) : AtomPat :=
  ⟨pred, pats items⟩

private def con0 (name : String) : Term := .con name .nil

private def policyId : PolicyId := ⟨"surface-policy"⟩
private def ruleMainId : RuleId := ⟨"main"⟩
private def ruleNestedId : RuleId := ⟨"nested"⟩
private def recheckRuleId : RuleId := ⟨"ord-recheck"⟩
private def bridgeRuleId : RuleId := ⟨"comparison-bridge"⟩
private def questionId : QuestionId := ⟨"cq"⟩
private def evidenceLabel : PremiseLabel := ⟨"evidence"⟩
private def innerLabel : PremiseLabel := ⟨"inner"⟩

private def x : Param := ⟨"X"⟩
private def y : Param := ⟨"Y"⟩
private def systemParam : Param := ⟨"S"⟩
private def baselineParam : Param := ⟨"B"⟩
private def measurandParam : Param := ⟨"Q"⟩
private def datasetParam : Param := ⟨"D"⟩
private def resultValueParam : Param := ⟨"RV"⟩
private def recheckSystemParam : Param := ⟨"RS"⟩
private def recheckBaselineParam : Param := ⟨"RB"⟩
private def recheckMeasurandParam : Param := ⟨"RQ"⟩
private def recheckDatasetParam : Param := ⟨"RD"⟩
private def recheckResultValueParam : Param := ⟨"RRV"⟩
private def recheckBaselineValueParam : Param := ⟨"RBV"⟩
private def baselineValueParam : Param := ⟨"BV"⟩

private def resultLeaf : LeafId := ⟨"e"⟩
private def baselineLeaf : LeafId := ⟨"baseline"⟩
private def bindingLeaf : LeafId := ⟨"binding"⟩
private def proofLeaf : LeafId := ⟨"proof"⟩
private def claimMain : PropId := ⟨"claim-main"⟩
private def claimComparison : PropId := ⟨"claim-comparison"⟩
private def argExplicit : ArgId := ⟨"arg-explicit"⟩
private def argInferred : ArgId := ⟨"arg-inferred"⟩

private def systemA : Term := con0 "system-a"
private def systemB : Term := con0 "system-b"
private def quality : Term := con0 "quality"
private def dataset : Term := con0 "dataset"

private def binding : Binding := ⟨"author", "surface witness", .reviewed⟩

private def entity : TermSort := .decl "Entity"

private def surfaceSigma : Sigma :=
  { sorts := ["Entity"]
    cons :=
      [ ⟨⟨"system-a"⟩, [], entity⟩
      , ⟨⟨"system-b"⟩, [], entity⟩
      , ⟨⟨"quality"⟩, [], entity⟩
      , ⟨⟨"dataset"⟩, [], entity⟩
      ]
    preds :=
      [ ⟨⟨"score"⟩, [.num]⟩
      , ⟨⟨"reported"⟩, [entity, entity, entity, .num]⟩
      , ⟨⟨"binding"⟩, [entity, entity, entity, entity, .num, .num]⟩
      , ⟨⟨"num_lt"⟩, [.num, .num]⟩
      , ⟨⟨"better"⟩, [entity, entity, entity, entity]⟩
      , ⟨⟨"verdict"⟩, [.num]⟩
      , ⟨⟨"flag"⟩, []⟩
      ] }

private def mainRule : Rule :=
  { id := ruleMainId
    params := [x]
    mode := .defeasible
    premises := [atomPat "score" [.var x]]
    premiseLabels := [some evidenceLabel]
    conclusion := atomPat "score" [.var x]
    allowTrusted := true
    certifiers := [⟨⟨"nd"⟩, 1, ⟨"theory"⟩⟩]
    questions := [⟨questionId, atomPat "score" [.var x], .optional⟩] }

private def nestedRule : Rule :=
  { id := ruleNestedId
    params := [y]
    mode := .strict
    premises := [atomPat "score" [.var y]]
    premiseLabels := [some innerLabel]
    conclusion := atomPat "score" [.var y]
    allowTrusted := true
    certifiers := [⟨⟨"nd"⟩, 1, ⟨"theory"⟩⟩]
    questions := [] }

private def verdictRuleId : RuleId := ⟨"verdict-rule"⟩

/-- A defeasible rule over the `verdict` family: the attack fixtures' source
and target cite it, and the contrary pair `verdict(1)`/`verdict(0)` stays
clear of every strict conclusion. -/
private def verdictRule : Rule :=
  { id := verdictRuleId
    params := [y]
    mode := .defeasible
    premises := [atomPat "verdict" [.var y]]
    premiseLabels := []
    conclusion := atomPat "verdict" [.var y]
    allowTrusted := false
    certifiers := []
    questions := [] }

private def recheckRule : Rule :=
  { id := recheckRuleId
    params := [recheckSystemParam, recheckBaselineParam,
      recheckMeasurandParam, recheckDatasetParam,
      recheckResultValueParam, recheckBaselineValueParam]
    mode := .strict
    premises :=
      [ atomPat "reported" [.var recheckSystemParam, .var recheckMeasurandParam,
          .var recheckDatasetParam, .var recheckResultValueParam]
      , atomPat "reported" [.var recheckBaselineParam, .var recheckMeasurandParam,
          .var recheckDatasetParam, .var recheckBaselineValueParam]
      ]
    premiseLabels := []
    conclusion := atomPat "num_lt"
      [.var recheckBaselineValueParam, .var recheckResultValueParam]
    allowTrusted := false
    certifiers := [⟨⟨"ord"⟩, 1, ⟨"theory"⟩⟩]
    questions := [] }

private def bridgeRule : Rule :=
  { id := bridgeRuleId
    params := [systemParam, baselineParam, measurandParam, datasetParam,
      resultValueParam, baselineValueParam]
    mode := .defeasible
    premises :=
      [ atomPat "binding" [.var systemParam, .var baselineParam,
          .var measurandParam, .var datasetParam, .var resultValueParam,
          .var baselineValueParam]
      , atomPat "num_lt" [.var baselineValueParam, .var resultValueParam]
      ]
    premiseLabels := []
    conclusion := atomPat "better" [.var systemParam, .var baselineParam,
      .var measurandParam, .var datasetParam]
    allowTrusted := false
    certifiers := []
    questions := [] }

private def allFormsPolicy : Policy :=
  { id := policyId
    sigma := surfaceSigma
    rules := [mainRule, nestedRule, verdictRule, recheckRule, bridgeRule]
    contraries := [⟨atomPat "verdict" [.lit (.num "1")], atomPat "verdict" [.lit (.num "0")]⟩]
    exceptions := [⟨ruleMainId, atomPat "verdict" [.lit (.num "1")]⟩]
    admission := [((.observed, .user), .admit)]
    theories := [(⟨"theory"⟩, [atom "score" [.num "1"]])]
    groupMode := .quarantineOnConflict
    measurands := [⟨⟨"quality"⟩, .num, some .higherIsBetter⟩]
    comparisonSchemes :=
      [⟨.strictlyBetter, .higherIsBetter, recheckRuleId, bridgeRuleId⟩] }

/-- The named `nd@1` payload: a named lambda whose body applies the bound
hypothesis to the labelled premise `inner` — `(app (lam h (prop "score(7)")
(hyp h)) (prem "inner"))` — lowering to the kernel derivation of `score(7)`
from the premise slot. -/
private def namedCertificatePayload : Sx :=
  .node "app"
    (.cons (.node "lam" (.cons (.str "h")
      (.cons (.node "prop" (.cons (.str "score(7)") .nil))
        (.cons (.node "hyp" (.cons (.str "h") .nil)) .nil))))
      (.cons (.node "prem" (.cons (.str "inner") .nil)) .nil))

private def namedCertificate : Assurance :=
  .cert ⟨⟨"nd"⟩, 1, ⟨"theory"⟩, namedCertificatePayload⟩

private def nestedTerm : SupportTerm :=
  .rule ruleNestedId [(y, .num "7")]
    (.cons (.leaf proofLeaf) .nil) .nil [] namedCertificate

private def explicitTerm : SupportTerm :=
  .rule ruleMainId [(x, con0 "threshold")]
    (.cons nestedTerm .nil)
    (.cons questionId (.leaf proofLeaf) .nil)
    [] .none

private def explicitArgument : Arg :=
  ⟨argExplicit, .supportsClaim claimMain, .explicitTheta explicitTerm⟩

private def inferredArgument : Arg :=
  ⟨argInferred, .supportsDerived claimComparison,
    .inferTheta ruleMainId [⟨"proof"⟩]
      [(questionId, ⟨"arg-explicit"⟩)] [] .none⟩

private def verdictProLeaf : LeafId := ⟨"verdict-pro"⟩
private def verdictConLeaf : LeafId := ⟨"verdict-con"⟩
private def argPro : ArgId := ⟨"arg-pro"⟩
private def argCon : ArgId := ⟨"arg-con"⟩

private def verdictProTerm : SupportTerm :=
  .rule verdictRuleId [(y, .num "1")]
    (.cons (.leaf verdictProLeaf) .nil) .nil [] .none

private def verdictConTerm : SupportTerm :=
  .rule verdictRuleId [(y, .num "0")]
    (.cons (.leaf verdictConLeaf) .nil) .nil [] .none

private def proArgument : Arg :=
  ⟨argPro, .challenges (.question questionId argInferred),
    .explicitTheta verdictProTerm⟩

private def conArgument : Arg :=
  ⟨argCon, .challenges (.leaf verdictConLeaf), .explicitTheta verdictConTerm⟩

private def substitutedExplicitTerm : SupportTerm :=
  .rule ruleMainId [(x, .num "7")] (.cons nestedTerm .nil)
    (.cons questionId (.leaf proofLeaf) .nil) [] .none

private def substitutedExplicitArgument : Arg :=
  ⟨argExplicit, .supportsClaim claimMain, .explicitTheta substitutedExplicitTerm⟩

private def comparison : Comparison :=
  { conclusion := atom "better" [systemA, systemB]
    measurand := ⟨"quality"⟩
    dataset := ⟨"dataset"⟩
    relation := .strictlyBetter
    recheckArg := ⟨"comparison-recheck"⟩
    bridgeArg := ⟨"comparison-bridge-arg"⟩
    result := resultLeaf
    baseline := baselineLeaf
    binding := bindingLeaf
    claim := ⟨claimComparison, "comparison {threshold}", binding⟩
    supports := none }

private def allFormsProgram : Program :=
  { artifact := "surface-all-forms"
    digest := ⟨"sha256:surface"⟩
    policy := policyId
    backends := [(⟨"nd"⟩, "1"), (⟨"ord"⟩, "1")]
    valueBindings := [⟨⟨"threshold"⟩, .num "7"⟩]
    decls :=
      [ .leaf ⟨resultLeaf, atom "reported" [systemA, quality, dataset, .num "7"],
          .observed, .user, [⟨"source:e"⟩]⟩
      , .leaf ⟨baselineLeaf, atom "reported" [systemB, quality, dataset, .num "5"],
          .attested, .aiExecuted, []⟩
      , .leaf ⟨bindingLeaf,
          atom "binding" [systemA, systemB, quality, dataset, .num "7", .num "5"],
          .assumed, .checker "checker" "1", []⟩
      , .leaf ⟨proofLeaf, atom "score" [.num "7"], .certified, .user, []⟩
      , .leaf ⟨verdictProLeaf, atom "verdict" [.num "1"], .observed, .user, []⟩
      , .leaf ⟨verdictConLeaf, atom "verdict" [.num "0"], .observed, .user, []⟩
      , .claim ⟨claimMain, "threshold {threshold}; observed {cell e}",
          atom "score" [con0 "threshold"], binding⟩
      , .arg explicitArgument
      , .arg inferredArgument
      , .arg proArgument
      , .arg conArgument
      , .attack (.rebut argPro argCon)
      , .attack (.undercut argPro argInferred [.name "cq"])
      , .attack (.undermine argPro argCon [.index 0])
      , .status claimMain
      , .group ⟨⟨"reported-quality"⟩, [resultLeaf, baselineLeaf]⟩
      , .comparison comparison
      ] }

def allFormsInput : Lara.Surface.Input := ⟨allFormsProgram, allFormsPolicy⟩

theorem allForms_supported : Lara.Surface.Supported allFormsInput := by
  apply (Lara.Surface.supportedB_iff allFormsInput).mp
  decide

/-! Required boundary witnesses. -/

def duplicateArgumentInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with decls := allFormsProgram.decls ++ [.arg explicitArgument] },
    allFormsPolicy⟩


theorem renamedComparisonParameters_supported :
    Lara.Surface.comparisonsWellFormedB allFormsProgram allFormsPolicy = true := by
  decide

private def literalRecheckRule : Rule :=
  { recheckRule with
    id := ⟨"literal-recheck"⟩
    params := [systemParam, baselineParam, recheckMeasurandParam,
      recheckDatasetParam, recheckResultValueParam, recheckBaselineValueParam]
    premises :=
      [ atomPat "reported" [.var systemParam, .var recheckMeasurandParam,
          .var recheckDatasetParam, .var recheckResultValueParam]
      , atomPat "reported" [.var baselineParam, .var recheckMeasurandParam,
          .var recheckDatasetParam, .var recheckBaselineValueParam]
      ]
    conclusion := atomPat "num_lt" [.lit (.num "5"), .lit (.num "7")] }

private def literalFallbackPolicy : Policy :=
  { allFormsPolicy with
    rules := [mainRule, nestedRule, literalRecheckRule, bridgeRule]
    comparisonSchemes :=
      [⟨.strictlyBetter, .higherIsBetter, ⟨"literal-recheck"⟩, bridgeRuleId⟩] }

theorem literalGoalFallback_supported :
    Lara.Surface.comparisonsWellFormedB allFormsProgram literalFallbackPolicy = true := by
  decide

private def normalizedRoleDecl : Decl → Decl
  | .leaf leaf =>
      if leaf.id = resultLeaf then
        .leaf { leaf with
          prop := atom "reported" [.num "1", quality, dataset, con0 "result-value"] }
      else if leaf.id = baselineLeaf then
        .leaf { leaf with
          prop := atom "reported" [.num "2", quality, dataset, con0 "baseline-value"] }
      else if leaf.id = bindingLeaf then
        .leaf { leaf with
          prop := atom "binding"
            [.num "1", .num "2", quality, dataset, .num "1", .num "2"] }
      else .leaf leaf
  | .comparison comparison =>
      .comparison { comparison with conclusion := atom "better" [.num "01", .num "02"] }
  | declaration => declaration

private def normalizedRoleProgram : Program :=
  { allFormsProgram with decls := allFormsProgram.decls.map normalizedRoleDecl }

private def normalizedRoleRecheckRule : Rule :=
  { literalRecheckRule with
    id := ⟨"normalized-role-recheck"⟩
    conclusion := atomPat "num_lt" [.lit (.num "2"), .lit (.num "1")] }

private def normalizedRolePolicy : Policy :=
  { allFormsPolicy with
    rules := [mainRule, nestedRule, normalizedRoleRecheckRule, bridgeRule]
    comparisonSchemes :=
      [⟨.strictlyBetter, .higherIsBetter, ⟨"normalized-role-recheck"⟩, bridgeRuleId⟩] }

theorem normalizedComparisonRoles_supported :
    Lara.Surface.comparisonsWellFormedB normalizedRoleProgram normalizedRolePolicy = true := by
  decide

private def resultCellSpellingDecl (spelling : String) : Decl → Decl
  | .leaf leaf =>
      if leaf.id = resultLeaf then
        .leaf { leaf with
          prop := atom "reported" [systemA, quality, dataset, .num spelling] }
      else if leaf.id = bindingLeaf then
        .leaf { leaf with
          prop := atom "binding"
            [systemA, systemB, quality, dataset, .num spelling, .num "5"] }
      else .leaf leaf
  | declaration => declaration

private def plusSevenResultProgram : Program :=
  { allFormsProgram with
    decls := allFormsProgram.decls.map (resultCellSpellingDecl "+7") }

theorem normalizedCellCanonicalLiteral_supported :
    Lara.Surface.comparisonsWellFormedB plusSevenResultProgram literalFallbackPolicy = true := by
  decide

private def noncanonicalLiteralRecheckRule : Rule :=
  { literalRecheckRule with
    id := ⟨"noncanonical-literal-recheck"⟩
    conclusion := atomPat "num_lt" [.lit (.num "5"), .lit (.num "+7")] }

private def noncanonicalLiteralPolicy : Policy :=
  { allFormsPolicy with
    rules := [mainRule, nestedRule, noncanonicalLiteralRecheckRule, bridgeRule]
    comparisonSchemes :=
      [⟨.strictlyBetter, .higherIsBetter,
        ⟨"noncanonical-literal-recheck"⟩, bridgeRuleId⟩] }

theorem rawMatchingNoncanonicalLiteral_unsupported :
    Lara.Surface.comparisonsWellFormedB plusSevenResultProgram
      noncanonicalLiteralPolicy = false := by
  decide

private def tieValueDecl : Decl → Decl
  | .leaf leaf =>
      if leaf.id = baselineLeaf then
        .leaf { leaf with
          prop := atom "reported" [systemB, quality, dataset, .num "7"] }
      else if leaf.id = bindingLeaf then
        .leaf { leaf with
          prop := atom "binding"
            [systemA, systemB, quality, dataset, .num "7", .num "7"] }
      else .leaf leaf
  | declaration => declaration

private def tieValueProgram : Program :=
  { allFormsProgram with decls := allFormsProgram.decls.map tieValueDecl }

theorem equalCellVariableProvenance_supported :
    Lara.Surface.comparisonsWellFormedB tieValueProgram allFormsPolicy = true := by
  decide

private def reversedVariableRecheckRule : Rule :=
  { recheckRule with
    id := ⟨"reversed-variable-recheck"⟩
    conclusion := atomPat "num_lt"
      [.var recheckResultValueParam, .var recheckBaselineValueParam] }

private def reversedVariableBridgeRule : Rule :=
  { bridgeRule with
    id := ⟨"reversed-variable-bridge"⟩
    premises :=
      [ atomPat "binding" [.var systemParam, .var baselineParam,
          .var measurandParam, .var datasetParam, .var resultValueParam,
          .var baselineValueParam]
      , atomPat "num_lt" [.var resultValueParam, .var baselineValueParam]
      ] }

private def reversedVariablePolicy : Policy :=
  { allFormsPolicy with
    rules :=
      [mainRule, nestedRule, reversedVariableRecheckRule, reversedVariableBridgeRule]
    comparisonSchemes :=
      [⟨.strictlyBetter, .higherIsBetter,
        ⟨"reversed-variable-recheck"⟩, ⟨"reversed-variable-bridge"⟩⟩] }

theorem equalCellReversedVariable_unsupported :
    Lara.Surface.comparisonsWellFormedB tieValueProgram reversedVariablePolicy = false := by
  decide
theorem duplicateArgument_unsupported :
    Lara.Surface.supportedB duplicateArgumentInput = false := by decide

private def collidingRule : Rule :=
  { nestedRule with
    id := ⟨"colliding-rule"⟩
    premiseLabels := [some ⟨"same-slot"⟩]
    questions := [⟨⟨"same-slot"⟩, atomPat "score" [.var y], .optional⟩] }

def premiseQuestionCollisionInput : Lara.Surface.Input :=
  ⟨allFormsProgram,
    { allFormsPolicy with rules := allFormsPolicy.rules ++ [collidingRule] }⟩

theorem premiseQuestionCollision_unsupported :
    Lara.Surface.supportedB premiseQuestionCollisionInput = false := by decide

private def withUnknownInterpolation : Decl → Decl
  | .claim claim => .claim { claim with nl := "unknown {missing-value}" }
  | declaration => declaration

def unknownValueInterpolationInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with decls := allFormsProgram.decls.map withUnknownInterpolation },
    allFormsPolicy⟩

theorem unknownValueInterpolation_unsupported :
    Lara.Surface.supportedB unknownValueInterpolationInput = false := by decide

private def withoutMatchingScheme : Decl → Decl
  | .comparison comparison => .comparison { comparison with relation := .atLeastAsGood }
  | declaration => declaration

def missingComparisonSchemeInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with decls := allFormsProgram.decls.map withoutMatchingScheme },
    allFormsPolicy⟩

theorem missingComparisonScheme_unsupported :
    Lara.Surface.supportedB missingComparisonSchemeInput = false := by decide

private def earlyArgument : Arg :=
  ⟨⟨"arg-early"⟩, .supportsClaim claimMain,
    .inferTheta ruleMainId [⟨"arg-later"⟩] [] [] .trusted⟩

private def laterArgument : Arg :=
  ⟨⟨"arg-later"⟩, .supportsClaim claimMain, .explicitTheta (.leaf proofLeaf)⟩

def laterArgumentReferenceInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      decls := .arg earlyArgument :: allFormsProgram.decls ++ [.arg laterArgument] },
    allFormsPolicy⟩

theorem laterArgumentReference_unsupported :
    Lara.Surface.supportedB laterArgumentReferenceInput = false := by decide

private def twoPremiseRule : Rule :=
  { nestedRule with
    id := ⟨"two-premise"⟩
    params := [x]
    premises := [atomPat "score" [.var x], atomPat "score" [.var x]]
    premiseLabels := []
    conclusion := atomPat "score" [.var x] }

private def ambiguousCertificate : Assurance :=
  .cert ⟨⟨"nd"⟩, 1, ⟨"theory"⟩,
    .node "prem" (.cons (.str "proof") .nil)⟩

private def ambiguousCertificateArgument : Arg :=
  ⟨⟨"arg-ambiguous-certificate"⟩, .supportsClaim claimMain,
    .inferTheta ⟨"two-premise"⟩ [⟨"proof"⟩, ⟨"proof"⟩] [] [] ambiguousCertificate⟩

def ambiguousNamedCertificateInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      decls := allFormsProgram.decls ++ [.arg ambiguousCertificateArgument] },
    { allFormsPolicy with rules := allFormsPolicy.rules ++ [twoPremiseRule] }⟩

theorem ambiguousNamedCertificate_unsupported :
    Lara.Surface.supportedB ambiguousNamedCertificateInput = false := by
  decide

def unresolvedAttackPathInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with decls := allFormsProgram.decls ++
      [.attack (.undercut argInferred argExplicit [.name "no-such-slot"])] },
    allFormsPolicy⟩

theorem unresolvedAttackPath_unsupported :
    Lara.Surface.supportedB unresolvedAttackPathInput = false := by
  decide

theorem duplicateArgument_isolated :
    Lara.Surface.declarationIdsNodupB duplicateArgumentInput.program = false ∧
    Lara.Surface.ruleNamespacesWellFormedB duplicateArgumentInput.policy = true ∧
    Lara.Surface.valueBindingsWellFormedB duplicateArgumentInput = true ∧
    Lara.Surface.comparisonsWellFormedB duplicateArgumentInput.program duplicateArgumentInput.policy = true ∧
    Lara.Surface.inferredArgsWellFormedB duplicateArgumentInput.program duplicateArgumentInput.policy = true ∧
    Lara.Surface.namedCertificatesWellFormedB duplicateArgumentInput.program duplicateArgumentInput.policy = true ∧
    Lara.Surface.surfaceAttacksWellFormedB duplicateArgumentInput.program duplicateArgumentInput.policy = true ∧
    Lara.Surface.canonicalPremiseLabelsB duplicateArgumentInput.policy = true := by decide

theorem premiseQuestionCollision_isolated :
    Lara.Surface.declarationIdsNodupB premiseQuestionCollisionInput.program = true ∧
    Lara.Surface.ruleNamespacesWellFormedB premiseQuestionCollisionInput.policy = false ∧
    Lara.Surface.valueBindingsWellFormedB premiseQuestionCollisionInput = true ∧
    Lara.Surface.comparisonsWellFormedB premiseQuestionCollisionInput.program premiseQuestionCollisionInput.policy = true ∧
    Lara.Surface.inferredArgsWellFormedB premiseQuestionCollisionInput.program premiseQuestionCollisionInput.policy = true ∧
    Lara.Surface.namedCertificatesWellFormedB premiseQuestionCollisionInput.program premiseQuestionCollisionInput.policy = true ∧
    Lara.Surface.surfaceAttacksWellFormedB premiseQuestionCollisionInput.program premiseQuestionCollisionInput.policy = true ∧
    Lara.Surface.canonicalPremiseLabelsB premiseQuestionCollisionInput.policy = true := by decide

theorem unknownValueInterpolation_isolated :
    Lara.Surface.declarationIdsNodupB unknownValueInterpolationInput.program = true ∧
    Lara.Surface.ruleNamespacesWellFormedB unknownValueInterpolationInput.policy = true ∧
    Lara.Surface.valueBindingsWellFormedB unknownValueInterpolationInput = false ∧
    Lara.Surface.comparisonsWellFormedB unknownValueInterpolationInput.program unknownValueInterpolationInput.policy = true ∧
    Lara.Surface.inferredArgsWellFormedB unknownValueInterpolationInput.program unknownValueInterpolationInput.policy = true ∧
    Lara.Surface.namedCertificatesWellFormedB unknownValueInterpolationInput.program unknownValueInterpolationInput.policy = true ∧
    Lara.Surface.surfaceAttacksWellFormedB unknownValueInterpolationInput.program unknownValueInterpolationInput.policy = true ∧
    Lara.Surface.canonicalPremiseLabelsB unknownValueInterpolationInput.policy = true := by decide

theorem missingComparisonScheme_isolated :
    Lara.Surface.declarationIdsNodupB missingComparisonSchemeInput.program = true ∧
    Lara.Surface.ruleNamespacesWellFormedB missingComparisonSchemeInput.policy = true ∧
    Lara.Surface.valueBindingsWellFormedB missingComparisonSchemeInput = true ∧
    Lara.Surface.comparisonsWellFormedB missingComparisonSchemeInput.program missingComparisonSchemeInput.policy = false ∧
    Lara.Surface.inferredArgsWellFormedB missingComparisonSchemeInput.program missingComparisonSchemeInput.policy = true ∧
    Lara.Surface.namedCertificatesWellFormedB missingComparisonSchemeInput.program missingComparisonSchemeInput.policy = true ∧
    Lara.Surface.surfaceAttacksWellFormedB missingComparisonSchemeInput.program missingComparisonSchemeInput.policy = true ∧
    Lara.Surface.canonicalPremiseLabelsB missingComparisonSchemeInput.policy = true := by decide

theorem laterArgumentReference_isolated :
    Lara.Surface.declarationIdsNodupB laterArgumentReferenceInput.program = true ∧
    Lara.Surface.ruleNamespacesWellFormedB laterArgumentReferenceInput.policy = true ∧
    Lara.Surface.valueBindingsWellFormedB laterArgumentReferenceInput = true ∧
    Lara.Surface.comparisonsWellFormedB laterArgumentReferenceInput.program laterArgumentReferenceInput.policy = true ∧
    Lara.Surface.inferredArgsWellFormedB laterArgumentReferenceInput.program laterArgumentReferenceInput.policy = false ∧
    Lara.Surface.namedCertificatesWellFormedB laterArgumentReferenceInput.program laterArgumentReferenceInput.policy = true ∧
    Lara.Surface.surfaceAttacksWellFormedB laterArgumentReferenceInput.program laterArgumentReferenceInput.policy = true ∧
    Lara.Surface.canonicalPremiseLabelsB laterArgumentReferenceInput.policy = true := by decide

theorem ambiguousNamedCertificate_isolated :
    Lara.Surface.declarationIdsNodupB ambiguousNamedCertificateInput.program = true ∧
    Lara.Surface.ruleNamespacesWellFormedB ambiguousNamedCertificateInput.policy = true ∧
    Lara.Surface.valueBindingsWellFormedB ambiguousNamedCertificateInput = true ∧
    Lara.Surface.comparisonsWellFormedB ambiguousNamedCertificateInput.program ambiguousNamedCertificateInput.policy = true ∧
    Lara.Surface.inferredArgsWellFormedB ambiguousNamedCertificateInput.program ambiguousNamedCertificateInput.policy = true ∧
    Lara.Surface.namedCertificatesWellFormedB ambiguousNamedCertificateInput.program ambiguousNamedCertificateInput.policy = false ∧
    Lara.Surface.surfaceAttacksWellFormedB ambiguousNamedCertificateInput.program ambiguousNamedCertificateInput.policy = true ∧
    Lara.Surface.canonicalPremiseLabelsB ambiguousNamedCertificateInput.policy = true := by decide

theorem unresolvedAttackPath_isolated :
    Lara.Surface.declarationIdsNodupB unresolvedAttackPathInput.program = true ∧
    Lara.Surface.ruleNamespacesWellFormedB unresolvedAttackPathInput.policy = true ∧
    Lara.Surface.valueBindingsWellFormedB unresolvedAttackPathInput = true ∧
    Lara.Surface.comparisonsWellFormedB unresolvedAttackPathInput.program unresolvedAttackPathInput.policy = true ∧
    Lara.Surface.inferredArgsWellFormedB unresolvedAttackPathInput.program unresolvedAttackPathInput.policy = true ∧
    Lara.Surface.namedCertificatesWellFormedB unresolvedAttackPathInput.program unresolvedAttackPathInput.policy = true ∧
    Lara.Surface.surfaceAttacksWellFormedB unresolvedAttackPathInput.program unresolvedAttackPathInput.policy = false ∧
    Lara.Surface.canonicalPremiseLabelsB unresolvedAttackPathInput.policy = true := by decide

/-! Additional frozen-boundary witnesses required by the typed resolver. -/

private def shadowingArgument : Arg :=
  ⟨⟨"proof"⟩, .supportsClaim claimMain, .explicitTheta (.leaf proofLeaf)⟩

def ambiguousInferenceReferenceInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with decls := .arg shadowingArgument :: allFormsProgram.decls },
    allFormsPolicy⟩

theorem ambiguousInferenceReference_unsupported :
    Lara.Surface.inferredArgsWellFormedB ambiguousInferenceReferenceInput.program
      ambiguousInferenceReferenceInput.policy = false := by decide

private def withShapeMismatch : Decl → Decl
  | .arg argument =>
      if argument.id = argInferred then
        .arg { argument with instantiation :=
          (.inferTheta ruleMainId [⟨"e"⟩]
            [(questionId, ⟨"arg-explicit"⟩)] [] .trusted) }
      else .arg argument
  | declaration => declaration

def inferenceShapeMismatchInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with decls := allFormsProgram.decls.map withShapeMismatch },
    allFormsPolicy⟩

theorem inferenceShapeMismatch_unsupported :
    Lara.Surface.inferredArgsWellFormedB inferenceShapeMismatchInput.program
      inferenceShapeMismatchInput.policy = false := by decide

private def unboundRule : Rule :=
  { nestedRule with
    id := ⟨"unbound-rule"⟩
    params := [x, ⟨"Z"⟩]
    premises := [atomPat "score" [.var x]]
    conclusion := atomPat "score" [.var x] }

private def unboundArgument : Arg :=
  ⟨⟨"arg-unbound"⟩, .supportsClaim claimMain,
    .inferTheta ⟨"unbound-rule"⟩ [⟨"proof"⟩] [] [] .trusted⟩

def unboundInferenceParameterInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with decls := allFormsProgram.decls ++ [.arg unboundArgument] },
    { allFormsPolicy with rules := allFormsPolicy.rules ++ [unboundRule] }⟩

theorem unboundInferenceParameter_unsupported :
    Lara.Surface.inferredArgsWellFormedB unboundInferenceParameterInput.program
      unboundInferenceParameterInput.policy = false := by decide

private def nonCellClaim : Decl → Decl
  | .claim claim => .claim { claim with nl := "not a cell {cell not-cell}" }
  | declaration => declaration

def declaredNonCellInterpolationInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with decls :=
      (.leaf ⟨⟨"not-cell"⟩, atom "flag" [], .observed, .user, []⟩) ::
        allFormsProgram.decls.map nonCellClaim }, allFormsPolicy⟩

theorem declaredNonCellInterpolation_unsupported :
    Lara.Surface.valueBindingsWellFormedB declaredNonCellInterpolationInput = false := by decide

theorem authoredCellSpellings_normalize :
    Lara.Surface.cellObligationB (atom "score" [.num "+7"]) = true ∧
    Lara.Surface.cellObligationB (atom "score" [.num "01"]) = true ∧
    Lara.Surface.cellObligationB (atom "score" [.num "1.0"]) = true ∧
    Lara.Surface.cellObligationB (atom "score" [.num "-0"]) = true ∧
    Lara.Surface.cellObligationB (atom "score" [.num "0.05"]) = true := by
  decide

theorem sourceIdentifierClassifier_boundaries :
    Lara.Surface.sourceStartsIdentifier "." = false ∧
    Lara.Surface.sourceStartsIdentifier "_" = true ∧
    Lara.Surface.sourceStartsIdentifier "A" = true := by
  decide

theorem asciiNumericStartParity :
    Lara.Surface.propTextWellFormedB "score(1)" = true ∧
    Lara.Surface.propTextWellFormedB "score(١)" = false := by
  decide

theorem asciiIdentifierTailParity :
    Lara.Surface.propTextWellFormedB "score1(7)" = true ∧
    Lara.Surface.propTextWellFormedB "score١(7)" = false := by
  decide



def noBindingsIllSortedClaimInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      valueBindings := []
      decls := [.claim ⟨⟨"unchecked-without-bindings"⟩, "plain prose",
        atom "undeclared-predicate" [], binding⟩] },
    allFormsPolicy⟩

theorem noBindings_skips_claim_sort_validation :
    Lara.Surface.valueBindingsWellFormedB noBindingsIllSortedClaimInput = true := by
  decide

/-! Binding and renaming witnesses. -/

private def X : Param := ⟨"X-alpha"⟩
private def Y : Param := ⟨"Y-alpha"⟩
private def Z : Param := ⟨"Z-alpha"⟩

private def ruleX : Rule :=
  { mainRule with
    params := [X]
    premises := [atomPat "score" [.var X]]
    conclusion := atomPat "score" [.var X]
    questions := [] }

private def ruleY : Rule :=
  { mainRule with
    params := [Y]
    premises := [atomPat "score" [.var Y]]
    conclusion := atomPat "score" [.var Y]
    questions := [] }

example : Lara.Surface.Binding.RuleAlpha ruleX ruleY := by
  rfl

private def ruleXX : Rule :=
  { mainRule with
    params := [X, X]
    premises := [atomPat "score" [.lit (.num "1")]]
    conclusion := atomPat "score" [.lit (.num "1")]
    questions := [] }

private def ruleYZ : Rule :=
  { ruleXX with params := [Y, Z] }

example : ¬ Lara.Surface.Binding.RuleAlpha ruleXX ruleYZ := by
  intro alpha
  have aliases := congrArg Lara.Surface.Binding.RuleView.paramAliases alpha
  change [0, 0] = [0, 1] at aliases
  contradiction

private def namedLamX : Lara.NDNamed.NCert :=
  .lam (some "hyp-x") (.atomKey "<F>") (.hypX "hyp-x")

private def namedLamY : Lara.NDNamed.NCert :=
  .lam (some "hyp-y") (.atomKey "<F>") (.hypX "hyp-y")

example : Lara.NDNamed.Alpha namedLamX namedLamY := by
  rfl

example :
    Lara.NDNamed.toDB (fun _ => none) (fun _ => none) 0 [] namedLamX =
      Lara.NDNamed.toDB (fun _ => none) (fun _ => none) 0 [] namedLamY :=
  Lara.NDNamed.toDB_eq_of_alpha (fun _ => none) (fun _ => none) 0 (by rfl)

private def replacement : Pat := .var Y

private def capturesY : Rule :=
  { mainRule with
    params := [X, Y]
    premises := [atomPat "score" [.var X]]
    conclusion := atomPat "score" [.var X]
    questions := [] }

example : Lara.Surface.Binding.substParam X replacement capturesY = none := by
  decide

private def replayIdentityChangedProgram : Program :=
  { allFormsProgram with digest := ⟨"sha256:changed"⟩ }

private def replayIdentityChangingRename :
    Lara.Surface.Binding.GlobalRenaming.Attempt :=
  { maps := Lara.Surface.Binding.GlobalRenaming.id
    sourceProgram := allFormsProgram
    targetProgram := replayIdentityChangedProgram
    sourcePolicy := allFormsPolicy
    targetPolicy := allFormsPolicy }

example : ¬ Lara.Surface.Binding.GlobalRenaming.Valid
    replayIdentityChangingRename := by
  intro valid
  have programEq := valid.1
  change replayIdentityChangedProgram =
    Lara.Surface.Binding.renameProgram
      Lara.Surface.Binding.GlobalRenaming.id allFormsProgram at programEq
  rw [Lara.Surface.Binding.renameProgram_id] at programEq
  have digestEq := congrArg Program.digest programEq
  simp [replayIdentityChangedProgram, allFormsProgram] at digestEq

private def sourceSwap (source : SourceRef) : SourceRef :=
  if source = ⟨"unused-source-a"⟩ then ⟨"unused-source-b"⟩
  else if source = ⟨"unused-source-b"⟩ then ⟨"unused-source-a"⟩
  else source

private theorem sourceSwap_injective : Function.Injective sourceSwap := by
  intro left right equal
  by_cases leftA : left = (⟨"unused-source-a"⟩ : SourceRef)
  · subst left
    by_cases rightA : right = (⟨"unused-source-a"⟩ : SourceRef)
    · exact rightA.symm
    · by_cases rightB : right = (⟨"unused-source-b"⟩ : SourceRef)
      · subst right
        simp [sourceSwap] at equal
      · simp [sourceSwap, rightA, rightB] at equal
        exact absurd equal.symm rightB
  · by_cases leftB : left = (⟨"unused-source-b"⟩ : SourceRef)
    · subst left
      by_cases rightA : right = (⟨"unused-source-a"⟩ : SourceRef)
      · subst right
        simp [sourceSwap] at equal
      · by_cases rightB : right = (⟨"unused-source-b"⟩ : SourceRef)
        · exact rightB.symm
        · simp [sourceSwap, rightA, rightB] at equal
          exact absurd equal.symm rightA
    · by_cases rightA : right = (⟨"unused-source-a"⟩ : SourceRef)
      · subst right
        simp [sourceSwap, leftA, leftB] at equal
      · by_cases rightB : right = (⟨"unused-source-b"⟩ : SourceRef)
        · subst right
          simp [sourceSwap, leftA, leftB] at equal
        · simpa [sourceSwap, leftA, leftB, rightA, rightB] using equal

example :
    sourceSwap ⟨"unused-source-a"⟩ = (⟨"unused-source-b"⟩ : SourceRef) := by
  rfl

example :
    Lara.Surface.Supported
        ⟨Lara.Surface.Binding.renameProgram
            (Lara.Surface.Binding.GlobalRenaming.sourceOnly
              sourceSwap sourceSwap_injective) allFormsProgram,
          allFormsPolicy⟩ ↔
      Lara.Surface.Supported ⟨allFormsProgram, allFormsPolicy⟩ := by
  simpa [Lara.Surface.Binding.renamePolicy_sourceOnly] using
    (Lara.Surface.Binding.supported_sourceOnly_rename_iff sourceSwap sourceSwap_injective
      allFormsProgram allFormsPolicy (by
        simp [Lara.Surface.Binding.SourcesFixed, allFormsProgram, sourceSwap]))

/-! A simultaneous nonidentity renaming witness for the public theorem. -/

private def multiNamespaceText (text : String) : String :=
  if text = "e" then "e-renamed"
  else if text = "e-renamed" then "e"
  else text

private theorem multiNamespaceText_involutive (text : String) :
    multiNamespaceText (multiNamespaceText text) = text := by
  simp only [multiNamespaceText]
  split <;> simp_all

private theorem multiNamespaceText_injective :
    Function.Injective multiNamespaceText := by
  intro left right equal
  calc
    left = multiNamespaceText (multiNamespaceText left) :=
      (multiNamespaceText_involutive left).symm
    _ = multiNamespaceText (multiNamespaceText right) :=
      congrArg multiNamespaceText equal
    _ = right := multiNamespaceText_involutive right

private def multiProp (id : PropId) : PropId :=
  ⟨multiNamespaceText id.val⟩
private def multiQuestion (id : QuestionId) : QuestionId :=
  ⟨multiNamespaceText id.val⟩
private def multiLeaf (id : LeafId) : LeafId :=
  ⟨multiNamespaceText id.val⟩
private def multiRule (id : RuleId) : RuleId :=
  ⟨multiNamespaceText id.val⟩
private def multiArg (id : ArgId) : ArgId :=
  ⟨multiNamespaceText id.val⟩
private def multiArgRef (id : ArgRef) : ArgRef :=
  ⟨multiNamespaceText id.val⟩
private def multiObligation (id : ObligationId) : ObligationId :=
  ⟨multiNamespaceText id.val⟩
private def multiGroup (id : GroupId) : GroupId :=
  ⟨multiNamespaceText id.val⟩
private def multiMeasurand (id : MeasurandId) : MeasurandId :=
  ⟨multiNamespaceText id.val⟩
private def multiDataset (id : DatasetId) : DatasetId :=
  ⟨multiNamespaceText id.val⟩
private def multiPremiseLabel (id : PremiseLabel) : PremiseLabel :=
  ⟨multiNamespaceText id.val⟩
private def multiValueName (id : ValueName) : ValueName :=
  ⟨multiNamespaceText id.val⟩

private def multiNamespaceRenaming :
    Lara.Surface.Binding.GlobalRenaming where
  prop := multiProp
  question := multiQuestion
  leaf := multiLeaf
  rule := multiRule
  arg := multiArg
  argRef := multiArgRef
  obligation := multiObligation
  source := id
  group := multiGroup
  measurand := multiMeasurand
  dataset := multiDataset
  premiseLabel := multiPremiseLabel
  valueName := multiValueName
  prop_injective := by
    rintro ⟨left⟩ ⟨right⟩ equal
    have same := multiNamespaceText_injective (congrArg PropId.val equal)
    cases same
    rfl
  question_injective := by
    rintro ⟨left⟩ ⟨right⟩ equal
    have same := multiNamespaceText_injective (congrArg QuestionId.val equal)
    cases same
    rfl
  leaf_injective := by
    rintro ⟨left⟩ ⟨right⟩ equal
    have same := multiNamespaceText_injective (congrArg LeafId.val equal)
    cases same
    rfl
  rule_injective := by
    rintro ⟨left⟩ ⟨right⟩ equal
    have same := multiNamespaceText_injective (congrArg RuleId.val equal)
    cases same
    rfl
  arg_injective := by
    rintro ⟨left⟩ ⟨right⟩ equal
    have same := multiNamespaceText_injective (congrArg ArgId.val equal)
    cases same
    rfl
  argRef_injective := by
    rintro ⟨left⟩ ⟨right⟩ equal
    have same := multiNamespaceText_injective (congrArg ArgRef.val equal)
    cases same
    rfl
  obligation_injective := by
    rintro ⟨left⟩ ⟨right⟩ equal
    have same := multiNamespaceText_injective (congrArg ObligationId.val equal)
    cases same
    rfl
  source_injective := fun _ _ equal => equal
  group_injective := by
    rintro ⟨left⟩ ⟨right⟩ equal
    have same := multiNamespaceText_injective (congrArg GroupId.val equal)
    cases same
    rfl
  measurand_injective := by
    rintro ⟨left⟩ ⟨right⟩ equal
    have same := multiNamespaceText_injective (congrArg MeasurandId.val equal)
    cases same
    rfl
  dataset_injective := by
    rintro ⟨left⟩ ⟨right⟩ equal
    have same := multiNamespaceText_injective (congrArg DatasetId.val equal)
    cases same
    rfl
  premiseLabel_injective := by
    rintro ⟨left⟩ ⟨right⟩ equal
    have same := multiNamespaceText_injective (congrArg PremiseLabel.val equal)
    cases same
    rfl
  valueName_injective := by
    rintro ⟨left⟩ ⟨right⟩ equal
    have same := multiNamespaceText_injective (congrArg ValueName.val equal)
    cases same
    rfl
  question_coherent := fun _ => rfl
  leaf_coherent := fun _ => rfl
  rule_coherent := fun _ => rfl
  arg_coherent := fun _ => rfl
  argRef_coherent := fun _ => rfl
  obligation_coherent := fun _ => rfl
  group_coherent := fun _ => rfl
  measurand_coherent := fun _ => rfl
  dataset_coherent := fun _ => rfl
  premiseLabel_coherent := fun _ => rfl
  valueName_coherent := fun _ => rfl


private theorem multiNamespaceText_cellCanonNat (text : String) :
    Lara.Cell.parseCanonNat (multiNamespaceText text) =
      Lara.Cell.parseCanonNat text := by
  by_cases isE : text = "e"
  · subst text
    native_decide
  by_cases isRenamed : text = "e-renamed"
  · subst text
    native_decide
  simp [multiNamespaceText, isE, isRenamed]

private theorem multiNamespaceText_identifier (text : String) :
    Lara.Surface.sourceStartsIdentifier (multiNamespaceText text) =
      Lara.Surface.sourceStartsIdentifier text := by
  by_cases isE : text = "e"
  · subst text
    native_decide
  by_cases isRenamed : text = "e-renamed"
  · subst text
    native_decide
  simp [multiNamespaceText, isE, isRenamed]

private theorem allForms_patternNullaryCons :
    Lara.Surface.patternNullaryCons allFormsPolicy = [] := by
  native_decide

private theorem allForms_programNullaryCons_excludes_e :
    "e" ∉ Lara.Surface.programNullaryCons allFormsProgram ∧
      "e-renamed" ∉ Lara.Surface.programNullaryCons allFormsProgram := by
  native_decide

private theorem allForms_valueNames :
    Lara.Surface.valueNames allFormsProgram = [⟨"threshold"⟩] := by
  native_decide

private theorem allForms_programBinderSpellings :
    Lara.Surface.programBinderSpellings allFormsProgram = ["h"] := by
  native_decide

private theorem allForms_programNlDirectiveBodies :
    Lara.Surface.programNlDirectiveBodies allFormsProgram =
      ["threshold".toList, "cell e".toList, "threshold".toList] := by
  native_decide

private theorem allForms_programOpaqueCertPremiseSpellings :
    Lara.Surface.programOpaqueCertPremiseSpellings allFormsProgram = [] := by
  native_decide

private theorem allForms_programDirectiveBodies :
    Lara.Surface.programDirectiveBodies allFormsProgram =
      [ "threshold".toList
      , "cell e".toList
      , "threshold".toList
      , "threshold".toList
      , "cell e".toList
      , "cell baseline".toList
      , "cell binding".toList
      , "cell proof".toList
      , "cell verdict-pro".toList
      , "cell verdict-con".toList
      ] := by
  native_decide

private theorem multiNamespaceRenaming_sound :
    Lara.Surface.RenamingSound multiNamespaceRenaming
      allFormsProgram allFormsPolicy := by
  refine
    { rule_spelling := by native_decide
      leaf_spelling := by native_decide
      cell_spelling := by native_decide
      empty := by native_decide
      numeric := ?_
      integer := ?_
      canonicalNat := ?_
      cellCanonNat := ?_
      identifier := ?_
      sigma := ?_
      atoms := ?_
      patterns := ?_
      certBinders := ?_
      directiveDelimiterFresh := ?_
      opaqueCertPremises := ?_
      directiveInjective := ?_
      noCellValues := ?_ }
  · intro n
    have eNotNat : "e".toNat? = none := by
      native_decide
    have renamedNotNat : "e-renamed".toNat? = none := by
      native_decide
    have neE : Nat.repr n ≠ "e" := by
      intro equal
      have impossible := congrArg String.toNat? equal
      rw [Nat.toNat?_repr, eNotNat] at impossible
      contradiction
    have neRenamed : Nat.repr n ≠ "e-renamed" := by
      intro equal
      have impossible := congrArg String.toNat? equal
      rw [Nat.toNat?_repr, renamedNotNat] at impossible
      contradiction
    simp [Lara.Surface.Binding.renameText, multiNamespaceRenaming, multiProp,
      multiNamespaceText, neE, neRenamed]
  · intro value
    cases value with
    | ofNat n =>
        have eNotNat : "e".toNat? = none := by
          native_decide
        have renamedNotNat : "e-renamed".toNat? = none := by
          native_decide
        have neE : Nat.repr n ≠ "e" := by
          intro equal
          have impossible := congrArg String.toNat? equal
          rw [Nat.toNat?_repr, eNotNat] at impossible
          contradiction
        have neRenamed : Nat.repr n ≠ "e-renamed" := by
          intro equal
          have impossible := congrArg String.toNat? equal
          rw [Nat.toNat?_repr, renamedNotNat] at impossible
          contradiction
        simp [Lara.Surface.Binding.renameText, multiNamespaceRenaming,
          multiProp, multiNamespaceText, Int.repr, neE, neRenamed]
    | negSucc n =>
        have neE : "-" ++ Nat.repr (n + 1) ≠ "e" := by
          intro equal
          have impossible := congrArg (fun text : String => text.toList.head?) equal
          simp at impossible
        have neRenamed : "-" ++ Nat.repr (n + 1) ≠ "e-renamed" := by
          intro equal
          have impossible := congrArg (fun text : String => text.toList.head?) equal
          simp at impossible
        simp [Lara.Surface.Binding.renameText, multiNamespaceRenaming,
          multiProp, multiNamespaceText, Int.repr, neE, neRenamed]
  · intro text
    by_cases isE : text = "e"
    · subst text
      native_decide
    by_cases isRenamed : text = "e-renamed"
    · subst text
      native_decide
    simp [Lara.Surface.Binding.renameText, multiNamespaceRenaming, multiProp,
      multiNamespaceText, isE, isRenamed]
  · intro text
    exact multiNamespaceText_cellCanonNat text
  · intro text
    exact multiNamespaceText_identifier text
  · intro con member
    simp [allFormsPolicy, surfaceSigma] at member
    rcases member with rfl | rfl | rfl | rfl <;> native_decide
  · intro text member _
    change multiNamespaceText text = text
    by_cases isE : text = "e"
    · subst text
      exact False.elim (allForms_programNullaryCons_excludes_e.1 member)
    by_cases isRenamed : text = "e-renamed"
    · subst text
      exact False.elim (allForms_programNullaryCons_excludes_e.2 member)
    simp [multiNamespaceText, isE, isRenamed]
  · intro text member
    rw [allForms_patternNullaryCons] at member
    simp at member
  · intro text member
    rw [allForms_programBinderSpellings] at member
    simp at member
    subst text
    native_decide
  · intro body member
    rw [allForms_programNlDirectiveBodies] at member
    simp at member
    rcases member with rfl | rfl | rfl <;> native_decide
  · intro text member
    rw [allForms_programOpaqueCertPremiseSpellings] at member
    simp at member
  · intro left leftMember right rightMember equal
    rw [allForms_programDirectiveBodies] at leftMember rightMember
    simp at leftMember rightMember
    rcases leftMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
      rcases rightMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
      first
      | rfl
      | exfalso
        exact (by native_decide : ¬ _) equal
  · intro value member
    rw [allForms_valueNames] at member
    simp at member
    subst value
    native_decide

example :
    multiNamespaceRenaming.leaf resultLeaf ≠ resultLeaf ∧
    multiNamespaceRenaming.arg ⟨"e"⟩ ≠ (⟨"e"⟩ : ArgId) ∧
    multiNamespaceRenaming.rule ⟨"e"⟩ ≠ (⟨"e"⟩ : RuleId) ∧
    multiNamespaceRenaming.premiseLabel ⟨"e"⟩ ≠
      (⟨"e"⟩ : PremiseLabel) ∧
    multiNamespaceRenaming.question ⟨"e"⟩ ≠ (⟨"e"⟩ : QuestionId) ∧
    multiNamespaceRenaming.prop ⟨"e"⟩ ≠ (⟨"e"⟩ : PropId) ∧
    multiNamespaceRenaming.valueName ⟨"e"⟩ ≠ (⟨"e"⟩ : ValueName) ∧
    multiNamespaceRenaming.measurand ⟨"e"⟩ ≠ (⟨"e"⟩ : MeasurandId) ∧
    multiNamespaceRenaming.dataset ⟨"e"⟩ ≠ (⟨"e"⟩ : DatasetId) := by
  native_decide

example :
    Lara.Surface.Supported
        ⟨Lara.Surface.Binding.renameProgram multiNamespaceRenaming allFormsProgram,
          Lara.Surface.Binding.renamePolicy multiNamespaceRenaming allFormsPolicy⟩ ↔
      Lara.Surface.Supported ⟨allFormsProgram, allFormsPolicy⟩ :=
  Lara.Surface.Binding.supported_rename_iff multiNamespaceRenaming
    allFormsProgram allFormsPolicy multiNamespaceRenaming_sound

example :
    Lara.Surface.Renaming.RenamedExcept
      (Lara.Surface.Renaming.ExpandValuesErrorRelated multiNamespaceRenaming)
      (Lara.Surface.Renaming.SemanticProgramRelated multiNamespaceRenaming)
      (Lara.Surface.expandValues allFormsPolicy allFormsProgram)
      (Lara.Surface.expandValues
        (Lara.Surface.Binding.renamePolicy multiNamespaceRenaming allFormsPolicy)
        (Lara.Surface.Binding.renameProgram multiNamespaceRenaming
          allFormsProgram)) :=
  Lara.Surface.Renaming.expandValues_rename_related
    multiNamespaceRenaming_sound

/-- A replay-neutral environment used to exercise the public all-namespace
transport theorem independently of the later all-forms acceptance fixture. -/
private def multiNamespaceTransportEnv :
    Lara.Surface.Env (fun source => source) where
  registry := fun _ => none
  startsIdent := fun _ => false
  startsIdent_nat_false := by intro; rfl
  encodeProp := fun _ => none

private theorem multiNamespaceTransportEnv_sound :
    Lara.Surface.Renaming.EnvRenamingSound multiNamespaceTransportEnv
      multiNamespaceRenaming := by
  constructor
  · intro
    rfl
  · intro backend digest certificate premises conclusion
    rfl

/-- The public global-renaming stage transports are exercised with simultaneous,
non-identity changes to every typed namespace listed above.  This is not the
binder-only alpha-equivalence theorem. -/
example :
    Lara.Surface.Renaming.GlobalRenamingStageTransports
      multiNamespaceTransportEnv multiNamespaceRenaming
      allFormsProgram allFormsPolicy :=
  Lara.Surface.Renaming.global_renaming_stage_transports
    multiNamespaceRenaming_sound multiNamespaceTransportEnv_sound

/-- The same public stage bundle exposes the final core acceptance bridge once
the lowered unit's signature is aligned with the surface policy signature. -/
example
    (gamma : Lara.Support.LeafId → Option Lara.Atom)
    (ground : List Lara.Atom) (unit : Lara.Unit)
    (sigmaEq : unit.sigma = allFormsPolicy.sigma) :
    Lara.Surface.exceptIsOk
        (Lara.Check.Unit.checkUnit
          (Lara.Surface.Renaming.renameGamma multiNamespaceRenaming gamma)
          multiNamespaceTransportEnv.registry
          (ground.map
            (Lara.Surface.Renaming.renameResidualAtom multiNamespaceRenaming))
          (Lara.Surface.Renaming.renameCoreUnit multiNamespaceRenaming unit)) =
      Lara.Surface.exceptIsOk
        (Lara.Check.Unit.checkUnit gamma multiNamespaceTransportEnv.registry
          ground unit) :=
  (Lara.Surface.Renaming.global_renaming_stage_transports
      multiNamespaceRenaming_sound multiNamespaceTransportEnv_sound).coreChecking
    gamma ground unit sigmaEq

/-! ### Task 3: expansion vectors (value and comparison) -/

private def expandedValueProgram : Program :=
  { allFormsProgram with
    valueBindings := []
    decls :=
      [ .leaf ⟨resultLeaf, atom "reported" [systemA, quality, dataset, .num "7"], .observed, .user, [⟨"source:e"⟩]⟩
      , .leaf ⟨baselineLeaf, atom "reported" [systemB, quality, dataset, .num "5"], .attested, .aiExecuted, []⟩
      , .leaf ⟨bindingLeaf, atom "binding" [systemA, systemB, quality, dataset, .num "7", .num "5"], .assumed, .checker "checker" "1", []⟩
      , .leaf ⟨proofLeaf, atom "score" [.num "7"], .certified, .user, []⟩
      , .leaf ⟨verdictProLeaf, atom "verdict" [.num "1"], .observed, .user, []⟩
      , .leaf ⟨verdictConLeaf, atom "verdict" [.num "0"], .observed, .user, []⟩
      , .claim ⟨claimMain, "threshold 7; observed 7", atom "score" [.num "7"], binding⟩
      , .arg substitutedExplicitArgument
      , .arg inferredArgument
      , .arg proArgument
      , .arg conArgument
      , .attack (.rebut argPro argCon)
      , .attack (.undercut argPro argInferred [.name "cq"])
      , .attack (.undermine argPro argCon [.index 0])
      , .status claimMain
      , .group ⟨⟨"reported-quality"⟩, [resultLeaf, baselineLeaf]⟩
      , .comparison { comparison with claim := { comparison.claim with nlRaw := "comparison 7" } }
      ] }

/-- Simultaneous, non-recursive value expansion: the second binding's value is
the constructor name `threshold` itself, never re-expanded to `7`. -/
example :
    Lara.Surface.substituteValueAtom
      [⟨⟨"threshold"⟩, .num "7"⟩, ⟨⟨"dup"⟩, con0 "threshold"⟩]
      (atom "score" [con0 "dup"]) = atom "score" [con0 "threshold"] := by
  rfl

/-- Applied-constructor traversal substitutes into argument terms but never
inside opaque certificate payloads. -/
private def certPayloadWithName : Sx :=
  .node "prop" (.cons (.str "score(threshold)") .nil)
private def certWithName : Assurance :=
  .cert ⟨⟨"nd"⟩, 1, ⟨"theory"⟩, certPayloadWithName⟩
private def argWithCert : Arg :=
  ⟨⟨"arg-cert"⟩, .supportsClaim claimMain,
    .explicitTheta (.rule ruleMainId [(x, con0 "threshold")] .nil .nil [] certWithName)⟩

example :
    Lara.Surface.substDecl [⟨⟨"threshold"⟩, .num "7"⟩] (.arg argWithCert) =
      .arg ⟨⟨"arg-cert"⟩, .supportsClaim claimMain,
        .explicitTheta (.rule ruleMainId [(x, .num "7")] .nil .nil [] certWithName)⟩ := by
  rfl

/-- The walk's Γ for the all-forms program after substitution: the six leaves. -/
private def fullGamma : List (LeafId × Atom) :=
  [ (resultLeaf, atom "reported" [systemA, quality, dataset, .num "7"])
  , (baselineLeaf, atom "reported" [systemB, quality, dataset, .num "5"])
  , (bindingLeaf, atom "binding" [systemA, systemB, quality, dataset, .num "7", .num "5"])
  , (proofLeaf, atom "score" [.num "7"])
  , (verdictProLeaf, atom "verdict" [.num "1"])
  , (verdictConLeaf, atom "verdict" [.num "0"]) ]

/-! `{cell e}` interpolation resolves a named leaf's numeric cell; `{{`/`}}`
escapes pass braces through literally. -/
/-- `{name}` interpolation inside a comparison block's prose. -/
private def comparisonProseRel :
    Lara.Surface.ExpandsNl [⟨⟨"threshold"⟩, .num "7"⟩]
      fullGamma "comparison {threshold}".toList "comparison 7".toList := by
  change Lara.Surface.ExpandsNl [⟨⟨"threshold"⟩, .num "7"⟩]
    fullGamma
    ('c' :: 'o' :: 'm' :: 'p' :: 'a' :: 'r' :: 'i' :: 's' :: 'o' :: 'n' :: ' ' :: '{' :: 't' :: 'h' :: 'r' :: 'e' :: 's' :: 'h' :: 'o' :: 'l' :: 'd' :: '}' :: [])
    ('c' :: 'o' :: 'm' :: 'p' :: 'a' :: 'r' :: 'i' :: 's' :: 'o' :: 'n' :: ' ' :: '7' :: [])
  repeat (first | apply Lara.Surface.ExpandsNl.char | simp)
  refine Lara.Surface.ExpandsNl.value (b := ⟨⟨"threshold"⟩, .num "7"⟩) ?_ ?_ ?_ ?_
  · rfl
  · simp
  · simp
  · exact Lara.Surface.ExpandsNl.nil

private def cellInterpRel :
    Lara.Surface.ExpandsNl [⟨⟨"threshold"⟩, .num "7"⟩]
      fullGamma
      "threshold {threshold}; observed {cell e}".toList
      "threshold 7; observed 7".toList := by
  change Lara.Surface.ExpandsNl [⟨⟨"threshold"⟩, .num "7"⟩]
    fullGamma
    ('t' :: 'h' :: 'r' :: 'e' :: 's' :: 'h' :: 'o' :: 'l' :: 'd' :: ' ' :: '{' :: 't' :: 'h' :: 'r' :: 'e' :: 's' :: 'h' :: 'o' :: 'l' :: 'd' :: '}' :: ';' :: ' ' :: 'o' :: 'b' :: 's' :: 'e' :: 'r' :: 'v' :: 'e' :: 'd' :: ' ' :: '{' :: 'c' :: 'e' :: 'l' :: 'l' :: ' ' :: 'e' :: '}' :: [])
    ('t' :: 'h' :: 'r' :: 'e' :: 's' :: 'h' :: 'o' :: 'l' :: 'd' :: ' ' :: '7' :: ';' :: ' ' :: 'o' :: 'b' :: 's' :: 'e' :: 'r' :: 'v' :: 'e' :: 'd' :: ' ' :: '7' :: [])
  repeat (first | apply Lara.Surface.ExpandsNl.char | simp)
  refine Lara.Surface.ExpandsNl.value (b := ⟨⟨"threshold"⟩, .num "7"⟩) ?_ ?_ ?_ ?_
  · rfl
  · simp
  · simp
  · change Lara.Surface.ExpandsNl [⟨⟨"threshold"⟩, .num "7"⟩]
      fullGamma
      (';' :: ' ' :: 'o' :: 'b' :: 's' :: 'e' :: 'r' :: 'v' :: 'e' :: 'd' :: ' ' :: '{' :: 'c' :: 'e' :: 'l' :: 'l' :: ' ' :: 'e' :: '}' :: [])
      (';' :: ' ' :: 'o' :: 'b' :: 's' :: 'e' :: 'r' :: 'v' :: 'e' :: 'd' :: ' ' :: '7' :: [])
    repeat (first | apply Lara.Surface.ExpandsNl.char | simp)
    change Lara.Surface.ExpandsNl [⟨⟨"threshold"⟩, .num "7"⟩]
      fullGamma
      ('{' :: "cell ".toList ++ resultLeaf.val.toList ++ '}' :: []) ('7' :: [])
    refine Lara.Surface.ExpandsNl.cell (leaf := resultLeaf)
      (prop := atom "reported" [systemA, quality, dataset, .num "7"]) (d := ⟨7, 1⟩)
      (rest := []) (out := []) ?_ ?_ ?_ ?_ ?_
    · rfl
    · native_decide
    · rfl
    · simp [resultLeaf]
    · exact Lara.Surface.ExpandsNl.nil

example : Lara.Surface.expandNl [⟨⟨"threshold"⟩, .num "7"⟩]
      fullGamma
      "claim" "threshold {threshold}; observed {cell e}" = .ok "threshold 7; observed 7" := by
  exact Lara.Surface.expandNl_complete cellInterpRel

private def braceEscapeRel :
    Lara.Surface.ExpandsNl [] [] "a {{b}} c".toList "a {b} c".toList := by
  change Lara.Surface.ExpandsNl [] []
    ('a' :: ' ' :: '{' :: '{' :: 'b' :: '}' :: '}' :: ' ' :: 'c' :: [])
    ('a' :: ' ' :: '{' :: 'b' :: '}' :: ' ' :: 'c' :: [])
  apply Lara.Surface.ExpandsNl.char
  · constructor <;> simp
  · change Lara.Surface.ExpandsNl [] [] (' ' :: '{' :: '{' :: 'b' :: '}' :: '}' :: ' ' :: 'c' :: [])
      (' ' :: '{' :: 'b' :: '}' :: ' ' :: 'c' :: [])
    apply Lara.Surface.ExpandsNl.char
    · constructor <;> simp
    · change Lara.Surface.ExpandsNl [] [] ('{' :: '{' :: 'b' :: '}' :: '}' :: ' ' :: 'c' :: [])
        ('{' :: 'b' :: '}' :: ' ' :: 'c' :: [])
      apply Lara.Surface.ExpandsNl.escLeft
      change Lara.Surface.ExpandsNl [] [] ('b' :: '}' :: '}' :: ' ' :: 'c' :: [])
        ('b' :: '}' :: ' ' :: 'c' :: [])
      apply Lara.Surface.ExpandsNl.char
      · constructor <;> simp
      · change Lara.Surface.ExpandsNl [] [] ('}' :: '}' :: ' ' :: 'c' :: [])
          ('}' :: ' ' :: 'c' :: [])
        apply Lara.Surface.ExpandsNl.escRight
        change Lara.Surface.ExpandsNl [] [] (' ' :: 'c' :: []) (' ' :: 'c' :: [])
        apply Lara.Surface.ExpandsNl.char
        · constructor <;> simp
        · change Lara.Surface.ExpandsNl [] [] ('c' :: []) ('c' :: [])
          apply Lara.Surface.ExpandsNl.char
          · constructor <;> simp
          · exact Lara.Surface.ExpandsNl.nil

example : Lara.Surface.expandNl [] [] "claim" "a {{b}} c" = .ok "a {b} c" := by
  exact Lara.Surface.expandNl_complete braceEscapeRel

/-- The full value expansion consumes the binding table and interpolates both
the named value and the cell, in the production order. -/
private theorem allForms_value_expansion_exact : Lara.Surface.expandValues allFormsPolicy allFormsProgram =
    .ok expandedValueProgram := by
  have hchecks : Lara.Surface.valueBindingErrors allFormsPolicy allFormsProgram = none := by
    native_decide
  have hclaim : Lara.Surface.claimFormalErrors allFormsPolicy allFormsProgram.valueBindings
      { allFormsProgram with
        decls := allFormsProgram.decls.map (Lara.Surface.substDecl allFormsProgram.valueBindings) } = none := by
    native_decide
  have hnl : Lara.Surface.expandDeclNls allFormsProgram.valueBindings
      (Lara.Surface.declaredLeaves
        { allFormsProgram with
          decls := allFormsProgram.decls.map (Lara.Surface.substDecl allFormsProgram.valueBindings) })
      ({ allFormsProgram with
          decls := allFormsProgram.decls.map (Lara.Surface.substDecl allFormsProgram.valueBindings) }.decls) =
      .ok expandedValueProgram.decls := by
    have hgamma : Lara.Surface.declaredLeaves
        { allFormsProgram with
          decls := allFormsProgram.decls.map (Lara.Surface.substDecl allFormsProgram.valueBindings) } =
        fullGamma := by
      native_decide
    rw [hgamma]
    change Lara.Surface.expandDeclNls allFormsProgram.valueBindings fullGamma
      (allFormsProgram.decls.map (Lara.Surface.substDecl allFormsProgram.valueBindings)) =
      .ok expandedValueProgram.decls
    simp [Lara.Surface.expandDeclNls, Lara.Surface.expandNl_complete cellInterpRel,
      Lara.Surface.expandNl_complete comparisonProseRel, Lara.Surface.bind_ok_reduce,
      allFormsProgram, expandedValueProgram, comparison, atom, terms, con0, binding,
      systemA, systemB, quality, dataset, resultLeaf, baselineLeaf, bindingLeaf, proofLeaf,
      verdictProLeaf, verdictConLeaf,
      explicitArgument, substitutedExplicitArgument, inferredArgument,
      proArgument, conArgument, verdictProTerm, verdictConTerm,
      explicitTerm, substitutedExplicitTerm, nestedTerm,
      Lara.Surface.substDecl, Lara.Surface.substArgInstantiation, Lara.Surface.substSupportTerm,
      Lara.Surface.substSupportTerms, Lara.Surface.substSupportDischarges,
      Lara.Surface.substituteValueAtom, Lara.Surface.substituteValueTerms,
      Lara.Surface.substituteValueTerm, Lara.Surface.lookupValue]
  rw [Lara.Surface.expandValues_eq_of_none_checks allFormsPolicy allFormsProgram
    expandedValueProgram.decls hchecks hclaim hnl]
  congr 1

/-- The executable pass rejects a duplicate binding name with the named error. -/
example : Lara.Surface.expandValues allFormsPolicy
    { allFormsProgram with
      valueBindings := [⟨⟨"threshold"⟩, .num "7"⟩, ⟨⟨"threshold"⟩, .num "8"⟩] } =
    .error (.duplicateValueName ⟨"threshold"⟩) := by
  rfl

/-- The independent whole-program value relation proves the same target. -/
example :
    Lara.Surface.ExpandsValues allFormsProgram expandedValueProgram :=
  Lara.Surface.expandValues_sound allFormsPolicy allForms_value_expansion_exact

/-- Duplicate reporting follows declaration order: the later `b`, not the
earlier `a` whose second occurrence is farther right. -/
example : Lara.Surface.duplicateName?
    [⟨⟨"a"⟩, .num "1"⟩, ⟨⟨"b"⟩, .num "2"⟩,
      ⟨⟨"b"⟩, .num "3"⟩, ⟨⟨"a"⟩, .num "4"⟩] = some ⟨"b"⟩ := by
  native_decide

/-- Constructor-name collisions are rejected before substitution. -/
example : Lara.Surface.expandValues allFormsPolicy
    { allFormsProgram with valueBindings := [⟨⟨"system-a"⟩, .num "7"⟩] } =
    .error (.invalidValueBinding ⟨"system-a"⟩) := by
  rfl

private def invalidInterpolationProgram : Program :=
  { allFormsProgram with
    decls := allFormsProgram.decls.map fun d =>
      match d with
      | .claim claim =>
          if claim.id = claimMain then .claim { claim with nl := "{missing}" }
          else d
      | _ => d }

/-- Invalid interpolation reports the missing binding name. -/
example : Lara.Surface.expandValues allFormsPolicy invalidInterpolationProgram =
    .error (.invalidValueBinding ⟨"missing"⟩) := by
  rfl

/-- Comparison scheme lookup uses the exact `(relation, polarity)` pair: the
matching scheme is found, and a different relation has none. -/
example : (Lara.Surface.comparisonExpansion? allFormsProgram allFormsPolicy comparison).isSome = true := by
  native_decide

example : (Lara.Surface.comparisonExpansion? missingComparisonSchemeInput.program allFormsPolicy
      { comparison with relation := .atLeastAsGood }).isSome = false := by
  native_decide

/-- Missing scheme surfaces as the coarse `invalidComparison` error naming the
block's claim id. -/
example : Lara.Surface.expandComparisons allFormsPolicy missingComparisonSchemeInput.program =
    .error (.invalidComparison claimComparison) := by
  have hnone : Lara.Surface.comparisonExpansion? missingComparisonSchemeInput.program allFormsPolicy
      { comparison with relation := .atLeastAsGood } = none := by
    native_decide
  have hf : Lara.Surface.GeneratedIdsFresh missingComparisonSchemeInput.program = true := by
    native_decide
  have hcollision :
      Lara.Surface.generatedIdCollisionClaim? missingComparisonSchemeInput.program = none := by
    simpa [Lara.Surface.GeneratedIdsFresh] using hf
  have hduplicate :
      Lara.Surface.duplicateComparisonClaim? missingComparisonSchemeInput.program = none := by
    native_decide
  have hgo : Lara.Surface.expandDecls allFormsPolicy missingComparisonSchemeInput.program
      missingComparisonSchemeInput.program.decls = .error (.invalidComparison claimComparison) := by
    rfl
  simp [Lara.Surface.expandComparisons, hcollision, hduplicate, hgo]

/-! ### Exact comparison expansion evidence -/

private def expandedComparison : Comparison :=
  { comparison with claim := { comparison.claim with nlRaw := "comparison 7" } }

private def explicitRecheckTerm : SupportTerm :=
  .rule recheckRuleId
    [(recheckSystemParam, systemA), (recheckBaselineParam, systemB),
      (recheckMeasurandParam, quality), (recheckDatasetParam, dataset),
      (recheckResultValueParam, .num "7"), (recheckBaselineValueParam, .num "5")]
    .nil .nil []
    (.cert ⟨⟨"ord"⟩, 1, ⟨"theory"⟩, Lara.Surface.ordcmpPayload 1 0⟩)

private def explicitBridgeTerm : SupportTerm :=
  .rule bridgeRuleId
    [(systemParam, systemA), (baselineParam, systemB),
      (measurandParam, quality), (datasetParam, dataset),
      (resultValueParam, .num "7"), (baselineValueParam, .num "5")]
    (.cons (.leaf bindingLeaf) (.cons explicitRecheckTerm .nil))
    .nil [] .none

private def explicitGeneratedDecls : List Decl :=
  [ .claim ⟨claimComparison, "comparison 7", atom "num_lt" [.num "5", .num "7"], binding⟩
  , .arg ⟨comparison.recheckArg, .supportsClaim claimComparison,
      .explicitTheta explicitRecheckTerm⟩
  , .arg ⟨comparison.bridgeArg, .supportsDerived ⟨comparison.bridgeArg.val⟩,
      .explicitTheta explicitBridgeTerm⟩ ]

private def explicitComparisonProgram : Program :=
  { expandedValueProgram with
    decls := expandedValueProgram.decls.dropLast ++ explicitGeneratedDecls }

private def explicitComparisonProvenance : List Lara.Surface.GeneratedArg :=
  [⟨claimComparison, comparison.recheckArg, .recheck⟩,
    ⟨claimComparison, comparison.bridgeArg, .bridge⟩]

/-- The executable pass produces the exact semantic program and provenance,
including generated declaration order, θs, support terms, and `ordcmp 1 0`. -/
theorem comparison_expansion_exact :
    Lara.Surface.expandComparisons allFormsPolicy expandedValueProgram =
      .ok (explicitComparisonProgram, explicitComparisonProvenance) := by
  rfl

/-- The independent declarative relation proves that same exact object. -/
theorem comparison_expansion_relation :
    Lara.Surface.ExpandsComparisons allFormsPolicy expandedValueProgram
      explicitComparisonProgram explicitComparisonProvenance :=
  Lara.Surface.expandComparisons_sound allFormsPolicy comparison_expansion_exact

/-- Every authored attack declaration is retained byte-for-byte by the shallow
comparison pass; the generated argument ids are the endpoints reconstructed by
Task 4. -/
example :
    explicitComparisonProgram.decls.filterMap
      (fun d => match d with | .attack attack => some attack | _ => none) =
      [.rebut argPro argCon, .undercut argPro argInferred [.name "cq"],
        .undermine argPro argCon [.index 0]] := by
  native_decide

/-- No comparison declaration remains after exact expansion. -/
example :
    explicitComparisonProgram.decls.all (fun d => !Lara.Surface.isComparison d) = true := by
  native_decide

/-- The named-value convenience lowers an actual support term to the explicit
support term, rather than merely comparing isolated atoms. -/
theorem named_value_explicit_same_term :
    Lara.Surface.substSupportTerm [⟨⟨"threshold"⟩, .num "7"⟩] explicitTerm =
      substitutedExplicitTerm := by
  rfl

/-- Generated claims and both generated arguments equal their fully explicit
declarations, including support trees and certificate payload. -/
theorem comparison_explicit_same_decls :
    (Lara.Surface.expandComparisons allFormsPolicy expandedValueProgram).map
      (fun output => output.1.decls.drop (expandedValueProgram.decls.length - 1)) =
      .ok explicitGeneratedDecls := by
  rw [comparison_expansion_exact]
  rfl

/-- Codec images compare the genuinely expanded semantic program with the
explicitly authored semantic program. -/
theorem comparison_explicit_same_printed_ast :
    (Lara.Surface.expandComparisons allFormsPolicy expandedValueProgram).map
      (fun output => Lara.Presentation.printProgram output.1) =
      .ok (Lara.Presentation.printProgram explicitComparisonProgram) := by
  rw [comparison_expansion_exact]
  rfl

private def duplicateAuthoredArgProgram : Program :=
  { expandedValueProgram with
    decls := expandedValueProgram.decls.dropLast ++
      [.arg substitutedExplicitArgument, .comparison expandedComparison] }

private def expandedDuplicateAuthoredArgProgram : Program :=
  { expandedValueProgram with
    decls := expandedValueProgram.decls.dropLast ++
      [.arg substitutedExplicitArgument] ++ explicitGeneratedDecls }

/-- Duplicate ids among authored arguments are outside comparison freshness:
the noncolliding comparison still expands normally. -/
example :
    Lara.Surface.GeneratedIdsFresh duplicateAuthoredArgProgram = true ∧
    Lara.Surface.generatedIdCollisionClaim? duplicateAuthoredArgProgram = none ∧
    Lara.Surface.expandComparisons allFormsPolicy duplicateAuthoredArgProgram =
      .ok (expandedDuplicateAuthoredArgProgram, explicitComparisonProvenance) := by
  constructor
  · rfl
  · constructor <;> rfl

private def expandedMainClaim : Claim :=
  ⟨claimMain, "threshold 7; observed 7", atom "score" [.num "7"], binding⟩

private def duplicateAuthoredClaimProgram : Program :=
  { expandedValueProgram with
    decls := expandedValueProgram.decls.dropLast ++
      [.claim expandedMainClaim, .comparison expandedComparison] }

private def expandedDuplicateAuthoredClaimProgram : Program :=
  { expandedValueProgram with
    decls := expandedValueProgram.decls.dropLast ++
      [.claim expandedMainClaim] ++ explicitGeneratedDecls }

/-- Duplicate ids among authored claims likewise do not become an
`invalidComparison` attributed to an unrelated block. -/
example :
    Lara.Surface.GeneratedIdsFresh duplicateAuthoredClaimProgram = true ∧
    Lara.Surface.generatedIdCollisionClaim? duplicateAuthoredClaimProgram = none ∧
    Lara.Surface.expandComparisons allFormsPolicy duplicateAuthoredClaimProgram =
      .ok (expandedDuplicateAuthoredClaimProgram, explicitComparisonProvenance) := by
  constructor
  · rfl
  · constructor <;> rfl

private def laterGeneratedCollision : Comparison :=
  { expandedComparison with
    claim := ⟨⟨"claim-comparison-later"⟩, "later", binding⟩
    recheckArg := argExplicit
    bridgeArg := ⟨"comparison-bridge-later"⟩ }

private def laterGeneratedCollisionProgram : Program :=
  { expandedValueProgram with
    decls := expandedValueProgram.decls ++ [.comparison laterGeneratedCollision] }

/-- A later generated-id collision is attributed to the later block. -/
example :
    Lara.Surface.generatedIdCollisionClaim? laterGeneratedCollisionProgram =
      some ⟨"claim-comparison-later"⟩ ∧
    Lara.Surface.expandComparisons allFormsPolicy laterGeneratedCollisionProgram =
      .error (.invalidComparison ⟨"claim-comparison-later"⟩) := by
  constructor <;> rfl

private def laterDuplicateComparison : Comparison :=
  { expandedComparison with
    claim := ⟨⟨"claim-comparison-duplicate"⟩, "duplicate", binding⟩
    recheckArg := ⟨"comparison-recheck-duplicate"⟩
    bridgeArg := ⟨"comparison-bridge-duplicate"⟩ }

private def laterDuplicateComparisonProgram : Program :=
  { expandedValueProgram with
    decls := expandedValueProgram.decls ++ [.comparison laterDuplicateComparison] }

/-- A repeated comparison key is likewise attributed to its later block. -/
example :
    Lara.Surface.duplicateComparisonClaim? laterDuplicateComparisonProgram =
      some ⟨"claim-comparison-duplicate"⟩ ∧
    Lara.Surface.expandComparisons allFormsPolicy laterDuplicateComparisonProgram =
      .error (.invalidComparison ⟨"claim-comparison-duplicate"⟩) := by
  constructor <;> rfl

/-! ### Task 4: the independent surface judgment -/

/-- The all-forms environment: the production registry over the declared
`theory` digest (`Lara.Driver.buildRegistry` over `nd@1`/`ra@1`/`ord@1`), the
production identifier classifier with numeral spellings excluded, and the
production proposition encoder (`parse`, normalize, key). -/
def surfaceEnv : Lara.Surface.Env Lara.Driver.dcanon where
  registry := Lara.Driver.buildRegistry [(⟨"theory"⟩, [atom "score" [.num "1"]])]
  startsIdent := fun source =>
    if source.isNat then false else Lara.Surface.sourceStartsIdentifier source
  startsIdent_nat_false := by
    intro n
    simp
  encodeProp := fun text =>
    (Lara.Surface.parseSurfaceProp text).map fun proposition =>
      Lara.Strict.encodeAtomKey (Lara.nf Lara.Driver.dcanon proposition)

/-- The concrete global-renaming elaboration fixture uses the same production
identifier classifier and proposition encoder as `surfaceEnv`; only the core
registry is replay-neutral because `elaborateWithAudit` is pure lowering and
does not consult it. -/
private def multiNamespaceElaborationEnv :
    Lara.Surface.Env Lara.Driver.dcanon where
  registry := fun _ => none
  startsIdent := surfaceEnv.startsIdent
  startsIdent_nat_false := surfaceEnv.startsIdent_nat_false
  encodeProp := surfaceEnv.encodeProp

private theorem multiNamespaceElaborationEnv_sound :
    Lara.Surface.Renaming.EnvRenamingSound multiNamespaceElaborationEnv
      multiNamespaceRenaming := by
  constructor
  · intro source
    change
      (if (multiNamespaceText source).isNat then false
        else Lara.Surface.sourceStartsIdentifier
          (multiNamespaceText source)) =
      (if source.isNat then false
        else Lara.Surface.sourceStartsIdentifier source)
    unfold multiNamespaceText
    split
    · rename_i equal
      subst source
      native_decide
    · split
      · rename_i equal
        subst source
        native_decide
      · rfl
  · intro backend digest certificate premises conclusion
    rfl

/-- The positive all-forms derivation: the executable checker accepts. -/
private theorem allForms_check_ok :
    ∃ output, Lara.Surface.check surfaceEnv allFormsInput = .ok output := by
  have h : Lara.Surface.exceptIsOk (Lara.Surface.check surfaceEnv allFormsInput) = true := by
    native_decide
  exact (Lara.Surface.exceptIsOk_iff).mp h

/-- The all-forms fixture derives `Surface.Checks`. -/
private theorem allForms_checks :
    ∃ output, Lara.Surface.Checks surfaceEnv allFormsInput output := by
  obtain ⟨output, hok⟩ := allForms_check_ok
  exact ⟨output, Lara.Surface.check_sound _ _ _ hok⟩

/-- Determinism in action: any two derivations over the fixture agree. -/
example (out₁ out₂ : Lara.Surface.Elaborated Lara.Driver.dcanon)
    (h₁ : Lara.Surface.Checks surfaceEnv allFormsInput out₁)
    (h₂ : Lara.Surface.Checks surfaceEnv allFormsInput out₂) : out₁ = out₂ :=
  Lara.Surface.checks_deterministic _ _ _ _ h₁ h₂

/-- The supported fragment is a consequence of the judgment. -/
example (output : Lara.Surface.Elaborated Lara.Driver.dcanon)
    (h : Lara.Surface.Checks surfaceEnv allFormsInput output) :
    Lara.Surface.Supported allFormsInput :=
  Lara.Surface.checks_supported _ _ _ h

/-! The eight Task-4 negative fixtures, each failing at its own surface rule.
Where Task 1–3 already built a suitable fixture, it is reused. -/

/-- A named `nd@1` lambda binder `proof` captures the premise named `proof`:
the naive lowering would produce a well-typed kernel certificate, so this is
exactly the freshness rule the surface enforces and the core does not. -/
private def capturedCertificatePayload : Sx :=
  .node "app"
    (.cons (.node "lam" (.cons (.str "proof")
      (.cons (.node "prop" (.cons (.str "score(7)") .nil))
        (.cons (.node "hyp" (.cons (.str "proof") .nil)) .nil))))
      (.cons (.node "prem" (.cons (.str "proof") .nil)) .nil))

private def capturedCertificate : Assurance :=
  .cert ⟨⟨"nd"⟩, 1, ⟨"theory"⟩, capturedCertificatePayload⟩

private def capturedNestedTerm : SupportTerm :=
  .rule ruleNestedId [(y, .num "7")]
    (.cons (.leaf proofLeaf) .nil) .nil [] capturedCertificate

private def capturedExplicitTerm : SupportTerm :=
  .rule ruleMainId [(x, con0 "threshold")]
    (.cons capturedNestedTerm .nil)
    (.cons questionId (.leaf proofLeaf) .nil) [] .none

private def capturedExplicitArgument : Arg :=
  ⟨argExplicit, .supportsClaim claimMain, .explicitTheta capturedExplicitTerm⟩

def capturedNamedBinderInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      decls := allFormsProgram.decls.map fun
        | .arg argument =>
            if argument.id = argExplicit then .arg capturedExplicitArgument
            else .arg argument
        | declaration => declaration },
    allFormsPolicy⟩

/-- The comparison block's authored bridge conclusion swaps system and
baseline: the merged substitution cannot match the binding premise, so the
block has no valid expansion. -/
def wrongBridgeConclusionInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      decls := allFormsProgram.decls.map fun
        | .comparison comparison =>
            .comparison { comparison with conclusion := atom "better" [systemB, systemA] }
        | declaration => declaration },
    allFormsPolicy⟩

/-- An explicit support term whose child does not instantiate the citing
rule's premise pattern (`binding` concludes a `binding` atom, not a `score`
atom): every surface rule passes, and only the core support judgment refuses
it. The leaf survives group admission, so the malformed argument reaches the
core boundary. -/
private def badPremiseExplicitArgument : Arg :=
  ⟨argExplicit, .supportsClaim claimMain,
    .explicitTheta (.rule ruleMainId [(x, con0 "threshold")]
      (.cons (.leaf bindingLeaf) .nil)
      (.cons questionId (.leaf proofLeaf) .nil) [] .none)⟩

def invalidCoreSupportInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      decls := allFormsProgram.decls.map fun
        | .arg argument =>
            if argument.id = argExplicit then .arg badPremiseExplicitArgument
            else .arg argument
        | declaration => declaration },
    allFormsPolicy⟩

/-- A certificate naming a backend the registry does not register: the
surface certificate form is schema-less and passes through, the citing rule's
allowlist and the registry refuse it at the core. -/
private def unknownBackendCertificate : Assurance :=
  .cert ⟨⟨"mystery"⟩, 1, ⟨"theory"⟩, namedCertificatePayload⟩

private def unknownBackendExplicitArgument : Arg :=
  ⟨argExplicit, .supportsClaim claimMain,
    .explicitTheta (.rule ruleMainId [(x, con0 "threshold")]
      (.cons (.rule ruleNestedId [(y, .num "7")]
        (.cons (.leaf proofLeaf) .nil) .nil [] unknownBackendCertificate) .nil)
      (.cons questionId (.leaf proofLeaf) .nil) [] .none)⟩

def invalidBackendCertificateInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      decls := allFormsProgram.decls.map fun
        | .arg argument =>
            if argument.id = argExplicit then .arg unknownBackendExplicitArgument
            else .arg argument
        | declaration => declaration },
    allFormsPolicy⟩

/-- The policy's admission table rejects the `certified`/`user` leaf
`proof`: every structural rule passes and the admission decision refuses the
source. -/
def admissionRejectedInput : Lara.Surface.Input :=
  ⟨allFormsProgram,
    { allFormsPolicy with
      admission := allFormsPolicy.admission ++ [((.certified, .user), .reject)] }⟩

/-- Unbound rule parameter: fails the argument fold. -/
example :
    Lara.Surface.errorOf? (Lara.Surface.check surfaceEnv unboundInferenceParameterInput) =
      some (.invalidInferredArgument ⟨"arg-unbound"⟩) := by
  native_decide

/-- Captured `nd@1` binder: fails the named-certificate rule. -/
example :
    Lara.Surface.errorOf? (Lara.Surface.check surfaceEnv capturedNamedBinderInput) =
      some (.invalidNamedCertificate argExplicit) := by
  native_decide

/-- Ambiguous named premise: fails the named-certificate rule. -/
example :
    Lara.Surface.errorOf? (Lara.Surface.check surfaceEnv ambiguousNamedCertificateInput) =
      some (.invalidNamedCertificate ⟨"arg-ambiguous-certificate"⟩) := by
  native_decide

/-- Wrong bridge conclusion: fails the comparison rule. -/
example :
    Lara.Surface.errorOf? (Lara.Surface.check surfaceEnv wrongBridgeConclusionInput) =
      some (.invalidComparison claimComparison) := by
  native_decide

/-- Unresolved attack path: fails the attack rule. -/
example :
    Lara.Surface.errorOf? (Lara.Surface.check surfaceEnv unresolvedAttackPathInput) =
      some (.invalidSurfaceAttack argInferred argExplicit) := by
  native_decide

/-- Invalid core support premise: supported at the surface, refused only by
the core check. -/
example :
    Lara.Surface.supportedB invalidCoreSupportInput = true := by
  native_decide

example :
    Lara.Surface.errorOf? (Lara.Surface.check surfaceEnv invalidCoreSupportInput) =
      some .unsupported := by
  native_decide

/-- Invalid backend certificate: supported at the surface, refused only by
the core check. -/
example :
    Lara.Surface.supportedB invalidBackendCertificateInput = true := by
  native_decide

example :
    Lara.Surface.errorOf? (Lara.Surface.check surfaceEnv invalidBackendCertificateInput) =
      some .unsupported := by
  native_decide

/-- Policy-admission rejection: fails the admission decision. -/
example :
    Lara.Surface.errorOf? (Lara.Surface.check surfaceEnv admissionRejectedInput) =
      some (.admissionRejected proofLeaf) := by
  native_decide

/-! Final whole-branch review regressions: authored roles, requested statuses,
and duplicate-report groups are production source guards.  Each input differs
from the accepted all-forms witness only at the named boundary, so an earlier
empty/duplicate/core failure cannot satisfy the test. -/

private def withArgumentConclusion (target : ArgId) (conclusion : ArgConcl) :
    Decl → Decl
  | .arg argument =>
      if argument.id = target then .arg { argument with concl := conclusion }
      else .arg argument
  | declaration => declaration

private def withRoleBeforeAttackAdversary (target : ArgId)
    (conclusion : ArgConcl) : Decl → Decl
  | .arg argument =>
      if argument.id = target then .arg { argument with concl := conclusion }
      else .arg argument
  | .attack (.undercut source attacked _) =>
      .attack (.undercut source attacked [.name "missing-step"])
  | declaration => declaration

def conclusionMismatchInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      decls := allFormsProgram.decls.map
        (withRoleBeforeAttackAdversary argExplicit
          (.supportsClaim claimComparison)) },
    allFormsPolicy⟩

def undeclaredChallengeInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      decls := allFormsProgram.decls.map
        (withArgumentConclusion argExplicit
          (.challenges (.question questionId ⟨"missing-argument"⟩))) },
    allFormsPolicy⟩

def unknownStatusInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      decls := allFormsProgram.decls.map fun
        | .status _ => .status ⟨"missing-claim"⟩
        | declaration => declaration },
    allFormsPolicy⟩

private def reportGroup (members : List LeafId) : DupGroup :=
  ⟨⟨"reported-quality"⟩, members⟩

def duplicateGroupIdInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      decls := allFormsProgram.decls ++
        [.group (reportGroup [resultLeaf, baselineLeaf]), .arg earlyArgument] },
    allFormsPolicy⟩

private def reportGroupWithId (id : String) : DupGroup :=
  ⟨⟨id⟩, [resultLeaf, baselineLeaf]⟩

def crossingGroupDuplicateInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      decls := allFormsProgram.decls ++
        [ .group (reportGroupWithId "first")
        , .group (reportGroupWithId "second")
        , .group (reportGroupWithId "second")
        , .group (reportGroupWithId "first") ] },
    allFormsPolicy⟩

def capturedRoleMismatchInput : Lara.Surface.Input :=
  ⟨{ capturedNamedBinderInput.program with
      decls := capturedNamedBinderInput.program.decls.map
        (withArgumentConclusion argExplicit (.supportsClaim claimComparison)) },
    capturedNamedBinderInput.policy⟩

def repeatedGroupMemberInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      decls := allFormsProgram.decls.map fun
        | .group _ => .group (reportGroup [resultLeaf, resultLeaf])
        | declaration => declaration },
    allFormsPolicy⟩

def singletonGroupInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      decls := allFormsProgram.decls.map fun
        | .group _ => .group (reportGroup [resultLeaf])
        | declaration => declaration },
    allFormsPolicy⟩

def undeclaredGroupMemberInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      decls := allFormsProgram.decls.map fun
        | .group _ =>
            .group (reportGroup [resultLeaf, ⟨"missing-leaf"⟩])
        | declaration => declaration },
    allFormsPolicy⟩

example :
    Lara.Surface.errorOf?
        (Lara.Surface.check surfaceEnv conclusionMismatchInput) =
      some (.conclusionMismatch argExplicit claimComparison) := by
  native_decide

example :
    Lara.Surface.errorOf?
        (Lara.Surface.check surfaceEnv undeclaredChallengeInput) =
      some (.challengeTargetUndeclared argExplicit) := by
  native_decide

example :
    Lara.Surface.errorOf?
        (Lara.Surface.check surfaceEnv unknownStatusInput) =
      some (.unknownStatusClaim ⟨"missing-claim"⟩) := by
  native_decide

example :
    Lara.Surface.errorOf?
        (Lara.Surface.check surfaceEnv duplicateGroupIdInput) =
      some (.duplicateGroupId ⟨"reported-quality"⟩) := by
  native_decide

/-- Production reports the value at the first repeated occurrence, rather
than the earliest value that happens to repeat later. -/
example :
    Lara.Surface.errorOf?
        (Lara.Surface.check surfaceEnv crossingGroupDuplicateInput) =
      some (.duplicateGroupId ⟨"second"⟩) := by
  native_decide

/-- Certificate lowering belongs to argument instantiation and therefore
precedes authored-role validation for the same argument. -/
example :
    Lara.Surface.errorOf?
        (Lara.Surface.elaborate surfaceEnv capturedRoleMismatchInput) =
      some (.invalidNamedCertificate argExplicit) := by
  native_decide

example :
    Lara.Surface.errorOf?
        (Lara.Surface.check surfaceEnv repeatedGroupMemberInput) =
      some (.groupRepeatedMember ⟨"reported-quality"⟩ resultLeaf) := by
  native_decide

example :
    Lara.Surface.errorOf?
        (Lara.Surface.check surfaceEnv singletonGroupInput) =
      some (.groupTooFewMembers ⟨"reported-quality"⟩) := by
  native_decide

example :
    Lara.Surface.errorOf?
        (Lara.Surface.check surfaceEnv undeclaredGroupMemberInput) =
      some (.groupMemberUndeclared ⟨"reported-quality"⟩ ⟨"missing-leaf"⟩) := by
  native_decide

/-! Task 4 Step 5: non-definitional independence. The captured-binder input
has no surface derivation. The following specialized lowering starts from the
captured payload and uses the independent named-certificate translation
`toDB`, which omits exactly the binder-versus-premise freshness premise
enforced by `lowerNamed`. It does not replace or repair the source argument. -/

def capturedNaiveNamedCertificate : Lara.NDNamed.NCert :=
  .app
    (.lam (some "proof") (.prop "score(7)") (.hypX "proof"))
    (.prem (.inr "proof"))

example :
    Lara.NDNamed.render capturedNaiveNamedCertificate =
      Lara.Surface.sxToSExpr capturedCertificatePayload := by
  native_decide

def capturedNaiveCertificateCore? : Option Lara.Support.Assurance := do
  let resolver := Lara.Surface.certificateResolver
    capturedNamedBinderInput.program nestedRule [] [.leaf proofLeaf]
  let lowered ← Lara.NDNamed.toDB resolver surfaceEnv.encodeProp 1 []
    capturedNaiveNamedCertificate
  pure (.cert
    (Lara.Surface.toSupportBackendId ⟨"nd"⟩ 1)
    (Lara.Surface.toSupportTheoryDigest ⟨"theory"⟩)
    ⟨Lara.NDNamed.encodeCert lowered⟩)

/-- The explicit core term obtained from the captured source after value
substitution when only named-binder freshness is omitted. -/
def capturedNaiveExplicitCore? : Option Lara.Support.SupportTerm := do
  let assurance ← capturedNaiveCertificateCore?
  let nested : Lara.Support.SupportTerm :=
    .inst (Lara.Surface.toSupportRuleId ruleNestedId)
      [(Lara.Surface.toSupportParam y, .num "7")]
      [.leaf (Lara.Surface.toSupportLeafId proofLeaf)] [] [] assurance
  pure (.inst (Lara.Surface.toSupportRuleId ruleMainId)
    [(Lara.Surface.toSupportParam x, .num "7")]
    [nested]
    [(Lara.Surface.toSupportQuestionId questionId,
      .leaf (Lara.Surface.toSupportLeafId proofLeaf))]
    [] .none)

example :
    capturedNaiveExplicitCore? =
      Lara.Surface.lowerToSupportTerm surfaceEnv allFormsProgram allFormsPolicy []
        substitutedExplicitTerm := by
  native_decide

private def replaceCapturedCore (replacement : Lara.Support.SupportTerm) :
    List ArgId → List Lara.Support.SupportTerm → List Lara.Support.SupportTerm
  | id :: ids, term :: terms =>
      if id = argExplicit then replacement :: terms
      else term :: replaceCapturedCore replacement ids terms
  | _, terms => terms

/-- The exact core unit obtained by inserting the capture-naively lowered
captured argument into the otherwise identical assembled carrier. -/
def capturedNaiveBypassUnit? : Option Lara.Unit :=
  match Lara.Surface.assemble surfaceEnv allFormsInput, capturedNaiveExplicitCore? with
  | .ok output, some core =>
      some { output.unit with args := replaceCapturedCore core output.argIds output.unit.args }
  | _, _ => none

private def acceptedAllFormsUnit? : Option Lara.Unit :=
  match Lara.Surface.assemble surfaceEnv allFormsInput with
  | .ok output => some output.unit
  | .error _ => none

private def capturedNaiveBypassArgs? : Option (List Lara.Support.SupportTerm) :=
  match Lara.Surface.assemble surfaceEnv allFormsInput, capturedNaiveExplicitCore? with
  | .ok output, some core =>
      some (replaceCapturedCore core output.argIds output.unit.args)
  | _, _ => none

private def acceptedAllFormsArgs? : Option (List Lara.Support.SupportTerm) :=
  match Lara.Surface.assemble surfaceEnv allFormsInput with
  | .ok output => some output.unit.args
  | .error _ => none

private theorem captured_naive_bypass_args_eq_accepted :
    capturedNaiveBypassArgs? = acceptedAllFormsArgs? := by
  native_decide

private theorem captured_naive_bypass_unit_eq_accepted :
    capturedNaiveBypassUnit? = acceptedAllFormsUnit? := by
  have hargs := captured_naive_bypass_args_eq_accepted
  unfold capturedNaiveBypassArgs? acceptedAllFormsArgs? at hargs
  unfold capturedNaiveBypassUnit? acceptedAllFormsUnit?
  cases hassemble : Lara.Surface.assemble surfaceEnv allFormsInput with
  | error error => simp
  | ok output =>
      cases hcore : capturedNaiveExplicitCore? with
      | none => simp [hassemble, hcore] at hargs
      | some core =>
          simp only [hassemble, hcore, Option.some.injEq] at hargs
          simp [hargs]


example :
    ¬ ∃ output, Lara.Surface.Checks surfaceEnv capturedNamedBinderInput output := by
  rintro ⟨output, h⟩
  have hfalse : Lara.Surface.namedCertificatesWellFormedB
      capturedNamedBinderInput.program capturedNamedBinderInput.policy = false := by
    native_decide
  have htrue := (Lara.Surface.namedCertificatesWellFormedB_iff
      capturedNamedBinderInput.program capturedNamedBinderInput.policy).mpr
    h.supported.named_certs_wf
  rw [hfalse] at htrue
  cases htrue

example :
    ∃ output bypassUnit checked,
      Lara.Surface.assemble surfaceEnv allFormsInput = .ok output ∧
      capturedNaiveBypassUnit? = some bypassUnit ∧
      bypassUnit = output.unit ∧
      Lara.Check.Unit.checkUnit output.gamma surfaceEnv.registry output.ground bypassUnit =
        .ok checked := by
  obtain ⟨output, hchecks⟩ := allForms_checks
  have hassemble := Lara.Surface.assemble_complete _ _ _ hchecks
  obtain ⟨checked, hchecked⟩ := hchecks.core.checkUnit_complete
  have hunit : capturedNaiveBypassUnit? = some output.unit := by
    rw [captured_naive_bypass_unit_eq_accepted]
    simp [acceptedAllFormsUnit?, hassemble]
  exact ⟨output, output.unit, checked, hassemble, hunit, rfl, hchecked⟩

/-! ### Task 5: production-ordered pure elaboration -/

private structure ResolvedAttackVector where
  kind : String
  source : Lara.Support.SupportTerm
  target : Lara.Support.SupportTerm
  position : Lara.Attack.Pos
deriving DecidableEq

private def resolvedAttackVector : Lara.Attack.Attack → ResolvedAttackVector
  | .rebut source target =>
      ⟨"rebut", source, target, []⟩
  | .undercut source target position =>
      ⟨"undercut", source, target, position⟩
  | .undermine source target position =>
      ⟨"undermine", source, target, position⟩

private theorem resolvedAttackVector_injective :
    Function.Injective resolvedAttackVector := by
  intro left right h
  cases left <;> cases right <;>
    simp_all [resolvedAttackVector]

private def claimVector :
    PropId × Lara.Grounded.Claim → String × List Nat × List Nat
  | (id, claim) => (id.val, claim.support, claim.holes)

private def obligationVector :
    ArgId × List ObligationId → String × List String
  | (id, obligations) => (id.val, obligations.map (·.val))

private def questionVector :
    ArgId × List Lara.Support.QuestionId → String × List String
  | (id, questions) => (id.val, questions.map (·.name))

private structure ElaborationVector where
  semanticProgram : Program
  argIds : List String
  coreArgs : List Lara.Support.SupportTerm
  unitSigma : Lara.Sigma.Sigma
  unitAttacks : List ResolvedAttackVector
  resolvedAttacks : List ResolvedAttackVector
  claims : List (String × List Nat × List Nat)
  authoredObligations : List (String × List String)
  openQuestions : List (String × List String)
  ground : List Lara.Atom
deriving DecidableEq

private def elaborationVector
    (output : Lara.Surface.Elaborated Lara.Driver.dcanon) :
    ElaborationVector :=
  { semanticProgram := output.semanticProgram
    argIds := output.argIds.map (·.val)
    coreArgs := output.unit.args
    unitSigma := output.unit.sigma
    unitAttacks := output.unit.atts.map resolvedAttackVector
    resolvedAttacks := output.resolvedAttacks.map resolvedAttackVector
    claims := output.claims.map claimVector
    authoredObligations := output.authoredObligations.map obligationVector
    openQuestions := output.openQuestions.map questionVector
    ground := output.ground }

private theorem map_injective_of_injective {α β : Type}
    {f : α → β} (hf : Function.Injective f) :
    Function.Injective (List.map f) := by
  intro left
  induction left with
  | nil =>
      intro right h
      cases right <;> simp_all
  | cons head tail ih =>
      intro right h
      cases right with
      | nil => simp at h
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at h
          cases hf h.1
          cases ih h.2
          rfl

private theorem idValue_injective :
    Function.Injective (fun id : ArgId => id.val) := by
  intro left right h
  cases left
  cases right
  simp_all

private theorem obligationIdValue_injective :
    Function.Injective (fun id : ObligationId => id.val) := by
  intro left right h
  cases left
  cases right
  simp_all

private theorem questionIdValue_injective :
    Function.Injective (fun id : Lara.Support.QuestionId => id.name) := by
  intro left right h
  cases left
  cases right
  simp_all

private theorem claimVector_injective :
    Function.Injective claimVector := by
  intro left right h
  rcases left with ⟨⟨leftId⟩, ⟨leftSupport, leftHoles⟩⟩
  rcases right with ⟨⟨rightId⟩, ⟨rightSupport, rightHoles⟩⟩
  simp [claimVector] at h
  simp_all

private theorem obligationVector_injective :
    Function.Injective obligationVector := by
  intro left right h
  rcases left with ⟨leftId, leftObligations⟩
  rcases right with ⟨rightId, rightObligations⟩
  simp only [obligationVector, Prod.mk.injEq] at h
  have hid := idValue_injective h.1
  have hobligations := map_injective_of_injective
    obligationIdValue_injective h.2
  simp_all

private theorem questionVector_injective :
    Function.Injective questionVector := by
  intro left right h
  rcases left with ⟨leftId, leftQuestions⟩
  rcases right with ⟨rightId, rightQuestions⟩
  simp only [questionVector, Prod.mk.injEq] at h
  have hid := idValue_injective h.1
  have hquestions := map_injective_of_injective
    questionIdValue_injective h.2
  simp_all

private theorem elaborated_eq_of_vector
    {left right : Lara.Surface.Elaborated Lara.Driver.dcanon}
    (hgamma : left.gamma = right.gamma)
    (hpolicy : left.unit.policy = right.unit.policy)
    (hvector : elaborationVector left = elaborationVector right) :
    left = right := by
  have hcoreArgs : left.unit.args = right.unit.args :=
    congrArg ElaborationVector.coreArgs hvector
  have hunitSigma : left.unit.sigma = right.unit.sigma :=
    congrArg ElaborationVector.unitSigma hvector
  have hargIds : left.argIds = right.argIds :=
    map_injective_of_injective idValue_injective
      (congrArg ElaborationVector.argIds hvector)
  have hunitAttacks : left.unit.atts = right.unit.atts :=
    map_injective_of_injective resolvedAttackVector_injective
      (congrArg ElaborationVector.unitAttacks hvector)
  have hresolvedAttacks : left.resolvedAttacks = right.resolvedAttacks :=
    map_injective_of_injective resolvedAttackVector_injective
      (congrArg ElaborationVector.resolvedAttacks hvector)
  have hclaims : left.claims = right.claims :=
    map_injective_of_injective claimVector_injective
      (congrArg ElaborationVector.claims hvector)
  have hobligations : left.authoredObligations = right.authoredObligations :=
    map_injective_of_injective obligationVector_injective
      (congrArg ElaborationVector.authoredObligations hvector)
  have hquestions : left.openQuestions = right.openQuestions :=
    map_injective_of_injective questionVector_injective
      (congrArg ElaborationVector.openQuestions hvector)
  have hunit : left.unit = right.unit := by
    calc
      left.unit =
          ⟨left.unit.sigma, left.unit.policy, left.unit.args, left.unit.atts⟩ := by
        cases left.unit
        rfl
      _ = ⟨right.unit.sigma, right.unit.policy, right.unit.args,
          right.unit.atts⟩ := by
        rw [hunitSigma, hpolicy, hcoreArgs, hunitAttacks]
      _ = right.unit := by
        cases right.unit
        rfl
  cases left
  cases right
  simp_all [elaborationVector]

private def manualExplicitCore : Lara.Support.SupportTerm :=
  .inst (Lara.Surface.toSupportRuleId ruleMainId)
    [(Lara.Surface.toSupportParam x, .num "7")]
    [ .inst (Lara.Surface.toSupportRuleId ruleNestedId)
        [(Lara.Surface.toSupportParam y, .num "7")]
        [.leaf (Lara.Surface.toSupportLeafId proofLeaf)] [] []
        (.cert
          (Lara.Surface.toSupportBackendId ⟨"nd"⟩ 1)
          (Lara.Surface.toSupportTheoryDigest ⟨"theory"⟩)
          ⟨.list
            [ .atom "app"
            , .list
                [ .atom "lam"
                , .list [.atom "atom", .atom "1:A5:score1:L1:16:1:N1:7"]
                , .list [.atom "hyp", .atom "0"]
                ]
            , .list [.atom "hyp", .atom "0"]
            ]⟩) ]
    [(Lara.Surface.toSupportQuestionId questionId,
      .leaf (Lara.Surface.toSupportLeafId proofLeaf))]
    [] .none

private def manualInferredCore : Lara.Support.SupportTerm :=
  .inst (Lara.Surface.toSupportRuleId ruleMainId)
    [(Lara.Surface.toSupportParam x, .num "7")]
    [.leaf (Lara.Surface.toSupportLeafId proofLeaf)]
    [(Lara.Surface.toSupportQuestionId questionId, manualExplicitCore)] [] .none

private def manualProCore : Lara.Support.SupportTerm :=
  .inst (Lara.Surface.toSupportRuleId verdictRuleId)
    [(Lara.Surface.toSupportParam y, .num "1")]
    [.leaf (Lara.Surface.toSupportLeafId verdictProLeaf)] [] [] .none

private def manualConCore : Lara.Support.SupportTerm :=
  .inst (Lara.Surface.toSupportRuleId verdictRuleId)
    [(Lara.Surface.toSupportParam y, .num "0")]
    [.leaf (Lara.Surface.toSupportLeafId verdictConLeaf)] [] [] .none

private def manualAllFormsArgs : List Lara.Support.SupportTerm :=
  [manualExplicitCore, manualInferredCore, manualProCore, manualConCore]

private def manualAllFormsAttacks : List Lara.Attack.Attack :=
  [ .rebut manualProCore manualConCore
  , .undercut manualProCore manualInferredCore
      [.ques (Lara.Surface.toSupportQuestionId questionId)]
  , .undermine manualProCore manualConCore [.prem 0]
  ]

private def manualAllFormsUnit : Lara.Unit :=
  { sigma := surfaceSigma
    policy := Lara.Surface.toCorePolicy allFormsPolicy
    args := manualAllFormsArgs
    atts := manualAllFormsAttacks }

private def manualAllFormsGround : List Lara.Atom :=
  [ atom "binding" [systemA, systemB, quality, dataset, .num "7", .num "5"]
  , atom "score" [.num "7"]
  , atom "verdict" [.num "1"]
  , atom "verdict" [.num "0"]
  , atom "score" [.num "7"]
  , atom "score" [.num "1"]
  ]

private def manualAllFormsClaims :
    List (PropId × Lara.Grounded.Claim) :=
  [ (claimMain, { support := [0], holes := [] })
  , (claimComparison, { support := [1], holes := [] })
  ]

private def manualAllFormsElaborated :
    Lara.Surface.Elaborated Lara.Driver.dcanon :=
  { gamma := Lara.Surface.surfaceGamma Lara.Driver.dcanon allFormsPolicy
      explicitComparisonProgram
    ground := manualAllFormsGround
    unit := manualAllFormsUnit
    claims := manualAllFormsClaims
    argIds := [argExplicit, argInferred, argPro, argCon]
    authoredObligations :=
      [(argExplicit, []), (argInferred, []), (argPro, []), (argCon, [])]
    openQuestions :=
      [(argExplicit, []), (argInferred, []), (argPro, []), (argCon, [])]
    resolvedAttacks := manualAllFormsAttacks
    semanticProgram := explicitComparisonProgram }

/-- Every finite field of the manually constructed carrier is exact. -/
private theorem allForms_elaboration_data_exact :
    (match Lara.Surface.elaborate surfaceEnv allFormsInput with
      | .error _ => false
      | .ok output =>
          decide (elaborationVector output =
            elaborationVector manualAllFormsElaborated)) = true := by
  native_decide

/-- The production elaborator returns the complete manually constructed carrier,
including the environment function and core policy. -/
private theorem allForms_elaboration_exact :
    Lara.Surface.elaborate surfaceEnv allFormsInput =
      .ok manualAllFormsElaborated := by
  obtain ⟨output, hchecks⟩ := allForms_checks
  have helaborate :=
    Lara.Surface.elaborate_complete surfaceEnv allFormsInput output hchecks
  have hdata := allForms_elaboration_data_exact
  rw [helaborate] at hdata
  have hvector :
      elaborationVector output =
        elaborationVector manualAllFormsElaborated :=
    of_decide_eq_true hdata
  have hsemantic :
      output.semanticProgram = manualAllFormsElaborated.semanticProgram :=
    congrArg ElaborationVector.semanticProgram hvector
  have hgamma : output.gamma = manualAllFormsElaborated.gamma := by
    calc
      output.gamma =
          Lara.Surface.surfaceGamma Lara.Driver.dcanon allFormsPolicy
            output.semanticProgram :=
        hchecks.gamma.symm
      _ = Lara.Surface.surfaceGamma Lara.Driver.dcanon allFormsPolicy
            manualAllFormsElaborated.semanticProgram :=
        congrArg
          (Lara.Surface.surfaceGamma Lara.Driver.dcanon allFormsPolicy)
          hsemantic
      _ = manualAllFormsElaborated.gamma := rfl
  have hpolicy : output.unit.policy = manualAllFormsElaborated.unit.policy := by
    calc
      output.unit.policy = Lara.Surface.toCorePolicy allFormsPolicy :=
        hchecks.unitPolicy.symm
      _ = manualAllFormsElaborated.unit.policy := rfl
  exact helaborate.trans
    (congrArg Except.ok
      (elaborated_eq_of_vector hgamma hpolicy hvector))

private theorem manualAllForms_checks :
    Lara.Surface.Checks surfaceEnv allFormsInput manualAllFormsElaborated := by
  obtain ⟨output, hchecks⟩ := allForms_checks
  have helaborate :=
    Lara.Surface.elaborate_complete surfaceEnv allFormsInput output hchecks
  have outputEq : output = manualAllFormsElaborated :=
    Except.ok.inj (helaborate.symm.trans allForms_elaboration_exact)
  simpa [outputEq] using hchecks

/-- The exact fixture also exposes the canonical execution alignment carried by
the accepted audited result. -/
example :
    ∃ result,
      Lara.Surface.elaborateWithAudit surfaceEnv allFormsInput = .ok result ∧
      result.output = manualAllFormsElaborated ∧
      Lara.Surface.ElaborationAlignment surfaceEnv allFormsInput result := by
  cases hrun :
      Lara.Surface.elaborateWithAudit surfaceEnv allFormsInput with
  | error error =>
      have hexact := allForms_elaboration_exact
      simp only [Lara.Surface.elaborate, hrun, Except.map] at hexact
      cases hexact
  | ok result =>
      have hexact := allForms_elaboration_exact
      have houtput : result.output = manualAllFormsElaborated := by
        simpa only [Lara.Surface.elaborate, hrun, Except.map,
          Except.ok.injEq] using hexact
      have halignment :=
        Lara.Surface.elaborateWithAudit_alignment hrun
      exact ⟨result, rfl, houtput, halignment⟩

/-- A closed successful all-forms run consumes the genuine public theorem
under the simultaneous non-identity multi-namespace renaming. -/
example : ∃ target,
    Lara.Surface.elaborateWithAudit multiNamespaceElaborationEnv
      ⟨Lara.Surface.Binding.renameProgram multiNamespaceRenaming
          allFormsProgram,
        Lara.Surface.Binding.renamePolicy multiNamespaceRenaming
          allFormsPolicy⟩ = .ok target := by
  have successful : Lara.Surface.exceptIsOk
      (Lara.Surface.elaborateWithAudit multiNamespaceElaborationEnv
        allFormsInput) = true := by
    native_decide
  obtain ⟨source, concreteAudit⟩ :=
    (Lara.Surface.exceptIsOk_iff).mp successful
  have transported := Lara.Surface.Renaming.global_renaming_equivariant
    multiNamespaceRenaming_sound multiNamespaceElaborationEnv_sound
    concreteAudit
  exact ⟨transported.choose, transported.choose_spec.1⟩

example :
    (match Lara.Surface.elaborateWithAudit surfaceEnv allFormsInput with
      | .error _ => false
      | .ok result =>
          decide (result.declared.admission.audit =
            { leaves :=
                [(Lara.Surface.toSupportLeafId resultLeaf,
                    [.group "reported-quality"]),
                  (Lara.Surface.toSupportLeafId baselineLeaf,
                    [.group "reported-quality"])]
              args := ["comparison-recheck", "comparison-bridge-arg"]
              attacks := [] })) = true := by
  native_decide

/-- The literal kernel certificate and complete core tree are exactly what the
per-argument fold lowers from the valid source certificate. -/


example :
    Lara.Surface.lowerToSupportTerm surfaceEnv allFormsProgram
        allFormsPolicy [] substitutedExplicitTerm =
      some manualExplicitCore := by
  native_decide

/-- Pass-specific failures retain their production attribution. -/
example :
    Lara.Surface.errorOf?
        (Lara.Surface.elaborate surfaceEnv wrongBridgeConclusionInput) =
      some (.invalidComparison claimComparison) := by
  native_decide

example :
    Lara.Surface.errorOf?
        (Lara.Surface.elaborate surfaceEnv unboundInferenceParameterInput) =
      some (.invalidInferredArgument ⟨"arg-unbound"⟩) := by
  native_decide

example :
    Lara.Surface.errorOf?
        (Lara.Surface.elaborate surfaceEnv capturedNamedBinderInput) =
      some (.invalidNamedCertificate argExplicit) := by
  native_decide

example :
    Lara.Surface.errorOf?
        (Lara.Surface.elaborate surfaceEnv unresolvedAttackPathInput) =
      some (.invalidSurfaceAttack argInferred argExplicit) := by
  native_decide

/-- An invalid attack authored against a generated argument is resolved before
admission can prune that argument. -/
private def prunedEndpointAttackInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with
      decls := allFormsProgram.decls ++
        [.attack (.undercut ⟨"comparison-recheck"⟩ argExplicit
          [.name "no-such-slot"])] },
    allFormsPolicy⟩

example :
    Lara.Surface.errorOf?
        (Lara.Surface.elaborate surfaceEnv prunedEndpointAttackInput) =
      some (.invalidSurfaceAttack ⟨"comparison-recheck"⟩ argExplicit) := by
  native_decide

/-- Attack reconstruction also precedes the R8 rejection pass. -/
private def attackAndAdmissionRejectedInput : Lara.Surface.Input :=
  ⟨unresolvedAttackPathInput.program, admissionRejectedInput.policy⟩

example :
    Lara.Surface.errorOf?
        (Lara.Surface.elaborate surfaceEnv attackAndAdmissionRejectedInput) =
      some (.invalidSurfaceAttack argInferred argExplicit) := by
  native_decide

example :
    Lara.Surface.errorOf?
        (Lara.Surface.elaborate surfaceEnv admissionRejectedInput) =
      some (.admissionRejected proofLeaf) := by
  native_decide

/-- Pure elaboration intentionally stops before core support checking. -/
example :
    Lara.Surface.exceptIsOk
        (Lara.Surface.elaborate surfaceEnv invalidCoreSupportInput) = true := by
  native_decide


/-! ### Task 6: necessity of the correctness hypotheses -/

/-- Necessity witness for `elaborate_reflects`' supported-fragment freshness:
dropping generated-ID freshness makes the comparison pass reject the later
colliding block. -/
theorem necessity_generated_ids_fresh :
    Lara.Surface.expandComparisons allFormsPolicy laterGeneratedCollisionProgram =
      .error (.invalidComparison ⟨"claim-comparison-later"⟩) := by
  rfl

/-- Necessity witness for unambiguous premise resolution in
`elaborate_reflects`: two prior arguments with the same authored reference make
the inferred argument inadmissible. -/
example :
    Lara.Surface.inferredArgsWellFormedB ambiguousInferenceReferenceInput.program
      ambiguousInferenceReferenceInput.policy = false := by
  native_decide

/-- Necessity witness for named-certificate capture freedom in
`alpha_elaboration_invariant`: the captured binder is rejected even though
naive de Bruijn lowering could produce accepted core data. -/
example :
    Lara.Surface.errorOf? (Lara.Surface.check surfaceEnv capturedNamedBinderInput) =
      some (.invalidNamedCertificate argExplicit) := by
  native_decide

private def wrongComparisonPolarityInput : Lara.Surface.Input :=
  ⟨allFormsProgram,
    { allFormsPolicy with
      measurands := [⟨⟨"quality"⟩, .num, some .lowerIsBetter⟩] }⟩

/-- Necessity witness for the comparison-polarity hypothesis used by
`elaborate_reflects`: a higher-is-better scheme cannot elaborate a
lower-is-better measurand. -/
example :
    Lara.Surface.errorOf?
        (Lara.Surface.elaborate surfaceEnv wrongComparisonPolarityInput) =
      some (.invalidComparison claimComparison) := by
  native_decide

private def duplicateAttackedArgumentInput : Lara.Surface.Input :=
  ⟨{ allFormsProgram with decls := allFormsProgram.decls ++ [.arg proArgument] },
    allFormsPolicy⟩

/-- Necessity witness for argument-ID uniqueness before attack indexing in
`elaborate_reflects`: duplicating the attacked source argument prevents a
unique endpoint index from being constructed. -/
example :
    Lara.Surface.errorOf?
        (Lara.Surface.elaborate surfaceEnv duplicateAttackedArgumentInput) =
      some (.duplicateArgId argPro) := by
  native_decide

/-- Necessity witness for `elaborate_reflects`' successful core-check
hypothesis: a surface-supported argument whose premise support is outside the
rule's accepted carrier elaborates, but the core support checker rejects it. -/
example :
    Lara.Surface.exceptIsOk
        (Lara.Surface.elaborate surfaceEnv invalidCoreSupportInput) = true ∧
      Lara.Surface.errorOf? (Lara.Surface.check surfaceEnv invalidCoreSupportInput) =
        some .unsupported := by
  constructor <;> native_decide

/-! ### Task 7: direct surface observation -/

/-- The accepted all-forms fixture computes the same claim observation directly
from its retained surface argument order and after checked compilation, for
every shipped extension semantics. -/
example :
    ∃ output checked, ∃ hchecks : Lara.Surface.Checks surfaceEnv allFormsInput output,
      Lara.Check.Unit.checkUnit output.gamma surfaceEnv.registry
          output.ground output.unit = .ok checked ∧
      Lara.Surface.observe Lara.Semantics.groundedSem hchecks claimMain =
        (Lara.Surface.coreClaim? output claimMain).map
          (Lara.Semantics.observe Lara.Semantics.groundedSem
            (Lara.Compile.checkedAF checked.program)) ∧
      Lara.Surface.observe Lara.Semantics.completeSem hchecks claimMain =
        (Lara.Surface.coreClaim? output claimMain).map
          (Lara.Semantics.observe Lara.Semantics.completeSem
            (Lara.Compile.checkedAF checked.program)) ∧
      Lara.Surface.observe Lara.Semantics.preferredSem hchecks claimMain =
        (Lara.Surface.coreClaim? output claimMain).map
          (Lara.Semantics.observe Lara.Semantics.preferredSem
            (Lara.Compile.checkedAF checked.program)) ∧
      Lara.Surface.observe Lara.Semantics.stableSem hchecks claimMain =
        (Lara.Surface.coreClaim? output claimMain).map
          (Lara.Semantics.observe Lara.Semantics.stableSem
            (Lara.Compile.checkedAF checked.program)) ∧
      Lara.Surface.observe Lara.Semantics.semiStableSem hchecks claimMain =
        (Lara.Surface.coreClaim? output claimMain).map
          (Lara.Semantics.observe Lara.Semantics.semiStableSem
            (Lara.Compile.checkedAF checked.program)) := by
  obtain ⟨output, hchecks⟩ := allForms_checks
  obtain ⟨checked, hchecked⟩ :=
    hchecks.core.checkUnit_complete
  refine ⟨output, checked, hchecks, hchecked, ?_, ?_, ?_, ?_, ?_⟩
  · exact Lara.Surface.observe_grounded_coherent hchecks hchecked claimMain
  · exact Lara.Surface.observe_complete_coherent hchecks hchecked claimMain
  · exact Lara.Surface.observe_preferred_coherent hchecks hchecked claimMain
  · exact Lara.Surface.observe_stable_coherent hchecks hchecked claimMain
  · exact Lara.Surface.observe_semiStable_coherent hchecks hchecked claimMain

/-- The direct all-forms computation reaches the defeated arm under each of
the five shipped semantics: the undercut covers the retained explicit
subargument supporting the claim. The optional claim boundary is preserved. -/
example :
    Lara.Surface.observe Lara.Semantics.groundedSem manualAllForms_checks claimMain =
        some (.observed .defeated) ∧
    Lara.Surface.observe Lara.Semantics.completeSem manualAllForms_checks claimMain =
        some (.observed .defeated) ∧
    Lara.Surface.observe Lara.Semantics.preferredSem manualAllForms_checks claimMain =
        some (.observed .defeated) ∧
    Lara.Surface.observe Lara.Semantics.stableSem manualAllForms_checks claimMain =
        some (.observed .defeated) ∧
    Lara.Surface.observe Lara.Semantics.semiStableSem manualAllForms_checks claimMain =
        some (.observed .defeated) := by
  native_decide

/-- Missing claim lookup remains absent on both independently defined sides;
it is never reclassified as an empty-support gap. -/
example :
    Lara.Surface.directClaim manualAllForms_checks ⟨"missing-claim"⟩ = none ∧
      Lara.Surface.coreClaim? manualAllFormsElaborated ⟨"missing-claim"⟩ = none ∧
      Lara.Surface.observe Lara.Semantics.groundedSem manualAllForms_checks
          ⟨"missing-claim"⟩ = none := by
  native_decide

private def allFormsCheckedResult :=
  Lara.Check.Unit.checkUnit manualAllFormsElaborated.gamma surfaceEnv.registry
    manualAllFormsElaborated.ground manualAllFormsElaborated.unit

private theorem allForms_checked_result_is_ok :
    allFormsCheckedResult.isOk = true := by
  native_decide

private def allFormsChecked :
    Lara.Unit.CheckedUnit Lara.Driver.dcanon manualAllFormsElaborated.gamma
      (Lara.Support.certOkOf surfaceEnv.registry) :=
  Lara.Check.Unit.okValue
    (Lara.Check.Unit.exists_ok_of_isOk allForms_checked_result_is_ok)

/-- The independently compiled all-forms carrier computes the same five
concrete observations. -/
example :
    (Lara.Surface.coreClaim? manualAllFormsElaborated claimMain).map
        (Lara.Semantics.observe Lara.Semantics.groundedSem
          (Lara.Compile.checkedAF allFormsChecked.program)) =
          some (.observed .defeated) ∧
    (Lara.Surface.coreClaim? manualAllFormsElaborated claimMain).map
        (Lara.Semantics.observe Lara.Semantics.completeSem
          (Lara.Compile.checkedAF allFormsChecked.program)) =
          some (.observed .defeated) ∧
    (Lara.Surface.coreClaim? manualAllFormsElaborated claimMain).map
        (Lara.Semantics.observe Lara.Semantics.preferredSem
          (Lara.Compile.checkedAF allFormsChecked.program)) =
          some (.observed .defeated) ∧
    (Lara.Surface.coreClaim? manualAllFormsElaborated claimMain).map
        (Lara.Semantics.observe Lara.Semantics.stableSem
          (Lara.Compile.checkedAF allFormsChecked.program)) =
          some (.observed .defeated) ∧
    (Lara.Surface.coreClaim? manualAllFormsElaborated claimMain).map
        (Lara.Semantics.observe Lara.Semantics.semiStableSem
          (Lara.Compile.checkedAF allFormsChecked.program)) =
          some (.observed .defeated) := by
  native_decide

/-! A stable-no-extension surface fixture.  The extra authored contrary and
self-rebut make `arg-pro` self-attacking.  No extension can contain it, while no
other argument attacks it, so the stable enumeration is empty. -/

private def stableNonePolicy : Policy :=
  { allFormsPolicy with
    contraries := allFormsPolicy.contraries ++
      [⟨atomPat "verdict" [.lit (.num "1")],
        atomPat "verdict" [.lit (.num "1")]⟩] }

private def stableNoneProgram : Program :=
  { allFormsProgram with
    decls := allFormsProgram.decls ++ [.attack (.rebut argPro argPro)] }

private def stableNoneInput : Lara.Surface.Input :=
  ⟨stableNoneProgram, stableNonePolicy⟩

private def stableNoneSurfaceResult :=
  Lara.Surface.check surfaceEnv stableNoneInput

private theorem stableNone_surface_result_is_ok :
    stableNoneSurfaceResult.isOk = true := by
  native_decide

private def stableNoneOutput : Lara.Surface.Elaborated Lara.Driver.dcanon :=
  stableNoneSurfaceResult.toOption.get (by native_decide)

private theorem stableNone_surface_result_eq :
    Lara.Surface.check surfaceEnv stableNoneInput = .ok stableNoneOutput := by
  cases h : stableNoneSurfaceResult with
  | error error =>
      have hs := stableNone_surface_result_is_ok
      rw [h] at hs
      contradiction
  | ok output =>
      have hoption : stableNoneSurfaceResult.toOption = some output :=
        congrArg Except.toOption h
      have houtput : stableNoneOutput = output := by
        unfold stableNoneOutput
        apply Option.get_of_eq_some
        exact hoption
      simpa [stableNoneSurfaceResult] using
        h.trans (congrArg Except.ok houtput.symm)

private theorem stableNone_checks :
    Lara.Surface.Checks surfaceEnv stableNoneInput stableNoneOutput :=
  Lara.Surface.check_sound _ _ _ stableNone_surface_result_eq

private def stableNoneCheckedResult :=
  Lara.Check.Unit.checkUnit stableNoneOutput.gamma surfaceEnv.registry
    stableNoneOutput.ground stableNoneOutput.unit

private theorem stableNone_checked_result_is_ok :
    stableNoneCheckedResult.isOk = true := by
  native_decide

private def stableNoneChecked :
    Lara.Unit.CheckedUnit Lara.Driver.dcanon stableNoneOutput.gamma
      (Lara.Support.certOkOf surfaceEnv.registry) :=
  Lara.Check.Unit.okValue
    (Lara.Check.Unit.exists_ok_of_isOk stableNone_checked_result_is_ok)

/-- Stable nonexistence is preserved as the dedicated `noExtension`
observation on both sides; it is not collapsed into a local four-state status. -/
example :
    Lara.Surface.observe Lara.Semantics.stableSem stableNone_checks claimMain =
        some .noExtension ∧
    (Lara.Surface.coreClaim? stableNoneOutput claimMain).map
        (Lara.Semantics.observe Lara.Semantics.stableSem
          (Lara.Compile.checkedAF stableNoneChecked.program)) =
        some .noExtension := by
  native_decide

/-- The Task-7 negative witness is executable at the public surface name. -/
example :
    Lara.Semantics.observe Lara.Semantics.groundedSem
        Lara.Observation.oneNoAttack Lara.Surface.unboundedDirectClaim ≠
      Lara.Semantics.observe Lara.Semantics.groundedSem
        Lara.Observation.oneAttacksJunk Lara.Surface.unboundedDirectClaim :=
  Lara.Surface.not_observe_coherent_of_unbounded_support
end Lara.Examples.Surface
