/-
Independent Lean emitter for Task 8 surface conformance.

The concrete files are parsed only by Haskell.  This executable constructs the
matching `Presentation.Program`/`Policy` values directly, runs both the verified
surface checker and elaborator, and computes observations through
`Lara.Semantics.observe` over `Surface.directAF`/`directClaim`.  It never reads
the Haskell output or the golden.

Both fingerprints use the shared Task-8 framing contract: FNV-1a-64 over the
UTF-8 bytes of `s<bytes>:TEXT`, `i<decimal>;`, and
`n<tag-bytes>:TAG<count>[CHILDREN]`.  The AST payload is exactly
`node "input" [Presentation.printProgram p, Presentation.printPolicy q]`.
The core payload independently encodes the semantic Unit with rule binders and
instance substitution keys alpha-normalized to `$0`, `$1`, ... .
-/
import Lara.Examples.Surface
import Lara.PresentationParity

namespace Lara.SurfaceConformance

open Lara
open Lara.Presentation

private def terms (items : List Term) : Terms := items.foldr .cons .nil
private def pats (items : List Pat) : Pats := items.foldr .cons .nil
private def atom (pred : String) (items : List Term) : Atom := .atom pred (terms items)
private def apat (pred : String) (items : List Pat) : AtomPat := ⟨pred, pats items⟩
private def con0 (name : String) : Term := .con name .nil
private def sxChildren (items : List Sx) : SxList := items.foldr .cons .nil
private def node (tag : String) (items : List Sx) : Sx := .node tag (sxChildren items)
private def sts (items : List SupportTerm) : SupportTerms := items.foldr .cons .nil
private def discharges (items : List (QuestionId × SupportTerm)) : Discharges :=
  items.foldr (fun item rest => .cons item.1 item.2 rest) .nil

private def policyId : PolicyId := ⟨"surface-policy"⟩
private def mainId : RuleId := ⟨"main"⟩
private def passId : RuleId := ⟨"pass"⟩
private def verdictId : RuleId := ⟨"verdict-rule"⟩
private def recheckId : RuleId := ⟨"ord-recheck"⟩
private def bridgeId : RuleId := ⟨"comparison-bridge"⟩
private def question : QuestionId := ⟨"cq"⟩
private def evidenceLabel : PremiseLabel := ⟨"evidence"⟩
private def supportLabel : PremiseLabel := ⟨"support"⟩
private def theory : TheoryDigest := ⟨"sha256:theory"⟩

private def entity : TermSort := .decl "Entity"

private def surfaceSigma : Sigma :=
  { sorts := ["Entity"]
    cons :=
      [ ⟨⟨"system-a"⟩, [], entity⟩
      , ⟨⟨"system-b"⟩, [], entity⟩
      , ⟨⟨"quality"⟩, [], entity⟩
      , ⟨⟨"dataset"⟩, [], entity⟩ ]
    preds :=
      [ ⟨⟨"score"⟩, [.num]⟩
      , ⟨⟨"evidence"⟩, [.num]⟩
      , ⟨⟨"reported"⟩, [entity, entity, entity, .num]⟩
      , ⟨⟨"binding"⟩, [entity, entity, entity, entity, .num, .num]⟩
      , ⟨⟨"num_lt"⟩, [.num, .num]⟩
      , ⟨⟨"better"⟩, [entity, entity, entity, entity]⟩
      , ⟨⟨"verdict"⟩, [.num]⟩ ] }

private def mainRule (binder : String := "X") : Rule :=
  let x : Param := ⟨binder⟩
  { id := mainId
    params := [x]
    mode := .strict
    premises := [apat "score" [.var x]]
    premiseLabels := [some evidenceLabel]
    conclusion := apat "score" [.var x]
    allowTrusted := true
    certifiers := [⟨⟨"nd"⟩, 1, theory⟩]
    questions := [] }

private def passRule : Rule :=
  let x : Param := ⟨"X"⟩
  { id := passId
    params := [x]
    mode := .defeasible
    premises := [apat "evidence" [.var x]]
    premiseLabels := [some supportLabel]
    conclusion := apat "score" [.var x]
    allowTrusted := false
    certifiers := []
    questions := [⟨question, apat "score" [.var x], .optional⟩] }

private def verdictRule : Rule :=
  let y : Param := ⟨"Y"⟩
  { id := verdictId
    params := [y]
    mode := .defeasible
    premises := [apat "verdict" [.var y]]
    premiseLabels := []
    conclusion := apat "verdict" [.var y]
    allowTrusted := false
    certifiers := []
    questions := [] }

private def recheckRule (reversed : Bool := false) : Rule :=
  let rs : Param := ⟨"RS"⟩
  let rb : Param := ⟨"RB"⟩
  let rq : Param := ⟨"RQ"⟩
  let rd : Param := ⟨"RD"⟩
  let rrv : Param := ⟨"RRV"⟩
  let rbv : Param := ⟨"RBV"⟩
  { id := recheckId
    params := [rs, rb, rq, rd, rrv, rbv]
    mode := .strict
    premises :=
      [ apat "reported" [.var rs, .var rq, .var rd, .var rrv]
      , apat "reported" [.var rb, .var rq, .var rd, .var rbv] ]
    premiseLabels := []
    conclusion := if reversed then apat "num_lt" [.var rrv, .var rbv]
      else apat "num_lt" [.var rbv, .var rrv]
    allowTrusted := false
    certifiers := [⟨⟨"ord"⟩, 1, theory⟩]
    questions := [] }

private def bridgeRule (reversed : Bool := false) : Rule :=
  let s : Param := ⟨"S"⟩
  let b : Param := ⟨"B"⟩
  let q : Param := ⟨"Q"⟩
  let d : Param := ⟨"D"⟩
  let rv : Param := ⟨"RV"⟩
  let bv : Param := ⟨"BV"⟩
  { id := bridgeId
    params := [s, b, q, d, rv, bv]
    mode := .defeasible
    premises :=
      [ apat "binding" [.var s, .var b, .var q, .var d, .var rv, .var bv]
      , if reversed then apat "num_lt" [.var rv, .var bv]
        else apat "num_lt" [.var bv, .var rv] ]
    premiseLabels := []
    conclusion := apat "better" [.var s, .var b, .var q, .var d]
    allowTrusted := false
    certifiers := []
    questions := [] }

private def surfacePolicy (mainBinder : String := "X")
    (reversed : Bool := false) (prune : Bool := false) : Policy :=
  { id := policyId
    sigma := surfaceSigma
    rules := [mainRule mainBinder, passRule, verdictRule,
      recheckRule reversed, bridgeRule reversed]
    contraries := [⟨apat "verdict" [.lit (.num "1")],
      apat "verdict" [.lit (.num "0")]⟩]
    exceptions := [⟨passId, apat "verdict" [.lit (.num "1")]⟩]
    admission := [((.observed, .user), .admit)] ++
      (if prune then [((.certified, .user), .quarantine)] else [])
    theories := [(theory, [atom "score" [.num "1"]])]
    groupMode := .quarantineOnConflict
    measurands := [⟨⟨"quality"⟩, .num, some .higherIsBetter⟩]
    comparisonSchemes :=
      [⟨.strictlyBetter, .higherIsBetter, recheckId, bridgeId⟩] }

private def binding (rationale : String) : Binding :=
  ⟨"author", rationale, .reviewed⟩

private def ndPayload (binder : String) : Sx :=
  node "app"
    [ node "lam"
        [ .str binder
        , node "prop" [.str "score(7)"]
        , node "hyp" [.str binder] ]
    , node "prem" [.str "evidence"] ]

private def capturedPayload : Sx := ndPayload "evidence"
private def ambiguousPayload : Sx := node "prem" [.str "evidence"]

private def namedCert (payload : Sx) : Assurance :=
  .cert ⟨⟨"nd"⟩, 1, theory, payload⟩

private def explicitRuleTerm (rule : RuleId) (term : Term)
    (discharge : List (QuestionId × SupportTerm) := [])
    (assurance : Assurance := .none) : SupportTerm :=
  .rule rule [(⟨"1"⟩, term)] .nil (discharges discharge) [] assurance

private def leaf (id : String) (proposition : Atom) (kind : LeafKind)
    (provenance : Provenance) (refs : List String := []) : Decl :=
  .leaf ⟨⟨id⟩, proposition, kind, provenance, refs.map (fun ref => ⟨ref⟩)⟩

private def claim (id nl : String) (formal : Atom) (rationale : String) : Decl :=
  .claim ⟨⟨id⟩, nl, formal, binding rationale⟩

private def baseProgram : Program :=
  { artifact := "surface_all_forms"
    digest := ⟨"sha256:surface"⟩
    policy := policyId
    backends := [(⟨"nd"⟩, "1"), (⟨"ord"⟩, "1")]
    valueBindings := [⟨⟨"threshold"⟩, .num "7"⟩]
    decls :=
      [ claim "claim-main" "threshold {threshold}; observed {cell proof}"
          (atom "score" [con0 "threshold"]) "surface witness"
      , claim "claim-pro" "positive verdict café" (atom "verdict" [.num "1"])
          "attack source"
      , leaf "e" (atom "reported" [con0 "system-a", con0 "quality",
          con0 "dataset", .num "7"]) .observed .user ["source/e"]
      , leaf "baseline" (atom "reported" [con0 "system-b", con0 "quality",
          con0 "dataset", .num "5"]) .attested .aiExecuted
      , leaf "binding" (atom "binding" [con0 "system-a", con0 "system-b",
          con0 "quality", con0 "dataset", .num "7", .num "5"])
          .assumed (.checker "checker" "v1")
      , leaf "proof" (atom "score" [.num "7"]) .certified .user ["source/proof"]
      , leaf "pass-proof" (atom "evidence" [.num "7"]) .certified .user
      , leaf "verdict-pro" (atom "verdict" [.num "1"]) .observed .user
      , leaf "verdict-con" (atom "verdict" [.num "0"]) .observed .user
      , .arg ⟨⟨"arg-strict"⟩, .supportsClaim ⟨"claim-main"⟩,
          .explicitTheta (explicitRuleTerm mainId (.num "7") []
            (namedCert (ndPayload "h")))⟩
      , .arg ⟨⟨"arg-pass-explicit"⟩, .supportsClaim ⟨"claim-main"⟩,
          .explicitTheta (explicitRuleTerm passId (.num "7")
            [(question, .leaf ⟨"proof"⟩)])⟩
      , .arg ⟨⟨"arg-pass-inferred"⟩, .supportsClaim ⟨"claim-main"⟩,
          .inferTheta passId [⟨"pass-proof"⟩]
            [(question, ⟨"arg-pass-explicit"⟩)] [] .none⟩
      , .arg ⟨⟨"arg-pro"⟩, .supportsClaim ⟨"claim-pro"⟩,
          .explicitTheta (explicitRuleTerm verdictId (.num "1"))⟩
      , .arg ⟨⟨"arg-con"⟩, .supportsClaim ⟨"claim-con"⟩,
          .explicitTheta (explicitRuleTerm verdictId (.num "0"))⟩
      , .attack (.rebut ⟨"arg-pro"⟩ ⟨"arg-con"⟩)
      , .attack (.undercut ⟨"arg-pro"⟩ ⟨"arg-pass-inferred"⟩ [.name "cq"])
      , .attack (.undermine ⟨"arg-pro"⟩ ⟨"arg-con"⟩ [.index 0])
      , .comparison
          { conclusion := atom "better" [con0 "system-a", con0 "system-b"]
            measurand := ⟨"quality"⟩
            dataset := ⟨"dataset"⟩
            relation := .strictlyBetter
            recheckArg := ⟨"comparison-recheck"⟩
            bridgeArg := ⟨"comparison-bridge-arg"⟩
            result := ⟨"e"⟩
            baseline := ⟨"baseline"⟩
            binding := ⟨"binding"⟩
            claim := ⟨⟨"claim-comparison"⟩,
              "comparison {threshold}; result {cell e}", binding "comparison witness"⟩
            supports := none }
      , .status ⟨"claim-main"⟩ ] }

private def namedProgram (binder : String) (payload : Option Sx := none) : Program :=
  { artifact := if binder == "evidence" then "capture_reject" else "nd_alpha"
    digest := if binder == "evidence" then ⟨"sha256:capture"⟩ else ⟨"sha256:nd-alpha"⟩
    policy := policyId
    backends := [(⟨"nd"⟩, "1")]
    valueBindings := []
    decls :=
      [ claim "claim-main"
          (if binder == "evidence" then "captured binder" else "named binder left")
          (atom "score" [.num "7"])
          (if binder == "evidence" then "negative" else "nd alpha")
      , leaf "proof" (atom "score" [.num "7"]) .certified .user
      , .arg ⟨⟨"arg-strict"⟩, .supportsClaim ⟨"claim-main"⟩,
          .explicitTheta (explicitRuleTerm mainId (.num "7") []
            (namedCert (payload.getD (ndPayload binder))))⟩
      , .status ⟨"claim-main"⟩ ] }

private def ambiguousProgram : Program :=
  { artifact := "ambiguous_premise"
    digest := ⟨"sha256:ambiguous"⟩
    policy := policyId
    backends := [(⟨"nd"⟩, "1")]
    valueBindings := []
    decls :=
      [ claim "claim-main" "ambiguous premise" (atom "score" [.num "7"]) "negative"
      , leaf "proof-left" (atom "score" [.num "7"]) .certified .user
      , leaf "proof-right" (atom "score" [.num "7"]) .certified .user
      , .arg ⟨⟨"arg-strict"⟩, .supportsClaim ⟨"claim-main"⟩,
          .explicitTheta (explicitRuleTerm mainId (.num "7") []
            (namedCert ambiguousPayload))⟩
      , .status ⟨"claim-main"⟩ ] }

private def attackProgram : Program :=
  { artifact := "attack_path_reject"
    digest := ⟨"sha256:attack-path"⟩
    policy := policyId
    backends := []
    valueBindings := []
    decls :=
      [ claim "claim-main" "invalid attack path" (atom "score" [.num "7"]) "negative"
      , claim "claim-pro" "positive verdict" (atom "verdict" [.num "1"]) "attack source"
      , leaf "proof" (atom "score" [.num "7"]) .certified .user
      , leaf "pass-proof" (atom "evidence" [.num "7"]) .certified .user
      , leaf "verdict-pro" (atom "verdict" [.num "1"]) .observed .user
      , .arg ⟨⟨"arg-pass-explicit"⟩, .supportsClaim ⟨"claim-main"⟩,
          .explicitTheta (explicitRuleTerm passId (.num "7")
            [(question, .leaf ⟨"proof"⟩)])⟩
      , .arg ⟨⟨"arg-pass-inferred"⟩, .supportsClaim ⟨"claim-main"⟩,
          .inferTheta passId [⟨"pass-proof"⟩]
            [(question, ⟨"arg-pass-explicit"⟩)] [] .none⟩
      , .arg ⟨⟨"arg-pro"⟩, .supportsClaim ⟨"claim-pro"⟩,
          .explicitTheta (explicitRuleTerm verdictId (.num "1"))⟩
      , .attack (.undercut ⟨"arg-pro"⟩ ⟨"arg-pass-inferred"⟩ [.name "missing"]) ] }

private def focusedProgram (artifact digest : String)
    (declarations : List Decl) : Program :=
  { artifact := artifact
    digest := ⟨digest⟩
    policy := policyId
    backends := []
    valueBindings := []
    decls := declarations }

private def observationSigma : Sigma :=
  { sorts := []
    cons := []
    preds := [⟨⟨"score"⟩, [.num]⟩, ⟨⟨"verdict"⟩, [.num]⟩] }

private def observationContrary (source target : String) : Contrary :=
  ⟨apat "verdict" [.lit (.num source)], apat "verdict" [.lit (.num target)]⟩

private def observationPolicy (contraries : List Contrary) : Policy :=
  { id := policyId
    sigma := observationSigma
    rules := [verdictRule]
    contraries := contraries
    exceptions := []
    admission := [((.observed, .user), .admit)]
    theories := []
    groupMode := .quarantineOnConflict
    measurands := []
    comparisonSchemes := [] }

private def observationArg (id claimId value : String) : Decl :=
  .arg ⟨⟨id⟩, .supportsClaim ⟨claimId⟩,
    .explicitTheta (explicitRuleTerm verdictId (.num value))⟩

private def observationGapProgram : Program :=
  focusedProgram "observation_gap" "sha256:observation-gap"
    [ claim "claim-main" "unsupported claim" (atom "score" [.num "7"])
        "gap witness"
    , .status ⟨"claim-main"⟩ ]

private def observationDefeatedProgram : Program :=
  focusedProgram "observation_defeated" "sha256:observation-defeated"
    [ claim "claim-main" "defeated claim" (atom "verdict" [.num "1"])
        "defeated witness"
    , claim "claim-con" "attacking claim" (atom "verdict" [.num "0"])
        "defeated witness"
    , leaf "verdict-pro" (atom "verdict" [.num "1"]) .observed .user
    , leaf "verdict-con" (atom "verdict" [.num "0"]) .observed .user
    , observationArg "arg-pro" "claim-main" "1"
    , observationArg "arg-con" "claim-con" "0"
    , .attack (.rebut ⟨"arg-con"⟩ ⟨"arg-pro"⟩)
    , .status ⟨"claim-main"⟩ ]

private def observationContestedProgram : Program :=
  focusedProgram "observation_contested" "sha256:observation-contested"
    [ claim "claim-main" "contested claim" (atom "verdict" [.num "1"])
        "contested witness"
    , claim "claim-con" "counterclaim" (atom "verdict" [.num "0"])
        "contested witness"
    , leaf "verdict-pro" (atom "verdict" [.num "1"]) .observed .user
    , leaf "verdict-con" (atom "verdict" [.num "0"]) .observed .user
    , observationArg "arg-pro" "claim-main" "1"
    , observationArg "arg-con" "claim-con" "0"
    , .attack (.rebut ⟨"arg-pro"⟩ ⟨"arg-con"⟩)
    , .attack (.rebut ⟨"arg-con"⟩ ⟨"arg-pro"⟩)
    , .status ⟨"claim-main"⟩ ]

private def observationNoExtensionProgram : Program :=
  focusedProgram "observation_no_extension" "sha256:observation-no-extension"
    [ claim "claim-main" "stable no-extension claim"
        (atom "verdict" [.num "1"]) "no-extension witness"
    , leaf "verdict-pro" (atom "verdict" [.num "1"]) .observed .user
    , observationArg "arg-pro" "claim-main" "1"
    , .attack (.rebut ⟨"arg-pro"⟩ ⟨"arg-pro"⟩)
    , .status ⟨"claim-main"⟩ ]

private def conclusionMismatchProgram : Program :=
  focusedProgram "conclusion_mismatch" "sha256:conclusion-mismatch"
    [ claim "claim-main" "conclusion mismatch" (atom "score" [.num "8"])
        "negative"
    , claim "claim-source" "attack source" (atom "verdict" [.num "1"])
        "precedence adversary"
    , leaf "premise" (atom "evidence" [.num "7"]) .observed .user
    , leaf "source" (atom "verdict" [.num "1"]) .observed .user
    , .arg ⟨⟨"arg-mismatch"⟩, .supportsClaim ⟨"claim-main"⟩,
        .inferTheta passId [⟨"premise"⟩] [] [] .none⟩
    , .arg ⟨⟨"arg-source"⟩, .supportsClaim ⟨"claim-source"⟩,
        .inferTheta verdictId [⟨"source"⟩] [] [] .none⟩
    , .attack (.undercut ⟨"arg-source"⟩ ⟨"arg-mismatch"⟩
        [.name "missing-step"]) ]

private def challengeTargetProgram : Program :=
  focusedProgram "challenge_target" "sha256:challenge-target"
    [ leaf "premise" (atom "evidence" [.num "7"]) .observed .user
    , .arg ⟨⟨"arg-challenge"⟩, .challenges (.leaf ⟨"no-such-leaf"⟩),
        .inferTheta passId [⟨"premise"⟩] [] [] .none⟩ ]

private def unknownStatusProgram : Program :=
  focusedProgram "unknown_status" "sha256:unknown-status"
    [ claim "claim-main" "known claim" (atom "score" [.num "7"]) "negative"
    , .status ⟨"no-such-claim"⟩ ]

private def groupLeaf (id : String) (value : String) : Decl :=
  leaf id (atom "score" [.num value]) .observed .user

private def duplicateGroupIdProgram : Program :=
  focusedProgram "duplicate_group" "sha256:duplicate-group"
    [ groupLeaf "e1" "1", groupLeaf "e2" "2", groupLeaf "e3" "3"
    , .group ⟨⟨"repeated-id"⟩, [⟨"e1"⟩, ⟨"e2"⟩]⟩
    , .group ⟨⟨"repeated-id"⟩, [⟨"e2"⟩, ⟨"e3"⟩]⟩
    , .arg ⟨⟨"arg-late"⟩, .supportsClaim ⟨"derived-late"⟩,
        .inferTheta passId [⟨"missing-leaf"⟩] [] [] .none⟩ ]

private def repeatedGroupMemberProgram : Program :=
  focusedProgram "repeated_group_member" "sha256:repeated-group-member"
    [ groupLeaf "e1" "1"
    , .group ⟨⟨"repeated-member"⟩, [⟨"e1"⟩, ⟨"e1"⟩]⟩ ]

private def shortGroupProgram : Program :=
  focusedProgram "short_group" "sha256:short-group"
    [ groupLeaf "e1" "1"
    , .group ⟨⟨"singleton"⟩, [⟨"e1"⟩]⟩ ]

private def danglingGroupMemberProgram : Program :=
  focusedProgram "dangling_group_member" "sha256:dangling-group-member"
    [ groupLeaf "e1" "1"
    , .group ⟨⟨"dangling"⟩, [⟨"e1"⟩, ⟨"no-such-leaf"⟩]⟩ ]

private def admissionPruneOpenProgram : Program :=
  focusedProgram "admission_prune_open" "sha256:admission-prune-open"
    [ claim "claim-main" "admission-pruned open obligation"
        (atom "score" [.num "7"]) "obligation witness"
    , leaf "keep" (atom "evidence" [.num "7"]) .observed .user
    , leaf "drop" (atom "evidence" [.num "7"]) .certified .user
    , .arg ⟨⟨"arg-open"⟩, .supportsClaim ⟨"claim-main"⟩,
        .inferTheta passId [⟨"keep"⟩] [] [⟨"cq"⟩] .none⟩
    , .arg ⟨⟨"arg-pruned"⟩, .supportsClaim ⟨"claim-main"⟩,
        .inferTheta passId [⟨"drop"⟩] [] [⟨"cq"⟩] .none⟩ ]

private structure Case where
  id : String
  programFile : String
  policyFile : String
  expected : String
  input : Lara.Surface.Input

private def caseById (id : String) : Option Case :=
  let base : Lara.Surface.Input := ⟨baseProgram, surfacePolicy⟩
  match id with
  | "all-forms-accept" => some ⟨id, "all-forms.lara", "surface.policy.lara", "accept", base⟩
  | "rule-alpha-left" => some ⟨id, "all-forms.lara", "surface.policy.lara", "accept", base⟩
  | "rule-alpha-right" => some ⟨id, "all-forms.lara", "rule-alpha-right.policy.lara",
      "accept", ⟨baseProgram, surfacePolicy "Z"⟩⟩
  | "nd-alpha-left" => some ⟨id, "nd-alpha-left.lara", "surface.policy.lara", "accept",
      ⟨namedProgram "h", surfacePolicy⟩⟩
  | "nd-alpha-right" => some ⟨id, "nd-alpha-right.lara", "surface.policy.lara", "accept",
      ⟨namedProgram "k", surfacePolicy⟩⟩
  | "comparison-accept" | "cell-interpolation-accept" |
    "named-cert-premise-accept" | "named-formula-accept" =>
      some ⟨id, "all-forms.lara", "surface.policy.lara", "accept", base⟩
  | "capture-reject" => some ⟨id, "capture-reject.lara", "surface.policy.lara",
      "reject:cert-binder-captures-premise", ⟨namedProgram "evidence", surfacePolicy⟩⟩
  | "ambiguous-premise-reject" => some ⟨id, "ambiguous-premise-reject.lara",
      "surface.policy.lara", "reject:ambiguous-premise", ⟨ambiguousProgram, surfacePolicy⟩⟩
  | "comparison-polarity-reject" => some ⟨id, "all-forms.lara",
      "comparison-polarity.policy.lara", "reject:comparison-polarity",
      ⟨baseProgram, surfacePolicy "X" true⟩⟩
  | "attack-path-reject" => some ⟨id, "attack-path-reject.lara", "surface.policy.lara",
      "reject:attack-path", ⟨attackProgram, surfacePolicy⟩⟩
  | "conclusion-mismatch-reject" => some ⟨id, "conclusion-mismatch-reject.lara",
      "surface.policy.lara", "reject:conclusion-mismatch",
      ⟨conclusionMismatchProgram, surfacePolicy⟩⟩
  | "challenge-target-reject" => some ⟨id, "challenge-target-reject.lara",
      "surface.policy.lara", "reject:challenge-target",
      ⟨challengeTargetProgram, surfacePolicy⟩⟩
  | "unknown-status-reject" => some ⟨id, "unknown-status-reject.lara",
      "surface.policy.lara", "reject:unknown-status",
      ⟨unknownStatusProgram, surfacePolicy⟩⟩
  | "duplicate-group-id-reject" => some ⟨id, "duplicate-group-id-reject.lara",
      "surface.policy.lara", "reject:duplicate-group-id",
      ⟨duplicateGroupIdProgram, surfacePolicy⟩⟩
  | "group-repeated-member-reject" => some ⟨id, "group-repeated-member-reject.lara",
      "surface.policy.lara", "reject:group-repeated-member",
      ⟨repeatedGroupMemberProgram, surfacePolicy⟩⟩
  | "group-too-few-members-reject" => some ⟨id, "group-too-few-members-reject.lara",
      "surface.policy.lara", "reject:group-too-few-members",
      ⟨shortGroupProgram, surfacePolicy⟩⟩
  | "group-member-undeclared-reject" =>
      some ⟨id, "group-member-undeclared-reject.lara", "surface.policy.lara",
        "reject:group-member-undeclared", ⟨danglingGroupMemberProgram, surfacePolicy⟩⟩
  | "admission-prune-accept" => some ⟨id, "admission-prune-open.lara",
      "admission-prune.policy.lara", "accept",
      ⟨admissionPruneOpenProgram, surfacePolicy "X" false true⟩⟩
  | "observation-gap" => some ⟨id, "observation-gap.lara",
      "observation-gap.policy.lara", "accept",
      ⟨observationGapProgram, observationPolicy []⟩⟩
  | "observation-defeated" => some ⟨id, "observation-defeated.lara",
      "observation.policy.lara", "accept",
      ⟨observationDefeatedProgram,
        observationPolicy [observationContrary "0" "1"]⟩⟩
  | "observation-contested" => some ⟨id, "observation-contested.lara",
      "observation-contested.policy.lara", "accept",
      ⟨observationContestedProgram,
        observationPolicy [observationContrary "1" "0",
          observationContrary "0" "1"]⟩⟩
  | "observation-no-extension" => some ⟨id, "observation-no-extension.lara",
      "observation-no-extension.policy.lara", "accept",
      ⟨observationNoExtensionProgram,
        observationPolicy [observationContrary "1" "1"]⟩⟩
  | _ => none

private def conformanceEnv : Lara.Surface.Env Lara.Driver.dcanon where
  registry := Lara.Driver.buildRegistry
    [(⟨"sha256:theory"⟩, [atom "score" [.num "1"]])]
  startsIdent := Lara.Examples.Surface.surfaceEnv.startsIdent
  startsIdent_nat_false := Lara.Examples.Surface.surfaceEnv.startsIdent_nat_false
  encodeProp := Lara.Examples.Surface.surfaceEnv.encodeProp

/-- Regression for the production parser shape: explicit `by r(t)` terms use
synthetic positional keys and omit premises until reconstruction. -/
private theorem parser_shallow_base_inferred_guard :
    Surface.inferredArgsWellFormedB baseProgram surfacePolicy = true := by
  native_decide

private theorem parser_shallow_base_certificate_guard :
    Surface.namedCertificatesWellFormedB baseProgram surfacePolicy = true := by
  native_decide

private theorem parser_shallow_base_check_ok :
    Surface.exceptIsOk (Surface.check conformanceEnv ⟨baseProgram, surfacePolicy⟩) = true := by
  native_decide

/-! Canonical framing and FNV-1a-64. -/

mutual
  private def renderSx : Sx → String
    | .str value => "s" ++ toString value.toUTF8.size ++ ":" ++ value
    | .int value => "i" ++ toString value ++ ";"
    | .node tag children =>
        "n" ++ toString tag.toUTF8.size ++ ":" ++ tag ++
          toString (sxListLength children) ++ "[" ++ renderSxList children ++ "]"
  private def renderSxList : SxList → String
    | .nil => ""
    | .cons value rest => renderSx value ++ renderSxList rest
  private def sxListLength : SxList → Nat
    | .nil => 0
    | .cons _ rest => sxListLength rest + 1
end

private def fnv1a64 (bytes : ByteArray) : UInt64 :=
  bytes.foldl (init := 14695981039346656037) fun hash byte =>
    (UInt64.xor hash byte.toUInt64) * 1099511628211

private def leftPad (width : Nat) (char : Char) (value : String) : String :=
  String.ofList (List.replicate (width - value.length) char) ++ value

private def fingerprint (value : Sx) : String :=
  let hash := fnv1a64 (renderSx value).toUTF8
  leftPad 16 '0' (String.ofList (Nat.toDigits 16 hash.toNat))

private def inputFingerprint (input : Lara.Surface.Input) : String :=
  fingerprint (node "input"
    [Presentation.printProgram input.program, Presentation.printPolicy input.policy])

/-! Alpha-normalized semantic core encoding. -/

private def coreMode : Support.Mode → Sx
  | .strict => node "strict" []
  | .defeasible => node "defeasible" []

private def paramIndex (needle : Support.VarId) : List Support.VarId → Nat → Option Nat
  | [], _ => none
  | candidate :: rest, index =>
      if candidate = needle then some index else paramIndex needle rest (index + 1)

private def alphaParam (params : List Support.VarId) (param : Support.VarId) : String :=
  match paramIndex param params 0 with
  | some index => "$" ++ toString index
  | none => param.name

mutual
  private def corePat (params : List Support.VarId) : Support.Pat → Sx
    | .var param => node "v" [.str (alphaParam params param)]
    | .num value => node "lit" [Presentation.sxTerm (.num value)]
    | .str value => node "lit" [Presentation.sxTerm (.str value)]
    | .con symbol arguments => node "con" (.str symbol.name :: corePats params arguments)
  private def corePats (params : List Support.VarId) : Support.Pats → List Sx
    | .nil => []
    | .cons pat rest => corePat params pat :: corePats params rest
end

private def coreAPat (params : List Support.VarId) (pattern : Support.APat) : Sx :=
  node "apat" (.str pattern.pred.name :: corePats params pattern.args)

private def coreCertifier (entry : Support.BackendId × Support.Digest) : Sx :=
  node "cref" [.str entry.1.name, .int (Int.ofNat entry.1.version), .str entry.2.hash]

private def coreQuestion (params : List Support.VarId) (question : Support.Question) : Sx :=
  node "question"
    [ .str question.name.name
    , coreAPat params question.answer
    , Presentation.sxBool question.mandatory ]

private def coreRule (declaration : Policy.RuleDecl) : Sx :=
  let rule := declaration.rule
  let params := rule.params
  node "rule"
    [ .str declaration.id.name
    , coreMode rule.mode
    , Presentation.sxList (fun param => .str (alphaParam params param)) params
    , Presentation.sxList (coreAPat params) rule.premises
    , coreAPat params rule.concl
    , Presentation.sxList (coreQuestion params) rule.questions
    , Presentation.sxBool rule.allowTrusted
    , Presentation.sxList coreCertifier rule.certifiers ]

private def paramsFor (rules : List Policy.RuleDecl) (id : Support.RuleId) :
    List Support.VarId :=
  match rules.find? (fun declaration => decide (declaration.id = id)) with
  | some declaration => declaration.rule.params
  | none => []

private def nativeSx : Support.SExpr → Sx
  | .atom value => .str value
  | .list (.atom tag :: children) => node tag (children.map nativeSx)
  | .list children => node "" (children.map nativeSx)

private def coreAssurance : Support.Assurance → Sx
  | .none => node "none" []
  | .trusted => node "trusted" []
  | .cert backend digest reference =>
      node "cert"
        [ .str backend.name
        , .int (Int.ofNat backend.version)
        , .str digest.hash
        , nativeSx reference.payload ]

mutual
  private def coreTerm (rules : List Policy.RuleDecl) : Support.SupportTerm → Sx
    | .leaf leaf => node "leaf" [.str leaf.name]
    | .inst rule subst premises discharge holes assurance =>
        let params := paramsFor rules rule
        node "inst"
          [ .str rule.name
          , Presentation.sxList
              (Presentation.sxPair
                (fun param => .str (alphaParam params param)) Presentation.sxTerm)
              subst
          , node "l" (coreTerms rules premises)
          , node "l" (coreDischarges rules discharge)
          , Presentation.sxList (fun hole => .str hole.name) holes
          , coreAssurance assurance ]
  private def coreTerms (rules : List Policy.RuleDecl) : List Support.SupportTerm → List Sx
    | [] => []
    | term :: rest => coreTerm rules term :: coreTerms rules rest
  private def coreDischarges (rules : List Policy.RuleDecl) :
      List (Support.QuestionId × Support.SupportTerm) → List Sx
    | [] => []
    | entry :: rest =>
        node "p" [.str entry.1.name, coreTerm rules entry.2] ::
          coreDischarges rules rest
end

private def corePosElem : Attack.PosElem → Sx
  | .prem index => node "prem" [.int (Int.ofNat index)]
  | .ques question => node "ques" [.str question.name]

private def coreAttack (rules : List Policy.RuleDecl) : Attack.Attack → Sx
  | .rebut source target =>
      node "rebut" [coreTerm rules source, coreTerm rules target]
  | .undercut source target position =>
      node "undercut"
        [coreTerm rules source, coreTerm rules target,
          Presentation.sxList corePosElem position]
  | .undermine source target position =>
      node "undermine"
        [coreTerm rules source, coreTerm rules target,
          Presentation.sxList corePosElem position]

private def coreContrary (entry : Support.APat × Support.APat) : Sx :=
  node "contrary" [coreAPat [] entry.1, coreAPat [] entry.2]

private def coreException (entry : Support.RuleId × Support.APat) : Sx :=
  node "exception" [.str entry.1.name, coreAPat [] entry.2]

private def coreUnitSx (unit : Lara.Unit) : Sx :=
  let rules := unit.policy.rules
  node "core"
    [ Presentation.sxSigma unit.sigma
    , Presentation.sxList coreRule rules
    , Presentation.sxList coreContrary unit.policy.defeat.contraries
    , Presentation.sxList coreException unit.policy.defeat.exceptions
    , Presentation.sxList (coreTerm rules) unit.args
    , Presentation.sxList (coreAttack rules) unit.atts ]

private def coreFingerprint (output : Lara.Surface.Elaborated Driver.dcanon) : String :=
  fingerprint (coreUnitSx output.unit)

/-! Human-readable list-cell codec and verified observations. -/

private def hexByte (byte : UInt8) : String :=
  leftPad 2 '0' (String.ofList (Nat.toDigits 16 byte.toNat))

private def safeByte (byte : UInt8) : Bool :=
  let value := byte.toNat
  (0x30 ≤ value && value ≤ 0x39) ||
  (0x41 ≤ value && value ≤ 0x5a) ||
  (0x61 ≤ value && value ≤ 0x7a) ||
  [0x2e, 0x5f, 0x3a, 0x40, 0x2f, 0x2b, 0x7e, 0x2d].contains value

private def percentAtom (value : String) : String :=
  if value == "-" then "%2d"
  else value.toUTF8.foldl (init := "") fun output byte =>
    if safeByte byte then output.push (Char.ofNat byte.toNat)
    else output ++ "%" ++ hexByte byte

private def renderList (values : List String) : String :=
  if values.isEmpty then "-" else String.intercalate "," (values.map percentAtom)

private def idForTerm : List Support.SupportTerm → List ArgId → Support.SupportTerm → Option ArgId
  | term :: terms, id :: ids, target =>
      if term = target then some id else idForTerm terms ids target
  | _, _, _ => none

private def renderPosition : List Attack.PosElem → String
  | [] => ""
  | .prem index :: rest => ":premise:" ++ toString index ++ renderPosition rest
  | .ques question :: rest => ":question:" ++ question.name ++ renderPosition rest

private def renderAttack (output : Lara.Surface.Elaborated Driver.dcanon)
    (attack : Attack.Attack) : Option String := do
  let source ← idForTerm output.unit.args output.argIds attack.source
  let target ← idForTerm output.unit.args output.argIds attack.target
  let kindText := match attack with
    | .rebut _ _ => "rebut"
    | .undercut _ _ _ => "undercut"
    | .undermine _ _ _ => "undermine"
  let position := match attack with
    | .rebut _ _ => ""
    | .undercut _ _ path | .undermine _ _ path => renderPosition path
  some (kindText ++ ":" ++ source.val ++ ":" ++ target.val ++ position)

private def statusText : Grounded.Status → String
  | .gap => "gap"
  | .justified => "justified"
  | .contested => "contested"
  | .defeated => "defeated"

private def observationText : Semantics.ClaimObservation → String
  | .noExtension => "noExtension"
  | .observed status => statusText status

private def semanticsTable : List (String × Semantics.ExtensionSemantics) :=
  [ ("grounded", Semantics.groundedSem)
  , ("complete", Semantics.completeSem)
  , ("preferred", Semantics.preferredSem)
  , ("stable", Semantics.stableSem)
  , ("semi-stable", Semantics.semiStableSem) ]

private def statusIds (program : Program) : List PropId :=
  program.decls.filterMap fun
    | .status id => some id
    | _ => none

private def observationCells (input : Lara.Surface.Input)
    (output : Lara.Surface.Elaborated Driver.dcanon)
    (h : Surface.Checks conformanceEnv input output) : List String :=
  semanticsTable.flatMap fun entry =>
    (statusIds input.program).map fun claimId =>
      entry.1 ++ ":" ++ claimId.val ++ ":" ++
        match Surface.observe entry.2 h claimId with
        | none => "missing"
        | some observation => observationText observation

mutual
  private def coreHoles : Support.SupportTerm → List Support.QuestionId
    | .leaf _ => []
    | .inst _ _ premises discharges holes _ =>
        holes ++ corePremiseHoles premises ++ coreDischargeHoles discharges
  private def corePremiseHoles : List Support.SupportTerm → List Support.QuestionId
    | [] => []
    | premise :: rest => coreHoles premise ++ corePremiseHoles rest
  private def coreDischargeHoles :
      List (Support.QuestionId × Support.SupportTerm) → List Support.QuestionId
    | [] => []
    | discharge :: rest => coreHoles discharge.2 ++ coreDischargeHoles rest
end

private def obligationCells
    (output : Lara.Surface.Elaborated Driver.dcanon) : List String :=
  (output.argIds.zip output.unit.args).flatMap fun entry =>
    (coreHoles entry.2).map fun obligation =>
      entry.1.val ++ ":" ++ obligation.name

private def attackCells (output : Lara.Surface.Elaborated Driver.dcanon) : Option (List String) :=
  output.resolvedAttacks.mapM (renderAttack output)

/-! Manifest validation and table emission. -/

private structure ManifestRow where
  caseId : String
  program : String
  policy : String
  expected : String
  features : List String

private def requiredFeatures : List String :=
  [ "labelled-premise", "named-discharge", "comparison"
  , "value-interpolation", "cell-interpolation", "named-cert-premise"
  , "named-formula", "rule-binder", "nd-binder", "surface-attacks"
  , "capture-rejection", "ambiguous-premise-rejection"
  , "comparison-polarity-rejection", "attack-path-rejection"
  , "conclusion-mismatch-rejection", "challenge-target-rejection"
  , "unknown-status-rejection", "duplicate-group-id-rejection"
  , "group-repeated-member-rejection", "group-too-few-members-rejection"
  , "group-member-undeclared-rejection", "admission-prune", "open-obligation" ]

private def parseManifestRow (line : String) : Except String ManifestRow :=
  match line.splitOn "\t" with
  | [caseId, program, policy, expected, featureText] =>
      let features := featureText.splitOn ","
      if caseId.isEmpty || program.isEmpty || policy.isEmpty || expected.isEmpty ||
          featureText.isEmpty then
        .error "manifest row has an empty cell"
      else if !(features.all (fun feature => requiredFeatures.contains feature)) then
        .error ("unknown feature in case " ++ caseId)
      else if !(decide features.Nodup) then
        .error ("duplicate feature in case " ++ caseId)
      else if !(expected == "accept" || expected.startsWith "reject:") then
        .error ("invalid expected outcome in case " ++ caseId)
      else .ok ⟨caseId, program, policy, expected, features⟩
  | _ => .error "manifest row does not have five columns"

private def parseManifest (contents : String) : Except String (List ManifestRow) := do
  let lines := (contents.splitOn "\n").filter (fun line => !line.isEmpty)
  match lines with
  | [] => .error "empty manifest"
  | header :: records =>
      if header != "case_id\tprogram\tpolicy\texpected\tfeatures" then
        .error "manifest header mismatch"
      else if records.isEmpty then .error "manifest has no cases"
      else do
        let rows ← records.mapM parseManifestRow
        if !(decide (rows.map (·.caseId)).Nodup) then
          .error "duplicate case_id"
        else
          let covered := rows.flatMap (·.features)
          if !(requiredFeatures.all covered.contains) then
            .error "required feature coverage missing"
          else .ok rows

private structure OutputRow where
  caseId : String
  ast : String
  outcome : String
  core : String
  obligations : String
  attacks : String
  observations : String

private def renderOutput (row : OutputRow) : String :=
  String.intercalate "\t"
    [row.caseId, row.ast, row.outcome, row.core, row.obligations,
      row.attacks, row.observations]

mutual
  private def payloadHasBinderFrom (names : List String) : Sx → Bool
    | .node "lam" children =>
        let atNode := match children with
          | .cons (.str binder) _ => names.contains binder
          | _ => false
        atNode || payloadListHasBinderFrom names children
    | .node _ children => payloadListHasBinderFrom names children
    | _ => false
  private def payloadListHasBinderFrom (names : List String) : SxList → Bool
    | .nil => false
    | .cons value rest =>
        payloadHasBinderFrom names value || payloadListHasBinderFrom names rest
end

private def rulePremiseLabelNames (policy : Policy) (ruleId : RuleId) : List String :=
  match Surface.ruleById policy ruleId with
  | none => []
  | some rule => rule.premiseLabels.filterMap (fun label => label.map (·.val))

private def assuranceCapturesLabel (labels : List String) : Assurance → Bool
  | .cert certificate =>
      certificate.backend.val == "nd" && certificate.version == 1 &&
        payloadHasBinderFrom labels certificate.payload
  | _ => false

mutual
  private def termCapturesPremiseLabel (policy : Policy) : SupportTerm → Bool
    | .leaf _ => false
    | .rule ruleId _ premises discharges _ assurance =>
        assuranceCapturesLabel (rulePremiseLabelNames policy ruleId) assurance ||
          termsCapturePremiseLabel policy premises ||
          dischargesCapturePremiseLabel policy discharges
  private def termsCapturePremiseLabel (policy : Policy) : SupportTerms → Bool
    | .nil => false
    | .cons term rest =>
        termCapturesPremiseLabel policy term || termsCapturePremiseLabel policy rest
  private def dischargesCapturePremiseLabel (policy : Policy) : Discharges → Bool
    | .nil => false
    | .cons _ term rest =>
        termCapturesPremiseLabel policy term ||
          dischargesCapturePremiseLabel policy rest
end

private def argumentCapturesPremiseLabel (policy : Policy) (argument : Arg) : Bool :=
  match argument.instantiation with
  | .explicitTheta term => termCapturesPremiseLabel policy term
  | .inferTheta rule _ _ _ assurance =>
      assuranceCapturesLabel (rulePremiseLabelNames policy rule) assurance

private def captureCauseB (input : Lara.Surface.Input) : Bool :=
  input.program.decls.any fun declaration => match declaration with
    | .arg argument => argumentCapturesPremiseLabel input.policy argument
    | _ => false

private def shallowTermHasAmbiguousLeafPremise (program : Program)
    (policy : Policy) : SupportTerm → Bool
  | .rule ruleId positionalTheta .nil _ _ _ =>
      match Surface.ruleById policy ruleId with
      | none => false
      | some rule =>
          if positionalTheta.length != rule.params.length then false
          else
            let theta := rule.params.zip (positionalTheta.map Prod.snd)
            rule.premises.any fun premise =>
              match Surface.instantiateSurfaceAtom theta premise with
              | none => false
              | some ground =>
                  decide (1 < ((Surface.declaredLeaves program).filter fun entry =>
                    Lara.equiv Driver.dcanon entry.2 ground).length)
  | _ => false

private def ambiguousPremiseCauseB (input : Lara.Surface.Input) : Bool :=
  input.program.decls.any fun declaration => match declaration with
    | .arg argument => match argument.instantiation with
      | .explicitTheta term =>
          shallowTermHasAmbiguousLeafPremise input.program input.policy term
      | _ => false
    | _ => false

private def binaryNumLtB : AtomPat → Bool
  | ⟨"num_lt", .cons _ (.cons _ .nil)⟩ => true
  | _ => false

private def flipBinaryNumLt : AtomPat → AtomPat
  | ⟨"num_lt", .cons left (.cons right .nil)⟩ =>
      ⟨"num_lt", .cons right (.cons left .nil)⟩
  | pattern => pattern

private def repairDirectionRule (scheme : ComparisonScheme) (rule : Rule) : Rule :=
  if rule.id = scheme.recheck then
    { rule with conclusion := flipBinaryNumLt rule.conclusion }
  else if rule.id = scheme.bridge then
    { rule with premises := rule.premises.map flipBinaryNumLt }
  else rule

private def comparisonDirectionMismatchForB (program : Program) (policy : Policy)
    (comparison : Comparison) : Bool :=
  match policy.measurands.find? (fun item => decide (item.id = comparison.measurand)) with
  | none => false
  | some measurand => match measurand.polarity with
    | none => false
    | some polarity =>
      match policy.comparisonSchemes.find? (fun scheme =>
          decide (scheme.relation = comparison.relation) &&
            decide (scheme.polarity = polarity)) with
      | none => false
      | some scheme =>
        match Surface.ruleById policy scheme.recheck,
            Surface.ruleById policy scheme.bridge with
        | some recheck, some bridge =>
            binaryNumLtB recheck.conclusion &&
              bridge.premises.any binaryNumLtB &&
              !Surface.comparisonCoreValidB program policy comparison &&
              Surface.comparisonCoreValidB program
                { policy with rules := policy.rules.map (repairDirectionRule scheme) }
                comparison
        | _, _ => false

private def comparisonPolarityCauseB (input : Lara.Surface.Input) : Bool :=
  (Surface.comparisonDecls input.program).any
    (comparisonDirectionMismatchForB input.program input.policy)

private def builtArgIds (input : Lara.Surface.Input) : List ArgId :=
  (Surface.collectProgramArguments input.program input.policy input.program.decls []).map (·.id)

private def attackPathCauseForB (input : Lara.Surface.Input)
    (attack : SurfaceAttack) : Bool :=
  let endpoints := Surface.attackEndpoints attack
  (Surface.argIds input.program).contains endpoints.1 &&
    (Surface.argIds input.program).contains endpoints.2 &&
    (builtArgIds input).contains endpoints.1 &&
    (builtArgIds input).contains endpoints.2 &&
    !Surface.surfaceAttackWellFormedB input.program input.policy attack

private def attackPathCauseB (input : Lara.Surface.Input) : Bool :=
  input.program.decls.any fun declaration => match declaration with
    | .attack attack => attackPathCauseForB input attack
    | _ => false

private def errorTag (input : Lara.Surface.Input) : Surface.Error → Option String
  | .invalidNamedCertificate _ =>
      if captureCauseB input then some "cert-binder-captures-premise" else none
  | .invalidInferredArgument _ =>
      if ambiguousPremiseCauseB input then some "ambiguous-premise" else none
  | .invalidComparison _ =>
      if comparisonPolarityCauseB input then some "comparison-polarity" else none
  | .invalidSurfaceAttack _ _ =>
      if attackPathCauseB input then some "attack-path" else none
  | .conclusionMismatch _ _ => some "conclusion-mismatch"
  | .challengeTargetUndeclared _ => some "challenge-target"
  | .unknownStatusClaim _ => some "unknown-status"
  | .duplicateGroupId _ => some "duplicate-group-id"
  | .groupRepeatedMember _ _ => some "group-repeated-member"
  | .groupTooFewMembers _ => some "group-too-few-members"
  | .groupMemberUndeclared _ _ => some "group-member-undeclared"
  | _ => none

private def adversarialNamedInput : Lara.Surface.Input :=
  ⟨namedProgram "h" (some (node "hyp" [.str "ghost"])), surfacePolicy⟩

/-- An unbound named hypothesis shares the coarse certificate error but is not
the capture boundary. A case-only tagger incorrectly labels this input. -/
private theorem adversarial_named_error_is_not_capture :
    Surface.errorOf? (Surface.check conformanceEnv adversarialNamedInput) =
       some (.invalidNamedCertificate ⟨"arg-strict"⟩) ∧
      (match Surface.errorOf? (Surface.check conformanceEnv adversarialNamedInput) with
       | some error => errorTag adversarialNamedInput error
       | none => none) = none := by
  native_decide

private theorem required_negative_causes_are_structural :
    captureCauseB ⟨namedProgram "evidence", surfacePolicy⟩ = true ∧
    ambiguousPremiseCauseB ⟨ambiguousProgram, surfacePolicy⟩ = true ∧
    comparisonPolarityCauseB ⟨baseProgram, surfacePolicy "X" true⟩ = true ∧
    attackPathCauseB ⟨attackProgram, surfacePolicy⟩ = true := by
  native_decide

private def rejectClassText : Check.RejectClass → String
  | .R1 => "R1" | .R2 => "R2" | .R3 => "R3" | .R4 => "R4"
  | .R5 => "R5" | .R6 => "R6" | .R7 => "R7" | .R9 => "R9"
  | .R10 => "R10" | .R11 => "R11" | .R12 => "R12" | .R13 => "R13"

private def unitErrorText : Check.Unit.UnitError → String
  | .duplicateRule _ => "duplicate-rule"
  | .signature _ => "signature"
  | .scopeViolation _ => "scope"
  | .policyViolation _ => "policy"
  | .program (.duplicateArgument _ _) => "duplicate-argument"
  | .program (.incompleteArgument _ _) => "incomplete-argument"
  | .program (.missingConflict _) => "missing-conflict"
  | .program (.rejection _ error) => rejectClassText error.rejectClass

private def surfaceErrorText : Surface.Error → String
  | .unsupported => "unsupported"
  | .policyMismatch _ _ => "policy-mismatch"
  | .duplicateLeafId _ => "duplicate-leaf"
  | .duplicateArgId _ => "duplicate-arg"
  | .duplicateClaimId _ => "duplicate-claim"
  | .duplicateValueName _ => "duplicate-value"
  | .malformedRuleNamespace _ => "rule-namespace"
  | .invalidValueBinding _ => "value-binding"
  | .invalidComparison _ => "comparison"
  | .invalidInferredArgument _ => "inferred-argument"
  | .invalidNamedCertificate _ => "named-certificate"
  | .conclusionMismatch _ _ => "conclusion-mismatch"
  | .challengeTargetUndeclared _ => "challenge-target"
  | .invalidSurfaceAttack _ _ => "surface-attack"
  | .unknownStatusClaim _ => "unknown-status"
  | .duplicateGroupId _ => "duplicate-group-id"
  | .groupRepeatedMember _ _ => "group-repeated-member"
  | .groupTooFewMembers _ => "group-too-few-members"
  | .groupMemberUndeclared _ _ => "group-member-undeclared"
  | .noncanonicalPremiseLabels _ => "premise-labels"
  | .duplicateAdmissionKey _ _ => "admission-key"
  | .admissionRejected _ => "admission-rejected"

private def validateManifestCase (row : ManifestRow) : Except String Case := do
  let spec ← match caseById row.caseId with
    | some spec => .ok spec
    | none => .error ("unknown case_id: " ++ row.caseId)
  if row.program != spec.programFile then
    .error (row.caseId ++ ": program file disagrees with case definition")
  else if row.policy != spec.policyFile then
    .error (row.caseId ++ ": policy file disagrees with case definition")
  else if row.expected != spec.expected then
    .error (row.caseId ++ ": expected outcome disagrees with case definition")
  else .ok spec

private def evaluateCase (row : ManifestRow) : Except String OutputRow := do
  let spec ← validateManifestCase row
  let ast := inputFingerprint spec.input
  match hchecked : Surface.check conformanceEnv spec.input,
      Surface.elaborate conformanceEnv spec.input with
  | .ok output, .ok _ => do
      if row.expected != "accept" then
        .error (row.caseId ++ ": accepted but manifest expects " ++ row.expected)
      let attacks ← match attackCells output with
        | some cells => .ok cells
        | none => .error (row.caseId ++ ": resolved attack endpoint is absent from argIds")
      .ok
        { caseId := row.caseId
          ast := ast
          outcome := "accept"
          core := coreFingerprint output
          obligations := renderList (obligationCells output)
          attacks := renderList attacks
          observations := renderList (observationCells spec.input output
            (Surface.check_sound conformanceEnv spec.input output hchecked)) }
  | .error checkError, .error elaborateError => do
      if checkError != elaborateError then
        .error (row.caseId ++ ": check/elaborate structural errors differ")
      let tag ← match errorTag spec.input checkError with
        | some tag => .ok tag
        | none => .error (row.caseId ++ ": unexpected structural rejection")
      let outcome := "reject:" ++ tag
      if outcome != row.expected then
        .error (row.caseId ++ ": expected " ++ row.expected ++ " but got " ++ outcome)
      .ok
        { caseId := row.caseId, ast := ast, outcome := outcome, core := "-"
          obligations := "-", attacks := "-", observations := "-" }
  | .ok _, .error _ => .error (row.caseId ++ ": check accepted but elaborate rejected")
  | .error surfaceError, .ok output =>
      match Check.Unit.checkUnit output.gamma conformanceEnv.registry output.ground output.unit with
      | .error error => .error (row.caseId ++ ": check rejected (" ++
          surfaceErrorText surfaceError ++ "/" ++ unitErrorText error ++
          ") but elaborate accepted")
      | .ok _ => .error (row.caseId ++ ": check rejected (" ++
          surfaceErrorText surfaceError ++ ") but direct core check accepted")

private def outputHeader : String :=
  "case_id\tast_fingerprint\toutcome\tcore_fingerprint\tobligations\tattacks\tobservations"

def emitManifest (path : String) : IO _root_.Unit := do
  let contents ← (do
    try IO.FS.readFile (⟨path⟩ : System.FilePath)
    catch _ =>
      IO.eprintln ("surface-conformance: cannot read " ++ path)
      IO.Process.exit 2)
  let rows ← match parseManifest contents with
    | .ok rows => pure rows
    | .error error =>
        IO.eprintln ("surface-conformance: " ++ error)
        IO.Process.exit 1
  let outputs ← match rows.mapM evaluateCase with
    | .ok outputs => pure outputs
    | .error error =>
        IO.eprintln ("surface-conformance: " ++ error)
        IO.Process.exit 1
  IO.println outputHeader
  for output in outputs do IO.println (renderOutput output)

end Lara.SurfaceConformance

def main (args : List String) : IO _root_.Unit :=
  match args with
  | ["--manifest", path] => Lara.SurfaceConformance.emitManifest path
  | _ => do
      IO.eprintln "usage: surface-conformance --manifest PATH"
      IO.Process.exit 2
