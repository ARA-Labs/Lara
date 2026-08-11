/-
Desired-shape witnesses for the result-12 **presentation parity** of
`Lara.Presentation` against `src/Lara/AST.hs`, plus the **Lean side** of the
cross-language presentation-shape parity guard.

Nothing here is a theorem. Each definition is a type ascription or an exhaustive
eliminator that *only* elaborates when the Lean presentation model has the same
constructor shape as the Haskell record or sum it models:

* `measurandCtor` pins `Measurand` to `(MeasurandId, TermSort, Option Polarity)` —
  the `lara-syntax@0.3` shape of `AST.Measurand`, with an arbitrary declared
  sort and the `Num`-gated *optional* polarity clause.
* `policyCtor` pins `Policy` to the ten fields of `AST.Policy` **in order**,
  including `policySigma` in second position.

Changing any Lean record field count or type stops this file compiling. Named
structure fields are also compared with the normalized inventory, and every
payload-carrying sum arm has an exact constructor-signature witness, so field
renames/reorders and same-arity payload retypes cannot drift silently while the
round-trip theorems keep passing.

## The cross-language guard

By itself the witness layer is a Lean-side pin: it reads no Haskell. `shapeRows`
below closes that gap. Both runtimes emit the *same* normalized ordered TSV
inventory of the complete surface-reachable shape; `scripts/check-presentation-parity.sh`
builds both and diffs the two outputs.

```
 Haskell types ──cabal build──▶ presentation-shape.hs ──┐  witnesses: compile-time
  (Lara.AST,                    (witnesses + shape      │  tripwire: rows ==
   Lara.Sigma)                   tripwire + shapeRows)  ▼            real shape
                                                  haskell.tsv ──┐
                                                                ├─ diff -u ─▶ PASS/FAIL
                                                    lean.tsv ───┘
  Lean types  ──lake build───▶ presentation-shape ──────▲
   (Lara.Presentation)          (lean_exe: witnesses + shapeRows)
```

`checkShapeRows` is the Lean shape tripwire: at **elaboration time** it
re-derives every row's real part count, unfolds alias rows against independent
expected types, and compares structure field labels in declaration order. It
fails the build naming the offending row on mismatch. Named structure rows
cannot be relabeled or reordered to fake agreement; positional semantic labels
and same-typed swaps remain assertions because those constructors expose no
field names.

## Named representation exemptions

1. **`SortName` is witnessed but row-erased.** Haskell has a `String -> SortName`
   newtype witness; there is no `SortName` inventory row, because Lean's
   `Sigma.sorts` is a `List String`, so the sort-name wrapper normalizes to a
   bare string on both sides.
2. **`Cert`'s `payload` is exempt from shape comparison.** It is each language's
   native S-expression type (Haskell `SExpr`, Lean `Sx`); the `Cert` row names
   the field, and nothing compares the two payload types.

Two further normalization notes, for the same reason:

* the `FunSym` / `Pred` rows are the Haskell `Lara.Prop` newtypes and the Lean
  `Lara.Support.ConSym` / `Lara.Support.PredSym` structures — the frozen Lean
  semantic core spells the symbol wrappers there, and `Lara.Presentation` reuses
  them through `ConSig` / `PredSig` rather than declaring a parallel pair;
* the `Prop` row is Haskell's `Lara.Prop.Prop` and Lean's `Lara.Atom` (`Prop` is
  a Lean keyword), which is why its parts are the two constructor arguments
  `pred` / `args` rather than field names.

Finally, the `Attack` / `Step` / `Position` rows are modeled by
`Lara.Presentation` even though the **elaborator**, not the surface parser,
produces resolved `Attack` values: `Decl.attack` carries the surface
`SurfaceAttack`, and the frozen trio is kept, codec'd, and proved alongside it.
Both are in the guard's scope.
-/
import Lean
import Lara.Presentation

namespace Lara.PresentationParity

open Lara (Term Terms Atom)
open Lara.Presentation

-- Without this, an unknown type name in a signature below would be silently
-- auto-bound as an implicit universe-polymorphic variable and unify with
-- whatever the model actually has — which would defeat the whole guard.
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## Identifier and symbol witnesses

Each is an exact `String → <structure>` ascription: retyping the payload, or
widening a one-field structure, stops this file compiling. -/

def propIdCtor       : String → PropId       := PropId.mk
def questionIdCtor   : String → QuestionId   := QuestionId.mk
def leafIdCtor       : String → LeafId       := LeafId.mk
def ruleIdCtor       : String → RuleId       := RuleId.mk
def argIdCtor        : String → ArgId        := ArgId.mk
def obligationIdCtor : String → ObligationId := ObligationId.mk
def backendIdCtor    : String → BackendId    := BackendId.mk
def policyIdCtor     : String → PolicyId     := PolicyId.mk
def paramCtor        : String → Param        := Param.mk
def sourceRefCtor    : String → SourceRef    := SourceRef.mk
def theoryDigestCtor : String → TheoryDigest := TheoryDigest.mk
def digestCtor       : String → Digest       := Digest.mk
def groupIdCtor      : String → GroupId      := GroupId.mk
def measurandIdCtor  : String → MeasurandId  := MeasurandId.mk
def datasetIdCtor    : String → DatasetId    := DatasetId.mk
def premiseLabelCtor : String → PremiseLabel := PremiseLabel.mk

/-- The `FunSym` row: the frozen semantic core's constructor-symbol wrapper,
which `ConSig` carries. -/
def funSymCtor : String → Lara.Support.ConSym := Lara.Support.ConSym.mk

/-- The `Pred` row: the frozen semantic core's predicate-symbol wrapper, which
`PredSig` carries. -/
def predCtor : String → Lara.Support.PredSym := Lara.Support.PredSym.mk

/-- The `Prop` row: Haskell's `Prop Pred [Term]` is Lean's `Atom.atom`. -/
def propCtor : String → Terms → Atom := Atom.atom
/-! ## Normalized alias/entry witnesses

These expected shapes are deliberately local to the guard. Exact identity or
constructor witnesses tie each normalized alias/entry row to the real
presentation type instead of relying on the cross-language diff alone. -/

abbrev ExpectedAdmissionEntry := (LeafKind × Provenance) × Admission
abbrev ExpectedTheoryEntry := TheoryDigest × List Atom
abbrev ExpectedBackendEntry := BackendId × String
abbrev ExpectedSubst := List (Param × Term)
abbrev ExpectedPosition := List Step

def substWitness : Subst → ExpectedSubst := id
def positionWitness : Position → ExpectedPosition := id
def dischargeEntryCtor :
    QuestionId → SupportTerm → Discharges → Discharges := Discharges.cons


/-! ## Record constructor witnesses -/

def atomPatCtor : String → Pats → AtomPat := AtomPat.mk

def leafCtor : LeafId → Atom → LeafKind → Provenance → List SourceRef → Leaf := Leaf.mk

def bindingCtor : String → String → AuditStatus → Binding := Binding.mk

def claimCtor : PropId → String → Atom → Binding → Claim := Claim.mk

def questionCtor : QuestionId → AtomPat → Necessity → Question := Question.mk

def certRefCtor : BackendId → Int → TheoryDigest → CertRef := CertRef.mk

def ruleCtor :
    RuleId → List Param → Mode → List AtomPat → List (Option PremiseLabel) →
    AtomPat → Bool → List CertRef → List Question → Rule := Rule.mk

def contraryCtor : AtomPat → AtomPat → Contrary := Contrary.mk

def exceptionCtor : RuleId → AtomPat → Exception := Exception.mk

def dupGroupCtor : GroupId → List LeafId → DupGroup := DupGroup.mk

def conSigCtor :
    Lara.Support.ConSym → List TermSort → TermSort → ConSig := Lara.Sigma.ConSig.mk

def predSigCtor : Lara.Support.PredSym → List TermSort → PredSig := Lara.Sigma.PredSig.mk

def sigmaCtor : List String → List ConSig → List PredSig → Sigma := Lara.Sigma.Sigma.mk

/-- `AST.Measurand`: id, declared sort, optional polarity. (`Sort` is a Lean
keyword, so the sort of a term is spelled `TermSort` throughout the port.) -/
def measurandCtor :
    MeasurandId → TermSort → Option Polarity → Measurand := Measurand.mk

def comparisonSchemeCtor :
    Relation → Polarity → RuleId → RuleId → ComparisonScheme := ComparisonScheme.mk

/-- `AST.Policy`: ten fields, `policySigma` second. -/
def policyCtor :
    PolicyId → Sigma → List Rule → List Contrary → List Exception →
    List ExpectedAdmissionEntry → List ExpectedTheoryEntry → GroupConflictMode →
    List Measurand → List ComparisonScheme → Policy := Policy.mk

/-- Exemption 2: `payload` is the native S-expression type and is not compared. -/
def certCtor : BackendId → Int → TheoryDigest → Sx → Cert := Cert.mk

/-- The `SRule` row: the six-argument rule-instance arm of `SupportTerm`. -/
def sruleCtor :
    RuleId → Subst → SupportTerms → Discharges → List ObligationId → Assurance →
    SupportTerm := SupportTerm.rule

def argCtor : ArgId → ArgConcl → SupportTerm → Arg := Arg.mk

def comparisonClaimCtor : PropId → String → Binding → ComparisonClaim := ComparisonClaim.mk

def comparisonCtor :
    Atom → MeasurandId → DatasetId → Relation → ArgId → ArgId →
    LeafId → LeafId → LeafId → ComparisonClaim → Option PropId → Comparison :=
  Comparison.mk

def programCtor :
    String → Digest → PolicyId → List ExpectedBackendEntry → List Decl → Program := Program.mk

/-! ## Sum-constructor payload witnesses

The exhaustive eliminators below pin constructor presence and positional arity.
These exact ascriptions additionally pin every payload type. -/

def termNumCtor : String → Term := Term.num
def termStrCtor : String → Term := Term.str
def termConCtor : String → Terms → Term := Term.con

def provenanceCheckerCtor : String → String → Provenance := Provenance.checker

def sortDeclCtor : String → TermSort := Lara.Sigma.TermSort.decl

def patVarCtor : Param → Pat := Pat.var
def patLitCtor : Term → Pat := Pat.lit
def patConCtor : String → Pats → Pat := Pat.con

def assuranceCertCtor : Cert → Assurance := Assurance.cert

def supportLeafCtor : LeafId → SupportTerm := SupportTerm.leaf

def stepPremiseCtor : Int → Step := Step.premise
def stepQuestionCtor : QuestionId → Step := Step.question

def rebutCtor : ArgId → ArgId → Attack := Attack.rebut
def undercutCtor : ArgId → ArgId → ExpectedPosition → Attack := Attack.undercut
def undermineCtor : ArgId → ArgId → ExpectedPosition → Attack := Attack.undermine

def surfaceStepIndexCtor : Int → SurfaceStep := SurfaceStep.index
def surfaceStepNameCtor : String → SurfaceStep := SurfaceStep.name

def surfaceRebutCtor : ArgId → ArgId → SurfaceAttack := SurfaceAttack.rebut
def surfaceUndercutCtor :
    ArgId → ArgId → List SurfaceStep → SurfaceAttack := SurfaceAttack.undercut
def surfaceUndermineCtor :
    ArgId → ArgId → List SurfaceStep → SurfaceAttack := SurfaceAttack.undermine

def challengeQuestionCtor :
    QuestionId → ArgId → ChallengeTarget := ChallengeTarget.question
def challengeLeafCtor : LeafId → ChallengeTarget := ChallengeTarget.leaf

def supportsClaimCtor : PropId → ArgConcl := ArgConcl.supportsClaim
def supportsDerivedCtor : PropId → ArgConcl := ArgConcl.supportsDerived
def challengesCtor : ChallengeTarget → ArgConcl := ArgConcl.challenges

def declLeafCtor : Leaf → Decl := Decl.leaf
def declClaimCtor : Claim → Decl := Decl.claim
def declArgCtor : Arg → Decl := Decl.arg
def declAttackCtor : SurfaceAttack → Decl := Decl.attack
def declStatusCtor : PropId → Decl := Decl.status
def declGroupCtor : DupGroup → Decl := Decl.group
def declComparisonCtor : Comparison → Decl := Decl.comparison

/-! ## Exhaustive eliminators

One per closed sum. Lean's exhaustiveness checker rejects a missing arm, so a
new constructor on either side breaks this file; every arm binds its
constructor's arguments at full positional arity, so a payload-arity change
breaks it too. Exact payload types are pinned by the witnesses above. -/

def termTag : Term → String
  | .num _   => "num"
  | .str _   => "str"
  | .con _ _ => "con"

def leafKindTag : LeafKind → String
  | .observed  => "observed"
  | .attested  => "attested"
  | .assumed   => "assumed"
  | .certified => "certified"

def provenanceTag : Provenance → String
  | .user        => "user"
  | .aiExecuted  => "ai-executed"
  | .checker _ _ => "checker(name,version)"

def auditStatusTag : AuditStatus → String
  | .unreviewed => "unreviewed"
  | .reviewed   => "reviewed"
  | .disputed   => "disputed"

def modeTag : Mode → String
  | .strict     => "strict"
  | .defeasible => "defeasible"

def necessityTag : Necessity → String
  | .mandatory => "mandatory"
  | .optional  => "optional"

def admissionTag : Admission → String
  | .admit      => "admit"
  | .quarantine => "quarantine"
  | .reject     => "reject"

def groupConflictModeTag : GroupConflictMode → String
  | .quarantineOnConflict => "quarantine-on-conflict"
  | .rejectOnConflict     => "reject-on-conflict"

def polarityTag : Polarity → String
  | .higherIsBetter => "higher-is-better"
  | .lowerIsBetter  => "lower-is-better"

def relationTag : Relation → String
  | .strictlyBetter => "strictly-better"
  | .atLeastAsGood  => "at-least-as-good"

def sortTag : TermSort → String
  | .num    => "num"
  | .str    => "str"
  | .decl _ => "decl"

def patTag : Pat → String
  | .var _   => "var"
  | .lit _   => "lit"
  | .con _ _ => "con"

def assuranceTag : Assurance → String
  | .none    => "none"
  | .trusted => "trusted"
  | .cert _  => "cert"

def supportTermTag : SupportTerm → String
  | .leaf _           => "leaf"
  | .rule _ _ _ _ _ _ => "rule"

def stepTag : Step → String
  | .premise _  => "premise"
  | .question _ => "question"

def attackTag : Attack → String
  | .rebut _ _       => "rebut"
  | .undercut _ _ _  => "undercut"
  | .undermine _ _ _ => "undermine"

def surfaceStepTag : SurfaceStep → String
  | .index _ => "index"
  | .name _  => "name"

def surfaceAttackTag : SurfaceAttack → String
  | .rebut _ _       => "rebut"
  | .undercut _ _ _  => "undercut"
  | .undermine _ _ _ => "undermine"

def challengeTargetTag : ChallengeTarget → String
  | .question _ _ => "question"
  | .leaf _       => "leaf"

def argConclTag : ArgConcl → String
  | .supportsClaim _   => "supports-claim"
  | .supportsDerived _ => "supports-derived"
  | .challenges _      => "challenges"

def declTag : Decl → String
  | .leaf _       => "leaf"
  | .claim _      => "claim"
  | .arg _        => "arg"
  | .attack _     => "attack"
  | .status _     => "status"
  | .group _      => "group"
  | .comparison _ => "comparison"

/-! ## The normalized inventory -/

/-- The complete surface-reachable shape, in the order both runtimes emit it.
Row order is part of the comparison contract. Row labels are **semantic**
strings, not identifiers: the `Sort` row is spelled `Sort` on both sides even
though the Lean identifier is `TermSort`. -/
def shapeRows : List (String × List String) :=
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
  , ("Rule",
      [ "id", "params", "mode", "premises", "premise-labels", "conclusion"
      , "allow-trusted", "certifiers", "questions" ])
  , ("Contrary", ["left", "right"])
  , ("Exception", ["rule", "atom"])
  , ("DupGroup", ["id", "members"])
  , ("ConSig", ["sym", "args", "result"])
  , ("PredSig", ["sym", "args"])
  , ("Sigma", ["sorts", "cons", "preds"])
  , ("Measurand", ["id", "sort", "polarity"])
  , ("ComparisonScheme", ["relation", "polarity", "recheck", "bridge"])
  , ("Policy",
      [ "id", "sigma", "rules", "contraries", "exceptions", "admission"
      , "theories", "group-mode", "measurands", "comparison-schemes" ])
  , ("Cert", ["backend", "version", "theory", "payload"])
  , ("SRule", ["rule", "subst", "premises", "discharge", "holes", "assurance"])
  , ("Arg", ["id", "conclusion", "term"])
  , ("ComparisonClaim", ["id", "nl-raw", "binding"])
  , ("Comparison",
      [ "conclusion", "measurand", "dataset", "relation", "recheck-arg"
      , "bridge-arg", "result", "baseline", "binding", "claim", "supports" ])
  , ("Program", ["artifact", "digest", "policy", "backends", "decls"])
  , ("AdmissionEntry", ["key:(LeafKind,Provenance)", "value:Admission"])
  , ("TheoryEntry", ["digest:TheoryDigest", "atoms:List Prop"])
  , ("BackendEntry", ["backend:BackendId", "version:String"])
  , ("Subst", ["entries:List (Param,Term)"])
  , ("DischargeEntry", ["question:QuestionId", "term:SupportTerm"])
  , ("Position", ["steps:List Step"])
  ]

/-- The inventory as the guard's normalized TSV: one row per line, name first,
parts tab-separated, trailing newline. -/
def renderShape : String :=
  String.intercalate "\n" (shapeRows.map fun row =>
    String.intercalate "\t" (row.1 :: row.2)) ++ "\n"

/-! ## The shape tripwire

Elaboration-time check that every row's part count equals the real shape of the
type it names. Structure rows also compare normalized field names, and alias
rows unfold and compare the actual and expected types. Core `Lean.Meta` only —
no new dependency. -/

/-- How a row's real shape is recovered from the environment. -/
inductive ShapeCheck where
  | /-- structure: field count plus normalized field-name sequence -/
    fields : Lean.Name → ShapeCheck
  | /-- inductive: the real count is its constructor count -/
    ctors : Lean.Name → ShapeCheck
  | /-- one named constructor of an inductive: the real count is that arm's arity -/
    ctorArity : Lean.Name → ShapeCheck
  | /-- constructor payload arity after excluding recursive representation fields -/
    ctorPayloadArity : Lean.Name → Nat → ShapeCheck
  | /-- abbreviation unfolded and checked definitionally against an expected type -/
    aliasDefEq : Lean.Name → Lean.Name → Nat → ShapeCheck

open Lean Meta in
def ShapeCheck.realCount : ShapeCheck → MetaM Nat
  | .fields n => do
      let env ← getEnv
      unless isStructure env n do
        throwError "presentation parity: {n} is not a structure"
      return (getStructureFields env n).size
  | .ctors n => do
      let info ← getConstInfoInduct n
      return info.ctors.length
  | .ctorArity c => do
      let info ← getConstInfoCtor c
      return info.numFields
  | .ctorPayloadArity c ignored => do
      let info ← getConstInfoCtor c
      if info.numFields < ignored then
        throwError "presentation parity: {c} has {info.numFields} fields, \
          cannot ignore {ignored}"
      return info.numFields - ignored
  | .aliasDefEq actual expected count => do
      let actualType ← whnf (mkConst actual)
      let expectedType ← whnf (mkConst expected)
      unless (← isDefEq actualType expectedType) do
        throwError "presentation parity: alias {actual} is not definitionally \
          equal to expected shape {expected}"
      return count

/-- Mechanical normalization from Lean lower-camel field names to the shared
semantic inventory. Identifier substitutions with different meanings are
handled separately by `normalizeFieldNameFor`. -/
def normalizeFieldName : String → String
  | "auditStatus" => "audit-status"
  | "premiseLabels" => "premise-labels"
  | "allowTrusted" => "allow-trusted"
  | "groupMode" => "group-mode"
  | "comparisonSchemes" => "comparison-schemes"
  | "recheckArg" => "recheck-arg"
  | "bridgeArg" => "bridge-arg"
  | "nlRaw" => "nl-raw"
  | field => field

/-- Type-scoped normalization for intentional cross-model identifier
differences. Scoping prevents an unrelated field rename to `name` or `concl`
from normalizing back to an old inventory label. -/
def normalizeFieldNameFor (owner : Lean.Name) (field : String) : String :=
  if (owner == ``Lara.Support.ConSym || owner == ``Lara.Support.PredSym) &&
      field == "name" then
    "val"
  else if owner == ``Lara.Presentation.Arg && field == "concl" then
    "conclusion"
  else
    normalizeFieldName field

example : normalizeFieldName "name" = "name" := by rfl
example : normalizeFieldNameFor ``Lara.Support.ConSym "name" = "val" := by rfl
example : normalizeFieldNameFor ``Lara.Support.PredSym "name" = "val" := by rfl
example : normalizeFieldNameFor ``Lara.Presentation.Arg "concl" = "conclusion" := by rfl
example : normalizeFieldNameFor ``Lara.Presentation.PropId "name" = "name" := by rfl
example : normalizeFieldNameFor ``Lara.Presentation.Comparison "concl" = "concl" := by rfl

open Lean Meta in
def ShapeCheck.realLabels : ShapeCheck → MetaM (Option (List String))
  | .fields n => do
      let env ← getEnv
      unless isStructure env n do
        throwError "presentation parity: {n} is not a structure"
      return some ((getStructureFields env n).toList.map fun field =>
        normalizeFieldNameFor n field.getString!)
  | _ => return none

/-- One entry per `shapeRows` entry, same order and same row name. The
association-list aliases and `Subst`/`Position` are unfolded and checked
definitionally against independent expected shapes. `DischargeEntry` is
recovered from `Discharges.cons`, excluding its recursive spine field; its
payload types are pinned by `dischargeEntryCtor`. -/
def shapeChecks : List (String × ShapeCheck) :=
  [ ("PropId", .fields ``Lara.Presentation.PropId)
  , ("QuestionId", .fields ``Lara.Presentation.QuestionId)
  , ("LeafId", .fields ``Lara.Presentation.LeafId)
  , ("RuleId", .fields ``Lara.Presentation.RuleId)
  , ("ArgId", .fields ``Lara.Presentation.ArgId)
  , ("ObligationId", .fields ``Lara.Presentation.ObligationId)
  , ("BackendId", .fields ``Lara.Presentation.BackendId)
  , ("PolicyId", .fields ``Lara.Presentation.PolicyId)
  , ("Param", .fields ``Lara.Presentation.Param)
  , ("SourceRef", .fields ``Lara.Presentation.SourceRef)
  , ("TheoryDigest", .fields ``Lara.Presentation.TheoryDigest)
  , ("Digest", .fields ``Lara.Presentation.Digest)
  , ("GroupId", .fields ``Lara.Presentation.GroupId)
  , ("MeasurandId", .fields ``Lara.Presentation.MeasurandId)
  , ("DatasetId", .fields ``Lara.Presentation.DatasetId)
  , ("PremiseLabel", .fields ``Lara.Presentation.PremiseLabel)
  , ("FunSym", .fields ``Lara.Support.ConSym)
  , ("Pred", .fields ``Lara.Support.PredSym)
  , ("Term", .ctors ``Lara.Term)
  , ("Prop", .ctorArity ``Lara.Atom.atom)
  , ("LeafKind", .ctors ``Lara.Presentation.LeafKind)
  , ("Provenance", .ctors ``Lara.Presentation.Provenance)
  , ("AuditStatus", .ctors ``Lara.Presentation.AuditStatus)
  , ("Mode", .ctors ``Lara.Presentation.Mode)
  , ("Necessity", .ctors ``Lara.Presentation.Necessity)
  , ("Admission", .ctors ``Lara.Presentation.Admission)
  , ("GroupConflictMode", .ctors ``Lara.Presentation.GroupConflictMode)
  , ("Polarity", .ctors ``Lara.Presentation.Polarity)
  , ("Relation", .ctors ``Lara.Presentation.Relation)
  , ("Sort", .ctors ``Lara.Sigma.TermSort)
  , ("Pat", .ctors ``Lara.Presentation.Pat)
  , ("Assurance", .ctors ``Lara.Presentation.Assurance)
  , ("SupportTerm", .ctors ``Lara.Presentation.SupportTerm)
  , ("Step", .ctors ``Lara.Presentation.Step)
  , ("Attack", .ctors ``Lara.Presentation.Attack)
  , ("SurfaceStep", .ctors ``Lara.Presentation.SurfaceStep)
  , ("SurfaceAttack", .ctors ``Lara.Presentation.SurfaceAttack)
  , ("ChallengeTarget", .ctors ``Lara.Presentation.ChallengeTarget)
  , ("ArgConcl", .ctors ``Lara.Presentation.ArgConcl)
  , ("Decl", .ctors ``Lara.Presentation.Decl)
  , ("AtomPat", .fields ``Lara.Presentation.AtomPat)
  , ("Leaf", .fields ``Lara.Presentation.Leaf)
  , ("Binding", .fields ``Lara.Presentation.Binding)
  , ("Claim", .fields ``Lara.Presentation.Claim)
  , ("Question", .fields ``Lara.Presentation.Question)
  , ("CertRef", .fields ``Lara.Presentation.CertRef)
  , ("Rule", .fields ``Lara.Presentation.Rule)
  , ("Contrary", .fields ``Lara.Presentation.Contrary)
  , ("Exception", .fields ``Lara.Presentation.Exception)
  , ("DupGroup", .fields ``Lara.Presentation.DupGroup)
  , ("ConSig", .fields ``Lara.Sigma.ConSig)
  , ("PredSig", .fields ``Lara.Sigma.PredSig)
  , ("Sigma", .fields ``Lara.Sigma.Sigma)
  , ("Measurand", .fields ``Lara.Presentation.Measurand)
  , ("ComparisonScheme", .fields ``Lara.Presentation.ComparisonScheme)
  , ("Policy", .fields ``Lara.Presentation.Policy)
  , ("Cert", .fields ``Lara.Presentation.Cert)
  , ("SRule", .ctorArity ``Lara.Presentation.SupportTerm.rule)
  , ("Arg", .fields ``Lara.Presentation.Arg)
  , ("ComparisonClaim", .fields ``Lara.Presentation.ComparisonClaim)
  , ("Comparison", .fields ``Lara.Presentation.Comparison)
  , ("Program", .fields ``Lara.Presentation.Program)
  , ("AdmissionEntry", .aliasDefEq ``Lara.Presentation.AdmissionEntry
      ``Lara.PresentationParity.ExpectedAdmissionEntry 2)
  , ("TheoryEntry", .aliasDefEq ``Lara.Presentation.TheoryEntry
      ``Lara.PresentationParity.ExpectedTheoryEntry 2)
  , ("BackendEntry", .aliasDefEq ``Lara.Presentation.BackendEntry
      ``Lara.PresentationParity.ExpectedBackendEntry 2)
  , ("Subst", .aliasDefEq ``Lara.Presentation.Subst
      ``Lara.PresentationParity.ExpectedSubst 1)
  , ("DischargeEntry",
      .ctorPayloadArity ``Lara.Presentation.Discharges.cons 1)
  , ("Position", .aliasDefEq ``Lara.Presentation.Position
      ``Lara.PresentationParity.ExpectedPosition 1)
  ]

open Lean Meta in
/-- Refuse to compile unless every row's part count equals the real shape of the
type it names. Names the offending row on mismatch. -/
def checkShapeRows : MetaM Unit := do
  unless shapeRows.length == shapeChecks.length do
    throwError "presentation parity: {shapeRows.length} inventory rows but \
      {shapeChecks.length} tripwire entries"
  for (row, chk) in shapeRows.zip shapeChecks do
    unless row.1 == chk.1 do
      throwError "presentation parity: tripwire row order disagrees: \
        {row.1} vs {chk.1}"
    let real ← chk.2.realCount
    unless real == row.2.length do
      throwError "presentation parity: {row.1}: inventory lists \
        {row.2.length} parts but the type has {real} \
        (update this row in BOTH inventories)"
    match (← chk.2.realLabels) with
    | none => pure ()
    | some labels =>
        unless labels == row.2 do
          throwError "presentation parity: {row.1}: inventory labels \
            {repr row.2} disagree with normalized fields {repr labels}"

#eval checkShapeRows

end Lara.PresentationParity
