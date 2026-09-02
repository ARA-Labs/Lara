import Lara.Presentation
import Lara.Unit
import Lara.Grounded
import Lara.Cell
import Lara.CertSlots
import Lara.NDNamed
import Lara.Surface.Binding

namespace Lara.Surface

open Lara

structure Env (canon : String → String) where
  registry : Support.BackendRegistry canon
  startsIdent : String → Bool
  startsIdent_nat_false : ∀ n, startsIdent (Nat.repr n) = false
  encodeProp : String → Option String

structure Input where
  program : Presentation.Program
  policy : Presentation.Policy
deriving DecidableEq

structure Elaborated (canon : String → String) where
  gamma : Support.LeafId → Option Atom
  ground : List Atom
  unit : Lara.Unit
  claims : List (Presentation.PropId × Grounded.Claim)
  argIds : List Presentation.ArgId
  authoredObligations : List (Presentation.ArgId × List Presentation.ObligationId)
  openQuestions : List (Presentation.ArgId × List Support.QuestionId)
  resolvedAttacks : List Attack.Attack
  semanticProgram : Presentation.Program

inductive Error where
  | unsupported
  | policyMismatch : Presentation.PolicyId → Presentation.PolicyId → Error
  | duplicateLeafId : Presentation.LeafId → Error
  | duplicateArgId : Presentation.ArgId → Error
  | duplicateClaimId : Presentation.PropId → Error
  | duplicateValueName : Presentation.ValueName → Error
  | malformedRuleNamespace : Presentation.RuleId → Error
  | invalidValueBinding : Presentation.ValueName → Error
  | invalidComparison : Presentation.PropId → Error
  | invalidInferredArgument : Presentation.ArgId → Error
  | invalidNamedCertificate : Presentation.ArgId → Error
  | conclusionMismatch : Presentation.ArgId → Presentation.PropId → Error
  | challengeTargetUndeclared : Presentation.ArgId → Error
  | invalidSurfaceAttack : Presentation.ArgId → Presentation.ArgId → Error
  | unknownStatusClaim : Presentation.PropId → Error
  | duplicateGroupId : Presentation.GroupId → Error
  | groupRepeatedMember : Presentation.GroupId → Presentation.LeafId → Error
  | groupTooFewMembers : Presentation.GroupId → Error
  | groupMemberUndeclared : Presentation.GroupId → Presentation.LeafId → Error
  | noncanonicalPremiseLabels : Presentation.RuleId → Error
  | duplicateAdmissionKey : Presentation.LeafKind → Presentation.Provenance → Error
  | admissionRejected : Presentation.LeafId → Error
deriving DecidableEq

/-! The sole presentation-to-core bridge. -/

def toSupportLeafId (id : Presentation.LeafId) : Support.LeafId := ⟨id.val⟩
def toSupportQuestionId (id : Presentation.QuestionId) : Support.QuestionId := ⟨id.val⟩
def toSupportRuleId (id : Presentation.RuleId) : Support.RuleId := ⟨id.val⟩
def toSupportBackendId (id : Presentation.BackendId) (version : Int) : Support.BackendId :=
  ⟨id.val, version.toNat⟩
def toSupportDigest (digest : Presentation.Digest) : Support.Digest := ⟨digest.val⟩
def toSupportTheoryDigest (digest : Presentation.TheoryDigest) : Support.Digest := ⟨digest.val⟩
def toSupportParam (param : Presentation.Param) : Support.VarId := ⟨param.val⟩
def toSupportObligationId (id : Presentation.ObligationId) : Support.QuestionId := ⟨id.val⟩

mutual
  def sxToSExpr : Presentation.Sx → Support.SExpr
    | .str s => .atom s
    | .int n => .atom (toString n)
    | .node tag children => .list (.atom tag :: sxListToSExprs children)
  def sxListToSExprs : Presentation.SxList → List Support.SExpr
    | .nil => []
    | .cons value rest => sxToSExpr value :: sxListToSExprs rest
end

def toSupportAssurance : Presentation.Assurance → Support.Assurance
  | .none => .none
  | .trusted => .trusted
  | .cert cert =>
      .cert (toSupportBackendId cert.backend cert.version)
        (toSupportTheoryDigest cert.theory) ⟨sxToSExpr cert.payload⟩

mutual
  def toSupportTerm : Presentation.SupportTerm → Support.SupportTerm
    | .leaf id => .leaf (toSupportLeafId id)
    | .rule rule subst premises discharges holes assurance =>
        .inst (toSupportRuleId rule)
          (subst.map fun pair => (toSupportParam pair.1, pair.2))
          (toSupportTerms premises) (toSupportDischarges discharges)
          (holes.map toSupportObligationId) (toSupportAssurance assurance)
  def toSupportTerms : Presentation.SupportTerms → List Support.SupportTerm
    | .nil => []
    | .cons term rest => toSupportTerm term :: toSupportTerms rest
  def toSupportDischarges : Presentation.Discharges →
      List (Support.QuestionId × Support.SupportTerm)
    | .nil => []
    | .cons question term rest =>
        (toSupportQuestionId question, toSupportTerm term) :: toSupportDischarges rest
end

/-! Typed inventories. -/

def leafIds (program : Presentation.Program) : List Presentation.LeafId :=
  program.decls.filterMap fun
    | .leaf leaf => some leaf.id
    | _ => none

def argIds (program : Presentation.Program) : List Presentation.ArgId :=
  program.decls.flatMap fun
    | .arg argument => [argument.id]
    | .comparison comparison => [comparison.recheckArg, comparison.bridgeArg]
    | _ => []

def claimIds (program : Presentation.Program) : List Presentation.PropId :=
  program.decls.filterMap fun
    | .claim claim => some claim.id
    | .comparison comparison => some comparison.claim.id
    | _ => none

def valueNames (program : Presentation.Program) : List Presentation.ValueName :=
  program.valueBindings.map (·.name)

/-- Requested claim-status identifiers, in declaration order. -/
def statusIds (program : Presentation.Program) : List Presentation.PropId :=
  program.decls.filterMap fun
    | .status id => some id
    | _ => none

/-- Duplicate-report groups, in declaration order. -/
def groupDecls (program : Presentation.Program) : List Presentation.DupGroup :=
  program.decls.filterMap fun
    | .group group => some group
    | _ => none

def ruleIds (policy : Presentation.Policy) : List Presentation.RuleId :=
  policy.rules.map (·.id)

def premiseLabels (rule : Presentation.Rule) : List Presentation.PremiseLabel :=
  rule.premiseLabels.filterMap id

def questionIds (rule : Presentation.Rule) : List Presentation.QuestionId :=
  rule.questions.map (·.id)

def declaredLeaves (program : Presentation.Program) :
    List (Presentation.LeafId × Atom) :=
  program.decls.filterMap fun
    | .leaf leaf => some (leaf.id, leaf.prop)
    | _ => none

private def declaredClaims (program : Presentation.Program) :
    List (Presentation.PropId × Atom) :=
  program.decls.filterMap fun
    | .claim claim => some (claim.id, claim.formal)
    | _ => none

def comparisonDecls (program : Presentation.Program) : List Presentation.Comparison :=
  program.decls.filterMap fun
    | .comparison comparison => some comparison
    | _ => none

def ruleById (policy : Presentation.Policy) (id : Presentation.RuleId) :
    Option Presentation.Rule :=
  policy.rules.find? (fun rule => decide (rule.id = id))

def leafProp? (program : Presentation.Program) (id : Presentation.LeafId) : Option Atom :=
  (declaredLeaves program).findSome? fun entry =>
    if entry.1 = id then some entry.2 else none

/-! Independent declaration and rule-namespace propositions. -/

def DeclarationIdsNodup (program : Presentation.Program) : Prop :=
  (((leafIds program).Nodup ∧ (argIds program).Nodup) ∧
    (claimIds program).Nodup) ∧ (valueNames program).Nodup

def declarationIdsNodupB (program : Presentation.Program) : Bool :=
  decide (leafIds program).Nodup && decide (argIds program).Nodup &&
  decide (claimIds program).Nodup && decide (valueNames program).Nodup

theorem declarationIdsNodupB_iff (program : Presentation.Program) :
    declarationIdsNodupB program = true ↔ DeclarationIdsNodup program := by
  simp [declarationIdsNodupB, DeclarationIdsNodup]

/-- Every requested status names a declared claim.  This is independent of
core ground construction: malformed status declarations are rejected rather
than silently omitted from the query ground. -/
def StatusesWellFormed (program : Presentation.Program) : Prop :=
  ∀ id ∈ statusIds program, id ∈ claimIds program

def statusesWellFormedB (program : Presentation.Program) : Bool :=
  (statusIds program).all fun id => (claimIds program).contains id

theorem statusesWellFormedB_iff (program : Presentation.Program) :
    statusesWellFormedB program = true ↔ StatusesWellFormed program := by
  simp [statusesWellFormedB, StatusesWellFormed, List.all_eq_true,
    List.contains_iff_mem]

/-- Production duplicate-report-group well-formedness: group identifiers are
unique; every group has distinct members, at least two members, and only
declared leaves. -/
def GroupsWellFormed (program : Presentation.Program) : Prop :=
  (groupDecls program |>.map (·.id)).Nodup ∧
    ∀ group ∈ groupDecls program,
      (group.members.Nodup ∧ 2 ≤ group.members.length) ∧
        ∀ leaf ∈ group.members, leaf ∈ leafIds program

private def groupWellFormedB (program : Presentation.Program)
    (group : Presentation.DupGroup) : Bool :=
  decide group.members.Nodup && decide (2 ≤ group.members.length) &&
    group.members.all fun leaf => (leafIds program).contains leaf

def groupsWellFormedB (program : Presentation.Program) : Bool :=
  decide (groupDecls program |>.map (·.id)).Nodup &&
    (groupDecls program).all (groupWellFormedB program)

theorem groupsWellFormedB_iff (program : Presentation.Program) :
    groupsWellFormedB program = true ↔ GroupsWellFormed program := by
  simp [groupsWellFormedB, groupWellFormedB, GroupsWellFormed,
    List.all_eq_true, List.contains_iff_mem]

def RuleNamespaceWellFormed (rule : Presentation.Rule) : Prop :=
  (((premiseLabels rule).Nodup ∧ (questionIds rule).Nodup) ∧
    (∀ label ∈ premiseLabels rule, label.val ≠ "rule" ∧ label.val ≠ "leaf")) ∧
  (∀ label ∈ premiseLabels rule, ∀ question ∈ questionIds rule,
    label.val ≠ question.val)

def RuleNamespacesWellFormed (policy : Presentation.Policy) : Prop :=
  (ruleIds policy).Nodup ∧
    ∀ rule ∈ policy.rules, RuleNamespaceWellFormed rule

def ruleNamespaceWellFormedB (rule : Presentation.Rule) : Bool :=
  decide (premiseLabels rule).Nodup && decide (questionIds rule).Nodup &&
  (premiseLabels rule).all (fun label => label.val != "rule" && label.val != "leaf") &&
  (premiseLabels rule).all (fun label =>
    (questionIds rule).all (fun question => label.val != question.val))

def ruleNamespacesWellFormedB (policy : Presentation.Policy) : Bool :=
  decide (ruleIds policy).Nodup && policy.rules.all ruleNamespaceWellFormedB

theorem ruleNamespacesWellFormedB_iff (policy : Presentation.Policy) :
    ruleNamespacesWellFormedB policy = true ↔ RuleNamespacesWellFormed policy := by
  simp [ruleNamespacesWellFormedB, ruleNamespaceWellFormedB,
    RuleNamespacesWellFormed, RuleNamespaceWellFormed]

/-! Value bindings and interpolation. -/

def lookupValue (bindings : List Presentation.ValueBinding)
    (name : Presentation.ValueName) : Option Term :=
  bindings.findSome? fun binding => if binding.name = name then some binding.term else none

mutual
  def substituteValueTerm (bindings : List Presentation.ValueBinding) : Term → Term
    | term@(.num _) => term
    | term@(.str _) => term
    | .con name .nil =>
        match lookupValue bindings ⟨name⟩ with
        | some replacement => replacement
        | none => .con name .nil
    | .con name terms => .con name (substituteValueTerms bindings terms)
  def substituteValueTerms (bindings : List Presentation.ValueBinding) : Terms → Terms
    | .nil => .nil
    | .cons term rest =>
        .cons (substituteValueTerm bindings term) (substituteValueTerms bindings rest)
end

def substituteValueAtom (bindings : List Presentation.ValueBinding) : Atom → Atom
  | .atom pred terms => .atom pred (substituteValueTerms bindings terms)

def takeDirective : List Char → Option (List Char × List Char)
  | [] => none
  | '}' :: rest => some ([], rest)
  | char :: rest => do
      let (body, after) ← takeDirective rest
      some (char :: body, after)

private def parseNlFuel : Nat → List Char → Option (List (List Char))
  | 0, chars => if chars.isEmpty then some [] else none
  | _ + 1, [] => some []
  | fuel + 1, '{' :: '{' :: rest => parseNlFuel fuel rest
  | fuel + 1, '}' :: '}' :: rest => parseNlFuel fuel rest
  | _ + 1, '}' :: _ => none
  | fuel + 1, '{' :: rest => do
      let (body, after) ← takeDirective rest
      let bodies ← parseNlFuel fuel after
      some (body :: bodies)
  | fuel + 1, _ :: rest => parseNlFuel fuel rest

private def parseNl (text : String) : Option (List (List Char)) :=
  parseNlFuel (text.toList.length + 1) text.toList

def claimNls (program : Presentation.Program) : List String :=
  program.decls.filterMap fun
    | .claim claim => some claim.nl
    | .comparison comparison => some comparison.claim.nlRaw
    | _ => none


private def splitDecimalChars : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | '.' :: rest => ([], some rest)
  | char :: rest =>
      let split := splitDecimalChars rest
      (char :: split.1, split.2)

private def canonicalNatCharsB : List Char → Bool
  | ['0'] => true
  | first :: rest =>
      first != '0' && first.isDigit && rest.all Char.isDigit
  | [] => false

private def canonicalFractionCharsB : List Char → Bool
  | [] => false
  | [last] => last.isDigit && last != '0'
  | char :: rest => char.isDigit && canonicalFractionCharsB rest

private def canonicalUnsignedDecimalCharsB (chars : List Char) : Bool :=
  let split := splitDecimalChars chars
  canonicalNatCharsB split.1 &&
    match split.2 with
    | none => true
    | some fraction => canonicalFractionCharsB fraction

private def decimalStringB (source : String) : Bool :=
  match source.toList with
  | '-' :: rest => rest != ['0'] && canonicalUnsignedDecimalCharsB rest
  | '+' :: _ => false
  | chars => canonicalUnsignedDecimalCharsB chars

def CellObligation : Atom → Prop
  | .atom _ terms =>
      match Lara.Cell.termsNums terms with
      | [number] => decimalStringB (Lara.canonNum number) = true
      | _ => False

def cellObligationB : Atom → Bool
  | .atom _ terms =>
      match Lara.Cell.termsNums terms with
      | [number] => decimalStringB (Lara.canonNum number)
      | _ => false

theorem cellObligationB_iff (proposition : Atom) :
    cellObligationB proposition = true ↔ CellObligation proposition := by
  cases proposition with
  | atom pred terms =>
      cases h : Lara.Cell.termsNums terms with
      | nil => simp [cellObligationB, CellObligation, h]
      | cons number rest =>
          cases rest with
          | nil => simp [cellObligationB, CellObligation, h]
          | cons next tail => simp [cellObligationB, CellObligation, h]

private def valueDirectiveBodies (input : Input) : List (List Char) :=
  (valueNames input.program).map (fun name => name.val.toList)

private def cellDirectiveBodies (input : Input) : List (List Char) :=
  (declaredLeaves input.program).filterMap fun entry =>
    if cellObligationB entry.2 then
      some ("cell ".toList ++ entry.1.val.toList)
    else none

def DirectiveWellFormed (input : Input) (body : List Char) : Prop :=
  body ∈ valueDirectiveBodies input ∨ body ∈ cellDirectiveBodies input

def NlWellFormed (input : Input) (text : String) : Prop :=
  match parseNl text with
  | none => False
  | some bodies => ∀ body ∈ bodies, DirectiveWellFormed input body

def ValueBindingsWellFormed (input : Input) : Prop :=
  (((((valueNames input.program).Nodup ∧
    (∀ binding ∈ input.program.valueBindings, binding.name.val ≠ "cell")) ∧
    (∀ binding ∈ input.program.valueBindings,
      ∀ con ∈ input.policy.sigma.cons, binding.name.val ≠ con.sym.name)) ∧
    (∀ binding ∈ input.program.valueBindings,
      (Lara.Sigma.sortOf input.policy.sigma binding.term).isSome = true)) ∧
    (input.program.valueBindings = [] ∨
      ∀ declaration ∈ input.program.decls,
        match declaration with
        | .claim claim =>
            Lara.Sigma.wsAtom input.policy.sigma
              (substituteValueAtom input.program.valueBindings claim.formal) = true
        | _ => True)) ∧
    ∀ text ∈ claimNls input.program, NlWellFormed input text

def valueBindingsWellFormedB (input : Input) : Bool :=
  decide (valueNames input.program).Nodup &&
  input.program.valueBindings.all (fun binding => binding.name.val != "cell") &&
  input.program.valueBindings.all (fun binding =>
    input.policy.sigma.cons.all (fun con => binding.name.val != con.sym.name)) &&
  input.program.valueBindings.all (fun binding =>
    (Lara.Sigma.sortOf input.policy.sigma binding.term).isSome) &&
  (input.program.valueBindings.isEmpty ||
    input.program.decls.all (fun declaration =>
      match declaration with
      | .claim claim =>
          Lara.Sigma.wsAtom input.policy.sigma
            (substituteValueAtom input.program.valueBindings claim.formal)
      | _ => true)) &&
  (claimNls input.program).all (fun text =>
    match parseNl text with
    | none => false
    | some bodies => bodies.all fun body =>
        (valueDirectiveBodies input).contains body ||
        (cellDirectiveBodies input).contains body)

theorem valueBindingsWellFormedB_iff (input : Input) :
    valueBindingsWellFormedB input = true ↔ ValueBindingsWellFormed input := by
  simp [valueBindingsWellFormedB, ValueBindingsWellFormed, NlWellFormed,
    DirectiveWellFormed, valueDirectiveBodies, cellDirectiveBodies] <;> grind

/-! Pattern matching used by comparison and inferred-reference validation. -/

abbrev SurfaceSubst := List (Presentation.Param × Term)

def lookupSurfaceSubst (subst : SurfaceSubst) (param : Presentation.Param) : Option Term :=
  subst.findSome? fun entry => if entry.1 = param then some entry.2 else none

def sameSurfaceTerm (left right : Term) : Bool :=
  Lara.nfTerm Lara.canonNum left == Lara.nfTerm Lara.canonNum right

private def bindSurfaceParam (subst : SurfaceSubst) (param : Presentation.Param)
    (term : Term) : Option SurfaceSubst :=
  match lookupSurfaceSubst subst param with
  | none => some (subst ++ [(param, term)])
  | some prior => if sameSurfaceTerm prior term then some subst else none

mutual
  def matchSurfacePat : SurfaceSubst → Presentation.Pat → Term → Option SurfaceSubst
    | subst, .var param, term => bindSurfaceParam subst param term
    | subst, .lit expected, actual =>
        if sameSurfaceTerm expected actual then some subst else none
    | subst, .con expected pats, .con actual terms =>
        if expected = actual then matchSurfacePats subst pats terms else none
    | _, _, _ => none
  def matchSurfacePats : SurfaceSubst → Presentation.Pats → Terms → Option SurfaceSubst
    | subst, .nil, .nil => some subst
    | subst, .cons pat pats, .cons term terms => do
        let next ← matchSurfacePat subst pat term
        matchSurfacePats next pats terms
    | _, _, _ => none
end

def matchSurfaceAtom (subst : SurfaceSubst)
    (pattern : Presentation.AtomPat) : Atom → Option SurfaceSubst
  | .atom pred terms =>
      if pattern.pred = pred then matchSurfacePats subst pattern.args terms else none

mutual
  def instantiateSurfacePat (subst : SurfaceSubst) : Presentation.Pat → Option Term
    | .var param => lookupSurfaceSubst subst param
    | .lit term => some term
    | .con name pats => (instantiateSurfacePats subst pats).map (.con name)
  def instantiateSurfacePats (subst : SurfaceSubst) :
      Presentation.Pats → Option Terms
    | .nil => some .nil
    | .cons pat rest => do
        let term ← instantiateSurfacePat subst pat
        let terms ← instantiateSurfacePats subst rest
        some (.cons term terms)
end

def instantiateSurfaceAtom (subst : SurfaceSubst)
    (pattern : Presentation.AtomPat) : Option Atom :=
  (instantiateSurfacePats subst pattern.args).map (.atom pattern.pred)

def paramsCoveredB (params : List Presentation.Param) (subst : SurfaceSubst) : Bool :=
  params.all fun param => (lookupSurfaceSubst subst param).isSome

private def patsToList : Presentation.Pats → List Presentation.Pat
  | .nil => []
  | .cons pat rest => pat :: patsToList rest


private def decimalCharsToNat? : List Char → Nat → Option Nat
  | [], value => some value
  | char :: rest, value =>
      if !char.isDigit then none
      else decimalCharsToNat? rest (value * 10 + (char.val - '0'.val).toNat)

private def parseComparisonUnsignedDecimal? (chars : List Char) : Option Lara.Cell.Dec := do
  if !canonicalUnsignedDecimalCharsB chars then none else pure ()
  let split := splitDecimalChars chars
  let whole ← decimalCharsToNat? split.1 0
  match split.2 with
  | none => some ⟨(whole : Int), 1⟩
  | some fraction => do
      let fractional ← decimalCharsToNat? fraction 0
      let scale := 10 ^ fraction.length
      some ⟨((whole * scale + fractional : Nat) : Int), scale⟩

private def parseComparisonDecimal? (source : String) : Option Lara.Cell.Dec :=
  match source.toList with
  | '-' :: rest =>
      (parseComparisonUnsignedDecimal? rest).map fun decimal =>
        { decimal with num := -decimal.num }
  | chars => parseComparisonUnsignedDecimal? chars

def atomCellDecimal? : Atom → Option Lara.Cell.Dec
  | .atom _ terms =>
      match Lara.Cell.termsNums terms with
      | [number] => parseComparisonDecimal? (Lara.canonNum number)
      | _ => none

def comparisonOperandSlot? (subst baseSubst resultSubst : SurfaceSubst)
    (baseSlot resultSlot : Nat) (baseCell resultCell : Lara.Cell.Dec)
    (pattern : Presentation.Pat) : Option Nat :=
  let byDecimal : Option Nat := do
    let term ← instantiateSurfacePat subst pattern
    let .num number := term | none
    let decimal ← parseComparisonDecimal? number
    if Lara.Cell.ratEqB decimal baseCell then some baseSlot
    else if Lara.Cell.ratEqB decimal resultCell then some resultSlot
    else none
  match pattern with
  | .var param =>
      let inBase := (baseSubst.map (·.1)).contains param
      let inResult := (resultSubst.map (·.1)).contains param
      if inBase && !inResult then some baseSlot
      else if inResult && !inBase then some resultSlot
      else byDecimal
  | _ => byDecimal

private def matchingSlotsAux (patternAtoms : List Presentation.AtomPat)
    (proposition : Atom) (index : Nat) : List (Nat × SurfaceSubst) :=
  match patternAtoms with
  | [] => []
  | pattern :: rest =>
      let tail := matchingSlotsAux rest proposition (index + 1)
      match matchSurfaceAtom [] pattern proposition with
      | some subst => (index, subst) :: tail
      | none => tail

def matchingSlots (rule : Presentation.Rule) (proposition : Atom) :
    List (Nat × SurfaceSubst) :=
  matchingSlotsAux rule.premises proposition 0

private structure BridgeParts where
  conclusionPred : String
  systemParam : Presentation.Param
  baselineParam : Presentation.Param
  measurandParam : Presentation.Param
  datasetParam : Presentation.Param
  resultValueParam : Presentation.Param
  baselineValueParam : Presentation.Param
  bindingSlot : Nat
  bindingPattern : Presentation.AtomPat
  comparisonSlot : Nat
  comparisonPattern : Presentation.AtomPat

def bindingPatternValues (s b q d : Presentation.Param)
    (pattern : Presentation.AtomPat) :
    Option (Presentation.Param × Presentation.Param) :=
  match patsToList pattern.args with
  | [.var s', .var b', .var q', .var d', .var result, .var baseline] =>
      if s' = s && b' = b && q' = q && d' = d &&
          [s, b, q, d, result, baseline].Nodup then
        some (result, baseline)
      else none
  | _ => none

def bridgeParts? (rule : Presentation.Rule) : Option BridgeParts := do
  let (pred, s, b, q, d) ← match rule.conclusion with
    | ⟨pred, .cons (.var s) (.cons (.var b) (.cons (.var q) (.cons (.var d) .nil)))⟩ =>
        if [s, b, q, d].Nodup then some (pred, s, b, q, d) else none
    | _ => none
  match rule.premises with
  | [first, second] =>
      match bindingPatternValues s b q d first, bindingPatternValues s b q d second with
      | some values, none =>
          some ⟨pred, s, b, q, d, values.1, values.2, 0, first, 1, second⟩
      | none, some values =>
          some ⟨pred, s, b, q, d, values.1, values.2, 1, second, 0, first⟩
      | _, _ => none
  | _ => none

mutual
  def alignedSurfacePat : Presentation.Pat → Presentation.Pat →
      Option (List (Presentation.Param × Presentation.Param))
    | .var recheck, .var bridge => some [(recheck, bridge)]
    | .lit left, .lit right => if sameSurfaceTerm left right then some [] else none
    | .con leftName leftArgs, .con rightName rightArgs =>
        if leftName = rightName then alignedSurfacePats leftArgs rightArgs else none
    | _, _ => none
  def alignedSurfacePats : Presentation.Pats → Presentation.Pats →
      Option (List (Presentation.Param × Presentation.Param))
    | .nil, .nil => some []
    | .cons left lefts, .cons right rights => do
        let head ← alignedSurfacePat left right
        let tail ← alignedSurfacePats lefts rights
        some (head ++ tail)
    | _, _ => none
end

def alignedSurfaceAtoms (recheck bridge : Presentation.AtomPat) :
    Option (List (Presentation.Param × Presentation.Param)) :=
  if recheck.pred = bridge.pred then
    alignedSurfacePats recheck.args bridge.args
  else none

def correspondingRecheckParam
    (pairs : List (Presentation.Param × Presentation.Param))
    (bridgeParam : Presentation.Param) : Option Presentation.Param :=
  match (pairs.filter (fun pair => pair.2 == bridgeParam)).map (·.1) |>.eraseDups with
  | [param] => some param
  | _ => none


def recoverRecheckParam (rule : Presentation.Rule)
    (fallback : Presentation.Param) (attempt : Option Presentation.Param) :
    Option Presentation.Param :=
  match attempt with
  | some param => some param
  | none => if rule.params.contains fallback then some fallback else none

def roleParams (resultSubst baseSubst : SurfaceSubst) (term : Term) :
    List Presentation.Param :=
  ((resultSubst ++ baseSubst).filter
    (fun entry => sameSurfaceTerm entry.2 term)).map (·.1) |>.eraseDups

def roleSeed (params : List Presentation.Param) (term : Term) : SurfaceSubst :=
  params.map (fun param => (param, term))
def comparisonKey (comparison : Presentation.Comparison) :=
  (comparison.result, comparison.baseline, comparison.measurand,
    comparison.dataset, comparison.relation)

/-- The full data a `comparison` block expands to: the generated goal, the two
complete rule substitutions (each over its own rule's parameter order), the
two selected rules, the bridge's binding/comparison premise slots, the two
certificate premise slots, and the `ord@1` certifier reference.  Everything
`expandComparisons` emits is a deterministic function of this data, so the
emitted declarations are pinned by the reviewed goal computation in
`comparisonGoal?` (defined below as the goal projection of this function). -/
structure ComparisonExpansionData where
  goal : Atom
  thetaRecheck : SurfaceSubst
  thetaBridge : SurfaceSubst
  recheck : Presentation.Rule
  bridge : Presentation.Rule
  bridgeBindingSlot : Nat
  bridgeComparisonSlot : Nat
  slotLeft : Nat
  slotRight : Nat
  certRef : Presentation.CertRef
deriving DecidableEq

/-- The full comparison expansion computation, mirroring the production
`Lara.Elaborate.Comparison.expandComparison` on the shared helpers above.  Any
failure returns `none`; the caller reports it as its coarse `Surface.Error`. -/
def comparisonExpansion? (program : Presentation.Program) (policy : Presentation.Policy)
    (comparison : Presentation.Comparison) : Option ComparisonExpansionData := do
  let measurand ← policy.measurands.find? (fun m => decide (m.id = comparison.measurand))
  let polarity ← measurand.polarity
  let scheme ← policy.comparisonSchemes.find? fun s =>
    decide (s.relation = comparison.relation ∧ s.polarity = polarity)
  let recheck ← ruleById policy scheme.recheck
  let bridge ← ruleById policy scheme.bridge
  let (goalLeft, goalRight) ←
    match patsToList recheck.conclusion.args with
    | [left, right] => some (left, right)
    | _ => none
  if recheck.mode != .strict || bridge.mode != .defeasible then none else pure ()
  let certRef ← recheck.certifiers.find? fun cert =>
    decide (cert.backend.val == "ord" && cert.version == 1)
  let parts ← bridgeParts? bridge
  let aligned := alignedSurfaceAtoms recheck.conclusion parts.comparisonPattern
  let recheckResultParam ← recoverRecheckParam recheck parts.systemParam
    (aligned >>= fun pairs => correspondingRecheckParam pairs parts.resultValueParam)
  let recheckBaselineParam ← recoverRecheckParam recheck parts.baselineParam
    (aligned >>= fun pairs => correspondingRecheckParam pairs parts.baselineValueParam)
  let authored ← match comparison.conclusion with
    | .atom pred (.cons system (.cons baseline .nil)) => some (pred, system, baseline)
    | _ => none
  if authored.1 != parts.conclusionPred then none else pure ()
  if comparison.result = comparison.baseline then none else pure ()
  let resultProp ← leafProp? program comparison.result
  let baseProp ← leafProp? program comparison.baseline
  let bindingProp ← leafProp? program comparison.binding
  let resultCell ← atomCellDecimal? resultProp
  let baseCell ← atomCellDecimal? baseProp
  let resultMatches := (matchingSlots recheck resultProp).filter fun entry =>
    (lookupSurfaceSubst entry.2 recheckResultParam).isSome
  let baseMatches := (matchingSlots recheck baseProp).filter fun entry =>
    (lookupSurfaceSubst entry.2 recheckBaselineParam).isSome
  let (resultSlot, resultSubst) ← match resultMatches with | [entry] => some entry | _ => none
  let (baseSlot, baseSubst) ← match baseMatches with | [entry] => some entry | _ => none
  if resultSlot = baseSlot then none else pure ()
  let measurandTerm : Term := .con comparison.measurand.val .nil
  let datasetTerm : Term := .con comparison.dataset.val .nil
  let systemRoles := roleParams resultSubst baseSubst authored.2.1
  let baselineRoles := roleParams resultSubst baseSubst authored.2.2
  let measurandRoles := roleParams resultSubst baseSubst measurandTerm
  let datasetRoles := roleParams resultSubst baseSubst datasetTerm
  if systemRoles.isEmpty || baselineRoles.isEmpty ||
      measurandRoles.isEmpty || datasetRoles.isEmpty then none else pure ()
  let thetaSeed :=
    roleSeed systemRoles authored.2.1 ++ roleSeed baselineRoles authored.2.2 ++
    roleSeed measurandRoles measurandTerm ++ roleSeed datasetRoles datasetTerm
  let resultPattern ← recheck.premises[resultSlot]?
  let basePattern ← recheck.premises[baseSlot]?
  let merged ←
    if baseSlot < resultSlot then do
      let afterBase ← matchSurfaceAtom thetaSeed basePattern baseProp
      matchSurfaceAtom afterBase resultPattern resultProp
    else do
      let afterResult ← matchSurfaceAtom thetaSeed resultPattern resultProp
      matchSurfaceAtom afterResult basePattern baseProp
  if !paramsCoveredB recheck.params merged then none else pure ()
  let goal ← instantiateSurfaceAtom merged recheck.conclusion
  let slotLeft ← comparisonOperandSlot? merged baseSubst resultSubst
    baseSlot resultSlot baseCell resultCell goalLeft
  let slotRight ← comparisonOperandSlot? merged baseSubst resultSubst
    baseSlot resultSlot baseCell resultCell goalRight
  let expectedSlots := match polarity with
    | .higherIsBetter => (baseSlot, resultSlot)
    | .lowerIsBetter => (resultSlot, baseSlot)
  if (slotLeft, slotRight) != expectedSlots then none else pure ()
  let seed : SurfaceSubst :=
    [(parts.systemParam, authored.2.1), (parts.baselineParam, authored.2.2),
      (parts.measurandParam, measurandTerm), (parts.datasetParam, datasetTerm)]
  let bindingSubst ← matchSurfaceAtom seed parts.bindingPattern bindingProp
  let bridgeSubst ← matchSurfaceAtom bindingSubst parts.comparisonPattern goal
  if !paramsCoveredB bridge.params bridgeSubst then none else pure ()
  some ⟨goal, merged, bridgeSubst, recheck, bridge,
    parts.bindingSlot, parts.comparisonSlot, slotLeft, slotRight, certRef⟩

/-! ### Independent one-block comparison expansion specification -/

/-- A declarative witness for one comparison block's expansion.  Unlike
`comparisonExpansion?`, this proposition exposes every policy lookup, pattern
match, slot choice, polarity check, and substitution used to construct the
generated data. -/
def ComparisonExpansionSpec (program : Presentation.Program)
    (policy : Presentation.Policy) (comparison : Presentation.Comparison)
    (data : ComparisonExpansionData) : Prop :=
  ∃ (measurand : Presentation.Measurand)
    (polarity : Presentation.Polarity)
    (scheme : Presentation.ComparisonScheme)
    (recheck bridge : Presentation.Rule)
    (goalLeft goalRight : Presentation.Pat)
    (certRef : Presentation.CertRef)
    (parts : BridgeParts)
    (recheckResultParam recheckBaselineParam : Presentation.Param)
    (authoredPred : String) (systemTerm baselineTerm : Term)
    (resultProp baseProp bindingProp : Atom)
    (resultCell baseCell : Lara.Cell.Dec)
    (resultSlot baseSlot : Nat)
    (resultSubst baseSubst merged : SurfaceSubst)
    (goal : Atom)
    (slotLeft slotRight : Nat)
    (bindingSubst bridgeSubst : SurfaceSubst),
    policy.measurands.find? (fun m => decide (m.id = comparison.measurand)) =
      some measurand ∧
    measurand.polarity = some polarity ∧
    policy.comparisonSchemes.find? (fun s =>
      decide (s.relation = comparison.relation ∧ s.polarity = polarity)) =
      some scheme ∧
    ruleById policy scheme.recheck = some recheck ∧
    ruleById policy scheme.bridge = some bridge ∧
    patsToList recheck.conclusion.args = [goalLeft, goalRight] ∧
    recheck.mode = .strict ∧
    bridge.mode = .defeasible ∧
    recheck.certifiers.find? (fun cert =>
      decide (cert.backend.val == "ord" && cert.version == 1)) = some certRef ∧
    bridgeParts? bridge = some parts ∧
    recoverRecheckParam recheck parts.systemParam
      (alignedSurfaceAtoms recheck.conclusion parts.comparisonPattern >>=
        fun pairs => correspondingRecheckParam pairs parts.resultValueParam) =
      some recheckResultParam ∧
    recoverRecheckParam recheck parts.baselineParam
      (alignedSurfaceAtoms recheck.conclusion parts.comparisonPattern >>=
        fun pairs => correspondingRecheckParam pairs parts.baselineValueParam) =
      some recheckBaselineParam ∧
    comparison.conclusion =
      .atom authoredPred (.cons systemTerm (.cons baselineTerm .nil)) ∧
    authoredPred = parts.conclusionPred ∧
    comparison.result ≠ comparison.baseline ∧
    leafProp? program comparison.result = some resultProp ∧
    leafProp? program comparison.baseline = some baseProp ∧
    leafProp? program comparison.binding = some bindingProp ∧
    atomCellDecimal? resultProp = some resultCell ∧
    atomCellDecimal? baseProp = some baseCell ∧
    (matchingSlots recheck resultProp).filter (fun entry =>
      (lookupSurfaceSubst entry.2 recheckResultParam).isSome) =
      [(resultSlot, resultSubst)] ∧
    (matchingSlots recheck baseProp).filter (fun entry =>
      (lookupSurfaceSubst entry.2 recheckBaselineParam).isSome) =
      [(baseSlot, baseSubst)] ∧
    resultSlot ≠ baseSlot ∧
    let measurandTerm : Term := .con comparison.measurand.val .nil
    let datasetTerm : Term := .con comparison.dataset.val .nil
    let systemRoles := roleParams resultSubst baseSubst systemTerm
    let baselineRoles := roleParams resultSubst baseSubst baselineTerm
    let measurandRoles := roleParams resultSubst baseSubst measurandTerm
    let datasetRoles := roleParams resultSubst baseSubst datasetTerm
    systemRoles ≠ [] ∧
    baselineRoles ≠ [] ∧
    measurandRoles ≠ [] ∧
    datasetRoles ≠ [] ∧
    let thetaSeed :=
      roleSeed systemRoles systemTerm ++ roleSeed baselineRoles baselineTerm ++
      roleSeed measurandRoles measurandTerm ++ roleSeed datasetRoles datasetTerm
    ∃ (resultPattern basePattern : Presentation.AtomPat),
      recheck.premises[resultSlot]? = some resultPattern ∧
      recheck.premises[baseSlot]? = some basePattern ∧
      (if baseSlot < resultSlot then do
          let afterBase ← matchSurfaceAtom thetaSeed basePattern baseProp
          matchSurfaceAtom afterBase resultPattern resultProp
        else do
          let afterResult ← matchSurfaceAtom thetaSeed resultPattern resultProp
          matchSurfaceAtom afterResult basePattern baseProp) = some merged ∧
      paramsCoveredB recheck.params merged = true ∧
      instantiateSurfaceAtom merged recheck.conclusion = some goal ∧
      comparisonOperandSlot? merged baseSubst resultSubst
        baseSlot resultSlot baseCell resultCell goalLeft = some slotLeft ∧
      comparisonOperandSlot? merged baseSubst resultSubst
        baseSlot resultSlot baseCell resultCell goalRight = some slotRight ∧
      (slotLeft, slotRight) =
        (match polarity with
        | .higherIsBetter => (baseSlot, resultSlot)
        | .lowerIsBetter => (resultSlot, baseSlot)) ∧
      let seed : SurfaceSubst :=
        [(parts.systemParam, systemTerm), (parts.baselineParam, baselineTerm),
          (parts.measurandParam, measurandTerm), (parts.datasetParam, datasetTerm)]
      matchSurfaceAtom seed parts.bindingPattern bindingProp = some bindingSubst ∧
      matchSurfaceAtom bindingSubst parts.comparisonPattern goal = some bridgeSubst ∧
      paramsCoveredB bridge.params bridgeSubst = true ∧
      data = ⟨goal, merged, bridgeSubst, recheck, bridge,
        parts.bindingSlot, parts.comparisonSlot, slotLeft, slotRight, certRef⟩

set_option maxHeartbeats 4000000 in
theorem comparisonExpansion?_sound {program : Presentation.Program}
    {policy : Presentation.Policy} {comparison : Presentation.Comparison}
    {data : ComparisonExpansionData}
    (h : comparisonExpansion? program policy comparison = some data) :
    ComparisonExpansionSpec program policy comparison data := by
  simp only [comparisonExpansion?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  rcases h with
    ⟨measurand, hmeasurand, polarity, hpolarity, scheme, hscheme,
      recheck, hrecheck, bridge, hbridge, h⟩
  split at h
  · rename_i goalLeft goalRight hgoalShape
    cases hmodes :
        (recheck.mode != Presentation.Mode.strict ||
          bridge.mode != Presentation.Mode.defeasible) with
    | true => simp [hmodes] at h
    | false =>
      have hmodes' := hmodes
      simp only [hmodes, Bool.false_eq_true, if_false, Option.bind_some] at h
      simp only [Option.bind_eq_some_iff] at h
      rcases h with
        ⟨certRef, hcertRef, parts, hparts,
          recheckResultParam, hresultParam,
          recheckBaselineParam, hbaselineParam, h⟩
      split at h
      · rename_i authoredPred systemTerm baselineTerm hauthored
        cases hpredBool : authoredPred != parts.conclusionPred with
        | true => simp [hpredBool] at h
        | false =>
          have hpred : authoredPred = parts.conclusionPred := by
            simpa using hpredBool
          simp only [hpredBool, Bool.false_eq_true, if_false, Option.bind_some] at h
          by_cases heq : comparison.result = comparison.baseline
          · simp [heq] at h
          · have hdistinct := heq
            simp only [heq, if_false] at h
            simp only [Option.bind_eq_some_iff] at h
            rcases h with
              ⟨resultProp, hresultProp, baseProp, hbaseProp,
                bindingProp, hbindingProp, resultCell, hresultCell,
                baseCell, hbaseCell, h⟩
            split at h
            · rename_i resultEntry hresultMatches
              rcases resultEntry with ⟨resultSlot, resultSubst⟩
              split at h
              · rename_i baseEntry hbaseMatches
                rcases baseEntry with ⟨baseSlot, baseSubst⟩
                by_cases hslotsEq : resultSlot = baseSlot
                · rw [if_pos hslotsEq] at h
                  simp at h
                · rw [if_neg hslotsEq] at h
                  have hslots := hslotsEq
                  cases hrolesBool :
                      ((roleParams resultSubst baseSubst systemTerm).isEmpty ||
                        (roleParams resultSubst baseSubst baselineTerm).isEmpty ||
                        (roleParams resultSubst baseSubst
                          (.con comparison.measurand.val .nil)).isEmpty ||
                        (roleParams resultSubst baseSubst
                          (.con comparison.dataset.val .nil)).isEmpty) with
                  | true => simp [hrolesBool] at h
                  | false =>
                    have hroles := hrolesBool
                    simp only [hrolesBool, Bool.false_eq_true, if_false] at h
                    by_cases hlt : baseSlot < resultSlot <;>
                      simp [hlt, Option.bind_eq_some_iff] at h
                    all_goals
                      rcases h with
                        ⟨resultPattern, hresultPattern, basePattern, hbasePattern,
                          afterFirst, hfirstMatch, h⟩
                      rcases h with ⟨merged, hsecondMatch, h⟩
                      have hmergedFull :
                          (if baseSlot < resultSlot then do
                              let afterBase ← matchSurfaceAtom
                                (roleSeed (roleParams resultSubst baseSubst systemTerm) systemTerm ++
                                  roleSeed (roleParams resultSubst baseSubst baselineTerm) baselineTerm ++
                                  roleSeed (roleParams resultSubst baseSubst
                                    (.con comparison.measurand.val .nil))
                                    (.con comparison.measurand.val .nil) ++
                                  roleSeed (roleParams resultSubst baseSubst
                                    (.con comparison.dataset.val .nil))
                                    (.con comparison.dataset.val .nil))
                                basePattern baseProp
                              matchSurfaceAtom afterBase resultPattern resultProp
                            else do
                              let afterResult ← matchSurfaceAtom
                                (roleSeed (roleParams resultSubst baseSubst systemTerm) systemTerm ++
                                  roleSeed (roleParams resultSubst baseSubst baselineTerm) baselineTerm ++
                                  roleSeed (roleParams resultSubst baseSubst
                                    (.con comparison.measurand.val .nil))
                                    (.con comparison.measurand.val .nil) ++
                                  roleSeed (roleParams resultSubst baseSubst
                                    (.con comparison.dataset.val .nil))
                                    (.con comparison.dataset.val .nil))
                                resultPattern resultProp
                              matchSurfaceAtom afterResult basePattern baseProp) =
                            some merged := by
                        simp [hlt, hfirstMatch, hsecondMatch]
                      rcases h with
                        ⟨hcovered, goal, hgoal, slotLeft, hslotLeft,
                          slotRight, hslotRight, hpolaritySlots,
                          bindingSubst, hbindingSubst, bridgeSubst,
                          hbridgeSubst, hbridgeCovered, hdata⟩
                      have hrecheckMode : recheck.mode = .strict := by
                        simp_all
                      have hbridgeMode : bridge.mode = .defeasible := by
                        simp_all
                      have hsystemRoles :
                          roleParams resultSubst baseSubst systemTerm ≠ [] := by
                        simp_all
                      have hbaselineRoles :
                          roleParams resultSubst baseSubst baselineTerm ≠ [] := by
                        simp_all
                      have hmeasurandRoles :
                          roleParams resultSubst baseSubst
                            (.con comparison.measurand.val .nil) ≠ [] := by
                        simp_all
                      have hdatasetRoles :
                          roleParams resultSubst baseSubst
                            (.con comparison.dataset.val .nil) ≠ [] := by
                        simp_all
                      refine ⟨measurand, polarity, scheme, recheck, bridge,
                        goalLeft, goalRight, certRef, parts,
                        recheckResultParam, recheckBaselineParam,
                        authoredPred, systemTerm, baselineTerm,
                        resultProp, baseProp, bindingProp, resultCell, baseCell,
                        resultSlot, baseSlot, resultSubst, baseSubst, merged,
                        goal, slotLeft, slotRight, bindingSubst, bridgeSubst,
                        hmeasurand, hpolarity, hscheme, hrecheck, hbridge,
                        hgoalShape, hrecheckMode, hbridgeMode, hcertRef, hparts,
                        hresultParam, hbaselineParam, hauthored, hpred,
                        hdistinct, hresultProp, hbaseProp, hbindingProp,
                        hresultCell, hbaseCell, hresultMatches,
                        hbaseMatches, hslots, hsystemRoles,
                        hbaselineRoles, hmeasurandRoles, hdatasetRoles,
                        resultPattern, basePattern, hresultPattern,
                        hbasePattern, hmergedFull, hcovered, hgoal, hslotLeft,
                        hslotRight, hpolaritySlots, hbindingSubst,
                        hbridgeSubst, hbridgeCovered, hdata.symm⟩
              · simp at h
            · simp at h
      · simp at h
  · simp at h

set_option maxHeartbeats 4000000 in
theorem comparisonExpansion?_complete {program : Presentation.Program}
    {policy : Presentation.Policy} {comparison : Presentation.Comparison}
    {data : ComparisonExpansionData}
    (h : ComparisonExpansionSpec program policy comparison data) :
    comparisonExpansion? program policy comparison = some data := by
  rcases h with
    ⟨measurand, polarity, scheme, recheck, bridge, goalLeft, goalRight,
      certRef, parts, recheckResultParam, recheckBaselineParam,
      authoredPred, systemTerm, baselineTerm,
      resultProp, baseProp, bindingProp, resultCell, baseCell,
      resultSlot, baseSlot, resultSubst, baseSubst, merged,
      goal, slotLeft, slotRight, bindingSubst, bridgeSubst,
      hmeasurand, hpolarity, hscheme, hrecheck, hbridge, hgoalShape,
      hrecheckMode, hbridgeMode, hcertRef, hparts, hresultParam,
      hbaselineParam, hauthored, hpred, hdistinct, hresultProp,
      hbaseProp, hbindingProp, hresultCell, hbaseCell,
      hresultMatches, hbaseMatches, hslots, hsystemRoles,
      hbaselineRoles, hmeasurandRoles, hdatasetRoles,
      resultPattern, basePattern, hresultPattern, hbasePattern,
      hmerged, hcovered, hgoal, hslotLeft, hslotRight,
      hpolaritySlots, hbindingSubst, hbridgeSubst, hbridgeCovered, hdata⟩
  have hscheme' :
      policy.comparisonSchemes.find? (fun s =>
        decide (s.relation = comparison.relation) &&
          decide (s.polarity = polarity)) = some scheme := by
    simpa using hscheme
  have hcertRef' :
      recheck.certifiers.find? (fun cert =>
        decide (cert.backend.val = "ord") &&
          decide (cert.version = 1)) = some certRef := by
    simpa using hcertRef
  have hresultParam' :
      recoverRecheckParam recheck parts.systemParam
        ((alignedSurfaceAtoms recheck.conclusion parts.comparisonPattern).bind
          fun pairs => correspondingRecheckParam pairs parts.resultValueParam) =
        some recheckResultParam := by
    simpa [Option.bind_eq_bind] using hresultParam
  have hbaselineParam' :
      recoverRecheckParam recheck parts.baselineParam
        ((alignedSurfaceAtoms recheck.conclusion parts.comparisonPattern).bind
          fun pairs => correspondingRecheckParam pairs parts.baselineValueParam) =
        some recheckBaselineParam := by
    simpa [Option.bind_eq_bind] using hbaselineParam
  unfold comparisonExpansion?
  simp [hmeasurand, hpolarity, hscheme', hrecheck, hbridge, hgoalShape,
    hrecheckMode, hbridgeMode, hcertRef', hparts, hresultParam',
    hbaselineParam', hauthored, hpred, hdistinct, hresultProp,
    hbaseProp, hbindingProp, hresultCell, hbaseCell,
    hresultMatches, hbaseMatches, hslots, hsystemRoles,
    hbaselineRoles, hmeasurandRoles, hdatasetRoles,
    hresultPattern, hbasePattern, hmerged, hcovered, hgoal,
    hslotLeft, hslotRight, hpolaritySlots, hbindingSubst,
    hbridgeSubst, hbridgeCovered, hdata]
  by_cases hlt : baseSlot < resultSlot <;>
    simp [hlt, ← Option.bind_assoc] at hmerged ⊢ <;>
    simp [hmerged, hcovered, hgoal, hslotLeft, hslotRight,
      hpolaritySlots, hbridgeSubst, hbridgeCovered, hdata]

/-- The goal projection of the full expansion: the recheck rule's conclusion
under the merged θ, exactly as the validation judgment consumes it. -/
private def comparisonGoal? (program : Presentation.Program) (policy : Presentation.Policy)
    (comparison : Presentation.Comparison) : Option Atom :=
  (comparisonExpansion? program policy comparison).map (·.goal)


def comparisonCoreValid (program : Presentation.Program)
    (policy : Presentation.Policy) (comparison : Presentation.Comparison) : Prop :=
  (∃ goal, comparisonGoal? program policy comparison = some goal) ∧
  (match comparison.supports with
   | none => True
   | some claim => claim ∈ claimIds program)

def comparisonCoreValidB (program : Presentation.Program)
    (policy : Presentation.Policy) (comparison : Presentation.Comparison) : Bool :=
  (comparisonGoal? program policy comparison).isSome &&
  (match comparison.supports with
   | none => true
   | some claim => (claimIds program).contains claim)

private theorem comparisonCoreValidB_iff (program : Presentation.Program)
    (policy : Presentation.Policy) (comparison : Presentation.Comparison) :
    comparisonCoreValidB program policy comparison = true ↔
      comparisonCoreValid program policy comparison := by
  unfold comparisonCoreValidB comparisonCoreValid comparisonGoal?
  cases h : comparisonExpansion? program policy comparison with
  | none =>
      cases comparison.supports <;> simp
  | some data =>
      cases comparison.supports <;> simp

def comparisonKeys (program : Presentation.Program) :=
  (comparisonDecls program).map comparisonKey

def ComparisonsWellFormed (program : Presentation.Program)
    (policy : Presentation.Policy) : Prop :=
  (comparisonKeys program).Nodup ∧
  ∀ comparison ∈ comparisonDecls program,
    comparisonCoreValid program policy comparison
def comparisonsWellFormedB (program : Presentation.Program)
    (policy : Presentation.Policy) : Bool :=
  decide (comparisonKeys program).Nodup &&
  (comparisonDecls program).all (comparisonCoreValidB program policy)

theorem comparisonsWellFormedB_iff (program : Presentation.Program)
    (policy : Presentation.Policy) :
    comparisonsWellFormedB program policy = true ↔
      ComparisonsWellFormed program policy := by
  simp [comparisonsWellFormedB, ComparisonsWellFormed,
    comparisonCoreValidB_iff] <;> grind

/-! Typed inference state. -/

structure PriorArgument where
  id : Presentation.ArgId
  term : Presentation.SupportTerm
  conclusion : Atom
deriving DecidableEq

structure ResolvedReference where
  term : Presentation.SupportTerm
  conclusion : Atom
  leafSource : Option Presentation.LeafId
  argumentSource : Option Presentation.ArgId
deriving DecidableEq

def resolveReference (program : Presentation.Program)
    (priors : List PriorArgument) (reference : Presentation.ArgRef) :
    Option ResolvedReference :=
  let leaves := (declaredLeaves program).filter (fun entry => entry.1.val == reference.val)
  let arguments := priors.filter (fun prior => prior.id.val == reference.val)
  match leaves, arguments with
  | [(leaf, proposition)], [] =>
      some ⟨.leaf leaf, proposition, some leaf, none⟩
  | [], [argument] =>
      some ⟨argument.term, argument.conclusion, none, some argument.id⟩
  | _, _ => none

def supportTermsFromList : List Presentation.SupportTerm → Presentation.SupportTerms
  | [] => .nil
  | term :: rest => .cons term (supportTermsFromList rest)

def dischargesFromList :
    List (Presentation.QuestionId × Presentation.SupportTerm) → Presentation.Discharges
  | [] => .nil
  | (question, term) :: rest => .cons question term (dischargesFromList rest)

def conclOfTerm (program : Presentation.Program) (policy : Presentation.Policy) :
    Presentation.SupportTerm → Option Atom
  | .leaf leaf => leafProp? program leaf
  | .rule rule subst _ _ _ _ => do
      let scheme ← ruleById policy rule
      instantiateSurfaceAtom subst scheme.conclusion

def matchResolvedPremises : SurfaceSubst → List Presentation.AtomPat →
    List ResolvedReference → Option SurfaceSubst
  | subst, [], [] => some subst
  | subst, pattern :: patterns, reference :: references => do
      let next ← matchSurfaceAtom subst pattern reference.conclusion
      matchResolvedPremises next patterns references
  | _, _, _ => none

def resolveReferences (program : Presentation.Program) (priors : List PriorArgument) :
    List Presentation.ArgRef → Option (List ResolvedReference)
  | [] => some []
  | reference :: rest => do
      let resolved ← resolveReference program priors reference
      let resolvedRest ← resolveReferences program priors rest
      some (resolved :: resolvedRest)

def resolveNamedDischarges (program : Presentation.Program)
    (priors : List PriorArgument) (rule : Presentation.Rule) :
    Presentation.ArgDischarge → Option (List (Presentation.QuestionId × Presentation.SupportTerm))
  | [] => some []
  | (question, reference) :: rest => do
      if !(questionIds rule).contains question then none else pure ()
      let resolved ← resolveReference program priors reference
      let resolvedRest ← resolveNamedDischarges program priors rule rest
      some ((question, resolved.term) :: resolvedRest)

/-! Production-parser explicit-term reconstruction.

`Lara.Syntax` records `by r(t₁,…,tₙ)` with synthetic positional substitution
keys `"1".."n"` and an empty premise spine.  The complete presentation model
also admits already-enriched terms (the original M5 witnesses).  The supported
fragment must accept both: re-associate only the parser-shallow arm, preserving
the enriched arm verbatim.  Canonical premise matching uses the production
numeric canonicalizer; the independent checker still derives its own
`ChecksImplicitPremises` proof and is not defined through elaboration. -/

def parserPremiseMatches (program : Presentation.Program)
    (priors : List PriorArgument) (ground : Atom) :
    List Presentation.SupportTerm :=
  (declaredLeaves program).filterMap (fun entry =>
    if equiv Lara.canonNum entry.2 ground then some (.leaf entry.1) else none) ++
  priors.filterMap (fun prior =>
    if equiv Lara.canonNum prior.conclusion ground then some prior.term else none)

def parserResolveImplicitPremise (program : Presentation.Program)
    (priors : List PriorArgument) (theta : SurfaceSubst)
    (pattern : Presentation.AtomPat) : Option Presentation.SupportTerm := do
  let ground ← instantiateSurfaceAtom theta pattern
  match parserPremiseMatches program priors ground with
  | [term] => some term
  | _ => none

def parserResolveImplicitPremises (program : Presentation.Program)
    (priors : List PriorArgument) (theta : SurfaceSubst) :
    List Presentation.AtomPat → Option Presentation.SupportTerms
  | [] => some .nil
  | pattern :: rest => do
      let term ← parserResolveImplicitPremise program priors theta pattern
      let terms ← parserResolveImplicitPremises program priors theta rest
      some (.cons term terms)

def parserResolveExplicitDischarges (program : Presentation.Program)
    (priors : List PriorArgument) :
    Presentation.Discharges → Option Presentation.Discharges
  | .nil => some .nil
  | .cons question (.leaf leaf) rest => do
      let rebuilt ← (resolveReference program priors ⟨leaf.val⟩).map (·.term)
      let rebuiltRest ← parserResolveExplicitDischarges program priors rest
      some (.cons question rebuilt rebuiltRest)
  | .cons _ (.rule ..) _ => none

def parserReconstructExplicitTerm (program : Presentation.Program)
    (policy : Presentation.Policy) (priors : List PriorArgument) :
    Presentation.SupportTerm → Option Presentation.SupportTerm
  | term@(.leaf _) => some term
  | .rule ruleId positionalTheta .nil shallowDischarges holes assurance => do
      let rule ← ruleById policy ruleId
      if positionalTheta.length != rule.params.length then none else pure ()
      let theta := rule.params.zip (positionalTheta.map Prod.snd)
      let premises ← parserResolveImplicitPremises program priors theta rule.premises
      let discharges ← parserResolveExplicitDischarges program priors shallowDischarges
      some (.rule ruleId theta premises discharges holes assurance)
  | term@(.rule _ _ (.cons _ _) _ _ _) => some term

def buildArgument (program : Presentation.Program) (policy : Presentation.Policy)
    (priors : List PriorArgument) (argument : Presentation.Arg) : Option PriorArgument :=
  match argument.instantiation with
  | .explicitTheta term => do
      let rebuilt ← parserReconstructExplicitTerm program policy priors term
      let conclusion ← conclOfTerm program policy rebuilt
      some ⟨argument.id, rebuilt, conclusion⟩
  | .inferTheta ruleId refs discharges holes assurance => do
      let rule ← ruleById policy ruleId
      if refs.length != rule.premises.length then none else pure ()
      let resolved ← resolveReferences program priors refs
      let subst ← matchResolvedPremises [] rule.premises resolved
      if !paramsCoveredB rule.params subst then none else pure ()
      let dischargeTerms ← resolveNamedDischarges program priors rule discharges
      let term := Presentation.SupportTerm.rule ruleId subst
        (supportTermsFromList (resolved.map (·.term)))
        (dischargesFromList dischargeTerms) holes assurance
      let conclusion ← instantiateSurfaceAtom subst rule.conclusion
      some ⟨argument.id, term, conclusion⟩

def generatedComparisonArguments (program : Presentation.Program)
    (policy : Presentation.Policy) (comparison : Presentation.Comparison) :
    Option (PriorArgument × PriorArgument) := do
  let goal ← comparisonGoal? program policy comparison
  let measurand ← policy.measurands.find? (fun m => decide (m.id = comparison.measurand))
  let polarity ← measurand.polarity
  let scheme ← policy.comparisonSchemes.find? fun s =>
    decide (s.relation = comparison.relation ∧ s.polarity = polarity)
  let recheck ← ruleById policy scheme.recheck
  let bridge ← ruleById policy scheme.bridge
  let recheckTerm := Presentation.SupportTerm.rule recheck.id []
    (supportTermsFromList [.leaf comparison.result, .leaf comparison.baseline])
    .nil [] .none
  let bridgeTerm := Presentation.SupportTerm.rule bridge.id []
    (supportTermsFromList [.leaf comparison.binding, recheckTerm]) .nil [] .none
  let bridgeConclusion ← match comparison.conclusion with
    | .atom pred (.cons system (.cons baseline .nil)) =>
        some (.atom pred (.cons system (.cons baseline
          (.cons (.con comparison.measurand.val .nil)
            (.cons (.con comparison.dataset.val .nil) .nil)))))
    | _ => none
  some (⟨comparison.recheckArg, recheckTerm, goal⟩,
    ⟨comparison.bridgeArg, bridgeTerm, bridgeConclusion⟩)

def buildProgramArguments (program : Presentation.Program)
    (policy : Presentation.Policy) : List Presentation.Decl → List PriorArgument →
    Option (List PriorArgument)
  | [], priors => some priors
  | .arg argument :: rest, priors => do
      let prior ← buildArgument program policy priors argument
      buildProgramArguments program policy rest (priors ++ [prior])
  | .comparison comparison :: rest, priors =>
      match generatedComparisonArguments program policy comparison with
      | none => buildProgramArguments program policy rest priors
      | some generated =>
          buildProgramArguments program policy rest (priors ++ [generated.1, generated.2])
  | _ :: rest, priors => buildProgramArguments program policy rest priors

def collectProgramArguments (program : Presentation.Program)
    (policy : Presentation.Policy) : List Presentation.Decl → List PriorArgument →
    List PriorArgument
  | [], priors => priors
  | .arg argument :: rest, priors =>
      match buildArgument program policy priors argument with
      | none => collectProgramArguments program policy rest priors
      | some prior =>
          collectProgramArguments program policy rest (priors ++ [prior])
  | .comparison comparison :: rest, priors =>
      match generatedComparisonArguments program policy comparison with
      | none => collectProgramArguments program policy rest priors
      | some generated =>
          collectProgramArguments program policy rest
            (priors ++ [generated.1, generated.2])
  | _ :: rest, priors => collectProgramArguments program policy rest priors

def InferredArgsWellFormed (program : Presentation.Program)
    (policy : Presentation.Policy) : Prop :=
  ∃ priors, buildProgramArguments program policy program.decls [] = some priors

def inferredArgsWellFormedB (program : Presentation.Program)
    (policy : Presentation.Policy) : Bool :=
  (buildProgramArguments program policy program.decls []).isSome

theorem inferredArgsWellFormedB_iff (program : Presentation.Program)
    (policy : Presentation.Policy) :
    inferredArgsWellFormedB program policy = true ↔
      InferredArgsWellFormed program policy := by
  unfold inferredArgsWellFormedB InferredArgsWellFormed
  cases buildProgramArguments program policy program.decls [] <;> simp

/-! Backend-specific certificate validation. -/
private def asciiAlphaB (char : Char) : Bool :=
  ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M',
    'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
    'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
    'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'].contains char

private def sourceAlphaB (char : Char) : Bool :=
  asciiAlphaB char || char.isAlpha

def sourceStartsIdentifier (source : String) : Bool :=
  match source.toList with
  | [] => false
  | char :: _ => sourceAlphaB char || char == '_'
private def surfaceWhitespaceB (char : Char) : Bool :=
  char == ' ' || char == '\t' || char == '\n' || char == '\r'

private def skipSurfaceWhitespace : List Char → List Char
  | char :: rest =>
      if surfaceWhitespaceB char then skipSurfaceWhitespace rest else char :: rest
  | [] => []

private def sourceIdentifierCharB (char : Char) : Bool :=
  sourceAlphaB char || char.isDigit || char == '_' || char == '-'

private def takeWhileChars (predicate : Char → Bool) :
    List Char → List Char × List Char
  | [] => ([], [])
  | char :: rest =>
      if predicate char then
        let taken := takeWhileChars predicate rest
        (char :: taken.1, taken.2)
      else ([], char :: rest)

private def takeSourceIdentifier (chars : List Char) : Option (String × List Char) :=
  match chars with
  | first :: _ =>
      if sourceAlphaB first || first == '_' then
        let taken := takeWhileChars sourceIdentifierCharB chars
        some (String.ofList taken.1, taken.2)
      else none
  | [] => none

private def surfaceNumberUnsignedB (chars : List Char) : Bool :=
  let split := splitDecimalChars chars
  !split.1.isEmpty && split.1.all Char.isDigit &&
    match split.2 with
    | none => true
    | some fraction => !fraction.isEmpty && fraction.all Char.isDigit

private def surfaceNumberTokenB : List Char → Bool
  | '+' :: rest => surfaceNumberUnsignedB rest
  | '-' :: rest => surfaceNumberUnsignedB rest
  | chars => surfaceNumberUnsignedB chars

private def numberTokenCharB (char : Char) : Bool :=
  char.isDigit || char == '+' || char == '-' || char == '.'

mutual
  private def parseSurfaceTermFuel : Nat → List Char → Option (Term × List Char)
    | 0, _ => none
    | fuel + 1, input =>
        let chars := skipSurfaceWhitespace input
        match chars with
        | first :: _ =>
            if first.isDigit || first == '+' || first == '-' then
              let token := takeWhileChars numberTokenCharB chars
              if surfaceNumberTokenB token.1 then
                some (.num (String.ofList token.1), token.2)
              else none
            else do
              let (name, afterName) ← takeSourceIdentifier chars
              match skipSurfaceWhitespace afterName with
              | '(' :: afterOpen => do
                  let (arguments, afterArgs) ← parseSurfaceTermArgsFuel fuel afterOpen
                  some (.con name arguments, afterArgs)
              | rest => some (.con name .nil, rest)
        | [] => none
  private def parseSurfaceTermArgsFuel : Nat → List Char → Option (Terms × List Char)
    | 0, _ => none
    | fuel + 1, input =>
        match skipSurfaceWhitespace input with
        | ')' :: rest => some (.nil, rest)
        | chars => do
            let (term, afterTerm) ← parseSurfaceTermFuel fuel chars
            match skipSurfaceWhitespace afterTerm with
            | ',' :: rest => do
                let (terms, afterTerms) ← parseSurfaceTermArgsFuel fuel rest
                match terms with
                | .nil => none
                | _ => some (.cons term terms, afterTerms)
            | ')' :: rest => some (.cons term .nil, rest)
            | _ => none
end

def parseSurfaceProp (source : String) : Option Atom := do
  let chars := skipSurfaceWhitespace source.toList
  let (predicate, afterPredicate) ← takeSourceIdentifier chars
  let (arguments, rest) ←
    match skipSurfaceWhitespace afterPredicate with
    | '(' :: afterOpen =>
        parseSurfaceTermArgsFuel (source.toList.length + 1) afterOpen
    | rest => some (.nil, rest)
  if (skipSurfaceWhitespace rest).isEmpty then
    some (.atom predicate arguments)
  else none

def PropTextWellFormed (source : String) : Prop :=
  ∃ proposition, parseSurfaceProp source = some proposition

def propTextWellFormedB (source : String) : Bool :=
  (parseSurfaceProp source).isSome

theorem propTextWellFormedB_iff (source : String) :
    propTextWellFormedB source = true ↔ PropTextWellFormed source := by
  unfold propTextWellFormedB PropTextWellFormed
  cases parseSurfaceProp source <;> simp

def supportTermsToList : Presentation.SupportTerms → List Presentation.SupportTerm
  | .nil => []
  | .cons term rest => term :: supportTermsToList rest

def dischargeTermsToList : Presentation.Discharges →
    List (Presentation.QuestionId × Presentation.SupportTerm)
  | .nil => []
  | .cons question term rest => (question, term) :: dischargeTermsToList rest

def labelIndex? (rule : Presentation.Rule) (name : String) : Option Nat :=
  let indexed := rule.premiseLabels.zipIdx
  match indexed.filter (fun pair =>
      match pair.1 with | some label => label.val == name | none => false) with
  | [(_, index)] => some index
  | _ => none

def locateUniqueTerm (candidates : List Presentation.SupportTerm)
    (premises : List Presentation.SupportTerm) : Option Nat :=
  let indices := premises.zipIdx.filter (fun pair => candidates.contains pair.1) |>.map (·.2)
  match indices with
  | [index] => some index
  | _ => none

def certificateResolver (program : Presentation.Program)
    (rule : Presentation.Rule) (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm) (name : String) : Option Nat :=
  let leaves := (declaredLeaves program).filter (fun entry => entry.1.val == name)
  let arguments := priors.filter (fun prior => prior.id.val == name)

  let label := labelIndex? rule name
  match label, leaves, arguments with
  | some index, [], [] => if index < premises.length then some index else none
  | some _, _, _ => none
  | none, [(leaf, _)], [] => locateUniqueTerm [.leaf leaf] premises
  | none, [], [argument] =>
      locateUniqueTerm [argument.term, .leaf ⟨argument.id.val⟩] premises
  | _, _, _ => none
private def digitValue? : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
  | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
  | '8' => some 8 | '9' => some 9 | _ => none

private def parseNatDigits : List Char → Nat → Option Nat
  | [], value => some value
  | char :: rest, value => do
      let digit ← digitValue? char
      parseNatDigits rest (value * 10 + digit)

private def parseCanonicalNat (source : String) : Option Nat :=
  match source.toList with
  | [] => none
  | ['0'] => some 0
  | '0' :: _ => none
  | chars => parseNatDigits chars 0

private def namedMarkerHereB : Presentation.Sx → Bool
  | .node head (.cons (.str source) .nil) =>
      head == Lara.Cell.Tag.prem.toString ||
      head == Lara.NDNamed.NamedTag.thy.toString ||
      head == Lara.NDNamed.NamedTag.prop.toString ||
        (head == Lara.ND.Tag.hyp.toString && sourceStartsIdentifier source)
  | .node head (.cons (.str _) (.cons _ (.cons _ .nil))) =>
      head == Lara.ND.Tag.lam.toString
  | _ => false

mutual
  private def hasNamedMarkerB : Presentation.Sx → Bool
    | expr@(.node _ children) =>
        namedMarkerHereB expr || hasNamedMarkerListB children
    | _ => false
  private def hasNamedMarkerListB : Presentation.SxList → Bool
    | .nil => false
    | .cons expr rest => hasNamedMarkerB expr || hasNamedMarkerListB rest
end

private def namedFormulaValidB : Presentation.Sx → Bool
  | .str _ => true
  | .node "prop" (.cons (.str text) .nil) =>
      propTextWellFormedB text
  | .node "atom" (.cons (.str _) .nil) => true
  | .node "imp" (.cons left (.cons right .nil)) =>
      namedFormulaValidB left && namedFormulaValidB right
  | expr => !hasNamedMarkerB expr

private def namedNdExprValidB (resolver : String → Option Nat) (premiseCount : Nat) :
    List (Option String) → Presentation.Sx → Bool
  | _, .str _ => true
  | _, .int _ => true
  | _, .node "prem" (.cons (.str source) .nil) =>
      match parseCanonicalNat source with
      | some slot => slot < premiseCount
      | none => sourceStartsIdentifier source && (resolver source).isSome
  | _, .node "thy" (.cons (.str source) .nil) =>
      (parseCanonicalNat source).isSome
  | binders, .node "hyp" (.cons (.str source) .nil) =>
      (parseCanonicalNat source).isNone && sourceStartsIdentifier source &&
        binders.contains (some source)
  | binders, .node "lam" (.cons formula (.cons body .nil)) =>
      namedFormulaValidB formula &&
        namedNdExprValidB resolver premiseCount (none :: binders) body
  | binders, .node "lam" (.cons (.str binder) (.cons formula (.cons body .nil))) =>
      sourceStartsIdentifier binder && !binders.contains (some binder) &&
        (resolver binder).isNone && namedFormulaValidB formula &&
        namedNdExprValidB resolver premiseCount (some binder :: binders) body
  | binders, .node "app" (.cons function (.cons argument .nil)) =>
      namedNdExprValidB resolver premiseCount binders function &&
        namedNdExprValidB resolver premiseCount binders argument
  | binders, .node "abort" (.cons formula (.cons body .nil)) =>
      namedFormulaValidB formula &&
        namedNdExprValidB resolver premiseCount binders body
  | _, expr => !hasNamedMarkerB expr

private def NamedFormulaWellFormed : Presentation.Sx → Prop
  | .str _ => True
  | .node "prop" (.cons (.str text) .nil) => PropTextWellFormed text
  | .node "atom" (.cons (.str _) .nil) => True
  | .node "imp" (.cons left (.cons right .nil)) =>
      NamedFormulaWellFormed left ∧ NamedFormulaWellFormed right
  | expr => !hasNamedMarkerB expr = true

private theorem namedFormulaValidB_iff :
    ∀ formula, namedFormulaValidB formula = true ↔
      NamedFormulaWellFormed formula
  | .str source => by simp [namedFormulaValidB, NamedFormulaWellFormed]
  | .int value => by simp [namedFormulaValidB, NamedFormulaWellFormed]
  | .node tag .nil => by
      simp [namedFormulaValidB, NamedFormulaWellFormed]
  | .node tag (.cons first .nil) => by
      cases first with
      | str text =>
          by_cases hprop : tag = "prop"
          · subst tag
            exact propTextWellFormedB_iff text
          · by_cases hatom : tag = "atom"
            · subst tag
              simp [namedFormulaValidB, NamedFormulaWellFormed]
            · simp [namedFormulaValidB, NamedFormulaWellFormed, hprop, hatom]
      | int value =>
          simp [namedFormulaValidB, NamedFormulaWellFormed]
      | node childTag children =>
          simp [namedFormulaValidB, NamedFormulaWellFormed]
  | .node tag (.cons left (.cons right .nil)) => by
      by_cases himp : tag = "imp"
      · subst tag
        simp [namedFormulaValidB, NamedFormulaWellFormed,
          namedFormulaValidB_iff left, namedFormulaValidB_iff right]
      · simp [namedFormulaValidB, NamedFormulaWellFormed, himp]
  | .node tag (.cons first (.cons second (.cons third rest))) => by
      simp [namedFormulaValidB, NamedFormulaWellFormed]

private def NamedNdExprWellFormed (resolver : String → Option Nat)
    (premiseCount : Nat) : List (Option String) → Presentation.Sx → Prop
  | _, .str _ => True
  | _, .int _ => True
  | _, .node "prem" (.cons (.str source) .nil) =>
      match parseCanonicalNat source with
      | some slot => slot < premiseCount
      | none =>
          sourceStartsIdentifier source = true ∧
            ∃ slot, resolver source = some slot
  | _, .node "thy" (.cons (.str source) .nil) =>
      ∃ slot, parseCanonicalNat source = some slot
  | binders, .node "hyp" (.cons (.str source) .nil) =>
      parseCanonicalNat source = none ∧
        sourceStartsIdentifier source = true ∧ some source ∈ binders
  | binders, .node "lam" (.cons formula (.cons body .nil)) =>
      NamedFormulaWellFormed formula ∧
        NamedNdExprWellFormed resolver premiseCount (none :: binders) body
  | binders, .node "lam" (.cons (.str binder) (.cons formula (.cons body .nil))) =>
      sourceStartsIdentifier binder = true ∧ some binder ∉ binders ∧
        resolver binder = none ∧ NamedFormulaWellFormed formula ∧
        NamedNdExprWellFormed resolver premiseCount (some binder :: binders) body
  | binders, .node "app" (.cons function (.cons argument .nil)) =>
      NamedNdExprWellFormed resolver premiseCount binders function ∧
        NamedNdExprWellFormed resolver premiseCount binders argument
  | binders, .node "abort" (.cons formula (.cons body .nil)) =>
      NamedFormulaWellFormed formula ∧
        NamedNdExprWellFormed resolver premiseCount binders body
  | _, expr => !hasNamedMarkerB expr = true

private theorem namedNdExprValidB_iff (resolver : String → Option Nat)
    (premiseCount : Nat) :
    ∀ binders expression,
      namedNdExprValidB resolver premiseCount binders expression = true ↔
        NamedNdExprWellFormed resolver premiseCount binders expression
  | _, .str source => by
      simp [namedNdExprValidB, NamedNdExprWellFormed]
  | _, .int value => by
      simp [namedNdExprValidB, NamedNdExprWellFormed]
  | binders, .node tag .nil => by
      simp [namedNdExprValidB, NamedNdExprWellFormed]
  | binders, .node tag (.cons first .nil) => by
      cases first with
      | str source =>
          by_cases hprem : tag = "prem"
          · subst tag
            cases hparse : parseCanonicalNat source with
            | none =>
                cases hresolve : resolver source <;>
                  simp [namedNdExprValidB, NamedNdExprWellFormed, hparse, hresolve]
            | some slot =>
                simp [namedNdExprValidB, NamedNdExprWellFormed, hparse]
          · by_cases hthy : tag = "thy"
            · subst tag
              cases hparse : parseCanonicalNat source <;>
                simp [namedNdExprValidB, NamedNdExprWellFormed, hparse]
            · by_cases hhyp : tag = "hyp"
              · subst tag
                cases hparse : parseCanonicalNat source <;>
                  simp [namedNdExprValidB, NamedNdExprWellFormed, hparse]
              · simp [namedNdExprValidB, NamedNdExprWellFormed,
                  hprem, hthy, hhyp]
      | int value =>
          simp [namedNdExprValidB, NamedNdExprWellFormed]
      | node childTag children =>
          simp [namedNdExprValidB, NamedNdExprWellFormed]
  | binders, .node tag (.cons first (.cons second .nil)) => by
      by_cases hlam : tag = "lam"
      · subst tag
        simp [namedNdExprValidB, NamedNdExprWellFormed,
          namedFormulaValidB_iff,
          namedNdExprValidB_iff resolver premiseCount (none :: binders) second]
      · by_cases happ : tag = "app"
        · subst tag
          simp [namedNdExprValidB, NamedNdExprWellFormed,
            namedNdExprValidB_iff resolver premiseCount binders first,
            namedNdExprValidB_iff resolver premiseCount binders second]
        · by_cases habort : tag = "abort"
          · subst tag
            simp [namedNdExprValidB, NamedNdExprWellFormed,
              namedFormulaValidB_iff,
              namedNdExprValidB_iff resolver premiseCount binders second]
          · simp [namedNdExprValidB, NamedNdExprWellFormed,
              hlam, happ, habort]
  | binders, .node tag (.cons first (.cons formula (.cons body .nil))) => by
      cases first with
      | str binder =>
          by_cases hlam : tag = "lam"
          · subst tag
            cases hresolve : resolver binder <;>
              simp [namedNdExprValidB, NamedNdExprWellFormed, hresolve,
                namedFormulaValidB_iff,
                namedNdExprValidB_iff resolver premiseCount
                  (some binder :: binders) body] <;>
              grind
          · simp [namedNdExprValidB, NamedNdExprWellFormed, hlam]
      | int value =>
          simp [namedNdExprValidB, NamedNdExprWellFormed]
      | node childTag children =>
          simp [namedNdExprValidB, NamedNdExprWellFormed]
  | binders, .node tag (.cons first (.cons second (.cons third (.cons fourth rest)))) => by
      simp [namedNdExprValidB, NamedNdExprWellFormed]

private def namedNdValidB (resolver : String → Option Nat)
    (premiseCount : Nat) (payload : Presentation.Sx) : Bool :=
  if hasNamedMarkerB payload then
    namedNdExprValidB resolver premiseCount [] payload
  else true

private def certificateFormValidB (program : Presentation.Program)
    (rule : Presentation.Rule) (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm) (certificate : Presentation.Cert) : Bool :=
  match certificate.version with
  | .negSucc _ => false
  | .ofNat version =>
      let resolver := certificateResolver program rule priors premises
      if certificate.backend.val == "nd" && version == 1 then
        namedNdValidB resolver premises.length certificate.payload
      else
        (Lara.CertSlots.lowerPayload sourceStartsIdentifier resolver
          certificate.backend.val version (sxToSExpr certificate.payload)).isSome

private def assuranceFormValidB (program : Presentation.Program)
    (rule : Presentation.Rule) (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm) : Presentation.Assurance → Bool
  | .none => true
  | .trusted => true
  | .cert certificate => certificateFormValidB program rule priors premises certificate

mutual
  def termCertificatesValidB (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument) :
      Presentation.SupportTerm → Bool
    | .leaf _ => true
    | .rule ruleId _ premises discharges _ assurance =>
        match ruleById policy ruleId with
        | none => false
        | some rule =>
            let premiseList := supportTermsToList premises
            assuranceFormValidB program rule priors premiseList assurance &&
            supportTermsCertificatesValidB program policy priors premises &&
            supportDischargesCertificatesValidB program policy priors discharges
  private def supportTermsCertificatesValidB (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument) :
      Presentation.SupportTerms → Bool
    | .nil => true
    | .cons term rest => termCertificatesValidB program policy priors term &&
        supportTermsCertificatesValidB program policy priors rest
  private def supportDischargesCertificatesValidB (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument) :
      Presentation.Discharges → Bool
    | .nil => true
    | .cons _ term rest => termCertificatesValidB program policy priors term &&
        supportDischargesCertificatesValidB program policy priors rest
end

private def validateCertificates (program : Presentation.Program)
    (policy : Presentation.Policy) : List Presentation.Decl → List PriorArgument → Bool
  | [], _ => true
  | .arg argument :: rest, priors =>
      match buildArgument program policy priors argument with
      | none => validateCertificates program policy rest priors
      | some built =>
          termCertificatesValidB program policy priors built.term &&
          validateCertificates program policy rest (priors ++ [built])
  | .comparison comparison :: rest, priors =>
      match generatedComparisonArguments program policy comparison with
      | none => validateCertificates program policy rest priors
      | some generated =>
          validateCertificates program policy rest (priors ++ [generated.1, generated.2])
  | _ :: rest, priors => validateCertificates program policy rest priors


def NamedNdWellFormed (resolver : String → Option Nat)
    (premiseCount : Nat) (payload : Presentation.Sx) : Prop :=
  if hasNamedMarkerB payload then
    NamedNdExprWellFormed resolver premiseCount [] payload
  else True

private theorem namedNdValidB_iff (resolver : String → Option Nat)
    (premiseCount : Nat) (payload : Presentation.Sx) :
    namedNdValidB resolver premiseCount payload = true ↔
      NamedNdWellFormed resolver premiseCount payload := by
  cases hmarker : hasNamedMarkerB payload with
  | false => simp [namedNdValidB, NamedNdWellFormed, hmarker]
  | true =>
      simp [namedNdValidB, NamedNdWellFormed, hmarker,
        namedNdExprValidB_iff]

private def CertificateFormWellFormed (program : Presentation.Program)
    (rule : Presentation.Rule) (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm) (certificate : Presentation.Cert) : Prop :=
  match certificate.version with
  | .negSucc _ => False
  | .ofNat version =>
      let resolver := certificateResolver program rule priors premises
      if certificate.backend.val = "nd" ∧ version = 1 then
        NamedNdWellFormed resolver premises.length certificate.payload
      else
        ∃ lowered, Lara.CertSlots.lowerPayload sourceStartsIdentifier resolver
          certificate.backend.val version (sxToSExpr certificate.payload) = some lowered

private theorem certificateFormValidB_iff (program : Presentation.Program)
    (rule : Presentation.Rule) (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm) (certificate : Presentation.Cert) :
    certificateFormValidB program rule priors premises certificate = true ↔
      CertificateFormWellFormed program rule priors premises certificate := by
  cases certificate with
  | mk backend version theory payload =>
      cases version with
      | negSucc n => simp [certificateFormValidB, CertificateFormWellFormed]
      | ofNat version =>
          by_cases hnd : backend.val = "nd" ∧ version = 1
          · simp [certificateFormValidB, CertificateFormWellFormed, hnd,
              namedNdValidB_iff]
          · simp [certificateFormValidB, CertificateFormWellFormed, hnd]
            cases Lara.CertSlots.lowerPayload sourceStartsIdentifier
              (certificateResolver program rule priors premises)
              backend.val version (sxToSExpr payload) <;> simp

private def AssuranceFormWellFormed (program : Presentation.Program)
    (rule : Presentation.Rule) (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm) : Presentation.Assurance → Prop
  | .none => True
  | .trusted => True
  | .cert certificate =>
      CertificateFormWellFormed program rule priors premises certificate

private theorem assuranceFormValidB_iff (program : Presentation.Program)
    (rule : Presentation.Rule) (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm) (assurance : Presentation.Assurance) :
    assuranceFormValidB program rule priors premises assurance = true ↔
      AssuranceFormWellFormed program rule priors premises assurance := by
  cases assurance <;> simp [assuranceFormValidB, AssuranceFormWellFormed,
    certificateFormValidB_iff]

mutual
  private def TermCertificatesWellFormed (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument) :
      Presentation.SupportTerm → Prop
    | .leaf _ => True
    | .rule ruleId _ premises discharges _ assurance =>
        match ruleById policy ruleId with
        | none => False
        | some rule =>
            AssuranceFormWellFormed program rule priors
              (supportTermsToList premises) assurance ∧
            SupportTermsCertificatesWellFormed program policy priors premises ∧
            SupportDischargesCertificatesWellFormed program policy priors discharges
  private def SupportTermsCertificatesWellFormed (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument) :
      Presentation.SupportTerms → Prop
    | .nil => True
    | .cons term rest =>
        TermCertificatesWellFormed program policy priors term ∧
        SupportTermsCertificatesWellFormed program policy priors rest
  private def SupportDischargesCertificatesWellFormed (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument) :
      Presentation.Discharges → Prop
    | .nil => True
    | .cons _ term rest =>
        TermCertificatesWellFormed program policy priors term ∧
        SupportDischargesCertificatesWellFormed program policy priors rest
end

mutual
  private theorem termCertificatesValidB_iff (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument)
      (term : Presentation.SupportTerm) :
      termCertificatesValidB program policy priors term = true ↔
        TermCertificatesWellFormed program policy priors term := by
    cases term with
    | leaf leaf => simp [termCertificatesValidB, TermCertificatesWellFormed]
    | rule ruleId subst premises discharges holes assurance =>
        cases h : ruleById policy ruleId with
        | none => simp [termCertificatesValidB, TermCertificatesWellFormed, h]
        | some rule =>
            simp [termCertificatesValidB, TermCertificatesWellFormed, h,
              assuranceFormValidB_iff, supportTermsCertificatesValidB_iff,
              supportDischargesCertificatesValidB_iff] <;> grind
  private theorem supportTermsCertificatesValidB_iff (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument)
      (terms : Presentation.SupportTerms) :
      supportTermsCertificatesValidB program policy priors terms = true ↔
        SupportTermsCertificatesWellFormed program policy priors terms := by
    cases terms with
    | nil => simp [supportTermsCertificatesValidB, SupportTermsCertificatesWellFormed]
    | cons term rest =>
        simp [supportTermsCertificatesValidB, SupportTermsCertificatesWellFormed,
          termCertificatesValidB_iff, supportTermsCertificatesValidB_iff]
  private theorem supportDischargesCertificatesValidB_iff
      (program : Presentation.Program) (policy : Presentation.Policy)
      (priors : List PriorArgument) (discharges : Presentation.Discharges) :
      supportDischargesCertificatesValidB program policy priors discharges = true ↔
        SupportDischargesCertificatesWellFormed program policy priors discharges := by
    cases discharges with
    | nil => simp [supportDischargesCertificatesValidB,
        SupportDischargesCertificatesWellFormed]
    | cons question term rest =>
        simp [supportDischargesCertificatesValidB,
          SupportDischargesCertificatesWellFormed, termCertificatesValidB_iff,
          supportDischargesCertificatesValidB_iff]
end

private def CertificatesWellFormedDecls (program : Presentation.Program)
    (policy : Presentation.Policy) : List Presentation.Decl → List PriorArgument → Prop
  | [], _ => True
  | .arg argument :: rest, priors =>
      match buildArgument program policy priors argument with
      | none => CertificatesWellFormedDecls program policy rest priors
      | some built =>
          TermCertificatesWellFormed program policy priors built.term ∧
          CertificatesWellFormedDecls program policy rest (priors ++ [built])
  | .comparison comparison :: rest, priors =>
      match generatedComparisonArguments program policy comparison with
      | none => CertificatesWellFormedDecls program policy rest priors
      | some generated =>
          CertificatesWellFormedDecls program policy rest
            (priors ++ [generated.1, generated.2])
  | _ :: rest, priors => CertificatesWellFormedDecls program policy rest priors

private theorem validateCertificates_iff (program : Presentation.Program)
    (policy : Presentation.Policy) (declarations : List Presentation.Decl)
    (priors : List PriorArgument) :
    validateCertificates program policy declarations priors = true ↔
      CertificatesWellFormedDecls program policy declarations priors := by
  induction declarations generalizing priors with
  | nil => simp [validateCertificates, CertificatesWellFormedDecls]
  | cons declaration rest ih =>
      cases declaration <;>
        simp [validateCertificates, CertificatesWellFormedDecls, ih] <;>
        split <;> simp_all [termCertificatesValidB_iff]

def NamedCertificatesWellFormed (program : Presentation.Program)
    (policy : Presentation.Policy) : Prop :=
  CertificatesWellFormedDecls program policy program.decls []

def namedCertificatesWellFormedB (program : Presentation.Program)
    (policy : Presentation.Policy) : Bool :=
  validateCertificates program policy program.decls []

theorem namedCertificatesWellFormedB_iff (program : Presentation.Program)
    (policy : Presentation.Policy) :
    namedCertificatesWellFormedB program policy = true ↔
      NamedCertificatesWellFormed program policy := by
  exact validateCertificates_iff program policy program.decls []

private def premiseAt? (premises : List Presentation.SupportTerm) (index : Int) :
    Option Presentation.SupportTerm :=
  if index < 0 then none else premises[index.toNat]?

private def dischargeByQuestion? (discharges :
    List (Presentation.QuestionId × Presentation.SupportTerm))
    (question : Presentation.QuestionId) : Option Presentation.SupportTerm :=
  discharges.findSome? fun entry => if entry.1 = question then some entry.2 else none

private def nextOccurrence? (policy : Presentation.Policy)
    (term : Presentation.SupportTerm) : Presentation.SurfaceStep →
    Option Presentation.SupportTerm
  | .index index =>
      match term with
      | .rule _ _ premises _ _ _ => premiseAt? (supportTermsToList premises) index
      | .leaf _ => none
  | .name name =>
      match term with
      | .leaf _ => none
      | .rule ruleId _ premises discharges _ _ =>
          match ruleById policy ruleId with
          | none => none
          | some rule =>
              match labelIndex? rule name with
              | some index => (supportTermsToList premises)[index]?
              | none =>
                  match (questionIds rule).find? (fun q => q.val == name) with
                  | some question => dischargeByQuestion? (dischargeTermsToList discharges) question
                  | none => none

private def pathWalks (policy : Presentation.Policy) :
    Presentation.SupportTerm → List Presentation.SurfaceStep → Prop
  | _, [] => True
  | term, step :: rest =>
      match nextOccurrence? policy term step with
      | none => False
      | some next => pathWalks policy next rest

private def targetTerm? (program : Presentation.Program) (policy : Presentation.Policy)
    (target : Presentation.ArgId) : Option Presentation.SupportTerm := do
  let priors := collectProgramArguments program policy program.decls []
  let prior ← priors.find? (fun argument => decide (argument.id = target))
  some prior.term

def attackEndpoints : Presentation.SurfaceAttack →
    Presentation.ArgId × Presentation.ArgId
  | .rebut source target => (source, target)
  | .undercut source target _ => (source, target)
  | .undermine source target _ => (source, target)

def attackPath : Presentation.SurfaceAttack → List Presentation.SurfaceStep
  | .rebut _ _ => []
  | .undercut _ _ path => path
  | .undermine _ _ path => path

private def pathWalksB (policy : Presentation.Policy) :
    Presentation.SupportTerm → List Presentation.SurfaceStep → Bool
  | _, [] => true
  | term, step :: rest =>
      match nextOccurrence? policy term step with
      | none => false
      | some next => pathWalksB policy next rest

private theorem pathWalksB_iff (policy : Presentation.Policy)
    (term : Presentation.SupportTerm) (path : List Presentation.SurfaceStep) :
    pathWalksB policy term path = true ↔ pathWalks policy term path := by
  induction path generalizing term with
  | nil => simp [pathWalksB, pathWalks]
  | cons step rest ih =>
      cases hnext : nextOccurrence? policy term step with
      | none => simp [pathWalksB, pathWalks, hnext]
      | some next => simp [pathWalksB, pathWalks, hnext, ih]

def SurfaceAttackWellFormed (program : Presentation.Program)
    (policy : Presentation.Policy) (attack : Presentation.SurfaceAttack) : Prop :=
  ((attackEndpoints attack).1 ∈ argIds program ∧
    (attackEndpoints attack).2 ∈ argIds program) ∧
  match targetTerm? program policy (attackEndpoints attack).2 with
  | none => False
  | some target => pathWalks policy target (attackPath attack)

def surfaceAttackWellFormedB (program : Presentation.Program)
    (policy : Presentation.Policy) (attack : Presentation.SurfaceAttack) : Bool :=
  ((argIds program).contains (attackEndpoints attack).1 &&
    (argIds program).contains (attackEndpoints attack).2) &&
  match targetTerm? program policy (attackEndpoints attack).2 with
  | none => false
  | some target => pathWalksB policy target (attackPath attack)

private theorem surfaceAttackWellFormedB_iff (program : Presentation.Program)
    (policy : Presentation.Policy) (attack : Presentation.SurfaceAttack) :
    surfaceAttackWellFormedB program policy attack = true ↔
      SurfaceAttackWellFormed program policy attack := by
  cases htarget : targetTerm? program policy (attackEndpoints attack).2 with
  | none =>
      simp [surfaceAttackWellFormedB, SurfaceAttackWellFormed, htarget]
  | some target =>
      simp [surfaceAttackWellFormedB, SurfaceAttackWellFormed, htarget,
        pathWalksB_iff] <;> grind

def SurfaceAttacksWellFormed (program : Presentation.Program)
    (policy : Presentation.Policy) : Prop :=
  ∀ declaration ∈ program.decls,
    match declaration with
    | .attack attack => SurfaceAttackWellFormed program policy attack
    | _ => True

private theorem declarationAttackWellFormedB_iff (program : Presentation.Program)
    (policy : Presentation.Policy) (declaration : Presentation.Decl) :
    (match declaration with
      | .attack attack => surfaceAttackWellFormedB program policy attack
      | _ => true) = true ↔
    (match declaration with
      | .attack attack => SurfaceAttackWellFormed program policy attack
      | _ => True) := by
  cases declaration <;> simp [surfaceAttackWellFormedB_iff]

def surfaceAttacksWellFormedB (program : Presentation.Program)
    (policy : Presentation.Policy) : Bool :=
  program.decls.all fun declaration =>
    match declaration with
    | .attack attack => surfaceAttackWellFormedB program policy attack
    | _ => true

theorem surfaceAttacksWellFormedB_iff (program : Presentation.Program)
    (policy : Presentation.Policy) :
    surfaceAttacksWellFormedB program policy = true ↔
      SurfaceAttacksWellFormed program policy := by
  simp [surfaceAttacksWellFormedB, SurfaceAttacksWellFormed,
    declarationAttackWellFormedB_iff]

def CanonicalPremiseLabels (policy : Presentation.Policy) : Prop :=
  ∀ rule ∈ policy.rules,
    rule.premiseLabels = [] ∨
      (rule.premiseLabels.length = rule.premises.length ∧
        ∃ label ∈ rule.premiseLabels, label.isSome = true)

def canonicalPremiseLabelsForRuleB (rule : Presentation.Rule) : Bool :=
  rule.premiseLabels.isEmpty ||
    (rule.premiseLabels.length == rule.premises.length &&
      rule.premiseLabels.any (fun label => label.isSome))

def canonicalPremiseLabelsB (policy : Presentation.Policy) : Bool :=
  policy.rules.all canonicalPremiseLabelsForRuleB

theorem canonicalPremiseLabelsB_iff (policy : Presentation.Policy) :
    canonicalPremiseLabelsB policy = true ↔ CanonicalPremiseLabels policy := by
  simp [canonicalPremiseLabelsB, canonicalPremiseLabelsForRuleB,
    CanonicalPremiseLabels]

structure Supported (input : Input) : Prop where
  policy_matches : input.program.policy = input.policy.id
  declaration_ids_nodup : DeclarationIdsNodup input.program
  rule_namespaces_wf : RuleNamespacesWellFormed input.policy
  value_bindings_wf : ValueBindingsWellFormed input
  comparisons_wf : ComparisonsWellFormed input.program input.policy
  inferred_args_wf : InferredArgsWellFormed input.program input.policy
  named_certs_wf : NamedCertificatesWellFormed input.program input.policy
  attack_names_wf : SurfaceAttacksWellFormed input.program input.policy
  canonical_labels : CanonicalPremiseLabels input.policy

private def policyMatchesB (input : Input) : Bool :=
  decide (input.program.policy = input.policy.id)

theorem policyMatchesB_iff (input : Input) :
    policyMatchesB input = true ↔ input.program.policy = input.policy.id := by
  simp [policyMatchesB]

def supportedB (input : Input) : Bool :=
  policyMatchesB input && declarationIdsNodupB input.program &&
  ruleNamespacesWellFormedB input.policy && valueBindingsWellFormedB input &&
  comparisonsWellFormedB input.program input.policy &&
  inferredArgsWellFormedB input.program input.policy &&
  namedCertificatesWellFormedB input.program input.policy &&
  surfaceAttacksWellFormedB input.program input.policy &&
  canonicalPremiseLabelsB input.policy

theorem supportedB_iff (input : Input) :
    supportedB input = true ↔ Supported input := by
  constructor
  · intro h
    simp only [supportedB, Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hp, hd⟩, hr⟩, hv⟩, hc⟩, hi⟩, hn⟩, ha⟩, hl⟩
    exact
      { policy_matches := (policyMatchesB_iff input).mp hp
        declaration_ids_nodup := (declarationIdsNodupB_iff input.program).mp hd
        rule_namespaces_wf := (ruleNamespacesWellFormedB_iff input.policy).mp hr
        value_bindings_wf := (valueBindingsWellFormedB_iff input).mp hv
        comparisons_wf := (comparisonsWellFormedB_iff input.program input.policy).mp hc
        inferred_args_wf := (inferredArgsWellFormedB_iff input.program input.policy).mp hi
        named_certs_wf := (namedCertificatesWellFormedB_iff input.program input.policy).mp hn
        attack_names_wf := (surfaceAttacksWellFormedB_iff input.program input.policy).mp ha
        canonical_labels := (canonicalPremiseLabelsB_iff input.policy).mp hl }
  · intro h
    simp only [supportedB, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨(policyMatchesB_iff input).mpr h.policy_matches,
      (declarationIdsNodupB_iff input.program).mpr h.declaration_ids_nodup⟩,
      (ruleNamespacesWellFormedB_iff input.policy).mpr h.rule_namespaces_wf⟩,
      (valueBindingsWellFormedB_iff input).mpr h.value_bindings_wf⟩,
      (comparisonsWellFormedB_iff input.program input.policy).mpr h.comparisons_wf⟩,
      (inferredArgsWellFormedB_iff input.program input.policy).mpr h.inferred_args_wf⟩,
      (namedCertificatesWellFormedB_iff input.program input.policy).mpr h.named_certs_wf⟩,
      (surfaceAttacksWellFormedB_iff input.program input.policy).mpr h.attack_names_wf⟩,
      (canonicalPremiseLabelsB_iff input.policy).mpr h.canonical_labels⟩

instance supportedDecidable (input : Input) : Decidable (Supported input) :=
  decidable_of_iff _ (supportedB_iff input)


/-! ### General multi-namespace renaming equivariance -/

/-- The declared value-name spellings of a program. -/
def programValues (program : Presentation.Program) : List Presentation.ValueName :=
  program.valueBindings.map (·.name)

/-- The value-name spellings of a program, as raw strings. -/
def valueSpellings (program : Presentation.Program) : List String :=
  programValues program |>.map (·.val)

/-- Lexically inventory every directive body rewritten by `Binding.renameNl`. -/
def nlDirectiveBodiesFuel : Nat → List Char → List (List Char)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, '{' :: '{' :: rest =>
      nlDirectiveBodiesFuel fuel rest
  | fuel + 1, '}' :: '}' :: rest =>
      nlDirectiveBodiesFuel fuel rest
  | fuel + 1, '{' :: rest =>
      match takeDirective rest with
      | none => []
      | some (body, after) =>
          body :: nlDirectiveBodiesFuel fuel after
  | fuel + 1, _ :: rest => nlDirectiveBodiesFuel fuel rest

def nlDirectiveBodies (text : String) : List (List Char) :=
  nlDirectiveBodiesFuel (text.toList.length + 1) text.toList

def programNlDirectiveBodies
    (program : Presentation.Program) : List (List Char) :=
  (claimNls program).flatMap nlDirectiveBodies
def programDirectiveBodies
    (program : Presentation.Program) : List (List Char) :=
  programNlDirectiveBodies program ++
    (valueNames program).map (fun value => value.val.toList) ++
    (leafIds program).map
      (fun leaf => "cell ".toList ++ leaf.val.toList)

mutual
  /-- Nullary constructor spellings of a term: `(con name nil)` occurrences. -/
  def termNullaryCons : Term → List String
    | .num _ => []
    | .str _ => []
    | .con name .nil => [name]
    | .con _ terms => termsNullaryCons terms
  def termsNullaryCons : Terms → List String
    | .nil => []
    | .cons term rest => termNullaryCons term ++ termsNullaryCons rest
end

def atomNullaryCons : Atom → List String
  | .atom _ terms => termsNullaryCons terms

mutual
  /-- Nullary constructor and literal-term spellings of a pattern: pattern
  spellings are fixed points of the renaming. -/
  private def patNullaryCons : Presentation.Pat → List String
    | .var _ => []
    | .lit term => termNullaryCons term
    | .con name .nil => [name]
    | .con _ pats => patsNullaryCons pats
  private def patsNullaryCons : Presentation.Pats → List String
    | .nil => []
    | .cons pat rest => patNullaryCons pat ++ patsNullaryCons rest
end

private def atomPatNullaryCons (pattern : Presentation.AtomPat) : List String :=
  patsNullaryCons pattern.args

mutual
  /-- Nullary constructor spellings inside the value terms of a support term. -/
  def supportTermNullaryCons : Presentation.SupportTerm → List String
    | .leaf _ => []
    | .rule _ subst premises discharges _ _ =>
        subst.flatMap (fun entry => termNullaryCons entry.2) ++
        supportTermsNullaryCons premises ++
        supportDischargesNullaryCons discharges
  def supportTermsNullaryCons : Presentation.SupportTerms → List String
    | .nil => []
    | .cons term rest => supportTermNullaryCons term ++ supportTermsNullaryCons rest
  def supportDischargesNullaryCons : Presentation.Discharges → List String
    | .nil => []
    | .cons _ term rest => supportTermNullaryCons term ++ supportDischargesNullaryCons rest
end

mutual
  /-- Named-binder spellings inside a certificate payload: these stay fixed
  while premise markers are renamed, so they must be renaming fixed points. -/
  def payloadBinderSpellings : Presentation.Sx → List String
    | .node "lam" (.cons (.str binder) (.cons _ (.cons body .nil))) =>
        binder :: payloadBinderSpellings body
    | .node "lam" (.cons _ (.cons body .nil)) =>
        payloadBinderSpellings body
    | .node _ children => sxListBinderSpellings children
    | .str _ => []
    | .int _ => []
  def sxListBinderSpellings : Presentation.SxList → List String
    | .nil => []
    | .cons expr rest => payloadBinderSpellings expr ++ sxListBinderSpellings rest
end

def assuranceBinderSpellings : Presentation.Assurance → List String
  | .none => []
  | .trusted => []
  | .cert cert => payloadBinderSpellings cert.payload

mutual
  def supportTermBinderSpellings : Presentation.SupportTerm → List String
    | .leaf _ => []
    | .rule _ _ premises discharges _ assurance =>
        assuranceBinderSpellings assurance ++
        supportTermsBinderSpellings premises ++
        supportDischargesBinderSpellings discharges
  def supportTermsBinderSpellings : Presentation.SupportTerms → List String
    | .nil => []
    | .cons term rest => supportTermBinderSpellings term ++ supportTermsBinderSpellings rest
  def supportDischargesBinderSpellings : Presentation.Discharges → List String
    | .nil => []
    | .cons _ term rest => supportTermBinderSpellings term ++ supportDischargesBinderSpellings rest
end

def argNullaryCons (argument : Presentation.Arg) : List String :=
  match argument.instantiation with
  | .explicitTheta term => supportTermNullaryCons term
  | .inferTheta _ _ _ _ assurance => assuranceBinderSpellings assurance

def argBinderSpellings (argument : Presentation.Arg) : List String :=
  match argument.instantiation with
  | .explicitTheta term => supportTermBinderSpellings term
  | .inferTheta _ _ _ _ assurance => assuranceBinderSpellings assurance

def declNullaryCons : Presentation.Decl → List String
  | .leaf leaf => atomNullaryCons leaf.prop
  | .claim claim => atomNullaryCons claim.formal
  | .arg argument => argNullaryCons argument
  | .attack _ => []
  | .status _ => []
  | .group _ => []
  | .comparison comparison => atomNullaryCons comparison.conclusion

private def declBinderSpellings : Presentation.Decl → List String
  | .arg argument => argBinderSpellings argument
  | _ => []

/-- All nullary constructor spellings occurring in the atoms of a program
(declared value names excluded by the caller). -/
def programNullaryCons (program : Presentation.Program) : List String :=
  program.decls.flatMap declNullaryCons

/-- All nullary constructor and literal-term spellings occurring in the rule
patterns of a policy. -/
def patternNullaryCons (policy : Presentation.Policy) : List String :=
  policy.rules.flatMap fun rule =>
    rule.premises.flatMap (fun pattern => atomPatNullaryCons pattern) ++
      atomPatNullaryCons rule.conclusion ++
      rule.questions.flatMap (fun question => atomPatNullaryCons question.answer)

/-- All named-binder spellings occurring in certificate payloads of a program. -/
def programBinderSpellings (program : Presentation.Program) : List String :=
  program.decls.flatMap declBinderSpellings

def assuranceOpaqueCertPremiseSpellings :
    Presentation.Assurance → List String
  | .none => []
  | .trusted => []
  | .cert certificate =>
      Binding.opaquePayloadPremiseSpellings certificate.payload

mutual
  def supportTermOpaqueCertPremiseSpellings :
      Presentation.SupportTerm → List String
    | .leaf _ => []
    | .rule _ _ premises discharges _ assurance =>
        assuranceOpaqueCertPremiseSpellings assurance ++
          supportTermsOpaqueCertPremiseSpellings premises ++
          dischargeOpaqueCertPremiseSpellings discharges
  def supportTermsOpaqueCertPremiseSpellings :
      Presentation.SupportTerms → List String
    | .nil => []
    | .cons term rest =>
        supportTermOpaqueCertPremiseSpellings term ++
          supportTermsOpaqueCertPremiseSpellings rest
  def dischargeOpaqueCertPremiseSpellings :
      Presentation.Discharges → List String
    | .nil => []
    | .cons _ term rest =>
        supportTermOpaqueCertPremiseSpellings term ++
          dischargeOpaqueCertPremiseSpellings rest
end

def argOpaqueCertPremiseSpellings
    (argument : Presentation.Arg) : List String :=
  match argument.instantiation with
  | .explicitTheta term => supportTermOpaqueCertPremiseSpellings term
  | .inferTheta _ _ _ _ assurance =>
      assuranceOpaqueCertPremiseSpellings assurance

def declOpaqueCertPremiseSpellings :
    Presentation.Decl → List String
  | .arg argument => argOpaqueCertPremiseSpellings argument
  | _ => []

/-- Symbolic premise spellings in certificate subtrees left opaque by the
canonical payload renamer. -/
def programOpaqueCertPremiseSpellings
    (program : Presentation.Program) : List String :=
  program.decls.flatMap declOpaqueCertPremiseSpellings

/-- The fixed-spelling premises consumed by comparison expansion.  Unlike
`RenamingSound`, this fragment remains valid after value interpolation because
comparison expansion never reads natural-language prose. -/
structure ComparisonRenamingSound (ρg : Binding.GlobalRenaming)
    (program : Presentation.Program) (policy : Presentation.Policy) : Prop where
  atoms : ∀ spelling ∈ programNullaryCons program,
    spelling ∉ valueSpellings program →
      Binding.renameText ρg spelling = spelling
  patterns : ∀ spelling ∈ patternNullaryCons policy,
    Binding.renameText ρg spelling = spelling

/-- Structural soundness of a global renaming over one concrete program and
policy.  These are the structural commutation premises: reserved and numeric
spellings are fixed, canonical-natural parsing and identifier-startingness are
preserved, and every spelling that occurs in a fixed (unrenamed) position —
sigma constructor names, nullary constructors in atoms and patterns, and
named certificate binders — is a fixed point of the renaming's spelling map.
Every `Supported` field invariant below is derived from these premises. -/
structure RenamingSound (ρg : Binding.GlobalRenaming)
    (program : Presentation.Program) (policy : Presentation.Policy) : Prop where
  rule_spelling : Binding.renameText ρg "rule" = "rule"
  leaf_spelling : Binding.renameText ρg "leaf" = "leaf"
  cell_spelling : Binding.renameText ρg "cell" = "cell"
  empty : Binding.renameText ρg "" = ""
  numeric : ∀ n : Nat, Binding.renameText ρg (Nat.repr n) = Nat.repr n
  integer : ∀ value : Int,
    Binding.renameText ρg (toString value) = toString value
  canonicalNat : ∀ s : String,
    parseCanonicalNat (Binding.renameText ρg s) = parseCanonicalNat s
  cellCanonNat : ∀ s : String,
    Lara.Cell.parseCanonNat (Binding.renameText ρg s) = Lara.Cell.parseCanonNat s
  identifier : ∀ s : String,
    sourceStartsIdentifier (Binding.renameText ρg s) = sourceStartsIdentifier s
  sigma : ∀ con ∈ policy.sigma.cons, Binding.renameText ρg con.sym.name = con.sym.name
  atoms : ∀ s ∈ programNullaryCons program,
    s ∉ valueSpellings program → Binding.renameText ρg s = s
  patterns : ∀ s ∈ patternNullaryCons policy, Binding.renameText ρg s = s
  certBinders : ∀ s ∈ programBinderSpellings program, Binding.renameText ρg s = s
  directiveDelimiterFresh : ∀ body ∈ programNlDirectiveBodies program,
    (Binding.renameDirective ρg body).head? ≠ some '{' ∧
      '}' ∉ Binding.renameDirective ρg body
  opaqueCertPremises : ∀ s ∈ programOpaqueCertPremiseSpellings program,
    Binding.renameText ρg s = s
  directiveInjective :
    ∀ left ∈ programDirectiveBodies program,
    ∀ right ∈ programDirectiveBodies program,
      Binding.renameDirective ρg left =
          Binding.renameDirective ρg right →
        left = right
  noCellValues : ∀ v ∈ valueNames program, v.val.startsWith "cell " = false

/-- Forget the soundness premises that comparison expansion does not read. -/
theorem RenamingSound.toComparison
    (sound : RenamingSound ρg program policy) :
    ComparisonRenamingSound ρg program policy :=
  ⟨sound.atoms, sound.patterns⟩

namespace Renaming

open Binding


@[simp] theorem programValues_renameProgram (ρg : GlobalRenaming)
    (program : Presentation.Program) :
    programValues (Binding.renameProgram ρg program) =
      (programValues program).map ρg.valueName := by
  simp [programValues, Binding.renameProgram]

@[simp] theorem valueNames_renameProgram (ρg : GlobalRenaming)
    (program : Presentation.Program) :
    valueNames (Binding.renameProgram ρg program) =
      (valueNames program).map ρg.valueName := by
  simp [valueNames, Binding.renameProgram]

@[simp] theorem leafIds_renameProgram (ρg : GlobalRenaming)
    (program : Presentation.Program) :
    leafIds (Binding.renameProgram ρg program) =
      (leafIds program).map ρg.leaf := by
  simp only [leafIds, Binding.renameProgram]
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp [Binding.renameDecl, ih]

@[simp] theorem argIds_renameProgram (ρg : GlobalRenaming)
    (program : Presentation.Program) :
    argIds (Binding.renameProgram ρg program) =
      (argIds program).map ρg.arg := by
  simp only [argIds, Binding.renameProgram]
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp [Binding.renameDecl, Binding.renameComparison,
        Binding.renameArg, ih]

@[simp] theorem claimIds_renameProgram (ρg : GlobalRenaming)
    (program : Presentation.Program) :
    claimIds (Binding.renameProgram ρg program) =
      (claimIds program).map ρg.prop := by
  simp only [claimIds, Binding.renameProgram]
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp [Binding.renameDecl, Binding.renameComparison, ih]

@[simp] theorem statusIds_renameProgram (ρg : GlobalRenaming)
    (program : Presentation.Program) :
    statusIds (Binding.renameProgram ρg program) =
      (statusIds program).map ρg.prop := by
  simp only [statusIds, Binding.renameProgram]
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp [Binding.renameDecl, ih]

private def renamePresentationGroup (ρg : GlobalRenaming)
    (group : Presentation.DupGroup) : Presentation.DupGroup :=
  { group with
    id := ρg.group group.id
    members := group.members.map ρg.leaf }

@[simp] theorem groupDecls_renameProgram (ρg : GlobalRenaming)
    (program : Presentation.Program) :
    groupDecls (Binding.renameProgram ρg program) =
      (groupDecls program).map (renamePresentationGroup ρg) := by
  simp only [groupDecls, Binding.renameProgram]
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp [Binding.renameDecl, renamePresentationGroup, ih]

@[simp] theorem ruleIds_renamePolicy (ρg : GlobalRenaming)
    (policy : Presentation.Policy) :
    ruleIds (Binding.renamePolicy ρg policy) =
      (ruleIds policy).map ρg.rule := by
  simp [ruleIds, Binding.renamePolicy, Binding.renameRule]

@[simp] theorem premiseLabels_renameRule (ρg : GlobalRenaming)
    (rule : Presentation.Rule) :
    premiseLabels (Binding.renameRule ρg rule) =
      (premiseLabels rule).map ρg.premiseLabel := by
  simp only [premiseLabels, Binding.renameRule]
  induction rule.premiseLabels with
  | nil => rfl
  | cons label rest ih =>
      cases label <;> simp [ih]

@[simp] theorem questionIds_renameRule (ρg : GlobalRenaming)
    (rule : Presentation.Rule) :
    questionIds (Binding.renameRule ρg rule) =
      (questionIds rule).map ρg.question := by
  simp [questionIds, Binding.renameRule]

@[simp] theorem comparisonDecls_renameProgram (ρg : GlobalRenaming)
    (program : Presentation.Program) :
    comparisonDecls (Binding.renameProgram ρg program) =
      (comparisonDecls program).map
        (Binding.renameComparison ρg (programValues program)) := by
  simp only [comparisonDecls, Binding.renameProgram, programValues]
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp [Binding.renameDecl, ih]

@[simp] theorem declaredLeaves_renameProgram (ρg : GlobalRenaming)
    (program : Presentation.Program) :
    declaredLeaves (Binding.renameProgram ρg program) =
      (declaredLeaves program).map fun entry =>
        (ρg.leaf entry.1,
          Binding.renameValueAtom ρg (programValues program) entry.2) := by
  simp only [declaredLeaves, Binding.renameProgram, programValues]
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;> simp [Binding.renameDecl, ih]

mutual
  /-- Rename the spelling of every constructor in a term. -/
  def renameSpellingTerm (ρg : GlobalRenaming) : Term → Term
    | .num s => .num s
    | .str s => .str s
    | .con k ts => .con (renameText ρg k) (renameSpellingTerms ρg ts)
  def renameSpellingTerms (ρg : GlobalRenaming) : Terms → Terms
    | .nil => .nil
    | .cons t ts => .cons (renameSpellingTerm ρg t) (renameSpellingTerms ρg ts)
end

/-- A term whose non-value nullary constructor spellings are all fixed points
of the renaming. -/
def TermFixed (ρg : GlobalRenaming) (values : List Presentation.ValueName)
    (t : Term) : Prop :=
  ∀ c, c ∈ termNullaryCons t → c ∉ values.map (·.val) → renameText ρg c = c

private def termsToList : Terms → List Term
  | .nil => []
  | .cons t ts => t :: termsToList ts

/-- Every term in a term list has fixed non-value nullary spellings. -/
def TermsFixed (ρg : GlobalRenaming) (values : List Presentation.ValueName)
    (terms : Terms) : Prop :=
  ∀ term ∈ termsToList terms, TermFixed ρg values term

/-- Every term argument of an atom has fixed non-value nullary spellings. -/
def AtomFixed (ρg : GlobalRenaming) (values : List Presentation.ValueName) :
    Atom → Prop
  | .atom _ terms => TermsFixed ρg values terms

/-- Every spelling in a fixed pattern position is a renaming fixed point. -/
def PatFixed (ρg : GlobalRenaming) (pattern : Presentation.Pat) : Prop :=
  ∀ spelling ∈ patNullaryCons pattern,
    renameText ρg spelling = spelling

def PatsFixed (ρg : GlobalRenaming) (patterns : Presentation.Pats) : Prop :=
  ∀ spelling ∈ patsNullaryCons patterns,
    renameText ρg spelling = spelling

def AtomPatFixed (ρg : GlobalRenaming)
    (pattern : Presentation.AtomPat) : Prop :=
  PatsFixed ρg pattern.args

/-- Every value term currently carried by a matcher substitution is fixed. -/
def SubstFixed (ρg : GlobalRenaming) (values : List Presentation.ValueName)
    (subst : SurfaceSubst) : Prop :=
  ∀ entry ∈ subst, TermFixed ρg values entry.2

/-- Every value term inside a support term has fixed non-value nullaries. -/
def SupportTermFixed (ρg : GlobalRenaming)
    (values : List Presentation.ValueName)
    (term : Presentation.SupportTerm) : Prop :=
  ∀ c, c ∈ supportTermNullaryCons term →
    c ∉ values.map (·.val) → renameText ρg c = c

private theorem contains_eq_false {α} [DecidableEq α] (l : List α) (a : α) :
    l.contains a = false ↔ a ∉ l := by
  constructor
  · intro h hmem
    have : l.contains a = true := List.contains_iff_mem.mpr hmem
    rw [h] at this
    simp at this
  · intro h
    by_cases hc : l.contains a = true
    · exact absurd (List.contains_iff_mem.mp hc) h
    · simpa using hc

private theorem mem_values_map (values : List Presentation.ValueName) (s : String) :
    s ∈ values.map (·.val) ↔ (⟨s⟩ : Presentation.ValueName) ∈ values := by
  constructor
  · intro h
    induction values with
    | nil => simp at h
    | cons v vs ih =>
        simp [List.mem_cons] at h ⊢
        rcases h with h | h
        · left
          exact (congrArg (fun (x : String) => (⟨x⟩ : Presentation.ValueName)) h.symm).symm
        · right
          exact ih (List.mem_map.mpr h)
  · intro h
    induction values with
    | nil => simp at h
    | cons v vs ih =>
        simp [List.mem_cons] at h ⊢
        rcases h with h | h
        · left
          exact congrArg (fun (x : Presentation.ValueName) => x.val) h
        · right
          exact List.mem_map.mp (ih h)

private theorem mem_contains_true {values : List Presentation.ValueName} {s : String}
    (h : s ∈ values.map (·.val)) : values.contains (⟨s⟩ : Presentation.ValueName) = true :=
  List.contains_iff_mem.mpr ((mem_values_map values s).mp h)

private theorem mem_contains_false {values : List Presentation.ValueName} {s : String}
    (h : s ∉ values.map (·.val)) :
    values.contains (⟨s⟩ : Presentation.ValueName) = false :=
  (contains_eq_false values (⟨s⟩ : Presentation.ValueName)).mpr (by
    intro hm
    exact h ((mem_values_map values s).mpr hm))

private theorem termNullaryCons_sub_terms (u : Term) : ∀ ts : Terms,
    u ∈ termsToList ts → termNullaryCons u ⊆ termsNullaryCons ts
  | .nil, hu => by simp [termsToList] at hu
  | .cons t ts', hu => by
      intro c hc
      simp [termsToList] at hu ⊢
      rcases hu with rfl | hu
      · exact List.mem_append.mpr (Or.inl hc)
      · exact List.mem_append.mpr (Or.inr (termNullaryCons_sub_terms u ts' hu hc))

private theorem patNullaryCons_sub_pats (pat : Presentation.Pat) :
    ∀ pats : Presentation.Pats,
    pat ∈ patsToList pats → patNullaryCons pat ⊆ patsNullaryCons pats
  | .nil, h => by simp [patsToList] at h
  | .cons first rest, h => by
      intro c hc
      simp [patsToList] at h
      simp [patsNullaryCons]
      rcases h with rfl | h
      · exact Or.inl hc
      · exact Or.inr (patNullaryCons_sub_pats pat rest h hc)

theorem atomFixed_of_decl
    (sound : ComparisonRenamingSound ρg program policy)
    (declaration : Presentation.Decl)
    (member : declaration ∈ program.decls)
    (atom : Atom)
    (contained : atomNullaryCons atom ⊆ declNullaryCons declaration) :
    AtomFixed ρg (programValues program) atom := by
  cases atom with
  | atom pred terms =>
      intro term termMember spelling spellingMember notValue
      apply sound.atoms spelling
      · exact List.mem_flatMap.mpr
          ⟨declaration, member,
            contained
              (termNullaryCons_sub_terms term terms termMember spellingMember)⟩
      · exact notValue

private theorem atomPatFixed_of_rule
    (sound : ComparisonRenamingSound ρg program policy)
    (rule : Presentation.Rule) (member : rule ∈ policy.rules)
    (pattern : Presentation.AtomPat)
    (contained : atomPatNullaryCons pattern ⊆
      rule.premises.flatMap atomPatNullaryCons ++
        atomPatNullaryCons rule.conclusion ++
        rule.questions.flatMap fun question =>
          atomPatNullaryCons question.answer) :
    AtomPatFixed ρg pattern := by
  intro spelling spellingMember
  apply sound.patterns spelling
  exact List.mem_flatMap.mpr
    ⟨rule, member, contained spellingMember⟩

private theorem renamed_leaf_arg_spelling_eq_iff
    (ρg : GlobalRenaming) (leaf : Presentation.LeafId)
    (argument : Presentation.ArgId) :
    (ρg.leaf leaf).val = (ρg.arg argument).val ↔
      leaf.val = argument.val := by
  simp only [Binding.rename_leaf_val, Binding.rename_arg_val]
  exact ⟨fun h => renameText_injective ρg (by simpa [renameText] using h),
    fun h => by simpa [renameText, h]⟩

private theorem renamed_leaf_argRef_spelling_eq_iff
    (ρg : GlobalRenaming) (leaf : Presentation.LeafId)
    (reference : Presentation.ArgRef) :
    (ρg.leaf leaf).val = (ρg.argRef reference).val ↔
      leaf.val = reference.val := by
  simp only [Binding.rename_leaf_val, Binding.rename_argRef_val]
  exact ⟨fun h => renameText_injective ρg (by simpa [renameText] using h),
    fun h => by simpa [renameText, h]⟩

private theorem renamed_arg_argRef_spelling_eq_iff
    (ρg : GlobalRenaming) (argument : Presentation.ArgId)
    (reference : Presentation.ArgRef) :
    (ρg.arg argument).val = (ρg.argRef reference).val ↔
      argument.val = reference.val := by
  simp only [Binding.rename_arg_val, Binding.rename_argRef_val]
  exact ⟨fun h => renameText_injective ρg (by simpa [renameText] using h),
    fun h => by simpa [renameText, h]⟩

private theorem renamed_label_question_spelling_eq_iff
    (ρg : GlobalRenaming) (label : Presentation.PremiseLabel)
    (question : Presentation.QuestionId) :
    (ρg.premiseLabel label).val = (ρg.question question).val ↔
      label.val = question.val := by
  simp only [Binding.rename_premiseLabel_val, Binding.rename_question_val]
  exact ⟨fun h => renameText_injective ρg (by simpa [renameText] using h),
    fun h => by simpa [renameText, h]⟩

private theorem renamed_label_text_eq_iff_of_fixed
    (ρg : GlobalRenaming) (label : Presentation.PremiseLabel)
    (text : String) (fixed : renameText ρg text = text) :
    (ρg.premiseLabel label).val = text ↔ label.val = text := by
  rw [Binding.rename_premiseLabel_val]
  constructor
  · intro h
    exact renameText_injective ρg (h.trans fixed.symm)
  · intro h
    rw [h]
    exact fixed

private theorem termFixed_of_num : TermFixed ρg values (.num s) := by
  intro c hc
  simp [termNullaryCons] at hc

private theorem termFixed_of_str : TermFixed ρg values (.str s) := by
  intro c hc
  simp [termNullaryCons] at hc

private theorem termFixed_of_cons_args {ρg} {values} {t : Term} {ts : Terms}
    (h : TermFixed ρg values (.con name (.cons t ts))) :
    TermFixed ρg values t ∧ ∀ u ∈ termsToList ts, TermFixed ρg values u := by
  constructor
  · intro c hc hnot
    exact h c (by
      simp [termNullaryCons, termsNullaryCons] at hc ⊢
      exact Or.inl hc) hnot
  · intro u hu c hc hnot
    exact h c (by
      simp [termNullaryCons, termsNullaryCons] at hc ⊢
      exact Or.inr (termNullaryCons_sub_terms u ts hu hc)) hnot

private theorem termFixed_cons_iff {ρg} {values} {t : Term} {ts : Terms}
    (h : TermFixed ρg values (.con name (.cons t ts))) :
    ∀ u ∈ termsToList (.cons t ts : Terms), TermFixed ρg values u := by
  intro u hu
  simp [termsToList] at hu
  rcases hu with rfl | hu
  · exact (termFixed_of_cons_args h).1
  · exact (termFixed_of_cons_args h).2 u hu

mutual
  /-- The canonical term transformer is injective on terms whose non-value
  constructor spellings are all fixed points of the renaming. -/
  private theorem renameValueTerm_eq_iff (ρg : GlobalRenaming)
      (values : List Presentation.ValueName) {a b : Term}
      (ha : TermFixed ρg values a) (hb : TermFixed ρg values b) :
      Binding.renameValueTerm ρg values a = Binding.renameValueTerm ρg values b ↔
        a = b := by
    constructor
    · intro h
      cases a with
      | num na =>
          cases b with
          | num nb => simpa [Binding.renameValueTerm] using h
          | str sb => simpa [Binding.renameValueTerm] using h
          | con cb tbs =>
              cases tbs with
              | nil =>
                  by_cases hcb : cb ∈ values.map (·.val)
                  · have hcbV : (⟨cb⟩ : Presentation.ValueName) ∈ values := (mem_values_map values cb).mp hcb
                    have h' : Term.num na = Term.con (renameText ρg cb) Terms.nil := by
                      simpa [Binding.renameValueTerm, hcbV] using h
                    cases h'
                  · have hcbV : ¬ (⟨cb⟩ : Presentation.ValueName) ∈ values := by
                      intro hm; exact hcb ((mem_values_map values cb).mpr hm)
                    have h' : Term.num na = Term.con cb Terms.nil := by
                      simpa [Binding.renameValueTerm, hcbV] using h
                    exact h'
              | cons tb tbs' => simpa [Binding.renameValueTerm] using h
      | str sa =>
          cases b with
          | num nb => simpa [Binding.renameValueTerm] using h
          | str sb => simpa [Binding.renameValueTerm] using h
          | con cb tbs =>
              cases tbs with
              | nil =>
                  by_cases hcb : cb ∈ values.map (·.val)
                  · have hcbV : (⟨cb⟩ : Presentation.ValueName) ∈ values := (mem_values_map values cb).mp hcb
                    have h' : Term.str sa = Term.con (renameText ρg cb) Terms.nil := by
                      simpa [Binding.renameValueTerm, hcbV] using h
                    cases h'
                  · have hcbV : ¬ (⟨cb⟩ : Presentation.ValueName) ∈ values := by
                      intro hm; exact hcb ((mem_values_map values cb).mpr hm)
                    have h' : Term.str sa = Term.con cb Terms.nil := by
                      simpa [Binding.renameValueTerm, hcbV] using h
                    exact h'
              | cons tb tbs' => simpa [Binding.renameValueTerm] using h
      | con ca tas =>
          cases b with
          | num nb =>
              cases tas with
              | nil =>
                  by_cases hca : ca ∈ values.map (·.val)
                  · have hcaV : (⟨ca⟩ : Presentation.ValueName) ∈ values := (mem_values_map values ca).mp hca
                    have h' : Term.con (renameText ρg ca) Terms.nil = Term.num nb := by
                      simpa [Binding.renameValueTerm, hcaV] using h
                    cases h'
                  · have hcaV : ¬ (⟨ca⟩ : Presentation.ValueName) ∈ values := by
                      intro hm; exact hca ((mem_values_map values ca).mpr hm)
                    have h' : Term.con ca Terms.nil = Term.num nb := by
                      simpa [Binding.renameValueTerm, hcaV] using h
                    exact h'
              | cons ta tas' => simpa [Binding.renameValueTerm] using h
          | str sb =>
              cases tas with
              | nil =>
                  by_cases hca : ca ∈ values.map (·.val)
                  · have hcaV : (⟨ca⟩ : Presentation.ValueName) ∈ values := (mem_values_map values ca).mp hca
                    have h' : Term.con (renameText ρg ca) Terms.nil = Term.str sb := by
                      simpa [Binding.renameValueTerm, hcaV] using h
                    cases h'
                  · have hcaV : ¬ (⟨ca⟩ : Presentation.ValueName) ∈ values := by
                      intro hm; exact hca ((mem_values_map values ca).mpr hm)
                    have h' : Term.con ca Terms.nil = Term.str sb := by
                      simpa [Binding.renameValueTerm, hcaV] using h
                    exact h'
              | cons ta tas' => simpa [Binding.renameValueTerm] using h
          | con cb tbs =>
              cases tas with
              | nil =>
                  cases tbs with
                  | nil =>
                      by_cases hca : ca ∈ values.map (·.val)
                      · by_cases hcb : cb ∈ values.map (·.val)
                        · have hcaV : (⟨ca⟩ : Presentation.ValueName) ∈ values := (mem_values_map values ca).mp hca
                          have hcbV : (⟨cb⟩ : Presentation.ValueName) ∈ values := (mem_values_map values cb).mp hcb
                          have h' : Term.con (renameText ρg ca) Terms.nil =
                              Term.con (renameText ρg cb) Terms.nil := by
                            simpa [Binding.renameValueTerm, hcaV, hcbV] using h
                          have hsp : renameText ρg ca = renameText ρg cb := (Term.con.inj h').1
                          have hc : ca = cb := renameText_injective ρg hsp
                          simp [hc]
                        · have hcaV : (⟨ca⟩ : Presentation.ValueName) ∈ values := (mem_values_map values ca).mp hca
                          have hcbV : ¬ (⟨cb⟩ : Presentation.ValueName) ∈ values := by
                            intro hm; exact hcb ((mem_values_map values cb).mpr hm)
                          have h' : Term.con (renameText ρg ca) Terms.nil = Term.con cb Terms.nil := by
                            simpa [Binding.renameValueTerm, hcaV, hcbV] using h
                          have hsp : renameText ρg ca = cb := (Term.con.inj h').1
                          have hfixb := hb cb (by simp [termNullaryCons]) hcb
                          have hc : ca = cb := renameText_injective ρg (by rw [hfixb]; exact hsp)
                          exact absurd (hc ▸ hca) hcb
                      · by_cases hcb : cb ∈ values.map (·.val)
                        · have hcaV : ¬ (⟨ca⟩ : Presentation.ValueName) ∈ values := by
                            intro hm; exact hca ((mem_values_map values ca).mpr hm)
                          have hcbV : (⟨cb⟩ : Presentation.ValueName) ∈ values := (mem_values_map values cb).mp hcb
                          have h' : Term.con ca Terms.nil = Term.con (renameText ρg cb) Terms.nil := by
                            simpa [Binding.renameValueTerm, hcaV, hcbV] using h
                          have hsp : ca = renameText ρg cb := (Term.con.inj h').1
                          have hfixa := ha ca (by simp [termNullaryCons]) hca
                          have hc : ca = cb := renameText_injective ρg (by rw [hfixa]; exact hsp)
                          exact absurd (hc ▸ hcb) hca
                        · have hcaV : ¬ (⟨ca⟩ : Presentation.ValueName) ∈ values := by
                            intro hm; exact hca ((mem_values_map values ca).mpr hm)
                          have hcbV : ¬ (⟨cb⟩ : Presentation.ValueName) ∈ values := by
                            intro hm; exact hcb ((mem_values_map values cb).mpr hm)
                          have h' : Term.con ca Terms.nil = Term.con cb Terms.nil := by
                            simpa [Binding.renameValueTerm, hcaV, hcbV] using h
                          exact h'
                  | cons tb tbs' =>
                      by_cases hca : ca ∈ values.map (·.val)
                      · have hcaV : (⟨ca⟩ : Presentation.ValueName) ∈ values := (mem_values_map values ca).mp hca
                        have h' : Term.con (renameText ρg ca) Terms.nil =
                            Term.con cb (Binding.renameValueTerms ρg values (.cons tb tbs' : Terms)) := by
                          simpa [Binding.renameValueTerm, hcaV] using h
                        cases h'
                      · have hcaV : ¬ (⟨ca⟩ : Presentation.ValueName) ∈ values := by
                          intro hm; exact hca ((mem_values_map values ca).mpr hm)
                        have h' : Term.con ca Terms.nil =
                            Term.con cb (Binding.renameValueTerms ρg values (.cons tb tbs' : Terms)) := by
                          simpa [Binding.renameValueTerm, hcaV] using h
                        cases h'
              | cons ta tas' =>
                  cases tbs with
                  | nil =>
                      by_cases hcb : cb ∈ values.map (·.val)
                      · have hcbV : (⟨cb⟩ : Presentation.ValueName) ∈ values := (mem_values_map values cb).mp hcb
                        have h' : Term.con ca (Binding.renameValueTerms ρg values (.cons ta tas' : Terms)) =
                            Term.con (renameText ρg cb) Terms.nil := by
                          simpa [Binding.renameValueTerm, hcbV] using h
                        cases h'
                      · have hcbV : ¬ (⟨cb⟩ : Presentation.ValueName) ∈ values := by
                          intro hm; exact hcb ((mem_values_map values cb).mpr hm)
                        have h' : Term.con ca (Binding.renameValueTerms ρg values (.cons ta tas' : Terms)) =
                            Term.con cb Terms.nil := by
                          simpa [Binding.renameValueTerm, hcbV] using h
                        cases h'
                  | cons tb tbs' =>
                      have hc : ca = cb := (Term.con.inj h).1
                      have ht : Binding.renameValueTerms ρg values (.cons ta tas' : Terms) =
                          Binding.renameValueTerms ρg values (.cons tb tbs' : Terms) := (Term.con.inj h).2
                      have hsub : (∀ u ∈ termsToList (.cons ta tas' : Terms), TermFixed ρg values u) ∧
                          (∀ u ∈ termsToList (.cons tb tbs' : Terms), TermFixed ρg values u) := by
                        exact ⟨termFixed_cons_iff ha, termFixed_cons_iff hb⟩
                      have hargs : (.cons ta tas' : Terms) = .cons tb tbs' :=
                        (renameValueTerms_eq_iff ρg values hsub.1 hsub.2).mp ht
                      rw [hc]
                      exact congrArg (Term.con cb) hargs
    · intro h
      subst h
      rfl
  /-- The canonical term-list transformer is injective on terms whose non-value
  constructor spellings are all fixed points of the renaming. -/
  private theorem renameValueTerms_eq_iff (ρg : GlobalRenaming)
      (values : List Presentation.ValueName) {as bs : Terms}
      (ha : ∀ u ∈ termsToList as, TermFixed ρg values u)
      (hb : ∀ u ∈ termsToList bs, TermFixed ρg values u) :
      Binding.renameValueTerms ρg values as = Binding.renameValueTerms ρg values bs ↔
        as = bs := by
    constructor
    · intro h
      cases as with
      | nil =>
          cases bs with
          | nil => rfl
          | cons b bs' => simp [Binding.renameValueTerms] at h
      | cons a as' =>
          cases bs with
          | nil => simp [Binding.renameValueTerms] at h
          | cons b bs' =>
              simp [Binding.renameValueTerms] at h
              have h1 : Binding.renameValueTerm ρg values a = Binding.renameValueTerm ρg values b := h.1
              have h2 : Binding.renameValueTerms ρg values as' = Binding.renameValueTerms ρg values bs' := h.2
              have ha' : a = b :=
                (renameValueTerm_eq_iff ρg values (ha a (by simp [termsToList]))
                  (hb b (by simp [termsToList]))).mp h1
              have hb' : as' = bs' :=
                (renameValueTerms_eq_iff ρg values
                  (by intro u hu; exact ha u (by
                    simp [termsToList]
                    exact Or.inr hu))
                  (by intro u hu; exact hb u (by
                    simp [termsToList]
                    exact Or.inr hu))).mp h2
              rw [ha', hb']
    · intro h
      subst h
      rfl
end





mutual
  /-- Normalization commutes with the canonical term transformer: `nfTerm`
  touches only numeric literals, `renameValueTerm` never touches them. -/
  private theorem nfTerm_renameValueTerm (ρg : GlobalRenaming)
      (values : List Presentation.ValueName) (t : Term) :
      Lara.nfTerm Lara.canonNum (Binding.renameValueTerm ρg values t) =
        Binding.renameValueTerm ρg values (Lara.nfTerm Lara.canonNum t) := by
    cases t with
    | num s => rfl
    | str s => rfl
    | con name terms =>
        cases terms with
        | nil =>
            by_cases hc : values.contains ⟨name⟩
            · have hm : (⟨name⟩ : Presentation.ValueName) ∈ values := List.contains_iff_mem.mp hc
              simp [Binding.renameValueTerm, Lara.nfTerm, Lara.nfTerms, hm]
            · have hm : ¬ (⟨name⟩ : Presentation.ValueName) ∈ values := by
                intro h
                exact hc (List.contains_iff_mem.mpr h)
              simp [Binding.renameValueTerm, Lara.nfTerm, Lara.nfTerms, hm]
        | cons term rest =>
            simp [Binding.renameValueTerm, Lara.nfTerm, Lara.nfTerms,
              nfTerms_renameValueTerms ρg values (.cons term rest)]
  private theorem nfTerms_renameValueTerms (ρg : GlobalRenaming)
      (values : List Presentation.ValueName) (ts : Terms) :
      Lara.nfTerms Lara.canonNum (Binding.renameValueTerms ρg values ts) =
        Binding.renameValueTerms ρg values (Lara.nfTerms Lara.canonNum ts) := by
    cases ts with
    | nil => rfl
    | cons t rest =>
        simp [Binding.renameValueTerms, Lara.nfTerms,
          nfTerm_renameValueTerm ρg values t, nfTerms_renameValueTerms ρg values rest]
end

mutual
  private theorem nfTerm_renameSpellingTerm (ρg : GlobalRenaming) (t : Term) :
      Lara.nfTerm Lara.canonNum (renameSpellingTerm ρg t) =
        renameSpellingTerm ρg (Lara.nfTerm Lara.canonNum t) := by
    cases t with
    | num s => rfl
    | str s => rfl
    | con name terms =>
        cases terms with
        | nil => rfl
        | cons term rest =>
            simp [renameSpellingTerm, Lara.nfTerm,
              nfTerms_renameSpellingTerms ρg (.cons term rest)]
  private theorem nfTerms_renameSpellingTerms (ρg : GlobalRenaming) (ts : Terms) :
      Lara.nfTerms Lara.canonNum (renameSpellingTerms ρg ts) =
        renameSpellingTerms ρg (Lara.nfTerms Lara.canonNum ts) := by
    cases ts with
    | nil => rfl
    | cons t rest =>
        simp [renameSpellingTerms, Lara.nfTerms,
          nfTerm_renameSpellingTerm ρg t, nfTerms_renameSpellingTerms ρg rest]
end

mutual
  /-- Normalization never introduces nullary constructor spellings. -/
  private theorem termNullaryCons_nf (t : Term) :
      termNullaryCons (Lara.nfTerm Lara.canonNum t) ⊆ termNullaryCons t := by
    cases t with
    | num s => intro c hc; simp [termNullaryCons, Lara.nfTerm] at hc
    | str s => intro c hc; simp [termNullaryCons, Lara.nfTerm] at hc
    | con name terms =>
        cases terms with
        | nil => intro c hc; simp [termNullaryCons, Lara.nfTerm, Lara.nfTerms] at hc;
                    simpa [termNullaryCons] using hc
        | cons term rest =>
            intro c hc
            simp [termNullaryCons, termsNullaryCons, Lara.nfTerm, Lara.nfTerms] at hc
            rcases hc with hc | hc
            · exact List.mem_append.mpr (Or.inl (termNullaryCons_nf term hc))
            · exact List.mem_append.mpr (Or.inr (termsNullaryCons_nf rest hc))
  private theorem termsNullaryCons_nf (ts : Terms) :
      termsNullaryCons (Lara.nfTerms Lara.canonNum ts) ⊆ termsNullaryCons ts := by
    cases ts with
    | nil => intro c hc; simp [termsNullaryCons, Lara.nfTerms] at hc
    | cons t rest =>
        intro c hc
        simp [termsNullaryCons, Lara.nfTerms] at hc
        rcases hc with hc | hc
        · exact List.mem_append.mpr (Or.inl (termNullaryCons_nf t hc))
        · exact List.mem_append.mpr (Or.inr (termsNullaryCons_nf rest hc))
end

/-- The `nfTerm` transfer of `TermFixed`: normalization never introduces or
removes nullary constructor spellings. -/
private theorem termFixed_of_nf (ρg : GlobalRenaming)
    (values : List Presentation.ValueName) {t : Term}
    (h : TermFixed ρg values t) : TermFixed ρg values (Lara.nfTerm Lara.canonNum t) := by
  intro c hc hnot
  exact h c (termNullaryCons_nf t hc) hnot

private theorem beq_eq_false_of_ne {α} [DecidableEq α] {a b : α} (h : a ≠ b) :
    (a == b) = false := by
  by_cases hb : (a == b) = true
  · have : a = b := beq_iff_eq.mp hb
    exact absurd this h
  · cases hb' : a == b
    · rfl
    · exfalso
      exact hb hb'

/-- Renaming preserves term equality of normal forms: the renamed terms
normalize equally exactly when the originals do. -/
private theorem sameSurfaceTerm_renameValueTerm_iff (ρg : GlobalRenaming)
    (values : List Presentation.ValueName) {a b : Term}
    (ha : TermFixed ρg values a) (hb : TermFixed ρg values b) :
    sameSurfaceTerm (Binding.renameValueTerm ρg values a)
        (Binding.renameValueTerm ρg values b) = true ↔
      sameSurfaceTerm a b = true := by
  unfold sameSurfaceTerm
  rw [nfTerm_renameValueTerm ρg values a, nfTerm_renameValueTerm ρg values b]
  rw [beq_iff_eq, beq_iff_eq]
  exact renameValueTerm_eq_iff ρg values (termFixed_of_nf ρg values ha)
    (termFixed_of_nf ρg values hb)

/-- Renaming preserves term equality of normal forms against a renamed-spelling
nullary term.  The spelling side needs no fixedness condition: canonicality is
forced by the injectivity of the renaming's spelling map. -/
private theorem sameSurfaceTerm_renameValueTerm_spelling_iff (ρg : GlobalRenaming)
    (values : List Presentation.ValueName) {a : Term}
    (ha : TermFixed ρg values a) (m : String) :
    sameSurfaceTerm (Binding.renameValueTerm ρg values a)
        (.con (renameText ρg m) .nil) = true ↔
      sameSurfaceTerm a (.con m .nil) = true := by
  unfold sameSurfaceTerm
  rw [nfTerm_renameValueTerm ρg values a]
  by_cases h : Lara.nfTerm Lara.canonNum a = .con m .nil
  · have h' : Binding.renameValueTerm ρg values (Lara.nfTerm Lara.canonNum a) =
        .con (renameText ρg m) .nil := by
      rw [h]
      by_cases hm : m ∈ values.map (·.val)
      · have hmV : (⟨m⟩ : Presentation.ValueName) ∈ values := (mem_values_map values m).mp hm
        simp [Binding.renameValueTerm, hmV]
      · have hmV : ¬ (⟨m⟩ : Presentation.ValueName) ∈ values := by
          intro hmem; exact hm ((mem_values_map values m).mpr hmem)
        have hfix := ha m (termNullaryCons_nf a (by
          rw [h]
          simp [termNullaryCons])) hm
        simp [Binding.renameValueTerm, hmV, hfix]
    simp only [Lara.nfTerm, Lara.nfTerms, beq_iff_eq]
    constructor
    · intro _
      exact h
    · intro _
      exact h'
  · have h' : Binding.renameValueTerm ρg values (Lara.nfTerm Lara.canonNum a) ≠
        .con (renameText ρg m) .nil := by
      intro heq
      cases hnf : Lara.nfTerm Lara.canonNum a with
      | num s => rw [hnf] at heq; simp [Binding.renameValueTerm] at heq
      | str s => rw [hnf] at heq; simp [Binding.renameValueTerm] at heq
      | con ca tas =>
          cases tas with
          | nil =>
              by_cases hca : ca ∈ values.map (·.val)
              · have hcaV : (⟨ca⟩ : Presentation.ValueName) ∈ values := (mem_values_map values ca).mp hca
                rw [hnf] at heq
                have heq' : Term.con (renameText ρg ca) Terms.nil = .con (renameText ρg m) .nil := by
                  simpa [Binding.renameValueTerm, hcaV] using heq
                have hsp : renameText ρg ca = renameText ρg m := (Term.con.inj heq').1
                have hc : ca = m := renameText_injective ρg hsp
                exact h (by
                  rw [hnf, hc])
              · have hcaV : ¬ (⟨ca⟩ : Presentation.ValueName) ∈ values := by
                  intro hm; exact hca ((mem_values_map values ca).mpr hm)
                rw [hnf] at heq
                have heq' : Term.con ca Terms.nil = .con (renameText ρg m) .nil := by
                  simpa [Binding.renameValueTerm, hcaV] using heq
                have hsp : ca = renameText ρg m := (Term.con.inj heq').1
                have hfix := ha ca (termNullaryCons_nf a (by
                  rw [hnf]
                  simp [termNullaryCons])) hca
                have hc : ca = m := renameText_injective ρg (by rw [hfix]; exact hsp)
                exact h (by
                  rw [hnf, hc])
          | cons _ _ =>
              rw [hnf] at heq
              simp [Binding.renameValueTerm] at heq
              cases heq.2
    simp only [Lara.nfTerm, Lara.nfTerms, beq_iff_eq]
    constructor
    · intro heq
      exact False.elim (h' heq)
    · intro heq
      exact False.elim (h heq)

private theorem sameSurfaceTerm_renameValueTerm
    (ha : TermFixed ρg values a) (hb : TermFixed ρg values b) :
    sameSurfaceTerm (Binding.renameValueTerm ρg values a)
        (Binding.renameValueTerm ρg values b) =
      sameSurfaceTerm a b := by
  apply Bool.eq_iff_iff.mpr
  exact sameSurfaceTerm_renameValueTerm_iff ρg values ha hb

mutual
  private theorem renameValueTerm_eq_self_of_fixedSpellings
      (t : Term)
      (fixed : ∀ c, c ∈ termNullaryCons t → renameText ρg c = c) :
      Binding.renameValueTerm ρg values t = t := by
    cases t with
    | num _ => rfl
    | str _ => rfl
    | con name terms =>
        cases terms with
        | nil =>
            by_cases member : (⟨name⟩ : Presentation.ValueName) ∈ values
            · simp [Binding.renameValueTerm, member,
                fixed name (by simp [termNullaryCons])]
            · simp [Binding.renameValueTerm, member]
        | cons term rest =>
            simp only [Binding.renameValueTerm]
            congr 1
            apply renameValueTerms_eq_self_of_fixedSpellings
            intro c hc
            exact fixed c (by
              simpa [termNullaryCons] using hc)
  private theorem renameValueTerms_eq_self_of_fixedSpellings
      (terms : Terms)
      (fixed : ∀ c, c ∈ termsNullaryCons terms → renameText ρg c = c) :
      Binding.renameValueTerms ρg values terms = terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp only [Binding.renameValueTerms]
        rw [renameValueTerm_eq_self_of_fixedSpellings term (by
          intro c hc
          exact fixed c (by
            simp [termsNullaryCons]
            exact Or.inl hc))]
        rw [renameValueTerms_eq_self_of_fixedSpellings rest (by
          intro c hc
          exact fixed c (by
            simp [termsNullaryCons]
            exact Or.inr hc))]
end

theorem lookupSurfaceSubst_rename
    (ρg : GlobalRenaming) (values : List Presentation.ValueName)
    (subst : SurfaceSubst) (param : Presentation.Param) :
    lookupSurfaceSubst (Binding.renameSubstValues ρg values subst) param =
      (lookupSurfaceSubst subst param).map
        (Binding.renameValueTerm ρg values) := by
  induction subst with
  | nil => rfl
  | cons entry rest ih =>
      simp only [Binding.renameSubstValues, List.map_cons,
        lookupSurfaceSubst, List.findSome?_cons]
      by_cases equal : entry.1 = param
      · simp [equal]
      · rw [if_neg equal, if_neg equal]
        change lookupSurfaceSubst (Binding.renameSubstValues ρg values rest) param =
          Option.map (Binding.renameValueTerm ρg values)
            (lookupSurfaceSubst rest param)
        exact ih

mutual
  private theorem instantiateSurfacePat_rename
      (hpat : PatFixed ρg pat) :
      instantiateSurfacePat (Binding.renameSubstValues ρg values subst) pat =
        (instantiateSurfacePat subst pat).map
          (Binding.renameValueTerm ρg values) := by
    cases pat with
    | var param =>
        exact lookupSurfaceSubst_rename ρg values subst param
    | lit term =>
        simp only [instantiateSurfacePat, Option.map_some]
        congr 1
        symm
        apply renameValueTerm_eq_self_of_fixedSpellings
        intro c hc
        exact hpat c (by simpa [patNullaryCons] using hc)
    | con name pats =>
        cases pats with
        | nil =>
            have nameFixed : renameText ρg name = name :=
              hpat name (by simp [patNullaryCons])
            by_cases member : (⟨name⟩ : Presentation.ValueName) ∈ values
            · simp [instantiateSurfacePat, instantiateSurfacePats,
                Binding.renameValueTerm, member, nameFixed]
            · simp [instantiateSurfacePat, instantiateSurfacePats,
                Binding.renameValueTerm, member]
        | cons first rest =>
            have hhead : PatFixed ρg first := by
              intro c hc
              exact hpat c (by
                simp [patNullaryCons, patsNullaryCons]
                exact Or.inl hc)
            have htail : PatsFixed ρg rest := by
              intro c hc
              exact hpat c (by
                simp [patNullaryCons, patsNullaryCons]
                exact Or.inr hc)
            simp only [instantiateSurfacePat, instantiateSurfacePats]
            rw [instantiateSurfacePat_rename (subst := subst) hhead]
            rw [instantiateSurfacePats_rename (subst := subst) htail]
            cases instantiateSurfacePat subst first <;>
              cases instantiateSurfacePats subst rest <;>
                simp [Binding.renameValueTerm, Binding.renameValueTerms]
  private theorem instantiateSurfacePats_rename
      (hpats : PatsFixed ρg pats) :
      instantiateSurfacePats (Binding.renameSubstValues ρg values subst) pats =
        (instantiateSurfacePats subst pats).map
          (Binding.renameValueTerms ρg values) := by
    cases pats with
    | nil => rfl
    | cons pat rest =>
        have hhead : PatFixed ρg pat := by
          intro c hc
          exact hpats c (by
            simp [patsNullaryCons]
            exact Or.inl hc)
        have htail : PatsFixed ρg rest := by
          intro c hc
          exact hpats c (by
            simp [patsNullaryCons]
            exact Or.inr hc)
        simp only [instantiateSurfacePats]
        rw [instantiateSurfacePat_rename (subst := subst) hhead]
        rw [instantiateSurfacePats_rename (subst := subst) htail]
        cases instantiateSurfacePat subst pat <;>
          cases instantiateSurfacePats subst rest <;> rfl
end

private theorem instantiateSurfaceAtom_rename
    (hpattern : AtomPatFixed ρg pattern) :
    instantiateSurfaceAtom (Binding.renameSubstValues ρg values subst) pattern =
      (instantiateSurfaceAtom subst pattern).map
        (Binding.renameValueAtom ρg values) := by
  simp only [instantiateSurfaceAtom]
  rw [instantiateSurfacePats_rename (subst := subst) hpattern]
  cases instantiateSurfacePats subst pattern.args <;>
    simp [Binding.renameValueAtom]

private theorem paramsCoveredB_rename
    (ρg : GlobalRenaming) (values : List Presentation.ValueName)
    (params : List Presentation.Param) (subst : SurfaceSubst) :
    paramsCoveredB params (Binding.renameSubstValues ρg values subst) =
      paramsCoveredB params subst := by
  unfold paramsCoveredB
  induction params with
  | nil => rfl
  | cons param rest ih =>
      simp [lookupSurfaceSubst_rename, ih]

private theorem lookupValue_renameBindings
    (ρg : GlobalRenaming)
    (bindings : List Presentation.ValueBinding)
    (name : Presentation.ValueName) :
    lookupValue
        (bindings.map fun binding =>
          { binding with name := ρg.valueName binding.name })
        (ρg.valueName name) =
      lookupValue bindings name := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      simp only [List.map_cons, lookupValue, List.findSome?_cons]
      by_cases equal : binding.name = name
      · simp [equal]
      · have renamedNe : ρg.valueName binding.name ≠ ρg.valueName name :=
          fun h => equal (ρg.valueName_injective h)
        rw [if_neg equal, if_neg renamedNe]
        change lookupValue
            (rest.map fun binding =>
              { binding with name := ρg.valueName binding.name })
            (ρg.valueName name) =
          lookupValue rest name
        exact ih

private theorem lookupValue_eq_none_of_not_mem
    {bindings : List Presentation.ValueBinding}
    {name : Presentation.ValueName}
    (notMember : name ∉ bindings.map (·.name)) :
    lookupValue bindings name = none := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      have headNe : binding.name ≠ name := by
        intro equal
        exact notMember (by simp [equal])
      have tailNot : name ∉ rest.map (·.name) := by
        intro member
        exact notMember (by simp [member])
      simp only [lookupValue, List.findSome?_cons]
      rw [if_neg headNe]
      exact ih tailNot

private theorem renamedValueName_eq_text
    (ρg : GlobalRenaming) (name : Presentation.ValueName) :
    ρg.valueName name =
      (⟨renameText ρg name.val⟩ : Presentation.ValueName) := by
  cases renamed : ρg.valueName name with
  | mk image =>
      have equal : image = renameText ρg name.val := by
        simpa [renamed, renameText] using ρg.valueName_coherent name
      rw [equal]

private theorem lookupValue_renameText
    (ρg : GlobalRenaming) (program : Presentation.Program)
    (name : Presentation.ValueName) :
    lookupValue (Binding.renameProgram ρg program).valueBindings
        (⟨renameText ρg name.val⟩ : Presentation.ValueName) =
      lookupValue program.valueBindings name := by
  rw [← renamedValueName_eq_text]
  simpa [Binding.renameProgram] using
    lookupValue_renameBindings ρg program.valueBindings name

private theorem lookupValue_some_of_mem
    {bindings : List Presentation.ValueBinding}
    {name : Presentation.ValueName}
    (member : name ∈ bindings.map (·.name)) :
    ∃ replacement, lookupValue bindings name = some replacement := by
  induction bindings with
  | nil => simp at member
  | cons binding rest ih =>
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with equal | tailMember
      · subst equal
        exact ⟨binding.term, by simp [lookupValue]⟩
      · by_cases equal : binding.name = name
        · subst equal
          exact ⟨binding.term, by simp [lookupValue]⟩
        · obtain ⟨replacement, found⟩ := ih tailMember
          refine ⟨replacement, ?_⟩
          simpa [lookupValue, equal] using found

mutual
  theorem substituteValueTerm_rename
      (ρg : GlobalRenaming) (program : Presentation.Program) (term : Term)
      (hterm : TermFixed ρg (programValues program) term) :
      substituteValueTerm (Binding.renameProgram ρg program).valueBindings
          (Binding.renameValueTerm ρg (programValues program) term) =
        substituteValueTerm program.valueBindings term := by
    cases term with
    | num _ => rfl
    | str _ => rfl
    | con name terms =>
        cases terms with
        | nil =>
            by_cases member :
                (⟨name⟩ : Presentation.ValueName) ∈ programValues program
            · rw [show Binding.renameValueTerm ρg (programValues program)
                    (.con name .nil) =
                    .con (renameText ρg name) .nil by
                  simp [Binding.renameValueTerm, member]]
              simp only [substituteValueTerm]
              rw [lookupValue_renameText]
              obtain ⟨replacement, found⟩ :=
                lookupValue_some_of_mem (by
                  simpa [programValues] using member)
              simp [found]
            · have nameNot :
                  name ∉ (programValues program).map (·.val) := by
                intro h
                exact member ((mem_values_map (programValues program) name).mp h)
              have nameFixed : renameText ρg name = name :=
                hterm name (by simp [termNullaryCons]) nameNot
              rw [show Binding.renameValueTerm ρg (programValues program)
                    (.con name .nil) = .con name .nil by
                  simp [Binding.renameValueTerm, member]]
              simp only [substituteValueTerm]
              rw [← nameFixed, lookupValue_renameText, nameFixed]
        | cons first rest =>
            change Term.con name
                (substituteValueTerms
                  (Binding.renameProgram ρg program).valueBindings
                  (Binding.renameValueTerms ρg (programValues program)
                    (.cons first rest))) =
              Term.con name
                (substituteValueTerms program.valueBindings (.cons first rest))
            rw [substituteValueTerms_rename ρg program (.cons first rest)
              (termFixed_cons_iff hterm)]
  theorem substituteValueTerms_rename
      (ρg : GlobalRenaming) (program : Presentation.Program) (terms : Terms)
      (hterms : TermsFixed ρg (programValues program) terms) :
      substituteValueTerms (Binding.renameProgram ρg program).valueBindings
          (Binding.renameValueTerms ρg (programValues program) terms) =
        substituteValueTerms program.valueBindings terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp only [Binding.renameValueTerms, substituteValueTerms]
        rw [substituteValueTerm_rename ρg program term
          (hterms term (by simp [termsToList]))]
        rw [substituteValueTerms_rename ρg program rest (by
          intro nested hnested
          exact hterms nested (by simp [termsToList, hnested]))]
end

theorem substituteValueAtom_rename
    (ρg : GlobalRenaming) (program : Presentation.Program) (atom : Atom)
    (hatom : AtomFixed ρg (programValues program) atom) :
    substituteValueAtom (Binding.renameProgram ρg program).valueBindings
        (Binding.renameValueAtom ρg (programValues program) atom) =
      substituteValueAtom program.valueBindings atom := by
  cases atom with
  | atom pred terms =>
      simp only [substituteValueAtom, Binding.renameValueAtom]
      rw [substituteValueTerms_rename ρg program terms hatom]

private theorem termFixed_of_lookupSurfaceSubst
    (hsubst : SubstFixed ρg values subst)
    (found : lookupSurfaceSubst subst param = some term) :
    TermFixed ρg values term := by
  induction subst with
  | nil => simp [lookupSurfaceSubst] at found
  | cons entry rest ih =>
      simp only [lookupSurfaceSubst, List.findSome?_cons] at found
      by_cases equal : entry.1 = param
      · rw [if_pos equal] at found
        cases found
        exact hsubst entry (by simp)
      · rw [if_neg equal] at found
        apply ih
        · intro nested hnested
          exact hsubst nested (by simp [hnested])
        · exact found

private theorem termsFixed_spelling
    (fixed : TermsFixed ρg values terms)
    (member : spelling ∈ termsNullaryCons terms)
    (notValue : spelling ∉ values.map (·.val)) :
    renameText ρg spelling = spelling := by
  cases terms with
  | nil => simp [termsNullaryCons] at member
  | cons term rest =>
      rcases List.mem_append.mp member with headMember | tailMember
      · exact fixed term (by simp [termsToList]) spelling headMember notValue
      · exact termsFixed_spelling
          (terms := rest)
          (by
            intro nested nestedMember
            exact fixed nested (by simp [termsToList, nestedMember]))
          tailMember notValue
termination_by terms

mutual
  private theorem termFixed_of_instantiateSurfacePat
      (substFixed : SubstFixed ρg values subst)
      (patternFixed : PatFixed ρg pattern)
      (found : instantiateSurfacePat subst pattern = some term) :
      TermFixed ρg values term := by
    cases pattern with
    | var param =>
        exact termFixed_of_lookupSurfaceSubst substFixed found
    | lit literal =>
        simp only [instantiateSurfacePat, Option.some.injEq] at found
        subst term
        intro spelling member _
        exact patternFixed spelling (by
          simpa [patNullaryCons] using member)
    | con name patterns =>
        cases patterns with
        | nil =>
            simp only [instantiateSurfacePat, instantiateSurfacePats,
              Option.map_some, Option.some.injEq] at found
            subst term
            intro spelling member _
            simp only [termNullaryCons, List.mem_singleton] at member
            subst spelling
            exact patternFixed name (by simp [patNullaryCons])
        | cons head tail =>
            cases termsFound :
                instantiateSurfacePats subst (.cons head tail) with
            | none =>
                simp [instantiateSurfacePat, termsFound] at found
            | some terms =>
                simp only [instantiateSurfacePat, termsFound, Option.map_some,
                  Option.some.injEq] at found
                subst term
                have patternsFixed : PatsFixed ρg (.cons head tail) := by
                  intro spelling member
                  exact patternFixed spelling (by
                    simpa [patNullaryCons] using member)
                have termsFixed :=
                  termsFixed_of_instantiateSurfacePats
                    substFixed patternsFixed termsFound
                intro spelling member notValue
                cases terms with
                | nil =>
                    cases headFound :
                        instantiateSurfacePat subst head with
                    | none =>
                        simp [instantiateSurfacePats, headFound] at termsFound
                    | some headTerm =>
                        cases tailFound :
                            instantiateSurfacePats subst tail with
                        | none =>
                            simp [instantiateSurfacePats, headFound,
                              tailFound] at termsFound
                        | some tailTerms =>
                            simp [instantiateSurfacePats, headFound,
                              tailFound] at termsFound
                | cons first rest =>
                    exact termsFixed_spelling termsFixed
                      (by simpa [termNullaryCons] using member) notValue
  private theorem termsFixed_of_instantiateSurfacePats
      (substFixed : SubstFixed ρg values subst)
      (patternsFixed : PatsFixed ρg patterns)
      (found : instantiateSurfacePats subst patterns = some terms) :
      TermsFixed ρg values terms := by
    cases patterns with
    | nil =>
        simp only [instantiateSurfacePats, Option.some.injEq] at found
        subst terms
        intro term member
        simp [termsToList] at member
    | cons head tail =>
        cases headFound : instantiateSurfacePat subst head with
        | none =>
            simp [instantiateSurfacePats, headFound] at found
        | some headTerm =>
            cases tailFound : instantiateSurfacePats subst tail with
            | none =>
                simp [instantiateSurfacePats, headFound, tailFound] at found
            | some tailTerms =>
                have termsEq :
                    terms = .cons headTerm tailTerms := by
                  symm
                  simpa [instantiateSurfacePats, headFound, tailFound] using found
                subst terms
                have headFixed : PatFixed ρg head := by
                  intro spelling member
                  exact patternsFixed spelling (by
                    simp [patsNullaryCons, member])
                have tailFixed : PatsFixed ρg tail := by
                  intro spelling member
                  exact patternsFixed spelling (by
                    simp [patsNullaryCons, member])
                have headTermFixed :=
                  termFixed_of_instantiateSurfacePat
                    substFixed headFixed headFound
                have tailTermsFixed :=
                  termsFixed_of_instantiateSurfacePats
                    substFixed tailFixed tailFound
                intro term member
                simp only [termsToList, List.mem_cons] at member
                rcases member with rfl | member
                · exact headTermFixed
                · exact tailTermsFixed term member
end

private theorem atomFixed_of_instantiateSurfaceAtom
    (substFixed : SubstFixed ρg values subst)
    (patternFixed : AtomPatFixed ρg pattern)
    (found : instantiateSurfaceAtom subst pattern = some atom) :
    AtomFixed ρg values atom := by
  cases termsFound : instantiateSurfacePats subst pattern.args with
  | none => simp [instantiateSurfaceAtom, termsFound] at found
  | some terms =>
      simp only [instantiateSurfaceAtom, termsFound, Option.map_some,
        Option.some.injEq] at found
      subst atom
      exact termsFixed_of_instantiateSurfacePats
        substFixed patternFixed termsFound

private theorem substFixed_append_term
    (hsubst : SubstFixed ρg values subst)
    (hterm : TermFixed ρg values term) :
    SubstFixed ρg values (subst ++ [(param, term)]) := by
  intro entry hentry
  rw [List.mem_append] at hentry
  rcases hentry with hentry | hentry
  · exact hsubst entry hentry
  · simp at hentry
    rcases hentry with rfl
    exact hterm

mutual
  private theorem substFixed_of_matchSurfacePat
      (hsubst : SubstFixed ρg values subst)
      (hpat : PatFixed ρg pat)
      (hterm : TermFixed ρg values term)
      (matched : matchSurfacePat subst pat term = some output) :
      SubstFixed ρg values output := by
    cases pat with
    | var param =>
        simp only [matchSurfacePat, bindSurfaceParam] at matched
        cases found : lookupSurfaceSubst subst param with
        | none =>
            rw [found] at matched
            cases matched
            exact substFixed_append_term hsubst hterm
        | some prior =>
            rw [found] at matched
            by_cases same : sameSurfaceTerm prior term = true
            · simp [same] at matched
              cases matched
              exact hsubst
            · simp [same] at matched
    | lit expected =>
        simp only [matchSurfacePat] at matched
        by_cases same : sameSurfaceTerm expected term = true
        · simp [same] at matched
          cases matched
          exact hsubst
        · simp [same] at matched
    | con expected pats =>
        cases term with
        | num _ => simp [matchSurfacePat] at matched
        | str _ => simp [matchSurfacePat] at matched
        | con actual terms =>
            simp only [matchSurfacePat] at matched
            split at matched
            · exact substFixed_of_matchSurfacePats hsubst
                (by
                  intro c hc
                  cases pats with
                  | nil => simp [patsNullaryCons] at hc
                  | cons first rest =>
                      exact hpat c (by
                        simpa [patNullaryCons] using hc))
                (by
                  cases terms with
                  | nil =>
                      intro nested hnested
                      simp [termsToList] at hnested
                  | cons first rest =>
                      exact termFixed_cons_iff hterm)
                matched
            · cases matched
  private theorem substFixed_of_matchSurfacePats
      (hsubst : SubstFixed ρg values subst)
      (hpats : PatsFixed ρg pats)
      (hterms : TermsFixed ρg values terms)
      (matched : matchSurfacePats subst pats terms = some output) :
      SubstFixed ρg values output := by
    cases pats with
    | nil =>
        cases terms with
        | nil =>
            simp [matchSurfacePats] at matched
            cases matched
            exact hsubst
        | cons _ _ => simp [matchSurfacePats] at matched
    | cons pat rest =>
        cases terms with
        | nil => simp [matchSurfacePats] at matched
        | cons term tail =>
            simp only [matchSurfacePats] at matched
            cases headMatch : matchSurfacePat subst pat term with
            | none => simp [headMatch] at matched
            | some next =>
                rw [headMatch] at matched
                have hhead : PatFixed ρg pat := by
                  intro c hc
                  exact hpats c (by
                    simp [patsNullaryCons]
                    exact Or.inl hc)
                have htail : PatsFixed ρg rest := by
                  intro c hc
                  exact hpats c (by
                    simp [patsNullaryCons]
                    exact Or.inr hc)
                apply substFixed_of_matchSurfacePats
                  (substFixed_of_matchSurfacePat hsubst hhead
                    (hterms term (by simp [termsToList])) headMatch)
                  htail
                  (by
                    intro nested hnested
                    exact hterms nested (by simp [termsToList, hnested]))
                  matched
end




private theorem fixedPattern_eq_renameText_iff
    (expected actual : String)
    (expectedFixed : renameText ρg expected = expected) :
    expected = renameText ρg actual ↔ expected = actual := by
  constructor
  · intro equal
    apply renameText_injective ρg
    rw [expectedFixed]
    exact equal
  · intro equal
    subst equal
    exact expectedFixed.symm

mutual
  private theorem matchSurfacePat_rename
      (hsubst : SubstFixed ρg values subst)
      (hpat : PatFixed ρg pat)
      (hterm : TermFixed ρg values term) :
      matchSurfacePat (Binding.renameSubstValues ρg values subst) pat
          (Binding.renameValueTerm ρg values term) =
        (matchSurfacePat subst pat term).map
          (Binding.renameSubstValues ρg values) := by
    cases pat with
    | var param =>
        simp only [matchSurfacePat, bindSurfaceParam]
        rw [lookupSurfaceSubst_rename]
        cases found : lookupSurfaceSubst subst param with
        | none =>
            simp [found, Binding.renameSubstValues, List.map_append]
        | some prior =>
            have priorFixed := termFixed_of_lookupSurfaceSubst hsubst found
            have same := sameSurfaceTerm_renameValueTerm priorFixed hterm
            simp [found, same]
    | lit expected =>
        have expectedFixed :
            Binding.renameValueTerm ρg values expected = expected :=
          renameValueTerm_eq_self_of_fixedSpellings expected (by
            intro c hc
            exact hpat c (by simpa [patNullaryCons] using hc))
        have expectedTermFixed : TermFixed ρg values expected := by
          intro c hc hnot
          exact hpat c (by simpa [patNullaryCons] using hc)
        have same := sameSurfaceTerm_renameValueTerm expectedTermFixed hterm
        rw [expectedFixed] at same
        simp [matchSurfacePat, same]
    | con expected pats =>
        cases term with
        | num _ => rfl
        | str _ => rfl
        | con actual terms =>
            cases pats with
            | nil =>
                have expectedFixed : renameText ρg expected = expected :=
                  hpat expected (by simp [patNullaryCons])
                cases terms with
                | nil =>
                    by_cases member :
                        (⟨actual⟩ : Presentation.ValueName) ∈ values
                    · have names := fixedPattern_eq_renameText_iff
                        expected actual expectedFixed
                      by_cases equal : expected = actual
                      · have actualFixed : renameText ρg actual = actual := by
                          rw [← equal]
                          exact expectedFixed
                        have renamedTerm :
                            Binding.renameValueTerm ρg values
                                (.con actual .nil) =
                              .con actual .nil := by
                          simp [Binding.renameValueTerm, member, actualFixed]
                        rw [renamedTerm]
                        simp only [matchSurfacePat]
                        rw [if_pos equal, if_pos equal]
                        rfl
                      · have targetNe : expected ≠ renameText ρg actual :=
                          fun h => equal (names.mp h)
                        have renamedTerm :
                            Binding.renameValueTerm ρg values
                                (.con actual .nil) =
                              .con (renameText ρg actual) .nil := by
                          simp [Binding.renameValueTerm, member]
                        rw [renamedTerm]
                        simp only [matchSurfacePat]
                        rw [if_neg targetNe, if_neg equal]
                        rfl
                    · have renamedTerm :
                          Binding.renameValueTerm ρg values
                              (.con actual .nil) =
                            .con actual .nil := by
                        simp [Binding.renameValueTerm, member]
                      rw [renamedTerm]
                      by_cases equal : expected = actual
                      · simp only [matchSurfacePat]
                        rw [if_pos equal, if_pos equal]
                        rfl
                      · simp only [matchSurfacePat]
                        rw [if_neg equal, if_neg equal]
                        rfl
                | cons first rest =>
                    by_cases equal : expected = actual
                    · simp [Binding.renameValueTerm, Binding.renameValueTerms,
                        matchSurfacePat, matchSurfacePats, equal]
                    · simp [Binding.renameValueTerm, matchSurfacePat, equal]
            | cons firstPat restPats =>
                cases terms with
                | nil =>
                    by_cases member :
                        (⟨actual⟩ : Presentation.ValueName) ∈ values
                    · have renamedTerm :
                          Binding.renameValueTerm ρg values
                              (.con actual .nil) =
                            .con (renameText ρg actual) .nil := by
                        simp [Binding.renameValueTerm, member]
                      rw [renamedTerm]
                      simp [matchSurfacePat, matchSurfacePats]
                    · have renamedTerm :
                          Binding.renameValueTerm ρg values
                              (.con actual .nil) =
                            .con actual .nil := by
                        simp [Binding.renameValueTerm, member]
                      rw [renamedTerm]
                      simp [matchSurfacePat, matchSurfacePats]
                | cons firstTerm restTerms =>
                    by_cases equal : expected = actual
                    · subst equal
                      have hpats : PatsFixed ρg
                          (.cons firstPat restPats) := by
                        intro c hc
                        exact hpat c (by
                          simpa [patNullaryCons] using hc)
                      simp only [Binding.renameValueTerm, matchSurfacePat,
                        if_pos]
                      rw [matchSurfacePats_rename hsubst hpats
                        (termFixed_cons_iff hterm)]
                    · simp [Binding.renameValueTerm, matchSurfacePat, equal]
  private theorem matchSurfacePats_rename
      (hsubst : SubstFixed ρg values subst)
      (hpats : PatsFixed ρg pats)
      (hterms : TermsFixed ρg values terms) :
      matchSurfacePats (Binding.renameSubstValues ρg values subst) pats
          (Binding.renameValueTerms ρg values terms) =
        (matchSurfacePats subst pats terms).map
          (Binding.renameSubstValues ρg values) := by
    cases pats with
    | nil =>
        cases terms <;> rfl
    | cons pat rest =>
        cases terms with
        | nil => rfl
        | cons term tail =>
            have hhead : PatFixed ρg pat := by
              intro c hc
              exact hpats c (by
                simp [patsNullaryCons]
                exact Or.inl hc)
            have htail : PatsFixed ρg rest := by
              intro c hc
              exact hpats c (by
                simp [patsNullaryCons]
                exact Or.inr hc)
            have hterm : TermFixed ρg values term :=
              hterms term (by simp [termsToList])
            have htermTail : TermsFixed ρg values tail := by
              intro nested hnested
              exact hterms nested (by simp [termsToList, hnested])
            simp only [Binding.renameValueTerms, matchSurfacePats]
            rw [matchSurfacePat_rename hsubst hhead hterm]
            cases matched : matchSurfacePat subst pat term with
            | none => rfl
            | some next =>
                simp only [Option.map_some]
                change
                  matchSurfacePats
                      (Binding.renameSubstValues ρg values next) rest
                      (Binding.renameValueTerms ρg values tail) =
                    (matchSurfacePats next rest tail).map
                      (Binding.renameSubstValues ρg values)
                exact matchSurfacePats_rename
                  (substFixed_of_matchSurfacePat hsubst hhead hterm matched)
                  htail htermTail
end

private theorem matchSurfaceAtom_rename
    (hsubst : SubstFixed ρg values subst)
    (hpattern : AtomPatFixed ρg pattern)
    (hatom : AtomFixed ρg values atom) :
    matchSurfaceAtom (Binding.renameSubstValues ρg values subst) pattern
        (Binding.renameValueAtom ρg values atom) =
      (matchSurfaceAtom subst pattern atom).map
        (Binding.renameSubstValues ρg values) := by
  cases atom with
  | atom pred terms =>
      simp only [Binding.renameValueAtom, matchSurfaceAtom]
      split
      · exact matchSurfacePats_rename hsubst hpattern hatom
      · rfl

private theorem matchingSlotsAux_rename
    (patternsFixed : ∀ pattern ∈ patterns, AtomPatFixed ρg pattern)
    (propositionFixed : AtomFixed ρg values proposition) :
    matchingSlotsAux patterns
        (Binding.renameValueAtom ρg values proposition) index =
      (matchingSlotsAux patterns proposition index).map fun entry =>
        (entry.1, Binding.renameSubstValues ρg values entry.2) := by
  induction patterns generalizing index with
  | nil => rfl
  | cons pattern rest ih =>
      have patternFixed : AtomPatFixed ρg pattern :=
        patternsFixed pattern (by simp)
      have restFixed : ∀ candidate ∈ rest, AtomPatFixed ρg candidate := by
        intro candidate member
        exact patternsFixed candidate (by simp [member])
      have emptyFixed : SubstFixed ρg values [] := by
        intro entry member
        simp at member
      simp only [matchingSlotsAux]
      have headMatch :
          matchSurfaceAtom [] pattern
              (Binding.renameValueAtom ρg values proposition) =
            (matchSurfaceAtom [] pattern proposition).map
              (Binding.renameSubstValues ρg values) := by
        simpa [Binding.renameSubstValues] using
          matchSurfaceAtom_rename emptyFixed patternFixed propositionFixed
      rw [headMatch]
      cases matched : matchSurfaceAtom [] pattern proposition with
      | none =>
          simp [matched, ih restFixed]
      | some subst =>
          simp [matched, ih restFixed]

private theorem matchingSlots_rename
    (patternsFixed : ∀ pattern ∈ rule.premises, AtomPatFixed ρg pattern)
    (propositionFixed : AtomFixed ρg values proposition) :
    matchingSlots (Binding.renameRule ρg rule)
        (Binding.renameValueAtom ρg values proposition) =
      (matchingSlots rule proposition).map fun entry =>
        (entry.1, Binding.renameSubstValues ρg values entry.2) := by
  exact matchingSlotsAux_rename patternsFixed propositionFixed

private theorem takeDirective_eq_takeNlDirective (chars : List Char) :
    takeDirective chars = Binding.takeNlDirective chars := by
  induction chars with
  | nil => rfl
  | cons char rest =>
      by_cases close : char = '}'
      · subst close
        rfl
      · simp [takeDirective, Binding.takeNlDirective, close, *]

private theorem takeDirective_append_close
    (output suffix : List Char) (fresh : '}' ∉ output) :
    takeDirective (output ++ ('}' :: suffix)) = some (output, suffix) := by
  induction output with
  | nil => rfl
  | cons char rest ih =>
      simp only [List.mem_cons, not_or] at fresh
      have notClose : char ≠ '}' := Ne.symm fresh.1
      simp [takeDirective, notClose, ih fresh.2]

private theorem takeDirective_after_length_lt
    (found : takeDirective chars = some (body, after)) :
    after.length < chars.length := by
  induction chars generalizing body after with
  | nil =>
      simp [takeDirective] at found
  | cons char rest ih =>
      by_cases close : char = '}'
      · subst close
        simp [takeDirective] at found
        obtain ⟨rfl, rfl⟩ := found
        simp
      · cases nestedFound : takeDirective rest with
        | none =>
            simp [takeDirective, close, nestedFound] at found
        | some pair =>
            obtain ⟨nestedBody, remaining⟩ := pair
            simp [takeDirective, close, nestedFound] at found
            obtain ⟨rfl, rfl⟩ := found
            have shorter := ih nestedFound
            simp
            omega

private theorem parseNlFuel_eq_of_length_lt
    (leftBound : chars.length < leftFuel)
    (rightBound : chars.length < rightFuel) :
    parseNlFuel leftFuel chars = parseNlFuel rightFuel chars := by
  induction leftFuel generalizing chars rightFuel with
  | zero => omega
  | succ leftFuel ih =>
      cases rightFuel with
      | zero => omega
      | succ rightFuel =>
          cases chars with
          | nil => rfl
          | cons char rest =>
              by_cases openBrace : char = '{'
              · subst char
                cases rest with
                | nil => rfl
                | cons second tail =>
                    by_cases escaped : second = '{'
                    · subst second
                      simp only [parseNlFuel]
                      apply ih <;> simp_all <;> omega
                    · cases found : takeDirective (second :: tail) with
                      | none =>
                          simp [parseNlFuel, escaped, found]
                      | some pair =>
                          obtain ⟨body, after⟩ := pair
                          unfold parseNlFuel
                          simp [escaped, found]
                          have afterLeft : after.length < leftFuel := by
                            have shorter := takeDirective_after_length_lt found
                            simp at shorter leftBound
                            omega
                          have afterRight : after.length < rightFuel := by
                            have shorter := takeDirective_after_length_lt found
                            simp at shorter rightBound
                            omega
                          exact congrArg
                            (fun result : Option (List (List Char)) =>
                              result.bind fun bodies => some (body :: bodies))
                            (ih afterLeft afterRight)
              · by_cases closeBrace : char = '}'
                · subst char
                  cases rest with
                  | nil => rfl
                  | cons second tail =>
                      by_cases escaped : second = '}'
                      · subst second
                        simp only [parseNlFuel]
                        apply ih <;> simp_all <;> omega
                      · simp [parseNlFuel, escaped]
                · simp [parseNlFuel, openBrace, closeBrace]
                  apply ih <;> simp_all <;> omega

private theorem parseNlFuel_renameNlChars
    (bound : chars.length < fuel)
    (fresh : ∀ body ∈ nlDirectiveBodiesFuel fuel chars,
      (Binding.renameDirective ρg body).head? ≠ some '{' ∧
        '}' ∉ Binding.renameDirective ρg body) :
    parseNlFuel
        ((Binding.renameNlChars ρg fuel chars).length + 1)
        (Binding.renameNlChars ρg fuel chars) =
      (parseNlFuel fuel chars).map
        (List.map (Binding.renameDirective ρg)) := by
  induction fuel generalizing chars with
  | zero => omega
  | succ fuel ih =>
      cases chars with
      | nil => rfl
      | cons char rest =>
          by_cases openBrace : char = '{'
          · subst char
            cases rest with
            | nil => rfl
            | cons second tail =>
                by_cases escaped : second = '{'
                · subst second
                  let output := Binding.renameNlChars ρg fuel tail
                  have tailBound : tail.length < fuel := by
                    simp at bound
                    omega
                  have tailFresh :
                      ∀ body ∈ nlDirectiveBodiesFuel fuel tail,
                        (Binding.renameDirective ρg body).head? ≠ some '{' ∧
                          '}' ∉ Binding.renameDirective ρg body := by
                    intro body member
                    exact fresh body (by
                      simpa [nlDirectiveBodiesFuel] using member)
                  have stable :
                      parseNlFuel (output.length + 2) output =
                        parseNlFuel (output.length + 1) output :=
                    parseNlFuel_eq_of_length_lt (by omega) (by omega)
                  simpa [Binding.renameNlChars, parseNlFuel, output] using
                    stable.trans (ih tailBound tailFresh)
                · cases found : takeDirective (second :: tail) with
                  | none =>
                      have bindingFound :
                          Binding.takeNlDirective (second :: tail) = none := by
                        rw [← takeDirective_eq_takeNlDirective]
                        exact found
                      simp [Binding.renameNlChars, parseNlFuel, escaped, found,
                        bindingFound]
                  | some pair =>
                      obtain ⟨body, after⟩ := pair
                      have bindingFound :
                          Binding.takeNlDirective (second :: tail) =
                            some (body, after) := by
                        rw [← takeDirective_eq_takeNlDirective]
                        exact found
                      have afterBound : after.length < fuel := by
                        have shorter := takeDirective_after_length_lt found
                        simp at shorter bound
                        omega
                      have bodyGuard :
                          (Binding.renameDirective ρg body).head? ≠ some '{' ∧
                            '}' ∉ Binding.renameDirective ρg body :=
                        fresh body (by
                          simp [nlDirectiveBodiesFuel, escaped, found])
                      have afterFresh :
                          ∀ candidate ∈ nlDirectiveBodiesFuel fuel after,
                            (Binding.renameDirective ρg candidate).head? ≠
                                some '{' ∧
                              '}' ∉ Binding.renameDirective ρg candidate := by
                        intro candidate member
                        exact fresh candidate (by
                          simp [nlDirectiveBodiesFuel, escaped, found, member])
                      let renamedBody := Binding.renameDirective ρg body
                      let output := Binding.renameNlChars ρg fuel after
                      have targetTake :
                          takeDirective (renamedBody ++ '}' :: output) =
                            some (renamedBody, output) :=
                        takeDirective_append_close renamedBody output bodyGuard.2
                      have targetStep :
                          parseNlFuel
                              (renamedBody.length + output.length + 3)
                              ('{' :: (renamedBody ++ '}' :: output)) =
                            (parseNlFuel
                                (renamedBody.length + output.length + 2)
                                output).bind
                              (fun bodies => some (renamedBody :: bodies)) := by
                        have headFresh := bodyGuard.1
                        have closeFresh := bodyGuard.2
                        change renamedBody.head? ≠ some '{' at headFresh
                        change '}' ∉ renamedBody at closeFresh
                        cases hRenamed : renamedBody with
                        | nil =>
                            rfl
                        | cons head bodyTail =>
                            rw [hRenamed] at headFresh closeFresh
                            simp only [List.head?_cons, List.mem_cons,
                              not_or] at headFresh closeFresh
                            have headNotOpen : head ≠ '{' := by
                              intro equal
                              apply headFresh
                              simp [equal]
                            have targetTakeCons :
                                takeDirective
                                    ((head :: bodyTail) ++ '}' :: output) =
                                  some (head :: bodyTail, output) :=
                              takeDirective_append_close (head :: bodyTail)
                                output (by
                                  simpa only [List.mem_cons, not_or] using
                                    closeFresh)
                            simp [parseNlFuel, headNotOpen]
                            rw [show head :: (bodyTail ++ '}' :: output) =
                              (head :: bodyTail) ++ '}' :: output by rfl,
                              targetTakeCons]
                            rfl
                      have sourceStep :
                          parseNlFuel (fuel + 1) ('{' :: second :: tail) =
                            (parseNlFuel fuel after).bind
                              (fun bodies => some (body :: bodies)) := by
                        simp [parseNlFuel, escaped, found]
                      have stable :
                          parseNlFuel (renamedBody.length + output.length + 2)
                              output =
                            parseNlFuel (output.length + 1) output :=
                        parseNlFuel_eq_of_length_lt (by omega) (by omega)
                      simp [Binding.renameNlChars, escaped, bindingFound]
                      change
                        parseNlFuel
                            (renamedBody.length + output.length + 3)
                            ('{' :: (renamedBody ++ '}' :: output)) =
                          Option.map (List.map (Binding.renameDirective ρg))
                            (parseNlFuel (fuel + 1) ('{' :: second :: tail))
                      rw [targetStep, sourceStep, stable,
                        ih afterBound afterFresh]
                      cases parseNlFuel fuel after <;> rfl
          · by_cases closeBrace : char = '}'
            · subst char
              cases rest with
              | nil =>
                  cases fuel with
                  | zero =>
                      simp at bound
                  | succ fuel => rfl
              | cons second tail =>
                  by_cases escaped : second = '}'
                  · subst second
                    let output := Binding.renameNlChars ρg fuel tail
                    have tailBound : tail.length < fuel := by
                      simp at bound
                      omega
                    have tailFresh :
                        ∀ body ∈ nlDirectiveBodiesFuel fuel tail,
                          (Binding.renameDirective ρg body).head? ≠ some '{' ∧
                            '}' ∉ Binding.renameDirective ρg body := by
                      intro body member
                      exact fresh body (by
                        simpa [nlDirectiveBodiesFuel] using member)
                    have stable :
                        parseNlFuel (output.length + 2) output =
                          parseNlFuel (output.length + 1) output :=
                      parseNlFuel_eq_of_length_lt (by omega) (by omega)
                    simpa [Binding.renameNlChars, parseNlFuel, output] using
                      stable.trans (ih tailBound tailFresh)
                  · cases fuel with
                    | zero =>
                        simp at bound
                    | succ fuel =>
                        by_cases secondOpen : second = '{'
                        · subst second
                          have outer :
                              Binding.renameNlChars ρg (fuel + 2)
                                  ('}' :: '{' :: tail) =
                                '}' :: Binding.renameNlChars ρg (fuel + 1)
                                  ('{' :: tail) := by
                            rfl
                          obtain ⟨renamedTail, inner⟩ :
                              ∃ renamedTail,
                                Binding.renameNlChars ρg (fuel + 1)
                                    ('{' :: tail) =
                                  '{' :: renamedTail := by
                            cases tail with
                            | nil => exact ⟨[], rfl⟩
                            | cons third remaining =>
                                by_cases escapedOpen : third = '{'
                                · subst third
                                  exact ⟨'{' ::
                                    Binding.renameNlChars ρg fuel remaining, rfl⟩
                                · cases directive :
                                    Binding.takeNlDirective (third :: remaining)
                                  <;> simp [Binding.renameNlChars, escapedOpen,
                                    directive]
                          rw [outer, inner]
                          rfl
                        · simp [Binding.renameNlChars, parseNlFuel, escaped,
                            secondOpen]
            · have restBound : rest.length < fuel := by
                simp at bound
                omega
              have restFresh :
                  ∀ body ∈ nlDirectiveBodiesFuel fuel rest,
                    (Binding.renameDirective ρg body).head? ≠ some '{' ∧
                      '}' ∉ Binding.renameDirective ρg body := by
                intro body member
                exact fresh body (by
                  simpa [nlDirectiveBodiesFuel, openBrace, closeBrace]
                    using member)
              simpa [Binding.renameNlChars, parseNlFuel, openBrace, closeBrace]
                using ih restBound restFresh
theorem parseNl_renameNl
    (sound : RenamingSound ρg program policy)
    (text : String) (member : text ∈ claimNls program) :
    parseNl (Binding.renameNl ρg text) =
      (parseNl text).map (List.map (Binding.renameDirective ρg)) := by
  unfold parseNl Binding.renameNl
  simp only [String.toList_ofList]
  apply parseNlFuel_renameNlChars
  · omega
  · intro body bodyMember
    exact sound.directiveDelimiterFresh body (by
      simp only [programNlDirectiveBodies, List.mem_flatMap]
      exact ⟨text, member, by
        simpa [nlDirectiveBodies] using bodyMember⟩)
private theorem stripPrefixChars_some_prefix
    (found : Binding.stripPrefixChars expectedPrefix input = some suffix) :
    expectedPrefix <+: input := by
  induction expectedPrefix generalizing input suffix with
  | nil => simp
  | cons expected rest ih =>
      cases input with
      | nil =>
          simp [Binding.stripPrefixChars] at found
      | cons actual tail =>
          unfold Binding.stripPrefixChars at found
          split at found
          · subst actual
            exact List.cons_prefix_cons.mpr ⟨rfl, ih found⟩
          · simp at found

private theorem valueDirectiveBodies_rename
    (sound : RenamingSound ρg program policy) :
    valueDirectiveBodies
        ⟨Binding.renameProgram ρg program, Binding.renamePolicy ρg policy⟩ =
      (valueDirectiveBodies ⟨program, policy⟩).map
        (Binding.renameDirective ρg) := by
  simp only [valueDirectiveBodies, valueNames_renameProgram, List.map_map]
  apply List.map_congr_left
  intro name member
  simp only [Function.comp_apply]
  unfold Binding.renameDirective
  cases found :
      Binding.stripPrefixChars "cell ".toList name.val.toList with
  | none =>
      simp [Binding.renameText]
  | some suffix =>
      have hasPrefix := stripPrefixChars_some_prefix found
      have starts : name.val.startsWith "cell " = true :=
        String.startsWith_string_iff.mpr hasPrefix
      rw [sound.noCellValues name member] at starts
      contradiction
mutual
  private theorem termNums_renameValueTerm
      (ρg : Binding.GlobalRenaming)
      (values : List Presentation.ValueName) (term : Term) :
      Lara.Cell.termNums (Binding.renameValueTerm ρg values term) =
        Lara.Cell.termNums term := by
    cases term with
    | num source => rfl
    | str source => rfl
    | con name terms =>
        cases terms with
        | nil =>
            by_cases member : (⟨name⟩ : Presentation.ValueName) ∈ values <;>
              simp [Binding.renameValueTerm, member, Lara.Cell.termNums,
                Lara.Cell.termsNums]
        | cons term rest =>
            simp [Binding.renameValueTerm, Lara.Cell.termNums,
              termsNums_renameValueTerms ρg values (.cons term rest)]
  private theorem termsNums_renameValueTerms
      (ρg : Binding.GlobalRenaming)
      (values : List Presentation.ValueName) (terms : Terms) :
      Lara.Cell.termsNums (Binding.renameValueTerms ρg values terms) =
        Lara.Cell.termsNums terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp [Binding.renameValueTerms, Lara.Cell.termsNums,
          termNums_renameValueTerm ρg values term,
          termsNums_renameValueTerms ρg values rest]
end

private theorem cellObligationB_renameValueAtom
    (ρg : Binding.GlobalRenaming)
    (values : List Presentation.ValueName) (atom : Atom) :
    cellObligationB (Binding.renameValueAtom ρg values atom) =
      cellObligationB atom := by
  cases atom with
  | atom predicate terms =>
      simp [cellObligationB, Binding.renameValueAtom,
        termsNums_renameValueTerms]

private theorem renameDirective_cell
    (ρg : Binding.GlobalRenaming) (leaf : Presentation.LeafId) :
    Binding.renameDirective ρg ("cell ".toList ++ leaf.val.toList) =
      "cell ".toList ++ (ρg.leaf leaf).val.toList := by
  simp [Binding.renameDirective, Binding.stripPrefixChars, Binding.renameText]

private theorem cellDirectiveBodies_rename
    (sound : RenamingSound ρg program policy) :
    cellDirectiveBodies
        ⟨Binding.renameProgram ρg program, Binding.renamePolicy ρg policy⟩ =
      (cellDirectiveBodies ⟨program, policy⟩).map
        (Binding.renameDirective ρg) := by
  simp only [cellDirectiveBodies, declaredLeaves_renameProgram]
  induction declaredLeaves program with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨leaf, atom⟩ := entry
      simp only [List.map_cons, List.filterMap_cons]
      rw [cellObligationB_renameValueAtom]
      by_cases obligation : cellObligationB atom = true
      · simp only [obligation, if_pos, List.map_cons]
        have headEq :
            "cell ".toList ++ (ρg.leaf leaf).val.toList =
              Binding.renameDirective ρg
                ("cell ".toList ++ leaf.val.toList) := by
          exact (renameDirective_cell ρg leaf).symm
        have restEq := ih
        rw [headEq]
        exact congrArg (List.cons (Binding.renameDirective ρg
          ("cell ".toList ++ leaf.val.toList))) restEq
      · cases cell : cellObligationB atom with
        | false =>
            simp only [cell, Bool.false_eq_true, if_false]
            simpa [Function.comp_def] using ih
        | true => exact (obligation cell).elim

private theorem claimNls_renameProgram
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program) :
    claimNls (Binding.renameProgram ρg program) =
      (claimNls program).map (Binding.renameNl ρg) := by
  simp only [claimNls, Binding.renameProgram]
  induction program.decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;>
        simp [Binding.renameDecl, Binding.renameComparison, ih]





theorem nodup_map_iff_of_injective
    {α β : Type} {f : α → β} {xs : List α}
    (injective : Function.Injective f) :
    (xs.map f).Nodup ↔ xs.Nodup := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      simp [ih, injective.eq_iff]
private theorem parseNlFuel_some_eq_nlDirectiveBodiesFuel :
    ∀ fuel chars bodies,
      parseNlFuel fuel chars = some bodies →
        nlDirectiveBodiesFuel fuel chars = bodies := by
  intro fuel
  induction fuel with
  | zero =>
      intro chars bodies found
      simp [parseNlFuel] at found
      rcases found with ⟨rfl, rfl⟩
      rfl
  | succ fuel ih =>
      intro chars bodies found
      cases chars with
      | nil =>
          simp [parseNlFuel, nlDirectiveBodiesFuel] at found ⊢
          exact found
      | cons char rest =>
          by_cases openBrace : char = '{'
          · subst char
            cases rest with
            | nil => simp [parseNlFuel, takeDirective] at found
            | cons second tail =>
                by_cases escaped : second = '{'
                · subst second
                  simpa [parseNlFuel, nlDirectiveBodiesFuel] using
                    ih tail bodies found
                · cases taken : takeDirective (second :: tail) with
                  | none =>
                      simp [parseNlFuel, escaped, taken] at found
                  | some result =>
                      obtain ⟨body, after⟩ := result
                      cases parsed : parseNlFuel fuel after with
                      | none =>
                          simp [parseNlFuel, escaped, taken, parsed] at found
                      | some parsedBodies =>
                          simp [parseNlFuel, escaped, taken, parsed] at found
                          subst bodies
                          simp [nlDirectiveBodiesFuel, escaped, taken,
                            ih after parsedBodies parsed]
          · by_cases closeBrace : char = '}'
            · subst char
              cases rest with
              | nil => simp [parseNlFuel] at found
              | cons second tail =>
                  by_cases escaped : second = '}'
                  · subst second
                    simpa [parseNlFuel, nlDirectiveBodiesFuel] using
                      ih tail bodies found
                  · simp [parseNlFuel, escaped] at found
            · have foundRest : parseNlFuel fuel rest = some bodies := by
                simpa [parseNlFuel, openBrace, closeBrace] using found
              simpa [nlDirectiveBodiesFuel, openBrace, closeBrace] using
                ih rest bodies foundRest

private theorem cellDirectiveBody_mem_leafDirectiveBodies
    (body : List Char)
    (member : body ∈ cellDirectiveBodies ⟨program, policy⟩) :
    body ∈ (leafIds program).map
      (fun leaf => "cell ".toList ++ leaf.val.toList) := by
  simp [cellDirectiveBodies, declaredLeaves] at member
  rcases member with
    ⟨leaf, atom, ⟨declaration, declarationMember, declarationEq⟩,
      obligation, rfl⟩
  simp only [List.mem_map]
  refine ⟨leaf, ?_, rfl⟩
  change leaf ∈ program.decls.filterMap fun
    | .leaf declared => some declared.id
    | _ => none
  cases declaration <;> simp at declarationEq
  obtain ⟨rfl, rfl⟩ := declarationEq
  exact List.mem_filterMap.mpr
    ⟨_, declarationMember, rfl⟩

private theorem directiveWellFormed_rename_iff
    (sound : RenamingSound ρg program policy)
    (body : List Char) (member : body ∈ programNlDirectiveBodies program) :
    DirectiveWellFormed
        ⟨Binding.renameProgram ρg program, Binding.renamePolicy ρg policy⟩
        (Binding.renameDirective ρg body) ↔
      DirectiveWellFormed ⟨program, policy⟩ body := by
  rw [DirectiveWellFormed, DirectiveWellFormed,
    valueDirectiveBodies_rename sound, cellDirectiveBodies_rename sound]
  have bodyMember : body ∈ programDirectiveBodies program := by
    simp [programDirectiveBodies, member]
  constructor
  · intro renamed
    rcases renamed with valueMember | cellMember
    · obtain ⟨candidate, candidateMember, equal⟩ :=
        List.mem_map.mp valueMember
      have candidateProgramMember :
          candidate ∈ programDirectiveBodies program := by
        simp only [programDirectiveBodies, List.mem_append]
        exact Or.inl (Or.inr (by
          simpa [valueDirectiveBodies] using candidateMember))
      have exact := sound.directiveInjective body bodyMember
        candidate candidateProgramMember equal.symm
      exact Or.inl (exact ▸ candidateMember)
    · obtain ⟨candidate, candidateMember, equal⟩ :=
        List.mem_map.mp cellMember
      have candidateProgramMember :
          candidate ∈ programDirectiveBodies program := by
        simp only [programDirectiveBodies, List.mem_append]
        exact Or.inr
          (cellDirectiveBody_mem_leafDirectiveBodies candidate candidateMember)
      have exact := sound.directiveInjective body bodyMember
        candidate candidateProgramMember equal.symm
      exact Or.inr (exact ▸ candidateMember)
  · intro source
    rcases source with valueMember | cellMember
    · exact Or.inl (List.mem_map.mpr ⟨body, valueMember, rfl⟩)
    · exact Or.inr (List.mem_map.mpr ⟨body, cellMember, rfl⟩)

private theorem nlWellFormed_rename_iff
    (sound : RenamingSound ρg program policy)
    (text : String) (member : text ∈ claimNls program) :
    NlWellFormed
        ⟨Binding.renameProgram ρg program, Binding.renamePolicy ρg policy⟩
        (Binding.renameNl ρg text) ↔
      NlWellFormed ⟨program, policy⟩ text := by
  unfold NlWellFormed
  rw [parseNl_renameNl sound text member]
  cases parsed : parseNl text with
  | none => rfl
  | some bodies =>
      simp only [Option.map_some]
      have inventoryEq : nlDirectiveBodies text = bodies := by
        unfold parseNl at parsed
        unfold nlDirectiveBodies
        exact parseNlFuel_some_eq_nlDirectiveBodiesFuel _ _ _ parsed
      have lexicalMember :
          ∀ body ∈ bodies, body ∈ programNlDirectiveBodies program := by
        intro body bodyMember
        apply List.mem_flatMap.mpr
        exact ⟨text, member, by simpa [inventoryEq] using bodyMember⟩
      constructor
      · intro renamed body bodyMember
        exact (directiveWellFormed_rename_iff sound body
          (lexicalMember body bodyMember)).mp
            (renamed (Binding.renameDirective ρg body)
              (List.mem_map.mpr ⟨body, bodyMember, rfl⟩))
      · intro source renamedBody renamedMember
        obtain ⟨body, bodyMember, rfl⟩ := List.mem_map.mp renamedMember
        exact (directiveWellFormed_rename_iff sound body
          (lexicalMember body bodyMember)).mpr (source body bodyMember)

private theorem declarationValueClaim_rename_iff
    (sound : RenamingSound ρg program policy)
    (declaration : Presentation.Decl)
    (member : declaration ∈ program.decls) :
    (match Binding.renameDecl ρg (programValues program) declaration with
      | .claim claim =>
          Lara.Sigma.wsAtom (Binding.renamePolicy ρg policy).sigma
            (substituteValueAtom
              (Binding.renameProgram ρg program).valueBindings claim.formal) =
            true
      | _ => True) ↔
      (match declaration with
      | .claim claim =>
          Lara.Sigma.wsAtom policy.sigma
            (substituteValueAtom program.valueBindings claim.formal) = true
      | _ => True) := by
  cases declaration with
  | claim claim =>
      have fixed : AtomFixed ρg (programValues program) claim.formal :=
        atomFixed_of_decl sound.toComparison (.claim claim) member claim.formal
          (by simp [declNullaryCons])
      simp [Binding.renameDecl, Binding.renamePolicy,
        substituteValueAtom_rename ρg program claim.formal fixed]
  | leaf leaf => simp [Binding.renameDecl]
  | arg argument => simp [Binding.renameDecl]
  | attack attack => simp [Binding.renameDecl]
  | status proposition => simp [Binding.renameDecl]
  | group group => simp [Binding.renameDecl]
  | comparison comparison => simp [Binding.renameDecl]

private theorem renamedValueName_ne_fixed_iff
    (ρg : Binding.GlobalRenaming) (name : Presentation.ValueName)
    (text : String) (fixed : Binding.renameText ρg text = text) :
    (ρg.valueName name).val ≠ text ↔ name.val ≠ text := by
  rw [ρg.valueName_coherent name]
  apply not_congr
  constructor
  · intro equal
    apply Binding.renameText_injective ρg
    exact equal.trans fixed.symm
  · intro equal
    simpa [Binding.renameText, equal] using fixed

theorem valueBindingsWellFormedB_rename
    (sound : RenamingSound ρg program policy) :
    valueBindingsWellFormedB
        ⟨Binding.renameProgram ρg program, Binding.renamePolicy ρg policy⟩ =
      valueBindingsWellFormedB ⟨program, policy⟩ := by
  apply Bool.eq_iff_iff.mpr
  rw [valueBindingsWellFormedB_iff, valueBindingsWellFormedB_iff]
  unfold ValueBindingsWellFormed
  have nodupIff :
      (valueNames (Binding.renameProgram ρg program)).Nodup ↔
        (valueNames program).Nodup := by
    rw [valueNames_renameProgram,
      nodup_map_iff_of_injective ρg.valueName_injective]
  have noCellIff :
      (∀ binding ∈ (Binding.renameProgram ρg program).valueBindings,
          binding.name.val ≠ "cell") ↔
        ∀ binding ∈ program.valueBindings, binding.name.val ≠ "cell" := by
    simp only [Binding.renameProgram, List.mem_map]
    constructor
    · intro renamed binding bindingMember
      apply (renamedValueName_ne_fixed_iff ρg binding.name "cell"
        sound.cell_spelling).mp
      exact renamed { binding with name := ρg.valueName binding.name }
        ⟨binding, bindingMember, rfl⟩
    · intro source renamedBinding renamedMember
      obtain ⟨binding, bindingMember, rfl⟩ := renamedMember
      exact (renamedValueName_ne_fixed_iff ρg binding.name "cell"
        sound.cell_spelling).mpr (source binding bindingMember)
  have sigmaIff :
      (∀ binding ∈ (Binding.renameProgram ρg program).valueBindings,
          ∀ con ∈ (Binding.renamePolicy ρg policy).sigma.cons,
            binding.name.val ≠ con.sym.name) ↔
        ∀ binding ∈ program.valueBindings,
          ∀ con ∈ policy.sigma.cons,
            binding.name.val ≠ con.sym.name := by
    simp only [Binding.renameProgram, Binding.renamePolicy, List.mem_map]
    constructor
    · intro renamed binding bindingMember con conMember
      apply (renamedValueName_ne_fixed_iff ρg binding.name con.sym.name
        (sound.sigma con conMember)).mp
      exact renamed { binding with name := ρg.valueName binding.name }
        ⟨binding, bindingMember, rfl⟩ con conMember
    · intro source renamedBinding renamedMember con conMember
      obtain ⟨binding, bindingMember, rfl⟩ := renamedMember
      exact (renamedValueName_ne_fixed_iff ρg binding.name con.sym.name
        (sound.sigma con conMember)).mpr
          (source binding bindingMember con conMember)
  have sortIff :
      (∀ binding ∈ (Binding.renameProgram ρg program).valueBindings,
          (Lara.Sigma.sortOf (Binding.renamePolicy ρg policy).sigma
            binding.term).isSome = true) ↔
        ∀ binding ∈ program.valueBindings,
          (Lara.Sigma.sortOf policy.sigma binding.term).isSome = true := by
    simp [Binding.renameProgram, Binding.renamePolicy]
  have claimsIff :
      ((Binding.renameProgram ρg program).valueBindings = [] ∨
        ∀ declaration ∈ (Binding.renameProgram ρg program).decls,
          match declaration with
          | .claim claim =>
              Lara.Sigma.wsAtom (Binding.renamePolicy ρg policy).sigma
                (substituteValueAtom
                  (Binding.renameProgram ρg program).valueBindings
                  claim.formal) = true
          | _ => True) ↔
        (program.valueBindings = [] ∨
          ∀ declaration ∈ program.decls,
            match declaration with
            | .claim claim =>
                Lara.Sigma.wsAtom policy.sigma
                  (substituteValueAtom program.valueBindings claim.formal) =
                    true
            | _ => True) := by
    constructor
    · intro renamed
      rcases renamed with empty | valid
      · exact Or.inl (by
          simpa [Binding.renameProgram] using empty)
      · refine Or.inr ?_
        intro declaration member
        cases declaration with
        | claim claim =>
            apply (declarationValueClaim_rename_iff sound (.claim claim)
              member).mp
            have renamedMember :
                Binding.renameDecl ρg (programValues program) (.claim claim) ∈
                  (Binding.renameProgram ρg program).decls :=
              List.mem_map.mpr ⟨.claim claim, member, rfl⟩
            exact valid
              (Binding.renameDecl ρg (programValues program) (.claim claim))
              renamedMember
        | leaf leaf => trivial
        | arg argument => trivial
        | attack attack => trivial
        | status proposition => trivial
        | group group => trivial
        | comparison comparison => trivial
    · intro source
      rcases source with empty | valid
      · exact Or.inl (by
          simp [Binding.renameProgram, empty])
      · refine Or.inr ?_
        intro renamedDeclaration renamedMember
        simp only [Binding.renameProgram, List.mem_map] at renamedMember
        obtain ⟨declaration, member, rfl⟩ := renamedMember
        cases declaration with
        | claim claim =>
            exact (declarationValueClaim_rename_iff sound (.claim claim)
              member).mpr (valid (.claim claim) member)
        | leaf leaf => trivial
        | arg argument => trivial
        | attack attack => trivial
        | status proposition => trivial
        | group group => trivial
        | comparison comparison => trivial
  have nlsIff :
      (∀ text ∈ claimNls (Binding.renameProgram ρg program),
          NlWellFormed
            ⟨Binding.renameProgram ρg program, Binding.renamePolicy ρg policy⟩
            text) ↔
        ∀ text ∈ claimNls program,
          NlWellFormed ⟨program, policy⟩ text := by
    rw [claimNls_renameProgram]
    constructor
    · intro renamed text member
      apply (nlWellFormed_rename_iff sound text member).mp
      exact renamed (Binding.renameNl ρg text)
        (List.mem_map.mpr ⟨text, member, rfl⟩)
    · intro source renamedText renamedMember
      obtain ⟨text, member, rfl⟩ := List.mem_map.mp renamedMember
      exact (nlWellFormed_rename_iff sound text member).mpr
        (source text member)
  constructor
  · rintro ⟨⟨⟨⟨⟨nodup, noCell⟩, sigma⟩, sorts⟩, claims⟩, nls⟩
    exact ⟨⟨⟨⟨⟨nodupIff.mp nodup, noCellIff.mp noCell⟩,
      sigmaIff.mp sigma⟩, sortIff.mp sorts⟩, claimsIff.mp claims⟩,
      nlsIff.mp nls⟩
  · rintro ⟨⟨⟨⟨⟨nodup, noCell⟩, sigma⟩, sorts⟩, claims⟩, nls⟩
    exact ⟨⟨⟨⟨⟨nodupIff.mpr nodup, noCellIff.mpr noCell⟩,
      sigmaIff.mpr sigma⟩, sortIff.mpr sorts⟩, claimsIff.mpr claims⟩,
      nlsIff.mpr nls⟩

def renameComparisonExpansionData (ρg : Binding.GlobalRenaming)
    (values : List Presentation.ValueName)
    (data : ComparisonExpansionData) : ComparisonExpansionData :=
  { data with
    goal := Binding.renameValueAtom ρg values data.goal
    thetaRecheck := Binding.renameSubstValues ρg values data.thetaRecheck
    thetaBridge := Binding.renameSubstValues ρg values data.thetaBridge
    recheck := Binding.renameRule ρg data.recheck
    bridge := Binding.renameRule ρg data.bridge }

theorem ruleById_rename
    (ρg : Binding.GlobalRenaming)
    (policy : Presentation.Policy) (id : Presentation.RuleId) :
    ruleById (Binding.renamePolicy ρg policy) (ρg.rule id) =
      (ruleById policy id).map (Binding.renameRule ρg) := by
  simp only [ruleById, Binding.renamePolicy]
  induction policy.rules with
  | nil => rfl
  | cons rule rest ih =>
      rw [List.map_cons, List.find?_cons, List.find?_cons]
      by_cases equal : rule.id = id
      · have renamedEqual :
            (Binding.renameRule ρg rule).id = ρg.rule id := by
          simp [Binding.renameRule, equal]
        simp [renamedEqual, equal]
      · have renamedNe :
            (Binding.renameRule ρg rule).id ≠ ρg.rule id := by
          simp only [Binding.renameRule]
          exact fun h => equal (ρg.rule_injective h)
        simp [renamedNe, equal, ih]

private theorem measurandById_rename
    (ρg : Binding.GlobalRenaming)
    (policy : Presentation.Policy) (id : Presentation.MeasurandId) :
    (Binding.renamePolicy ρg policy).measurands.find?
        (fun measurand => decide (measurand.id = ρg.measurand id)) =
      (policy.measurands.find?
        (fun measurand => decide (measurand.id = id))).map
          (fun measurand => { measurand with id := ρg.measurand measurand.id }) := by
  simp only [Binding.renamePolicy]
  induction policy.measurands with
  | nil => rfl
  | cons measurand rest ih =>
      rw [List.map_cons, List.find?_cons, List.find?_cons]
      by_cases equal : measurand.id = id
      · simp [equal]
      · have renamedNe : ρg.measurand measurand.id ≠ ρg.measurand id :=
          fun h => equal (ρg.measurand_injective h)
        simp [renamedNe, equal, ih]

private theorem comparisonScheme_rename
    (ρg : Binding.GlobalRenaming)
    (policy : Presentation.Policy) (relation : Presentation.Relation)
    (polarity : Presentation.Polarity) :
    (Binding.renamePolicy ρg policy).comparisonSchemes.find?
        (fun scheme =>
          decide (scheme.relation = relation ∧ scheme.polarity = polarity)) =
      (policy.comparisonSchemes.find?
        (fun scheme =>
          decide (scheme.relation = relation ∧
            scheme.polarity = polarity))).map
              (Binding.renameComparisonScheme ρg) := by
  simp only [Binding.renamePolicy]
  induction policy.comparisonSchemes with
  | nil => rfl
  | cons scheme rest ih =>
      rw [List.map_cons, List.find?_cons, List.find?_cons]
      by_cases selected :
          scheme.relation = relation ∧ scheme.polarity = polarity
      · simp [Binding.renameComparisonScheme, selected]
      · simp only [Binding.renameComparisonScheme, selected, decide_false,
          Bool.false_eq_true, List.find?_cons, if_false, Option.map_map]
        rw [ih]

private theorem leafProp?_rename
    (ρg : Binding.GlobalRenaming)
    (program : Presentation.Program) (id : Presentation.LeafId) :
    leafProp? (Binding.renameProgram ρg program) (ρg.leaf id) =
      (leafProp? program id).map
        (Binding.renameValueAtom ρg (programValues program)) := by
  simp only [leafProp?, declaredLeaves_renameProgram]
  induction declaredLeaves program with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨leaf, atom⟩ := entry
      rw [List.map_cons, List.findSome?_cons, List.findSome?_cons]
      by_cases equal : leaf = id
      · simp [equal]
      · have renamedNe : ρg.leaf leaf ≠ ρg.leaf id :=
          fun h => equal (ρg.leaf_injective h)
        simp [renamedNe, equal, ih]

private theorem atomCellDecimal?_rename
    (ρg : Binding.GlobalRenaming)
    (values : List Presentation.ValueName) (atom : Atom) :
    atomCellDecimal? (Binding.renameValueAtom ρg values atom) =
      atomCellDecimal? atom := by
  cases atom with
  | atom predicate terms =>
      simp [atomCellDecimal?, Binding.renameValueAtom,
        termsNums_renameValueTerms]

private theorem bridgeParts?_renameRule
    (ρg : Binding.GlobalRenaming) (rule : Presentation.Rule) :
    bridgeParts? (Binding.renameRule ρg rule) = bridgeParts? rule := by
  rfl

private theorem bridgeParts_patterns_mem
    (found : bridgeParts? rule = some parts) :
    parts.bindingPattern ∈ rule.premises ∧
      parts.comparisonPattern ∈ rule.premises := by
  unfold bridgeParts? at found
  split at found <;> simp_all [bindingPatternValues] <;> grind

private theorem roleParams_rename
    (ρg : Binding.GlobalRenaming)
    (values : List Presentation.ValueName)
    (resultSubst baseSubst : SurfaceSubst) (term : Term)
    (resultFixed : SubstFixed ρg values resultSubst)
    (baseFixed : SubstFixed ρg values baseSubst)
    (termFixed : TermFixed ρg values term) :
    roleParams (Binding.renameSubstValues ρg values resultSubst)
        (Binding.renameSubstValues ρg values baseSubst)
        (Binding.renameValueTerm ρg values term) =
      roleParams resultSubst baseSubst term := by
  unfold roleParams Binding.renameSubstValues
  rw [← List.map_append]
  have allFixed : SubstFixed ρg values (resultSubst ++ baseSubst) := by
    intro entry member
    rcases List.mem_append.mp member with member | member
    · exact resultFixed entry member
    · exact baseFixed entry member
  apply congrArg List.eraseDups
  have transport : ∀ subst : SurfaceSubst,
      SubstFixed ρg values subst →
      (((subst.map fun entry =>
          (entry.1, Binding.renameValueTerm ρg values entry.2)).filter
            (fun entry => sameSurfaceTerm entry.2
              (Binding.renameValueTerm ρg values term))).map (·.1)) =
        ((subst.filter fun entry =>
          sameSurfaceTerm entry.2 term).map (·.1)) := by
    intro subst fixed
    induction subst with
    | nil => rfl
    | cons entry rest ih =>
        simp only [List.map_cons, List.filter_cons]
        rw [sameSurfaceTerm_renameValueTerm
          (fixed entry (by simp)) termFixed]
        cases sameTerm : sameSurfaceTerm entry.2 term <;>
          simp [sameTerm, ih (fun candidate member =>
            fixed candidate (by simp [member]))]
  exact transport (resultSubst ++ baseSubst) allFixed

private theorem roleParams_renameSpelling
    (ρg : Binding.GlobalRenaming)
    (values : List Presentation.ValueName)
    (resultSubst baseSubst : SurfaceSubst) (spelling : String)
    (resultFixed : SubstFixed ρg values resultSubst)
    (baseFixed : SubstFixed ρg values baseSubst) :
    roleParams (Binding.renameSubstValues ρg values resultSubst)
        (Binding.renameSubstValues ρg values baseSubst)
        (.con (Binding.renameText ρg spelling) .nil) =
      roleParams resultSubst baseSubst (.con spelling .nil) := by
  unfold roleParams Binding.renameSubstValues
  rw [← List.map_append]
  have allFixed : SubstFixed ρg values (resultSubst ++ baseSubst) := by
    intro entry member
    rcases List.mem_append.mp member with member | member
    · exact resultFixed entry member
    · exact baseFixed entry member
  apply congrArg List.eraseDups
  have transport : ∀ subst : SurfaceSubst,
      SubstFixed ρg values subst →
      (((subst.map fun entry =>
          (entry.1, Binding.renameValueTerm ρg values entry.2)).filter
            (fun entry => sameSurfaceTerm entry.2
              (.con (Binding.renameText ρg spelling) .nil))).map (·.1)) =
        ((subst.filter fun entry =>
          sameSurfaceTerm entry.2 (.con spelling .nil)).map (·.1)) := by
    intro subst fixed
    induction subst with
    | nil => rfl
    | cons entry rest ih =>
        simp only [List.map_cons, List.filter_cons]
        have same :
            sameSurfaceTerm (Binding.renameValueTerm ρg values entry.2)
                (.con (Binding.renameText ρg spelling) .nil) =
              sameSurfaceTerm entry.2 (.con spelling .nil) := by
          apply Bool.eq_iff_iff.mpr
          exact sameSurfaceTerm_renameValueTerm_spelling_iff ρg values
            (fixed entry (by simp)) spelling
        rw [same]
        cases sameTerm :
            sameSurfaceTerm entry.2 (.con spelling .nil) <;>
          simp [sameTerm, ih (fun candidate member =>
            fixed candidate (by simp [member]))]
  exact transport (resultSubst ++ baseSubst) allFixed

private theorem roleSeed_rename
    (ρg : Binding.GlobalRenaming)
    (values : List Presentation.ValueName)
    (params : List Presentation.Param) (term : Term) :
    Binding.renameSubstValues ρg values (roleSeed params term) =
      roleSeed params (Binding.renameValueTerm ρg values term) := by
  simp [Binding.renameSubstValues, roleSeed, Function.comp_def]

private theorem substFixed_roleSeed
    (termFixed : TermFixed ρg values term) :
    SubstFixed ρg values (roleSeed params term) := by
  intro entry member
  unfold roleSeed at member
  obtain ⟨param, _, rfl⟩ := List.mem_map.mp member
  exact termFixed
private theorem substFixed_append
    (leftFixed : SubstFixed ρg values left)
    (rightFixed : SubstFixed ρg values right) :
    SubstFixed ρg values (left ++ right) := by
  intro entry member
  exact (List.mem_append.mp member).elim
    (leftFixed entry) (rightFixed entry)

private theorem renameSubstValues_append :
    Binding.renameSubstValues ρg values (left ++ right) =
      Binding.renameSubstValues ρg values left ++
        Binding.renameSubstValues ρg values right := by
  simp [Binding.renameSubstValues, List.map_append]


private theorem comparisonOperandSlot?_rename
    (ρg : Binding.GlobalRenaming)
    (values : List Presentation.ValueName)
    (subst baseSubst resultSubst : SurfaceSubst)
    (baseSlot resultSlot : Nat) (baseCell resultCell : Lara.Cell.Dec)
    (pattern : Presentation.Pat) (patternFixed : PatFixed ρg pattern) :
    comparisonOperandSlot?
        (Binding.renameSubstValues ρg values subst)
        (Binding.renameSubstValues ρg values baseSubst)
        (Binding.renameSubstValues ρg values resultSubst)
        baseSlot resultSlot baseCell resultCell pattern =
      comparisonOperandSlot? subst baseSubst resultSubst
        baseSlot resultSlot baseCell resultCell pattern := by
  have paramKeys : ∀ candidate : SurfaceSubst,
      (Binding.renameSubstValues ρg values candidate).map (·.1) =
        candidate.map (·.1) := by
    intro candidate
    simp [Binding.renameSubstValues, Function.comp_def]
  have byDecimal_rename : ∀ candidate : Term,
      (do
        let .num number := Binding.renameValueTerm ρg values candidate | none
        let decimal ← parseComparisonDecimal? number
        if Lara.Cell.ratEqB decimal baseCell then some baseSlot
        else if Lara.Cell.ratEqB decimal resultCell then some resultSlot
        else none) =
      (do
        let .num number := candidate | none
        let decimal ← parseComparisonDecimal? number
        if Lara.Cell.ratEqB decimal baseCell then some baseSlot
        else if Lara.Cell.ratEqB decimal resultCell then some resultSlot
        else none) := by
    intro candidate
    cases candidate with
    | num _ => rfl
    | str _ => rfl
    | con name terms =>
        cases terms with
        | nil =>
            by_cases member : (⟨name⟩ : Presentation.ValueName) ∈ values <;>
              simp [Binding.renameValueTerm, member]
        | cons _ _ => rfl
  unfold comparisonOperandSlot?
  rw [instantiateSurfacePat_rename patternFixed,
    paramKeys baseSubst, paramKeys resultSubst]
  cases instantiated : instantiateSurfacePat subst pattern with
  | none =>
      cases pattern <;> simp
  | some term =>
      cases pattern with
      | var param =>
          exact congrArg
            (fun byDecimal =>
              if (baseSubst.map (·.1)).contains param &&
                  !(resultSubst.map (·.1)).contains param then
                some baseSlot
              else if (resultSubst.map (·.1)).contains param &&
                  !(baseSubst.map (·.1)).contains param then
                some resultSlot
              else byDecimal)
            (byDecimal_rename term)
      | lit _ => exact byDecimal_rename term
      | con _ _ => exact byDecimal_rename term

private theorem substFixed_of_matchSurfaceAtom
    (substFixed : SubstFixed ρg values subst)
    (patternFixed : AtomPatFixed ρg pattern)
    (propositionFixed : AtomFixed ρg values proposition)
    (matched : matchSurfaceAtom subst pattern proposition = some result) :
    SubstFixed ρg values result := by
  cases proposition with
  | atom pred terms =>
      simp only [matchSurfaceAtom] at matched
      by_cases samePred : pattern.pred = pred
      · simp only [samePred, if_pos] at matched
        exact substFixed_of_matchSurfacePats substFixed patternFixed
          propositionFixed matched
      · simp [samePred] at matched

private theorem nullaryTermFixed_of_sameSurfaceTerm
    (entryFixed : TermFixed ρg values entry)
    (same : sameSurfaceTerm entry (.con spelling .nil) = true) :
    TermFixed ρg values (.con spelling .nil) := by
  intro candidate candidateMember notValue
  simp only [termNullaryCons, List.mem_singleton] at candidateMember
  subst candidate
  cases entry with
  | num source =>
      simp [sameSurfaceTerm, Lara.nfTerm, Lara.nfTerms] at same
  | str source =>
      simp [sameSurfaceTerm, Lara.nfTerm, Lara.nfTerms] at same
  | con name terms =>
      cases terms with
      | nil =>
          simp [sameSurfaceTerm, Lara.nfTerm, Lara.nfTerms] at same
          subst name
          exact entryFixed spelling (by simp [termNullaryCons]) notValue
      | cons head rest =>
          simp [sameSurfaceTerm, Lara.nfTerm, Lara.nfTerms] at same

private theorem nullaryTermFixed_of_roleParams_nonempty
    (resultFixed : SubstFixed ρg values resultSubst)
    (baseFixed : SubstFixed ρg values baseSubst)
    (nonempty :
      (roleParams resultSubst baseSubst (.con spelling .nil)).isEmpty =
        false) :
    TermFixed ρg values (.con spelling .nil) := by
  cases rolesFound :
      roleParams resultSubst baseSubst (.con spelling .nil) with
  | nil => simp [rolesFound] at nonempty
  | cons param rest =>
      have paramMember :
          param ∈ roleParams resultSubst baseSubst (.con spelling .nil) := by
        rw [rolesFound]
        simp
      unfold roleParams at paramMember
      simp only [List.mem_eraseDups, List.mem_map, List.mem_filter] at paramMember
      obtain ⟨entry, ⟨entryMember, same⟩, _⟩ := paramMember
      have entryFixed : TermFixed ρg values entry.2 := by
        rcases List.mem_append.mp entryMember with member | member
        · exact resultFixed entry member
        · exact baseFixed entry member
      exact nullaryTermFixed_of_sameSurfaceTerm entryFixed same

private theorem renameValueTerm_nullary_eq_renameText_of_fixed
    (fixed : TermFixed ρg values (.con spelling .nil)) :
    Binding.renameValueTerm ρg values (.con spelling .nil) =
      .con (Binding.renameText ρg spelling) .nil := by
  cases member : values.contains (⟨spelling⟩ : Presentation.ValueName)
  · have notValue : spelling ∉ values.map (·.val) := by
      intro spellingMember
      obtain ⟨value, valueMember, valueSpelling⟩ :=
        List.mem_map.mp spellingMember
      have valueEq : value = (⟨spelling⟩ : Presentation.ValueName) := by
        cases value
        simp_all
      have contained :
          (⟨spelling⟩ : Presentation.ValueName) ∈ values :=
        valueEq ▸ valueMember
      simpa [contained] using member
    unfold Binding.renameValueTerm
    rw [member]
    rw [fixed spelling (by simp [termNullaryCons]) notValue]
    simp
  · unfold Binding.renameValueTerm
    rw [member]
    simp

private theorem substFixed_of_matchingSlotsAux_member
    (patternsFixed :
      ∀ pattern ∈ patterns, AtomPatFixed ρg pattern)
    (propositionFixed : AtomFixed ρg values proposition)
    (member : (slot, subst) ∈
      matchingSlotsAux patterns proposition start) :
    SubstFixed ρg values subst := by
  induction patterns generalizing start with
  | nil => simp [matchingSlotsAux] at member
  | cons pattern rest ih =>
      have patternFixed := patternsFixed pattern (by simp)
      have restFixed :
          ∀ candidate ∈ rest, AtomPatFixed ρg candidate := by
        intro candidate candidateMember
        exact patternsFixed candidate (by simp [candidateMember])
      have emptyFixed : SubstFixed ρg values [] := by simp [SubstFixed]
      simp only [matchingSlotsAux] at member
      cases matched : matchSurfaceAtom [] pattern proposition with
      | none =>
          simp only [matched] at member
          exact ih restFixed member
      | some headSubst =>
          simp only [matched, List.mem_cons] at member
          rcases member with equal | tailMember
          · cases equal
            exact substFixed_of_matchSurfaceAtom emptyFixed patternFixed
              propositionFixed matched
          · exact ih restFixed tailMember

private theorem substFixed_of_matchingSlots_member
    (patternsFixed :
      ∀ pattern ∈ rule.premises, AtomPatFixed ρg pattern)
    (propositionFixed : AtomFixed ρg values proposition)
    (member : (slot, subst) ∈ matchingSlots rule proposition) :
    SubstFixed ρg values subst :=
  substFixed_of_matchingSlotsAux_member patternsFixed propositionFixed member

private theorem matchingSlotsFiltered_rename
    (patternsFixed :
      ∀ pattern ∈ rule.premises, AtomPatFixed ρg pattern)
    (propositionFixed : AtomFixed ρg values proposition)
    (param : Presentation.Param) :
    (matchingSlots (Binding.renameRule ρg rule)
        (Binding.renameValueAtom ρg values proposition)).filter
        (fun entry => (lookupSurfaceSubst entry.2 param).isSome) =
      ((matchingSlots rule proposition).filter
        (fun entry => (lookupSurfaceSubst entry.2 param).isSome)).map
          (fun entry =>
            (entry.1, Binding.renameSubstValues ρg values entry.2)) := by
  rw [matchingSlots_rename patternsFixed propositionFixed]
  induction matchingSlots rule proposition with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.map_cons, List.filter_cons,
        lookupSurfaceSubst_rename]
      cases lookupSurfaceSubst entry.2 param <;> simp [ih]

private theorem atomFixed_of_leafProp
    (sound : ComparisonRenamingSound ρg program policy)
    (id : Presentation.LeafId) (atom : Atom)
    (found : leafProp? program id = some atom) :
    AtomFixed ρg (programValues program) atom := by
  have pairMember : (id, atom) ∈ declaredLeaves program := by
    unfold leafProp? at found
    obtain ⟨before, entry, after, listEq, selected, _⟩ :=
      List.findSome?_eq_some_iff.mp found
    have entryEq : entry = (id, atom) := by
      rcases entry with ⟨entryId, entryAtom⟩
      by_cases equal : entryId = id
      · simp [equal] at selected
        simp [equal, selected]
      · simp [equal] at selected
    rw [listEq]
    simp [entryEq]
  obtain ⟨declaration, declarationMember, mapped⟩ :=
    List.mem_filterMap.mp pairMember
  apply atomFixed_of_decl sound declaration declarationMember atom
  cases declaration <;> simp_all [declaredLeaves, declNullaryCons]

private theorem recoverRecheckParam_renameRule
    (ρg : Binding.GlobalRenaming) (rule : Presentation.Rule)
    (fallback : Presentation.Param) (attempt : Option Presentation.Param) :
    recoverRecheckParam (Binding.renameRule ρg rule) fallback attempt =
      recoverRecheckParam rule fallback attempt := by
  simp [recoverRecheckParam, Binding.renameRule]

private def orderedComparisonMatch
    (baseSlot resultSlot : Nat)
    (seed : SurfaceSubst)
    (basePattern resultPattern : Presentation.AtomPat)
    (baseProposition resultProposition : Atom) : Option SurfaceSubst :=
  if baseSlot < resultSlot then
    (matchSurfaceAtom seed basePattern baseProposition).bind fun afterBase =>
      matchSurfaceAtom afterBase resultPattern resultProposition
  else
    (matchSurfaceAtom seed resultPattern resultProposition).bind fun afterResult =>
      matchSurfaceAtom afterResult basePattern baseProposition


private theorem orderedComparisonMatch_eq
    (baseSlot resultSlot : Nat)
    (seed : SurfaceSubst)
    (basePattern resultPattern : Presentation.AtomPat)
    (baseProposition resultProposition : Atom) :
    (if baseSlot < resultSlot then
      (matchSurfaceAtom seed basePattern baseProposition).bind fun afterBase =>
        matchSurfaceAtom afterBase resultPattern resultProposition
    else
      (matchSurfaceAtom seed resultPattern resultProposition).bind fun afterResult =>
        matchSurfaceAtom afterResult basePattern baseProposition) =
      orderedComparisonMatch baseSlot resultSlot seed basePattern resultPattern
        baseProposition resultProposition := rfl

private theorem orderedComparisonMatch_bind
    (baseSlot resultSlot : Nat)
    (seed : SurfaceSubst)
    (basePattern resultPattern : Presentation.AtomPat)
    (baseProposition resultProposition : Atom)
    (continuation : SurfaceSubst → Option α) :
    (if baseSlot < resultSlot then
      (matchSurfaceAtom seed basePattern baseProposition).bind fun afterBase =>
        (matchSurfaceAtom afterBase resultPattern resultProposition).bind continuation
    else
      (matchSurfaceAtom seed resultPattern resultProposition).bind fun afterResult =>
        (matchSurfaceAtom afterResult basePattern baseProposition).bind continuation) =
      (orderedComparisonMatch baseSlot resultSlot seed basePattern resultPattern
        baseProposition resultProposition).bind continuation := by
  unfold orderedComparisonMatch
  by_cases order : baseSlot < resultSlot
  · rw [if_pos order, if_pos order]
    cases first : matchSurfaceAtom seed basePattern baseProposition <;>
      simp [first]
  · rw [if_neg order, if_neg order]
    cases first : matchSurfaceAtom seed resultPattern resultProposition <;>
      simp [first]
private theorem orderedComparisonMatch_rename
    (seedFixed : SubstFixed ρg values seed)
    (basePatternFixed : AtomPatFixed ρg basePattern)
    (resultPatternFixed : AtomPatFixed ρg resultPattern)
    (basePropositionFixed : AtomFixed ρg values baseProposition)
    (resultPropositionFixed : AtomFixed ρg values resultProposition) :
    orderedComparisonMatch baseSlot resultSlot
        (Binding.renameSubstValues ρg values seed)
        basePattern resultPattern
        (Binding.renameValueAtom ρg values baseProposition)
        (Binding.renameValueAtom ρg values resultProposition) =
      (orderedComparisonMatch baseSlot resultSlot seed
        basePattern resultPattern baseProposition resultProposition).map
          (Binding.renameSubstValues ρg values) := by
  unfold orderedComparisonMatch
  by_cases order : baseSlot < resultSlot
  · rw [if_pos order, matchSurfaceAtom_rename seedFixed
      basePatternFixed basePropositionFixed]
    cases firstFound :
        matchSurfaceAtom seed basePattern baseProposition with
    | none => simp [order, firstFound]
    | some afterBase =>
        simp only [order, if_pos, firstFound, Option.map_some, Option.bind_some]
        have afterBaseFixed :=
          substFixed_of_matchSurfaceAtom seedFixed basePatternFixed
            basePropositionFixed firstFound
        rw [matchSurfaceAtom_rename afterBaseFixed
          resultPatternFixed resultPropositionFixed] <;> simp [order]
  · rw [if_neg order, matchSurfaceAtom_rename seedFixed
      resultPatternFixed resultPropositionFixed]
    cases firstFound :
        matchSurfaceAtom seed resultPattern resultProposition with
    | none => simp [order, firstFound]
    | some afterResult =>
        simp only [order, if_neg, firstFound, Option.map_some, Option.bind_some]
        have afterResultFixed :=
          substFixed_of_matchSurfaceAtom seedFixed resultPatternFixed
            resultPropositionFixed firstFound
        rw [matchSurfaceAtom_rename afterResultFixed
          basePatternFixed basePropositionFixed] <;> simp [order]

private theorem substFixed_of_orderedComparisonMatch
    (seedFixed : SubstFixed ρg values seed)
    (basePatternFixed : AtomPatFixed ρg basePattern)
    (resultPatternFixed : AtomPatFixed ρg resultPattern)
    (basePropositionFixed : AtomFixed ρg values baseProposition)
    (resultPropositionFixed : AtomFixed ρg values resultProposition)
    (found : orderedComparisonMatch baseSlot resultSlot seed
      basePattern resultPattern baseProposition resultProposition =
        some result) :
    SubstFixed ρg values result := by
  unfold orderedComparisonMatch at found
  by_cases order : baseSlot < resultSlot
  · rw [if_pos order] at found
    cases firstFound :
        matchSurfaceAtom seed basePattern baseProposition with
    | none => simp [firstFound] at found
    | some afterBase =>
        simp only [firstFound, Option.bind_some] at found
        have afterBaseFixed :=
          substFixed_of_matchSurfaceAtom seedFixed basePatternFixed
            basePropositionFixed firstFound
        exact substFixed_of_matchSurfaceAtom afterBaseFixed
          resultPatternFixed resultPropositionFixed found
  · rw [if_neg order] at found
    cases firstFound :
        matchSurfaceAtom seed resultPattern resultProposition with
    | none => simp [firstFound] at found
    | some afterResult =>
        simp only [firstFound, Option.bind_some] at found
        have afterResultFixed :=
          substFixed_of_matchSurfaceAtom seedFixed resultPatternFixed
            resultPropositionFixed firstFound
        exact substFixed_of_matchSurfaceAtom afterResultFixed
          basePatternFixed basePropositionFixed found

private def comparisonExpectedSlots
    (polarity : Presentation.Polarity) (baseSlot resultSlot : Nat) :
    Nat × Nat :=
  match polarity with
  | .higherIsBetter => (baseSlot, resultSlot)
  | .lowerIsBetter => (resultSlot, baseSlot)

private theorem comparisonExpectedSlots_eq
    (polarity : Presentation.Polarity) (baseSlot resultSlot : Nat) :
    comparisonExpectedSlots polarity baseSlot resultSlot =
      match polarity with
      | .higherIsBetter => (baseSlot, resultSlot)
      | .lowerIsBetter => (resultSlot, baseSlot) := by
  cases polarity <;> rfl

set_option maxHeartbeats 2000000 in
theorem comparisonExpansion?_rename
    (sound : ComparisonRenamingSound ρg program policy)
    (comparison : Presentation.Comparison)
    (member : Presentation.Decl.comparison comparison ∈ program.decls) :
    comparisonExpansion?
        (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (Binding.renameComparison ρg (programValues program) comparison) =
      (comparisonExpansion? program policy comparison).map
        (renameComparisonExpansionData ρg (programValues program)) := by
  have conclusionFixed :
      AtomFixed ρg (programValues program) comparison.conclusion :=
    atomFixed_of_decl sound (.comparison comparison) member
      comparison.conclusion (by simp [declNullaryCons])
  unfold Binding.renameComparison
  unfold comparisonExpansion?
  rw [measurandById_rename]
  cases measurandFound :
      policy.measurands.find?
        (fun measurand => decide (measurand.id = comparison.measurand)) with
  | none => rfl
  | some measurand =>
      simp only [Option.map_some, Option.bind_some]
      cases polarityFound : measurand.polarity with
      | none => simp [polarityFound]
      | some polarity =>
          simp only [Option.bind_eq_bind, Option.bind_some]
          rw [comparisonScheme_rename]
          cases schemeFound :
              policy.comparisonSchemes.find? (fun scheme =>
                decide (scheme.relation = comparison.relation ∧
                  scheme.polarity = polarity)) with
          | none =>
              rw [polarityFound]
              rw [Option.bind_some, schemeFound]
              rw [Option.map_none, Option.bind_none]
              rw [Option.bind_none, Option.map_none]
          | some scheme =>
              rw [polarityFound]
              rw [Option.bind_some, schemeFound]
              rw [Option.map_some, Option.bind_some]
              simp only [Binding.renameComparisonScheme]
              rw [ruleById_rename]
              cases recheckFound : ruleById policy scheme.recheck with
              | none =>
                  rw [Option.map_none, Option.bind_none]
                  rw [Option.bind_some, recheckFound, Option.bind_none, Option.map_none]
              | some recheck =>
                  rw [Option.map_some, Option.bind_some]
                  rw [Option.bind_some, recheckFound, Option.bind_some]
                  rw [ruleById_rename]
                  cases bridgeFound : ruleById policy scheme.bridge with
                  | none =>
                      rw [Option.map_none, Option.bind_none]
                      rw [Option.bind_none, Option.map_none]
                  | some bridge =>
                      rw [Option.map_some, Option.bind_some]
                      rw [Option.bind_some]
                      rw [bridgeParts?_renameRule]
                      simp only [Binding.renameRule]
                      cases goalShape : patsToList recheck.conclusion.args with
                      | nil => simp [goalShape]
                      | cons goalLeft tail =>
                          cases tail with
                          | nil => simp [goalShape]
                          | cons goalRight rest =>
                              cases rest with
                              | cons third rest => simp [goalShape]
                              | nil =>
                                  cases modeCheck :
                                      (recheck.mode != .strict ||
                                        bridge.mode != .defeasible) with
                                  | true => simp [modeCheck]
                                  | false =>
                                      simp only [modeCheck, Bool.false_eq_true,
                                        if_false, Option.bind_some]
                                      cases certFound :
                                          recheck.certifiers.find? (fun cert =>
                                            decide (cert.backend.val == "ord" &&
                                              cert.version == 1)) with
                                      | none => simp [certFound]
                                      | some certRef =>
                                          simp only [certFound, Option.bind_some]
                                          cases partsFound : bridgeParts? bridge with
                                          | none => simp [partsFound]
                                          | some parts =>
                                              simp only [partsFound, Option.bind_some]
                                              have resultRecovery :=
                                                recoverRecheckParam_renameRule
                                                  ρg recheck parts.systemParam
                                                  ((alignedSurfaceAtoms
                                                    recheck.conclusion
                                                    parts.comparisonPattern).bind
                                                      fun pairs =>
                                                        correspondingRecheckParam
                                                          pairs
                                                          parts.resultValueParam)
                                              simp only [Binding.renameRule] at resultRecovery
                                              rw [resultRecovery]
                                              cases resultParamFound :
                                                  recoverRecheckParam recheck
                                                    parts.systemParam
                                                    ((alignedSurfaceAtoms
                                                      recheck.conclusion
                                                      parts.comparisonPattern).bind
                                                        fun pairs =>
                                                          correspondingRecheckParam
                                                            pairs
                                                            parts.resultValueParam) with
                                              | none => simp [resultParamFound]
                                              | some recheckResultParam =>
                                                  simp only [resultParamFound,
                                                    Option.bind_some]
                                                  have baselineRecovery :=
                                                    recoverRecheckParam_renameRule
                                                      ρg recheck
                                                      parts.baselineParam
                                                      ((alignedSurfaceAtoms
                                                        recheck.conclusion
                                                        parts.comparisonPattern).bind
                                                          fun pairs =>
                                                            correspondingRecheckParam
                                                              pairs
                                                              parts.baselineValueParam)
                                                  simp only [Binding.renameRule] at baselineRecovery
                                                  rw [baselineRecovery]
                                                  cases baselineParamFound :
                                                      recoverRecheckParam recheck
                                                        parts.baselineParam
                                                        ((alignedSurfaceAtoms
                                                          recheck.conclusion
                                                          parts.comparisonPattern).bind
                                                            fun pairs =>
                                                              correspondingRecheckParam
                                                                pairs
                                                                parts.baselineValueParam) with
                                                  | none => simp [baselineParamFound]
                                                  | some recheckBaselineParam =>
                                                      simp only [baselineParamFound,
                                                        Option.bind_some]
                                                      cases conclusionEq :
                                                          comparison.conclusion with
                                                      | atom authoredPred authoredArgs =>
                                                          cases authoredArgs with
                                                          | nil =>
                                                              simp [conclusionEq,
                                                                Binding.renameValueAtom,
                                                                Binding.renameValueTerms]
                                                          | cons systemTerm rest =>
                                                              cases rest with
                                                              | nil =>
                                                                  simp [conclusionEq,
                                                                    Binding.renameValueAtom,
                                                                    Binding.renameValueTerms]
                                                              | cons baselineTerm tail =>
                                                                  cases tail with
                                                                  | cons extra tail =>
                                                                      simp [conclusionEq,
                                                                        Binding.renameValueAtom,
                                                                        Binding.renameValueTerms]
                                                                  | nil =>
                                                                      simp only [conclusionEq,
                                                                        Binding.renameValueAtom,
                                                                        Binding.renameValueTerms,
                                                                        Option.bind_some]
                                                                      have authoredFixed :=
                                                                        conclusionFixed
                                                                      rw [conclusionEq] at authoredFixed
                                                                      have systemFixed :
                                                                          TermFixed ρg
                                                                            (programValues program)
                                                                            systemTerm :=
                                                                        authoredFixed systemTerm
                                                                          (by simp [termsToList])
                                                                      have baselineFixed :
                                                                          TermFixed ρg
                                                                            (programValues program)
                                                                            baselineTerm :=
                                                                        authoredFixed baselineTerm
                                                                          (by simp [termsToList])
                                                                      cases predCheck :
                                                                          authoredPred !=
                                                                            parts.conclusionPred with
                                                                      | true => simp [predCheck]
                                                                      | false =>
                                                                          simp only [predCheck,
                                                                            Bool.false_eq_true,
                                                                            if_false,
                                                                            Option.bind_some]
                                                                          by_cases sameLeaf :
                                                                              comparison.result =
                                                                                comparison.baseline
                                                                          · have renamedSame :
                                                                                ρg.leaf comparison.result =
                                                                                  ρg.leaf comparison.baseline :=
                                                                              congrArg ρg.leaf sameLeaf
                                                                            simp [sameLeaf,
                                                                              renamedSame]
                                                                          · have renamedNe :
                                                                                ρg.leaf comparison.result ≠
                                                                                  ρg.leaf comparison.baseline :=
                                                                              fun equal =>
                                                                                sameLeaf
                                                                                  (ρg.leaf_injective
                                                                                    equal)
                                                                            simp only [sameLeaf,
                                                                              renamedNe, if_false,
                                                                              Option.bind_some]
                                                                            rw [leafProp?_rename,
                                                                              leafProp?_rename,
                                                                              leafProp?_rename]
                                                                            cases resultFound :
                                                                                leafProp? program
                                                                                  comparison.result with
                                                                            | none => simp [resultFound]
                                                                            | some resultProp =>
                                                                                simp only [resultFound,
                                                                                  Option.map_some,
                                                                                  Option.bind_some]
                                                                                cases baseFound :
                                                                                    leafProp? program
                                                                                      comparison.baseline with
                                                                                | none => simp [baseFound]
                                                                                | some baseProp =>
                                                                                    simp only [baseFound,
                                                                                      Option.map_some,
                                                                                      Option.bind_some]
                                                                                    cases bindingFound :
                                                                                        leafProp? program
                                                                                          comparison.binding with
                                                                                    | none =>
                                                                                        simp [bindingFound]
                                                                                    | some bindingProp =>
                                                                                        simp only [bindingFound,
                                                                                          Option.map_some,
                                                                                          Option.bind_some]
                                                                                        rw [atomCellDecimal?_rename,
                                                                                          atomCellDecimal?_rename]
                                                                                        cases resultCellFound :
                                                                                            atomCellDecimal?
                                                                                              resultProp with
                                                                                        | none =>
                                                                                            simp [resultCellFound]
                                                                                        | some resultCell =>
                                                                                            simp only [resultCellFound,
                                                                                              Option.bind_some]
                                                                                            cases baseCellFound :
                                                                                                atomCellDecimal?
                                                                                                  baseProp with
                                                                                            | none =>
                                                                                                simp [baseCellFound]
                                                                                            | some baseCell =>
                                                                                                simp only [baseCellFound,
                                                                                                  Option.bind_some]
                                                                                                have recheckMember :
                                                                                                    recheck ∈ policy.rules := by
                                                                                                  unfold ruleById at recheckFound
                                                                                                  exact
                                                                                                    List.mem_of_find?_eq_some
                                                                                                      recheckFound
                                                                                                have patternsFixed :
                                                                                                    ∀ pattern ∈
                                                                                                        recheck.premises,
                                                                                                      AtomPatFixed ρg
                                                                                                        pattern := by
                                                                                                  intro pattern
                                                                                                    patternMember
                                                                                                  apply
                                                                                                    atomPatFixed_of_rule
                                                                                                      sound recheck
                                                                                                      recheckMember
                                                                                                      pattern
                                                                                                  intro spelling
                                                                                                    spellingMember
                                                                                                  apply
                                                                                                    List.mem_append.mpr
                                                                                                  exact Or.inl
                                                                                                    (List.mem_append.mpr
                                                                                                      (Or.inl
                                                                                                        (List.mem_flatMap.mpr
                                                                                                          ⟨pattern,
                                                                                                            patternMember,
                                                                                                            spellingMember⟩)))
                                                                                                have resultPropFixed :=
                                                                                                  atomFixed_of_leafProp
                                                                                                    sound
                                                                                                    comparison.result
                                                                                                    resultProp
                                                                                                    resultFound
                                                                                                have basePropFixed :=
                                                                                                  atomFixed_of_leafProp
                                                                                                    sound
                                                                                                    comparison.baseline
                                                                                                    baseProp
                                                                                                    baseFound
                                                                                                have resultMatchesRename :=
                                                                                                  matchingSlotsFiltered_rename
                                                                                                    patternsFixed
                                                                                                    resultPropFixed
                                                                                                    recheckResultParam
                                                                                                simp only [Binding.renameRule] at resultMatchesRename
                                                                                                rw [resultMatchesRename]
                                                                                                have baseMatchesRename :=
                                                                                                  matchingSlotsFiltered_rename
                                                                                                    patternsFixed
                                                                                                    basePropFixed
                                                                                                    recheckBaselineParam
                                                                                                simp only [Binding.renameRule] at baseMatchesRename
                                                                                                rw [baseMatchesRename]
                                                                                                cases resultMatchesFound :
                                                                                                    (matchingSlots recheck
                                                                                                      resultProp).filter
                                                                                                        (fun entry =>
                                                                                                          (lookupSurfaceSubst
                                                                                                            entry.2
                                                                                                            recheckResultParam).isSome) with
                                                                                                | nil =>
                                                                                                    simp [resultMatchesFound]
                                                                                                | cons resultEntry resultRest =>
                                                                                                    cases resultRest with
                                                                                                    | cons another rest =>
                                                                                                        simp [resultMatchesFound]
                                                                                                    | nil =>
                                                                                                        simp only [resultMatchesFound,
                                                                                                          List.map_cons,
                                                                                                          List.map_nil,
                                                                                                          Option.bind_some]

                                                                                                        cases baseMatchesFound :
                                                                                                            (matchingSlots recheck
                                                                                                              baseProp).filter
                                                                                                                (fun entry =>
                                                                                                                  (lookupSurfaceSubst
                                                                                                                    entry.2
                                                                                                                    recheckBaselineParam).isSome) with
                                                                                                        | nil =>
                                                                                                            simp [baseMatchesFound]
                                                                                                        | cons baseEntry baseRest =>
                                                                                                            cases baseRest with
                                                                                                            | cons another rest =>
                                                                                                                simp [baseMatchesFound]
                                                                                                            | nil =>
                                                                                                                simp only [baseMatchesFound,
                                                                                                                  List.map_cons,
                                                                                                                  List.map_nil,
                                                                                                                  Option.bind_some]
                                                                                                                have resultFilteredMember :
                                                                                                                    resultEntry ∈
                                                                                                                      (matchingSlots recheck
                                                                                                                        resultProp).filter
                                                                                                                        (fun entry =>
                                                                                                                          (lookupSurfaceSubst
                                                                                                                            entry.2
                                                                                                                            recheckResultParam).isSome) := by
                                                                                                                  rw [resultMatchesFound]
                                                                                                                  simp
                                                                                                                have resultEntryMember :
                                                                                                                    resultEntry ∈
                                                                                                                      matchingSlots recheck
                                                                                                                        resultProp :=
                                                                                                                  (List.mem_filter.mp
                                                                                                                    resultFilteredMember).1
                                                                                                                have baseFilteredMember :
                                                                                                                    baseEntry ∈
                                                                                                                      (matchingSlots recheck
                                                                                                                        baseProp).filter
                                                                                                                        (fun entry =>
                                                                                                                          (lookupSurfaceSubst
                                                                                                                            entry.2
                                                                                                                            recheckBaselineParam).isSome) := by
                                                                                                                  rw [baseMatchesFound]
                                                                                                                  simp
                                                                                                                have baseEntryMember :
                                                                                                                    baseEntry ∈
                                                                                                                      matchingSlots recheck
                                                                                                                        baseProp :=
                                                                                                                  (List.mem_filter.mp
                                                                                                                    baseFilteredMember).1
                                                                                                                have resultSubstFixed :=
                                                                                                                  substFixed_of_matchingSlots_member
                                                                                                                    patternsFixed
                                                                                                                    resultPropFixed
                                                                                                                    resultEntryMember
                                                                                                                have baseSubstFixed :=
                                                                                                                  substFixed_of_matchingSlots_member
                                                                                                                    patternsFixed
                                                                                                                    basePropFixed
                                                                                                                    baseEntryMember
                                                                                                                by_cases sameSlot :
                                                                                                                    resultEntry.1 =
                                                                                                                      baseEntry.1
                                                                                                                · simp [sameSlot]
                                                                                                                · simp only [sameSlot,
                                                                                                                    if_false,
                                                                                                                    Option.bind_some]
                                                                                                                  rw [roleParams_rename
                                                                                                                    ρg
                                                                                                                    (programValues program)
                                                                                                                    resultEntry.2
                                                                                                                    baseEntry.2
                                                                                                                    systemTerm
                                                                                                                    resultSubstFixed
                                                                                                                    baseSubstFixed
                                                                                                                    systemFixed]
                                                                                                                  rw [roleParams_rename
                                                                                                                    ρg
                                                                                                                    (programValues program)
                                                                                                                    resultEntry.2
                                                                                                                    baseEntry.2
                                                                                                                    baselineTerm
                                                                                                                    resultSubstFixed
                                                                                                                    baseSubstFixed
                                                                                                                    baselineFixed]
                                                                                                                  rw [Binding.rename_measurand_val,
                                                                                                                    Binding.rename_dataset_val]
                                                                                                                  have measurandRolesRename :=
                                                                                                                    roleParams_renameSpelling
                                                                                                                      ρg
                                                                                                                      (programValues program)
                                                                                                                      resultEntry.2
                                                                                                                      baseEntry.2
                                                                                                                      comparison.measurand.val
                                                                                                                      resultSubstFixed
                                                                                                                      baseSubstFixed
                                                                                                                  simp only [renameText] at measurandRolesRename
                                                                                                                  rw [measurandRolesRename]
                                                                                                                  have datasetRolesRename :=
                                                                                                                    roleParams_renameSpelling
                                                                                                                      ρg
                                                                                                                      (programValues program)
                                                                                                                      resultEntry.2
                                                                                                                      baseEntry.2
                                                                                                                      comparison.dataset.val
                                                                                                                      resultSubstFixed
                                                                                                                      baseSubstFixed
                                                                                                                  simp only [renameText] at datasetRolesRename
                                                                                                                  rw [datasetRolesRename]
                                                                                                                  cases rolesEmpty :
                                                                                                                      ((roleParams
                                                                                                                            resultEntry.2
                                                                                                                            baseEntry.2
                                                                                                                            systemTerm).isEmpty ||
                                                                                                                        (roleParams
                                                                                                                            resultEntry.2
                                                                                                                            baseEntry.2
                                                                                                                            baselineTerm).isEmpty ||
                                                                                                                        (roleParams
                                                                                                                            resultEntry.2
                                                                                                                            baseEntry.2
                                                                                                                            (.con
                                                                                                                              comparison.measurand.val
                                                                                                                              .nil)).isEmpty ||
                                                                                                                        (roleParams
                                                                                                                            resultEntry.2
                                                                                                                            baseEntry.2
                                                                                                                            (.con
                                                                                                                              comparison.dataset.val
                                                                                                                              .nil)).isEmpty)
                                                                                                                  · simp only [rolesEmpty,
                                                                                                                      Bool.false_eq_true,
                                                                                                                      if_false,
                                                                                                                      Option.bind_some]
                                                                                                                    have measurandRolesNonempty :
                                                                                                                        (roleParams
                                                                                                                            resultEntry.2
                                                                                                                            baseEntry.2
                                                                                                                            (.con
                                                                                                                              comparison.measurand.val
                                                                                                                              .nil)).isEmpty =
                                                                                                                          false := by
                                                                                                                      cases empty :
                                                                                                                          (roleParams
                                                                                                                              resultEntry.2
                                                                                                                              baseEntry.2
                                                                                                                              (.con
                                                                                                                                comparison.measurand.val
                                                                                                                                .nil)).isEmpty
                                                                                                                      · rfl
                                                                                                                      · simp [empty] at rolesEmpty
                                                                                                                    have datasetRolesNonempty :
                                                                                                                        (roleParams
                                                                                                                            resultEntry.2
                                                                                                                            baseEntry.2
                                                                                                                            (.con
                                                                                                                              comparison.dataset.val
                                                                                                                              .nil)).isEmpty =
                                                                                                                          false := by
                                                                                                                      cases empty :
                                                                                                                          (roleParams
                                                                                                                              resultEntry.2
                                                                                                                              baseEntry.2
                                                                                                                              (.con
                                                                                                                                comparison.dataset.val
                                                                                                                                .nil)).isEmpty
                                                                                                                      · rfl
                                                                                                                      · simp [empty] at rolesEmpty
                                                                                                                    have measurandTermFixed :=
                                                                                                                      nullaryTermFixed_of_roleParams_nonempty
                                                                                                                        resultSubstFixed
                                                                                                                        baseSubstFixed
                                                                                                                        measurandRolesNonempty
                                                                                                                    have datasetTermFixed :=
                                                                                                                      nullaryTermFixed_of_roleParams_nonempty
                                                                                                                        resultSubstFixed
                                                                                                                        baseSubstFixed
                                                                                                                        datasetRolesNonempty
                                                                                                                    have measurandTermRename :=
                                                                                                                      renameValueTerm_nullary_eq_renameText_of_fixed
                                                                                                                        measurandTermFixed
                                                                                                                    have datasetTermRename :=
                                                                                                                      renameValueTerm_nullary_eq_renameText_of_fixed
                                                                                                                        datasetTermFixed
                                                                                                                    simp only [renameText] at measurandTermRename
                                                                                                                    simp only [renameText] at datasetTermRename
                                                                                                                    rw [← measurandTermRename,
                                                                                                                      ← datasetTermRename]
                                                                                                                    rw [← roleSeed_rename
                                                                                                                      ρg
                                                                                                                      (programValues program)
                                                                                                                      (roleParams
                                                                                                                        resultEntry.2
                                                                                                                        baseEntry.2
                                                                                                                        systemTerm)
                                                                                                                      systemTerm]
                                                                                                                    rw [← roleSeed_rename
                                                                                                                      ρg
                                                                                                                      (programValues program)
                                                                                                                      (roleParams
                                                                                                                        resultEntry.2
                                                                                                                        baseEntry.2
                                                                                                                        baselineTerm)
                                                                                                                      baselineTerm]
                                                                                                                    rw [← roleSeed_rename
                                                                                                                      ρg
                                                                                                                      (programValues program)
                                                                                                                      (roleParams
                                                                                                                        resultEntry.2
                                                                                                                        baseEntry.2
                                                                                                                        (.con
                                                                                                                          comparison.measurand.val
                                                                                                                          .nil))
                                                                                                                      (.con
                                                                                                                        comparison.measurand.val
                                                                                                                        .nil)]
                                                                                                                    rw [← roleSeed_rename
                                                                                                                      ρg
                                                                                                                      (programValues program)
                                                                                                                      (roleParams
                                                                                                                        resultEntry.2
                                                                                                                        baseEntry.2
                                                                                                                        (.con
                                                                                                                          comparison.dataset.val
                                                                                                                          .nil))
                                                                                                                      (.con
                                                                                                                        comparison.dataset.val
                                                                                                                        .nil)]
                                                                                                                    have thetaSeedMap :
                                                                                                                        Binding.renameSubstValues
                                                                                                                            ρg
                                                                                                                            (programValues program)
                                                                                                                            (roleSeed
                                                                                                                              (roleParams
                                                                                                                                resultEntry.2
                                                                                                                                baseEntry.2
                                                                                                                                systemTerm)
                                                                                                                              systemTerm) ++
                                                                                                                          Binding.renameSubstValues
                                                                                                                            ρg
                                                                                                                            (programValues program)
                                                                                                                            (roleSeed
                                                                                                                              (roleParams
                                                                                                                                resultEntry.2
                                                                                                                                baseEntry.2
                                                                                                                                baselineTerm)
                                                                                                                              baselineTerm) ++
                                                                                                                          Binding.renameSubstValues
                                                                                                                            ρg
                                                                                                                            (programValues program)
                                                                                                                            (roleSeed
                                                                                                                              (roleParams
                                                                                                                                resultEntry.2
                                                                                                                                baseEntry.2
                                                                                                                                (.con
                                                                                                                                  comparison.measurand.val
                                                                                                                                  .nil))
                                                                                                                              (.con
                                                                                                                                comparison.measurand.val
                                                                                                                                .nil)) ++
                                                                                                                          Binding.renameSubstValues
                                                                                                                            ρg
                                                                                                                            (programValues program)
                                                                                                                            (roleSeed
                                                                                                                              (roleParams
                                                                                                                                resultEntry.2
                                                                                                                                baseEntry.2
                                                                                                                                (.con
                                                                                                                                  comparison.dataset.val
                                                                                                                                  .nil))
                                                                                                                              (.con
                                                                                                                                comparison.dataset.val
                                                                                                                                .nil)) =
                                                                                                                          Binding.renameSubstValues
                                                                                                                            ρg
                                                                                                                            (programValues program)
                                                                                                                            (roleSeed
                                                                                                                                (roleParams
                                                                                                                                  resultEntry.2
                                                                                                                                  baseEntry.2
                                                                                                                                  systemTerm)
                                                                                                                                systemTerm ++
                                                                                                                              roleSeed
                                                                                                                                (roleParams
                                                                                                                                  resultEntry.2
                                                                                                                                  baseEntry.2
                                                                                                                                  baselineTerm)
                                                                                                                                baselineTerm ++
                                                                                                                              roleSeed
                                                                                                                                (roleParams
                                                                                                                                  resultEntry.2
                                                                                                                                  baseEntry.2
                                                                                                                                  (.con
                                                                                                                                    comparison.measurand.val
                                                                                                                                    .nil))
                                                                                                                                (.con
                                                                                                                                  comparison.measurand.val
                                                                                                                                  .nil) ++
                                                                                                                              roleSeed
                                                                                                                                (roleParams
                                                                                                                                  resultEntry.2
                                                                                                                                  baseEntry.2
                                                                                                                                  (.con
                                                                                                                                    comparison.dataset.val
                                                                                                                                    .nil))
                                                                                                                                (.con
                                                                                                                                  comparison.dataset.val
                                                                                                                                  .nil)) := by
                                                                                                                      simp [Binding.renameSubstValues,
                                                                                                                        List.map_append]
                                                                                                                    rw [thetaSeedMap]
                                                                                                                    cases resultPatternFound :
                                                                                                                        recheck.premises[resultEntry.1]? with
                                                                                                                    | none =>
                                                                                                                        simp [resultPatternFound]
                                                                                                                    | some resultPattern =>
                                                                                                                        simp only [resultPatternFound,
                                                                                                                          Option.bind_some]
                                                                                                                        cases basePatternFound :
                                                                                                                            recheck.premises[baseEntry.1]? with
                                                                                                                        | none =>
                                                                                                                            simp [basePatternFound]
                                                                                                                        | some basePattern =>
                                                                                                                            simp only [basePatternFound,
                                                                                                                              Option.bind_some]
                                                                                                                            have resultPatternFixed :=
                                                                                                                              patternsFixed
                                                                                                                                resultPattern
                                                                                                                                (List.mem_of_getElem?
                                                                                                                                  resultPatternFound)
                                                                                                                            have basePatternFixed :=
                                                                                                                              patternsFixed
                                                                                                                                basePattern
                                                                                                                                (List.mem_of_getElem?
                                                                                                                                  basePatternFound)
                                                                                                                            have thetaSeedFixed :
                                                                                                                                SubstFixed
                                                                                                                                  ρg
                                                                                                                                  (programValues program)
                                                                                                                                  (roleSeed
                                                                                                                                      (roleParams
                                                                                                                                        resultEntry.2
                                                                                                                                        baseEntry.2
                                                                                                                                        systemTerm)
                                                                                                                                      systemTerm ++
                                                                                                                                    roleSeed
                                                                                                                                      (roleParams
                                                                                                                                        resultEntry.2
                                                                                                                                        baseEntry.2
                                                                                                                                        baselineTerm)
                                                                                                                                      baselineTerm ++
                                                                                                                                    roleSeed
                                                                                                                                      (roleParams
                                                                                                                                        resultEntry.2
                                                                                                                                        baseEntry.2
                                                                                                                                        (.con
                                                                                                                                          comparison.measurand.val
                                                                                                                                          .nil))
                                                                                                                                      (.con
                                                                                                                                        comparison.measurand.val
                                                                                                                                        .nil) ++
                                                                                                                                    roleSeed
                                                                                                                                      (roleParams
                                                                                                                                        resultEntry.2
                                                                                                                                        baseEntry.2
                                                                                                                                        (.con
                                                                                                                                          comparison.dataset.val
                                                                                                                                          .nil))
                                                                                                                                      (.con
                                                                                                                                        comparison.dataset.val
                                                                                                                                        .nil)) := by
                                                                                                                              exact substFixed_append
                                                                                                                                (substFixed_append
                                                                                                                                  (substFixed_append
                                                                                                                                    (substFixed_roleSeed
                                                                                                                                      systemFixed)
                                                                                                                                    (substFixed_roleSeed
                                                                                                                                      baselineFixed))
                                                                                                                                  (substFixed_roleSeed
                                                                                                                                    measurandTermFixed))
                                                                                                                                (substFixed_roleSeed
                                                                                                                                  datasetTermFixed)
                                                                                                                            let thetaSeed : SurfaceSubst :=
                                                                                                                              roleSeed
                                                                                                                                  (roleParams
                                                                                                                                    resultEntry.2
                                                                                                                                    baseEntry.2
                                                                                                                                    systemTerm)
                                                                                                                                  systemTerm ++
                                                                                                                                roleSeed
                                                                                                                                  (roleParams
                                                                                                                                    resultEntry.2
                                                                                                                                    baseEntry.2
                                                                                                                                    baselineTerm)
                                                                                                                                  baselineTerm ++
                                                                                                                                roleSeed
                                                                                                                                  (roleParams
                                                                                                                                    resultEntry.2
                                                                                                                                    baseEntry.2
                                                                                                                                    (.con
                                                                                                                                      comparison.measurand.val
                                                                                                                                      .nil))
                                                                                                                                  (.con
                                                                                                                                    comparison.measurand.val
                                                                                                                                    .nil) ++
                                                                                                                                roleSeed
                                                                                                                                  (roleParams
                                                                                                                                    resultEntry.2
                                                                                                                                    baseEntry.2
                                                                                                                                    (.con
                                                                                                                                      comparison.dataset.val
                                                                                                                                      .nil))
                                                                                                                                  (.con
                                                                                                                                    comparison.dataset.val
                                                                                                                                    .nil)
                                                                                                                            have thetaSeedFixed' :
                                                                                                                                SubstFixed
                                                                                                                                  ρg
                                                                                                                                  (programValues program)
                                                                                                                                  thetaSeed := by
                                                                                                                              simpa [thetaSeed] using thetaSeedFixed
                                                                                                                            rw [orderedComparisonMatch_bind]
                                                                                                                            rw [orderedComparisonMatch_bind]
                                                                                                                            rw [orderedComparisonMatch_rename
                                                                                                                              thetaSeedFixed'
                                                                                                                              basePatternFixed
                                                                                                                              resultPatternFixed
                                                                                                                              basePropFixed
                                                                                                                              resultPropFixed]
                                                                                                                            cases mergedFound :
                                                                                                                                orderedComparisonMatch
                                                                                                                                  baseEntry.1
                                                                                                                                  resultEntry.1
                                                                                                                                  thetaSeed
                                                                                                                                  basePattern
                                                                                                                                  resultPattern
                                                                                                                                  baseProp
                                                                                                                                  resultProp with
                                                                                                                            | none =>
                                                                                                                                simp [mergedFound]
                                                                                                                            | some merged =>
                                                                                                                                simp only [mergedFound,
                                                                                                                                  Option.map_some,
                                                                                                                                  Option.bind_some]
                                                                                                                                have mergedFixed :=
                                                                                                                                  substFixed_of_orderedComparisonMatch
                                                                                                                                    thetaSeedFixed'
                                                                                                                                    basePatternFixed
                                                                                                                                    resultPatternFixed
                                                                                                                                    basePropFixed
                                                                                                                                    resultPropFixed
                                                                                                                                    mergedFound
                                                                                                                                rw [paramsCoveredB_rename]
                                                                                                                                cases covered :
                                                                                                                                    paramsCoveredB
                                                                                                                                      recheck.params
                                                                                                                                      merged with
                                                                                                                                | false =>
                                                                                                                                    simp [covered]
                                                                                                                                | true =>
                                                                                                                                    simp only [covered,
                                                                                                                                      Bool.not_true,
                                                                                                                                      Bool.false_eq_true,
                                                                                                                                      if_false,
                                                                                                                                      Option.bind_some]
                                                                                                                                    have conclusionPatternFixed :
                                                                                                                                        AtomPatFixed
                                                                                                                                          ρg
                                                                                                                                          recheck.conclusion := by
                                                                                                                                      apply atomPatFixed_of_rule
                                                                                                                                        sound
                                                                                                                                        recheck
                                                                                                                                        recheckMember
                                                                                                                                        recheck.conclusion
                                                                                                                                      intro spelling
                                                                                                                                        spellingMember
                                                                                                                                      apply List.mem_append.mpr
                                                                                                                                      exact Or.inl
                                                                                                                                        (List.mem_append.mpr
                                                                                                                                          (Or.inr
                                                                                                                                            spellingMember))
                                                                                                                                    rw [instantiateSurfaceAtom_rename
                                                                                                                                      conclusionPatternFixed]
                                                                                                                                    cases goalFound :
                                                                                                                                        instantiateSurfaceAtom
                                                                                                                                          merged
                                                                                                                                          recheck.conclusion with
                                                                                                                                    | none =>
                                                                                                                                        simp [goalFound]
                                                                                                                                    | some goal =>
                                                                                                                                        simp only [goalFound,
                                                                                                                                          Option.map_some,
                                                                                                                                          Option.bind_some]
                                                                                                                                        have goalFixed :
                                                                                                                                            AtomFixed
                                                                                                                                              ρg
                                                                                                                                              (programValues program)
                                                                                                                                              goal :=
                                                                                                                                          atomFixed_of_instantiateSurfaceAtom
                                                                                                                                            mergedFixed
                                                                                                                                            conclusionPatternFixed
                                                                                                                                            goalFound
                                                                                                                                        have goalLeftFixed :
                                                                                                                                            PatFixed ρg goalLeft := by
                                                                                                                                          intro spelling
                                                                                                                                            spellingMember
                                                                                                                                          apply conclusionPatternFixed
                                                                                                                                            spelling
                                                                                                                                          exact
                                                                                                                                            patNullaryCons_sub_pats
                                                                                                                                              goalLeft
                                                                                                                                              recheck.conclusion.args
                                                                                                                                              (by
                                                                                                                                                rw [goalShape]
                                                                                                                                                simp)
                                                                                                                                              spellingMember
                                                                                                                                        have goalRightFixed :
                                                                                                                                            PatFixed ρg goalRight := by
                                                                                                                                          intro spelling
                                                                                                                                            spellingMember
                                                                                                                                          apply conclusionPatternFixed
                                                                                                                                            spelling
                                                                                                                                          exact
                                                                                                                                            patNullaryCons_sub_pats
                                                                                                                                              goalRight
                                                                                                                                              recheck.conclusion.args
                                                                                                                                              (by
                                                                                                                                                rw [goalShape]
                                                                                                                                                simp)
                                                                                                                                              spellingMember
                                                                                                                                        rw [comparisonOperandSlot?_rename
                                                                                                                                          ρg
                                                                                                                                          (programValues program)
                                                                                                                                          merged
                                                                                                                                          baseEntry.2
                                                                                                                                          resultEntry.2
                                                                                                                                          baseEntry.1
                                                                                                                                          resultEntry.1
                                                                                                                                          baseCell
                                                                                                                                          resultCell
                                                                                                                                          goalLeft
                                                                                                                                          goalLeftFixed]
                                                                                                                                        cases slotLeftFound :
                                                                                                                                            comparisonOperandSlot?
                                                                                                                                              merged
                                                                                                                                              baseEntry.2
                                                                                                                                              resultEntry.2
                                                                                                                                              baseEntry.1
                                                                                                                                              resultEntry.1
                                                                                                                                              baseCell
                                                                                                                                              resultCell
                                                                                                                                              goalLeft with
                                                                                                                                        | none =>
                                                                                                                                            simp [slotLeftFound]
                                                                                                                                        | some slotLeft =>
                                                                                                                                            simp only [slotLeftFound,
                                                                                                                                              Option.bind_some]
                                                                                                                                            rw [comparisonOperandSlot?_rename
                                                                                                                                              ρg
                                                                                                                                              (programValues program)
                                                                                                                                              merged
                                                                                                                                              baseEntry.2
                                                                                                                                              resultEntry.2
                                                                                                                                              baseEntry.1
                                                                                                                                              resultEntry.1
                                                                                                                                              baseCell
                                                                                                                                              resultCell
                                                                                                                                              goalRight
                                                                                                                                              goalRightFixed]
                                                                                                                                            cases slotRightFound :
                                                                                                                                                comparisonOperandSlot?
                                                                                                                                                  merged
                                                                                                                                                  baseEntry.2
                                                                                                                                                  resultEntry.2
                                                                                                                                                  baseEntry.1
                                                                                                                                                  resultEntry.1
                                                                                                                                                  baseCell
                                                                                                                                                  resultCell
                                                                                                                                                  goalRight with
                                                                                                                                            | none =>
                                                                                                                                                simp [slotRightFound]
                                                                                                                                            | some slotRight =>
                                                                                                                                                simp only [slotRightFound,
                                                                                                                                                  Option.bind_some]
                                                                                                                                                by_cases slotsCorrect :
                                                                                                                                                    (slotLeft, slotRight) =
                                                                                                                                                      comparisonExpectedSlots
                                                                                                                                                        polarity
                                                                                                                                                        baseEntry.1
                                                                                                                                                        resultEntry.1
                                                                                                                                                · simp [comparisonExpectedSlots,
                                                                                                                                                    slotsCorrect]
                                                                                                                                                  have bindingPropFixed :=
                                                                                                                                                    atomFixed_of_leafProp
                                                                                                                                                      sound
                                                                                                                                                      comparison.binding
                                                                                                                                                      bindingProp
                                                                                                                                                      bindingFound
                                                                                                                                                  have bridgeSeedFixed :
                                                                                                                                                      SubstFixed
                                                                                                                                                        ρg
                                                                                                                                                        (programValues program)
                                                                                                                                                        [(parts.systemParam,
                                                                                                                                                            systemTerm),
                                                                                                                                                          (parts.baselineParam,
                                                                                                                                                            baselineTerm),
                                                                                                                                                          (parts.measurandParam,
                                                                                                                                                            (.con
                                                                                                                                                              comparison.measurand.val
                                                                                                                                                              .nil)),
                                                                                                                                                          (parts.datasetParam,
                                                                                                                                                            (.con
                                                                                                                                                              comparison.dataset.val
                                                                                                                                                              .nil))] := by
                                                                                                                                                    intro entry entryMember
                                                                                                                                                    simp only [List.mem_cons,
                                                                                                                                                      List.not_mem_nil,
                                                                                                                                                      or_false] at entryMember
                                                                                                                                                    rcases entryMember with
                                                                                                                                                      rfl | rfl | rfl | rfl
                                                                                                                                                    · exact systemFixed
                                                                                                                                                    · exact baselineFixed
                                                                                                                                                    · exact measurandTermFixed
                                                                                                                                                    · exact datasetTermFixed
                                                                                                                                                  have bridgeMember :
                                                                                                                                                      bridge ∈ policy.rules := by
                                                                                                                                                    unfold ruleById at bridgeFound
                                                                                                                                                    exact
                                                                                                                                                      List.mem_of_find?_eq_some
                                                                                                                                                        bridgeFound
                                                                                                                                                  have bridgePatternsFixed :
                                                                                                                                                      ∀ pattern ∈ bridge.premises,
                                                                                                                                                        AtomPatFixed ρg pattern := by
                                                                                                                                                    intro pattern patternMember
                                                                                                                                                    apply atomPatFixed_of_rule
                                                                                                                                                      sound
                                                                                                                                                      bridge
                                                                                                                                                      bridgeMember
                                                                                                                                                      pattern
                                                                                                                                                    intro spelling spellingMember
                                                                                                                                                    apply List.mem_append.mpr
                                                                                                                                                    exact Or.inl
                                                                                                                                                      (List.mem_append.mpr
                                                                                                                                                        (Or.inl
                                                                                                                                                          (List.mem_flatMap.mpr
                                                                                                                                                            ⟨pattern,
                                                                                                                                                              patternMember,
                                                                                                                                                              spellingMember⟩)))
                                                                                                                                                  have bridgePatternMembers :=
                                                                                                                                                    bridgeParts_patterns_mem
                                                                                                                                                      partsFound
                                                                                                                                                  have bindingPatternFixed :=
                                                                                                                                                    bridgePatternsFixed
                                                                                                                                                      parts.bindingPattern
                                                                                                                                                      bridgePatternMembers.1
                                                                                                                                                  have comparisonPatternFixed :=
                                                                                                                                                    bridgePatternsFixed
                                                                                                                                                      parts.comparisonPattern
                                                                                                                                                      bridgePatternMembers.2
                                                                                                                                                  have bridgeSeedRename :
                                                                                                                                                      Binding.renameSubstValues
                                                                                                                                                          ρg
                                                                                                                                                          (programValues program)
                                                                                                                                                          [(parts.systemParam,
                                                                                                                                                              systemTerm),
                                                                                                                                                            (parts.baselineParam,
                                                                                                                                                              baselineTerm),
                                                                                                                                                            (parts.measurandParam,
                                                                                                                                                              (.con
                                                                                                                                                                comparison.measurand.val
                                                                                                                                                                .nil)),
                                                                                                                                                            (parts.datasetParam,
                                                                                                                                                              (.con
                                                                                                                                                                comparison.dataset.val
                                                                                                                                                                .nil))] =
                                                                                                                                                        [(parts.systemParam,
                                                                                                                                                            Binding.renameValueTerm
                                                                                                                                                              ρg
                                                                                                                                                              (programValues program)
                                                                                                                                                              systemTerm),
                                                                                                                                                          (parts.baselineParam,
                                                                                                                                                            Binding.renameValueTerm
                                                                                                                                                              ρg
                                                                                                                                                              (programValues program)
                                                                                                                                                              baselineTerm),
                                                                                                                                                          (parts.measurandParam,
                                                                                                                                                            Binding.renameValueTerm
                                                                                                                                                              ρg
                                                                                                                                                              (programValues program)
                                                                                                                                                              (.con
                                                                                                                                                                comparison.measurand.val
                                                                                                                                                                .nil)),
                                                                                                                                                          (parts.datasetParam,
                                                                                                                                                            Binding.renameValueTerm
                                                                                                                                                              ρg
                                                                                                                                                              (programValues program)
                                                                                                                                                              (.con
                                                                                                                                                                comparison.dataset.val
                                                                                                                                                                .nil))] := by
                                                                                                                                                    rfl
                                                                                                                                                  rw [← bridgeSeedRename]
                                                                                                                                                  rw [matchSurfaceAtom_rename
                                                                                                                                                    bridgeSeedFixed
                                                                                                                                                    bindingPatternFixed
                                                                                                                                                    bindingPropFixed]
                                                                                                                                                  cases bindingSubstFound :
                                                                                                                                                      matchSurfaceAtom
                                                                                                                                                        [(parts.systemParam,
                                                                                                                                                            systemTerm),
                                                                                                                                                          (parts.baselineParam,
                                                                                                                                                            baselineTerm),
                                                                                                                                                          (parts.measurandParam,
                                                                                                                                                            (.con
                                                                                                                                                              comparison.measurand.val
                                                                                                                                                              .nil)),
                                                                                                                                                          (parts.datasetParam,
                                                                                                                                                            (.con
                                                                                                                                                              comparison.dataset.val
                                                                                                                                                              .nil))]
                                                                                                                                                        parts.bindingPattern
                                                                                                                                                        bindingProp with
                                                                                                                                                  | none =>
                                                                                                                                                      simp [bindingSubstFound]
                                                                                                                                                  | some bindingSubst =>
                                                                                                                                                      simp only [bindingSubstFound,
                                                                                                                                                        Option.map_some,
                                                                                                                                                        Option.bind_some]
                                                                                                                                                      have bindingSubstFixed :=
                                                                                                                                                        substFixed_of_matchSurfaceAtom
                                                                                                                                                          bridgeSeedFixed
                                                                                                                                                          bindingPatternFixed
                                                                                                                                                          bindingPropFixed
                                                                                                                                                          bindingSubstFound
                                                                                                                                                      rw [matchSurfaceAtom_rename
                                                                                                                                                        bindingSubstFixed
                                                                                                                                                        comparisonPatternFixed
                                                                                                                                                        goalFixed]
                                                                                                                                                      cases bridgeSubstFound :
                                                                                                                                                          matchSurfaceAtom
                                                                                                                                                            bindingSubst
                                                                                                                                                            parts.comparisonPattern
                                                                                                                                                            goal with
                                                                                                                                                      | none =>
                                                                                                                                                          simp [bridgeSubstFound]
                                                                                                                                                      | some bridgeSubst =>
                                                                                                                                                          simp only [bridgeSubstFound,
                                                                                                                                                            Option.map_some,
                                                                                                                                                            Option.bind_some]
                                                                                                                                                          rw [paramsCoveredB_rename]
                                                                                                                                                          cases bridgeCovered :
                                                                                                                                                              paramsCoveredB
                                                                                                                                                                bridge.params
                                                                                                                                                                bridgeSubst with
                                                                                                                                                          | false =>
                                                                                                                                                              simp [bridgeSubstFound,
                                                                                                                                                                bridgeCovered]
                                                                                                                                                          | true =>
                                                                                                                                                              simp [bridgeSubstFound,
                                                                                                                                                                bridgeCovered,
                                                                                                                                                                renameComparisonExpansionData,
                                                                                                                                                                Binding.renameRule]
                                                                                                                                                · rw [← comparisonExpectedSlots_eq]
                                                                                                                                                  simp [slotsCorrect]
                                                                                                                  · simp [rolesEmpty]

private theorem comparisonGoal?_rename
    (sound : RenamingSound ρg program policy)
    (comparison : Presentation.Comparison)
    (member : Presentation.Decl.comparison comparison ∈ program.decls) :
    comparisonGoal?
        (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (Binding.renameComparison ρg (programValues program) comparison) =
      (comparisonGoal? program policy comparison).map
        (Binding.renameValueAtom ρg (programValues program)) := by
  unfold comparisonGoal?
  rw [comparisonExpansion?_rename sound.toComparison comparison member]
  cases comparisonExpansion? program policy comparison <;> rfl

private def renameComparisonKey (ρg : Binding.GlobalRenaming)
    (key : Presentation.LeafId × Presentation.LeafId ×
      Presentation.MeasurandId × Presentation.DatasetId ×
      Presentation.Relation) :=
  let (result, baseline, measurand, dataset, relation) := key
  (ρg.leaf result, ρg.leaf baseline, ρg.measurand measurand,
    ρg.dataset dataset, relation)

private theorem renameComparisonKey_injective
    (ρg : Binding.GlobalRenaming) :
    Function.Injective (renameComparisonKey ρg) := by
  rintro ⟨result₁, baseline₁, measurand₁, dataset₁, relation₁⟩
    ⟨result₂, baseline₂, measurand₂, dataset₂, relation₂⟩ equal
  simp only [renameComparisonKey, Prod.mk.injEq] at equal ⊢
  exact
    ⟨ρg.leaf_injective equal.1,
      ρg.leaf_injective equal.2.1,
      ρg.measurand_injective equal.2.2.1,
      ρg.dataset_injective equal.2.2.2.1,
      equal.2.2.2.2⟩

private theorem comparisonKeys_rename
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program) :
    comparisonKeys (Binding.renameProgram ρg program) =
      (comparisonKeys program).map (renameComparisonKey ρg) := by
  simp [comparisonKeys, comparisonKey, renameComparisonKey,
    Binding.renameComparison, List.map_map, Function.comp_def]

private theorem claim_mem_rename_iff
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program)
    (claim : Presentation.PropId) :
    ρg.prop claim ∈ claimIds (Binding.renameProgram ρg program) ↔
      claim ∈ claimIds program := by
  rw [claimIds_renameProgram]
  constructor
  · intro member
    obtain ⟨candidate, candidateMember, renamedEq⟩ :=
      List.mem_map.mp member
    have candidateEq : candidate = claim :=
      ρg.prop_injective renamedEq
    simpa [candidateEq] using candidateMember
  · intro member
    exact List.mem_map.mpr ⟨claim, member, rfl⟩
private theorem comparisonDecls_member
    (comparison : Presentation.Comparison)
    (member : comparison ∈ comparisonDecls program) :
    Presentation.Decl.comparison comparison ∈ program.decls := by
  unfold comparisonDecls at member
  simp only [List.mem_filterMap] at member
  obtain ⟨declaration, declarationMember, selected⟩ := member
  cases declaration <;> simp_all


private theorem comparisonCoreValid_rename
    (sound : RenamingSound ρg program policy)
    (comparison : Presentation.Comparison)
    (member : Presentation.Decl.comparison comparison ∈ program.decls) :
    comparisonCoreValid
        (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (Binding.renameComparison ρg (programValues program) comparison) ↔
      comparisonCoreValid program policy comparison := by
  unfold comparisonCoreValid
  rw [comparisonGoal?_rename sound comparison member]
  cases goalFound : comparisonGoal? program policy comparison with
  | none =>
      simp [goalFound, Binding.renameComparison]
  | some goal =>
      cases supportsFound : comparison.supports with
      | none =>
          simp [goalFound, supportsFound, Binding.renameComparison]
      | some claim =>
          simpa [Binding.renameComparison, supportsFound] using
            (claim_mem_rename_iff ρg program claim)

theorem comparisonsWellFormedB_rename
    (sound : RenamingSound ρg program policy) :
    comparisonsWellFormedB (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy) =
      comparisonsWellFormedB program policy := by
  apply Bool.eq_iff_iff.mpr
  rw [comparisonsWellFormedB_iff, comparisonsWellFormedB_iff]
  constructor
  · intro renamedWellFormed
    constructor
    · have renamedKeys := renamedWellFormed.1
      rw [comparisonKeys_rename,
        nodup_map_iff_of_injective (renameComparisonKey_injective ρg)]
        at renamedKeys
      exact renamedKeys
    · intro comparison comparisonMember
      apply (comparisonCoreValid_rename sound comparison
        (comparisonDecls_member comparison comparisonMember)).mp
      apply renamedWellFormed.2
      simp only [comparisonDecls_renameProgram, List.mem_map]
      exact ⟨comparison, comparisonMember, rfl⟩
  · intro wellFormed
    constructor
    · rw [comparisonKeys_rename,
        nodup_map_iff_of_injective (renameComparisonKey_injective ρg)]
      exact wellFormed.1
    · intro renamedComparison renamedMember
      simp only [comparisonDecls_renameProgram, List.mem_map] at renamedMember
      obtain ⟨comparison, comparisonMember, comparisonEq⟩ := renamedMember
      subst renamedComparison
      exact (comparisonCoreValid_rename sound comparison
        (comparisonDecls_member comparison comparisonMember)).mpr
        (wellFormed.2 comparison comparisonMember)


/-! #### Inferred-argument transport -/

mutual
  /-- Rename every nullary constructor carried by inference state.  Unlike the
  authored-term renamer, this also covers constructor names synthesized from
  measurand and dataset identifiers. -/
  def renameResidualTerm (ρg : Binding.GlobalRenaming) : Term → Term
    | .num source => .num source
    | .str source => .str source
    | .con name .nil => .con (Binding.renameText ρg name) .nil
    | .con name (.cons term rest) =>
        .con name (.cons (renameResidualTerm ρg term)
          (renameResidualTerms ρg rest))
  def renameResidualTerms (ρg : Binding.GlobalRenaming) : Terms → Terms
    | .nil => .nil
    | .cons term rest =>
        .cons (renameResidualTerm ρg term) (renameResidualTerms ρg rest)
end

def renameResidualAtom (ρg : Binding.GlobalRenaming) : Atom → Atom
  | .atom predicate terms =>
      .atom predicate (renameResidualTerms ρg terms)

def renameResidualSubst (ρg : Binding.GlobalRenaming)
    (subst : SurfaceSubst) : SurfaceSubst :=
  subst.map fun entry => (entry.1, renameResidualTerm ρg entry.2)

mutual
  def renameResidualSupportTerm (ρg : Binding.GlobalRenaming) :
      Presentation.SupportTerm → Presentation.SupportTerm
    | .leaf leaf => .leaf (ρg.leaf leaf)
    | .rule rule subst premises discharges holes assurance =>
        .rule (ρg.rule rule) (renameResidualSubst ρg subst)
          (renameResidualSupportTerms ρg premises)
          (renameResidualDischarges ρg discharges)
          (holes.map ρg.obligation) (Binding.renameAssurance ρg assurance)
  def renameResidualSupportTerms (ρg : Binding.GlobalRenaming) :
      Presentation.SupportTerms → Presentation.SupportTerms
    | .nil => .nil
    | .cons term rest =>
        .cons (renameResidualSupportTerm ρg term)
          (renameResidualSupportTerms ρg rest)
  def renameResidualDischarges (ρg : Binding.GlobalRenaming) :
      Presentation.Discharges → Presentation.Discharges
    | .nil => .nil
    | .cons question term rest =>
        .cons (ρg.question question) (renameResidualSupportTerm ρg term)
          (renameResidualDischarges ρg rest)
end

def renamePriorArgument (ρg : Binding.GlobalRenaming)
    (prior : PriorArgument) : PriorArgument :=
  { id := ρg.arg prior.id
    term := renameResidualSupportTerm ρg prior.term
    conclusion := renameResidualAtom ρg prior.conclusion }

def renameResolvedReference (ρg : Binding.GlobalRenaming)
    (resolved : ResolvedReference) : ResolvedReference :=
  { term := renameResidualSupportTerm ρg resolved.term
    conclusion := renameResidualAtom ρg resolved.conclusion
    leafSource := resolved.leafSource.map ρg.leaf
    argumentSource := resolved.argumentSource.map ρg.arg }

def PriorPayloadsFromProgram (program : Presentation.Program)
    (priors : List PriorArgument) : Prop :=
  ∀ prior ∈ priors,
    supportTermBinderSpellings prior.term ⊆ programBinderSpellings program ∧
    supportTermOpaqueCertPremiseSpellings prior.term ⊆
      programOpaqueCertPremiseSpellings program

@[simp] theorem priorPayloadsFromProgram_nil
    (program : Presentation.Program) :
    PriorPayloadsFromProgram program [] := by
  intro prior member
  simp at member

theorem priorPayloadsFromProgram_append_one
    (safe : PriorPayloadsFromProgram program priors)
    (prior : PriorArgument)
    (binders : supportTermBinderSpellings prior.term ⊆
      programBinderSpellings program)
    (opaquePayloads : supportTermOpaqueCertPremiseSpellings prior.term ⊆
      programOpaqueCertPremiseSpellings program) :
    PriorPayloadsFromProgram program (priors ++ [prior]) := by
  intro candidate member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact safe candidate member
  · exact ⟨binders, opaquePayloads⟩

mutual
  theorem renameResidualTerm_eq_iff
      (ρg : Binding.GlobalRenaming) {left right : Term} :
      renameResidualTerm ρg left = renameResidualTerm ρg right ↔
        left = right := by
    constructor
    · intro equal
      cases left with
      | num leftSource =>
          cases right with
          | num rightSource =>
              simpa [renameResidualTerm] using equal
          | str rightSource => simp [renameResidualTerm] at equal
          | con rightName rightTerms =>
              cases rightTerms <;> simp [renameResidualTerm] at equal
      | str leftSource =>
          cases right with
          | num rightSource => simp [renameResidualTerm] at equal
          | str rightSource =>
              simpa [renameResidualTerm] using equal
          | con rightName rightTerms =>
              cases rightTerms <;> simp [renameResidualTerm] at equal
      | con leftName leftTerms =>
          cases right with
          | num rightSource =>
              cases leftTerms <;> simp [renameResidualTerm] at equal
          | str rightSource =>
              cases leftTerms <;> simp [renameResidualTerm] at equal
          | con rightName rightTerms =>
              cases leftTerms with
              | nil =>
                  cases rightTerms with
                  | nil =>
                      have names :
                          Binding.renameText ρg leftName =
                            Binding.renameText ρg rightName :=
                        (Term.con.inj equal).1
                      have : leftName = rightName :=
                        Binding.renameText_injective ρg names
                      simp [this]
                  | cons rightTerm rightRest =>
                      simp [renameResidualTerm] at equal
              | cons leftTerm leftRest =>
                  cases rightTerms with
                  | nil => simp [renameResidualTerm] at equal
                  | cons rightTerm rightRest =>
                      have names : leftName = rightName :=
                        (Term.con.inj equal).1
                      have terms :
                          renameResidualTerms ρg (.cons leftTerm leftRest) =
                            renameResidualTerms ρg (.cons rightTerm rightRest) :=
                        (Term.con.inj equal).2
                      have originalTerms :
                          (.cons leftTerm leftRest : Terms) =
                            .cons rightTerm rightRest :=
                        (renameResidualTerms_eq_iff ρg).mp terms
                      simpa [names, originalTerms]
    · intro equal
      subst right
      rfl
  theorem renameResidualTerms_eq_iff
      (ρg : Binding.GlobalRenaming) {left right : Terms} :
      renameResidualTerms ρg left = renameResidualTerms ρg right ↔
        left = right := by
    constructor
    · intro equal
      cases left with
      | nil =>
          cases right <;> simp [renameResidualTerms] at equal ⊢
      | cons leftTerm leftRest =>
          cases right with
          | nil => simp [renameResidualTerms] at equal
          | cons rightTerm rightRest =>
              have head :
                  renameResidualTerm ρg leftTerm =
                    renameResidualTerm ρg rightTerm :=
                (Terms.cons.inj equal).1
              have tail :
                  renameResidualTerms ρg leftRest =
                    renameResidualTerms ρg rightRest :=
                (Terms.cons.inj equal).2
              have originalHead : leftTerm = rightTerm :=
                (renameResidualTerm_eq_iff ρg).mp head
              have originalTail : leftRest = rightRest :=
                (renameResidualTerms_eq_iff ρg).mp tail
              simp [originalHead, originalTail]
    · intro equal
      subst right
      rfl
end

mutual
  private theorem nfTerm_renameResidualTerm
      (ρg : Binding.GlobalRenaming) (term : Term) :
      Lara.nfTerm Lara.canonNum (renameResidualTerm ρg term) =
        renameResidualTerm ρg (Lara.nfTerm Lara.canonNum term) := by
    cases term with
    | num _ => rfl
    | str _ => rfl
    | con name terms =>
        cases terms with
        | nil => rfl
        | cons term rest =>
            simp only [renameResidualTerm, Lara.nfTerm]
            congr 1
            exact nfTerms_renameResidualTerms ρg (.cons term rest)
  private theorem nfTerms_renameResidualTerms
      (ρg : Binding.GlobalRenaming) (terms : Terms) :
      Lara.nfTerms Lara.canonNum (renameResidualTerms ρg terms) =
        renameResidualTerms ρg (Lara.nfTerms Lara.canonNum terms) := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp [renameResidualTerms, Lara.nfTerms,
          nfTerm_renameResidualTerm ρg term,
          nfTerms_renameResidualTerms ρg rest]
end

private theorem sameSurfaceTerm_renameResidual
    (ρg : Binding.GlobalRenaming) (left right : Term) :
    sameSurfaceTerm (renameResidualTerm ρg left)
        (renameResidualTerm ρg right) =
      sameSurfaceTerm left right := by
  apply Bool.eq_iff_iff.mpr
  simp only [sameSurfaceTerm, nfTerm_renameResidualTerm, beq_iff_eq]
  exact renameResidualTerm_eq_iff ρg

mutual
  private theorem renameResidualTerm_eq_self
      (term : Term)
      (fixed : ∀ spelling, spelling ∈ termNullaryCons term →
        Binding.renameText ρg spelling = spelling) :
      renameResidualTerm ρg term = term := by
    cases term with
    | num _ => rfl
    | str _ => rfl
    | con name terms =>
        cases terms with
        | nil => simp [renameResidualTerm,
            fixed name (by simp [termNullaryCons])]
        | cons term rest =>
            simp only [renameResidualTerm]
            exact congrArg (Term.con name)
              (renameResidualTerms_eq_self (.cons term rest) (by
                intro spelling member
                exact fixed spelling (by
                  simpa [termNullaryCons] using member)))
  private theorem renameResidualTerms_eq_self
      (terms : Terms)
      (fixed : ∀ spelling, spelling ∈ termsNullaryCons terms →
        Binding.renameText ρg spelling = spelling) :
      renameResidualTerms ρg terms = terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp only [renameResidualTerms]
        rw [renameResidualTerm_eq_self term (by
          intro spelling member
          exact fixed spelling (by
            simp [termsNullaryCons]
            exact Or.inl member))]
        rw [renameResidualTerms_eq_self rest (by
          intro spelling member
          exact fixed spelling (by
            simp [termsNullaryCons]
            exact Or.inr member))]
end

private theorem lookupSurfaceSubst_renameResidual
    (ρg : Binding.GlobalRenaming) (subst : SurfaceSubst)
    (param : Presentation.Param) :
    lookupSurfaceSubst (renameResidualSubst ρg subst) param =
      (lookupSurfaceSubst subst param).map (renameResidualTerm ρg) := by
  induction subst with
  | nil => rfl
  | cons entry rest ih =>
      simp only [renameResidualSubst, List.map_cons, lookupSurfaceSubst,
        List.findSome?_cons]
      by_cases equal : entry.1 = param
      · simp [equal]
      · rw [if_neg equal, if_neg equal]
        change lookupSurfaceSubst (renameResidualSubst ρg rest) param =
          Option.map (renameResidualTerm ρg) (lookupSurfaceSubst rest param)
        exact ih

private theorem paramsCoveredB_renameResidual
    (ρg : Binding.GlobalRenaming) (params : List Presentation.Param)
    (subst : SurfaceSubst) :
    paramsCoveredB params (renameResidualSubst ρg subst) =
      paramsCoveredB params subst := by
  unfold paramsCoveredB
  induction params with
  | nil => rfl
  | cons param rest ih =>
      simp only [List.all_cons]
      rw [lookupSurfaceSubst_renameResidual, ih]
      cases lookupSurfaceSubst subst param <;> rfl

mutual
  private theorem instantiateSurfacePat_renameResidual
      (fixed : PatFixed ρg pattern) :
      instantiateSurfacePat (renameResidualSubst ρg subst) pattern =
        (instantiateSurfacePat subst pattern).map
          (renameResidualTerm ρg) := by
    cases pattern with
    | var param =>
        exact lookupSurfaceSubst_renameResidual ρg subst param
    | lit term =>
        simp only [instantiateSurfacePat, Option.map_some]
        congr 1
        symm
        apply renameResidualTerm_eq_self term
        intro spelling member
        exact fixed spelling (by simpa [patNullaryCons] using member)
    | con name patterns =>
        cases patterns with
        | nil =>
            have nameFixed : Binding.renameText ρg name = name :=
              fixed name (by simp [patNullaryCons])
            simp [instantiateSurfacePat, instantiateSurfacePats,
              renameResidualTerm, nameFixed]
        | cons first rest =>
            have firstFixed : PatFixed ρg first := by
              intro spelling member
              exact fixed spelling (by
                simp [patNullaryCons, patsNullaryCons]
                exact Or.inl member)
            have restFixed : PatsFixed ρg rest := by
              intro spelling member
              exact fixed spelling (by
                simp [patNullaryCons, patsNullaryCons]
                exact Or.inr member)
            simp only [instantiateSurfacePat, instantiateSurfacePats]
            rw [instantiateSurfacePat_renameResidual
              (subst := subst) firstFixed]
            rw [instantiateSurfacePats_renameResidual
              (subst := subst) restFixed]
            cases instantiateSurfacePat subst first <;>
              cases instantiateSurfacePats subst rest <;>
                simp [renameResidualTerm, renameResidualTerms]
  private theorem instantiateSurfacePats_renameResidual
      (fixed : PatsFixed ρg patterns) :
      instantiateSurfacePats (renameResidualSubst ρg subst) patterns =
        (instantiateSurfacePats subst patterns).map
          (renameResidualTerms ρg) := by
    cases patterns with
    | nil => rfl
    | cons pattern rest =>
        have headFixed : PatFixed ρg pattern := by
          intro spelling member
          exact fixed spelling (by
            simp [patsNullaryCons]
            exact Or.inl member)
        have tailFixed : PatsFixed ρg rest := by
          intro spelling member
          exact fixed spelling (by
            simp [patsNullaryCons]
            exact Or.inr member)
        simp only [instantiateSurfacePats]
        rw [instantiateSurfacePat_renameResidual
          (subst := subst) headFixed]
        rw [instantiateSurfacePats_renameResidual
          (subst := subst) tailFixed]
        cases instantiateSurfacePat subst pattern <;>
          cases instantiateSurfacePats subst rest <;> rfl
end

theorem instantiateSurfaceAtom_renameResidual
    (fixed : AtomPatFixed ρg pattern) :
    instantiateSurfaceAtom (renameResidualSubst ρg subst) pattern =
      (instantiateSurfaceAtom subst pattern).map
        (renameResidualAtom ρg) := by
  simp only [instantiateSurfaceAtom]
  rw [instantiateSurfacePats_renameResidual (subst := subst) fixed]
  cases instantiateSurfacePats subst pattern.args <;>
    simp [renameResidualAtom]

mutual
  private theorem matchSurfacePat_renameResidual
      (fixed : PatFixed ρg pattern) :
      matchSurfacePat (renameResidualSubst ρg subst) pattern
          (renameResidualTerm ρg term) =
        (matchSurfacePat subst pattern term).map
          (renameResidualSubst ρg) := by
    cases pattern with
    | var param =>
        simp only [matchSurfacePat, bindSurfaceParam]
        rw [lookupSurfaceSubst_renameResidual]
        cases found : lookupSurfaceSubst subst param with
        | none =>
            simp [renameResidualSubst, List.map_append]
        | some prior =>
            simp only [Option.map_some]
            rw [sameSurfaceTerm_renameResidual]
            simp
    | lit expected =>
        have expectedFixed :
            renameResidualTerm ρg expected = expected :=
          renameResidualTerm_eq_self expected (by
            intro spelling member
            exact fixed spelling (by
              simpa [patNullaryCons] using member))
        have same :=
          sameSurfaceTerm_renameResidual ρg expected term
        rw [expectedFixed] at same
        simp [matchSurfacePat, same]
    | con expected patterns =>
        cases term with
        | num _ => rfl
        | str _ => rfl
        | con actual terms =>
            cases patterns with
            | nil =>
                have expectedFixed : Binding.renameText ρg expected = expected :=
                  fixed expected (by simp [patNullaryCons])
                cases terms with
                | nil =>
                    have names :=
                      fixedPattern_eq_renameText_iff
                        expected actual expectedFixed
                    by_cases equal : expected = actual
                    · subst actual
                      simp [matchSurfacePat, matchSurfacePats,
                        renameResidualTerm, expectedFixed]
                    · have renamedNe : expected ≠
                          Binding.renameText ρg actual :=
                        fun h => equal (names.mp h)
                      simp [matchSurfacePat, renameResidualTerm,
                        equal, renamedNe]
                | cons first rest =>
                    by_cases equal : expected = actual
                    · simp [matchSurfacePat, matchSurfacePats,
                        renameResidualTerm, renameResidualTerms, equal]
                    · simp [matchSurfacePat, renameResidualTerm, equal]
            | cons firstPattern restPatterns =>
                cases terms with
                | nil =>
                    simp [matchSurfacePat, matchSurfacePats,
                      renameResidualTerm]
                | cons firstTerm restTerms =>
                    by_cases equal : expected = actual
                    · subst actual
                      have patternsFixed :
                          PatsFixed ρg (.cons firstPattern restPatterns) := by
                        intro spelling member
                        exact fixed spelling (by
                          simpa [patNullaryCons] using member)
                      simp only [renameResidualTerm, matchSurfacePat, if_pos]
                      change
                        matchSurfacePats (renameResidualSubst ρg subst)
                            (.cons firstPattern restPatterns)
                            (renameResidualTerms ρg
                              (.cons firstTerm restTerms)) =
                          (matchSurfacePats subst
                            (.cons firstPattern restPatterns)
                            (.cons firstTerm restTerms)).map
                              (renameResidualSubst ρg)
                      exact matchSurfacePats_renameResidual
                        (subst := subst) patternsFixed
                    · simp [renameResidualTerm, matchSurfacePat, equal]
  private theorem matchSurfacePats_renameResidual
      (fixed : PatsFixed ρg patterns) :
      matchSurfacePats (renameResidualSubst ρg subst) patterns
          (renameResidualTerms ρg terms) =
        (matchSurfacePats subst patterns terms).map
          (renameResidualSubst ρg) := by
    cases patterns with
    | nil =>
        cases terms <;> rfl
    | cons pattern rest =>
        cases terms with
        | nil => rfl
        | cons term tail =>
            have headFixed : PatFixed ρg pattern := by
              intro spelling member
              exact fixed spelling (by
                simp [patsNullaryCons]
                exact Or.inl member)
            have tailFixed : PatsFixed ρg rest := by
              intro spelling member
              exact fixed spelling (by
                simp [patsNullaryCons]
                exact Or.inr member)
            simp only [renameResidualTerms, matchSurfacePats]
            rw [matchSurfacePat_renameResidual
              (subst := subst) headFixed]
            cases matched : matchSurfacePat subst pattern term with
            | none => rfl
            | some next =>
                simp only [Option.map_some]
                exact matchSurfacePats_renameResidual
                  (subst := next) tailFixed
end

private theorem matchSurfaceAtom_renameResidual
    (fixed : AtomPatFixed ρg pattern) :
    matchSurfaceAtom (renameResidualSubst ρg subst) pattern
        (renameResidualAtom ρg atom) =
      (matchSurfaceAtom subst pattern atom).map
        (renameResidualSubst ρg) := by
  cases atom with
  | atom predicate terms =>
      simp only [renameResidualAtom, matchSurfaceAtom]
      split
      · exact matchSurfacePats_renameResidual (subst := subst) fixed
      · rfl


mutual
  private theorem renameResidualTerm_eq_renameValueTerm
      (fixed : TermFixed ρg values term) :
      renameResidualTerm ρg term =
        Binding.renameValueTerm ρg values term := by
    cases term with
    | num _ => rfl
    | str _ => rfl
    | con name terms =>
        cases terms with
        | nil =>
            by_cases member : name ∈ values.map (·.val)
            · have typedMember :
                  (⟨name⟩ : Presentation.ValueName) ∈ values :=
                (mem_values_map values name).mp member
              simp [renameResidualTerm, Binding.renameValueTerm,
                typedMember]
            · have typedNotMember :
                  (⟨name⟩ : Presentation.ValueName) ∉ values := by
                intro typedMember
                exact member ((mem_values_map values name).mpr typedMember)
              have nameFixed :=
                fixed name (by simp [termNullaryCons]) member
              simp [renameResidualTerm, Binding.renameValueTerm,
                typedNotMember, nameFixed]
        | cons term rest =>
            simp only [renameResidualTerm, Binding.renameValueTerm]
            congr 1
            exact renameResidualTerms_eq_renameValueTerms
              (termFixed_cons_iff fixed)
  private theorem renameResidualTerms_eq_renameValueTerms
      (fixed : TermsFixed ρg values terms) :
      renameResidualTerms ρg terms =
        Binding.renameValueTerms ρg values terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp only [renameResidualTerms, Binding.renameValueTerms]
        rw [renameResidualTerm_eq_renameValueTerm
          (fixed term (by simp [termsToList]))]
        rw [renameResidualTerms_eq_renameValueTerms (by
          intro nested member
          exact fixed nested (by
            simp [termsToList]
            exact Or.inr member))]
end

theorem renameResidualAtom_eq_renameValueAtom
    (fixed : AtomFixed ρg values atom) :
    renameResidualAtom ρg atom =
      Binding.renameValueAtom ρg values atom := by
  cases atom with
  | atom predicate terms =>
      simp only [renameResidualAtom, Binding.renameValueAtom]
      rw [renameResidualTerms_eq_renameValueTerms fixed]

mutual
  theorem renameResidualSupportTerm_eq_renameSupportTerm
      (fixed : SupportTermFixed ρg values term) :
      renameResidualSupportTerm ρg term =
        Binding.renameSupportTerm ρg values term := by
    cases term with
    | leaf leaf => rfl
    | rule rule subst premises discharges holes assurance =>
        have substEqual :
            renameResidualSubst ρg subst =
              Binding.renameSubstValues ρg values subst := by
          apply List.map_congr_left
          intro entry member
          congr 1
          apply renameResidualTerm_eq_renameValueTerm
          intro spelling spellingMember notValue
          apply fixed spelling
          · simp only [supportTermNullaryCons, List.mem_append]
            exact Or.inl (Or.inl
              (List.mem_flatMap.mpr ⟨entry, member, spellingMember⟩))
          · exact notValue
        have premisesFixed :
            ∀ spelling, spelling ∈ supportTermsNullaryCons premises →
              spelling ∉ values.map (·.val) →
                Binding.renameText ρg spelling = spelling := by
          intro spelling spellingMember notValue
          apply fixed spelling
          · simp [supportTermNullaryCons]
            exact Or.inr (Or.inl spellingMember)
          · exact notValue
        have dischargesFixed :
            ∀ spelling, spelling ∈ supportDischargesNullaryCons discharges →
              spelling ∉ values.map (·.val) →
                Binding.renameText ρg spelling = spelling := by
          intro spelling spellingMember notValue
          apply fixed spelling
          · simp [supportTermNullaryCons]
            exact Or.inr (Or.inr spellingMember)
          · exact notValue
        simp only [renameResidualSupportTerm, Binding.renameSupportTerm]
        rw [substEqual]
        rw [renameResidualSupportTerms_eq_renameSupportTerms premisesFixed]
        rw [renameResidualDischarges_eq_renameDischarges dischargesFixed]
  private theorem renameResidualSupportTerms_eq_renameSupportTerms
      (fixed : ∀ spelling, spelling ∈ supportTermsNullaryCons terms →
        spelling ∉ values.map (·.val) →
          Binding.renameText ρg spelling = spelling) :
      renameResidualSupportTerms ρg terms =
        Binding.renameSupportTerms ρg values terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        have headFixed : SupportTermFixed ρg values term := by
          intro spelling member notValue
          exact fixed spelling (by
            simp [supportTermsNullaryCons]
            exact Or.inl member) notValue
        have tailFixed :
            ∀ spelling, spelling ∈ supportTermsNullaryCons rest →
              spelling ∉ values.map (·.val) →
                Binding.renameText ρg spelling = spelling := by
          intro spelling member notValue
          exact fixed spelling (by
            simp [supportTermsNullaryCons]
            exact Or.inr member) notValue
        simp only [renameResidualSupportTerms, Binding.renameSupportTerms]
        rw [renameResidualSupportTerm_eq_renameSupportTerm headFixed]
        rw [renameResidualSupportTerms_eq_renameSupportTerms tailFixed]
  private theorem renameResidualDischarges_eq_renameDischarges
      (fixed : ∀ spelling, spelling ∈ supportDischargesNullaryCons discharges →
        spelling ∉ values.map (·.val) →
          Binding.renameText ρg spelling = spelling) :
      renameResidualDischarges ρg discharges =
        Binding.renameDischarges ρg values discharges := by
    cases discharges with
    | nil => rfl
    | cons question term rest =>
        have headFixed : SupportTermFixed ρg values term := by
          intro spelling member notValue
          exact fixed spelling (by
            simp [supportDischargesNullaryCons]
            exact Or.inl member) notValue
        have tailFixed :
            ∀ spelling, spelling ∈ supportDischargesNullaryCons rest →
              spelling ∉ values.map (·.val) →
                Binding.renameText ρg spelling = spelling := by
          intro spelling member notValue
          exact fixed spelling (by
            simp [supportDischargesNullaryCons]
            exact Or.inr member) notValue
        simp only [renameResidualDischarges, Binding.renameDischarges]
        rw [renameResidualSupportTerm_eq_renameSupportTerm headFixed]
        rw [renameResidualDischarges_eq_renameDischarges tailFixed]
end

theorem supportTermFixed_of_explicitArg
    (sound : RenamingSound ρg program policy)
    (argument : Presentation.Arg) (term : Presentation.SupportTerm)
    (member : Presentation.Decl.arg argument ∈ program.decls)
    (explicit : argument.instantiation = .explicitTheta term) :
    SupportTermFixed ρg (programValues program) term := by
  intro spelling spellingMember notValue
  apply sound.atoms spelling
  · exact List.mem_flatMap.mpr
      ⟨.arg argument, member, by
        simp [declNullaryCons, argNullaryCons, explicit]
        exact spellingMember⟩
  · exact notValue

private theorem atomFixed_of_declaredLeaf
    (sound : RenamingSound ρg program policy)
    {leaf : Presentation.LeafId} {atom : Atom}
    (member : (leaf, atom) ∈ declaredLeaves program) :
    AtomFixed ρg (programValues program) atom := by
  obtain ⟨declaration, declarationMember, selected⟩ :=
    List.mem_filterMap.mp member
  apply atomFixed_of_decl sound.toComparison declaration declarationMember atom
  cases declaration <;> simp_all [declaredLeaves, declNullaryCons]

theorem declaredLeaves_renameResidual
    (sound : RenamingSound ρg program policy) :
    declaredLeaves (Binding.renameProgram ρg program) =
      (declaredLeaves program).map fun entry =>
        (ρg.leaf entry.1, renameResidualAtom ρg entry.2) := by
  rw [declaredLeaves_renameProgram]
  apply List.map_congr_left
  intro entry member
  obtain ⟨leaf, atom⟩ := entry
  simp only [Prod.mk.injEq, true_and]
  symm
  exact renameResidualAtom_eq_renameValueAtom
    (atomFixed_of_declaredLeaf sound member)

private theorem supportTermsFromList_rename
    (ρg : Binding.GlobalRenaming)
    (terms : List Presentation.SupportTerm) :
    renameResidualSupportTerms ρg (supportTermsFromList terms) =
      supportTermsFromList (terms.map (renameResidualSupportTerm ρg)) := by
  induction terms with
  | nil => rfl
  | cons term rest ih =>
      simp [supportTermsFromList, renameResidualSupportTerms, ih]

private theorem dischargesFromList_rename
    (ρg : Binding.GlobalRenaming)
    (discharges :
      List (Presentation.QuestionId × Presentation.SupportTerm)) :
    renameResidualDischarges ρg (dischargesFromList discharges) =
      dischargesFromList (discharges.map fun entry =>
        (ρg.question entry.1, renameResidualSupportTerm ρg entry.2)) := by
  induction discharges with
  | nil => rfl
  | cons discharge rest ih =>
      obtain ⟨question, term⟩ := discharge
      simp [dischargesFromList, renameResidualDischarges, ih]

theorem premisePatternFixed
    (sound : RenamingSound ρg program policy)
    (rule : Presentation.Rule) (ruleMember : rule ∈ policy.rules)
    (pattern : Presentation.AtomPat) (patternMember : pattern ∈ rule.premises) :
    AtomPatFixed ρg pattern := by
  apply atomPatFixed_of_rule sound.toComparison rule ruleMember pattern
  intro spelling spellingMember
  apply List.mem_append.mpr
  exact Or.inl (List.mem_append.mpr (Or.inl
    (List.mem_flatMap.mpr ⟨pattern, patternMember, spellingMember⟩)))

theorem conclusionPatternFixed
    (sound : RenamingSound ρg program policy)
    (rule : Presentation.Rule) (ruleMember : rule ∈ policy.rules) :
    AtomPatFixed ρg rule.conclusion := by
  apply atomPatFixed_of_rule sound.toComparison rule ruleMember rule.conclusion
  intro spelling spellingMember
  apply List.mem_append.mpr
  exact Or.inl (List.mem_append.mpr (Or.inr spellingMember))

theorem conclOfTerm_rename
    (sound : RenamingSound ρg program policy)
    (term : Presentation.SupportTerm) :
    conclOfTerm (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (renameResidualSupportTerm ρg term) =
      (conclOfTerm program policy term).map
        (renameResidualAtom ρg) := by
  cases term with
  | leaf leaf =>
      simp only [conclOfTerm, renameResidualSupportTerm]
      rw [leafProp?_rename]
      cases found : leafProp? program leaf with
      | none => rfl
      | some atom =>
          simp only [Option.map_some]
          rw [renameResidualAtom_eq_renameValueAtom
            (atomFixed_of_leafProp sound.toComparison leaf atom found)]
  | rule ruleId subst premises discharges holes assurance =>
      simp only [conclOfTerm, renameResidualSupportTerm]
      rw [ruleById_rename]
      cases found : ruleById policy ruleId with
      | none => rfl
      | some rule =>
          simp only [Option.map_some, Option.bind_some,
            Binding.renameRule]
          have ruleMember : rule ∈ policy.rules := by
            unfold ruleById at found
            exact List.mem_of_find?_eq_some found
          exact instantiateSurfaceAtom_renameResidual
            (subst := subst) (conclusionPatternFixed sound rule ruleMember)

private theorem filterDeclaredLeaves_rename
    (ρg : Binding.GlobalRenaming)
    (leaves : List (Presentation.LeafId × Atom))
    (reference : Presentation.ArgRef) :
    (leaves.map fun entry =>
        (ρg.leaf entry.1, renameResidualAtom ρg entry.2)).filter
          (fun entry => entry.1.val == (ρg.argRef reference).val) =
      (leaves.filter fun entry => entry.1.val == reference.val).map
        (fun entry =>
          (ρg.leaf entry.1, renameResidualAtom ρg entry.2)) := by
  induction leaves with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨leaf, atom⟩ := entry
      have test :
          ((ρg.leaf leaf).val == (ρg.argRef reference).val) =
            (leaf.val == reference.val) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        exact renamed_leaf_argRef_spelling_eq_iff ρg leaf reference
      simp only [List.map_cons, List.filter_cons]
      rw [test]
      cases original : leaf.val == reference.val
      · simp only [original, Bool.false_eq_true, if_false]
        exact ih
      · simp only [original, if_true, List.map_cons]
        rw [ih]

private theorem filterPriorArguments_rename
    (ρg : Binding.GlobalRenaming) (priors : List PriorArgument)
    (reference : Presentation.ArgRef) :
    (priors.map (renamePriorArgument ρg)).filter
        (fun prior => prior.id.val == (ρg.argRef reference).val) =
      (priors.filter fun prior => prior.id.val == reference.val).map
        (renamePriorArgument ρg) := by
  induction priors with
  | nil => rfl
  | cons prior rest ih =>
      have test :
          ((ρg.arg prior.id).val == (ρg.argRef reference).val) =
            (prior.id.val == reference.val) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        exact renamed_arg_argRef_spelling_eq_iff ρg prior.id reference
      simp only [List.map_cons, List.filter_cons, renamePriorArgument]
      rw [test]
      cases original : prior.id.val == reference.val
      · simp only [original, Bool.false_eq_true, if_false]
        exact ih
      · simp only [original, if_true, List.map_cons,
          renamePriorArgument]
        rw [ih]

theorem resolveReference_rename
    (sound : RenamingSound ρg program policy)
    (priors : List PriorArgument) (reference : Presentation.ArgRef) :
    resolveReference (Binding.renameProgram ρg program)
        (priors.map (renamePriorArgument ρg))
        (ρg.argRef reference) =
      (resolveReference program priors reference).map
        (renameResolvedReference ρg) := by
  unfold resolveReference
  rw [declaredLeaves_renameResidual sound]
  rw [filterDeclaredLeaves_rename]
  rw [filterPriorArguments_rename]
  generalize (declaredLeaves program).filter
      (fun entry => entry.1.val == reference.val) = leaves
  generalize priors.filter
      (fun prior => prior.id.val == reference.val) = arguments
  cases leaves with
  | nil =>
      cases arguments with
      | nil => rfl
      | cons argument rest =>
          cases rest with
          | nil => simp [renamePriorArgument, renameResolvedReference]
          | cons next tail => rfl
  | cons leaf rest =>
      cases rest with
      | cons next tail => rfl
      | nil =>
          obtain ⟨leafId, atom⟩ := leaf
          cases arguments with
          | nil =>
              simp [renameResolvedReference, renameResidualSupportTerm]
          | cons argument tail => rfl

private theorem resolveReferences_rename
    (sound : RenamingSound ρg program policy)
    (priors : List PriorArgument) (references : List Presentation.ArgRef) :
    resolveReferences (Binding.renameProgram ρg program)
        (priors.map (renamePriorArgument ρg))
        (references.map ρg.argRef) =
      (resolveReferences program priors references).map
        (List.map (renameResolvedReference ρg)) := by
  induction references with
  | nil => rfl
  | cons reference rest ih =>
      simp only [List.map_cons, resolveReferences]
      rw [resolveReference_rename sound priors reference]
      cases resolved : resolveReference program priors reference with
      | none => rfl
      | some first =>
          simp only [Option.map_some, Option.bind_some]
          rw [ih]
          cases resolveReferences program priors rest <;> rfl

private theorem matchResolvedPremises_rename
    (patterns : List Presentation.AtomPat)
    (references : List ResolvedReference)
    (patternsFixed : ∀ pattern ∈ patterns, AtomPatFixed ρg pattern) :
    matchResolvedPremises (renameResidualSubst ρg subst) patterns
        (references.map (renameResolvedReference ρg)) =
      (matchResolvedPremises subst patterns references).map
        (renameResidualSubst ρg) := by
  induction patterns generalizing subst references with
  | nil =>
      cases references <;> rfl
  | cons pattern rest ih =>
      cases references with
      | nil => rfl
      | cons reference tail =>
          have headFixed := patternsFixed pattern (by simp)
          have tailFixed :
              ∀ candidate ∈ rest, AtomPatFixed ρg candidate := by
            intro candidate member
            exact patternsFixed candidate (by simp [member])
          simp only [List.map_cons, matchResolvedPremises,
            renameResolvedReference]
          rw [matchSurfaceAtom_renameResidual
            (subst := subst) headFixed]
          cases matched :
              matchSurfaceAtom subst pattern reference.conclusion with
          | none => rfl
          | some next =>
              simp only [Option.map_some, Option.bind_some]
              exact ih tail tailFixed

private theorem questionContains_rename
    (ρg : Binding.GlobalRenaming) (rule : Presentation.Rule)
    (question : Presentation.QuestionId) :
    (questionIds (Binding.renameRule ρg rule)).contains
        (ρg.question question) =
      (questionIds rule).contains question := by
  apply Bool.eq_iff_iff.mpr
  simp only [questionIds_renameRule, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨candidate, member, equal⟩
    have same : candidate = question := ρg.question_injective equal
    simpa [same] using member
  · intro member
    exact ⟨question, member, rfl⟩

private def renameArgDischarge (ρg : Binding.GlobalRenaming) :
    Presentation.ArgDischarge → Presentation.ArgDischarge
  | [] => []
  | (question, reference) :: rest =>
      (ρg.question question, ρg.argRef reference) ::
        renameArgDischarge ρg rest

private theorem resolveNamedDischarges_rename
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program)
    (policy : Presentation.Policy) (priors : List PriorArgument)
    (rule : Presentation.Rule) (discharges : Presentation.ArgDischarge)
    (sound : RenamingSound ρg program policy) :
    resolveNamedDischarges (Binding.renameProgram ρg program)
        (priors.map (renamePriorArgument ρg)) (Binding.renameRule ρg rule)
        (renameArgDischarge ρg discharges) =
      (resolveNamedDischarges program priors rule discharges).map
        (List.map fun entry =>
          (ρg.question entry.1, renameResidualSupportTerm ρg entry.2)) := by
  induction discharges with
  | nil => rfl
  | cons discharge rest ih =>
      obtain ⟨question, reference⟩ := discharge
      simp only [renameArgDischarge, resolveNamedDischarges]
      rw [questionContains_rename]
      cases contains : (questionIds rule).contains question with
      | false => simp [contains]
      | true =>
          simp only [contains, Bool.not_true, Bool.false_eq_true,
            if_false, pure, Option.bind_some]
          rw [resolveReference_rename sound]
          cases resolved : resolveReference program priors reference with
          | none => rfl
          | some reference =>
              simp only [Option.map_some, Option.bind_some]
              rw [ih]
              cases tail :
                  resolveNamedDischarges program priors rule rest with
              | none => rfl
              | some entries =>
                  simp [renameResolvedReference,
                    renameResidualSupportTerm]

private theorem parserNfAtom_renameResidual
    (ρg : Binding.GlobalRenaming) (atom : Atom) :
    Lara.nf Lara.canonNum (renameResidualAtom ρg atom) =
      renameResidualAtom ρg (Lara.nf Lara.canonNum atom) := by
  cases atom
  simp [Lara.nf, renameResidualAtom, nfTerms_renameResidualTerms]

private theorem parserResidualAtom_injective (ρg : Binding.GlobalRenaming) :
    Function.Injective (renameResidualAtom ρg) := by
  intro left right equal
  cases left with
  | atom leftPred leftTerms =>
      cases right with
      | atom rightPred rightTerms =>
          simp only [renameResidualAtom, Atom.atom.injEq] at equal
          have terms := (renameResidualTerms_eq_iff ρg).mp equal.2
          simp [equal.1, terms]

private theorem parserEquiv_renameResidual
    (ρg : Binding.GlobalRenaming) (left right : Atom) :
    Lara.equiv Lara.canonNum (renameResidualAtom ρg left)
        (renameResidualAtom ρg right) ↔
      Lara.equiv Lara.canonNum left right := by
  simp only [Lara.equiv, parserNfAtom_renameResidual]
  exact (parserResidualAtom_injective ρg).eq_iff

private theorem parserFilterMapLeaves_rename
    (sound : RenamingSound ρg program policy)
    (ground : Atom) :
    (declaredLeaves (Binding.renameProgram ρg program)).filterMap
        (fun entry =>
          if Lara.equiv Lara.canonNum entry.2 (renameResidualAtom ρg ground) then
            some (Presentation.SupportTerm.leaf entry.1)
          else none) =
      ((declaredLeaves program).filterMap fun entry =>
        if Lara.equiv Lara.canonNum entry.2 ground then
          some (Presentation.SupportTerm.leaf entry.1)
        else none).map (renameResidualSupportTerm ρg) := by
  rw [declaredLeaves_renameResidual sound]
  induction declaredLeaves program with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨leaf, proposition⟩ := entry
      simp only [List.map_cons, List.filterMap_cons]
      by_cases original : Lara.equiv Lara.canonNum proposition ground
      · have renamed :=
          (parserEquiv_renameResidual ρg proposition ground).mpr original
        simp [original, renamed, ih, renameResidualSupportTerm]
      · have renamed :=
          (not_congr
            (parserEquiv_renameResidual ρg proposition ground)).mpr original
        simp [original, renamed, ih]

private theorem parserFilterMapPriors_rename
    (ρg : Binding.GlobalRenaming) (priors : List PriorArgument)
    (ground : Atom) :
    (priors.map (renamePriorArgument ρg)).filterMap
        (fun prior =>
          if Lara.equiv Lara.canonNum prior.conclusion
              (renameResidualAtom ρg ground) then some prior.term else none) =
      (priors.filterMap fun prior =>
        if Lara.equiv Lara.canonNum prior.conclusion ground then some prior.term
        else none).map (renameResidualSupportTerm ρg) := by
  induction priors with
  | nil => rfl
  | cons prior rest ih =>
      simp only [List.map_cons, List.filterMap_cons, renamePriorArgument]
      by_cases original : Lara.equiv Lara.canonNum prior.conclusion ground
      · have renamed :=
          (parserEquiv_renameResidual ρg prior.conclusion ground).mpr original
        simp [original, renamed, ih]
      · have renamed :=
          (not_congr
            (parserEquiv_renameResidual ρg prior.conclusion ground)).mpr original
        simp [original, renamed, ih]

private theorem parserPremiseMatches_rename
    (sound : RenamingSound ρg program policy)
    (priors : List PriorArgument) (ground : Atom) :
    parserPremiseMatches (Binding.renameProgram ρg program)
        (priors.map (renamePriorArgument ρg))
        (renameResidualAtom ρg ground) =
      (parserPremiseMatches program priors ground).map
        (renameResidualSupportTerm ρg) := by
  simp only [parserPremiseMatches, List.map_append]
  rw [parserFilterMapLeaves_rename sound, parserFilterMapPriors_rename]

private theorem parserZipParams_renameResidual
    (ρg : Binding.GlobalRenaming) (params : List Presentation.Param)
    (subst : SurfaceSubst) :
    params.zip ((renameResidualSubst ρg subst).map Prod.snd) =
      renameResidualSubst ρg (params.zip (subst.map Prod.snd)) := by
  induction params generalizing subst with
  | nil => rfl
  | cons param rest ih =>
      cases subst with
      | nil => rfl
      | cons entry entries =>
          obtain ⟨key, term⟩ := entry
          simp only [renameResidualSubst, List.map_cons, List.zip_cons_cons]
          congr 1
          simpa [renameResidualSubst, Function.comp_def] using ih entries

private theorem parserResolveImplicitPremise_rename
    (sound : RenamingSound ρg program policy)
    (priors : List PriorArgument) (theta : SurfaceSubst)
    (pattern : Presentation.AtomPat) (fixed : AtomPatFixed ρg pattern) :
    parserResolveImplicitPremise (Binding.renameProgram ρg program)
        (priors.map (renamePriorArgument ρg))
        (renameResidualSubst ρg theta) pattern =
      (parserResolveImplicitPremise program priors theta pattern).map
        (renameResidualSupportTerm ρg) := by
  unfold parserResolveImplicitPremise
  rw [instantiateSurfaceAtom_renameResidual fixed]
  cases instantiated : instantiateSurfaceAtom theta pattern with
  | none => rfl
  | some ground =>
      simp [instantiated]
      rw [parserPremiseMatches_rename sound]
      cases parserPremiseMatches program priors ground with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second tail => rfl

private theorem parserResolveImplicitPremises_rename
    (sound : RenamingSound ρg program policy)
    (priors : List PriorArgument) (theta : SurfaceSubst)
    (patterns : List Presentation.AtomPat)
    (fixed : ∀ pattern ∈ patterns, AtomPatFixed ρg pattern) :
    parserResolveImplicitPremises (Binding.renameProgram ρg program)
        (priors.map (renamePriorArgument ρg))
        (renameResidualSubst ρg theta) patterns =
      (parserResolveImplicitPremises program priors theta patterns).map
        (renameResidualSupportTerms ρg) := by
  induction patterns with
  | nil => rfl
  | cons pattern rest ih =>
      simp only [parserResolveImplicitPremises]
      rw [parserResolveImplicitPremise_rename sound priors theta pattern
        (fixed pattern (by simp))]
      cases parserResolveImplicitPremise program priors theta pattern with
      | none => rfl
      | some term =>
          simp only [Option.map_some, Option.bind_some]
          rw [ih (fun candidate member => fixed candidate (by simp [member]))]
          cases parserResolveImplicitPremises program priors theta rest <;> rfl

private theorem parserResolveExplicitDischarges_rename
    (sound : RenamingSound ρg program policy)
    (priors : List PriorArgument) (discharges : Presentation.Discharges) :
    parserResolveExplicitDischarges (Binding.renameProgram ρg program)
        (priors.map (renamePriorArgument ρg))
        (renameResidualDischarges ρg discharges) =
      (parserResolveExplicitDischarges program priors discharges).map
        (renameResidualDischarges ρg) := by
  cases discharges with
  | nil => rfl
  | cons question term rest =>
      cases term with
      | leaf leaf =>
          simp only [renameResidualDischarges, renameResidualSupportTerm,
            parserResolveExplicitDischarges]
          have referenceEq :
              (⟨(ρg.leaf leaf).val⟩ : Presentation.ArgRef) =
                ρg.argRef ⟨leaf.val⟩ := by
            have valEq :
                (ρg.leaf leaf).val = (ρg.argRef ⟨leaf.val⟩).val := by
              rw [Binding.rename_leaf_val, Binding.rename_argRef_val]
            cases mapped : ρg.argRef ⟨leaf.val⟩ with
            | mk target =>
                apply congrArg (fun value : String =>
                  (⟨value⟩ : Presentation.ArgRef))
                simpa [mapped] using valEq
          rw [referenceEq, resolveReference_rename sound,
            parserResolveExplicitDischarges_rename sound priors rest]
          cases resolveReference program priors ⟨leaf.val⟩ <;>
            cases parserResolveExplicitDischarges program priors rest <;>
            simp [renameResolvedReference, renameResidualDischarges]
      | rule rule subst premises nested holes assurance => rfl

private theorem parserReconstructExplicitTerm_rename
    (sound : RenamingSound ρg program policy)
    (priors : List PriorArgument) (term : Presentation.SupportTerm) :
    parserReconstructExplicitTerm (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (priors.map (renamePriorArgument ρg))
        (renameResidualSupportTerm ρg term) =
      (parserReconstructExplicitTerm program policy priors term).map
        (renameResidualSupportTerm ρg) := by
  cases term with
  | leaf leaf => rfl
  | rule ruleId positionalTheta premises shallowDischarges holes assurance =>
      cases premises with
      | nil =>
          simp only [renameResidualSupportTerm, renameResidualSupportTerms,
            renameResidualDischarges, parserReconstructExplicitTerm]
          rw [ruleById_rename]
          cases found : ruleById policy ruleId with
          | none => rfl
          | some rule =>
              simp [found]
              simp only [Binding.renameRule]
              rw [parserZipParams_renameResidual]
              have member : rule ∈ policy.rules := List.mem_of_find?_eq_some found
              rw [parserResolveImplicitPremises_rename sound priors
                (rule.params.zip (positionalTheta.map Prod.snd)) rule.premises
                (fun pattern patternMember =>
                  premisePatternFixed sound rule member pattern patternMember)]
              rw [parserResolveExplicitDischarges_rename sound priors shallowDischarges]
              by_cases arity : positionalTheta.length = rule.params.length
              · have renamedArity :
                    (renameResidualSubst ρg positionalTheta).length =
                      rule.params.length := by
                  simpa [renameResidualSubst] using arity
                simp only [if_pos arity, if_pos renamedArity]
                cases parserResolveImplicitPremises program priors
                    (rule.params.zip (positionalTheta.map Prod.snd)) rule.premises <;>
                  cases parserResolveExplicitDischarges program priors shallowDischarges <;>
                  simp [renameResidualSupportTerm, renameResidualSubst,
                    renameResidualDischarges, parserZipParams_renameResidual, arity]
              · have renamedArity :
                    (renameResidualSubst ρg positionalTheta).length ≠
                      rule.params.length := by
                  simpa [renameResidualSubst] using arity
                simp [arity, renamedArity]
      | cons premise rest => rfl

theorem buildArgument_rename
    (sound : RenamingSound ρg program policy)
    (priors : List PriorArgument) (argument : Presentation.Arg)
    (member : Presentation.Decl.arg argument ∈ program.decls) :
    buildArgument (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (priors.map (renamePriorArgument ρg))
        (Binding.renameArg ρg (programValues program) argument) =
      (buildArgument program policy priors argument).map
        (renamePriorArgument ρg) := by
  cases instantiation : argument.instantiation with
  | explicitTheta term =>
      have fixed :=
        supportTermFixed_of_explicitArg sound argument term member
          instantiation
      have termRename :=
        renameResidualSupportTerm_eq_renameSupportTerm fixed
      simp only [Binding.renameArg, instantiation,
        Binding.renameArgInstantiation, buildArgument]
      rw [← termRename, parserReconstructExplicitTerm_rename sound priors term]
      cases rebuiltFound : parserReconstructExplicitTerm program policy priors term with
      | none => rfl
      | some rebuilt =>
          simp [rebuiltFound]
          rw [conclOfTerm_rename sound]
          cases found : conclOfTerm program policy rebuilt <;>
            simp [renamePriorArgument]
  | inferTheta ruleId refs discharges holes assurance =>
      simp only [Binding.renameArg, instantiation,
        Binding.renameArgInstantiation, buildArgument]
      rw [ruleById_rename]
      cases found : ruleById policy ruleId with
      | none => simp
      | some rule =>
          simp only [Option.map_some, Option.bind_some,
            Binding.renameRule, List.length_map]
          have ruleMember : rule ∈ policy.rules := by
            unfold ruleById at found
            exact List.mem_of_find?_eq_some found
          cases lengthCheck : refs.length != rule.premises.length with
          | true =>
              have lengthNe : refs.length ≠ rule.premises.length := by
                simpa using lengthCheck
              simp [lengthNe]
          | false =>
              have lengthEq : refs.length = rule.premises.length := by
                simpa using lengthCheck
              simp [Binding.renameRule, lengthEq]
              rw [resolveReferences_rename sound]
              cases resolved :
                  resolveReferences program priors refs with
              | none => rfl
              | some references =>
                  simp only [Option.map_some, Option.bind_some]
                  have matchedRename :=
                    matchResolvedPremises_rename (ρg := ρg) (subst := [])
                      rule.premises references
                      (fun pattern patternMember =>
                        premisePatternFixed sound rule ruleMember pattern
                          patternMember)
                  simp [renameResidualSubst] at matchedRename
                  rw [matchedRename]
                  cases matched :
                      matchResolvedPremises [] rule.premises references with
                  | none => simp [matched]
                  | some subst =>
                      simp only [Option.map_some, Option.bind_some]
                      rw [paramsCoveredB_renameResidual]
                      cases covered : paramsCoveredB rule.params subst with
                      | false => simp [matched, covered]
                      | true =>
                          simp [matched, covered]
                          have dischargesEq :
                              List.map (fun discharge =>
                                  (ρg.question discharge.1,
                                    ρg.argRef discharge.2)) discharges =
                                renameArgDischarge ρg discharges := by
                            clear instantiation
                            induction discharges with
                            | nil => rfl
                            | cons discharge rest ih =>
                                obtain ⟨question, reference⟩ := discharge
                                simp [renameArgDischarge, ih]
                          rw [dischargesEq]
                          have dischargeRename :=
                            resolveNamedDischarges_rename ρg program policy
                              priors rule discharges sound
                          simp only [Binding.renameRule] at dischargeRename
                          rw [dischargeRename]
                          cases dischargeFound :
                              resolveNamedDischarges program priors rule
                                discharges with
                          | none => rfl
                          | some dischargeTerms =>
                              simp only [Option.map_some, Option.bind_some]
                              have referenceTermsEq :
                                  List.map
                                      ((fun reference => reference.term) ∘
                                        renameResolvedReference ρg)
                                      references =
                                    List.map (renameResidualSupportTerm ρg)
                                      (List.map (fun reference =>
                                        reference.term) references) := by
                                simp [renameResolvedReference,
                                  Function.comp_def, List.map_map]
                              rw [referenceTermsEq]
                              rw [← supportTermsFromList_rename,
                                ← dischargesFromList_rename]
                              rw [instantiateSurfaceAtom_renameResidual
                                (subst := subst)
                                (conclusionPatternFixed sound rule
                                  ruleMember)]
                              cases conclusionFound :
                                  instantiateSurfaceAtom subst
                                    rule.conclusion with
                              | none => rfl
                              | some conclusion =>
                                  simp [renamePriorArgument,
                                    renameResidualSupportTerm,
                                    renameResidualSubst,
                                    Binding.renameAssurance]

private theorem atomFixed_of_comparisonGoal
    (sound : RenamingSound ρg program policy)
    (comparison : Presentation.Comparison)
    (member : Presentation.Decl.comparison comparison ∈ program.decls)
    (goal : Atom)
    (found : comparisonGoal? program policy comparison = some goal) :
    AtomFixed ρg (programValues program) goal := by
  unfold comparisonGoal? at found
  cases expansionFound :
      comparisonExpansion? program policy comparison with
  | none => simp [expansionFound] at found
  | some data =>
      have spec := comparisonExpansion?_sound expansionFound
      rcases spec with
        ⟨measurand, polarity, scheme, recheck, bridge,
          goalLeft, goalRight, certRef, parts,
          recheckResultParam, recheckBaselineParam, authoredPred,
          systemTerm, baselineTerm, resultProp, baseProp, bindingProp,
          resultCell, baseCell, resultSlot, baseSlot,
          resultSubst, baseSubst, merged, expandedGoal,
          slotLeft, slotRight, bindingSubst, bridgeSubst,
          _, _, _, recheckFound, _, _, _, _, _, _, _, _,
          conclusionEq, _, _, resultFound, baseFound, _, _, _,
          resultMatchesFound, baseMatchesFound, _,
          systemRolesNonempty, baselineRolesNonempty,
          measurandRolesNonempty, datasetRolesNonempty,
          resultPattern, basePattern, resultPatternFound,
          basePatternFound, mergedFound, _, goalFound,
          _, _, _, _, _, _, dataEq⟩
      have recheckMember : recheck ∈ policy.rules := by
        unfold ruleById at recheckFound
        exact List.mem_of_find?_eq_some recheckFound
      have patternsFixed :
          ∀ pattern ∈ recheck.premises, AtomPatFixed ρg pattern :=
        fun pattern patternMember =>
          premisePatternFixed sound recheck recheckMember pattern
            patternMember
      have resultPropFixed :=
        atomFixed_of_leafProp sound.toComparison comparison.result resultProp
          resultFound
      have basePropFixed :=
        atomFixed_of_leafProp sound.toComparison comparison.baseline baseProp
          baseFound
      have resultFilteredMember :
          (resultSlot, resultSubst) ∈
            (matchingSlots recheck resultProp).filter (fun entry =>
              (lookupSurfaceSubst entry.2 recheckResultParam).isSome) := by
        rw [resultMatchesFound]
        simp
      have baseFilteredMember :
          (baseSlot, baseSubst) ∈
            (matchingSlots recheck baseProp).filter (fun entry =>
              (lookupSurfaceSubst entry.2 recheckBaselineParam).isSome) := by
        rw [baseMatchesFound]
        simp
      have resultSubstFixed :=
        substFixed_of_matchingSlots_member patternsFixed resultPropFixed
          (List.mem_filter.mp resultFilteredMember).1
      have baseSubstFixed :=
        substFixed_of_matchingSlots_member patternsFixed basePropFixed
          (List.mem_filter.mp baseFilteredMember).1
      have authoredFixed :=
        atomFixed_of_decl sound.toComparison (.comparison comparison) member
          comparison.conclusion (by simp [declNullaryCons])
      rw [conclusionEq] at authoredFixed
      have systemFixed : TermFixed ρg (programValues program) systemTerm :=
        authoredFixed systemTerm (by simp [termsToList])
      have baselineFixed :
          TermFixed ρg (programValues program) baselineTerm :=
        authoredFixed baselineTerm (by simp [termsToList])
      have measurandTermFixed :
          TermFixed ρg (programValues program)
            (.con comparison.measurand.val .nil) :=
        nullaryTermFixed_of_roleParams_nonempty resultSubstFixed
          baseSubstFixed (by simpa using measurandRolesNonempty)
      have datasetTermFixed :
          TermFixed ρg (programValues program)
            (.con comparison.dataset.val .nil) :=
        nullaryTermFixed_of_roleParams_nonempty resultSubstFixed
          baseSubstFixed (by simpa using datasetRolesNonempty)
      let thetaSeed :=
        roleSeed (roleParams resultSubst baseSubst systemTerm) systemTerm ++
        roleSeed (roleParams resultSubst baseSubst baselineTerm)
          baselineTerm ++
        roleSeed (roleParams resultSubst baseSubst
          (.con comparison.measurand.val .nil))
          (.con comparison.measurand.val .nil) ++
        roleSeed (roleParams resultSubst baseSubst
          (.con comparison.dataset.val .nil))
          (.con comparison.dataset.val .nil)
      have thetaSeedFixed :
          SubstFixed ρg (programValues program) thetaSeed := by
        exact substFixed_append
          (substFixed_append
            (substFixed_append
              (substFixed_roleSeed systemFixed)
              (substFixed_roleSeed baselineFixed))
            (substFixed_roleSeed measurandTermFixed))
          (substFixed_roleSeed datasetTermFixed)
      have resultPatternFixed :=
        patternsFixed resultPattern
          (List.mem_of_getElem? resultPatternFound)
      have basePatternFixed :=
        patternsFixed basePattern
          (List.mem_of_getElem? basePatternFound)
      have mergedFixed :
          SubstFixed ρg (programValues program) merged :=
        substFixed_of_orderedComparisonMatch thetaSeedFixed
          basePatternFixed resultPatternFixed basePropFixed
          resultPropFixed (by
            simpa [orderedComparisonMatch, thetaSeed] using mergedFound)
      have conclusionFixed :=
        conclusionPatternFixed sound recheck recheckMember
      have expandedGoalFixed :
          AtomFixed ρg (programValues program) expandedGoal :=
        atomFixed_of_instantiateSurfaceAtom mergedFixed conclusionFixed
          goalFound
      have expandedEq : expandedGoal = goal := by
        simp only [expansionFound, Option.map_some,
          Option.some.injEq] at found
        rw [dataEq] at found
        simpa using found
      simpa [expandedEq] using expandedGoalFixed

/-- Every executable term synthesized by a successful real comparison
expansion has fixed non-value constructor spellings.  This covers the complete
recheck and bridge substitutions carried by `ComparisonExpansionData`; it is
strictly about the production expansion record, not the certificate
pre-validation approximation. -/
theorem comparisonExpansionData_fixed
    (sound : RenamingSound ρg program policy)
    (comparison : Presentation.Comparison)
    (member : Presentation.Decl.comparison comparison ∈ program.decls)
    (data : ComparisonExpansionData)
    (found : comparisonExpansion? program policy comparison = some data) :
    AtomFixed ρg (programValues program) data.goal ∧
      SubstFixed ρg (programValues program) data.thetaRecheck ∧
      SubstFixed ρg (programValues program) data.thetaBridge := by
  have spec := comparisonExpansion?_sound found
  rcases spec with
    ⟨measurand, polarity, scheme, recheck, bridge,
      goalLeft, goalRight, certRef, parts,
      recheckResultParam, recheckBaselineParam, authoredPred,
      systemTerm, baselineTerm, resultProp, baseProp, bindingProp,
      resultCell, baseCell, resultSlot, baseSlot,
      resultSubst, baseSubst, merged, goal, slotLeft, slotRight,
      bindingSubst, bridgeSubst, _, _, _, recheckFound, bridgeFound,
      _, _, _, _, partsFound, _, _, conclusionEq, _, _, resultFound,
      baseFound, bindingFound, _, _, resultMatchesFound,
      baseMatchesFound, _, systemRolesNonempty, baselineRolesNonempty,
      measurandRolesNonempty, datasetRolesNonempty, resultPattern,
      basePattern, resultPatternFound, basePatternFound, mergedFound,
      _, goalFound, _, _, _, bindingSubstFound, bridgeSubstFound, _,
      dataEq⟩
  have recheckMember : recheck ∈ policy.rules := by
    unfold ruleById at recheckFound
    exact List.mem_of_find?_eq_some recheckFound
  have bridgeMember : bridge ∈ policy.rules := by
    unfold ruleById at bridgeFound
    exact List.mem_of_find?_eq_some bridgeFound
  have patternsFixed :
      ∀ pattern ∈ recheck.premises, AtomPatFixed ρg pattern :=
    fun pattern patternMember =>
      premisePatternFixed sound recheck recheckMember pattern patternMember
  have resultPropFixed :=
    atomFixed_of_leafProp sound.toComparison comparison.result resultProp
      resultFound
  have basePropFixed :=
    atomFixed_of_leafProp sound.toComparison comparison.baseline baseProp
      baseFound
  have bindingPropFixed :=
    atomFixed_of_leafProp sound.toComparison comparison.binding bindingProp
      bindingFound
  have resultFilteredMember :
      (resultSlot, resultSubst) ∈
        (matchingSlots recheck resultProp).filter (fun entry =>
          (lookupSurfaceSubst entry.2 recheckResultParam).isSome) := by
    rw [resultMatchesFound]
    simp
  have baseFilteredMember :
      (baseSlot, baseSubst) ∈
        (matchingSlots recheck baseProp).filter (fun entry =>
          (lookupSurfaceSubst entry.2 recheckBaselineParam).isSome) := by
    rw [baseMatchesFound]
    simp
  have resultSubstFixed :=
    substFixed_of_matchingSlots_member patternsFixed resultPropFixed
      (List.mem_filter.mp resultFilteredMember).1
  have baseSubstFixed :=
    substFixed_of_matchingSlots_member patternsFixed basePropFixed
      (List.mem_filter.mp baseFilteredMember).1
  have authoredFixed :=
    atomFixed_of_decl sound.toComparison (.comparison comparison) member
      comparison.conclusion (by simp [declNullaryCons])
  rw [conclusionEq] at authoredFixed
  have systemFixed : TermFixed ρg (programValues program) systemTerm :=
    authoredFixed systemTerm (by simp [termsToList])
  have baselineFixed : TermFixed ρg (programValues program) baselineTerm :=
    authoredFixed baselineTerm (by simp [termsToList])
  have measurandTermFixed : TermFixed ρg (programValues program)
      (.con comparison.measurand.val .nil) :=
    nullaryTermFixed_of_roleParams_nonempty resultSubstFixed baseSubstFixed
      (by simpa using measurandRolesNonempty)
  have datasetTermFixed : TermFixed ρg (programValues program)
      (.con comparison.dataset.val .nil) :=
    nullaryTermFixed_of_roleParams_nonempty resultSubstFixed baseSubstFixed
      (by simpa using datasetRolesNonempty)
  let thetaSeed :=
    roleSeed (roleParams resultSubst baseSubst systemTerm) systemTerm ++
      roleSeed (roleParams resultSubst baseSubst baselineTerm) baselineTerm ++
      roleSeed (roleParams resultSubst baseSubst
        (.con comparison.measurand.val .nil))
        (.con comparison.measurand.val .nil) ++
      roleSeed (roleParams resultSubst baseSubst
        (.con comparison.dataset.val .nil))
        (.con comparison.dataset.val .nil)
  have thetaSeedFixed : SubstFixed ρg (programValues program) thetaSeed :=
    substFixed_append
      (substFixed_append
        (substFixed_append
          (substFixed_roleSeed systemFixed)
          (substFixed_roleSeed baselineFixed))
        (substFixed_roleSeed measurandTermFixed))
      (substFixed_roleSeed datasetTermFixed)
  have resultPatternFixed :=
    patternsFixed resultPattern (List.mem_of_getElem? resultPatternFound)
  have basePatternFixed :=
    patternsFixed basePattern (List.mem_of_getElem? basePatternFound)
  have mergedFixed : SubstFixed ρg (programValues program) merged :=
    substFixed_of_orderedComparisonMatch thetaSeedFixed basePatternFixed
      resultPatternFixed basePropFixed resultPropFixed (by
        simpa [orderedComparisonMatch, thetaSeed] using mergedFound)
  have goalFixed : AtomFixed ρg (programValues program) goal :=
    atomFixed_of_instantiateSurfaceAtom mergedFixed
      (conclusionPatternFixed sound recheck recheckMember) goalFound
  have bridgeSeedFixed : SubstFixed ρg (programValues program)
      [(parts.systemParam, systemTerm),
        (parts.baselineParam, baselineTerm),
        (parts.measurandParam, (.con comparison.measurand.val .nil)),
        (parts.datasetParam, (.con comparison.dataset.val .nil))] := by
    intro entry entryMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at entryMember
    rcases entryMember with rfl | rfl | rfl | rfl
    · exact systemFixed
    · exact baselineFixed
    · exact measurandTermFixed
    · exact datasetTermFixed
  have bridgePatterns := bridgeParts_patterns_mem partsFound
  have bindingPatternFixed :=
    premisePatternFixed sound bridge bridgeMember parts.bindingPattern
      bridgePatterns.1
  have comparisonPatternFixed :=
    premisePatternFixed sound bridge bridgeMember parts.comparisonPattern
      bridgePatterns.2
  have bindingSubstFixed : SubstFixed ρg (programValues program)
      bindingSubst :=
    substFixed_of_matchSurfaceAtom bridgeSeedFixed bindingPatternFixed
      bindingPropFixed bindingSubstFound
  have bridgeSubstFixed : SubstFixed ρg (programValues program)
      bridgeSubst :=
    substFixed_of_matchSurfaceAtom bindingSubstFixed comparisonPatternFixed
      goalFixed bridgeSubstFound
  subst data
  exact ⟨goalFixed, mergedFixed, bridgeSubstFixed⟩
private theorem generatedComparisonArguments_rename
    (sound : RenamingSound ρg program policy)
    (comparison : Presentation.Comparison)
    (member : Presentation.Decl.comparison comparison ∈ program.decls) :
    generatedComparisonArguments (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (Binding.renameComparison ρg (programValues program) comparison) =
      (generatedComparisonArguments program policy comparison).map fun pair =>
        (renamePriorArgument ρg pair.1,
          renamePriorArgument ρg pair.2) := by
  unfold generatedComparisonArguments
  rw [comparisonGoal?_rename sound comparison member]
  cases goalFound : comparisonGoal? program policy comparison with
  | none => rfl
  | some goal =>
      simp
      have goalFixed :=
        atomFixed_of_comparisonGoal sound comparison member goal goalFound
      rw [← renameResidualAtom_eq_renameValueAtom goalFixed]
      unfold Binding.renameComparison
      rw [measurandById_rename]
      cases measurandFound :
          policy.measurands.find? (fun measurand =>
            decide (measurand.id = comparison.measurand)) with
      | none => rfl
      | some measurand =>
          simp
          cases polarityFound : measurand.polarity <;>
            simp [polarityFound]
          rename_i polarity
          have predicateEq :
              (fun scheme : Presentation.ComparisonScheme =>
                decide (scheme.relation = comparison.relation) &&
                  decide (scheme.polarity = polarity)) =
              (fun scheme =>
                decide (scheme.relation = comparison.relation ∧
                  scheme.polarity = polarity)) := by
            funext scheme
            by_cases relationEq :
                scheme.relation = comparison.relation <;>
              by_cases polarityEq : scheme.polarity = polarity <;>
              simp [relationEq, polarityEq]
          rw [predicateEq, comparisonScheme_rename]
          cases schemeFound :
              policy.comparisonSchemes.find? (fun scheme =>
                decide (scheme.relation = comparison.relation ∧
                  scheme.polarity = polarity)) with
          | none => rfl
          | some scheme =>
              simp only [Option.map_some, Option.bind_some,
                Binding.renameComparisonScheme]
              rw [ruleById_rename]
              cases recheckFound : ruleById policy scheme.recheck with
              | none => simp [recheckFound]
              | some recheck =>
                  simp only [Option.map_some, Option.bind_some,
                    Binding.renameRule]
                  rw [ruleById_rename]
                  cases bridgeFound : ruleById policy scheme.bridge with
                  | none => simp [recheckFound, bridgeFound]
                  | some bridge =>
                      simp [recheckFound, bridgeFound]
                      have conclusionFixed :
                          AtomFixed ρg (programValues program)
                            comparison.conclusion :=
                        atomFixed_of_decl sound.toComparison
                          (.comparison comparison) member comparison.conclusion
                          (by simp [declNullaryCons])
                      unfold AtomFixed TermsFixed at conclusionFixed
                      cases conclusionEq : comparison.conclusion with
                      | atom pred terms =>
                          simp [conclusionEq] at conclusionFixed
                          cases terms with
                          | nil =>
                              simp [Binding.renameComparison,
                                Binding.renameValueAtom,
                                Binding.renameValueTerms,
                                renamePriorArgument,
                                renameResidualSupportTerm,
                                renameResidualSupportTerms]
                          | cons system tail =>
                              cases tail with
                              | nil =>
                                  simp [Binding.renameComparison,
                                    Binding.renameValueAtom,
                                    Binding.renameValueTerms,
                                    renamePriorArgument,
                                    renameResidualSupportTerm,
                                    renameResidualSupportTerms]
                              | cons baseline rest =>
                                  cases rest with
                                  | cons extra more =>
                                      simp [Binding.renameComparison,
                                        Binding.renameValueAtom,
                                        Binding.renameValueTerms,
                                        renamePriorArgument,
                                        renameResidualSupportTerm,
                                        renameResidualSupportTerms]
                                  | nil =>
                                      have systemFixed :
                                          TermFixed ρg
                                            (programValues program) system :=
                                        conclusionFixed system
                                          (by simp [termsToList])
                                      have baselineFixed :
                                          TermFixed ρg
                                            (programValues program) baseline :=
                                        conclusionFixed baseline
                                          (by simp [termsToList])
                                      simp only [Binding.renameValueAtom,
                                        Binding.renameValueTerms]
                                      rw [← renameResidualTerm_eq_renameValueTerm
                                        systemFixed]
                                      rw [← renameResidualTerm_eq_renameValueTerm
                                        baselineFixed]
                                      simp [Binding.renameComparison,
                                        renamePriorArgument,
                                        renameResidualSupportTerm,
                                        renameResidualSupportTerms,
                                        renameResidualAtom,
                                        renameResidualTerms,
                                        renameResidualSubst,
                                        renameResidualDischarges,
                                        Binding.renameAssurance,
                                        Binding.renameRule,
                                        renameResidualTerm,
                                        Binding.renameText,
                                        supportTermsFromList]

theorem argumentPayloadsFromProgram
    (member : Presentation.Decl.arg argument ∈ program.decls) :
    argBinderSpellings argument ⊆ programBinderSpellings program ∧
    argOpaqueCertPremiseSpellings argument ⊆
      programOpaqueCertPremiseSpellings program := by
  constructor
  · intro spelling spellingMember
    exact List.mem_flatMap.mpr
      ⟨.arg argument, member, by
        simpa [declBinderSpellings] using spellingMember⟩
  · intro spelling spellingMember
    exact List.mem_flatMap.mpr
      ⟨.arg argument, member, by
        simpa [declOpaqueCertPremiseSpellings] using spellingMember⟩

theorem resolveReference_preserves_priorPayloads
    (safe : PriorPayloadsFromProgram program priors)
    (found : resolveReference program priors reference = some resolved) :
    supportTermBinderSpellings resolved.term ⊆
        programBinderSpellings program ∧
      supportTermOpaqueCertPremiseSpellings resolved.term ⊆
        programOpaqueCertPremiseSpellings program := by
  have filteredSafe :
      ∀ prior ∈ priors.filter (fun prior => prior.id.val == reference.val),
        supportTermBinderSpellings prior.term ⊆
            programBinderSpellings program ∧
          supportTermOpaqueCertPremiseSpellings prior.term ⊆
            programOpaqueCertPremiseSpellings program := by
    intro prior priorMember
    exact safe prior (List.mem_filter.mp priorMember).1
  unfold resolveReference at found
  generalize leavesSelected :
      (declaredLeaves program).filter
        (fun entry => entry.1.val == reference.val) = leaves at found
  generalize argumentsSelected :
      priors.filter (fun prior => prior.id.val == reference.val) =
        arguments at found
  cases leaves with
  | nil =>
      cases arguments with
      | nil => simp at found
      | cons argument rest =>
          cases rest with
          | nil =>
              simp only [Option.some.injEq] at found
              subst resolved
              exact filteredSafe argument (by
                rw [argumentsSelected]
                simp)
          | cons next tail => simp at found
  | cons leaf rest =>
      cases rest with
      | cons next tail => simp at found
      | nil =>
          cases arguments with
          | nil =>
              obtain ⟨leafId, proposition⟩ := leaf
              simp only [Option.some.injEq] at found
              subst resolved
              simp [supportTermBinderSpellings,
                supportTermOpaqueCertPremiseSpellings]
          | cons argument tail => simp at found

private theorem resolveReferences_preserve_priorPayloads
    (safe : PriorPayloadsFromProgram program priors)
    (found : resolveReferences program priors references = some resolved) :
    ∀ reference ∈ resolved,
      supportTermBinderSpellings reference.term ⊆
          programBinderSpellings program ∧
        supportTermOpaqueCertPremiseSpellings reference.term ⊆
          programOpaqueCertPremiseSpellings program := by
  induction references generalizing resolved with
  | nil =>
      simp only [resolveReferences, Option.some.injEq] at found
      subst resolved
      simp
  | cons reference rest ih =>
      cases headFound : resolveReference program priors reference with
      | none =>
          simp [resolveReferences, headFound] at found
      | some head =>
          cases tailFound : resolveReferences program priors rest with
          | none =>
              simp [resolveReferences, headFound, tailFound] at found
          | some tail =>
              simp [resolveReferences, headFound, tailFound] at found
              subst resolved
              intro candidate candidateMember
              simp only [List.mem_cons] at candidateMember
              rcases candidateMember with rfl | candidateMember
              · exact resolveReference_preserves_priorPayloads safe headFound
              · exact ih tailFound candidate candidateMember

private theorem resolveNamedDischarges_preserve_priorPayloads
    (safe : PriorPayloadsFromProgram program priors)
    (found : resolveNamedDischarges program priors rule discharges =
      some resolved) :
    ∀ entry ∈ resolved,
      supportTermBinderSpellings entry.2 ⊆
          programBinderSpellings program ∧
        supportTermOpaqueCertPremiseSpellings entry.2 ⊆
          programOpaqueCertPremiseSpellings program := by
  induction discharges generalizing resolved with
  | nil =>
      simp only [resolveNamedDischarges, Option.some.injEq] at found
      subst resolved
      simp
  | cons entry rest ih =>
      obtain ⟨question, reference⟩ := entry
      cases contains : (questionIds rule).contains question with
      | false =>
          simp_all [resolveNamedDischarges]
      | true =>
          cases headFound : resolveReference program priors reference with
          | none =>
              simp [resolveNamedDischarges, contains, headFound] at found
          | some head =>
              cases tailFound :
                  resolveNamedDischarges program priors rule rest with
              | none =>
                  simp [resolveNamedDischarges, contains, headFound,
                    tailFound] at found
              | some tail =>
                  simp [resolveNamedDischarges, contains, headFound,
                    tailFound] at found
                  rcases found with ⟨_, equal⟩
                  subst resolved
                  intro candidate candidateMember
                  simp only [List.mem_cons] at candidateMember
                  rcases candidateMember with rfl | candidateMember
                  · exact
                      resolveReference_preserves_priorPayloads safe headFound
                  · exact ih tailFound candidate candidateMember

private theorem supportTermsFromList_preserves_payloads
    (safe : ∀ term ∈ terms,
      supportTermBinderSpellings term ⊆ programBinderSpellings program ∧
      supportTermOpaqueCertPremiseSpellings term ⊆
        programOpaqueCertPremiseSpellings program) :
    supportTermsBinderSpellings (supportTermsFromList terms) ⊆
        programBinderSpellings program ∧
      supportTermsOpaqueCertPremiseSpellings (supportTermsFromList terms) ⊆
        programOpaqueCertPremiseSpellings program := by
  induction terms with
  | nil =>
      simp [supportTermsFromList, supportTermsBinderSpellings,
        supportTermsOpaqueCertPremiseSpellings]
  | cons term rest ih =>
      have headSafe := safe term (by simp)
      have tailSafe := ih (by
        intro candidate candidateMember
        exact safe candidate (by simp [candidateMember]))
      constructor
      · intro spelling spellingMember
        simp only [supportTermsFromList, supportTermsBinderSpellings,
          List.mem_append] at spellingMember
        rcases spellingMember with spellingMember | spellingMember
        · exact headSafe.1 spellingMember
        · exact tailSafe.1 spellingMember
      · intro spelling spellingMember
        simp only [supportTermsFromList,
          supportTermsOpaqueCertPremiseSpellings,
          List.mem_append] at spellingMember
        rcases spellingMember with spellingMember | spellingMember
        · exact headSafe.2 spellingMember
        · exact tailSafe.2 spellingMember

private theorem dischargesFromList_preserves_payloads
    (safe : ∀ entry ∈ discharges,
      supportTermBinderSpellings entry.2 ⊆ programBinderSpellings program ∧
      supportTermOpaqueCertPremiseSpellings entry.2 ⊆
        programOpaqueCertPremiseSpellings program) :
    supportDischargesBinderSpellings (dischargesFromList discharges) ⊆
        programBinderSpellings program ∧
      dischargeOpaqueCertPremiseSpellings (dischargesFromList discharges) ⊆
        programOpaqueCertPremiseSpellings program := by
  induction discharges with
  | nil =>
      simp [dischargesFromList, supportDischargesBinderSpellings,
        dischargeOpaqueCertPremiseSpellings]
  | cons entry rest ih =>
      obtain ⟨question, term⟩ := entry
      have headSafe := safe (question, term) (by simp)
      have tailSafe := ih (by
        intro candidate candidateMember
        exact safe candidate (by simp [candidateMember]))
      constructor
      · intro spelling spellingMember
        simp only [dischargesFromList, supportDischargesBinderSpellings,
          List.mem_append] at spellingMember
        rcases spellingMember with spellingMember | spellingMember
        · exact headSafe.1 spellingMember
        · exact tailSafe.1 spellingMember
      · intro spelling spellingMember
        simp only [dischargesFromList,
          dischargeOpaqueCertPremiseSpellings,
          List.mem_append] at spellingMember
        rcases spellingMember with spellingMember | spellingMember
        · exact headSafe.2 spellingMember
        · exact tailSafe.2 spellingMember

private def ParserSupportPayloadsFromProgram
    (program : Presentation.Program) (term : Presentation.SupportTerm) : Prop :=
  supportTermBinderSpellings term ⊆ programBinderSpellings program ∧
    supportTermOpaqueCertPremiseSpellings term ⊆
      programOpaqueCertPremiseSpellings program

private theorem parserPremiseMatches_payloads
    (safe : PriorPayloadsFromProgram program priors)
    (ground : Atom) (term : Presentation.SupportTerm)
    (member : term ∈ parserPremiseMatches program priors ground) :
    ParserSupportPayloadsFromProgram program term := by
  unfold parserPremiseMatches at member
  simp only [List.mem_append] at member
  rcases member with leafMember | priorMember
  · obtain ⟨entry, entryMember, selected⟩ := List.mem_filterMap.mp leafMember
    split at selected
    · simp only [Option.some.injEq] at selected
      subst term
      simp [ParserSupportPayloadsFromProgram, supportTermBinderSpellings,
        supportTermOpaqueCertPremiseSpellings]
    · simp at selected
  · obtain ⟨prior, priorInPriors, selected⟩ := List.mem_filterMap.mp priorMember
    split at selected
    · simp only [Option.some.injEq] at selected
      subst term
      exact safe prior priorInPriors
    · simp at selected

private theorem parserResolveImplicitPremise_payloads
    (safe : PriorPayloadsFromProgram program priors)
    (found : parserResolveImplicitPremise program priors theta pattern = some term) :
    ParserSupportPayloadsFromProgram program term := by
  unfold parserResolveImplicitPremise at found
  cases groundFound : instantiateSurfaceAtom theta pattern with
  | none => simp [groundFound] at found
  | some ground =>
      simp only [groundFound, Option.bind_some] at found
      cases matchesFound : parserPremiseMatches program priors ground with
      | nil => simp [matchesFound] at found
      | cons head rest =>
          cases rest with
          | nil =>
              simp [matchesFound] at found
              subst term
              exact parserPremiseMatches_payloads safe ground head (by
                rw [matchesFound]
                simp)
          | cons next tail => simp [matchesFound] at found

private theorem parserResolveImplicitPremises_payloads
    (safe : PriorPayloadsFromProgram program priors)
    (found : parserResolveImplicitPremises program priors theta patterns = some terms) :
    supportTermsBinderSpellings terms ⊆ programBinderSpellings program ∧
      supportTermsOpaqueCertPremiseSpellings terms ⊆
        programOpaqueCertPremiseSpellings program := by
  induction patterns generalizing terms with
  | nil =>
      simp [parserResolveImplicitPremises] at found
      subst terms
      simp [supportTermsBinderSpellings, supportTermsOpaqueCertPremiseSpellings]
  | cons pattern rest ih =>
      cases headFound : parserResolveImplicitPremise program priors theta pattern with
      | none => simp [parserResolveImplicitPremises, headFound] at found
      | some head =>
          cases tailFound : parserResolveImplicitPremises program priors theta rest with
          | none => simp [parserResolveImplicitPremises, headFound, tailFound] at found
          | some tail =>
              simp [parserResolveImplicitPremises, headFound, tailFound] at found
              subst terms
              have headSafe := parserResolveImplicitPremise_payloads safe headFound
              have tailSafe := ih tailFound
              constructor
              · intro name member
                simp only [supportTermsBinderSpellings, List.mem_append] at member
                exact member.elim (fun h => headSafe.1 h) (fun h => tailSafe.1 h)
              · intro name member
                simp only [supportTermsOpaqueCertPremiseSpellings,
                  List.mem_append] at member
                exact member.elim (fun h => headSafe.2 h) (fun h => tailSafe.2 h)

private theorem parserResolveExplicitDischarges_payloads
    (safe : PriorPayloadsFromProgram program priors)
    (found : parserResolveExplicitDischarges program priors authored = some rebuilt) :
    supportDischargesBinderSpellings rebuilt ⊆ programBinderSpellings program ∧
      dischargeOpaqueCertPremiseSpellings rebuilt ⊆
        programOpaqueCertPremiseSpellings program := by
  cases authored with
  | nil =>
      simp [parserResolveExplicitDischarges] at found
      subst rebuilt
      simp [supportDischargesBinderSpellings, dischargeOpaqueCertPremiseSpellings]
  | cons question term rest =>
      cases term with
      | rule rule subst premises nested holes assurance =>
          simp [parserResolveExplicitDischarges] at found
      | leaf leaf =>
          cases headFound : resolveReference program priors ⟨leaf.val⟩ with
          | none => simp [parserResolveExplicitDischarges, headFound] at found
          | some head =>
              cases tailFound : parserResolveExplicitDischarges program priors rest with
              | none => simp [parserResolveExplicitDischarges, headFound, tailFound] at found
              | some tail =>
                  simp [parserResolveExplicitDischarges, headFound, tailFound] at found
                  subst rebuilt
                  have headSafe := resolveReference_preserves_priorPayloads safe headFound
                  have tailSafe := parserResolveExplicitDischarges_payloads safe tailFound
                  constructor
                  · intro name member
                    simp only [supportDischargesBinderSpellings,
                      List.mem_append] at member
                    exact member.elim (fun h => headSafe.1 h) (fun h => tailSafe.1 h)
                  · intro name member
                    simp only [dischargeOpaqueCertPremiseSpellings,
                      List.mem_append] at member
                    exact member.elim (fun h => headSafe.2 h) (fun h => tailSafe.2 h)

private theorem parserReconstructExplicitTerm_payloads
    (safe : PriorPayloadsFromProgram program priors)
    (authored : ParserSupportPayloadsFromProgram program term)
    (found : parserReconstructExplicitTerm program policy priors term = some rebuilt) :
    ParserSupportPayloadsFromProgram program rebuilt := by
  cases term with
  | leaf leaf =>
      simp [parserReconstructExplicitTerm] at found
      subst rebuilt
      exact authored
  | rule ruleId positionalTheta premises shallowDischarges holes assurance =>
      cases premises with
      | cons premise rest =>
          simp [parserReconstructExplicitTerm] at found
          subst rebuilt
          exact authored
      | nil =>
          cases ruleFound : ruleById policy ruleId with
          | none => simp [parserReconstructExplicitTerm, ruleFound] at found
          | some rule =>
              cases lengthCheck : positionalTheta.length != rule.params.length with
              | true =>
                  have lengthNe : positionalTheta.length ≠ rule.params.length := by
                    simpa using lengthCheck
                  have impossible :
                      parserReconstructExplicitTerm program policy priors
                        (.rule ruleId positionalTheta .nil shallowDischarges holes assurance) =
                          none := by
                    simp [parserReconstructExplicitTerm, ruleFound, lengthNe]
                  rw [impossible] at found
                  cases found
              | false =>
                  cases premiseFound : parserResolveImplicitPremises program priors
                      (rule.params.zip (positionalTheta.map Prod.snd)) rule.premises with
                  | none => simp [parserReconstructExplicitTerm, ruleFound,
                      lengthCheck, premiseFound] at found
                  | some loweredPremises =>
                      cases dischargeFound :
                          parserResolveExplicitDischarges program priors shallowDischarges with
                      | none => simp [parserReconstructExplicitTerm, ruleFound,
                          lengthCheck, premiseFound, dischargeFound] at found
                      | some loweredDischarges =>
                          simp [parserReconstructExplicitTerm, ruleFound, lengthCheck,
                            premiseFound, dischargeFound] at found
                          rcases found with ⟨_, found⟩
                          subst rebuilt
                          have premiseSafe :=
                            parserResolveImplicitPremises_payloads safe premiseFound
                          have dischargeSafe :=
                            parserResolveExplicitDischarges_payloads safe dischargeFound
                          constructor
                          · intro name member
                            simp only [supportTermBinderSpellings,
                              List.mem_append] at member
                            rcases member with (member | member) | member
                            · exact authored.1 (by
                                simpa [ParserSupportPayloadsFromProgram,
                                  supportTermBinderSpellings,
                                  supportTermsBinderSpellings,
                                  supportDischargesBinderSpellings] using (Or.inl member))
                            · exact premiseSafe.1 member
                            · exact dischargeSafe.1 member
                          · intro name member
                            simp only [supportTermOpaqueCertPremiseSpellings,
                              List.mem_append] at member
                            rcases member with (member | member) | member
                            · exact authored.2 (by
                                simpa [ParserSupportPayloadsFromProgram,
                                  supportTermOpaqueCertPremiseSpellings,
                                  supportTermsOpaqueCertPremiseSpellings,
                                  dischargeOpaqueCertPremiseSpellings] using (Or.inl member))
                            · exact premiseSafe.2 member
                            · exact dischargeSafe.2 member

theorem buildArgument_preserves_priorPayloads
    (safe : PriorPayloadsFromProgram program priors)
    (member : Presentation.Decl.arg argument ∈ program.decls)
    (built : buildArgument program policy priors argument = some prior) :
    PriorPayloadsFromProgram program (priors ++ [prior]) := by
  cases instantiation : argument.instantiation with
  | explicitTheta term =>
      cases rebuiltFound : parserReconstructExplicitTerm program policy priors term with
      | none => simp [buildArgument, instantiation, rebuiltFound] at built
      | some rebuilt =>
          cases conclusionFound : conclOfTerm program policy rebuilt with
          | none => simp [buildArgument, instantiation, rebuiltFound,
              conclusionFound] at built
          | some conclusion =>
              simp [buildArgument, instantiation, rebuiltFound, conclusionFound] at built
              subst prior
              have authored := argumentPayloadsFromProgram member
              simp only [argBinderSpellings, instantiation,
                argOpaqueCertPremiseSpellings] at authored
              have rebuiltSafe := parserReconstructExplicitTerm_payloads
                safe authored rebuiltFound
              intro candidate candidateMember
              simp only [List.mem_append, List.mem_singleton] at candidateMember
              rcases candidateMember with candidateMember | rfl
              · exact safe candidate candidateMember
              · exact rebuiltSafe
  | inferTheta ruleId refs discharges holes assurance =>
      cases ruleFound : ruleById policy ruleId with
      | none =>
          simp [buildArgument, instantiation, ruleFound] at built
      | some rule =>
          cases lengthCheck : refs.length != rule.premises.length with
          | true =>
              simp_all [buildArgument]
          | false =>
              cases referencesFound :
                  resolveReferences program priors refs with
              | none =>
                  simp [buildArgument, instantiation, ruleFound, lengthCheck,
                    referencesFound] at built
              | some references =>
                  cases matched :
                      matchResolvedPremises [] rule.premises references with
                  | none =>
                      simp [buildArgument, instantiation, ruleFound,
                        lengthCheck, referencesFound, matched] at built
                  | some subst =>
                      cases covered : paramsCoveredB rule.params subst with
                      | false =>
                          simp [buildArgument, instantiation, ruleFound,
                            lengthCheck, referencesFound, matched, covered]
                            at built
                      | true =>
                          cases dischargeFound :
                              resolveNamedDischarges program priors rule
                                discharges with
                          | none =>
                              simp [buildArgument, instantiation, ruleFound,
                                lengthCheck, referencesFound, matched, covered,
                                dischargeFound] at built
                          | some dischargeTerms =>
                              cases conclusionFound :
                                  instantiateSurfaceAtom subst rule.conclusion
                                  with
                              | none =>
                                  simp [buildArgument, instantiation, ruleFound,
                                    lengthCheck, referencesFound, matched,
                                    covered, dischargeFound, conclusionFound]
                                    at built
                              | some conclusion =>
                                  simp [buildArgument, instantiation, ruleFound,
                                    lengthCheck, referencesFound, matched,
                                    covered, dischargeFound, conclusionFound]
                                    at built
                                  rcases built with ⟨_, builtEq⟩
                                  subst prior
                                  have authored :=
                                    argumentPayloadsFromProgram member
                                  simp only [argBinderSpellings, instantiation,
                                    argOpaqueCertPremiseSpellings] at authored
                                  have referenceSafe :=
                                    resolveReferences_preserve_priorPayloads
                                      safe referencesFound
                                  have premisePayloads :=
                                    supportTermsFromList_preserves_payloads
                                      (program := program) (terms :=
                                        references.map (fun reference =>
                                          reference.term)) (by
                                        intro term termMember
                                        obtain ⟨reference, referenceMember,
                                          rfl⟩ := List.mem_map.mp termMember
                                        exact referenceSafe reference
                                          referenceMember)
                                  have dischargeSafe :=
                                    resolveNamedDischarges_preserve_priorPayloads
                                      safe dischargeFound
                                  have dischargePayloads :=
                                    dischargesFromList_preserves_payloads
                                      (program := program)
                                      (discharges := dischargeTerms)
                                      dischargeSafe
                                  intro candidate candidateMember
                                  simp only [List.mem_append,
                                    List.mem_singleton] at candidateMember
                                  rcases candidateMember with candidateMember | rfl
                                  · exact safe candidate candidateMember
                                  · constructor
                                    · intro spelling spellingMember
                                      change spelling ∈
                                        assuranceBinderSpellings assurance ++
                                          supportTermsBinderSpellings
                                            (supportTermsFromList
                                              (references.map fun reference =>
                                                reference.term)) ++
                                          supportDischargesBinderSpellings
                                            (dischargesFromList dischargeTerms)
                                        at spellingMember
                                      rcases List.mem_append.mp spellingMember with
                                        prefixMember | dischargeMember
                                      · rcases List.mem_append.mp prefixMember with
                                          assuranceMember | premiseMember
                                        · exact authored.1 assuranceMember
                                        · exact premisePayloads.1 premiseMember
                                      · exact dischargePayloads.1 dischargeMember
                                    · intro spelling spellingMember
                                      change spelling ∈
                                        assuranceOpaqueCertPremiseSpellings
                                            assurance ++
                                          supportTermsOpaqueCertPremiseSpellings
                                            (supportTermsFromList
                                              (references.map fun reference =>
                                                reference.term)) ++
                                          dischargeOpaqueCertPremiseSpellings
                                            (dischargesFromList dischargeTerms)
                                        at spellingMember
                                      rcases List.mem_append.mp spellingMember with
                                        prefixMember | dischargeMember
                                      · rcases List.mem_append.mp prefixMember with
                                          assuranceMember | premiseMember
                                        · exact authored.2 assuranceMember
                                        · exact premisePayloads.2 premiseMember
                                      · exact dischargePayloads.2 dischargeMember

private theorem generatedComparisonArguments_preserve_priorPayloads
    (safe : PriorPayloadsFromProgram program priors)
    (_member : Presentation.Decl.comparison comparison ∈ program.decls)
    (generated : generatedComparisonArguments program policy comparison =
      some pair) :
    PriorPayloadsFromProgram program (priors ++ [pair.1, pair.2]) := by
  unfold generatedComparisonArguments at generated
  cases goalFound : comparisonGoal? program policy comparison with
  | none => simp [goalFound] at generated
  | some goal =>
      cases measurandFound :
          policy.measurands.find? (fun measurand =>
            decide (measurand.id = comparison.measurand)) with
      | none => simp [goalFound, measurandFound] at generated
      | some measurand =>
          cases polarityFound : measurand.polarity with
          | none =>
              simp [goalFound, measurandFound, polarityFound] at generated
          | some polarity =>
              cases schemeFound :
                  policy.comparisonSchemes.find? (fun scheme =>
                    decide (scheme.relation = comparison.relation) &&
                      decide (scheme.polarity = polarity)) with
              | none =>
                  have schemeFoundConj :
                      policy.comparisonSchemes.find? (fun scheme =>
                        decide (scheme.relation = comparison.relation ∧
                          scheme.polarity = polarity)) = none := by
                    have predicateEq :
                        (fun scheme : Presentation.ComparisonScheme =>
                          decide (scheme.relation = comparison.relation ∧
                            scheme.polarity = polarity)) =
                          (fun scheme =>
                            decide (scheme.relation = comparison.relation) &&
                              decide (scheme.polarity = polarity)) := by
                      funext candidate
                      simp
                    rw [predicateEq]
                    exact schemeFound
                  simp [goalFound, measurandFound, polarityFound, schemeFound,
                    schemeFoundConj]
                    at generated
              | some scheme =>
                  have schemeFoundConj :
                      policy.comparisonSchemes.find? (fun candidate =>
                        decide (candidate.relation = comparison.relation ∧
                          candidate.polarity = polarity)) = some scheme := by
                    have predicateEq :
                        (fun candidate : Presentation.ComparisonScheme =>
                          decide (candidate.relation = comparison.relation ∧
                            candidate.polarity = polarity)) =
                          (fun candidate =>
                            decide (candidate.relation = comparison.relation) &&
                              decide (candidate.polarity = polarity)) := by
                      funext candidate
                      simp
                    rw [predicateEq]
                    exact schemeFound
                  cases recheckFound : ruleById policy scheme.recheck with
                  | none =>
                      simp [goalFound, measurandFound, polarityFound,
                        schemeFound, schemeFoundConj, recheckFound] at generated
                  | some recheck =>
                      cases bridgeFound : ruleById policy scheme.bridge with
                      | none =>
                          simp [goalFound, measurandFound, polarityFound,
                            schemeFound, schemeFoundConj, recheckFound,
                            bridgeFound] at generated
                      | some bridge =>
                          cases conclusionEq : comparison.conclusion with
                          | atom pred terms =>
                              cases terms with
                              | nil =>
                                  simp [goalFound, measurandFound,
                                    polarityFound, schemeFound, schemeFoundConj,
                                    recheckFound, bridgeFound, conclusionEq]
                                    at generated
                              | cons system tail =>
                                  cases tail with
                                  | nil =>
                                      simp [goalFound, measurandFound,
                                        polarityFound, schemeFound,
                                        schemeFoundConj, recheckFound,
                                        bridgeFound, conclusionEq] at generated
                                  | cons baseline rest =>
                                      cases rest with
                                      | cons extra more =>
                                          simp [goalFound, measurandFound,
                                            polarityFound, schemeFound,
                                            schemeFoundConj, recheckFound,
                                            bridgeFound, conclusionEq]
                                            at generated
                                      | nil =>
                                          simp [goalFound, measurandFound,
                                            polarityFound, schemeFound,
                                            schemeFoundConj, recheckFound,
                                            bridgeFound, conclusionEq]
                                            at generated
                                          rcases generated with rfl
                                          have firstSafe :
                                              supportTermBinderSpellings
                                                  (.rule recheck.id []
                                                    (supportTermsFromList
                                                      [.leaf comparison.result,
                                                        .leaf
                                                          comparison.baseline])
                                                    .nil [] .none) ⊆
                                                    programBinderSpellings
                                                      program ∧
                                                supportTermOpaqueCertPremiseSpellings
                                                  (.rule recheck.id []
                                                    (supportTermsFromList
                                                      [.leaf comparison.result,
                                                        .leaf
                                                          comparison.baseline])
                                                    .nil [] .none) ⊆
                                                    programOpaqueCertPremiseSpellings
                                                      program := by
                                            simp [supportTermBinderSpellings,
                                              supportTermsFromList,
                                              supportTermsBinderSpellings,
                                              supportDischargesBinderSpellings,
                                              assuranceBinderSpellings,
                                              supportTermOpaqueCertPremiseSpellings,
                                              supportTermsOpaqueCertPremiseSpellings,
                                              dischargeOpaqueCertPremiseSpellings,
                                              assuranceOpaqueCertPremiseSpellings]
                                          have bridgeSafe :
                                              supportTermBinderSpellings
                                                  (.rule bridge.id []
                                                    (supportTermsFromList
                                                      [.leaf comparison.binding,
                                                        .rule recheck.id []
                                                          (supportTermsFromList
                                                            [.leaf
                                                              comparison.result,
                                                              .leaf
                                                                comparison.baseline])
                                                          .nil [] .none])
                                                    .nil [] .none) ⊆
                                                    programBinderSpellings
                                                      program ∧
                                                supportTermOpaqueCertPremiseSpellings
                                                  (.rule bridge.id []
                                                    (supportTermsFromList
                                                      [.leaf comparison.binding,
                                                        .rule recheck.id []
                                                          (supportTermsFromList
                                                            [.leaf
                                                              comparison.result,
                                                              .leaf
                                                                comparison.baseline])
                                                          .nil [] .none])
                                                    .nil [] .none) ⊆
                                                    programOpaqueCertPremiseSpellings
                                                      program := by
                                            simp [supportTermBinderSpellings,
                                              supportTermsFromList,
                                              supportTermsBinderSpellings,
                                              supportDischargesBinderSpellings,
                                              assuranceBinderSpellings,
                                              supportTermOpaqueCertPremiseSpellings,
                                              supportTermsOpaqueCertPremiseSpellings,
                                              dischargeOpaqueCertPremiseSpellings,
                                              assuranceOpaqueCertPremiseSpellings]
                                          intro candidate candidateMember
                                          simp at candidateMember
                                          rcases candidateMember with
                                            candidateMember | firstEq | secondEq
                                          · exact safe candidate candidateMember
                                          · exact firstEq.symm ▸ firstSafe
                                          · exact secondEq.symm ▸ bridgeSafe

theorem buildProgramArguments_rename
    (sound : RenamingSound ρg program policy)
    (declarations : List Presentation.Decl)
    (priors : List PriorArgument)
    (contained : ∀ declaration ∈ declarations,
      declaration ∈ program.decls) :
    buildProgramArguments (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (declarations.map
          (Binding.renameDecl ρg (programValues program)))
        (priors.map (renamePriorArgument ρg)) =
      (buildProgramArguments program policy declarations priors).map
        (List.map (renamePriorArgument ρg)) := by
  induction declarations generalizing priors with
  | nil => rfl
  | cons declaration rest ih =>
      have headMember : declaration ∈ program.decls :=
        contained declaration (by simp)
      have tailContained :
          ∀ candidate ∈ rest, candidate ∈ program.decls := by
        intro candidate candidateMember
        exact contained candidate (by simp [candidateMember])
      cases declaration with
      | leaf leaf =>
          simp only [List.map_cons, Binding.renameDecl,
            buildProgramArguments]
          exact ih priors tailContained
      | claim claim =>
          simp only [List.map_cons, Binding.renameDecl,
            buildProgramArguments]
          exact ih priors tailContained
      | arg argument =>
          simp only [List.map_cons, Binding.renameDecl,
            buildProgramArguments]
          rw [buildArgument_rename sound priors argument headMember]
          cases built : buildArgument program policy priors argument with
          | none => rfl
          | some prior =>
              simpa [List.map_append, built] using
                ih (priors ++ [prior]) tailContained
      | attack attack =>
          simp only [List.map_cons, Binding.renameDecl,
            buildProgramArguments]
          exact ih priors tailContained
      | status status =>
          simp only [List.map_cons, Binding.renameDecl,
            buildProgramArguments]
          exact ih priors tailContained
      | group group =>
          simp only [List.map_cons, Binding.renameDecl,
            buildProgramArguments]
          exact ih priors tailContained
      | comparison comparison =>
          simp only [List.map_cons, Binding.renameDecl,
            buildProgramArguments]
          rw [generatedComparisonArguments_rename sound comparison
            headMember]
          cases generated :
              generatedComparisonArguments program policy comparison with
          | none =>
              simp only [Option.map_none]
              exact ih priors tailContained
          | some pair =>
              simpa [List.map_append, generated] using
                ih (priors ++ [pair.1, pair.2]) tailContained

theorem inferredArgsWellFormedB_rename
    (sound : RenamingSound ρg program policy) :
    inferredArgsWellFormedB (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy) =
      inferredArgsWellFormedB program policy := by
  unfold inferredArgsWellFormedB
  change
    (buildProgramArguments (Binding.renameProgram ρg program)
      (Binding.renamePolicy ρg policy)
      (program.decls.map
        (Binding.renameDecl ρg (programValues program))) []).isSome =
    (buildProgramArguments program policy program.decls []).isSome
  have transported := buildProgramArguments_rename sound program.decls [] (by
    intro declaration declarationMember
    exact declarationMember)
  have transportedSome :=
    congrArg (fun result : Option (List PriorArgument) => result.isSome)
      transported
  cases original :
      buildProgramArguments program policy program.decls [] with
  | none => simpa [original] using transportedSome
  | some arguments => simpa [original] using transportedSome

private noncomputable def restoreRenameText
    (ρg : Binding.GlobalRenaming) (spelling : String) : String := by
  classical
  exact if h : ∃ original, Binding.renameText ρg original = spelling then
    Classical.choose h
  else spelling

private theorem restoreRenameText_rename
    (ρg : Binding.GlobalRenaming) (spelling : String) :
    restoreRenameText ρg (Binding.renameText ρg spelling) = spelling := by
  classical
  unfold restoreRenameText
  split
  · rename_i h
    apply Binding.renameText_injective ρg
    exact Classical.choose_spec h
  · rename_i h
    exact False.elim (h ⟨spelling, rfl⟩)

private noncomputable def restoreRenamedCertPayload
    (ρg : Binding.GlobalRenaming) : Presentation.Sx → Presentation.Sx
  | .node "prem" (.cons (.str source) .nil) =>
      .node "prem" (.cons (.str (restoreRenameText ρg source)) .nil)
  | .node "lam" (.cons formula (.cons body .nil)) =>
      .node "lam"
        (.cons formula (.cons (restoreRenamedCertPayload ρg body) .nil))
  | .node "lam" (.cons binder (.cons formula (.cons body .nil))) =>
      .node "lam" (.cons binder (.cons formula
        (.cons (restoreRenamedCertPayload ρg body) .nil)))
  | .node "app" (.cons function (.cons argument .nil)) =>
      .node "app" (.cons (restoreRenamedCertPayload ρg function)
        (.cons (restoreRenamedCertPayload ρg argument) .nil))
  | .node "abort" (.cons formula (.cons body .nil)) =>
      .node "abort"
        (.cons formula (.cons (restoreRenamedCertPayload ρg body) .nil))
  | expression => expression
termination_by expression => sizeOf expression

private theorem restoreRenamedCertPayload_rename
    (ρg : Binding.GlobalRenaming) (payload : Presentation.Sx) :
    restoreRenamedCertPayload ρg (Binding.renameCertPayload ρg payload) =
      payload := by
  induction payload using Binding.renameCertPayload.induct <;>
    simp_all [Binding.renameCertPayload, restoreRenamedCertPayload,
      restoreRenameText_rename]

/-! #### Named-certificate validator transport -/

theorem supportTermsToList_rename
    (ρg : Binding.GlobalRenaming)
    (terms : Presentation.SupportTerms) :
    supportTermsToList (renameResidualSupportTerms ρg terms) =
      (supportTermsToList terms).map (renameResidualSupportTerm ρg) := by
  cases terms with
  | nil => rfl
  | cons term rest =>
      simp [supportTermsToList, renameResidualSupportTerms,
        supportTermsToList_rename ρg rest]

private theorem dischargeTermsToList_rename
    (ρg : Binding.GlobalRenaming)
    (discharges : Presentation.Discharges) :
    dischargeTermsToList (renameResidualDischarges ρg discharges) =
      (dischargeTermsToList discharges).map fun entry =>
        (ρg.question entry.1, renameResidualSupportTerm ρg entry.2) := by
  cases discharges with
  | nil => rfl
  | cons question term rest =>
      simp [dischargeTermsToList, renameResidualDischarges,
        dischargeTermsToList_rename ρg rest]

mutual
  private theorem renameCertPayload_eq_iff
      (ρg : Binding.GlobalRenaming) {left right : Presentation.Sx} :
      Binding.renameCertPayload ρg left =
          Binding.renameCertPayload ρg right ↔
        left = right := by
    constructor
    · intro equal
      have restored := congrArg (restoreRenamedCertPayload ρg) equal
      simpa only [restoreRenamedCertPayload_rename] using restored
    · intro equal
      subst right
      rfl
  private theorem renameAssurance_eq_iff
      (ρg : Binding.GlobalRenaming)
      {left right : Presentation.Assurance} :
      Binding.renameAssurance ρg left = Binding.renameAssurance ρg right ↔
        left = right := by
    constructor
    · intro equal
      cases left <;> cases right <;>
        simp [Binding.renameAssurance] at equal ⊢
      rename_i leftCert rightCert
      cases leftCert
      cases rightCert
      simp only [Binding.renameAssurance, Presentation.Assurance.cert.injEq,
        Presentation.Cert.mk.injEq] at equal ⊢
      exact ⟨equal.1, equal.2.1, equal.2.2.1,
        (renameCertPayload_eq_iff ρg).mp equal.2.2.2⟩
    · intro equal
      subst right
      rfl
end

private theorem listMap_injective_of_injective
    {α β : Type} {f : α → β} (injective : Function.Injective f) :
    Function.Injective (List.map f) := by
  intro left
  induction left with
  | nil =>
      intro right equal
      cases right <;> simp at equal ⊢
  | cons head tail ih =>
      intro right equal
      cases right with
      | nil => simp at equal
      | cons rightHead rightTail =>
          simp only [List.map_cons, List.cons.injEq] at equal
          rw [injective equal.1, ih equal.2]

mutual
  theorem renameResidualSupportTerm_eq_iff
      (ρg : Binding.GlobalRenaming)
      {left right : Presentation.SupportTerm} :
      renameResidualSupportTerm ρg left =
          renameResidualSupportTerm ρg right ↔
        left = right := by
    constructor
    · intro equal
      cases left with
      | leaf leftLeaf =>
          cases right with
          | leaf rightLeaf =>
              have := ρg.leaf_injective
                (Presentation.SupportTerm.leaf.inj equal)
              simpa [this]
          | rule => simp [renameResidualSupportTerm] at equal
      | rule leftRule leftSubst leftPremises leftDischarges leftHoles
          leftAssurance =>
          cases right with
          | leaf => simp [renameResidualSupportTerm] at equal
          | rule rightRule rightSubst rightPremises rightDischarges rightHoles
              rightAssurance =>
              have fields := Presentation.SupportTerm.rule.inj equal
              have ruleEq := ρg.rule_injective fields.1
              have substEntryInjective :
                  Function.Injective
                    (fun entry : Presentation.Param × Term =>
                      (entry.1, renameResidualTerm ρg entry.2)) := by
                rintro ⟨leftParam, leftTerm⟩
                  ⟨rightParam, rightTerm⟩ equal
                have paramEq' : leftParam = rightParam := by
                  simpa using congrArg Prod.fst equal
                have termEq : leftTerm = rightTerm := by
                  apply (renameResidualTerm_eq_iff ρg).mp
                  simpa using congrArg Prod.snd equal
                exact Prod.ext paramEq' termEq
              have substEq : leftSubst = rightSubst :=
                listMap_injective_of_injective substEntryInjective fields.2.1
              have premisesEq :=
                (renameResidualSupportTerms_eq_iff ρg).mp fields.2.2.1
              have dischargesEq :=
                (renameResidualDischarges_eq_iff ρg).mp fields.2.2.2.1
              have holesEq : leftHoles = rightHoles :=
                listMap_injective_of_injective ρg.obligation_injective
                  fields.2.2.2.2.1
              have assuranceEq :=
                (renameAssurance_eq_iff ρg).mp fields.2.2.2.2.2
              simp [ruleEq, substEq, premisesEq, dischargesEq, holesEq,
                assuranceEq]
    · intro equal
      subst right
      rfl
  private theorem renameResidualSupportTerms_eq_iff
      (ρg : Binding.GlobalRenaming)
      {left right : Presentation.SupportTerms} :
      renameResidualSupportTerms ρg left =
          renameResidualSupportTerms ρg right ↔
        left = right := by
    constructor
    · intro equal
      cases left with
      | nil =>
          cases right <;> simp [renameResidualSupportTerms] at equal ⊢
      | cons leftTerm leftRest =>
          cases right with
          | nil => simp [renameResidualSupportTerms] at equal
          | cons rightTerm rightRest =>
              have head := (renameResidualSupportTerm_eq_iff ρg).mp
                (Presentation.SupportTerms.cons.inj equal).1
              have tail := (renameResidualSupportTerms_eq_iff ρg).mp
                (Presentation.SupportTerms.cons.inj equal).2
              simp [head, tail]
    · intro equal
      subst right
      rfl
  private theorem renameResidualDischarges_eq_iff
      (ρg : Binding.GlobalRenaming)
      {left right : Presentation.Discharges} :
      renameResidualDischarges ρg left =
          renameResidualDischarges ρg right ↔
        left = right := by
    constructor
    · intro equal
      cases left with
      | nil =>
          cases right <;> simp [renameResidualDischarges] at equal ⊢
      | cons leftQuestion leftTerm leftRest =>
          cases right with
          | nil => simp [renameResidualDischarges] at equal
          | cons rightQuestion rightTerm rightRest =>
              have fields := Presentation.Discharges.cons.inj equal
              have questionEq := ρg.question_injective fields.1
              have termEq := (renameResidualSupportTerm_eq_iff ρg).mp
                fields.2.1
              have restEq := (renameResidualDischarges_eq_iff ρg).mp
                fields.2.2
              simp [questionEq, termEq, restEq]
    · intro equal
      subst right
      rfl
end

theorem labelIndex?_rename
    (ρg : Binding.GlobalRenaming) (rule : Presentation.Rule) (name : String) :
    labelIndex? (Binding.renameRule ρg rule) (Binding.renameText ρg name) =
      labelIndex? rule name := by
  unfold labelIndex?
  simp only [Binding.renameRule, List.zipIdx_map, List.filter_map,
    Function.comp_def]
  have predicateEq :
      ∀ pair : Option Presentation.PremiseLabel × Nat,
        (match (Prod.map (Option.map ρg.premiseLabel) id pair).1 with
          | some label =>
              label.val == Binding.renameText ρg name
          | none => false) =
        (match pair.1 with
          | some label => label.val == name
          | none => false) := by
    rintro ⟨label, index⟩
    cases label with
    | none => rfl
    | some label =>
        simp only [Prod.map, Option.map, Binding.rename_premiseLabel_val]
        apply Bool.eq_iff_iff.mpr
        simpa only [Binding.renameText, beq_iff_eq] using
          (Binding.renameText_injective ρg).eq_iff
  have filterEq :
      rule.premiseLabels.zipIdx.filter (fun pair =>
        match (Prod.map (Option.map ρg.premiseLabel) id pair).1 with
        | some label => label.val == Binding.renameText ρg name
        | none => false) =
      rule.premiseLabels.zipIdx.filter (fun pair =>
        match pair.1 with
        | some label => label.val == name
        | none => false) := by
    induction rule.premiseLabels.zipIdx with
    | nil => rfl
    | cons pair rest ih =>
        simp only [List.filter_cons, predicateEq pair, ih]
  rw [filterEq]
  generalize selected :
      rule.premiseLabels.zipIdx.filter (fun pair =>
        match pair.1 with
        | some label => label.val == name
        | none => false) = entries
  cases entries with
  | nil => rfl
  | cons entry rest =>
      cases entry
      cases rest <;> rfl

private theorem locateUniqueTerm_rename
    (ρg : Binding.GlobalRenaming)
    (candidates premises : List Presentation.SupportTerm) :
    locateUniqueTerm
        (candidates.map (renameResidualSupportTerm ρg))
        (premises.map (renameResidualSupportTerm ρg)) =
      locateUniqueTerm candidates premises := by
  unfold locateUniqueTerm
  simp only [List.zipIdx_map, List.filter_map, List.map_map,
    Function.comp_def, Prod.map]
  have predicateEq :
      ∀ pair : Presentation.SupportTerm × Nat,
        (candidates.map (renameResidualSupportTerm ρg)).contains
            (renameResidualSupportTerm ρg pair.1) =
          candidates.contains pair.1 := by
    intro pair
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem]
    constructor
    · intro member
      obtain ⟨candidate, candidateMember, equal⟩ :=
        List.mem_map.mp member
      have originalEqual :=
        (renameResidualSupportTerm_eq_iff ρg).mp equal
      simpa [originalEqual] using candidateMember
    · intro member
      exact List.mem_map.mpr ⟨pair.1, member, rfl⟩
  simp only [predicateEq]
  rfl

theorem certificateResolver_rename
    (sound : RenamingSound ρg program policy)
    (rule : Presentation.Rule) (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm) (name : String) :
    certificateResolver (Binding.renameProgram ρg program)
        (Binding.renameRule ρg rule)
        (priors.map (renamePriorArgument ρg))
        (premises.map (renameResidualSupportTerm ρg))
        (Binding.renameText ρg name) =
      certificateResolver program rule priors premises name := by
  unfold certificateResolver
  rw [declaredLeaves_renameResidual sound, labelIndex?_rename]
  have leafPredicate :
      ∀ entry : Presentation.LeafId × Atom,
        ((ρg.leaf entry.1).val == Binding.renameText ρg name) =
          (entry.1.val == name) := by
    rintro ⟨leaf, atom⟩
    simp only [Binding.rename_leaf_val]
    apply Bool.eq_iff_iff.mpr
    simpa only [Binding.renameText, beq_iff_eq] using
      (Binding.renameText_injective ρg).eq_iff
  have argumentPredicate :
      ∀ prior : PriorArgument,
        ((renamePriorArgument ρg prior).id.val ==
          Binding.renameText ρg name) =
        (prior.id.val == name) := by
    intro prior
    simp only [renamePriorArgument, Binding.rename_arg_val]
    apply Bool.eq_iff_iff.mpr
    simpa only [Binding.renameText, beq_iff_eq] using
      (Binding.renameText_injective ρg).eq_iff
  have filterLeaves :
      ((declaredLeaves program).map fun entry =>
          (ρg.leaf entry.1, renameResidualAtom ρg entry.2)).filter
          (fun entry => entry.1.val == Binding.renameText ρg name) =
        ((declaredLeaves program).filter
          (fun entry => entry.1.val == name)).map fun entry =>
            (ρg.leaf entry.1, renameResidualAtom ρg entry.2) := by
    induction declaredLeaves program with
    | nil => rfl
    | cons entry rest ih =>
        have condition := leafPredicate entry
        cases keep : entry.1.val == name <;>
          simp [keep] at condition ⊢ <;>
          simp [condition, ih]
  have filterArguments :
      (priors.map (renamePriorArgument ρg)).filter
          (fun prior => prior.id.val == Binding.renameText ρg name) =
        (priors.filter (fun prior => prior.id.val == name)).map
          (renamePriorArgument ρg) := by
    induction priors with
    | nil => rfl
    | cons prior rest ih =>
        have condition := argumentPredicate prior
        cases keep : prior.id.val == name <;>
          simp [keep] at condition ⊢ <;>
          simp [condition, ih]
  rw [filterLeaves, filterArguments]
  generalize leavesSelected :
      (declaredLeaves program).filter
        (fun entry => entry.1.val == name) = leaves
  generalize argumentsSelected :
      priors.filter (fun prior => prior.id.val == name) = arguments
  cases label : labelIndex? rule name with
  | some index =>
      cases leaves with
      | nil =>
          cases arguments with
          | nil => simp
          | cons argument rest => rfl
      | cons leaf rest => rfl
  | none =>
      cases leaves with
      | nil =>
          cases arguments with
          | nil => rfl
          | cons argument rest =>
              cases rest with
              | nil =>
                  simp only [List.map_cons, List.map_nil, renamePriorArgument]
                  rw [Binding.rename_arg_val]
                  rw [← Binding.rename_leaf_val ρg
                    (⟨argument.id.val⟩ : Presentation.LeafId)]
                  exact locateUniqueTerm_rename ρg
                    [argument.term, .leaf ⟨argument.id.val⟩] premises
              | cons next tail => rfl
      | cons leaf rest =>
          cases rest with
          | nil =>
              cases arguments with
              | nil =>
                  obtain ⟨leafId, atom⟩ := leaf
                  exact locateUniqueTerm_rename ρg [.leaf leafId] premises
              | cons argument tail => rfl
          | cons next tail => rfl

private theorem hasNamedMarkerB_renameCertPayload_core
    (sound : RenamingSound ρg program policy)
    (payload : Presentation.Sx) :
    hasNamedMarkerB (Binding.renameCertPayload ρg payload) =
      hasNamedMarkerB payload := by
  induction payload using Binding.renameCertPayload.induct with
  | case1 source =>
      simp [Binding.renameCertPayload, hasNamedMarkerB,
        hasNamedMarkerListB, namedMarkerHereB, Lara.Cell.Tag.toString,
        Lara.NDNamed.NamedTag.toString, Lara.ND.Tag.toString]
  | case2 formula body ih =>
      simp [Binding.renameCertPayload, hasNamedMarkerB,
        hasNamedMarkerListB, namedMarkerHereB, ih]
  | case3 binder formula body ih =>
      cases binder <;>
        simp_all [Binding.renameCertPayload, hasNamedMarkerB,
          hasNamedMarkerListB, namedMarkerHereB]
  | case4 function argument ihFunction ihArgument =>
      simp [Binding.renameCertPayload, hasNamedMarkerB,
        hasNamedMarkerListB, namedMarkerHereB, ihFunction, ihArgument]
  | case5 formula body ih =>
      simp [Binding.renameCertPayload, hasNamedMarkerB,
        hasNamedMarkerListB, namedMarkerHereB, ih]
  | case6 expression =>
      simp_all [Binding.renameCertPayload]

private theorem hasNamedMarkerB_renameCertPayload
    (sound : RenamingSound ρg program policy)
    (payload : Presentation.Sx)
    (_member : payloadBinderSpellings payload ⊆
      programBinderSpellings program) :
    hasNamedMarkerB (Binding.renameCertPayload ρg payload) =
      hasNamedMarkerB payload :=
  hasNamedMarkerB_renameCertPayload_core sound payload

private theorem namedFormulaValidB_renameCertPayload
    (sound : RenamingSound ρg program policy)
    (formula : Presentation.Sx) :
    namedFormulaValidB (Binding.renameCertPayload ρg formula) =
      namedFormulaValidB formula := by
  induction formula using Binding.renameCertPayload.induct with
  | case1 source =>
      simp [Binding.renameCertPayload, namedFormulaValidB,
        hasNamedMarkerB, hasNamedMarkerListB, namedMarkerHereB,
        Lara.Cell.Tag.toString, Lara.NDNamed.NamedTag.toString,
        Lara.ND.Tag.toString]
  | case2 formula body ih =>
      simpa [Binding.renameCertPayload, namedFormulaValidB] using
        congrArg Bool.not (hasNamedMarkerB_renameCertPayload_core sound
          (.node "lam" (.cons formula (.cons body .nil))))
  | case3 binder formula body ih =>
      simpa [Binding.renameCertPayload, namedFormulaValidB] using
        congrArg Bool.not (hasNamedMarkerB_renameCertPayload_core sound
          (.node "lam" (.cons binder (.cons formula (.cons body .nil)))))
  | case4 function argument ihFunction ihArgument =>
      simpa [Binding.renameCertPayload, namedFormulaValidB] using
        congrArg Bool.not (hasNamedMarkerB_renameCertPayload_core sound
          (.node "app" (.cons function (.cons argument .nil))))
  | case5 formula body ih =>
      simpa [Binding.renameCertPayload, namedFormulaValidB] using
        congrArg Bool.not (hasNamedMarkerB_renameCertPayload_core sound
          (.node "abort" (.cons formula (.cons body .nil))))
  | case6 expression =>
      simp_all [Binding.renameCertPayload]

private theorem namedNdExprValidB_renameCertPayload
    (sound : RenamingSound ρg program policy)
    (resolver resolverRenamed : String → Option Nat)
    (resolverCommutes : ∀ name,
      resolverRenamed (Binding.renameText ρg name) = resolver name)
    (premiseCount : Nat) (binders : List (Option String))
    (payload : Presentation.Sx)
    (bindersFixed : ∀ name, some name ∈ binders →
      Binding.renameText ρg name = name)
    (payloadBindersContained : payloadBinderSpellings payload ⊆
      programBinderSpellings program) :
    namedNdExprValidB resolverRenamed premiseCount
        binders (Binding.renameCertPayload ρg payload) =
      namedNdExprValidB resolver premiseCount binders payload := by
  induction payload using Binding.renameCertPayload.induct generalizing binders with
  | case1 source =>
      simp [Binding.renameCertPayload, namedNdExprValidB,
        sound.canonicalNat, sound.identifier, resolverCommutes]
  | case2 formula body ih =>
      simp_all [Binding.renameCertPayload, namedNdExprValidB,
        payloadBinderSpellings,
        namedFormulaValidB_renameCertPayload sound]
  | case3 binder formula body ih =>
      cases binder with
      | str binder =>
          have binderMember : binder ∈ programBinderSpellings program :=
            payloadBindersContained (by simp [payloadBinderSpellings])
          have fixed : Binding.renameText ρg binder = binder :=
            sound.certBinders binder binderMember
          have resolverFixed : resolverRenamed binder = resolver binder :=
            calc
              resolverRenamed binder =
                  resolverRenamed (Binding.renameText ρg binder) := by rw [fixed]
              _ = resolver binder := resolverCommutes binder
          simp_all [Binding.renameCertPayload, namedNdExprValidB,
            payloadBinderSpellings, namedFormulaValidB_renameCertPayload sound,
            resolverFixed]
      | int value =>
          simpa [Binding.renameCertPayload, namedNdExprValidB] using
            congrArg Bool.not (hasNamedMarkerB_renameCertPayload_core sound
              (.node "lam" (.cons (.int value)
                (.cons formula (.cons body .nil)))))
      | node tag children =>
          simpa [Binding.renameCertPayload, namedNdExprValidB] using
            congrArg Bool.not (hasNamedMarkerB_renameCertPayload_core sound
              (.node "lam" (.cons (.node tag children)
                (.cons formula (.cons body .nil)))))
  | case4 function argument ihFunction ihArgument =>
      simp_all [Binding.renameCertPayload, namedNdExprValidB,
        payloadBinderSpellings, sxListBinderSpellings,
        hasNamedMarkerB_renameCertPayload_core sound]
  | case5 formula body ih =>
      simp_all [Binding.renameCertPayload, namedNdExprValidB,
        payloadBinderSpellings, sxListBinderSpellings,
        namedFormulaValidB_renameCertPayload sound,
        hasNamedMarkerB_renameCertPayload_core sound]
  | case6 expression =>
      have unchanged : Binding.renameCertPayload ρg expression = expression := by
        simp_all [Binding.renameCertPayload]
      rw [unchanged]
      cases expression with
      | str source => rfl
      | int value => rfl
      | node tag children =>
          cases children with
          | nil => simp [namedNdExprValidB]
          | cons first rest =>
              cases rest with
              | nil =>
                  cases first with
                  | str source =>
                      by_cases thy : tag = "thy"
                      · subst tag; rfl
                      · by_cases hyp : tag = "hyp"
                        · subst tag; rfl
                        · simp_all [namedNdExprValidB]
                  | int value => simp [namedNdExprValidB]
                  | node childTag childList => simp [namedNdExprValidB]
              | cons second rest =>
                  cases rest with
                  | nil => simp_all [namedNdExprValidB]
                  | cons third rest =>
                      cases rest with
                      | nil =>
                          by_cases lam : tag = "lam"
                          · subst tag
                            simp_all
                          · simp_all [namedNdExprValidB]
                      | cons fourth rest => simp [namedNdExprValidB]
private theorem namedNdValidB_renameCertPayload
    (sound : RenamingSound ρg program policy)
    (resolver resolverRenamed : String → Option Nat)
    (resolverCommutes : ∀ name,
      resolverRenamed (Binding.renameText ρg name) = resolver name)
    (premiseCount : Nat) (payload : Presentation.Sx)
    (payloadBindersContained : payloadBinderSpellings payload ⊆
      programBinderSpellings program) :
    namedNdValidB resolverRenamed premiseCount
        (Binding.renameCertPayload ρg payload) =
      namedNdValidB resolver premiseCount payload := by
  unfold namedNdValidB
  rw [hasNamedMarkerB_renameCertPayload sound payload
    payloadBindersContained]
  split
  · exact namedNdExprValidB_renameCertPayload sound resolver resolverRenamed
      resolverCommutes premiseCount [] payload (by simp)
      payloadBindersContained
  · rfl

theorem hasSymbolicRef_renameCertPayload
    (sound : RenamingSound ρg program policy) (payload : Presentation.Sx) :
    Lara.CertSlots.hasSymbolicRef
        (sxToSExpr (Binding.renameCertPayload ρg payload)) =
      Lara.CertSlots.hasSymbolicRef (sxToSExpr payload) := by
  induction payload using Binding.renameCertPayload.induct with
  | case1 source =>
      simp [Binding.renameCertPayload, sxToSExpr, sxListToSExprs,
        Lara.CertSlots.hasSymbolicRef,
        Lara.CertSlots.hasSymbolicRefList,
        Lara.CertSlots.symbolicRefName, sound.cellCanonNat]
      cases Lara.Cell.parseCanonNat source <;> rfl
  | case2 formula body ih =>
      simp_all [Binding.renameCertPayload, sxToSExpr, sxListToSExprs,
        Lara.CertSlots.hasSymbolicRef, Lara.CertSlots.hasSymbolicRefList,
        Lara.CertSlots.symbolicRefName]
  | case3 binder formula body ih =>
      simp_all [Binding.renameCertPayload, sxToSExpr, sxListToSExprs,
        Lara.CertSlots.hasSymbolicRef, Lara.CertSlots.hasSymbolicRefList,
        Lara.CertSlots.symbolicRefName]
  | case4 function argument ihFunction ihArgument =>
      simp_all [Binding.renameCertPayload, sxToSExpr, sxListToSExprs,
        Lara.CertSlots.hasSymbolicRef, Lara.CertSlots.hasSymbolicRefList,
        Lara.CertSlots.symbolicRefName]
  | case5 formula body ih =>
      simp_all [Binding.renameCertPayload, sxToSExpr, sxListToSExprs,
        Lara.CertSlots.hasSymbolicRef, Lara.CertSlots.hasSymbolicRefList,
        Lara.CertSlots.symbolicRefName]
  | case6 expression =>
      simp_all [Binding.renameCertPayload]

private theorem cellParseCanonNat_repr (value : Nat) :
    Lara.Cell.parseCanonNat (Nat.repr value) = some value := by
  simp [Lara.Cell.parseCanonNat]

private theorem symbolicRefName_sx_mem
    (expression : Presentation.Sx) (name : String)
    (found : Lara.CertSlots.symbolicRefName (sxToSExpr expression) = some name)
    (accepted : Lara.CertSlots.numeralTypo sourceStartsIdentifier name = false) :
    name ∈ Binding.allPayloadPremiseSpellings expression := by
  cases expression with
  | str source => simp [sxToSExpr, Lara.CertSlots.symbolicRefName] at found
  | int value => simp [sxToSExpr, Lara.CertSlots.symbolicRefName] at found
  | node tag children =>
      cases children with
      | nil =>
          simp [sxToSExpr, sxListToSExprs,
            Lara.CertSlots.symbolicRefName] at found
      | cons first rest =>
          cases rest with
          | cons second tail =>
              simp [sxToSExpr, sxListToSExprs,
                Lara.CertSlots.symbolicRefName] at found
          | nil =>
              cases first with
              | str source =>
                  by_cases prem : tag = "prem"
                  · subst tag
                    cases parsed : Lara.Cell.parseCanonNat source with
                    | none =>
                        simp [sxToSExpr, sxListToSExprs,
                          Lara.CertSlots.symbolicRefName,
                          Lara.Cell.Tag.parse, Lara.Cell.Tag.all,
                          Lara.Cell.Tag.toString, parsed] at found
                        subst name
                        simp [Binding.allPayloadPremiseSpellings]
                    | some value =>
                        simp [sxToSExpr, sxListToSExprs,
                          Lara.CertSlots.symbolicRefName,
                          Lara.Cell.Tag.parse, Lara.Cell.Tag.all,
                          Lara.Cell.Tag.toString, parsed] at found
                  · have prem' : ¬"prem" = tag := fun equal => prem equal.symm
                    simp [sxToSExpr, sxListToSExprs,
                      Lara.CertSlots.symbolicRefName,
                      Lara.Cell.Tag.parse, Lara.Cell.Tag.all,
                      Lara.Cell.Tag.toString, prem'] at found
              | int value =>
                  cases value with
                  | ofNat value =>
                      simp [sxToSExpr, sxListToSExprs,
                        Lara.CertSlots.symbolicRefName,
                        Lara.Cell.Tag.parse, Lara.Cell.Tag.all,
                        Lara.Cell.Tag.toString, Int.repr,
                        cellParseCanonNat_repr] at found
                      split at found <;> simp_all
                  | negSucc value =>
                      by_cases prem : "prem" = tag
                      · cases parsed : Lara.Cell.parseCanonNat
                            ("-" ++ Nat.repr (value + 1)) with
                        | some parsedValue =>
                            simp [sxToSExpr, sxListToSExprs,
                              Lara.CertSlots.symbolicRefName,
                              Lara.Cell.Tag.parse, Lara.Cell.Tag.all,
                              Lara.Cell.Tag.toString, Int.repr, prem,
                              parsed] at found
                        | none =>
                            simp [sxToSExpr, sxListToSExprs,
                              Lara.CertSlots.symbolicRefName,
                              Lara.Cell.Tag.parse, Lara.Cell.Tag.all,
                              Lara.Cell.Tag.toString, Int.repr, prem,
                              parsed] at found
                            subst name
                            simp [Lara.CertSlots.numeralTypo,
                              sourceStartsIdentifier, sourceAlphaB,
                              asciiAlphaB] at accepted
                      · simp [sxToSExpr, sxListToSExprs,
                          Lara.CertSlots.symbolicRefName,
                          Lara.Cell.Tag.parse, Lara.Cell.Tag.all,
                          Lara.Cell.Tag.toString, Int.repr, prem] at found
              | node childTag childChildren =>
                  simp [sxToSExpr, sxListToSExprs,
                    Lara.CertSlots.symbolicRefName] at found

private theorem lowerAt_sx_resolver_fixed
    (sound : RenamingSound ρg program policy)
    (resolver resolverRenamed : String → Option Nat)
    (resolverCommutes : ∀ name,
      resolverRenamed (Binding.renameText ρg name) = resolver name)
    (schema : Lara.CertSlots.SlotSchema) (index : Nat)
    (expression : Presentation.Sx)
    (contained : Binding.allPayloadPremiseSpellings expression ⊆
      programOpaqueCertPremiseSpellings program) :
    Lara.CertSlots.lowerAt sourceStartsIdentifier resolverRenamed schema index
        (sxToSExpr expression) =
      Lara.CertSlots.lowerAt sourceStartsIdentifier resolver schema index
        (sxToSExpr expression) := by
  have resolverFixed : ∀ name,
      name ∈ Binding.allPayloadPremiseSpellings expression →
      resolverRenamed name = resolver name := by
    intro name member
    have fixed := sound.opaqueCertPremises name (contained member)
    calc
      resolverRenamed name =
          resolverRenamed (Binding.renameText ρg name) := by rw [fixed]
      _ = resolver name := resolverCommutes name
  unfold Lara.CertSlots.lowerAt
  split
  · generalize found : Lara.CertSlots.symbolicRefName
        (sxToSExpr expression) = symbolic
    cases symbolic with
    | none => rfl
    | some name =>
        simp only [found]
        cases accepted : Lara.CertSlots.numeralTypo
            sourceStartsIdentifier name with
        | true => rfl
        | false =>
            simp only [accepted, Bool.false_eq_true, if_false]
            rw [resolverFixed name
              (symbolicRefName_sx_mem expression name found accepted)]
  · rfl

private theorem lowerArgs_sx_resolver_fixed
    (sound : RenamingSound ρg program policy)
    (resolver resolverRenamed : String → Option Nat)
    (resolverCommutes : ∀ name,
      resolverRenamed (Binding.renameText ρg name) = resolver name)
    (schema : Lara.CertSlots.SlotSchema) (index : Nat)
    (expressions : Presentation.SxList)
    (contained : Binding.allPayloadPremiseSpellingsList expressions ⊆
      programOpaqueCertPremiseSpellings program) :
    Lara.CertSlots.lowerArgs sourceStartsIdentifier resolverRenamed schema index
        (sxListToSExprs expressions) =
      Lara.CertSlots.lowerArgs sourceStartsIdentifier resolver schema index
        (sxListToSExprs expressions) := by
  cases expressions with
  | nil => rfl
  | cons expression rest =>
      simp only [sxListToSExprs, Lara.CertSlots.lowerArgs]
      rw [lowerAt_sx_resolver_fixed sound resolver resolverRenamed
        resolverCommutes schema index expression (fun name member =>
          contained (by
            simp only [Binding.allPayloadPremiseSpellingsList,
              List.mem_append]
            exact Or.inl member))]
      rw [lowerArgs_sx_resolver_fixed sound resolver resolverRenamed
        resolverCommutes schema (index + 1) rest (fun name member =>
          contained (by
            simp only [Binding.allPayloadPremiseSpellingsList,
              List.mem_append]
            exact Or.inr member))]

theorem lowerPayload_sx_resolver_fixed
    (sound : RenamingSound ρg program policy)
    (resolver resolverRenamed : String → Option Nat)
    (resolverCommutes : ∀ name,
      resolverRenamed (Binding.renameText ρg name) = resolver name)
    (backend : String) (version : Nat) (payload : Presentation.Sx)
    (contained : ∀ tag children, payload = .node tag children →
      Binding.allPayloadPremiseSpellingsList children ⊆
        programOpaqueCertPremiseSpellings program) :
    Lara.CertSlots.lowerPayload sourceStartsIdentifier resolverRenamed
        backend version (sxToSExpr payload) =
      Lara.CertSlots.lowerPayload sourceStartsIdentifier resolver
        backend version (sxToSExpr payload) := by
  cases payload with
  | str source => rfl
  | int value => rfl
  | node tag children =>
      unfold Lara.CertSlots.lowerPayload Lara.CertSlots.matchSchema
      simp only [sxToSExpr]
      generalize selected :
          (Lara.CertSlots.schemasFor backend version).filter
            (fun schema =>
              schema.head == tag &&
                schema.arity == (sxListToSExprs children).length) =
            selectedSchemas
      cases selectedSchemas with
      | nil => rfl
      | cons schema rest =>
          cases rest with
          | nil =>
              simp only
              rw [lowerArgs_sx_resolver_fixed sound resolver resolverRenamed
                resolverCommutes schema 0 children
                (contained tag children rfl)]
          | cons next tail => rfl

theorem opaqueDefault_node_children_contained
    (tag : String) (children : Presentation.SxList)
    (notPrem : ∀ source, (.node tag children : Presentation.Sx) ≠
      .node "prem" (.cons (.str source) .nil))
    (contained : Binding.allPayloadPremiseSpellings (.node tag children) ⊆
      programOpaqueCertPremiseSpellings program) :
    Binding.allPayloadPremiseSpellingsList children ⊆
      programOpaqueCertPremiseSpellings program := by
  rw [Binding.allPayloadPremiseSpellings.eq_2 tag children (by
    intro source tagEq childrenEq
    apply notPrem source
    rw [tagEq, childrenEq])] at contained
  exact contained

theorem lowerPayload_isSome_renameCertPayload
    (sound : RenamingSound ρg program policy)
    (resolver resolverRenamed : String → Option Nat)
    (resolverCommutes : ∀ name,
      resolverRenamed (Binding.renameText ρg name) = resolver name)
    (backend : String) (version : Nat) (payload : Presentation.Sx)
    (_opaqueContained : Binding.opaquePayloadPremiseSpellings payload ⊆
      programOpaqueCertPremiseSpellings program) :
    (Lara.CertSlots.lowerPayload sourceStartsIdentifier resolverRenamed
        backend version (sxToSExpr (Binding.renameCertPayload ρg payload))).isSome =
      (Lara.CertSlots.lowerPayload sourceStartsIdentifier resolver
        backend version (sxToSExpr payload)).isSome := by
  induction payload using Binding.renameCertPayload.induct with
  | case1 source =>
      have symbolic := hasSymbolicRef_renameCertPayload sound
        (.node "prem" (.cons (.str source) .nil))
      have renamedMatch : Lara.CertSlots.matchSchema backend version
          (sxToSExpr (Binding.renameCertPayload ρg
            (.node "prem" (.cons (.str source) .nil)))) = none := by
        simp [Binding.renameCertPayload, sxToSExpr,
          Lara.CertSlots.matchSchema, Lara.CertSlots.schemasFor,
          Lara.CertSlots.slotSchemas, Lara.CertSlots.ordSlotSchema,
          Lara.CertSlots.raSlotSchema, Lara.Ord.Tag.toString,
          Lara.RA.Tag.toString]
      have originalMatch : Lara.CertSlots.matchSchema backend version
          (sxToSExpr (.node "prem" (.cons (.str source) .nil))) = none := by
        simp [sxToSExpr, Lara.CertSlots.matchSchema,
          Lara.CertSlots.schemasFor, Lara.CertSlots.slotSchemas,
          Lara.CertSlots.ordSlotSchema, Lara.CertSlots.raSlotSchema,
          Lara.Ord.Tag.toString, Lara.RA.Tag.toString]
      simp only [Lara.CertSlots.lowerPayload, renamedMatch, originalMatch]
      rw [symbolic]
      split <;> rfl
  | case2 formula body ih =>
      have symbolic := hasSymbolicRef_renameCertPayload sound
        (.node "lam" (.cons formula (.cons body .nil)))
      have renamedMatch : Lara.CertSlots.matchSchema backend version
          (sxToSExpr (Binding.renameCertPayload ρg
            (.node "lam" (.cons formula (.cons body .nil))))) = none := by
        simp [Binding.renameCertPayload, sxToSExpr, sxListToSExprs,
          Lara.CertSlots.matchSchema, Lara.CertSlots.schemasFor,
          Lara.CertSlots.slotSchemas, Lara.CertSlots.ordSlotSchema,
          Lara.CertSlots.raSlotSchema, Lara.Ord.Tag.toString,
          Lara.RA.Tag.toString]
      have originalMatch : Lara.CertSlots.matchSchema backend version
          (sxToSExpr (.node "lam" (.cons formula (.cons body .nil)))) =
            none := by
        simp [sxToSExpr, sxListToSExprs, Lara.CertSlots.matchSchema,
          Lara.CertSlots.schemasFor, Lara.CertSlots.slotSchemas,
          Lara.CertSlots.ordSlotSchema, Lara.CertSlots.raSlotSchema,
          Lara.Ord.Tag.toString, Lara.RA.Tag.toString]
      simp only [Lara.CertSlots.lowerPayload, renamedMatch, originalMatch]
      rw [symbolic]
      split <;> rfl
  | case3 binder formula body ih =>
      have symbolic := hasSymbolicRef_renameCertPayload sound
        (.node "lam" (.cons binder (.cons formula (.cons body .nil))))
      have renamedMatch : Lara.CertSlots.matchSchema backend version
          (sxToSExpr (Binding.renameCertPayload ρg
            (.node "lam"
              (.cons binder (.cons formula (.cons body .nil)))))) = none := by
        simp [Binding.renameCertPayload, sxToSExpr, sxListToSExprs,
          Lara.CertSlots.matchSchema, Lara.CertSlots.schemasFor,
          Lara.CertSlots.slotSchemas, Lara.CertSlots.ordSlotSchema,
          Lara.CertSlots.raSlotSchema, Lara.Ord.Tag.toString,
          Lara.RA.Tag.toString]
      have originalMatch : Lara.CertSlots.matchSchema backend version
          (sxToSExpr (.node "lam"
            (.cons binder (.cons formula (.cons body .nil))))) = none := by
        simp [sxToSExpr, sxListToSExprs, Lara.CertSlots.matchSchema,
          Lara.CertSlots.schemasFor, Lara.CertSlots.slotSchemas,
          Lara.CertSlots.ordSlotSchema, Lara.CertSlots.raSlotSchema,
          Lara.Ord.Tag.toString, Lara.RA.Tag.toString]
      simp only [Lara.CertSlots.lowerPayload, renamedMatch, originalMatch]
      rw [symbolic]
      split <;> rfl
  | case4 function argument ihFunction ihArgument =>
      have symbolic := hasSymbolicRef_renameCertPayload sound
        (.node "app" (.cons function (.cons argument .nil)))
      have renamedMatch : Lara.CertSlots.matchSchema backend version
          (sxToSExpr (Binding.renameCertPayload ρg
            (.node "app" (.cons function (.cons argument .nil))))) = none := by
        simp [Binding.renameCertPayload, sxToSExpr, sxListToSExprs,
          Lara.CertSlots.matchSchema, Lara.CertSlots.schemasFor,
          Lara.CertSlots.slotSchemas, Lara.CertSlots.ordSlotSchema,
          Lara.CertSlots.raSlotSchema, Lara.Ord.Tag.toString,
          Lara.RA.Tag.toString]
      have originalMatch : Lara.CertSlots.matchSchema backend version
          (sxToSExpr (.node "app"
            (.cons function (.cons argument .nil)))) = none := by
        simp [sxToSExpr, sxListToSExprs, Lara.CertSlots.matchSchema,
          Lara.CertSlots.schemasFor, Lara.CertSlots.slotSchemas,
          Lara.CertSlots.ordSlotSchema, Lara.CertSlots.raSlotSchema,
          Lara.Ord.Tag.toString, Lara.RA.Tag.toString]
      simp only [Lara.CertSlots.lowerPayload, renamedMatch, originalMatch]
      rw [symbolic]
      split <;> rfl
  | case5 formula body ih =>
      have symbolic := hasSymbolicRef_renameCertPayload sound
        (.node "abort" (.cons formula (.cons body .nil)))
      have renamedMatch : Lara.CertSlots.matchSchema backend version
          (sxToSExpr (Binding.renameCertPayload ρg
            (.node "abort" (.cons formula (.cons body .nil))))) = none := by
        simp [Binding.renameCertPayload, sxToSExpr, sxListToSExprs,
          Lara.CertSlots.matchSchema, Lara.CertSlots.schemasFor,
          Lara.CertSlots.slotSchemas, Lara.CertSlots.ordSlotSchema,
          Lara.CertSlots.raSlotSchema, Lara.Ord.Tag.toString,
          Lara.RA.Tag.toString]
      have originalMatch : Lara.CertSlots.matchSchema backend version
          (sxToSExpr (.node "abort"
            (.cons formula (.cons body .nil)))) = none := by
        simp [sxToSExpr, sxListToSExprs, Lara.CertSlots.matchSchema,
          Lara.CertSlots.schemasFor, Lara.CertSlots.slotSchemas,
          Lara.CertSlots.ordSlotSchema, Lara.CertSlots.raSlotSchema,
          Lara.Ord.Tag.toString, Lara.RA.Tag.toString]
      simp only [Lara.CertSlots.lowerPayload, renamedMatch, originalMatch]
      rw [symbolic]
      split <;> rfl
  | case6 expression notPrem notLam notNamedLam notApp notAbort =>
      have unchanged : Binding.renameCertPayload ρg expression = expression := by
        simp_all [Binding.renameCertPayload]
      rw [unchanged]
      have opaqueEq : Binding.opaquePayloadPremiseSpellings expression =
          Binding.allPayloadPremiseSpellings expression := by
        simp_all [Binding.opaquePayloadPremiseSpellings]
      rw [opaqueEq] at _opaqueContained
      exact congrArg Option.isSome
        (lowerPayload_sx_resolver_fixed sound resolver resolverRenamed
          resolverCommutes backend version expression (by
            intro tag children equal
            subst expression
            exact opaqueDefault_node_children_contained tag children
              notPrem _opaqueContained))

private theorem certificateFormValidB_rename
    (sound : RenamingSound ρg program policy)
    (rule : Presentation.Rule) (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm)
    (certificate : Presentation.Cert)
    (binderContained : payloadBinderSpellings certificate.payload ⊆
      programBinderSpellings program)
    (opaqueContained : Binding.opaquePayloadPremiseSpellings certificate.payload ⊆
      programOpaqueCertPremiseSpellings program) :
    certificateFormValidB (Binding.renameProgram ρg program)
        (Binding.renameRule ρg rule)
        (priors.map (renamePriorArgument ρg))
        (premises.map (renameResidualSupportTerm ρg))
        { certificate with payload :=
            Binding.renameCertPayload ρg certificate.payload } =
      certificateFormValidB program rule priors premises certificate := by
  cases certificate with
  | mk backend version theory payload =>
      cases version with
      | negSucc n => rfl
      | ofNat version =>
          simp only [certificateFormValidB, List.length_map]
          have resolverCommutes : ∀ name,
              certificateResolver (Binding.renameProgram ρg program)
                  (Binding.renameRule ρg rule)
                  (priors.map (renamePriorArgument ρg))
                  (premises.map (renameResidualSupportTerm ρg))
                  (Binding.renameText ρg name) =
                certificateResolver program rule priors premises name :=
            certificateResolver_rename sound rule priors premises
          by_cases named : backend.val == "nd" && version == 1
          · simp only [named, if_true]
            exact namedNdValidB_renameCertPayload sound _ _
              resolverCommutes premises.length payload binderContained
          · simp only [named, if_false]
            exact lowerPayload_isSome_renameCertPayload sound _ _
              resolverCommutes backend.val version payload opaqueContained

private theorem assuranceFormValidB_rename
    (sound : RenamingSound ρg program policy)
    (rule : Presentation.Rule) (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm)
    (assurance : Presentation.Assurance)
    (binderContained : assuranceBinderSpellings assurance ⊆
      programBinderSpellings program)
    (opaqueContained : assuranceOpaqueCertPremiseSpellings assurance ⊆
      programOpaqueCertPremiseSpellings program) :
    assuranceFormValidB (Binding.renameProgram ρg program)
        (Binding.renameRule ρg rule)
        (priors.map (renamePriorArgument ρg))
        (premises.map (renameResidualSupportTerm ρg))
        (Binding.renameAssurance ρg assurance) =
      assuranceFormValidB program rule priors premises assurance := by
  cases assurance with
  | none => rfl
  | trusted => rfl
  | cert certificate =>
      exact certificateFormValidB_rename sound rule priors premises certificate
        binderContained opaqueContained

mutual
  private theorem termCertificatesValidB_rename
      (sound : RenamingSound ρg program policy)
      (priors : List PriorArgument) (term : Presentation.SupportTerm)
      (binderContained : supportTermBinderSpellings term ⊆
        programBinderSpellings program)
      (opaqueContained : supportTermOpaqueCertPremiseSpellings term ⊆
        programOpaqueCertPremiseSpellings program) :
    termCertificatesValidB (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (priors.map (renamePriorArgument ρg))
        (renameResidualSupportTerm ρg term) =
      termCertificatesValidB program policy priors term := by
    cases term with
    | leaf leafId => rfl
    | rule ruleId substitution premises discharges conclusion assurance =>
        simp only [renameResidualSupportTerm, termCertificatesValidB]
        rw [ruleById_rename]
        cases found : ruleById policy ruleId with
        | none => rfl
        | some rule =>
            simp only [Option.map_some]
            rw [supportTermsToList_rename]
            rw [assuranceFormValidB_rename sound rule priors
              (supportTermsToList premises) assurance (by
                intro spelling member
                exact binderContained (by
                  simp only [supportTermBinderSpellings, List.mem_append]
                  exact Or.inl (Or.inl member))) (by
                intro spelling member
                exact opaqueContained (by
                  simp only [supportTermOpaqueCertPremiseSpellings,
                    List.mem_append]
                  exact Or.inl (Or.inl member)))]
            rw [supportTermsCertificatesValidB_rename sound priors premises (by
              intro spelling member
              exact binderContained (by
                simp only [supportTermBinderSpellings, List.mem_append]
                exact Or.inl (Or.inr member))) (by
              intro spelling member
              exact opaqueContained (by
                simp only [supportTermOpaqueCertPremiseSpellings,
                  List.mem_append]
                exact Or.inl (Or.inr member)))]
            rw [supportDischargesCertificatesValidB_rename sound priors
              discharges (by
                intro spelling member
                exact binderContained (by
                  simp only [supportTermBinderSpellings, List.mem_append]
                  exact Or.inr member)) (by
                intro spelling member
                exact opaqueContained (by
                  simp only [supportTermOpaqueCertPremiseSpellings,
                    List.mem_append]
                  exact Or.inr member))]
  private theorem supportTermsCertificatesValidB_rename
      (sound : RenamingSound ρg program policy)
      (priors : List PriorArgument) (terms : Presentation.SupportTerms)
      (binderContained : supportTermsBinderSpellings terms ⊆
        programBinderSpellings program)
      (opaqueContained : supportTermsOpaqueCertPremiseSpellings terms ⊆
        programOpaqueCertPremiseSpellings program) :
    supportTermsCertificatesValidB (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (priors.map (renamePriorArgument ρg))
        (renameResidualSupportTerms ρg terms) =
      supportTermsCertificatesValidB program policy priors terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp only [renameResidualSupportTerms,
          supportTermsCertificatesValidB]
        rw [termCertificatesValidB_rename sound priors term (by
          intro spelling member
          exact binderContained (by
            simp only [supportTermsBinderSpellings, List.mem_append]
            exact Or.inl member)) (by
          intro spelling member
          exact opaqueContained (by
            simp only [supportTermsOpaqueCertPremiseSpellings,
              List.mem_append]
            exact Or.inl member))]
        rw [supportTermsCertificatesValidB_rename sound priors rest (by
          intro spelling member
          exact binderContained (by
            simp only [supportTermsBinderSpellings, List.mem_append]
            exact Or.inr member)) (by
          intro spelling member
          exact opaqueContained (by
            simp only [supportTermsOpaqueCertPremiseSpellings,
              List.mem_append]
            exact Or.inr member))]
  private theorem supportDischargesCertificatesValidB_rename
      (sound : RenamingSound ρg program policy)
      (priors : List PriorArgument) (discharges : Presentation.Discharges)
      (binderContained : supportDischargesBinderSpellings discharges ⊆
        programBinderSpellings program)
      (opaqueContained : dischargeOpaqueCertPremiseSpellings discharges ⊆
        programOpaqueCertPremiseSpellings program) :
    supportDischargesCertificatesValidB (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (priors.map (renamePriorArgument ρg))
        (renameResidualDischarges ρg discharges) =
      supportDischargesCertificatesValidB program policy priors discharges := by
    cases discharges with
    | nil => rfl
    | cons question term rest =>
        simp only [renameResidualDischarges,
          supportDischargesCertificatesValidB]
        rw [termCertificatesValidB_rename sound priors term (by
          intro spelling member
          exact binderContained (by
            simp only [supportDischargesBinderSpellings, List.mem_append]
            exact Or.inl member)) (by
          intro spelling member
          exact opaqueContained (by
            simp only [dischargeOpaqueCertPremiseSpellings, List.mem_append]
            exact Or.inl member))]
        rw [supportDischargesCertificatesValidB_rename sound priors rest (by
          intro spelling member
          exact binderContained (by
            simp only [supportDischargesBinderSpellings, List.mem_append]
            exact Or.inr member)) (by
          intro spelling member
          exact opaqueContained (by
            simp only [dischargeOpaqueCertPremiseSpellings, List.mem_append]
            exact Or.inr member))]
end

private theorem validateCertificates_rename
    (sound : RenamingSound ρg program policy)
    (declarations : List Presentation.Decl) (priors : List PriorArgument)
    (contained : ∀ declaration ∈ declarations, declaration ∈ program.decls)
    (safe : PriorPayloadsFromProgram program priors) :
    validateCertificates (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (declarations.map
          (Binding.renameDecl ρg (programValues program)))
        (priors.map (renamePriorArgument ρg)) =
      validateCertificates program policy declarations priors := by
  induction declarations generalizing priors with
  | nil => rfl
  | cons declaration rest ih =>
      have headMember : declaration ∈ program.decls :=
        contained declaration (by simp)
      have tailContained : ∀ candidate ∈ rest,
          candidate ∈ program.decls := by
        intro candidate candidateMember
        exact contained candidate (by simp [candidateMember])
      cases declaration with
      | leaf leaf =>
          simp only [List.map_cons, Binding.renameDecl, validateCertificates]
          exact ih priors tailContained safe
      | claim claim =>
          simp only [List.map_cons, Binding.renameDecl, validateCertificates]
          exact ih priors tailContained safe
      | arg argument =>
          simp only [List.map_cons, Binding.renameDecl, validateCertificates]
          rw [buildArgument_rename sound priors argument headMember]
          cases built : buildArgument program policy priors argument with
          | none => exact ih priors tailContained safe
          | some prior =>
              simp only [Option.map_some]
              change
                (termCertificatesValidB (Binding.renameProgram ρg program)
                    (Binding.renamePolicy ρg policy)
                    (priors.map (renamePriorArgument ρg))
                    (renameResidualSupportTerm ρg prior.term) &&
                  _) = _
              have safeNext := buildArgument_preserves_priorPayloads
                safe headMember built
              have priorSafe := safeNext prior (by simp)
              rw [termCertificatesValidB_rename sound priors prior.term
                priorSafe.1 priorSafe.2]
              exact congrArg
                (fun result =>
                  termCertificatesValidB program policy priors prior.term &&
                    result) (by
                  simpa [List.map_append] using
                    ih (priors ++ [prior]) tailContained safeNext)
      | attack attack =>
          simp only [List.map_cons, Binding.renameDecl, validateCertificates]
          exact ih priors tailContained safe
      | status status =>
          simp only [List.map_cons, Binding.renameDecl, validateCertificates]
          exact ih priors tailContained safe
      | group group =>
          simp only [List.map_cons, Binding.renameDecl, validateCertificates]
          exact ih priors tailContained safe
      | comparison comparison =>
          simp only [List.map_cons, Binding.renameDecl, validateCertificates]
          rw [generatedComparisonArguments_rename sound comparison headMember]
          cases generated : generatedComparisonArguments program policy comparison with
          | none =>
              simp only [Option.map_none]
              exact ih priors tailContained safe
          | some pair =>
              simp only [Option.map_some]
              have safeNext := generatedComparisonArguments_preserve_priorPayloads
                safe headMember generated
              simpa [List.map_append] using
                ih (priors ++ [pair.1, pair.2]) tailContained safeNext

theorem namedCertificatesWellFormedB_rename
    (sound : RenamingSound ρg program policy) :
    namedCertificatesWellFormedB (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy) =
      namedCertificatesWellFormedB program policy := by
  unfold namedCertificatesWellFormedB
  change validateCertificates (Binding.renameProgram ρg program)
      (Binding.renamePolicy ρg policy)
      (program.decls.map
        (Binding.renameDecl ρg (programValues program))) [] =
    validateCertificates program policy program.decls []
  exact validateCertificates_rename sound program.decls []
    (by intro declaration member; exact member)
    (priorPayloadsFromProgram_nil program)

/-! #### Surface-attack validator transport -/

theorem collectProgramArguments_rename
    (sound : RenamingSound ρg program policy)
    (declarations : List Presentation.Decl) (priors : List PriorArgument)
    (contained : ∀ declaration ∈ declarations,
      declaration ∈ program.decls) :
    collectProgramArguments (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (declarations.map
          (Binding.renameDecl ρg (programValues program)))
        (priors.map (renamePriorArgument ρg)) =
      (collectProgramArguments program policy declarations priors).map
        (renamePriorArgument ρg) := by
  induction declarations generalizing priors with
  | nil => rfl
  | cons declaration rest ih =>
      have headMember : declaration ∈ program.decls :=
        contained declaration (by simp)
      have tailContained :
          ∀ candidate ∈ rest, candidate ∈ program.decls := by
        intro candidate candidateMember
        exact contained candidate (by simp [candidateMember])
      cases declaration with
      | leaf leaf =>
          simp only [List.map_cons, Binding.renameDecl,
            collectProgramArguments]
          exact ih priors tailContained
      | claim claim =>
          simp only [List.map_cons, Binding.renameDecl,
            collectProgramArguments]
          exact ih priors tailContained
      | arg argument =>
          simp only [List.map_cons, Binding.renameDecl,
            collectProgramArguments]
          rw [buildArgument_rename sound priors argument headMember]
          cases built : buildArgument program policy priors argument with
          | none =>
              simp only [Option.map_none]
              exact ih priors tailContained
          | some prior =>
              simpa [List.map_append, built] using
                ih (priors ++ [prior]) tailContained
      | attack attack =>
          simp only [List.map_cons, Binding.renameDecl,
            collectProgramArguments]
          exact ih priors tailContained
      | status status =>
          simp only [List.map_cons, Binding.renameDecl,
            collectProgramArguments]
          exact ih priors tailContained
      | group group =>
          simp only [List.map_cons, Binding.renameDecl,
            collectProgramArguments]
          exact ih priors tailContained
      | comparison comparison =>
          simp only [List.map_cons, Binding.renameDecl,
            collectProgramArguments]
          rw [generatedComparisonArguments_rename sound comparison
            headMember]
          cases generated :
              generatedComparisonArguments program policy comparison with
          | none =>
              simp only [Option.map_none]
              exact ih priors tailContained
          | some pair =>
              simpa [List.map_append, generated] using
                ih (priors ++ [pair.1, pair.2]) tailContained

private theorem premiseAt?_map
    (f : Presentation.SupportTerm → Presentation.SupportTerm)
    (premises : List Presentation.SupportTerm) (index : Int) :
    premiseAt? (premises.map f) index =
      (premiseAt? premises index).map f := by
  unfold premiseAt?
  by_cases negative : index < 0
  · simp [negative]
  · simp [negative]

private theorem dischargeByQuestion?_rename
    (ρg : Binding.GlobalRenaming)
    (discharges :
      List (Presentation.QuestionId × Presentation.SupportTerm))
    (question : Presentation.QuestionId) :
    dischargeByQuestion?
        (discharges.map fun entry =>
          (ρg.question entry.1, renameResidualSupportTerm ρg entry.2))
        (ρg.question question) =
      (dischargeByQuestion? discharges question).map
        (renameResidualSupportTerm ρg) := by
  induction discharges with
  | nil => rfl
  | cons entry rest ih =>
      unfold dischargeByQuestion? at ih ⊢
      simp only [List.map_cons, List.findSome?_cons]
      by_cases equal : entry.1 = question
      · have renamedEqual : ρg.question entry.1 = ρg.question question :=
          congrArg ρg.question equal
        rw [if_pos renamedEqual, if_pos equal]
        rfl
      · have renamedNe : ρg.question entry.1 ≠ ρg.question question :=
          fun h => equal (ρg.question_injective h)
        rw [if_neg renamedNe, if_neg equal]
        exact ih

theorem questionByName?_rename
    (ρg : Binding.GlobalRenaming)
    (questions : List Presentation.QuestionId) (name : String) :
    (questions.map ρg.question).find?
        (fun question =>
          question.val == Binding.renameText ρg name) =
      (questions.find? (fun question => question.val == name)).map
        ρg.question := by
  induction questions with
  | nil => rfl
  | cons question rest ih =>
      simp only [List.map_cons, List.find?_cons]
      by_cases equal : question.val = name
      · have renamedEqual :
            (ρg.question question).val =
              Binding.renameText ρg name := by
          simp [Binding.renameText, equal]
        have originalTest : (question.val == name) = true :=
          beq_iff_eq.mpr equal
        have renamedTest :
            ((ρg.question question).val ==
              Binding.renameText ρg name) = true :=
          beq_iff_eq.mpr renamedEqual
        simp only [originalTest, renamedTest, if_true, Option.map_some]
      · have renamedNe :
            (ρg.question question).val ≠
              Binding.renameText ρg name := by
          intro h
          apply equal
          apply Binding.renameText_injective ρg
          simpa [Binding.renameText] using h
        have originalTest : (question.val == name) = false :=
          beq_eq_false_iff_ne.mpr equal
        have renamedTest :
            ((ρg.question question).val ==
              Binding.renameText ρg name) = false :=
          beq_eq_false_iff_ne.mpr renamedNe
        simp only [originalTest, renamedTest, Bool.false_eq_true, if_false]
        simpa only [Function.comp_apply] using ih

private theorem nextOccurrence?_rename
    (sound : RenamingSound ρg program policy)
    (term : Presentation.SupportTerm)
    (step : Presentation.SurfaceStep) :
    nextOccurrence? (Binding.renamePolicy ρg policy)
        (renameResidualSupportTerm ρg term)
        (Binding.renameSurfaceStep ρg step) =
      (nextOccurrence? policy term step).map
        (renameResidualSupportTerm ρg) := by
  cases step with
  | index index =>
      cases term with
      | leaf leaf => rfl
      | rule rule subst premises discharges holes assurance =>
          simp only [Binding.renameSurfaceStep, renameResidualSupportTerm,
            nextOccurrence?]
          rw [supportTermsToList_rename, premiseAt?_map]
  | name name =>
      cases term with
      | leaf leaf => rfl
      | rule ruleId subst premises discharges holes assurance =>
          simp only [Binding.renameSurfaceStep, renameResidualSupportTerm,
            nextOccurrence?]
          rw [ruleById_rename]
          cases found : ruleById policy ruleId with
          | none => rfl
          | some rule =>
              simp only [Option.map_some]
              rw [labelIndex?_rename]
              cases label : labelIndex? rule name with
              | some index =>
                  simp only [supportTermsToList_rename, List.getElem?_map,
                    Option.map_map, Function.comp_apply]
              | none =>
                  simp only [questionIds_renameRule]
                  rw [questionByName?_rename]
                  cases question :
                      (questionIds rule).find?
                        (fun question => question.val == name) with
                  | none => rfl
                  | some question =>
                      simp only [Option.map_some]
                      rw [dischargeTermsToList_rename,
                        dischargeByQuestion?_rename]

private theorem pathWalksB_rename
    (sound : RenamingSound ρg program policy)
    (term : Presentation.SupportTerm)
    (path : List Presentation.SurfaceStep) :
    pathWalksB (Binding.renamePolicy ρg policy)
        (renameResidualSupportTerm ρg term)
        (path.map (Binding.renameSurfaceStep ρg)) =
      pathWalksB policy term path := by
  induction path generalizing term with
  | nil => rfl
  | cons step rest ih =>
      simp only [List.map_cons, pathWalksB]
      rw [nextOccurrence?_rename sound]
      cases found : nextOccurrence? policy term step with
      | none => rfl
      | some next =>
          simp only [Option.map_some]
          exact ih next

private theorem priorById?_rename
    (ρg : Binding.GlobalRenaming)
    (priors : List PriorArgument) (target : Presentation.ArgId) :
    (priors.map (renamePriorArgument ρg)).find?
        (fun argument => decide (argument.id = ρg.arg target)) =
      (priors.find? (fun argument =>
        decide (argument.id = target))).map
          (renamePriorArgument ρg) := by
  induction priors with
  | nil => rfl
  | cons prior rest ih =>
      by_cases equal : prior.id = target
      · have renamedEqual :
            (renamePriorArgument ρg prior).id = ρg.arg target := by
          simp [renamePriorArgument, equal]
        simp [equal, renamedEqual]
      · have renamedNe :
            (renamePriorArgument ρg prior).id ≠ ρg.arg target := by
          simp only [renamePriorArgument]
          exact fun h => equal (ρg.arg_injective h)
        simp [equal, renamedNe, ih]

private theorem targetTerm?_rename
    (sound : RenamingSound ρg program policy)
    (target : Presentation.ArgId) :
    targetTerm? (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy) (ρg.arg target) =
      (targetTerm? program policy target).map
        (renameResidualSupportTerm ρg) := by
  unfold targetTerm?
  change
    (do
      let prior ←
        (collectProgramArguments (Binding.renameProgram ρg program)
          (Binding.renamePolicy ρg policy)
          (program.decls.map
            (Binding.renameDecl ρg (programValues program))) []).find?
          (fun (argument : PriorArgument) =>
            decide (argument.id = ρg.arg target))
      some prior.term) =
    (do
      let prior ←
        (collectProgramArguments program policy program.decls []).find?
          (fun (argument : PriorArgument) =>
            decide (argument.id = target))
      some prior.term).map (renameResidualSupportTerm ρg)
  have collected :=
    collectProgramArguments_rename sound program.decls [] (by
      intro declaration member
      exact member)
  simp only [List.map_nil] at collected
  rw [collected]
  rw [priorById?_rename]
  cases found :
      (collectProgramArguments program policy program.decls []).find?
        (fun argument => decide (argument.id = target)) <;>
    rfl

private theorem attackEndpoints_rename
    (ρg : Binding.GlobalRenaming)
    (attack : Presentation.SurfaceAttack) :
    attackEndpoints (Binding.renameSurfaceAttack ρg attack) =
      (ρg.arg (attackEndpoints attack).1,
        ρg.arg (attackEndpoints attack).2) := by
  cases attack <;> rfl

private theorem attackPath_rename
    (ρg : Binding.GlobalRenaming)
    (attack : Presentation.SurfaceAttack) :
    attackPath (Binding.renameSurfaceAttack ρg attack) =
      (attackPath attack).map (Binding.renameSurfaceStep ρg) := by
  cases attack <;> rfl

private theorem contains_map_of_injective
    {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (injective : Function.Injective f)
    (values : List α) (value : α) :
    (values.map f).contains (f value) = values.contains value := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨candidate, member, equal⟩
    simpa [injective equal] using member
  · intro member
    exact ⟨value, member, rfl⟩

private theorem surfaceAttackWellFormedB_rename
    (sound : RenamingSound ρg program policy)
    (attack : Presentation.SurfaceAttack) :
    surfaceAttackWellFormedB (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (Binding.renameSurfaceAttack ρg attack) =
      surfaceAttackWellFormedB program policy attack := by
  unfold surfaceAttackWellFormedB
  rw [argIds_renameProgram, attackEndpoints_rename,
    contains_map_of_injective ρg.arg ρg.arg_injective,
    contains_map_of_injective ρg.arg ρg.arg_injective,
    targetTerm?_rename sound, attackPath_rename]
  cases found :
      targetTerm? program policy (attackEndpoints attack).2 with
  | none => rfl
  | some target =>
      simp only [Option.map_some]
      rw [pathWalksB_rename sound target (attackPath attack)]

theorem surfaceAttacksWellFormedB_rename
    (sound : RenamingSound ρg program policy) :
    surfaceAttacksWellFormedB (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy) =
      surfaceAttacksWellFormedB program policy := by
  unfold surfaceAttacksWellFormedB
  change
    (program.decls.map
        (Binding.renameDecl ρg (programValues program))).all
        (fun declaration =>
          match declaration with
          | .attack attack =>
              surfaceAttackWellFormedB
                (Binding.renameProgram ρg program)
                (Binding.renamePolicy ρg policy) attack
          | _ => true) =
      program.decls.all fun declaration =>
        match declaration with
        | .attack attack =>
            surfaceAttackWellFormedB program policy attack
        | _ => true
  generalize program.decls = declarations
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;>
        simp [Binding.renameDecl, surfaceAttackWellFormedB_rename sound, ih]

theorem policyMatchesB_rename
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program)
    (policy : Presentation.Policy) :
    policyMatchesB
        ⟨Binding.renameProgram ρg program, Binding.renamePolicy ρg policy⟩ =
      policyMatchesB ⟨program, policy⟩ := by
  rfl

theorem declarationIdsNodupB_rename
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program) :
    declarationIdsNodupB (Binding.renameProgram ρg program) =
      declarationIdsNodupB program := by
  apply Bool.eq_iff_iff.mpr
  rw [declarationIdsNodupB_iff, declarationIdsNodupB_iff]
  simp only [DeclarationIdsNodup, leafIds_renameProgram,
    argIds_renameProgram, claimIds_renameProgram, valueNames_renameProgram]

  rw [nodup_map_iff_of_injective ρg.leaf_injective,
    nodup_map_iff_of_injective ρg.arg_injective,
    nodup_map_iff_of_injective ρg.prop_injective,
    nodup_map_iff_of_injective ρg.valueName_injective]
private theorem ruleNamespaceWellFormed_rename
    (sound : RenamingSound ρg program policy)
    (rule : Presentation.Rule) :
    RuleNamespaceWellFormed (Binding.renameRule ρg rule) ↔
      RuleNamespaceWellFormed rule := by
  have propTextNe (spelling text : String)
      (fixed : renameText ρg text = text) :
      (ρg.prop ⟨spelling⟩).val ≠ text ↔ spelling ≠ text := by
    apply not_congr
    change renameText ρg spelling = text ↔ spelling = text
    constructor
    · intro equal
      apply renameText_injective ρg
      exact equal.trans fixed.symm
    · intro equal
      rw [equal]
      exact fixed
  have propPropNe (left right : String) :
      (ρg.prop ⟨left⟩).val ≠ (ρg.prop ⟨right⟩).val ↔
        left ≠ right := by
    apply not_congr
    change renameText ρg left = renameText ρg right ↔ left = right
    exact ⟨fun equal => renameText_injective ρg equal,
      fun equal => congrArg (renameText ρg) equal⟩
  simp only [RuleNamespaceWellFormed, premiseLabels_renameRule,
    questionIds_renameRule]
  rw [nodup_map_iff_of_injective ρg.premiseLabel_injective,
    nodup_map_iff_of_injective ρg.question_injective]
  simp [propTextNe _ "rule" sound.rule_spelling,
    propTextNe _ "leaf" sound.leaf_spelling, propPropNe]

theorem ruleNamespacesWellFormedB_rename
    (sound : RenamingSound ρg program policy) :
    ruleNamespacesWellFormedB (Binding.renamePolicy ρg policy) =
      ruleNamespacesWellFormedB policy := by
  apply Bool.eq_iff_iff.mpr
  rw [ruleNamespacesWellFormedB_iff, ruleNamespacesWellFormedB_iff]
  unfold RuleNamespacesWellFormed
  rw [ruleIds_renamePolicy]
  constructor
  · rintro ⟨ids, rules⟩
    refine ⟨(nodup_map_iff_of_injective ρg.rule_injective).mp ids, ?_⟩
    intro rule member
    apply (ruleNamespaceWellFormed_rename sound rule).mp
    exact rules (Binding.renameRule ρg rule)
      (List.mem_map.mpr ⟨rule, member, rfl⟩)
  · rintro ⟨ids, rules⟩
    refine ⟨(nodup_map_iff_of_injective ρg.rule_injective).mpr ids, ?_⟩
    intro renamed member
    simp only [Binding.renamePolicy, List.mem_map] at member
    obtain ⟨rule, ruleMember, rfl⟩ := member
    exact (ruleNamespaceWellFormed_rename sound rule).mpr
      (rules rule ruleMember)


theorem canonicalPremiseLabelsB_rename
    (ρg : Binding.GlobalRenaming) (policy : Presentation.Policy) :
    canonicalPremiseLabelsB (Binding.renamePolicy ρg policy) =
      canonicalPremiseLabelsB policy := by
  have optionIsSome : ∀ label : Option Presentation.PremiseLabel,
      (label.map ρg.premiseLabel).isSome = label.isSome := by
    intro label
    cases label <;> rfl
  have anyIsSome : ∀ labels : List (Option Presentation.PremiseLabel),
      (labels.map (Option.map ρg.premiseLabel)).any
          (fun label => label.isSome) =
        labels.any (fun label => label.isSome) := by
    intro labels
    induction labels with
    | nil => rfl
    | cons label rest ih =>
        simp [optionIsSome, ih]
  have perRule : ∀ rule,
      canonicalPremiseLabelsForRuleB (Binding.renameRule ρg rule) =
        canonicalPremiseLabelsForRuleB rule := by
    intro rule
    simp [canonicalPremiseLabelsForRuleB, Binding.renameRule, anyIsSome]
  simp only [canonicalPremiseLabelsB, Binding.renamePolicy]
  induction policy.rules with
  | nil => rfl
  | cons rule rest ih =>
      simp [perRule, ih]

private theorem statusesWellFormed_rename_iff
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program) :
    StatusesWellFormed (Binding.renameProgram ρg program) ↔
      StatusesWellFormed program := by
  simp only [StatusesWellFormed, statusIds_renameProgram,
    claimIds_renameProgram]
  constructor
  · intro renamed id statusMember
    have renamedStatus : ρg.prop id ∈ (statusIds program).map ρg.prop :=
      List.mem_map.mpr ⟨id, statusMember, rfl⟩
    obtain ⟨source, sourceMember, equal⟩ :=
      List.mem_map.mp (renamed (ρg.prop id) renamedStatus)
    have sourceEq : source = id := ρg.prop_injective equal
    simpa [sourceEq] using sourceMember
  · intro source renamedId statusMember
    obtain ⟨id, idMember, rfl⟩ := List.mem_map.mp statusMember
    exact List.mem_map.mpr ⟨id, source id idMember, rfl⟩

theorem statusesWellFormedB_rename
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program) :
    statusesWellFormedB (Binding.renameProgram ρg program) =
      statusesWellFormedB program := by
  apply Bool.eq_iff_iff.mpr
  rw [statusesWellFormedB_iff, statusesWellFormedB_iff]
  exact statusesWellFormed_rename_iff ρg program

private theorem groupsWellFormed_rename_iff
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program) :
    GroupsWellFormed (Binding.renameProgram ρg program) ↔
      GroupsWellFormed program := by
  unfold GroupsWellFormed
  rw [show groupDecls (Binding.renameProgram ρg program) =
      (groupDecls program).map (renamePresentationGroup ρg) from
    groupDecls_renameProgram ρg program]
  rw [show leafIds (Binding.renameProgram ρg program) =
      (leafIds program).map ρg.leaf from leafIds_renameProgram ρg program]
  have idsMap :
      ((groupDecls program).map (renamePresentationGroup ρg)).map (·.id) =
        ((groupDecls program).map (·.id)).map ρg.group := by
    simp [List.map_map, renamePresentationGroup, Function.comp_def]
  rw [idsMap, nodup_map_iff_of_injective ρg.group_injective]
  constructor
  · rintro ⟨renamedIds, renamedGroups⟩
    refine ⟨renamedIds, ?_⟩
    intro group groupMember
    have renamedMember : renamePresentationGroup ρg group ∈
        (groupDecls program).map (renamePresentationGroup ρg) :=
      List.mem_map.mpr ⟨group, groupMember, rfl⟩
    obtain ⟨⟨membersNodup, lengthBound⟩, declared⟩ :=
      renamedGroups (renamePresentationGroup ρg group) renamedMember
    change (group.members.map ρg.leaf).Nodup at membersNodup
    change 2 ≤ (group.members.map ρg.leaf).length at lengthBound
    refine ⟨⟨(nodup_map_iff_of_injective ρg.leaf_injective).mp
        membersNodup, by simpa using lengthBound⟩, ?_⟩
    intro leaf leafMember
    have renamedLeaf : ρg.leaf leaf ∈ group.members.map ρg.leaf :=
      List.mem_map.mpr ⟨leaf, leafMember, rfl⟩
    have renamedDeclared : ρg.leaf leaf ∈ (leafIds program).map ρg.leaf := by
      apply declared (ρg.leaf leaf)
      simpa [renamePresentationGroup] using renamedLeaf
    obtain ⟨sourceLeaf, sourceMember, equal⟩ :=
      List.mem_map.mp renamedDeclared
    have sourceEq : sourceLeaf = leaf := ρg.leaf_injective equal
    simpa [sourceEq] using sourceMember
  · rintro ⟨sourceIds, sourceGroups⟩
    refine ⟨sourceIds, ?_⟩
    intro renamedGroup renamedMember
    obtain ⟨group, groupMember, rfl⟩ := List.mem_map.mp renamedMember
    obtain ⟨⟨membersNodup, lengthBound⟩, declared⟩ :=
      sourceGroups group groupMember
    refine ⟨⟨by
        change (group.members.map ρg.leaf).Nodup
        exact (nodup_map_iff_of_injective ρg.leaf_injective).mpr membersNodup,
      by simpa [renamePresentationGroup] using lengthBound⟩, ?_⟩
    intro renamedLeaf renamedLeafMember
    obtain ⟨leaf, leafMember, rfl⟩ := List.mem_map.mp
      (by simpa [renamePresentationGroup] using renamedLeafMember)
    exact List.mem_map.mpr ⟨leaf, declared leaf leafMember, rfl⟩

theorem groupsWellFormedB_rename
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program) :
    groupsWellFormedB (Binding.renameProgram ρg program) =
      groupsWellFormedB program := by
  apply Bool.eq_iff_iff.mpr
  rw [groupsWellFormedB_iff, groupsWellFormedB_iff]
  exact groupsWellFormed_rename_iff ρg program

theorem supportedB_rename
    (sound : RenamingSound ρg program policy) :
    supportedB
        ⟨Binding.renameProgram ρg program,
          Binding.renamePolicy ρg policy⟩ =
      supportedB ⟨program, policy⟩ := by
  unfold supportedB
  rw [policyMatchesB_rename, declarationIdsNodupB_rename,
    ruleNamespacesWellFormedB_rename sound,
    valueBindingsWellFormedB_rename sound,
    comparisonsWellFormedB_rename sound,
    inferredArgsWellFormedB_rename sound,
    namedCertificatesWellFormedB_rename sound,
    surfaceAttacksWellFormedB_rename sound,
    canonicalPremiseLabelsB_rename]

end Renaming

theorem Binding.supported_rename_iff
    (ρg : Binding.GlobalRenaming)
    (program : Presentation.Program) (policy : Presentation.Policy)
    (sound : RenamingSound ρg program policy) :
    Supported
        ⟨Binding.renameProgram ρg program,
          Binding.renamePolicy ρg policy⟩ ↔
      Supported ⟨program, policy⟩ := by
  constructor
  · intro renamed
    apply (supportedB_iff ⟨program, policy⟩).mp
    rw [← Renaming.supportedB_rename sound]
    exact (supportedB_iff
      ⟨Binding.renameProgram ρg program,
        Binding.renamePolicy ρg policy⟩).mpr renamed
  · intro source
    apply (supportedB_iff
      ⟨Binding.renameProgram ρg program,
        Binding.renamePolicy ρg policy⟩).mp
    rw [Renaming.supportedB_rename sound]
    exact (supportedB_iff ⟨program, policy⟩).mpr source


/-! ### The metadata-source renaming theorem (round 2 special case). -/

theorem Binding.supported_sourceOnly_rename_iff
    (f : Presentation.SourceRef → Presentation.SourceRef)
    (injective : Function.Injective f)
    (program : Presentation.Program) (policy : Presentation.Policy)
    (fixed : Binding.SourcesFixed f program.decls) :
    Supported
        ⟨Binding.renameProgram (Binding.GlobalRenaming.sourceOnly f injective) program,
          Binding.renamePolicy (Binding.GlobalRenaming.sourceOnly f injective) policy⟩ ↔
      Supported ⟨program, policy⟩ := by
  rw [Binding.renameProgram_sourceOnly, Binding.renamePolicy_sourceOnly,
    Binding.renameSourceRefsProgram_eq_of_fixed f program fixed]
end Lara.Surface
