/-
The independent syntax-directed surface judgment (`Lara.Surface.Check`) — M5
Task 4.

`Surface.Checks` is a Prop-level derivation over the presentation AST, split
by responsibility:

* `ChecksRule` — one policy rule's namespace and canonical premise labels;
* `ChecksCertificate` — one reconstructed support term lowers to a core
  support term (named-certificate and slot-schema payload lowering);
* `ChecksArgument` — one argument resolves its references against declared
  leaves and *prior* arguments, covers the citing rule's parameters, and
  carries a certificate lowering;
* `ChecksAttack` / `ChecksAttacks` — one surface attack resolves its source
  and target ids and walks its authored path to a core position;
* `ChecksDeclaration` / `ChecksProgram` — the declaration fold threading
  prior arguments left-to-right, so a reference to a later argument is
  unrepresentable in a successful derivation;
* `Checks` — the top-level judgment: the supported fragment, admission,
  the expansion relations, the program derivation, resolved attacks, and
  core acceptance of the assembled unit.

Per D3, the judgment is *not* defined as "`checkUnit` accepts the elaborated
input": the surface conjuncts are syntax-directed over the presentation AST,
and core acceptance is one conjunct beside them. `Surface.check` is the
executable implementation of the derivation rules; `check_sound` and
`check_complete` give the exact correspondence, `checks_deterministic` the
unique carrier, and `checks_supported` the supported-fragment implication.
Error constructors are structural and stable inside Lean; no parity with
Haskell message text is claimed.
-/

import Lara.Surface.ValueBinding
import Lara.Surface.Comparison
import Lara.Check.Unit
import Lara.Admission

namespace Lara.Surface

open Lara

/-! ### Small executable utilities -/

/-- Boolean success of an `Except`, local so the correspondence theorems do
not depend on library `Except` lemmas. -/
def exceptIsOk : Except α β → Bool
  | .ok _ => true
  | .error _ => false

theorem exceptIsOk_iff {e : Except α β} : exceptIsOk e = true ↔ ∃ b, e = .ok b := by
  cases e <;> simp [exceptIsOk]

/-- The rejection of an `Except`, when it is one. -/
def errorOf? : Except α β → Option α
  | .error e => some e
  | .ok _ => none

/-- The first value occurring twice in a list, if any. -/
def findDuplicate [DecidableEq α] : List α → Option α
  | [] => none
  | x :: rest =>
      match rest.find? (fun y => decide (y = x)) with
      | some _ => some x
      | none => findDuplicate rest

/-- Production diagnostic order: return the value at its first repeated
occurrence, not the earliest value that has some duplicate later. -/
private def firstRepeatedAux [DecidableEq α] : List α → List α → Option α
  | _, [] => none
  | seen, value :: rest =>
      if value ∈ seen then some value
      else firstRepeatedAux (value :: seen) rest

def firstRepeated [DecidableEq α] (values : List α) : Option α :=
  firstRepeatedAux [] values

theorem findDuplicate_none_nodup [DecidableEq α] :
    ∀ {xs : List α}, findDuplicate xs = none → xs.Nodup := by
  intro xs
  induction xs with
  | nil => intro _; exact List.nodup_nil
  | cons x rest ih =>
      intro h
      simp only [findDuplicate] at h
      cases hfind : rest.find? (fun y => decide (y = x)) with
      | some y => rw [hfind] at h; cases h
      | none =>
          rw [hfind] at h
          refine List.nodup_cons.mpr ⟨?_, ih h⟩
          intro hmem
          have := (List.find?_eq_none).mp hfind x hmem
          simp at this
theorem findDuplicate_none_of_nodup [DecidableEq α] :
    ∀ {xs : List α}, xs.Nodup → findDuplicate xs = none := by
  intro xs h
  induction h with
  | nil => rfl
  | @cons x rest hnotmem _ ih =>
      simp only [findDuplicate]
      have hfind : rest.find? (fun y => decide (y = x)) = none := by
        apply List.find?_eq_none.mpr
        intro y hy
        intro htrue
        have hyx : y = x := of_decide_eq_true htrue
        exact hnotmem y hy hyx.symm
      rw [hfind]
      exact ih

/-- Membership as a `Bool`, over `DecidableEq` only. -/
def memberOf [DecidableEq α] (x : α) (xs : List α) : Bool :=
  xs.any fun y => decide (x = y)

theorem memberOf_iff [DecidableEq α] (x : α) (xs : List α) :
    memberOf x xs = true ↔ x ∈ xs := by
  induction xs with
  | nil => simp [memberOf]
  | cons y rest ih =>
      simp only [memberOf, List.any_cons, Bool.or_eq_true, List.mem_cons]
      by_cases hxy : x = y
      · subst hxy
        simp
      · simp [hxy, ih]

theorem map_pair_eq_zip_map (xs : List α) (f : α → β) (g : α → γ) :
    xs.map (fun x => (f x, g x)) = (xs.map f).zip (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      change (f x, g x) :: rest.map (fun x => (f x, g x)) =
        (f x, g x) :: (rest.map f).zip (rest.map g)
      rw [ih]

/-! ### Admission at the source boundary -/

/-- Total admission lookup: omitted and unmatched keys default to `admit`
(the Haskell `decisionFor`). -/
def admissionDecision (table : List Presentation.AdmissionEntry)
    (kind : Presentation.LeafKind) (provenance : Presentation.Provenance) :
    Presentation.Admission :=
  match table.find? (fun entry => decide (entry.1 = (kind, provenance))) with
  | some entry => entry.2
  | none => .admit

/-- The declared leaf records of a program, in declaration order. -/
def leafRecords (program : Presentation.Program) : List Presentation.Leaf :=
  program.decls.filterMap fun
    | .leaf leaf => some leaf
    | _ => none

/-- The first declared leaf the policy's admission table rejects. -/
def firstRejectedLeaf (policy : Presentation.Policy) (program : Presentation.Program) :
    Option Presentation.Leaf :=
  (leafRecords program).find? fun leaf =>
    decide (admissionDecision policy.admission leaf.kind leaf.provenance = .reject)

/-- The declared leaves the policy's admission table quarantines. -/
def quarantinedLeafIds (policy : Presentation.Policy) (program : Presentation.Program) :
    List Presentation.LeafId :=
  (leafRecords program).filterMap fun leaf =>
    if admissionDecision policy.admission leaf.kind leaf.provenance = .quarantine then
      some leaf.id
    else none

/-- The admission leaves of a program: every declared leaf the table does
not quarantine or reject. -/
def admittedLeaves (policy : Presentation.Policy) (program : Presentation.Program) :
    List Presentation.Leaf :=
  (leafRecords program).filter fun leaf =>
    admissionDecision policy.admission leaf.kind leaf.provenance = .admit

/-- The source-boundary admission judgment: distinct admission keys and no
rejected declared leaf (the `prepareSource` prologue and decision). -/
def AdmissionOK (input : Input) : Prop :=
  (input.policy.admission.map Prod.fst).Nodup ∧
    ∀ leaf ∈ leafRecords input.program,
      admissionDecision input.policy.admission leaf.kind leaf.provenance ≠ .reject

/-! ### The syntax-directed judgments -/

/-- One policy rule: namespace well-formedness and canonical premise labels. -/
inductive ChecksRule (rule : Presentation.Rule) : Prop where
  | intro
      (hnamespace : RuleNamespaceWellFormed rule)
      (hlabels : rule.premiseLabels = [] ∨
        (rule.premiseLabels.length = rule.premises.length ∧
          ∃ label ∈ rule.premiseLabels, label.isSome = true)) :
      ChecksRule rule

/-- Lower one assurance's certificate payload; `none` and `trusted` carry no
payload and always lower. -/
def lowerAssuranceCertificate (env : Env canon) (program : Presentation.Program)
    (rule : Presentation.Rule) (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm) :
    Presentation.Assurance → Option Lara.Support.Assurance
  | .none => some .none
  | .trusted => some .trusted
  | .cert certificate =>
      match certificate.version with
      | .negSucc _ => none
      | .ofNat version =>
          let resolver := certificateResolver program rule priors premises
          if certificate.backend.val == "nd" && version == 1 then
            (Lara.NDNamed.lowerNamed env.startsIdent resolver env.encodeProp
              premises.length [] (sxToSExpr certificate.payload)).map fun lowered =>
              .cert (toSupportBackendId certificate.backend certificate.version)
                (toSupportTheoryDigest certificate.theory) ⟨lowered⟩
          else
            (Lara.CertSlots.lowerPayload sourceStartsIdentifier resolver
              certificate.backend.val version (sxToSExpr certificate.payload)).map
              fun lowered =>
              .cert (toSupportBackendId certificate.backend certificate.version)
                (toSupportTheoryDigest certificate.theory) ⟨lowered⟩

mutual
  /-- Lower one presentation support term to a core support term, lowering
  every certificate payload on the way: `nd@1` named payloads through
  `NDNamed.lowerNamed`, schema'd backends through `CertSlots.lowerPayload`,
  everything else byte-identical. The resolver is computed from the citing
  rule and the reconstructed premise sequence, exactly as the validation
  judgment computes it. -/
  def lowerToSupportTerm (env : Env canon) (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument) :
      Presentation.SupportTerm → Option Lara.Support.SupportTerm
    | .leaf leaf => some (.leaf (toSupportLeafId leaf))
    | .rule ruleId subst premises discharges holes assurance => do
        let rule ← ruleById policy ruleId
        let loweredAssurance ← lowerAssuranceCertificate env program rule priors
          (supportTermsToList premises) assurance
        let loweredPremises ← lowerToSupportTerms env program policy priors premises
        let loweredDischarges ← lowerToSupportDischarges env program policy priors discharges
        some (.inst (toSupportRuleId ruleId)
          (subst.map fun pair => (toSupportParam pair.1, pair.2))
          loweredPremises loweredDischarges (holes.map toSupportObligationId)
          loweredAssurance)

  def lowerToSupportTerms (env : Env canon) (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument) :
      Presentation.SupportTerms → Option (List Lara.Support.SupportTerm)
    | .nil => some []
    | .cons term rest => do
        let lowered ← lowerToSupportTerm env program policy priors term
        let loweredRest ← lowerToSupportTerms env program policy priors rest
        some (lowered :: loweredRest)

  def lowerToSupportDischarges (env : Env canon) (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument) :
      Presentation.Discharges →
        Option (List (Lara.Support.QuestionId × Lara.Support.SupportTerm))
    | .nil => some []
    | .cons question term rest => do
        let lowered ← lowerToSupportTerm env program policy priors term
        let loweredRest ← lowerToSupportDischarges env program policy priors rest
        some ((toSupportQuestionId question, lowered) :: loweredRest)
end

/-! ### Recursive explicit-term reconstruction -/

/-- Every declared leaf and prior argument whose conclusion is canonically
equivalent to an instantiated premise, in declaration order. -/
def premiseMatches (canon : String → String) (program : Presentation.Program)
    (priors : List PriorArgument) (ground : Atom) :
    List Presentation.SupportTerm :=
  (declaredLeaves program).filterMap (fun entry =>
    if equiv canon entry.2 ground then some (.leaf entry.1) else none) ++
  priors.filterMap (fun prior =>
    if equiv canon prior.conclusion ground then some prior.term else none)

/-- Resolve one omitted premise only when its instantiated proposition has one
declared-leaf-or-prior-argument match. -/
def resolveImplicitPremise (canon : String → String)
    (program : Presentation.Program) (priors : List PriorArgument)
    (theta : SurfaceSubst) (pattern : Presentation.AtomPat) :
    Option Presentation.SupportTerm := do
  let ground ← instantiateSurfaceAtom theta pattern
  match premiseMatches canon program priors ground with
  | [term] => some term
  | _ => none

/-- Resolve omitted premises in the citing rule's slot order. -/
def resolveImplicitPremises (canon : String → String)
    (program : Presentation.Program) (priors : List PriorArgument)
    (theta : SurfaceSubst) :
    List Presentation.AtomPat → Option Presentation.SupportTerms
  | [] => some .nil
  | pattern :: rest => do
      let term ← resolveImplicitPremise canon program priors theta pattern
      let terms ← resolveImplicitPremises canon program priors theta rest
      some (.cons term terms)

mutual
  /-- Rebuild a complete explicit support term. Rule occurrences re-associate
  positional theta values with the selected rule's declared parameters. An
  omitted premise list is reconstructed by unique canonical matching; an
  authored list is recursively rebuilt. Certificates remain presentation data
  here and are lowered only after the final premise list is known. -/
  def reconstructExplicitTerm (canon : String → String)
      (program : Presentation.Program) (policy : Presentation.Policy)
      (priors : List PriorArgument) :
      Presentation.SupportTerm → Option Presentation.SupportTerm
    | .leaf leaf => some (.leaf leaf)
    | .rule ruleId positionalTheta .nil shallowDischarges holes assurance => do
        let rule ← ruleById policy ruleId
        if positionalTheta.length != rule.params.length then none else pure ()
        let theta := rule.params.zip (positionalTheta.map Prod.snd)
        let premises ← resolveImplicitPremises canon program priors theta rule.premises
        let discharges ←
          reconstructExplicitDischarges canon program policy priors shallowDischarges
        some (.rule ruleId theta premises discharges holes assurance)
    | .rule ruleId positionalTheta (.cons premise premises) shallowDischarges
        holes assurance => do
        let rule ← ruleById policy ruleId
        if positionalTheta.length != rule.params.length then none else pure ()
        let theta := rule.params.zip (positionalTheta.map Prod.snd)
        let premises ← reconstructExplicitTerms canon program policy priors
          (.cons premise premises)
        let discharges ←
          reconstructExplicitDischarges canon program policy priors shallowDischarges
        some (.rule ruleId theta premises discharges holes assurance)

  /-- Recursively rebuild an authored premise sequence. -/
  def reconstructExplicitTerms (canon : String → String)
      (program : Presentation.Program) (policy : Presentation.Policy)
      (priors : List PriorArgument) :
      Presentation.SupportTerms → Option Presentation.SupportTerms
    | .nil => some .nil
    | .cons term rest => do
        let rebuilt ← reconstructExplicitTerm canon program policy priors term
        let rebuiltRest ← reconstructExplicitTerms canon program policy priors rest
        some (.cons rebuilt rebuiltRest)

  /-- Rebuild explicit discharges in the parser-supported fragment. Production
  resolves leaf-shaped source references and preserves non-leaf targets. The
  surface calculus makes that parser boundary explicit by deriving only the
  leaf-shaped form; a non-leaf authored target is therefore rejected here
  rather than assigned a different recursive meaning. -/
  def reconstructExplicitDischarges (canon : String → String)
      (program : Presentation.Program) (policy : Presentation.Policy)
      (priors : List PriorArgument) :
      Presentation.Discharges → Option Presentation.Discharges
    | .nil => some .nil
    | .cons question (.leaf leaf) rest => do
        let rebuilt ← (resolveReference program priors ⟨leaf.val⟩).map (·.term)
        let rebuiltRest ←
          reconstructExplicitDischarges canon program policy priors rest
        some (.cons question rebuilt rebuiltRest)
    | .cons _ (.rule ..) _ => none
end

/-- Reconstruct the complete presentation term at the argument boundary.
Inferred arguments already construct complete terms from their authored
references; explicit arguments use the recursive production-compatible pass. -/
def reconstructArgument (canon : String → String)
    (program : Presentation.Program) (policy : Presentation.Policy)
    (priors : List PriorArgument) (argument : Presentation.Arg) :
    Option PriorArgument :=
  match argument.instantiation with
  | .inferTheta _ _ _ _ _ => buildArgument program policy priors argument
  | .explicitTheta term => do
      let rebuilt ← reconstructExplicitTerm canon program policy priors term
      let conclusion ← conclOfTerm program policy rebuilt
      some ⟨argument.id, rebuilt, conclusion⟩

/-- One reconstructed argument: the authored declaration, the resolved
presentation-level build, and the lowered core support term. -/
structure ReconstructedArgument where
  argument : Presentation.Arg
  built : PriorArgument
  core : Lara.Support.SupportTerm

/-! ### Independent argument and certificate derivations -/

/-- Declarative first-match rule lookup over the authored rule list. -/
inductive FindsRule : List Presentation.Rule → Presentation.RuleId →
    Presentation.Rule → Prop where
  | here {id rule rest} (hid : rule.id = id) :
      FindsRule (rule :: rest) id rule
  | there {id head rest rule} (hne : head.id ≠ id)
      (tail : FindsRule rest id rule) :
      FindsRule (head :: rest) id rule

/-- A source reference resolves in exactly one side of the shared namespace. -/
inductive ChecksReference (program : Presentation.Program)
    (priors : List PriorArgument) (reference : Presentation.ArgRef) :
    ResolvedReference → Prop where
  | leaf {leaf proposition}
      (hleaves : (declaredLeaves program).filter
        (fun entry => entry.1.val == reference.val) = [(leaf, proposition)])
      (hargs : priors.filter (fun prior => prior.id.val == reference.val) = []) :
      ChecksReference program priors reference
        ⟨.leaf leaf, proposition, some leaf, none⟩
  | argument {prior}
      (hleaves : (declaredLeaves program).filter
        (fun entry => entry.1.val == reference.val) = [])
      (hargs : priors.filter (fun candidate =>
        candidate.id.val == reference.val) = [prior]) :
      ChecksReference program priors reference
        ⟨prior.term, prior.conclusion, none, some prior.id⟩

/-- Pointwise source-reference resolution in authored order. -/
inductive ChecksReferences (program : Presentation.Program)
    (priors : List PriorArgument) :
    List Presentation.ArgRef → List ResolvedReference → Prop where
  | nil : ChecksReferences program priors [] []
  | cons (head : ChecksReference program priors reference resolved)
      (tail : ChecksReferences program priors references resolvedRest) :
      ChecksReferences program priors (reference :: references)
        (resolved :: resolvedRest)

/-- Syntax-directed premise-pattern matching and substitution threading. -/
inductive ChecksPremiseMatch :
    SurfaceSubst → List Presentation.AtomPat → List ResolvedReference →
      SurfaceSubst → Prop where
  | nil : ChecksPremiseMatch subst [] [] subst
  | cons
      (hmatch : matchSurfaceAtom subst pattern reference.conclusion = some next)
      (tail : ChecksPremiseMatch next patterns references out) :
      ChecksPremiseMatch subst (pattern :: patterns) (reference :: references) out

/-- Every declared parameter has an associated term in theta. -/
def ParamsCovered (params : List Presentation.Param) (theta : SurfaceSubst) : Prop :=
  ∀ param ∈ params, ∃ term, lookupSurfaceSubst theta param = some term

/-- Named inferred discharges resolve declared questions through the same
leaf/prior namespace as premise references. -/
inductive ChecksNamedDischarges (program : Presentation.Program)
    (priors : List PriorArgument) (rule : Presentation.Rule) :
    Presentation.ArgDischarge →
      List (Presentation.QuestionId × Presentation.SupportTerm) → Prop where
  | nil : ChecksNamedDischarges program priors rule [] []
  | cons
      (hquestion : question ∈ questionIds rule)
      (hreference : ChecksReference program priors reference resolved)
      (tail : ChecksNamedDischarges program priors rule rest resolvedRest) :
      ChecksNamedDischarges program priors rule
        ((question, reference) :: rest)
        ((question, resolved.term) :: resolvedRest)

/-- One omitted premise slot resolves to the only canonically equivalent
declared leaf or prior argument. -/
inductive ChecksImplicitPremises (canon : String → String)
    (program : Presentation.Program) (priors : List PriorArgument)
    (theta : SurfaceSubst) :
    List Presentation.AtomPat → Presentation.SupportTerms → Prop where
  | nil : ChecksImplicitPremises canon program priors theta [] .nil
  | cons
      (hground : instantiateSurfaceAtom theta pattern = some ground)
      (hunique : premiseMatches canon program priors ground = [term])
      (tail : ChecksImplicitPremises canon program priors theta patterns terms) :
      ChecksImplicitPremises canon program priors theta (pattern :: patterns)
        (.cons term terms)

mutual
  /-- Independent reconstruction of an explicit support term. Omitted premises
  use unique matching; authored premises recurse. -/
  inductive ReconstructsExplicitTerm (canon : String → String)
      (program : Presentation.Program) (policy : Presentation.Policy)
      (priors : List PriorArgument) :
      Presentation.SupportTerm → Presentation.SupportTerm → Prop where
    | leaf {leaf} :
        ReconstructsExplicitTerm canon program policy priors (.leaf leaf) (.leaf leaf)
    | implicit
        (hrule : FindsRule policy.rules ruleId rule)
        (harity : positionalTheta.length = rule.params.length)
        (hpremises : ChecksImplicitPremises canon program priors
          (rule.params.zip (positionalTheta.map Prod.snd)) rule.premises rebuiltPremises)
        (hdischarges : ReconstructsExplicitDischarges canon program policy priors
          shallowDischarges rebuiltDischarges) :
        ReconstructsExplicitTerm canon program policy priors
          (.rule ruleId positionalTheta .nil shallowDischarges holes assurance)
          (.rule ruleId (rule.params.zip (positionalTheta.map Prod.snd))
            rebuiltPremises rebuiltDischarges holes assurance)
    | provided
        (hrule : FindsRule policy.rules ruleId rule)
        (harity : positionalTheta.length = rule.params.length)
        (hpremises : ReconstructsExplicitTerms canon program policy priors
          (.cons premise premises) rebuiltPremises)
        (hdischarges : ReconstructsExplicitDischarges canon program policy priors
          shallowDischarges rebuiltDischarges) :
        ReconstructsExplicitTerm canon program policy priors
          (.rule ruleId positionalTheta (.cons premise premises)
            shallowDischarges holes assurance)
          (.rule ruleId (rule.params.zip (positionalTheta.map Prod.snd))
            rebuiltPremises rebuiltDischarges holes assurance)

  /-- Pointwise reconstruction of authored premise terms. -/
  inductive ReconstructsExplicitTerms (canon : String → String)
      (program : Presentation.Program) (policy : Presentation.Policy)
      (priors : List PriorArgument) :
      Presentation.SupportTerms → Presentation.SupportTerms → Prop where
    | nil : ReconstructsExplicitTerms canon program policy priors .nil .nil
    | cons
        (head : ReconstructsExplicitTerm canon program policy priors term rebuilt)
        (tail : ReconstructsExplicitTerms canon program policy priors rest rebuiltRest) :
        ReconstructsExplicitTerms canon program policy priors (.cons term rest)
          (.cons rebuilt rebuiltRest)

  /-- Parser-supported explicit discharges are leaf-shaped source references.
  This explicit premise excludes the non-leaf AST case that production preserves
  unchanged, preventing Lean from silently assigning it recursive semantics. -/
  inductive ReconstructsExplicitDischarges (canon : String → String)
      (program : Presentation.Program) (policy : Presentation.Policy)
      (priors : List PriorArgument) :
      Presentation.Discharges → Presentation.Discharges → Prop where
    | nil : ReconstructsExplicitDischarges canon program policy priors .nil .nil
    | cons
        (hreference : ChecksReference program priors ⟨leaf.val⟩ resolved)
        (tail : ReconstructsExplicitDischarges canon program policy priors rest rebuiltRest) :
        ReconstructsExplicitDischarges canon program policy priors
          (.cons question (.leaf leaf) rest)
          (.cons question resolved.term rebuiltRest)
end

/-- Independent conclusion lookup over a reconstructed term. -/
inductive ChecksConclusion (program : Presentation.Program)
    (policy : Presentation.Policy) :
    Presentation.SupportTerm → Atom → Prop where
  | leaf (h : leafProp? program leaf = some proposition) :
      ChecksConclusion program policy (.leaf leaf) proposition
  | rule
      (hrule : FindsRule policy.rules ruleId rule)
      (hinst : instantiateSurfaceAtom theta rule.conclusion = some proposition) :
      ChecksConclusion program policy
        (.rule ruleId theta premises discharges holes assurance) proposition

/-- Why one argument of the declaration fold failed.  Authored-conclusion
failures are separate from reconstruction/certificate failures so the surface
error preserves production diagnostics. -/
inductive ReconstructFailure where
  | build : Presentation.ArgId → ReconstructFailure
  | lower : Presentation.ArgId → ReconstructFailure
  | conclusionMismatch : Presentation.ArgId → Presentation.PropId → ReconstructFailure
  | challengeTargetUndeclared : Presentation.ArgId → ReconstructFailure

/-- Lookup of a declared claim formal in declaration order. -/
def claimFormalIn? (declarations : List Presentation.Decl)
    (id : Presentation.PropId) : Option Atom :=
  declarations.findSome? fun declaration => match declaration with
    | .claim claim => if claim.id = id then some claim.formal else none
    | _ => none

def claimFormal? (program : Presentation.Program)
    (id : Presentation.PropId) : Option Atom :=
  claimFormalIn? program.decls id

/-- Independent validation of the role announced by an authored argument.
Declared `supportsClaim` roles must agree with the reconstructed conclusion;
an undeclared id is production's derived-support arm.  Challenge roles only
validate the declared target namespace at this stage. -/
inductive ChecksAuthoredConclusion (canon : String → String)
    (program : Presentation.Program) (derived : Atom) :
    Presentation.ArgConcl → Prop where
  | supportsClaimKnown
      {id : Presentation.PropId} {formal : Atom}
      (hclaim : claimFormal? program id = some formal)
      (hequiv : Lara.equiv canon derived formal) :
      ChecksAuthoredConclusion canon program derived (.supportsClaim id)
  | supportsClaimDerived
      {id : Presentation.PropId}
      (hclaim : claimFormal? program id = none) :
      ChecksAuthoredConclusion canon program derived (.supportsClaim id)
  | supportsDerived {id : Presentation.PropId} :
      ChecksAuthoredConclusion canon program derived (.supportsDerived id)
  | challengesQuestion
      {question : Presentation.QuestionId} {target : Presentation.ArgId}
      (hdeclared : target ∈ argIds program) :
      ChecksAuthoredConclusion canon program derived
        (.challenges (.question question target))
  | challengesLeaf
      {leaf : Presentation.LeafId}
      (hdeclared : leaf ∈ leafIds program) :
      ChecksAuthoredConclusion canon program derived
        (.challenges (.leaf leaf))

/-- Executable counterpart of `ChecksAuthoredConclusion`, with the exact two
production failure classes. -/
def checkAuthoredConclusion (canon : String → String)
    (program : Presentation.Program) (argument : Presentation.ArgId)
    (authored : Presentation.ArgConcl) (derived : Atom) :
    Except ReconstructFailure _root_.Unit :=
  match authored with
  | .supportsClaim id =>
      match claimFormal? program id with
      | none => .ok ()
      | some formal =>
          if Lara.equiv canon derived formal then .ok ()
          else .error (.conclusionMismatch argument id)
  | .supportsDerived _ => .ok ()
  | .challenges (.question _ target) =>
      if target ∈ argIds program then .ok ()
      else .error (.challengeTargetUndeclared argument)
  | .challenges (.leaf leaf) =>
      if leaf ∈ leafIds program then .ok ()
      else .error (.challengeTargetUndeclared argument)

theorem checkAuthoredConclusion_sound {program : Presentation.Program}
    {argument : Presentation.ArgId} {authored : Presentation.ArgConcl}
    {derived : Atom}
    (h : checkAuthoredConclusion canon program argument authored derived = .ok ()) :
    ChecksAuthoredConclusion canon program derived authored := by
  cases authored with
  | supportsClaim id =>
      simp only [checkAuthoredConclusion] at h
      cases hclaim : claimFormal? program id with
      | none => exact .supportsClaimDerived hclaim
      | some formal =>
          by_cases hequiv : Lara.equiv canon derived formal
          · exact .supportsClaimKnown hclaim hequiv
          · simp [hclaim, hequiv] at h
  | supportsDerived id => exact .supportsDerived
  | challenges target =>
      cases target with
      | question question target =>
          by_cases hdeclared : target ∈ argIds program
          · exact .challengesQuestion hdeclared
          · simp [checkAuthoredConclusion, hdeclared] at h
      | leaf leaf =>
          by_cases hdeclared : leaf ∈ leafIds program
          · exact .challengesLeaf hdeclared
          · simp [checkAuthoredConclusion, hdeclared] at h

theorem checkAuthoredConclusion_complete {program : Presentation.Program}
    {argument : Presentation.ArgId} {authored : Presentation.ArgConcl}
    {derived : Atom}
    (h : ChecksAuthoredConclusion canon program derived authored) :
    checkAuthoredConclusion canon program argument authored derived = .ok () := by
  cases h with
  | supportsClaimKnown hclaim hequiv =>
      simp [checkAuthoredConclusion, hclaim, hequiv]
  | supportsClaimDerived hclaim =>
      simp [checkAuthoredConclusion, hclaim]
  | supportsDerived => rfl
  | challengesQuestion hdeclared =>
      simp [checkAuthoredConclusion, hdeclared]
  | challengesLeaf hdeclared =>
      simp [checkAuthoredConclusion, hdeclared]

/-- Assurance lowering is split by authored form. Certificate payload lowering
is delegated to the already verified backend-specific lowering boundary. -/
inductive ChecksAssurance (env : Env canon) (program : Presentation.Program)
    (rule : Presentation.Rule) (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm) :
    Presentation.Assurance → Lara.Support.Assurance → Prop where
  | none : ChecksAssurance env program rule priors premises .none .none
  | trusted : ChecksAssurance env program rule priors premises .trusted .trusted
  | cert
      (hlower : lowerAssuranceCertificate env program rule priors premises
        (.cert certificate) = some core) :
      ChecksAssurance env program rule priors premises (.cert certificate) core

mutual
  /-- Recursive presentation-to-core support derivation. -/
  inductive ChecksCertificate (env : Env canon) (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument) :
      Presentation.SupportTerm → Lara.Support.SupportTerm → Prop where
    | leaf {leaf} :
        ChecksCertificate env program policy priors (.leaf leaf)
          (.leaf (toSupportLeafId leaf))
    | rule
        (hrule : FindsRule policy.rules ruleId rule)
        (hpremises : ChecksCertificates env program policy priors premises corePremises)
        (hdischarges : ChecksCertificateDischarges env program policy priors
          discharges coreDischarges)
        (hassurance : ChecksAssurance env program rule priors
          (supportTermsToList premises) assurance coreAssurance) :
        ChecksCertificate env program policy priors
          (.rule ruleId theta premises discharges holes assurance)
          (.inst (toSupportRuleId ruleId)
            (theta.map fun pair => (toSupportParam pair.1, pair.2))
            corePremises coreDischarges (holes.map toSupportObligationId) coreAssurance)

  inductive ChecksCertificates (env : Env canon) (program : Presentation.Program)
      (policy : Presentation.Policy) (priors : List PriorArgument) :
      Presentation.SupportTerms → List Lara.Support.SupportTerm → Prop where
    | nil : ChecksCertificates env program policy priors .nil []
    | cons
        (head : ChecksCertificate env program policy priors term core)
        (tail : ChecksCertificates env program policy priors rest coreRest) :
        ChecksCertificates env program policy priors (.cons term rest) (core :: coreRest)

  inductive ChecksCertificateDischarges (env : Env canon)
      (program : Presentation.Program) (policy : Presentation.Policy)
      (priors : List PriorArgument) :
      Presentation.Discharges →
        List (Lara.Support.QuestionId × Lara.Support.SupportTerm) → Prop where
    | nil : ChecksCertificateDischarges env program policy priors .nil []
    | cons
        (head : ChecksCertificate env program policy priors term core)
        (tail : ChecksCertificateDischarges env program policy priors rest coreRest) :
        ChecksCertificateDischarges env program policy priors
          (.cons question term rest) ((toSupportQuestionId question, core) :: coreRest)
end

/-- One argument is derived by its authored form, then its reconstructed term
is recursively lowered. No constructor mentions `reconstructArgument`. -/
inductive ChecksArgument (env : Env canon) (program : Presentation.Program)
    (policy : Presentation.Policy) (priors : List PriorArgument) :
    Presentation.Arg → PriorArgument → Lara.Support.SupportTerm → Prop where
  | explicit {id : Presentation.ArgId}
      (hreconstruct : ReconstructsExplicitTerm canon program policy priors term rebuilt)
      (hconclusion : ChecksConclusion program policy rebuilt conclusion)
      (hauthored : ChecksAuthoredConclusion canon program conclusion authoredConclusion)
      (hcertificate : ChecksCertificate env program policy priors rebuilt core) :
      ChecksArgument env program policy priors
        ⟨id, authoredConclusion, .explicitTheta term⟩
        ⟨id, rebuilt, conclusion⟩ core
  | inferred {id : Presentation.ArgId}
      (hrule : FindsRule policy.rules ruleId rule)
      (hlength : references.length = rule.premises.length)
      (hreferences : ChecksReferences program priors references resolved)
      (hmatch : ChecksPremiseMatch [] rule.premises resolved theta)
      (hcovered : ParamsCovered rule.params theta)
      (hdischarges : ChecksNamedDischarges program priors rule discharges resolvedDischarges)
      (hconclusion : instantiateSurfaceAtom theta rule.conclusion = some conclusion)
      (hauthored : ChecksAuthoredConclusion canon program conclusion authoredConclusion)
      (hcertificate : ChecksCertificate env program policy priors
        (.rule ruleId theta
          (supportTermsFromList (resolved.map (·.term)))
          (dischargesFromList resolvedDischarges) holes assurance) core) :
      ChecksArgument env program policy priors
        ⟨id, authoredConclusion,
          .inferTheta ruleId references discharges holes assurance⟩
        ⟨id, .rule ruleId theta
          (supportTermsFromList (resolved.map (·.term)))
          (dischargesFromList resolvedDischarges) holes assurance, conclusion⟩ core

/-- The core term a resolved argument id denotes. -/
def findArgTerm (args : List (Presentation.ArgId × Lara.Support.SupportTerm))
    (id : Presentation.ArgId) : Option Lara.Support.SupportTerm :=
  (args.find? fun entry => decide (entry.1 = id)).map Prod.snd

/-- Walk an authored surface path over a core support term, producing the
core position. Mirrors `nextOccurrence?` step-for-step: a numeric step is a
premise index; a name is first a premise label, then a question id whose
discharge is followed. -/
def resolvePathCore (policy : Presentation.Policy) :
    Lara.Support.SupportTerm → List Presentation.SurfaceStep → Option Lara.Attack.Pos
  | _, [] => some []
  | term, step :: rest =>
      match step with
      | .index index =>
          if index < 0 then none else
          match term with
          | .leaf _ => none
          | .inst _ _ children _ _ _ =>
              match children[index.toNat]? with
              | none => none
              | some next =>
                  (resolvePathCore policy next rest).map
                    (Lara.Attack.PosElem.prem index.toNat :: ·)
      | .name name =>
          match term with
          | .leaf _ => none
          | .inst ruleId _ children discharges _ _ =>
              match ruleById policy ⟨ruleId.name⟩ with
              | none => none
              | some rule =>
                  match labelIndex? rule name with
                  | some index =>
                      match children[index]? with
                      | none => none
                      | some next =>
                          (resolvePathCore policy next rest).map
                            (Lara.Attack.PosElem.prem index :: ·)
                  | none =>
                      match (questionIds rule).find? (fun q => q.val == name) with
                      | none => none
                      | some question =>
                          match Lara.Attack.lookupDis discharges
                              (toSupportQuestionId question) with
                          | none => none
                          | some next =>
                              (resolvePathCore policy next rest).map
                                (Lara.Attack.PosElem.ques
                                  (toSupportQuestionId question) :: ·)

/-- Resolve one surface attack against the resolved core argument terms:
endpoints by argument id, the authored path to a core position. -/
def resolveSurfaceAttack (policy : Presentation.Policy)
    (args : List (Presentation.ArgId × Lara.Support.SupportTerm)) :
    Presentation.SurfaceAttack → Option Lara.Attack.Attack
  | .rebut source target => do
      let sourceTerm ← findArgTerm args source
      let targetTerm ← findArgTerm args target
      some (.rebut sourceTerm targetTerm)
  | .undercut source target path => do
      let sourceTerm ← findArgTerm args source
      let targetTerm ← findArgTerm args target
      let pos ← resolvePathCore policy targetTerm path
      some (.undercut sourceTerm targetTerm pos)
  | .undermine source target path => do
      let sourceTerm ← findArgTerm args source
      let targetTerm ← findArgTerm args target
      let pos ← resolvePathCore policy targetTerm path
      some (.undermine sourceTerm targetTerm pos)

/-- Resolve every surface attack in order; the failure carries the offending
attack's endpoints. -/
def resolveSurfaceAttacks (policy : Presentation.Policy)
    (args : List (Presentation.ArgId × Lara.Support.SupportTerm)) :
    List Presentation.SurfaceAttack →
      Except (Presentation.ArgId × Presentation.ArgId) (List Lara.Attack.Attack)
  | [] => .ok []
  | attack :: rest =>
      match resolveSurfaceAttack policy args attack with
      | none => .error (attackEndpoints attack)
      | some resolved =>
          match resolveSurfaceAttacks policy args rest with
          | .error failure => .error failure
          | .ok resolvedRest => .ok (resolved :: resolvedRest)

/-- Structural path derivation over a core support term. -/
inductive ChecksPath (policy : Presentation.Policy) :
    Lara.Support.SupportTerm → List Presentation.SurfaceStep → Lara.Attack.Pos → Prop where
  | nil {term} : ChecksPath policy term [] []
  | index
      (hnonnegative : 0 ≤ index)
      (hchild : children[index.toNat]? = some child)
      (tail : ChecksPath policy child rest position) :
      ChecksPath policy
        (.inst rule theta children discharges holes assurance)
        (.index index :: rest)
        (.prem index.toNat :: position)
  | premise
      (hrule : FindsRule policy.rules ⟨ruleId.name⟩ rule)
      (hlabel : labelIndex? rule name = some index)
      (hchild : children[index]? = some child)
      (tail : ChecksPath policy child rest position) :
      ChecksPath policy
        (.inst ruleId theta children discharges holes assurance)
        (.name name :: rest)
        (.prem index :: position)
  | question
      (hrule : FindsRule policy.rules ⟨ruleId.name⟩ rule)
      (hlabel : labelIndex? rule name = none)
      (hquestion : (questionIds rule).find? (fun q => q.val == name) = some question)
      (hdischarge : Lara.Attack.lookupDis discharges
        (toSupportQuestionId question) = some child)
      (tail : ChecksPath policy child rest position) :
      ChecksPath policy
        (.inst ruleId theta children discharges holes assurance)
        (.name name :: rest)
        (.ques (toSupportQuestionId question) :: position)

/-- One surface attack resolves by endpoint lookup and structural path
derivation. No constructor mentions `resolveSurfaceAttack`. -/
inductive ChecksAttack (policy : Presentation.Policy)
    (args : List (Presentation.ArgId × Lara.Support.SupportTerm)) :
    Presentation.SurfaceAttack → Lara.Attack.Attack → Prop where
  | rebut
      (hsource : findArgTerm args source = some sourceTerm)
      (htarget : findArgTerm args target = some targetTerm) :
      ChecksAttack policy args (.rebut source target) (.rebut sourceTerm targetTerm)
  | undercut
      (hsource : findArgTerm args source = some sourceTerm)
      (htarget : findArgTerm args target = some targetTerm)
      (hpath : ChecksPath policy targetTerm path position) :
      ChecksAttack policy args (.undercut source target path)
        (.undercut sourceTerm targetTerm position)
  | undermine
      (hsource : findArgTerm args source = some sourceTerm)
      (htarget : findArgTerm args target = some targetTerm)
      (hpath : ChecksPath policy targetTerm path position) :
      ChecksAttack policy args (.undermine source target path)
        (.undermine sourceTerm targetTerm position)

/-- Every declared surface attack resolves, in declaration order. -/
inductive ChecksAttacks (policy : Presentation.Policy)
    (args : List (Presentation.ArgId × Lara.Support.SupportTerm)) :
    List Presentation.SurfaceAttack → List Lara.Attack.Attack → Prop where
  | nil : ChecksAttacks policy args [] []
  | cons {attack resolved rest resolvedRest}
      (head : ChecksAttack policy args attack resolved)
      (tail : ChecksAttacks policy args rest resolvedRest) :
      ChecksAttacks policy args (attack :: rest) (resolved :: resolvedRest)

/-- One semantic declaration against the prior-argument environment. Comparison
blocks have already been eliminated by `ExpandsComparisons`, so only `.arg`
extends the environment. -/
inductive ChecksDeclaration (env : Env canon) (program : Presentation.Program)
    (policy : Presentation.Policy) (priors : List PriorArgument) :
    Presentation.Decl → List PriorArgument → List ReconstructedArgument → Prop where
  | leaf {leaf} : ChecksDeclaration env program policy priors (.leaf leaf) [] []
  | claim {claim} : ChecksDeclaration env program policy priors (.claim claim) [] []
  | status {status} : ChecksDeclaration env program policy priors (.status status) [] []
  | group {group} : ChecksDeclaration env program policy priors (.group group) [] []
  | attack {attack} : ChecksDeclaration env program policy priors (.attack attack) [] []
  | arg {argument built core}
      (h : ChecksArgument env program policy priors argument built core) :
      ChecksDeclaration env program policy priors (.arg argument) [built]
        [⟨argument, built, core⟩]

/-- The declaration fold threading prior arguments left-to-right: every
argument is derived against the declarations before it, so a reference to a
later-only argument is unrepresentable in a successful derivation. -/
inductive ChecksProgram (env : Env canon) (program : Presentation.Program)
    (policy : Presentation.Policy) :
    List Presentation.Decl → List PriorArgument → List ReconstructedArgument → Prop where
  | nil {priors} : ChecksProgram env program policy [] priors []
  | cons {priors declaration rest news newPairs pairs}
      (head : ChecksDeclaration env program policy priors declaration news newPairs)
      (tail : ChecksProgram env program policy rest (priors ++ news) pairs) :
      ChecksProgram env program policy (declaration :: rest) priors (newPairs ++ pairs)

/-- The executable declaration fold mirroring `ChecksProgram`. -/
def reconstructArgs (env : Env canon) (program : Presentation.Program)
    (policy : Presentation.Policy) :
    List Presentation.Decl → List PriorArgument →
      Except ReconstructFailure (List ReconstructedArgument)
  | [], _ => .ok []
  | .arg argument :: rest, priors =>
      match reconstructArgument canon program policy priors argument with
      | none => .error (.build argument.id)
      | some built =>
          match lowerToSupportTerm env program policy priors built.term with
          | none => .error (.lower argument.id)
          | some core =>
              match checkAuthoredConclusion canon program argument.id
                  argument.concl built.conclusion with
              | .error failure => .error failure
              | .ok _ =>
                  match reconstructArgs env program policy rest (priors ++ [built]) with
                  | .error failure => .error failure
                  | .ok tail => .ok (⟨argument, built, core⟩ :: tail)
  | .comparison comparison :: _, _ => .error (.build comparison.recheckArg)
  | _ :: rest, priors => reconstructArgs env program policy rest priors

/-! ### Executable/derivational correspondence -/

theorem findsRule_sound {rules id rule}
    (h : FindsRule rules id rule) :
    rules.find? (fun candidate => decide (candidate.id = id)) = some rule := by
  induction h with
  | here hid => simp [hid]
  | there hne _ ih => simp [hne, ih]

theorem findsRule_complete {rules id rule}
    (h : rules.find? (fun candidate => decide (candidate.id = id)) = some rule) :
    FindsRule rules id rule := by
  induction rules with
  | nil => simp at h
  | cons head rest ih =>
      by_cases heq : head.id = id
      · simp [heq] at h
        cases h
        exact .here heq
      · simp [heq] at h
        exact .there heq (ih h)

theorem ruleById_sound {policy id rule}
    (h : ruleById policy id = some rule) : FindsRule policy.rules id rule :=
  findsRule_complete h

theorem ruleById_complete {policy id rule}
    (h : FindsRule policy.rules id rule) : ruleById policy id = some rule :=
  findsRule_sound h

theorem resolveReference_sound {program priors reference resolved}
    (h : resolveReference program priors reference = some resolved) :
    ChecksReference program priors reference resolved := by
  unfold resolveReference at h
  generalize hl : (declaredLeaves program).filter
    (fun entry => entry.1.val == reference.val) = leaves at h
  generalize ha : priors.filter (fun prior => prior.id.val == reference.val) = args at h
  cases leaves with
  | nil =>
      cases args with
      | nil => simp at h
      | cons prior rest =>
          cases rest with
          | nil =>
              simp at h
              cases h
              exact .argument hl ha
          | cons _ _ => simp at h
  | cons leaf rest =>
      cases rest with
      | nil =>
          cases args with
          | nil =>
              rcases leaf with ⟨leaf, proposition⟩
              simp at h
              cases h
              exact .leaf hl ha
          | cons _ _ => simp at h
      | cons _ _ => simp at h

theorem resolveReference_complete {program priors reference resolved}
    (h : ChecksReference program priors reference resolved) :
    resolveReference program priors reference = some resolved := by
  cases h with
  | leaf hleaves hargs => simp [resolveReference, hleaves, hargs]
  | argument hleaves hargs => simp [resolveReference, hleaves, hargs]

theorem resolveReferences_sound {program priors references resolved}
    (h : resolveReferences program priors references = some resolved) :
    ChecksReferences program priors references resolved := by
  induction references generalizing resolved with
  | nil =>
      simp [resolveReferences] at h
      cases h
      exact .nil
  | cons reference rest ih =>
      simp only [resolveReferences] at h
      cases hhead : resolveReference program priors reference with
      | none => simp [hhead] at h
      | some head =>
          simp only [hhead] at h
          cases htail : resolveReferences program priors rest with
          | none => simp [htail] at h
          | some tail =>
              simp only [htail] at h
              cases h
              exact .cons (resolveReference_sound hhead) (ih htail)

theorem resolveReferences_complete {program priors references resolved}
    (h : ChecksReferences program priors references resolved) :
    resolveReferences program priors references = some resolved := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
      simp [resolveReferences, resolveReference_complete head, ih]

theorem matchResolvedPremises_sound {subst patterns references out}
    (h : matchResolvedPremises subst patterns references = some out) :
    ChecksPremiseMatch subst patterns references out := by
  induction patterns generalizing subst references out with
  | nil =>
      cases references <;> simp [matchResolvedPremises] at h
      cases h
      exact .nil
  | cons pattern patterns ih =>
      cases references with
      | nil => simp [matchResolvedPremises] at h
      | cons reference references =>
          simp only [matchResolvedPremises] at h
          cases hmatch : matchSurfaceAtom subst pattern reference.conclusion with
          | none => simp [hmatch] at h
          | some next =>
              simp only [hmatch] at h
              exact .cons hmatch (ih h)

theorem matchResolvedPremises_complete {subst patterns references out}
    (h : ChecksPremiseMatch subst patterns references out) :
    matchResolvedPremises subst patterns references = some out := by
  induction h with
  | nil => rfl
  | cons hmatch _ ih => simp [matchResolvedPremises, hmatch, ih]

theorem paramsCoveredB_iff (params : List Presentation.Param) (theta : SurfaceSubst) :
    paramsCoveredB params theta = true ↔ ParamsCovered params theta := by
  unfold paramsCoveredB ParamsCovered
  rw [List.all_eq_true]
  constructor
  · intro h param hmem
    have hok := h param hmem
    cases heq : lookupSurfaceSubst theta param with
    | none => simp [heq] at hok
    | some term => exact ⟨term, rfl⟩
  · intro h param hmem
    obtain ⟨term, hterm⟩ := h param hmem
    simp [hterm]

theorem resolveNamedDischarges_sound {program priors rule authored resolved}
    (h : resolveNamedDischarges program priors rule authored = some resolved) :
    ChecksNamedDischarges program priors rule authored resolved := by
  induction authored generalizing resolved with
  | nil =>
      simp [resolveNamedDischarges] at h
      cases h
      exact .nil
  | cons entry rest ih =>
      rcases entry with ⟨question, reference⟩
      simp [resolveNamedDischarges] at h
      rcases h with ⟨hquestion, h⟩
      cases href : resolveReference program priors reference with
      | none => simp [href] at h
      | some one =>
          simp only [href] at h
          cases hrest : resolveNamedDischarges program priors rule rest with
          | none => simp [hrest] at h
          | some tail =>
              simp only [hrest] at h
              cases h
              exact .cons hquestion (resolveReference_sound href) (ih hrest)

theorem resolveNamedDischarges_complete {program priors rule authored resolved}
    (h : ChecksNamedDischarges program priors rule authored resolved) :
    resolveNamedDischarges program priors rule authored = some resolved := by
  induction h with
  | nil => rfl
  | @cons question reference resolved rest resolvedRest hquestion hreference tail ih =>
      simp [resolveNamedDischarges, hquestion,
        resolveReference_complete hreference, ih]

theorem resolveImplicitPremises_sound {canon program priors theta patterns terms}
    (h : resolveImplicitPremises canon program priors theta patterns = some terms) :
    ChecksImplicitPremises canon program priors theta patterns terms := by
  induction patterns generalizing terms with
  | nil =>
      simp [resolveImplicitPremises] at h
      cases h
      exact .nil
  | cons pattern rest ih =>
      simp only [resolveImplicitPremises, resolveImplicitPremise] at h
      cases hground : instantiateSurfaceAtom theta pattern with
      | none => simp [hground] at h
      | some ground =>
          simp only [hground] at h
          cases hm : premiseMatches canon program priors ground with
          | nil => simp [hm] at h
          | cons term tailMatches =>
              cases tailMatches with
              | nil =>
                  cases htail : resolveImplicitPremises canon program priors theta rest with
                  | none => simp [hm, htail] at h
                  | some tail =>
                      simp [hm, htail] at h
                      cases h
                      exact .cons hground hm (ih htail)
              | cons _ _ => simp [hm] at h

theorem resolveImplicitPremises_complete {canon program priors theta patterns terms}
    (h : ChecksImplicitPremises canon program priors theta patterns terms) :
    resolveImplicitPremises canon program priors theta patterns = some terms := by
  induction h with
  | nil => rfl
  | cons hground hunique _ ih =>
      simp [resolveImplicitPremises, resolveImplicitPremise, hground, hunique, ih]

mutual
  private def explicitTermSize : Presentation.SupportTerm → Nat
    | .leaf _ => 1
    | .rule _ _ premises discharges _ _ =>
        1 + explicitTermsSize premises + explicitDischargesSize discharges

  private def explicitTermsSize : Presentation.SupportTerms → Nat
    | .nil => 0
    | .cons term rest => 1 + explicitTermSize term + explicitTermsSize rest

  private def explicitDischargesSize : Presentation.Discharges → Nat
    | .nil => 0
    | .cons _ term rest => 1 + explicitTermSize term + explicitDischargesSize rest
end

mutual
  theorem reconstructExplicitTerm_sound (canon : String → String)
      (program : Presentation.Program) (policy : Presentation.Policy)
      (priors : List PriorArgument) {source rebuilt}
      (h : reconstructExplicitTerm canon program policy priors source = some rebuilt) :
      ReconstructsExplicitTerm canon program policy priors source rebuilt := by
    cases source with
    | leaf leaf =>
        simp [reconstructExplicitTerm] at h
        cases h
        exact .leaf
    | rule ruleId theta premises discharges holes assurance =>
        cases hrule : ruleById policy ruleId with
        | none =>
            have hnone :
                reconstructExplicitTerm canon program policy priors
                  (.rule ruleId theta premises discharges holes assurance) = none := by
              cases premises <;> simp [reconstructExplicitTerm, hrule]
            have impossible : (none : Option Presentation.SupportTerm) = some rebuilt :=
              hnone.symm.trans h
            cases impossible
        | some rule =>
            by_cases harity : theta.length = rule.params.length
            · cases premises with
              | nil =>
                  cases hprem : resolveImplicitPremises canon program priors
                      (rule.params.zip (theta.map Prod.snd)) rule.premises with
                  | none => simp [reconstructExplicitTerm, hrule, harity, hprem] at h
                  | some rebuiltPremises =>
                      cases hdis : reconstructExplicitDischarges canon program policy
                          priors discharges with
                      | none =>
                          simp [reconstructExplicitTerm, hrule, harity, hprem, hdis] at h
                      | some rebuiltDischarges =>
                          have heq : rebuilt = .rule ruleId
                              (rule.params.zip (theta.map Prod.snd))
                              rebuiltPremises rebuiltDischarges holes assurance := by
                            simpa [reconstructExplicitTerm, hrule, harity, hprem, hdis] using h.symm
                          rw [heq]
                          exact .implicit (ruleById_sound hrule) harity
                            (resolveImplicitPremises_sound hprem)
                            (reconstructExplicitDischarges_sound canon program policy priors hdis)
              | cons premise premises =>
                  cases hprem : reconstructExplicitTerms canon program policy priors
                      (.cons premise premises) with
                  | none => simp [reconstructExplicitTerm, hrule, harity, hprem] at h
                  | some rebuiltPremises =>
                      cases hdis : reconstructExplicitDischarges canon program policy
                          priors discharges with
                      | none =>
                          simp [reconstructExplicitTerm, hrule, harity, hprem, hdis] at h
                      | some rebuiltDischarges =>
                          have heq : rebuilt = .rule ruleId
                              (rule.params.zip (theta.map Prod.snd))
                              rebuiltPremises rebuiltDischarges holes assurance := by
                            simpa [reconstructExplicitTerm, hrule, harity, hprem, hdis] using h.symm
                          rw [heq]
                          exact .provided (ruleById_sound hrule) harity
                            (reconstructExplicitTerms_sound canon program policy priors hprem)
                            (reconstructExplicitDischarges_sound canon program policy priors hdis)
            · cases premises <;> simp [reconstructExplicitTerm, hrule, harity] at h
  termination_by explicitTermSize source
  decreasing_by
    all_goals simp_all [explicitTermSize, explicitTermsSize, explicitDischargesSize]
    all_goals omega

  theorem reconstructExplicitTerms_sound (canon : String → String)
      (program : Presentation.Program) (policy : Presentation.Policy)
      (priors : List PriorArgument) {source rebuilt}
      (h : reconstructExplicitTerms canon program policy priors source = some rebuilt) :
      ReconstructsExplicitTerms canon program policy priors source rebuilt := by
    cases source with
    | nil =>
        simp [reconstructExplicitTerms] at h
        cases h
        exact .nil
    | cons term rest =>
        simp only [reconstructExplicitTerms] at h
        cases hhead : reconstructExplicitTerm canon program policy priors term with
        | none => simp [hhead] at h
        | some head =>
            simp only [hhead] at h
            cases htail : reconstructExplicitTerms canon program policy priors rest with
            | none => simp [htail] at h
            | some tail =>
                simp only [htail] at h
                cases h
                exact .cons
                  (reconstructExplicitTerm_sound canon program policy priors hhead)
                  (reconstructExplicitTerms_sound canon program policy priors htail)
  termination_by explicitTermsSize source
  decreasing_by
    all_goals simp_all [explicitTermSize, explicitTermsSize, explicitDischargesSize]
    all_goals omega

  theorem reconstructExplicitDischarges_sound (canon : String → String)
      (program : Presentation.Program) (policy : Presentation.Policy)
      (priors : List PriorArgument) {source rebuilt}
      (h : reconstructExplicitDischarges canon program policy priors source = some rebuilt) :
      ReconstructsExplicitDischarges canon program policy priors source rebuilt := by
    cases source with
    | nil =>
        simp [reconstructExplicitDischarges] at h
        cases h
        exact .nil
    | cons question term rest =>
        cases term with
        | leaf leaf =>
            simp only [reconstructExplicitDischarges] at h
            cases href : resolveReference program priors ⟨leaf.val⟩ with
            | none => simp [href] at h
            | some resolved =>
                simp only [href] at h
                cases htail : reconstructExplicitDischarges canon program policy priors rest with
                | none => simp [htail] at h
                | some tail =>
                    simp only [htail] at h
                    cases h
                    exact .cons (resolveReference_sound href)
                      (reconstructExplicitDischarges_sound canon program policy priors htail)
        | rule rule theta premises discharges holes assurance =>
            simp [reconstructExplicitDischarges] at h
  termination_by explicitDischargesSize source
  decreasing_by
    all_goals simp_all [explicitTermSize, explicitTermsSize, explicitDischargesSize]
    all_goals omega
end
mutual
  theorem reconstructExplicitTerm_complete {canon program policy priors source rebuilt}
      (h : ReconstructsExplicitTerm canon program policy priors source rebuilt) :
      reconstructExplicitTerm canon program policy priors source = some rebuilt := by
    cases h with
    | leaf => rfl
    | implicit hrule harity hpremises hdischarges =>
        simp [reconstructExplicitTerm, ruleById_complete hrule, harity,
          resolveImplicitPremises_complete hpremises,
          reconstructExplicitDischarges_complete hdischarges]
    | provided hrule harity hpremises hdischarges =>
        simp [reconstructExplicitTerm, ruleById_complete hrule, harity,
          reconstructExplicitTerms_complete hpremises,
          reconstructExplicitDischarges_complete hdischarges]

  theorem reconstructExplicitTerms_complete {canon program policy priors source rebuilt}
      (h : ReconstructsExplicitTerms canon program policy priors source rebuilt) :
      reconstructExplicitTerms canon program policy priors source = some rebuilt := by
    cases h with
    | nil => rfl
    | cons head tail =>
        simp [reconstructExplicitTerms, reconstructExplicitTerm_complete head,
          reconstructExplicitTerms_complete tail]

  theorem reconstructExplicitDischarges_complete {canon program policy priors source rebuilt}
      (h : ReconstructsExplicitDischarges canon program policy priors source rebuilt) :
      reconstructExplicitDischarges canon program policy priors source = some rebuilt := by
    cases h with
    | nil => rfl
    | cons hreference tail =>
        simp [reconstructExplicitDischarges, resolveReference_complete hreference,
          reconstructExplicitDischarges_complete tail]
end

theorem conclOfTerm_sound {program policy term conclusion}
    (h : conclOfTerm program policy term = some conclusion) :
    ChecksConclusion program policy term conclusion := by
  cases term with
  | leaf leaf => exact .leaf h
  | rule ruleId theta premises discharges holes assurance =>
      simp only [conclOfTerm] at h
      cases hrule : ruleById policy ruleId with
      | none => simp [hrule] at h
      | some rule =>
          simp only [hrule] at h
          exact .rule (ruleById_sound hrule) h

theorem conclOfTerm_complete {program policy term conclusion}
    (h : ChecksConclusion program policy term conclusion) :
    conclOfTerm program policy term = some conclusion := by
  cases h with
  | leaf hleaf => exact hleaf
  | rule hrule hinst =>
      simp [conclOfTerm, ruleById_complete hrule, hinst]

theorem checksAssurance_complete {env : Env canon} {program rule priors premises authored core}
    (h : ChecksAssurance env program rule priors premises authored core) :
    lowerAssuranceCertificate env program rule priors premises authored = some core := by
  cases h with
  | none => rfl
  | trusted => rfl
  | cert hlower => exact hlower

mutual
  theorem lowerToSupportTerm_sound (env : Env canon) {program policy priors term core}
      (h : lowerToSupportTerm env program policy priors term = some core) :
      ChecksCertificate env program policy priors term core := by
    cases term with
    | leaf leaf =>
        simp [lowerToSupportTerm] at h
        cases h
        exact .leaf
    | rule ruleId theta premises discharges holes assurance =>
        cases hrule : ruleById policy ruleId with
        | none => simp [lowerToSupportTerm, hrule] at h
        | some rule =>
            cases hassurance : lowerAssuranceCertificate env program rule priors
                (supportTermsToList premises) assurance with
            | none => simp [lowerToSupportTerm, hrule, hassurance] at h
            | some coreAssurance =>
                cases hpremises : lowerToSupportTerms env program policy priors premises with
                | none => simp [lowerToSupportTerm, hrule, hassurance, hpremises] at h
                | some corePremises =>
                    cases hdischarges :
                        lowerToSupportDischarges env program policy priors discharges with
                    | none =>
                        simp [lowerToSupportTerm, hrule, hassurance, hpremises,
                          hdischarges] at h
                    | some coreDischarges =>
                        simp [lowerToSupportTerm, hrule, hassurance, hpremises,
                          hdischarges] at h
                        cases h
                        refine .rule (ruleById_sound hrule)
                          (lowerToSupportTerms_sound env hpremises)
                          (lowerToSupportDischarges_sound env hdischarges) ?_
                        cases assurance with
                        | none => cases hassurance; exact .none
                        | trusted => cases hassurance; exact .trusted
                        | cert certificate => exact .cert hassurance

  theorem lowerToSupportTerms_sound (env : Env canon) {program policy priors terms core}
      (h : lowerToSupportTerms env program policy priors terms = some core) :
      ChecksCertificates env program policy priors terms core := by
    cases terms with
    | nil =>
        simp [lowerToSupportTerms] at h
        cases h
        exact .nil
    | cons term rest =>
        simp only [lowerToSupportTerms] at h
        cases hhead : lowerToSupportTerm env program policy priors term with
        | none => simp [hhead] at h
        | some head =>
            simp only [hhead] at h
            cases htail : lowerToSupportTerms env program policy priors rest with
            | none => simp [htail] at h
            | some tail =>
                simp only [htail] at h
                cases h
                exact .cons (lowerToSupportTerm_sound env hhead)
                  (lowerToSupportTerms_sound env htail)

  theorem lowerToSupportDischarges_sound (env : Env canon)
      {program policy priors discharges core}
      (h : lowerToSupportDischarges env program policy priors discharges = some core) :
      ChecksCertificateDischarges env program policy priors discharges core := by
    cases discharges with
    | nil =>
        simp [lowerToSupportDischarges] at h
        cases h
        exact .nil
    | cons question term rest =>
        simp only [lowerToSupportDischarges] at h
        cases hhead : lowerToSupportTerm env program policy priors term with
        | none => simp [hhead] at h
        | some head =>
            simp only [hhead] at h
            cases htail : lowerToSupportDischarges env program policy priors rest with
            | none => simp [htail] at h
            | some tail =>
                simp only [htail] at h
                cases h
                exact .cons (lowerToSupportTerm_sound env hhead)
                  (lowerToSupportDischarges_sound env htail)
end

mutual
  theorem lowerToSupportTerm_complete {env : Env canon} {program policy priors term core}
      (h : ChecksCertificate env program policy priors term core) :
      lowerToSupportTerm env program policy priors term = some core := by
    cases h with
    | leaf => rfl
    | rule hrule hpremises hdischarges hassurance =>
        simp [lowerToSupportTerm, ruleById_complete hrule,
          checksAssurance_complete hassurance,
          lowerToSupportTerms_complete hpremises,
          lowerToSupportDischarges_complete hdischarges]

  theorem lowerToSupportTerms_complete {env : Env canon} {program policy priors terms core}
      (h : ChecksCertificates env program policy priors terms core) :
      lowerToSupportTerms env program policy priors terms = some core := by
    cases h with
    | nil => rfl
    | cons head tail =>
        simp [lowerToSupportTerms, lowerToSupportTerm_complete head,
          lowerToSupportTerms_complete tail]

  theorem lowerToSupportDischarges_complete {env : Env canon}
      {program policy priors discharges core}
      (h : ChecksCertificateDischarges env program policy priors discharges core) :
      lowerToSupportDischarges env program policy priors discharges = some core := by
    cases h with
    | nil => rfl
    | cons head tail =>
        simp [lowerToSupportDischarges, lowerToSupportTerm_complete head,
          lowerToSupportDischarges_complete tail]
end

/-- Reconstruction alone independently derives the rebuilt term's conclusion;
authored-role and certificate checks are separate judgments. -/
theorem reconstructArgument_conclusion_sound {program policy priors argument built}
    (hbuild : reconstructArgument canon program policy priors argument = some built) :
    ChecksConclusion program policy built.term built.conclusion := by
  rcases argument with ⟨id, authoredConclusion, instantiation⟩
  cases instantiation with
  | explicitTheta term =>
      simp only [reconstructArgument] at hbuild
      cases hreconstruct :
          reconstructExplicitTerm canon program policy priors term with
      | none => simp [hreconstruct] at hbuild
      | some rebuilt =>
          simp only [hreconstruct] at hbuild
          cases hconclusion : conclOfTerm program policy rebuilt with
          | none => simp [hconclusion] at hbuild
          | some conclusion =>
              simp [hconclusion] at hbuild
              cases hbuild
              exact conclOfTerm_sound hconclusion
  | inferTheta ruleId references discharges holes assurance =>
      simp only [reconstructArgument, buildArgument] at hbuild
      cases hrule : ruleById policy ruleId with
      | none => simp [hrule] at hbuild
      | some rule =>
          simp only [hrule] at hbuild
          by_cases hlength : references.length = rule.premises.length
          · simp [hlength] at hbuild
            cases hreferences : resolveReferences program priors references with
            | none => simp [hreferences] at hbuild
            | some resolved =>
                simp only [hreferences, Option.bind_some] at hbuild
                cases hmatch : matchResolvedPremises [] rule.premises resolved with
                | none => simp [hmatch] at hbuild
                | some theta =>
                    simp only [hmatch, Option.bind_some] at hbuild
                    cases hcovered : paramsCoveredB rule.params theta with
                    | false => simp [hcovered] at hbuild
                    | true =>
                        simp only [hcovered, Bool.true_eq_false, ↓reduceIte] at hbuild
                        cases hdischarges :
                            resolveNamedDischarges program priors rule discharges with
                        | none => simp [hdischarges] at hbuild
                        | some resolvedDischarges =>
                            simp only [hdischarges] at hbuild
                            cases hconclusion :
                                instantiateSurfaceAtom theta rule.conclusion with
                            | none => simp [hconclusion] at hbuild
                            | some conclusion =>
                                simp only [hconclusion] at hbuild
                                cases hbuild
                                exact .rule (ruleById_sound hrule) hconclusion
          · simp [hlength] at hbuild

theorem reconstructArgument_sound (env : Env canon) {program policy priors argument built core}
    (hbuild : reconstructArgument canon program policy priors argument = some built)
    (hauthored : ChecksAuthoredConclusion canon program built.conclusion argument.concl)
    (hlower : lowerToSupportTerm env program policy priors built.term = some core) :
    ChecksArgument env program policy priors argument built core := by
  rcases argument with ⟨id, authoredConclusion, instantiation⟩
  cases instantiation with
  | explicitTheta term =>
      simp only [reconstructArgument] at hbuild
      cases hreconstruct :
          reconstructExplicitTerm canon program policy priors term with
      | none => simp [hreconstruct] at hbuild
      | some rebuilt =>
          simp only [hreconstruct] at hbuild
          cases hconclusion : conclOfTerm program policy rebuilt with
          | none => simp [hconclusion] at hbuild
          | some conclusion =>
              simp [hconclusion] at hbuild
              cases hbuild
              exact .explicit (reconstructExplicitTerm_sound canon program policy priors hreconstruct)
                (conclOfTerm_sound hconclusion) hauthored
                (lowerToSupportTerm_sound env hlower)
  | inferTheta ruleId references discharges holes assurance =>
      simp only [reconstructArgument, buildArgument] at hbuild
      cases hrule : ruleById policy ruleId with
      | none => simp [hrule] at hbuild
      | some rule =>
          simp only [hrule] at hbuild
          by_cases hlength : references.length = rule.premises.length
          · simp [hlength] at hbuild
            cases hreferences : resolveReferences program priors references with
            | none => simp [hreferences] at hbuild
            | some resolved =>
                simp only [hreferences, Option.bind_some] at hbuild
                cases hmatch : matchResolvedPremises [] rule.premises resolved with
                | none => simp [hmatch] at hbuild
                | some theta =>
                    simp only [hmatch, Option.bind_some] at hbuild
                    cases hcovered : paramsCoveredB rule.params theta with
                    | false =>
                        simp [hcovered] at hbuild
                    | true =>
                        simp only [hcovered, Bool.true_eq_false, ↓reduceIte] at hbuild
                        cases hdischarges :
                            resolveNamedDischarges program priors rule discharges with
                        | none => simp [hdischarges] at hbuild
                        | some resolvedDischarges =>
                            simp only [hdischarges] at hbuild
                            cases hconclusion :
                                instantiateSurfaceAtom theta rule.conclusion with
                            | none => simp [hconclusion] at hbuild
                            | some conclusion =>
                                simp only [hconclusion] at hbuild
                                cases hbuild
                                exact .inferred (ruleById_sound hrule) hlength
                                  (resolveReferences_sound hreferences)
                                  (matchResolvedPremises_sound hmatch)
                                  ((paramsCoveredB_iff _ _).1 hcovered)
                                  (resolveNamedDischarges_sound hdischarges)
                                  hconclusion hauthored
                                  (lowerToSupportTerm_sound env hlower)
          · simp [hlength] at hbuild

theorem reconstructArgument_complete {env : Env canon}
    {program policy priors argument built core}
    (h : ChecksArgument env program policy priors argument built core) :
    reconstructArgument canon program policy priors argument = some built ∧
      checkAuthoredConclusion canon program argument.id argument.concl
          built.conclusion = .ok () ∧
      lowerToSupportTerm env program policy priors built.term = some core := by
  cases h with
  | explicit hreconstruct hconclusion hauthored hcertificate =>
      exact ⟨by
        simp [reconstructArgument, reconstructExplicitTerm_complete hreconstruct,
          conclOfTerm_complete hconclusion],
        checkAuthoredConclusion_complete hauthored,
        lowerToSupportTerm_complete hcertificate⟩
  | inferred hrule hlength hreferences hmatch hcovered hdischarges hconclusion
      hauthored hcertificate =>
      have hcoveredB : paramsCoveredB _ _ = true :=
        (paramsCoveredB_iff _ _).2 hcovered
      exact ⟨by
        simp [reconstructArgument, buildArgument, ruleById_complete hrule, hlength,
          resolveReferences_complete hreferences, matchResolvedPremises_complete hmatch,
          hcoveredB, resolveNamedDischarges_complete hdischarges, hconclusion],
        checkAuthoredConclusion_complete hauthored,
        lowerToSupportTerm_complete hcertificate⟩

theorem reconstructArgs_sound (env : Env canon) (program : Presentation.Program)
    (policy : Presentation.Policy) {decls priors pairs}
    (h : reconstructArgs env program policy decls priors = .ok pairs) :
    ChecksProgram env program policy decls priors pairs := by
  induction decls generalizing priors pairs with
  | nil =>
      simp [reconstructArgs] at h
      cases h
      exact .nil
  | cons declaration rest ih =>
      cases declaration with
      | leaf leaf =>
          simp only [reconstructArgs] at h
          have htail : ChecksProgram env program policy rest (priors ++ []) pairs := by
            simpa using ih (priors := priors) h
          exact .cons .leaf htail
      | claim claim =>
          simp only [reconstructArgs] at h
          have htail : ChecksProgram env program policy rest (priors ++ []) pairs := by
            simpa using ih (priors := priors) h
          exact .cons .claim htail
      | attack attack =>
          simp only [reconstructArgs] at h
          have htail : ChecksProgram env program policy rest (priors ++ []) pairs := by
            simpa using ih (priors := priors) h
          exact .cons .attack htail
      | status status =>
          simp only [reconstructArgs] at h
          have htail : ChecksProgram env program policy rest (priors ++ []) pairs := by
            simpa using ih (priors := priors) h
          exact .cons .status htail
      | group group =>
          simp only [reconstructArgs] at h
          have htail : ChecksProgram env program policy rest (priors ++ []) pairs := by
            simpa using ih (priors := priors) h
          exact .cons .group htail
      | comparison comparison =>
          simp [reconstructArgs] at h
      | arg argument =>
          simp only [reconstructArgs] at h
          cases hbuild : reconstructArgument canon program policy priors argument with
          | none => simp [hbuild] at h
          | some built =>
              simp only [hbuild] at h
              cases hlower : lowerToSupportTerm env program policy priors built.term with
              | none => simp [hlower] at h
              | some core =>
                simp only [hlower] at h
                cases hauthored : checkAuthoredConclusion canon program argument.id
                    argument.concl built.conclusion with
                | error failure => simp [hauthored] at h
                | ok _ =>
                  simp only [hauthored] at h
                  cases htail :
                      reconstructArgs env program policy rest (priors ++ [built]) with
                  | error failure => simp [htail] at h
                  | ok tail =>
                      simp only [htail] at h
                      cases h
                      exact .cons (.arg (reconstructArgument_sound env hbuild
                        (checkAuthoredConclusion_sound hauthored) hlower))
                        (ih htail)

theorem reconstructArgs_complete {env : Env canon} {program policy decls priors pairs}
    (h : ChecksProgram env program policy decls priors pairs) :
    reconstructArgs env program policy decls priors = .ok pairs := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | leaf => simpa [reconstructArgs] using ih
      | claim => simpa [reconstructArgs] using ih
      | attack => simpa [reconstructArgs] using ih
      | status => simpa [reconstructArgs] using ih
      | group => simpa [reconstructArgs] using ih
      | arg hargument =>
          obtain ⟨hbuild, hauthored, hlower⟩ :=
            reconstructArgument_complete hargument
          simp [reconstructArgs, hbuild, hauthored, hlower, ih]
theorem resolvePathCore_sound {policy term path position}
    (h : resolvePathCore policy term path = some position) :
    ChecksPath policy term path position := by
  induction path generalizing term position with
  | nil =>
      simp [resolvePathCore] at h
      cases h
      exact .nil
  | cons step rest ih =>
      cases step with
      | index index =>
          cases term with
          | leaf leaf => simp [resolvePathCore] at h
          | inst rule theta children discharges holes assurance =>
              by_cases hnegative : index < 0
              · simp [resolvePathCore, hnegative] at h
              · cases hchild : children[index.toNat]? with
                | none => simp [resolvePathCore, hnegative, hchild] at h
                | some child =>
                    cases htail : resolvePathCore policy child rest with
                    | none => simp [resolvePathCore, hnegative, hchild, htail] at h
                    | some tail =>
                        simp [resolvePathCore, hnegative, hchild, htail] at h
                        cases h
                        exact .index (Int.not_lt.mp hnegative) hchild (ih htail)
      | name name =>
          cases term with
          | leaf leaf => simp [resolvePathCore] at h
          | inst ruleId theta children discharges holes assurance =>
              cases hrule : ruleById policy ⟨ruleId.name⟩ with
              | none => simp [resolvePathCore, hrule] at h
              | some rule =>
                  cases hlabel : labelIndex? rule name with
                  | some index =>
                      cases hchild : children[index]? with
                      | none => simp [resolvePathCore, hrule, hlabel, hchild] at h
                      | some child =>
                          cases htail : resolvePathCore policy child rest with
                          | none =>
                              simp [resolvePathCore, hrule, hlabel, hchild, htail] at h
                          | some tail =>
                              simp [resolvePathCore, hrule, hlabel, hchild, htail] at h
                              cases h
                              exact .premise (ruleById_sound hrule) hlabel hchild (ih htail)
                  | none =>
                      cases hquestion :
                          (questionIds rule).find? (fun q => q.val == name) with
                      | none => simp [resolvePathCore, hrule, hlabel, hquestion] at h
                      | some question =>
                          cases hdischarge : Lara.Attack.lookupDis discharges
                              (toSupportQuestionId question) with
                          | none =>
                              simp [resolvePathCore, hrule, hlabel, hquestion,
                                hdischarge] at h
                          | some child =>
                              cases htail : resolvePathCore policy child rest with
                              | none =>
                                  simp [resolvePathCore, hrule, hlabel, hquestion,
                                    hdischarge, htail] at h
                              | some tail =>
                                  simp [resolvePathCore, hrule, hlabel, hquestion,
                                    hdischarge, htail] at h
                                  cases h
                                  exact .question (ruleById_sound hrule) hlabel
                                    hquestion hdischarge (ih htail)

theorem resolvePathCore_complete {policy term path position}
    (h : ChecksPath policy term path position) :
    resolvePathCore policy term path = some position := by
  induction h with
  | nil => rfl
  | index hnonnegative hchild _ ih =>
      simp [resolvePathCore, Int.not_lt.mpr hnonnegative, hchild, ih]
  | premise hrule hlabel hchild _ ih =>
      simp [resolvePathCore, ruleById_complete hrule, hlabel, hchild, ih]
  | question hrule hlabel hquestion hdischarge _ ih =>
      simp [resolvePathCore, ruleById_complete hrule, hlabel, hquestion,
        hdischarge, ih]

theorem resolveSurfaceAttack_sound {policy args attack resolved}
    (h : resolveSurfaceAttack policy args attack = some resolved) :
    ChecksAttack policy args attack resolved := by
  cases attack with
  | rebut source target =>
      simp only [resolveSurfaceAttack] at h
      cases hsource : findArgTerm args source with
      | none => simp [hsource] at h
      | some sourceTerm =>
          simp only [hsource] at h
          cases htarget : findArgTerm args target with
          | none => simp [htarget] at h
          | some targetTerm =>
              simp [htarget] at h
              cases h
              exact .rebut hsource htarget
  | undercut source target path =>
      simp only [resolveSurfaceAttack] at h
      cases hsource : findArgTerm args source with
      | none => simp [hsource] at h
      | some sourceTerm =>
          simp only [hsource] at h
          cases htarget : findArgTerm args target with
          | none => simp [htarget] at h
          | some targetTerm =>
              simp only [htarget] at h
              cases hpath : resolvePathCore policy targetTerm path with
              | none => simp [hpath] at h
              | some position =>
                  simp [hpath] at h
                  cases h
                  exact .undercut hsource htarget (resolvePathCore_sound hpath)
  | undermine source target path =>
      simp only [resolveSurfaceAttack] at h
      cases hsource : findArgTerm args source with
      | none => simp [hsource] at h
      | some sourceTerm =>
          simp only [hsource] at h
          cases htarget : findArgTerm args target with
          | none => simp [htarget] at h
          | some targetTerm =>
              simp only [htarget] at h
              cases hpath : resolvePathCore policy targetTerm path with
              | none => simp [hpath] at h
              | some position =>
                  simp [hpath] at h
                  cases h
                  exact .undermine hsource htarget (resolvePathCore_sound hpath)

theorem resolveSurfaceAttack_complete {policy args attack resolved}
    (h : ChecksAttack policy args attack resolved) :
    resolveSurfaceAttack policy args attack = some resolved := by
  cases h with
  | rebut hsource htarget =>
      simp [resolveSurfaceAttack, hsource, htarget]
  | undercut hsource htarget hpath =>
      simp [resolveSurfaceAttack, hsource, htarget, resolvePathCore_complete hpath]
  | undermine hsource htarget hpath =>
      simp [resolveSurfaceAttack, hsource, htarget, resolvePathCore_complete hpath]

theorem resolveSurfaceAttacks_sound (policy : Presentation.Policy)
    {args attacks resolved}
    (h : resolveSurfaceAttacks policy args attacks = .ok resolved) :
    ChecksAttacks policy args attacks resolved := by
  induction attacks generalizing resolved with
  | nil =>
      simp [resolveSurfaceAttacks] at h
      cases h
      exact .nil
  | cons attack rest ih =>
      simp only [resolveSurfaceAttacks] at h
      cases hhead : resolveSurfaceAttack policy args attack with
      | none => simp [hhead] at h
      | some head =>
          simp only [hhead] at h
          cases htail : resolveSurfaceAttacks policy args rest with
          | error failure => simp [htail] at h
          | ok tail =>
              simp [htail] at h
              cases h
              exact .cons (resolveSurfaceAttack_sound hhead) (ih htail)

theorem resolveSurfaceAttacks_complete {policy args attacks resolved}
    (h : ChecksAttacks policy args attacks resolved) :
    resolveSurfaceAttacks policy args attacks = .ok resolved := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
      simp [resolveSurfaceAttacks, resolveSurfaceAttack_complete head, ih]

theorem expandDecls_complete_independent (policy : Presentation.Policy)
    (program : Presentation.Program) {source target generated}
    (h : DeclsExpandComparisons policy program source target generated) :
    expandDecls policy program source = .ok (target, generated) := by
  induction h with
  | nil => rfl
  | @keep d ds ts gs hkeep _ ih =>
      cases d <;> simp [expandDecls, isComparison, ih] at hkeep ⊢
  | expand hdata _ ih =>
      simp [expandDecls, comparisonExpansion?_complete hdata, ih]

theorem expandComparisons_complete_independent (policy : Presentation.Policy)
    {program target generated}
    (hfresh : GeneratedIdsFresh program = true)
    (hkeys : (comparisonKeys program).Nodup)
    (h : ExpandsComparisons policy program target generated) :
    expandComparisons policy program = .ok (target, generated) := by
  rcases h with ⟨hdecls, hartifact, hdigest, hpolicy, hbackends, hbindings⟩
  have hgo := expandDecls_complete_independent policy program hdecls
  have hcollision : generatedIdCollisionClaim? program = none := by
    simpa [GeneratedIdsFresh] using hfresh
  have hduplicate : duplicateComparisonClaim? program = none :=
    duplicateComparisonClaim?_eq_none_iff program |>.mpr hkeys
  unfold expandComparisons
  simp [hcollision, hduplicate, hgo]
  cases target
  simp_all

theorem expandComparisons_guards (policy : Presentation.Policy)
    {program target generated}
    (h : expandComparisons policy program = .ok (target, generated)) :
    GeneratedIdsFresh program = true ∧ (comparisonKeys program).Nodup := by
  unfold expandComparisons at h
  cases hcollision : generatedIdCollisionClaim? program with
  | some claim => simp [hcollision] at h
  | none =>
      have hfresh : GeneratedIdsFresh program = true := by
        simpa [GeneratedIdsFresh] using hcollision
      cases hduplicate : duplicateComparisonClaim? program with
      | some claim => simp [hcollision, hduplicate] at h
      | none =>
          exact ⟨hfresh, duplicateComparisonClaim?_eq_none_iff program |>.mp hduplicate⟩


/-! ### Presentation-to-core policy conversion -/

mutual
  /-- A literal term as a core pattern (numerals, strings, constructors). -/
  def termToPat : Term → Lara.Support.Pat
    | .num s => .num s
    | .str s => .str s
    | .con name terms => .con ⟨name⟩ (termsToPats terms)
  def termsToPats : Terms → Lara.Support.Pats
    | .nil => .nil
    | .cons term rest => .cons (termToPat term) (termsToPats rest)
end

mutual
  /-- A presentation pattern as a core pattern. -/
  def toCorePat : Presentation.Pat → Lara.Support.Pat
    | .var param => .var (toSupportParam param)
    | .lit term => termToPat term
    | .con name pats => .con ⟨name⟩ (toCorePats pats)
  def toCorePats : Presentation.Pats → Lara.Support.Pats
    | .nil => .nil
    | .cons pat rest => .cons (toCorePat pat) (toCorePats rest)
end

/-- A presentation atom pattern as a core atom pattern. -/
def toCoreAtomPat (pattern : Presentation.AtomPat) : Lara.Support.APat :=
  ⟨⟨pattern.pred⟩, toCorePats pattern.args⟩

/-- A presentation rule as a core rule. -/
def toCoreRule (rule : Presentation.Rule) : Lara.Support.Rule where
  mode := match rule.mode with | .strict => .strict | .defeasible => .defeasible
  params := rule.params.map toSupportParam
  premises := rule.premises.map toCoreAtomPat
  concl := toCoreAtomPat rule.conclusion
  questions := rule.questions.map fun question =>
    ⟨toSupportQuestionId question.id, toCoreAtomPat question.answer,
      match question.necessity with | .mandatory => true | .optional => false⟩
  allowTrusted := rule.allowTrusted
  certifiers := rule.certifiers.map fun certifier =>
    (toSupportBackendId certifier.backend certifier.version,
      toSupportTheoryDigest certifier.theory)

/-- The core policy of a presentation policy: converted rules and defeat
material; signature, admission, theories, groups, measurands, and comparison
schemes are surface material and do not enter the core policy. -/
def toCorePolicy (policy : Presentation.Policy) : Lara.Policy.Policy where
  rules := policy.rules.map fun rule => ⟨toSupportRuleId rule.id, toCoreRule rule⟩
  defeat :=
    { contraries := policy.contraries.map fun contrary =>
        (toCoreAtomPat contrary.left, toCoreAtomPat contrary.right)
      exceptions := policy.exceptions.map fun exception =>
        (toSupportRuleId exception.rule, toCoreAtomPat exception.atom) }

/-! ### Carrier computations -/

/-- The declared surface attacks of a program, in declaration order. -/
def surfaceAttacksOf (program : Presentation.Program) : List Presentation.SurfaceAttack :=
  program.decls.filterMap fun
    | .attack attack => some attack
    | _ => none

/-- The declared surface attacks whose endpoints both survive the admission
prune. -/
def keptSurfaceAttacks (program : Presentation.Program) (kept : List Presentation.ArgId) :
    List Presentation.SurfaceAttack :=
  (surfaceAttacksOf program).filter fun attack =>
    memberOf (attackEndpoints attack).1 kept && memberOf (attackEndpoints attack).2 kept

/-- Select declaration-aligned semantic attacks using the same authored
endpoint predicate as `keptSurfaceAttacks`. The two lists are consumed in
lockstep; successful declared resolution proves their lengths agree. -/
def selectResolvedAttacks (kept : List Presentation.ArgId) :
    List Presentation.SurfaceAttack → List Lara.Attack.Attack →
      List Lara.Attack.Attack
  | attack :: attacks, resolved :: resolvedRest =>
      let tail := selectResolvedAttacks kept attacks resolvedRest
      if memberOf (attackEndpoints attack).1 kept &&
          memberOf (attackEndpoints attack).2 kept then
        resolved :: tail
      else
        tail
  | _, _ => []

mutual
  /-- The leaf ids a presentation support term mentions. -/
  def leavesOfTerm : Presentation.SupportTerm → List Presentation.LeafId
    | .leaf leaf => [leaf]
    | .rule _ _ premises discharges _ _ =>
        leavesOfTerms premises ++ leavesOfDischarges discharges
  def leavesOfTerms : Presentation.SupportTerms → List Presentation.LeafId
    | .nil => []
    | .cons term rest => leavesOfTerm term ++ leavesOfTerms rest
  def leavesOfDischarges : Presentation.Discharges → List Presentation.LeafId
    | .nil => []
    | .cons _ term rest => leavesOfTerm term ++ leavesOfDischarges rest
end

/-- Presentation admission rows in the verified admission model. -/
def admissionRows (policy : Presentation.Policy) :
    List Lara.Admission.AdmissionRow :=
  policy.admission.map fun row => ⟨row.1, row.2⟩

/-- Declared leaf metadata in source declaration order. -/
def admissionLeafMetas (program : Presentation.Program) :
    List Lara.Admission.LeafMeta :=
  (leafRecords program).map fun leaf =>
    ⟨toSupportLeafId leaf.id, leaf.kind, leaf.provenance⟩

/-- Declared leaf propositions in source declaration order. -/
def admissionLeafTable (program : Presentation.Program) :
    List (Lara.Support.LeafId × Atom) :=
  (declaredLeaves program).map fun row => (toSupportLeafId row.1, row.2)

/-- Reconstructed core arguments with authored ids retained until admission. -/
def admissionArgs (pairs : List ReconstructedArgument) :
    List (String × Lara.Support.SupportTerm) :=
  pairs.map fun pair => (pair.argument.id.val, pair.core)

/-- Duplicate-report groups converted once to the core admission vocabulary. -/
def admissionGroups (program : Presentation.Program) : List Lara.Groups.DupGroup :=
  program.decls.filterMap fun
    | .group group =>
        some
          { id := group.id.val
            members := group.members.map toSupportLeafId }
    | _ => none

/-- The single policy/group removal seed, expressed in source leaf ids. -/
def quarantinedSurfaceLeafIds (canon : String → String)
    (policy : Presentation.Policy) (program : Presentation.Program) :
    List Presentation.LeafId :=
  quarantinedLeafIds policy program ++
    (Lara.Groups.quarantined canon
      ((declaredLeaves program).map fun entry => (toSupportLeafId entry.1, entry.2))
      (admissionGroups program)).map fun leaf => ⟨leaf.name⟩

/-- The reconstructed arguments surviving the production admission prune:
no policy- or duplicate-group-quarantined leaf occurs anywhere in the
reconstructed term. References embed their targets, so this also removes every
argument depending on a removed argument. -/
def keptReconstructed (canon : String → String) (policy : Presentation.Policy)
    (program : Presentation.Program) (pairs : List ReconstructedArgument) :
    List ReconstructedArgument :=
  let removed :=
    Lara.Admission.policyQuarantineSeed (admissionRows policy)
        (admissionLeafMetas program) ++
      Lara.Groups.quarantined canon (admissionLeafTable program)
        (admissionGroups program)
  pairs.filter fun pair => !Lara.Groups.usesLeaf removed pair.core

/-- The root holes of a core support term. -/
def rootHoles : Lara.Support.SupportTerm → List Lara.Support.QuestionId
  | .leaf _ => []
  | .inst _ _ _ _ holes _ => holes

/-- The root holes of a presentation support term. -/
def rootAuthoredHoles : Presentation.SupportTerm → List Presentation.ObligationId
  | .leaf _ => []
  | .rule _ _ _ _ holes _ => holes

/-- Does this argument conclusion support the given claim? -/
def argSupportsClaim (claim : Presentation.PropId) : Presentation.ArgConcl → Bool
  | .supportsClaim id => decide (id = claim)
  | .supportsDerived id => decide (id = claim)
  | .challenges _ => false

/-- The claim map: for each declared claim (including comparison-generated
sub-claims), the positions of its complete supporting arguments and of its
hole-bearing supporting alternatives, in the unit's argument order. -/
def claimsOf (pairs : List ReconstructedArgument) (program : Presentation.Program) :
    List (Presentation.PropId × Lara.Grounded.Claim) :=
  (program.decls.filterMap fun
    | .claim claim => some claim
    | _ => none).map fun claim =>
      let supporting := pairs.zipIdx.filter fun (pair, _) =>
        argSupportsClaim claim.id pair.argument.concl
      (claim.id,
        { support := (supporting.filter fun (pair, _) => rootHoles pair.core = []).map (·.2)
          holes := (supporting.filter fun (pair, _) => rootHoles pair.core != []).map (·.2) })

/-- The authored obligations of the source program's arguments. -/
def authoredObligationsOf (program : Presentation.Program) :
    List (Presentation.ArgId × List Presentation.ObligationId) :=
  program.decls.filterMap fun
    | .arg argument =>
        some (argument.id, match argument.instantiation with
          | .explicitTheta term => rootAuthoredHoles term
          | .inferTheta _ _ _ holes _ => holes)
    | _ => none

/-- The open critical questions of each reconstructed argument. -/
def openQuestionsOf (pairs : List ReconstructedArgument) :
    List (Presentation.ArgId × List Lara.Support.QuestionId) :=
  pairs.map fun pair => (pair.argument.id, rootHoles pair.core)

/-- The declared leaf rows surviving the same policy/group admission seed used
for argument pruning. -/
def checkedSurfaceLeaves (canon : String → String) (policy : Presentation.Policy)
    (program : Presentation.Program) : List Presentation.Leaf :=
  (leafRecords program).filter fun leaf =>
    admissionDecision policy.admission leaf.kind leaf.provenance = .admit &&
      !memberOf leaf.id (quarantinedSurfaceLeafIds canon policy program)

/-- The environment the core checker sees after the one policy/group prune. -/
def surfaceGamma (canon : String → String) (policy : Presentation.Policy)
    (program : Presentation.Program) : Lara.Support.LeafId → Option Atom :=
  Lara.Admission.buildGamma
    (Lara.Admission.checkedLeafTable canon (admissionRows policy)
      (admissionLeafMetas program) (admissionLeafTable program)
      (admissionGroups program))

/-- Requested query atoms in authored status-declaration order.  Invalid ids
are rejected by `resolveStatuses`; `filterMap` is only the data projection used
after that declarative guard succeeds. -/
def requestedStatusAtoms (program : Presentation.Program) : List Atom :=
  (statusIds program).filterMap (claimFormal? program)

private def firstUnknownStatus? (program : Presentation.Program) :
    Option Presentation.PropId :=
  (statusIds program).find? fun id => (claimFormal? program id).isNone

/-- Resolve requested statuses after attack resolution, as production does. -/
def resolveStatuses (program : Presentation.Program) :
    Except Error (List Atom) :=
  if statusesWellFormedB program then .ok (requestedStatusAtoms program)
  else .error (.unknownStatusClaim ((firstUnknownStatus? program).getD ⟨""⟩))

theorem resolveStatuses_sound {program : Presentation.Program} {atoms : List Atom}
    (h : resolveStatuses program = .ok atoms) :
    StatusesWellFormed program ∧ atoms = requestedStatusAtoms program := by
  unfold resolveStatuses at h
  by_cases valid : statusesWellFormedB program = true
  · simp only [valid, ↓reduceIte] at h
    exact ⟨(statusesWellFormedB_iff program).mp valid, (Except.ok.inj h).symm⟩
  · simp only [valid, ↓reduceIte] at h
    cases h

theorem resolveStatuses_complete {program : Presentation.Program}
    (h : StatusesWellFormed program) :
    resolveStatuses program = .ok (requestedStatusAtoms program) := by
  simp [resolveStatuses, (statusesWellFormedB_iff program).mpr h]

private def firstPerGroupError? (program : Presentation.Program) :
    List Presentation.DupGroup → Option Error
  | [] => none
  | group :: rest =>
      match firstRepeated group.members with
      | some leaf => some (.groupRepeatedMember group.id leaf)
      | none =>
          if group.members.length < 2 then some (.groupTooFewMembers group.id)
          else
            match group.members.find? fun leaf => !(leafIds program).contains leaf with
            | some leaf => some (.groupMemberUndeclared group.id leaf)
            | none => firstPerGroupError? program rest

/-- Validate duplicate-report groups in production order: duplicate group id
globally, then repeated member, cardinality, and undeclared member per group. -/
def validateGroups (program : Presentation.Program) : Except Error _root_.Unit :=
  if groupsWellFormedB program then .ok ()
  else
    match firstRepeated ((groupDecls program).map (·.id)) with
    | some group => .error (.duplicateGroupId group)
    | none => .error ((firstPerGroupError? program (groupDecls program)).getD
        (.groupTooFewMembers ⟨""⟩))

theorem validateGroups_sound {program : Presentation.Program}
    (h : validateGroups program = .ok ()) : GroupsWellFormed program := by
  unfold validateGroups at h
  by_cases valid : groupsWellFormedB program = true
  · exact (groupsWellFormedB_iff program).mp valid
  · simp only [valid, ↓reduceIte] at h
    cases hrepeat : firstRepeated ((groupDecls program).map (·.id)) <;>
      simp [hrepeat] at h

theorem validateGroups_complete {program : Presentation.Program}
    (h : GroupsWellFormed program) : validateGroups program = .ok () := by
  simp [validateGroups, (groupsWellFormedB_iff program).mpr h]

/-- The finite ground atoms of the checked environment: retained leaf
conclusions, resolved requested status formals, and the declared theory table. -/
def surfaceGround (canon : String → String) (policy : Presentation.Policy)
    (program : Presentation.Program) : List Atom :=
  (Lara.Admission.checkedLeafTable canon (admissionRows policy)
      (admissionLeafMetas program) (admissionLeafTable program)
      (admissionGroups program)).map (·.2) ++
    requestedStatusAtoms program ++
    policy.theories.flatMap (·.2)

/-! ### Production boundary staging -/

/-- Endpoint declaration is independent of path resolution: production checks
it after semantic identifiers and before duplicate-report groups. -/
def AttackEndpointsDeclared (program : Presentation.Program) : Prop :=
  ∀ declaration ∈ program.decls,
    match declaration with
    | .attack attack =>
        (attackEndpoints attack).1 ∈ argIds program ∧
          (attackEndpoints attack).2 ∈ argIds program
    | _ => True

def attackEndpointDeclaredB (ids : List Presentation.ArgId) :
    Presentation.Decl → Bool
  | .attack attack =>
      ids.contains (attackEndpoints attack).1 &&
        ids.contains (attackEndpoints attack).2
  | _ => true

def attackEndpointsDeclaredB (program : Presentation.Program) : Bool :=
  program.decls.all (attackEndpointDeclaredB (argIds program))

theorem attackEndpointsDeclaredB_iff (program : Presentation.Program) :
    attackEndpointsDeclaredB program = true ↔ AttackEndpointsDeclared program := by
  unfold attackEndpointsDeclaredB AttackEndpointsDeclared
  rw [List.all_eq_true]
  constructor
  · intro h declaration member
    have checked := h declaration member
    cases declaration <;> simp_all [attackEndpointDeclaredB]
  · intro h declaration member
    have checked := h declaration member
    cases declaration <;> simp_all [attackEndpointDeclaredB]

def firstBadEndpointAttackIn? (ids : List Presentation.ArgId) :
    List Presentation.Decl → Option Presentation.SurfaceAttack
  | [] => none
  | .attack attack :: rest =>
      if attackEndpointDeclaredB ids (.attack attack) then
        firstBadEndpointAttackIn? ids rest
      else some attack
  | _ :: rest => firstBadEndpointAttackIn? ids rest

def firstBadEndpointAttack? (program : Presentation.Program) :
    Option Presentation.SurfaceAttack :=
  firstBadEndpointAttackIn? (argIds program) program.decls

def validateAttackEndpoints (program : Presentation.Program) :
    Except Error _root_.Unit :=
  if attackEndpointsDeclaredB program then .ok ()
  else
    let attack := (firstBadEndpointAttack? program).getD
      (.rebut ⟨""⟩ ⟨""⟩)
    .error (.invalidSurfaceAttack
      (attackEndpoints attack).1 (attackEndpoints attack).2)

theorem validateAttackEndpoints_sound {program : Presentation.Program}
    (h : validateAttackEndpoints program = .ok ()) :
    AttackEndpointsDeclared program := by
  unfold validateAttackEndpoints at h
  by_cases valid : attackEndpointsDeclaredB program = true
  · exact (attackEndpointsDeclaredB_iff program).mp valid
  · simp [valid] at h

theorem validateAttackEndpoints_complete {program : Presentation.Program}
    (h : AttackEndpointsDeclared program) :
    validateAttackEndpoints program = .ok () := by
  simp [validateAttackEndpoints, (attackEndpointsDeclaredB_iff program).mpr h]

theorem AttackEndpointsDeclared.of_surfaceAttacksWellFormed
    {program : Presentation.Program} {policy : Presentation.Policy}
    (h : SurfaceAttacksWellFormed program policy) :
    AttackEndpointsDeclared program := by
  intro declaration member
  have checked := h declaration member
  cases declaration <;> simp_all [SurfaceAttackWellFormed]

/-- The validations that production performs before semantic expansion. -/
def elaborationPrologue (input : Input) : Except Error _root_.Unit :=
  if input.program.policy = input.policy.id then
    if canonicalPremiseLabelsB input.policy then
      match findDuplicate (input.policy.admission.map Prod.fst) with
      | some key => .error (.duplicateAdmissionKey key.1 key.2)
      | none =>
          match findDuplicate (leafIds input.program) with
          | some id => .error (.duplicateLeafId id)
          | none => .ok ()
    else
      .error (.noncanonicalPremiseLabels
        (((input.policy.rules.find? fun rule =>
          !canonicalPremiseLabelsForRuleB rule).map (·.id)).getD ⟨""⟩))
  else .error (.policyMismatch input.program.policy input.policy.id)

/-- Post-expansion identifiers and raw attack endpoints, before groups. -/
def semanticIdentifierChecks (policy : Presentation.Policy)
    (source : Presentation.Program) : Except Error _root_.Unit :=
  match findDuplicate (argIds source) with
  | some id => .error (.duplicateArgId id)
  | none =>
      match findDuplicate (claimIds source) with
      | some id => .error (.duplicateClaimId id)
      | none =>
          if ruleNamespacesWellFormedB policy then
            validateAttackEndpoints source
          else .error (.malformedRuleNamespace ⟨""⟩)

/-! ### The guard stage and its inversion -/

/-- The first rule id whose namespace is ill-formed (duplicate policy rule
ids reported first). -/
private def firstBadRuleNamespaceId? (policy : Presentation.Policy) : Option Presentation.RuleId :=
  match findDuplicate (ruleIds policy) with
  | some id => some id
  | none => (policy.rules.find? fun rule => !ruleNamespaceWellFormedB rule).map (·.id)

/-- The first value name involved in a value-binding failure. -/
private def firstBadValueName (input : Input) : Presentation.ValueName :=
  match findDuplicate (valueNames input.program) with
  | some name => name
  | none => (valueNames input.program).head?.getD ⟨""⟩

/-- The claim id naming the first comparison failure. -/
private def firstComparisonErrorId (program : Presentation.Program) : Presentation.PropId :=
  ((comparisonDecls program).head?.map (·.claim.id)).getD ⟨""⟩

/-- The first argument of the source program whose reconstruction fails. -/
private def firstArgBuildFailure? (program : Presentation.Program)
    (policy : Presentation.Policy) :
    List Presentation.Decl → List PriorArgument → Option Presentation.ArgId
  | [], _ => none
  | .arg argument :: rest, priors =>
      match buildArgument program policy priors argument with
      | none => some argument.id
      | some built => firstArgBuildFailure? program policy rest (priors ++ [built])
  | .comparison comparison :: rest, priors =>
      match generatedComparisonArguments program policy comparison with
      | none => some comparison.recheckArg
      | some generated =>
          firstArgBuildFailure? program policy rest (priors ++ [generated.1, generated.2])
  | _ :: rest, priors => firstArgBuildFailure? program policy rest priors

/-- The first argument of the source program whose certificates are
ill-formed. -/
private def firstCertFailure? (program : Presentation.Program)
    (policy : Presentation.Policy) :
    List Presentation.Decl → List PriorArgument → Option Presentation.ArgId
  | [], _ => none
  | .arg argument :: rest, priors =>
      match buildArgument program policy priors argument with
      | none => firstCertFailure? program policy rest priors
      | some built =>
          if termCertificatesValidB program policy priors built.term then
            firstCertFailure? program policy rest (priors ++ [built])
          else some argument.id
  | .comparison comparison :: rest, priors =>
      match generatedComparisonArguments program policy comparison with
      | none => firstCertFailure? program policy rest priors
      | some generated =>
          firstCertFailure? program policy rest (priors ++ [generated.1, generated.2])
  | _ :: rest, priors => firstCertFailure? program policy rest priors

/-- The endpoints of the first ill-formed declared surface attack. -/
private def firstBadAttackEndpoints? (input : Input) :
    Option (Presentation.ArgId × Presentation.ArgId) :=
  input.program.decls.findSome? fun
    | .attack attack =>
        if surfaceAttackWellFormedB input.program input.policy attack then none
        else some (attackEndpoints attack)
    | _ => none

/-- The first rule id whose premise labels are noncanonical. -/
private def firstNoncanonicalRuleId? (policy : Presentation.Policy) : Option Presentation.RuleId :=
  (policy.rules.find? fun rule => !canonicalPremiseLabelsForRuleB rule).map Presentation.Rule.id

/-- The complete structural supported-fragment/admission guard. Executable
assembly runs this after the precise production-staged passes, so its broad
static predicates cannot preempt endpoint/group/fold/path/status diagnostics. -/
def assembleGuards (input : Input) : Except Error _root_.Unit :=
  if input.program.policy = input.policy.id then
    match findDuplicate (input.policy.admission.map Prod.fst) with
    | some key => .error (.duplicateAdmissionKey key.1 key.2)
    | none =>
    match findDuplicate (leafIds input.program) with
    | some id => .error (.duplicateLeafId id)
    | none =>
    match findDuplicate (argIds input.program) with
    | some id => .error (.duplicateArgId id)
    | none =>
    match findDuplicate (claimIds input.program) with
    | some id => .error (.duplicateClaimId id)
    | none =>
    match findDuplicate (valueNames input.program) with
    | some id => .error (.duplicateValueName id)
    | none =>
    if ruleNamespacesWellFormedB input.policy then
    if valueBindingsWellFormedB input then
    if GeneratedIdsFresh input.program then
    if comparisonsWellFormedB input.program input.policy then
    if inferredArgsWellFormedB input.program input.policy then
    if namedCertificatesWellFormedB input.program input.policy then
    if surfaceAttacksWellFormedB input.program input.policy then
    if canonicalPremiseLabelsB input.policy then
    match firstRejectedLeaf input.policy input.program with
    | some leaf => .error (.admissionRejected leaf.id)
    | none => .ok ()
    else .error (.noncanonicalPremiseLabels ((firstNoncanonicalRuleId? input.policy).getD ⟨""⟩))
    else .error (((firstBadAttackEndpoints? input).map fun pair =>
      Error.invalidSurfaceAttack pair.1 pair.2).getD
        (Error.invalidSurfaceAttack ⟨""⟩ ⟨""⟩))
    else .error (.invalidNamedCertificate
      ((firstCertFailure? input.program input.policy input.program.decls []).getD ⟨""⟩))
    else .error (.invalidInferredArgument
      ((firstArgBuildFailure? input.program input.policy input.program.decls []).getD ⟨""⟩))
    else .error (.invalidComparison (firstComparisonErrorId input.program))
    else .error (.invalidComparison (firstComparisonErrorId input.program))
    else .error (.invalidValueBinding (firstBadValueName input))
    else .error (.malformedRuleNamespace ((firstBadRuleNamespaceId? input.policy).getD ⟨""⟩))
  else .error (.policyMismatch input.program.policy input.policy.id)

/-- Successful guards establish the supported fragment, admission, and
generated-id freshness. -/
theorem assembleGuards_ok (input : Input) (h : assembleGuards input = .ok ()) :
    Supported input ∧ AdmissionOK input ∧ GeneratedIdsFresh input.program = true := by
  unfold assembleGuards at h
  by_cases hpolicy : input.program.policy = input.policy.id
  · rw [if_pos hpolicy] at h
    cases hadm : findDuplicate (input.policy.admission.map Prod.fst) with
    | some key => simp only [hadm] at h; cases h
    | none =>
      simp only [hadm] at h
      cases hleaf : findDuplicate (leafIds input.program) with
      | some id => simp only [hleaf] at h; cases h
      | none =>
        simp only [hleaf] at h
        cases harg : findDuplicate (argIds input.program) with
        | some id => simp only [harg] at h; cases h
        | none =>
          simp only [harg] at h
          cases hclaim : findDuplicate (claimIds input.program) with
          | some id => simp only [hclaim] at h; cases h
          | none =>
            simp only [hclaim] at h
            cases hvalue : findDuplicate (valueNames input.program) with
            | some id => simp only [hvalue] at h; cases h
            | none =>
              simp only [hvalue] at h
              by_cases hrules : ruleNamespacesWellFormedB input.policy = true
              · rw [if_pos hrules] at h
                by_cases hvalues : valueBindingsWellFormedB input = true
                · rw [if_pos hvalues] at h
                  by_cases hfresh : GeneratedIdsFresh input.program = true
                  · rw [if_pos hfresh] at h
                    by_cases hcomps : comparisonsWellFormedB input.program input.policy = true
                    · rw [if_pos hcomps] at h
                      by_cases hinferred :
                          inferredArgsWellFormedB input.program input.policy = true
                      · rw [if_pos hinferred] at h
                        by_cases hcerts :
                            namedCertificatesWellFormedB input.program input.policy = true
                        · rw [if_pos hcerts] at h
                          by_cases hattacks :
                              surfaceAttacksWellFormedB input.program input.policy = true
                          · rw [if_pos hattacks] at h
                            by_cases hlabels : canonicalPremiseLabelsB input.policy = true
                            · rw [if_pos hlabels] at h
                              cases hreject : firstRejectedLeaf input.policy input.program with
                              | some leaf => simp only [hreject] at h; cases h
                              | none =>
                                refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
                                  ⟨findDuplicate_none_nodup hadm, ?_⟩, hfresh⟩
                                · exact hpolicy
                                · exact ⟨⟨⟨findDuplicate_none_nodup hleaf,
                                    findDuplicate_none_nodup harg⟩,
                                    findDuplicate_none_nodup hclaim⟩,
                                    findDuplicate_none_nodup hvalue⟩
                                · exact (ruleNamespacesWellFormedB_iff input.policy).mp hrules
                                · exact (valueBindingsWellFormedB_iff input).mp hvalues
                                · exact (comparisonsWellFormedB_iff input.program
                                    input.policy).mp hcomps
                                · exact (inferredArgsWellFormedB_iff input.program
                                    input.policy).mp hinferred
                                · exact (namedCertificatesWellFormedB_iff input.program
                                    input.policy).mp hcerts
                                · exact (surfaceAttacksWellFormedB_iff input.program
                                    input.policy).mp hattacks
                                · exact (canonicalPremiseLabelsB_iff input.policy).mp hlabels
                                · intro leaf hleafmem hcontra
                                  unfold firstRejectedLeaf at hreject
                                  have hnone := (List.find?_eq_none).mp hreject leaf hleafmem
                                  rw [hcontra] at hnone
                                  simp at hnone
                            · rw [if_neg hlabels] at h; cases h
                          · rw [if_neg hattacks] at h; cases h
                        · rw [if_neg hcerts] at h; cases h
                      · rw [if_neg hinferred] at h; cases h
                    · rw [if_neg hcomps] at h; cases h
                  · rw [if_neg hfresh] at h; cases h
                · rw [if_neg hvalues] at h; cases h
              · rw [if_neg hrules] at h; cases h
  · rw [if_neg hpolicy] at h; cases h
theorem firstRejectedLeaf_none_of_admission {input : Input}
    (h : AdmissionOK input) :
    firstRejectedLeaf input.policy input.program = none := by
  unfold firstRejectedLeaf
  apply List.find?_eq_none.mpr
  intro leaf hmem
  simpa using h.2 leaf hmem

theorem assembleGuards_complete {input : Input}
    (hsupported : Supported input) (hadmission : AdmissionOK input)
    (hfresh : GeneratedIdsFresh input.program = true) :
    assembleGuards input = .ok () := by
  rcases hsupported.declaration_ids_nodup with
    ⟨⟨⟨hleaf, harg⟩, hclaim⟩, hvalue⟩
  have hadm := findDuplicate_none_of_nodup hadmission.1
  have hleaf' := findDuplicate_none_of_nodup hleaf
  have harg' := findDuplicate_none_of_nodup harg
  have hclaim' := findDuplicate_none_of_nodup hclaim
  have hvalue' := findDuplicate_none_of_nodup hvalue
  have hrules := (ruleNamespacesWellFormedB_iff input.policy).2
    hsupported.rule_namespaces_wf
  have hvalues := (valueBindingsWellFormedB_iff input).2
    hsupported.value_bindings_wf
  have hcomps := (comparisonsWellFormedB_iff input.program input.policy).2
    hsupported.comparisons_wf
  have hinferred := (inferredArgsWellFormedB_iff input.program input.policy).2
    hsupported.inferred_args_wf
  have hcerts := (namedCertificatesWellFormedB_iff input.program input.policy).2
    hsupported.named_certs_wf
  have hattacks := (surfaceAttacksWellFormedB_iff input.program input.policy).2
    hsupported.attack_names_wf
  have hlabels := (canonicalPremiseLabelsB_iff input.policy).2
    hsupported.canonical_labels
  have hreject := firstRejectedLeaf_none_of_admission hadmission
  simp [assembleGuards, hsupported.policy_matches, hadm, hleaf', harg', hclaim',
    hvalue', hrules, hvalues, hfresh, hcomps, hinferred, hcerts, hattacks,
    hlabels, hreject]

/-! ### The assembly -/

/-- Assemble the elaborated carrier in production diagnostic order, then run
the complete structural guard before constructing the retained core unit. -/
def assemble (env : Env canon) (input : Input) : Except Error (Elaborated canon) :=
  match elaborationPrologue input with
  | .error error => .error error
  | .ok _ =>
  match expandValues input.policy input.program with
  | .error error => .error error
  | .ok valueExpanded =>
  match expandComparisons input.policy valueExpanded with
  | .error error => .error error
  | .ok (semantic, _) =>
  match semanticIdentifierChecks input.policy input.program with
  | .error error => .error error
  | .ok _ =>
  match validateGroups semantic with
  | .error error => .error error
  | .ok _ =>
  match reconstructArgs env semantic input.policy semantic.decls [] with
  | .error (.build id) => .error (.invalidInferredArgument id)
  | .error (.lower id) => .error (.invalidNamedCertificate id)
  | .error (.conclusionMismatch id claim) => .error (.conclusionMismatch id claim)
  | .error (.challengeTargetUndeclared id) =>
      .error (.challengeTargetUndeclared id)
  | .ok pairs =>
  if _hpairIds :
      (pairs.map fun pair => pair.argument.id.val).Nodup then
  match resolveSurfaceAttacks input.policy
      (pairs.map fun pair => (pair.argument.id, pair.core))
      (surfaceAttacksOf semantic) with
  | .error (source, target) => .error (.invalidSurfaceAttack source target)
  | .ok declaredResolved =>
  match resolveStatuses semantic with
  | .error error => .error error
  | .ok _ =>
  match assembleGuards input with
  | .error error => .error error
  | .ok _ =>
      let keptIds :=
        (keptReconstructed canon input.policy semantic pairs).map (·.argument.id)
      let resolved :=
        selectResolvedAttacks keptIds (surfaceAttacksOf semantic) declaredResolved
      .ok
        { gamma := surfaceGamma canon input.policy semantic
          ground := surfaceGround canon input.policy semantic
          unit :=
            { sigma := input.policy.sigma
              policy := toCorePolicy input.policy
              args := (keptReconstructed canon input.policy semantic pairs).map (·.core)
              atts := resolved }
          claims := claimsOf (keptReconstructed canon input.policy semantic pairs) semantic
          argIds := keptIds
          authoredObligations := authoredObligationsOf input.program
          openQuestions :=
            openQuestionsOf (keptReconstructed canon input.policy semantic pairs)
          resolvedAttacks := resolved
          semanticProgram := semantic }
  else .error (.duplicateArgId ⟨""⟩)

/-! ### The top-level judgment -/

/-- Declarative core-acceptance obligations carried by a surface derivation.
No field invokes `checkUnit` or stores executable success: these are exactly
the independent signature, policy, support/certificate, attack, endpoint, and
conflict-completeness premises consumed by `Check.Unit.checkUnit_complete`. -/
structure CoreObligations (env : Env canon) (output : Elaborated canon) : Prop where
  sigmaWellFormed : Sigma.sigmaWellFormed output.unit.sigma = true
  policyWellSorted : Lara.policyWellSorted output.unit.sigma output.unit.policy = true
  groundWellSorted : Lara.groundWellSorted output.unit.sigma output.ground = true
  argsWellSorted :
    Lara.argsWellSorted output.unit.sigma output.unit.policy output.unit.args = true
  scopesWellFormed : Policy.ScopesWellFormed output.unit.policy
  ruleIdsNodup : (output.unit.policy.rules.map (·.id)).Nodup
  policyWellFormed : Policy.WellFormed canon output.unit.policy
  argsNodup : output.unit.args.Nodup
  supports : ∀ term ∈ output.unit.args, ∃ conclusion,
    Support.HasSupport canon output.unit.policy.ruleLookup output.gamma
      (Support.certOkOf env.registry) term conclusion []
  attacksTyped : ∀ attack ∈ output.unit.atts,
    Attack.HasAttack canon output.unit.policy.ruleLookup output.gamma
      (Support.certOkOf env.registry) output.unit.policy.defeat attack
  sourcesDeclared : ∀ attack ∈ output.unit.atts,
    attack.source ∈ output.unit.args
  targetsDeclared : ∀ attack ∈ output.unit.atts,
    attack.target ∈ output.unit.args
  attackComplete : Compile.AttackComplete canon output.unit.policy.ruleLookup
    output.gamma (Support.certOkOf env.registry) output.unit.policy.defeat
    output.unit.args output.unit.atts

theorem CoreObligations.signatureStage_none
    {env : Env canon} {output : Elaborated canon}
    (h : CoreObligations env output) :
    Check.Unit.signatureStage output.ground output.unit = none := by
  simp [Check.Unit.signatureStage, h.sigmaWellFormed, h.policyWellSorted,
    h.groundWellSorted, h.argsWellSorted]

/-- Declarative surface/core obligations derive concrete checker success by
the core checker's completeness theorem. -/
theorem CoreObligations.checkUnit_complete
    {env : Env canon} {output : Elaborated canon}
    (h : CoreObligations env output) :
    ∃ checked,
      Check.Unit.checkUnit output.gamma env.registry output.ground output.unit =
        .ok checked :=
  Check.Unit.checkUnit_complete h.signatureStage_none h.scopesWellFormed
    h.ruleIdsNodup h.policyWellFormed h.argsNodup h.supports h.attacksTyped
    h.sourcesDeclared h.targetsDeclared h.attackComplete

/-- Executable core success exposes the independent obligations.  This is the
soundness direction used by `Surface.check`; preservation uses the converse
`CoreObligations.checkUnit_complete`. -/
theorem CoreObligations.of_checkUnit_ok
    {env : Env canon} {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hchecked : Check.Unit.checkUnit output.gamma env.registry output.ground
      output.unit = .ok checked) : CoreObligations env output := by
  have hsound := Check.Unit.checkUnit_sound hchecked
  have sigmaEq := hsound.sigma_eq
  have sigmaWf := hsound.sigma_wf
  have policySorted := hsound.policy_sorted
  have groundSorted := hsound.ground_sorted
  have argsSorted := hsound.args_sorted
  have policyEq := hsound.policy_eq
  have ruleIds := hsound.ruleIds_nodup
  have policyWf := hsound.policy_wf
  have argumentsEq := hsound.args_eq
  have attacksEq := hsound.atts_eq
  have attackComplete := hsound.attack_complete
  have nodeTerms := hsound.nodes_terms
  refine
    { sigmaWellFormed := ?_
      policyWellSorted := ?_
      groundWellSorted := ?_
      argsWellSorted := ?_
      scopesWellFormed := ?_
      ruleIdsNodup := ?_
      policyWellFormed := ?_
      argsNodup := ?_
      supports := ?_
      attacksTyped := ?_
      sourcesDeclared := ?_
      targetsDeclared := ?_
      attackComplete := ?_ }
  · simpa only [sigmaEq] using sigmaWf
  · simpa only [sigmaEq, policyEq] using policySorted
  · simpa only [sigmaEq] using groundSorted
  · simpa only [sigmaEq, policyEq, argumentsEq] using argsSorted
  · simpa only [policyEq] using checked.scopes_wf
  · simpa only [policyEq] using ruleIds
  · simpa only [policyEq] using policyWf
  · simpa only [argumentsEq] using checked.program.nodup
  · intro term member
    obtain ⟨conclusion, valid⟩ := checked.program.complete term (by
      simpa only [argumentsEq] using member)
    exact ⟨conclusion, by simpa only [policyEq] using valid⟩
  · intro attack member
    have valid := checked.program.typed attack (by
      simpa only [attacksEq] using member)
    simpa only [policyEq] using valid
  · intro attack member
    have declared := checked.program.source_declared attack (by
      simpa only [attacksEq] using member)
    simpa only [argumentsEq] using declared
  · intro attack member
    have declared := checked.program.target_declared attack (by
      simpa only [attacksEq] using member)
    simpa only [argumentsEq] using declared
  · simpa only [policyEq, argumentsEq, attacksEq] using attackComplete

/-- The independent surface judgment. Its derivations reconstruct the
presentation program syntax-directly; the output equalities identify each
assembled component without assuming that `assemble` itself succeeded. Core
acceptance is a separate final premise. -/
structure Checks (env : Env canon) (input : Input) (output : Elaborated canon) : Prop where
  /-- The source lies in the supported fragment. -/
  supported : Supported input
  /-- Admission keys are distinct and no declared leaf is rejected. -/
  admission : AdmissionOK input
  /-- The comparison blocks' generated ids collide with nothing. -/
  freshness : GeneratedIdsFresh input.program = true
  /-- Every policy rule's namespace and premise labels are well-formed. -/
  rules : ∀ rule ∈ input.policy.rules, ChecksRule rule
  /-- Every requested status and duplicate-report group is well-formed after
  value/comparison expansion, matching the production source boundary. -/
  statuses : StatusesWellFormed output.semanticProgram
  groups : GroupsWellFormed output.semanticProgram
  /-- The semantic program is exactly the value and comparison expansion of
  the source program. The intermediate freshness premises are precisely the
  executable comparison-expansion guards. -/
  expansions : ∃ mid target generated,
    ExpandsValues input.program mid ∧
      GeneratedIdsFresh mid = true ∧
      (comparisonKeys mid).Nodup ∧
      ExpandsComparisons input.policy mid target generated ∧
      target = output.semanticProgram
  /-- The semantic program's declarations derive, threading priors; the kept
  reconstructed arguments determine every pair-dependent output component. -/
  program : ∃ pairs declaredResolved,
    ChecksProgram env output.semanticProgram input.policy
      output.semanticProgram.decls [] pairs ∧
    (pairs.map fun pair => pair.argument.id.val).Nodup ∧
    ChecksAttacks input.policy
      (pairs.map fun pair => (pair.argument.id, pair.core))
      (surfaceAttacksOf output.semanticProgram) declaredResolved ∧
    selectResolvedAttacks
        ((keptReconstructed canon input.policy output.semanticProgram pairs).map
          (·.argument.id))
        (surfaceAttacksOf output.semanticProgram) declaredResolved =
      output.resolvedAttacks ∧
    (keptReconstructed canon input.policy output.semanticProgram pairs).map
        (·.argument.id) =
      output.argIds ∧
    (keptReconstructed canon input.policy output.semanticProgram pairs).map (·.core) =
      output.unit.args ∧
    claimsOf (keptReconstructed canon input.policy output.semanticProgram pairs)
      output.semanticProgram = output.claims ∧
    openQuestionsOf (keptReconstructed canon input.policy output.semanticProgram pairs) =
      output.openQuestions
  gamma : surfaceGamma canon input.policy output.semanticProgram = output.gamma
  ground : surfaceGround canon input.policy output.semanticProgram = output.ground
  sigma : input.policy.sigma = output.unit.sigma
  unitPolicy : toCorePolicy input.policy = output.unit.policy
  unitAttacks : output.resolvedAttacks = output.unit.atts
  authoredObligations :
    authoredObligationsOf input.program = output.authoredObligations
  /-- Independent premises sufficient for core acceptance. -/
  core : CoreObligations env output

/-- A derivation discharges the production pre-expansion prologue. -/
theorem elaborationPrologue_complete {env : Env canon} {input : Input}
    {output : Elaborated canon} (h : Checks env input output) :
    elaborationPrologue input = .ok () := by
  have hadm := findDuplicate_none_of_nodup h.admission.1
  rcases h.supported.declaration_ids_nodup with
    ⟨⟨⟨hleaves, _⟩, _⟩, _⟩
  have hleaf := findDuplicate_none_of_nodup hleaves
  have hlabels := (canonicalPremiseLabelsB_iff input.policy).2
    h.supported.canonical_labels
  simp [elaborationPrologue, h.supported.policy_matches, hlabels, hadm, hleaf]

/-- A derivation discharges post-expansion identifier and raw-endpoint checks. -/
theorem semanticIdentifierChecks_complete {env : Env canon} {input : Input}
    {output : Elaborated canon} (h : Checks env input output) :
    semanticIdentifierChecks input.policy input.program = .ok () := by
  rcases h.supported.declaration_ids_nodup with
    ⟨⟨⟨_, hargIds⟩, hclaimIds⟩, _⟩
  have harg := findDuplicate_none_of_nodup hargIds
  have hclaim := findDuplicate_none_of_nodup hclaimIds
  have hrules := (ruleNamespacesWellFormedB_iff input.policy).2
    h.supported.rule_namespaces_wf
  have hendpoints := validateAttackEndpoints_complete
    (AttackEndpointsDeclared.of_surfaceAttacksWellFormed
      h.supported.attack_names_wf)
  simp [semanticIdentifierChecks, harg, hclaim, hrules, hendpoints]

/-- Successful assembly against a core-accepted unit yields a derivation. -/
theorem assemble_sound (env : Env canon) (input : Input) (output : Elaborated canon)
    (h : assemble env input = .ok output)
    (hcore : CoreObligations env output) :
    Checks env input output := by
  unfold assemble at h
  cases hprologue : elaborationPrologue input with
  | error e => simp only [hprologue] at h; cases h
  | ok _ =>
    simp only [hprologue] at h
    cases hvalues : expandValues input.policy input.program with
    | error e => simp only [hvalues] at h; cases h
    | ok mid =>
      simp only [hvalues] at h
      cases hcomps : expandComparisons input.policy mid with
      | error e => simp only [hcomps] at h; cases h
      | ok expansion =>
        obtain ⟨semantic, generated⟩ := expansion
        simp only [hcomps] at h
        obtain ⟨hmfresh, hmkeys⟩ :=
          expandComparisons_guards input.policy hcomps
        cases hsemantic : semanticIdentifierChecks input.policy input.program with
        | error error => simp only [hsemantic] at h; cases h
        | ok _ =>
          simp only [hsemantic] at h
          cases hgroups : validateGroups semantic with
          | error error => simp only [hgroups] at h; cases h
          | ok _ =>
            simp only [hgroups] at h
            have hgroupsProp := validateGroups_sound hgroups
            cases hfold : reconstructArgs env semantic input.policy semantic.decls [] with
            | error failure =>
                cases failure with
                | build id => simp only [hfold] at h; cases h
                | lower id => simp only [hfold] at h; cases h
                | conclusionMismatch id claim => simp only [hfold] at h; cases h
                | challengeTargetUndeclared id => simp only [hfold] at h; cases h
            | ok pairs =>
              simp only [hfold] at h
              by_cases hpairIds :
                  (pairs.map fun pair => pair.argument.id.val).Nodup
              · rw [dif_pos hpairIds] at h
                cases hdeclared : resolveSurfaceAttacks input.policy
                    (pairs.map fun pair => (pair.argument.id, pair.core))
                    (surfaceAttacksOf semantic) with
                | error failure => simp only [hdeclared] at h; cases h
                | ok declaredResolved =>
                  simp only [hdeclared] at h
                  cases hstatuses : resolveStatuses semantic with
                  | error error => simp only [hstatuses] at h; cases h
                  | ok atoms =>
                    simp only [hstatuses] at h
                    have hstatusesProp := (resolveStatuses_sound hstatuses).1
                    cases hguards : assembleGuards input with
                    | error error => simp only [hguards] at h; cases h
                    | ok _ =>
                      simp only [hguards] at h
                      obtain ⟨hsupported, hadmission, hfresh⟩ :=
                        assembleGuards_ok input hguards
                      cases h
                      refine
                        { supported := hsupported
                          admission := hadmission
                          freshness := hfresh
                          rules := ?_
                          statuses := hstatusesProp
                          groups := hgroupsProp
                          expansions := ?_
                          program := ?_
                          gamma := rfl
                          ground := rfl
                          sigma := rfl
                          unitPolicy := rfl
                          unitAttacks := rfl
                          authoredObligations := rfl
                          core := hcore }
                      · intro rule hrule
                        exact ⟨hsupported.rule_namespaces_wf.2 rule hrule,
                          hsupported.canonical_labels rule hrule⟩
                      · exact ⟨mid, semantic, generated,
                          expandValues_sound input.policy hvalues, hmfresh, hmkeys,
                          expandComparisons_sound input.policy hcomps, rfl⟩
                      · exact ⟨pairs, declaredResolved,
                          reconstructArgs_sound env semantic input.policy hfold,
                          hpairIds,
                          resolveSurfaceAttacks_sound input.policy hdeclared,
                          rfl, rfl, rfl, rfl, rfl⟩
              · rw [dif_neg hpairIds] at h
                cases h
/-- Independent derivations reconstruct the exact executable assembly result. -/
theorem assemble_complete (env : Env canon) (input : Input) (output : Elaborated canon)
    (h : Checks env input output) :
    assemble env input = .ok output := by
  have hprologue := elaborationPrologue_complete h
  have hsemantic := semanticIdentifierChecks_complete h
  have hguards := assembleGuards_complete h.supported h.admission h.freshness
  rcases h.expansions with
    ⟨mid, target, generated, hvalues, hmidFresh, hkeys, hcomparisons, htarget⟩
  have hvalues' := expandValues_complete input.policy
    h.supported.value_bindings_wf hvalues
  have hcomparisons' := expandComparisons_complete_independent input.policy
    hmidFresh hkeys hcomparisons
  subst target
  have hgroups := validateGroups_complete h.groups
  have hstatuses := resolveStatuses_complete h.statuses
  rcases h.program with
    ⟨pairs, declaredResolved, hprogram, hpairIds, hdeclaredRelation,
      hselected, hids, hargs, hclaims, hquestions⟩
  have hfold := reconstructArgs_complete hprogram
  have hdeclared :
      resolveSurfaceAttacks input.policy
        (pairs.map fun pair => (pair.argument.id, pair.core))
        (surfaceAttacksOf output.semanticProgram) =
        .ok declaredResolved :=
    resolveSurfaceAttacks_complete hdeclaredRelation
  unfold assemble
  simp only [hprologue, hvalues', hcomparisons', hsemantic, hgroups, hfold,
    dif_pos hpairIds, hdeclared, hstatuses, hguards]
  have hgamma := h.gamma
  have hground := h.ground
  have hsigma := h.sigma
  have hunitPolicy := h.unitPolicy
  have hunitAttacks := h.unitAttacks
  have hauthored := h.authoredObligations
  apply congrArg Except.ok
  cases output with
  | mk gamma ground unit claims argIds authoredObligations openQuestions
      resolvedAttacks semanticProgram =>
    cases unit with
    | mk sigma policy args atts =>
      simp_all


/-! ### The executable checker and the correspondence -/

/-- The executable surface checker: staged source validation and assembly,
then core acceptance of the assembled unit. -/
def check (env : Env canon) (input : Input) : Except Error (Elaborated canon) :=
  match assemble env input with
  | .error error => .error error
  | .ok output =>
      match Check.Unit.checkUnit output.gamma env.registry output.ground output.unit with
      | .ok _ => .ok output
      | .error _ => .error .unsupported

/-- One reduction step of `check` through a known assembly result. -/
theorem check_eq_of_assemble (env : Env canon) (input : Input) (out : Elaborated canon)
    (h : assemble env input = .ok out) :
    check env input =
      match Check.Unit.checkUnit out.gamma env.registry out.ground out.unit with
      | .ok _ => .ok out
      | .error _ => .error .unsupported := by
  simp only [check, h]

/-- **Soundness**: a successful run constructs a derivation. -/
theorem check_sound (env : Env canon) (input : Input) (output : Elaborated canon)
    (h : check env input = .ok output) : Checks env input output := by
  cases hassemble : assemble env input with
  | error e =>
      have : check env input = .error e := by simp only [check, hassemble]
      rw [this] at h
      cases h
  | ok out =>
    rw [check_eq_of_assemble env input out hassemble] at h
    cases hcore : Check.Unit.checkUnit out.gamma env.registry out.ground out.unit with
    | error e => rw [hcore] at h; cases h
    | ok checked =>
      rw [hcore] at h
      have hout : out = output := Except.ok.inj h
      subst hout
      exact assemble_sound env input out hassemble
        (CoreObligations.of_checkUnit_ok hcore)

/-- **Completeness**: every derivation is decided successfully. -/
theorem check_complete (env : Env canon) (input : Input) (output : Elaborated canon)
    (h : Checks env input output) : check env input = .ok output := by
  rw [check_eq_of_assemble env input output (assemble_complete env input output h)]
  obtain ⟨checked, hchecked⟩ := h.core.checkUnit_complete
  rw [hchecked]

/-- **Determinism**: independent derivations reconstruct one carrier. -/
theorem checks_deterministic (env : Env canon) (input : Input)
    (out₁ out₂ : Elaborated canon)
    (h₁ : Checks env input out₁) (h₂ : Checks env input out₂) : out₁ = out₂ :=
  Except.ok.inj ((assemble_complete env input out₁ h₁).symm.trans
    (assemble_complete env input out₂ h₂))

/-- Every derivable source lies in the supported fragment. -/
theorem checks_supported (env : Env canon) (input : Input) (output : Elaborated canon)
    (h : Checks env input output) : Supported input :=
  h.supported


/-! ### Executable renaming transport -/

namespace Renaming

def renameCoreRuleId (ρg : Binding.GlobalRenaming)
    (id : Support.RuleId) : Support.RuleId :=
  ⟨(ρg.rule ⟨id.name⟩).val⟩

def renameCoreLeafId (ρg : Binding.GlobalRenaming)
    (id : Support.LeafId) : Support.LeafId :=
  ⟨(ρg.leaf ⟨id.name⟩).val⟩

def renameCoreQuestionId (ρg : Binding.GlobalRenaming)
    (id : Support.QuestionId) : Support.QuestionId :=
  ⟨(ρg.question ⟨id.name⟩).val⟩

def renameCoreCertPayload (ρg : Binding.GlobalRenaming) :
    Support.SExpr → Support.SExpr
  | .list [.atom "prem", .atom source] =>
      .list [.atom "prem", .atom (Binding.renameText ρg source)]
  | .list [.atom "lam", formula, body] =>
      .list [.atom "lam", formula, renameCoreCertPayload ρg body]
  | .list [.atom "lam", binder, formula, body] =>
      .list [.atom "lam", binder, formula, renameCoreCertPayload ρg body]
  | .list [.atom "app", function, argument] =>
      .list [.atom "app", renameCoreCertPayload ρg function,
        renameCoreCertPayload ρg argument]
  | .list [.atom "abort", formula, body] =>
      .list [.atom "abort", formula, renameCoreCertPayload ρg body]
  | expression => expression
termination_by expression => sizeOf expression

def renameCoreCertRef (ρg : Binding.GlobalRenaming)
    (certificate : Support.CertRef) : Support.CertRef :=
  ⟨renameCoreCertPayload ρg certificate.payload⟩

def renameCoreAssurance (ρg : Binding.GlobalRenaming) :
    Support.Assurance → Support.Assurance
  | .none => .none
  | .trusted => .trusted
  | .cert backend digest certificate =>
      .cert backend digest (renameCoreCertRef ρg certificate)

mutual
  def renameCoreSupportTerm (ρg : Binding.GlobalRenaming) :
      Support.SupportTerm → Support.SupportTerm
    | .leaf leaf => .leaf (renameCoreLeafId ρg leaf)
    | .inst rule subst premises discharges holes assurance =>
        .inst (renameCoreRuleId ρg rule)
          (subst.map fun entry =>
            (entry.1, renameResidualTerm ρg entry.2))
          (renameCoreSupportTerms ρg premises)
          (renameCoreSupportDischarges ρg discharges)
          (holes.map (renameCoreQuestionId ρg))
          (renameCoreAssurance ρg assurance)
  def renameCoreSupportTerms (ρg : Binding.GlobalRenaming) :
      List Support.SupportTerm → List Support.SupportTerm
    | [] => []
    | term :: rest =>
        renameCoreSupportTerm ρg term :: renameCoreSupportTerms ρg rest
  def renameCoreSupportDischarges (ρg : Binding.GlobalRenaming) :
      List (Support.QuestionId × Support.SupportTerm) →
        List (Support.QuestionId × Support.SupportTerm)
    | [] => []
    | (question, term) :: rest =>
        (renameCoreQuestionId ρg question, renameCoreSupportTerm ρg term) ::
          renameCoreSupportDischarges ρg rest
end

def renameCorePos (ρg : Binding.GlobalRenaming) :
    Lara.Attack.Pos → Lara.Attack.Pos :=
  List.map fun step => match step with
    | .prem index => .prem index
    | .ques question => .ques (renameCoreQuestionId ρg question)

def renameCoreAttack (ρg : Binding.GlobalRenaming) :
    Lara.Attack.Attack → Lara.Attack.Attack
  | .rebut source target =>
      .rebut (renameCoreSupportTerm ρg source)
        (renameCoreSupportTerm ρg target)
  | .undercut source target position =>
      .undercut (renameCoreSupportTerm ρg source)
        (renameCoreSupportTerm ρg target) (renameCorePos ρg position)
  | .undermine source target position =>
      .undermine (renameCoreSupportTerm ρg source)
        (renameCoreSupportTerm ρg target) (renameCorePos ρg position)

def renameRawAttack (ρg : Binding.GlobalRenaming) :
    Lara.RawAttack.RawAttack → Lara.RawAttack.RawAttack
  | .rebut source target =>
      .rebut (ρg.arg ⟨source⟩).val (ρg.arg ⟨target⟩).val
  | .undercut source target position =>
      .undercut (ρg.arg ⟨source⟩).val (ρg.arg ⟨target⟩).val
        (renameCorePos ρg position)
  | .undermine source target position =>
      .undermine (ρg.arg ⟨source⟩).val (ρg.arg ⟨target⟩).val
        (renameCorePos ρg position)

def renameAdmissionCause (ρg : Binding.GlobalRenaming) :
    Lara.Admission.AdmissionCause → Lara.Admission.AdmissionCause
  | .policy => .policy
  | .group group => .group (ρg.group ⟨group⟩).val

def renameAdmissionAudit (ρg : Binding.GlobalRenaming)
    (audit : Lara.Admission.AdmissionAudit) :
    Lara.Admission.AdmissionAudit :=
  { leaves := audit.leaves.map fun entry =>
      (renameCoreLeafId ρg entry.1, entry.2.map (renameAdmissionCause ρg))
    args := audit.args.map fun argument => (ρg.arg ⟨argument⟩).val
    attacks := audit.attacks.map (renameRawAttack ρg) }

def renameAdmissionPrune (ρg : Binding.GlobalRenaming)
    (prune : Lara.Admission.AdmissionPrune) :
    Lara.Admission.AdmissionPrune :=
  let removedSeed := prune.removedSeed.map (renameCoreLeafId ρg)
  let keptIds := prune.keptIds.map fun argument => (ρg.arg ⟨argument⟩).val
  { policySeed := prune.policySeed.map (renameCoreLeafId ρg)
    groupSeed := prune.groupSeed.map (renameCoreLeafId ρg)
    removedSeed := removedSeed
    removedLeaves := prune.removedLeaves.map (renameCoreLeafId ρg)
    checkedLeaves := prune.checkedLeaves.map fun entry =>
      (renameCoreLeafId ρg entry.1, renameResidualAtom ρg entry.2)
    keptArgs := prune.keptArgs.map fun entry =>
      ((ρg.arg ⟨entry.1⟩).val, renameCoreSupportTerm ρg entry.2)
    keptIds := keptIds
    removedArgs := prune.removedArgs.map fun argument =>
      (ρg.arg ⟨argument⟩).val
    keptAttacks := prune.keptAttacks.map (renameCoreAttack ρg)
    removedAttacks := prune.removedAttacks.map (renameRawAttack ρg)
    keep := fun argument =>
      !Lara.Groups.usesLeaf removedSeed argument.2
    keepAttack := fun rawAttack =>
      let endpoints := rawAttack.endpoints
      decide (endpoints.1 ∈ keptIds) && decide (endpoints.2 ∈ keptIds) }

def renameAdmissionResult (ρg : Binding.GlobalRenaming)
    (result : Lara.Admission.AdmissionResult) :
    Lara.Admission.AdmissionResult :=
  { prune := renameAdmissionPrune ρg result.prune
    declaredResolved := result.declaredResolved.map (renameCoreAttack ρg)
    audit := renameAdmissionAudit ρg result.audit }

def renameAdmissionRejection (ρg : Binding.GlobalRenaming)
    (rejection : Lara.Admission.AdmissionRejection) :
    Lara.Admission.AdmissionRejection :=
  { rejection with leaf := renameCoreLeafId ρg rejection.leaf }

def renameSourceInvalid (ρg : Binding.GlobalRenaming) :
    Lara.Admission.SourceInvalid → Lara.Admission.SourceInvalid
  | .duplicateAdmissionKey key => .duplicateAdmissionKey key
  | .duplicateLeafId leaf => .duplicateLeafId (renameCoreLeafId ρg leaf)
  | .metadataLeafMisalignment => .metadataLeafMisalignment

def renameSourceAdmission (ρg : Binding.GlobalRenaming) :
    Lara.Admission.SourceAdmission → Lara.Admission.SourceAdmission
  | .invalid failure => .invalid (renameSourceInvalid ρg failure)
  | .rejected rejection =>
      .rejected (renameAdmissionRejection ρg rejection)
  | .accepted result => .accepted (renameAdmissionResult ρg result)

noncomputable def renameGamma (ρg : Binding.GlobalRenaming)
    (gamma : Support.LeafId → Option Atom) :
    Support.LeafId → Option Atom := fun target =>
  letI := Classical.propDecidable
  if witness : ∃ source, renameCoreLeafId ρg source = target then
    (gamma (Classical.choose witness)).map (renameResidualAtom ρg)
  else none

def renameCoreRule (ρg : Binding.GlobalRenaming)
    (rule : Support.Rule) : Support.Rule :=
  { rule with
    questions := rule.questions.map fun question =>
      { question with name := renameCoreQuestionId ρg question.name } }

def renameCorePolicy (ρg : Binding.GlobalRenaming)
    (policy : Lara.Policy.Policy) : Lara.Policy.Policy :=
  { rules := policy.rules.map fun declaration =>
      { id := renameCoreRuleId ρg declaration.id
        rule := renameCoreRule ρg declaration.rule }
    defeat :=
      { contraries := policy.defeat.contraries
        exceptions := policy.defeat.exceptions.map fun exception =>
          (renameCoreRuleId ρg exception.1, exception.2) } }

def renameCoreUnit (ρg : Binding.GlobalRenaming) (unit : Lara.Unit) : Lara.Unit :=
  { sigma := unit.sigma
    policy := renameCorePolicy ρg unit.policy
    args := unit.args.map (renameCoreSupportTerm ρg)
    atts := unit.atts.map (renameCoreAttack ρg) }

def renameSemanticArgInstantiation (ρg : Binding.GlobalRenaming) :
    Presentation.ArgInstantiation → Presentation.ArgInstantiation
  | .explicitTheta term => .explicitTheta (renameResidualSupportTerm ρg term)
  | .inferTheta rule references discharges obligations assurance =>
      .inferTheta (ρg.rule rule) (references.map ρg.argRef)
        (discharges.map fun discharge =>
          (ρg.question discharge.1, ρg.argRef discharge.2))
        (obligations.map ρg.obligation) (Binding.renameAssurance ρg assurance)

def renameSemanticArg (ρg : Binding.GlobalRenaming)
    (argument : Presentation.Arg) : Presentation.Arg :=
  { id := ρg.arg argument.id
    concl := Binding.renameArgConcl ρg argument.concl
    instantiation := renameSemanticArgInstantiation ρg argument.instantiation }

def renameSemanticDecl (ρg : Binding.GlobalRenaming) :
    Presentation.Decl → Presentation.Decl
  | .leaf leaf =>
      .leaf ⟨ρg.leaf leaf.id, renameResidualAtom ρg leaf.prop,
        leaf.kind, leaf.provenance, leaf.refs.map ρg.source⟩
  | .claim claim =>
      .claim ⟨ρg.prop claim.id, claim.nl,
        renameResidualAtom ρg claim.formal, claim.binding⟩
  | .arg argument => .arg (renameSemanticArg ρg argument)
  | .attack attack => .attack (Binding.renameSurfaceAttack ρg attack)
  | .status proposition => .status (ρg.prop proposition)
  | .group group =>
      .group ⟨ρg.group group.id, group.members.map ρg.leaf⟩
  | .comparison comparison =>
      .comparison
        { comparison with
          conclusion := renameResidualAtom ρg comparison.conclusion
          measurand := ρg.measurand comparison.measurand
          dataset := ρg.dataset comparison.dataset
          recheckArg := ρg.arg comparison.recheckArg
          bridgeArg := ρg.arg comparison.bridgeArg
          result := ρg.leaf comparison.result
          baseline := ρg.leaf comparison.baseline
          binding := ρg.leaf comparison.binding
          claim := { comparison.claim with id := ρg.prop comparison.claim.id }
          supports := comparison.supports.map ρg.prop }

def renameSemanticProgram (ρg : Binding.GlobalRenaming)
    (program : Presentation.Program) : Presentation.Program :=
  { program with
    valueBindings := program.valueBindings.map fun binding =>
      { binding with name := ρg.valueName binding.name }
    decls := program.decls.map (renameSemanticDecl ρg) }

def renameError (ρg : Binding.GlobalRenaming) : Error → Error
  | .unsupported => .unsupported
  | .policyMismatch expected actual => .policyMismatch expected actual
  | .duplicateLeafId id => .duplicateLeafId (ρg.leaf id)
  | .duplicateArgId id => .duplicateArgId (ρg.arg id)
  | .duplicateClaimId id => .duplicateClaimId (ρg.prop id)
  | .duplicateValueName name => .duplicateValueName (ρg.valueName name)
  | .malformedRuleNamespace id => .malformedRuleNamespace (ρg.rule id)
  | .invalidValueBinding name => .invalidValueBinding (ρg.valueName name)
  | .invalidComparison id => .invalidComparison (ρg.prop id)
  | .invalidInferredArgument id => .invalidInferredArgument (ρg.arg id)
  | .invalidNamedCertificate id => .invalidNamedCertificate (ρg.arg id)
  | .conclusionMismatch id claim =>
      .conclusionMismatch (ρg.arg id) (ρg.prop claim)
  | .challengeTargetUndeclared id => .challengeTargetUndeclared (ρg.arg id)
  | .invalidSurfaceAttack source target =>
      .invalidSurfaceAttack (ρg.arg source) (ρg.arg target)
  | .unknownStatusClaim id => .unknownStatusClaim (ρg.prop id)
  | .duplicateGroupId id => .duplicateGroupId (ρg.group id)
  | .groupRepeatedMember group leaf =>
      .groupRepeatedMember (ρg.group group) (ρg.leaf leaf)
  | .groupTooFewMembers id => .groupTooFewMembers (ρg.group id)
  | .groupMemberUndeclared group leaf =>
      .groupMemberUndeclared (ρg.group group) (ρg.leaf leaf)
  | .noncanonicalPremiseLabels id =>
      .noncanonicalPremiseLabels (ρg.rule id)
  | .duplicateAdmissionKey kind provenance =>
      .duplicateAdmissionKey kind provenance
  | .admissionRejected id => .admissionRejected (ρg.leaf id)

def renameExcept (renameFailure : ε → ε') (renameSuccess : α → β) :
    Except ε α → Except ε' β
  | .error failure => .error (renameFailure failure)
  | .ok success => .ok (renameSuccess success)

structure EnvRenamingSound (env : Env canon)
    (ρg : Binding.GlobalRenaming) : Prop where
  startsIdent : ∀ source,
    env.startsIdent (Binding.renameText ρg source) =
      env.startsIdent source
  registryReplay : ∀ backend digest certificate premises conclusion,
    Support.certOkBOf env.registry backend digest
        (renameCoreCertRef ρg certificate)
        (premises.map (renameResidualAtom ρg))
        (renameResidualAtom ρg conclusion) =
      Support.certOkBOf env.registry backend digest certificate
        premises conclusion

theorem sxToSExpr_renameCertPayload
    (sound : RenamingSound ρg program policy)
    (payload : Presentation.Sx) :
    sxToSExpr (Binding.renameCertPayload ρg payload) =
      renameCoreCertPayload ρg (sxToSExpr payload) := by
  induction payload using Binding.renameCertPayload.induct <;>
    simp_all [Binding.renameCertPayload, sxToSExpr, sxListToSExprs,
      renameCoreCertPayload]
  case case6 expression notPrem notLam notNamedLam notApp notAbort =>
    cases expression with
    | str source =>
        simp [sxToSExpr, renameCoreCertPayload]
    | int value =>
        simp [sxToSExpr, renameCoreCertPayload]
    | node tag children =>
        cases children with
        | nil =>
            simp [sxToSExpr, sxListToSExprs, renameCoreCertPayload]
        | cons first rest =>
            cases rest with
            | nil =>
                cases first with
                | str source =>
                    simp_all [sxToSExpr, sxListToSExprs,
                      renameCoreCertPayload]
                | int value =>
                    by_cases tagged : tag = "prem"
                    · subst tag
                      simpa [sxToSExpr, sxListToSExprs,
                        renameCoreCertPayload] using (sound.integer value).symm
                    · simp [sxToSExpr, sxListToSExprs,
                        renameCoreCertPayload, tagged]
                | node childTag childValues =>
                    simp [sxToSExpr, sxListToSExprs,
                      renameCoreCertPayload]
            | cons second rest =>
                cases rest with
                | nil =>
                    simp_all [sxToSExpr, sxListToSExprs,
                      renameCoreCertPayload]
                | cons third rest =>
                    cases rest with
                    | nil =>
                        by_cases tagged : tag = "lam"
                        · apply False.elim
                          apply notNamedLam first second third
                          simpa [tagged]
                        · simp [sxToSExpr, sxListToSExprs,
                            renameCoreCertPayload, tagged]
                    | cons fourth rest =>
                        cases rest <;>
                          simp_all [sxToSExpr, sxListToSExprs,
                            renameCoreCertPayload]




private theorem firstNamedMarker_isSome_renameCoreCertPayload
    (envSound : EnvRenamingSound env ρg)
    (expression : Support.SExpr) :
    (Lara.NDNamed.firstNamedMarker env.startsIdent
        (renameCoreCertPayload ρg expression)).isSome =
      (Lara.NDNamed.firstNamedMarker env.startsIdent expression).isSome := by
  induction expression using renameCoreCertPayload.induct with
  | case1 source =>
      simp [renameCoreCertPayload, Lara.NDNamed.firstNamedMarker,
        Lara.NDNamed.firstNamedMarkerList, Lara.NDNamed.markerHere,
        Lara.NDNamed.premiseSource, Lara.NDNamed.theorySource,
        Lara.NDNamed.propSource, Lara.NDNamed.hypothesisSource,
        Lara.NDNamed.namedHypSource, Lara.NDNamed.namedAbstraction,
        Lara.Cell.Tag.parse, Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
        Lara.NDNamed.NamedTag.parse, Lara.NDNamed.NamedTag.all,
        Lara.NDNamed.NamedTag.toString, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString, envSound.startsIdent]
  | case2 formula body ih =>
      simp [renameCoreCertPayload, Lara.NDNamed.firstNamedMarker,
        Lara.NDNamed.firstNamedMarkerList, Lara.NDNamed.markerHere,
        Lara.NDNamed.premiseSource, Lara.NDNamed.theorySource,
        Lara.NDNamed.propSource, Lara.NDNamed.hypothesisSource,
        Lara.NDNamed.namedHypSource, Lara.NDNamed.namedAbstraction,
        Lara.Cell.Tag.parse, Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
        Lara.NDNamed.NamedTag.parse, Lara.NDNamed.NamedTag.all,
        Lara.NDNamed.NamedTag.toString, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString, envSound.startsIdent]
      cases h : Lara.NDNamed.firstNamedMarker env.startsIdent formula <;>
        simp_all
      cases hRenamed :
          Lara.NDNamed.firstNamedMarker env.startsIdent
            (renameCoreCertPayload ρg body) <;>
        cases hOriginal :
          Lara.NDNamed.firstNamedMarker env.startsIdent body <;>
        simp_all
  | case3 binder formula body ih =>
      simp [renameCoreCertPayload, Lara.NDNamed.firstNamedMarker,
        Lara.NDNamed.firstNamedMarkerList, Lara.NDNamed.markerHere,
        Lara.NDNamed.premiseSource, Lara.NDNamed.theorySource,
        Lara.NDNamed.propSource, Lara.NDNamed.hypothesisSource,
        Lara.NDNamed.namedHypSource, Lara.NDNamed.namedAbstraction,
        Lara.Cell.Tag.parse, Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
        Lara.NDNamed.NamedTag.parse, Lara.NDNamed.NamedTag.all,
        Lara.NDNamed.NamedTag.toString, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString, envSound.startsIdent]
      cases binder <;> simp_all
  | case4 function argument ihFunction ihArgument =>
      simp [renameCoreCertPayload, Lara.NDNamed.firstNamedMarker,
        Lara.NDNamed.firstNamedMarkerList, Lara.NDNamed.markerHere,
        Lara.NDNamed.premiseSource, Lara.NDNamed.theorySource,
        Lara.NDNamed.propSource, Lara.NDNamed.hypothesisSource,
        Lara.NDNamed.namedHypSource, Lara.NDNamed.namedAbstraction,
        Lara.Cell.Tag.parse, Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
        Lara.NDNamed.NamedTag.parse, Lara.NDNamed.NamedTag.all,
        Lara.NDNamed.NamedTag.toString, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString, envSound.startsIdent]
      cases hFunction :
          Lara.NDNamed.firstNamedMarker env.startsIdent
            (renameCoreCertPayload ρg function) <;>
        cases hOriginal :
          Lara.NDNamed.firstNamedMarker env.startsIdent function <;>
        simp_all
      cases hArgumentRenamed :
          Lara.NDNamed.firstNamedMarker env.startsIdent
            (renameCoreCertPayload ρg argument) <;>
        cases hArgumentOriginal :
          Lara.NDNamed.firstNamedMarker env.startsIdent argument <;>
        simp_all
  | case5 formula body ih =>
      simp [renameCoreCertPayload, Lara.NDNamed.firstNamedMarker,
        Lara.NDNamed.firstNamedMarkerList, Lara.NDNamed.markerHere,
        Lara.NDNamed.premiseSource, Lara.NDNamed.theorySource,
        Lara.NDNamed.propSource, Lara.NDNamed.hypothesisSource,
        Lara.NDNamed.namedHypSource, Lara.NDNamed.namedAbstraction,
        Lara.Cell.Tag.parse, Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
        Lara.NDNamed.NamedTag.parse, Lara.NDNamed.NamedTag.all,
        Lara.NDNamed.NamedTag.toString, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString, envSound.startsIdent]
      cases h : Lara.NDNamed.firstNamedMarker env.startsIdent formula <;>
        simp_all
      cases hRenamed :
          Lara.NDNamed.firstNamedMarker env.startsIdent
            (renameCoreCertPayload ρg body) <;>
        cases hOriginal :
          Lara.NDNamed.firstNamedMarker env.startsIdent body <;>
        simp_all
  | case6 expression =>
      simp [renameCoreCertPayload]


private theorem ndTag_parse_eq_some_iff (source : String) (tag : Lara.ND.Tag) :
    Lara.ND.Tag.parse source = some tag ↔ source = tag.toString := by
  cases tag <;> constructor
  all_goals
    intro h
    first
    | subst source; rfl
    | unfold Lara.ND.Tag.parse at h; split at h <;> simp_all
  all_goals simp [Lara.ND.Tag.toString]
private theorem cellTag_parse_eq_some_iff (source : String)
    (tag : Lara.Cell.Tag) :
    Lara.Cell.Tag.parse source = some tag ↔ source = tag.toString := by
  cases tag <;>
    simp [Lara.Cell.Tag.parse, Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
      eq_comm]

private theorem namedTag_parse_eq_some_iff (source : String)
    (tag : Lara.NDNamed.NamedTag) :
    Lara.NDNamed.NamedTag.parse source = some tag ↔
      source = tag.toString := by
  cases tag with
  | thy =>
      by_cases thy : source = "thy"
      · subst source
        simp [Lara.NDNamed.NamedTag.parse, Lara.NDNamed.NamedTag.all,
          Lara.NDNamed.NamedTag.toString]
      · by_cases prop : source = "prop"
        · subst source
          simp [Lara.NDNamed.NamedTag.parse, Lara.NDNamed.NamedTag.all,
            Lara.NDNamed.NamedTag.toString]
        · have thyReverse : ¬"thy" = source := by
            simpa [eq_comm] using thy
          have propReverse : ¬"prop" = source := by
            simpa [eq_comm] using prop
          simp [Lara.NDNamed.NamedTag.parse, Lara.NDNamed.NamedTag.all,
            Lara.NDNamed.NamedTag.toString, thy, prop, thyReverse,
            propReverse]
  | prop =>
      by_cases thy : source = "thy"
      · subst source
        simp [Lara.NDNamed.NamedTag.parse, Lara.NDNamed.NamedTag.all,
          Lara.NDNamed.NamedTag.toString]
      · by_cases prop : source = "prop"
        · subst source
          simp [Lara.NDNamed.NamedTag.parse, Lara.NDNamed.NamedTag.all,
            Lara.NDNamed.NamedTag.toString]
        · have thyReverse : ¬"thy" = source := by
            simpa [eq_comm] using thy
          have propReverse : ¬"prop" = source := by
            simpa [eq_comm] using prop
          simp [Lara.NDNamed.NamedTag.parse, Lara.NDNamed.NamedTag.all,
            Lara.NDNamed.NamedTag.toString, thy, prop, thyReverse,
            propReverse]


@[simp] private theorem renameCoreCertPayload_kernelHypothesis
    (ρg : Binding.GlobalRenaming) (index : Nat) :
    renameCoreCertPayload ρg (Lara.NDNamed.kernelHypothesis index) =
      Lara.NDNamed.kernelHypothesis index := by
  simp [Lara.NDNamed.kernelHypothesis, renameCoreCertPayload,
    Lara.ND.Tag.toString]

@[simp] private theorem renameCoreCertPayload_lam
    (ρg : Binding.GlobalRenaming) (formula body : Support.SExpr) :
    renameCoreCertPayload ρg
        (.list [.atom Lara.ND.Tag.lam.toString, formula, body]) =
      .list [.atom Lara.ND.Tag.lam.toString, formula,
        renameCoreCertPayload ρg body] := by
  simp [Lara.ND.Tag.toString, renameCoreCertPayload]

@[simp] private theorem renameCoreCertPayload_app
    (ρg : Binding.GlobalRenaming) (function argument : Support.SExpr) :
    renameCoreCertPayload ρg
        (.list [.atom Lara.ND.Tag.app.toString, function, argument]) =
      .list [.atom Lara.ND.Tag.app.toString,
        renameCoreCertPayload ρg function,
        renameCoreCertPayload ρg argument] := by
  simp [Lara.ND.Tag.toString, renameCoreCertPayload]

@[simp] private theorem renameCoreCertPayload_abort
    (ρg : Binding.GlobalRenaming) (formula body : Support.SExpr) :
    renameCoreCertPayload ρg
        (.list [.atom Lara.ND.Tag.abort.toString, formula, body]) =
      .list [.atom Lara.ND.Tag.abort.toString, formula,
        renameCoreCertPayload ρg body] := by
  simp [Lara.ND.Tag.toString, renameCoreCertPayload]

private theorem lowerNamedExpr_renameCertPayload
    (sound : RenamingSound ρg program policy)
    (envSound : EnvRenamingSound env ρg)
    (resolver resolverRenamed : String → Option Nat)
    (resolverCommutes : ∀ name,
      resolverRenamed (Binding.renameText ρg name) = resolver name)
    (premiseCount : Nat) (binders : List (Option String))
    (payload : Presentation.Sx)
    (bindersFixed : ∀ name, some name ∈ binders →
      Binding.renameText ρg name = name)
    (payloadBindersContained : payloadBinderSpellings payload ⊆
      programBinderSpellings program) :
    Lara.NDNamed.lowerNamedExpr env.startsIdent resolverRenamed env.encodeProp
        premiseCount binders
        (sxToSExpr (Binding.renameCertPayload ρg payload)) =
      (Lara.NDNamed.lowerNamedExpr env.startsIdent resolver env.encodeProp
        premiseCount binders (sxToSExpr payload)).map
          (renameCoreCertPayload ρg) := by
  induction payload using Binding.renameCertPayload.induct generalizing binders <;>
    simp_all [Binding.renameCertPayload, sxToSExpr, sxListToSExprs,
      renameCoreCertPayload, Lara.NDNamed.lowerNamedExpr,
      Lara.NDNamed.lowerFormula,
      Lara.Cell.Tag.parse, Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
      Lara.NDNamed.NamedTag.parse, Lara.NDNamed.NamedTag.all,
      Lara.NDNamed.NamedTag.toString, Lara.ND.Tag.parse,
      Lara.ND.Tag.toString, envSound.startsIdent, resolverCommutes,
      sound.cellCanonNat, sound.numeric, sound.integer,
      payloadBinderSpellings, sxListBinderSpellings]
  case case1 =>
    rename_i source
    cases parsed : Lara.Cell.parseCanonNat source <;> simp_all
    split <;> simp_all
    cases resolved : resolver source <;> simp_all
  case case2 formula body ih =>
    cases formulaResult :
        Lara.NDNamed.lowerFormula env.encodeProp (sxToSExpr formula) <;>
      simp_all
    cases bodyResult :
        Lara.NDNamed.lowerNamedExpr env.startsIdent resolver env.encodeProp
          premiseCount _ (sxToSExpr body) <;>
      simp_all [renameCoreCertPayload]
  case case3 binder formula body ih =>
    have bodyContained : payloadBinderSpellings body ⊆
        programBinderSpellings program := by
      intro name member
      apply payloadBindersContained
      cases binder <;>
        simp_all [payloadBinderSpellings, sxListBinderSpellings]
    cases binder with
    | str name =>
        have binderContained : name ∈ programBinderSpellings program := by
          apply payloadBindersContained
          simp [payloadBinderSpellings, sxListBinderSpellings]
        have binderFixed := sound.certBinders name binderContained
        have resolverFixed : resolverRenamed name = resolver name := by
          calc
            resolverRenamed name =
                resolverRenamed (Binding.renameText ρg name) := by
              rw [binderFixed]
            _ = resolver name := resolverCommutes name
        have ihBody := ih (some name :: binders)
          (by
            intro candidate member
            simp only [List.mem_cons, Option.some.injEq] at member
            cases member with
            | inl equal => simpa [equal] using binderFixed
            | inr rest => exact bindersFixed candidate rest)
          bodyContained
        simp [sxToSExpr, Lara.NDNamed.lowerNamedExpr, resolverFixed,
          ihBody, renameCoreCertPayload, Lara.ND.Tag.parse]
        by_cases starts : env.startsIdent name = true <;> simp_all
        cases binderResult :
            Lara.NDNamed.binderIndex name binders <;> simp_all
        cases resolverResult : resolver name <;> simp_all
        cases formulaResult :
            Lara.NDNamed.lowerFormula env.encodeProp
              (sxToSExpr formula) <;> simp_all
        cases bodyResult :
            Lara.NDNamed.lowerNamedExpr env.startsIdent resolver
              env.encodeProp premiseCount (some name :: binders)
              (sxToSExpr body) <;> simp_all [renameCoreCertPayload]
    | int value =>
        have valueFixed :
            Binding.renameText ρg value.repr = value.repr := by
          simpa using sound.integer value
        have resolverFixed : resolverRenamed value.repr =
            resolver value.repr := by
          calc
            resolverRenamed value.repr =
                resolverRenamed (Binding.renameText ρg value.repr) := by
              rw [valueFixed]
            _ = resolver value.repr := resolverCommutes value.repr
        have ihBody := ih (some value.repr :: binders)
          (by
            intro candidate member
            simp only [List.mem_cons, Option.some.injEq] at member
            cases member with
            | inl equal => simpa [equal] using valueFixed
            | inr rest => exact bindersFixed candidate rest)
          bodyContained
        simp [sxToSExpr, Lara.NDNamed.lowerNamedExpr, resolverFixed,
          ihBody, renameCoreCertPayload, Lara.ND.Tag.parse]
        by_cases starts : env.startsIdent value.repr = true <;> simp_all
        cases binderResult :
            Lara.NDNamed.binderIndex value.repr binders <;> simp_all
        cases resolverResult : resolver value.repr <;> simp_all
        cases formulaResult :
            Lara.NDNamed.lowerFormula env.encodeProp
              (sxToSExpr formula) <;> simp_all
        cases bodyResult :
            Lara.NDNamed.lowerNamedExpr env.startsIdent resolver
              env.encodeProp premiseCount (some value.repr :: binders)
              (sxToSExpr body) <;> simp_all [renameCoreCertPayload]
    | node tag children =>
        simp [sxToSExpr, Lara.NDNamed.lowerNamedExpr,
          Lara.ND.Tag.parse]
  case case4 function argument ihFunction ihArgument =>
    cases functionResult :
        Lara.NDNamed.lowerNamedExpr env.startsIdent resolver env.encodeProp
          premiseCount _ (sxToSExpr function) <;>
      simp_all
    cases argumentResult :
        Lara.NDNamed.lowerNamedExpr env.startsIdent resolver env.encodeProp
          premiseCount _ (sxToSExpr argument) <;>
      simp_all [renameCoreCertPayload]
  case case5 formula body ih =>
    cases formulaResult :
        Lara.NDNamed.lowerFormula env.encodeProp (sxToSExpr formula) <;>
      simp_all
    cases bodyResult :
        Lara.NDNamed.lowerNamedExpr env.startsIdent resolver env.encodeProp
          premiseCount _ (sxToSExpr body) <;>
      simp_all [renameCoreCertPayload]
  case case6 expression hPrem hLam hNamedLam hApp hAbort =>
    cases expression with
    | str source =>
        simp [sxToSExpr, Lara.NDNamed.lowerNamedExpr,
          renameCoreCertPayload]
    | int value =>
        simp [sxToSExpr, Lara.NDNamed.lowerNamedExpr,
          renameCoreCertPayload, sound.integer]
    | node tag children =>
        cases children with
        | nil =>
            simp [sxToSExpr, sxListToSExprs,
              Lara.NDNamed.lowerNamedExpr, renameCoreCertPayload]
        | cons first rest =>
            cases rest with
            | nil =>
                cases first with
                | str source =>
                    have notPrem : tag ≠ "prem" := by
                      intro equal
                      exact hPrem source (by simp [equal])
                    by_cases thy : tag = "thy"
                    · subst tag
                      simp [sxToSExpr, sxListToSExprs,
                        Lara.NDNamed.lowerNamedExpr,
                        renameCoreCertPayload, Lara.Cell.Tag.parse,
                        Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
                        Lara.NDNamed.NamedTag.parse,
                        Lara.NDNamed.NamedTag.all,
                        Lara.NDNamed.NamedTag.toString,
                        Lara.ND.Tag.parse, Lara.ND.Tag.toString]
                      cases parsed :
                          Lara.Cell.parseCanonNat source <;> simp_all
                    · by_cases hyp : tag = "hyp"
                      · subst tag
                        simp [sxToSExpr, sxListToSExprs,
                          Lara.NDNamed.lowerNamedExpr,
                          renameCoreCertPayload, Lara.Cell.Tag.parse,
                          Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
                          Lara.NDNamed.NamedTag.parse,
                          Lara.NDNamed.NamedTag.all,
                          Lara.NDNamed.NamedTag.toString,
                          Lara.ND.Tag.parse, Lara.ND.Tag.toString]
                        cases parsed : Lara.Cell.parseCanonNat source <;>
                          simp_all
                        cases found :
                            Lara.NDNamed.binderIndex source binders <;>
                          simp_all
                      · simp [sxToSExpr, sxListToSExprs,
                          Lara.NDNamed.lowerNamedExpr,
                          renameCoreCertPayload,
                          cellTag_parse_eq_some_iff,
                          namedTag_parse_eq_some_iff,
                          ndTag_parse_eq_some_iff,
                          Lara.Cell.Tag.toString,
                          Lara.NDNamed.NamedTag.toString,
                          Lara.ND.Tag.toString, notPrem, thy, hyp]
                | int value =>
                    have valueFixed :
                        Binding.renameText ρg value.repr = value.repr := by
                      simpa using sound.integer value
                    have resolverFixed :
                        resolverRenamed value.repr = resolver value.repr := by
                      calc
                        resolverRenamed value.repr =
                            resolverRenamed
                              (Binding.renameText ρg value.repr) := by
                          rw [valueFixed]
                        _ = resolver value.repr :=
                          resolverCommutes value.repr
                    by_cases prem : tag = "prem"
                    · subst tag
                      simp [sxToSExpr, sxListToSExprs,
                        Lara.NDNamed.lowerNamedExpr,
                        renameCoreCertPayload, resolverFixed,
                        Lara.Cell.Tag.parse, Lara.Cell.Tag.all,
                        Lara.Cell.Tag.toString,
                        Lara.NDNamed.NamedTag.parse,
                        Lara.NDNamed.NamedTag.all,
                        Lara.NDNamed.NamedTag.toString,
                        Lara.ND.Tag.parse, Lara.ND.Tag.toString]
                      cases parsed :
                          Lara.Cell.parseCanonNat value.repr <;> simp_all
                      split <;> simp_all
                      cases resolved : resolver value.repr <;> simp_all
                    · by_cases thy : tag = "thy"
                      · subst tag
                        simp [sxToSExpr, sxListToSExprs,
                          Lara.NDNamed.lowerNamedExpr,
                          renameCoreCertPayload, Lara.Cell.Tag.parse,
                          Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
                          Lara.NDNamed.NamedTag.parse,
                          Lara.NDNamed.NamedTag.all,
                          Lara.NDNamed.NamedTag.toString,
                          Lara.ND.Tag.parse, Lara.ND.Tag.toString]
                        cases parsed :
                            Lara.Cell.parseCanonNat value.repr <;> simp_all
                      · by_cases hyp : tag = "hyp"
                        · subst tag
                          simp [sxToSExpr, sxListToSExprs,
                            Lara.NDNamed.lowerNamedExpr,
                            renameCoreCertPayload, Lara.Cell.Tag.parse,
                            Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
                            Lara.NDNamed.NamedTag.parse,
                            Lara.NDNamed.NamedTag.all,
                            Lara.NDNamed.NamedTag.toString,
                            Lara.ND.Tag.parse, Lara.ND.Tag.toString]
                          cases parsed :
                              Lara.Cell.parseCanonNat value.repr <;> simp_all
                          cases found :
                              Lara.NDNamed.binderIndex value.repr binders <;>
                            simp_all
                        · simp [sxToSExpr, sxListToSExprs,
                            Lara.NDNamed.lowerNamedExpr,
                            renameCoreCertPayload,
                            cellTag_parse_eq_some_iff,
                            namedTag_parse_eq_some_iff,
                            ndTag_parse_eq_some_iff,
                            Lara.Cell.Tag.toString,
                            Lara.NDNamed.NamedTag.toString,
                            Lara.ND.Tag.toString, prem, thy, hyp]
                | node childTag childChildren =>
                    simp [sxToSExpr, sxListToSExprs,
                      Lara.NDNamed.lowerNamedExpr, renameCoreCertPayload]
            | cons second rest =>
                cases rest with
                | nil =>
                    simp_all [sxToSExpr, sxListToSExprs,
                      Lara.NDNamed.lowerNamedExpr, renameCoreCertPayload,
                      ndTag_parse_eq_some_iff, Lara.ND.Tag.toString]
                | cons third rest =>
                    cases rest with
                    | nil =>
                        have notLam : tag ≠ "lam" := by
                          intro equal
                          exact hNamedLam first second third (by simp [equal])
                        have notLamParse :
                            Lara.ND.Tag.parse tag ≠ some .lam := by
                          intro parsed
                          have equal :=
                            (ndTag_parse_eq_some_iff tag .lam).mp parsed
                          exact notLam (by
                            simpa [Lara.ND.Tag.toString] using equal)
                        change
                          Lara.NDNamed.lowerNamedExpr env.startsIdent
                              resolverRenamed env.encodeProp premiseCount binders
                              (.list [.atom tag, sxToSExpr first,
                                sxToSExpr second, sxToSExpr third]) =
                            Option.map (renameCoreCertPayload ρg)
                              (Lara.NDNamed.lowerNamedExpr env.startsIdent
                                resolver env.encodeProp premiseCount binders
                                (.list [.atom tag, sxToSExpr first,
                                  sxToSExpr second, sxToSExpr third]))
                        unfold Lara.NDNamed.lowerNamedExpr
                        simp [notLamParse, renameCoreCertPayload,
                          Lara.ND.Tag.toString, notLam]
                    | cons fourth rest =>
                        cases rest <;>
                          simp_all [sxToSExpr, sxListToSExprs,
                            Lara.NDNamed.lowerNamedExpr,

                            renameCoreCertPayload]
private theorem lowerNamed_renameCertPayload
    (sound : RenamingSound ρg program policy)
    (envSound : EnvRenamingSound env ρg)
    (resolver resolverRenamed : String → Option Nat)
    (resolverCommutes : ∀ name,
      resolverRenamed (Binding.renameText ρg name) = resolver name)
    (premiseCount : Nat) (binders : List (Option String))
    (payload : Presentation.Sx)
    (bindersFixed : ∀ name, some name ∈ binders →
      Binding.renameText ρg name = name)
    (payloadBindersContained : payloadBinderSpellings payload ⊆
      programBinderSpellings program) :
    Lara.NDNamed.lowerNamed env.startsIdent resolverRenamed env.encodeProp
        premiseCount binders
        (sxToSExpr (Binding.renameCertPayload ρg payload)) =
      (Lara.NDNamed.lowerNamed env.startsIdent resolver env.encodeProp
        premiseCount binders (sxToSExpr payload)).map
          (renameCoreCertPayload ρg) := by
  unfold Lara.NDNamed.lowerNamed
  have initialSome :
      (Lara.NDNamed.firstNamedMarker env.startsIdent
        (sxToSExpr (Binding.renameCertPayload ρg payload))).isSome =
      (Lara.NDNamed.firstNamedMarker env.startsIdent
        (sxToSExpr payload)).isSome := by
    rw [sxToSExpr_renameCertPayload sound]
    exact firstNamedMarker_isSome_renameCoreCertPayload envSound
      (sxToSExpr payload)
  generalize renamedInitial :
      Lara.NDNamed.firstNamedMarker env.startsIdent
        (sxToSExpr (Binding.renameCertPayload ρg payload)) = renamedMarker
  generalize sourceInitial :
      Lara.NDNamed.firstNamedMarker env.startsIdent
        (sxToSExpr payload) = sourceMarker
  cases renamedMarker <;> cases sourceMarker
  case none.none =>
    simpa using sxToSExpr_renameCertPayload sound payload
  case none.some => simp_all
  case some.none => simp_all
  case some.some =>
    rw [lowerNamedExpr_renameCertPayload sound envSound resolver
      resolverRenamed resolverCommutes premiseCount binders payload
      bindersFixed payloadBindersContained]
    generalize sourceLowered :
        Lara.NDNamed.lowerNamedExpr env.startsIdent resolver env.encodeProp
          premiseCount binders (sxToSExpr payload) = lowered
    cases lowered with
    | none => simp
    | some lowered =>
        simp only [Option.map_some, Option.bind_some]
        have residualSome :=
          firstNamedMarker_isSome_renameCoreCertPayload envSound lowered
        generalize renamedResidual :
            Lara.NDNamed.firstNamedMarker env.startsIdent
              (renameCoreCertPayload ρg lowered) = renamedMarker
        generalize sourceResidual :
            Lara.NDNamed.firstNamedMarker env.startsIdent lowered = sourceMarker
        cases renamedMarker <;> cases sourceMarker <;>
          simp_all
private theorem matchSchema_head_notCert
    (found : Lara.CertSlots.matchSchema backend version payload =
      some (schema, head, arguments)) :
    head ≠ "prem" ∧ head ≠ "lam" ∧ head ≠ "app" ∧ head ≠ "abort" := by
  have shape := Lara.CertSlots.matchSchema_shape found
  subst payload
  constructor
  · intro equal
    subst head
    simp [Lara.CertSlots.matchSchema, Lara.CertSlots.schemasFor,
      Lara.CertSlots.slotSchemas, Lara.CertSlots.ordSlotSchema,
      Lara.CertSlots.raSlotSchema, Lara.Ord.Tag.toString,
      Lara.RA.Tag.toString] at found
  constructor
  · intro equal
    subst head
    simp [Lara.CertSlots.matchSchema, Lara.CertSlots.schemasFor,
      Lara.CertSlots.slotSchemas, Lara.CertSlots.ordSlotSchema,
      Lara.CertSlots.raSlotSchema, Lara.Ord.Tag.toString,
      Lara.RA.Tag.toString] at found
  constructor
  · intro equal
    subst head
    simp [Lara.CertSlots.matchSchema, Lara.CertSlots.schemasFor,
      Lara.CertSlots.slotSchemas, Lara.CertSlots.ordSlotSchema,
      Lara.CertSlots.raSlotSchema, Lara.Ord.Tag.toString,
      Lara.RA.Tag.toString] at found
  · intro equal
    subst head
    simp [Lara.CertSlots.matchSchema, Lara.CertSlots.schemasFor,
      Lara.CertSlots.slotSchemas, Lara.CertSlots.ordSlotSchema,
      Lara.CertSlots.raSlotSchema, Lara.Ord.Tag.toString,
      Lara.RA.Tag.toString] at found

private theorem lowerPayload_map_renameCoreCertPayload_of_fixed
    (fixed : renameCoreCertPayload ρg payload = payload) :
    Lara.CertSlots.lowerPayload sourceStartsIdentifier resolver
        backend version payload =
      (Lara.CertSlots.lowerPayload sourceStartsIdentifier resolver
        backend version payload).map (renameCoreCertPayload ρg) := by
  unfold Lara.CertSlots.lowerPayload
  generalize matched :
      Lara.CertSlots.matchSchema backend version payload = selected
  cases selected with
  | none =>
      by_cases dead :
          Lara.CertSlots.backendHasSchema backend version = true ∧
            Lara.CertSlots.hasSymbolicRef payload = true
      · simp [dead]
      · simp [dead, fixed]
  | some selected =>
      rcases selected with ⟨schema, head, arguments⟩
      have notCert := matchSchema_head_notCert matched
      generalize lowered :
          Lara.CertSlots.lowerArgs sourceStartsIdentifier resolver schema 0
            arguments = result
      cases result with
      | none => simp [lowered]
      | some result =>
          rcases notCert with ⟨notPrem, notLam, notApp, notAbort⟩
          cases result with
          | nil =>
              simp [lowered, Function.comp_def, renameCoreCertPayload]
          | cons first rest =>
              cases rest with
              | nil =>
                  simp [lowered, Function.comp_def, renameCoreCertPayload,
                    notPrem]
              | cons second rest =>
                  cases rest with
                  | nil =>
                      simp [lowered, Function.comp_def, renameCoreCertPayload,
                        notLam, notApp, notAbort]
                  | cons third rest =>
                      cases rest with
                      | nil =>
                          simp [lowered, Function.comp_def,
                            renameCoreCertPayload, notLam]
                      | cons fourth rest =>
                          simp [lowered, Function.comp_def,
                            renameCoreCertPayload]

private theorem lowerPayload_renameCertPayload
    (sound : RenamingSound ρg program policy)
    (resolver resolverRenamed : String → Option Nat)
    (resolverCommutes : ∀ name,
      resolverRenamed (Binding.renameText ρg name) = resolver name)
    (backend : String) (version : Nat) (payload : Presentation.Sx)
    (opaqueContained : Binding.opaquePayloadPremiseSpellings payload ⊆
      programOpaqueCertPremiseSpellings program) :
    Lara.CertSlots.lowerPayload sourceStartsIdentifier resolverRenamed
        backend version
        (sxToSExpr (Binding.renameCertPayload ρg payload)) =
      (Lara.CertSlots.lowerPayload sourceStartsIdentifier resolver
        backend version (sxToSExpr payload)).map
          (renameCoreCertPayload ρg) := by
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
      split
      · rfl
      · simpa using sxToSExpr_renameCertPayload sound
          (.node "prem" (.cons (.str source) .nil))
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
      split
      · rfl
      · simpa using sxToSExpr_renameCertPayload sound
          (.node "lam" (.cons formula (.cons body .nil)))
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
      split
      · rfl
      · simpa using sxToSExpr_renameCertPayload sound
          (.node "lam"
            (.cons binder (.cons formula (.cons body .nil))))
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
      split
      · rfl
      · simpa using sxToSExpr_renameCertPayload sound
          (.node "app" (.cons function (.cons argument .nil)))
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
      split
      · rfl
      · simpa using sxToSExpr_renameCertPayload sound
          (.node "abort" (.cons formula (.cons body .nil)))
  | case6 expression notPrem notLam notNamedLam notApp notAbort =>
      have unchanged : Binding.renameCertPayload ρg expression = expression := by
        simp_all [Binding.renameCertPayload]
      rw [unchanged]
      have opaqueEq : Binding.opaquePayloadPremiseSpellings expression =
          Binding.allPayloadPremiseSpellings expression := by
        simp_all [Binding.opaquePayloadPremiseSpellings]
      rw [opaqueEq] at opaqueContained
      rw [lowerPayload_sx_resolver_fixed sound resolver resolverRenamed
        resolverCommutes backend version expression (by
          intro tag children equal
          subst expression
          exact opaqueDefault_node_children_contained tag children
            notPrem opaqueContained)]
      apply lowerPayload_map_renameCoreCertPayload_of_fixed
      exact (sxToSExpr_renameCertPayload sound expression).symm.trans
        (congrArg sxToSExpr unchanged)


def renameReconstructedArgument (ρg : Binding.GlobalRenaming)
    (values : List Presentation.ValueName)
    (row : ReconstructedArgument) : ReconstructedArgument :=
  { argument := Binding.renameArg ρg values row.argument
    built := renamePriorArgument ρg row.built

    core := renameCoreSupportTerm ρg row.core }
theorem lowerAssuranceCertificate_rename
    (sound : RenamingSound ρg program policy)
    (envSound : EnvRenamingSound env ρg)
    (rule : Presentation.Rule) (priors : List PriorArgument)
    (premises : List Presentation.SupportTerm)
    (assurance : Presentation.Assurance)
    (binderContained : assuranceBinderSpellings assurance ⊆
      programBinderSpellings program)
    (opaqueContained : assuranceOpaqueCertPremiseSpellings assurance ⊆
      programOpaqueCertPremiseSpellings program) :
    lowerAssuranceCertificate env (Binding.renameProgram ρg program)
        (Binding.renameRule ρg rule)
        (priors.map (renamePriorArgument ρg))
        (premises.map (renameResidualSupportTerm ρg))
        (Binding.renameAssurance ρg assurance) =
      (lowerAssuranceCertificate env program rule priors premises assurance).map
        (renameCoreAssurance ρg) := by
  cases assurance with
  | none => rfl
  | trusted => rfl
  | cert certificate =>
      cases version : certificate.version with
      | negSucc value =>
          simp [lowerAssuranceCertificate, Binding.renameAssurance, version]
      | ofNat value =>
          have resolverCommutes : ∀ name,
              certificateResolver (Binding.renameProgram ρg program)
                  (Binding.renameRule ρg rule)
                  (priors.map (renamePriorArgument ρg))
                  ((premises.map (renameResidualSupportTerm ρg)))
                  (Binding.renameText ρg name) =
                certificateResolver program rule priors premises name :=
            certificateResolver_rename sound rule priors premises
          by_cases named : certificate.backend.val == "nd" && value == 1
          · simp only [lowerAssuranceCertificate, Binding.renameAssurance,
              version, named, if_true, List.length_map]
            rw [lowerNamed_renameCertPayload sound envSound _ _
              resolverCommutes premises.length [] certificate.payload
              (by simp) binderContained]
            simp [Option.map_map, Function.comp_def, renameCoreAssurance,
              renameCoreCertRef]
          · simp only [lowerAssuranceCertificate, Binding.renameAssurance,
              version, named, if_false, List.length_map]
            simp only [Bool.false_eq_true, if_false]
            rw [lowerPayload_renameCertPayload sound _ _ resolverCommutes
              certificate.backend.val value certificate.payload
              opaqueContained]
            simp [Option.map_map, Function.comp_def, renameCoreAssurance,
              renameCoreCertRef]
@[simp] private theorem renameCoreSupportTerms_eq_map
    (ρg : Binding.GlobalRenaming)
    (terms : List Lara.Support.SupportTerm) :
    renameCoreSupportTerms ρg terms =
      terms.map (renameCoreSupportTerm ρg) := by
  induction terms <;> simp_all [renameCoreSupportTerms]

@[simp] private theorem renameCoreSupportDischarges_eq_map
    (ρg : Binding.GlobalRenaming)
    (discharges :
      List (Lara.Support.QuestionId × Lara.Support.SupportTerm)) :
    renameCoreSupportDischarges ρg discharges =
      discharges.map fun entry =>
        (renameCoreQuestionId ρg entry.1,
          renameCoreSupportTerm ρg entry.2) := by
  induction discharges <;> simp_all [renameCoreSupportDischarges]
mutual
  theorem lowerToSupportTerm_rename
      (sound : RenamingSound ρg program policy)
      (envSound : EnvRenamingSound env ρg)
      (priors : List PriorArgument) (term : Presentation.SupportTerm)
      (binderContained : supportTermBinderSpellings term ⊆
        programBinderSpellings program)
      (opaqueContained : supportTermOpaqueCertPremiseSpellings term ⊆
        programOpaqueCertPremiseSpellings program) :
      lowerToSupportTerm env (Binding.renameProgram ρg program)
          (Binding.renamePolicy ρg policy)
          (priors.map (renamePriorArgument ρg))
          (renameResidualSupportTerm ρg term) =
        (lowerToSupportTerm env program policy priors term).map
          (renameCoreSupportTerm ρg) := by
    cases term with
    | leaf leaf =>
        simp [lowerToSupportTerm, renameResidualSupportTerm,
          renameCoreSupportTerm, toSupportLeafId, renameCoreLeafId]
    | rule ruleId subst premises discharges holes assurance =>
        have assuranceBinders : assuranceBinderSpellings assurance ⊆
            programBinderSpellings program := by
          intro name member
          exact binderContained (by
            simp only [supportTermBinderSpellings, List.mem_append]
            exact Or.inl (Or.inl member))
        have premiseBinders : supportTermsBinderSpellings premises ⊆
            programBinderSpellings program := by
          intro name member
          exact binderContained (by
            simp only [supportTermBinderSpellings, List.mem_append]
            exact Or.inl (Or.inr member))
        have dischargeBinders :
            supportDischargesBinderSpellings discharges ⊆
              programBinderSpellings program := by
          intro name member
          exact binderContained (by
            simp only [supportTermBinderSpellings, List.mem_append]
            exact Or.inr member)
        have assuranceOpaque :
            assuranceOpaqueCertPremiseSpellings assurance ⊆
              programOpaqueCertPremiseSpellings program := by
          intro name member
          exact opaqueContained (by
            simp only [supportTermOpaqueCertPremiseSpellings, List.mem_append]
            exact Or.inl (Or.inl member))
        have premiseOpaque :
            supportTermsOpaqueCertPremiseSpellings premises ⊆
              programOpaqueCertPremiseSpellings program := by
          intro name member
          exact opaqueContained (by
            simp only [supportTermOpaqueCertPremiseSpellings, List.mem_append]
            exact Or.inl (Or.inr member))
        have dischargeOpaque :
            dischargeOpaqueCertPremiseSpellings discharges ⊆
              programOpaqueCertPremiseSpellings program := by
          intro name member
          exact opaqueContained (by
            simp only [supportTermOpaqueCertPremiseSpellings, List.mem_append]
            exact Or.inr member)
        simp only [renameResidualSupportTerm, lowerToSupportTerm]
        rw [ruleById_rename]
        cases found : ruleById policy ruleId with
        | none => rfl
        | some rule =>
            simp only [Option.map_some, Option.bind_some]
            rw [supportTermsToList_rename]
            change
              (lowerAssuranceCertificate env
                (Binding.renameProgram ρg program) (Binding.renameRule ρg rule)
                (priors.map (renamePriorArgument ρg))
                ((supportTermsToList premises).map
                  (renameResidualSupportTerm ρg))
                (Binding.renameAssurance ρg assurance)).bind _ =
              Option.map (renameCoreSupportTerm ρg)
                ((lowerAssuranceCertificate env program rule priors
                  (supportTermsToList premises) assurance).bind _)
            rw [lowerAssuranceCertificate_rename sound envSound rule priors
              (supportTermsToList premises) assurance assuranceBinders
              assuranceOpaque]
            rw [lowerToSupportTerms_rename sound envSound priors premises
              premiseBinders premiseOpaque]
            rw [lowerToSupportDischarges_rename sound envSound priors
              discharges dischargeBinders dischargeOpaque]
            cases assuranceResult :
                lowerAssuranceCertificate env program rule priors
                  (supportTermsToList premises) assurance <;>
              cases premiseResult :
                lowerToSupportTerms env program policy priors premises <;>
              cases dischargeResult :
                lowerToSupportDischarges env program policy priors discharges <;>
              simp_all [Option.map_map, Function.comp_def,
                renameCoreSupportTerm, renameCoreSupportTerms,
                renameCoreSupportDischarges, renameResidualSubst,
                toSupportRuleId, renameCoreRuleId, toSupportParam,
                toSupportObligationId, renameCoreQuestionId]

  theorem lowerToSupportTerms_rename
      (sound : RenamingSound ρg program policy)
      (envSound : EnvRenamingSound env ρg)
      (priors : List PriorArgument) (terms : Presentation.SupportTerms)
      (binderContained : supportTermsBinderSpellings terms ⊆
        programBinderSpellings program)
      (opaqueContained : supportTermsOpaqueCertPremiseSpellings terms ⊆
        programOpaqueCertPremiseSpellings program) :
      lowerToSupportTerms env (Binding.renameProgram ρg program)
          (Binding.renamePolicy ρg policy)
          (priors.map (renamePriorArgument ρg))
          (renameResidualSupportTerms ρg terms) =
        (lowerToSupportTerms env program policy priors terms).map
          (List.map (renameCoreSupportTerm ρg)) := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        have termBinders : supportTermBinderSpellings term ⊆
            programBinderSpellings program := by
          intro name member
          exact binderContained (by
            simp only [supportTermsBinderSpellings, List.mem_append]
            exact Or.inl member)
        have restBinders : supportTermsBinderSpellings rest ⊆
            programBinderSpellings program := by
          intro name member
          exact binderContained (by
            simp only [supportTermsBinderSpellings, List.mem_append]
            exact Or.inr member)
        have termOpaque : supportTermOpaqueCertPremiseSpellings term ⊆
            programOpaqueCertPremiseSpellings program := by
          intro name member
          exact opaqueContained (by
            simp only [supportTermsOpaqueCertPremiseSpellings,
              List.mem_append]
            exact Or.inl member)
        have restOpaque : supportTermsOpaqueCertPremiseSpellings rest ⊆
            programOpaqueCertPremiseSpellings program := by
          intro name member
          exact opaqueContained (by
            simp only [supportTermsOpaqueCertPremiseSpellings,
              List.mem_append]
            exact Or.inr member)
        simp only [renameResidualSupportTerms, lowerToSupportTerms]
        rw [lowerToSupportTerm_rename sound envSound priors term termBinders
          termOpaque]
        rw [lowerToSupportTerms_rename sound envSound priors rest restBinders
          restOpaque]
        cases termResult :
            lowerToSupportTerm env program policy priors term <;>
          cases restResult :
            lowerToSupportTerms env program policy priors rest <;>
          simp_all

  theorem lowerToSupportDischarges_rename
      (sound : RenamingSound ρg program policy)
      (envSound : EnvRenamingSound env ρg)
      (priors : List PriorArgument) (discharges : Presentation.Discharges)
      (binderContained : supportDischargesBinderSpellings discharges ⊆
        programBinderSpellings program)
      (opaqueContained : dischargeOpaqueCertPremiseSpellings discharges ⊆
        programOpaqueCertPremiseSpellings program) :
      lowerToSupportDischarges env (Binding.renameProgram ρg program)
          (Binding.renamePolicy ρg policy)
          (priors.map (renamePriorArgument ρg))
          (renameResidualDischarges ρg discharges) =
        (lowerToSupportDischarges env program policy priors discharges).map
          (List.map fun entry =>
            (renameCoreQuestionId ρg entry.1,
              renameCoreSupportTerm ρg entry.2)) := by
    cases discharges with
    | nil => rfl
    | cons question term rest =>
        have termBinders : supportTermBinderSpellings term ⊆
            programBinderSpellings program := by
          intro name member
          exact binderContained (by
            simp only [supportDischargesBinderSpellings, List.mem_append]
            exact Or.inl member)
        have restBinders : supportDischargesBinderSpellings rest ⊆
            programBinderSpellings program := by
          intro name member
          exact binderContained (by
            simp only [supportDischargesBinderSpellings, List.mem_append]
            exact Or.inr member)
        have termOpaque : supportTermOpaqueCertPremiseSpellings term ⊆
            programOpaqueCertPremiseSpellings program := by
          intro name member
          exact opaqueContained (by
            simp only [dischargeOpaqueCertPremiseSpellings, List.mem_append]
            exact Or.inl member)
        have restOpaque : dischargeOpaqueCertPremiseSpellings rest ⊆
            programOpaqueCertPremiseSpellings program := by
          intro name member
          exact opaqueContained (by
            simp only [dischargeOpaqueCertPremiseSpellings, List.mem_append]
            exact Or.inr member)
        simp only [renameResidualDischarges, lowerToSupportDischarges]
        rw [lowerToSupportTerm_rename sound envSound priors term termBinders
          termOpaque]
        rw [lowerToSupportDischarges_rename sound envSound priors rest
          restBinders restOpaque]
        cases termResult :
            lowerToSupportTerm env program policy priors term <;>
          cases restResult :
            lowerToSupportDischarges env program policy priors rest <;>
          simp_all [toSupportQuestionId, renameCoreQuestionId]
end


def renameReconstructFailure (ρg : Binding.GlobalRenaming) :
    ReconstructFailure → ReconstructFailure
  | .build argument => .build (ρg.arg argument)
  | .lower argument => .lower (ρg.arg argument)
  | .conclusionMismatch argument claim =>
      .conclusionMismatch (ρg.arg argument) (ρg.prop claim)
  | .challengeTargetUndeclared argument =>
      .challengeTargetUndeclared (ρg.arg argument)


mutual
  private theorem nfTerm_renameResidual (canon : String → String)
      (ρg : Binding.GlobalRenaming) (term : Term) :
      Lara.nfTerm canon (renameResidualTerm ρg term) =
        renameResidualTerm ρg (Lara.nfTerm canon term) := by
    cases term with
    | num source => rfl
    | str source => rfl
    | con name terms =>
        cases terms with
        | nil => rfl
        | cons term rest =>
            change Term.con name
                (Lara.nfTerms canon (renameResidualTerms ρg (.cons term rest))) =
              Term.con name (renameResidualTerms ρg
                (Lara.nfTerms canon (.cons term rest)))
            rw [nfTerms_renameResidual]
  private theorem nfTerms_renameResidual (canon : String → String)
      (ρg : Binding.GlobalRenaming) (terms : Terms) :
      Lara.nfTerms canon (renameResidualTerms ρg terms) =
        renameResidualTerms ρg (Lara.nfTerms canon terms) := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp [Lara.nfTerms, renameResidualTerms,
          nfTerm_renameResidual canon ρg term,
          nfTerms_renameResidual canon ρg rest]
end

private theorem nfAtom_renameResidual (canon : String → String)
    (ρg : Binding.GlobalRenaming) (atom : Atom) :
    Lara.nf canon (renameResidualAtom ρg atom) =
      renameResidualAtom ρg (Lara.nf canon atom) := by
  cases atom
  simp [Lara.nf, renameResidualAtom, nfTerms_renameResidual]

private theorem residualAtom_injective (ρg : Binding.GlobalRenaming) :
    Function.Injective (renameResidualAtom ρg) := by
  intro left right equal
  cases left with
  | atom leftPred leftTerms =>
      cases right with
      | atom rightPred rightTerms =>
          simp only [renameResidualAtom, Atom.atom.injEq] at equal
          have terms := (renameResidualTerms_eq_iff ρg).mp equal.2
          simp [equal.1, terms]

private theorem equiv_renameResidual (canon : String → String)
    (ρg : Binding.GlobalRenaming) (left right : Atom) :
    Lara.equiv canon (renameResidualAtom ρg left)
        (renameResidualAtom ρg right) ↔
      Lara.equiv canon left right := by
  simp only [Lara.equiv, nfAtom_renameResidual]
  exact (residualAtom_injective ρg).eq_iff

private theorem claimFormalIn?_rename
    (sound : RenamingSound ρg program policy)
    (declarations : List Presentation.Decl)
    (contained : ∀ declaration ∈ declarations, declaration ∈ program.decls)
    (id : Presentation.PropId) :
    claimFormalIn?
        (declarations.map (Binding.renameDecl ρg (programValues program)))
        (ρg.prop id) =
      (claimFormalIn? declarations id).map (renameResidualAtom ρg) := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
      have headMember : declaration ∈ program.decls :=
        contained declaration (by simp)
      have tailContained : ∀ candidate ∈ rest, candidate ∈ program.decls := by
        intro candidate member
        exact contained candidate (by simp [member])
      cases declaration with
      | claim claim =>
          have fixed : AtomFixed ρg (programValues program) claim.formal :=
            atomFixed_of_decl sound.toComparison (.claim claim) headMember
              claim.formal (by simp [declNullaryCons])
          have formalEq :
              Binding.renameValueAtom ρg (programValues program) claim.formal =
                renameResidualAtom ρg claim.formal :=
            (renameResidualAtom_eq_renameValueAtom fixed).symm
          by_cases same : claim.id = id
          · have renamedSame : ρg.prop claim.id = ρg.prop id :=
              congrArg ρg.prop same
            simp only [claimFormalIn?, List.map_cons, Binding.renameDecl,
              List.findSome?_cons, renamedSame, ↓reduceIte, same,
              Option.map_some]
            exact congrArg some formalEq
          · have renamedNe : ρg.prop claim.id ≠ ρg.prop id := fun equal =>
              same (ρg.prop_injective equal)
            simp only [claimFormalIn?, List.map_cons, Binding.renameDecl,
              List.findSome?_cons, renamedNe, ↓reduceIte, same]
            simpa only [claimFormalIn?] using ih tailContained
      | leaf leaf =>
          simpa [claimFormalIn?, Binding.renameDecl] using ih tailContained
      | arg argument =>
          simpa [claimFormalIn?, Binding.renameDecl] using ih tailContained
      | attack attack =>
          simpa [claimFormalIn?, Binding.renameDecl] using ih tailContained
      | status status =>
          simpa [claimFormalIn?, Binding.renameDecl] using ih tailContained
      | group group =>
          simpa [claimFormalIn?, Binding.renameDecl] using ih tailContained
      | comparison comparison =>
          simpa [claimFormalIn?, Binding.renameDecl] using ih tailContained

private theorem claimFormal?_rename
    (sound : RenamingSound ρg program policy)
    (id : Presentation.PropId) :
    claimFormal? (Binding.renameProgram ρg program) (ρg.prop id) =
      (claimFormal? program id).map (renameResidualAtom ρg) := by
  change
    claimFormalIn?
        (program.decls.map (Binding.renameDecl ρg (programValues program)))
        (ρg.prop id) =
      (claimFormalIn? program.decls id).map (renameResidualAtom ρg)
  exact claimFormalIn?_rename sound program.decls (fun _ member => member) id

private theorem renamedArgMem_iff (ρg : Binding.GlobalRenaming)
    (id : Presentation.ArgId) (ids : List Presentation.ArgId) :
    ρg.arg id ∈ ids.map ρg.arg ↔ id ∈ ids := by
  constructor
  · intro member
    obtain ⟨source, sourceMember, equal⟩ := List.mem_map.mp member
    simpa [ρg.arg_injective equal] using sourceMember
  · exact fun member => List.mem_map.mpr ⟨id, member, rfl⟩

private theorem renamedLeafMem_iff (ρg : Binding.GlobalRenaming)
    (id : Presentation.LeafId) (ids : List Presentation.LeafId) :
    ρg.leaf id ∈ ids.map ρg.leaf ↔ id ∈ ids := by
  constructor
  · intro member
    obtain ⟨source, sourceMember, equal⟩ := List.mem_map.mp member
    simpa [ρg.leaf_injective equal] using sourceMember
  · exact fun member => List.mem_map.mpr ⟨id, member, rfl⟩

private theorem checkAuthoredConclusion_rename
    (sound : RenamingSound ρg program policy)
    (argument : Presentation.ArgId) (authored : Presentation.ArgConcl)
    (derived : Atom) :
    checkAuthoredConclusion canon (Binding.renameProgram ρg program)
        (ρg.arg argument) (Binding.renameArgConcl ρg authored)
        (renameResidualAtom ρg derived) =
      renameExcept (renameReconstructFailure ρg) id
        (checkAuthoredConclusion canon program argument authored derived) := by
  cases authored with
  | supportsClaim claim =>
      simp only [Binding.renameArgConcl, checkAuthoredConclusion]
      rw [claimFormal?_rename sound]
      cases found : claimFormal? program claim with
      | none => simp [checkAuthoredConclusion, found, Binding.renameArgConcl,
          renameExcept]
      | some formal =>
          by_cases equivalent : Lara.equiv canon derived formal
          · have renamedEquivalent : Lara.equiv canon
                (renameResidualAtom ρg derived)
                (renameResidualAtom ρg formal) :=
              (equiv_renameResidual canon ρg derived formal).mpr equivalent
            simp [checkAuthoredConclusion, found, Binding.renameArgConcl,
              equivalent, renamedEquivalent, renameExcept]
          · have renamedNotEquivalent : ¬ Lara.equiv canon
                (renameResidualAtom ρg derived)
                (renameResidualAtom ρg formal) :=
              (not_congr (equiv_renameResidual canon ρg derived formal)).mpr
                equivalent
            simp [checkAuthoredConclusion, found, Binding.renameArgConcl,
              equivalent, renamedNotEquivalent, renameExcept,
              renameReconstructFailure]
  | supportsDerived claim =>
      simp [checkAuthoredConclusion, Binding.renameArgConcl, renameExcept]
  | challenges target =>
      cases target with
      | question question target =>
          simp only [Binding.renameArgConcl]
          unfold checkAuthoredConclusion
          rw [argIds_renameProgram]
          have memberIff := renamedArgMem_iff ρg target (argIds program)
          by_cases member : target ∈ argIds program
          · have renamedMember := memberIff.mpr member
            simp [checkAuthoredConclusion, Binding.renameArgConcl, member,
              renamedMember, renameExcept]
          · have renamedNotMember : ρg.arg target ∉ (argIds program).map ρg.arg :=
              fun found => member (memberIff.mp found)
            simp [checkAuthoredConclusion, Binding.renameArgConcl, member,
              renamedNotMember, renameExcept, renameReconstructFailure]
      | leaf leaf =>
          simp only [Binding.renameArgConcl]
          unfold checkAuthoredConclusion
          rw [leafIds_renameProgram]
          have memberIff := renamedLeafMem_iff ρg leaf (leafIds program)
          by_cases member : leaf ∈ leafIds program
          · have renamedMember := memberIff.mpr member
            simp [checkAuthoredConclusion, Binding.renameArgConcl, member,
              renamedMember, renameExcept]
          · have renamedNotMember : ρg.leaf leaf ∉ (leafIds program).map ρg.leaf :=
              fun found => member (memberIff.mp found)
            simp [checkAuthoredConclusion, Binding.renameArgConcl, member,
              renamedNotMember, renameExcept, renameReconstructFailure]

private theorem filterMapLeaves_rename
    (sound : RenamingSound ρg program policy)
    (canon : String → String) (ground : Atom) :
    (declaredLeaves (Binding.renameProgram ρg program)).filterMap
        (fun entry =>
          if Lara.equiv canon entry.2 (renameResidualAtom ρg ground) then
            some (Presentation.SupportTerm.leaf entry.1)
          else none) =
      ((declaredLeaves program).filterMap fun entry =>
        if Lara.equiv canon entry.2 ground then
          some (Presentation.SupportTerm.leaf entry.1)
        else none).map (renameResidualSupportTerm ρg) := by
  rw [declaredLeaves_renameResidual sound]
  induction declaredLeaves program with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨leaf, atom⟩ := entry
      simp only [List.map_cons, List.filterMap_cons]
      by_cases original : Lara.equiv canon atom ground
      · have renamed :=
          (equiv_renameResidual canon ρg atom ground).mpr original
        simp [original, renamed, ih, renameResidualSupportTerm]
      · have renamed :=
          (not_congr (equiv_renameResidual canon ρg atom ground)).mpr original
        simp [original, renamed, ih]

private theorem filterMapPriors_rename
    (canon : String → String) (ρg : Binding.GlobalRenaming)
    (priors : List PriorArgument) (ground : Atom) :
    (priors.map (renamePriorArgument ρg)).filterMap
        (fun prior =>
          if Lara.equiv canon prior.conclusion (renameResidualAtom ρg ground) then
            some prior.term
          else none) =
      (priors.filterMap fun prior =>
        if Lara.equiv canon prior.conclusion ground then some prior.term
        else none).map (renameResidualSupportTerm ρg) := by
  induction priors with
  | nil => rfl
  | cons prior rest ih =>
      simp only [List.map_cons, List.filterMap_cons, renamePriorArgument]
      by_cases original : Lara.equiv canon prior.conclusion ground
      · have renamed :=
          (equiv_renameResidual canon ρg prior.conclusion ground).mpr original
        simp [original, renamed, ih]
      · have renamed :=
          (not_congr
            (equiv_renameResidual canon ρg prior.conclusion ground)).mpr original
        simp [original, renamed, ih]

theorem premiseMatches_rename
    (sound : RenamingSound ρg program policy)
    (canon : String → String) (priors : List PriorArgument) (ground : Atom) :
    premiseMatches canon (Binding.renameProgram ρg program)
        (priors.map (renamePriorArgument ρg))
        (renameResidualAtom ρg ground) =
      (premiseMatches canon program priors ground).map
        (renameResidualSupportTerm ρg) := by
  simp only [premiseMatches, List.map_append]
  rw [filterMapLeaves_rename sound, filterMapPriors_rename]
private theorem zipParams_renameResidual
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

private theorem resolveImplicitPremise_rename
    (sound : RenamingSound ρg program policy)
    (canon : String → String) (priors : List PriorArgument)
    (theta : SurfaceSubst) (pattern : Presentation.AtomPat)
    (fixed : AtomPatFixed ρg pattern) :
    resolveImplicitPremise canon (Binding.renameProgram ρg program)
        (priors.map (renamePriorArgument ρg))
        (renameResidualSubst ρg theta) pattern =
      (resolveImplicitPremise canon program priors theta pattern).map
        (renameResidualSupportTerm ρg) := by
  unfold resolveImplicitPremise
  rw [instantiateSurfaceAtom_renameResidual fixed]
  cases instantiated : instantiateSurfaceAtom theta pattern with
  | none => rfl
  | some ground =>
      simp [instantiated]
      rw [premiseMatches_rename sound]
      cases premiseMatches canon program priors ground with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second tail => rfl

private theorem resolveImplicitPremises_rename
    (sound : RenamingSound ρg program policy)
    (canon : String → String) (priors : List PriorArgument)
    (theta : SurfaceSubst) (patterns : List Presentation.AtomPat)
    (fixed : ∀ pattern ∈ patterns, AtomPatFixed ρg pattern) :
    resolveImplicitPremises canon (Binding.renameProgram ρg program)
        (priors.map (renamePriorArgument ρg))
        (renameResidualSubst ρg theta) patterns =
      (resolveImplicitPremises canon program priors theta patterns).map
        (renameResidualSupportTerms ρg) := by
  induction patterns with
  | nil => rfl
  | cons pattern rest ih =>
      simp only [resolveImplicitPremises]
      rw [resolveImplicitPremise_rename sound canon priors theta pattern
        (fixed pattern (by simp))]
      cases head : resolveImplicitPremise canon program priors theta pattern with
      | none => rfl
      | some term =>
          simp only [Option.map_some, Option.bind_some]
          rw [ih (fun candidate member =>
            fixed candidate (by simp [member]))]
          cases resolveImplicitPremises canon program priors theta rest <;> rfl

mutual
  theorem reconstructExplicitTerm_rename
      (sound : RenamingSound ρg program policy)
      (canon : String → String) (priors : List PriorArgument)
      (term : Presentation.SupportTerm) :
      reconstructExplicitTerm canon (Binding.renameProgram ρg program)
          (Binding.renamePolicy ρg policy)
          (priors.map (renamePriorArgument ρg))
          (renameResidualSupportTerm ρg term) =
        (reconstructExplicitTerm canon program policy priors term).map
          (renameResidualSupportTerm ρg) := by
    cases term with
    | leaf leaf => rfl
    | rule ruleId positionalTheta premises shallowDischarges holes assurance =>
        cases premises with
        | nil =>
            simp only [renameResidualSupportTerm, renameResidualSupportTerms,
              renameResidualDischarges]
            simp only [reconstructExplicitTerm]
            rw [ruleById_rename]
            cases found : ruleById policy ruleId with
            | none => rfl
            | some rule =>
                simp [found]
                simp only [Binding.renameRule]
                rw [zipParams_renameResidual]
                have member : rule ∈ policy.rules :=
                  List.mem_of_find?_eq_some found
                rw [resolveImplicitPremises_rename sound canon priors
                  (rule.params.zip (positionalTheta.map Prod.snd))
                  rule.premises (fun pattern patternMember =>
                    premisePatternFixed sound rule member pattern patternMember)]
                rw [reconstructExplicitDischarges_rename sound canon priors
                  shallowDischarges]
                by_cases arity : positionalTheta.length = rule.params.length
                · have renamedArity :
                      (renameResidualSubst ρg positionalTheta).length =
                        rule.params.length := by
                    simpa [renameResidualSubst] using arity
                  simp only [if_pos arity, if_pos renamedArity]
                  cases resolveImplicitPremises canon program priors
                      (rule.params.zip (positionalTheta.map Prod.snd))
                      rule.premises <;>
                    cases reconstructExplicitDischarges canon program policy priors
                      shallowDischarges <;>
                    simp [renameResidualSupportTerm, renameResidualSubst,
                      renameResidualDischarges, zipParams_renameResidual, arity]
                · have renamedArity :
                      (renameResidualSubst ρg positionalTheta).length ≠
                        rule.params.length := by
                    simpa [renameResidualSubst] using arity
                  simp [arity, renamedArity]
        | cons premise rest =>
            simp only [renameResidualSupportTerm, renameResidualSupportTerms,
              renameResidualDischarges]
            simp only [reconstructExplicitTerm]
            rw [ruleById_rename]
            cases found : ruleById policy ruleId with
            | none => rfl
            | some rule =>
                simp [found]
                simp only [Binding.renameRule]
                have hterms := reconstructExplicitTerms_rename sound canon priors
                  (.cons premise rest)
                simp only [renameResidualSupportTerms] at hterms
                rw [hterms]
                rw [reconstructExplicitDischarges_rename sound canon priors
                  shallowDischarges]
                by_cases arity : positionalTheta.length = rule.params.length
                · have renamedArity :
                      (renameResidualSubst ρg positionalTheta).length =
                        rule.params.length := by
                    simpa [renameResidualSubst] using arity
                  simp only [if_pos arity, if_pos renamedArity]
                  cases reconstructExplicitTerms canon program policy priors
                      (.cons premise rest) <;>
                    cases reconstructExplicitDischarges canon program policy priors
                      shallowDischarges <;>
                    simp [renameResidualSupportTerm, renameResidualSubst,
                      renameResidualDischarges, zipParams_renameResidual, arity]
                  simpa [renameResidualSubst, Function.comp_def] using
                    zipParams_renameResidual ρg rule.params positionalTheta
                · have renamedArity :
                      (renameResidualSubst ρg positionalTheta).length ≠
                        rule.params.length := by
                    simpa [renameResidualSubst] using arity
                  simp [arity, renamedArity]

  theorem reconstructExplicitTerms_rename
      (sound : RenamingSound ρg program policy)
      (canon : String → String) (priors : List PriorArgument)
      (terms : Presentation.SupportTerms) :
      reconstructExplicitTerms canon (Binding.renameProgram ρg program)
          (Binding.renamePolicy ρg policy)
          (priors.map (renamePriorArgument ρg))
          (renameResidualSupportTerms ρg terms) =
        (reconstructExplicitTerms canon program policy priors terms).map
          (renameResidualSupportTerms ρg) := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp only [renameResidualSupportTerms, reconstructExplicitTerms]
        rw [reconstructExplicitTerm_rename sound canon priors term,
          reconstructExplicitTerms_rename sound canon priors rest]
        cases reconstructExplicitTerm canon program policy priors term <;>
          cases reconstructExplicitTerms canon program policy priors rest <;> rfl

  theorem reconstructExplicitDischarges_rename
      (sound : RenamingSound ρg program policy)
      (canon : String → String) (priors : List PriorArgument)
      (discharges : Presentation.Discharges) :
      reconstructExplicitDischarges canon (Binding.renameProgram ρg program)
          (Binding.renamePolicy ρg policy)
          (priors.map (renamePriorArgument ρg))
          (renameResidualDischarges ρg discharges) =
        (reconstructExplicitDischarges canon program policy priors discharges).map
          (renameResidualDischarges ρg) := by
    cases discharges with
    | nil => rfl
    | cons question term rest =>
        cases term with
        | leaf leaf =>
            simp only [renameResidualDischarges, renameResidualSupportTerm,
              reconstructExplicitDischarges]
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
            rw [referenceEq]
            rw [resolveReference_rename sound,
              reconstructExplicitDischarges_rename sound canon priors rest]
            cases resolveReference program priors ⟨leaf.val⟩ <;>
              cases reconstructExplicitDischarges canon program policy priors rest <;>
              simp [renameResolvedReference, renameResidualDischarges]
        | rule rule subst premises nested holes assurance =>
            rfl
end
theorem reconstructArgument_rename
    (sound : RenamingSound ρg program policy)
    (canon : String → String) (priors : List PriorArgument)
    (argument : Presentation.Arg)
    (member : Presentation.Decl.arg argument ∈ program.decls) :
    reconstructArgument canon (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (priors.map (renamePriorArgument ρg))
        (Binding.renameArg ρg (programValues program) argument) =
      (reconstructArgument canon program policy priors argument).map
        (renamePriorArgument ρg) := by
  cases instantiation : argument.instantiation with
  | inferTheta rule references discharges obligations assurance =>
      simp only [reconstructArgument, Binding.renameArg, instantiation,
        Binding.renameArgInstantiation]
      simpa [Binding.renameArg, instantiation,
        Binding.renameArgInstantiation] using
        buildArgument_rename sound priors argument member
  | explicitTheta term =>
      have fixed := supportTermFixed_of_explicitArg sound argument term member
        instantiation
      have termEq :=
        renameResidualSupportTerm_eq_renameSupportTerm fixed
      simp only [reconstructArgument, Binding.renameArg, instantiation,
        Binding.renameArgInstantiation]
      rw [← termEq, reconstructExplicitTerm_rename sound canon priors term]
      cases rebuiltFound :
          reconstructExplicitTerm canon program policy priors term with
      | none => rfl
      | some rebuilt =>
          simp [rebuiltFound]
          rw [conclOfTerm_rename sound]
          cases conclOfTerm program policy rebuilt <;>
            simp [renamePriorArgument]
private def SupportPayloadsFromProgram
    (program : Presentation.Program)
    (term : Presentation.SupportTerm) : Prop :=
  supportTermBinderSpellings term ⊆ programBinderSpellings program ∧
    supportTermOpaqueCertPremiseSpellings term ⊆
      programOpaqueCertPremiseSpellings program

private theorem premiseMatches_payloads
    (safe : PriorPayloadsFromProgram program priors)
    (ground : Atom) (term : Presentation.SupportTerm)
    (member : term ∈ premiseMatches canon program priors ground) :
    SupportPayloadsFromProgram program term := by
  unfold premiseMatches at member
  simp only [List.mem_append] at member
  rcases member with leafMember | priorMember
  · obtain ⟨entry, entryMember, selected⟩ :=
      List.mem_filterMap.mp leafMember
    split at selected
    · simp only [Option.some.injEq] at selected
      subst term
      simp [SupportPayloadsFromProgram, supportTermBinderSpellings,
        supportTermOpaqueCertPremiseSpellings]
    · simp at selected
  · obtain ⟨prior, priorInPriors, selected⟩ :=
      List.mem_filterMap.mp priorMember
    split at selected
    · simp only [Option.some.injEq] at selected
      subst term
      exact safe prior priorInPriors
    · simp at selected

private theorem resolveImplicitPremise_payloads
    (safe : PriorPayloadsFromProgram program priors)
    (found : resolveImplicitPremise canon program priors theta pattern =
      some term) :
    SupportPayloadsFromProgram program term := by
  unfold resolveImplicitPremise at found
  cases groundFound : instantiateSurfaceAtom theta pattern with
  | none => simp [groundFound] at found
  | some ground =>
      simp only [groundFound, Option.bind_some] at found
      cases matchesFound :
          premiseMatches canon program priors ground with
      | nil => simp [matchesFound] at found
      | cons head rest =>
          cases rest with
          | nil =>
              simp [matchesFound] at found
              subst term
              exact premiseMatches_payloads safe ground head (by
                rw [matchesFound]
                simp)
          | cons next tail => simp [matchesFound] at found

private theorem resolveImplicitPremises_payloads
    (safe : PriorPayloadsFromProgram program priors)
    (found : resolveImplicitPremises canon program priors theta patterns =
      some terms) :
    supportTermsBinderSpellings terms ⊆ programBinderSpellings program ∧
      supportTermsOpaqueCertPremiseSpellings terms ⊆
        programOpaqueCertPremiseSpellings program := by
  induction patterns generalizing terms with
  | nil =>
      simp [resolveImplicitPremises] at found
      subst terms
      simp [supportTermsBinderSpellings,
        supportTermsOpaqueCertPremiseSpellings]
  | cons pattern rest ih =>
      cases headFound :
          resolveImplicitPremise canon program priors theta pattern with
      | none => simp [resolveImplicitPremises, headFound] at found
      | some head =>
          cases tailFound :
              resolveImplicitPremises canon program priors theta rest with
          | none =>
              simp [resolveImplicitPremises, headFound, tailFound] at found
          | some tail =>
              simp [resolveImplicitPremises, headFound, tailFound] at found
              subst terms
              have headSafe := resolveImplicitPremise_payloads safe headFound
              have tailSafe := ih tailFound
              constructor
              · intro name member
                simp only [supportTermsBinderSpellings,
                  List.mem_append] at member
                rcases member with member | member
                · exact headSafe.1 member
                · exact tailSafe.1 member
              · intro name member
                simp only [supportTermsOpaqueCertPremiseSpellings,
                  List.mem_append] at member
                rcases member with member | member
                · exact headSafe.2 member
                · exact tailSafe.2 member

mutual
  private theorem reconstructExplicitTerm_payloads
      (safe : PriorPayloadsFromProgram program priors)
      (authored : SupportPayloadsFromProgram program term)
      (found : reconstructExplicitTerm canon program policy priors term =
        some rebuilt) :
      SupportPayloadsFromProgram program rebuilt := by
    cases term with
    | leaf leaf =>
        simp [reconstructExplicitTerm] at found
        subst rebuilt
        exact authored
    | rule ruleId positionalTheta premises shallowDischarges holes assurance =>
        have assuranceSafe : SupportPayloadsFromProgram program
            (.rule ruleId positionalTheta .nil .nil holes assurance) := by
          constructor
          · intro name member
            exact authored.1 (by
              cases premises <;>
                simp_all [supportTermBinderSpellings,
                  supportTermsBinderSpellings,
                  supportDischargesBinderSpellings])
          · intro name member
            exact authored.2 (by
              cases premises <;>
                simp_all [supportTermOpaqueCertPremiseSpellings,
                  supportTermsOpaqueCertPremiseSpellings,
                  dischargeOpaqueCertPremiseSpellings])
        have premisesAuthored :
            supportTermsBinderSpellings premises ⊆
                programBinderSpellings program ∧
              supportTermsOpaqueCertPremiseSpellings premises ⊆
                programOpaqueCertPremiseSpellings program := by
          constructor
          · intro name member
            exact authored.1 (by
              simp only [supportTermBinderSpellings, List.mem_append]
              exact Or.inl (Or.inr member))
          · intro name member
            exact authored.2 (by
              simp only [supportTermOpaqueCertPremiseSpellings,
                List.mem_append]
              exact Or.inl (Or.inr member))
        have dischargesAuthored :
            supportDischargesBinderSpellings shallowDischarges ⊆
                programBinderSpellings program ∧
              dischargeOpaqueCertPremiseSpellings shallowDischarges ⊆
                programOpaqueCertPremiseSpellings program := by
          constructor
          · intro name member
            exact authored.1 (by
              simp only [supportTermBinderSpellings, List.mem_append]
              exact Or.inr member)
          · intro name member
            exact authored.2 (by
              simp only [supportTermOpaqueCertPremiseSpellings,
                List.mem_append]
              exact Or.inr member)
        cases premises with
        | nil =>
            cases ruleFound : ruleById policy ruleId with
            | none =>
                simp [reconstructExplicitTerm, ruleFound] at found
            | some rule =>
                cases lengthCheck :
                    positionalTheta.length != rule.params.length with
                | true =>
                    simp [reconstructExplicitTerm, ruleFound] at found
                    simp_all
                | false =>
                    cases premiseFound :
                        resolveImplicitPremises canon program priors
                          (rule.params.zip (positionalTheta.map Prod.snd))
                          rule.premises with
                    | none =>
                        simp [reconstructExplicitTerm, ruleFound, lengthCheck,
                          premiseFound] at found
                    | some loweredPremises =>
                        cases dischargeFound :
                            reconstructExplicitDischarges canon program policy
                              priors shallowDischarges with
                        | none =>
                            simp [reconstructExplicitTerm, ruleFound,
                              lengthCheck, premiseFound, dischargeFound] at found
                        | some loweredDischarges =>
                            simp [reconstructExplicitTerm, ruleFound,
                              lengthCheck, premiseFound, dischargeFound] at found
                            rcases found with ⟨_, found⟩
                            subst rebuilt
                            have premiseSafe :=
                              resolveImplicitPremises_payloads safe premiseFound
                            have dischargeSafe :=
                              reconstructExplicitDischarges_payloads safe
                                dischargesAuthored dischargeFound
                            constructor
                            · intro name member
                              simp only [supportTermBinderSpellings,
                                List.mem_append] at member
                              rcases member with (member | member) | member
                              · exact assuranceSafe.1 (by
                                  simpa [SupportPayloadsFromProgram,
                                    supportTermBinderSpellings,
                                    supportTermsBinderSpellings,
                                    supportDischargesBinderSpellings] using member)
                              · exact premiseSafe.1 member
                              · exact dischargeSafe.1 member
                            · intro name member
                              simp only [supportTermOpaqueCertPremiseSpellings,
                                List.mem_append] at member
                              rcases member with (member | member) | member
                              · exact assuranceSafe.2 (by
                                  simpa [SupportPayloadsFromProgram,
                                    supportTermOpaqueCertPremiseSpellings,
                                    supportTermsOpaqueCertPremiseSpellings,
                                    dischargeOpaqueCertPremiseSpellings] using member)
                              · exact premiseSafe.2 member
                              · exact dischargeSafe.2 member
        | cons premise rest =>
            cases ruleFound : ruleById policy ruleId with
            | none =>
                simp [reconstructExplicitTerm, ruleFound] at found
            | some rule =>
                cases lengthCheck :
                    positionalTheta.length != rule.params.length with
                | true =>
                    simp [reconstructExplicitTerm, ruleFound] at found
                    simp_all
                | false =>
                    cases premiseFound :
                        reconstructExplicitTerms canon program policy priors
                          (.cons premise rest) with
                    | none =>
                        simp [reconstructExplicitTerm, ruleFound, lengthCheck,
                          premiseFound] at found
                    | some loweredPremises =>
                        cases dischargeFound :
                            reconstructExplicitDischarges canon program policy
                              priors shallowDischarges with
                        | none =>
                            simp [reconstructExplicitTerm, ruleFound,
                              lengthCheck, premiseFound, dischargeFound] at found
                        | some loweredDischarges =>
                            simp [reconstructExplicitTerm, ruleFound,
                              lengthCheck, premiseFound, dischargeFound] at found
                            rcases found with ⟨_, found⟩
                            subst rebuilt
                            have premiseSafe :=
                              reconstructExplicitTerms_payloads safe
                                premisesAuthored premiseFound
                            have dischargeSafe :=
                              reconstructExplicitDischarges_payloads safe
                                dischargesAuthored dischargeFound
                            constructor
                            · intro name member
                              simp only [supportTermBinderSpellings,
                                List.mem_append] at member
                              rcases member with (member | member) | member
                              · exact assuranceSafe.1 (by
                                  simpa [SupportPayloadsFromProgram,
                                    supportTermBinderSpellings,
                                    supportTermsBinderSpellings,
                                    supportDischargesBinderSpellings] using member)
                              · exact premiseSafe.1 member
                              · exact dischargeSafe.1 member
                            · intro name member
                              simp only [supportTermOpaqueCertPremiseSpellings,
                                List.mem_append] at member
                              rcases member with (member | member) | member
                              · exact assuranceSafe.2 (by
                                  simpa [SupportPayloadsFromProgram,
                                    supportTermOpaqueCertPremiseSpellings,
                                    supportTermsOpaqueCertPremiseSpellings,
                                    dischargeOpaqueCertPremiseSpellings] using member)
                              · exact premiseSafe.2 member
                              · exact dischargeSafe.2 member

  private theorem reconstructExplicitTerms_payloads
      (safe : PriorPayloadsFromProgram program priors)
      (authored :
        supportTermsBinderSpellings terms ⊆ programBinderSpellings program ∧
          supportTermsOpaqueCertPremiseSpellings terms ⊆
            programOpaqueCertPremiseSpellings program)
      (found : reconstructExplicitTerms canon program policy priors terms =
        some rebuilt) :
      supportTermsBinderSpellings rebuilt ⊆ programBinderSpellings program ∧
        supportTermsOpaqueCertPremiseSpellings rebuilt ⊆
          programOpaqueCertPremiseSpellings program := by
    cases terms with
    | nil =>
        simp [reconstructExplicitTerms] at found
        subst rebuilt
        simp [supportTermsBinderSpellings,
          supportTermsOpaqueCertPremiseSpellings]
    | cons term rest =>
        cases headFound :
            reconstructExplicitTerm canon program policy priors term with
        | none =>
            simp [reconstructExplicitTerms, headFound] at found
        | some head =>
            cases tailFound :
                reconstructExplicitTerms canon program policy priors rest with
            | none =>
                simp [reconstructExplicitTerms, headFound, tailFound] at found
            | some tail =>
                simp [reconstructExplicitTerms, headFound, tailFound] at found
                subst rebuilt
                have termAuthored : SupportPayloadsFromProgram program term := by
                  constructor
                  · intro name member
                    exact authored.1 (by
                      simp only [supportTermsBinderSpellings,
                        List.mem_append]
                      exact Or.inl member)
                  · intro name member
                    exact authored.2 (by
                      simp only [supportTermsOpaqueCertPremiseSpellings,
                        List.mem_append]
                      exact Or.inl member)
                have restAuthored :
                    supportTermsBinderSpellings rest ⊆
                        programBinderSpellings program ∧
                      supportTermsOpaqueCertPremiseSpellings rest ⊆
                        programOpaqueCertPremiseSpellings program := by
                  constructor
                  · intro name member
                    exact authored.1 (by
                      simp only [supportTermsBinderSpellings,
                        List.mem_append]
                      exact Or.inr member)
                  · intro name member
                    exact authored.2 (by
                      simp only [supportTermsOpaqueCertPremiseSpellings,
                        List.mem_append]
                      exact Or.inr member)
                have headSafe :=
                  reconstructExplicitTerm_payloads safe termAuthored headFound
                have tailSafe :=
                  reconstructExplicitTerms_payloads safe restAuthored tailFound
                constructor
                · intro name member
                  simp only [supportTermsBinderSpellings,
                    List.mem_append] at member
                  rcases member with member | member
                  · exact headSafe.1 member
                  · exact tailSafe.1 member
                · intro name member
                  simp only [supportTermsOpaqueCertPremiseSpellings,
                    List.mem_append] at member
                  rcases member with member | member
                  · exact headSafe.2 member
                  · exact tailSafe.2 member

  private theorem reconstructExplicitDischarges_payloads
      (safe : PriorPayloadsFromProgram program priors)
      (authored :
        supportDischargesBinderSpellings discharges ⊆
            programBinderSpellings program ∧
          dischargeOpaqueCertPremiseSpellings discharges ⊆
            programOpaqueCertPremiseSpellings program)
      (found : reconstructExplicitDischarges canon program policy priors
        discharges = some rebuilt) :
      supportDischargesBinderSpellings rebuilt ⊆
          programBinderSpellings program ∧
        dischargeOpaqueCertPremiseSpellings rebuilt ⊆
          programOpaqueCertPremiseSpellings program := by
    cases discharges with
    | nil =>
        simp [reconstructExplicitDischarges] at found
        subst rebuilt
        simp [supportDischargesBinderSpellings,
          dischargeOpaqueCertPremiseSpellings]
    | cons question term rest =>
        cases term with
        | rule ruleId subst premises nested holes assurance =>
            simp [reconstructExplicitDischarges] at found
        | leaf leaf =>
            cases headFound : resolveReference program priors ⟨leaf.val⟩ with
            | none =>
                simp [reconstructExplicitDischarges, headFound] at found
            | some head =>
                cases tailFound :
                    reconstructExplicitDischarges canon program policy priors
                      rest with
                | none =>
                    simp [reconstructExplicitDischarges, headFound, tailFound]
                      at found
                | some tail =>
                    simp [reconstructExplicitDischarges, headFound, tailFound]
                      at found
                    subst rebuilt
                    have headSafe :=
                      resolveReference_preserves_priorPayloads safe headFound
                    have restAuthored :
                        supportDischargesBinderSpellings rest ⊆
                            programBinderSpellings program ∧
                          dischargeOpaqueCertPremiseSpellings rest ⊆
                            programOpaqueCertPremiseSpellings program := by
                      constructor
                      · intro name member
                        exact authored.1 (by
                          simp only [supportDischargesBinderSpellings,
                            List.mem_append]
                          exact Or.inr member)
                      · intro name member
                        exact authored.2 (by
                          simp only [dischargeOpaqueCertPremiseSpellings,
                            List.mem_append]
                          exact Or.inr member)
                    have tailSafe :=
                      reconstructExplicitDischarges_payloads safe restAuthored
                        tailFound
                    constructor
                    · intro name member
                      simp only [supportDischargesBinderSpellings,
                        List.mem_append] at member
                      rcases member with member | member
                      · exact headSafe.1 member
                      · exact tailSafe.1 member
                    · intro name member
                      simp only [dischargeOpaqueCertPremiseSpellings,
                        List.mem_append] at member
                      rcases member with member | member
                      · exact headSafe.2 member
                      · exact tailSafe.2 member
end

private theorem reconstructArgument_preserves_priorPayloads
    (safe : PriorPayloadsFromProgram program priors)
    (member : Presentation.Decl.arg argument ∈ program.decls)
    (found : reconstructArgument canon program policy priors argument =
      some prior) :
    PriorPayloadsFromProgram program (priors ++ [prior]) := by
  cases instantiation : argument.instantiation with
  | inferTheta rule references discharges obligations assurance =>
      have buildFound : buildArgument program policy priors argument =
          some prior := by
        simpa [reconstructArgument, instantiation] using found
      exact buildArgument_preserves_priorPayloads safe member buildFound
  | explicitTheta term =>
      have authored := argumentPayloadsFromProgram member
      simp only [argBinderSpellings, instantiation,
        argOpaqueCertPremiseSpellings] at authored
      cases rebuiltFound :
          reconstructExplicitTerm canon program policy priors term with
      | none =>
          simp [reconstructArgument, instantiation, rebuiltFound] at found
      | some rebuilt =>
          cases conclusionFound : conclOfTerm program policy rebuilt with
          | none =>
              simp [reconstructArgument, instantiation, rebuiltFound,
                conclusionFound] at found
          | some conclusion =>
              simp [reconstructArgument, instantiation, rebuiltFound,
                conclusionFound] at found
              subst prior
              have rebuiltSafe :=
                reconstructExplicitTerm_payloads safe authored rebuiltFound
              exact priorPayloadsFromProgram_append_one safe
                ⟨argument.id, rebuilt, conclusion⟩ rebuiltSafe.1 rebuiltSafe.2

theorem reconstructArgs_rename
    (sound : RenamingSound ρg program policy)
    (envSound : EnvRenamingSound env ρg)
    (declarations : List Presentation.Decl) (priors : List PriorArgument)
    (contained : ∀ declaration ∈ declarations, declaration ∈ program.decls)
    (safe : PriorPayloadsFromProgram program priors) :
    reconstructArgs env (Binding.renameProgram ρg program)
        (Binding.renamePolicy ρg policy)
        (declarations.map (Binding.renameDecl ρg (programValues program)))
        (priors.map (renamePriorArgument ρg)) =
      renameExcept (renameReconstructFailure ρg)
        (List.map (renameReconstructedArgument ρg (programValues program)))
        (reconstructArgs env program policy declarations priors) := by
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
          simp only [List.map_cons, Binding.renameDecl, reconstructArgs]
          exact ih priors tailContained safe
      | claim claim =>
          simp only [List.map_cons, Binding.renameDecl, reconstructArgs]
          exact ih priors tailContained safe
      | attack attack =>
          simp only [List.map_cons, Binding.renameDecl, reconstructArgs]
          exact ih priors tailContained safe
      | status status =>
          simp only [List.map_cons, Binding.renameDecl, reconstructArgs]
          exact ih priors tailContained safe
      | group group =>
          simp only [List.map_cons, Binding.renameDecl, reconstructArgs]
          exact ih priors tailContained safe
      | comparison comparison =>
          simp [List.map_cons, Binding.renameDecl, Binding.renameComparison,
            reconstructArgs, renameExcept, renameReconstructFailure]
      | arg argument =>
          simp only [List.map_cons, Binding.renameDecl, reconstructArgs]
          rw [reconstructArgument_rename sound _ priors argument headMember]
          cases builtFound :
              reconstructArgument _ program policy priors argument with
          | none =>
              simp [Binding.renameArg, renameExcept, renameReconstructFailure,
                renameReconstructedArgument]
          | some built =>
              simp only [Option.map_some]
              have safeNext :=
                reconstructArgument_preserves_priorPayloads safe headMember
                  builtFound
              have builtSafe := safeNext built (by simp)
              rw [show (renamePriorArgument ρg built).term =
                renameResidualSupportTerm ρg built.term by rfl]
              rw [lowerToSupportTerm_rename sound envSound priors built.term
                builtSafe.1 builtSafe.2]
              cases loweredFound :
                  lowerToSupportTerm env program policy priors built.term with
              | none =>
                  simp [Binding.renameArg, renameExcept,
                    renameReconstructFailure, renameReconstructedArgument]
              | some core =>
                simp only [Option.map_some]
                rw [show (renamePriorArgument ρg built).conclusion =
                  renameResidualAtom ρg built.conclusion by rfl]
                simp only [Binding.renameArg]
                rw [checkAuthoredConclusion_rename sound argument.id
                  argument.concl built.conclusion]
                cases authoredFound : checkAuthoredConclusion _ program argument.id
                    argument.concl built.conclusion with
                | error failure =>
                    simp [authoredFound, renameExcept]
                | ok _ =>
                    simp only [Option.map_some]
                    have tailRename := ih (priors ++ [built]) tailContained safeNext
                    cases tailFound :
                        reconstructArgs env program policy rest
                          (priors ++ [built]) with
                    | error failure =>
                        have renamedTail :
                            reconstructArgs env (Binding.renameProgram ρg program)
                                (Binding.renamePolicy ρg policy)
                                (rest.map
                                  (Binding.renameDecl ρg (programValues program)))
                                (priors.map (renamePriorArgument ρg) ++
                                  [renamePriorArgument ρg built]) =
                              .error (renameReconstructFailure ρg failure) := by
                          simpa [List.map_append, tailFound, renameExcept] using
                            tailRename
                        rw [renamedTail]
                        simp [authoredFound, tailFound, renameExcept]
                    | ok tail =>
                        have renamedTail :
                            reconstructArgs env (Binding.renameProgram ρg program)
                                (Binding.renamePolicy ρg policy)
                                (rest.map
                                  (Binding.renameDecl ρg (programValues program)))
                                (priors.map (renamePriorArgument ρg) ++
                                  [renamePriorArgument ρg built]) =
                              .ok (tail.map
                                (renameReconstructedArgument ρg
                                  (programValues program))) := by
                          simpa [List.map_append, tailFound, renameExcept] using
                            tailRename
                        rw [renamedTail]
                        simp [authoredFound, tailFound, renameExcept,
                          renameReconstructedArgument, Binding.renameArg]





private theorem renameCoreQuestionId_injective
    (ρg : Binding.GlobalRenaming) :
    Function.Injective (renameCoreQuestionId ρg) := by
  rintro ⟨left⟩ ⟨right⟩ equal
  have outputEq :
      ρg.question (⟨left⟩ : Presentation.QuestionId) =
        ρg.question ⟨right⟩ := by
    cases leftMapped : ρg.question (⟨left⟩ : Presentation.QuestionId)
    cases rightMapped : ρg.question (⟨right⟩ : Presentation.QuestionId)
    simp_all [renameCoreQuestionId]
  have inputEq := ρg.question_injective outputEq
  cases inputEq
  rfl

private theorem renamedCoreRule_as_presentation
    (ρg : Binding.GlobalRenaming) (rule : Lara.Support.RuleId) :
    (⟨(renameCoreRuleId ρg rule).name⟩ :
        Presentation.RuleId) =
      ρg.rule ⟨rule.name⟩ := by
  cases rule with
  | mk name =>
      cases mapped : ρg.rule ⟨name⟩ with
      | mk target =>
          apply congrArg Presentation.RuleId.mk
          simpa [renameCoreRuleId, Binding.renameText, mapped] using
            (ρg.rule_coherent ⟨name⟩).symm

private theorem renamedCoreQuestion_as_support
    (ρg : Binding.GlobalRenaming)
    (question : Presentation.QuestionId) :
    toSupportQuestionId (ρg.question question) =
      renameCoreQuestionId ρg (toSupportQuestionId question) := by
  cases question with
  | mk name =>
      cases mapped : ρg.question ⟨name⟩ with
      | mk target =>
          apply congrArg Support.QuestionId.mk
          simpa [toSupportQuestionId, renameCoreQuestionId,
            Binding.renameText, mapped] using
            ρg.question_coherent ⟨name⟩

private theorem findArgTerm_rename
    (ρg : Binding.GlobalRenaming)
    (arguments : List
      (Presentation.ArgId × Lara.Support.SupportTerm))
    (id : Presentation.ArgId) :
    findArgTerm
        (arguments.map fun entry =>
          (ρg.arg entry.1, renameCoreSupportTerm ρg entry.2))
        (ρg.arg id) =
      (findArgTerm arguments id).map (renameCoreSupportTerm ρg) := by
  induction arguments with
  | nil => rfl
  | cons entry rest ih =>
      unfold findArgTerm at ih ⊢
      simp only [List.map_cons, List.find?_cons]
      by_cases equal : entry.1 = id
      · have renamedEqual : ρg.arg entry.1 = ρg.arg id :=
          congrArg ρg.arg equal
        simp [renamedEqual, equal]
      · have renamedNe : ρg.arg entry.1 ≠ ρg.arg id :=
          fun h => equal (ρg.arg_injective h)
        simpa [renamedNe, equal, Function.comp_def] using ih

private theorem lookupDis_rename
    (ρg : Binding.GlobalRenaming)
    (discharges :
      List (Lara.Support.QuestionId × Lara.Support.SupportTerm))
    (question : Lara.Support.QuestionId) :
    Lara.Attack.lookupDis
        (discharges.map fun entry =>
          (renameCoreQuestionId ρg entry.1,
            renameCoreSupportTerm ρg entry.2))
        (renameCoreQuestionId ρg question) =
      (Lara.Attack.lookupDis discharges question).map
        (renameCoreSupportTerm ρg) := by
  induction discharges with
  | nil => rfl
  | cons entry rest ih =>
      simp only [Lara.Attack.lookupDis, List.findSome?_cons, List.map_cons]
      by_cases equal : entry.1 = question
      · have renamedEqual :
            renameCoreQuestionId ρg entry.1 =
              renameCoreQuestionId ρg question :=
          congrArg (renameCoreQuestionId ρg) equal
        simp [renamedEqual, equal]
      · have renamedNe :
            renameCoreQuestionId ρg entry.1 ≠
              renameCoreQuestionId ρg question :=
          fun h => equal (renameCoreQuestionId_injective ρg h)
        simp [renamedNe, equal, ih]

theorem resolvePathCore_rename
    (sound : RenamingSound ρg program policy)
    (term : Lara.Support.SupportTerm)
    (path : List Presentation.SurfaceStep) :
    resolvePathCore (Binding.renamePolicy ρg policy)
        (renameCoreSupportTerm ρg term)
        (path.map (Binding.renameSurfaceStep ρg)) =
      (resolvePathCore policy term path).map (renameCorePos ρg) := by
  induction path generalizing term with
  | nil => rfl
  | cons step rest ih =>
      cases step with
      | index index =>
          cases term with
          | leaf leaf =>
              simp [List.map_cons, Binding.renameSurfaceStep,
                renameCoreSupportTerm, resolvePathCore]
          | inst rule subst premises discharges holes assurance =>
              simp only [List.map_cons, Binding.renameSurfaceStep,
                renameCoreSupportTerm, renameCoreSupportTerms_eq_map,
                renameCoreSupportDischarges_eq_map, resolvePathCore]
              by_cases negative : index < 0
              · simp [negative]
              · simp only [if_neg negative, List.getElem?_map,
                  Option.map_eq_some_iff]
                cases found : premises[index.toNat]? with
                | none => rfl
                | some next =>
                    simp only [Option.map_some]
                    rw [ih next]
                    cases resolvePathCore policy next rest <;>
                      simp [renameCorePos]
      | name name =>
          cases term with
          | leaf leaf =>
              simp [List.map_cons, Binding.renameSurfaceStep,
                renameCoreSupportTerm, resolvePathCore]
          | inst ruleId subst premises discharges holes assurance =>
              simp only [List.map_cons, Binding.renameSurfaceStep,
                renameCoreSupportTerm, renameCoreSupportTerms_eq_map,
                renameCoreSupportDischarges_eq_map, resolvePathCore]
              rw [renamedCoreRule_as_presentation, ruleById_rename]
              cases found : ruleById policy ⟨ruleId.name⟩ with
              | none => rfl
              | some rule =>
                  simp only [Option.map_some]
                  rw [labelIndex?_rename]
                  cases label : labelIndex? rule name with
                  | some index =>
                      simp only [List.getElem?_map]
                      cases child : premises[index]? with
                      | none => rfl
                      | some next =>
                          simp only [Option.map_some]
                          rw [ih next]
                          cases resolvePathCore policy next rest <;>
                            simp [renameCorePos]
                  | none =>
                      simp only [questionIds_renameRule]
                      rw [questionByName?_rename]
                      cases questionFound :
                          (questionIds rule).find?
                            (fun q => q.val == name) with
                      | none => rfl
                      | some question =>
                          simp only [Option.map_some]
                          rw [renamedCoreQuestion_as_support, lookupDis_rename]
                          cases discharge :
                              Lara.Attack.lookupDis discharges
                                (toSupportQuestionId question) with
                          | none => rfl
                          | some next =>
                              simp only [Option.map_some]
                              rw [ih next]
                              cases resolvePathCore policy next rest <;>
                                simp [renameCorePos, renameCoreQuestionId,
                                  toSupportQuestionId, Binding.renameText]

private theorem resolveSurfaceAttack_rename
    (sound : RenamingSound ρg program policy)
    (arguments : List
      (Presentation.ArgId × Lara.Support.SupportTerm))
    (attack : Presentation.SurfaceAttack) :
    resolveSurfaceAttack (Binding.renamePolicy ρg policy)
        (arguments.map fun entry =>
          (ρg.arg entry.1, renameCoreSupportTerm ρg entry.2))
        (Binding.renameSurfaceAttack ρg attack) =
      (resolveSurfaceAttack policy arguments attack).map
        (renameCoreAttack ρg) := by
  cases attack with
  | rebut source target =>
      simp only [Binding.renameSurfaceAttack, resolveSurfaceAttack]
      rw [findArgTerm_rename, findArgTerm_rename]
      cases findArgTerm arguments source <;>
        cases findArgTerm arguments target <;>
        rfl
  | undercut source target path =>
      simp only [Binding.renameSurfaceAttack, resolveSurfaceAttack]
      rw [findArgTerm_rename, findArgTerm_rename]
      cases sourceFound : findArgTerm arguments source with
      | none => rfl
      | some sourceTerm =>
          cases targetFound : findArgTerm arguments target with
          | none => rfl
          | some targetTerm =>
              simp
              rw [resolvePathCore_rename sound]
              cases resolvePathCore policy targetTerm path <;>
                rfl
  | undermine source target path =>
      simp only [Binding.renameSurfaceAttack, resolveSurfaceAttack]
      rw [findArgTerm_rename, findArgTerm_rename]
      cases sourceFound : findArgTerm arguments source with
      | none => rfl
      | some sourceTerm =>
          cases targetFound : findArgTerm arguments target with
          | none => rfl
          | some targetTerm =>
              simp
              rw [resolvePathCore_rename sound]
              cases resolvePathCore policy targetTerm path <;>
                rfl

theorem resolveSurfaceAttacks_rename
    (sound : RenamingSound ρg program policy)
    (arguments : List
      (Presentation.ArgId × Lara.Support.SupportTerm))
    (attacks : List Presentation.SurfaceAttack) :
    resolveSurfaceAttacks (Binding.renamePolicy ρg policy)
        (arguments.map fun entry =>
          (ρg.arg entry.1, renameCoreSupportTerm ρg entry.2))
        (attacks.map (Binding.renameSurfaceAttack ρg)) =
      renameExcept
        (fun failure => (ρg.arg failure.1, ρg.arg failure.2))
        (List.map (renameCoreAttack ρg))
        (resolveSurfaceAttacks policy arguments attacks) := by
  induction attacks with
  | nil => rfl
  | cons attack rest ih =>
      simp only [List.map_cons, resolveSurfaceAttacks]
      rw [resolveSurfaceAttack_rename sound]
      cases resolveSurfaceAttack policy arguments attack with
      | none =>
          cases attack <;>
            rfl
      | some resolved =>
          simp only [Option.map_some]
          rw [ih]
          cases resolveSurfaceAttacks policy arguments rest <;>
            rfl

end Renaming

end Lara.Surface
