# lara-syntax@0.5 Plain-Argument Theta Inference Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use `subagent-driven-development` (recommended) or `executing-plans` to implement this plan task-by-task. Use `test-driven-development` for every behavior change and `verification-before-completion` before reporting completion. Track each checkbox as work proceeds.

**Goal:** Let an ordinary `.lara` argument name the leaves or prior arguments that instantiate a rule, derive the rule's complete ground substitution theta by one-way matching, and lower to the same `lara-core@0.2` support term and bytes as the existing explicit positional-theta form.

**Architecture:** Add one presentation-only `ArgInstantiation` payload to `Arg`: existing arguments retain `ExplicitTheta SupportTerm`, while `InferTheta` carries the rule id, premise references, shallow discharge references, open-obligation ids, and assurance. The parser accepts `by rule from [ref, ...]`; the elaborator resolves each reference to a declared leaf or prior argument, folds the existing `Lara.Elaborate.Subst.matchAPat` over the corresponding rule premise, orders the resulting theta by `ruleParams`, and constructs the unchanged semantic `SRule`. Mirror the widened presentation shape and private structured codec in Lean. Do not change `SupportTerm`, `Unit`, `.core.sexp`, checking, replay, strict backends, or frozen measurements.

**Tech stack:** Haskell/GHC 9.6+, QuickCheck, Lean 4.32.0/Lake, the existing `Lara.Syntax`, `Lara.Elaborate.Subst`, `Lara.Elaborate.Internal`, `Lara.Presentation`, `AxCheck`, presentation-parity tooling, worked-example generators, and differential/replay gates.

---

## 1. Background

PR #103 merged as `039c1d6` and completed `lara-syntax@0.4`: ordered typed value bindings, one-pass prose interpolation, strict-Sigma validation, synchronized Haskell/Lean presentation models, and a 70-row cross-language shape guard. Issues #88, #90, and #91 are closed. Their two residual concerns are now independent:

- #104 — plain-`arg` theta inference, covered by this plan;
- #105 — named certificate premise slots, blocked on an opaque-certificate layering decision and explicitly outside this plan.

The existing `.lara` argument form supplies the full ground theta positionally:

```lara
arg a1 : supports(c1) by controlled_experiment(M, accuracy, D, exp_3)
  discharge randomization     with e2
  discharge adequate_power    with e3
  discharge external_validity with e6
```

`Lara.Syntax.supportTermP` records those terms as a shallow `SRule`; `Lara.Elaborate.Internal.elabTerm` looks up the policy rule, associates the positional values with `ruleParams`, and then reconstructs each premise by global unique equivalence matching.

The repository already contains the inverse operation needed here. `Lara.Elaborate.Subst.matchAPat` one-way matches a policy `AtomPat` against a ground `Prop`, extends a substitution, and distinguishes a shape mismatch from a repeated-parameter conflict under the same normalized term equality used elsewhere. `Lara.Elaborate.Comparison` uses it to derive theta for generated comparison arguments. Plain arguments should reuse that implementation rather than maintain a second matcher.

---

## 2. Motivation

The positional form makes an author copy values already present in a premise leaf and know the policy's parameter order. In Example A, the single premise

```lara
leaf e1 : reports(exp_3, effect(M, accuracy, D, positive))
```

already determines all four parameters of `controlled_experiment(M, Q, D, Exp)`. Repeating `M, accuracy, D, exp_3` in the argument adds no evidence and no proof obligation; it adds a transcription surface.

The proposed form is:

```lara
arg a1 : supports(c1) by controlled_experiment from [e1]
  discharge randomization     with e2
  discharge adequate_power    with e3
  discharge external_validity with e6
```

The reference list does two jobs with one checked source of truth:

1. it names the exact support term used for each policy premise;
2. its ground conclusion derives theta by matching the corresponding premise pattern.

This improves diagnostics. A copied value that drifts currently tends to fail later as `UnresolvedPremise`, naming a generated ground proposition. The inferred form can instead name the authored reference, the rule premise position, and either the shape mismatch or conflicting parameter binding.

### Applicability (measured 2026-08-12)

The value claim is not carried by the two migrated witnesses alone:

- 54 of the 55 rules declared across `corpus-units/corpus-v1.policy.lara` and
  the `examples/*` policies are **single-premise**; exactly one rule declares two
  premises;
- 52 rule-backed arguments exist today (39 across `examples/*/example.lara`, 13
  across `corpus-units/*/*/unit.lara`) and are candidate call sites;
- the dominant corpus rule `controlled_comparison(S, B, Q, D, Exp)` binds all
  five parameters from its single premise
  `reports(Exp, compares(S, B, Q, D, favorable))` — the exact transcription this
  feature removes.

The residual caveat is honest: for a multi-premise rule the author must supply
references in exact premise order, which relocates rather than removes
positional knowledge. At one such rule in 55, that trade is worth taking, and
D6's per-position diagnostics name the premise index when the order is wrong.

The feature removes author transcription only. It does not infer evidence, search over leaves, choose among matches, alter the rule, or weaken checker validation.

---

## 3. Scope and Non-goals

### In scope

- `lara-syntax@0.5`, additive over `@0.4`.
- The concrete form `by ruleId from [argRef, ...]` for ordinary rule-backed `arg` declarations.
- References to declared leaves and prior arguments.
- Exact rule-premise-order alignment: one authored reference per policy premise.
- One-way theta derivation through the existing normalized matcher.
- Dedicated fail-closed diagnostics for malformed or impossible inference.
- Preservation of the existing positional form `by ruleId(term, ...)`.
- Haskell/Lean presentation parity and structured-codec round trips.
- Migration of Example A and S1 as defeasible/discharged and strict/certified witnesses.

### Explicit non-goals

- Named certificate slots or rewriting any opaque `Cert` payload; see #105.
- Inferring theta from the announced claim conclusion, discharge answers, attacks, or arbitrary declarations.
- Searching the declaration environment for a premise. The author supplies every premise reference.
- Reordering references to find a successful match, backtracking, best-match selection, or ambiguity resolution by preference.
- Partial theta with explicit overrides, mixed positional terms plus named references, optional references, wildcards, or recursive inference.
- Forward argument references.
- Changing discharge syntax or the existing open-hole representation.
- Migrating `corpus-units/` or changing generated core, expected JSON, manifests, bundles, measurements, or freeze tags.
- Any change to `SupportTerm`, `Unit`, `Lara.Wire`, `checkUnit`, replay identity, strict backend semantics, or Lean checker proofs.

---

## 4. Decisions Locked by This Plan

### D1. Concrete grammar and canonical spelling

Add one alternative to the ordinary argument head:

```text
argHead ::= "leaf" "(" leafId ")"
          | ruleId "(" termList? ")"
          | ruleId "from" "[" argRefList? "]"

argRefList ::= argRef ("," argRef)*
argRef     ::= ident
```

Canonical examples:

```lara
arg a1 : supports(c1) by controlled_experiment from [e1]
arg a2 : supports(c2) by bridge_rule from [a1, e_binding]
arg a3 : supports(c3) by zero_premise_rule from []
```

`from []` carries no expressive power over `r()`: a zero-premise rule with
parameters can never bind them from premises (it fails `ThetaParameterUnbound`),
and a zero-premise, zero-parameter rule has nothing to transcribe. It stays
legal so the list production, printer, and generator remain total, with both
degenerate outcomes pinned by test rather than by a parser carve-out.

`from` is contextual after a rule identifier. It is added to the documented `@0.5` vocabulary and the `SyntaxSpec` generator's reserved list so generated identifiers do not collide with the grammar, but the lexer remains unchanged.

Reference order is policy premise order. The first source reference instantiates `rulePremises[0]`, the second instantiates `rulePremises[1]`, and so on. Source diagnostics report these positions as 1-based; semantic support-term positions remain 0-based as before.

The existing spellings remain unchanged:

```lara
arg a1 : supports(c1) by controlled_experiment(M, accuracy, D, exp_3)
arg d1 : challenges(e4) by leaf(e5)
```

The printer emits exactly one of the two rule forms from the recorded `ArgInstantiation`. It never reconstructs an inferred source from a semantic theta and never prints an inferred source as positional.

### D2. Presentation AST: state-safe instantiation payload, unchanged semantic term

Add to `src/Lara/AST.hs`:

```haskell
newtype ArgRef = ArgRef String
  deriving (Eq, Ord, Show)

type ArgDischarge = [(QuestionId, ArgRef)]

data ArgInstantiation
  = ExplicitTheta SupportTerm
  | InferTheta RuleId [ArgRef] ArgDischarge [ObligationId] Assurance
  deriving (Eq, Show)

data Arg = Arg
  { argId :: ArgId
  , argConcl :: ArgConcl
  , argInstantiation :: ArgInstantiation
  }
  deriving (Eq, Show)
```

`ArgRef` is a presentation token because a bare reference cannot be classified
as `LeafId` or `ArgId` until declaration scope is available. Do not use
`String`, `LeafId`, or `ArgId` for the field. `ArgDischarge` keeps the same
source-level namespace discipline for shallow discharge targets.

`ExplicitTheta` carries the complete authored `SupportTerm`, including
comparison-generated nested premises. `InferTheta` carries its complete
presentation payload: the rule id, premise references, shallow discharge
references, open-obligation ids, and assurance. The elaborator resolves this
payload to the semantic `SRule`; the semantic `SupportTerm` type itself does
not gain a presentation-only constructor.

Keeping the support carrier inside the `ArgInstantiation` sum makes invalid
pairings unrepresentable: an inferred argument cannot be paired with a leaf,
positional substitutions, or pre-populated premises. The parser constructs
consistent payloads, while a hand-built invalid pairing cannot typecheck and
there is no malformed-carrier printer or elaborator fallback.

Before modifying exported `Arg`, run HLS references from the current
implementation checkout and migrate every constructor. Current verified
concentrations include `Lara.Syntax`, `Lara.Elaborate.Comparison`,
`Lara.Examples`, `Lara.ClaimSupport`, `SyntaxSpec`, `ElaborateSpec`,
`AdmissionSpec`, `ClaimSupportSpec`, `ValueBindingsSpec`,
`scripts/presentation-shape.hs`, and the Lean presentation mirror.
### D3. Reference resolution is exact and scope-ordered

For `InferTheta refs`, process arguments in existing declaration order. At argument `a`, one `ArgRef name` resolves as follows:

1. if exactly one declared leaf has `LeafId name`, select `SLeaf` and its proposition from `envGamma`;
2. if exactly one already-elaborated prior argument has `ArgId name`, select its complete `SupportTerm` and derive its proposition with `conclOf`;
3. if both namespaces contain `name`, reject it as ambiguous;
4. if neither contains `name`, reject it as unresolved; a later argument is not a prior argument and receives this same deterministic failure;
5. if an in-memory environment contains duplicate matching leaf ids, fail before inference at the existing source-boundary duplicate-leaf guard; duplicate argument ids already fail before lowering.

Do not fall back to global equivalence search. The source reference selects the support term; equivalence is used only inside `matchAPat` to compare repeated parameter bindings.

The resolver returns both values together so the selected semantic premise and the proposition used to derive theta cannot drift:

```haskell
data ResolvedArgRef = ResolvedArgRef
  { resolvedRefTerm :: SupportTerm
  , resolvedRefProp :: Prop
  }
```

Keep `ResolvedArgRef` private to `Lara.Elaborate.Internal`; it is not an AST or public API type.

### D4. Theta derivation is one pass in rule-premise order

Inference for argument `aid`, rule `rule`, and `refs` runs in this order:

```haskell
when (length refs /= length (rulePremises rule))
  (Left (ThetaReferenceCountMismatch aid (ruleId rule)
          (length (rulePremises rule)) (length refs)))

resolved <- mapM (resolveArgRef env priors aid (ruleId rule)) refs

theta0 <- foldM matchOne []
  (zip3 [1 :: Int ..] refs (zip (rulePremises rule) resolved))

mapM_ (requireThetaParameter aid (ruleId rule) theta0) (ruleParams rule)

let theta =
      [ (param, term)
      | param <- ruleParams rule
      , Just term <- [lookup param theta0]
      ]
    premises = map resolvedRefTerm resolved
```

`matchOne` delegates directly to `matchAPat`:

- `MatchShape` becomes a premise-position/reference-located shape error;
- `MatchConflict param old new` becomes a premise-position/reference-located theta conflict;
- success extends the same substitution used for subsequent premises.

After all matches, every `ruleParam` must be present. A parameter that occurs only in the conclusion, a critical question, or nowhere in the cited premises produces `ThetaParameterUnbound`; the elaborator never guesses it from the announced claim or discharge lines.

Reorder the final theta by `ruleParams`, not matcher discovery order. This is the byte-stability requirement: the inferred `SRule.srSubst` must be byte-identical to the explicit form's positional association.

The byte-equality contract is ordered *and* spelling-conditional. Inferred theta
adopts each term's spelling from the cited premise's ground `Prop`; explicit
theta adopts the author's typed spelling. `matchAPat` compares with `sameTerm`,
but the wire encoder does not normalize numeric spellings, so:

- when the explicit source spells every parameter exactly as the cited premises
  do, explicit and inferred lower to byte-identical units — this is the invariant
  the paired fixtures and the A/S1 witnesses pin;
- when the spellings differ but are `sameTerm`-equal (`0.710` typed against a
  leaf spelling `0.71`), the two forms lower to checker-equivalent units with
  identical verdicts that may differ in bytes.

State the condition wherever the invariant is documented. An unconditional
byte-identity claim is false and must not enter the grammar appendix.

Construct the semantic term directly:

```haskell
SRule (ruleId rule) theta premises discharges holes assurance
```

The selected premises are used exactly as named, including a complete prior argument term. Do not call `resolvePremises` on the inferred path; doing so would throw away the source's selection and reintroduce global ambiguity.

### D5. Explicit theta behavior is frozen

`ExplicitTheta` continues through the current path without semantic changes:

1. check positional arity against `ruleParams`;
2. associate supplied terms with parameters in rule order;
3. use pre-populated generated premises when present;
4. otherwise reconstruct implicit premises by the existing unique `equiv` search;
5. resolve discharges and preserve holes/assurance.

Do not route explicit arguments through the new named-reference matcher. The two forms must meet only at their resulting complete `SRule`, which is compared byte-for-byte in tests.

Comparison-generated `Arg`s use `ExplicitTheta`. The comparison pass already derives theta and exact nested premises under stricter scheme-specific checks; re-inferring them would duplicate logic and could change its dedicated diagnostics.

### D6. Dedicated fail-closed diagnostics

Add these constructors to `Lara.Elaborate.Error` with stable author-facing renderings:

```haskell
ThetaReferenceCountMismatch ArgId RuleId Int Int
ThetaReferenceUnresolved ArgId RuleId Int ArgRef
ThetaReferenceAmbiguous ArgId RuleId Int ArgRef
ThetaReferenceShapeMismatch ArgId RuleId Int ArgRef Prop
ThetaReferenceConflict ArgId RuleId Int ArgRef Param Term Term
ThetaReferenceConclUnderivable ArgId RuleId Int ArgRef
ThetaParameterUnbound ArgId RuleId Param
```

`ThetaReferenceConclUnderivable` covers a reference that resolves to a prior
argument whose conclusion `conclOf` cannot derive. This is reachable today: an
argument backed by an undeclared leaf survives elaboration (`elabTerm` passes
`SLeaf` through for `checkUnit` R1, and `validateConcl` accepts the unknown
conclusion), so a later inferred argument can cite it. The resolver must fail
with this dedicated diagnostic — never a partial-function crash and never the
unresolved-name message, because the name did resolve.

Required message content:

- argument id and rule id for every rule-backed failure;
- 1-based policy premise number for every reference failure;
- exact source `ArgRef` spelling;
- selected proposition for a shape mismatch;
- parameter plus old/new terms for a conflict;
- the unbound policy parameter for incomplete theta;
- “declared leaf or prior argument” for unresolved scope;
- both namespaces for an ambiguous same-spelling reference;
- the cited prior argument id and “conclusion underivable” for a resolved
  reference whose proposition cannot be derived.

Error ordering is deterministic:

1. unknown rule;
2. reference-count mismatch;
3. references resolved left to right, including the underivable-conclusion
   check at resolution time;
4. patterns matched left to right;
5. unbound parameters checked in `ruleParams` order;
6. inferred discharge and announced-conclusion validation.

This ordering prevents an unrelated later discharge or claim mismatch from
hiding the source-level inference defect.

### D7. Value bindings and secondary consumers remain exact

`Lara.Elaborate.ValueBinding` substitutes `Term` fields inside an
`ExplicitTheta` support payload. `InferTheta` contains identifiers and
metadata, not rewriteable `Term` references, so value substitution must not
enter or rename its `ArgRef` values. An inferred argument sees the already-
substituted leaf/claim declarations because value expansion still precedes
argument lowering.

The semantic `Program` returned by `elaborateWithSemanticProgram` retains the
authored `ArgInstantiation` for printing and audits. Consumers that need actual
dependency leaves must use the elaborated `Unit` argument term, not infer
dependencies from the authored payload:

- `Lara.ClaimSupport.strictAuditSubject` already roots refs in the checked term;
- typed-attack audit refs and dead-end-source detection use
  `surfaceDerivedArgTermById` rather than the shallow authored payload.

This consumer change is intentionally **not** inferred-only. An authored
explicit rule-backed payload has an empty shallow premise list, and an inferred
payload has only named references, so reading the elaborated term widens audit
refs to the full resolved premise tree for both forms. That is the correct
reading — the surface payload under-reports real dependencies — but it is a
behavior change to existing programs and must be documented as one, not
presented as inference plumbing.

Verified blast radius at plan time: every `corpus-units/` attack source is
`by leaf(...)` (no rule-backed challenge sources, no rebut declarations), and
examples A and S1 commit no claim-support or binding-audit artifacts, so no
frozen bytes move. Re-verify rather than assume if the corpus gains a
rule-backed attack source before this lands.

- preserve `printArg surfaceArg` for the authored formal object, so reports show
  `from [e1]` rather than reverse-engineered positional terms.

Add a claim-support regression containing an inferred attack source. It must
render the inferred source form while deriving trace refs from the complete
elaborated term.

### D8. Lean result-12 and shape parity move together

Mirror the state-safe D2 payload in `lean/Lara/Presentation.lean`:

```lean
structure ArgRef where
  mk :: (val : String)
  deriving DecidableEq

abbrev ArgDischarge := List (QuestionId × ArgRef)

inductive ArgInstantiation where
  | explicitTheta (term : SupportTerm)
  | inferTheta (rule : RuleId) (refs : List ArgRef)
      (discharge : ArgDischarge) (obligations : List ObligationId)
      (assurance : Assurance)
  deriving DecidableEq

structure Arg where
  id : ArgId
  concl : ArgConcl
  instantiation : ArgInstantiation
  deriving DecidableEq
```

Add:

- `ArgRef` string codec and round-trip theorem;
- `ArgDischarge` alias witness and complete `ArgInstantiation` codec and
  round-trip theorem;
- widened `Arg` codec and updated `un_sxArg` proof;
- all new round-trip theorem audits in `lean/AxCheck.lean`.

Update both parity witnesses with exact constructor signatures, exhaustive
eliminators, and normalized shape rows. The inventory grows from 70 to 73
rows:

1. `ArgRef` — one-field structure;
2. `ArgDischarge` — one-part `(QuestionId, ArgRef)` list alias;
3. `ArgInstantiation` — the explicit and complete inferred payload arms.

The existing `Arg` row remains in place with its three fields; only the field
type changes from a separate shallow `SupportTerm` to the state-safe
`ArgInstantiation` payload. Keep `SupportTerm` unchanged. Any implementation
that changes its row, constructor inventory, or Lean semantic mirror has
crossed the checker-boundary non-goal and must stop.


### D9. Witness migrations are narrow and byte-neutral

After all feature and parity tests pass, migrate only these authored arguments:

- `examples/A/example.lara`
  - `a1`: `controlled_experiment from [e1]`;
  - `d3`: `null_result from [e7]`;
- `examples/S1/example.lara`
  - `a1`: `certified_citation from [e1]` while preserving the `nd@1` certificate verbatim.

These cover:

- defeasible inference with mandatory discharge lines;
- repeated-parameter consistency derived from one nested premise;
- strict inference with an opaque certificate;
- attack paths targeting the inferred arguments;
- no corpus or frozen-measurement migration.

The generated `.core.sexp`, expected JSON, report bytes, and exit codes for A and S1 must remain unchanged. If any move, stop and diagnose; no semantic change is legitimate for this feature.

### D10. Version and documentation contract

Update active presentation documentation to `lara-syntax@0.5` while retaining historical `@0.3` comparison and `@0.4` value-binding appendices as historical contracts. Add a new grammar appendix that specifies D1-D7, exact error ordering, and the explicit-vs-inferred byte-equality invariant with its spelling condition stated (D4).

Update:

- `docs/lara-surface-grammar.md`;
- `docs/spec.md` presentation-version pointer only; `lara-core@0.2` stays fixed;
- `README.md` authoring example/version references;
- `docs/mechanization-plan.md`, `lean/README.md`, and `lean/Lara.lean` result-12 scope/count;
- current-surface headers in Haskell/Lean presentation modules and tests;
- `TODOS.md`: mark #104 complete only after verification; keep #105 open and separate.

Mechanization claims, backlog completion, and ARA trace records are updated only after the complete verification matrix is green.

---

## 5. Implementation

### Task 1: Add red source and semantic-contract tests

**Files**

- Create: `test/ThetaInferenceSpec.hs`
- Modify: `test/Spec.hs`
- Modify: `lara.cabal`

**Interfaces**

- Consumes: current `parseProgram`, `parsePolicy`, `elaborate`, `encodeUnit`.
- Produces: `thetaInferenceSpecProps :: [(String, IO Result)]` and paired explicit/inferred fixtures used by later tasks.

- [ ] Define one small strict policy with:
  - `source(X, V)` as a leaf-shaped premise;
  - `selected(X, V)` as the first rule conclusion;
  - a second rule consuming `selected(X, V)` so a prior argument reference is exercised;
  - a two-premise rule that repeats `X`, so normalized consistency and conflicts are observable;
  - one parameter present only in a conclusion, so unbound-parameter rejection is observable.
- [ ] Define `explicitSource`, `inferredLeafSource`, and `inferredPriorArgSource`. The inferred forms use exactly `by select from [e1]` and `by promote from [a1]`.
- [ ] Add `prop_parserAcceptsInference` expecting `parseProgram inferredLeafSource` to succeed and `printProgram` to preserve `from [e1]`.
- [ ] Register the property group and run:

```bash
cabal test lara-test --test-show-details=direct
```

Expected RED: the parser rejects the new `from` token after a rule identifier.

- [ ] Add red semantic assertions that explicit and inferred leaf forms produce equal `Unit`, equal `encodeUnit`, and equal verdict JSON after checking.
- [ ] Add red prior-argument assertions that the inferred second rule embeds the complete earlier `SRule` as its selected premise, not an `SLeaf` placeholder.
- [ ] Add a parser/printer fixture for `from []` and for a comma-separated two-reference list.
- [ ] Keep all fixtures inline and policy-local; do not copy Example A or S1 into the test module.

### Task 2: Widen the Haskell presentation AST and concrete codec

**Files**

- Modify: `src/Lara/AST.hs`
- Modify: `src/Lara/Syntax.hs`
- Modify: `src/Lara/Elaborate/Comparison.hs`
- Modify: `src/Lara/Examples.hs`
- Modify: `src/Lara/ClaimSupport.hs`
- Modify: every HLS-reported `Arg` constructor in `test/`
- Modify: `test/SyntaxSpec.hs`
- Modify: `test/ThetaInferenceSpec.hs`

**Interfaces**

- Produces: `ArgRef`, `ArgDischarge`, complete `ArgInstantiation`, and the
  three-field `Arg` exactly as D2.
- Preserves: all `SupportTerm` constructors and existing explicit parser
  output; explicit support terms now travel inside `ExplicitTheta`.

- [ ] Run HLS references for exported `Arg` on the implementation checkout and record the complete callsite set in the commit notes.
- [ ] Add `ArgRef`, `ArgDischarge`, complete `ArgInstantiation`, and the
  three-field `Arg` in the exact D2 field order.
- [ ] Migrate every existing constructor to `ExplicitTheta`. Use named record syntax in production and fixture builders; retain positional construction only in shape witnesses that intentionally pin arity.
- [ ] Refactor `supportTermP`/`argP` to return the complete `ArgInstantiation`:

```haskell
explicitRuleP :: RuleId -> P ArgInstantiation
inferredRuleP :: RuleId -> P ArgInstantiation
```

The inferred parser creates `InferTheta rid refs [] [] AssuranceNone`;
`argBody` folds discharges, holes, and assurance into that payload.
- [ ] Add comma-list parsing for `from [refs]`, including the empty list, without accepting a trailing comma or a missing closing bracket.
- [ ] Update the `argP`/`supportTermP` haddock grammar comments and any §3/§5 grammar references in the `Lara.Syntax` module header to include the `ruleId "from" "[" argRefList? "]"` alternative, in the same commit that changes the parsers.
- [ ] Update `printArg` to select:

```haskell
ExplicitTheta term -> print the complete authored SupportTerm
InferTheta r rs ds hs as -> print the rule, refs, discharges, and assurance
```

Leaf-backed arguments use `ExplicitTheta (SLeaf ...)`; no hand-built inferred
leaf pairing is representable.
- [ ] Add a contextual-keyword collision fixture. `from` is reserved only in the generator, so the lexer still admits a rule or leaf literally named `from`. Declare both, then assert `by from(x)` parses as positional, `by from from [x]` parses as inferred, `from [from]` resolves the leaf reference, and every spelling survives `parseProgram . printProgram`. The generator's reserved list bars QuickCheck from this case, so a hand-written fixture is the only place it can be executed.
- [ ] Extend `SyntaxSpec` generators with both instantiation modes. Generated inferred `Arg`s must carry complete payload metadata and no shallow positional term. Add `from` to `reservedWords`.
- [ ] Assert `parseProgram . printProgram == Right` for inferred leaf-reference lists of length 0-3 and for legacy explicit programs.
- [ ] Run the focused syntax suite. Expected GREEN: parsing and round trip. Semantic inference remains RED until Task 3.

### Task 3: Derive theta and selected premises in the elaborator

**Files**

- Modify: `src/Lara/Elaborate/Error.hs`
- Modify: `src/Lara/Elaborate/Internal.hs`
- Modify: `test/ThetaInferenceSpec.hs`
- Modify: affected `test/ElaborateSpec.hs` helpers

**Interfaces**

- Consumes: `matchAPat :: Subst -> AtomPat -> Prop -> Either MatchFailure Subst`.
- Produces private helpers:

```haskell
resolveArgRef
  :: Env
  -> [(ArgId, SupportTerm)]
  -> ArgId
  -> RuleId
  -> Int
  -> ArgRef
  -> Either ElabError ResolvedArgRef

inferTheta
  :: Env
  -> [(ArgId, SupportTerm)]
  -> ArgId
  -> Rule
  -> [ArgRef]
  -> Either ElabError (Subst, [SupportTerm])
```

- [ ] Add all D6 error constructors and exact `elabErrorMessage` cases first. Add direct constructor-to-message tests so public wording cannot drift independently of behavior.
- [ ] Split `elabTerm` into a shared rule lookup/discharge tail and two instantiation branches. Keep the explicit branch textually equivalent to the current arity/association/premise-resolution logic.
- [ ] Preserve the type-level invariant: `InferTheta` carries its complete
  payload, so no runtime malformed-carrier branch or diagnostic is needed.
- [ ] Implement `resolveArgRef` with leaf/prior-arg exact-name lookup and explicit same-spelling ambiguity detection. Derive prior-argument propositions through `conclOf`.
- [ ] Implement `inferTheta` in the exact D4 order. Reuse `matchAPat`; do not call `matchPat` directly and do not duplicate normalized-equality logic.
- [ ] Reorder successful bindings by `ruleParams` and pair them with the exact selected `SupportTerm`s.
- [ ] Add the following focused negatives, asserting constructors and stable rendered fragments:
  - too few and too many references;
  - undeclared reference;
  - forward argument reference;
  - a reference to a prior argument whose conclusion is underivable (an
    undeclared-leaf-rooted prior argument cited in `from [...]`) producing
    `ThetaReferenceConclUnderivable`, not a crash or the unresolved message;
  - leaf/prior-argument same-spelling ambiguity;
  - premise predicate/arity/constructor/literal shape mismatch;
  - repeated parameter conflict across two premises;
  - parameter absent from every premise;
  - unknown rule takes precedence over all inference errors;
  - inference error precedes discharge and conclusion mismatch.
- [ ] Add normalized numeric consistency: references binding `0.71` and `0.710` to the same repeated parameter must succeed because `matchAPat` uses `sameTerm`.
- [ ] Add a duplicate-reference positive case: `by rule from [e1, e1]` where both premises match `e1`'s proposition succeeds, both `srPremises` entries are the same selected term (no dedup), and the result is byte-equal to the explicit form.
- [ ] Add the spelling-divergence case: an explicit source spelling a parameter `0.710` against a leaf spelling `0.71` is `sameTerm`-equal to the inferred form; assert equal verdicts and equal exit classification, and pin the byte divergence explicitly so the conditional contract has a regression rather than an assumption.
- [ ] Add zero-premise semantic cases: a zero-premise, zero-parameter rule elaborated via `from []` equals its explicit `r()` form through `Unit` and `encodeUnit`; a zero-premise rule with a parameter fails `ThetaParameterUnbound` under `from []`.
- [ ] Assert explicit and inferred forms produce exactly equal ordered substitutions, selected premise trees, `Unit`s, rendered core S-expressions, verdict JSON, and exit classification.
- [ ] Run:

```bash
cabal test lara-test --test-show-details=direct
```

Expected GREEN for every Haskell feature and legacy test.

### Task 4: Keep value substitution and audit consumers exact

**Files**

- Modify: `src/Lara/Elaborate/ValueBinding.hs`
- Modify: `src/Lara/ClaimSupport.hs`
- Modify: `test/ValueBindingsSpec.hs`
- Modify: `test/ClaimSupportSpec.hs`
- Modify: `test/ThetaInferenceSpec.hs`

**Interfaces**

- [ ] Update value-binding test helpers for the widened `Arg`; keep
  `substSupportTerm` focused on `ExplicitTheta` payloads and assert an adjacent
  `InferTheta` reference list is byte/value unchanged.
- [ ] Add a fixture where a bound value appears in the selected leaf. Verify
  value expansion runs first, inference derives the substituted theta, and the
  result equals the explicit unbound source.
- [ ] Change typed-attack audit refs and dead-end-source detection to inspect
  the elaborated term found by argument id, not the authored surface payload.
- [ ] Preserve authored rendering through `printArg surfaceArg`; assert the
  audit subject contains `from [e1]` while its refs come from the resolved
  semantic premise tree.
- [ ] Add the explicit-path counterpart regression: an **explicit** rule-backed attack source whose premise leaves carry refs absent from its discharge witnesses. Pin the widened ref set so the intended change to legacy behavior has a test, and assert the rendered formal object still prints the positional form.
- [ ] Run focused value-binding, claim-support, and theta-inference properties, then the complete Haskell suite.

### Task 5: Restore Lean presentation parity immediately

**Files**

- Modify: `lean/Lara/Presentation.lean`
- Modify: `lean/AxCheck.lean`
- Modify: `scripts/presentation-shape.hs`
- Modify: `lean/Lara/PresentationParity.lean`
- Modify: `lean/Lara/PresentationParityMain.lean` only if its inventory interface changes

**Interfaces**

- Produces: Lean `ArgRef`, `ArgDischarge`, state-safe `ArgInstantiation`,
  widened `Arg`, codecs, and round-trip theorems exactly as D8.
- Preserves: Lean/Haskell semantic `SupportTerm` shape and all checker-side proof statements.

- [ ] Add the Lean structures and constructors in the exact D8 order.
- [ ] Add `ArgRef`, `ArgDischarge`, and `ArgInstantiation` codecs plus round-trip proofs; widen `sxArg`, `unArg`, and `un_sxArg`.
- [ ] Add every new theorem to `lean/AxCheck.lean`; keep the standard axiom trio and no `sorry`.
- [ ] Update the Haskell witness with exact `ArgRef`, `ArgDischarge`, `ArgInstantiation`, and three-field `Arg` signatures, exhaustive eliminators, field normalization, and generic metadata checks.
- [ ] Update the Lean witness with the matching exact signatures, constructor checks, and Meta field checks.
- [ ] Grow the normalized inventory from 70 to 73 rows and retain derived row-count tripwires on both sides.
- [ ] Run:

```bash
make presentation-parity
cd lean
lake build
../scripts/test-check-axioms.sh
lake env lean AxCheck.lean | ../scripts/check-axioms.sh
```

Expected: 73 byte-identical parity rows; Lean build and axiom audit pass.

### Task 6: Migrate witnesses and active documentation

**Files**

- Modify: `examples/A/example.lara`
- Modify: `examples/S1/example.lara`
- Modify: `docs/lara-surface-grammar.md`
- Modify: `docs/spec.md`
- Modify: `README.md`
- Modify: `docs/mechanization-plan.md`
- Modify: `lean/README.md`
- Modify: `lean/Lara.lean`
- Modify: current-version headers in `src/Lara/Syntax.hs`, `src/Lara/Elaborate/Internal.hs`, `src/Lara/Elaborate/Error.hs`, `test/SyntaxSpec.hs`, and `lean/Lara/Presentation.lean`

**Interfaces**

- Consumes: fully verified `@0.5` parser/elaborator/parity contract.
- Produces: byte-neutral A/S1 source witnesses and active documentation; no completion claim yet.

- [ ] Record hashes for A and S1 `example.core.sexp`, `expected.json`, and any generated report files before source migration.
- [ ] Apply only the D9 argument rewrites. Keep all discharge lines, assurance bytes, claims, leaves, attacks, statuses, comments, and identifiers unchanged except version/explanation comments that directly describe the old positional spelling.
- [ ] Run the worked-example generator once and require all recorded hashes to remain unchanged.
- [ ] Run it a second time and require the same hashes again, proving idempotence.
- [ ] Add the `@0.5` grammar appendix with syntax, scope, matching order, diagnostics, and explicit/inferred equality contract.
- [ ] Update active result-12 counts to 73 while preserving historical `@0.3`/`@0.4` statements where they describe when a feature was introduced.
- [ ] Keep `lara-core@0.2`, frozen corpus counts, and measurement claims unchanged.

### Task 7: Evaluate the complete contract

- [ ] **Focused smoke:** run the CLI on inferred Example A and S1; require exit 0 and their existing expected statuses.
- [ ] **Source/core equality:** run each migrated `.lara` and sibling `.core.sexp`; compare stdout byte-for-byte and require equal exit codes.
- [ ] **Concrete round trip:** require QuickCheck coverage of both instantiation modes, empty/non-empty reference lists, discharges, and assurances.
- [ ] **Exact lowering:** compare explicit/inferred semantic support terms, `Unit`, `encodeUnit`, verdict JSON, and exit classification.
- [ ] **Fail closed:** run every D6 negative plus malformed parser forms and precedence checks.
- [ ] **Secondary consumers:** require claim-support rendering to preserve the inferred source form while dependency refs come from the complete elaborated term.
- [ ] **Haskell gate:** `cabal build all && cabal test all --test-show-details=direct`.
- [ ] **Presentation gate:** `make presentation-parity` with 73 byte-identical rows.
- [ ] **Lean gate:** `cd lean && lake build`, `../scripts/test-check-axioms.sh`, and the complete `AxCheck` audit.
- [ ] **Python auxiliaries:** `uv run --no-project python -m unittest discover -s elaborator -v` and `python3 -m unittest scripts/test_freeze_bundle.py -v`.
- [ ] **Walking skeleton:** `test/walking-skeleton-golden.sh`.
- [ ] **Replay:** `scripts/replay.sh` and `scripts/test-replay-tamper.sh`.
- [ ] **Differential:** `scripts/differential.sh` and `scripts/admission-differential.sh`.
- [ ] **Generation:** run worked-example and protected-artifact generators twice; require byte-identical second runs.
- [ ] **Freshness:** require no corpus core, expected JSON, manifest, bundle, or `measurements/frozen/` byte to change. Any drift is a blocker, not an accepted regeneration.
- [ ] **Hosted CI:** after opening the implementation PR, require both Haskell and Lean jobs green on the final head.

### Task 8: Record completion only after verification

**Files**

- Modify: `TODOS.md`
- Modify: `ara/staging/observations.yaml`
- Modify: `ara/trace/exploration_tree.yaml`
- Modify: `ara/trace/pm_reasoning_log.yaml`
- Modify: current `ara/trace/sessions/*.yaml` and session index according to the repository's ARA workflow

- [ ] Record #104 as complete with the exact verified syntax, diagnostics, 73-row parity result, and unchanged core/replay artifacts.
- [ ] Keep #105 open as a separate certificate-layer design problem; do not imply named certificate slots were implemented.
- [ ] Update mechanization/backlog claims only with outputs observed in Task 7.
- [ ] Parse every modified YAML file and run the repository's ARA structural checks.
- [ ] Re-run the smallest gates affected by final documentation/ARA edits, then review the final diff for stale `@0.4` live-version claims and accidental frozen-artifact changes.

---

## 6. Verification Matrix

| Property | Primary evidence | Failure caught |
| --- | --- | --- |
| New concrete syntax is lossless | Haskell parse/print QuickCheck and focused fixtures | inferred form prints as positional, loses order, or accepts malformed lists |
| Explicit syntax is unchanged | legacy round-trip and exact source fixtures | `@0.5` silently changes existing argument parsing/printing |
| References select exact premises | inferred semantic `srPremises` equality | elaborator discards authored selection and performs global search |
| Prior arguments are scope-safe | prior/forward reference pair | forward reference or incomplete prior term admitted |
| Theta is complete and ordered | exact `srSubst` equality in `ruleParams` order | matcher discovery order changes core bytes; missing parameter guessed |
| Matching uses one equality | `0.71`/`0.710` consistency case | duplicated syntactic matcher disagrees with `equiv` |
| Conflicts fail at source boundary | shape/conflict/unbound diagnostics | drift reaches generic unresolved premise or checker rejection |
| Value binding composes once | bound-leaf inferred/explicit equality | references renamed or inference runs before substitution |
| Certificates remain opaque | S1 source/core equality and tamper gate | theta feature rewrites certificate payload or replay identity |
| Secondary audits remain grounded | inferred attack-source audit regression | shallow source term hides actual dependency leaves |
| Presentation mirrors stay complete | Lean round trip + 73-row parity gate | Haskell-only field/type or constructor drift |
| Core semantics are unchanged | A/S1 hashes, source/core CLI equality, differential | surface sugar perturbs `Unit`, verdict, or replay |
| Generation is deterministic | two consecutive generator runs | non-canonical or stateful output |
| Frozen evaluation stays frozen | protected-artifact and freshness checks | accidental corpus/refreeze scope expansion |

---

## 7. Completion Criteria

The implementation is complete only when all of the following hold:

1. An ordinary argument can use `by rule from [refs]`, and parser/printer round-trip preserves that spelling and order.
2. Each reference resolves to exactly one declared leaf or prior argument; no global search, forward reference, or namespace ambiguity is accepted.
3. `matchAPat` is the only theta matcher, every policy parameter is bound, and final theta order is exactly `ruleParams` order.
4. Explicit and inferred sources that spell each parameter as the cited premises do produce equal semantic support terms, byte-identical `lara-core@0.2` units, identical verdict JSON, and identical exit behavior; sources differing only by `sameTerm`-equal spellings produce checker-equivalent units with identical verdicts, and the documentation states this condition rather than claiming unconditional byte-identity.
5. Existing explicit positional arguments and comparison-generated arguments retain their prior behavior and bytes.
6. Every D6 count/scope/shape/conflict/unbound case has a focused deterministic regression and stable author-facing diagnostic.
7. Value bindings run before inference without rewriting `ArgRef`; claim-support and audit consumers use complete elaborated terms for dependency refs.
8. Haskell and Lean model the same three-field `Arg`, distinct `ArgRef`, and two-arm `ArgInstantiation`; the 73-row parity and full axiom gates pass.
9. Example A and S1 demonstrate the feature while their core, expected JSON, reports, replay, and statuses remain unchanged.
10. No corpus, manifest, bundle, measurement, checker, wire, backend, or freeze-tag artifact changes.
11. #104 is closed only after local and hosted verification; #105 remains open and accurately scoped.

---

## 8. Reviewed Data Flow

```text
raw .lara Program
  -> parse ArgInstantiation
       ExplicitTheta term
       InferTheta rule refs discharge obligations assurance
  -> value-binding expansion (Term fields only; ArgRef unchanged)
  -> comparison expansion (generated Args remain ExplicitTheta)
  -> declaration-order argument lowering
       ExplicitTheta -> existing positional association + unique premise search
       InferTheta
         -> exact named leaf/prior-arg selection
         -> matchAPat in rule-premise order
         -> complete/reorder theta by ruleParams
         -> exact selected premise terms
  -> unchanged semantic SRule
  -> unchanged Unit / .core.sexp / checker / replay
```

### Failure handling

| Failure | Boundary | Deterministic response |
| --- | --- | --- |
| malformed `from` list | parser | located parse error |
| invalid inferred carrier | typed presentation sum | complete `ArgInstantiation` makes the pairing unrepresentable | no author-facing path |
| wrong reference count | elaborator before name lookup | expected/got count diagnostic |
| unknown or forward reference | declaration-order resolver | unresolved reference diagnostic |
| resolved prior arg with underivable conclusion | declaration-order resolver | conclusion-underivable diagnostic |
| leaf/prior-arg spelling collision | declaration-order resolver | ambiguous reference diagnostic |
| premise pattern mismatch | `matchAPat` | premise/ref/prop shape diagnostic |
| repeated parameter disagreement | `matchAPat` | parameter old/new conflict diagnostic |
| parameter absent from all premises | post-match completeness check | unbound parameter diagnostic |
| discharge or announced conclusion wrong | existing checks after inference | existing discharge/conclusion diagnostic |
| semantic or artifact byte drift | verification | stop; feature is not byte-neutral |

### Implementation order

Sequential. Tasks 1-5 share the exported `Arg` shape and cannot be independently merged. Task 6 depends on the complete parser/elaborator/parity contract. Task 7 establishes evidence. Task 8 records completion only from that evidence.

### Expected mid-flight gate state

Tasks 2-4 widen the exported Haskell `Arg` while Task 5 restores the Lean
mirror, so the cross-language gates **cannot** pass in between:

- `make presentation-parity` and `cd lean && lake build` are **expected red from
  Task 2 through Task 4**, and must be green at Task 5. A red parity gate before
  Task 5 is the plan working, not a break to diagnose.
- The meaningful mid-flight gate is `cabal test lara-test`. Keep it green at
  every task boundary.
- Never edit the parity witnesses or the row-count tripwire to make an
  intermediate commit pass. That guard exists because result 12 narrowed
  silently three times; defeating it to get a green intermediate commit
  reintroduces exactly the failure it was built to catch.
- The branch is not CI-green until Task 5 lands. Do not open the implementation
  PR before then.

---

## 9. Engineering Review Notes (2026-08-12)

Produced by `/plan-eng-review`. Scope was challenged and accepted as-is: the
~30-file footprint is mechanical fallout of widening an exported record under
`-Wall -Werror=missing-fields` plus the mandatory cross-language parity
discipline, not scope creep.

### What already exists (reused, not rebuilt)

| Existing machinery | Location | How this plan uses it |
| --- | --- | --- |
| One-way pattern matcher with shape/conflict distinction | `Lara.Elaborate.Subst.matchAPat` (`src/Lara/Elaborate/Subst.hs:82`) | Reused verbatim as the only theta matcher; no second matcher is introduced |
| Normalized term equality | `sameTerm` / `equiv` inside `matchAPat` | Gives `0.71`/`0.710` consistency for free |
| Prior-argument threading in declaration order | `elabOne` / `priors` (`src/Lara/Elaborate/Internal.hs:387-397`) | Reused for prior-argument reference resolution; forward references fail naturally |
| Rule-instance conclusion derivation | `conclOf` (`Internal.hs:517-521`) | Derives the proposition for a prior-argument reference |
| Discharge/hole/assurance folding | `argBody` (`src/Lara/Syntax.hs:1017`) | Unchanged; attaches to the inferred `SRule` exactly as to the explicit one |
| Elaborated-term lookup for consumers | `surfaceDerivedArgTermById` (`src/Lara/ClaimSupport.hs:271`) | Already present; D7 switches audit refs onto it rather than adding a new traversal |
| Cross-language shape guard | `scripts/presentation-shape.hs` + `lean/Lara/PresentationParity.lean` | Extended from 70 to 73 rows; the row-count tripwire (`presentation-shape.hs:957`) enforces both sides |
| Compiler-enforced constructor migration | `lara.cabal:18` (`-Wall -Werror=missing-fields`) | Any `Arg` construction site missed by the HLS sweep fails the build; the D2 site list is a convenience, not the safety net |

Nothing in the plan rebuilds an existing capability.

### NOT in scope (considered during review, explicitly deferred)

| Deferred | Rationale |
| --- | --- |
| Discharge-witness namespace-collision policy | `resolveDischarges` (`Internal.hs:471-473`) silently prefers a leaf where `from [...]` errors as ambiguous. Fixing it is a breaking surface change needing its own version treatment; recorded in `TODOS.md` |
| Rejecting `from []` at the parser | Keeping the list production total is less machinery than a carve-out; both degenerate outcomes are pinned by test instead |
| Parser-only sugar with canonical (lossy) printing | Reference resolution needs elaboration scope, so it cannot live in the parser; lossy printing would also violate the result-12 presentation-parity doctrine the parity guard exists to enforce |
| `#105` named certificate premise slots | Blocked on the opaque-certificate layering decision; whether `from [refs]` extends or collides with named slots belongs to that plan |
| Corpus migration to the inferred form | Byte-neutrality of frozen artifacts is a hard gate; the two witnesses prove the feature without touching corpus bytes |

### Failure modes for the new codepaths

| New codepath | Realistic production failure | Test? | Error handling? | Author sees |
| --- | --- | --- | --- | --- |
| `inferredRuleP` list parsing | Trailing comma / missing bracket in a hand-edited file | yes (Task 2 negatives) | yes — located parse error | clear parse error with position |
| `resolveArgRef` name lookup | Author renames a leaf and forgets the reference | yes (Task 3) | yes — `ThetaReferenceUnresolved` | clear: names the ref and the 1-based premise |
| `resolveArgRef` on underivable prior arg | Citing an argument rooted at an undeclared leaf | yes (added this review) | yes — `ThetaReferenceConclUnderivable` | clear; previously would have been a partial-function crash |
| `inferTheta` shape match | Policy premise pattern edited without updating authors | yes (Task 3) | yes — `ThetaReferenceShapeMismatch` with the selected `Prop` | clear |
| `inferTheta` repeated-parameter conflict | Two cited premises disagree on a shared parameter | yes (Task 3) | yes — `ThetaReferenceConflict` with old/new terms | clear |
| `ruleParams` completeness sweep | Rule gains a conclusion-only parameter | yes (Task 3) | yes — `ThetaParameterUnbound` | clear |
| Spelling-divergent explicit vs inferred | Equivalent sources differ in bytes | yes (added this review) | n/a — equivalent, not an error | no error; contract now documents the condition |
| D7 audit-ref widening | Legacy explicit rule-backed attack source reports more refs | yes (added this review) | n/a — intended widening | report shows fuller dependency set |

**Critical gaps: 0.** Every failure mode has both a test and a fail-closed
diagnostic; none is silent.

### Inline ASCII diagrams to add during implementation

- `src/Lara/Elaborate/Internal.hs`, above the inference branch: the D4 pipeline
  (refs → resolution → `matchAPat` fold → `ruleParams` reorder → `SRule`),
  showing where each D6 error exits.
- `src/Lara/Syntax.hs`, above `supportTermP`: the three-way head dispatch
  (`leaf(...)` / `rule(...)` / `rule from [...]`) and the contextual-`from` peek.
- `test/ThetaInferenceSpec.hs`, above the fixture policy: which rule exercises
  which property (prior-arg reference, repeated parameter, conclusion-only
  parameter), since the policy's shape is otherwise non-obvious.
- Review the existing `argP` / `supportTermP` haddock grammar while editing —
  it states the surface grammar and goes stale the moment Task 2 lands.

### Parallelization

Sequential implementation, no parallelization opportunity. Tasks 1-5 all touch
the exported `Arg` shape, so no two can proceed in isolated worktrees without
conflicting; Tasks 6-8 depend on the completed contract and its evidence.

### Implementation Tasks

Synthesized from this review's findings. Each derives from a specific finding
above; all are folded into the task checklists in §5.

- [ ] **T1 (P1, human: ~30min / CC: ~3min)** — elaborator — add `ThetaReferenceConclUnderivable` and its negative test
  - Surfaced by: Architecture review issue 1 / outside voice OV-2 — `conclOf` returns `Nothing` for an undeclared-leaf-rooted prior argument
  - Files: `src/Lara/Elaborate/Error.hs`, `src/Lara/Elaborate/Internal.hs`, `test/ThetaInferenceSpec.hs`
  - Verify: `cabal test lara-test --test-show-details=direct`
- [ ] **T2 (P1, human: ~40min / CC: ~5min)** — docs/elaborator — qualify the explicit≡inferred byte-equality contract as spelling-conditional and pin it with a divergence test
  - Surfaced by: outside voice OV-1 — inferred theta inherits the cited premise's spelling; the wire encoder does not normalize
  - Files: plan D4/D10/§7, `docs/lara-surface-grammar.md`, `test/ThetaInferenceSpec.hs`
  - Verify: `cabal test lara-test`; grammar appendix states the condition
- [ ] **T3 (P1, human: ~1h / CC: ~10min)** — claim-support — document the D7 audit widening and pin the explicit path
  - Surfaced by: outside voice OV-3 — `surfaceDerivedArgTermById` widens refs for existing explicit rule-backed attack sources, not only inferred ones
  - Files: `src/Lara/ClaimSupport.hs`, `test/ClaimSupportSpec.hs`
  - Verify: `cabal test lara-test`; A/S1 report bytes unchanged
- [ ] **T4 (P2, human: ~20min / CC: ~2min)** — tests — duplicate-reference positive case `from [e1, e1]`
  - Surfaced by: Test review gap 1 — no coverage of one leaf instantiating two premises
  - Files: `test/ThetaInferenceSpec.hs`
  - Verify: `cabal test lara-test`
- [ ] **T5 (P2, human: ~15min / CC: ~2min)** — tests — zero-premise semantics for `from []`
  - Surfaced by: Test review gap 2 / outside voice OV-5 — canonical form was parse/print-only
  - Files: `test/ThetaInferenceSpec.hs`
  - Verify: `cabal test lara-test`
- [ ] **T6 (P2, human: ~20min / CC: ~3min)** — parser — contextual-keyword fixture for identifiers named `from`
  - Surfaced by: outside voice OV-8 — `from` is reserved only in the generator, so QuickCheck can never reach the collision
  - Files: `test/SyntaxSpec.hs` or `test/ThetaInferenceSpec.hs`
  - Verify: `cabal test lara-test`
- [ ] **T7 (P2, human: ~10min / CC: ~1min)** — parser docs — update `argP` / `supportTermP` haddock grammar in the same commit as the parser change
  - Surfaced by: Code quality review issue 2 — grammar comments state the surface grammar and go stale at Task 2
  - Files: `src/Lara/Syntax.hs`
  - Verify: read the haddocks against D1's grammar block
- [ ] **T8 (P3, human: ~10min / CC: ~1min)** — plan — record the expected mid-flight red state of the parity and Lean gates
  - Surfaced by: outside voice OV-10 — Tasks 2-4 cannot pass cross-language gates
  - Files: this plan §8
  - Verify: §8 names which gate is meaningful mid-flight

---

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | `/codex review` | Independent 2nd opinion | 0 | — | — |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | CLEAR | 9 issues, 0 critical gaps |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | — |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | — |

**CROSS-MODEL:** The outside voice ran as a Claude subagent after Codex timed out
at 5 minutes mid-exploration. It independently reproduced two review findings
(the underivable prior-argument conclusion, and the discharge-vs-reference
namespace inconsistency) and added six accepted ones: the spelling-conditional
byte-equality contract, the D7 audit widening reaching legacy explicit sources,
the `from []` justification, the applicability survey, the contextual-`from`
fixture, and the mid-flight gate-red note. During implementation, D2 was
strengthened to carry the complete inferred payload, making malformed
inferred/leaf pairings unrepresentable; no `ThetaInferenceMalformed` diagnostic
is part of the final contract. Parser-only lossy sugar remains rejected because
reference resolution needs elaboration scope and it would violate the result-12
presentation-parity doctrine.

**VERDICT:** ENG CLEARED — ready to implement.

NO UNRESOLVED DECISIONS
