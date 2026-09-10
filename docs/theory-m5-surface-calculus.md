# M5 Surface Calculus and Verified Elaboration

This document is the durable claim boundary for Theory M5. It records what the
Lean development proves about the full structured presentation AST, which
hypotheses are load-bearing, how the verified model relates to the shipped
Haskell path, and which stronger statements the paper must not make. The Lean
sources are authoritative.

_Status: settled record (2026-09-01; theory spine, tracker #180)._

## Motivation and Trusted Boundary

Before M5, the structured presentation codec had a proved round trip and the
core checker/compiler had proved metatheory, but the lowering between those two
boundaries was justified only by executable tests. That left a trusted-boundary
gap: a parsed value-binding, comparison, inferred argument, named certificate,
or surface attack could in principle be lowered differently from the object
assumed by the core proof.

M5 closes that gap for a model whose input is already a
`Lara.Presentation.Program` paired with a `Lara.Presentation.Policy`.
`Lara.Surface.Input` contains those two complete live
`lara-syntax@0.10` AST values unchanged. The environment is quantified:

```lean
structure Lara.Surface.Env (canon : String → String) where
  registry : Support.BackendRegistry canon
  startsIdent : String → Bool
  startsIdent_nat_false : ∀ n, startsIdent (Nat.repr n) = false
  encodeProp : String → Option String
```

The theorem therefore begins after concrete parsing. It covers the full
structured AST and the pure elaboration model, not source bytes, lexer tokens,
comments, whitespace, source locations, or concrete parser diagnostics. The
backend registry and identifier classifier remain parameters with explicit
soundness premises where they are transported. The proposition encoder is
also a parameter, but global renaming reuses it unchanged on formula source
text that `RenamingSound` requires to remain fixed; there is no separate
encoder-renaming premise.

`Lara.Surface.Elaborated canon` retains the core gamma, ground atoms and
`Lara.Unit`, as well as surface-visible claims, authored argument IDs and
obligations, open questions, resolved attacks, and the expanded semantic
program. These extra fields are the alignment witnesses needed to state
preservation without pretending that the core `Unit` retains authored names.

## Supported Fragment and Production Declaration Guards

The supported fragment is not a smaller AST. `Supported` records the complete
live AST's structural lowering restrictions represented by this structure:

```lean
structure Lara.Surface.Supported (input : Input) : Prop where
  policy_matches : input.program.policy = input.policy.id
  declaration_ids_nodup : DeclarationIdsNodup input.program
  rule_namespaces_wf : RuleNamespacesWellFormed input.policy
  value_bindings_wf : ValueBindingsWellFormed input
  comparisons_wf : ComparisonsWellFormed input.program input.policy
  inferred_args_wf : InferredArgsWellFormed input.program input.policy
  named_certs_wf : NamedCertificatesWellFormed input.program input.policy
  attack_names_wf : SurfaceAttacksWellFormed input.program input.policy
  canonical_labels : CanonicalPremiseLabels input.policy
```

The fields mean, exactly:

- the program names the supplied policy;
- leaf, argument, claim, and value-binding identifiers are duplicate-free;
- rule IDs are duplicate-free, each rule's premise-label and question
  namespaces are duplicate-free and disjoint, and reserved labels are absent;
- value bindings, structured value substitution, prose interpolation, and
  `{cell ...}` references satisfy the frozen sort/name restrictions;
- every comparison has one matching relation/polarity scheme and its generated
  declarations, roles, substitutions, and conclusions have the required shape;
- inferred arguments refer only to uniquely resolved earlier declarations,
  cover their rule parameters, and have shape-correct named discharges;
- named certificates have an allowed schema, unambiguous premise slots,
  well-formed named binders, and valid formula annotations;
- rebut, undercut, and undermine endpoints and paths resolve in their typed
  namespaces; and
- premise labels are either absent or have rule-premise length with at least
  one named slot, matching the current concrete-surface convention.

`supportedB` is the executable conjunction of the named field deciders.
`supportedB_iff (input)` proves both directions:

```lean
Lara.Surface.supportedB input = true ↔ Lara.Surface.Supported input
```

The component correspondences
`declarationIdsNodupB_iff`, `ruleNamespacesWellFormedB_iff`,
`valueBindingsWellFormedB_iff`, `comparisonsWellFormedB_iff`,
`inferredArgsWellFormedB_iff`, `namedCertificatesWellFormedB_iff`,
`surfaceAttacksWellFormedB_iff`, and
`canonicalPremiseLabelsB_iff` expose the projections used by reflection.

Role, status, and group checks run after value/comparison expansion and are
carried separately by the syntax-directed judgment, matching production order:

- `ChecksAuthoredConclusion` validates a reconstructed argument's announced
  role. A declared `supports(c)` must have a conclusion equivalent to
  `claimFormal(c)`; an undeclared support ID is the explicit derived-support
  arm; a challenge must name a declared target argument or leaf.
- `StatusesWellFormed` / `statusesWellFormedB_iff` require every requested
  status ID to name a declared (including comparison-generated) claim.
- `GroupsWellFormed` / `groupsWellFormedB_iff` require unique group IDs,
  distinct members, at least two members, and only declared leaves.

`AttackEndpointsDeclared` and `validateAttackEndpoints` are the adjacent raw
namespace guard before groups. Group diagnostics use production's seen-prefix
rule: they report the value at the first repeated occurrence (so
`[a,b,b,a]` reports `b`), not the earliest value that repeats somewhere later.

These are independent predicates and deciders, not consequences of core
acceptance. Together with `Supported`, they delimit the derivable production
surface. Keeping them separate makes their post-expansion error precedence
explicit rather than moving them into the early structural guard.

## Binding Is Not Global Renaming

Alpha-equivalence is reserved for genuine lexical binders.
`Surface.Binding.RuleAlpha` abstracts rule parameters by declaration slot;
`ruleAlpha_refl`, `ruleAlpha_symm`, and `ruleAlpha_trans` make it an
equivalence. `substParam` is capture-avoiding and partial:
`substParam_fresh_identity`, `substParam_preserves_wellSorted`, and
`substParam_compose_of_fresh` state its identity, preservation, and
fresh-composition laws.

`NDNamed.Alpha` similarly abstracts only named `nd@1` lambda binders and
their bound `.hypX` occurrences. Numeric and symbolic premise references,
theory indices, formula text, and anonymous binders remain fixed.
`NDNamed.toDB_eq_of_alpha` and `NDNamed.lowerNamed_eq_of_alpha` prove that
alpha-equivalent well-formed named certificates have identical de Bruijn and
kernel lowerings. `Surface.alpha_elaboration_invariant` exposes the
paper-facing lowering equality under both well-formedness premises and
`startsIdent_nat_false`.

Top-level declaration IDs, argument references, premise labels, value names,
source references, and related global namespaces are not binders. They use the
typed `Surface.Binding.GlobalRenaming`. Backend IDs, versions, theory and
artifact digests, policy IDs, and other replay-significant identities are not
fields of this renamer and stay fixed.

Global equivariance has two explicit hypotheses:
`RenamingSound ρg program policy` supplies the structural and fixed-spelling
conditions. `EnvRenamingSound env ρg` supplies preservation of
`env.startsIdent` under `renameText` and registry replay under the renamed
certificate, premise, and conclusion data. It has no proposition-encoder
field: `env.encodeProp` is reused unchanged on fixed formula source text.
Under those hypotheses:

- `Binding.supported_rename_iff` preserves and reflects `Supported`;
- `Renaming.global_renaming_stage_transports` packages transport of
  supportedness, value and comparison expansion, reconstruction/certificate
  lowering, attack resolution, admission/pruning, and core-check acceptance;
  and
- `Renaming.global_renaming_equivariant` says that a successful audited
  source elaboration has a related successful audited renamed elaboration,
  both pure elaborations return their audit outputs, core-check success agrees,
  and every accepted source checked unit has a related accepted renamed unit.

Two ground relations appear in that last theorem, for different purposes.
`ElaboratedRelated.ground` uses `GroundRelated`: it renames the executable
retained-leaf/requested-status prefix but keeps the policy theory table as a
literal replay-significant suffix. Consequently, the theorem's equality of
`exceptIsOk` results compares the actual source and target elaboration outputs.
The final `CheckedUnitRelated` witness instead checks
`source.output.ground.map (renameResidualAtom ρg)` together with
`renameCoreUnit ρg source.output.unit`. It is the fully mapped-ground core
transport witness supplied by `checkUnit_ok_rename`; it is not a claim that
this ground equals `target.output.ground` when fixed theory atoms are present.

This is typed equivariance, not alpha-equivalence and not permission to rename
replay identities.

## Production-Ordered Passes

`Surface.elaborateWithAudit` performs one canonical sequence:

```text
program/policy ID match
  → canonical premise-label validation
  → duplicate admission-key and leaf-ID validation
  → value substitution, prose interpolation, and {cell ...} expansion
  → comparison expansion in declaration order
  → authored argument/claim and rule-namespace checks
  → raw surface-attack endpoint declaration checks
  → duplicate-group validation
  → left-to-right argument reconstruction
      (reference resolution, theta inference, named discharges,
       certificate-name/formula lowering, authored-role validation)
  → surface attack resolution, then raw attack alignment
  → requested-status resolution
  → declared Unit assembly
  → one admission evaluation and policy/group prune
  → retained Elaborated output
```

`{cell ...}` belongs to value expansion, not comparison expansion.
Certificate-name and source-authored formula lowering occur inside the
left-to-right argument fold, where earlier declarations form the reference
environment. All declared surface attacks resolve before admission pruning.
The declared unit is assembled before the one admission evaluation; the
retained unit is constructed from that evaluation's prune.

The finite core-check ground is retained leaf conclusions, resolved requested
status formals, and the policy theory table. Unrequested declared claims do not
silently enter `surfaceGround`.

`Surface.elaborate` projects the audited output. It intentionally does not
call `Check.Unit.checkUnit`, `Surface.check`, or a concrete parser. In
particular, it does not itself establish core signature/ground sorting,
recursive support typing, typed conflict completeness, or backend certificate
acceptance.

## Independent Relations and Executable Correspondence

Value interpolation and comparison expansion each have an independent
relation:

```lean
expandValues policy program = .ok out → ExpandsValues program out
ValueBindingsWellFormed ⟨program, policy⟩ →
  ExpandsValues program out → expandValues policy program = .ok out

expandComparisons policy program = .ok (target, generated) →
  ExpandsComparisons policy program target generated
GeneratedIdsFresh program = true →
  ComparisonsWellFormed program policy →
  ExpandsComparisons policy program target generated →
  expandComparisons policy program = .ok (target, generated)
```

These are `expandValues_sound`/`expandValues_complete` and
`expandComparisons_sound`/`expandComparisons_complete`. The prose walker
has the corresponding `expandNl_sound`/`expandNl_complete` pair against
`ExpandsNl`.

`Surface.Checks env input output` is syntax-directed. Its constructors and
fields carry supportedness, admission, generated-ID freshness, per-rule,
role, status, and group well-formedness, the two independent expansion
derivations, the left-to-right argument and attack derivations, exact output
component equalities, and `CoreObligations env output`. `CoreObligations`
contains declarative signature/policy sorting, scope and rule-ID conditions,
argument uniqueness, `HasSupport` derivations (including certificate/backend
acceptance), typed attacks, endpoint membership, and `AttackComplete`. It does
not contain `checkUnit` success, `exceptIsOk`, or an equivalent wrapper.

`CoreObligations.checkUnit_complete` feeds those fields to
`Check.Unit.checkUnit_complete` and derives a concrete accepted carrier.
`CoreObligations.of_checkUnit_ok` is the converse extraction used by the
executable checker. Thus `Checks` is not defined as successful `elaborate` or
successful core execution, and no derivation constructor calls `elaborate`.

For all `env`, `input`, and `output`:

```lean
check env input = .ok output → Checks env input output       -- check_sound
Checks env input output → check env input = .ok output       -- check_complete
Checks env input out₁ → Checks env input out₂ → out₁ = out₂  -- checks_deterministic
Checks env input output → Supported input                    -- checks_supported
```

`check` is the executable decider for the independent judgment. It executes
the core checker after declarative surface assembly; soundness extracts
`CoreObligations`, while completeness derives the execution from those
obligations. This differs from defining `Checks` in terms of `check`,
`elaborate`, or an executable-success predicate.

## Elaboration Theorems

Pure elaboration completeness is one-way and unconditional once a derivation
exists:

```lean
theorem elaborate_complete
    (env) (input) (output)
    (h : Checks env input output) :
    elaborate env input = .ok output
```

There is deliberately no unconditional
`elaborate_sound : elaborate env input = .ok output → Checks env input output`.
Pure elaboration omits the core check and the full supported-fragment
validation, so that statement is false.

The preservation theorem quantifies over `env : Env canon`,
`input : Input`, `output : Elaborated canon`, and a surface derivation:

```lean
theorem elaborate_preserves
    (env) (input) (output) (h : Checks env input output) :
  ∃ checked,
    elaborate env input = .ok output ∧
    Check.Unit.checkUnit output.gamma env.registry output.ground output.unit =
      .ok checked ∧
    output.openQuestions.map Prod.fst = output.argIds ∧
    output.openQuestions.map Prod.snd = coreOpenQuestions output.unit ∧
    output.unit.atts = output.resolvedAttacks
```

Thus a derivable surface input lowers successfully to the same output, the
actual core checker accepts that output, authored argument order aligns with
the core-visible question sequence, and retained attacks are exact.

Reflection quantifies over an explicit checked-unit witness and has both
load-bearing hypotheses:

```lean
theorem elaborate_reflects
    (env) (input) (output) (checked)
    (hsupported : Supported input)
    (helab : elaborate env input = .ok output)
    (hcore :
      Check.Unit.checkUnit output.gamma env.registry output.ground output.unit =
        .ok checked) :
    Checks env input output
```

Its direction is from this already-parsed, supported input's successful
canonical lowering plus successful core checking back to the independent
surface judgment. It does not quantify over arbitrary core units.

The separately quotable projections are exact:

- `obligations_preserved h`:
  `output.authoredObligations = authoredObligationsOf input.program`;
- `attacks_preserved h`:
  `output.unit.atts = output.resolvedAttacks`;
- `conclusions_preserved`: a successful `reconstructArgument` followed by
  successful `lowerToSupportTerm` has
  `conclOfTerm ... built.term = some built.conclusion`; and
- `argument_order_preserved h`: authored IDs equal the first projection of
  `openQuestions`, while `coreOpenQuestions output.unit` equals its second
  projection.

## Direct and Compiled Observation

`directAF hsurface` is indexed by a surface derivation. It uses
`List.range output.argIds.length` as its carrier and computes attacks from
`output.resolvedAttacks` and the retained surface argument order. It does not
call `elaborate`, `Compile.edgeB`, or `Compile.checkedAF`.

The two claim APIs are independently defined and optional. `directClaims`
re-runs source reconstruction over the semantic program and does not read
`output.claims`; `directClaim hsurface claimId` looks up that reconstructed
ledger. `coreClaim? output claimId` separately looks up the retained core-side
ledger. `directClaims_eq_claims` and `directClaim_eq_coreClaim?` prove their
agreement for an accepted surface derivation. A missing ID remains `none` on
both sides and is never manufactured into an empty-support gap claim.

For a surface derivation `hsurface : Checks env input output` and a concrete
successful core check `hchecked`:

- `directClaim_support_bound hsurface claimId hclaim` proves every support
  index of the claim selected by `hclaim : directClaim hsurface claimId =
  some claim` is in the direct carrier; and
- `direct_compiled_agree hsurface hchecked` proves exact AF equality:
  `directAF hsurface = Compile.checkedAF checked.program`.

The public observation theorem is parametric over attack-extensional extension
semantics:

```lean
theorem observe_coherent
    (sem : Semantics.ExtensionSemantics)
    (hext : Observation.AttackExtensional sem.spec)
    (hsurface : Checks env input output)
    (hchecked :
      Check.Unit.checkUnit output.gamma env.registry output.ground output.unit =
        .ok checked)
    (claimId : Presentation.PropId) :
  Surface.observe sem hsurface claimId =
    (coreClaim? output claimId).map
      (Semantics.observe sem (Compile.checkedAF checked.program))
```

The named corollaries instantiate grounded, complete, preferred, stable, and
semi-stable semantics and discharge the corresponding `AttackExtensional`
premise internally; callers supply only the surface/core acceptance data and
claim ID. The stable corollary preserves `noExtension`; it does not collapse
nonexistence into a local claim status. Grounded coherence uses
`Observation.attackExtensional_leastComplete`, because grounded semantics is
represented by the least complete extension specification. All six coherence
results preserve lookup absence as `none` as well as comparing present claims.

## Load-Bearing Counterexamples

The following checked witnesses target distinct hypotheses rather than merely
showing generic rejection:

| Dropped hypothesis | Mechanized witness | Observed consequence |
| --- | --- | --- |
| Generated comparison IDs are fresh | `Examples.Surface.necessity_generated_ids_fresh` | The later colliding comparison returns `invalidComparison`. |
| Premise resolution is unambiguous and earlier-only | Executable example beside `inferredArgsWellFormedB_iff` | Two prior rows with one authored reference make `inferredArgsWellFormedB = false`. |
| Named binders are capture-free | Executable captured-binder and naive-core-bypass examples | The surface checker rejects the captured binder even though a naive lowered core bypass is accepted. |
| Comparison polarity matches the scheme | Executable example beside `comparisonsWellFormedB_iff` | A higher-is-better scheme with a lower-is-better measurand returns `invalidComparison`. |
| Argument IDs are unique before attack indexing | Executable duplicate-ID example | Duplicating the attacked source argument returns `duplicateArgId`. |
| A declared support role matches its claim | Executable conclusion-mismatch example beside `checkAuthoredConclusion_sound` | A `supports(c)` argument with a non-equivalent conclusion returns `conclusionMismatch`. |
| Challenge targets are declared | Executable undeclared-challenge example | A challenge naming an absent argument returns `challengeTargetUndeclared`. |
| Requested statuses name declared claims | Executable unknown-status example beside `resolveStatuses_sound` | An unknown status ID returns `unknownStatusClaim` before core assembly. |
| Group declarations match production invariants | Executable duplicate-ID/member, singleton, and undeclared-member examples beside `validateGroups_sound` | Duplicate IDs/members, cardinality below two, and undeclared leaf members return their distinct group errors. |
| Production precedence is compositional | Executable first-repeat and certificate-precedence examples plus the strengthened conclusion/group conformance fixtures | Endpoints precede groups; groups precede the argument fold; certificate lowering precedes the same argument's role; roles precede attack paths; group payloads use first-repeat order. |
| The lowered unit passes the core checker | Executable invalid-core-support examples beside `CoreObligations.checkUnit_complete` | `supportedB` remains true and pure elaboration succeeds, while `check` rejects the unsupported core unit. |
| Direct claim support is carrier-local | `Surface.not_observe_coherent_of_unbounded_support` | Two frameworks that agree on their retained carrier can yield different observations for junk support outside it. |
| Missing claims remain absent | Executable example beside `directClaim_eq_coreClaim?` | Independent direct/core lookup and optional direct observation all return `none`. |

The supported-fragment decider also has isolated boundary fixtures:
`duplicateArgument_unsupported`,
`premiseQuestionCollision_unsupported`,
`unknownValueInterpolation_unsupported`,
`missingComparisonScheme_unsupported`,
`laterArgumentReference_unsupported`,
`ambiguousNamedCertificate_unsupported`, and
`unresolvedAttackPath_unsupported`. Each proves a distinct malformed input
has `supportedB = false`.

## Cross-Language Conformance Provenance

`fixtures/surface/MANIFEST.tsv` is the ordered provenance source. It contains
25 cases: the all-forms acceptor, rule- and ND-alpha pairs, focused comparison,
cell interpolation, named premise and formula cases, eleven named structural
rejections, an admission-pruned open-obligation case, and accepted fixtures
that force `gap`, `defeated`, `contested`, and stable `noExtension`. Its closed feature
vocabulary covers labelled premises, named discharges, comparisons, both
interpolation forms, named certificates/formulas, both binder classes, all
surface attacks, capture/ambiguity/comparison/attack-path rejection, role and
challenge rejection, status rejection, all four group guards, admission
pruning, and an open obligation.

This manifest is complete with respect to that closed required-feature
vocabulary, not with respect to the parser or AST input space. The 25 fixtures
are representative finite exercised production behavior. They are not a
parser-correctness proof, exhaustive parser coverage, or exhaustive coverage
of every instance of the presentation AST.

The two emitters are independent:

- Haskell parses the concrete files through the production parser and runs the
  production `prepareSource`/`runSourceCheck` path.
- Lean constructs matching `Presentation.Program`/`Policy` values directly
  and runs the verified surface checker, elaborator, and observation functions.

Each emits the same seven-column canonical table:

```text
case_id  ast_fingerprint  outcome  core_fingerprint
obligations  attacks  observations
```

The `obligations` column has retained, post-admission semantics: it walks the
holes of retained `output.unit.args` in retained argument order and renders
`arg-id:question-id`. It is deliberately not the pre-prune
`output.authoredObligations` ledger used by `obligations_preserved`. The real
`admission-prune-accept` row proves the distinction: the quarantined argument
is removed, while the retained open argument emits exactly `arg-open:cq`.

The AST fingerprint prevents output agreement over different inputs. The gate
`scripts/check-surface-conformance.sh` rejects an empty or malformed
manifest, unknown or uncovered features, empty outputs, missing/extra/reordered
case IDs, disagreement between either emitter and
`test/surface-conformance.golden`, or disagreement between the emitters
during an update. `scripts/check-presentation-parity.sh` separately checks
the full AST shape inventory.

## Explicit Exclusions

M5 does not prove any of the following:

- **Concrete parser correctness.** No theorem starts from `.lara` bytes or
  relates the Haskell parser to `Presentation.Program`/`Policy`.
- **Surjectivity onto the core.** There is no theorem saying every accepted
  `Lara.Unit` or checked core program has a surface preimage.
- **Injectivity or unique recovery.** Value expansion, generated comparisons,
  binder alpha-equivalence, admission pruning, and erased authored names can
  map distinct surface inputs to the same core result. No unique source
  recovery theorem is stated.
- **Unconditional elaboration soundness.** A successful pure `elaborate`
  call alone does not imply `Checks`; reflection also requires `Supported`
  and a successful `checkUnit`.
- **Haskell correctness from Lean alone.** Lean proves the model. The shared
  table and Haskell tests provide finite conformance evidence.
- **Diagnostic or byte preservation beyond the stated gates.** Error-message
  text, parser locations, comments, and whitespace are outside the theorem.

## Paper-Safe Claim Language

The paper may claim:

- verified full-structured-AST elaboration for the exact supported fragment;
- an independent syntax-directed surface judgment with a sound, complete, and
  deterministic executable checker;
- preservation from a surface derivation to pure lowering and actual core
  acceptance;
- supported-fragment reflection from canonical lowering plus actual core
  acceptance back to the independent surface judgment;
- exact preservation of authored obligations, retained attacks, reconstructed
  conclusions, and authored/core argument-question order in the forms stated
  above;
- production-ordered validation of authored roles, requested status IDs, and
  group IDs/members, with requested statuses (not all declared claims) feeding
  the finite core-check ground;
- genuine-binder alpha-lowering invariance and typed global-renaming
  equivariance under their explicit soundness hypotheses; and
- optional, independently defined direct/core claim lookup and
  direct/compiled observation coherence for extension semantics satisfying
  `Observation.AttackExtensional sem.spec`, with named grounded, complete,
  preferred, stable, and semi-stable corollaries that discharge that premise
  and preserve missing claims as `none`.

The paper must not claim:

- verified correctness of the concrete `.lara` parser;
- that every accepted core program has a source preimage;
- that a source preimage is unique or recoverable;
- that `elaborate ok` alone implies surface validity;
- that replay-significant identities are alpha-renamable; or
- that Haskell correctness follows from the Lean proof alone.

## Evaluation and Evidence

M5 succeeds only when all three evidence layers pass:

1. **Formal evidence.** The theorem-bearing Lean modules must build, and the
   axiom audit must report the public theorem families without proof holes or
   dependencies beyond `propext`, `Classical.choice`, and `Quot.sound`. This
   establishes the surface model's formal contracts; it does not establish
   properties of the shipped Haskell implementation.
2. **Cross-language conformance evidence.** The independent Haskell
   production-path emitter and Lean verified-model emitter must produce the
   same nonempty, ordered canonical rows for the finite manifest, including
   AST fingerprints, outcomes, core images, obligations, attacks, and
   observations. This connects the model to exercised shipped behavior; it
   remains finite conformance evidence, not parser or Haskell correctness.
3. **Regression evidence.** The pre-existing core bytes, verdicts,
   differential anchors, semantics/backend goldens, and generated core
   artifacts must remain unchanged. The M5 surface fixtures and their own
   seven-column golden intentionally advance together; the adapted before/after
   patch comparison below proves their generators introduce no further drift.
   This demonstrates that the repair did not silently change the frozen core
   contract.

No layer substitutes for another: Lean proof without cross-language evidence
does not validate the shipped path; matching emitters without the independent
surface theorems remain testing; and both are insufficient if the established
core bytes, verdicts, or artifacts drift.

The stable declaration map is in
`docs/paper-lean-name-map.md`. `lean/AxCheck.lean` imports every
theorem-bearing M5 module and audits the public theorem families against the
standard Lean axiom trio: `propext`, `Classical.choice`, and
`Quot.sound`. The complete evaluation command set is recorded below so this
durable contract does not depend on the retired implementation plan. These
command names do not replace the conceptual acceptance layers above.

```bash
(cd lean && lake build Lara.Surface.Syntax Lara.Surface.Binding \
  Lara.Surface.ValueBinding Lara.Surface.Comparison Lara.Surface.Check \
  Lara.Surface.Elaborate Lara.Surface.Correctness Lara.Surface.Observation \
  Lara.Examples.Surface)
(set -o pipefail; cd lean && lake env lean AxCheck.lean |
  ../scripts/check-axioms.sh)
cabal test lara-test --test-show-details=direct
cabal test all --test-show-details=direct
make presentation-parity
make surface-conformance
make surface-conformance-gate-test
bash scripts/differential.sh
bash scripts/admission-differential.sh
make semantics-goldens backend-deps-golden update-goldens update-differential
git diff --binary -- fixtures/surface test/surface-conformance.golden \
  > /tmp/m5-surface-intended-before.patch
cabal exec -- runghc scripts/gen-worked-examples.hs
cabal exec -- runghc --ghc-arg=-package --ghc-arg=lara \
  scripts/gen-corpus-units.hs
git diff --exit-code -- examples corpus-units
git diff --binary -- fixtures/surface test/surface-conformance.golden \
  > /tmp/m5-surface-intended-after.patch
cmp /tmp/m5-surface-intended-before.patch \
  /tmp/m5-surface-intended-after.patch
make ara-source-spans
ara check ara --json
```
