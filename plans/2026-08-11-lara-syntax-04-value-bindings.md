# lara-syntax@0.4 Value Bindings Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use `subagent-driven-development` (recommended) or `executing-plans` to implement this plan task-by-task. Use `test-driven-development` for every behavior change and `verification-before-completion` before reporting completion. Track each checkbox as work proceeds.

**Goal:** Add program-level named ground-term bindings and natural-language interpolation so an author states each repeated value once, while elaboration still produces the exact `lara-core@0.2` `Unit` that an equivalent unbound program produces.

**Architecture:** Widen only the presentation layer. `Program` carries an ordered list of typed `ValueBinding`s. `Lara.Syntax` parses and canonically prints `let name = term` lines after the program header. A new `Lara.Elaborate.ValueBinding` pass validates the binding environment against the policy's strict many-sorted signature, substitutes only nullary term occurrences, expands `{name}` and existing `{cell leaf}` natural-language forms, removes the binding table, and then hands the ordinary presentation program to the existing comparison expansion. Mirror the widened presentation AST and private structured codec in Lean, including the cross-language shape guard. Do not change `Unit`, `.core.sexp`, replay identity, checking, or any strict backend.

**Tech stack:** Haskell/GHC 9.6+, QuickCheck, Lean 4.32.0/Lake, the existing `Lara.Syntax`, `Lara.Elaborate`, `Lara.Presentation`, `AxCheck`, and presentation-parity tooling.

---

## 1. Background

PR #102 closed result 12 on merged `main` (`56decad`): Haskell and Lean now model the complete live `lara-syntax@0.3` presentation shape, Lean proves its private structured-codec round trip, and a 68-row compiler-checked inventory rejects cross-language drift. Both hosted Haskell and Lean checks pass on that merge.

The remaining surface deliverable is issue #88b / plan D7 in `plans/2026-08-08-lara-syntax-03-surface.md`. The earlier blocker is gone: PR #97 shipped strict many-sorted `Sigma` as `lara-core@0.2`. A misspelled bare value name can therefore fail closed as an undeclared constructor rather than becoming a silently accepted constant.

Today a value such as `0.74`, `sys_new`, or `imagenet_val` is copied into several term positions and often into claim prose. The copies can disagree while each line remains locally well formed. Existing `{cell e2}` interpolation helps when prose should quote a measured leaf, but it does not let the author name a general ground term reused across claims, leaves, comparison setup, and prose.

---

## 2. Motivation

The feature removes transcription, not proof obligations.

```lara
let candidate       = sys_new
let baseline        = sys_base
let candidate_score = 0.74
let baseline_score  = 0.71

claim c1
  nl      = "{candidate} outperforms {baseline} on ImageNet-val accuracy ({candidate_score} vs {baseline_score})"
  formal  = better(candidate, baseline, accuracy, imagenet_val)
```

The elaborator replaces the four bare binding names with their declared ground terms and renders the same terms in `nl`. The strict checker receives no binding object. A malformed value still fails the declared `Sigma`; a binding used at a wrong sort still fails R2 after substitution; certificates stay opaque and unchanged.

This is worth a syntax-version bump because it changes the live `Program` shape and concrete `.lara` grammar. It is not a core-version bump because the expanded `Unit` and every checker boundary remain unchanged.

---

## 3. Scope and Non-goals

### In scope

- `lara-syntax@0.4`, additive over `@0.3`.
- Program-header `let valueName = term` declarations.
- Bare-name substitution in every program-side ground-term position.
- `{valueName}` interpolation in ordinary claim `nl` and comparison sub-claim `nl`.
- Existing `{cell leafId}` interpolation and `{{` / `}}` literal-brace behavior.
- Strict duplicate, reserved-name, constructor-collision, malformed-value, and missing-interpolation diagnostics.
- Complete Haskell/Lean presentation parity and round-trip coverage.
- Migration of `examples/S2` and `examples/S5` as higher-is-better and lower-is-better acceptance exemplars.

### Explicit non-goals

- Named certificate premise slots such as `(prem e1)`. `Cert` payloads remain opaque by design; that needs a separate layering decision.
- The optional plain-`arg` theta-inference rider from `TODOS.md`.
- Recursive bindings, binding-to-binding references, local scopes, shadowing, imports, destructuring, or expressions.
- Substitution in policy declarations, identifier namespaces, source paths, binding metadata, certificate `SExpr` payloads, attack paths, measurand IDs, dataset IDs, rule IDs, claim IDs, or leaf IDs.
- New string-literal term syntax. A binding RHS uses the existing surface-representable `term` grammar; `Term.TStr` remains outside the concrete `.lara` surface.
- Any change to `Unit`, `Lara.Wire`, `checkUnit`, `.core.sexp`, core replay identity, strict backends, frozen measurements, or generated mutation semantics.

---

## 4. Decisions Locked by This Plan

### D1. Grammar position and canonical form

Bindings appear after the fixed program header and before the first declaration:

```text
program      ::= artifactHeader valueBinding* declaration*
valueBinding ::= "let" valueName "=" term
```

The parser rejects a `let` after the first declaration. The printer emits bindings in source order, one per line, followed by one blank line before declarations when the list is non-empty. Legacy programs parse with an empty binding list and print exactly as before.

`cell` is reserved from `valueName` because `{cell leafId}` already owns that natural-language directive head. Other tokens use the existing `ident` lexical class; semantic collisions are handled by D4.

### D2. Typed presentation AST

Add to `src/Lara/AST.hs`:

```haskell
newtype ValueName = ValueName String
  deriving (Eq, Ord, Show)

data ValueBinding = ValueBinding
  { valueName :: ValueName
  , valueTerm :: Term
  }
  deriving (Eq, Show)
```

Add `programValueBindings :: [ValueBinding]` between `programBackends` and `programDecls`. The list retains declaration order for deterministic printing and diagnostics. `ValueName` is a distinct namespace; do not reuse `FunSym`, `Param`, or a raw `String`.

Every existing non-surface `Program` construction site supplies `[]`. Expected sites, confirmed from the current symbol references, are:

- `src/Lara/Examples.hs`
- `src/Lara/Negatives.hs`
- `test/AdmissionSpec.hs`
- `test/ClaimSupportSpec.hs`
- `test/MechReviewSpec.hs`
- `test/ReplaySpec.hs`
- `test/SyntaxSpec.hs`
- `scripts/presentation-shape.hs`

Before editing the exported `Program` symbol, run LSP references again and migrate any additional live callsite reported by the current checkout.

### D3. Flat, simultaneous, non-recursive environment

Build one `Map ValueName Term` from the authored list. Binding right-hand sides are validated as written and are never expanded through the environment. This makes the semantics simultaneous and order-independent while preserving declaration order for printing.

For example:

```lara
let x = y
let y = 0.74
```

is not a chain. `y` in `x`'s RHS is an ordinary constructor occurrence and must itself be declared by `Sigma`; the second binding does not rewrite it.

### D4. Fail-closed name and value checks

Before substitution:

1. reject duplicate `ValueName`s, including hand-constructed AST values that bypass the parser;
2. reject the reserved `ValueName "cell"` even for a hand-constructed AST;
3. reject any `ValueName n` for which `lookupCon policySigma (FunSym n)` succeeds, regardless of constructor arity;
4. run `sortOf policySigma` on every RHS and reject its exact `SortFault` at that binding.

The collision rule prevents a binding from hijacking an already-valid constructor occurrence. Strict `Sigma` remains the fallback for unbound bare terms: an unbound nullary term is left untouched and the existing checker rejects it as R2 if it is undeclared. There is no permissive or guessed fallback.

A RHS has no declared expected sort by itself; `sortOf` proves it is a valid ground term and obtains its result sort. After substitution, run `sortCheckProp policySigma` over every ordinary claim formal before any unqueried or unsupported claim can disappear during lowering; report a dedicated claim-located binding-use sort error. Surviving leaves, argument substitutions, and generated comparison structure still reach the existing R2 pass. This closes the otherwise-valid escape where a wrong-sort value appears only in an unqueried, unsupported claim.

### D5. Substitution surface

Replace exactly `TCon (FunSym n) []` when `ValueName n` exists in the environment. Recurse into the arguments of non-nullary `TCon`, but never replace a constructor head. This preserves the term grammar and avoids treating arbitrary text as an identifier substitution.

Traverse every program-side term-bearing field:

- `Leaf.leafProp`;
- `Claim.claimFormal`;
- `Arg.argTerm`, recursively through every `SRule.srSubst` term and nested premise/discharge support term;
- `Comparison.cmpConclusion`.

`Comparison` expansion runs after this pass, so generated claims, theta vectors, and certificates are derived from already-substituted source values. No second binding pass is needed.

After successful substitution and `nl` expansion, set `programValueBindings = []`. The post-expansion presentation program can therefore be compared directly with an equivalent hand-written unbound program. This remains a deliberately one-way phase boundary: escaped literal braces have become semantic prose, so the pass must run exactly once rather than claim idempotence.

### D6. Natural-language interpolation

Extend the brace grammar to:

```text
directive ::= "{" "cell" leafId "}"
            | "{" valueName "}"
            | "{{"
            | "}}"
```

- `{cell e2}` retains its current premise-cell validation and `renderDecimal` behavior.
- `{candidate_score}` looks up the binding and renders its RHS with `prettyTerm`.
- `{missing}` is syntactically a value reference and becomes a located elaboration error naming the claim and missing `ValueName`.
- `{cel e2}` and other multi-token unknown directive heads remain located parse errors; they must not silently become literal prose.
- `{{` and `}}` still produce literal braces.

Apply this to both `Claim.claimNl` and `ComparisonClaim.ccNlRaw`. Expose one consuming `expandValueBindings :: Sigma -> Program -> Either ElabError Program` API from the new module. It validates, substitutes every term field, validates all substituted claim formals, expands both cell and value references exactly once, and clears the binding table. There is no NL-only public helper: it would leave formal terms inconsistent with checked queries and could reinterpret a literal brace on a second call.

### D7. One ordered surface pipeline

Create `src/Lara/Elaborate/ValueBinding.hs`. `Lara.Elaborate.Comparison.expandSurfaceProvenance` calls its full pass before duplicate comparison checks and comparison generation:

```text
parsed Program
  -> validate bindings against Policy.policySigma
  -> substitute all authored term positions
  -> expand claim NL ({name}, {cell leaf}, brace escapes)
  -> clear programValueBindings
  -> expand comparison blocks
  -> resolve labels/attacks and lower to Unit
```

Move brace-expansion ownership out of `Lara.Elaborate.Comparison`. Remove the ordinary-claim and comparison-sub-claim calls to `expandClaimNl`: D7 has already expanded both before comparison generation, and a second pass could reinterpret a literal brace produced from `{{` / `}}`. Do not leave a compatibility re-export.

### D8. Dedicated diagnostics

Add explicit `ElabError` constructors and `elabErrorMessage` cases for:

- duplicate value binding;
- reserved value name, including a hand-built `ValueName "cell"`;
- value name colliding with a declared constructor;
- ill-sorted binding RHS, retaining the `SortFault`;
- ill-sorted substituted claim formal, naming the claim and retaining the `SortFault`;
- missing value referenced by a specific claim's `nl`.

Parser errors still cover reserved source `cell` at declaration time, duplicate source declarations at the second declaration, malformed RHS syntax, and late `let` placement. Tests assert constructor payloads and exact stable message fragments at the public rendering boundary. Do not expose raw `show` output as the author-facing diagnostic.

### D9. Version and parity contract

`lara-syntax@0.4` still decodes to `lara-core@0.2`. Mirror D2 in `lean/Lara/Presentation.lean`:

```lean
structure ValueName where
  mk :: (val : String)
  deriving DecidableEq

structure ValueBinding where
  name : ValueName
  term : Term

structure Program where
  ...
  backends : List BackendEntry
  valueBindings : List ValueBinding
  decls : List Decl
```

Add private structured codecs and round-trip lemmas for `ValueBinding`; update `Program` codec/proof and audit every new theorem in `lean/AxCheck.lean`.

Update both presentation-parity witnesses:

- exact one-field `ValueName` structure and constructor anchor;
- exact `ValueBinding` constructor signature and fields;
- widened six-field `Program` signature;
- exhaustive destructuring and normalized rows;
- scoped field-name normalization assertions for Haskell `valueName` / `valueTerm` / `programValueBindings` versus Lean `name` / `term` / `valueBindings`.

The normalized inventory grows from 68 to 70 rows (`ValueName` and `ValueBinding` are new rows; `Program` changes in place). The parity gate must continue to derive and reject a stale row count rather than trusting the literal 70.

### D10. One semantic presentation value for secondary consumers

The once-expanded `Program` is a semantic artifact of elaboration, not something loaders may reconstruct independently. Add a package-internal elaboration entry point that returns `(Unit, [GeneratedArg], Program)`, where the `Program` is the exact post-binding, post-comparison value used to lower that `Unit`. Preserve existing `elaborate` and `elaborateWithProvenance` APIs as projections so current callers do not gain accidental coupling.

`Lara.ClaimSupport.Load` must pass this semantic `Program` to `computeUnit` instead of the raw parsed source; its leaf, argument, claim, and prose parity checks otherwise compare bound syntax with expanded core. `Lara.MechReview.Load` must likewise load the policy, invoke this same elaboration entry point once, compare the produced `Unit` to the decoded core as its existing exactness boundary requires, and pass the returned semantic `Program` to review rendering. Update the two renderer/test callsites for the loader's policy-path input. Neither loader calls `expandValueBindings` or comparison expansion independently.

---

## 5. Implementation

### Task 1: Add red acceptance tests for the source contract

**Files**

- Create: `test/ValueBindingsSpec.hs`
- Modify: `test/Spec.hs`
- Modify: `lara.cabal`

- [ ] Add a focused test group `valueBindingSpecProps` and register it in the one existing `lara-test` runner.
- [ ] Define paired inline programs over one small strict policy: one uses `let` bindings in leaves, a claim, an `SRule` theta, a nested constructor, a comparison conclusion, and `nl`; the other writes the expanded terms directly.
- [ ] First assertion: the bound source parses. Run `cabal test lara-test --test-show-details=direct` and record the expected RED parse failure on `let`.
- [ ] Add parser-level negative cases for duplicate names, reserved `cell`, malformed RHS, late `let`, and malformed multi-token brace directives. These remain red until Task 2.
- [ ] Add an explicit parser regression that one-token `{cell}` is rejected as a malformed cell directive; the reserved directive head must not enter the value-reference path.
- [ ] Keep fixtures small and self-contained; do not copy a full worked example into the test module.

### Task 2: Widen the Haskell AST and concrete codec

**Files**

- Modify: `src/Lara/AST.hs`
- Modify: `src/Lara/Syntax.hs`
- Modify: `src/Lara/Examples.hs`
- Modify: `src/Lara/Negatives.hs`
- Modify: `test/AdmissionSpec.hs`
- Modify: `test/ClaimSupportSpec.hs`
- Modify: `test/MechReviewSpec.hs`
- Modify: `test/ReplaySpec.hs`
- Modify: `test/SyntaxSpec.hs`

- [ ] Add and export `ValueName`, `ValueBinding`, and `programValueBindings` exactly as D2 specifies.
- [ ] Re-run LSP references on `Program`; update every constructor atomically. Prefer named record construction; keep the positional constructor witness in `MechReviewSpec` only if that test intentionally checks positional arity, otherwise convert it to named fields.
- [ ] Add a `valueBindingP` and a seen-set parser loop before `declsP`. Reject duplicates at the second `let`, reject `cell`, and leave `let` in declaration position as a located syntax error.
- [ ] Print bindings deterministically in authored order and preserve legacy output byte-for-byte when the list is empty.
- [ ] Extend `nlStringLit` lexical validation to admit one-token `{valueName}` while preserving strict errors for unknown multi-token directives and unmatched braces.
- [ ] Extend `SyntaxSpec.genProgram` with duplicate-free value names and surface-representable RHS terms. Add explicit parse/print properties for empty and non-empty binding tables.
- [ ] Run `cabal test lara-test --test-show-details=direct`. Parser and round-trip tests should be GREEN; semantic identity tests remain red because no expansion exists.

### Task 3: Implement validation, substitution, and NL expansion

**Files**

- Create: `src/Lara/Elaborate/ValueBinding.hs`
- Modify: `src/Lara/Elaborate/Comparison.hs`
- Modify: `src/Lara/Elaborate/Error.hs`
- Modify: `src/Lara/MechReview/Load.hs`
- Modify: `src/Lara/Elaborate/Internal.hs`
- Modify: `src/Lara/ClaimSupport/Load.hs`
- Modify: `test/ClaimSupportSpec.hs`
- Modify: `test/MechReviewSpec.hs`
- Modify: `scripts/render-reviews.hs`
- Modify: `lara.cabal`
- Modify: `test/ValueBindingsSpec.hs`
- Modify: affected `test/ElaborateSpec.hs` NL cases

- [ ] Add the dedicated errors from D8 and stable renderer text before implementing the pass.
- [ ] Assert stable author-facing `elabErrorMessage` fragments for all six new error classes: duplicate binding, reserved name, constructor collision, ill-sorted RHS, ill-sorted substituted claim, and missing value interpolation.
- [ ] Build the environment once with `Data.Map.Strict`; reject duplicates, reserved `cell`, and declared-constructor collisions before traversal.
- [ ] Validate every RHS with `sortOf policySigma`, including unused bindings. After substitution, validate every ordinary claim formal with `sortCheckProp policySigma`, including unsupported and unqueried claims that lowering would otherwise erase.
- [ ] Implement small total traversals for `Term`, `Prop`, `SupportTerm`, `Decl`, and nested `ComparisonClaim`. Do not traverse non-term identifier fields or `Cert` payloads.
- [ ] Cover substitution through a nested `SRule` premise and discharge explicitly, while asserting that an adjacent `Cert` payload is byte-for-byte untouched.
- [ ] Expand `{name}`, `{cell leaf}`, and escaped braces in one left-to-right NL pass. Preserve the existing exact numeric rendering for premise cells; use `prettyTerm` for value bindings.
- [ ] Clear `programValueBindings` after the full pass and make the no-binding path preserve existing behavior.
- [ ] Call `expandValueBindings` exactly once at the start of `expandSurfaceProvenance`; remove the later ordinary-claim and comparison-sub-claim NL calls and the old `expandClaimNls` API. Add a literal-brace regression that would fail if interpolation ran twice.
- [ ] Add the package-internal D10 elaboration entry point returning the exact semantic `Program` beside `Unit` and provenance; preserve `elaborate` and `elaborateWithProvenance` as projections. Update `Lara.ClaimSupport.Load` and `Lara.MechReview.Load` plus their callers to consume that returned program, and assert their core/surface parity with bindings in a load-bearing leaf, argument theta, claim formal, and claim NL.
- [ ] Assert the paired bound/unbound programs produce equal post-expansion `Program`s, equal `Unit`s, and byte-identical `printSExpr . encodeUnit` output.
- [ ] Add focused negatives for hand-built duplicate/reserved AST bindings, constructor collision, undeclared/wrong-arity/wrong-sort RHS, undeclared `{name}`, wrong-sort use in an unsupported and unqueried claim, wrong-sort surviving use, and non-recursive RHS behavior.
- [ ] Assert a legacy program with `programValueBindings = []` has unchanged expansion and `Unit` bytes.
- [ ] Run `cabal test lara-test --test-show-details=direct`; all Haskell feature tests must be GREEN.

### Task 4: Restore Lean presentation parity immediately

**Files**

- Modify: `lean/Lara/Presentation.lean`
- Modify: `lean/AxCheck.lean`
- Modify: `scripts/presentation-shape.hs`
- Modify: `lean/Lara/PresentationParity.lean`
- Modify: `lean/Lara/PresentationParityMain.lean` only if its expected inventory interface changes

- [ ] Add `ValueName`, `ValueBinding`, and the widened `Program` in Lean with the exact field order in D9.
- [ ] Add the `ValueName` one-field string codec/round-trip theorem plus `sxValueBinding`, `unValueBinding`, and its helper round-trip lemma; thread the binding list through `sxProgram`, `unProgram`, and `parse_printProgram`.
- [ ] Add every new theorem to `AxCheck.lean`. Keep proofs `sorry`-free and within the existing standard-axiom policy.
- [ ] Update Haskell exact signatures, field witnesses, eliminators, type-row metadata, selector normalization, and generic row-count tripwire.
- [ ] Update Lean exact signatures, Meta field checks, normalized rows, and expected count. Do not weaken exhaustiveness or compare only arity.
- [ ] Run `make presentation-parity`; require both runtimes to build and the normalized 70-row inventories to compare byte-exactly.
- [ ] Run `cd lean && lake build && ../scripts/test-check-axioms.sh && lake env lean AxCheck.lean | ../scripts/check-axioms.sh`.

### Task 5: Migrate two worked examples and active documentation

**Files**

- Modify: `examples/S2/example.lara`
- Modify: `examples/S5/example.lara`
- Modify: `docs/lara-surface-grammar.md`
- Modify: `docs/spec.md`
- Modify: `README.md`
- Modify: `docs/mechanization-plan.md`
- Modify: `lean/README.md`
- Modify: `lean/Lara.lean`
- Modify: current-surface headers/comments in `src/Lara/Syntax.hs`, `src/Lara/Elaborate/Internal.hs`, `src/Lara/Elaborate/Error.hs`, `test/SyntaxSpec.hs`, and `lean/Lara/Presentation.lean`
- Modify: `TODOS.md`
- Preserve explicitly historical `@0.3` references: grammar Appendix B, comments tied to comparison/premise-label introduction, and dated rejection-surface evidence.

- [ ] Add bindings for candidate, baseline, metric, dataset, candidate score, and baseline score in S2 and S5. Use them in ground-term positions; keep typed measurand/dataset selector fields in the `comparison ... on ... @ ...` line unchanged.
- [ ] Use `{candidate}`, `{baseline}`, `{candidate_score}`, and `{baseline_score}` in claim prose so expanded text is byte-for-byte the previous prose.
- [ ] Update the examples' explanatory comments from the `@0.3` comparison migration to the additive `@0.4` value-binding migration without changing their scientific claim or expected verdict.
- [ ] Record checksums of S2/S5 `example.core.sexp` and `expected.json`, run `cabal exec -- runghc scripts/gen-worked-examples.hs`, and require those four checksums to remain unchanged.
- [ ] Run the generator a second time and require all generated checksums to remain unchanged (idempotence).
- [ ] Change the grammar document's live version to `lara-syntax@0.4`, retain Appendix B as the historical `@0.3` contract, and add Appendix C with D1-D6, examples, errors, and the explicit opaque-certificate boundary.
- [ ] Update `docs/spec.md` §2.1 and `lean/README.md` result 12 to the live `@0.4` structured shape while keeping `lara-core@0.2` fixed.
- [ ] Mark #88b/D7 complete in `TODOS.md`; leave named certificate slots and the theta rider explicitly deferred rather than silently deleting them.

### Task 6: Evaluate the complete contract
- [ ] **Secondary consumers:** run focused claim-support and mechanical-review tests; require both to use the once-expanded semantic `Program`, preserve literal braces, and match the decoded core.

- [ ] **Authoring reduction:** count repeated authored occurrences in migrated S2/S5 and report the before/after counts for the six bound values. This is descriptive evidence, not a semantic gate.
- [ ] **Round trip:** QuickCheck covers `parseProgram . printProgram == Right` for generated programs with empty/non-empty binding tables; Lean covers the widened private structured codec.
- [ ] **Exact expansion:** paired bound/unbound tests compare expanded `Program`, `Unit`, and rendered `encodeUnit` bytes.
- [ ] **Fail closed:** every D8 error and strict-Sigma fallback has a focused regression.
- [ ] **CLI smoke:** run `cabal run exe:lara -- check examples/S2/example.lara` and `examples/S5/example.lara`; require acceptance, exit 0, and the existing expected statuses.
- [ ] **Source/core replay equality:** run the CLI on each migrated `.lara` and its sibling `.core.sexp`; compare verdict stdout byte-for-byte and require equal exit codes.
- [ ] **Haskell gate:** `cabal build all` then `cabal test all --test-show-details=direct`.
- [ ] **Presentation gate:** `make presentation-parity`.
- [ ] **Lean gate:** `cd lean && lake build`, then the complete axiom audit.
- [ ] **Python auxiliaries:** `uv run --no-project python -m unittest discover -s elaborator -v` and `python3 -m unittest scripts/test_freeze_bundle.py -v`.
- [ ] **Replay/tamper/differential gates:** run `test/walking-skeleton-golden.sh`, `scripts/replay.sh`, `scripts/test-replay-tamper.sh`, `scripts/differential.sh`, and `scripts/admission-differential.sh` exactly as `.github/workflows/ci.yml` does.
- [ ] **Freshness:** verify no generated core, JSON, manifest, frozen measurement, or bundle byte changed. If any does, stop and diagnose; a binding-only surface change has no legitimate core drift.
- [ ] **Hosted CI:** after opening the PR, require both `Haskell (cabal build + test)` and `Lean (lake build)` to pass on the final head.

---

## 6. Evaluation Matrix

| Property | Primary evidence | Failure caught |
| --- | --- | --- |
| Concrete syntax is lossless | Haskell QuickCheck + explicit parser fixtures | printer drops/reorders bindings; parser ambiguity |
| Structured AST stays cross-language complete | Lean round trip + 70-row parity gate | Haskell-only or Lean-only field/type drift |
| Bindings are pure sugar | bound/unbound expanded `Program`, `Unit`, and wire-byte equality | substitution changes checker input |
| Values are well formed | RHS `sortOf` negatives | unused or malformed value disappears before R2 |
| Use sites remain typed | post-substitution claim validation + existing R2 | unqueried/unsupported claim or surviving use bypasses contextual sort checks |
| Bare names cannot hijack constants | constructor-collision regression | valid constant silently changes meaning |
| Missing names fail loudly | `{missing}` diagnostic + unbound-term R2 | typo remains prose or permissive constant |
| Existing interpolation remains strict | `{cell e}`, braces, `{cel e}` tests | regression in `@0.3` stale-prose protection |
| Certificates remain opaque | fixture with unchanged `Cert` payload + core bytes | accidental substitution inside backend language |
| Secondary presentation consumers stay exact | claim-support + mechanical-review regressions | raw bound syntax is compared with expanded core; NL is expanded twice |
| Core and verdict are unchanged | S2/S5 checksums, CLI source/core comparison, differential | surface migration perturbs semantics or replay |
| Generation is deterministic | two consecutive generator runs | non-canonical or stateful output |

---

## 7. Completion Criteria

The milestone is complete only when all of the following hold:

1. S2 and S5 each declare repeated terms once and use those names in formal and prose positions.
2. Equivalent bound and unbound sources elaborate to byte-identical `lara-core@0.2` `Unit`s.
3. Duplicate, reserved, colliding, malformed, missing, non-recursive, and wrong-sort cases fail at the specified boundary with stable diagnostics, including an unsupported and unqueried ill-sorted claim.
4. Legacy `programValueBindings = []` sources retain their prior parse/print and elaboration bytes.
5. Claim-support and mechanical-review consume the exact once-expanded semantic `Program`; no raw/expanded mismatch or second interpolation path remains.
6. Haskell and Lean describe the same widened `Program` with distinct `ValueName` namespace types; the 70-row parity gate and complete axiom audit pass.
7. S2/S5 core and expected-JSON checksums do not move, generator reruns are idempotent, and the full local/hosted CI gates pass.
8. Active docs name `lara-syntax@0.4`; historical `@0.3` material remains accurately labeled.
9. #88b/D7 is closed. Named certificate slots and theta inference remain separate, explicit follow-up decisions.

## 8. Engineering Review Addendum

### What already exists

- `Lara.Syntax` already owns the complete program parser/printer and strict `nl` brace lexer; Task 2 extends that single codec rather than adding another parser.
- `Lara.Elaborate.Comparison` already owns one-way surface expansion and exact `{cell leaf}` rendering; Task 3 moves the shared brace pass to `Lara.Elaborate.ValueBinding` and leaves comparison generation downstream.
- `Lara.Sigma.sortOf` and `sortCheckProp` already implement the strict many-sorted ground judgments; the binding pass reuses them rather than creating a second type checker.
- `Lara.Elaborate.Internal.elaborateWithProvenance` already derives `Unit` and comparison breadcrumbs from one semantic program; D10 adds a package-internal three-result form and preserves existing projections.
- `Lara.ClaimSupport.Load` and `Lara.MechReview.Load` already enforce surface/core parity for secondary artifacts; they will consume the exact semantic `Program` instead of reconstructing expansion.
- `lean/Lara/Presentation.lean` and both presentation-parity witnesses already enforce distinct identifier namespaces, codec round trips, exhaustive fields, and a derived row-count tripwire.

### NOT in scope

- Certificate premise-name syntax or substitution inside opaque `Cert` payloads: this requires a separate backend-layer contract.
- Plain-`arg` theta inference: independent authoring sugar with different ambiguity rules.
- Recursive, local, imported, shadowed, destructured, or expression bindings: the feature is intentionally one flat simultaneous environment.
- Substitution in policy declarations, identifiers, paths, metadata, attacks, selector IDs, or certificate S-expressions: none are ground-term occurrence positions.
- New `Term.TStr` concrete syntax: value RHS terms remain limited to the existing surface grammar.
- Any checker, wire, replay-identity, strict-backend, measurement, or mutation-semantics change: `lara-core@0.2` remains byte-stable.

### Reviewed data flow

```text
raw .lara Program
  -> parse ordered bindings and strict braces
  -> validate duplicate/reserved/colliding names and every RHS
  -> substitute all authored ground-term positions
  -> validate every substituted ordinary claim
  -> expand value/cell/escaped-brace NL exactly once
  -> clear bindings
  -> expand comparisons
  -> semantic Program --------------------+-> claim-support / mechanical review
  -> lower to unchanged Unit -------------+-> exact core parity check
```

### Failure modes and coverage

| Failure | Handling | Focused evidence |
| --- | --- | --- |
| Duplicate, reserved, or constructor-colliding name | located parser or `ElabError`; no environment built | source and hand-built AST negatives |
| Invalid or unused RHS | exact retained `SortFault` | undeclared, wrong-arity, and wrong-sort RHS negatives |
| Wrong-sort use only in an erased claim | claim-located sort error before lowering | unsupported, unqueried claim regression |
| Missing value or malformed directive | claim-located elaboration or parse error | `{missing}`, `{cell}`, `{cel e}` regressions |
| Literal brace reinterpreted by a second pass | no NL-only API; consuming pass clears bindings | `{{name}}` one-pass regression |
| Secondary consumer compares raw source with expanded core | exact semantic `Program` returned with the `Unit` | claim-support and mechanical-review parity tests |
| Certificate payload accidentally rewritten | traversal excludes `Cert` | adjacent payload byte-equality regression |
| Haskell/Lean shape drift | distinct Lean `ValueName`, codecs, exhaustive 70-row inventory | parity and axiom gates |
| Generated example or replay drift | hard checksum and stdout equality failure | double generation, source/core CLI, differential gates |

### Worktree parallelization

Sequential implementation, no parallelization opportunity. Tasks 1-4 form one dependency chain through the same `Program` shape and elaboration modules. Task 5 depends on the completed codec and parity contract; Task 6 evaluates the integrated branch. Parallel implementers would either edit the same modules or validate an unstable intermediate syntax.

### Implementation Tasks

- [ ] **T1 (P2)** — Add nested support-term, certificate-opacity, diagnostic-renderer, and reserved-`cell` regressions.
- [ ] **T2 (P1)** — Validate every substituted ordinary claim before lowering can erase it.
- [ ] **T3 (P1)** — Replace the NL-only helper with one consuming value-binding pass.
- [ ] **T4 (P1)** — Return the exact semantic `Program` beside `Unit` and provenance for secondary consumers.
- [ ] **T5 (P1)** — Migrate claim-support and mechanical-review loaders to the shared semantic program.
- [ ] **T6 (P1)** — Mirror `ValueName` as a distinct Lean one-field structure with codec and parity witnesses.
- [ ] **T7 (P2)** — Revalidate reserved `cell` for hand-built AST values.
- [ ] **T8 (P2)** — Preserve frozen example, replay, differential, and generated-artifact bytes through the full gate.

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | -- | Not required for this bounded syntax feature |
| Codex Review | `/codex review` | Independent 2nd opinion | 1 | ISSUES FOLDED (Claude fallback) | 5 findings; all accepted into D4, D6-D10, and Tasks 3-4 |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | CLEAR (PLAN) | 8 issues, 0 critical gaps, 0 unresolved |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | -- | No UI scope |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | -- | Not required |

- **CROSS-MODEL:** The independent reviewer found five repository-specific gaps; all five recommendations were accepted and integrated without narrowing the atomic syntax-version cutover.
- **VERDICT:** ENG CLEARED — ready to implement.

NO UNRESOLVED DECISIONS
