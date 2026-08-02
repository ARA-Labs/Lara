# Heuristics

## H01: Prove one generic frame-stream inverse before the recursive AST inverse
- **Rationale**: Framing every token as `UTF8_BYTE_LENGTH:PAYLOAD` reduces delimiter,
  Unicode, truncation, and trailing-input reasoning to one reusable
  `decodeFrames (renderFrames xs) = some xs` theorem. The Atom proof then reasons
  structurally over decoded fields instead of reparsing raw strings at every constructor.
- **Provenance**: ai-suggested
- **Sensitivity**: medium
- **Code ref**: ["lean/Lara/Strict.lean", "src/Lara/Strict/ND.hs"]

## H02: Separate executable matrices from soundness-facing proofs
- **Rationale**: Lean `native_decide` is convenient for external String evaluation but
  introduces generated axioms. Runtime matrices should remain executable `Bool` definitions
  enforced by `#guard`, so a false matrix fails the build without entering the theorem TCB;
  audited soundness theorems should cross `replay_iff` and construct `HasType` witnesses
  explicitly.
- **Provenance**: ai-suggested
- **Sensitivity**: high
- **Code ref**: ["lean/Lara/Strict.lean", "lean/Lara/Examples.lean", "lean/AxCheck.lean"]
- **Last revised**: 2026-07-25 (2026-07-25_002)

## H03: Store raw matcher bindings and normalize only at equality boundaries
- **Rationale**: A contrary matcher must remain exact for an arbitrary canonicalizer,
  not merely an idempotent one. Retaining the first raw ground term and applying
  `nfTerm canon` exactly once to it and the comparison term enforces repeated-variable
  equality without silently assuming `canon (canon s) = canon s`.
- **Provenance**: ai-suggested
- **Sensitivity**: high
- **Code ref**: ["lean/Lara/Attack.lean", "lean/Lara/Examples.lean"]

## H04: Retain proof-bearing support results across the attack pass
- **Rationale**: A whole-program checker should infer each declared support term
  exactly once, retain an index-aligned `List CheckedSupport`, and transport the
  cached proof to an attack source through a named structural-equality witness.
  This prevents diagnostic drift and duplicated backend replay while making the
  compile-boundary proof fields direct consequences of checker soundness.
- **Provenance**: ai-suggested
- **Sensitivity**: high
- **Code ref**: ["lean/Lara/Check/Program.lean", "lean/Lara/Check/Attack.lean"]

## H05: Keep executable recursion first-order and move dependent adequacy proofs beside it
- **Rationale**: Lean can accept a dependent proof-carrying recursion into an
  `.olean` while its C-code generation path still revisits and times out on the
  dependent proof terms. A first-order `Except` checker plus a proof-only
  companion module preserves executable code generation, exact
  soundness/completeness, and readable stage boundaries.
- **Provenance**: ai-suggested
- **Sensitivity**: high
- **Code ref**: ["lean/Lara/Check/Support.lean", "lean/Lara/Check/SupportProof.lean"]

## H06: Verify specified-outcome fixtures at generation time
- **Rationale**: A fixture generator that runs each generated artifact through the
  production pipeline and ABORTS on any specification mismatch makes the committed
  suite verified-by-construction — generation itself is the first experiment run
  (148/148 mutants matched their specified class/status on the first full
  generation, which would otherwise have silently mis-pinned the R7-vs-R13 cert
  boundary). Standing re-verification (MutationSpec / CorpusUnitsSpec freshness +
  expected-status pins) plus seeded or manifest-driven reproducibility then keep
  the suite honest without trusting the generation event. Reused for the T2
  corpus units: the generator fails loudly on parse/elaborate/replay errors and
  the spec cross-checks manifest expected_status against computed verdicts.
- **Sources**: ["148 ← plans/2026-08-01-m5-mutation-suite-worked-cases.md:97 «Generated suite: **148 mutants** over 8 accept bases (A, B, E1–E5, S1), seed» [result]", "zero mismatches ← plans/2026-08-01-m5-mutation-suite-worked-cases.md:99 «decodeCheckInputFile` — zero specification mismatches on the first full» [result]"]
- **Status**: active
- **Provenance**: ai-suggested
- **Sensitivity**: medium
- **Code ref**: ["scripts/gen-mutants.hs", "scripts/gen-corpus-units.hs", "test/MutationSpec.hs", "test/CorpusUnitsSpec.hs"]

## H07: Audit gate coverage of the mutation suite before trusting any ablation number
- **Rationale**: An ablation over a mutation suite measures nothing unless the
  suite contains inputs that actually exercise the ablated check. The pre-T6
  suite had zero mutants reaching the obligation gate — its open-obligation
  operator dropped a discharge without leaving a hole, so those mutants were
  caught earlier by an always-on rule (R5 Uncovered) — which would have made the
  no-cq ablation report a vacuous null (0 missed of 0 reachable) that reads like
  a passing result. The fix belongs in the SUITE (add an operator that seeds
  inputs reaching the gate — `OpHoleObligation`, 18 mutants, suite 340→358), not
  in widening the ablation to reach into the kernel. Confirm each ablated check
  has ≥1 reaching input before reporting its miss rate.
- **Sources**: ["0 reaching / 340 ← trace/exploration_tree.yaml:N97.result «the pre-T6 suite had ZERO inputs reaching the obligation gate (open-obligation fires R5 Uncovered instead)» [result]", "18 / 340→358 ← trace/exploration_tree.yaml:N97.result «18 new mutants, additions-only, suite 340->358, first cross-driver coverage of the IncompleteArgument reject path» [result]"]
- **Status**: active
- **Provenance**: ai-suggested
- **Sensitivity**: high
- **Code ref**: ["src/Lara/Mutate.hs", "test/AblationSpec.hs", "scripts/measure.hs"]
