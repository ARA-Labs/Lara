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
- **Sources**: ["148 → 295 seeded mutants over 8 accept bases (A, B, E1–E5, S1), then the frozen 358→360 suite ← docs/m5-freeze-checklist.md", "zero specification mismatches on the first full sweep ← test/MutationSpec.hs"]
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

## H08: Filter declarations and derived values as one aligned view
- **Rationale**: When a production transformation selects source declarations but checks or proves properties about values derived from them, pair each value with its source identity before filtering, or filter two already-aligned lists in lockstep. Re-resolving after filtering or matching derived values by structural equality creates an identity seam: duplicate terms can collapse distinct declarations, and the proof may describe a different AF from the checker. The quarantine bridge uses indexed argument pairs and aligned raw/resolved attack lists, yielding both the exact checked lists and their subset/lookup witnesses by construction.
- **Status**: active
- **Provenance**: ai-suggested
- **Sensitivity**: high
- **Code ref**: ["lean/Lara/BlockedProgram.lean", "lean/Lara/Driver.lean", "src/Lara/Blocked.hs"]

## H09: Make the trusted wrapper the only public way to reach its input
- **Rationale**: When a wrapper enforces a policy that its input type cannot carry — an admission table checked over a `Program`+`Policy` before lowering, not a property of the resulting `Unit` — the enforcement is exactly as narrow as the module's export list. Any other exported function that produces the same input is an equal-authority entry point, and documenting it as "the unsafe one" does not close it. Move the bare producer out of the public module into an `.Internal` escape hatch so the wrapper is the only public path, and keep the raw-wire front door (which has no policy to enforce) separately legitimate. `Lara.Elaborate` now exports only `prepareSource`/`runSourceCheck`; the admission-free lowering lives in `Lara.Elaborate.Internal` for tests and golden generators that study the lowering itself.
- **Status**: active
- **Provenance**: ai-suggested
- **Sensitivity**: high
- **Code ref**: ["src/Lara/Elaborate.hs", "src/Lara/Elaborate/Internal.hs", "lara.cabal"]

## H10: Export a decoder's well-formedness decision as a proof, not a boolean
- **Rationale**: A front door that decides an invariant and then discards the decision forces every downstream consumer to re-decide it or silently assume it. Return the invariant instead: `firstDup xs [] = none → xs.Nodup` turns the wire decoder's R14 duplicate-argument-id rejection into a `Decoded.argIdsNodup` field, which the admission carrier (`AlignedAttacks.ids_nodup`) transports into the model where it is load-bearing. It is load-bearing because retention is decided per argument row while attacks are filtered by endpoint *id*: without uniqueness a surviving duplicate keeps an id present after the resolved row was pruned, so the prune retains an attack whose semantic source is gone. With the proof carried, kept id and kept row coincide (`lookupArg_of_mem_nodup`, `retained_attack_source_retained`). Related to [H08]: H08 aligns declarations with derived values, H10 supplies the uniqueness that makes id-based alignment exact.
- **Status**: active
- **Provenance**: ai-suggested
- **Sensitivity**: high
- **Code ref**: ["lean/Lara/Driver.lean", "lean/Lara/RawAttack.lean", "lean/Lara/Admission.lean", "lean/AxCheck.lean"]

## H11: Expand surface sugar into the AST's own declaration forms, not into kernel structures
- **Rationale**: A derived surface form has to produce exactly what a hand-written source produces, or its "sugar" claim is false. Building the kernel structure directly re-implements the lowering — premise resolution, discharge resolution, conclusion checking — in a second place that can drift from the first, and the drift is invisible until a golden moves. Expanding instead into the *presentation* declarations the sugar stands for, spliced in place, and letting the existing pipeline lower them makes the equality **structural rather than coincidental**: `expandComparison` returns `[DeclClaim, DeclArg, DeclArg]`, so a generated argument reaches `Unit` through the same `resolvePremises`/`resolveDischarges`/conclusion checks as an authored one, and there is no second lowering to keep in sync. The complementary half is that anything the sugar must NOT invent stays authored — the `comparison_setup` binding leaf is named, never synthesized, so the evidence an attack targets is not something the compiler made up. Contrast [H09]: H09 narrows the public path so a policy cannot be bypassed; H11 narrows the *construction* path so a second lowering cannot diverge.
- **Sources**: ["+137/-62 ← examples/S{2,3,4}/example.lara «git diff --stat main...HEAD» [result]", "0 ← examples/S{2,3,4}/example.core.sexp «git diff --stat main...HEAD -- examples/S2/example.core.sexp … (empty output)» [result]"]
- **Status**: active
- **Provenance**: ai-suggested
- **Sensitivity**: high
- **Code ref**: ["src/Lara/Elaborate/Comparison.hs", "src/Lara/Elaborate/Internal.hs", "test/SurfaceRewriteSpec.hs"]

## H12: Declare what cannot be inferred; derive what a declaration would only let the frontend contradict
- **Rationale**: A signature has two kinds of content. Sorts themselves must be *declared*: inferring them presumes an answer the corpus has not settled (whether `imagenet_val` is a `Dataset` or an `EvalSetting` is exactly the open possible-worlds question), and a tool that guesses would freeze that guess into the artifact. Rule *parameter* sorts must be *derived*: under a validated signature every parameter already occupies sorted positions in its own rule's patterns, so a declaration adds a wire field, a rule-grammar change, and a second place the same fact can be written — creating a way for the declaration to disagree with the patterns beside it, and buying nothing. The test is not "can this be inferred" but "does declaring it create a disagreement the checker would then have to adjudicate".
- **Sources**: [
  `no ninth wire field` ← `src/Lara/Sigma/WellSorted.hs` «This is why there is no ninth wire field in the @rules@ section and no stored 'Rule' field.» [input];
  `opaque names shipped` ← `corpus-units/corpus-v1.policy.lara` «# Sort names are deliberately OPAQUE (S1, S2, …). Naming them is a separate, tracked pass: whether» [input]
  ]
- **Status**: active
- **Provenance**: ai-suggested
- **Sensitivity**: medium
- **Code ref**: [`src/Lara/Sigma/WellSorted.hs` (`ruleParamSorts`), `lean/Lara/Sigma.lean` (`ruleParamSorts`, `RuleSortRespecting`), `scripts/infer-sigma.hs`, `docs/spec.md` §3.4]

## H13: Close a cross-language AST mirror before extending its source surface
- **Rationale**: A round-trip theorem over a hand-maintained mirror can stay green
  while the production AST grows, because the theorem proves only the smaller
  model it was given. Before adding another surface feature, first port every live
  top-level field and reachable datatype into the mirror, then make both
  compilers witness their own constructor shape and compare one normalized
  inventory in CI. This turns an otherwise silent claim-width regression into a
  review-visible build failure without pretending the mirror proves the concrete
  source parser correct.
- **Status**: active
- **Provenance**: ai-suggested, user-affirmed
- **Sensitivity**: high
- **Code ref**: ["scripts/check-presentation-parity.sh", "scripts/presentation-shape.hs", "lean/Lara/PresentationParity.lean", "lean/Lara/Presentation.lean", "src/Lara/AST.hs", "plans/2026-08-10-result-12-presentation-parity.md"]
- **Last revised**: 2026-08-11 (2026-08-11_001#1)

## H14: Mirror lexical refusal order through an explicit classifier
- **Rationale**: A prover mirror with a coarser error type may collapse distinct
  failure kinds, but it must preserve which refusals happen before which inputs
  are consulted. Agreement under ordinary resolvers does not pin that order:
  an adversarial resolver can turn a misplaced lexical refusal into success.
  When the production lexer and prover have different character libraries,
  pass the production source-identifier classifier into the abstract mirror
  rather than reconstructing it independently. Test both resolver-independent
  refusal and resolver-reachable success with leading-zero, signed, legal
  non-ASCII, and illegal-start references. The certificate-slot mirror applies
  this rule while still representing every Lean failure as `none`.
- **Status**: active
- **Provenance**: ai-suggested
- **Sensitivity**: high
- **Code ref**: ["src/Lara/Syntax.hs", "src/Lara/Elaborate/CertSlots.hs", "lean/Lara/CertSlots.lean", "test/CertSlotsSpec.hs"]
- **Last revised**: 2026-08-13 (2026-08-13_001#3)
