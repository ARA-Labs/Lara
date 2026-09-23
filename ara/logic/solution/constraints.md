# Constraints, assumptions, limitations

_Source: `docs/spec.md` §1, §11; `docs/strict-backend-decision.md`
§7. What LARA does and does not guarantee, stated plainly (the "state the trusted boundary bluntly"
lesson from EG-VAR, `docs/prior-art-lessons.md`)._

## Boundary conditions

- **Structural validity only.** Checker acceptance means the argument is well-typed and undefeated
  relative to the selected policy, backend theories, and admitted leaves — NOT that any claim is
  empirically true. "compiles ≠ claim true; compiles = the argument is well-typed and undefeated, given
  its evidence and the chosen policy."
- **Policy-relative completeness.** "Complete" means every premise and critical question of an
  instantiated scheme is discharged or surfaced as a hole — not mechanical completeness of a scientific
  argument (which is undecidable from a finite artifact without a closed-world assumption).
- **v0.1 fragment.** Support-level propositions are ground first-order atoms; grounded semantics only;
  Path B consistency (strict chains may only target uncontested claims); no AC/symmetric predicates, no
  binders in `nf`. Each is a documented flip criterion, not a permanent limit.
- **Surface/core boundary (`lara-syntax@0.3`).** The presentation surface elaborates before the frozen
  `lara-core@0.1` boundary: measurand polarity, `comparison` blocks, premise labels, `nl` interpolation,
  and surface attack steps never enter `Unit`, and S2/S3/S4 elaborating to byte-identical Units is the
  acceptance gate for any surface change. The paper states this boundary and keeps the elaborator
  validated-not-verified, exactly like the parser.
- **No tactic DSL, IDE, package manager, or standard library** for the initial contribution.

## Assumptions (the three-way conditional guarantee)

The end-to-end guarantee is conditional on three unchecked things:

1. **Leaf truth (soundness).** Evidence atoms are untrusted hypotheses; provenance tags and admission
   gate them, but the checker never proves them.
2. **NL→proposition faithfulness (the translation gap).** That `c.formal` faithfully renders `c.nl`.
   No checker can verify this; it is the single most load-bearing unchecked step, human-signed and
   evaluated on the semantic-faithfulness axis (spec §11).
3. **Policy faithfulness.** That a defeasible scheme (and its critical questions) is a correct account
   of what supports the claim. `Π` is a trusted input; policy quality is an evaluated axis, not a
   proven property. "Your checker is only as good as its policy" is the rebuttal-bait — the answer is
   curated-from-methodology-literature, versioned, corpus-validated.

## Known limitations

- **The hard problem is relocated, not removed.** LARA's exposure is not dishonest framing but a
  relocated hard problem: the epistemic content moves into `Π` (trusted, unchecked) and the leaves.
- **Curry–Howard covers adapters, not LARA as a whole.** The clean "well-typed proof term ⟹ valid
  derivation" story applies to proof-term adapters (spec §5). The defeasible layer is
  argumentation-framework defeat, which is not a Curry–Howard phenomenon — a valid argument can be
  retracted by a dead end. The honest framing is a typed argument checker with pluggable strict
  adapters, not an end-to-end Curry–Howard proof system.
- **Realization is not a lowering guarantee.** Artemov's `S4 ⊢ F ⟹ LP ⊢ Fʳ` is theorem-to-realization;
  it says nothing about NL→formal faithfulness (the pivot, trace N05). LP realization is
  optional-adapter metatheory, never the guarantee behind lowering.
- **Two definitional points are open** (must close before M1 freeze): the hole-vs-complete-alternative
  status case (spec §8), and `contested`-SCC provenance reporting (review §6).
- **Result 6 is currently unprovable as written** — no independent direct source semantics exists to
  preserve (see `mechanization.md` §5).
- **Most of the checker is unimplemented.** Only `Lara.Prop` (`nf`/`≡`) is built and tested; the strict
  registry, ND adapter, policy/support-term/attack/compile/grounded layers, JSON codec, parser, and the
  Python elaborator are spec-only. The existing LP code is a non-conforming adapter seed.
- **Benchmarking is out of scope for this work** — which raises the weight on metatheory +
  worked examples, so the differentiator (E3) and the rejection-class conformance must be airtight.

## What is out of scope by design

- A graded/probabilistic core (the kernel stays boolean; graded confidence lives in the judge as
  metadata).
- Provenance-as-attack (low-trust provenance supports an admission policy and audit report; it does not
  logically rebut or undercut an argument).
- Model-checker behavioral leaves (TL-1) — optional, strictly outside the kernel, gated by corpus
  open question §8 #7.

## Corpus-derived pipeline constraints (M0, 2026-07-22 — grounds: C16, E09)

- **Attack candidates come from the whole trace.** The elaborator's attack walk must cover
  experiment nodes and score-filtered runs, not only `dead_end` nodes — two artifacts held their
  strongest counter-evidence outside dead ends (fix_embedding C12, triton_cumsum C09).
- **Unmet mandatory CQs are holes, not defeaters.** 39% of mandatory critical questions in the
  corpus are unmet; treating them as attacks would spuriously defeat nearly every claim.
- **Dead ends can support.** A `dead_end` node can be a claim's primary *evidence*
  (restricted_mlm C14); the lowering map needs a support-from-dead-end path, not only attack typing.
- **Result-cell conflicts quarantine to gap** (decided 2026-07-22, spec §4.3). Conflicting duplicate
  reports of one result cell (figure vs text, bridging-data-gaps C05) are neither an attack nor a
  provenance grade: the elaborator declares duplicate-report groups, admission enforces `≡` within
  each group, and a conflicted group is quarantined whole — dependent arguments fail at that
  occurrence and the claim surfaces as `gap` (absence of reliable evidence, not a counter-argument).
  Policy may escalate quarantine → reject.
- **Rebut/undermine test coverage is authored, not mined** (decision N29): the corpus is polished,
  peer-reviewed top-venue work; adversarial reports/mutations against corpus claims are written by
  us at language-testing time, extending the rejection-class negative-suite discipline to the
  defeat layer.

## Design-audience constraint (user, 2026-07-22 — grounds: N32)

- **Surface syntax targets Python-literate domain researchers, not PL experts.** ARA/LARA's
  readers are researchers across fields who will read (and sometimes write) the formalizations of
  their own artifacts; every concrete-syntax, identifier, and presentation decision weighs their
  readability above PL convention or terseness (hence descriptive snake_case scheme names,
  spec §4.5). The kernel stays symbolic regardless — this constraint governs only the
  decode-boundary / surface layer.
- **Frontend concrete-syntax naming is co-decided with the ARA maintainer** at frontend design
  time; both the canonical long vocabulary and the reserved short vocabulary are held in spec
  §4.5 until then.

## v0.1 residual construct wishlist (M0, 2026-07-22 — grounds: C17, E09)

The coverage gate passed at ~90% treating the inexpressible residue as a **closed** six-item construct
wishlist — post-v0.1 candidates, deliberately outside the frozen v0.1 fragment, not an open-ended gap:

1. **Equivalence / non-inferiority as a first-class scheme** with its own defeat conditions
   (all-in-one C06) — currently expressible only as a plain `controlled_comparison`.
2. **Monotone-functional-relationship propositions** (pinn C01) — "as X rises, Y rises".
3. **Parametric growth-rate claims** (nanogpt_chat_rl C04) — asymptotic/scaling statements.
4. **Stochastic measurand dispersion** (triton_cumsum C09) — a leaf whose value is a *distribution*,
   not a single number (see the leaf-granularity note, `spec.md` §3).
5. **Negative existentials over code** (rust_codecontests C09) — "no path in the source does X"; partly
   served by the code-inspection adapter (`spec.md` §5.2).
6. **Graded / undefined predicates** (what-will-my-model-forget C03) — resolvable by binding discipline
   rather than a new core construct.

The two evidence-model decisions that were open at gate time are now resolved into `spec.md` and are
**not** on this wishlist: dead-end-as-support (§7, §11 task 6 — elaborator lowers a `dead_end` to
support or attack) and result-cell conflict (§4.3 — duplicate-report groups quarantined on `≡`
disagreement; dependent claims surface as `gap`).

## M4a surface front-end constraints (2026-07-29 — grounds: N68, N69, N74, O15, O17)

- **The original M4a suite was defeasible-only; S1 closes the frontend-cert
  gap.** O17 remains the historical constraint on the `lara-syntax@0.1` suite:
  its eight examples cannot author a strict argument and `use backends [nd@1]`
  is inert. Additive `lara-syntax@0.2` now supplies support-term assurance and a
  policy theory table; `examples/S1/` exercises `.lara` → elaboration →
  `Driver.buildCertOk` → `nd@1` replay. The original rejection representatives
  remain **R1 / R12 / R10**; S1 is an accepted strict-path witness, not a
  remapping of that M4a rejection trio.

- **Both production drivers share `canonNum` (O15 resolved 2026-08-05).** Haskell
  `Lara.Prop.nfTerm` and Lean `Lara.Driver.dcanon` now normalize numeric literals with the same
  function. `group-quarantine-numeric-multi-blocked.sexp` deliberately mixes canonical and
  non-canonical spellings in a case where identity canonicalization would publish two false
  `justified` statuses; `DifferentialSpec` and `scripts/differential.sh` pin the corrected
  byte-identical `evidence-blocked` verdict. Numeric fixtures no longer require a num-free policy.

- **Result 12's Lean anchor certifies the AST shape, not the concrete parser (from O18, staged).**
  The mechanized `parse ∘ print = id` (`lean/Lara/Presentation.lean`) is over a structured
  S-expression codec on the frozen presentation AST — it proves no field loses information, but
  does not transfer to the concrete-syntax Haskell parser; the QuickCheck round-trip
  (`SyntaxSpec`, 2000 iters) remains the surface-syntax conformance evidence.

- **The two checking-time columns are different protocols and must never be ratioed (from O31).**
  `hs_check` is in-process, decode excluded, verdict forced (median ~7 µs); `lean_wall` is
  subprocess wall time including startup + decode (median ~2.6 ms, trace N96). The ~370× gap is
  process startup, not semantics — any cross-driver speed claim needs a same-protocol measurement.
  The harness labels the columns separately for exactly this reason, and an unforced lazy
  `runCheck` would instead read ~0 ns (D8/5A), so the forcing discipline is part of the protocol.

## Naturalness boundary (user, 2026-08-25 — grounds: N215, `docs/naturalness-boundary.md`, issue #109)

Where natural language may and may not enter the system, split by **trust direction** rather
than by convenience. Fixed policy so that ease-of-use work cites it instead of re-deciding
"how natural should this be?" once per feature. Extends the design-audience constraint above
(Python readability stays the calibration baseline).

- **Layer 1 — the verified surface (`.lara`) gets more readable, never natural.** The
  precedent is Isar, not the controlled-natural-language one: a surface that looks like
  English but parses a fragment has an *invisible parse boundary*, so every rejection reads as
  arbitrary to an author who cannot see where the fragment ends. The surface exists for
  auditability — a human must be able to read what the checker actually saw — which requires
  determinism, not naturalness. **NL-in through the verified parser is permanently out of
  scope**, not deferred; a proposal to accept prose here reopens this constraint rather than
  being a per-feature call.

- **Layer 2 — NL as input belongs exclusively to the untrusted producer** (`Lara.Json` / the
  LLM elaborator, issue #30). Already pinned by the tree: `docs/spec.md` §1.1 places the
  elaborator outside the TCB, §11 makes NL formalization the first of its six logged lowering
  tasks, and §3.1's claim triple carries `binding` as an untrusted, audited annotation. The two
  mechanisms any layer-2 feature inherits are **replay** (nothing a producer emits is believed
  until re-checked by trusted code) and the **binding audit** (prose-to-formal agreement is
  confirmed by a human, not the checker — #121). Consequence: an NL-in feature cannot be made
  safe by improving the producer.

- **Layer 3 — NL as output is free and worth exploiting.** Verdicts, rejection reasons and
  reports derive from already-checked artifacts and feed nothing back, so improving their prose
  cannot change what is accepted. Two bounds (ai-suggested, added at crystallization): a
  rendering must **stay** a rendering — the moment an output becomes an input it is a layer-1
  or layer-2 change; and "free" describes the *prose*, not the *templates*, which are normative
  (surface-grammar H.5 fixes eight `CertNd*` templates verbatim and `scripts/differential.sh`
  byte-compares the two drivers' stdout and exit code).

- **The design rule: every ease-of-use feature must remove transcription, never checking.** A
  convenience crosses the line the moment the checker sees something the author did not legibly
  write. At layer 1 the rule has an **executable form** — the readable spelling must lower to
  the terse spelling's exact bytes — which is the invariant the surface grammar already records
  for the `@0.6`/`@0.8`/`@0.9`/`@0.10` named certificate spellings. Every surface version `@0.4`
  through `@0.10` satisfies it.

- **Permissible is not the same as worth building** (ai-suggested). The rule licenses a
  convenience; it does not schedule one. #151 is the worked case: the `nd@1` binder half is
  squarely layer 3 and therefore permitted, yet correctly deferred, because the only sound
  implementation restructures a backend seam `ord@1` and `ra@1` share and the Lean side mirrors.
  The same framing rejects that issue's option (c) on principle — a best-effort reconstruction
  outside the adapter could print a *wrong* name, i.e. a layer-3 rendering that has stopped
  being faithful to the checked artifact.

**Scope split.** The core paper may cite the design rule and layer 1 as a
language-design commitment; layer-2 evaluation (how faithfully a producer lowers prose) is
deferred, with #52 and #30.

## M2b restricted-class complexity constraints (2026-08-31 — grounds: O105, O106, N255, N264)

- **A restricted-class lower-bound witness carries class membership.** A family over
  arbitrary `Grounded.AF` values is not evidence of tightness over M1-realizable
  carriers. The witness must provide an executable checker equation and
  `StructuredAFIso` under the same fixed canon, signature, policy, and registry as
  the paper claim. The implemented fixed context, family-wide checker equation,
  and realizable witnesses are documented in `docs/theory-m2b-complexity.md`;
  `docs/theory-m2b-complexity-spike.md` preserves both gate decisions.
- **Oracle cost and classical input size use separate frozen representations.**
  Grounded evaluation counts calls to the attack oracle on the frozen carrier.
  Classical hardness uses `CarrierCode`: finite node labels, a square adjacency
  matrix, and an in-range query. `CarrierCode.byteSize` is a carrier accounting
  measure charging atom-key text, matrix cells, query-index text, and one framing
  unit; it is not serialized wire length because no `CarrierCode` serializer
  exists. `Formula3.byteSize`, by contrast, is the UTF-8 length of its canonical
  S-expression (`lean/Lara/Complexity/Encoding.lean`).

## M2b follow-up realization constraints (2026-08-31 — grounds: O108, O109, N257, N263, N264)

- **A family-wide realization theorem requires compositional checker lemmas, not
  closed fixtures.** Closed `checkUnit` fixtures establish schema directionality and
  concrete realizability, but they do not discharge the family-wide obligations
  `Check.Unit.checkUnit_complete` exposes for a generated map/flatMap unit family:
  duplicate-freedom of root support terms, recursive `HasSupport` with exact
  substitution domains, `HasAttack` for every declaration, attack-endpoint
  membership, and exact `Compile.AttackComplete`. A realization attempt over a
  formula-indexed family must first package compositional lifting lemmas for those
  obligations, or select a separately reviewed specialized construction; it may not
  extrapolate acceptance from closed instances. Issue #209 discharges this
  constraint through the compositional-lemma architecture in
  `lean/Lara/Complexity/Gadget.lean`; the durable account is
  `docs/theory-m2b-complexity.md`, and the retired execution plan is preserved
  at git object `8155ec7:plans/2026-08-30-m2b-realization-followup.md`.

## PW-T6 translation-form constraint (2026-09-02 — grounds: O113, N271, N276)

- **A bridge-global partial translation cannot express target-world-dependent
  resolution, and moving past it is a contract change, not a refinement.** One
  `translate : B → Query src → Option (Query tgt)` answers once for every world
  pair of the bridge; a source atom whose resolution depends on the target world
  (the obsolete-alias case: one target world carries the resolving ontology
  version, another does not) is inexpressible, as is ambiguity — several target
  queries for one source query — which `Option` forbids by construction. The
  edge-indexed successor `Translate : (b) → World src → World tgt → Query src →
  Query tgt → Prop` repairs both, but `mem_compare_iff_sat_dia`,
  `compare_translationUndefined_iff`, and the executable `crossCompare` are all
  stated against the `Option` form, so adopting it re-opens the adequacy layer
  and must be budgeted as such. T6 (#191, PR #223) deliberately stayed on the
  bridge-global form — `Lara.PW.SymMap` is functional, and the frozen
  limitation is recorded in `docs/theory-pw-t6-structural-transport.md` §8.1
  with the sizing note at `docs/theory-pw0-outer-model.md` §6. T8/T9 designs
  choose the translation form *first*; a design assuming per-world resolution
  on the `Option` interface is wrong before it starts.

## PW-T9 path-witness constraint (2026-09-03 — grounds: O127, N292, N293)

- **A path-level failure must be witnessed on a typed structural path.** A
  failed translation computed from standalone `SymMap` values cannot establish
  failure along a path of contract-valid bridges. The witness must inhabit
  `BridgePath`, expose the successful prefix and failing next edge, and connect
  the folded path translation to the outer comparison result. PW-T9 discharges
  this with `gapPath`, `mid_path_out_of_vocabulary`, and
  `mid_path_translationUndefined` in
  `lean/Lara/Examples/PWCompose.lean`.

## M4 axiom-discipline witness constraint (2026-09-07 — grounds: O120, N281, N318, N320)

- **An axiom discipline can put a milestone's own witnesses out of reach of its
  existing fixtures.** D9 admits only `propext`, `Classical.choice`,
  `Quot.sound`, while every accepted surface fixture in
  `lean/Lara/Examples/Surface.lean` is proved by `native_decide`. A witness
  built on one would import `Lean.ofReduceBool` into the audit and fail
  `scripts/check-axioms.sh`. The cost of a discipline is paid where a new
  result wants to reuse old evidence, not where the discipline is adopted, so
  a corollary can be proved, audited, and still uninstantiable from the
  development's own examples.
- **The escape is a purpose-built pair, not a reduction of an existing one.**
  `lean/Lara/Examples/SurfaceTransport.lean` supplies its own environment,
  program, and certificate rather than shrinking `Examples/Surface.lean`, and
  `surfaceTransport_directAF_eq` witnesses
  `Lara.Context.surface_directAF_relabel` inside the trio.
- **What made it cheap was narrowing the opaque surface, not avoiding the
  kernel.** The one kernel-opaque function on the path is
  `NDNamed.lowerFormula` / `lowerNamedExpr` (`WellFounded.Nat.fix`,
  `@[irreducible]`), reached only through certificate-payload lowering. A
  payload authored in kernel form never reaches it, and
  `NDNamed.lowerNamed_id_of_kernel` discharges the obligation with a hypothesis
  that is literally the `Env.startsIdent_nat_false` field. `reconstructExplicitTerm`
  was never the obstacle — it compiles to `brecOn` and the kernel unfolds it.
  The earlier sizing that deferred this as "milestone-sized" (N300) rested on
  the wrong blocker; the module builds in 485 ms. See N318.
- **A witness that discharges every hypothesis can still be degenerate.** The
  current pair declares no attacks, so the edge half of `checkedAF_map`
  (`coveredB_relabel`) is exercised on an empty list and the AF equality holds
  for any two attack-free single-argument programs. Non-vacuity guards on the
  relabel do not establish non-degeneracy of the framework equality. Tracked
  as issue #258; `surface_directAF_link` remains #255.
