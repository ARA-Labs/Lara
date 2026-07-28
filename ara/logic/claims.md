# Claims

_Design and metatheory claims of the LARA claim-support calculus. Because LARA is a language-design
contribution, the "evidence" for each claim is its **mechanization / proof status** and the Haskell
checker's **test results**, recorded in `evidence/status/` and `evidence/proofs/`. A claim's `Status`
reflects that grounding: `supported` where a paper proof or passing test exists, `hypothesis` where
the result is stated but not yet proved or mechanized._

## C01: Claim support can be decided by normalized positional identity, with no entailment procedure in the trusted base
- **Statement**: When "an argument supports a claim" is defined as syntactic identity (up to a fixed,
  total literal-canonicalizing normal form) between the argument's conclusion and the claim's formal
  target, the support relation is decidable, total, and an equivalence — so a claim-support checker
  needs no solver or entailment engine in its trusted base. Reordering-sensitivity is retained (no
  predicate is treated as commutative), keeping the normal form linear and binder-free.
- **Conditions**: Holds for ground first-order atoms with no bound variables (rule parameters are
  ground-substituted away before a proposition forms). If the corpus needs AC predicates or binders,
  the normal form extends with argument sorting / de Bruijn indexing and the same properties must be
  re-established (the documented flip criterion), so the claim is bounded to the v0.1 atom language.
- **Sources**: ["`≡` is thus decidable, total, reflexive, symmetric, transitive, and linear in term size — a trivial addition to the TCB." ← docs/spec.md:154 «`≡` is thus decidable, total, reflexive, symmetric, transitive, and linear in term size» [input]", "8/8 properties pass ← evidence/status/test_status.md «prop ≡ reflexive … +++ OK, passed 100 tests» [result]"]
- **Status**: supported
- **Falsification criteria**: Exhibit two propositions the corpus treats as the same claim that
  `nf`/`≡` separates (or vice versa) without the AC/binder extension applying — i.e. a support
  decision the identity relation gets wrong on real claims — or a QuickCheck counterexample to
  reflexivity/symmetry/transitivity/idempotence.
- **Proof**: [E01]
- **Evidence basis**: `Lara.Prop` implements `nf`/`≡`; `test/PropSpec.hs` establishes the equivalence
  laws, no-argument-reordering, and `canonNum` variant-collapse — all 8 properties pass (100 cases each).
- **Tags**: normalization, identity, decidability, trusted-base

## C02: The three structured-argumentation attack types coincide with the three position kinds of a support term
- **Statement**: Rebut, undercut, and undermine are not independent primitives to be matched by
  bespoke rules — they are exactly the attacks on a term's three position kinds (root conclusion,
  internal rule occurrence, frontier leaf). Consequently attack well-formedness reduces to
  subterm-occurrence checking plus a contrary-relation lookup, which is decidable and local, and the
  attacked position doubles as the diagnostic's source location.
- **Conditions**: Holds under a policy-declared `contrary` relation (not classical negation) and the
  ASPIC+ restriction that strict rules are unattackable; positions are paths of premise indices and
  question names.
- **Sources**: ["\"The three attack kinds are exactly the three kinds of positions in a term\" ← docs/spec.md:447 «The three attack kinds are exactly the three kinds of positions in a term» [input]", "\"Attack checking is subterm-occurrence checking plus a contrary-relation lookup: decidable and local\" ← docs/spec.md:472 «Attack checking is subterm-occurrence checking plus a contrary-relation lookup» [input]"]
- **Status**: supported
- **Falsification criteria**: A defeat pattern the corpus annotators find that cannot be typed as an
  attack on a root / internal-rule / leaf position (e.g. a genuine attack on something other than
  those three positions), forcing a fourth attack primitive.
- **Proof**: [E05, "lean/Lara/Attack.lean: undercut_target_rule / undermine_target_leaf,
  rebut_top_defeasible / undercut_pos_defeasible, rebut_concl_coherent;
  lean/Lara/Check/Attack.lean: checkAttack_sound / checkAttack_complete;
  lean/Lara/Check/Program.lean: checkProgram_sound / checkProgram_complete;
  lean/Lara/Examples.lean: check_rebut_success /
  check_nested_undercut_success / check_mixed_undermine_success /
  check_program_endpoint_reject_classes;
  all listed explicitly in lean/AxCheck.lean"]
- **Evidence basis**: spec §7.1 fixes the positional judgment and
  `lean/Lara/Attack.lean` mechanizes the position-kind partition,
  strict-unattackability, and local/global conclusion coherence sorry-free;
  `Lara.Check` now adds exact executable positional-attack and raw-program
  checking with soundness/completeness. AxCheck audits the adequacy theorems
  and concrete positive/rejection fixtures within the standard axiom trio.
  N29 adversarial corpus coverage remains evaluation work, not a gap in the
  formal checker claim.
- **Dependencies**: C01
- **Tags**: attacks, positions, ASPIC+, decidability
- **Last revised**: 2026-07-24 (result-1 checker closure; N52, N53, N57,
  session 2026-07-24_008)

## C03: An accepted strict certificate establishes a conditional deductive consequence, never premise truth
- **Statement**: Routing strict steps through a backend that returns only accept/reject + dependencies
  + diagnostics makes the source judgment non-factive by construction: an accepted certificate proves
  the encoded conclusion is a backend consequence of the encoded premise conclusions and declared
  theory, and nothing about whether any premise is true. No backend formula or proof term can be
  eliminated into a source truth judgment.
- **Conditions**: Holds for `Strict-Cert` instances under a registered backend meeting the six backend
  obligations; explicitly excludes `Strict-Trusted` (trusted-policy) instances, which get structural
  validation but no consequence theorem.
- **Sources**: ["\"a successful check discharges the deductive validity of this strict step, conditional on its premise conclusions and the declared theory; it does not establish that the premise support terms' conclusions are true\" ← docs/strict-backend-decision.md:35 «it does not establish that the premise support terms' conclusions are true» [input]", "Theorem 3 (source non-factivity), proved by inversion ← evidence/proofs/nonfactivity_and_defeat.md [result]"]
- **Status**: supported
- **Falsification criteria**: A source derivation that uses backend acceptance to derive a truth
  judgment `⊢ p true` for a supported proposition — i.e. a rule that eliminates support into truth —
  would refute the non-factivity theorem.
- **Proof**: [E03]
- **Evidence basis**: `lean/Lara/Strict.lean` mechanizes the factivity firewall through the concrete
  executable ND backend: `nonfactiveJudgment` is built from exact symbolic replay of `hyp 0`,
  `nd_nonfactive_witness` refutes premise-free validity, and `no_truth_projection` lifts the witness
  to all backends. `Lara.Strict.ND` supplies the matching Haskell adapter.
- **Dependencies**: C04
- **Tags**: strict-backend, non-factivity, soundness, trust-boundary
- **Last revised**: 2026-07-24 (2026-07-24_004)

## C04: Confining strict logic behind an opaque interface makes claim-support status independent of certificate internals
- **Statement**: If two backends accept exactly the same strict instances, then after erasing
  certificate payloads the compiled argumentation frameworks are isomorphic and every claim gets the
  same four-state status — so which strict logic (natural deduction, LP, an arithmetic or model
  checker) sits behind the seam is not part of claim-status semantics. This is the formal reason not
  to make any one logic foundational.
- **Conditions**: Holds for source-identical programs differing only in strict-certificate payloads,
  under grounded semantics; backend identity, theory, dependencies, and certificate size remain
  visible in audit reports (only *status* is invariant).
- **Sources**: ["\"status cannot distinguish LP from another adapter with the same strict acceptance profile\" ← docs/strict-backend-decision.md:302 «status cannot distinguish LP from another adapter with the same strict acceptance profile» [input]", "Theorem 2 (backend replacement), proved by AF isomorphism + grounded-lfp invariance ← evidence/proofs/backend_replacement.md [result]"]
- **Status**: supported
- **Falsification criteria**: Two backends with identical strict-acceptance profiles whose programs
  nonetheless compile to non-isomorphic AFs or yield a differing claim status — i.e. a status
  difference traceable purely to certificate internals.
- **Proof**: [E04]
- **Evidence basis**: Theorem 2 (strict-backend-decision §5) proves backend replacement via structural
  induction, `eraseCert` graph isomorphism, and invariance of the grounded least fixed point; it is a
  paper proof slated for mechanization (result 9), not yet machine-checked.
- **Tags**: backend-parametricity, replacement, status-semantics

## C05: A registered backend's soundness discharges as a per-instance corollary when the interface carries soundness as an obligation
- **Statement**: Structuring a backend as an interface that *carries its own soundness obligation* (a
  proof that acceptance implies backend consequence) makes each strict step's soundness a one-line
  application of that obligation, and reduces each new adapter's burden to discharging the same fixed
  contract. For the required intuitionistic natural-deduction adapter the obligation is met by
  induction on the typing derivation, with exact dependency accountability from free de Bruijn indices.
- **Conditions**: Holds for any backend meeting the six obligations (decidable replay, normalization
  fidelity, certificate soundness, dependency accountability, closed registration, structural
  consequence laws); the ND adapter is sound but not complete for its Boolean semantics — completeness
  is deliberately not required because LARA checks submitted certificates rather than searching.
- **Sources**: ["\"Intuitionistic natural deduction is sound but not complete for this Boolean semantics; completeness is not required because LARA checks submitted certificates rather than searching for every valid proof.\" ← docs/strict-backend-decision.md:210 «completeness is not required because LARA checks submitted certificates» [input]", "Theorem 4 (ND soundness) + Lemma 5 (dependency exactness) ← evidence/proofs/nd_adapter_soundness.md [result]"]
- **Status**: supported
- **Falsification criteria**: A well-typed natural-deduction certificate whose conclusion is not a
  Boolean consequence of its context (refuting Theorem 4), or a well-typed certificate whose true
  premise/theory dependencies are not exactly its free de Bruijn indices (refuting Lemma 5).
- **Proof**: [E03]
- **Evidence basis**: `lean/Lara/ND.lean` proves `infer` sound and complete for `HasType` and proves
  exact free-variable dependencies. `lean/Lara/Strict.lean` now adds the closed symbolic decoder,
  exact submitted-certificate replay, replay/acceptance adequacy, and a source atom-key decoder
  left-inverse establishing normalization fidelity without relying on generated display text.
  `src/Lara/Strict/ND.hs` implements the identical framed encoding and executable adapter.
- **Dependencies**: C03
- **Tags**: natural-deduction, soundness, dependency-accountability, modularity
- **Last revised**: 2026-07-24 (2026-07-24_004)

## C06: Claim acceptance is non-monotonic and cannot be captured by any monotonic consequence relation
- **Statement**: Because a newly supplied, checked attacker can move a claim from `justified` to not
  `justified` while its original support term stays well-typed, claim acceptance is non-monotonic
  across framework extensions — a property no monotonic consequence relation (S4, LP, J, J4) can
  represent. This defeasibility is intentional for empirical reasoning, and it is what a purely
  proof-theoretic (monotonic) approach cannot express.
- **Conditions**: Non-monotonicity is at the *consequence level*, across extensions of the input
  framework; for a *fixed* framework the internal transfer operator is monotone over a finite-height
  lattice, so grounded evaluation is still deterministic and terminating (no contradiction).
- **Sources**: ["\"adding evidence or attacks can retract a claim's justified status even though the original support term remains well typed\" ← docs/spec.md:510 «adding evidence or attacks can retract a claim's `justified` status even though the» [input]", "Proposition 8 (monotonic consequence cannot represent defeat-driven retraction), proved by a subset counterexample ← evidence/proofs/nonfactivity_and_defeat.md [result]"]
- **Status**: supported
- **Falsification criteria**: A monotonic consequence relation that reproduces LARA's grounded claim
  acceptance under all framework extensions (i.e. never needs to retract) — its existence would refute
  Proposition 8.
- **Proof**: [E06]
- **Evidence basis**: Proposition 8 (strict-backend-decision §6) proves that no monotonic relation
  represents acceptance under framework extension; spec §8 gives the monotone-operator-on-finite-lattice
  construction that keeps evaluation deterministic. Grounded engine (`Lara.Grounded`) is spec-only.
- **Dependencies**: C04
- **Tags**: non-monotonic, defeat, grounded-semantics, the-differentiator

## C07: Grounded four-state status is deterministic and terminating; cycles yield undecided, not nontermination
- **Statement**: Compiling to a finite Dung framework and taking the least fixed point of Dung's
  monotone characteristic function from the empty set gives a unique grounded labelling in at most
  |Args| growth steps, so the four-state claim status (justified / gap / defeated / contested) is
  deterministic and terminating; attack cycles produce `undec` (reported as `contested`) rather than
  divergence.
- **Conditions**: Holds because `Args` is finite and the operator is monotone on the subset lattice;
  `contested` = grounded `undec`, which is broader than mutual defeat (even/odd cycles,
  undec-propagation) and must be explained by the responsible SCC in the report.
- **Sources**: ["\"the ascending chain stabilizes after at most `|Args|` strict-growth steps, so grounded evaluation is deterministic and terminating; attack cycles produce `undec` labels rather than nontermination\" ← docs/spec.md:506 «grounded evaluation is deterministic and terminating; attack cycles produce `undec` labels rather than nontermination» [input]"]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification criteria**: A finite compiled framework on which grounded iteration fails to
  stabilize within |Args| steps or admits two distinct grounded labellings — refuting determinism or
  termination (spec §9 result 5).
- **Proof**: [E07]
- **Evidence basis**: spec §8 gives the fixed-point argument; `lean/Lara/Grounded.lean` proves
  bounded stabilization and fixed-point determinism, while `lean/Lara/Compile.lean`
  `srcStatus_unique`/`srcStatus_iff` prove that source four-state status is functional and equals
  compiled executable status under a faithful edge decider. That `Faithful` edge decider is no longer
  an assumption: the checker-built `edgeB` (from `containsB`/`attackClosureB`) decides the frozen
  closure `Edge` exactly (`edgeB_faithful`), so `srcIn_iff_checkedGrounded`/`srcStatus_iff_checked`
  carry source-vs-compiled status agreement over an accepted program with **no oracle hypothesis**
  (the source status is the Prop shadow of that same compiled closure `Edge`, not an independent
  calculus). Issue #18 subsequently supplies checked-unit attack completeness and result 7.
  `lean/AxCheck.lean` audits these theorems without `sorryAx`.
- **Dependencies**: C06
- **Tags**: grounded-semantics, determinism, termination, four-state-status
- **Last revised**: 2026-07-25 (issue #17 close: `Faithful` oracle discharged by `edgeB_faithful`)

## C08: The reported leaf-dependency set equals the term's leaf frontier — accountability is an inversion lemma, not a tracked judgment component
- **Statement**: Making the leaf-dependency set *derived* (`leaves(w)` = the leaf constants occurring
  in the term) rather than a judgment component collapses the former accountability theorem into a
  structural inversion lemma: the reported dependencies are exactly the term's frontier, and
  strict-certificate theory dependencies are reported separately via each backend's `uses` function.
- **Conditions**: Holds for checked support terms; every leaf in `leaves(w)` must be declared in the
  admitted context `Γ`, and backend dependencies (`certDeps`) are unioned in from accepted certificates.
- **Sources**: ["\"The former accountability theorem … is thereby an inversion lemma on term structure: the reported leaf dependency set is exactly `leaves(w)`.\" ← docs/spec.md:424 «the reported leaf dependency set is exactly `leaves(w)`» [input]"]
- **Status**: testing
- **Falsification criteria**: A checked support term whose actual load-bearing leaf set differs from
  `leaves(w)`, or a strict certificate whose consulted theory/premise dependency is not returned by
  its adapter's `uses` — refuting dependency accountability (spec §9 result 3).
- **Proof**: [E08]
- **Evidence basis**: spec §6 defines `leaves(w)`/`certDeps(w)`;
  `lean/Lara/Support.lean` proves `leaves_declared` for the source-leaf half, while backend
  `certDeps` accountability still awaits a `uses` field on the executable backend interface.
- **Dependencies**: C01
- **Tags**: dependency-accountability, leaves, inversion-lemma
- **Last revised**: 2026-07-22 (2026-07-22_002)

## C09: Restricting contrary-instance overlap off strict-reachable patterns buys consistency by construction
- **Provenance**: ai-suggested
- **Statement**: A compile-time well-formedness check that forbids any strict-rule consequent — and
  any pattern on a strict chain — from having a canonically equivalent ground instance with either
  side of a declared `contrary` pair (Path B) makes every conflict rebuttable at a defeasible step,
  so direct = indirect consistency hold under grounded semantics and two contrary claims are never
  jointly `justified`. The cost is an expressiveness limit: strict chains may only target
  uncontested claims.
- **Conditions**: v0.1 chooses Path B; if the corpus shows strict rules genuinely feeding contested
  claims, the flip is Path A (total involutive contradictory map + transposition closure), which buys
  all four rationality postulates at the cost of structuring the contrary relation. The v0.1
  executable `mayOverlap` check is conservative for non-linear patterns: it may reject a safe policy
  but cannot accept two patterns with canonically equivalent ground instances.
- **Sources**: ["\"strict closure introduces no new conflict and direct = indirect consistency hold by construction — two contrary claims are never jointly justified\" ← docs/spec.md:546 «introduces no new conflict and direct = indirect consistency hold by construction — two contrary» [input]"]
- **Status**: supported
- **Falsification criteria**: A Path-B-well-formed policy under which two contrary claims are both
  labelled `justified` by grounded semantics — refuting consistency (spec §9 result 7); or corpus
  evidence that Path B's expressiveness limit rejects a large fraction of real strict chains.
- **Proof**: [E05, "lean/Lara/Policy.lean: strictReachable_iff_mem /
  aPatMayOverlap_of_instances / wfB_iff / wellFormed_no_strict_contrary_left/right;
  lean/Lara/Compile.lean: coveredB_iff / complete_conflict_edge;
  lean/Lara/Check/Unit.lean: checkUnit_sound;
  lean/Lara/Grounded.lean: grounded_conflictFree / statusC_justified_iff;
  lean/Lara/Consistency.lean: wellFormed_contrary_target_attackable /
  contrary_args_not_both_grounded / contrary_claims_not_both_justified;
  exact self-conflict and rejection fixtures; audited by AxCheck"]
- **Evidence basis**: spec §8.1 states the Path-B restriction and
  `lean/Lara/Policy.lean` mechanizes its finite strict-reachable set and exact
  executable judgment. `checkUnit` is now the canonical executable constructor
  of `Unit.CheckedUnit`: it rejects duplicate rule IDs and R12 violations before
  detailed program checking, retains the checked-node cache, and proves exact
  compiled-edge coverage for every ordered attackable contrary pair (including
  self-pairs). Generic `CheckedProgram` deliberately remains only the
  attack-soundness boundary. Generic grounded conflict-freedom plus exact
  `claimSupportFor` indexing proves that two computed `completeClaimFor` contrary
  claims cannot both be justified. This supports result 7 for the Lean reference
  PL only: it does not implement Path A, the production Haskell checker,
  natural-language validation, or the full `holes(P,p)` /
  `incompleteAlternative` computation.
- **Dependencies**: C02
- **Tags**: rationality-postulates, consistency, strict-rules, path-B
- **Last revised**: 2026-07-26 (2026-07-25_005)

## C10: For a calculus-contribution paper, mechanized metatheory + worked examples + rejection conformance is the evaluation — not benchmarks or user studies
- **Statement**: When a paper's contribution is a calculus rather than a system, the credible
  evaluation is (a) machine-checked metatheory, (b) worked examples spanning every status/attack, and
  (c) adversarial rejection-class conformance with zero false positives — while performance numbers
  and user studies are essentially never load-bearing. Mechanization can *be* the evaluation, and
  because artifact evaluation excludes non-mechanized proofs from review, an un-mechanized soundness
  argument earns no artifact credit.
- **Conditions**: Holds for language-design / type-theory submissions at POPL/PLDI-class venues; this
  claim is about *evaluation methodology*, grounded in a deep-research pass over accepted exemplars,
  not about LARA's own internals. Benchmarking was decided out of scope for the first submission.
- **Sources**: ["\"POPL artifact evaluation explicitly excludes non-mechanized (paper) proofs from review\" ← docs/mechanization-plan.md:25 «POPL artifact evaluation explicitly excludes non-mechanized (paper) proofs from review» [input]", "Two Mechanisations of WebAssembly 1.0 (FM 2021): two mechanised semantics + type-soundness as the whole evaluation ← docs/mechanization-plan.md:21 «Mechanized metatheory *can be the entire evaluation* for a language-semantics paper» [input]"]
- **Status**: supported
- **Falsification criteria**: A recent accepted POPL/PLDI calculus paper whose evaluation rests on
  performance benchmarks or a user study with no mechanized metatheory or worked examples — i.e. an
  accepted counterexample to the methodology claim.
- **Proof**: [E02]
- **Evidence basis**: Deep-research report (adversarially verified, 24/25 claims confirmed) folded
  into `docs/mechanization-plan.md` §0 and `docs/worked-examples-plan.md` §6; exemplars: WebAssembly
  mechanisation (FM 2021), DSP/Baldur/LeanDojo/Clover, Csmith/JEST.
- **Tags**: evaluation-methodology, mechanization, popl, meta-claim

## C11: An untrusted-producer / trusted-checker split is accepted when soundness rests entirely on the checker and rejection is adversarially validated
- **Statement**: A hybrid where an untrusted LLM proposes certificates that a trusted core re-checks
  is judged by verified-success-rate plus adversarial zero-false-positive rejection plus evidence the
  producer generalizes (anti-memorization) — not by user studies or latency. The LLM component is
  accepted precisely when it is untrusted-by-construction, so a producer error costs one failed check,
  never a false acceptance.
- **Conditions**: Holds for the proof-carrying-output / neurosymbolic pattern (DSP, Baldur, LeanDojo,
  Clover); LARA's Haskell checker is the trusted arbiter and the Python LLM front-end (Phase E) is the
  untrusted producer that may never define policy rules or logical schemas at runtime.
- **Sources**: ["\"it reports high acceptance on correct instances and zero false positives on deliberately-incorrect (adversarial) instances\" ← docs/worked-examples-plan.md:160 «zero false positives on deliberately-incorrect (adversarial)» [input]", "\"An untrusted LLM front-end (added later, in Python) proposes certificates; the checker is the sole arbiter of structural validity.\" ← README.md:11 «front-end (added later, in Python) proposes certificates; the checker is the» [input]"]
- **Status**: hypothesis
- **Falsification criteria**: A seeded-incorrect certificate that the LARA checker *accepts* (a false
  positive) would refute the untrusted-by-construction guarantee; or an evaluation showing the split
  is judged by latency/user-study rather than verified-success + rejection.
- **Proof**: [E02]
- **Evidence basis**: Deep-research report (Clover zero-false-positives, LeanDojo novel-premises split,
  DSP/Baldur verified-success-rate); LARA's elaborator is Phase E, not yet built, so the split is a
  design commitment grounded in exemplars.
- **Dependencies**: C10
- **Tags**: proof-carrying, untrusted-producer, rejection-class, adversarial

## C12: Differential testing against a mechanized reference should be framed as N+1-version (the reference is a fallible oracle), not oracle-free voting
- **Statement**: When cross-checking a production checker against a mechanized reference semantics, the
  right frame is JEST-style N+1-version differential testing — the reference is one *fallible* oracle
  among N, and a divergence indicts either the implementation or the spec — rather than Csmith-style
  oracle-free voting. Finding a bug in the mechanized reference is therefore a legitimate result, and
  the single-interpretation discipline (deterministic verdicts, no undefined behavior) is what makes
  any divergence a real defect.
- **Conditions**: Holds for the Haskell↔Lean cross-check once both share one serialized first-order
  core AST; LARA's grounded status is deterministic (C07), so the single-interpretation precondition
  holds by construction, with no undefined behavior to quotient out. The shared serialized core is
  now built (`Lara.Wire` S-expr codec, the N11 anchor) and the harness (`scripts/differential.sh`)
  runs both drivers byte-for-byte; the framing localized one concrete Haskell-vs-Lean divergence to a
  spec/implementation choice (non-canonical numeric literals: `canonNum` vs `canon = id`, O15) rather
  than a voting tie, consistent with the N+1 frame.
- **Sources**: ["\"treat the reference semantics as one fallible oracle among N\" ← docs/mechanization-plan.md:129 «fallible oracle among N» [input]", "\"JEST found 44 engine bugs and 27 spec bugs\" ← docs/mechanization-plan.md:130 «JEST found 44 engine bugs and 27 spec bugs» [input]", "19/19 fixtures agree byte-exact across both drivers ← scripts/differential.sh «pass=19 fail=0» [result]"]
- **Status**: testing
- **Falsification criteria**: A demonstration that the shared-core differential setup cannot localize
  whether a divergence is a Haskell-checker bug or a Lean-model bug (i.e. the N+1 framing gives no
  more than oracle-free voting here) — undercutting the methodological claim.
- **Proof**: [E02, "scripts/differential.sh + test/DifferentialSpec.hs: 19/19 corpus fixtures agree byte-exact across the Haskell and Lean drivers; the numeric-literal divergence is localized as an implementation/spec choice (docs/m3-closeout-notes.md)"]
- **Evidence basis**: Deep-research report (Csmith PLDI 2011 = oracle-free voting; JEST ICSE 2021 =
  N+1; Marmsoler–Brucker executable-oracle-from-Isabelle); folded into `docs/mechanization-plan.md` §3.
  The shared-core serialization, an M1 design requirement, is now realized in M3 as `Lara.Wire` with a
  both-drivers differential harness; no divergence has yet indicted a genuine bug (the one localized
  divergence is a documented deferred normalization choice, not a defect).
- **Dependencies**: C07, C10
- **Tags**: differential-testing, conformance, mechanization, methodology
- **Last revised**: 2026-07-27 (2026-07-27_001)

## C13: A small fixed scheme vocabulary covers the corpus's argument shapes
- **Statement**: The inference schemes that ARA corpus claims instantiate collapse into a small
  closed family set dominated by controlled comparison and intervention/ablation, so the policy
  layer can ship a fixed scheme vocabulary rather than an open-ended scheme language.
- **Conditions**: Established on the 60-claim stratified M0 sample at corpus pin `62e9b54`
  (single-AI annotation; only the typing field double-annotated). Family count is ~9 after
  normalizing annotator-coined names; the unsampled reserve (171 claims) is unannotated.
- **Sources**: ["9 families / all assignable ← m0/annotation-summary.md:44 «Top-3 families cover 46/60 (77%); all 60 are assignable to the 9 families» [result]", "two-thirds ← m0/annotation-summary.md:45–46 «comparison + ablation alone carry two-thirds of the corpus» [result]"]
- **Status**: supported
- **Provenance**: user-revised
- **Falsification criteria**: A corpus or reserve claim whose supporting argument fits none of the
  nine families without encoding the whole reasoning step as an opaque leaf, or reserve annotation
  showing family count grows open-endedly rather than converging.
- **Proof**: [E09]
- **Dependencies**: []
- **Tags**: corpus-study, schemes, policy-layer
- **Last revised**: 2026-07-22 (2026-07-22_001#2)

## C14: Corpus strict-step demand is arithmetic re-checking and code inspection — not LP
- **Statement**: The strict steps corpus arguments actually need are certifiable by a
  rational-arithmetic/table-recheck checker plus a static code-inspection checker; justification-
  logic (LP) certificates answer no observed corpus demand, so the optional adapter portfolio
  should lead with the arithmetic checker and LP stays a non-shipping option.
- **Conditions**: 60-claim sample at pin `62e9b54`; "smallest plausible certifier" judgments by AI
  annotators — the strict steps are identified, not discharged, inside the artifacts. The single
  reference-nd call (nanogpt_chat_rl C04) splits on review (2026-07-22): its counting instance
  identities are arithmetic, but its ≥ N−1 optimality lower bound is a genuine quantified
  derivation — the corpus's one ND-shaped demand, carried by the reference backend with the
  combinatorial content as a declared theory dependency (spec §5.2, N33).
- **Sources**: ["certifier counts ← m0/annotation-summary.md:48 «domain-checker 35, none 21, lp 3, reference-nd 1» [result]", "arithmetic character ← m0/annotation-summary.md:49–50 «overwhelmingly *arithmetic re-checks of reported tables* (deltas, ratios, aggregations, inequalities) plus a few code inspectors» [result]"]
- **Status**: supported
- **Provenance**: user-revised
- **Falsification criteria**: Corpus/reserve strict steps at meaningful frequency that need nested
  justification-term structure (LP) or genuine ND derivations rather than arithmetic or code
  inspection; or an implemented arithmetic checker failing to certify the identified calls.
- **Proof**: [E09]
- **Dependencies**: []
- **Tags**: corpus-study, strict-backend, adapter-portfolio
- **Last revised**: 2026-07-22 (2026-07-22_001#9)

## C15: Per-result-cell is the default evidence-leaf granularity
- **Statement**: Corpus evidence decomposes naturally at the granularity of the individual reported
  result cell (one number in a table or figure), not whole experiments or runs; the leaf layer
  should default to per-result-cell atoms with coarser grains as explicit, minority exceptions.
- **Conditions**: 60-claim sample at pin `62e9b54`; coarser or mixed grains cover the remaining
  quarter of claims and must stay expressible.
- **Sources**: ["grain distribution ← m0/annotation-summary.md:64–65 «per-result-cell 45, mixed 7, per-experiment-claim 6, per-run 2» [result]"]
- **Status**: supported
- **Provenance**: user-revised
- **Falsification criteria**: Further annotation showing cell-level atoms are systematically the
  wrong grain — e.g. distribution-valued or aggregate leaves dominating (cf. the stochastic-
  dispersion wishlist item), or cell-level leaves proliferating beyond audit practicality.
- **Proof**: [E09]
- **Dependencies**: []
- **Tags**: corpus-study, leaf-granularity, evidence-layer
- **Last revised**: 2026-07-22 (2026-07-22_001#2)

## C16: Defeat edges are rare and undercut-dominant; unmet critical questions must be gaps, not attacks
- **Statement**: In real research artifacts genuine defeat edges are rare (a few percent of
  dead-end classifications) and skew entirely to undercuts, while unmet mandatory critical
  questions are pervasive; a sound defeat layer therefore routes unmet CQs to holes/gaps rather
  than attack edges, and draws attack candidates from the whole exploration trace — experiment
  nodes included — since counter-evidence can live outside dead ends and dead ends can even serve
  as support.
- **Conditions**: 60-claim sample at pin `62e9b54`. Rebut/undermine are unexercised in-corpus and
  expectedly so: the corpus is polished, peer-reviewed top-venue work. By decision N29 (user,
  2026-07-22), rebut/undermine are exercised via self-authored adversarial reports/mutations
  against corpus claims at language-testing time, not by corpus mining.
- **Sources**: ["attack profile ← m0/annotation-summary.md:55–56 «4 undercut, 0 rebut, 0 undermine, 190 none (98%)» [result]", "CQ profile ← m0/annotation-summary.md:67–68 «Mandatory: 105 met, **68 unmet-gap (39%)**, 3 unmet-defeater» [result]"]
- **Status**: supported
- **Provenance**: user-revised
- **Falsification criteria**: Authored-adversarial or reserve annotation showing that gap-treatment
  of unmet mandatory CQs suppresses defeats the artifact itself licenses (claims that should flip
  status but do not), or that whole-trace attack walking still misses documented counter-evidence.
- **Proof**: [E09]
- **Dependencies**: [C02, C06]
- **Tags**: corpus-study, defeat-layer, critical-questions
- **Last revised**: 2026-07-22 (2026-07-22_001#2)

## C17: The v0.1 construct set passes the M0 coverage gate at ~90% with a finite residual wishlist
- **Statement**: The sampled argument shapes are expressible in the planned v0.1 construct set —
  nine scheme families plus the nl/formal/binding scope discipline, multi-arg support, and
  claim-splitting conventions — without opaque-leaf encoding of whole reasoning steps, clearing the
  ≥80% exit gate; the inexpressible residue is a closed six-item construct wishlist, not an
  open-ended gap.
- **Conditions**: Preliminary: single-AI annotation with only the typing field double-annotated;
  coverage-flag adjudication user-affirmed (2026-07-22) but not independently reviewed; pooled
  across benchmark populations (per-population split of O01 not yet applied); rebut/undermine
  exercise deferred to authored adversarial tests (N29). The three evidence-model decisions
  flagged at gate time (whole-trace attack walk, dead-end-as-support, result-cell conflict) were
  resolved into spec §7/§4.3/§11 on 2026-07-22 (N30, N31, PR #9), leaving the six-item wishlist
  as the whole residue.
- **Sources**: ["gate verdict ← m0/annotation-summary.md:99 «PASS — ~90% of sampled argument shapes are expressible» [result]", "flag partition ← m0/annotation-summary.md:75 «21/60 claims (35%) carry coverage flags» [result]"]
- **Status**: supported
- **Provenance**: user-revised
- **Falsification criteria**: Full-schema double annotation or reserve annotation pushing
  expressibility below 80%, or wishlist growth across further samples showing the residue is
  open-ended rather than closed.
- **Proof**: [E09]
- **Dependencies**: [C13, C15, C16]
- **Tags**: corpus-study, coverage-gate, v0.1-freeze
- **Last revised**: 2026-07-22 (2026-07-22_001#10)

## C18: Kernel-attestation verifiers are bounded by their grounding interface, not their kernel logic
- **Statement**: In a kernel-attestation verifier of research artifacts (rit-style: sha256-locked
  evidence + proof-kernel discharge), the world-facing expressible fragment is capped by the
  grounding interface — only predicates over deterministically extractable quantities can be claim
  content — so every paper-level claim enters the kernel through an unchecked, defeasible narrowing
  from prose to a numeric shadow. The kernel's own expressiveness (full CIC) is not the binding
  constraint; the extraction interface and the auto-discharge tactic portfolio are.
- **Conditions**: Verified against rit's source tree as of 2026-07-25 (post-restructure:
  `src/rit/{formal,gate,...}`); rit's implemented vocabulary is five object kinds and six relations
  over log-extracted naturals, discharged `by decide` (solver portfolio decide → omega → simp).
  Generalization to other kernel-attestation systems (e.g. EG-VAR) is argued, not yet verified
  against their sources. Says nothing against the kernel's value on the numeric fragment itself —
  that fragment is exactly what LARA delegates to a strict backend.
- **Sources**: ["six relations ← ../rit/src/rit/formal/primitives.py «RELATIONS = {\"GROUNDS\" … \"ORDER\" … \"BEAT\" … \"BOUND\" … \"ENTAIL\" … \"CONTRADICT\" …}» (dict has exactly six keys) [result]", "five objects ← ../rit/src/rit/formal/primitives.py «OBJECTS = {\"GOAL\" … \"EVIDENCE\" … \"FACT\" … \"RECORD\" … \"BASELINE\" …}» [result]", "by decide default ← ../rit/src/rit/formal/grammar.py «proof: the proof script. Defaults to `by decide` (decidable arithmetic)» [result]", "non-formalizability admission ← ../rit/src/rit/formal/primitives.py «(\"why\" as VALUE (important/novel) is NOT formalizable and is kept as context, never proven.)» [result]"]
- **Status**: supported
- **Provenance**: user-revised
- **Falsification criteria**: A kernel-attestation system mechanically checking a non-numeric
  world-facing claim (causal, methodological, generalization) without a trusted human/LLM
  narrowing step — e.g., a checked scheme-instantiation or a verified prose-to-formal lowering
  admitted through its kernel gate.
- **Proof**: [docs/comparison-rit-lara.md §11.1–§11.2 (source-verified addendum, commit d192047)]
- **Dependencies**: [C06]
- **Tags**: related-work, novelty-defense, rit, expressiveness
- **Last revised**: 2026-07-25 (2026-07-25_001#3)

## C19: A verification system's real guarantee is what its commit gate enforces, not what its write-up claims
- **Statement**: For a kernel-attestation research verifier, the trust guarantee actually delivered
  is the fixed point of its admission gate — the set of checks that run before a commit is accepted —
  and this can be strictly weaker than the trust architecture the system's own documentation
  describes. Aggregate/whole-artifact guarantees (single proof environment, machine-read cross-claim
  dependency graph, extraction moved into the kernel, a falsifiability filter) are especially prone
  to being designed-but-unwired: present as helpers, prose, or stubs yet never invoked on the write
  path. Auditing such a system therefore requires reading the gate path, not the write-up; the
  per-artifact leaf guarantee can be sound while the aggregate one is not enforced.
- **Conditions**: Verified against rit's shipping tree 2026-07-25 (commit path `rit.py` →
  `action/push` → `admit.gate` → `grounding` + `formal/kernel`). Four advertised aggregate
  guarantees found not enforced (per-file compilation not one Lean env; `used_constants` a
  `return []` stub so claim→claim edges are declared; `bind()` emits only L1/L2 so K-tier never
  fires; `tautological` never called at commit); the per-fact re-extraction + kernel sorry/rogue-axiom
  rejection core does hold. Generalization to other kernel-attestation systems is argued from the
  mechanism, not yet source-verified elsewhere.
- **Sources**: ["per-file compilation ← ../rit/src/rit/admit/__init__.py «for f in files: ok, why = _check_one(f)» (loop; _check_one runs kernel._run_lean on one file) [result]", "used_constants stub ← ../rit/src/rit/formal/uses.py «def used_constants(lean_path): … Returns []. return []» [result]", "L1/L2 only ← ../rit/src/rit/grounding/__init__.py «tier, exid, spec = \"L2\", extractor_id(extractor), extractor … tier, exid, spec = \"L1\", \"\", None» (bind() branches; no K) [result]", "falsifiability gate not called ← ../rit/src/rit/admit/__init__.py «gate(): p = check_proofs(repo); g = grounding.reextract_all(repo); admitted = p[\"ok\"] and g[\"ok\"]» (no tautological) [result]", "per-fact core holds ← ../rit/src/rit/action/push.py «axiom {b['label']}_grounded : {b['label']} = {int(b['value'])}» + admit.gate re-extracts every binding [result]"]
- **Status**: supported
- **Provenance**: user-revised
- **Falsification criteria**: Reading rit's `admit.gate` and finding it does invoke, on the commit
  path, the whole-repo single-environment check, a kernel `getUsedConstants` read of claim→claim
  edges, a K-tier (`native_decide`-over-evidence) grounding, and the `tautological` falsifiability
  filter — i.e. the write-up's aggregate guarantees are in fact enforced, not merely documented.
- **Proof**: [docs/comparison-rit-lara.md §11.5 (commit-path audit, commit ba6c45e); trace N47]
- **Dependencies**: [C18]
- **Tags**: related-work, rit, verification-method, spec-vs-code, trust-architecture

## C20: Verified-node / declared-edge attestation graphs launder weak claims through missing dependency edges
- **Statement**: When an attestation system kernel-checks individual claim nodes but takes the
  dependency edges between them from the untrusted proposer's declaration (rather than deriving
  them from the proof terms), its weakest-link / status roll-up becomes a conditional guarantee
  whose antecedent — that the declared edge set is the true dependency set — is never verified.
  The roll-up stays arithmetically sound over the given graph, so a *spurious* edge only over-
  penalizes; but an *omitted* real edge silently upgrades a claim that rests on a weak or refuted
  fact to a falsely high grade, and the system cannot detect it because it never reads the true
  dependency. Node-level formal verification therefore does not transfer to the composed artifact:
  the aggregate verdict is an unverified composition of verified parts.
- **Conditions**: Holds for kernel-attestation verifiers whose inter-claim edges are proposer-
  declared and whose leaf/relation facts are individually checked — verified against rit's shipping
  code 2026-07-25 (`declared_claim_deps` in `push.py`; `used_constants` a `return []` stub;
  `derive.grade`/`gate.grade` roll-up over that declared cone). Does not apply to systems that read
  dependencies from the proof term (Lean `getUsedConstants`, or a single-environment check where a
  proof must actually consume another's theorem) — there the edge set is kernel-derived, and this
  laundering channel closes.
- **Sources**: ["declared edges ← ../rit/src/rit/action/push.py «u = USES.uses(repo.proofs / f\"{thm}.lean\", declared_claim_deps=deps)» (edges = the deps argument, not read from the term) [result]", "used_constants stub ← ../rit/src/rit/formal/uses.py «def used_constants(lean_path): … return []» [result]", "roll-up over declared cone ← ../rit/src/rit/derive/__init__.py «grade(): … tiers = [by_label[l]... for l in claim.get(\"grounding_deps\", [])] … floor = min(...)» + gate/grade.py grade_block walks b.references [result]"]
- **Status**: supported
- **Provenance**: user-revised
- **Falsification criteria**: Exhibiting, in rit's shipping code, a path by which an omitted
  claim→claim dependency edge is detected at the commit gate — e.g. `admit.gate` deriving the
  true dependency cone from the proof terms and rejecting a grade computed over an incomplete
  declared cone. If the gate reads real edges, the laundering channel this claim names does not exist.
- **Proof**: [docs/comparison-rit-lara.md §11.6 (conditional-roll-up + missing-edge analysis); trace N47]
- **Dependencies**: [C19]
- **Tags**: rit, verification-method, trust-architecture, composition, roll-up
