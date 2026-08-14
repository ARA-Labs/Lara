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
- **Statement**: If two well-checked programs differ only by a uniform certificate relabel — the same
  source certified under two backends with identical strict-acceptance profiles — their compiled
  argumentation frameworks coincide (identity node bijection) and every claim gets the same four-state
  status, so which strict logic (natural deduction, LP, an arithmetic or model checker) sits behind the
  seam is not part of claim-status semantics. This is the formal reason not to make any one logic
  foundational.
- **Conditions**: Holds under grounded semantics for programs related by a uniform *injective* relabel
  of certificate payloads — a genuine backend swap: one payload per source step, so a shared source
  subterm carries the same payload at every occurrence and distinct certificates stay distinct. This
  injective condition is load-bearing: erasing every payload to a single `certified` marker (the paper's
  non-injective `eraseCert`) is NOT itself an isomorphism — collapsing distinct subterms can merge
  occurrences and add subargument-closure edges, because the compiled edge relation (`containsB`) keys on
  exact structural equality (found while mechanizing, 2026-07-30). Backend identity, theory, dependencies,
  and certificate size remain visible in audit reports; only *status* is invariant.
- **Sources**: ["\"status cannot distinguish LP from another adapter with the same strict acceptance profile\" ← docs/strict-backend-decision.md:302 «status cannot distinguish LP from another adapter with the same strict acceptance profile» [input]", "Theorem 2 (backend replacement), proved by AF isomorphism + grounded-lfp invariance ← evidence/proofs/backend_replacement.md [result]", "backend_replacement mechanized (Model A, uniform injective relabel) ← lean/Lara/Erase.lean «theorem backend_replacement … statusC (checkedAF P₁) c = statusC (checkedAF P₂) c» [result]", "0 sorryAx across 509 declarations, axioms ⊆ trio ← lean AxCheck run 2026-07-30 «sorryAx count: 0 / none — all within the trio» [result]"]
- **Status**: supported
- **Falsification criteria**: Two backends with identical strict-acceptance profiles whose programs,
  related by a uniform injective certificate relabel, nonetheless compile to non-isomorphic AFs or yield
  a differing claim status — i.e. a status difference traceable purely to certificate internals.
- **Proof**: [E04, "lean/Lara/Erase.lean: backend_replacement / checkedAF_relabel / labelC_relabel"]
- **Evidence basis**: Theorem 2 (strict-backend-decision §5) is now **machine-checked** in
  `lean/Lara/Erase.lean` (`backend_replacement`, `checkedAF_relabel`, `labelC_relabel`) under Model A —
  a uniform injective certificate relabel `mapAssur f`. Relabeled programs share a definitionally equal
  `checkedAF` (nodes are list positions, so the bijection is the identity), giving equal grounded labels
  and statuses. Mechanizing surfaced that the paper's non-injective erase-to-`certified` form is not an
  isomorphism; injectivity-on-used-certs is the faithful condition (see dead-end N76). Now **non-vacuous
  by construction** — `lean/Lara/EraseTransport.lean` transports well-checkedness (`hasSupport_mapAssur`,
  `hasAttack_mapAssur`, `mapCertProg`) under any acceptance-preserving relabel, so
  `backend_replacement_transport` exhibits the second `CheckedProgram` rather than assuming it, and
  Theorem 2's "accept the same strict instances" clause is discharged constructively. AxCheck 0 sorryAx
  across 516 decls, only `propext`/`Quot.sound` for the new declarations.
- **Tags**: backend-parametricity, replacement, status-semantics
- **Last revised**: 2026-07-30 (2026-07-30_001#3)

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
- **Status**: supported
- **Falsification criteria**: A checked support term whose actual load-bearing leaf set differs from
  `leaves(w)`, or a strict certificate whose consulted theory/premise dependency is not returned by
  its adapter's `uses` — refuting dependency accountability (spec §9 result 3).
- **Proof**: [E08]
- **Evidence basis**: spec §6 defines `leaves(w)`/`certDeps(w)`;
  `lean/Lara/Support.lean` proves `leaves_declared` for the source-leaf half, and (as of #46/PR #47)
  the certificate half is mechanized: one fixed backend core per registered `(name, version)` carries
  obligation 4's coverage/validity/accounting laws over the full consulted context, digests resolve
  only to theory *data* (so hidden theory consultation through the digest mechanism is impossible —
  `replay_theory_covers`/`certOkBOf_theory_covers`), and the support-level `certDeps` layer resolves
  every reported slot to a premise occurrence or digest-addressed theory entry
  (`cert_steps_accounted`, `certDeps_resolved`, `certDeps_theory_valid`).
- **Dependencies**: C01
- **Tags**: dependency-accountability, leaves, inversion-lemma
- **Last revised**: 2026-07-31 (PR #47: certificate-half mechanization, fixed-core/data-only-digest registry; status testing → supported)

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
  runs both drivers byte-for-byte; the framing localized one concrete Haskell-vs-Lean divergence to
  inconsistent driver identity functions (non-canonical numeric literals: `canonNum` vs the former
  Lean `canon = id`, O15), rather than a voting tie. The production Lean driver now uses `canonNum`, and the
  numeric/multi-blocked differential fixture prevents that defect from recurring.
- **Sources**: ["\"treat the reference semantics as one fallible oracle among N\" ← docs/mechanization-plan.md:129 «fallible oracle among N» [input]", "\"JEST found 44 engine bugs and 27 spec bugs\" ← docs/mechanization-plan.md:130 «JEST found 44 engine bugs and 27 spec bugs» [input]", "436/436 positive anchors agree byte-exact across both drivers ← scripts/differential.sh «pass=436 fail=0» [result]"]
- **Status**: testing
- **Falsification criteria**: A demonstration that the shared-core differential setup cannot localize
  whether a divergence is a Haskell-checker bug or a Lean-model bug (i.e. the N+1 framing gives no
  more than oracle-free voting here) — undercutting the methodological claim.
- **Proof**: [E02, "scripts/differential.sh + test/DifferentialSpec.hs: corpus fixtures agree byte-exact across the Haskell and Lean drivers; the numeric-literal divergence was localized and is now a pinned production-driver regression"]
- **Evidence basis**: Deep-research report (Csmith PLDI 2011 = oracle-free voting; JEST ICSE 2021 =
  N+1; Marmsoler–Brucker executable-oracle-from-Isabelle); folded into `docs/mechanization-plan.md` §3.
  The shared-core serialization, an M1 design requirement, is now realized in M3 as `Lara.Wire` with a
  both-drivers differential harness. The numeric divergence indicted a genuine Lean production-driver
  defect: the executable driver still used the deferred identity canonicalizer after Haskell normalized
  numeric literals. The shared `canonNum` implementation and numeric fixture now pin the fix.
- **Dependencies**: C07, C10
- **Tags**: differential-testing, conformance, mechanization, methodology
- **Last revised**: 2026-08-05 (2026-08-05_002)

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
<!-- CONFLICT: N104/O37 show that rit accepts stored L1 values without replay; C19 Conditions' unqualified “per-fact re-extraction core does hold” requires user adjudication. See N105. -->
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

## C21: A duplicate-report data conflict is missing evidence, not a counter-argument, and is escalatable to a whole-program reject
- **Statement**: When one measurand cell is reported by several leaves declared a duplicate-report group, disagreement among them is treated as *missing* evidence, not as an attack. An inconsistent group quarantines all its members. A claim whose own support is removed therefore has an evidence gap rather than acquiring a defeating attack. Other claims can nevertheless change status when quarantine removes attackers; the public verdict prevents that deletion from being reported as unqualified justification (C25). A policy may instead escalate a detected conflict to a whole-program rejection. This is the same gap-not-defeat routing C16 fixes for unmet critical questions, applied to data integrity rather than argument completeness.
- **Conditions**: The consistency test is decidable and local — group membership plus the frozen `≡` relation; because `≡` is an equivalence, pairwise-`≡` is exactly "every member `≡` the first". Default outcome is quarantine plus evidence-blocking at the public boundary; the escalation (rejection class R9) is a driver-boundary decision located at the group declaration, computed from the unit before the executable checker runs (the same tier as the R13 replay preflight), so the executable six-stage core is untouched. Untested boundary: groups spanning non-leaf occurrences, and interaction with strict-certificate leaves.
- **Sources**: [41/41 ← trace N86:evidence «differential.sh: pass=41 fail=0» [result]; 6 ← trace N86:result «6 sorry-free theorems … Lara.Groups» [result]; R9-decidable-local ← docs/spec.md §4.3 «The check is decidable and local (group membership plus ≡)» [input]]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: A directly support-dependent claim whose quarantined support is retained as usable evidence, a quarantine operation that creates an attack rather than deleting evidence, or a conflict under the escalating policy that fails to reject would disprove the routing. Status changes in other claims after deletion are outside this claim and governed by C25.
- **Proof**: [trace N86 (both-drivers differential 41/41 incl. group-consistent-accept/group-conflict-quarantine/reject-r9; AxCheck 6 Lara.Groups theorems trio-only), trace N87 (PR #45 review remediation: R9 stderr byte-compared across both drivers; .lara front-door R14 parity closes a silent-R9-evasion hole; R13→R9 precedence + multi-group independence pinned), trace N88 (Lean twin re-synced: consistentB matches Haskell groupConsistent on dangling members, consistentB_iff re-proved; all four malformed group shapes differential-pinned, negatives 9/9), trace N91 (7 seeded R9 group-escalation mutants generated over the worked examples all verify as reject R9 byte-identically through both drivers), lean/Lara/Groups.lean, PR #45]
- **Dependencies**: [C01, C16]
- **Last revised**: 2026-08-05 (2026-08-05_001#1)
- **Tags**: admission, data-integrity, gap-not-defeat, mechanized, spec-4.3, R9

## C22: Reinstatement vs contested is decided by the declared attack set, and the lever is the completeness scan's scope
- **Statement**: Which of reinstatement (justified-under-attack) and contested a unit exhibits is determined by the declared attack SET, not by which attack kinds are available. The mechanism is the scope of the attack-completeness scan: completeness is arg-conclusion-level over declared contrary pairs, so a symmetric contrary pair forces mutual rebut/undermine edges between any two args concluding the pair's sides (locking them into a 2-cycle → contested), a one-directional contrary permits an unattackable defender (→ reinstatement), and exceptions sit outside the scan entirely, so undercut edges are always voluntary — the same policy vocabulary yields reinstatement or contested depending on one declared edge.
- **Conditions**: Grounded semantics with the frozen v0.1 checker (completeness = `firstMissingConflictInfo`, arg-conclusion-level, contraries only); holds for rebut/undermine (contrary-licensed) vs undercut (exception-licensed). Untested boundary: alternative semantics (preferred/stable) and completeness scans over sub-argument occurrences.
- **Sources**: []
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: An accepted unit with two args concluding the two sides of a declared symmetric contrary pair but no mutual edges; or a one-directional contrary whose reverse edge the checker mandates; or an undercut edge required by the completeness scan. Any of these breaks the claimed decision boundary.
- **Proof**: [trace N90 (E4/E5 designed against this mechanism: E4's undermine-reinstatement needs the one-directional refuted_by_metareview contrary — the symmetric pair collapsed it into a cycle; E4 context X vs E5 context W differ by exactly one voluntary undercut edge), examples/E4, examples/E5, test/WorkedExamplesSpec.hs prop_coverageMatrix (all nine attack-kind × target-label cells measured), differential harness byte-parity on the E4/E5 anchors (both drivers), trace N95 (the accept-verdict mutation family instantiates the mechanism at corpus scale over all 9 justified units: attach-rebut-cycle forces the mutual edge via a symmetric contrary → contested, attach-undermine's one-directional contrary avoids the back-edge → clean defeat, attach-reinstate's voluntary counter-undercut → justified-under-attack; every mutant byte-identical across both drivers)]
- **Dependencies**: []
- **Tags**: attack-completeness, reinstatement, contested, grounded-semantics, worked-examples
- **Last revised**: 2026-08-01 (2026-08-01_001#3)

## C23: Single-seeded-defect localization accuracy is verification-style, not a discriminating benchmark
- **Statement**: When every mutant seeds exactly one defect at a known constituent and the checker reports its first failure in a deterministic order, measured localization accuracy sits at ceiling by construction — the number verifies diagnostic ordering rather than discriminating localization ability. Localization becomes a real signal only over inputs whose defect manifests off the seeded site or that carry multiple defects.
- **Conditions**: Single-defect seeded mutation suites checked by a deterministic first-failure checker (the LARA T3 harness regime). Untested boundary: multi-defect and off-site-manifesting suites (the recorded T6 localization follow-up in TODOS.md) — the claim predicts accuracy detaches from 100% there for reasons other than diagnostic ordering.
- **Sources**: [246/246 ← trace/exploration_tree.yaml:N96.result «drivers via subprocess), location-accuracy 246/246, replay 60/60. Certificate» [result]]
- **Status**: testing
- **Provenance**: ai-suggested
- **Falsification**: A single-defect seeded run in this harness whose localization accuracy lands significantly below 100% without any change to the checker's diagnostic ordering — i.e., the number moving as a detection signal in the very regime where the claim says it cannot.
- **Proof**: [trace N96 (T3 smoke: location-accuracy 246/246 over the single-defect manifest), docs/m5-freeze-checklist.md (T6 scoped confirmatory-by-construction on this ground), TODOS.md "Discriminating localization benchmark" entry]
- **Dependencies**: []
- **Tags**: evaluation, mutation-testing, localization, methodology, benchmark-design

## C24: A single-rule ablation admits exactly its mapped defect class — surgical and monotone, confirmatory by construction on a seeded corpus
- **Statement**: Disabling one checker rule makes the checker admit exactly the defect class that rule is responsible for and no other: the previously-rejected certificates in that class flip to accept while every other input's verdict stays byte-identical (surgical), and no certificate the full checker accepts changes (monotone). On a seeded corpus where each mutant carries one defect mapped to one rule, this demonstrates each rule is load-bearing for its class — it is confirmatory by construction and does not measure how many real, unplanted defects the rule would catch.
- **Conditions**: Seeded single-defect mutation corpus; ablation cells `noCQConfig` / `noTypedConfig` of `Lara.Check.CheckConfig`, each removing exactly one rejection arm. The surgical+monotone property is mechanically checked (`AblationSpec`, 10 pure properties). Untested boundary: the discriminating form over human-authored NATURAL defects — where the missed-defect rate is a discovery, not a construction — is deferred to #52 (ACL/EMNLP follow-up); this claim says nothing about that regime.
- **Sources**: ["18 ← measurements/frozen/ablation.json «\"ablation\": \"no-cq\", \"aggregate\": {\"count\": 418, \"missed-rejects\": 18, \"unchanged\": 400» [result]", "18/18 ← measurements/frozen/ablation.json «\"reject-IncompleteArgument\": {\"total\": 18, \"missed-rejects\": 18, \"missed-accept-classes\": {...}, \"unchanged\": 0}» [result]", "30 ← measurements/frozen/ablation.json «\"ablation\": \"no-typed\", \"aggregate\": {\"count\": 418, \"missed-rejects\": 30, \"unchanged\": 388» [result]", "11+19 ← measurements/frozen/ablation.json «\"reject-R10\": {\"total\": 11, \"missed-rejects\": 11 ... \"reject-R11\": {\"total\": 19, \"missed-rejects\": 19» [result]"]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: A seeded single-defect mutant that, under an ablated config, either flips a rejection outside the ablated rule's mapped class, or changes the verdict of a certificate the full checker accepts. Either observation breaks surgicality or monotonicity.
- **Proof**: [measurements/frozen/ablation.{json,tsv} (post-freeze run: no-cq missed-rejects 18 all reject-IncompleteArgument / unchanged 400; no-typed missed-rejects 30 = R10 11 + R11 19 / unchanged 388), test/AblationSpec.hs (surgical-flip, monotonicity, partition-totality, conflict-scan gating — 10 pure properties), trace N97 (T6 execution, PR #53 merged)]
- **Dependencies**: []
- **Tags**: evaluation, ablation, rule-necessity, axis-a, confirmatory-by-construction

## C25: Production quarantine cannot manufacture an unqualified justified verdict for a query omitted from evidence-blocked output
- **Statement**: For the shipped quarantine path, if the compact checked argumentation framework labels a query's complete compact support `justified`, and that query is absent from the driver's evidence-blocked output, then the corresponding declared-index claim is justified in the structurally reconstructed pre-quarantine framework over all declared arguments. Thus deleting inconsistent evidence cannot be the sole reason an affected claim is publicly presented as unqualified `justified`. The reconstructed `declaredAF` is not itself asserted to be the output of a successful `checkUnit` run.
- **Conditions**: At least one argument is quarantined. The retained arguments are the support-filtered subsequence selected by `Groups.keepArg` (each retained support uses no quarantined leaf); retained attacks are the resolved attacks aligned with raw declarations whose endpoint IDs both survive; `checkUnit` succeeds on exactly those retained support terms and attacks; the compact claim is `completeClaimFor` for the query; and the public blocked-query computation is the production `BlockedProgram.blockedQueries`. The result is a non-promotion theorem, not equality of statuses: unaffected attacks may still make the compact status more conservative. `statusC_agree` separately requires equal support sets.
- **Sources**: ["436/436 ← scripts/differential.sh positive anchors [result]", "54/54 ← scripts/differential.sh negative anchors [result]", "axiom audit passed ← cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh [result]"]
- **Status**: supported
- **Provenance**: ai-executed
- **Falsification**: A production input accepted by `checkUnit` for which a query is omitted from the evidence-blocked list, its compact complete claim is justified, but its lifted declared-index claim is not justified; or any hidden axiom in the checker-instantiated theorem's audit.
- **Proof**: [ara/evidence/proofs/quarantine_nonpromotion.md, lean/Lara/BlockedProgram.lean `checked_production_justified_nonpromotion_of_not_blocked`, lean/AxCheck.lean, trace N108]
- **Dependencies**: [C01, C21]
- **Tags**: quarantine, non-promotion, production-bridge, mechanized, unblocked-query

## C26: Canonical-numeral injectivity makes literal-equality goals degenerate to syntactic identity
- **Statement**: When a wire format admits exactly one canonical spelling per representable rational and a strict backend's numeral parser accepts only that canonical image, an equality goal over two numeral literals can only ever be accepted with the two literals syntactically identical -- so a comparison-family equality relation adds no judgment beyond syntactic identity, and cross-report exact agreement must be certified elsewhere (duplicate-report grouping), not by a comparison backend.
- **Conditions**: Holds for LARA's canonNum image and parseDecimal (optional sign, no leading zeros, no trailing fraction zeros): distinct canonical strings denote distinct rationals. Would not hold for a wire format admitting aliases (non-canonical zeros, scientific notation) or for goals whose arguments are computed expressions rather than literals.
- **Sources**: []
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit two distinct strings both accepted by parseDecimal that denote the same rational, or a sound accepted num_eq instance over syntactically distinct canonical numerals.
- **Proof**: [src/Lara/Prop.hs canonNum, src/Lara/Strict/Cell.hs parseDecimal (canonical-image acceptance), trace N122]
- **Dependencies**: []
- **Tags**: strict-backend, canonical-numerals, kernel-minimality, ord1

## C27: A certificate's provenance guarantee must be enforced by the backend that claims it, not inherited from the seam
- **Statement**: When a checker resolves a certificate's referenced data from a table the artifact itself supplies, and the preflight validates only that table's identity and ordering rather than its content, then any backend whose soundness story asserts that cited values trace to independently-admitted evidence must enforce that restriction inside its own decoder and replay. The guarantee cannot be inherited from the seam, because the seam's admission layer never inspected the self-supplied entries; and it cannot be assumed away by declaring the table empty, because emptiness of a registered theory is a convention of the registration site, not a property the artifact is prevented from violating.
- **Conditions**: Holds for LARA's raw `.sexp` door, where `buildCertOk` builds the strict-backend theory table from the unit's own wire `theories` section and replay preflight checks digest canonical order and duplicates only. Does not apply to the `.lara` policy door, which pins theory content via the elaborator's `registryOf`. Scope is provenance/accountability, not deductive soundness: `ra@1` cited free-context slots without the restriction and was still sound, because it never claimed premise-backing. The seam-wide question of whether `ra@1` should adopt the same guard is **resolved in favour of parity** — `ra@1` now refuses theory-entry slots exactly as `ord@1` does, so both rational-arithmetic backends carry the same trusted-base sentence, and `nd@1` is the sole remaining backend that indexes free context (deliberately: its de Bruijn free variables are meant to reach theory axioms). That resolution is an instance of this claim, not a counterexample to it: parity was obtained by moving the guard *into each backend's own decoder and replay*, not by hardening the seam.
- **Sources**: []
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit a raw-door path on which an artifact-supplied theory entry is content-validated before a backend consults it, or an `ord@1` *or* `ra@1` certificate accepted while citing a value that reaches the checker without passing the leaf/admission layer.
- **Proof**: [src/Lara/Strict/Ord.hs and src/Lara/Strict/RA.hs (premise-only slot resolution in both), src/Lara/Driver/Internal.hs buildCertOk, src/Lara/Replay.hs preflight, fixtures/corpus/ord-premise-only-{reject,accept}.sexp and ra-premise-only-{reject,accept}.sexp (each reject twin's theory entry carries the value the goal needs, so free-context indexing would have accepted), lean/Lara/Driver.lean buildRegistry, lean/Lara/Examples.lean ord_/ra_ replay_context_is_premises and models_context_is_premises (AxCheck-covered), trace N123 N125]
- **Dependencies**: []
- **Tags**: strict-backend, provenance, trusted-base, raw-door, ord1, ra1

## C28: An unenforced rejection class does not stay merely unexercised — its documented content drifts undetectably
- **Statement**: A specification class with no executable enforcement accumulates falsehoods that survive review, because nothing can contradict them. The failure is not the absence of coverage; it is that the *description* of the class becomes unfalsifiable and then wrong — including triggers that are unsatisfiable by construction, and coverage prose that asserts exercise where there is none.
- **Conditions**: Holds for a frozen, enumerated rejection surface whose classes are documented ahead of implementation and whose test suite is generated from the implemented classes. Observed on one class (R2) in one system; the untested boundary is whether a class enforced *partially* drifts the same way, and whether a hand-written (rather than generated) suite would have caught it.
- **Sources**: [
  `R2 documented trigger, unsatisfiable` ← `git dfa9811~1:docs/spec.md:1339` «| **R2** signature | arity or symbol mismatch against `Sigma`; non-ground term where ground required | the offending term | §3, §4.1 |» [input];
  `coverage prose asserting exercise` ← `git dfa9811~1:docs/rejection-surface.md:93` «Two classes are not individually anchored above because they are exercised only inside larger» [input];
  `0` ← `git dfa9811~1:fixtures/mutants/MANIFEST.tsv` «`cut -f5 | grep -c '^reject-R2$'` → 0 over 369 rows» [result];
  `107` ← `fixtures/mutants/MANIFEST.tsv` «`cut -f5 | grep -c '^reject-R2$'` → 107 over 496 rows, after enforcement landed» [result]
  ]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Find a rejection class in this surface that has been documented-but-unenforced across at least one freeze cycle and whose documented triggers and coverage prose are nonetheless all true when enforcement lands. Conversely, if R2's two documented errors turn out to have been detectable from the artifact alone — e.g. a static check that could have flagged the unsatisfiable groundness trigger from `Term`'s constructors — the mechanism is weaker than stated.
- **Proof**: [`measurements/frozen/lara-core-0.2-regeneration-diffs.md`, `docs/rejection-surface.md` (corrected note), `docs/spec.md` §10.1 amendment, `examples/R2-sort/`]
- **Dependencies**: []
- **Tags**: specification-drift, rejection-surface, coverage, lara-core@0.2

## C29: A zero reclassification delta across a new checker stage is a property of the mutation generators, not of the checker
- **Statement**: Adding an early stage to a checker silently migrates a seeded-defect suite into the new class wherever the operators synthesize their own vocabulary — the injected symbols are, by construction, exactly what the new stage rejects. "The suite's expected outcomes did not move" is therefore a claim about the generators having been made aware of the new stage, and is only meaningful if it is measured after that change rather than assumed from the stage's intent.
- **Conditions**: Holds where the new stage rejects *undeclared* material and the suite's operators create material rather than only permuting existing declarations. The complementary half is class-boundary discipline: the delta also depends on the new stage declining jurisdiction it could plausibly claim (here, substitution-domain totality and rule-id resolution, which stay R3 and R1). Observed once, over one suite; the untested boundary is a stage that rejects *relational* rather than *declarational* facts.
- **Sources**: [
  `369` ← `git dfa9811~1:fixtures/mutants/MANIFEST.tsv` «369 data rows (`wc -l` minus header)» [input];
  `empty` ← `measurements/frozen/lara-core-0.2-regeneration-diffs.md:23` «(empty)» [result];
  `three operator groups` ← `measurements/frozen/lara-core-0.2-regeneration-diffs.md:26` «**Why it is empty, and why that was not free.** Three operator groups synthesize» [result]
  ]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Revert the Σ-awareness of the symbol-injecting operators, regenerate, and observe an empty expected-column diff anyway — that would show the migration this claim asserts does not occur. Equally, a new early stage whose addition leaves a symbol-synthesizing suite's expected column unchanged *without* any generator change refutes the mechanism.
- **Proof**: [`measurements/frozen/lara-core-0.2-regeneration-diffs.md`, `src/Lara/Mutate/Sorts.hs`, `src/Lara/Mutate/Accept.hs`, `src/Lara/Sigma.hs` (`declarePred`/`declarePredFor`/`declareCon`)]
- **Dependencies**: [C28]
- **Tags**: mutation-testing, evaluation-validity, seeded-defects, lara-core@0.2

## C30: A substitution lemma is what licenses a thin per-instance check; the thinness is a result, not a scoping judgement
- **Statement**: A checker that validates a rule's patterns once, statically, and each instance's substitution range separately can leave the instantiated atoms unvalidated only if a substitution lemma carries pattern well-formedness through instantiation. Without the lemma the per-instance check's scope is an unjustified guess that happens to work on the corpus; with it, the minimality of that check is derived rather than chosen.
- **Conditions**: Holds for ground, first-order instantiation with an explicit substitution (no unification in the trusted core) and a property compositional over term structure. Mechanized here for the finite ground environment and for premises, conclusions, and answers of actual rule instances recursively reachable through accepted support terms. Exception-pattern and attack/undercut closure is not included in `checkUnit_wellSorted`; those remain separate per-pattern applications of `wellSorted_subst`.
- **Sources**: [
  `result 13` ← `docs/mechanization-plan.md` «| 13 | Well-sortedness is decidable and preserved by rule instantiation (`lara-core@0.2`, issue #89) |» [result];
  `axiom set` ← `lean/AxCheck.lean` via `scripts/check-axioms.sh` «Axiom audit passed.» [result]
  ]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit an accepted unit whose ground environment or actual recursively reachable support-rule premise, conclusion, or answer is ill-sorted while stage 2 accepts it. That would contradict `checkUnit_wellSorted` directly. An ill-sorted instantiated exception would expose the explicitly unproved boundary rather than directly contradict this theorem.
- **Proof**: [`lean/Lara/Sigma.lean` (`wellSorted_subst`, `wellSorted_rule`), `lean/Lara/Check/Unit.lean` (`thetaWellSorted_ruleSortRespecting`, `checkUnit_wellSorted`), `docs/mechanization-plan.md` result 13, `fixtures/mutants/*--wrong-theta-sort-*.sexp`]
- **Dependencies**: []
- **Tags**: mechanization, substitution-lemma, checker-design, lara-core@0.2
- **Last revised**: 2026-08-10 (2026-08-10_001#2)

## C31: Citation lowering is representation-total over the authorable surface
- **Statement**: A presentation-layer name resolver stays spelling-invariant only if its locate step matches every representation the elaboration paths can place in the resolved sequence, not just the one the designer expects. For `lara-syntax@0.6` certificate citations this means locating a prior-argument name against both the argument's elaborated term (what inferred-theta resolution stores) and its bare-leaf spelling (what a hand-built premise list stores, passed through unre-pointed); term-equality locate over that candidate set makes the explicit and inferred spellings of the same argument lower to identical slots.
- **Conditions**: Holds for the current surface, where premise lists are not authorable (`explicitRuleP` stores none) and nested assurances are not surface-expressible — so every parsed premise is constructed by `resolvePremises`/`inferTheta` — plus hand-built ASTs accepted by the elaborator, which the second locate candidate covers. No false ambiguity: a leaf sharing the cited name already fails upstream as `SlotNameAmbiguous` in `refMatches` scope resolution. Untested boundary: a future grammar extension making premise lists authorable would add new reachable representations and must extend the candidate set.
- **Sources**: []
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit a program or elaborator-accepted AST whose certificate citation lowers under `by r from [...]` but fails with `CertSlotNotAPremise` under the explicit spelling of the same argument (or vice versa), or one where the two spellings lower to different slots.
- **Proof**: [`test/CertSlotsSpec.hs` (`prop_priorArgumentCitationBothSpellings`, `prop_priorArgumentPremiseSpellingsAgree`, nested-certificate D8 fixtures), `src/Lara/Elaborate/Internal.hs` (`certSlotResolver` two-candidate locate), adversarial spec-review verification (trace N180, session 2026-08-13_001)]
- **Dependencies**: []
- **Tags**: elaboration, presentation-layer, name-resolution, lara-syntax@0.6
