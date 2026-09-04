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
- **Sources**: ["`≡` is thus decidable, total, reflexive, symmetric, transitive, and linear in term size — a trivial addition to the TCB." ← docs/spec.md:274-275 «`≡` is thus decidable, total, reflexive, symmetric, transitive, and linear in term size» [input]", "8/8 properties pass ← evidence/status/test_status.md «prop ≡ reflexive … +++ OK, passed 100 tests» [result]"]
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
- **Sources**: ["\"The three attack kinds are exactly the three kinds of positions in a term\" ← docs/spec.md:937-938 «The three attack kinds are exactly the three kinds of positions in a term» [input]", "\"Attack checking is subterm-occurrence checking plus a contrary-relation lookup: decidable and local\" ← docs/spec.md:962-963 «Attack checking is subterm-occurrence checking plus a contrary-relation lookup» [input]"]
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
- **Sources**: ["\"Intuitionistic natural deduction is sound but not complete for this Boolean semantics; completeness is not required because LARA checks submitted certificates rather than searching for every valid proof.\" ← docs/strict-backend-decision.md:210-211 «completeness is not required because LARA checks submitted certificates» [input]", "Theorem 4 (ND soundness) + Lemma 5 (dependency exactness) ← evidence/proofs/nd_adapter_soundness.md [result]"]
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
- **Sources**: ["\"adding evidence or attacks can retract a claim's justified status even though the original support term remains well typed\" ← docs/spec.md:1131-1132 «adding evidence or attacks can retract a claim's `justified` status even though the» [input]", "Proposition 8 (monotonic consequence cannot represent defeat-driven retraction), proved by a subset counterexample ← evidence/proofs/nonfactivity_and_defeat.md [result]"]
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
- **Sources**: ["\"the ascending chain stabilizes after at most `|Args|` strict-growth steps, so grounded evaluation is deterministic and terminating; attack cycles produce `undec` labels rather than nontermination\" ← docs/spec.md:1126-1127 «grounded evaluation is deterministic and terminating; attack cycles produce `undec` labels rather than nontermination» [input]"]
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
- **Sources**: ["\"The former accountability theorem … is thereby an inversion lemma on term structure: the reported leaf dependency set is exactly `leaves(w)`.\" ← docs/spec.md:823 «the reported leaf dependency set is exactly `leaves(w)`» [input]"]
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
- **Sources**: ["\"strict closure introduces no new conflict and direct = indirect consistency hold by construction — two contrary claims are never jointly justified\" ← docs/spec.md:1193 «introduces no new conflict and direct = indirect consistency hold by construction — two contrary» [input]"]
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
- **Sources**: ["\"it reports high acceptance on correct instances and zero false positives on deliberately-incorrect (adversarial) instances\" ← docs/worked-examples-plan.md:197-198 «zero false positives on deliberately-incorrect (adversarial)» [input]", "\"An untrusted LLM front-end (added later, in Python) proposes certificates; the checker is the sole arbiter of structural validity.\" ← docs/substrate-decision.md:11-13 «Python emits claim-support programs, opaque strict-certificate payloads, and leaf atoms; the Haskell checker decides validity.» [input]"]
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
- **Sources**: ["\"treat the reference semantics as one fallible oracle among N\" ← docs/mechanization-plan.md:141 «fallible oracle among N» [input]", "\"JEST found 44 engine bugs and 27 spec bugs\" ← docs/mechanization-plan.md:142 «JEST found 44 engine bugs / 27 spec bugs» [input]", "436/436 positive anchors agree byte-exact across both drivers ← scripts/differential.sh «pass=436 fail=0» [result]"]
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
- **Sources**: ["grain distribution ← m0/annotation-summary.md:66–67 «per-result-cell 45, mixed 7, per-experiment-claim 6, per-run 2» [result]"]
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
- **Sources**: ["attack profile ← m0/annotation-summary.md:55–56 «4 undercut, 0 rebut, 0 undermine, 190 none (98%)» [result]", "CQ profile ← m0/annotation-summary.md:69–70 «Mandatory: 105 met, **68 unmet-gap (39%)**, 3 unmet-defeater» [result]"]
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
- **Sources**: ["gate verdict ← m0/annotation-summary.md:101 «PASS — ~90% of sampled argument shapes are expressible» [result]", "flag partition ← m0/annotation-summary.md:77 «21/60 claims (35%) carry coverage flags» [result]"]
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
<!-- CONFLICT: see trace N210 / N212, staging O85. The #123 families were built (2026-08-24) and reviewed (#167, 2026-08-25). They do NOT detach location_match from 100%: every published ground-truth site is gated against the checker by prop_siteMatchesChecker / prop_localizationSites before it reaches MANIFEST.tsv, so a mislocating key fails CI at generation time instead of lowering the rate. This contradicts (a) the Statement's last clause and (b) the Conditions' untested-boundary prediction. The single-defect Statement itself is untouched and still supported by N96. Adjudication deferred to the researcher — the honest replacement generalizes past this harness (O85). -->
- **Statement**: When every mutant seeds exactly one defect at a known constituent and the checker reports its first failure in a deterministic order, measured localization accuracy sits at ceiling by construction — the number verifies diagnostic ordering rather than discriminating localization ability. Localization becomes a real signal only over inputs whose defect manifests off the seeded site or that carry multiple defects.
- **Conditions**: Single-defect seeded mutation suites checked by a deterministic first-failure checker (the LARA T3 harness regime). Untested boundary: multi-defect and off-site-manifesting suites (the recorded T6 localization follow-up, issue #123) — the claim predicts accuracy detaches from 100% there for reasons other than diagnostic ordering.
- **Sources**: [246/246 ← trace/exploration_tree.yaml:N96.result «drivers via subprocess), location-accuracy 246/246, replay 60/60. Certificate» [result]]
- **Status**: testing
- **Provenance**: ai-suggested
- **Falsification**: A single-defect seeded run in this harness whose localization accuracy lands significantly below 100% without any change to the checker's diagnostic ordering — i.e., the number moving as a detection signal in the very regime where the claim says it cannot.
- **Proof**: [trace N96 (T3 smoke: location-accuracy 246/246 over the single-defect manifest), docs/m5-freeze-checklist.md (T6 scoped confirmatory-by-construction on this ground), issue #123 "Discriminating localization benchmark"]
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
- **Sources**: ["436/436 ← scripts/differential.sh positive anchors [result]", "54/54 ← scripts/differential.sh negative anchors [result]", "axiom audit passed ← (set -o pipefail; cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh) [result]"]
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
  `empty` ← `measurements/frozen/lara-core-0.2-regeneration-diffs.md:37` «(empty)» [result];
  `three operator groups` ← `measurements/frozen/lara-core-0.2-regeneration-diffs.md:40` «**Why it is empty, and why that was not free.** Three operator groups synthesize» [result]
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
- **Conditions**: Holds for the current surface, where premise lists are not authorable (`explicitRuleP` stores none) and nested assurances are not surface-expressible — so every parsed premise is constructed by `resolvePremises`/`inferTheta` — plus hand-built ASTs accepted by the elaborator, which the second locate candidate covers. No false ambiguity: a leaf sharing the cited name already fails upstream as `SlotNameAmbiguous` in `refMatches` scope resolution. Untested boundary: a future grammar extension making premise lists authorable would add new reachable representations and must extend the candidate set. Scope, from `lara-syntax@0.8` (#131): the claim is about the resolver's *locate* step, and the resolver now has a class that has no locate step — a rule premise label denotes its slot directly, so it is representation-invariant by construction and neither confirms nor tests this claim. The claim therefore covers two of the resolver's three name classes, and the candidate-set obligation above applies to those two.
- **Sources**: []
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit a program or elaborator-accepted AST whose certificate citation lowers under `by r from [...]` but fails with `CertSlotNotAPremise` under the explicit spelling of the same argument (or vice versa), or one where the two spellings lower to different slots.
- **Proof**: [`test/CertSlotsSpec.hs` (`prop_priorArgumentCitationBothSpellings`, `prop_priorArgumentPremiseSpellingsAgree`, nested-certificate D8 fixtures), `src/Lara/Elaborate/Internal.hs` (`certSlotResolver` two-candidate locate), adversarial spec-review verification (trace N180, session 2026-08-13_001)]
- **Dependencies**: []
- **Tags**: elaboration, presentation-layer, name-resolution, lara-syntax@0.6
- **Last revised**: 2026-08-21 (2026-08-21_001#1)

## C32: A derived Map tag table materially reduces wire-decoder dispatch cost under the fixed #114 protocol
- **Statement**: On the fixed Apple M5 Pro, GHC 9.14.1, Lean 4.32.0, 60-unit, 564-record protocol used for issue #114, replacing `Lara.Wire.parseTag`'s 97-entry association-list scan with one top-level `Data.Map.Strict` table reduced median parse time from 1264.0 to 581.2 microseconds (54.02%) and median end-to-end time from 1459.8 to 784.8 microseconds (46.24%), without an observed Haskell-Lean verdict, exit-code, codec-boundary, replay, or frozen-byte divergence.
- **Conditions**: The table is a `NOINLINE` top-level CAF derived from `tagToString` over every bounded `Tag`; `tagToString` remains injective; measurements use the same machine, compiler versions, harness, and five-section protocol. The result does not estimate other machines or the separate issue #115 parser change. The pre-decoded check + render median moved by +5.55% despite an untouched path; that movement is recorded as noise, not attributed to the lookup change.
- **Sources**: []
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Re-run the fixed protocol with the association-list and Map implementations under matched conditions and observe a median parse reduction below 15%, or exhibit any accepted/rejected input whose stdout, stderr-pinned codec message, position, or exit code differs between the new Haskell driver and the Lean oracle.
- **Proof**: [`ara/evidence/results/parsetag_map_lookup.md`, `src/Lara/Wire.hs`, `test/WireSpec.hs`, `scripts/differential.sh`, trace N187, trace N188, PR #117, commit `a7b498a`]
- **Dependencies**: []
- **Tags**: performance, wire-codec, differential-testing, parseTag, issue-114
- **Last revised**: 2026-08-18 (2026-08-18_001#1)

## C33: Cursor representation, not tag dispatch, is what remained of the wire decoder's cost — and a byte-sliced cursor can carry code-point semantics without changing the observable contract
- **Statement**: A textual-wire decoder whose parser state is a lazy list of boxed characters pays enough per-character cons and pointer-chase cost that replacing the state with an O(1)-sliced strict byte buffer materially reduces decode latency, and the reduction is available without any change to accepted inputs, rejected inputs, or located error positions provided the cursor is made to count code points rather than bytes. The code-point discipline is what makes the substitution contract-preserving: it is forced by any reference implementation that locates errors over characters, and it is nearly free because the delimiter alphabet is ASCII, so only quoted payloads and comments pay the count while the bulk of the input advances by byte length.
- **Conditions**: The measured instance is `Lara.Wire`'s S-expression reader under the fixed Apple M5 Pro, GHC 9.14.1, Lean 4.32.0, 60-unit, 564-record protocol, with `SExpr` still carrying `String` atoms — the further gain from byte-backed atoms is untaken and unmeasured here. The contract-preservation argument holds because the bare-atom alphabet is printable ASCII and UTF-8 is self-synchronizing, so byte-level escape scanning and byte-length columns coincide with character-level ones exactly outside quoted payloads and comments; a grammar with non-ASCII delimiters would not inherit it. The frozen-measurement invariance is by construction, not coincidence: both `String` entry points were retained as wrappers, so the deterministic projection's `total_bytes` column kept its code-point semantics. The benchmark machine was under a load average of 3.0 to 4.4, so only the same-session baseline/after pair is comparable; the previously published table is not a valid comparator. The decode-latency reduction is separated from run-to-run drift by roughly a factor of eighteen: repeats of an identical binary move the pre-decoded check-and-render row by 2.5% to 2.6%, while the parse row moves by 46% with no unit slower. The concurrent movement on the pre-decoded row is ambient drift, not an effect of the change — it tracks a sub-path containing none of the edited module's code, and it grows with wall-clock time instead of staying fixed. The claim does not estimate other machines, other grammars, or the untaken byte-atom variant.
- **Sources**: [813.0 µs ← ara/evidence/results/bytestring_wire_parser.md «| Parse | 813.0 µs | 442.8 µs | −45.5% |» [result]; 442.8 µs ← ara/evidence/results/bytestring_wire_parser.md «| Parse | 813.0 µs | 442.8 µs | −45.5% |» [result]; 1115.5 µs ← ara/evidence/results/bytestring_wire_parser.md «| End-to-end | 1115.5 µs | 747.2 µs | −33.0% |» [result]; 747.2 µs ← ara/evidence/results/bytestring_wire_parser.md «| End-to-end | 1115.5 µs | 747.2 µs | −33.0% |» [result]; +2.96% ← ara/evidence/results/bytestring_wire_parser.md «| `String` → `ByteString` | +2.96% | +3.07% | −46.13% |» [result]; 2.51%..2.63% ← ara/evidence/results/bytestring_wire_parser.md «| Same `String` binary, run 1 → run 2 | −2.63% | −2.66% | −1.73% |» [result]; -46.13% (range -52.10%..-39.81%, 0/60 slower) ← ara/evidence/results/bytestring_wire_parser.md «and **0 of 60 units slower**, and it still measures −44.24% against the slowest» [result]; 1.43x ← ara/evidence/results/bytestring_wire_parser.md «The parse to check + render ratio fell from 2.71× to 1.43×.» [result]; 581 positive / 56 negative ← ara/evidence/results/bytestring_wire_parser.md «`scripts/differential.sh`: 581 positive cases passed with zero failures; 56» [result]]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit an input — accepted or rejected — whose stdout, exit code, or located codec message and position differ between the byte-sliced reader and the character-list reader it replaced; or re-run the fixed protocol with both readers under matched conditions and observe a median parse reduction below 15%, which would mean cursor representation was not what remained of the decoder's cost.
- **Proof**: [`ara/evidence/results/bytestring_wire_parser.md`, `src/Lara/Wire.hs`, `test/WireSpec.hs` (`referenceParseSExpr` differential over 581 committed inputs plus eleven exact position pins), `scripts/differential.sh`, `docs/m5-freeze-checklist.md`, trace N191, trace N192, trace N193, PR #118, commit `a2904d7`]
- **Dependencies**: [C32]
- **Tags**: performance, wire-codec, differential-testing, unicode, trusted-base, issue-115, issue-116

## C34: Necessity holds in every fixed context, while empty defeat refutes the universal converse
- **Statement**: For every fixed signature, policy, and backend registry, executable realizability implies the frozen `CompilerInvariant`. A converse quantified over all fixed contexts is false: when `policy.defeat = emptyDefeat`, the singleton self-edge satisfies the invariant but is not realizable.
- **Conditions**: The counterexample uses a valid context whose defeat policy has no contrary or exception declarations. Under such a policy every compiled edge is false, while the singleton self-edge still satisfies the frozen range and conflict-completeness fields. This establishes non-sufficiency for the empty-defeat class and refutes the universal converse; it does not establish non-sufficiency for every fixed policy. Generated-policy universality is a different theorem. The M0 carrier remains unchanged.
- **Sources**: [`singleton self-edge ← lean/Lara/Examples/Realizability.lean:24-26 «def oneSelfEdge (p : Atom) : Invariants.StructuredAF := { nodes := [p], attack := fun i j => decide (i = 0 ∧ j = 0) }» [input]`, `axiom set ← focused AxCheck gate «Axiom audit passed.» [result]`]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit a successful checker witness under a policy whose defeat component is `emptyDefeat` that compiles, up to `StructuredAFIso`, to `oneSelfEdge`; or refute the necessity theorem by exhibiting an executable realization whose target violates `CompilerInvariant`.
- **Proof**: [`lean/Lara/Realizability.lean` (`realizable_invariant`), `lean/Lara/Examples/Realizability.lean` (`noAttack_of_emptyDefeat`, `compiled_no_edges_of_emptyDefeat`, `emptyUnitCheck_ok`, `oneSelfEdge_invariant`, `oneSelfEdge_not_realizable`), `lean/AxCheck.lean`, trace N225, trace N228, trace N229]
- **Dependencies**: []
- **Tags**: mechanization, compilation-image, realizability, counterexample, fixed-policy, M1
- **Last revised**: 2026-08-26 (2026-08-26_001#5)

## C35: The skeptical reading of claim status generalizes across extension semantics; the credulous reading is not a function into it
- **Statement**: A four-state claim status defined per extension lifts to many extensions under the skeptical (universally quantified) reading, and the lift agrees with the single-extension definition when the semantics has exactly one extension. Under the credulous (existentially quantified) reading, no four-state function can simultaneously return `justified` exactly when `inSome` is true and `defeated` exactly when `outSome` is true. On the preferred-semantics two-cycle, one argument satisfies both bits. Separately, the claim-level lift ("in every extension some support argument is accepted") is not recoverable from per-argument acceptance data, so an observation function cannot factor through a per-argument profile.
- **Conditions**: Holds over a finite conclusion-labelled framework with a decidable attack relation, for the five semantics mechanized here (grounded, complete, preferred, stable, semi-stable). The agreement half additionally requires a duplicate-free carrier, which compilation supplies. The non-functionality theorem fixes preferred semantics and quantifies over every `AF → Arg → Status` candidate satisfying the two biconditionals; it does not claim that every semantics admits the two-cycle witness. Mutual exclusivity of the justified and defeated skeptical readings requires a non-empty extension set and conflict-freedom of every extension, which the interface does not require and which is therefore supplied per instance. The interface cannot detect a semantics declared outside its module (#198).
- **Sources**: [`two-cycle ← lean/Lara/Examples/Semantics.lean «def twoCycle : AF where args := [0, 1]» [input]`, `preferred extensions ← lean/Lara/Examples/Semantics.lean «theorem preferredSem_enumerate_twoCycle : preferredSem.enumerate twoCycle = [[0], [1]]» [result]`, `credulous non-functionality ← lean/Lara/Examples/Semantics.lean «theorem credulous_not_functional : ¬ ∃ credulous : AF → Arg → Status» [result]`, `ten pairwise separations ← lean/Lara/Examples/Semantics.lean «theorem five_semantics_pairwise_distinct» [result]`, `axiom set ← lake env lean AxCheck.lean | scripts/check-axioms.sh «Axiom audit passed.» [result]`]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit a semantics among the five whose observation disagrees with `Grounded.statusC` on a framework with exactly one extension; exhibit an `AF → Arg → Status` function satisfying both credulous biconditionals under preferred semantics; or exhibit two semantics agreeing on every per-argument acceptance profile and every claim observation, which would show the non-factoring result vacuous.
- **Proof**: [`lean/Lara/Semantics.lean` (`observe_grounded`, `groundedSem_enumerate`, `observe_gap`, `justified_defeated_exclusive`, the five `*_specConflictFree`), `lean/Lara/Examples/Semantics.lean` (`credulous_not_functional`, `profile_preferredSem_twoCycle_symm`, `observe_not_determined_by_profile`, `five_semantics_pairwise_distinct`), `lean/AxCheck.lean`, `docs/theory-m2a-observation.md`, trace N230, trace N232, trace N236]
- **Dependencies**: []
- **Tags**: mechanization, extension-semantics, claim-status, credulous-skeptical, non-collapse, M2a
- **Last revised**: 2026-08-28 (2026-08-28_001#2)

## C36: A semantics with no extension must report its silence, not a verdict
- **Statement**: An aggregation over extensions that yields only a status fabricates verdicts when the extension set is empty, because a universally quantified guard over an empty collection is vacuously true for opposing conditions simultaneously. The failure is not hypothetical for any semantics whose existence is conditional. Making the empty case a distinct constructor of the answer type — rather than a side condition in prose — is what forces callers to distinguish "the semantics rejects this claim" from "the semantics says nothing here". The same vacuity arises independently at the support quantifier, where it is asymmetric and therefore worse: it yields specifically the rejecting verdict.
- **Conditions**: Established for stable semantics, which is the one of the five whose extension set can be empty; the bare odd cycle is the witness, and emptiness is a property of the whole framework rather than of containing an odd cycle — adding an argument that attacks the cycle restores a stable extension. The guard-order question is separate and carries no safety content: both hazards are blocked under either arrangement of the first two guards, since each precedes the aggregation guards. Untested boundary: no claim is made that stable is the only semantics with conditional existence.
- **Sources**: [`bare three-cycle ← lean/Lara/Examples/Semantics.lean «def threeCycle : AF where args := [0, 1, 2]» [input]`, `stable emptiness ← lean/Lara/Examples/Semantics.lean «theorem stableSem_enumerate_threeCycle : stableSem.enumerate threeCycle = []» [result]`, `emptiness is not the odd cycle ← lean/Lara/Examples/Semantics.lean «theorem stableSem_enumerate_threeCycleAttacked» [result]`, `support-level vacuity ← lean/Lara/Semantics.lean «theorem claimDefeatedB_of_nil {F : AF} {E : List Arg} {c : Grounded.Claim} (hs : c.support = []) : claimDefeatedB F E c = true» [result]`]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit a framework on which `observe` returns a `Status` for a claim with non-empty support while the semantics has no extension; or show that the aggregation guards are reachable on an empty extension set, which would make the constructor unnecessary; or exhibit a semantics whose empty-extension case yields a defensible verdict rather than silence.
- **Proof**: [`lean/Lara/Semantics.lean` (`no_verdict_on_empty`, `observe_noExtension_iff`, `enumerate_ne_nil_of_observed_ne_gap`, `claimDefeatedB_of_nil`, `claimAcceptedB_of_nil`), `lean/Lara/Examples/Semantics.lean` (`stableSem_enumerate_threeCycle`, `observe_stableSem_threeCycle`, `observe_stableSem_threeCycle_ne_justified`, `observe_stableSem_threeCycle_ne_defeated`, `threeCycle_enumerate_nonStable`), `lean/AxCheck.lean`, `docs/theory-m2a-observation.md`, trace N232, trace N236]
- **Dependencies**: [C35]
- **Tags**: mechanization, extension-semantics, nonexistence, fabricated-verdicts, stable, M2a

## C37: Fresh accepted instance addition is a sink extension on the old grounded carrier
- **Statement**: When a source update appends one fresh, fully supported rule instance and the edited source is accepted, the old compiled argumentation framework embeds as the old-node subgraph of a sink extension. Old grounded labels are preserved; a justified source claim cannot become refuted or both, and a both source claim cannot become refuted solely through that append.
- **Conditions**: Holds for the one-step `addInstance` constructor with exact accepted source and target runs, name-and-term freshness, complete support for the new term, and the extended-list attack-completeness obligation. It is a grounded-semantics result about the old carrier; it does not claim label preservation for the new node or for arbitrary extension semantics.
- **Sources**: [`sink boundary` ← `docs/theory-m3-source-updates.md:239-240` «A fresh instance is a sink in the old framework: freshness prevents old raw attacks from naming it, while old-to-old edges and labels are preserved.» [result]; `axiom set` ← `lean/AxCheck.lean` via `scripts/check-axioms.sh` «Axiom audit passed.» [result]]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit an accepted successful fresh `addInstance` update satisfying the stated support and coverage conditions that changes an old justified claim to refuted or both, or an old both claim to refuted.
- **Proof**: [`lean/Lara/Grounded.lean` (`Grounded.SinkExtension`, `label_old`, `justified_preserved`, `contested_not_defeated`), `lean/Lara/Update.lean` (`addInstance_sink_status_monotone`), `lean/Lara/Examples/Update.lean` (typed addInstance matrix), trace N239, trace N240]
- **Dependencies**: []
- **Tags**: mechanization, source-update, addInstance, sink-extension, grounded-semantics, M3

## C38: CleanBase is a sufficient boundary for public additive/core equality
- **Statement**: A successful additive source update has the same public and grounded-core report when its exact accepted source run starts with an empty quarantine seed. Without that condition, equality is not guaranteed: adding an attack from a blocked source can expand the blocked closure and change another query's public report to `evidence-blocked`.
- **Conditions**: Applies to one-step `addLeaf`, `addAttack`, and `addInstance` updates. `CleanBase` means the source accepted run's `removedSeed` is empty. The claim does not cover an additive update after an earlier quarantine, update composition, or tightening.
- **Sources**: [`clean-base definition` ← `docs/theory-m3-source-updates.md:136-142` «`Lara.Update.CleanBase run` means exactly `run.admission.prune.removedSeed = []` for the source accepted run.» [input]; `unconditional counterexample` ← `docs/theory-m3-source-updates.md:158-165` «This witness refutes an unconditional additive/core equality theorem; it does not make `CleanBase` necessary for every individual run.» [result]]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit an accepted successful additive update satisfying `CleanBase` whose public and grounded-core reports differ, or show that the blocked-growth witness does not pass the real admission/check/update pipeline.
- **Proof**: [`lean/Lara/Update.lean` (`additive_target_blockedSet_eq_nil`, `additive_public_eq_core`, `additive_public_ne_evidenceBlocked`), `lean/Lara/Examples/Update.lean` (`addAttack_blocked_growth`, typed additive public matrices), `test/update-matrices.golden`, trace N239]
- **Dependencies**: [C25]
- **Tags**: mechanization, source-update, quarantine, public-reporting, clean-base, M3

## C39: Pairwise attack completeness is a real admissibility condition for instance addition
- **Statement**: Adding a fresh, completely supported rule instance can still make an accepted source invalid, because the new argument creates contrary pairs that require declared covering attacks. The extended argument list's `AttackComplete` property is therefore a genuine admissibility condition, not proof scaffolding.
- **Conditions**: Holds at the one-step `addInstance` boundary. The rejection witness keeps name and term fresh and supplies complete support; it fails specifically because one new contrary pair has no declared conflict edge. Other update rejection causes are outside this witness.
- **Sources**: [`preservation premise` ← `docs/theory-m3-source-updates.md:83-86` «`applyUpdate_addInstance_ok` assumes an accepted source, name-and-term freshness, well-sortedness of the new term, a complete support derivation for it, and `Compile.AttackComplete` for the old retained arguments extended by that term.» [input]; `non-unconditional boundary` ← `docs/theory-m3-source-updates.md:88-89` «None says that its constructor always succeeds.» [result]]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Prove that every fresh, well-sorted, completely supported single-instance append preserves `AttackComplete`, or show that `addInstance_uncovered_rejected` fails for a reason other than its uncovered contrary pair.
- **Proof**: [`lean/Lara/Update.lean` (`applyUpdate_addInstance_ok`), `lean/Lara/Examples/Update.lean` (`addInstance_uncovered_rejected`), trace N239]
- **Dependencies**: []
- **Tags**: mechanization, source-update, addInstance, attack-completeness, rejection-witness, M3

## C40: A parent's typing is insensitive to which backend certified its children
- **Statement**: In a proof-carrying argument calculus where a rule instance's side conditions reach its subterms only through their arity and their conclusions, a subterm may be replaced by any term with the same conclusion and obligations without disturbing the parent's typing — and the parent has no side condition able to express which backend certified the replacement. Backend opacity is therefore a consequence of how the instance rule is shaped, not an extra property that must be imposed on it.
- **Conditions**: Holds for both the premise and the discharge position of the support-term instance rule. The premise case needs only that `List.set` preserves length; the discharge case additionally needs the question key carried across the swap, since four side conditions read the discharge map through its key projection. Requires the replacement to be independently typed at the same conclusion and obligations — the firewall composes derivations, it does not manufacture one. Untested boundary: rule forms whose side conditions inspect a subterm's structure rather than its conclusion.
- **Sources**: [`three length fields` ← `docs/theory-b0-backend-compositionality.md:~110` «`InstSide` reaches `ws` only through three length fields — `lenAs`, `lenCs`, `lenOs` — and `List.set` preserves length.» [result]; `mechanical confirmation` ← `docs/theory-b0-backend-compositionality.md:~113` «the premise half's proof is `refine .inst { hside with lenAs := …, lenCs := …, lenOs := … }`, and *that elaborating* is Lean confirming those three fields are the only place `InstSide` mentions `ws`.» [result]]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit a side condition of the instance rule that constrains a premise or discharge subterm beyond its length, conclusion, and obligations — which would make the structure update over only the length fields fail to elaborate — or a swap of same-conclusion subterms that does not preserve the parent's typing.
- **Proof**: [`lean/Lara/BackendComposition.lean` (`prem_subterm_swap`, `dis_subterm_swap`, `map_fst_set_of_getElem?`), `lean/Lara/Examples/BackendComposition.lean` (`mixed_swap`, `mixed_dis_swap`), trace N248]
- **Dependencies**: []
- **Tags**: mechanization, backend-composition, firewall, opacity, B0

## C41: A backend's dependency report is evaluable where its acceptance is not
- **Statement**: Dependency reporting and certificate acceptance have different evaluation requirements, and the gap is exploitable. Reporting needs only that the step resolves — rule, instantiation, registry entry, theory digest — plus the certificate decoder; acceptance additionally needs the backend's domain computation. So a backend whose acceptance cannot be evaluated in a given setting may still have its report evaluated there, and conformance artifacts built on reports are not blocked by the obstacles that block artifacts built on acceptance.
- **Conditions**: Requires the dependency report to be a function of the certificate alone, as the backend interface's `uses` field is, rather than of the acceptance run. Demonstrated where the obstacle is kernel reducibility: the report path terminates at a decoder primitive that reduces per literal, while the acceptance path reaches primitives that do not. The two paths sit in the same parser module, so which side of the line a given backend falls on must be checked, not assumed.
- **Sources**: [`report path stops at toNat?` ← `docs/theory-b0-backend-compositionality.md:~250` «`ord@1`'s `ordUses` routes through `decodeCert` → `decodeSlot` → `parseCanonNat` → `String.toNat?`, which is per-literal provable» [result]; `acceptance path is blocked` ← `docs/theory-b0-backend-compositionality.md:~215` «`ord@1` acceptance routes through `Cell.parseDecimal` → `parseUnsigned` → `String.splitOn`, and through `parseCanonInt` → `String.startsWith`.» [result]; `stepDeps never calls acceptance` ← `lean/BackendDepsGolden.lean` «`Lara.Support.stepDeps` never calls `acceptsFull`.» [result]]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Show that computing a dependency report for a registered backend requires its acceptance to hold or be evaluated — for instance a report definition that consults the acceptance result — or exhibit a backend whose `uses` path reaches the same irreducible primitives its acceptance path does, making the separation unavailable in practice.
- **Proof**: [`lean/Lara/Examples/BackendComposition.lean` (`depsMixedTerm_certDeps`, `depsMixedTerm_both_halves_nonempty`), `test/backend-deps.golden`, `scripts/check-backend-deps-golden.sh`, trace N246, N244]
- **Dependencies**: [C43]
- **Tags**: mechanization, backend-composition, dependency-accounting, conformance, kernel-reduction, B0

## C42: A sealed judgment reached only from tests is not evidence about the production path
- **Statement**: The existence and correctness of a sealed type that carries an invariant says nothing about whether the shipped system establishes that invariant; what matters is whether the production path constructs it. A mechanized accounting result can therefore have no executable counterpart while every component needed for one is present and correct — the components compute the right value and the production path discards it before anything can observe it.
- **Conditions**: Arises where a checker reaches a subsystem through a lower-level entry point than the sealed constructor — here the production oracle calls the backend directly rather than through the sealing function, so the sealed judgment is only ever built by tests. The failure is invisible to component-level tests, which exercise the sealing function, and to end-to-end acceptance tests, which do not observe the discarded value. Detected by locating the constructor's call sites in shipped code specifically.
- **Sources**: [`sealed constructor is test-only` ← `docs/theory-b0-backend-compositionality.md:~176` «`strictCheck` — the only constructor of the sealed `StrictJudgment`, and the only thing retaining `sjDependencies` — is called from `test/` and from nowhere in `src/`.» [result]; `the discard` ← `docs/theory-b0-backend-compositionality.md:~180` «The production checker reaches backends through `buildCertOk`, which called `runBackend` and **discarded the dependency report**.» [result]; `the consequence` ← `docs/theory-b0-backend-compositionality.md:~182` «Lean proved `certDeps` accounts for every certified occurrence; the shipped checker accounted for none of them.» [result]]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Show that the pre-repair production path did observe the dependency report — a shipped call site constructing the sealed judgment, or a consumer reading the report through some other route — which would make the accounting gap illusory rather than real.
- **Proof**: [`src/Lara/Driver/Internal.hs` (`buildCertOk`), `src/Lara/SupportTerm.hs` (`CertOutcome`, `certAccepted`), `src/Lara/Strict/Deps.hs`, `test/StrictSpec.hs` (`prop_mixedBackendDepsCollected`), issue #204, trace N247]
- **Dependencies**: []
- **Tags**: mechanization, conformance, production-parity, dependency-accounting, B0

## C43: Heterogeneous backend composition requires no relating binder
- **Statement**: Certified steps from different registered backends compose in one checked argument without any shared backend logic, because each occurrence's formula type, theory data, and consequence relation are bound inside its own existential. Conjoining two occurrences' consequences asserts nothing that connects them. The content of the result is the *absence of a binder relating* the occurrences — not the disjointness of what they range over, which is neither provable nor true in general, since a registry may map two identities to the same core.
- **Conditions**: Holds for the per-occurrence consequence obtained from any registered identity in a backend-first closed registry, where digest selection occurs only after exact identity lookup and a digest resolves to theory data rather than to behavior. The accompanying dependency-union law holds for the same reason and needed no change: it never had to look inside a backend. Registration distinctness at a concrete registry is provable only through projections that do not mention the record's own formula type. Not parametricity — this quantifies over registered identities, not relationally over related backends.
- **Sources**: [`the binder structure` ← `docs/theory-b0-backend-compositionality.md:~72` «conjoining two occurrences' consequences introduces **no binder requiring them to share a formula type, a theory, or a consequence relation**.» [result]; `the disclaimer` ← `docs/theory-b0-backend-compositionality.md:~78` «A registry is an arbitrary function `BackendId → Option (RegisteredBackend canon)`; nothing stops it mapping two identities to the same core, in which case the two formula types *are* equal.» [result]; `distinctness via projection` ← `docs/theory-b0-backend-compositionality.md:~262` «`mixed_registrations_distinct` is proved through a **non-dependent projection** — the resolved theory's *length*» [result]]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit a binder in the occurrence-local consequence, or in the typing judgment above it, that forces two occurrences with different registered identities to share a formula type, theory, or consequence relation — or a checked term carrying two identities that fails to type for a reason traceable to their being different.
- **Proof**: [`lean/Lara/BackendComposition.lean` (`OccurrenceConsequence`, `hetero_occurrences_accounted`, `certDeps_eq_union`, `usedBackends_accounted`), `lean/Lara/Examples/BackendComposition.lean` (`mixed_usedBackends`, `mixed_registrations_distinct`, `mixed_swap_accounted`), trace N243, N248]
- **Dependencies**: [C40]
- **Tags**: mechanization, backend-composition, heterogeneity, occurrence-level, B0

## C44: A universal lower bound is distinct from worst-case tightness
- **Statement**: In the transparent grounded evaluator, every finite framework incurs at least `n²` attack queries. The two-node all-attacks regression refutes the rejected exact pointwise `n³` inequality at `n = 2`, but does not prove that the quadratic lower bound is asymptotically optimal. Quartic lower bounds are existential worst-case results requiring families whose successful defense scans run late, and an unrestricted witness does not establish tightness on the realizable class.
- **Conditions**: Applies to the frozen attacker-first, defense-scan-second evaluator and attack-oracle query model over finite carriers. Restricted-class tightness uses the fixed-context realizable `quarticAF` family, and the carrier-status transfer applies after the nonempty-support guard. No unrestricted-AF witness establishes a result for the fixed-context realizable class without its own realization proof.
- **Sources**: [`universal bounds` ← `docs/theory-m2b-complexity.md:203-208` «`groundedC_cost_le : cost ≤ n³(1 + n)` and `groundedC_cost_ge : n² ≤ cost` for every framework, `n = F.args.length`.» [result]; `realizable quartic witness` ← `docs/theory-m2b-complexity.md:209-217` «The three-block family `quarticAF k` / is realizable in the fixed context (`quartic_realizable`, with `quartic_size : size = 3k`), and for `2 ≤ k` pays at least `k⁴` attack queries (`quartic_cost_ge`) / Together with `groundedC_cost_le` this is worst-case Θ(n⁴) *over the fixed-context realizable class*» [result]; `carrier-status transfer` ← `docs/theory-m2b-complexity.md:218-229` «The quartic floor transfers to this surface: `carrierStatus_quartic_cost_ge` (the `d` claim has nonempty complete support, so the grounded branch runs and is fully counted).» [result]]
- **Status**: supported
- **Provenance**: user-revised
- **Falsification**: Exhibit a finite carrier violating either proved universal grounded-cost bound, a fixed-context checker or compile-image counterexample to `quartic_realizable`, a qualifying quartic-family instance violating `quartic_cost_ge`, or a carrier-status execution that bypasses the stated nonempty-support condition.
- **Proof**: [`groundedC_cost_ge`, `groundedC_cost_le`, `quartic_realizable`, `quartic_cost_ge`, `carrierStatus_quartic_cost_ge`; commits f0e36ab, 9e3d557, 0193f5c; `docs/theory-m2b-complexity.md`]
- **Dependencies**: [C34]
- **Tags**: M2b, grounded-semantics, query-complexity, short-circuiting, realizability, tightness
- **Last revised**: 2026-08-31 (2026-08-31_001#3)

## C45: Failure of one realization construction does not establish tractability
- **Statement**: Rejecting an arbitrary-digraph realization kit does not by itself imply a tractability-inducing invariant; a restricted class may reject that construction and remain hard through a specialized reduction. Allowing the policy to vary with each source instance also changes the class whose restriction is being studied.
- **Conditions**: Applies to complexity claims over M1 `Realizable` carriers. The present support is one formula-independent canon, signature, policy, and registry with a realization theorem for every output of a specialized 3SAT reduction. It does not establish that every failed realization construction preserves hardness; NP-membership bookkeeping remains paper-level.
- **Sources**: [`renewed gate` ← `docs/theory-m2b-complexity.md:126-134` «2026-08-31 — HARDNESS / Every mandatory theorem named by the INCONCLUSIVE record's obstruction section exists `sorry`-free under the frozen context / the reduction target family is realizable with polynomially bounded carrier accounting» [result]; `mechanized reduction` ← `docs/theory-m2b-complexity.md:235-246` «`reduce_correct : Formula3.Satisfiable φ ↔ FixedCredComplete (reduceCode φ)` / `reduce_realizable : M2bPromise (reduceCode φ)` / `reduce_nodes` and `reduce_byteSize` — polynomial output size under the frozen D5 measures.» [result]; `paper boundary` ← `docs/theory-m2b-complexity.md:248-250` «Paper-level only: NP-completeness bookkeeping (encodings, machine model, membership in NP). It is deliberately not a Lean statement» [result]]
- **Status**: supported
- **Provenance**: user-revised
- **Falsification**: Prove that failure of the specified realization kit entails a tractability-inducing invariant and adequate algorithm, find a source formula whose `reduceCode` output violates the fixed `M2bPromise`, invalidate either direction of `reduce_correct`, or prove that synthesizing a fresh policy per source instance preserves the same fixed-context class.
- **Proof**: [`checkUnit_formula_ok`, `reduceIso`, `reduce_realizable`, `reduce_nodes`, `reduce_byteSize`, `reduce_correct`, `selfEdgeCode_not_realizable`; commits e9f7842, 8155ec7; `docs/theory-m2b-complexity.md`]
- **Dependencies**: [C34]
- **Tags**: M2b, realizability, hardness, tractability, fixed-policy, reduction-discipline
- **Last revised**: 2026-08-31 (2026-08-31_001#3)

## C46: Verified numeral decoding separates identifier injectivity from attack completeness
- **Statement**: When generated decimal identifiers are inverted through a proved decoder round-trip, their atom representation is injective; identifier-collision obligations can be discharged independently of the generated attack-family completeness proof.
- **Conditions**: Applies to the M2b gadget's decimal payloads and closed `GadgetLeaf` encoding under the fixed module-ownership boundary. It does not make `AttackComplete` automatic: the assembly still needs root-conclusion inversion, contrary characterization, and declared-attack witnesses.
- **Sources**: [`decoder round-trip` ← `docs/theory-m2b-complexity.md:83-92` «`natRepr_inj : Nat.repr m = Nat.repr n → m = n` is proved by applying a decoder with a proven round-trip, never by induction over string representations.» [result]; `attack-completeness boundary` ← `docs/theory-m2b-complexity.md:170-181` «**Exact attack completeness** (`formulaAttacks_complete`, the highest-risk step) / `litAtom_inj` (which is two applications of `natRepr_inj` to the `lit` atom's decimal payloads) forces equal variable indices when two root conclusions collide.» [result]]
- **Status**: testing
- **Provenance**: ai-suggested
- **Falsification**: Exhibit distinct natural-number payloads with equal `Nat.repr`, a collision in `GadgetLeaf.encode`, or a proof dependency showing that decimal injectivity cannot be established before the attack-completeness characterization.
- **Proof**: [`natRepr_inj`, `GadgetLeaf.encode_inj`, `formulaAttacks_complete`, `checkUnit_formula_ok`; commits 44ba0bf, a28ed93, e9f7842]
- **Dependencies**: [C34, C45]
- **Tags**: M2b, numeral-injectivity, gadget-encoding, attack-completeness, proof-architecture
- **Last revised**: 2026-08-31 (2026-08-31_001#3)

## C47: Transporting well-formed checked support across an accepted bridge does not transport grounded status
- **Statement**: Preservation of a claim's grounded status across a structural bridge is strictly stronger than preservation of its checked support. A bridge edge can be accepted, and the source claim's complete checked support can be present unchanged and still checked in the target, while the claim's four-state status differs at the two endpoints — because status is fixed by the whole attack structure the target admits, not by the support term alone. Exact support transport is therefore necessary but not sufficient for status preservation, and any status-preservation theorem must quantify over the target's attackers rather than over the transported term.
- **Conditions**: Shown for one accepted endobridge between two worlds of a single scientific context, under identity claim translation, where the target admits one additional unattacked checked attacker whose conclusion is declared contrary to the source claim. The separation depends on the missing-conflict search being directional, so the contrary pair forces one edge and not its converse; a symmetric conflict requirement would leave the claim contested rather than defeated and would not exhibit the gap. The other side of the boundary is now T8 (C50): under the additional StatusBridge hypotheses — matched and attack forth/back — status is preserved, and the T7 edge fails matched at leaf l2; justified, defeated, gap, and contested transport off the identity across contexts with disjoint signatures. Untested boundary: status behaviour under non-injective (merging) translations.
- **Sources**: [`source status justified` ← `lean/Lara/Examples/PW.lean:117` «theorem t7_src_justified : cmpStatus wT7src pA = Status.justified := by decide» [result]; `target status defeated` ← `lean/Lara/Examples/PW.lean:122` «theorem t7_tgt_defeated : cmpStatus wT7tgt pA = Status.defeated := by decide» [result]; `support identity across the bridge` ← `lean/Lara/Examples/PW.lean:142` «    (claimAt wT7src pA).support = [0]» [result]; `directionality of the conflict search` ← `lean/Lara/Check/Program.lean:279` «      if Attack.contraryMatchB canon dp» [input]; `T7 fails matched at leaf l2` ← `lean/Lara/Examples/PWStatus.lean` «theorem t7_not_statusBridge :» [result]; `four statuses transport off the identity` ← `ara/evidence/proofs/pw_t8_status_preservation.md:47-51` «transports `justified`, `defeated`, `gap`, and
`contested` off the identity» [result]]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit a checked bridge discipline under which equality of source and target complete checked supports forces equality of grounded status — i.e. prove status preservation from support transport alone, with no premise about the target's attackers. Equivalently, show that the T7 witness is not a legal model: that `unitT7tgt` is rejected by the unchanged `checkUnit`, that the bridge edge fails `Frame.A`, or that `claimAt` disagrees at the two worlds.
- **Proof**: [`Lara.Examples.PW.t7_witness`, `t7_src_justified`, `t7_tgt_defeated`, `t7_transport_wellFormed`, `t7_support_transported`, `t7_dia_defeated`, `t7_box_defeated`, `t7_dia_defeated_src`, `t7_box_defeated_src`; `evidence/proofs/pw0_outer_model.md`; PR #221, commits 817824f and 86c5163; axiom audit 1619 declarations PASS]
- **Dependencies**: []
- **Tags**: PW0, possible-world, status-preservation, support-transport, T7, T8-boundary, mechanized
- **Last revised**: 2026-09-04 (2026-09-04_004#1)

## C48: Checked-support transport needs only environment-parameter correspondences, and it ties the outer model's applicability judgment to the checker
- **Statement**: Exact transport of the checked-support judgment across a structural bridge is provable from correspondences on exactly the parameters the typing judgment reads — evidence typing under a leaf renaming, policy carrying the translated rule at the same identifier, and certificate acceptance surviving translation of the encoded step — over a shared source canonicalizer, with no condition on anything the judgment does not read. Under such a bridge the obligation list transports verbatim (question keys are rule-local vocabulary the claim translation never touches), so completeness transports unconditionally; and the transport supplies the outer possible-world model's applicability judgment with a checker tie: an admitted world pair carries every complete checked source argument into the target's own accepted program with the translated conclusion. Support transport remains strictly weaker than status preservation.
- **Conditions**: Shown for a bridge-global, functional partial symbol translation (predicate and constructor namespaces independent), a total leaf renaming, question keys frozen across the bridge, and a canonicalizer shared by both environments. Untested boundary: edge-indexed (world-dependent or ambiguous) translation, partial leaf maps, and bridges renaming question vocabulary. Attack correspondence is now a separate T8 theorem package (C50; `Lara.PW.Status`; `ara/evidence/proofs/pw_t8_status_preservation.md`), not a remaining boundary of this T6 claim. Exact path composition is now a separate T9 theorem package (`Lara.PW.Compose`; `ara/evidence/proofs/pw_t9_path_composition.md`), not a remaining boundary of this T6 claim.
- **Sources**: [`1713 audited declarations, 84 PW-T6` ← `ara/evidence/proofs/pw_t6_transport.md` «1713 audited declarations across the library, of which 84 are PW-T6 — every» [result]; `130-job build` ← `ara/evidence/proofs/pw_t6_transport.md` «Build completed successfully (130 jobs).                        EXIT: 0» [result]; `cert_ok inhabited off the identity` ← `ara/evidence/proofs/pw_t6_transport.md` «`cert_transport` running the transported derivation through the» [result]]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit a checked source support and a bridge satisfying the three contract clauses whose transport is defined but not checked in the target environment, or whose obligation list changes under transport; or show a fourth clause is required — a `HasSupport` parameter correspondence outside leaf typing, rule lookup, and certificate acceptance without which transport fails.
- **Proof**: [`Lara.PW.support_transport`, `support_transport_complete`, `supports_transport`, `transport_occurrences_accounted`, `Admits`, `admits_transport`, `instAPat_tr`, `equiv_tr`; `Lara.Examples.PW.t7_t6_boundary`, `ren_transport`, `ren_translationUndefined`, `bridgeCert`, `cert_accept_translated`, `cert_reject_untranslated`, `cert_transport`; `ara/evidence/proofs/pw_t6_transport.md`; PR #223, commit 13ae1d7, plus the #224 witness; axiom audit 1713 declarations PASS]
- **Dependencies**: [C47]
- **Tags**: PW-T6, possible-world, structural-bridge, support-transport, obligations, accept-discharge, mechanized
- **Last revised**: 2026-09-04 (2026-09-04_004#1)

## C49: Preserving a linking discipline's whole occurrence profile buys the context quantifier for free
- **Statement**: A program transformation that preserves everything a linking discipline reads — each argument's conclusion, each rule instance's identity, and therefore every contrary match and every attackability test — commutes with the saturation that linking performs, so the linked programs compile to the same abstract framework and no context can separate them. Certificate relabeling is such a transformation. The consequence is that backend replacement is a *congruence*, not merely a whole-program equivalence: the context quantifier costs no additional argument, because what carries the proof is profile-preservation rather than any property of the interface between fragment and context. That is also why this route does not have to answer what a fragment's semantic interface *is* — the question that blocks a logical-relation formulation of the same milestone.
- **Conditions**: Holds for grounded semantics over the frozen compilation carrier, for admissible contexts — the link guard passes, both sides' declared material is well-formed relative to the *linked* environment, and the linked program passes the signature stage — whose own assurances satisfy `FixesContext`, and for a forward-only acceptance-preservation hypothesis. Admissibility supplies an accepted source and preservation supplies an accepted target, so both detailed observations land in `.observed`; without it their rejection outcomes need not agree. Openness is leaf-name openness only: term-level holes are unrepresentable because the compile boundary forces an empty obligation set on every declared argument. Untested boundary: contexts carrying assurances moved by the relabel, generic extension semantics, two-way acceptance, and relational quantification over related backends.
- **Sources**: [`138-job build` ← `ara/evidence/proofs/m4_contextual_adequacy.md:54` «Build completed successfully (138 jobs).» [result]; `audit outcome` ← `ara/evidence/proofs/m4_contextual_adequacy.md:51` «Axiom audit passed.» [result]; `coverage outcome` ← `ara/evidence/proofs/m4_contextual_adequacy.md:47` «AxCheck coverage passed (218 declarations).» [result]; `1925-entry audit roster` ← `ara/evidence/proofs/m4_contextual_adequacy.md:57` «`AxCheck.lean` now lists 1925 declarations across the library.» [result]]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit an admissible context and an injective, acceptance-preserving certificate relabel whose two links observe different statuses for some exported conclusion; or show the saturation does not commute — a cross-boundary attack the link emits for one side and not for its relabeling. Either would have to defeat the profile-preservation argument, since the compiled frameworks are equal by node-conclusion and edge-relation equality rather than by a bisimulation.
- **Proof**: [`Lara.Context.crossAttsFrom_map`, `crossAtts_relabel`, `link_relabel_commutes`, `checkUnit_map`, `compileUnit_map`, `backend_replacement_congruence`, `registry_swap_congruence`, `link_attackComplete`, `link_checked`, `link_merge_status_eq`; witnesses `Lara.Examples.Linking.certAdmissible`, `cert_congruence_witness`, `cert_relabel_moves`, `cert_registry_swap_witness`; `ara/evidence/proofs/m4_contextual_adequacy.md`; `docs/theory-m4-contextual-adequacy.md`; PR #218, commits 78493f5, 776e50c, 0dc676c, 4c308c2, c61c91f]
- **Dependencies**: []
- **Tags**: M4, context-calculus, backend-replacement, congruence, representation-independence, saturation, mechanized
- **Last revised**: 2026-09-03 (2026-09-03_001#1)

## C50: Grounded status is preserved across a structural bridge exactly when the compiled attack structures are related by a total attack bisimulation that respects support — and the design's isomorphism is stronger than needed
- **Statement**: A claim's four-state grounded status is invariant between two compiled argumentation frameworks whenever the frameworks are related by a total attack bisimulation — a relation on arguments that is total both ways, matches every source attacker of a related pair by a related target attacker (forth) and every target attacker by a related source attacker (back) — and the two claims' complete-support index sets correspond under it. The invariance is an equation between status values, so all four statuses transfer at once and none is read as an argument label. The design's condition, an argumentation-framework isomorphism, is strictly stronger than what the proof uses: the isomorphism's injectivity is consumed by no step, so a surjective bounded morphism already suffices. At a structural bridge the bisimulation is the bridge-induced correspondence between compiled argument positions, its totality clauses are the checker's applicability judgment and its converse (every target argument is a transport), and the support correspondence is derived for every translatable query rather than assumed — its backward half needing the translation to be injective where defined. Under those hypotheses the bridge preserves status, the guarded modal readings collapse to the local status atom, and the hypotheses compose along composite bridges through a chosen intermediate world.
- **Conditions**: Shown for the bridge-global, functional partial translation and total leaf renaming of T6, over a shared canonicalizer, with attack forth/back stated on the compiled edge decider `Compile.edgeB` (index level) rather than derived from a correspondence of declared attacks. Injectivity-where-defined of the symbol translation is required for the derived support correspondence; bridges that supply the correspondence by other means use `status_transport_of_corr` without it. Executable cells cover `justified`, `defeated`, `gap`, and `contested` under one renaming translation between contexts with disjoint signatures, and one `[b]` collapse. Untested boundary: status under non-injective (merging) translations; attack correspondence at the declared-attack level (#238); an executable `StatusBridge` decider (#239); T6 limitations 1, 2, and 5 inherited.
- **Sources**: [`inj consumed by no proof` ← `ara/evidence/proofs/pw_t8_status_preservation.md:19` «field is consumed by no proof, so a surjective bounded morphism already» [result]; `143-job build` ← `ara/evidence/proofs/pw_t8_status_preservation.md:62` «Build completed successfully (143 jobs).» [result]; `60 gated declarations` ← `ara/evidence/proofs/pw_t8_status_preservation.md:66` «AxCheck coverage passed (60 declarations).» [result]; `2058 audited, 60 PW-T8` ← `ara/evidence/proofs/pw_t8_status_preservation.md:72` «The audit reports 2058 declarations across the library, of which 60 are PW-T8» [result]; `Classical.choice via labelC_spec` ← `ara/evidence/proofs/pw_t8_status_preservation.md:76` «`Classical.choice` reaches the T8 rows through `Grounded.labelC_spec`; the» [result]; `hSB and hinj both necessary` ← `ara/evidence/proofs/pw_t8_status_preservation.md:82` «`hinj` from `status_transport`'s signature leaves an unfillable goal» [result]; `contested cell admissible` ← `ara/evidence/proofs/pw_t8_status_preservation.md:54` «strict-reachable rule conclusions. `t8_box_defeated_r` instantiates the `[b]`» [result]]
- **Status**: supported
- **Provenance**: ai-suggested
- **Falsification**: Exhibit two compiled frameworks and a total attack bisimulation with corresponding complete-support sets under which a claim's grounded status differs — i.e. a counterexample to `statusC_of_bisim` — or exhibit an accepted structural-bridge edge satisfying every `StatusBridge` clause and injectivity under which `cmpStatus` differs at the two endpoints. Equivalently, show the T7 identity edge does satisfy `matched`, or that the injectivity hypothesis can be dropped from `status_transport` without a replacement support correspondence.
- **Proof**: [`Lara.PW.AttackBisim`, `labelC_of_bisim`, `statusC_congr`, `statusC_of_bisim`, `AFIso.toBisim`, `statusC_of_iso`, `supportCorr_of_image`; `Lara.PW.StatusBridge`, `StatusBridge.bisim`, `corr_conclusion`, `claimSupport_corr`, `equiv_tr_reflect`, `status_transport`, `status_transport_of_corr`, `srcStatus_transport`, `sat_status_iff_box`, `sat_status_iff_dia`, `sat_status_iff_box_src`, `StatusBridge.comp`, `corr_comp_iff`; witnesses `Lara.Examples.PW.Status.t7_forward_hom_insufficient`, `t7_not_statusBridge`, `t7_not_statusBridge_of_flip`, `t8_justified_preserved`, `t8_defeated_preserved`, `t8_gap_preserved`, `t8_contested_preserved`, `t8_box_defeated_r_holds`; `ara/evidence/proofs/pw_t8_status_preservation.md`; `docs/theory-pw-t8-status-preservation.md`; PR #240, commits 424e4e7..5637540; axiom audit 2058 declarations PASS]
- **Dependencies**: [C47, C48]
- **Tags**: PW-T8, possible-world, status-preservation, bisimulation, structural-bridge, T7-boundary, modal-collapse, composition, mechanized
- **Last revised**: 2026-09-04 (2026-09-04_004#1)
