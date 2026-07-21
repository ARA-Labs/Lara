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
- **Status**: hypothesis
- **Falsification criteria**: A defeat pattern the corpus annotators find that cannot be typed as an
  attack on a root / internal-rule / leaf position (e.g. a genuine attack on something other than
  those three positions), forcing a fourth attack primitive.
- **Proof**: [E05]
- **Evidence basis**: spec §7 defines the positional attack judgment; `Lara.Attack` is spec-only
  pending the M0 defeat-typing decision, so this is a design claim not yet mechanized.
- **Dependencies**: C01
- **Tags**: attacks, positions, ASPIC+, decidability

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
- **Evidence basis**: Theorem 3 (strict-backend-decision §5) proves source non-factivity syntactically
  by inversion; the current Haskell `Kernel` is an LP adapter *seed*, so the interface itself is
  spec-only and this is a paper-proved (not mechanized) result.
- **Dependencies**: C04
- **Tags**: strict-backend, non-factivity, soundness, trust-boundary

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
- **Evidence basis**: Theorem 4 and Lemma 5 (strict-backend-decision §5) give the reference adapter's
  soundness and dependency exactness by structural induction; both are paper-proved, targeted for
  mechanization (result 10), not yet machine-checked, and no conforming adapter is yet implemented.
- **Dependencies**: C03
- **Tags**: natural-deduction, soundness, dependency-accountability, modularity

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
- **Status**: hypothesis
- **Falsification criteria**: A finite compiled framework on which grounded iteration fails to
  stabilize within |Args| steps or admits two distinct grounded labellings — refuting determinism or
  termination (spec §9 result 5).
- **Proof**: [E07]
- **Evidence basis**: spec §8 gives the fixed-point argument; `Lara.Grounded` and the four-state
  aggregation are spec-only, so this is a stated-not-mechanized result (target: result 5).
- **Dependencies**: C06
- **Tags**: grounded-semantics, determinism, termination, four-state-status

## C08: The reported leaf-dependency set equals the term's leaf frontier — accountability is an inversion lemma, not a tracked judgment component
- **Statement**: Making the leaf-dependency set *derived* (`leaves(w)` = the leaf constants occurring
  in the term) rather than a judgment component collapses the former accountability theorem into a
  structural inversion lemma: the reported dependencies are exactly the term's frontier, and
  strict-certificate theory dependencies are reported separately via each backend's `uses` function.
- **Conditions**: Holds for checked support terms; every leaf in `leaves(w)` must be declared in the
  admitted context `Γ`, and backend dependencies (`certDeps`) are unioned in from accepted certificates.
- **Sources**: ["\"The former accountability theorem … is thereby an inversion lemma on term structure: the reported leaf dependency set is exactly `leaves(w)`.\" ← docs/spec.md:424 «the reported leaf dependency set is exactly `leaves(w)`» [input]"]
- **Status**: hypothesis
- **Falsification criteria**: A checked support term whose actual load-bearing leaf set differs from
  `leaves(w)`, or a strict certificate whose consulted theory/premise dependency is not returned by
  its adapter's `uses` — refuting dependency accountability (spec §9 result 3).
- **Proof**: [E08]
- **Evidence basis**: spec §6 defines `leaves(w)`/`certDeps(w)`; `Lara.SupportTerm` is corpus-gated
  and spec-only, so this is a design claim awaiting mechanization (result 3).
- **Dependencies**: C01
- **Tags**: dependency-accountability, leaves, inversion-lemma

## C09: Restricting contrary relations off strict-reachable propositions buys consistency by construction
- **Statement**: A compile-time well-formedness check that forbids any strict-rule consequent — and
  any proposition on a strict chain — from participating in a declared `contrary` pair (Path B) makes
  every conflict rebuttable at a defeasible step, so direct = indirect consistency hold under grounded
  semantics and two contrary claims are never jointly `justified`. The cost is an expressiveness limit:
  strict chains may only target uncontested claims.
- **Conditions**: v0.1 chooses Path B; if the corpus shows strict rules genuinely feeding contested
  claims, the flip is Path A (total involutive contradictory map + transposition closure), which buys
  all four rationality postulates at the cost of structuring the contrary relation.
- **Sources**: ["\"strict closure introduces no new conflict and direct = indirect consistency hold by construction — two contrary claims are never jointly justified\" ← docs/spec.md:546 «introduces no new conflict and direct = indirect consistency hold by construction — two contrary» [input]"]
- **Status**: hypothesis
- **Falsification criteria**: A Path-B-well-formed policy under which two contrary claims are both
  labelled `justified` by grounded semantics — refuting consistency (spec §9 result 7); or corpus
  evidence that Path B's expressiveness limit rejects a large fraction of real strict chains.
- **Proof**: [E05]
- **Evidence basis**: spec §8.1 states the strict-reachable validator and the consistency argument
  (from Caminada–Amgoud Examples 5–6); the validator (`Lara.Policy`) is an early M3 target but
  spec-only now.
- **Dependencies**: C02
- **Tags**: rationality-postulates, consistency, strict-rules, path-B

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
  holds by construction, with no undefined behavior to quotient out.
- **Sources**: ["\"treat the reference semantics as one fallible oracle among N\" ← docs/mechanization-plan.md:129 «fallible oracle among N» [input]", "\"JEST found 44 engine bugs and 27 spec bugs\" ← docs/mechanization-plan.md:130 «JEST found 44 engine bugs and 27 spec bugs» [input]"]
- **Status**: hypothesis
- **Falsification criteria**: A demonstration that the shared-core differential setup cannot localize
  whether a divergence is a Haskell-checker bug or a Lean-model bug (i.e. the N+1 framing gives no
  more than oracle-free voting here) — undercutting the methodological claim.
- **Proof**: [E02]
- **Evidence basis**: Deep-research report (Csmith PLDI 2011 = oracle-free voting; JEST ICSE 2021 =
  N+1; Marmsoler–Brucker executable-oracle-from-Isabelle); folded into `docs/mechanization-plan.md` §3.
  The shared-core serialization is an M1 design requirement, not yet built.
- **Dependencies**: C07, C10
- **Tags**: differential-testing, conformance, mechanization, methodology
