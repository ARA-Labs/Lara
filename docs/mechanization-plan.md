# LARA mechanization plan

_How the metatheory gets machine-checked, and how the mechanized model stays tied to the Haskell
checker. Expands `engineering-plan.md` §4 (the parallel mechanization track) and `research-proposal.md`
§4 with a concrete architecture. The theorem list is `spec.md` §9 (results 1–12); the review's
restatement is `../plans/popl-research-review.md` §4._

## 0. Why mechanize at all (POPL calibration)

The POPL 2027+ call strongly encourages submission-time proof scripts when mechanized proofs are a
main contribution (`popl-research-review.md` §1, §4). For LARA, one of the five headline
contributions is a *semantics-preserving compilation* into structured argumentation
(`popl-research-review.md` §9 item 2). A paper proof of that is acceptable; a machine-checked one is
the difference between "principled language result" and "trust the appendix." Property tests are
**conformance evidence, not soundness** (`spec.md` §9 closing note) — the mechanized theorems carry
soundness. Plan the project around a mechanized language result, not a checker demo.

**External corroboration (deep-research, 2026-07-21, adversarially verified).** Three findings raise
mechanization from "encouraged" to "load-bearing" for this paper:

- Mechanized metatheory *can be the entire evaluation* for a language-semantics paper — e.g. *Two
  Mechanisations of WebAssembly 1.0* (Watt et al., FM 2021) ships two independent mechanised
  semantics + a type-soundness result as its substance, with no performance numbers or user studies.
  This is exactly LARA's Axis (a) shape.
- **POPL artifact evaluation explicitly excludes non-mechanized (paper) proofs from review** — the
  committee "lacks time and expertise to check them" (POPL 2025 AEC). So an un-mechanized soundness
  argument gets *no* artifact credit; only the mechanized development is checkable. This is the
  decisive reason to keep M2 on the critical path.
- Artifact evaluation certifies **reproducibility, not claim-support** (SIGPLAN "Checklist
  Manifesto," 2019): a weak evaluation cannot be rescued by a badge. The mechanized theorems must
  themselves convince reviewers — the badge is not a substitute.

Scope discipline: mechanize the **frozen first-order core and the headline theorems only.** The LLM
elaborator has no theorem (it is the untrusted producer); the JSON/presentation codec is tested, not
proven (result 12 is a round-trip property, optionally mechanized; the structured codec now *is*
mechanized, while the concrete `.lara` parser stays test-only).

## 1. What gets mechanized

From `spec.md` §9. "Must" = on the critical path for the paper's formal claim; "should" = strengthens
it; "test-only" = conformance evidence, no theorem.

| # | Result | Status | Note |
| --- | --- | --- | --- |
| 1 | Decidability of program + attack checking | **mechanized (checker portion)** | Legacy `inferSupport`, `checkAttack`, and `checkProgram` remain generic and unchanged; `checkUnit` adds the detailed accepted-unit path. |
| 2 | Strict-backend isolation | **mechanized** | Structural isolation plus the concrete non-factivity witness (`no_truth_projection`, `nd_nonfactive_witness`, `nd_relative_not_absolute`). |
| 3 | Dependency accountability (`leaves(w)`, `certDeps`) | **mechanized** | `leaves_declared` proves the source-leaf half; `Backend.uses` under obligation 4's coverage/validity/accounting laws and the support-level `certDeps` layer (typed premise/theory `CertDep` report, `cert_steps_accounted`, collection in both directions, `certDeps_resolved`, `certDeps_theory_valid`) close the certificate half (#46). |
| 4 | Compilation soundness (no untyped node/attack; subargument closure) | **mechanized (relational)** | `compile_nodes_checked`, `edge_iff`, and `closure_includes_direct`; closed examples exercise direct and strict-superset closure. |
| 5 | Termination + determinism of grounded evaluation | **mechanized** | Bounded characteristic-operator iteration reaches the least fixed point within `\|Args\|`. |
| 6 | **Status preservation: direct source semantics ≡ compiled-AF semantics** | **source-vs-compiled half done (#17 closed)** | Direct semantics and the source-vs-compiled bridge are proved; the checker-built `edgeB`/`edgeB_faithful` discharges `Faithful` constructively. Issue #18 separately closes the attack-completeness premise used by result 7. |
| 7 | Rationality postulates (sub-argument closure unconditional; consistency under §8.1) | **mechanized for the Lean reference PL (#18 implementation; C09)** | `checkUnit` enforces Path B and exact conflict coverage; `Lara.Consistency` proves the computed-`completeClaimFor` headline, including self-conflict. |
| 8 | Strict-certificate soundness (excludes `trusted-policy`) | **mechanized** | `strict_step_sound` is the backend obligation projection; `ndBackend` discharges it via `nd_sound`. |
| 9 | Backend replacement | **mechanized (Model A)** | `Erase.backend_replacement` proves status invariance under a uniform injective assurance relabel; `EraseTransport.backend_replacement_transport` constructs the relabeled well-checked program under acceptance preservation. |
| 10 | Reference natural-deduction adapter soundness + exact dependencies | **mechanized and executable** | `nd_sound`, `nd_relevance`, `fv_in_range`, the sound/complete `infer` bridge, and the concrete `ndBackend` replay boundary. |
| 11 | Support adequacy (`w supports c` = normalized identity) | **mechanized** | `nf`/`≡` frozen (`spec.md` §3.2); property-tested in Haskell AND machine-checked in Lean 4 (`../lean/Lara/Prop.lean`: equivalence laws, decidability, idempotence, no-reorder; no `sorry`, axioms `propext` only). The completed warm-up. |
| 12 | Codec round-trip to α-equivalent AST | **mechanized structured presentation codec** (+ current Haskell conformance) | Lean mechanizes `parse ∘ print = id` for the complete live structured `Program`/`Policy` AST at `lara-syntax@0.7`, including value bindings, inferred argument instantiations, `policySigma`, and optional measurand polarity (`../lean/Lara/Presentation.lean`). The theorem was proved against the `@0.6` AST and holds verbatim at `@0.7`: that release restricts the concrete `.lara` surface only (grammar Appendix F) and changes no `Lara.AST` type, so the modeled shape is the same one and no re-proof was owed. Haskell QuickCheck separately covers the concrete `.lara` parser/printer. The Lean theorem is an AST-shape anchor, **not** a correctness proof for the Haskell concrete parser. `../scripts/check-presentation-parity.sh` compares normalized shape inventories between the two models. Exact compiler witnesses pin record fields, sum payloads, aliases, and anonymous entry types; the tripwires compare named record selectors in order. Positional constructors have no source selector names: exact signatures pin their arity and positional type sequence, but semantic labels and swaps among same-typed positions remain assertions. Two representation exemptions are documented (`SortName` erasure; `Cert`'s native payload); the `Cert` exemption is unchanged at `lara-syntax@0.7` — the named-slot lowering is mechanized separately from the codec (`../lean/Lara/CertSlots.lean`: `lower_id_of_no_symbolic`, `lower_eq_numeric_subst`). |
| 13 | Well-sortedness is decidable and preserved by rule instantiation (`lara-core@0.2`, issue #89) | **mechanized** | `../lean/Lara/Sigma.lean`. (a) `wellSorted_decidable` — the executable check *is* the relation, so decidability is definitional and needs no classical input. (b) `wellSorted_subst` (+ `_list`, `_mem`, `_rule`) — the substitution lemma: a rule whose premises, conclusion, and answers are well-sorted under Σ extended with its derived parameter sorts, instantiated by a sort-respecting θ, yields well-sorted atoms; the same lemma applies to checked exception patterns. (c) `thetaWellSorted_ruleSortRespecting` combines stage 2's θ-range check with accepted support's R3 exact-domain invariant. (d) `checkUnit_wellSorted` (`../lean/Lara/Check/Unit.lean`) closes over every actual rule instance recursively reachable through an accepted support term, plus the environment's ground atoms (Γ, the theory table, and queries). |

Optional LP-adapter conservativity/realization (`spec.md` §5.2) is adapter-specific and mechanized
only if the LP adapter ships (gated by corpus open question §8 #1).

## 2. Prover choice

**Default: Lean 4** (`research-proposal.md` §8 #8 leaves Lean-vs-Rocq open until M1; Lean 4 is the
default, Rocq if a collaborator's expertise dominates). Rationale:

- Mathlib has the order-theory / fixpoint infrastructure for result 5 (complete lattices, monotone
  maps, `OrderHom`) and finite-set machinery for the AF.
- Lean's `Decidable` typeclass makes results 1 and 11 executable *and* proved-decidable in one
  artifact — which is what the differential-testing anchor (§3) needs.
- Community familiarity for POPL reviewers is high.

Decide before M1 freeze (`spec.md` §9 note: core 1–9 + reference-adapter 10 must be mechanized). Do
**not** start proving until M1 freezes the definitions — a theorem about the model does not transfer
to the Haskell checker without the conformance argument, and re-proving after a definition churn is
the main way a mechanization track blows its schedule (`research-proposal.md` risk table).

## 3. Architecture: one shared core, two implementations, a differential anchor

This is the load-bearing decision. The Haskell checker and the Lean model are **separate
developments sharing one serialized first-order core AST** (`research-proposal.md` §4). That shared
serialization is the differential-testing anchor.

```
                    hand-written / elaborator-emitted
                         core programs + expected verdicts
                                     │
                    ┌────────────────┴────────────────┐
                    │  serialized first-order core     │   ← the shared vocabulary
                    │  (S-expressions on disk)         │      (see IR decision in chat/history)
                    └────────────────┬────────────────┘
                     decode                     decode
                    ┌───┴───┐                 ┌───┴───┐
                    │Haskell│                 │ Lean  │
                    │checker│                 │ model │
                    └───┬───┘                 └───┬───┘
                    verdict                   verdict
                        └──────── compare ────────┘
                              (differential test)
```

- **Lean model = definitions + theorems.** Syntax (`Prop`, `Term`, support terms `w`, attacks),
  checking judgments as inductive relations *and* as decidable functions proved to agree, the
  `Backend` structure, the ND adapter as an instance, `compile`, and grounded labelling as a bounded
  lfp. Plus the results in §1.
- **Haskell = the production-checker target** (`engineering-plan.md` §3 layers 1–8). The current
  Haskell commands provide regression compatibility; issue #18 adds no production Haskell checker
  or new Haskell acceptance flow.
- **Shared = the serialized core.** The same S-expression programs and their expected four-state
  verdicts run through both. Because the Lean definitions are executable (result 1/5/11 are decidable),
  the Lean side *runs*, not just *proves* — so the differential test is model-vs-implementation, not
  proof-vs-nothing.

Design implication that must land early: **`Lara.SupportTerm`'s AST must serialize losslessly into
the Lean inductive from day one** (`engineering-plan.md` §4). Fix the S-expression grammar for the
core AST as part of M1, not later. This is why the "Haskell-AST now, S-expr codec later" IR decision
matters: the S-expr codec *is* the differential anchor, so it is not merely a convenience layer.

### Framing the differential test correctly (deep-research correction)

The deep-research pass flagged a methodological precision point worth stating so the paper cites the
right precedent:

- **Csmith (PLDI 2011) is oracle-free cross-implementation *voting*** — N independent implementations
  of one spec, any disagreement flags a bug, no reference is trusted. Its transferable lesson for
  LARA is the *single-interpretation* requirement: generated core programs must have one well-defined
  verdict (LARA's grounded status is deterministic by result 5, so this holds by construction — no
  undefined behavior to quotient out). Cite Csmith for that discipline, **not** for testing against a
  reference.
- **The correct precedent for "test the implementation against the mechanized reference" is JEST-style
  N+1-version differential testing** (Park et al., ICSE 2021): treat the reference semantics as *one
  fallible oracle among N*, cross-execute, and statistically localize whether the **spec** or an
  **implementation** is wrong. JEST found 44 engine bugs *and* 27 spec bugs — the point being that the
  mechanized reference can itself be buggy, and the differential harness surfaces that. Frame the
  Haskell↔Lean cross-check this way: divergence indicts *either* side, and finding a Lean-model bug is
  a legitimate result, not an embarrassment.
- **Executable-oracle-from-mechanized-semantics is a proven pattern**: Marmsoler & Brucker (TAP 2022)
  code-generate a Haskell oracle from an Isabelle Solidity semantics (found 30+ deviations, then
  10k+ passing tests); an SQL-in-Prolog reference RDBMS does the same for databases. This is precisely
  the executable-Lean route in §3/§7 decision 4 — it has precedent, so prefer it.
- **Coverage over the reference semantics** (feature-sensitive coverage, OOPSLA 2023 / TOSEM 2026):
  graph-coverage criteria apply to inductive semantic definitions, giving a *coverage argument* that
  the worked examples exercise every rule/status. Use this to defend "the six examples span every
  status" rather than asserting it (see `worked-examples-plan.md` §1).

## 4. How the hard results are mechanized

- **Result 5 (grounded lfp, determinism, termination).** Do *not* reach for domain-theoretic
  fixpoints. `Args` is finite, so define Dung's characteristic function `D_AF` on `Finset Args`,
  prove monotone, and compute the least fixpoint by **bounded iteration from ∅ with fuel `|Args|`**
  (the chain strictly grows until it stabilizes, `spec.md` §8). Determinism and termination are then
  immediate, and the function is executable for the differential anchor. Mathlib `OrderHom` +
  `Finset` carry the monotonicity lemma.
- **Result 8 + 10 (strict soundness, modularly).** Make the backend a **structure carrying its own
  soundness obligation as a field**:

  ```
  structure Backend where
    Form    : Type
    encode  : Prop → Form
    Theory  : Type
    check   : Theory → List Form → Form → Cert → Bool
    models  : Theory → List Form → Form → Prop
    sound   : ∀ T Δ φ κ, check T Δ φ κ = true → models T Δ φ   -- obligation
    reflects_nf : ∀ p q, encode p = encode q ↔ p ≡ q             -- normalization
    -- + weakening / cut / dependency-accountability obligations
  ```

  Result 8 is then one line per accepted instance (apply `sound`). The **ND adapter is an
  `instance : Backend`** whose `sound` is discharged by induction on the ND typing derivation
  (`spec.md` §5.1). Any future adapter must discharge the same fields — the structure *is* the
  conformance contract.
- **Result 9 (backend replacement).** Parametricity over `Backend`: two backends with equal
  acceptance profiles produce, after `eraseCert`, isomorphic AFs; the grounded lfp is invariant under
  that isomorphism. Structural induction on support checking + graph iso + lfp-invariance
  (`spec.md` §5.3). This is the proof that backend internals are outside claim-status semantics —
  high reviewer value. **Current representation blocker (2026-07-24):**
  `Compile.CheckedProgram` stores certificate-bearing `SupportTerm` nodes but no stable argument id
  or certificate-erased skeleton. Add that compile-boundary identity/bijection before stating the
  payload-varying graph isomorphism; queue order is not the blocker.
- **Result 4 (compilation soundness + subargument closure).** The fiddly one. Positions `π` are
  paths; an attack on `w@π` compiles to edges onto *every* argument containing that occurrence
  (`spec.md` §8). Mechanize `w@π` as a partial subterm lookup and prove (a) every compiled edge has a
  typed source construct, (b) closure adds edges only onto arguments containing the attacked
  occurrence. Get the `w@π` datatype right before proving anything.
- **Result 7 (consistency, Path B).** Mechanize the **compile-time strict-reachable validator**
  (`spec.md` §8.1): least set closed under strict rules' premises→conclusion; reject policies whose
  `contrary` sides may overlap it at the ground-instance level. Then direct = indirect consistency
  by construction. Do *not* mechanize Path A (transposition + involutive contradictories) unless the
  corpus forces the flip. **Issue #18 closes this scope for the Lean reference PL:**
  `Lara.Policy.strictReachable_iff_mem`, `aPatMayOverlap_of_instances`, and `wfB_iff`, plus the
  instantiated-contrary boundary theorems and located R12 payload feed the public
  `Lara.Check.Unit.checkUnit` boundary. `Unit.CheckedUnit` carries rule-ID uniqueness, Path-B
  well-formedness, exact attack completeness, and the retained checker nodes.
  `Lara.Consistency.contrary_claims_not_both_justified` combines those with generic grounded
  conflict-freedom and exact complete-support aggregation. Its claims are computed by
  `completeClaimFor`; arbitrary caller-supplied claims are outside the theorem. Ordered self-pairs
  cover self-conflict.

- **Result 1 (checking decidability).** `Lara.Check.inferSupport` and
  `checkAttack` exactly decide the frozen §6.1/§7.1 judgments, and
  `checkProgram` constructs a `CheckedProgram` from raw argument/attack
  declarations. That legacy `checkProgram`/`CheckedProgram` behavior remains
  the generic attack-soundness boundary. `checkProgramDetailed` additionally
  carries retained nodes and attack completeness, and the public `checkUnit`
  canonicalizes whole-unit acceptance. Its fixed order is:

  ```text
  duplicate rule IDs → R2 signature → R12 policy violation
                     → duplicate arguments → support
                     → typed attacks → missing conflict
  ```

  The support stage builds the exact retained checked-node cache; the typed-attack
  and missing-conflict stages reuse it, as does downstream claim aggregation, so
  no support re-inference occurs. Manual proof-level construction of `CheckedUnit`
  remains possible only by supplying all invariants. This paragraph states the
  scope of the Lean proof; the existing production Haskell checker is separate
  conformance evidence, not part of that proof.

## 5. Result 6: source-vs-compiled half complete — oracle eliminated (#17 closed) ◐

Result 6 ("status preservation between a direct source semantics and the compiled-AF semantics") was
**unprovable as originally stated** because `spec.md` §8 defined only the compiled route — no
independent direct semantics, so the theorem had nothing to preserve (exploration tree N16). The
**abstract core is mechanized** (2026-07-21, issue #4), and the M1 lock pass now composes it with
the frozen source compile relation.

**Done — abstract AF layer.** `spec.md` §8.2 defines a direct big-step claim-status judgment

```
W ⊢ a ⇓ in | out | undec        (aggregated to justified | defeated | contested | gap)
```

as the least fixed point of the defense operator (mutually-inductive `DirectIn`/`DirectOut`), and
`lean/Lara/Grounded.lean` proves it equal to the executable bounded-iteration labelling over an
**arbitrary** framework — `directIn_iff` (argument level), `labelC_inn/out/undec_iff` (label
partition), `status_preservation` (claim status) — plus the grounded-termination/determinism core
(`grounded_stable`, result 5). `sorry`-free, standard axiom trio. This discharges N16's "no
independent semantics exists" objection: there is now a declarative grounded semantics distinct from
the iteration, proved to agree with it.

**Done — source composition, oracle eliminated.** `Lara.Compile.SrcIn`/`SrcOut` and
`SrcStatus` read the Prop-level frozen closure relation directly — the shadow of the *same*
compiled `Edge`, not an independent calculus; `srcIn_iff_grounded`/`srcStatus_iff` prove equality
with executable grounded status over `toAF` given `Compile.Faithful`. That `Faithful` obligation is
no longer parametric: the checker-built closure decider `edgeB` (from `containsB` and
`attackClosureB`) decides the frozen closure `Edge` exactly (`containsB_iff`, `attackClosureB_iff`,
`edgeB_iff`, `edgeB_faithful`, with the `DisNodup` side condition from `hasSupport_disNodup`), so
the specialized wrappers `checkedAF`, `srcIn_iff_checkedGrounded`, `srcStatus_checked`, and
`srcStatus_iff_checked` state source-vs-compiled agreement over an accepted program with **no oracle
hypothesis**. `Lara.Examples` pins the decider (`checked_edge_fixture_faithful`,
`checked_closure_status`) on concrete fixtures. Executable replay and proof-bearing raw-source
`checkProgram` are in place. This closes issue #17. Issue #18 separately closes the
accepted-unit attack-completeness premise and result 7/C09 for the Lean reference PL.

The two definitional holes that made the status function partial (N17) are addressed in `spec.md` §8:
the **hole-vs-complete-alternative** case (a complete `in` alternative dominates; `statusC_gap_iff`
mechanizes "gap only on empty complete support"; the `incompleteAlternative` diagnostic is a defined
convention) and **`contested` = grounded `undec`** (SCC provenance a separate defined report). The
four-state status is total and deterministic by construction.

For result 7, `completeClaimFor` is only a complete-support projection with empty
holes. No implementation of full `holes(P,p)` or `incompleteAlternative` is
claimed. Nor does issue #18 claim Path A, NL-to-structure validation, the
production Haskell checker, or an optimized grounded evaluator:
`Lara.Grounded` remains the proof-oriented reference implementation.

**Issue-#18 verification.** All 70 traceability IDs and six author flows pass;
`lake build` completes 25 jobs; AxCheck emits 430 reports with no `sorryAx` and
only `propext`, `Classical.choice`, and `Quot.sound`; and the multiline CI axiom
parser is repaired and negative-tested. `cabal build` and `cabal test` pass (one
suite, 30 QuickCheck groups, 100 cases each), but these are
regression-compatibility evidence only, not new Lean acceptance-flow evidence.

## 6. Sequencing and artifact hygiene

- **Gate.** Mechanization starts at **M1 freeze**, runs parallel to the Haskell compiler (M3)
  (`engineering-plan.md` §6, `research-proposal.md` §8 #8 decides Lean/Rocq before M1). The two
  carve-outs (`nf`/`≡`, the ND adapter) can be *ported* to the prover early since they are already
  frozen — a low-risk warm-up that also seeds result 10/11. **Done for `nf`/`≡` (result 11):** the
  Lean 4 development lives in `../lean/` (Lake project, toolchain pinned to v4.32.0);
  `lean/Lara/Prop.lean` machine-checks the equivalence laws, decidability, idempotence, and
  no-argument-reordering with no `sorry` and `propext` as the only axiom. **Lean 4 is the settled
  prover choice** (open question §8 #8 resolved). The ND adapter (result 10),
  executable support/attack/program checkers (result 1), and the source-vs-compiled
  bridge (result 6, `Faithful` now discharged by the checker-built `edgeB`) are now mechanized.
- **Anonymizable from day one** (`popl-research-review.md` Phase C). No author-identifying paths,
  comments, or repo metadata in the proof development.
- **No `sorry`/`admit` in main theorems** at M2 exit; a single replay command must check the whole
  development. Record every prover axiom and every backend assumption explicitly (the POPL call asks
  for non-standard axioms; the `sorry`-audit lesson from `prior-art-lessons.md` applies to proof
  holes too).
- **Differential + property + golden + mutation tests remain conformance evidence** across the
  Haskell↔Lean boundary (`engineering-plan.md` §5); they do not replace the mechanized theorems.

## 7. Resolved decisions and remaining work

1. **Result 9** — done under Model A (uniform injective assurance relabel);
   `EraseTransport` adds constructive well-checkedness transport.
2. **General executable edge decider (#17)** — done:
   `Compile.edgeB`/`edgeB_faithful` construct `Compile.Faithful`.
3. **Attack completeness (#18)** — done for the Lean reference PL:
   `checkUnit` constructs the exact accepted-unit invariant used by result 7.
4. **Dependency accountability (result 3)** — done (#46): `Backend.uses`
   carries obligation 4 as three laws over the explicit full consulted
   context `Δ ++ T`, for one fixed backend core per registered identity
   with digests resolving only to theory data — coverage (`uses_covers`:
   replay consults no premise or theory entry outside the report; its
   specialization `certOkBOf_theory_covers` makes a digest swap observable
   only through reported theory slots), validity (`uses_valid`:
   reported slots stay within the consulted context), and semantic
   accounting (`uses_account`: the conclusion follows from just the
   reported entries);
   the ND adapter discharges them via `infer_agree`/`fv_in_range`/
   `nd_relevance`, with `ndUses_eq_infer_deps` tying the report to the
   running checker's output. `Lara.Support` lifts it to `certDeps` over the
   typed premise/theory `CertDep` report — `cert_steps_accounted`,
   `mem_certDeps_step`/`certStep_deps_subset`, `certDeps_resolved`,
   `certDeps_theory_valid`; `Lara.Examples.certDeps_theory_entry_reported`
   pins the accepted theory-consuming fixture's report.
