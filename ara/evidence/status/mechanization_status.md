# Mechanization status ledger (the primary "experiment")

- **Source**: spec.md §9 (the 12 required results); docs/mechanization-plan.md §1 (the status table);
  docs/strict-backend-decision.md §5 (the paper proofs).
- **As of**: 2026-07-26.
- **Legend**: `paper-proved` = proof written in a decision record; `mechanized` = machine-checked in
  Lean/Rocq; `implemented+tested` = Haskell code + passing
  properties; `spec-only` = defined in the spec, no proof or code yet; `open` = not yet provable /
  definitionally incomplete.

## The 12 required results (spec §9) × status

| # | Result | Status | Grounds | Note |
|---|--------|--------|---------|------|
| 1 | Decidability of program + attack checking | **checker portion mechanized** | C02 | `Lara.Check.inferSupport_sound/complete`, `checkAttack_sound/complete`, and `checkProgram_sound/complete` exactly decide the frozen support, positional-attack, and raw-program judgments over the finite executable backend registry. `checkProgram` constructs the proof-bearing `CheckedProgram` boundary, with deterministic duplicate and located rejection behavior. This is Lean mechanization; the production Haskell M3 checker is not implemented here. |
| 2 | Strict-backend isolation | **mechanized** (+Haskell conformance) | C03 | Theorem 3 (non-factivity, the factivity firewall). `lean/Lara/Strict.lean`: `no_truth_projection` — no uniform map from a checked `StrictJudgment B` to premise-free truth `B.models [] (enc goal)` — proved via the reference ND witness `nd_nonfactive_witness` (the backend accepts `p ⊢ p` yet `⊨_ND p` fails under the all-false valuation), so it bites even against a factive backend; `nd_relative_not_absolute` pairs the relative-consequence projection (`strict_step_sound`) against the failure of absolute truth. No `sorry`; AxCheck reports `propext`, `Classical.choice`, and `Quot.sound` for all three results. Also enforced structurally in both Haskell (sealed `StrictJudgment`, opaque `SExpr` cert, no backend formula exported) and Lean (`StrictJudgment` carries only source data). |
| 3 | Dependency accountability (`leaves(w)`, `certDeps`) | **partially mechanized** | C08 | `Lara.Support.leaves_declared` proves the leaf half; `certDeps` awaits `Backend.uses` |
| 4 | Compilation soundness + subargument closure | **mechanized (relational)** | C02 | `Lara.Compile.compile_nodes_checked`, `edge_iff`, and `closure_includes_direct`; closed examples exercise direct and strict-superset closure |
| 5 | Grounded determinism + termination | **mechanized** (core) | C07 | `lean/Lara/Grounded.lean`: grounded extension = bounded characteristic-operator iteration; `grounded_stable` proves the ascending chain reaches the least fixed point within `\|Args\|` steps (deficit measure + strict-filter-length), so the labelling is a total, deterministic function and aggregation (`statusC`) is total. `Lara.Compile.toAF` instantiates the core for proof-bearing checked programs. |
| 6 | **Status preservation (direct vs compiled)** | **source-vs-compiled half mechanized (oracle eliminated)** | C08 | `Lara.Compile.srcIn_iff_grounded`/`srcStatus_iff` compose source status with grounded execution under `Faithful`; the checker-built decider `edgeB` (from `containsB`/`attackClosureB`) discharges `Faithful` constructively via `edgeB_faithful`, so `checkedAF`, `srcIn_iff_checkedGrounded`, `srcStatus_checked`, and `srcStatus_iff_checked` hold over an accepted program with no oracle hypothesis (`SrcIn`/`SrcOut` are the Prop shadow of the same compiled `Edge`, not an independent calculus). Issue #17 closed this half; issue #18 subsequently supplies checked-unit attack completeness for result 7. |
| 7 | Rationality postulates (consistency under §8.1) | **mechanized for checked complete claims** | C09 | `checkUnit` constructs the proof-bearing `CheckedUnit` boundary after duplicate-rule, exact Path-B/R12, and detailed program checks. `coveredB_iff` and `checkUnit_sound` establish attack completeness for all ordered attackable contrary pairs, including self-pairs; `grounded_conflictFree`, exact `claimSupportFor`, and `contrary_claims_not_both_justified` prove computed `completeClaimFor` contrary claims are not jointly justified. This is the Lean reference PL result: no Path A, production Haskell checker, NL validation, or full holes computation is claimed. |
| 8 | Strict-certificate soundness | **mechanized** (+Haskell conformance) | C03 | Theorem 1, `lean/Lara/Strict.lean`: backend-as-structure carrying obligation 3 as a field; `strict_step_sound` is its projection (needs **no** axioms) and `ndBackend` discharges the field via `nd_sound`. Its concrete projection `nd_strict_step_sound` uses the standard trio (`propext`, `Classical.choice`, `Quot.sound`). Excludes trusted-policy instances. |
| 9 | Backend replacement | **mechanized** (Model A: uniform injective relabel) | C04 | Theorem 2, `lean/Lara/Erase.lean`: `backend_replacement` — two `CheckedProgram`s related by a uniform assurance relabel `mapAssur f` (`P₂.args = P₁.args.map (mapAssur f)`, `P₂.atts = P₁.atts.map (mapAssurAtt f)`) with `f` injective compile to a *definitionally equal* AF (`checkedAF_relabel`), hence agree on every grounded label (`labelC_relabel`) and every claim status. The node bijection is the identity on list positions (`toAF.args = List.range`); `containsB_mapAssur`/`mapAssur_injective` carry the payload-independence of the edge relation. Statement-model note: the doc's non-injective erase-to-a-single-`certified`-marker is *not* an isomorphism (it can merge distinct subterms and add subargument-closure edges — `containsB` keys on exact structural equality); injectivity-on-used-certs is the faithful backend-swap condition, and both programs being well-checked discharges "accept the same strict instances." **Now non-vacuous by construction** — `lean/Lara/EraseTransport.lean` proves well-checkedness transport (`hasSupport_mapAssur`, `hasAttack_mapAssur`, `mapCertProg`): a uniform relabel that preserves `AssuranceOk` acceptance (`hpres`, the formal content of "accept the same strict instances") maps a `CheckedProgram` over one backend to a `CheckedProgram` over the other, so `backend_replacement_transport` exhibits the second program rather than assuming it. No `sorry`; AxCheck reports only `propext` and `Quot.sound`. |
| 10 | Reference ND adapter soundness + dependency exactness | **mechanized and executable** (+Haskell conformance) | C05 | Theorem 4 + Lemma 5, `lean/Lara/ND.lean`: `nd_sound`, `nd_relevance`, `fv_in_range`, and the sound/complete `infer` bridge. `lean/Lara/Strict.lean` now closes the concrete boundary: total Formula/Cert decoding, canonical Nat indices, exact `ndReplay`, `ndReplay_iff`, and the fully instantiated `ndBackend`. Its UTF-8 framed A/N/S/C/L atom codec has the proved left inverse `decodeAtomKey_encodeAtomKey`, yielding encoder injectivity and `ndEnc_iff` without `repr`. Theory-resolved backends append fixed selected-theory encodings after premise encodings. No `sorry`; AxCheck reports only the standard trio. The matching Haskell adapter passes normalization, golden-vector, malformed-wire, closed-decoder, replay, soundness, and registry conformance properties. |
| 11 | Support adequacy (`w supports c` = normalized identity) | **mechanized** (+implemented+tested) | C01 | `lean/Lara/Prop.lean`: `nf`/`≡`, equivalence laws, decidability, idempotence, no-reorder — no `sorry`, axioms `propext` only. Also `Lara.Prop` Haskell + 8 QuickCheck properties. |
| 12 | Codec round-trip to α-equivalent AST | spec-only | C12 | test-only (not a soundness result); codec not built |

**Summary**: results 2, 4 (relational), 5, 7 (checked complete claims), 8, 9 (Model A), 10, and 11 are
mechanized; result 6's source-vs-compiled half is mechanized with the `Faithful` oracle eliminated (the
checker-built `edgeB`/`edgeB_faithful` discharges it constructively); result 1 has
an exact executable support/positional-attack/raw-program checker with relational adequacy; result 3
has its mechanized leaf half; result 7 closes Path-B consistency at the Lean `CheckedUnit` boundary;
result 9 is mechanized under the uniform injective certificate-relabel model (Model A), which supersedes
the earlier statement-model blocker; result 12 remains spec-only. Every theorem
is `sorry`-free and audited within the standard axiom trio. Haskell conformance still covers the
implemented lower layers with 30 property groups and is regression evidence only for this Lean-only
result.

### Verification run (2026-07-30, result 9 close)

- `cd lean && lake build` → **`Build completed successfully (47 jobs).`** (`Lara/Erase.lean` new,
  ~290 lines; only pre-existing `unusedSimpArgs` warnings in `Examples.lean`).
- `lake env lean AxCheck.lean` → **509 declaration reports**, `sorryAx` count **0**, and no axiom
  outside `{propext, Classical.choice, Quot.sound}`. The new `Lara.Erase.*` declarations depend
  only on `propext` and `Quot.sound` (two term-level lemmas depend on none).
- Statement model chosen: **A (uniform injective relabel)** over the shared-skeleton (B) and
  `EraseEq`+intra-program-canonicity (C) alternatives — see
  `plans/2026-07-30-result9-backend-replacement.md` and the ara journey record. Purely additive,
  Lean-only: no wire codec, Haskell, or differential-anchor change, so the Haskell↔Lean differential
  is unaffected.

### Verification run (2026-07-30, result 9 transport / non-vacuity)

- `cd lean && lake build` → **`Build completed successfully (48 jobs).`** (`Lara/EraseTransport.lean`
  new, ~230 lines; only pre-existing `unusedSimpArgs` warnings in `Examples.lean`).
- `lake env lean AxCheck.lean` → **516 declaration reports**, `sorryAx` count **0**, no axiom outside
  the trio. The transport decls (`hasSupport_mapAssur`, `hasAttack_mapAssur`, `mapCertProg_args`,
  `mapCertProg_atts`, `backend_replacement_transport`) use only `propext` + `Quot.sound`;
  `mapAssurAtt_target` uses none, `mapAssurDis_eq` only `propext`.
- Strengthening: `mapCertProg` transports well-checkedness under any acceptance-preserving relabel
  (`hpres`), so `backend_replacement_transport` produces the second `CheckedProgram` constructively —
  the earlier statement (both programs assumed well-checked) is now non-vacuous by construction. The
  two transport lemmas need only `hpres`, not injectivity (`hf` is required only for `mapCertProg`'s
  `nodup`). Purely additive, Lean-only (issue #42). The `mapAssurDis_eq`/`mapAssurAtt_target` helpers
  dropped in the PR-#41 review are re-added here as genuinely-used lemmas.

### Verification run (2026-07-26, issue #18 close)

- `cd lean && lake build` → **`Build completed successfully (25 jobs).`**
- `lake env lean AxCheck.lean` → **430 declaration reports**, no `sorryAx`, and the sorted-unique
  axiom set is exactly `Classical.choice`, `propext`, and `Quot.sound`. The CI parser now normalizes
  multiline reports before extraction; a synthetic non-standard axiom fixture demonstrates that the
  old line parser missed the violation and the repaired parser catches it.
- `cabal build` and `cabal test all --test-show-details=direct` → **PASS** (one suite, all 30
  QuickCheck groups, 100 tests each). These Haskell gates establish regression compatibility, not
  implementation of the new Lean acceptance path.
- The closed matrix covers all 70 traceability obligations and six author flows, including exact
  error ordering, alternate-reason and closure coverage, strict-root R12 ownership, computed support
  order, and self-conflict rejection/consistency.

### Verification run (2026-07-25, issue #17 close)

Commands run at the #17 commit and their outcomes:

- `cd lean && lake build` → **`Build completed successfully (19 jobs).`**
- `lake env lean AxCheck.lean` → prints `#print axioms` for every audited theorem (including the new
  `Compile.hasSupport_disNodup`, `lookupDis_some_mem`, `containsB_iff`, `attackClosureB_iff`,
  `edgeB_iff`, `edgeB_faithful`, `srcIn_iff_checkedGrounded`, `srcStatus_checked`,
  `srcStatus_iff_checked`, and the `Examples.checked_edge_fixture*` / `containsB_dupkey*` /
  `attackClosureB_*` fixtures). **No `sorryAx`.** The sorted-unique axiom set across the whole audit
  is exactly `Classical.choice`, `propext`, `Quot.sound` — no non-trio axiom appears.
- `cabal test all --test-show-details=direct` → **`Test suite lara-test: PASS`** (all 30 property
  groups, 100 tests each; this change is Lean-only, so the Haskell conformance suite is unchanged).

## Methodology grounding (C10, C11, C12 — from the deep-research pass, E02)

| Finding | Status | Grounds | Source |
|---------|--------|---------|--------|
| Mechanized metatheory can BE the evaluation | verified (3-0) | C10 | Two Mechanisations of WebAssembly 1.0, FM 2021 |
| POPL AEC excludes non-mechanized proofs from review | verified | C10 | POPL 2025 AEC page |
| AEC certifies reproducibility, not claim-support | verified (3-0) | C10 | SIGPLAN Checklist Manifesto 2019 |
| Untrusted-producer/checker judged by verified-success + adversarial zero-false-positive | verified (3-0) | C11 | DSP, Baldur, LeanDojo, Clover |
| Anti-memorization via novel-premises split | verified (3-0) | C11 | LeanDojo |
| Differential testing = N+1 (fallible oracle), not Csmith voting | verified (3-0 / 2-1 on Csmith framing) | C12 | JEST ICSE 2021; Csmith PLDI 2011 |
| Executable-oracle-from-mechanized-semantics has precedent | verified (3-0) | C12 | Marmsoler–Brucker TAP 2022 |

Deep-research run: 104 agents, 21 sources fetched, 95 claims extracted, 25 verified, 24 confirmed / 1
refuted. The refuted claim (useful): beating LLM baselines is NOT a required acceptance criterion for
the neural component (failed 1-2) — so LARA need not over-invest in baseline-beating for the producer.

## What this ledger drives (design decisions grounded by status)

- Result 11 `implemented+tested` → C01's "trivial TCB addition" is empirically grounded, so `nf`/`≡`
  is frozen and the carve-out can be ported to Lean early.
- Result 6 `source-vs-compiled half mechanized, oracle eliminated` → **N16 discharged semantically,
  #17 closed.** Source `SrcStatus` equals `grounded(checkedAF P)` for an accepted program with no
  `Faithful` hypothesis: the checker-built `edgeB` decides the frozen closure `Edge` exactly
  (`edgeB_faithful`), so the specialized wrappers (`srcIn_iff_checkedGrounded`,
  `srcStatus_iff_checked`) carry it.
- Results 2/8/10 `mechanized` → the strict-backend soundness *and* isolation claims (Theorems 1, 3,
  4) are now artifact-checkable, not just paper proofs (C10). Result 9 `paper-proved` stays on the M2
  critical path until the compiled AF layer exists to state backend replacement against.
- Result 7's validator, attack-completeness checker invariant, and computed-claim status theorem are
  mechanized at `CheckedUnit` (**N60 executed; #18 closed for the Lean reference PL**). Result 9
  waits on certificate-erased argument identity, not proof queue order.
