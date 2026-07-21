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
proven (result 12 is a round-trip property, optionally mechanized).

## 1. What gets mechanized

From `spec.md` §9. "Must" = on the critical path for the paper's formal claim; "should" = strengthens
it; "test-only" = conformance evidence, no theorem.

| # | Result | Status | Note |
| --- | --- | --- | --- |
| 1 | Decidability of program + attack checking | **must** | Definitions are decidable functions; the theorem is that they terminate and agree with the relations. |
| 2 | Strict-backend isolation | **must** | Structural: no term/attack/proof crosses the interface. Falls out of the `Backend` structure's typing. |
| 3 | Dependency accountability (`leaves(w)`, `certDeps`) | **must** | Inversion lemma on term structure (`spec.md` §6). |
| 4 | Compilation soundness (no untyped node/attack; subargument closure) | **must** | The combinatorially fiddly one — positional attacks × closure. |
| 5 | Termination + determinism of grounded evaluation | **must** | Monotone operator on a finite-height lattice; bounded iteration ≤ `|Args|`. |
| 6 | **Status preservation: direct source semantics ≡ compiled-AF semantics** | **must** | ⚠️ **requires a direct semantics that does not yet exist** — see §5. Headline compilation theorem. |
| 7 | Rationality postulates (sub-argument closure unconditional; consistency under §8.1) | **must** | Mechanize Path B (the compile-time strict-reachable validator), not Path A. |
| 8 | Strict-certificate soundness (excludes `trusted-policy`) | **must** | A field/obligation of the `Backend` structure; proved once, per adapter. |
| 9 | Backend replacement | **should** | Parametricity over the `Backend` structure + graph isomorphism under `eraseCert`. High reviewer value; the "backend internals are not part of claim-status semantics" result. |
| 10 | Reference natural-deduction adapter soundness + exact dependencies | **must** | The one shipped adapter; induction on the typing derivation (`spec.md` §5.1). |
| 11 | Support adequacy (`w supports c` = normalized identity) | **done** | `nf`/`≡` frozen (`spec.md` §3.2); already property-tested in Haskell. Port the definition + laws to the prover. |
| 12 | Codec round-trip to α-equivalent AST | **test-only** | QuickCheck in Haskell; mechanize only if cheap. Not a soundness result. |

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
- **Haskell = the production checker** (`engineering-plan.md` §3 layers 1–8). Faster to iterate,
  drives the implementation.
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
  high reviewer value, hence "should" not "must," but do it if the schedule allows.
- **Result 4 (compilation soundness + subargument closure).** The fiddly one. Positions `π` are
  paths; an attack on `w@π` compiles to edges onto *every* argument containing that occurrence
  (`spec.md` §8). Mechanize `w@π` as a partial subterm lookup and prove (a) every compiled edge has a
  typed source construct, (b) closure adds edges only onto arguments containing the attacked
  occurrence. Get the `w@π` datatype right before proving anything.
- **Result 7 (consistency, Path B).** Mechanize the **compile-time strict-reachable validator**
  (`spec.md` §8.1): least set closed under strict rules' premises→conclusion; reject policies whose
  `contrary` touches it. Then direct = indirect consistency by construction. Do *not* mechanize Path A
  (transposition + involutive contradictories) unless the corpus forces the flip.

## 5. Blocker for result 6: define the direct semantics first

Result 6 ("status preservation between a direct source semantics and the compiled-AF semantics") is
currently **unprovable as stated** because `spec.md` §8 defines only the compiled route. There is no
independent direct semantics, so the theorem has nothing to preserve.

**Action before M1 freeze:** define a direct big-step claim-status judgment

```
Σ; Π; Γ; R ; W ⊢ p ⇓ justified | defeated | contested | gap
```

directly on the well-formed program `W` (the judgment `popl-research-review.md` §3.3 already lists),
*without* going through the Dung translation, then state result 6 as: for every well-formed `W` and
claim `p`, the direct judgment and `grounded(compile(W))` assign the same status. Mechanize both.

Alternative if a direct semantics proves awkward: reframe the compilation as *the* definition and
drop result 6, keeping only results 4/5/7 as the compilation's correctness. This weakens the
"semantics-preserving compilation" headline, so the direct-semantics route is preferred.

Two other definitional holes must close before freeze (they make the status function total, needed
for result 5): the **hole-vs-complete-alternative** case (`spec.md` §8, marked open) and the report
obligation for **`contested` SCC provenance** (`popl-research-review.md` §6).

## 6. Sequencing and artifact hygiene

- **Gate.** Mechanization starts at **M1 freeze**, runs parallel to the Haskell compiler (M3)
  (`engineering-plan.md` §6, `research-proposal.md` §8 #8 decides Lean/Rocq before M1). The two
  carve-outs (`nf`/`≡`, the ND adapter) can be *ported* to the prover early since they are already
  frozen — a low-risk warm-up that also seeds result 10/11.
- **Anonymizable from day one** (`popl-research-review.md` Phase C). No author-identifying paths,
  comments, or repo metadata in the proof development.
- **No `sorry`/`admit` in main theorems** at M2 exit; a single replay command must check the whole
  development. Record every prover axiom and every backend assumption explicitly (the POPL call asks
  for non-standard axioms; the `sorry`-audit lesson from `prior-art-lessons.md` applies to proof
  holes too).
- **Differential + property + golden + mutation tests remain conformance evidence** across the
  Haskell↔Lean boundary (`engineering-plan.md` §5); they do not replace the mechanized theorems.

## 7. Open decisions

1. **Lean 4 vs Rocq** — default Lean 4; decide before M1 by collaborator expertise
   (`research-proposal.md` §8 #8).
2. **Direct semantics for result 6** — define it (preferred) or reframe the compilation as
   definitional (§5).
3. **Result 9 in scope for the paper?** — high value, "should"; include if the M2 schedule holds.
4. **Executable-Lean vs separate reference interpreter** — prefer executable Lean definitions so one
   development both proves and runs the differential anchor (§3); fall back to a separate reference
   interpreter only if key definitions resist decidability.
