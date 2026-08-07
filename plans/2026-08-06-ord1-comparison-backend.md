# `ord@1`: the ordered-comparison strict backend

**Goal:** Give Lara native, kernel-minimal support for the most common claim shape in ML
methodology papers — "this number beats that number" — as a second rational-arithmetic
strict backend, `ord@1`, certifying a closed family of comparison goals over measured
cells. Design fixed here; implementation, Lean metatheory, and conformance land together
per the mechanization discipline.

**Positioning constraint (2026-08-06):** Lara is a calculus and a language — the
Lean/Isabelle of research — not a workflow tool. This backend adds *judgments with
metatheory*. Everything about how numbers reach a `.lara` file (evidence hashing,
extraction, re-execution, ledgers) is tool-layer and permanently out of scope; the
language's contact with evidence remains the typed leaf (`kind × provenance`) plus the
admission policy.

**Compatibility boundary:** `Prop`/`nf`/`≡` untouched (frozen carve-out, spec result 11).
The frozen corpus-v1 untouched. Framework metatheory untouched (see §5). `ra@1`
untouched except for factoring shared helpers (§3.5).

---

## 1. What already exists

| Component | Role |
|---|---|
| `Lara.Strict` (`Backend`, closed `Registry`, sealed `StrictJudgment`) | The extension seam. `ord@1` registers beside `nd@1`/`ra@1` in `Lara.Driver.Internal.mkRegistry`. |
| `Lara.Strict.RA` | The precedent. `parseDecimal`, `premiseCell` (the premise-cell convention), canonical-numeral wire discipline, empty-theory digest (S1 precedent) are reused, not reinvented. |
| `docs/strict-backend-decision.md` obligations 1–6 | The per-backend proof obligations `ord@1` must discharge. |
| `lean/Lara/{Strict,RA,Erase,EraseTransport}.lean` | Parametric framework metatheory + the adapter-proof template. |
| Corpus policy R12 comment (`corpus-v1.policy.lara`) | The well-formedness pattern: strict conclusions head no contrary. |

## 2. The judgment

### 2.1 Goal family

A closed two-predicate family, each over exactly two canonical decimal numerals:

```text
num_lt(A, B)    -- A < B
num_le(A, B)    -- A <= B
```

Internally one closed sum (`Tag` discipline: spellings live in exactly one
`toString`/`parse` table):

```haskell
data OrdRel = OLt | OLe
```

**Decision: no `num_gt`/`num_ge`.** "A > B" is authored as `num_lt(B, A)`. The kernel
stays minimal; a frontend that wants `>` spells it and swaps arguments at elaboration.
Recorded alternative: a five-spelling family decoding to an oriented internal relation —
rejected because it doubles the Lean surface for zero semantic gain.

**Decision: no `num_eq` (eng review 2026-08-06).** Canonical decimal form is injective
on representable rationals (`canonNum`; `parseDecimal` accepts only the canonical
image), so `num_eq(A, B)` could only ever accept when `A` and `B` are the *same*
numeral — the goal degenerates to `num_eq(A, A)`, a shape no paper claim takes. The
one genuine use, exact agreement between two reports of one measurand, is `DupGroup ≡`
territory (§6, first non-goal). The same minimality argument that killed
`num_gt`/`num_ge` applies; the family is `{lt, le}`. Reopening (a premise-backed
exactness judgment outside `DupGroup`) is an additive version decision.

**Proposition identity (eng review 2026-08-06, D15).** A comparison goal is a ground
arithmetic proposition: `num_lt(0.71, 0.74)` claimed for two different measurands is
one and the same `Prop`, so claim status, support merging, and quarantine behave
per-proposition, not per-comparison. This aliasing is by design — the truth of the
bare comparison does not depend on which measurand produced the numbers. Measurand
identity lives in the premises and in the bridge rule's conclusion (§3.6), which
carries the distinguishing arguments.

### 2.2 Certificate

```text
cert ::= (ordcmp (prem N) (prem M))
```

`N`, `M` name **premise slots only** (0-based, submission order). The relation is
read off the goal predicate, not the certificate. There is **no witness value**:
unlike `ra@1`'s recomputed fraction, a comparison over ground literals has nothing to
recompute — the replay decides it directly. `uses` is a function of the certificate
alone (obligation 4): deps = the two slots, always `PremiseSlot`.

**Decision: premise-only slots (eng review 2026-08-06, D12).** Unlike `ra@1`'s
free-context indexing (premises then theory entries), `ord@1` rejects any slot
`≥ nPrem`. Rationale: on the raw `.sexp` door the backend theory table is built from
the unit's own wire `theories` section (`buildCertOk` in
`src/Lara/Driver/Internal.hs`) and replay preflight never validates content —
so a theory-entry slot would let an artifact cite a self-supplied, unattackable,
non-leaf value, resurrecting the rejected `(lit)` alternative (§2.4) through a side
door. The guard makes §2.4 true by construction rather than by assumption. The
seam-wide question for `ra@1` is a recorded TODO, not this plan's scope.

> **Correction (implementation, PR #83 review).** This paragraph originally
> read "The guard costs nothing (the theory is empty by design)". That is
> wrong, and it inverts the argument the rest of the paragraph makes: on the
> raw door the theory is *not* empty by design and is not under the checker's
> control — `buildCertOk` hands the adapter whatever the artifact supplied,
> which is the very reason the guard is load-bearing rather than free. A
> well-formed unit's `ord@1` theory is empty **by convention**, pinned at the
> `.lara` door by the elaborator's `registryOf`. The guard does not enforce
> emptiness — a unit may declare entries and still be accepted — it makes
> theory entries **uncitable**. The implementation says this correctly in
> `Lara.Strict.Ord`, `Lara.Strict.Cell`, and `examples/S2/ord-v1.policy.lara`;
> §2.2 is corrected here because the module header cites it. The Lean side
> reaches the same acceptance set from the other direction: `buildRegistry`
> resolves any *known* `ord@1` digest to `[]`.

### 2.3 Replay

Given `(digest, premises, goal, cert)`:

1. digest must be registered (empty theory, selection-identity digest, S1 precedent);
2. decode cert (closed decoder: unknown tags, non-canonical naturals rejected);
3. parse goal: one of the two predicate spellings over exactly two `TNum` literals,
   each a canonical decimal (`parseDecimal`, the `canonNum` image — anything else
   rejects);
4. resolve both slots against the premise list only (`slot ≥ nPrem` rejects, §2.2);
   extract each cell by the **premise-cell convention** (exactly one numeric literal
   anywhere in the normalized premise's terms; zero or several is a refusal to guess);
5. left cell `==` goal's `A`, right cell `==` goal's `B` (exact `Rational`);
6. the relation holds in exact rational arithmetic;
7. accept with deps `{slot N, slot M}` (a same-slot cert dedups to one dependency).

Any failure is a rejection (R13 at the replay boundary), never a decode-and-guess.

The rejection funnel, marking which stages are shared `Lara.Strict.Cell` code after
the §3.5 factoring (this diagram also lives as the `Cell.hs` module comment):

```text
        (digest, premises, goal, cert)
                    │
   ┌────────────────▼─────────────────┐
   │ 1 digest registered?             │──no──▶ reject: unknown digest
   ├──────────────────────────────────┤
   │ 2 decode (ordcmp (prem N)(prem M)│──no──▶ reject: malformed cert     ┐ shared:
   │   [Cell: decodeSlot, canonical   │                                   │ decodeSlot,
   │    naturals]                     │                                   │ parseCanonicalNat
   ├──────────────────────────────────┤                                   │
   │ 3 goal = num_lt/num_le over two  │──no──▶ reject: bad goal           │ shared:
   │   canonical decimals             │                                   │ parseDecimal
   │   [Cell: parseDecimal]           │                                   │
   ├──────────────────────────────────┤                                   │
   │ 4 slots < nPrem? premiseCell on  │──no──▶ reject: slot out of range, │ shared:
   │   each (exactly one literal)     │        slot names a theory entry, │ premiseCell
   │   [Cell: premiseCell]            │        or 0-or-2+ literals        ┘
   ├──────────────────────────────────┤
   │ 5 cells == goal numerals?        │──no──▶ reject: wrong cell (L or R)  ord-only
   ├──────────────────────────────────┤
   │ 6 relation holds (exact ℚ)?      │──no──▶ reject: relation fails       ord-only
   └────────────────┬─────────────────┘
                    ▼
      accept, deps = {PremiseSlot N, PremiseSlot M}
```

### 2.4 Both sides premise-backed

**Decision:** every compared value traces to a consulted premise. A threshold or
public baseline is not a bare goal constant; it enters as a leaf (`Attested` for a
cited baseline, `Assumed` for a stipulated target) feeding a premise slot. This keeps
dependency accountability total and the certificate grammar uniform.
Recorded alternative: a `(lit)` side-marker for premise-free goal constants — deferred;
it weakens accountability and saves only one leaf declaration.

## 3. Factivity, conflict, and framework fit

### 3.1 Factivity firewall

An accepted certificate discharges the *comparison relative to the premise
conclusions* — never the truth of any cell. The measurement leaves stay defeasible:
attackable, quarantinable, admission-governed. You cannot argue with the arithmetic;
you argue with the measurements. This is the same sentence `ra@1` and the corpus policy
already state, and it is the paper's Hume's-fork side condition.

Stated exactly (eng review 2026-08-06, D13): since both numerals appear in the goal,
the relation itself is decidable from the goal alone; what the premises add is
**provenance anchoring** — an accepted `ord@1` step certifies that each cited
premise's unique numeric literal equals the corresponding goal numeral (and that the
goal's relation holds of those numerals). The plan and the paper should say this
plainly rather than let "certifies the comparison" suggest more. Note also that the
dependency set is a metatheory-level obligation: the runtime seam (`buildCertOk`)
collapses acceptance to a `Bool`, so `deps` feeds the soundness statement and audit
reports, not the checked graph.

### 3.2 R12 and why comparisons declare no contraries

`num_lt`/`num_le` must head **no** declared contrary pair (spec §8.1 Path B).
This is not a workaround but a theorem: comparison goals are *decidable against a
shared ground truth*, so a sound backend can never accept two conflicting members of
the family over the same literals. Intra-family consistency is enforced at acceptance
time by arithmetic, not by attack structure — declared contraries would add nothing
and would trip R12.

**Mechanized, not prose (eng review 2026-08-06, D9):** the exclusivity facts are
proved in `Ord.lean` as intra-family exclusion lemmas over the shared `Dec`
comparisons — `lt(A,B) ⊥ lt(B,A)` and `lt(A,B) ⊥ le(B,A)` on identical literals
(cross-multiplied `Int` trichotomy, core Lean) — and covered by `AxCheck.lean` like
every other theorem. The paper cites the lemma, not an observation.

### 3.3 Framework fit

The Dung layer never sees a number. A strict comparison instance is an ordinary
argument node whose sub-arguments are the (defeasible) measurement leaves; grounded
semantics stays purely qualitative. This is the classic strict-over-defeasible ASPIC
pattern the framework already accommodates. Explicit non-goal: numeric *semantics*
(weighted or graded argumentation) — numbers live only inside literals that one
backend interprets.

### 3.4 Relation to `rel_drop_ge`

`ra@1` stays as is: its goal bundles a computation (the recomputed drop) that plain
comparison cannot express. `ord@1` is not a generalization of `ra@1`; they are sibling
theories behind the same seam.

### 3.5 Shared helpers

Factor `parseDecimal`, `parseCanonicalNat`/`parseCanonicalInt`, `premiseCell`, **and
`decodeSlot` with the shared `"prem"` spelling** (eng review 2026-08-06, D7) out of
`Lara.Strict.RA` into `Lara.Strict.Cell` (one definition, two importers; keeps both
modules inside the file-size discipline). Each backend keeps its own closed top-level
cert tag (`radrop` / `ordcmp`); the slot-reference sub-grammar has exactly one home,
so the Tag discipline gets stronger, not weaker. Pure move — `ra@1` behavior
byte-identical (`RASpec` + existing differential pins are the regression suite).

**Lean mirror (eng review 2026-08-06, D5):** the same factoring lands as
`lean/Lara/Cell.lean` — `Dec`, `parseCanonNat`/`parseCanonInt`/`parseFracDigits`,
`parseDecimal`, `premiseCell`, the slot decoder, and the cross-multiplied comparisons
(`RatEq`/`RatGe`, plus new `RatLt`/`RatLe`) move out of `namespace Lara.RA`;
`RA.lean` and `Ord.lean` both import it. Definitions travel with their lemmas;
sibling theories stay symmetric with no `Ord → RA` dependency.

### 3.6 Composition: the bridge rule

An accepted comparison atom is terminal unless a policy rule consumes it — in
corpus-v1 the actual "beats" claim is `better(S, B, Q, D)` and nothing consumes a
bare `num_lt`. The deliverable-6 fixture therefore includes a **bridge rule**: a
defeasible policy rule whose premises are the strict `num_lt` conclusion plus the
binding atoms naming the systems/measurand, and whose conclusion is the comparative
claim. This demonstrates "this number beats that number" as a *supported claim*, not
a free-floating ground fact, and is the template a future corpus unit instantiates.

## 4. Deliverables

1. `src/Lara/Strict/Ord.hs` — `OrdRel` (`OLt | OLe`), `OrdCert`, closed decoder
   (premise-only slots, §2.2), replay, `mkOrdBackend`; registered in
   `Lara.Driver.Internal.mkRegistry`.
2. `src/Lara/Strict/Cell.hs` — the factored cell helpers incl. `decodeSlot` (§3.5);
   module comment carries the §2.3 funnel diagram.
3. `lean/Lara/Cell.lean` — the Lean mirror of the factoring (§3.5): `Dec`, parsers,
   `premiseCell`, slot decoder, `RatEq`/`RatGe` + new `RatLt`/`RatLe`.
4. `lean/Lara/Ord.lean` — adapter soundness: accepted certificate ⟹ the comparison
   holds of the premise cells, discharging the same obligations `RA.lean` discharges
   (1–4 as Lean theorems via the `Backend` structure fields; 5 by construction;
   6 doc-level per `docs/strict-backend-decision.md`). Proof core: the shared `Dec`
   cross-multiplied `Int` comparisons — core Lean, no `Rat`, no Mathlib; `soundFull`
   repackages `checkB` facts (no witness cancellation, simpler than RA). Plus the
   §3.2 intra-family exclusivity lemmas. `AxCheck.lean` extended; `sorry`-free,
   standard axiom trio.
5. Lean-side registration: extend the registry in `lean/Lara/Driver.lean` (the
   `nd@1`/`ra@1` pair) and `Lara.Examples.registryEx` with `ord@1`, so the
   differential driver exercises accept paths on both sides.
6. Differential driver + `Examples/` conformance pins covering the full replay branch
   matrix: per-relation accepts (`num_lt`, `num_le`, incl. negative and fractional
   cells), boundary pins (`num_lt(A,A)` rejects; `num_le(A,A)` accepts), same-slot
   cert (deps dedup to one slot), and rejects for wrong cell (left AND right),
   zero-literal premise, ambiguous (2+-literal) premise, non-canonical numeral (goal
   and cert slot), malformed/unknown cert tag, wrong predicate/arity, slot out of
   range, theory-entry slot (`≥ nPrem`, §2.2), relation fails per arm, unknown
   digest.
7. Haskell property tests mirroring the `ra@1` suite (conformance evidence; Lean
   carries soundness).
8. A policy fixture with a beats-baseline `num_lt` strict rule **and the §3.6 bridge
   rule** composing it into a comparative claim (frozen corpus-v1 is not touched;
   corpus extension is a separate decision, recorded in `TODOS.md`).

## 5. Metatheory impact: none framework-level, one local proof

The framework theorems (support typing, compilation, grounded fixpoint, four-state
status, consistency, Erase/backend-replacement Theorem 2) are parametric in the backend
registry: they quantify over any backend satisfying the seam obligations. Adding
`ord@1` therefore changes **zero existing proofs**. The new obligation is exactly one
adapter-level Lean module (deliverable 4), the same shape as `RA.lean`. This is the
conservative-extension story the paper should state: theories plug in; Theorem 2 is why
nothing else moves.

## 6. Non-goals

- ε-tolerance agreement between duplicate reports of one measurand — belongs in
  `DupGroup`/`GroupConflictMode` (data integrity, failure mode quarantine → `gap`),
  a separate plan.
- Units, magnitudes, significant figures.
- Arithmetic *expressions* in goals (`num_lt(A - B, C)`): the goal grammar stays
  literals-only; computation belongs in a dedicated theory (as `ra@1` shows).
- Evidence grounding (hash + re-extraction) — tool layer, permanently out of the
  language.
- Any numeric weighting of the argumentation semantics.

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | `/codex review` | Independent 2nd opinion | 1 | issues_found (Claude subagent fallback) | 6 findings, 4 accepted, 2 procedural/absorbed |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | CLEAR (PLAN) | 12 issues, 0 critical gaps, all folded into plan |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | — |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | — |

- **CROSS-MODEL:** Outside voice (Claude subagent; Codex at usage limit) found 4 substantive tensions beyond the 8 section findings — theory-entry back door (accepted: premise-only slots), missing composition story (accepted: bridge rule + plain semantics wording), `num_eq` degeneracy (accepted: family is `{lt, le}`), proposition-identity aliasing (accepted: documented, no design change). All resolutions user-approved and folded into §2–§4.
- **VERDICT:** ENG CLEARED — ready to implement (2026-08-06, commit 1e6cd88).

NO UNRESOLVED DECISIONS
