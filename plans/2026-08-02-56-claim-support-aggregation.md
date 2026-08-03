# #56 — Corpus claim-support aggregation (the paper's `\msfive` numbers)

> **Status: complete — closed by PR #58.**

Branch: `56-corpus-claim-support`. Follow-up milestone (non-zero certificate
path): #57.

## Goal

A deterministic, corpus-descriptive aggregation over the **frozen** 60 corpus
units (`corpus-units/MANIFEST.tsv`) that emits the four numbers the paper's
*Claim-support outcomes* paragraph needs, checked into `measurements/` beside
`report.*` / `ablation.*`. Reuse the T3 decode/run core (`decodeCheckInputFile`
+ `runCheck`); this is a reporting pass, **not** new metatheory, so no Lean
obligation (the checker theorems it rests on already exist and are proven).

## Inputs per unit (three, joined by claim/leaf id)

1. `unit.core.sexp` → `decodeCheckInputFile` → `CheckInput`; `runCheck` →
   `Verdict (Accept verdictLabels _ verdictStatuses)`. The core is authoritative
   for **status** and **load-bearing labels**, but drops leaf metadata
   (`unitLeaves :: [(LeafId, Prop)]` only).
2. `unit.lara` → `Lara.Syntax.parseProgram` → `Program` with full `DeclLeaf`
   (kind/provenance/refs), `DeclArg` (`argConcl`, incl. `Challenges` targets),
   `DeclAttack`. The surface is authoritative for **provenance/refs** and
   **dead-end classification**.
3. `unit.lara` raw text → scan for the documented `strict_certifier` /
   `strict-flavored` header annotations (context for number 4).

`runCheck` is the same function that generated the frozen `expected.json`, so
computing from it keeps the differential/freeze discipline; the T3 harness
already guarantees `runCheck ≡ expected.json`.

## The four numbers — operationalizations

**(1) Status distribution.** Over the 60 claims, count `verdictStatuses` by
`Status ∈ {Justified, Defeated, Contested, Gap}`.

**(2) Load-bearing leaves by provenance.**
- *Load-bearing leaf* = a `LeafId` in `Lara.SupportTerm.leaves` of a support
  argument whose `verdictLabels` label is `LIn` (it actually holds up a
  justified claim). Arg index ↔ `unitArgs` declaration order.
- **Abandoned axis (recorded so we don't retry it):** an *evidence origin*
  refs-split (paper-derived = has a non-trace ref, else agent-generated) was
  planned to give a substantive "paper-derived vs agent-generated" breakdown.
  It is DEGENERATE on the frozen corpus — the refs are ~96% pointers into the
  agent's OWN artifact files (`logic/` 261, `trace/` 63, `evidence/` 33,
  `src/`+`kernel/` 26), with only 7 direct paper pointers — so any trace-based
  split collapses (167/0). This corpus is agent-native: its evidence is
  agent-produced, so there is no honest balanced split.
- **As-built axes (decision: provenance field + paper-anchor sub-number):**
  - *provenance field* — `{User, AiExecuted, Checker}` counts. All load-bearing
    leaves are `AiExecuted` (0 human/paper-authored): the honest headline for
    (2), and itself a finding — the corpus is fully agent-lowered.
  - *paper-anchor sub-number* — how many load-bearing leaves additionally cite a
    DIRECT paper-document locator (`isPaperAnchorRef`: `E\d+#…`, or a bare
    `Table`/`Figure`/`Appendix`/`Theorem`/`Lemma`/`Section`/`paper-`/`PAPER.`
    token). Measures paper-anchoring without pretending human-authored leaves
    exist.
  - *kind* — `observed`/`attested` breakdown, included as free context.
- Emit the same three axes over ALL leaves for context.

**(3) Dead ends that produce a valid typed attack.**
- *Valid typed attack* = a decoded `Attack` (Rebut/Undercut/Undermine) present
  in the accepted unit (accept-class ⇒ every declared attack type-checked).
- *Dead-end-sourced* = the attacking arg's `argConcl = Challenges …` and *any*
  leaf of its support term carries a ref whose path contains `trace/` or
  `exploration_tree` (the shipped `deadEndSourced`; inert-equivalent to the
  narrower leaf-root `uN` phrasing on this corpus, where every challenge arg is
  single-leaf).
- Report total valid typed attacks, the dead-end-sourced subset (the paragraph's
  number), and the by-type breakdown (corpus is undercut-only).

**(4) Fraction of load-bearing strict steps carrying a checked certificate.**
- *Load-bearing strict step* = an `LIn` argument instantiating a **strict**
  policy rule. corpus-v1 is all-defeasible ⇒ denominator 0.
- Numerator = those with a checked certificate ⇒ 0.
- Emit `0 / 0` (fraction N/A) with the documented strict-flavored population
  (the 5 units carrying the `strict_certifier` M0 annotation) and the #57
  pointer. Compute the denominator from actual rule modes (via `parsePolicy` on
  `corpus-v1.policy.lara`) so the number goes non-zero automatically once #57
  lands.

## Deliverables

- `src/Lara/ClaimSupport.hs` (pure): record + aggregate types, `computeUnit`,
  `aggregate`, ref-origin/dead-end classifiers, JSON/TSV rendering via
  `Lara.ExpectedJson.JValue`. Reuse `Lara.Measure.EnvBlock`. (~450 lines as
  shipped; the per-unit IO loader lives in `Lara/ClaimSupport/Load.hs`, shared
  by the harness and the test.)
- `scripts/claim-support.hs` (IO): manifest-driven discovery, per-unit
  decode+run+parse, env, write `measurements/claim-support.{json,tsv}`.
- `test/ClaimSupportSpec.hs`: pure-classifier tests (`isPaperAnchorRef`) + an
  end-to-end run over the 60 units that PINS every headline number as a
  regression guard. Wire into `lara.cabal` + `test/Spec.hs`.
- Run the harness; the committed deliverable is `measurements/frozen/`
  claim-support.{json,tsv} (the working `measurements/` copy is gitignored).

## Out of scope

- Making (4) non-zero (implement a certifier) → #57.
- Enriching (2) by re-tagging provenance to `user` → dishonest (every leaf is
  genuinely agent-lowered); the paper-anchor sub-number gives the real,
  substantive figure with no corpus edit.

## Results (as-built, frozen at `ee01ae3`)

Emitted to `measurements/frozen/claim-support.{json,tsv}`; pinned by
`test/ClaimSupportSpec.hs`.

1. **Status:** 48 gap / 9 justified / 3 defeated (matches the frozen `MANIFEST`).
2. **Load-bearing leaves:** 36 total, all `ai-executed` (0 human/paper-authored);
   **13 paper-anchored**; kind 20 attested / 16 observed. (All leaves: 167;
   49 paper-anchored; 106 attested / 61 observed.)
3. **Dead ends → valid typed attack:** 3 typed attacks total, **2 dead-end-sourced**
   (the third, `fre/C04`, is a CQ-driven paper-evidence undercut).
4. **Load-bearing strict steps w/ checked certificate:** **0 / 0** (corpus-v1
   all-defeasible); 5 `strict_certifier`-annotated units; future work → #57.

Follow-up: #57 (exercise the strict/certificate path so number 4 is non-zero).
