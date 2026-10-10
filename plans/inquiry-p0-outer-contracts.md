# Inquiry P0: freeze the outer process contracts
**Date:** 2026-10-10

## TL;DR

[Issue #22](https://github.com/ARA-Labs/Lara/issues/22) adds checked stability and claim-impact analysis on top of the research-process layer that [#41](https://github.com/ARA-Labs/Lara/pull/41) mechanized. Its first stage, P0, freezes the outer contracts every later stage reads and writes: one versioned input document that carries a decoded process record, the finite universe of possible completions, and the queries to answer; one versioned result document; and the limits at which evaluation refuses instead of answering. P0 lands these as Lean definitions with their metatheory, a wire grammar, and a fixture set whose expected outputs the Lean reference computes. It adds no Haskell code. The Haskell codecs and CLI door are P6, and the Haskell evaluator conforms to the frozen contract from P1 on.

Plan status: **draft, awaiting review.** No definition below is frozen until this plan is approved and its Lean port lands.

## Problem

`docs/theory-process.md` defines verdicts and entitlement over a *declared finite carrier* of complete histories. Every fixture declares that carrier by hand: `Lara.Examples.ProcessARA` lists its `Candidate` traces and decodes its `AraSource` in Lean. Nothing outside Lean can state a process record, and nothing says where a carrier comes from for a record nobody hand-modeled. So the checker cannot be handed a process question at all.

Three gaps block every later #22 stage:

- **No input contract.** `DecodedRecord`, `AraSource` and `extract` (`lean/Lara/Process/Bridge.lean`) have no wire form, on either side.
- **No carrier contract.** `verdict` quantifies over a `Fintype X`, but the set of histories a record could have come from is infinite unless something bounds which events could have happened unrecorded. That bound is a modeling assumption, and it has to be stated in the input, not inferred from the record.
- **No result or refusal contract.** Exact evaluation is exponential in the universe. #22 requires it to fail closed at declared limits, and there is no shape for a refused answer.

#22 was written before #41 and names the old T0–T8 stages and a `plans/inquiry-stability-and-impact.md` that is no longer in the repo or its history. This plan restates P0 against the definitions that actually landed.

## Constraints

- Preserve `lara-core@0.3`, the core wire, every existing theorem statement, the corpus, the mutation base and the freeze tags. The new documents are a separately versioned outer layer, like `lara-map@1` and `pw-run 1`. If a step finds it needs a core or corpus change, it stops and the change is budgeted in an issue first.
- Mirror the frozen Lean vocabulary in `Lara.Process.Vocabulary` exactly. The wire adds spellings and an identifier table; it adds no semantics.
- Keep the core symbolic (`CLAUDE.md`). Fixed vocabularies are closed sum types with one spelling table each; identifiers stay distinct newtypes per namespace. Strings exist only in the pre-parse `SAtom` and in `SourceRef`, which is decode-boundary evidence the theory never interprets.
- Fail closed. A missing field stays unknown, absence of an entry is never read as completeness, and a limit breach yields a refusal, never a partial or approximate verdict.
- Hypothetical completions never acquire observed standing. Nothing in the universe declaration is evidence that an event happened.
- Mechanization discipline applies: every definition frozen here lands in Lean with its metatheory and `AxCheck.lean` rows, `sorry`-free, within `propext`, `Classical.choice` and `Quot.sound`. P0 touches `lean/` and defines a wire contract, so it must pass `make local-gates` before review.
- No empirical protocol. Fixtures are finite reference models, not measurements.

## Proposed approach

### What does the input document contain?

One top-level form, `process-input 1`, in the canonical S-expression printer of `Lara.Wire`:

```text
(process-input 1
  (names    ...)              ; per-namespace identifier tables
  (record   ...)              ; the AraSource: events, orderings, coverage, submissions, cutoff
  (reader   (admits instrumented-log signed-attestation))
  (universe ...)              ; events that may have happened unrecorded
  (limits   (events N) (completions N))
  (queries  ...))
```

**Record.** The entries of `AraSource` in file order, each event, ordering and coverage entry carrying its `SourceRef` (file, entry, optional span). The decoder produces exactly `AraSource`; `extract` then runs in the shared definitions. Entry order carries no meaning, as in the theory (`reordered_equivalent`).

**Identifiers.** ARA names events, runs and datasets with strings; the Lean vocabulary uses `Nat`-indexed newtypes. The `names` block declares, per namespace (event, actor, plan, run, claim, source, data, version, family, witness), the list of names in use. The decoder interns each name to its index in that list, and the result printer spells indices back through the same table. A name used but not declared, or declared twice in one namespace, is a decode error. Separate namespaces get separate tables, so a plan name cannot silently resolve to a dataset.

**Universe.** A finite list of stamped events that may appear in a completion without appearing in the record, for example "an evaluation read of dataset D by actor A". Completions of a record over a universe `U` with horizon `cutoff` are exactly the histories that:

1. are `ValidThrough cutoff`;
2. contain every recorded event, plus only events from `U`, each at most once;
3. are compatible with the extracted record under the admitted bases (`DecodedRecord.Compatible`).

This set is finite by construction, which gives the `Fintype` carrier `verdict` needs. Declaring `U` is a modeling assumption, printed in every result next to the verdict it conditions. An empty universe states that nothing unrecorded happened. That is a strong assumption, and the result says so rather than treating it as a default.

**Queries.** Two forms:

- `(verdict <name> <formula>)`. A formula is `Lara.Process.Formula` over a closed atom vocabulary taken from `Lara.Process.Order` and `Lara.Process.Statistics`: `run-precommitted`, `predictable`, `split-selection`, `family-count-at-most`, and a ledger form reading `warrantedLevel` against a stated level. The answer is the exact supervaluation `verdict` over the completions. The Kleene evaluator is sound but weaker (`kleene_incomplete`), so it is not reported as the verdict.
- `(audit <name> <claim> <witness> <profile>)`. This runs `ArgumentEntitled` with the submitted witness, which must appear in the record's submissions. The profile is spelled field by field. `acceptsCoverage` is a predicate in Lean, so the wire spells it as the finite list of coverage kinds the profile accepts. `Warranted` needs each completion's argumentation framework, which comes from the checked Lara source, and that runtime is P1. P0 freezes the audit syntax and its Lean meaning over a supplied `WarrantModel`, and the P0 reference answers audits only for the hand-modeled warrant fixtures.

**Declared policies.** `RecordCoverage.declaredPolicy` needs a policy vocabulary its model interprets. Version 1 has none: the policy type is `Empty`, and a `declared-policy` coverage entry is a decode error with tag `unsupported`. Adding policies is a version bump.

### What does the result contain?

`process-result 1` on success, `process-error 1` on refusal. Both go to stdout with exit codes 0, 1 and 2, as for the PW doors, and stderr stays empty.

A result reports, per query: its name; its verdict (`inconsistent`, `certainTrue`, `certainFalse`, `unknown`); the number of completions; and for `unknown`, one completion where the formula holds and one where it fails. The witnesses use the history's event names, so a reader can check them by hand. `sensitivity` from `Lara.Process.Inquiry` is the general form, and P3 builds on it. The result also echoes the admitted and unadmitted coverage attestations with their source references, and the universe and limits, because every verdict is conditional on them.

A refusal has a closed tag (`syntax`, `malformed`, `unsupported-version`, `unsupported`, `limit-exceeded`) and a detail string. Consumers branch on the tag only; cross-checks mask the detail, as in `scripts/check-pw-conformance.py`.

### Where are the limits?

`limits` in the input caps the number of distinct events (recorded plus universe) and the number of completions enumerated. Exceeding either yields `limit-exceeded` and no verdicts. The checker also has fixed ceilings that no input can raise: the existing `maxDepth = 10000`, plus new `maxProcessEvents` and `maxProcessCompletions`. Each ceiling is declared once in Lean and once in Haskell, and a script checks the two values match, as `scripts/differential.sh` does for `maxDepth`. The ceiling values are set at review, sized so the largest P0 fixture stays well inside them.

### What does P0 prove?

New Lean module `lean/Lara/Process/Wire.lean`, with fixtures in `lean/Lara/Examples/ProcessWire.lean`:

| Obligation | Statement |
| --- | --- |
| Codec retraction | `decode (encode d) = ok d` for every well-formed input document, and the same for results |
| Identifier renaming | for every injective renaming of identifiers within each namespace, the decoded record's completions correspond one to one, and every query's verdict is unchanged. This justifies interning names by position |
| Universe semantics | `mem_completions`: a history is in the enumerated completions iff it satisfies conditions 1–3 above. `completions_nodup` holds too |
| Universe monotonicity | a larger universe gives a superset of completions, so certainty can only be lost (`certain_antitone_universe`). The empty universe is the strongest assumption |
| Bridge agreement | over the universe carrier, a query's verdict equals `verdict (decodedCompat src) φ` from `Lara.Process.Bridge`, so P0 adds no second semantics |
| Fail closed | a limit breach or an `unsupported` form produces a refusal and no verdict (`limitExceeded_noVerdict`) |
| Spelling tables | every closed vocabulary's spelling table is injective (as `tagToString_injective`) |

The enumerator P0 ships is the plain reference one: subsets of the universe, interleaved with the recorded events, then filtered. P2 replaces it with an efficient generator proved equal to this one. P0 only has to be correct on small fixtures.

### What does P0 ship besides Lean?

- A grammar section in `docs/theory-process.md`, and a row for the process input/result documents in the "Which contracts are current?" table of `docs/spec.md`.
- `fixtures/process/run/*.sexp` with `*.expected` goldens. The fixture set re-expresses every ARA fixture in `Lara.Examples.ProcessARA` as a wire document (omitted read, admitted log coverage, declared coverage not admitted, failed sibling preserved, contradictory ordering, reordered entries), plus refused documents covering each refusal tag. A Lean exe `process-run` emits the goldens. Until the Haskell door exists in P6, `make process-theory` checks only that `process-run` reproduces them.
- `AxCheck.lean` rows for every new theorem.

### Which choices need the reviewer?

1. **Freeze `audit` now or later.** Freezing it now avoids a hard version bump when P1 lands, but the frozen syntax will exist before any runtime outside the warrant fixtures can execute it. I recommend freezing it now: the Lean meaning is already fixed by `ArgumentEntitled`.
2. **Report the Kleene verdict as well.** I recommend no. Two verdicts invite readers to cite the weaker one.
3. **Reporting choices.** `DecodedRecord.Compatible` reads the record's events as the reported ones, so the universe carrier has no separate reporting choice `rho`. Version 1 keeps that. A record whose reporting protocol matters (for example, selective reporting of runs) then needs a coverage assertion to say so. Adding `rho` to the wire later is a version bump.

## Stage map for #22 after this plan

| Stage | Scope | Depends on |
| --- | --- | --- |
| P0 | This plan: input/result/refusal contracts, universe carrier, limits, Lean codec and metatheory, fixtures | #41 (landed) |
| P1 | Checked-source runtime: per-completion argumentation framework from the Lara checker, so audits run on real sources | P0 |
| P2 | Efficient finite family generation, proved equal to the P0 reference enumerator | P0 |
| P3 | Exact stability, single and joint sensitivity, minimal conditional assumptions | P1, P2 |
| P4 | Graph-difference locality | P1 |
| P5 | Source and public-status impact certificates | P3, P4 |
| P6 | Haskell codecs and `lara process` CLI door | P0 (codec), P3 (analysis) |
| P7 | Haskell–Lean conformance gate and adversarial runtime cases | P6 |
| P8 | Bounded semantic evaluation and source-transition measurements | P7 |
| P9 | Separately designed and budgeted live-loop protocol and run | P8 |

The Haskell codec half of P6 can start as soon as P0 lands. It does not wait for P3.

## Out of scope

- Decoding ARA prose into a record, and capturing processes as they happen (`docs/corpus-map.md`, "The process boundary").
- Haskell code of any kind.
- Infinite horizons and online FDR ([#39](https://github.com/ARA-Labs/Lara/issues/39)).
- Any change to `lara-core@0.3`, the corpus, the mutation base or a freeze tag.

## Cost

Estimate: 800–1,500 lines of Lean (codec, renaming invariance, universe semantics, reference enumerator, fixtures), about 15 fixture documents with goldens, and two documentation sections. One PR, titled `feat(process): freeze the inquiry outer contracts`. No corpus regeneration, no axis-(c) rerun, no freeze-tag bump.
