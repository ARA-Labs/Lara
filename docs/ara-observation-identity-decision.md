# Decision: unique observation lookup without rewriting ARA history
**Date:** 2026-10-06

## TL;DR

Use O190 through O193 to identify the four historical observations that shared O176 and O177. The original observations, reasoning log, session records and inventory report remain unchanged. A new append-only record, `ara/staging/observation_aliases.yaml`, names each occurrence and qualifies each historical reference. Bare lookup of O176 or O177 fails; an aggregate duplicate finding cannot select an observation.

## Problem

[Issue 18](https://github.com/ARA-Labs/Lara/issues/18) found two occurrences each of O176 and O177 in `ara/staging/observations.yaml`. One pair was recorded at `2026-09-12T01:38+00:00`, the other at `2026-09-12T05:54+00:00`. Choosing the first or last row by ID would silently attach the wrong content and provenance to a reference.

The September 12 session also retained the first pair's pre-merge spellings, O174 and O175, after the reasoning log recorded their renumbering. Those spellings still identify different, valid observations globally: O174 concerns cross-runtime nesting refusal categories, and O175 concerns source checks for duplicated constants. Only the qualified September 12 references change their effective target.

## Constraints

Preserve every historical row and reference line. Do not copy content into replacement observations, invent an endorsement, change a promotion, or alter compiler and evidence semantics. All four observations remain unendorsed, unpromoted, ai-suggested heuristics. The repair allocates IDs after O189, the highest observation ID present when the audit ran; it does not use the issue's outdated O186 maximum.

The observation identity gate runs alongside the existing session-index and located-source quotation gates. Their contracts and projection rules remain unchanged.

## Proposed approach

`load_observations(repo_root)` in `scripts/check_ara_observations.py` builds the effective index only after the complete registry validates. Each unique original ID remains a lookup key. Every occurrence of a duplicated ID must have one fresh canonical alias. Canonical IDs cannot collide with any original ID or another alias. Missing registrations, a new duplicate, duplicate YAML keys, selector mismatches and fingerprint mismatches fail before any lookup succeeds.

| Canonical ID | Historical ID | Timestamp (UTC) | Exact `bound_to` | Content identified |
| --- | --- | --- | --- | --- |
| O190 | O176 | 2026-09-12T01:38+00:00 | N326_consistent_groups | Conditioning edit is the identity when its trigger set is empty |
| O191 | O177 | 2026-09-12T01:38+00:00 | N327_lara_sources, N326_327_conformance | A derivation door admits frontend-only sources to a two-runtime comparison |
| O192 | O176 | 2026-09-12T05:54+00:00 | N334_cli_text_boundary, N334_solo_locale_gate | A process owns its text boundary across entry points and output handles |
| O193 | O177 | 2026-09-12T05:54+00:00 | N334_solo_locale_gate | A locale harness decodes its child's streams independently |

The registry uses `schema_version: 1`, an `aliases` list and a `references` list. An alias contains `canonical_id`, `historical_id`, `timestamp`, exact ordered `bound_to`, and `record_sha256`. Optional `prior_ids` records pre-merge spellings for qualified references only: O190 allows O174 and O191 allows O175. To compute the record fingerprint, remove exactly `promoted`, `promoted_to`, `crystallized_via` and `stale` from the parsed mapping, then hash the UTF-8 serialization from Python `json.dumps(identity, ensure_ascii=False, sort_keys=True, separators=(",", ":"), default=str)` with SHA-256. These four fields track later promotion and maturity updates; they do not identify the historical occurrence. Every other field remains protected, including content, context, provenance, timestamp, node bindings, potential type and any newly added field. A sanctioned promotion or stale-flag update therefore preserves the alias and reference fingerprints. The returned observation retains its original `id` and its current promotion state; the canonical key identifies it without modifying that row.

A reference contains a normalized repository-relative `path`, one-based `line`, `line_sha256`, `kind`, `reason`, and `bindings`. The line fingerprint hashes the exact UTF-8 line without its line terminator. Each lookup binding names `historical_id`, `canonical_id` and the expected `record_sha256`, so changing the target to the other occurrence fails even if the source line is unchanged. An `aggregate` reference has no bindings and rejects lookup. The checker scans all Markdown and YAML files under `ara/`, excluding the original observations and the registry itself, and rejects any unregistered mention of a duplicated observation ID.

## Alternatives considered

Renumbering the original rows and rewriting old trace text would remove ambiguity by destroying the record of what each session actually wrote. Keeping the earlier occurrence as O176 and O177 would leave bare references open to a misleading interpretation. Fresh canonical IDs for all four occurrences avoid both problems.

Selecting a row from timestamp alone would miss a wrong node binding. Selecting from position alone would turn list ordering into identity. The exact timestamp and node selector plus the immutable-field fingerprint pin the intended occurrence without either shortcut.

## Tradeoffs

The registry is a local repository extension, not a change to the external ARA framework. The code-consumer audit found no pre-existing observation reader in the repository's Python, Haskell, shell, JavaScript, TypeScript, Lean or workflow files. The new API and CLI therefore need no in-repository caller migration. External tools that read only `observations.yaml` will still see the historical duplicates; they must adopt this registry or refuse ambiguous IDs before promotion. The external `ara check` command is not claimed to understand this extension.

Line-qualified forward records are intentionally strict. Append-only additions leave their source locations intact. Rewriting or moving an audited line fails the gate rather than silently rebinding its meaning. The registry itself must grow by appending new alias and reference entries; existing bindings are durable decisions. Future ID allocation must reserve both original IDs and `aliases[].canonical_id`, so O190 through O193 cannot be allocated again.

## Migration

The audit found fourteen historical source lines outside the observation rows: nine lookup lines and five non-lookup aggregate lines. Each is recorded in the registry. No original observation, trace line, index row or frozen report is rewritten by this repair.

| Source (repository-relative) | Line | Effective reading |
| --- | --- | --- |
| `ara/trace/pm_reasoning_log.yaml` | 1611 | Turn 1 O176 points to O190; O177 points to O191 |
| `ara/trace/pm_reasoning_log.yaml` | 1634 | Turn 3 O176 points to O192; O177 points to O193 |
| `ara/trace/pm_reasoning_log.yaml` | 1680 | Same-day staleness summary covers all four occurrences; non-lookup aggregate |
| `ara/trace/pm_reasoning_log.yaml` | 1743 | Duplicate discovery and issue creation; non-lookup aggregate |
| `ara/trace/sessions/2026-09-12_001.yaml` | 74 | Turn 1 event's pre-merge O174 points to O190 |
| `ara/trace/sessions/2026-09-12_001.yaml` | 81 | Turn 1 event's pre-merge O175 points to O191 |
| `ara/trace/sessions/2026-09-12_001.yaml` | 107 | Turn 3 O176 observation event points to O192 |
| `ara/trace/sessions/2026-09-12_001.yaml` | 114 | Turn 3 O177 observation event points to O193 |
| `ara/trace/sessions/2026-09-12_001.yaml` | 358 | Pending identity-of-empty-edit O174 points to O190 |
| `ara/trace/sessions/2026-09-12_001.yaml` | 359 | Pending derivation-door O175 points to O191 |
| `ara/trace/sessions/2026-09-12_001.yaml` | 361 | Explicit turn 3 pending O176/O177 point to O192/O193 |
| `ara/trace/sessions/2026-10-06_001.yaml` | 176 | Earlier duplicate audit finding; non-lookup aggregate |
| `ara/trace/sessions/2026-10-06_001.yaml` | 192 | Repair worklist names the collision, not an occurrence; non-lookup aggregate |
| `ara/evidence/results/certified_evidence_inventory_2026-10-06.md` | 69 | Frozen duplicate census remains true of raw historical rows; non-lookup aggregate |

The four staging occurrences are the only original rows using O176 or O177. No other existing trace, logic, evidence or staging-content reference to either ID was found. The old inventory's raw duplicate count remains correct; the new effective lookup is unique because aliases distinguish the contents. The O174/O175 remappings above are contextual exceptions, not global aliases.

## Recommendations

Use canonical IDs in new records. For a historical reference, pass its registered source and line to `ObservationIndex.lookup(identifier, source=..., line=...)`. Never use an aggregate finding as an observation key. For example:

```sh
python3 scripts/check_ara_observations.py --lookup O190
python3 scripts/check_ara_observations.py --lookup O176 \
  --source ara/trace/sessions/2026-09-12_001.yaml --line 107
```

Run the observation regressions and all three provenance gates after integration. The required Haskell workflow runs the observation tests and checker beside the session-index gate, using its existing PyYAML installation pattern. The commands below are verification instructions, not a claim that they ran during implementation.

```sh
make ara-observations-test ara-observations ara-session-index ara-source-spans
python3 -m unittest scripts/test_check_ara_session_index.py scripts/test_check_ara_source_spans.py -v
```

The negative regressions cover bare ambiguous lookup, unregistered and future duplicates, wrong occurrence selectors, changed immutable observation fields, colliding canonical IDs, repeated occurrence registration, unregistered or changed reference lines, incorrect reference targets, aggregate lookup refusal, strict YAML parsing and preserved global O174/O175 lookup. Positive regressions permit each of the four sanctioned state fields to change and preserve canonical and contextual lookup after promotion. Unknown state fields remain protected by the fingerprint.
