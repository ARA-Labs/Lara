# Contributing to Lara

This file is the short version of how changes are made and verified here; the
[README](README.md) covers what Lara is and how to use it.

## Development setup

Two toolchains:

- **Haskell** (checker, CLI, tests): GHC + cabal via
  [ghcup](https://www.haskell.org/ghcup/); developed on GHC 9.14.1 /
  cabal 3.16; CI and the release binaries build with GHC 9.6.
- **Lean 4** (mechanized reference semantics): [elan](https://github.com/leanprover/elan)
  with the toolchain pinned in [`lean/lean-toolchain`](lean/lean-toolchain).

```sh
cabal build all          # library + CLI
cabal test               # property + doctest suites
cd lean && lake build    # proofs
```

## Verification gates

The required `Haskell` workflow builds and tests the checker on every push
to `main` and every PR into it. Lean checks run separately. The optional
`Lean` workflow runs the proof build, axiom audit, PW and axiom-withdrawal
examples, and semantics-registry checks when a reviewer adds the `lean` label.
Local `make lean-gate` also runs the BHL examples; `make cross-check` runs only
locally. See [verification scope](docs/implementation.md#ci-and-local-gates).

Before asking for review on any change that touches `lean/`, a wire contract,
or a golden either side emits, run:

```sh
make local-gates         # lean-gate + cross-check, in that order
```

On macOS this needs GNU sed and coreutils
(`brew install gnu-sed coreutils`) on `PATH` ahead of the BSD tools.

## How work is tracked

- Open work lives in [GitHub issues](https://github.com/ARA-Labs/Lara/issues).
  There is no in-repo backlog file; do not create one.
- [`docs/`](docs/README.md) describes the current design of Lara by subject:
  contracts, semantics, mechanized results, assumptions and limits. Fold a
  settled decision into its subject document as a present-tense statement,
  keeping at most the rationale or counterexample that explains it. Decision
  history, rejected alternatives, review records and dated status notes belong
  in `ara/` and Git history, not in `docs/`. Unlanded implementation plans live
  in `plans/` and are deleted once executed.
- [`ara/`](ara/) is this project's own research artifact. A session that
  introduces or materially changes a feature, design, or theory — or runs or
  interprets an experiment — updates it; routine fixes, guidance, and review
  cycles do not.

## Code conventions

- Keep the compiler core symbolic: a fixed vocabulary is a closed sum type
  with one `toString`/`parse` table; a domain-meaningful identifier is its own
  newtype, one type per namespace; a value carrying a kernel invariant is
  built only through its sanctioned smart constructor. Plain `String` is
  correct only at the pre-parse wire boundary (`SExpr.SAtom`).
- Byte-exactness is a contract, not a nicety: goldens and cross-driver
  differentials compare bytes, so regenerate them deliberately, never
  casually.
- Module size is a guideline (a hint that a seam may have appeared), not a
  gate; see
  [docs/evaluation.md#mutation-generation-and-module-ownership](docs/evaluation.md#mutation-generation-and-module-ownership).
- Prefer boring code. Correctness first, then maintainability six months out.

## Mechanization

As soon as a definition freezes and is corpus-independent, port it to the
Lean development in `lean/` and prove its metatheory — do not batch provable
results for later. Every theorem must be covered by `lean/AxCheck.lean`, stay
`sorry`-free, and use only the standard axiom trio (`propext`,
`Classical.choice`, `Quot.sound`); `make lean-gate` audits all of this.
Haskell property tests are conformance evidence, never a substitute for the
theorems.

## Research record maintenance

Research-record rules live here rather than in the language design docs. The
session files are authoritative; their index is a checked projection, not a
second source of truth. Historical records remain append-only when current
design documentation moves.

### Session records and their index

Each `ara/trace/sessions/<id>.yaml` file is a YAML mapping with unique keys.
`session.id` must equal the filename stem. New records require `id`, `date`,
`turn_count` and `summary` under `session`. The legacy shape uses `id`,
`timestamp`, `summary` and optional `ended`; its date is the first ten timestamp
characters and its index-only turn count cannot be checked against the file.
A record with `date` but no `turn_count` is invalid.

Across turns, the reader accepts plain blocks, top-level suffixed continuations
such as `events_logged_turn2`, and copies nested under `turn_3`, `turn_4`, etc.
It reads plain blocks, then suffixed blocks, then nested copies, in file order
within each group. The index projects them as follows:

| Index field | Source |
| --- | --- |
| `date` | `session.date`, or the day of `session.timestamp` |
| `turn_count` | `session.turn_count`; unchecked for the legacy shape |
| `events_count` | Total entries in every `events_logged` block |
| `claims_touched` | Set of IDs in every `claims_touched` block |
| `open_threads` | Length of the last `open_threads` block, or zero if absent |

A `claims_touched` entry is an ID string or a mapping with an `id`; claim and
heuristic IDs belong here, not event IDs. `ai_actions`, `logic_revisions`,
`key_context` and `ai_suggestions_pending` may use the same continuation
convention but are not projected into the index.

The `before` and `after` fields in `logic_revisions` record what a turn read
and wrote, not the current wording. Correct current claims in `ara/logic/`,
observation context in staging, or mark a trace node `CORRECTED`; do not
rewrite a past revision's `after`. A later revision adds a new entry.

### Observation identity and historical lookup

Use `load_observations(repo_root)` from
[`scripts/check_ara_observations.py`](scripts/check_ara_observations.py), not
first-match lookup in the raw observation list. The loader validates the
entire registry before returning an index. Unique original IDs remain valid.
Every duplicated occurrence needs a fresh canonical alias in
`ara/staging/observation_aliases.yaml`; canonical IDs must not collide with
original IDs or other aliases. Reserve both namespaces when allocating IDs.

The registry has `schema_version: 1`, `aliases` and `references`. An alias
contains `canonical_id`, `historical_id`, `timestamp`, exact ordered `bound_to`
and `record_sha256`; optional `prior_ids` are valid only in qualified historical
references. The fingerprint removes exactly `promoted`, `promoted_to`,
`crystallized_via` and `stale`, serializes the remaining parsed mapping with
`json.dumps(identity, ensure_ascii=False, sort_keys=True, separators=(",", ":"), default=str)`,
then hashes the UTF-8 bytes with SHA-256. Every other field is protected.

A reference records normalized repository-relative `path`, one-based `line`,
`line_sha256`, `kind`, `reason` and `bindings`. Its fingerprint covers the exact
UTF-8 line without the terminator. A lookup binding contains `historical_id`,
`canonical_id` and the target `record_sha256`. An `aggregate` reference has no
bindings and cannot select an observation. Unregistered duplicate-ID mentions
in Markdown or YAML under `ara/` fail validation; the observation source and
registry are excluded from that reference scan.

O190 and O191 identify the earlier O176/O177 occurrences at
`2026-09-12T01:38+00:00`; O192 and O193 identify the later pair at
`2026-09-12T05:54+00:00`. The registry also qualifies the earlier pair's
pre-merge O174/O175 references without changing the global meaning of those
IDs. Bare O176/O177 lookup fails. Aliases identify records, not endorsements.
Append new aliases and reference records rather than changing existing
bindings. External readers must adopt this registry or reject ambiguity;
the external `ara check` command is not claimed to support it.

```sh
python3 scripts/check_ara_observations.py --lookup O190
python3 scripts/check_ara_observations.py --lookup O176 \
  --source ara/trace/sessions/2026-09-12_001.yaml --line 107
make ara-observations-test ara-observations ara-session-index ara-source-spans
```

## Bug reports

Open an [issue](https://github.com/ARA-Labs/Lara/issues) with the `.lara`
file (or `.laramap`), the exact `lara` invocation, the verdict you got, and
what you expected. Include the commit you ran it on, and the `replay-id`
block from the verdict if you have one.
