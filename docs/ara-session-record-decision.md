# Decision: the ARA session record and what its index row projects

_Records the schema of the per-session trace files under
`ara/trace/sessions/` and the projection rule that fixes what each
`session_index.yaml` row must say about its file (issues #333, #337, #338;
gate `scripts/check_ara_session_index.py`, `make ara-session-index`). Settled
2026-09-12. The session file is authoritative; the index row is derived from
it and is checked, never the other way round._

## Why a record was needed

The index is the only enumeration of the trace, so a row that disagrees with
its file misreports the session to every reader that stops at the index. #333
found exactly that (a duplicate row whose counts were stale), #337 gated
totality and uniqueness, and #338 asked for the counts to be compared too. The
comparison was not decidable until the file shape was fixed: the 79 files
written between July and September 2026 came in six spellings, and a naive
count of `events_logged` disagreed with 16 rows. This record states which
spellings are accepted and how each counted field is computed, so the gate has
a definition to enforce rather than a guess.

## The session file

`ara/trace/sessions/<id>.yaml`, one per session, where `<id>` is
`YYYY-MM-DD_<n>` or `YYYY-MM-DD_<tag>`. A file is a YAML mapping and **must
not repeat a top-level key** — a permissive reader keeps only the last
occurrence, which is how one file silently lost a turn's `ai_actions`. The
gate reads every file under a loader that refuses duplicate keys.

### `session:` — two accepted shapes

| shape | required fields | when |
| --- | --- | --- |
| **current** | `id`, `date`, `turn_count`, `summary` | every file from 2026-07-26 on, and any new file |
| **legacy** | `id`, `timestamp`, `summary` (`ended` optional) | 17 files dated 2026-07-22 … 2026-07-25 |

`session.id` must equal the file stem. In the legacy shape the day is the
first ten characters of `timestamp`, and the row's `turn_count` is the only
record of that number — it is accepted unchecked. A file that carries `date`
but no `turn_count` is an error: the current shape is complete or it is wrong.
The legacy files were **not** rewritten; the alternative (copying the row's
`turn_count` into each file) adds no information and edits history for the
sake of one fewer branch in the gate.

### Blocks that accumulate across turns

A session that spans several turns appends to the file rather than editing
the blocks already written. Two spellings of that appendix exist and both are
read:

- **suffixed continuation blocks** at top level — `events_logged_turn2`,
  `claims_touched_turns3_10`, `open_threads_turns11_18` — any key of the form
  `<block>_<suffix>`;
- **nested turn mappings** — `turn_3:`, `turn_4:` … — each holding its own
  `events_logged` / `claims_touched` / `open_threads` lists.

The blocks the gate reads are, in file order, the plain key, then its
suffixed continuations, then the nested copies. `ai_actions`,
`logic_revisions`, `key_context` and `ai_suggestions_pending` follow the same
convention but are not projected into the index.

### `claims_touched` entries

An entry is a mapping with an `id` (typically `{id, action, turn}` or
`{id, action, provenance}`) or a bare id string (`C08`). Three files use the
bare form; it is accepted as "touched, action unrecorded" rather than
rewritten with an invented action. The ids are claim (`C…`) and heuristic
(`H…`) identifiers from `ara/logic/`; events (`N…`, `O…`) do not belong here.

## The projection: what a row must say

| row field | computed from the file |
| --- | --- |
| `date` | `session.date`, or the day of `session.timestamp` |
| `turn_count` | `session.turn_count`; unchecked for the legacy shape |
| `events_count` | total entries across **every** `events_logged` block |
| `claims_touched` | the **set** of ids across every `claims_touched` block (order-insensitive) |
| `open_threads` | the length of the **last** `open_threads` block |

`events_count` and `claims_touched` accumulate because a later turn adds to
what earlier turns logged. `open_threads` does not: each turn's block is a
snapshot of what was open when it was written, so the last block is the state
at session end — this is the reading under which every multi-turn row that
was already correct stays correct. A file with no `open_threads` block has
zero open threads on record.

## How the 16 disagreeing rows were resolved

The file wins wherever it is well-formed. Twelve rows had stale counts
(turns appended without the row being touched, or open-thread lists that had
grown) and were corrected to the file; that includes
`2026-09-05_001`, whose row claimed four open threads the file never listed.
Four files were themselves malformed and were repaired to the shape their row
already summarised:

- `2026-07-24_003` — six `ai_actions` entries had been written under
  `events_logged`; moved under their own key.
- `2026-09-05_001` — truncated after its events; `claims_touched` (C50
  revised, as the row and summary state) and an empty `open_threads` added.
- `2026-09-09_issue307` — turn 3's events had been appended under
  `claims_touched`, and its `ai_actions` repeated the top-level key; the events
  moved under `events_logged`, H18 kept as a claim entry, the two `ai_actions`
  lists merged.
- `2026-09-10_001` — recorded C55 as the claim created; the session created
  C56 (the multi-artifact composition claim), and C55 belongs to
  `2026-09-09_issue307`.

No corpus, fixture, or wire content was touched; no freeze tag moves.

## Rejected alternatives

- **Keep the gate stdlib-only.** The files use block scalars, quoted strings
  with escapes and nested mappings; a line grammar would have to re-derive
  YAML. PyYAML is the gate's one dependency; CI supplies it with
  `uv run --with pyyaml`, and the row enumeration still uses the #337 line
  grammar so a reshaped index fails loudly rather than being half-read.
- **Sum the `open_threads` blocks.** Gives 21 for `2026-07-22_001` where the
  row (correctly) says 5; the blocks are snapshots, not increments.
- **Filter `claims_touched` by id prefix.** Would have hidden the misfiled
  events in `2026-09-09_issue307` instead of surfacing them.
