# Freeze v8 regeneration diffs (located-gap follow-ups, issues #15 and #16)

The diffs taken across the v7 → v8 regeneration. v8 keeps `lara-core@0.3`:
the core was amended in place before it shipped (D12 in
`docs/located-gap-decision.md`), and the corpus was re-lowered to declare its
incomplete arguments (issue #15). Both changes move measured bytes, so the
diffs are recorded here, in the same shape as
`lara-core-0.3-regeneration-diffs.md`.

## 1. Hole rows carry obligation sites (issue #16, D12)

Every verdict hole row changes from `(obligations ID+)` to
`(obligations (obligation ID POS+)+)`. No status, label, edge or accept/reject
outcome moves. The mutant manifest stores no hole-row bytes, so this change
alone left all 595 mutants byte-identical (`gen-mutants.hs --check`).

## 2. Corpus re-lowering (issue #15)

All 48 `gap` units now declare the incomplete argument they used to omit, with
`open <question>` for each unanswered question. Each is accepted with exactly
one located hole and its claim stays `gap`:

```
corpus-units/MANIFEST.tsv expected_status: 9 justified / 48 gap / 3 defeated  (unchanged)
located_holes (new column):               48 units carry 1 hole, 12 carry none
```

Two units also declare their dead-end undercut against the hole
(`rebench-nanogpt_chat_rl/C04` N604, `rebench-fix_embedding/C12` N603/N759):
a leaf `u1`, a challenge `d1`, and `undercut d1 a1.rule`. The undercut types
and is inert (no complete argument contains the attacked occurrence, D4/D6),
so `d1` is a new `in` node with no edge and the claims stay `gap`. Every other
corpus unit's labels and edges are unchanged.

## 3. Mutants: 595 → 600

The corpus units are mutation bases, so re-lowering adds sites:

| Expected | v7 | v8 |
| --- | ---: | ---: |
| `reject-R10` | 11 | 13 |
| `reject-R4` | 34 | 37 |

All other expected classes keep their counts; the 18 `accept-located-hole`
mutants are unchanged. The `hole-obligation` operator now seeds only complete
arguments (`Lara.Mutate.Sites.holeObligationSites`): on a base argument that
is already a hole, the seeded question would join pre-existing obligations and
the mutant would not be a single seeded defect. File names shift where an
operator's per-family index moved.

## 4. Measurement classes

A corpus unit with `located_holes > 0` is now measured as
`accept-located-hole` (`Lara.Measure.parseCorpusManifest`), the class the full
system reports for it; its `gap` status stays pinned by
`test/CorpusUnitsSpec.hs`. So `accept-gap` drops 57 → 9 (the hole-free gap
mutants) and `accept-located-hole` rises 18 → 66.

## 5. Claim support and the binding audit

| Field | v7 | v8 |
| --- | ---: | ---: |
| all leaves | 169 | 171 (observed 63 → 65) |
| typed attacks | 3 | 5 |
| dead-end-sourced attacks | 2 | 4 |
| load-bearing leaves | 38 | 38 |
| audit subjects | 1 strict + 3 attacks | 1 strict + 3 attacks |

The two new attacks and their challenge leaves bear on no status, so they are
not binding-audit subjects: `Lara.ClaimSupport` audits only attacks whose
source is a complete node and whose attacked occurrence lies in a complete
node, and does not count an `in` challenge whose every attack is inert as
load-bearing. The committed worklist is byte-identical.
