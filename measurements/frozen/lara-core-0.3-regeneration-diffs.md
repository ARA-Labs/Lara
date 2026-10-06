# `lara-core@0.3` regeneration diffs (located gap, `docs/located-gap-decision.md`)

The same two diffs as the `lara-core@0.2` pass (`lara-core-0.2-regeneration-diffs.md`),
taken across the located-gap regeneration. Unlike that pass, the first diff is
**not** empty: the cutover changes which units are accepted, and the diff is the
measurement of exactly how far that reaches. Both are committed here so a later
regeneration that moves either one is visible in review.

Commands, run against the pre-regeneration tree (the parent of the regeneration
commit) and the regenerated tree:

```
# 1. the expected-column diff over all 595 mutants
git show <parent>:fixtures/mutants/MANIFEST.tsv | cut -f1,5 | sort > old.tsv
cut -f1,5 fixtures/mutants/MANIFEST.tsv | sort                    > new.tsv
diff old.tsv new.tsv
# every other manifest column (file, base, family, operator, both
# diagnostics, expected-location)
diff <(git show <parent>:fixtures/mutants/MANIFEST.tsv | cut -f1-4,6-8) \
     <(cut -f1-4,6-8 fixtures/mutants/MANIFEST.tsv)

# 2. the verdict + status diff over all 60 corpus expected.json files
#    (the same extraction as the lara-core@0.2 record)
```

## 1. `MANIFEST.tsv` expected-column diff, 595 mutants

Exactly the 18 `hole-obligation` rows move, each
`reject-IncompleteArgument` → `accept-located-hole`:

```
A  B  E1  E3  E4  E5
bam.C05  fre.C01  fre.C04  pinn.C01  rice.C01
rebench-restricted_mlm.C14  rebench-rust_codecontests.C02  rebench-triton_cumsum.C09
sample-specific-masks.C05  sample-specific-masks.C06
self-composing-policies.C01  test-time-model-adaptation.C04
```

Every other column of every row, the seeded `expected-location` included, is
byte-identical. The mutation itself did not change: each mutant still swaps one
mandatory discharge for a declared open question. What changed is the
outcome the core assigns to it (D3), and `gen-mutants.hs` now verifies the
stronger property the new outcome allows — exactly one hole row, at the seeded
argument's declaration index, named by that argument's id, with exactly one
obligation. All 595 mutants are re-verified; none of the 18 is masked by a
later defect in the same unit.

The seeded location is now the hole's **declared** index (the space verdict
hole rows use), where the retired rejection published the checked index. On
every committed base the two coincide, which is why the column did not move;
`MutationSpec.prop_siteDirectionSkewed` pins the declared direction on skewed
bases where they differ.

The other 577 rows keep their expectation, and so does every mutant file except
for its replay identity: the codec `codec-core-version` operator now presents
the just-retired `lara-core@0.2` instead of `lara-core@0.1`, with the same pinned
diagnostic.

## 2. Corpus verdict + status diff, all 60 units

```
(empty)
```

No frozen corpus unit declares an incomplete argument (they were lowered under
`lara-core@0.2`, which rejected one; re-lowering them is follow-up work), so the
version bump moves only their replay identity.

## Worked examples

Every worked-example anchor changes only its replay identity, except the two
the plan names, whose sources now declare the incomplete argument they
previously had to omit:

- `examples/running-example/run1` declares `a1` with `open external_validity`;
  its verdict gains `(holes (arg 1 a1 (obligations external_validity) (attacks)))`
  and its statuses are unchanged (`c1` gap, `c2` justified).
- `examples/rebuttal-replay/round0` and `round1` declare `a_kurt` with
  `open variance_reported`; each verdict gains
  `(holes (arg 2 a_kurt (obligations variance_reported) (attacks)))`, the labels,
  edges and statuses are unchanged, and `round2` (which completes `a_kurt`) is
  unchanged apart from its replay identity.

## Conservative reporting (D7)

No committed input quarantines a typed hole, so the D7 change to the
`evidence-blocked` reference framework moves no committed status. It is pinned
by the new corpus anchors `fixtures/corpus/group-quarantine-hole-attacker.sexp`
(a quarantined hole attacker blocks nothing) and
`fixtures/corpus/group-quarantine-hole-lost-edge.sexp` (an attack into a
quarantined hole still seeds a retained complete argument sharing the attacked
occurrence), both byte-compared across the two drivers.
