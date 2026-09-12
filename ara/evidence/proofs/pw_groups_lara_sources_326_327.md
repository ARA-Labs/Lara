# PW outer runtime: consistent groups and `.lara` world sources (#326, #327)

The user asked for #326 and #327 to be addressed together, directly, with a
PR. The work is on branch `feat/pw-groups-and-lara-sources`, built on main
`28cae19` (#328 merged). The decision record is `docs/theory-pw-outer-runtime.md`
§1–§5, revised in place.

## What was decided

- **#326 — consistent groups are inert.** A world whose duplicate-report
  groups all agree is accepted and checked exactly as declared. A world with a
  group whose members are not pairwise `≡` is refused as
  `(world-groups W G)`, naming the first such group in declaration order,
  whatever the policy's conflict mode: under `quarantine` the local status
  would be conditional (`evidence-blocked`), under `reject` the local checker
  would refuse the unit (R9). The fifth-outer-observation option was not taken
  (it changes `Sorted.cmpVal` and every theorem over it). Consistent groups do
  not enter the context environment.
- **#327 — `(lara PATH)` world sources and `lara pw-input`.** A world may be a
  `.lara` program with its co-located policy; `lara pw` elaborates it through
  the `.lara` door's own steps (`Lara.Source.Load`, `prepareSource`) and uses
  the envelope it binds, read back through the same `decodeCheckInput` as an
  inline world. Whatever stops the program before an envelope exists —
  unreadable, unparsable, source invalid, admission stop, policy quarantine —
  is `world-input`. The Lean reference has no surface parser and reports a
  `lara` world as `world-input`. `lara pw-input <run.sexp>` prints the same
  document with every source inline; the gate compares both runtimes on it.
  `pw-run 1` keeps version `1`: the change adds a `SOURCE` production and moves
  nothing an old reader accepts.

## What is proved (Lean, all pinned in AxCheck, standard trio only)

- `Lara.Groups.quarantined_eq_nil`: with every group `consistentB`, the §4.3
  quarantine set is `[]`.
- `Lara.Groups.quarantineLeaves_nil`, `quarantineArgs_nil` (via `usesLeaf_nil`,
  `usesLeafList_nil`, `usesLeafDisch_nil`, `keepArg_nil`): an empty quarantine
  set makes both quarantine operations the identity.
- `Lara.Groups.anyConflict_eq_false_iff`.
- `Lara.PW.Run.addWorld_decoded`, `addWorld_quarantine_empty`,
  `addWorld_checks_declared`: a world `addWorld` accepts was decoded, none of
  its groups conflicts, its quarantine set is empty, and the leaf table and
  argument list it hands `checkUnit` are the declared ones — the unit the local
  driver checks.
- `decodeSource_encode` / `decodeRun_encode` re-prove over the extended
  `WorldSource` unchanged (`cases s <;> simp`).

Verification output (this session):

```
AxCheck coverage passed (3127 declarations).
'Lara.Groups.quarantined_eq_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Groups.quarantineArgs_nil' depends on axioms: [propext, Quot.sound]
'Lara.PW.Run.addWorld_checks_declared' depends on axioms: [propext, Classical.choice, Quot.sound]
Axiom audit passed.
```

## Conformance experiment

```
PW outer runtime conformance passed: 7 fixtures, 99 cases, 112 runs; 1 .lara source fixtures, 17 source cases, 21 runs.
```

- New fixture `fixtures/pw/run/groups.sexp` (the T7 witness with l1 and l3
  grouped as two reports of p, w0 supported from the grouped report l3 under
  `quarantine`, w1 under `reject`). Both drivers print `inline.sexp`'s golden
  bytes.
- New group cases: conflicting group under both modes → `world-groups w0 g1`;
  consistent group under both modes → `inline` golden; three groups with the
  consistent one first → `g1` named; undeclared member → `world-input`
  (R14 at decoding). Order cases updated for the two-atom fault.
- New family: `fixtures/pw/source/lara.sexp` with `worlds/{w0,w1}.lara` and
  `pw-lara.policy.lara`. `lara pw` prints the golden; `pw-run` on the same file
  prints `(pw-error 1 world (world-input w0 …))` exit 1; `lara pw-input`
  derives an all-inline document on which both drivers print the golden. 17
  cases: missing/unparsable program, program text that is not UTF-8, missing
  policy, duplicate leaf (source invalid), admission stop, policy quarantine,
  first unreadable world named, conflicting group through elaboration under
  both modes, consistent group under `reject`, mixed `.lara` + inline worlds in
  one context, checker R1 and `missing-conflict` on elaborated worlds,
  non-ASCII program path and program text under the default, `LC_ALL=C` and
  ISO-8859-1 locales (this exposed the need for `setLocaleEncoding` on the PW
  doors: `.lara` text is read through the locale), and an undecodable run file
  from both doors. Each pre-envelope refusal is pinned to the text of the step
  that stopped, not only to the shared `world-input` constructor, so a
  policy-parse failure cannot pass a source-invalid case vacuously.
- Review follow-up (#332): the locale encoding the PW doors set is __strict__
  UTF-8, not `UTF-8//ROUNDTRIP`. With the permissive variant a `.lara` file
  carrying a non-UTF-8 byte decoded to surrogate escapes and elaborated, so
  `lara pw` accepted a world `lara check` refuses to read at all — and because
  both PW doors agreed, the cross-driver comparison could not see it. The gate
  now has a direct case for it. The converse asymmetry (`lara check` still
  reads `.lara` through the locale) is recorded in
  `docs/theory-pw-outer-runtime.md` §2 and tracked by #334.
- Every `fixtures/pw/run` fixture is also derived with `pw-input` and rerun on
  both drivers to its golden.

## Other verification

- `cabal test lara-test`: all 37 property groups pass, including three new
  PWSpec properties (derivation preserves every fixture's run; consistent
  groups inert / conflicting refused in-process; `lara` in the codec round
  trip and malformed matrix).
- `scripts/differential.sh`: pass (positive anchors and negative
  `pass=66 fail=0`). This exposed a pre-existing gap: `fixtures/pw/**/*.sexp`
  (from #314 and #322) were discovered by the anchor glob but absent from
  `fixtures/ANCHORS.tsv`, so the wire differential failed on main. Fixed by
  excluding `fixtures/pw/` from anchor discovery in `scripts/differential.sh`
  and `scripts/gen-anchor-manifest.sh`; PW fixtures have their own harness.
- `scripts/check-lean-citations.py`: PASS (420 citations).

## Authoring corrections during the gate build (not research dead ends)

- An undeclared leaf in a `.lara` world elaborates and is the checker's R1,
  not a source-invalid failure; the case was renamed accordingly and a
  duplicate leaf id used for source invalidity.
- Making the grouped report l3 conflict broke the argument resting on it
  (conclusion `≢` claim formal → source invalid); the conflicting report was
  moved to the unused leaf l1.
- Changing w1's leaf table for a checker-rejection case tripped the
  context-environment check first; the undermine was removed instead.
