# Issue #38 — Duplicate-report groups (spec §4.3): cross-layer implementation

Status: complete — closed by PR #45 (worktree `worktree-issue-38-duplicate-report-groups`).

## Problem

Spec §4.3 (M0 C16) requires the elaborator to declare **duplicate-report
groups** over leaf ids and the **checker** to enforce agreement within each
group by the frozen `≡` relation:

- members pairwise `≡` → admitted normally;
- otherwise → **quarantine every member** (default): every argument whose support
  term uses a conflicted leaf is dropped from the checked program, so the
  dependent claim loses that support and routes to `gap` (the conflicted leaves
  also leave the checking context `Γ`);
- a policy may **escalate** the outcome to **reject** (class R9), a
  whole-program data-integrity error located at the group declaration.

Before this change no implementation layer carried groups: zero `group` matches
in `AST.hs`, `Wire.hs`, `Unit.lean`, `Policy.lean`; R9 was a spec-table row only.
Both `RejectClass` enums (Haskell `AST.hs`, Lean `Check/Error.lean`) omit R9.

## Key architectural findings (reconnaissance)

1. **The group check is a Driver-boundary check, not a `checkUnit` stage.**
   In both drivers the leaf→`Γ` map is built once at the boundary
   (`Lara.Driver.buildGamma` / `Lara/Driver.lean:buildGamma`) and passed to
   `checkUnit`. Replay preflight already rejects **R13 before `checkUnit` runs**
   from that same boundary. Groups follow the R13 precedent exactly: the group
   consistency decision is computed at the Driver boundary from the Unit, and it
   either (a) produces a quarantine-aware `Γ` or (b) rejects with R9 — leaving
   `checkUnit`'s six stages untouched. This keeps the executable core symbolic
   and makes the feature differential (both drivers run their Driver) and
   mechanizable.

2. **`≡` is a transitive equivalence** (`p ≡ q iff nf p = nf q`,
   `Lara.Prop`/`Lara/Prop.lean`), so *pairwise-`≡`* over a group ⟺ *every member
   `≡` the first member*. The check is therefore `all (≡ head) tail`, decidable
   and linear.

3. **The two `Unit`s differ but the wire is shared.** Haskell `Unit` bundles
   `unitLeaves :: [(LeafId, Prop)]` (that list *is* `Γ`); Lean `Unit` has no
   leaves — they are a separate wire `leaves` section decoded into
   `Γ : LeafId → Option Atom`. The group construct is therefore a **new shared
   wire section** both drivers decode, feeding each driver's boundary check.

## Design decisions

### Surface syntax (program `.lara`)

A new top-level declaration, named for a located R9 diagnostic:

```
group <ident> = [ <leafId> { , <leafId> } ]
```

Group conflict escalation is a **policy** decision (whole-artifact), declared in
`.policy.lara`:

```
duplicate-reports = quarantine        -- default; may be omitted
duplicate-reports = reject            -- escalate any conflict to R9
```

`quarantine`/`reject` are a closed vocabulary (`GroupConflictMode`), one
`toString`/`parse` table, per the symbolic-core discipline.

### Carrier

- New closed types in `Lara.AST`:
  - `newtype GroupId = GroupId String`
  - `data DupGroup = DupGroup { dgId :: GroupId, dgMembers :: [LeafId] }`
  - `data GroupConflictMode = QuarantineOnConflict | RejectOnConflict`
- New `Decl` constructor `DeclGroup DupGroup`.
- New `Policy` field for the escalation mode.
- **`Unit` gains two fields**: `unitGroups :: [DupGroup]` and
  `unitGroupMode :: GroupConflictMode`. The mode is baked into the Unit at
  elaboration (the checker never sees the policy record), mirroring how rules /
  contraries are compiled in. Default `QuarantineOnConflict`.
- Lean: a `groups` wire section decoded into `List DupGroup` + a mode, added to
  the Driver's `Decoded`; feeds `buildGamma`.

### Wire section (shared, byte-identical)

Emitted **only when `unitGroups` is non-empty**, so every existing fixture
round-trips unchanged:

```
(groups <quarantine|reject> (group <gid> (<leafId> ...)) ...)
```

Well-formedness at decode (mirrors `checkArgInvariants`): every member is a
declared leaf, groups have ≥2 members, no duplicate members, unique group ids;
violations are R14 codec/wf errors.

### Boundary semantics (both drivers, before `checkUnit`)

Let `conflicted = { l | g ∈ unitGroups, members of g not all-≡, l ∈ members g }`.

- if `unitGroupMode = RejectOnConflict` and any group is inconsistent →
  `Reject (RejectClass R9)`;
- else every argument whose support term uses a conflicted leaf is dropped from
  the checked Unit (its claim loses that support and routes to `gap`), together
  with every attack whose endpoints no longer resolve; the conflicted leaves
  themselves leave `Γ`.

### Rejection class

Add `R9` to both `RejectClass` enums and the wire tag tables
(`(verdict reject R9)`, exactly like R13). Update the "outside the executable
core" comments: R9 is now enforced at the driver boundary; R2/R8/R14 remain out.

## Mechanization (Lean, sorry-free, standard axiom trio)

Frozen definitions ported to `lean/Lara/Groups.lean` and their metatheory proved
now (six theorems):

1. `all_equiv_head_iff` — pairwise-`≡` over a list ⟺ every element `≡` the head
   (the load-bearing use of `≡`'s symmetry and transitivity).
2. `consistentB_iff` — the linear `consistentB` decides the quadratic spec-level
   `Consistent`.
3. `mem_quarantined_iff` — the quarantine set is exactly the members of the
   inconsistent groups.
4. `quarantined_arg_excluded` — an argument using a quarantined leaf does not
   survive `quarantineArgs`, so its dependent claim can never be `justified`.
5. `quarantined_leaf_absent` — a quarantined leaf has no entry in the
   post-quarantine context.
6. `conflictReject_iff` — the R9 reject fires exactly when the policy escalates
   and some declared group is `≢`.

Every theorem has an `import` + `#print axioms` line in `AxCheck.lean`.

## Differential fixtures

Three new corpus fixtures via `scripts/gen-corpus.hs`, pinned in
`DifferentialSpec`:

- `group-consistent-accept` — two `≡` leaves grouped, both used → justified.
- `group-conflict-quarantine` — two `≢` leaves grouped, default mode → the
  dependent claim is `gap` (accept verdict).
- `reject-r9` — same conflict, `duplicate-reports = reject` → `(verdict reject R9)`.

Plus an R9 `Negative` in `Lara.Negatives`.

## Layer checklist

- [x] AST + Unit carrier (Haskell)
- [x] Surface parser + printer + grammar doc
- [x] Wire codec (encode/decode/wf) + R9 tag
- [x] Driver boundary check (quarantine / R9)
- [x] Elaborator emits groups + bakes mode
- [x] Lean: carrier + wire decode + boundary check + R9
- [x] Lean: metatheory + AxCheck (6 theorems, standard axiom trio)
- [x] Fixtures + negatives + tests; `cabal test`, `differential.sh` (41/41),
      `lake build`, `check-axioms.sh` all green

## Status: complete

All layers land, all gates green. `runCheck` precedence is R13 (replay) → R9
(escalated group conflict) → `checkUnit`; quarantine drops the affected
arguments so the dependent claim is `gap` (never a rejection). The three
differential fixtures pass both drivers byte-exact.
