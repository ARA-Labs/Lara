# Issue #18 Attack Completeness and Result 7 Consistency Implementation Plan

> **Status: complete — closed by PR #26.**

> **For agentic workers:** REQUIRED SUB-SKILL: Use `executing-plans` to
> implement this plan task-by-task. Keep checkbox state current as each focused
> test, proof, and gate lands.

**Goal:** Define the accepted-program boundary of the new PL so one
proof-bearing `CheckedUnit` establishes rule-table coherence, Path-B policy
well-formedness, typed and attack-complete arguments, exact retained-node
metadata, and the premises needed to machine-check spec §9 result 7: contrary
computed claims cannot both be `justified`.

**Architecture:** Preserve `Attack.HasAttack`, `Compile.Edge`,
`Compile.CheckedProgram`, `Policy.WellFormed`, and grounded semantics as the
existing language relations and generic compile boundary. Add `Lara.Unit` for
neutral unit and accepted-unit data, `Lara.Check.Program.checkProgramDetailed`
for the new proof-bearing program acceptance result, `Lara.Check.Unit.checkUnit`
as the canonical executable PL acceptance procedure, and `Lara.Consistency` as
a downstream theorem consumer. A shared base checker retains the existing
checked-argument cache: legacy `checkProgram` projects the old
`CheckedProgram`, while `checkProgramDetailed` continues through the
completeness scan and returns `ProgramAcceptance`. `checkUnit` derives the
policy rule lookup, rejects duplicate rule identifiers, proves Path B, consumes
that detailed result, and returns `CheckedUnit`.

**Tech Stack:** Lean 4.32 core library, the existing proof-bearing `Lara.Check`
pipeline, `Compile.edgeB`, `Lara.Policy`, `Lara.Grounded`, Lake/AxCheck, and the
unchanged Cabal/QuickCheck regression-compatibility suite.

**Tracker:** GitHub issue #18, the final child of M2 tracker #15. Dependencies
#16 and #17 are closed on `main` at `65491b0`.

## Definition of Done

- A raw `Unit` has one finite policy, argument list, and attack list.
- `checkUnit` is the canonical executable acceptance boundary for Path B.
- Rule identifiers are unique before a policy lookup is accepted.
- The exact rejection order is:
  duplicate rule identifiers → R12 policy violation → duplicate arguments →
  support checking → attack checking → missing conflict.
- `Policy.firstViolation?` is one proof-bearing scan with exact `none`
  adequacy and sound returned violations.
- `Compile.CheckedProgram` and legacy `checkProgram` retain their existing
  generic attack-soundness meaning and behavior.
- `checkProgramDetailed` returns one named `ProgramAcceptance` record carrying
  attack completeness for attackable contrary targets and retained nodes.
- `CheckedUnit.nodes` is derived from the existing checker cache, retains each
  exact conclusion, and is aligned with `program.args`.
- `claimSupportFor` computes exact complete-support indices from those nodes in
  stable declaration order; `completeClaimFor` supplies the complete-only
  `Grounded.Claim` consumed by result 7.
- Subargument closure counts as conflict coverage. No redundant root attack is
  required when a declared attack already compiles onto a wrapper.
- Grounded extensions are conflict-free for arbitrary finite AFs.
- Contrary arguments cannot both be grounded-`in`, including self-conflict.
- Contrary computed claims cannot both be `justified`.
- Every atomic obligation in the deduplicated traceability matrix and all six
  language-author flows are covered.
- Every new public adequacy and integration theorem appears in
  `lean/AxCheck.lean`, with no `sorryAx` and only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Lean build and standalone axiom audit pass; the unchanged Haskell suite
  passes as a regression-compatibility gate only.
- The spec, status files, M1 checklist, Lean README, and ARA claim C09 are
  synchronized without claiming Path A or a production Haskell checker.

## Language and Trust Boundaries

- This work designs the accepted-program abstraction of the new PL. A theorem
  that takes independently supplied `Policy.WellFormed`,
  `CheckedProgram`, or cache-alignment hypotheses is a useful helper, but is
  not the public language guarantee.
- `Lara.Check.Unit.checkUnit` is the canonical executable constructor for
  `Lara.Unit.CheckedUnit`. The public proof-bearing structure may also be
  constructed manually only by supplying every invariant.
- Preserve the frozen meanings of `Attack.HasAttack`, `Compile.Edge`,
  `Policy.WellFormed`, and grounded status. New Boolean procedures decide
  those relations or accepted-unit invariants; they do not replace them.
- Completeness is directional compiled-edge coverage. For each ordered
  contrary pair of complete arguments, an attack is required only when the
  target is a leaf or a defeasible-root instance.
- Completeness is intentionally over unlabelled `Compile.Edge`, not the reason
  for an attack. Any typed declared attack that compiles from the source onto
  the target supplies the edge result 7 needs, even if a different attacked
  occurrence caused it.
- A strict-root contrary is owned by Path B/R12. It must be rejected before
  program checking and must never be mislabeled as a missing conflict.
- Include self-pairs in the ordered pair scan. A self-contrary argument needs
  a typed self-edge or the unit is rejected at `(i, i)`.
- A missing conflict is a program-boundary outcome, not a new frozen R1–R14
  class.
- Keep symbolic diagnostics: indices, identifiers, atoms, and closed AST
  values only. Rendering belongs outside the checker.
- Do not add another edge algorithm. `Compile.edgeB` and the completeness scan
  share `coveredB`.
- Do not rerun support inference during completeness or claim aggregation.
  Reuse the checker-produced exact conclusions.
- Use Lean core `List.findSome?`, `List.zipIdx`, and their adequacy lemmas.
  Do not add custom pair-recursion machinery or derive `DecidableEq` for a
  recursive wire type nested through `List`.
- Do not materialize an `n × n` pair list or edge matrix in the reference
  checker.

## Module Boundaries

```text
Lara.Attack ---> Lara.Compile ---> Lara.Unit ---> Lara.Check.Program
                       ^                |                  |
                       |                |                  v
Lara.Policy -----------+----------------+--------> Lara.Check.Unit
                                        |
Lara.Grounded --------------------------+--------> Lara.Consistency
```

- `Lara.Compile` and `Lara.Policy` remain independent.
- `Lara.Unit` owns neutral raw/accepted-unit data and the checked-node record.
- `Lara.Check.Unit` owns duplicate-rule, R12, and program-check orchestration.
- `Lara.Consistency` imports the accepted-unit surface and grounded semantics;
  no upstream module imports it.

## Accepted-Unit Flow

```text
raw Unit(policy, args, attacks)
            |
            v
firstDuplicateRuleId? -----------------> UnitError.duplicateRule
            |
            v
Policy.firstViolation? ----------------> UnitError.policyViolation (R12)
            |
            v
Policy.ruleLookup + shared base program check
            |
            +-- duplicate argument ----> UnitError.program
            +-- support rejection -----> UnitError.program
            +-- attack rejection ------> UnitError.program
            |
            +--> legacy checkProgram projects CheckedProgram
            |
            v
checkProgramDetailed completeness scan
            +-- missing conflict ------> UnitError.program
            |
            v
ProgramAcceptance
  program : unchanged CheckedProgram
  attack_complete
  retained nodes + alignment
            |
            v
CheckedUnit
  policy + policy_wf + unique rule ids
  program : CheckedProgram
  nodes   : List CheckedNode
  nodes.map term = program.args
            |
            +--> claimSupportFor p : List Nat
            +--> completeClaimFor p : Grounded.Claim
            |
            `--> Consistency result 7
```

## Fixed Diagnostic Order

| Priority | Check | Typed error |
|---:|---|---|
| 1 | duplicate rule identifiers | `UnitError.duplicateRule` |
| 2 | first Path-B violation | `UnitError.policyViolation` |
| 3 | duplicate arguments | `UnitError.program (.duplicateArgument ...)` |
| 4 | support inference/completeness | wrapped `ProgramError` |
| 5 | declared attack typing/endpoints | wrapped `ProgramError` |
| 6 | first uncovered conflict | `UnitError.program (.missingConflict ...)` |

This order is part of the language-facing checker contract and is pinned by
closed fixtures.

---

### Task 1: Factor Exact Conflict Coverage and Indexed Node Metadata

**Files:**

- Modify: `lean/Lara/Compile.lean`
- Modify: `lean/Lara/Check/Program.lean`
- Create: `lean/Lara/Examples/AttackCompleteness.lean`

**Produces:**

- `ConflictAttackable` / `conflictAttackableB`
- `Covered` / `coveredB`
- a behavior-preserving `Edge` / `edgeB` refactor
- exact checked-node metadata derived from the current cache

- [x] **Step 1: Add failing coverage fixtures**

Cover:

1. leaf attackability;
2. defeasible-root attackability;
3. strict-root non-attackability;
4. unknown-rule non-attackability;
5. direct coverage;
6. coverage through subargument closure;
7. wrong-target coverage returning `false`;
8. no-attacks coverage returning `false`;
9. a typed attack with the same source and compiled target but a different
   attack reason returning `true`.

The wrapper case is load-bearing: an undermine on a contained leaf already
compiles onto its wrapper and must not require a redundant root rebut.
The ninth case freezes edge completeness explicitly: the compiled AF has no
attack-reason labels, and result 7 depends only on the resulting edge.

- [x] **Step 2: Define the relational and Boolean attackability boundary**

```lean
def ConflictAttackable
    (Pi : RuleId → Option Rule) : SupportTerm → Prop
  | .leaf _ => True
  | .inst rn _ _ _ _ _ =>
      ∃ r, Pi rn = some r ∧ r.mode = .defeasible

def conflictAttackableB
    (Pi : RuleId → Option Rule) : SupportTerm → Bool

theorem conflictAttackableB_iff
    (Pi : RuleId → Option Rule) (target : SupportTerm) :
    conflictAttackableB Pi target = true ↔
      ConflictAttackable Pi target
```

Call the property `ConflictAttackable`, not `Rebuttable`: leaves are
undermined.

- [x] **Step 3: Factor declared-attack coverage**

```lean
def Covered (atts : List Attack.Attack)
    (source target : SupportTerm) : Prop :=
  ∃ k ∈ atts, k.source = source ∧
    ∃ t, AttackOcc k t ∧ Contains target t

def coveredB (atts : List Attack.Attack)
    (source target : SupportTerm) : Bool :=
  atts.any (fun k =>
    decide (k.source = source) && attackClosureB k target)

theorem coveredB_iff {target : SupportTerm}
    (hwf : DisNodup target)
    (atts : List Attack.Attack) (source : SupportTerm) :
    coveredB atts source target = true ↔
      Covered atts source target
```

- [x] **Step 4: Refactor `Edge` and `edgeB` through coverage**

```lean
def Edge (P : CheckedProgram canon Pi Gamma CertOk dp)
    (source target : SupportTerm) : Prop :=
  source ∈ P.args ∧ target ∈ P.args ∧
    Covered P.atts source target

def edgeB (P : CheckedProgram canon Pi Gamma CertOk dp)
    (i j : Nat) : Bool :=
  match P.args[i]?, P.args[j]? with
  | some source, some target => coveredB P.atts source target
  | _, _ => false
```

Repair existing public theorems extensionally. Keep
`edgeB_PEx_eq_edgeBEx` and the full old edge matrix green.

- [x] **Step 5: Name the retained node representation**

Add a `CheckedNode` representation whose data is derived from each existing
checked-argument cache entry:

```lean
structure CheckedNode
    (canon : String → String) (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop) where
  term       : SupportTerm
  conclusion : Atom
  valid      : HasSupport canon Pi Gamma CertOk term conclusion []
```

Do not add a second conclusion list to `CheckedProgram`. The later
`CheckedUnit.nodes` field is the one retained indexed view, derived from the
cache already built by `checkArguments`.

- [x] **Step 6: Run the focused regression**

```bash
cd lean
lake env lean Lara/Compile.lean
lake env lean Lara/Check/Program.lean
lake env lean Lara/Examples/AttackCompleteness.lean
```

- [x] **Step 7: Commit**

```bash
git add lean/Lara/Compile.lean lean/Lara/Check/Program.lean \
  lean/Lara/Examples/AttackCompleteness.lean
git commit -m "refactor(compile): expose exact conflict coverage"
```

---

### Task 2: Add Detailed Program Acceptance Without Changing `checkProgram`

**Files:**

- Modify: `lean/Lara/Compile.lean`
- Modify: `lean/Lara/Check/Program.lean`
- Modify: `lean/Lara/Examples/AttackCompleteness.lean`

**Produces:**

- `Compile.AttackComplete`
- deterministic `firstMissingConflict?`
- `ProgramAcceptance`
- `checkProgramDetailed`

- [x] **Step 1: Define the completeness postcondition**

```lean
def AttackComplete
    (canon : String → String) (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop)
    (dp : Attack.DefeatPolicy)
    (args : List SupportTerm) (atts : List Attack.Attack) : Prop :=
  ∀ source, source ∈ args →
    ∀ target, target ∈ args →
    ∀ sourceConclusion targetConclusion,
      HasSupport canon Pi Gamma CertOk source sourceConclusion [] →
      HasSupport canon Pi Gamma CertOk target targetConclusion [] →
      Attack.ContraryMatch canon dp sourceConclusion targetConclusion →
      ConflictAttackable Pi target →
      Covered atts source target
```

Do not add a field to `CheckedProgram`. Prove the edge consequence with a
separate completeness witness:

```lean
theorem complete_conflict_edge
    (P : CheckedProgram canon Pi Gamma CertOk dp)
    (hcomplete : AttackComplete canon Pi Gamma CertOk dp P.args P.atts)
    ... :
    Edge P source target
```

- [x] **Step 2: Add the located diagnostic**

```lean
structure MissingConflict where
  sourceIndex      : Nat
  targetIndex      : Nat
  sourceConclusion : Atom
  targetConclusion : Atom
deriving DecidableEq

inductive ProgramError where
  ...
  | missingConflict : MissingConflict → ProgramError
```

`ProgramError.rejectClass` returns `none` for this constructor. Do not invent
R15.

- [x] **Step 3: Precompute one immutable indexed cache**

Before scanning pairs, derive an indexed node view from the existing cache.
Each entry stores:

- declaration index;
- checked term;
- exact checked conclusion;
- the proof needed by `coveredB_iff`;
- precomputed `ConflictAttackable` Boolean for target use;
- the exact bucket of typed declared attacks sourced at that node.

Compute exact conclusions, attackability, and source attack buckets once per
node. Prove bucket adequacy:

```lean
k ∈ source.attacks ↔ k ∈ atts ∧ k.source = source.term
```

The pair scan calls `coveredB source.attacks source.term target.term`. Do not
build an edge matrix.

- [x] **Step 4: Implement the source-major pair scan with core list tools**

Implement `firstMissingConflict?` with `List.zipIdx` and nested
`List.findSome?`. For each source entry, restart the target cache:

```text
source-major zipIdx.findSome?
  target-major zipIdx.findSome?
    contraryMatchB?
    precomputed conflictAttackableB?
    coveredB source.attacks?
```

Include self-pairs. Return the first `MissingConflict`. Do not create parallel
Boolean and diagnostic procedures.

- [x] **Step 5: Prove scan exactness**

Prove:

```lean
firstMissingConflict? ... = none ↔
  ∀ source ∈ cache, ∀ target ∈ cache,
    Attack.ContraryMatch canon dp
      source.conclusion target.conclusion →
    Compile.ConflictAttackable Pi target.term →
    Compile.Covered atts source.term target.term
```

Use `List.findSome?_eq_none_iff`, `contraryMatchB_iff`,
`conflictAttackableB_iff`, `coveredB_iff`, cache alignment, and
`hasSupport_unique`.

- [x] **Step 6: Share the old checker pipeline without changing its behavior**

Factor the existing work into a private/internal base result that retains the
cache:

```text
duplicate args → checked args/cache → typed attacks → retained base result
                                                     |
                           +-------------------------+------------------+
                           |                                            |
                           v                                            v
              legacy checkProgram projects             checkProgramDetailed runs
                   CheckedProgram                        missing-conflict scan
```

Legacy `checkProgram` projects `CheckedProgram` immediately after typed attack
checking. Its signature, accepted inputs, errors, `checkProgram_sound`, and
`checkProgram_complete` remain unchanged.

- [x] **Step 7: Return executable retained data from `checkProgramDetailed`**

Define a named result:

```lean
structure ProgramAcceptance ... where
  program              : Compile.CheckedProgram ...
  attack_complete      :
    Compile.AttackComplete ... program.args program.atts
  arguments_eq         : program.args = args
  attacks_eq           : program.atts = atts
  nodes                 : List CheckedNode ...
  nodes_terms           : nodes.map (·.term) = program.args
```

`checkProgramDetailed` continues from the base result, runs
`firstMissingConflict?`, and returns `ProgramAcceptance` directly. A soundness
theorem cannot recover executable nodes after a checker has discarded them, so
do not construct this record through `checkProgram_sound`.

Add:

```lean
checkProgramDetailed_sound
checkProgramDetailed_complete
```

Keep compatibility accessors for existing `checkProgram_sound` callers and
replace brittle `.2.2...` proof projections where touched. Do not rewrite
`CheckedProgram` or copy its existing theorem fields into this record.

- [x] **Step 8: Pin program-checker behavior**

Closed fixtures must cover:

- first missing pair and crossing-pair lexicographic order;
- closure-covered wrapper acceptance;
- nonmatching attack decoy;
- self-conflict missing at `(0, 0)`;
- support and attack errors winning before missing conflict;
- empty and no-contrary programs accepted vacuously;
- retained-node alignment;
- legacy `checkProgram` acceptance and exact errors unchanged;
- `checkProgramDetailed_sound` and `checkProgramDetailed_complete`.

- [x] **Step 9: Add a default-heartbeat stress fixture**

Use a representative closed program that reaches the late no-gap path and
traverses its ordered pairs under default heartbeats. The test must not raise
`maxHeartbeats`. Pair it with the source-bucket adequacy theorem. The fixture is
a regression guard, not proof of asymptotic scaling.

- [x] **Step 10: Build and commit**

```bash
cd lean
lake env lean Lara/Check/Program.lean
lake env lean Lara/Examples/AttackCompleteness.lean
lake build
```

```bash
git add lean/Lara/Compile.lean lean/Lara/Check/Program.lean \
  lean/Lara/Examples/AttackCompleteness.lean
git commit -m "feat(check): reject uncovered contrary conflicts"
```

---

### Task 3: Make Policy Lookup and Path-B Checking Exact

**Files:**

- Modify: `lean/Lara/Policy.lean`
- Create: `lean/Lara/Examples/PolicyAcceptance.lean`

**Produces:**

- unique rule-identifier check
- canonical first-match rule lookup
- exact and sound `firstViolation?`

- [x] **Step 1: Add rule-identifier uniqueness**

Define a located duplicate payload and a deterministic
`firstDuplicateRuleId?` using `List.zipIdx`/`List.findSome?`. Prove:

```lean
firstDuplicateRuleId? rules = none ↔
  (rules.map (·.id)).Nodup
```

Pin the first duplicate's two declaration indices. The accepted boundary
rejects duplicates; it never silently relies on first-match shadowing.

- [x] **Step 2: Define the canonical lookup**

```lean
def lookupRuleDecl : List RuleDecl → RuleId → Option Rule

def Policy.ruleLookup (P : Policy) : RuleId → Option Rule :=
  lookupRuleDecl P.rules
```

Prove membership and uniqueness-aware lookup theorems. Keep first-match
behavior explicit for raw policies, even though accepted policies have unique
identifiers.

- [x] **Step 3: Refactor `firstViolation?` into one proof-bearing scan**

Use one deterministic scan returning the first strict conclusion/contrary
overlap. Prove both public properties:

```lean
theorem firstViolation_none_iff :
    firstViolation? canon policy = none ↔
      WellFormed canon policy

theorem firstViolation_some_sound
    (h : firstViolation? canon policy = some violation) :
    IsViolation canon policy violation
```

Do not maintain a separate Boolean traversal whose order or predicate can
drift.

- [x] **Step 4: Pin false/none cases**

Closed fixtures cover:

- empty policy;
- defeasible-only policy;
- first located strict violation;
- multiple violations with deterministic first result;
- duplicate rule identifiers with deterministic indices;
- valid unique policy.

- [x] **Step 5: Build and commit**

```bash
cd lean
lake env lean Lara/Policy.lean
lake env lean Lara/Examples/PolicyAcceptance.lean
```

```bash
git add lean/Lara/Policy.lean lean/Lara/Examples/PolicyAcceptance.lean
git commit -m "feat(policy): prove exact accepted lookup boundary"
```

---

### Task 4: Add the Public `Unit` Acceptance Boundary

**Files:**

- Create: `lean/Lara/Unit.lean`
- Create: `lean/Lara/Check/Unit.lean`
- Modify: `lean/Lara.lean`
- Modify: `lean/Lara/Examples.lean`
- Modify: `lean/lakefile.toml` only if module discovery requires it

**Produces:**

- `Unit`
- proof-bearing `CheckedUnit`
- typed `UnitError`
- `checkUnit`

- [x] **Step 1: Define neutral raw and accepted data in `Lara.Unit`**

The raw unit owns exactly one policy, argument list, and attack list. Define
`CheckedUnit` over the accepted policy-derived lookup:

```lean
structure CheckedUnit
    (canon : String → String) (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop) where
  policy          : Policy.Policy
  ruleIds_nodup   : (policy.rules.map (·.id)).Nodup
  policy_wf       : Policy.WellFormed canon policy
  program         : Compile.CheckedProgram canon policy.ruleLookup
                      Gamma CertOk policy.defeat
  attack_complete :
    Compile.AttackComplete canon policy.ruleLookup Gamma CertOk
      policy.defeat program.args program.atts
  nodes           : List (CheckedNode canon policy.ruleLookup Gamma CertOk)
  nodes_terms     : nodes.map (·.term) = program.args
```

Use the exact concrete parameter order required by Lean. The semantic
obligations above may not be weakened. `CheckedUnit.mk` remains public and
safe because constructing it requires every proof. `checkUnit` is the canonical
executable constructor, not the only possible proof-level constructor.

- [x] **Step 2: Define one typed unit error**

In `Lara.Check.Unit`:

```lean
inductive UnitError where
  | duplicateRule   : Policy.DuplicateRule → UnitError
  | policyViolation : Policy.Violation → UnitError
  | program          : ProgramError → UnitError
```

Define one `UnitError.rejectClass` projection:

- duplicate rule → `none`;
- policy violation → `some .R12`;
- wrapped program error → `ProgramError.rejectClass`.

- [x] **Step 3: Implement `checkUnit` in the fixed order**

```text
firstDuplicateRuleId?
  → firstViolation?
  → checkProgramDetailed policy.ruleLookup ... policy.defeat
  → CheckedUnit
```

Use `ProgramAcceptance.attack_complete`, `nodes`, and `nodes_terms` to populate
`CheckedUnit`; do not recheck supports and do not ask executable callers to
supply alignment proofs.

- [x] **Step 4: Prove unit soundness and completeness**

Expose:

```lean
theorem checkUnit_sound ...
theorem checkUnit_complete ...
```

Soundness must make every `CheckedUnit` field available by name. Completeness
must state exactly the raw-unit premises corresponding to the six checks in
the fixed order.

- [x] **Step 5: Add the closed integration matrix**

Cover:

1. valid unit;
2. duplicate rule with location;
3. R12 violation with location;
4. policy error before duplicate argument/program error;
5. wrapped support error;
6. wrapped typed-attack error;
7. wrapped missing conflict;
8. retained-node alignment and exact conclusions;
9. final accepted status theorem through the checked unit.

- [x] **Step 6: Export, build, and commit**

Add imports and update adjacent scope comments in `Lara.lean`.

```bash
cd lean
lake env lean Lara/Unit.lean
lake env lean Lara/Check/Unit.lean
lake env lean Lara/Examples.lean
lake env lean Lara.lean
lake build
```

```bash
git add lean/Lara/Unit.lean lean/Lara/Check/Unit.lean lean/Lara.lean \
  lean/Lara/Examples.lean lean/lakefile.toml
git commit -m "feat(check): add proof-bearing unit acceptance"
```

Stage `lean/lakefile.toml` only if it changed.

---

### Task 5: Prove Grounded Conflict-Freedom and Computed-Claim Result 7

**Files:**

- Modify: `lean/Lara/Attack.lean`
- Modify: `lean/Lara/Grounded.lean`
- Create: `lean/Lara/Consistency.lean`
- Modify: `lean/Lara.lean`
- Create: `lean/Lara/Examples/GroundedConsistency.lean`
- Modify: `lean/Lara/Examples.lean`

**Produces:**

- generic grounded conflict-freedom
- executable `claimSupportFor` and `completeClaimFor`
- accepted-unit direct and claim-level consistency

- [x] **Step 1: Add exact contrary congruence**

In `Lara.Attack`, prove:

```lean
theorem contraryMatch_congr
    {p p' q q' : Atom}
    (hp : equiv canon p p') (hq : equiv canon q q') :
    ContraryMatch canon dp p q ↔
      ContraryMatch canon dp p' q'
```

- [x] **Step 2: Prove generic grounded conflict-freedom**

```lean
def ConflictFree (F : AF) (S : List Arg) : Prop :=
  ∀ a, a ∈ S → ∀ b, b ∈ S → F.attack a b ≠ true

theorem iter_conflictFree (F : AF) :
    ∀ k, ConflictFree F (iter F k)

theorem grounded_conflictFree {F : AF} :
    ConflictFree F (grounded F)

theorem labelC_inn_no_attack ...
```

For the successor proof, defend the target against the source, then defend the
source against the resulting attacker, and contradict the induction
hypothesis. Keep the proof over the existing executable iteration.

- [x] **Step 3: Add exact status witnesses**

Prove:

```lean
theorem statusC_justified_iff (F : AF) (c : Claim) :
    statusC F c = Status.justified ↔
      ∃ i ∈ c.support, labelC F i = Label.inn
```

Also pin:

- empty support is not justified;
- an all-`out` support list is not justified.

- [x] **Step 4: Document reference-evaluator cost**

Adjacent to `defendedB`, `step`, `iter`, and `grounded`, state that this is the
proof-oriented executable reference semantics. Its nested scans are not a
production evaluator. Keep the current definitions unchanged and add a
representative default-heartbeat regression.

Cached adjacency and an optimized production evaluator are deferred to M3.

- [x] **Step 5: Prove the Path-B attackability bridge**

In `Lara.Consistency`:

```lean
theorem wellFormed_contrary_target_attackable
    (unit : Unit.CheckedUnit canon Gamma CertOk)
    {source target : SupportTerm} {Cs Ct : Atom}
    (htarget : HasSupport canon unit.policy.ruleLookup Gamma CertOk
      target Ct [])
    (hcontrary :
      Attack.ContraryMatch canon unit.policy.defeat Cs Ct) :
    Compile.ConflictAttackable unit.policy.ruleLookup target
```

For strict instances, use lookup membership plus
`wellFormed_no_strict_contrary_right unit.policy_wf`; leaves are immediate and
the remaining instance mode is defeasible.

- [x] **Step 6: Compute exact claim support from retained nodes**

Define the complete-support projection:

```lean
def claimSupportFor
    (unit : Unit.CheckedUnit canon Gamma CertOk)
    (p : Atom) : List Nat

def completeClaimFor
    (unit : Unit.CheckedUnit canon Gamma CertOk)
    (p : Atom) : Grounded.Claim :=
  { support := claimSupportFor unit p, holes := [] }
```

`claimSupportFor` is produced from `unit.nodes.zipIdx` in stable declaration
order, selecting exactly the nodes whose retained conclusion is equivalent to
`p`. `completeClaimFor.holes` is empty because it denotes the complete-support
projection only. It does not compute the spec's full `holes(P,p)` collection or
the `incompleteAlternative` diagnostic; that work is tracked separately for
M3.

Prove exactness:

```lean
theorem mem_claimSupportFor_iff :
    i ∈ claimSupportFor unit p ↔
      ∃ node, unit.nodes[i]? = some node ∧
        equiv canon node.conclusion p
```

Cover zero, one, and multiple supports, canonical-equivalent conclusions,
nonmatching decoys, and stable index order.

- [x] **Step 7: Prove direct accepted-unit consistency**

```lean
theorem contrary_args_not_both_grounded
    (unit : Unit.CheckedUnit canon Gamma CertOk)
    ...
    (hcontrary :
      Attack.ContraryMatch canon unit.policy.defeat Cs Ct) :
    ¬ (i ∈ Grounded.grounded (Compile.checkedAF unit.program) ∧
       j ∈ Grounded.grounded (Compile.checkedAF unit.program))
```

Chain:

1. aligned retained nodes provide exact terms and conclusions;
2. Path B makes the target attackable;
3. `unit.attack_complete` provides `Covered`;
4. `complete_conflict_edge` and `edgeB_iff` provide the compiled edge;
5. `grounded_conflictFree` rejects joint membership.

- [x] **Step 8: Prove result 7 only for computed claims**

```lean
theorem contrary_claims_not_both_justified
    (unit : Unit.CheckedUnit canon Gamma CertOk)
    {p q : Atom}
    (hcontrary :
      Attack.ContraryMatch canon unit.policy.defeat p q) :
    ¬ (Grounded.statusC (Compile.checkedAF unit.program)
          (completeClaimFor unit p) = Grounded.Status.justified ∧
       Grounded.statusC (Compile.checkedAF unit.program)
          (completeClaimFor unit q) = Grounded.Status.justified)
```

No arbitrary caller-supplied `Grounded.Claim` appears in the headline theorem.

- [x] **Step 9: Pin the self-conflict flow**

Use a self-contrary atom and one argument:

- without a self-edge, `checkUnit` rejects missing conflict `(0, 0)`;
- with a typed self-edge, `checkUnit` accepts;
- the node is not grounded-`in`;
- `claimSupportFor` includes the node;
- the computed claim is not justified.

- [x] **Step 10: Export, build, and commit**

```bash
cd lean
lake env lean Lara/Grounded.lean
lake env lean Lara/Consistency.lean
lake env lean Lara/Examples/GroundedConsistency.lean
lake env lean Lara/Examples.lean
lake env lean Lara.lean
lake build
```

```bash
git add lean/Lara/Attack.lean lean/Lara/Grounded.lean \
  lean/Lara/Consistency.lean lean/Lara.lean \
  lean/Lara/Examples/GroundedConsistency.lean lean/Lara/Examples.lean
git commit -m "feat(lean): prove checked-unit result 7"
```

---

### Task 6: Close the Test Matrix and Axiom Surface

**Files:**

- Create: `lean/Lara/Examples/AttackCompleteness.lean`
- Create: `lean/Lara/Examples/PolicyAcceptance.lean`
- Create: `lean/Lara/Examples/GroundedConsistency.lean`
- Modify: `lean/Lara/Examples.lean`
- Modify: `lean/AxCheck.lean`

**Target:** Every row in the atomic traceability matrix and all six
language-author flows. The deduplicated matrix below contains **70 unique
obligations**; the number is derived from its stable IDs.

| ID | Layer | Atomic obligation | Planned evidence |
|---|---|---|---|
| COV-01 | Compile | leaf is attackable | closed `decide` fixture |
| COV-02 | Compile | defeasible root is attackable | closed `decide` fixture |
| COV-03 | Compile | strict root is not attackable | closed `decide` fixture |
| COV-04 | Compile | unknown rule is not attackable | closed `decide` fixture |
| COV-05 | Compile | direct declared attack is covered | closed fixture |
| COV-06 | Compile | contained occurrence covers wrapper | closed fixture |
| COV-07 | Compile | wrong target is not covered | closed fixture |
| COV-08 | Compile | empty attack list is not covered | closed fixture |
| COV-09 | Compile | same edge with different typed reason is covered | semantic-boundary fixture |
| COV-10 | Compile | `coveredB` exactly decides `Covered` | public iff theorem |
| PRG-01 | Check.Program | first source-major missing pair is returned | exact error fixture |
| PRG-02 | Check.Program | crossing gaps preserve lexicographic order | exact error fixture |
| PRG-03 | Check.Program | nonmatching edge decoy does not cover target | exact error fixture |
| PRG-04 | Check.Program | support failure precedes missing conflict | exact error fixture |
| PRG-05 | Check.Program | attack failure precedes missing conflict | exact error fixture |
| PRG-06 | Check.Program | empty program detailed-checks successfully | closed fixture |
| PRG-07 | Check.Program | no-contrary program detailed-checks successfully | closed fixture |
| PRG-08 | Check.Program | per-source attack buckets are exact | public iff theorem |
| PRG-09 | Check.Program | retained node terms align with arguments | acceptance-field theorem |
| PRG-10 | Check.Program | legacy accepted result is unchanged | old fixture retained |
| PRG-11 | Check.Program | legacy rejection result is unchanged | old precedence fixtures retained |
| PRG-12 | Check.Program | missing scan `none` is exact | public iff theorem |
| PRG-13 | Check.Program | detailed checker is sound | public theorem |
| PRG-14 | Check.Program | detailed checker is complete | public theorem |
| PRG-15 | Check.Program | late no-gap path passes default heartbeats | representative stress fixture |
| POL-01 | Policy | no duplicate result iff rule IDs are `Nodup` | public iff theorem |
| POL-02 | Policy | first duplicate indices are deterministic | exact fixture |
| POL-03 | Policy | successful lookup denotes a declaration | public theorem |
| POL-04 | Policy | unknown rule lookup returns `none` | closed fixture |
| POL-05 | Policy | empty policy has no R12 violation | closed fixture |
| POL-06 | Policy | defeasible-only policy has no R12 violation | closed fixture |
| POL-07 | Policy | first strict violation is located | exact fixture |
| POL-08 | Policy | multiple R12 violations preserve order | exact fixture |
| POL-09 | Policy | no violation iff `WellFormed` | public iff theorem |
| POL-10 | Policy | returned violation is sound | public theorem |
| UNT-01 | Check.Unit | valid unique Path-B unit accepts | author-flow fixture |
| UNT-02 | Check.Unit | duplicate rule rejects with location | author-flow fixture |
| UNT-03 | Check.Unit | R12 rejects with location | author-flow fixture |
| UNT-04 | Check.Unit | R12 precedes duplicate-argument error | exact precedence fixture |
| UNT-05 | Check.Unit | duplicate argument is wrapped exactly | exact error fixture |
| UNT-06 | Check.Unit | support failure is wrapped exactly | exact error fixture |
| UNT-07 | Check.Unit | attack failure is wrapped exactly | exact error fixture |
| UNT-08 | Check.Unit | missing conflict is wrapped exactly | exact error fixture |
| UNT-09 | Check.Unit | accepted nodes retain exact conclusions and alignment | field/fixture theorem |
| UNT-10 | Check.Unit | `checkUnit` is sound | public theorem |
| UNT-11 | Check.Unit | `checkUnit` is complete | public theorem |
| GRD-01 | Grounded | one-way AF grounded set is conflict-free | closed fixture |
| GRD-02 | Grounded | cycle remains allowed while conflict-free | closed fixture |
| GRD-03 | Grounded | every iteration is conflict-free | public theorem |
| GRD-04 | Grounded | final grounded extension is conflict-free | public theorem |
| GRD-05 | Grounded | two `inn` labels cannot carry an edge | public theorem |
| GRD-06 | Grounded | justified status has an exact `inn` witness | public iff theorem |
| GRD-07 | Grounded | empty support is not justified | closed fixture |
| GRD-08 | Grounded | all-`out` support is not justified | closed fixture |
| GRD-09 | Grounded | representative reference evaluation passes default heartbeats | stress fixture |
| CLM-01 | Consistency | zero complete supports compute `[]` | closed fixture |
| CLM-02 | Consistency | one complete support computes one index | closed fixture |
| CLM-03 | Consistency | multiple supports all appear | closed fixture |
| CLM-04 | Consistency | canonical-equivalent conclusion appears | closed fixture |
| CLM-05 | Consistency | nonmatching conclusion is omitted | closed fixture |
| CLM-06 | Consistency | support indices preserve declaration order | exact-list fixture |
| CLM-07 | Consistency | computed membership is exact | public iff theorem |
| CLM-08 | Consistency | `completeClaimFor` has empty holes by definition | public equation/fixture |
| CNS-01 | Consistency | Path B makes contrary target attackable | public theorem |
| CNS-02 | Consistency | contrary arguments are not jointly grounded | public theorem |
| CNS-03 | Consistency | contrary complete claims are not jointly justified | headline theorem |
| CNS-04 | Integration | missing self-edge rejects at `(0, 0)` | end-to-end fixture |
| CNS-05 | Integration | typed self-edge unit accepts | end-to-end fixture |
| CNS-06 | Integration | accepted self-attacking node is not grounded-`in` | end-to-end theorem |
| CNS-07 | Integration | computed self-contrary claim is not justified | end-to-end theorem |

The six language-author flows are:

1. **AF-01:** valid unique Path-B unit accepts (`UNT-01`);
2. **AF-02:** duplicate rule identifier rejects first (`UNT-02`);
3. **AF-03:** R12 rejects before any program error (`UNT-03`, `UNT-04`);
4. **AF-04:** malformed program errors preserve their internal order
   (`UNT-05`–`UNT-07`);
5. **AF-05:** missing required edge rejects with the first ordered pair
   (`PRG-01`, `PRG-02`, `UNT-08`);
6. **AF-06:** accepted unit computes complete claims and invokes result 7
   (`CLM-07`, `CNS-03`).

- [x] **Step 1: Complete the explicit false/none matrix**

Pin:

- attackability with an unknown rule;
- lookup of an unknown rule identifier;
- `coveredB` with the wrong target;
- `firstViolation?` on empty and defeasible-only policies;
- justified status with empty and all-`out` support.

- [x] **Step 2: Audit every new public adequacy theorem**

`lean/AxCheck.lean` must include at least:

```lean
#print axioms Lara.Attack.contraryMatch_congr
#print axioms Lara.Compile.conflictAttackableB_iff
#print axioms Lara.Compile.coveredB_iff
#print axioms Lara.Compile.complete_conflict_edge
#print axioms Lara.Check.sourceAttackBucket_mem_iff
#print axioms Lara.Check.firstMissingConflict_none_iff
#print axioms Lara.Check.checkProgram_sound
#print axioms Lara.Check.checkProgram_complete
#print axioms Lara.Check.checkProgramDetailed_sound
#print axioms Lara.Check.checkProgramDetailed_complete
#print axioms Lara.Policy.firstDuplicateRuleId_none_iff
#print axioms Lara.Policy.firstViolation_none_iff
#print axioms Lara.Policy.firstViolation_some_sound
#print axioms Lara.Check.Unit.checkUnit_sound
#print axioms Lara.Check.Unit.checkUnit_complete
#print axioms Lara.Unit.CheckedUnit.nodes_terms
#print axioms Lara.Unit.CheckedUnit.attack_complete
#print axioms Lara.Grounded.iter_conflictFree
#print axioms Lara.Grounded.grounded_conflictFree
#print axioms Lara.Grounded.labelC_inn_no_attack
#print axioms Lara.Grounded.statusC_justified_iff
#print axioms Lara.Consistency.wellFormed_contrary_target_attackable
#print axioms Lara.Consistency.mem_claimSupportFor_iff
#print axioms Lara.Consistency.contrary_args_not_both_grounded
#print axioms Lara.Consistency.contrary_claims_not_both_justified
```

Use final elaborated names if a namespace differs. Do not omit a theorem
because a helper name changed.

- [x] **Step 3: Run the full Lean and axiom gates**

```bash
cd lean
lake build
lake env lean AxCheck.lean | tee /tmp/lara-issue-18-axcheck.txt
! rg -q 'sorryAx' /tmp/lara-issue-18-axcheck.txt
```

Inspect all output and confirm only:

```text
propext
Classical.choice
Quot.sound
```

- [x] **Step 4: Run the unchanged Haskell regression-compatibility suite**

```bash
cabal build all
cabal test all --test-show-details=direct
```

These commands detect regressions in existing shared surfaces. They do not
test the six new acceptance flows because no production Haskell unit/program
checker exists yet.

- [x] **Step 5: Commit**

```bash
git add lean/Lara/Examples.lean lean/AxCheck.lean
git commit -m "test(lean): audit checked-unit consistency"
```

---

### Task 7: Reconcile Documentation and ARA Status

**Files:**

- Modify: `plans/2026-07-25-issue-18-attack-completeness-result-7.md`
- Modify: `lean/README.md`
- Modify: `docs/spec.md`
- Modify: `docs/mechanization-plan.md`
- Modify: `docs/m1-freeze-checklist.md`
- Modify: `ara/evidence/status/mechanization_status.md`
- Modify: `ara/logic/claims.md`
- Modify: `ara/logic/solution/mechanization.md`
- Modify: `ara/trace/exploration_tree.yaml`
- Modify: `ara/trace/sessions/` through the research-manager epilogue

- [x] **Step 1: Update flow and dependency diagrams**

Update this plan plus adjacent module/file headers and comments in:

- `Lara.Policy`;
- `Lara.Compile`;
- `Lara.Check.Program`;
- `Lara.Unit`;
- `Lara.Check.Unit`;
- `Lara.Consistency`;
- `Lara.Grounded`;
- `Lara.lean`.

The comments must identify the public `checkUnit` boundary, fixed error order,
retained-node source, and downstream-only consistency module.

Implemented public flow:

```text
Unit
  │
  ▼
checkUnit
  ├─ duplicate rule IDs
  ├─ R12 policy violation
  └─ checkProgramDetailed
       ├─ duplicate arguments
       ├─ support (build retained checked-node cache)
       ├─ typed attacks (reuse cache; no support re-inference)
       └─ missing conflict (reuse cache; exact Covered/coveredB)
              │
              ▼
         Unit.CheckedUnit
              │
              ├─ Compile.checkedAF ──► Grounded (generic reference evaluator)
              └─ completeClaimFor ───► Consistency (downstream-only result 7)
```

`checkProgram`/`CheckedProgram` remains the legacy generic attack-soundness
boundary. Detailed `ProgramAcceptance` and `CheckedUnit` carry attack
completeness and retained nodes, preserving the acyclic dependency direction.

- [x] **Step 2: Update status without overclaiming**

Record:

- issue #18 closes attack completeness and result 7 for the Lean reference PL;
- `CheckedUnit`, built only by `checkUnit`, is the accepted-program
  abstraction;
- Path B is enforced before program checking;
- exact computed support aggregation is part of the theorem;
- self-conflict is handled;
- grounded is a proof-oriented reference evaluator;
- the Haskell commands are regression-compatibility evidence only, not
  evidence for the new Lean-only acceptance flows;
- no Path A, production Haskell checker, or NL-to-structure validation is
  claimed.

Issue #18 closes attack completeness and spec §9 result 7 / mechanization claim
C09 for the Lean reference PL. `checkUnit` is the canonical executable
`CheckedUnit` constructor; manual proof-level construction still requires all
invariants. The headline theorem consumes exact computed `completeClaimFor`
claims only, includes ordered self-pairs, and does not claim full `holes(P,p)`
or `incompleteAlternative` computation. `Lara.Grounded` remains a
proof-oriented reference evaluator.

Verified implementation evidence: tasks 1–6 landed in `a0cf49c`, `8ed5714`,
`3acd6e0`, `7b79004`, `677cf8b`, and `27b36c3`; all 70 traceability IDs and six
author flows pass; `lake build` passes 25 jobs; AxCheck emits 430 reports with
no `sorryAx` and only `propext`, `Classical.choice`, and `Quot.sound`; the CI
multiline axiom parser is repaired and negative-tested. `cabal build` and
`cabal test` pass one suite / 30 QuickCheck groups / 100 cases each, but are
regression-compatibility evidence only, not new Lean acceptance-flow evidence.

- [x] **Step 3: Run the ARA research-manager epilogue**

Capture the accepted-unit boundary, error order, rule-ID uniqueness, coverage
definition, Path-B split, retained-node decision, computed-claim boundary,
self-conflict case, performance boundary, proof dead ends, and final gate
results.

- [x] **Step 4: Review repository integrity**

```bash
git diff --check
git status --short
git diff --stat origin/main...HEAD
git log --oneline --decorate origin/main..HEAD
```

- [x] **Step 5: Commit**

```bash
git add plans/2026-07-25-issue-18-attack-completeness-result-7.md \
  lean/README.md docs/spec.md docs/mechanization-plan.md \
  docs/m1-freeze-checklist.md ara/evidence/status/mechanization_status.md \
  ara/logic/claims.md ara/logic/solution/mechanization.md ara/trace
git commit -m "docs(m2): record checked-unit result 7"
```

## Final Acceptance Checklist

- [x] `checkUnit` is the canonical executable `CheckedUnit` constructor; manual
      proof-level construction still requires every invariant.
- [x] Duplicate rule identifiers are rejected deterministically.
- [x] `firstViolation? = none ↔ Policy.WellFormed`, and every returned
      violation is sound.
- [x] The fixed six-stage error order is pinned by closed fixtures.
- [x] `coveredB` exactly decides compiled-edge coverage.
- [x] Same-source/same-target coverage from a different typed attack reason is
      explicitly accepted as unlabelled edge completeness.
- [x] `edgeB` reuses `coveredB`; no duplicate edge algorithm exists.
- [x] `AttackComplete` is carried by `ProgramAcceptance` and `CheckedUnit`, not
      the generic `CheckedProgram`.
- [x] The completeness scan uses one indexed cache, exact per-source attack
      buckets, and nested `findSome?`, without a materialized pair list or edge
      matrix.
- [x] `ProgramAcceptance` replaces positional conjunction projections.
- [x] `CheckedUnit.nodes` comes from the checker cache and aligns exactly with
      `program.args`.
- [x] Strict-root conflicts are rejected by R12 before program checking.
- [x] Subargument closure satisfies completeness without redundant attacks.
- [x] Grounded extensions are conflict-free for arbitrary finite AFs.
- [x] `claimSupportFor` computes exact stable complete-support indices.
- [x] `completeClaimFor` is documented as a complete-only projection, not a
      computation of `holes(P,p)`.
- [x] The headline result-7 theorem consumes computed complete claims.
- [x] The self-conflict flow rejects a missing edge and prevents justification
      when a typed self-edge exists.
- [x] All 70 traceability obligations and six author flows pass.
- [x] Every public adequacy/integration theorem appears in AxCheck.
- [x] No `sorryAx`; only the allowed axiom trio.
- [x] Lean proof gates and Haskell regression-compatibility gates pass.
- [x] Result 7/C09 status is updated precisely.

## What Already Exists and Is Reused

| Existing surface | Reuse decision |
|---|---|
| `Attack.ContraryMatch` / `contraryMatchB_iff` | Keep the directional conflict relation and exact decider. Add congruence only. |
| `Attack.HasAttack` / attack checker | Preserve declared-attack soundness. Completeness is a later whole-program invariant. |
| `Compile.Contains` / `AttackOcc` | Keep the frozen occurrence and subargument semantics. |
| `Compile.attackClosureB_iff` | Reuse to prove `coveredB_iff`. |
| `Compile.Edge` / `edgeB` | Refactor through `Covered` / `coveredB` without behavior change. |
| `Compile.CheckedProgram` | Preserve its existing generic soundness boundary; carry attack completeness only in detailed/unit acceptance. |
| `Check.CheckedArguments.cache` | Derive exact indexed nodes and never rerun support inference. |
| `Policy.WellFormed` / `wfB_iff` | Preserve as the Path-B relation; make the located scan exact. |
| `Grounded.iter` / `defendedB_iff` | Reuse for finite conflict-freedom. |
| `Grounded.statusC` | Preserve the frozen priority and prove exact justified witnesses. |
| `Compile.checkedAF` | Use the checker-built edge decider from #17. |

## NOT in scope

- Path A, transposition, contraposition, or total/involutive negation.
- Completeness for attacks against every internal subterm.
- Redundant root attacks when closure already supplies the edge.
- A full edge/coverage matrix.
- Cached adjacency or a production grounded evaluator; tracked as a P2 M3
  TODO.
- Full `holes(P,p)` aggregation and `incompleteAlternative` reporting; tracked
  as a P2 M3 TODO.
- Production Haskell policy/program checking or JSON decoding.
- R2/R8/R9/R14 implementation.
- `Backend.uses` / `certDeps`.
- Certificate-erased identity or backend replacement.
- Preferred, stable, or complete argumentation semantics.
- Natural-language claim/edge extraction faithfulness.
- Closing issues or publishing a PR without a separate publish request.

## Failure Modes and Coverage

| Path | Failure | Test/proof | Handling | Visibility |
|---|---|---|---|---|
| rule lookup | duplicate identifier silently shadows a rule | duplicate exactness + located fixture | typed rejection | clear `UnitError.duplicateRule` |
| Path B | located scan disagrees with `WellFormed` | `firstViolation_none_iff` + soundness | typed rejection | clear R12 payload |
| error order | missing conflict masks R12 or support failure | `checkUnit` precedence matrix | ordered `Except` branches | first typed error |
| coverage | wrapper demands redundant rebut | closure fixture + accepted wrapper unit | no erroneous rejection | accepted result |
| edge meaning | attack reason is mistaken for an AF edge label | different-reason edge fixture | documented semantic choice | accepted result |
| direction | reverse-only contrary is required | asymmetric ordered-pair fixture | typed missing edge only in required direction | located pair |
| pair scan | later gap wins or self-pair is skipped | crossing + `(0, 0)` fixtures | source-major `findSome?` | located first pair |
| cache | conclusion is re-inferred or misaligned | acceptance/unit alignment theorems | construction impossible without proof | elaboration failure |
| performance | every pair rescans all attacks | bucket exactness + heartbeat fixture | source-indexed cache | CI/elaboration failure on regression |
| grounded | two `in` nodes attack each other | generic conflict-free theorem | theorem excludes state | elaboration/AxCheck failure |
| claims | unchecked indices enter result 7 | `claimSupportFor` exactness | headline accepts computed projection only | elaboration failure |
| equivalence | canonical-equivalent conclusion is omitted | congruence + claim fixtures | exact Boolean/proof bridge | fixture failure |
| self-conflict | self-contrary claim becomes justified | rejected/accepted self-edge E2E | missing edge or grounded exclusion | typed error or theorem |
| status | empty/all-`out` support becomes justified | closed false fixtures | total status function | fixture failure |

No reviewed path may fail silently: checker gaps are typed `Except.error`
values; theorem gaps fail elaboration or AxCheck.

## Worktree Parallelization

Three early lanes can proceed without overlapping semantic ownership or
fixture files:

| Step | Modules touched | Depends on |
|---|---|---|
| coverage and detailed program acceptance | `Lara.Compile`, `Lara.Check.Program`, `Lara.Examples.AttackCompleteness` | None |
| policy acceptance | `Lara.Policy`, `Lara.Examples.PolicyAcceptance` | None |
| grounded lemmas | `Lara.Attack`, `Lara.Grounded`, `Lara.Examples.GroundedConsistency` | None |
| unit acceptance | `Lara.Unit`, `Lara.Check.Unit` | coverage + policy |
| result-7 integration | `Lara.Consistency`, `Lara.Examples` | all three early lanes + unit acceptance |
| audit and status | `AxCheck`, `docs`, `ara` | result-7 integration |

```text
Lane A: Task 1 → Task 2
  coverage, cache metadata, program completeness
  fixtures: Lara/Examples/AttackCompleteness.lean

Lane B: Task 3
  rule uniqueness, lookup, Path-B exactness
  fixtures: Lara/Examples/PolicyAcceptance.lean

Lane C: Task 5 steps 1–4
  contrary congruence, grounded conflict-freedom, status lemmas
  fixtures: Lara/Examples/GroundedConsistency.lean

             A + B
               |
               v
             Task 4
          Unit / Check.Unit
               |
          A + B + C
               |
               v
        Task 5 steps 5–10
         accepted-unit result 7
               |
               v
          Task 6 → Task 7
```

The three lane-specific fixture modules are committed independently. Only the
integration owner edits `Lara/Examples.lean` to import them and add cross-layer
`checkUnit` flows. AxCheck and documentation remain single-owner closeout work.
Launch lanes A, B, and C in parallel worktrees. Merge all three, run Task 4,
then finish the dependent consistency, audit, and documentation work
sequentially. No parallel lanes share a module after the fixture split.

## Performance Budget

- The completeness scan remains quadratic in retained node count for contrary
  comparison.
- Exact conclusions, target attackability, and typed attacks bucketed by source
  are computed once.
- Nested `findSome?` short-circuits on the first diagnostic and does not
  allocate all pairs.
- With `n` retained nodes, `m` attacks, and target traversal cost `t`, the
  intended reference bound is approximately `O(n² + n·m·t)` after bucket
  construction, rather than rescanning all `m` attacks for all `n²` pairs.
- The reference grounded evaluator retains its existing nested scans. Document
  the cost and protect a representative input under default heartbeats.
- An adjacency cache, edge matrix, or production evaluator spends a separate
  optimization token and belongs to M3.

## Implementation Tasks

Synthesized from this review's findings. Each task derives from a specific
finding above. Run with Claude Code or Codex; checkbox as you ship.

- [x] **T1 (P1, human: ~2–3d / CC: ~2–4h)**: Program acceptance: Retain one
  executable checked-node result without changing legacy `checkProgram`
  - Surfaced by: Architecture and outside review; cache data cannot be
    recovered through a later soundness theorem.
  - Files: `lean/Lara/Unit.lean`, `lean/Lara/Check/Program.lean`
  - Verify: `cd lean && lake env lean Lara/Check/Program.lean`
- [x] **T2 (P1, human: ~1–2d / CC: ~1–2h)**: Policy acceptance: Make rule
  uniqueness and the located Path-B scan exact
  - Surfaced by: Architecture review; raw first-match lookup is ambiguous
    with duplicate identifiers, and `firstViolation?` lacks exactness.
  - Files: `lean/Lara/Policy.lean`,
    `lean/Lara/Examples/PolicyAcceptance.lean`
  - Verify: `cd lean && lake env lean Lara/Examples/PolicyAcceptance.lean`
- [x] **T3 (P1, human: ~2–3d / CC: ~2–4h)**: Attack completeness: Decide
  unlabelled edge coverage with source-indexed attack buckets
  - Surfaced by: Architecture and performance review; result 7 needs ordered
    edge completeness, deterministic diagnostics, and no full attack rescan per
    pair.
  - Files: `lean/Lara/Compile.lean`, `lean/Lara/Check/Program.lean`,
    `lean/Lara/Examples/AttackCompleteness.lean`
  - Verify: `cd lean && lake env lean Lara/Examples/AttackCompleteness.lean`
- [x] **T4 (P1, human: ~2d / CC: ~2h)**: Unit checker: Implement the fixed
  six-stage `checkUnit` acceptance procedure
  - Surfaced by: Architecture review; Path-B and program premises must be one
    executable PL boundary with a typed error.
  - Files: `lean/Lara/Unit.lean`, `lean/Lara/Check/Unit.lean`,
    `lean/Lara/Examples.lean`
  - Verify: `cd lean && lake env lean Lara/Check/Unit.lean && lake env lean Lara/Examples.lean`
- [x] **T5 (P1, human: ~2–3d / CC: ~3–5h)**: Consistency: Prove generic
  grounded conflict-freedom and accepted-unit result 7
  - Surfaced by: Architecture review; typed edges alone do not establish
    direct or claim-level consistency.
  - Files: `lean/Lara/Attack.lean`, `lean/Lara/Grounded.lean`,
    `lean/Lara/Consistency.lean`,
    `lean/Lara/Examples/GroundedConsistency.lean`
  - Verify: `cd lean && lake env lean Lara/Consistency.lean`
- [x] **T6 (P1, human: ~1–2d / CC: ~1–2h)**: Claim aggregation: Compute
  exact complete support and keep hole aggregation out of the theorem
  - Surfaced by: Code-quality and outside review; unchecked claim lists and
    `holes := []` must not be presented as full claim construction.
  - Files: `lean/Lara/Consistency.lean`, `lean/Lara/Examples.lean`
  - Verify: run `CLM-01` through `CLM-08` and the `CNS-03` headline theorem.
- [x] **T7 (P2, human: ~1–2d / CC: ~2h)**: Test and audit: Close all
  traceability IDs and AxCheck entries
  - Surfaced by: Test review; the original plan lacked 17 cases, six author
    flows, self-conflict, and a one-to-one evidence map.
  - Files: `lean/Lara/Examples/`, `lean/Lara/Examples.lean`,
    `lean/AxCheck.lean`
  - Verify: `cd lean && lake build && lake env lean AxCheck.lean`
- [x] **T8 (P2, human: ~1d / CC: ~1h)**: Status reconciliation: Update
  module diagrams and report only Lean-backed issue #18 claims
  - Surfaced by: Code-quality and outside review; dependency flow, plan
    staging, complete-support scope, and Haskell evidence need precise wording.
  - Files: this plan, `lean/README.md`, `docs/`, `ara/`
  - Verify: `git diff --check` and review every changed status claim against
    AxCheck output.
- [ ] **T9 (P3, human: ~1–2w / CC: ~1–2d)**: Runtime: Build cached grounded
  adjacency for the M3 evaluator
  - Surfaced by: Performance review; the Lean evaluator is a proof reference,
    not the intended production runtime.
  - Files: M3 checker/runtime modules and differential tests, as chosen by the
    M3 implementation plan
  - Verify: differential labels and statuses against `Grounded.grounded`.
- [ ] **T10 (P3, human: ~3–5d / CC: ~4–8h)**: Reporting: Compute full claim
  holes and incomplete-alternative diagnostics
  - Surfaced by: Outside review; issue #18 computes complete support only.
  - Files: M3 raw-unit/reporting modules and shared claim fixtures
  - Verify: golden cases for empty support, unresolved alternatives, and a
    complete winning alternative with separate hole diagnostics.

## Plan Review

**Architecture findings resolved:** six of six. The accepted boundary is
`checkUnit → CheckedUnit`; rule IDs are unique; error precedence is fixed;
modules remain acyclic; the policy scan is proof-bearing; and result 7 uses
computed complete-support claims.

**Code-quality findings resolved:** four of four. `ProgramAcceptance` names the
checker result; `UnitError` is typed; retained nodes are aligned without
rewriting `CheckedProgram`; and dependency/error-flow comments are explicit.

**Test findings resolved:** the initial plan claimed 39 obligations without a
one-to-one mapping and missed all six end-to-end author flows. The revised
matrix has 70 deduplicated stable IDs, maps each to planned evidence, and maps
all six author flows to those IDs.

**Performance findings resolved:** the pair scan reuses precomputed immutable
node metadata and exact per-source attack buckets, and avoids pair
materialization. The grounded evaluator remains the proof reference, with a
default-heartbeat stress guard and optimized adjacency deferred.

**Key language decision:** a raw policy and program enter the executable PL
only through `checkUnit`. Proof-level users may manually construct
`CheckedUnit`, but only by supplying the same uniqueness, Path-B,
attack-completeness, and alignment invariants.

**Outside review decisions:** retain executable nodes through a shared base
checker and `checkProgramDetailed`; preserve generic `CheckedProgram` and
legacy `checkProgram`; keep unlabelled edge completeness; distinguish complete
support from full hole aggregation; index attacks by source; split fixture
modules; replace the unsupported test count with traceability IDs; stage this
plan during closeout; and describe Cabal as regression evidence only.

**Verdict:** Ready to implement. No unresolved decisions remain.

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | Not run | Not run |
| Codex Review | `/codex review` | Independent 2nd opinion | 1 | RESOLVED | 10 challenges: 9 accepted/refined, 1 current semantic choice retained |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 2 | CLEAR | 29 issues, 0 critical gaps |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | Not run | No UI scope |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | Not run | Not run |

**CROSS-MODEL:** Both reviews converged on a proof-bearing accepted-unit
boundary. The outside pass corrected executable cache retention, API
ownership, performance indexing, claim scope, and test traceability. Its
reason-sensitive attack proposal was rejected because the frozen compiled AF
stores unlabelled edges and result 7 depends on edge existence.

**VERDICT:** ENG CLEARED; ready to implement.

NO UNRESOLVED DECISIONS
