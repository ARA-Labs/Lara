# PW-T8 Executable StatusBridge Checker Implementation Plan (issue #239)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add `statusBridgeB : SymMap → (LeafId → LeafId) → World κ → World lam → Bool`, a decider for the `StatusBridge` hypotheses that scans the finite index ranges of the two compiled programs, with `statusBridgeB_sound` (and completeness, which turns out cheap), so every future PW-T8 conformance cell is one `decide`.

**Architecture:** One new section (§5) in `lean/Lara/PW/Status.lean`: a per-index-pair decider `corrB` for `Corr`, per-clause deciders `admitsB`/`matchedB`/`forthB`/`backB` each with its correctness lemma, and the conjunction `statusBridgeB` with `_sound`/`_complete`/`_iff`. `Lara/Examples/PWStatus.lean` then replaces its three index-by-index positive `StatusBridge` proofs with `statusBridgeB_sound (by decide)` and adds a checker cell to the negative T7 half. AxCheck rows and a `docs/paper-lean-name-map.md` row land with the theorems.

**Tech Stack:** Lean 4 (repo toolchain in `lean/lean-toolchain`), lake, existing CI gates (`check-axcheck-coverage.py`, `check-axioms.sh`).

## Background and motivation

PW-T8 (`Lara/PW/Status.lean`, landed via #193/#240) proves conditional status
preservation: under the `StatusBridge` hypotheses — `admits` (left-totality of
the translation on program arguments), `matched` (right-totality), and attack
`forth`/`back` on the compiled edge decider `Compile.edgeB` — the translated
claim has at the target world exactly the status it has at the source world
(`status_transport`). The hypotheses are a `Prop`-valued structure, and the
example module `Lara/Examples/PWStatus.lean` discharges them **by hand, index
by index**: `s2_r2_statusBridge` alone is ~70 lines of `edgeB_faithful`
range recovery, `omega` index pinning, and per-edge case splits, and
`s3_r3_statusBridge` needs a bespoke helper (`s3_corr_diag`) just to pin the
correlation to the diagonal. Every further conformance cell — every new pair of
worlds anyone wants a T8 instance for — repeats that ritual.

But everything quantified in `StatusBridge` is secretly finite:

- `Corr m lm w v i j` (`Status.lean:167`) is a pair of `getElem?` hits plus a
  `trSupport` equation — decidable per index pair given `DecidableEq
  SupportTerm`, which `Lara/Support.lean` provides (the hand-rolled mutual
  `decEq` at `Support.lean:250`).
- `admits`/`matched` quantify over list membership in the two programs'
  `args`.
- `forth`/`back` quantify over **all** naturals, but each hypothesis pins its
  indices into range: `corr_lt` bounds the `Corr` pair, and
  `(Compile.edgeB_faithful P).ranged` bounds the attacker index — the
  `StatusBridge` docstring (`Status.lean:201-204`) already tells instances to
  recover in-rangeness exactly this way. So a scan over `List.range` of the
  two argument counts loses nothing, and completeness (not just soundness) is
  cheap: the existential witnesses produced by the `Prop` clauses are
  themselves in range by `corr_lt`.

This is the same executable-layer pattern the repo already uses twice: `Edge`
and its decider `edgeB` + `edgeB_faithful` living side by side in
`Compile.lean`, and T5's `crossCompare` + `Presents` adequacy layer in
`PW/Compare.lean` (the style the issue names). Cost is Lean-only: no corpus
regeneration, no freeze impact. Per CLAUDE.md's mechanization discipline, the
decider and its metatheory land together, `sorry`-free, inside the standard
axiom trio, with AxCheck rows for every theorem (the #242 whole-tree coverage
gate enforces this).

### Design decisions (locked)

1. **Location: `Lara/PW/Status.lean`, new §5.** `StatusBridge` and its decider
   change together (the `Edge`/`edgeB` precedent). The module grows ~180
   lines past the 400-line guideline; per CLAUDE.md that guideline yields to
   ownership, and "the T8 hypotheses and their checker" is one thing. No new
   imports are needed: `Status.lean` already sees `Compile.edgeB`,
   `edgeB_faithful`, `trSupport`, and `Admits` (via `Lara.PW.Structural`).
2. **Completeness is in scope.** The issue says "if cheap"; the analysis above
   shows it is. It also pays for itself immediately: the negative T7 cell in
   the example module gets a checker route (`statusBridgeB = false` refutes
   `StatusBridge` via the contrapositive of completeness).
3. **Example module:** the three positive hand proofs (`s1_r1_statusBridge`,
   `s2_r2_statusBridge`, `s3_r3_statusBridge`) become
   `statusBridgeB_sound (by decide)` — that is the issue's stated payoff, and
   the theorem names/statements (registered in `docs/paper-lean-name-map.md`)
   do not change. The negative T7 half stays hand-proved: `t7_unmatched` /
   `t7_not_statusBridge` document *which* clause fails and where, which a
   `false` scan cannot. `s3_corr_diag` stays (registered in the name map,
   independently meaningful); only the bridge proofs shrink.
4. **Names per the issue:** `statusBridgeB`, `statusBridgeB_sound`. Clause
   deciders follow the repo's `*B` convention (`edgeB`, `coveredB`,
   `acceptB`).

## Global Constraints

- Proofs `sorry`-free; axioms limited to `propext`, `Classical.choice`,
  `Quot.sound` (CI: `lake env lean AxCheck.lean | ../scripts/check-axioms.sh`).
- Every new `theorem`/`lemma` in `lean/Lara/**` gets a `#print axioms` row in
  `lean/AxCheck.lean` **in the same commit** (CI:
  `python3 ../scripts/check-axcheck-coverage.py AxCheck.lean $(find Lara -name '*.lean' | sort)`).
- `native_decide` is banned in the PW example modules (see the
  `Examples/PWStatus.lean` header); use `decide` only.
- No new backlog files; deferred work → `gh issue create`.
- Exact core-lemma names (`Bool.and_eq_false_iff`, `Bool.not_eq_true'`,
  `List.any_eq_true`, …) are written against the repo toolchain from memory;
  the per-task `lake build` step is the check, and small tactic adjustments
  are expected and fine. The *statements* of the new theorems are the
  contract and must not drift.
- Commit messages follow the repo pattern: `theory(PW-T8): <what> (#239)`.

---

### Task 0: Branch

- [ ] **Step 1: Create the working branch off `main`**

```bash
cd /home/yfhe/ara/lara
git checkout main && git pull
git checkout -b theory/pw-t8-statusbridge-checker
```

- [ ] **Step 2: Confirm the tree builds before touching anything**

Run: `cd lean && lake build`
Expected: build succeeds with no output changes (baseline).

### Task 1: `corrB` — decide `Corr` at one index pair

**Files:**
- Modify: `lean/Lara/PW/Status.lean` (append a new section after §4
  `Compose`, i.e. after `end Compose`, before `end Lara.PW`)
- Modify: `lean/AxCheck.lean` (PW-T8 section, after
  `#print axioms Lara.PW.StatusBridge.comp`)

**Interfaces:**
- Consumes: `Corr` (`Status.lean:167`), `corr_lt` (`Status.lean:174`),
  `trSupport` (`PW/Translation.lean:170`), `DecidableEq SupportTerm`
  (`Support.lean`).
- Produces: `def corrB (m : SymMap) (lm : LeafId → LeafId) (w : World κ)
  (v : World lam) (i j : Nat) : Bool` and
  `theorem corrB_iff : corrB m lm w v i j = true ↔ Corr m lm w v i j`
  (implicit arguments throughout). Tasks 2–4 use both.

- [ ] **Step 1: Write the definition and lemma**

Append to `lean/Lara/PW/Status.lean`:

```lean
/-! ### §5 The executable checker (issue #239)

`StatusBridge` is finitely checkable: `Corr` is a pair of `getElem?` hits
plus a `trSupport` equation, `admits`/`matched` quantify over the two
argument lists, and although `forth`/`back` quantify over all naturals,
`corr_lt` bounds the correlated pair and `(edgeB_faithful _).ranged` bounds
the attacker index — the very recovery the `StatusBridge` docstring
prescribes to instances. So a scan over `List.range` of the two argument
counts is sound *and* complete, and a conformance cell is one `decide`
(`statusBridgeB_sound (by decide)`), in the executable-layer style of
`Compile.edgeB` and T5's `crossCompare`. -/

section Checker
variable {κ lam : Instance.Context}

/-- Decides `Corr` at one index pair: both positions are hits and the source
term translates to the target term. Term equality is `SupportTerm`'s derived
decidable equality — structural source equality, certificates included. -/
def corrB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) (i j : Nat) : Bool :=
  match w.unit.program.args[i]?, v.unit.program.args[j]? with
  | some t, some t' => trSupport m lm t == some t'
  | _, _ => false

theorem corrB_iff {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} {i j : Nat} :
    corrB m lm w v i j = true ↔ Corr m lm w v i j := by
  unfold corrB Corr
  cases ht : w.unit.program.args[i]? with
  | none => simp [ht]
  | some t =>
    cases ht' : v.unit.program.args[j]? with
    | none => simp [ht, ht']
    | some t' => simp [ht, ht', beq_iff_eq]

end Checker
```

(The `section Checker` opens here and is *extended* by Tasks 2–4: place
later definitions before `end Checker`.)

- [ ] **Step 2: Build**

Run: `cd lean && lake build Lara.PW.Status`
Expected: success. If the `simp` sets stall, the manual shape is: forward
direction destructs the match and applies `beq_iff_eq`/`Option.some.inj`;
backward direction destructs `Corr`'s existential, rewrites both `getElem?`
equations, and closes with `beq_iff_eq.mpr`.

- [ ] **Step 3: Add the AxCheck row**

In `lean/AxCheck.lean`, after `#print axioms Lara.PW.StatusBridge.comp`, add:

```lean
-- The executable checker (issue #239).
#print axioms Lara.PW.corrB_iff
```

- [ ] **Step 4: Verify the audit still passes**

Run: `cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh`
Expected: exit 0, no `sorryAx`, no axiom outside the trio.

- [ ] **Step 5: Commit**

```bash
git add lean/Lara/PW/Status.lean lean/AxCheck.lean
git commit -m "theory(PW-T8): decide Corr at an index pair (#239)"
```

### Task 2: `admitsB` and `matchedB` — the two totality clauses

**Files:**
- Modify: `lean/Lara/PW/Status.lean` (inside `section Checker`, after
  `corrB_iff`)
- Modify: `lean/AxCheck.lean` (extend the issue-#239 block)

**Interfaces:**
- Consumes: `Admits` (`PW/Structural.lean:465`), `trSupport`,
  `DecidableEq SupportTerm`.
- Produces:
  `def admitsB (m : SymMap) (lm : LeafId → LeafId) (w : World κ) (v : World lam) : Bool`,
  `theorem admitsB_iff : admitsB m lm w v = true ↔ Admits m lm w v`,
  `def matchedB (m : SymMap) (lm : LeafId → LeafId) (w : World κ) (v : World lam) : Bool`,
  `theorem matchedB_iff : matchedB m lm w v = true ↔ ∀ t', t' ∈ v.unit.program.args → ∃ t, t ∈ w.unit.program.args ∧ trSupport m lm t = some t'`.
  Task 4 consumes all four.

- [ ] **Step 1: Write the definitions and lemmas**

```lean
/-- Decides T6's `Admits`: every source argument translates and its image is
a target argument. -/
def admitsB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Bool :=
  w.unit.program.args.all fun t =>
    match trSupport m lm t with
    | some t' => decide (t' ∈ v.unit.program.args)
    | none => false

theorem admitsB_iff {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} :
    admitsB m lm w v = true ↔ Admits m lm w v := by
  unfold admitsB Admits
  rw [List.all_eq_true]
  constructor
  · intro h t ht
    have hb := h t ht
    cases htr : trSupport m lm t with
    | none => rw [htr] at hb; exact absurd hb (by simp)
    | some t' => rw [htr] at hb; exact ⟨t', rfl, of_decide_eq_true hb⟩
  · intro h t ht
    obtain ⟨t', htr, hmem⟩ := h t ht
    rw [htr]
    exact decide_eq_true hmem

/-- Decides `StatusBridge.matched`: every target argument is the transport of
some source argument. -/
def matchedB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Bool :=
  v.unit.program.args.all fun t' =>
    w.unit.program.args.any fun t => trSupport m lm t == some t'

theorem matchedB_iff {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} :
    matchedB m lm w v = true ↔
      ∀ t', t' ∈ v.unit.program.args →
        ∃ t, t ∈ w.unit.program.args ∧ trSupport m lm t = some t' := by
  unfold matchedB
  rw [List.all_eq_true]
  constructor
  · intro h t' ht'
    obtain ⟨t, ht, htr⟩ := List.any_eq_true.mp (h t' ht')
    exact ⟨t, ht, beq_iff_eq.mp htr⟩
  · intro h t' ht'
    obtain ⟨t, ht, htr⟩ := h t' ht'
    exact List.any_eq_true.mpr ⟨t, ht, beq_iff_eq.mpr htr⟩
```

- [ ] **Step 2: Build**

Run: `cd lean && lake build Lara.PW.Status`
Expected: success.

- [ ] **Step 3: Extend the AxCheck block**

```lean
#print axioms Lara.PW.admitsB_iff
#print axioms Lara.PW.matchedB_iff
```

- [ ] **Step 4: Verify audit**

Run: `cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh`
Expected: exit 0.

- [ ] **Step 5: Commit**

```bash
git add lean/Lara/PW/Status.lean lean/AxCheck.lean
git commit -m "theory(PW-T8): decide the two totality clauses (#239)"
```

### Task 3: `forthB` and `backB` — the attack clauses over `List.range`

**Files:**
- Modify: `lean/Lara/PW/Status.lean` (inside `section Checker`, after
  `matchedB_iff`)
- Modify: `lean/AxCheck.lean` (extend the issue-#239 block)

**Interfaces:**
- Consumes: `corrB`/`corrB_iff` (Task 1), `corr_lt`, `Compile.edgeB`,
  `Compile.edgeB_faithful` (`Compile.lean:617`, `:650`).
- Produces:
  `def forthB (m : SymMap) (lm : LeafId → LeafId) (w : World κ) (v : World lam) : Bool`,
  `theorem forthB_sound : forthB m lm w v = true → ∀ i j k, Corr m lm w v i j → edgeB w.unit.program k i = true → ∃ k', Corr m lm w v k k' ∧ edgeB v.unit.program k' j = true`,
  `theorem forthB_complete` (converse), and the mirrored
  `backB`/`backB_sound`/`backB_complete` for
  `∀ i j k', Corr m lm w v i j → edgeB v.unit.program k' j = true → ∃ k, Corr m lm w v k k' ∧ edgeB w.unit.program k i = true`.

- [ ] **Step 1: Write `forthB` and its two lemmas**

```lean
/-- The `forth` scan. The Bool quantifiers range over list positions only;
this loses nothing against the unbounded `StatusBridge.forth` because `Corr`
bounds its own pair (`corr_lt`) and an edge bounds its attacker
(`(edgeB_faithful _).ranged`) — the recovery the `StatusBridge` docstring
prescribes, done once here instead of once per instance. -/
def forthB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Bool :=
  (List.range w.unit.program.args.length).all fun i =>
    (List.range v.unit.program.args.length).all fun j =>
      (List.range w.unit.program.args.length).all fun k =>
        !(corrB m lm w v i j && edgeB w.unit.program k i) ||
          (List.range v.unit.program.args.length).any fun k' =>
            corrB m lm w v k k' && edgeB v.unit.program k' j

theorem forthB_sound {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} (h : forthB m lm w v = true) :
    ∀ i j k, Corr m lm w v i j → edgeB w.unit.program k i = true →
      ∃ k', Corr m lm w v k k' ∧ edgeB v.unit.program k' j = true := by
  intro i j k hC hE
  have hi : i < w.unit.program.args.length := (corr_lt hC).1
  have hj : j < v.unit.program.args.length := (corr_lt hC).2
  have hk : k < w.unit.program.args.length :=
    ((edgeB_faithful w.unit.program).ranged k i hE).1
  unfold forthB at h
  simp only [List.all_eq_true, List.mem_range] at h
  have hcell := h i hi j hj k hk
  rw [Bool.or_eq_true] at hcell
  rcases hcell with hno | hyes
  · rw [Bool.not_eq_true', Bool.and_eq_false_iff] at hno
    rcases hno with hno | hno
    · rw [corrB_iff.mpr hC] at hno; exact Bool.noConfusion hno
    · rw [hE] at hno; exact Bool.noConfusion hno
  · obtain ⟨k', _, hkk'⟩ := List.any_eq_true.mp hyes
    rw [Bool.and_eq_true] at hkk'
    exact ⟨k', corrB_iff.mp hkk'.1, hkk'.2⟩

theorem forthB_complete {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam}
    (h : ∀ i j k, Corr m lm w v i j → edgeB w.unit.program k i = true →
      ∃ k', Corr m lm w v k k' ∧ edgeB v.unit.program k' j = true) :
    forthB m lm w v = true := by
  unfold forthB
  simp only [List.all_eq_true, List.mem_range]
  intro i _ j _ k _
  rw [Bool.or_eq_true]
  cases hguard : corrB m lm w v i j && edgeB w.unit.program k i with
  | false => left; rw [hguard]; rfl
  | true =>
    right
    rw [Bool.and_eq_true] at hguard
    obtain ⟨k', hC', hE'⟩ := h i j k (corrB_iff.mp hguard.1) hguard.2
    exact List.any_eq_true.mpr
      ⟨k', List.mem_range.mpr (corr_lt hC').2,
        Bool.and_eq_true.mpr ⟨corrB_iff.mpr hC', hE'⟩⟩
```

- [ ] **Step 2: Write `backB` and its two lemmas** (the mirror: the guard
edge is on the target program, the witness scan and its range bound are on
the source side — `(corr_lt hC').1` supplies the witness's in-rangeness)

```lean
/-- The `back` scan — `forthB` mirrored: guard edge on the target program,
witness scan over the source range. -/
def backB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Bool :=
  (List.range w.unit.program.args.length).all fun i =>
    (List.range v.unit.program.args.length).all fun j =>
      (List.range v.unit.program.args.length).all fun k' =>
        !(corrB m lm w v i j && edgeB v.unit.program k' j) ||
          (List.range w.unit.program.args.length).any fun k =>
            corrB m lm w v k k' && edgeB w.unit.program k i

theorem backB_sound {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} (h : backB m lm w v = true) :
    ∀ i j k', Corr m lm w v i j → edgeB v.unit.program k' j = true →
      ∃ k, Corr m lm w v k k' ∧ edgeB w.unit.program k i = true := by
  intro i j k' hC hE
  have hi : i < w.unit.program.args.length := (corr_lt hC).1
  have hj : j < v.unit.program.args.length := (corr_lt hC).2
  have hk' : k' < v.unit.program.args.length :=
    ((edgeB_faithful v.unit.program).ranged k' j hE).1
  unfold backB at h
  simp only [List.all_eq_true, List.mem_range] at h
  have hcell := h i hi j hj k' hk'
  rw [Bool.or_eq_true] at hcell
  rcases hcell with hno | hyes
  · rw [Bool.not_eq_true', Bool.and_eq_false_iff] at hno
    rcases hno with hno | hno
    · rw [corrB_iff.mpr hC] at hno; exact Bool.noConfusion hno
    · rw [hE] at hno; exact Bool.noConfusion hno
  · obtain ⟨k, _, hkk⟩ := List.any_eq_true.mp hyes
    rw [Bool.and_eq_true] at hkk
    exact ⟨k, corrB_iff.mp hkk.1, hkk.2⟩

theorem backB_complete {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam}
    (h : ∀ i j k', Corr m lm w v i j → edgeB v.unit.program k' j = true →
      ∃ k, Corr m lm w v k k' ∧ edgeB w.unit.program k i = true) :
    backB m lm w v = true := by
  unfold backB
  simp only [List.all_eq_true, List.mem_range]
  intro i _ j _ k' _
  rw [Bool.or_eq_true]
  cases hguard : corrB m lm w v i j && edgeB v.unit.program k' j with
  | false => left; rw [hguard]; rfl
  | true =>
    right
    rw [Bool.and_eq_true] at hguard
    obtain ⟨k, hC', hE'⟩ := h i j k' (corrB_iff.mp hguard.1) hguard.2
    exact List.any_eq_true.mpr
      ⟨k, List.mem_range.mpr (corr_lt hC').1,
        Bool.and_eq_true.mpr ⟨corrB_iff.mpr hC', hE'⟩⟩
```

- [ ] **Step 3: Build**

Run: `cd lean && lake build Lara.PW.Status`
Expected: success.

- [ ] **Step 4: Extend the AxCheck block**

```lean
#print axioms Lara.PW.forthB_sound
#print axioms Lara.PW.forthB_complete
#print axioms Lara.PW.backB_sound
#print axioms Lara.PW.backB_complete
```

- [ ] **Step 5: Verify audit**

Run: `cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh`
Expected: exit 0.

- [ ] **Step 6: Commit**

```bash
git add lean/Lara/PW/Status.lean lean/AxCheck.lean
git commit -m "theory(PW-T8): decide the attack clauses over the index ranges (#239)"
```

### Task 4: `statusBridgeB` with soundness, completeness, and the iff

**Files:**
- Modify: `lean/Lara/PW/Status.lean` (inside `section Checker`; also the
  module header comment)
- Modify: `lean/AxCheck.lean` (extend the issue-#239 block)
- Modify: `docs/paper-lean-name-map.md` (add one row in the PW-T8 block,
  after the `PW.StatusBridge.comp` row near line 1169)

**Interfaces:**
- Consumes: all of Tasks 1–3.
- Produces:
  `def statusBridgeB (m : SymMap) (lm : LeafId → LeafId) (w : World κ) (v : World lam) : Bool`,
  `theorem statusBridgeB_sound : statusBridgeB m lm w v = true → StatusBridge m lm w v`,
  `theorem statusBridgeB_complete : StatusBridge m lm w v → statusBridgeB m lm w v = true`,
  `theorem statusBridgeB_iff : statusBridgeB m lm w v = true ↔ StatusBridge m lm w v`.
  Task 5 consumes `statusBridgeB_sound` and `statusBridgeB_complete`.

- [ ] **Step 1: Write the checker and the three theorems**

```lean
/-- **The executable status-bridge checker** (issue #239): the four
`StatusBridge` clauses, each scanned over the finite index ranges of the two
compiled programs. -/
def statusBridgeB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Bool :=
  admitsB m lm w v && matchedB m lm w v && forthB m lm w v && backB m lm w v

/-- **Soundness.** A `true` scan is a `StatusBridge` — a conformance cell is
`statusBridgeB_sound (by decide)`. -/
theorem statusBridgeB_sound {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} (h : statusBridgeB m lm w v = true) :
    StatusBridge m lm w v := by
  unfold statusBridgeB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨ha, hm⟩, hf⟩, hb⟩ := h
  exact { admits := admitsB_iff.mp ha
        , matched := matchedB_iff.mp hm
        , forth := forthB_sound hf
        , back := backB_sound hb }

/-- **Completeness.** The range scan misses nothing: the `Prop` clauses' own
witnesses are in range (`corr_lt`), so a `StatusBridge` makes every scan
succeed. With soundness this also refutes: `statusBridgeB … = false` denies
`StatusBridge` by contraposition. -/
theorem statusBridgeB_complete {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} (h : StatusBridge m lm w v) :
    statusBridgeB m lm w v = true := by
  unfold statusBridgeB
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨admitsB_iff.mpr h.admits, matchedB_iff.mpr h.matched⟩,
    forthB_complete h.forth⟩, backB_complete h.back⟩

/-- The checker decides the T8 hypotheses exactly. -/
theorem statusBridgeB_iff {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} :
    statusBridgeB m lm w v = true ↔ StatusBridge m lm w v :=
  ⟨statusBridgeB_sound, statusBridgeB_complete⟩
```

- [ ] **Step 2: Update the module header of `Status.lean`**

In the header comment (`Status.lean:5-31`), change "Four sections" to "Five
sections" and append after the §4 item:

```
5. **The executable checker.** `statusBridgeB` scans the finite index ranges
   of the two compiled programs for `admits`, `matched`, `forth`, `back`;
   `statusBridgeB_sound`/`_complete`/`_iff` show the scan decides
   `StatusBridge` exactly (`forth`/`back` lose nothing to the range bound:
   `corr_lt` and `(edgeB_faithful _).ranged` pin every relevant index into
   range). A conformance cell is one `decide` (issue #239).
```

- [ ] **Step 3: Build**

Run: `cd lean && lake build Lara.PW.Status`
Expected: success.

- [ ] **Step 4: Extend the AxCheck block**

```lean
#print axioms Lara.PW.statusBridgeB_sound
#print axioms Lara.PW.statusBridgeB_complete
#print axioms Lara.PW.statusBridgeB_iff
```

- [ ] **Step 5: Add the name-map row**

In `docs/paper-lean-name-map.md`, after the `PW.StatusBridge.comp` row
(near line 1169), add:

```markdown
| Executable status-bridge checker over the finite compiled index ranges, sound and complete for the T8 hypotheses (a conformance cell is one `decide`) | `PW.statusBridgeB`, `PW.statusBridgeB_sound`, `PW.statusBridgeB_complete`, `PW.statusBridgeB_iff` | `Lara/PW/Status.lean` |
```

- [ ] **Step 6: Verify audit**

Run: `cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh`
Expected: exit 0.

- [ ] **Step 7: Commit**

```bash
git add lean/Lara/PW/Status.lean lean/AxCheck.lean docs/paper-lean-name-map.md
git commit -m "theory(PW-T8): executable StatusBridge checker, sound and complete (#239)"
```

### Task 5: One-`decide` conformance cells in the example module

**Files:**
- Modify: `lean/Lara/Examples/PWStatus.lean`
- Modify: `lean/AxCheck.lean` (example rows)

**Interfaces:**
- Consumes: `statusBridgeB_sound`, `statusBridgeB_complete` (Task 4);
  existing example worlds `wS1/wR1/wS2/wR2/wS3/wR3`, `symR`, `leafMapR`,
  `wT7src/wT7tgt` (from `Lara.Examples.PWStructural`).
- Produces: same theorem names and statements as today for
  `s1_r1_statusBridge`, `s2_r2_statusBridge`, `s3_r3_statusBridge`; new
  `t7_statusBridgeB_false`, `t7_not_statusBridge_of_checker`.

- [ ] **Step 1: Replace the three positive hand proofs**

Replace the whole `s1_r1_statusBridge` declaration (`PWStatus.lean:220-256`)
with:

```lean
/-- One argument each, no attacks. Discharged by the checker: the four
clauses are one finite scan (`statusBridgeB_sound`, issue #239). -/
theorem s1_r1_statusBridge : StatusBridge symR leafMapR wS1 wR1 :=
  statusBridgeB_sound (by decide)
```

Replace the whole `s2_r2_statusBridge` declaration (`PWStatus.lean:258-336`)
with:

```lean
/-- Two arguments each, one attack `1 → 0` on each side: `forth`/`back` are
exercised on a real compiled edge — by the checker's scan rather than the
former index-by-index argument. -/
theorem s2_r2_statusBridge : StatusBridge symR leafMapR wS2 wR2 :=
  statusBridgeB_sound (by decide)
```

Replace the whole `s3_r3_statusBridge` declaration (`PWStatus.lean:444-487`)
with (leave `s3_corr_diag` in place — it is registered in the name map and
independently documents that `Corr` is the diagonal here):

```lean
/-- Two arguments, two attacks each way (`{1→0, 0→1}` on both sides), `Corr`
the diagonal (`s3_corr_diag`): all of it inside one checker scan. -/
theorem s3_r3_statusBridge : StatusBridge symR leafMapR wS3 wR3 :=
  statusBridgeB_sound (by decide)
```

- [ ] **Step 2: Add the checker route to the negative T7 half**

After `t7_not_statusBridge_of_flip` (`PWStatus.lean:76-83`), add:

```lean
/-- The checker agrees that the T7 identity edge is no status bridge: the
scan comes back `false`… -/
theorem t7_statusBridgeB_false :
    statusBridgeB SymMap.id (fun l => l) wT7src wT7tgt = false := by decide

/-- …so completeness refutes by contraposition — a third route to the same
boundary fact, this one requiring no diagnosis of *which* clause fails
(that record stays with `t7_unmatched`). -/
theorem t7_not_statusBridge_of_checker :
    ¬ StatusBridge SymMap.id (fun l => l) wT7src wT7tgt := fun h => by
  have hb := statusBridgeB_complete h
  rw [t7_statusBridgeB_false] at hb
  exact Bool.noConfusion hb
```

- [ ] **Step 3: Update the module header**

In the header comment (`PWStatus.lean:1-30`), in the "Positive" paragraph,
change the sentence describing how `StatusBridge` is discharged to say the
three bridges are discharged by the executable checker
(`statusBridgeB_sound (by decide)`, issue #239), and note in the negative
paragraph that the checker's `false` verdict refutes via completeness.
Keep the closing line about `decide`/`native_decide` unchanged.

- [ ] **Step 4: Build the example module and the whole tree**

Run: `cd lean && lake build`
Expected: success. Risk to watch: `by decide` on `statusBridgeB` must
kernel-reduce through the `checkUnit … |>.toOption.get` programs — the same
reduction the file's existing `by decide` proofs (e.g.
`wS2.unit.program.args = …`) already perform, so this should be fast. If a
`decide` times out, the fallback is `decide +kernel` is *not* available;
instead split the four clauses (`admitsB_iff.mpr`, etc.) — but do not reach
for `native_decide` (banned here).

- [ ] **Step 5: Extend AxCheck's example rows**

After `#print axioms Lara.Examples.PW.Status.t7_forward_hom_insufficient`,
add:

```lean
#print axioms Lara.Examples.PW.Status.t7_statusBridgeB_false
#print axioms Lara.Examples.PW.Status.t7_not_statusBridge_of_checker
```

(The rows for `s1_r1_statusBridge`, `s2_r2_statusBridge`,
`s3_r3_statusBridge`, `s3_corr_diag` already exist and keep their names.)

- [ ] **Step 6: Verify audit**

Run: `cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh`
Expected: exit 0.

- [ ] **Step 7: Commit**

```bash
git add lean/Lara/Examples/PWStatus.lean lean/AxCheck.lean
git commit -m "theory(PW-T8): conformance cells are one decide (#239)"
```

### Task 6: Full gates, index comment, PR

**Files:**
- Modify: `lean/Lara.lean` (the PW-T8 index comment near lines 263–266)

- [ ] **Step 1: Update the library index comment**

In `lean/Lara.lean`, extend the PW-T8 comment block (before
`import Lara.PW.Status`) with one line noting the executable checker, e.g.
append to the existing sentence: `… — Lara.Examples.PWStatus.` becomes
`… — Lara.Examples.PWStatus. statusBridgeB decides the hypotheses over the
finite compiled index ranges (sound and complete), so a cell is one decide.`

- [ ] **Step 2: Run every CI gate locally**

```bash
cd lean
lake build
python3 ../scripts/check-axcheck-coverage.py AxCheck.lean $(find Lara -name '*.lean' | sort)
set -o pipefail
lake env lean AxCheck.lean | ../scripts/check-axioms.sh
```

Expected: all exit 0. Do not claim completion without this output.

- [ ] **Step 3: Commit and open the PR**

```bash
git add lean/Lara.lean
git commit -m "theory(PW-T8): index the checker in the library comment (#239)"
git push -u origin theory/pw-t8-statusbridge-checker
gh pr create --title "theory(PW-T8): executable StatusBridge checker with soundness and completeness (#239)" \
  --body "Closes #239. Adds statusBridgeB (finite-range scan of the four StatusBridge clauses) with statusBridgeB_sound / _complete / _iff in Lara/PW/Status.lean §5; the example module's three positive bridges become statusBridgeB_sound (by decide) and the T7 negative cell gains a checker route. AxCheck rows and a paper-lean-name-map row included. Lean only; no corpus or freeze impact."
```

- [ ] **Step 4: Post-land bookkeeping**

This session introduces a mechanization feature, so per CLAUDE.md run
`/research-manager` at the end of the implementing session, and delete this
plan file in the landing PR (executed plans do not stay in `plans/`; the
durable record is the name-map row and the module headers).

## Self-review notes

- Spec coverage: signature, scan shape, soundness, completeness ("if cheap"
  — shown cheap), `Presents`/`crossCompare` style (decider + adequacy
  lemmas), `DecidableEq SupportTerm` dependency, `Corr`-over-`List.range`
  Bool translation, no corpus/freeze impact — all mapped to Tasks 1–5.
- Type consistency: `corrB_iff`, `admitsB_iff`, `matchedB_iff`,
  `forthB_sound/_complete`, `backB_sound/_complete` are consumed in Task 4
  with exactly the statements produced in Tasks 1–3; Task 5 uses
  `statusBridgeB_sound`/`_complete` as produced in Task 4.
- Known soft spots (expected to need toolchain-level tweaks, not design
  changes): core lemma spellings (`Bool.and_eq_false_iff`,
  `Bool.not_eq_true'`, `of_decide_eq_true`), the `simp` closing of
  `corrB_iff`, and whether `cases hguard : …` needs `Bool.not_eq_true'`
  massaging in the `_complete` proofs.
