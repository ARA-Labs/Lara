# PW-T8 Executable StatusBridge Checker Implementation Plan (issue #239)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add `statusBridgeB : SymMap → (LeafId → LeafId) → World κ → World lam → Bool`, a decider for the `StatusBridge` hypotheses that scans the finite index ranges of the two compiled programs, with `statusBridgeB_sound` (and completeness, which turns out cheap), so every future PW-T8 conformance cell is one `decide`.

**Architecture:** One new section (§5) in `lean/Lara/PW/Status.lean`: a
per-index-pair decider `corrB` for `Corr`; a shared `transportsB` helper on
which the two totality deciders `admitsB`/`matchedB` are symmetric; one
generic directed scan `bisimScanB` over abstract `Nat → Nat → Bool`
relations, proved sound and complete once and instantiated twice as
`forthB`/`backB`; and the conjunction `statusBridgeB` with
`_sound`/`_complete`/`_iff`. A small §2 edit names the `matched` clause as
`def Matched`, mirroring `Admits`. `Lara/Examples/PWStatus.lean` then
replaces its three index-by-index positive `StatusBridge` proofs with
`statusBridgeB_sound (by decide)` and gains four clause-level cells on the
negative T7 side. AxCheck rows and a `docs/paper-lean-name-map.md` row land
with the theorems.

**Feasibility: measured, not assumed.** The six definitions below were
prototyped verbatim against the real example worlds before this plan was
approved. All four proposed `decide` cells elaborate — three `true`, T7
`false` — in **0.58s total, with no `maxRecDepth` bump**, and flipping the
T7 cell to `= true` correctly errors. The nested scans do *not* blow up
re-reducing `checkUnit … |>.toOption.get`. Kernel-reduction cost is a settled
question, not a risk to manage.

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
- Modify: `lean/Lara/PW/Status.lean` — **§2** (name the `matched` clause) and
  `section Checker` (after `corrB_iff`)
- Modify: `lean/AxCheck.lean` (extend the issue-#239 block)

**Interfaces:**
- Consumes: `Admits` (`PW/Structural.lean:465`), `trSupport`,
  `DecidableEq SupportTerm`.
- Produces: `def Matched`, `def transportsB`,
  `def admitsB (m : SymMap) (lm : LeafId → LeafId) (w : World κ) (v : World lam) : Bool`,
  `theorem admitsB_iff : admitsB m lm w v = true ↔ Admits m lm w v`,
  `def matchedB (m : SymMap) (lm : LeafId → LeafId) (w : World κ) (v : World lam) : Bool`,
  `theorem matchedB_iff : matchedB m lm w v = true ↔ Matched m lm w v`.
  Task 4 consumes all four lemmas.

- [ ] **Step 1: Name the `matched` clause (§2)**

`Admits` is a named `def` (`PW/Structural.lean:465`) but `matched` is an
anonymous field type, so its `∀∃` statement would have to be retyped in
`matchedB_iff`. Name it, next to `Corr` in §2:

```lean
/-- Right-totality of the translation on program arguments: every target
argument *is* a transport. The converse of T6's `Admits`, and the clause the
T7 target violates at `leaf l2` (`Lara.Examples.PW.Status.t7_unmatched`). -/
def Matched (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Prop :=
  ∀ t', t' ∈ v.unit.program.args →
    ∃ t, t ∈ w.unit.program.args ∧ trSupport m lm t = some t'
```

and restate the `StatusBridge` field as `matched : Matched m lm w v`.

**Build-check point (do not skip):** this edits a structure that #193/#240
already build on. `Matched` unfolds definitionally, so `h.matched t' ht'`
should still elaborate everywhere, but `StatusBridge.bisim`,
`claimSupport_corr` and `StatusBridge.comp` are the three consumers to watch.
If any breaks, `unfold Matched` at the use site is the fix — **not** reverting
the field, and **not** weakening any statement.

- [ ] **Step 2: Write the shared helper and the two totality deciders**

One idiom for "does this term transport to that one", so both clauses and
both proofs have the same shape:

```lean
/-- The transport test both totality clauses quantify over. -/
def transportsB (m : SymMap) (lm : LeafId → LeafId)
    (t t' : SupportTerm) : Bool :=
  trSupport m lm t == some t'

theorem transportsB_iff {m : SymMap} {lm : LeafId → LeafId}
    {t t' : SupportTerm} :
    transportsB m lm t t' = true ↔ trSupport m lm t = some t' :=
  beq_iff_eq

/-- Decides T6's `Admits`: every source argument transports to some target
argument. -/
def admitsB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Bool :=
  w.unit.program.args.all fun t =>
    v.unit.program.args.any fun t' => transportsB m lm t t'

/-- Decides `Matched` — `admitsB` with the two argument lists swapped. -/
def matchedB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Bool :=
  v.unit.program.args.all fun t' =>
    w.unit.program.args.any fun t => transportsB m lm t t'

theorem admitsB_iff {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} :
    admitsB m lm w v = true ↔ Admits m lm w v := by
  unfold admitsB Admits
  rw [List.all_eq_true]
  constructor
  · intro h t ht
    obtain ⟨t', ht', htr⟩ := List.any_eq_true.mp (h t ht)
    exact ⟨t', transportsB_iff.mp htr, ht'⟩
  · intro h t ht
    obtain ⟨t', htr, hmem⟩ := h t ht
    exact List.any_eq_true.mpr ⟨t', hmem, transportsB_iff.mpr htr⟩

theorem matchedB_iff {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} :
    matchedB m lm w v = true ↔ Matched m lm w v := by
  unfold matchedB Matched
  rw [List.all_eq_true]
  constructor
  · intro h t' ht'
    obtain ⟨t, ht, htr⟩ := List.any_eq_true.mp (h t' ht')
    exact ⟨t, ht, transportsB_iff.mp htr⟩
  · intro h t' ht'
    obtain ⟨t, ht, htr⟩ := h t' ht'
    exact List.any_eq_true.mpr ⟨t, ht, transportsB_iff.mpr htr⟩
```

Note the evaluation-order tradeoff, taken deliberately: phrasing `admitsB`
as `all/any` recomputes `trSupport` once per *pair* rather than once per
source argument. The 0.58s measurement says that is free at these sizes, and
one idiom for one concept is worth more than the saved reductions.

- [ ] **Step 3: Build the whole tree**

Run: `cd lean && lake build`
Expected: success. Build the **whole tree**, not just `Lara.PW.Status` — the
§2 field rename can only surface in the downstream consumers.

- [ ] **Step 4: Extend the AxCheck block**

```lean
#print axioms Lara.PW.transportsB_iff
#print axioms Lara.PW.admitsB_iff
#print axioms Lara.PW.matchedB_iff
```

- [ ] **Step 5: Verify audit**

Run: `cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh`
Expected: exit 0.

- [ ] **Step 6: Commit**

```bash
git add lean/Lara/PW/Status.lean lean/AxCheck.lean
git commit -m "theory(PW-T8): name Matched and decide the two totality clauses (#239)"
```

### Task 3: `bisimScanB` — one directed scan, instantiated as `forthB`/`backB`

`StatusBridge.back` is `StatusBridge.forth` with the two sides swapped, so
the scan, its soundness argument, and its completeness argument are written
**once** over abstract `Nat → Nat → Bool` relations and instantiated at the
two orientations. Writing them out twice would duplicate ~40 lines of
mirrored tactic proof.

**The scan geometry** (this diagram goes in the plan *and* verbatim in the
`bisimScanB` docstring — it is the whole reason the bounded scan loses
nothing):

```
source program w                target program v
  args 0..n-1                     args 0..m-1

        i ───────── Corr ──────────► j
        ▲                            ▲
        │ edgeB w k i                │ edgeB v k' j
        │                            │
        k ───────── Corr ──────────► k'   (∃ k', forth)

  bound     source of in-rangeness
  ─────────────────────────────────────────────────
  i < n     (corr_lt hC).1
  j < m     (corr_lt hC).2
  k < n     ((edgeB_faithful w).ranged k i hE).1
  k' < m    (corr_lt hC').2      ← completeness witness

  backB = this diagram with the two columns swapped.
```

**Files:**
- Modify: `lean/Lara/PW/Status.lean` (inside `section Checker`, after
  `matchedB_iff`)
- Modify: `lean/AxCheck.lean` (extend the issue-#239 block)

**Interfaces:**
- Consumes: `corrB`/`corrB_iff` (Task 1), `corr_lt`, `Compile.edgeB`,
  `Compile.edgeB_faithful` (`Compile.lean:617`, `:650`).
- Produces: `def bisimScanB`, `theorem bisimScanB_sound`,
  `theorem bisimScanB_complete`, `theorem corrB_lt`, and the two
  instantiations `def forthB` / `def backB` with
  `forthB_sound`/`forthB_complete`/`backB_sound`/`backB_complete` whose
  statements are **exactly** the `StatusBridge.forth`/`.back` field types.
  Those four statements are the contract and must not drift.

- [ ] **Step 1: The range bound for `corrB`**

```lean
/-- A `true` `corrB` cell is in range on both sides — `corr_lt` through the
decider. -/
theorem corrB_lt {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} {i j : Nat}
    (h : corrB m lm w v i j = true) :
    i < w.unit.program.args.length ∧ j < v.unit.program.args.length :=
  corr_lt (corrB_iff.mp h)
```

- [ ] **Step 2: The generic scan and its two lemmas**

```lean
/-- **One directed bisimulation scan**, over abstract index relations.

    source (n)                      target (m)

        i ───────── corr ──────────► j
        ▲                            ▲
        │ eSrc k i                   │ eTgt k' j
        │                            │
        k ───────── corr ──────────► k'   (∃ k')

The scan is bounded but loses nothing: `hcorr` says a `corr` cell bounds its
own pair, `hsrc` says an edge bounds its attacker, and the completeness
witness is bounded by `hcorr` at the witnessing pair. `forthB` is this at
`(corrB, edgeB w, edgeB v, n, m)`; `backB` is this at the swap. -/
def bisimScanB (corr eSrc eTgt : Nat → Nat → Bool) (n m : Nat) : Bool :=
  (List.range n).all fun i =>
    (List.range m).all fun j =>
      (List.range n).all fun k =>
        !(corr i j && eSrc k i) ||
          (List.range m).any fun k' => corr k k' && eTgt k' j

theorem bisimScanB_sound {corr eSrc eTgt : Nat → Nat → Bool} {n m : Nat}
    (hcorr : ∀ i j, corr i j = true → i < n ∧ j < m)
    (hsrc : ∀ k i, eSrc k i = true → k < n)
    (h : bisimScanB corr eSrc eTgt n m = true) :
    ∀ i j k, corr i j = true → eSrc k i = true →
      ∃ k', corr k k' = true ∧ eTgt k' j = true := by
  intro i j k hC hE
  unfold bisimScanB at h
  simp only [List.all_eq_true, List.mem_range] at h
  have hcell := h i (hcorr i j hC).1 j (hcorr i j hC).2 k (hsrc k i hE)
  rw [Bool.or_eq_true] at hcell
  rcases hcell with hno | hyes
  · rw [Bool.not_eq_true', Bool.and_eq_false_iff] at hno
    rcases hno with hno | hno
    · rw [hC] at hno; exact Bool.noConfusion hno
    · rw [hE] at hno; exact Bool.noConfusion hno
  · obtain ⟨k', _, hkk'⟩ := List.any_eq_true.mp hyes
    rw [Bool.and_eq_true] at hkk'
    exact ⟨k', hkk'.1, hkk'.2⟩

theorem bisimScanB_complete {corr eSrc eTgt : Nat → Nat → Bool} {n m : Nat}
    (hcorr : ∀ i j, corr i j = true → i < n ∧ j < m)
    (h : ∀ i j k, corr i j = true → eSrc k i = true →
      ∃ k', corr k k' = true ∧ eTgt k' j = true) :
    bisimScanB corr eSrc eTgt n m = true := by
  unfold bisimScanB
  simp only [List.all_eq_true, List.mem_range]
  intro i _ j _ k _
  rw [Bool.or_eq_true]
  cases hguard : corr i j && eSrc k i with
  | false => left; rw [hguard]; rfl
  | true =>
    right
    rw [Bool.and_eq_true] at hguard
    obtain ⟨k', hC', hE'⟩ := h i j k hguard.1 hguard.2
    exact List.any_eq_true.mpr
      ⟨k', List.mem_range.mpr (hcorr k k' hC').2,
        Bool.and_eq_true.mpr ⟨hC', hE'⟩⟩
```

- [ ] **Step 3: Instantiate as `forthB` and its two lemmas**

```lean
/-- The `forth` scan: `bisimScanB` at the source-to-target orientation. -/
def forthB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Bool :=
  bisimScanB (corrB m lm w v) (edgeB w.unit.program) (edgeB v.unit.program)
    w.unit.program.args.length v.unit.program.args.length

theorem forthB_sound {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} (h : forthB m lm w v = true) :
    ∀ i j k, Corr m lm w v i j → edgeB w.unit.program k i = true →
      ∃ k', Corr m lm w v k k' ∧ edgeB v.unit.program k' j = true := by
  intro i j k hC hE
  obtain ⟨k', hC', hE'⟩ :=
    bisimScanB_sound (fun _ _ => corrB_lt)
      (fun k i hk => ((edgeB_faithful w.unit.program).ranged k i hk).1)
      h i j k (corrB_iff.mpr hC) hE
  exact ⟨k', corrB_iff.mp hC', hE'⟩

theorem forthB_complete {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam}
    (h : ∀ i j k, Corr m lm w v i j → edgeB w.unit.program k i = true →
      ∃ k', Corr m lm w v k k' ∧ edgeB v.unit.program k' j = true) :
    forthB m lm w v = true :=
  bisimScanB_complete (fun _ _ => corrB_lt) fun i j k hC hE => by
    obtain ⟨k', hC', hE'⟩ := h i j k (corrB_iff.mp hC) hE
    exact ⟨k', corrB_iff.mpr hC', hE'⟩
```

- [ ] **Step 4: Instantiate as `backB` — the same scan at the swap**

`backB` is `bisimScanB` with the two *columns* exchanged: the correlation is
transposed (`fun j i => corrB … i j`), the guard edge moves to the target
program, the witness scan to the source. No second proof — the two lemmas are
`bisimScanB_sound`/`_complete` applied at the swapped instance, with the
`hcorr` pair reversed by `⟨(corrB_lt h).2, (corrB_lt h).1⟩`.

```lean
/-- The `back` scan: `bisimScanB` at the transposed orientation. -/
def backB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Bool :=
  bisimScanB (fun j i => corrB m lm w v i j)
    (edgeB v.unit.program) (edgeB w.unit.program)
    v.unit.program.args.length w.unit.program.args.length

theorem backB_sound {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} (h : backB m lm w v = true) :
    ∀ i j k', Corr m lm w v i j → edgeB v.unit.program k' j = true →
      ∃ k, Corr m lm w v k k' ∧ edgeB w.unit.program k i = true := by
  intro i j k' hC hE
  obtain ⟨k, hC', hE'⟩ :=
    bisimScanB_sound (fun _ _ hb => ⟨(corrB_lt hb).2, (corrB_lt hb).1⟩)
      (fun k a hk => ((edgeB_faithful v.unit.program).ranged k a hk).1)
      h j i k' (corrB_iff.mpr hC) hE
  exact ⟨k, corrB_iff.mp hC', hE'⟩

theorem backB_complete {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam}
    (h : ∀ i j k', Corr m lm w v i j → edgeB v.unit.program k' j = true →
      ∃ k, Corr m lm w v k k' ∧ edgeB w.unit.program k i = true) :
    backB m lm w v = true :=
  bisimScanB_complete (fun _ _ hb => ⟨(corrB_lt hb).2, (corrB_lt hb).1⟩)
    fun j i k' hC hE => by
      obtain ⟨k, hC', hE'⟩ := h i j k' (corrB_iff.mp hC) hE
      exact ⟨k, corrB_iff.mpr hC', hE'⟩
```

- [ ] **Step 5: Build**

Run: `cd lean && lake build Lara.PW.Status`
Expected: success.

- [ ] **Step 6: Extend the AxCheck block**

```lean
#print axioms Lara.PW.corrB_lt
#print axioms Lara.PW.bisimScanB_sound
#print axioms Lara.PW.bisimScanB_complete
#print axioms Lara.PW.forthB_sound
#print axioms Lara.PW.forthB_complete
#print axioms Lara.PW.backB_sound
#print axioms Lara.PW.backB_complete
```

- [ ] **Step 7: Verify audit**

Run: `cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh`
Expected: exit 0.

- [ ] **Step 8: Commit**

```bash
git add lean/Lara/PW/Status.lean lean/AxCheck.lean
git commit -m "theory(PW-T8): one bisimulation scan, instantiated forth and back (#239)"
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
   of the two compiled programs for `admits`, `matched`, `forth`, `back`.
   `admitsB`/`matchedB` are one `transportsB` test at the two argument
   orders; `forthB`/`backB` are one generic `bisimScanB` at the two
   orientations, so the scan is written and proved once.
   `statusBridgeB_sound`/`_complete`/`_iff` show it decides `StatusBridge`
   exactly (`forth`/`back` lose nothing to the range bound: `corr_lt` and
   `(edgeB_faithful _).ranged` pin every relevant index into range). A
   conformance cell is one `decide` (issue #239).
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
| Right-totality of the translation on program arguments (the `matched` clause, named) | `PW.Matched` | `Lara/PW/Status.lean` |
| One directed bisimulation scan over abstract index relations, sound and complete under a correlation bound and an edge-range bound; `forth`/`back` are its two orientations | `PW.bisimScanB`, `PW.bisimScanB_sound`, `PW.bisimScanB_complete` | `Lara/PW/Status.lean` |
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
  `t7_statusBridgeB_false`, `t7_not_statusBridge_of_checker`,
  `t7_matchedB_false`, `t7_admits_forth_hold`, `forthB_discriminates`.

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

A bare `statusBridgeB … = false` says the conjunction fails but not *which*
clause, so a later semantic drift in one clause would still satisfy it. Pin
the verdict clause by clause instead. **Every cell below was evaluated
against the real worlds before this plan was approved and holds as stated —
no new worlds are required.**

After `t7_not_statusBridge_of_flip` (`PWStatus.lean:76-83`), add:

```lean
/-- The checker agrees that the T7 identity edge is no status bridge: the
scan comes back `false`… -/
theorem t7_statusBridgeB_false :
    statusBridgeB SymMap.id (fun l => l) wT7src wT7tgt = false := by decide

/-- …so completeness refutes by contraposition — a third route to the same
boundary fact. -/
theorem t7_not_statusBridge_of_checker :
    ¬ StatusBridge SymMap.id (fun l => l) wT7src wT7tgt := fun h => by
  have hb := statusBridgeB_complete h
  rw [t7_statusBridgeB_false] at hb
  exact Bool.noConfusion hb

/-- The checker's verdict is `matched`, clause for clause with the hand
diagnosis at `t7_unmatched`. -/
theorem t7_matchedB_false :
    matchedB SymMap.id (fun l => l) wT7src wT7tgt = false := by decide

/-- …and it reproduces `t7_forward_hom_insufficient` from the other side:
T7 *is* a forward homomorphism — `admits` and `forth` both hold. The scan
therefore fails exactly where the hand proof says it must, and nowhere else
on the forward side. (The scan additionally reports `backB = false`, which
the hand proofs never recorded.) -/
theorem t7_admits_forth_hold :
    admitsB SymMap.id (fun l => l) wT7src wT7tgt = true ∧
      forthB SymMap.id (fun l => l) wT7src wT7tgt = true := by decide
```

Then, so the `forth` scan has a `false` verdict on record — without it
nothing documents that the hardest clause discriminates — add after
`s3_r3_statusBridge`:

```lean
/-- **The `forth` scan discriminates.** At this deliberately mismatched pair
`admits` and `back` both hold and only `forth` fails: `wS3`'s attack has no
counterpart across the correlation into `wR2`. Guards against a `forthB`
that silently degenerates to a vacuous scan. -/
theorem forthB_discriminates :
    admitsB symR leafMapR wS3 wR2 = true ∧
      backB symR leafMapR wS3 wR2 = true ∧
        forthB symR leafMapR wS3 wR2 = false := by decide
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
Expected: success.

**Measured, not predicted.** These cells were prototyped verbatim against the
real worlds: all four `statusBridgeB` cells plus the clause-level cells above
elaborate in **0.58s total with no `maxRecDepth` bump**. The nested scans do
not blow up re-reducing `checkUnit … |>.toOption.get`. If a `decide` ever
does become slow at a larger conformance cell, the ladder is, in order:
`decide +kernel` (**available** on this toolchain — `v4.32.0`; an earlier
draft of this plan wrongly claimed it was not), then splitting the four
clauses through `admitsB_iff.mpr` etc., then a `simp only` normalising
`args` via the already-decided list equalities. `native_decide` stays banned
here regardless.

- [ ] **Step 5: Extend AxCheck's example rows**

After `#print axioms Lara.Examples.PW.Status.t7_forward_hom_insufficient`,
add:

```lean
#print axioms Lara.Examples.PW.Status.t7_statusBridgeB_false
#print axioms Lara.Examples.PW.Status.t7_not_statusBridge_of_checker
#print axioms Lara.Examples.PW.Status.t7_matchedB_false
#print axioms Lara.Examples.PW.Status.t7_admits_forth_hold
#print axioms Lara.Examples.PW.Status.forthB_discriminates
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

- [ ] **Step 3: Delete this plan file — *before* opening the PR**

CLAUDE.md: executed plans do not stay in `plans/`. The durable record is the
name-map rows, the §5 docstrings (including the scan-geometry diagram), and
the module headers — all of which land in Tasks 3–5. Delete the plan in the
same commit as the index update so the PR is correct on its first push, not
patched afterwards:

```bash
cd /home/yfhe/ara/lara
git rm plans/2026-09-05-pw-t8-statusbridge-checker.md
git add lean/Lara.lean
git commit -m "theory(PW-T8): index the checker and retire the plan (#239)"
```

- [ ] **Step 4: Push and open the PR**

```bash
git push -u origin theory/pw-t8-statusbridge-checker
gh pr create --title "theory(PW-T8): executable StatusBridge checker with soundness and completeness (#239)" \
  --body "Closes #239. Adds statusBridgeB (finite-range scan of the four StatusBridge clauses) with statusBridgeB_sound / _complete / _iff in Lara/PW/Status.lean §5. forth/back are one generic bisimScanB proved sound and complete once and instantiated at both orientations; admitsB/matchedB share one transportsB test; the matched clause is named as PW.Matched, mirroring Admits. The example module's three positive bridges become statusBridgeB_sound (by decide) and the T7 negative half gains clause-level cells (matchedB = false, admits and forth hold) plus a forth-discriminates cell. AxCheck rows and paper-lean-name-map rows included. Lean only; no corpus or freeze impact."
```

- [ ] **Step 5: Post-land bookkeeping**

This session introduces a mechanization feature, so per CLAUDE.md run
`/research-manager` at the end of the implementing session.

**Do not rely on CI to catch a miss here.** Issue #225 records that CI has
not run since 2026-08-25 (both jobs fail in ~3s with zero steps executed).
Until that is fixed, Step 2's local gate run is the *only* gate — treat its
output as required evidence, not a formality.

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
  `Bool.not_eq_true'`), the `simp` closing of `corrB_iff`, and whether
  `cases hguard : …` needs `Bool.not_eq_true'` massaging in
  `bisimScanB_complete`. The `of_decide_eq_true` dependency is gone — the
  shared `transportsB` idiom removed the `decide (_ ∈ _)` branch.
- Verified during eng review, not assumed: `Faithful.ranged`
  (`Compile.lean:607`) has the shape the scans consume; `corr_lt`
  (`Status.lean:174`) bounds both components; `check-axcheck-coverage.py:24`
  matches only `theorem|lemma`, so the eight new `def`s correctly need no
  `#print axioms` row; `SupportTerm.decEq` (`Support.lean:250`) is structural,
  not well-founded, so it kernel-reduces.

## What already exists (reused, not rebuilt)

| Sub-problem | Existing code | Treatment |
|---|---|---|
| Decider + adequacy-lemma pattern | `Compile.edgeB` / `edgeB_faithful` (`Compile.lean:617`, `:649`) | Pattern followed; `edgeB` consumed directly |
| Attacker index in-rangeness | `Faithful.ranged` (`Compile.lean:607`) | Consumed verbatim as `bisimScanB`'s `hsrc` |
| Correlated-pair in-rangeness | `corr_lt` (`Status.lean:174`) | Consumed via `corrB_lt` as `bisimScanB`'s `hcorr` |
| Structural term equality | `instance : DecidableEq SupportTerm` (`Support.lean:353`) | Consumed by `transportsB`'s `==` |
| Executable-layer precedent | T5 `crossCompare` / `Presents` (`PW/Compare.lean`) | Style model named by issue #239 |
| Left-totality judgment | `Admits` (`PW/Structural.lean:465`) | Consumed; `Matched` added to match it |

Nothing here is reimplemented. Every quantifier bound the scans need already
existed as a lemma; the plan's contribution is applying them once centrally
instead of once per conformance cell.

## NOT in scope (considered, deliberately deferred)

- **Deriving the compiled attack correspondence from declared-attack
  transport.** `StatusBridge.forth`/`back` stay index-level conditions on
  `Compile.edgeB`. Tracked in **issue #238**; needs `trSupport` to commute
  with `Attack.subterm`, `Compile.Contains`, `Compile.AttackOcc` and
  `coveredB` — an `Erase.lean`-scale lemma set. Not this PR.
- **Retiring the hand-proved T7 negative half.** `t7_unmatched`,
  `t7_forth`, `t7_forward_hom_insufficient` stay. They state *why* T7 fails
  in the source language's own terms; the checker cells added in Task 5 Step
  2 now cross-check them but do not replace them.
- **`s3_corr_diag`.** Stays. Registered in the name map and independently
  documents that `Corr` is the diagonal at s3.
- **A `Decidable (StatusBridge …)` instance.** Rejected: `StatusBridge`
  quantifies unboundedly over `Nat`, so it is not decidable as stated. A
  `Bool` checker with a sound/complete pair is the correct shape, and matches
  `edgeB`/`edgeB_faithful`.
- **Fixing CI (#225).** Out of this branch's scope; flagged in Task 6 Step 5
  so the local gate run is not mistaken for a formality.

## Failure modes for the new code paths

| Failure mode | Covered by a test? | Guarded by a proof? | Visible or silent? |
|---|---|---|---|
| `forthB`/`backB` degenerate to a vacuous scan (bad range, always `true`) | Yes — `forthB_discriminates` (Task 5 Step 2) | Yes — `bisimScanB_sound` is unprovable if the scan is vacuous | Visible: build fails |
| `statusBridgeB` returns `false` for the wrong reason (clause drift) | Yes — `t7_matchedB_false` + `t7_admits_forth_hold` pin the clause | Partly | Visible: `decide` errors |
| §2 `Matched` rename breaks a downstream #193/#240 proof | Yes — Task 2 Step 3 builds the whole tree, not one module | n/a | Visible: build fails |
| A new theorem lands without an AxCheck row | Yes — `check-axcheck-coverage.py` in Task 6 Step 2 | n/a | Visible **only if run locally** — CI is down (#225) |
| An axiom outside the trio leaks in | Yes — `check-axioms.sh` in Task 6 Step 2 | n/a | Same caveat as above |
| `decide` becomes slow at a future larger cell | Not a test; measured at 0.58s today | n/a | Visible: build slows, ladder in Task 5 Step 4 |

**Critical gaps: none.** Every failure mode above has both a check and a
proof-level or build-level guard. The one caveat is that two of the checks
currently only fire locally, which Task 6 Step 5 calls out explicitly.

## Worktree parallelization strategy

**Sequential implementation, no parallelization opportunity.** Tasks 1 → 2 →
3 → 4 → 5 → 6 form a strict dependency chain, and Tasks 1–4 all edit the same
file (`lean/Lara/PW/Status.lean`). Task 5 depends on Task 4's
`statusBridgeB_sound`/`_complete`; Task 6 depends on everything. Splitting
across worktrees would produce guaranteed conflicts in `Status.lean` and
`AxCheck.lean` for zero wall-clock gain.

## Implementation Tasks

Synthesized from the engineering review. Each derives from a specific finding.

- [ ] **T1 (P1, human: ~3h / CC: ~20min)** — `PW/Status.lean` — Factor `forthB`/`backB` into one `bisimScanB` proved sound and complete once
  - Surfaced by: Architecture issue 1 — two ~9-line defs and four ~20-line tactic proofs that are the same argument with the sides swapped
  - Files: `lean/Lara/PW/Status.lean`, `lean/AxCheck.lean`
  - Verify: `cd lean && lake build Lara.PW.Status`
- [ ] **T2 (P2, human: ~1h / CC: ~10min)** — `PW/Status.lean` — Name the `matched` clause as `def Matched`, mirroring `Admits`
  - Surfaced by: Architecture issue 2 — `Admits` is a named def at `Structural.lean:465`; `matched` is anonymous, so its ∀∃ gets retyped in `matchedB_iff`
  - Files: `lean/Lara/PW/Status.lean` (§2 and §5), `docs/paper-lean-name-map.md`
  - Verify: `cd lean && lake build` (whole tree — the rename can only surface downstream)
- [ ] **T3 (P2, human: ~15min / CC: ~3min)** — `Task 6` — Move the plan-file deletion into the commit before `gh pr create`
  - Surfaced by: Architecture issue 3 — Step 4 said "delete in the landing PR" with no commit or push step, so the plan ships inside `plans/`
  - Files: `plans/2026-09-05-pw-t8-statusbridge-checker.md` (deletion)
  - Verify: `git show --stat HEAD` lists the deletion before the PR is opened
- [ ] **T4 (P2, human: ~45min / CC: ~8min)** — `PW/Status.lean` — Unify `admitsB`/`matchedB` on one `transportsB` helper
  - Surfaced by: Code Quality issue 4 — two idioms (`match … decide (∈)` vs `any … ==`) for one concept
  - Files: `lean/Lara/PW/Status.lean`, `lean/AxCheck.lean`
  - Verify: `cd lean && lake build Lara.PW.Status`
- [ ] **T5 (P2, human: ~30min / CC: ~5min)** — `PW/Status.lean` — Add the scan-geometry ASCII diagram to the plan and the `bisimScanB` docstring
  - Surfaced by: Code Quality issue 5 — which bound comes from `corr_lt` vs `.ranged` is the crux of completeness and was prose-only
  - Files: `lean/Lara/PW/Status.lean`
  - Verify: read the `bisimScanB` docstring; the four bounds must match the four hypotheses actually used
- [ ] **T6 (P2, human: ~1h / CC: ~10min)** — `Examples/PWStatus.lean` — Add the four clause-level negative cells
  - Surfaced by: Test review — `forthB`/`backB` had no `false` verdict on record and `t7_statusBridgeB_false` did not say which clause failed
  - Files: `lean/Lara/Examples/PWStatus.lean`, `lean/AxCheck.lean`
  - Verify: `cd lean && lake build Lara.Examples.PWStatus` — all cells verified to hold before approval
- [ ] **T7 (P3, human: ~10min / CC: ~2min)** — `Task 5` — Correct the `decide +kernel` fallback claim
  - Surfaced by: Code Quality — plan asserted `decide +kernel` is unavailable; it compiles on `leanprover/lean4:v4.32.0`
  - Files: `plans/…` (Task 5 Step 4 text, folded into `Status.lean` guidance)
  - Verify: `lean -e 'example : (2+2:Nat) = 4 := by decide +kernel'` compiles

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | `/codex review` | Independent 2nd opinion | 0 | — | — |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | CLEAR | 6 issues, 0 critical gaps |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | n/a (Lean proof library) |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | — |

**Findings by section:** Architecture 3 (forth/back duplication; unnamed
`matched` clause; plan-deletion sequencing) · Code Quality 2 (split transport
idiom; missing scan-geometry diagram) · Tests 1 (no `false` verdict on record
for `forthB`/`backB`; T7 negative did not pin the failing clause) ·
Performance 0. All 6 accepted and folded into Tasks 2–6 above.

**Empirical verification (this review did not argue, it measured):** the six
proposed definitions were prototyped verbatim against the real example
worlds. All four `decide` cells elaborate in **0.58s, no `maxRecDepth`
bump**; flipping the T7 cell to `= true` correctly errors. A cross-pair sweep
then located every negative test cell the plan was missing *using only worlds
already in the module*, and confirmed the checker independently reproduces
`t7_forward_hom_insufficient` and `t7_unmatched` clause by clause. Two plan
claims were checked and one was wrong: `decide +kernel` **is** available on
`leanprover/lean4:v4.32.0` (corrected in Task 5 Step 4).

**Standing risk, not this branch's to fix:** issue #225 — CI has not run
since 2026-08-25. The AxCheck coverage gate and the axiom audit currently
fire only when run locally (Task 6 Step 2).

**OUTSIDE VOICE:** not run. Codex returned `ERROR: You've hit your usage
limit … try again at Sep 8th, 2026`; the Claude-subagent fallback was
declined by the user. No cross-model check on the `bisimScanB` abstraction —
re-runnable later with `/codex consult`.

**VERDICT:** ENG CLEARED — ready to implement.

NO UNRESOLVED DECISIONS
