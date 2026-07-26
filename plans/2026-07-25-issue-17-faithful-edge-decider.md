# Issue #17 Faithful Edge Decider Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use `superpowers:subagent-driven-development` (recommended) or `superpowers:executing-plans` to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Construct the executable compiled-edge relation directly from every `Compile.CheckedProgram`, prove it `Compile.Faithful`, and expose the source-to-grounded result-6 bridge without a caller-supplied oracle.

**Architecture:** Keep `Compile.Edge` as the frozen relational specification and keep the generic `toAF`/`Faithful` theorems available. Add a structural Boolean containment test, a Boolean closure test for each declared attack, and an indexed `edgeB P i j` that retrieves both arguments from `P.args` and scans `P.atts`. Prove the algorithm agrees with `Edge` and is false out of range; package that proof as `edgeB_faithful`. Define checked-program-specific AF/status wrappers by instantiating the existing generic bridge with this witness.

**Tech Stack:** Lean 4.32 core library, Lake, the existing `Lara.Check` proof-bearing checker, `lean/AxCheck.lean`, and Cabal/QuickCheck for the unchanged Haskell conformance suite.

## Global Constraints

- `Compile.Edge` is the frozen §8 relational compilation specification; the Boolean algorithm must be proved equivalent to it, never replace it.
- `Compile.CheckedProgram` remains the checker boundary. Do not add a second raw-program checker or mutate `Check.checkProgram` merely to carry a redundant closure cache.
- The decider must implement all frozen closure cases: declared typed attack, attacked occurrence, and structural occurrence containment; it must return `false` whenever either argument index is out of range.
- Preserve generic `toAF`, `Faithful`, `srcIn_iff_grounded`, and `srcStatus_iff` for reusable relational metatheory; add specialized wrappers rather than duplicating their proofs.
- Do not add attack completeness, a missing-edge diagnostic, or the result-7 consistency theorem. Those belong exclusively to issue #18.
- Do not change `Backend.uses`/`certDeps`, certificate-erased argument identity, the Haskell M3 checker, or the codec.
- Every new Lean theorem is listed in `lean/AxCheck.lean`; `lake env lean AxCheck.lean` must report no `sorryAx` and only `propext`, `Classical.choice`, and `Quot.sound` when axioms are needed.

---

### Task 1: Add total Boolean occurrence and closure predicates

**Files:**

- Modify: `lean/Lara/Compile.lean:54-182`
- Modify: `lean/Lara/Examples.lean:1515-1601`
- Test: closed `#guard`/theorem fixtures in `lean/Lara/Examples.lean`

**Interfaces:**

- Consumes: `SupportTerm`, structural equality (`SupportTerm.decEq`), `Attack.subterm`, `Attack.lookupDis`, `AttackOcc`, relational `Contains`, and `HasSupport`/`WellFormedInst.dNodup`.
- Produces: `containsB`/`containsBList`/`containsBDis` (explicit mutual helpers — see Issue 2 below), `attackClosureB : Attack.Attack → SupportTerm → Bool`, a recursive discharge-key-distinctness predicate `DisNodup` with a `HasSupport → DisNodup` bridge, and **well-formedness-guarded** iff lemmas usable by the indexed edge proof.

> **Review findings folded in (2026-07-25 `/plan-eng-review`).** Three defects in the
> original sketch were caught before implementation and are corrected below:
> - **Issue 1 (faithfulness).** `Contains v t := ∃ π, Attack.subterm v π = some t`, and
>   `subterm`'s discharge step (`Attack.lean:66-73`) resolves keys via `lookupDis`, which is
>   **first-match** (`Attack.lean:58-60`). A `.inst` node with two discharge entries sharing a
>   `QuestionId` shadows the second: it is unreachable by any position, yet a scan-all
>   `containsB` would descend into it. So `containsB_iff` stated `∀ v t` is **false**. The
>   checker forbids duplicate discharge keys (`WellFormedInst.dNodup`, `Support.lean:577`) —
>   but that is an invariant of *checked* terms, not of the type. Fix: guard the iff lemmas
>   with a recursive discharge-nodup predicate `DisNodup`, discharged from `P.complete` at the
>   `edgeB` boundary. (`CheckedProgram.nodup` does **not** help — it only dedups whole
>   arguments, not discharge keys.)
> - **Issue 2 (definability).** Lean 4.32 cannot synthesize recursion through `SupportTerm`'s
>   nested `List SupportTerm` / `List (QuestionId × SupportTerm)` fields (documented,
>   `Support.lean:214-218`) — every existing traversal (`leaves`/`leavesList`/`leavesDis`,
>   `decEq`/`decEqList`/`decEqDis`) uses explicit structurally-recursive list helpers. A
>   recursive `ws.any (fun w => containsB w t)` gives the termination checker no visible
>   decrease, so the single-def `mutual` block would not elaborate. Fix: explicit
>   `containsBList`/`containsBDis` helpers, mirroring the house pattern.
> - **Typo.** The original `attackClosureB_iff (k target : Attack.Attack)` types `target` as
>   an `Attack.Attack`; it must be a `SupportTerm` (the def takes `target : SupportTerm`).

- [ ] **Step 1: Add a failing closure fixture before defining the predicates**

Add the following assertions next to the existing `PEx` closure fixtures. They deliberately name the intended public API and must fail until the definitions exist:

```lean
theorem containsB_wrapper_leaf :
    Compile.containsB vWrap (.leaf l1) = true := by decide

theorem containsB_leaf_unrelated :
    Compile.containsB (.leaf l2) (.leaf l1) = false := by decide

theorem attackClosureB_direct :
    Compile.attackClosureB kAtk (.leaf l1) = true := by decide

theorem attackClosureB_wrapper :
    Compile.attackClosureB kAtk vWrap = true := by decide
```

**Branch-coverage fixtures (Issue 3 — full coverage).** The four fixtures above never
exercise the discharge branch, the `.rebut` form, or positional attacks with a non-empty
`π`. Add fixtures covering every remaining branch. Introduce the small supporting terms
these need (a term carrying a discharge subterm, a term with **duplicate** discharge keys,
a `.rebut` attack, and an attack whose position descends one level) next to the existing
`vWrap`/`kAtk` defs — reuse `rWrapId`/`q1`/`l1`/`l2` and existing rule ids where possible.
Concrete assertions to land:

```lean
-- containsB: `inst` self-equal true branch (decide (inst = t) = true)
theorem containsB_inst_self : Compile.containsB vWrap vWrap = true := by decide

-- containsB: positive discharge containment (exercises containsBDis)
--   vDis := .inst rWrapId [] [] [(q1, .leaf l1)] [] .none
theorem containsB_discharge_hit : Compile.containsB vDis (.leaf l1) = true := by decide

-- containsB vs Contains DIVERGE off the well-formed domain (Issue 1 guard).
--   vDup := .inst rWrapId [] [] [(q1, .leaf l1), (q1, .leaf l2)] [] .none
--   The second entry is shadowed by lookupDis first-match, so it is NOT `Contains`,
--   yet the scan-all `containsB` returns true. This fixture PINS the reason
--   `containsB_iff` must carry `DisNodup`; keep both halves as a compiled contract.
theorem containsB_dupkey_true  : Compile.containsB vDup (.leaf l2) = true := by decide
theorem containsB_dupkey_not_contains : ¬ Compile.Contains vDup (.leaf l2) := by decide

-- attackClosureB: `.rebut` branch (occurrence IS the whole target term)
--   kReb := .rebut (.leaf l2) vWrap   -- rebut attacks the whole term vWrap
theorem attackClosureB_rebut : Compile.attackClosureB kReb vWrap = true := by decide

-- attackClosureB: positional π ≠ [] some-case, and the out-of-position none→false case
--   kPos  := .undermine (.leaf l2) vWrap [.prem 0]   -- descends to vWrap's premise .leaf l1
--   kBadPos := .undermine (.leaf l2) vWrap [.prem 9] -- index out of range → subterm none
theorem attackClosureB_positional : Compile.attackClosureB kPos (.leaf l1) = true := by decide
theorem attackClosureB_badpos     : Compile.attackClosureB kBadPos (.leaf l1) = false := by decide
```

`Contains` is `Decidable` only where its `∃ π` search is bounded; if `by decide` cannot
close `containsB_dupkey_not_contains` directly, prove it by exhausting the finitely-many
reachable positions of `vDup` (`[]`, `.prem _`, `.ques q1` → `lookupDis` first-match `.leaf l1`)
— never assert it without a proof.

- [ ] **Step 2: Run the focused Lean compile and confirm the expected missing-name failure**

Run: `cd lean && lake env lean Lara/Examples.lean`

Expected: failure mentioning `Compile.containsB` and `Compile.attackClosureB` are unknown constants.

- [ ] **Step 3: Implement structural containment and attack closure in `Compile`**

Add these definitions below `Contains`/`AttackOcc`. Use **explicit structurally-recursive
list helpers** (Issue 2) — the same shape as `leaves`/`leavesList`/`leavesDis`
(`Support.lean:327-337`) — never a recursive `List.any` lambda, which will not elaborate
through `SupportTerm`'s nested list fields in Lean 4.32:

```lean
mutual
  def containsB : SupportTerm → SupportTerm → Bool
    | .leaf l, t => decide (.leaf l = t)
    | .inst r θ ws ds hs a, t =>
        decide (.inst r θ ws ds hs a = t) || containsBList ws t || containsBDis ds t
  def containsBList : List SupportTerm → SupportTerm → Bool
    | [], _ => false
    | w :: ws, t => containsB w t || containsBList ws t
  def containsBDis : List (QuestionId × SupportTerm) → SupportTerm → Bool
    | [], _ => false
    | (_, w) :: rest, t => containsB w t || containsBDis rest t
end

def attackClosureB (k : Attack.Attack) (target : SupportTerm) : Bool :=
  match k with
  | .rebut _ u => containsB target u
  | .undercut _ u π | .undermine _ u π =>
      match Attack.subterm u π with
      | some t => containsB target t
      | none => false
```

**Well-formedness predicate (Issue 1).** `containsB`/`containsBDis` scan every discharge
entry, but `subterm` reaches only the first entry per `QuestionId` (via `lookupDis`). The two
coincide **exactly when discharge keys are distinct at every nested node.** Define that
invariant recursively and bridge it from the checker's postcondition — do not restate
`containsB_iff` unconditionally:

```lean
mutual
  /-- Recursive discharge-key distinctness: the invariant `HasSupport` already proves
  (`WellFormedInst.dNodup`), lifted to every nested instance. Exactly the hypothesis under
  which scan-all `containsB` agrees with first-match `subterm` reachability. -/
  def DisNodup : SupportTerm → Prop
    | .leaf _ => True
    | .inst _ _ ws D _ _ => (D.map Prod.fst).Nodup ∧ DisNodupList ws ∧ DisNodupDis D
  def DisNodupList : List SupportTerm → Prop
    | [] => True
    | w :: ws => DisNodup w ∧ DisNodupList ws
  def DisNodupDis : List (QuestionId × SupportTerm) → Prop
    | [] => True
    | (_, w) :: rest => DisNodup w ∧ DisNodupDis rest
end

/-- Every checked support term satisfies `DisNodup` — by induction on `HasSupport`,
reading off each `WellFormedInst.dNodup` and recursing into premises and discharges. -/
theorem hasSupport_disNodup {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk w C O) : DisNodup w
```

Prove the exact bridges, **guarded by `DisNodup`**, including every branch of
`SupportTerm.inst` and both positional attack forms (note the corrected `target : SupportTerm`
type):

```lean
theorem containsB_iff {v : SupportTerm} (hwf : DisNodup v) (t : SupportTerm) :
    containsB v t = true ↔ Contains v t

theorem attackClosureB_iff {target : SupportTerm} (hwf : DisNodup target)
    (k : Attack.Attack) :
    attackClosureB k target = true ↔ ∃ t, AttackOcc k t ∧ Contains target t
```

For `containsB_iff`, prove the mutual block over all three helpers simultaneously
(`containsB`/`containsBList`/`containsBDis`), strengthening the IH over all query terms.
Forward: a `containsBList` success at index `i` gives the `.prem i :: π` witness directly; a
`containsBDis` success at `(q, w)` gives the `.ques q :: π` witness **only because** `hwf`'s
`(D.map Prod.fst).Nodup` makes `lookupDis D q = some w` (standard nodup-assoc lookup), i.e.
this is the exact step the shadowing counterexample breaks without `hwf`. Reverse: destruct
`Contains`'s position witness and reduce the same branch. Do not infer containment from term
equality alone: descendants through both premise and discharge lists must succeed.

`attackClosureB_iff` threads `hwf` straight into `containsB_iff` in each branch. Both undercut
and undermine close over `u@π` identically — that is the frozen compilation rule (the
undercut/undermine distinction is enforced by `P.typed`, not by closure), so a single
positional branch is correct; the coverage fixtures above test both forms.

- [ ] **Step 4: Re-run the focused fixtures**

Run: `cd lean && lake env lean Lara/Examples.lean`

Expected: success; the four new fixtures and the pre-existing direct/wrapper/no-edge theorems compile.

- [ ] **Step 5: Commit the independently testable closure predicate layer**

```bash
git add lean/Lara/Compile.lean lean/Lara/Examples.lean
git commit -m "feat(compile): decide structural attack closure"
```

### Task 2: Construct and prove the checked-program edge decider

**Files:**

- Modify: `lean/Lara/Compile.lean:184-217`
- Modify: `lean/Lara/Examples.lean:1543-1601`
- Test: closed theorems in `lean/Lara/Examples.lean`

**Interfaces:**

- Consumes: `attackClosureB_iff`, `hasSupport_disNodup`, `CheckedProgram.args`, `CheckedProgram.complete`, `CheckedProgram.atts`, and `Faithful`.
- Produces: `edgeB : CheckedProgram canon Pi Gamma CertOk dp → Nat → Nat → Bool`, `edgeB_iff`, and `edgeB_faithful : Faithful P (edgeB P)`.

> **Threading note (Issue 1 / cross-model).** `attackClosureB_iff` now requires
> `DisNodup target`. At the `edgeB` boundary `target = P.args[j]?`, a **checked** argument, so
> `P.complete` gives `HasSupport … target …` and `hasSupport_disNodup` discharges the
> hypothesis — no caller ever sees `DisNodup`. This threading lives in `edgeB_iff` (Task 2)
> and was already introduced in `attackClosureB_iff` (Task 1); nothing above the `Faithful`
> API changes.

- [ ] **Step 1: Add a failing checker-built-decider fixture**

Replace the assertion of only the hand-written `edgeBEx` behavior with the checker-built equivalent:

```lean
theorem checked_edge_fixture :
    Compile.edgeB PEx 0 1 = true ∧
    Compile.edgeB PEx 0 2 = true ∧
    Compile.edgeB PEx 1 1 = false ∧
    Compile.edgeB PEx 3 1 = false ∧
    Compile.edgeB PEx 0 3 = false := by decide

theorem checked_edge_fixture_faithful :
    Compile.Faithful PEx (Compile.edgeB PEx) :=
  Compile.edgeB_faithful PEx
```

- [ ] **Step 2: Run the fixture and confirm that `edgeB`/`edgeB_faithful` are absent**

Run: `cd lean && lake env lean Lara/Examples.lean`

Expected: failure mentioning the two missing `Compile` declarations.

- [ ] **Step 3: Implement the indexed decider and exact adequacy theorem**

Define the decider adjacent to `Faithful`, so its out-of-range behavior is visible at the compilation boundary:

```lean
def edgeB (P : CheckedProgram canon Pi Gamma CertOk dp)
    (i j : Nat) : Bool :=
  match P.args[i]?, P.args[j]? with
  | some source, some target =>
      P.atts.any (fun k =>
        decide (k.source = source) && attackClosureB k target)
  | _, _ => false
```

Prove the in-range characterization without using `P.typed` as a substitute for the algorithm:

```lean
theorem edgeB_iff {P : CheckedProgram canon Pi Gamma CertOk dp}
    {i j : Nat} {source target : SupportTerm}
    (hsource : P.args[i]? = some source)
    (htarget : P.args[j]? = some target) :
    edgeB P i j = true ↔ Edge P source target
```

The forward proof must: unpack `List.any_eq_true` to a member `k ∈ P.atts`, convert the
source-equality Boolean with `of_decide_eq_true`, discharge `attackClosureB_iff`'s
`DisNodup target` hypothesis via `hasSupport_disNodup (P.complete target (getElem?-mem htarget))`,
and apply `attackClosureB_iff` to get `∃ t, AttackOcc k t ∧ Contains target t`. **`Edge` also
requires both endpoints declared** (`source ∈ P.args ∧ target ∈ P.args`, `Compile.lean:135`):
derive both from `hsource`/`htarget` with the getElem?-membership lemma — the plan's original
sketch omitted this and it is not optional. The reverse proof obtains the declared attack
witness from `Edge`, shows its source equality using the witness equation, threads `DisNodup`
the same way, and selects that list member with `List.any_eq_true`. `args.Nodup` is **not**
used in this proof.

Then package the boundary and agreement obligations. Prove `ranged` by an **explicit** case
split on the two `getElem?` options — do **not** rely on blind `split at h <;> split at h <;>
simp_all`, which is fragile: after the first split the non-`some` branches carry `h : false =
true` with no remaining match to split, and `simp_all` cannot invent both index bounds:

```lean
theorem edgeB_faithful (P : CheckedProgram canon Pi Gamma CertOk dp) :
    Faithful P (edgeB P) := by
  refine ⟨?_, ?_⟩
  · intro i j h
    unfold edgeB at h
    -- explicit case analysis on the two option discriminants
    cases hi : P.args[i]? with
    | none => rw [hi] at h; simp at h            -- edgeB reduces to `false`
    | some source =>
      cases hj : P.args[j]? with
      | none => rw [hi, hj] at h; simp at h       -- edgeB reduces to `false`
      | some target =>
        exact ⟨lt_of_getElem?_some hi, lt_of_getElem?_some hj⟩
  · intro i j source target hi hj
    exact edgeB_iff hi hj
```

Adjust the exact `rw`/`simp` shape to however `edgeB`'s `match` reduces after `unfold`; the
load-bearing move is eliminating the two non-`some/some` cases explicitly, then applying
`lt_of_getElem?_some` to the retained `some` equalities. Do not weaken `Faithful.ranged`.

- [ ] **Step 4: Replace the manual oracle as the primary fixture**

Keep `edgeBEx` only as an extensional regression oracle if it remains useful; add:

```lean
theorem edgeB_PEx_eq_edgeBEx : Compile.edgeB PEx = edgeBEx := by
  funext i j
  interval_cases i <;> interval_cases j <;>
    simp [Compile.edgeB, edgeBEx, PEx_args, PEx_atts, kAtk,
      Compile.attackClosureB, Compile.containsB, vWrap]
```

Rewrite `closure_grounded_verdict` to use `toAF PEx (Compile.edgeB PEx)`. This proves the real checker-built path has the same direct and strict-superset closure outcome, rather than merely checking a manually encoded truth table.

- [ ] **Step 5: Run the focused checker-built closure matrix**

Run: `cd lean && lake env lean Lara/Examples.lean`

Expected: success; the generic decider, its `Faithful` witness, out-of-range rejection, direct edge, strict-superset wrapper edge, and grounded defeated verdict all compile.

- [ ] **Step 6: Commit the exact edge-decision layer**

```bash
git add lean/Lara/Compile.lean lean/Lara/Examples.lean
git commit -m "feat(compile): build faithful edges from checked programs"
```

### Task 3: Expose oracle-free compiled AF and result-6 wrappers

**Files:**

- Modify: `lean/Lara/Compile.lean:184-410`
- Modify: `lean/Lara/Examples.lean:1590-1601`
- Modify: `lean/Lara.lean:1-25`
- Test: theorem fixtures in `lean/Lara/Examples.lean`

**Interfaces:**

- Consumes: `toAF`, `edgeB_faithful`, `srcIn_iff_grounded`, `srcStatus_correct`, and `srcStatus_iff`.
- Produces: `checkedAF`, `srcIn_iff_checkedGrounded`, `srcStatus_checked`, and `srcStatus_iff_checked`; no caller needs to manufacture `Faithful`.

- [ ] **Step 1: Add a failing source-to-compiled wrapper fixture**

Use the existing `PEx` status case with the new public wrappers:

```lean
theorem checked_closure_status :
    Grounded.statusC (Compile.checkedAF PEx) ⟨[2], []⟩ =
      Grounded.Status.defeated := by decide

theorem checked_src_status_exists :
    ∃ s, Compile.SrcStatus PEx ⟨[2], []⟩ s :=
  ⟨Grounded.Status.defeated,
    Compile.srcStatus_checked PEx ⟨[2], []⟩⟩
```

- [ ] **Step 2: Compile and confirm the wrappers are not yet defined**

Run: `cd lean && lake env lean Lara/Examples.lean`

Expected: failure mentioning `Compile.checkedAF` and `Compile.srcStatus_checked`.

- [ ] **Step 3: Define wrappers by direct instantiation of the existing theorems**

Add the following after `edgeB_faithful` and retain the generic oracle-parametric API unchanged:

```lean
def checkedAF (P : CheckedProgram canon Pi Gamma CertOk dp) : Grounded.AF :=
  toAF P (edgeB P)

theorem srcIn_iff_checkedGrounded
    (P : CheckedProgram canon Pi Gamma CertOk dp) (i : Nat) :
    SrcIn P i ↔ i ∈ Grounded.grounded (checkedAF P) :=
  srcIn_iff_grounded (edgeB_faithful P) i

theorem srcStatus_checked
    (P : CheckedProgram canon Pi Gamma CertOk dp) (c : Grounded.Claim) :
    SrcStatus P c (Grounded.statusC (checkedAF P) c) :=
  srcStatus_correct (edgeB_faithful P) c

theorem srcStatus_iff_checked
    (P : CheckedProgram canon Pi Gamma CertOk dp) (c : Grounded.Claim)
    (s : Grounded.Status) :
    SrcStatus P c s ↔ s = Grounded.statusC (checkedAF P) c :=
  srcStatus_iff (edgeB_faithful P) c s
```

Ensure elaboration sees `checkedAF P` definitionally as `toAF P (edgeB P)`; if it does not, use `simpa [checkedAF]` rather than duplicating the source/grounded proof.

- [ ] **Step 4: Update the library-root scope comment**

Change `lean/Lara.lean` so result 6 is described as complete and remove Issue #17 from its “To come” list. Preserve #18, result 3 certificate half, and result 9 as remaining work.

- [ ] **Step 5: Run the source-to-compiled focused suite**

Run: `cd lean && lake env lean Lara/Examples.lean && lake env lean Lara.lean`

Expected: success; the checker-built fixture can evaluate grounded status and derive the source status without an explicit Boolean edge function or `Faithful` proof argument.

- [ ] **Step 6: Commit the result-6 public API**

```bash
git add lean/Lara/Compile.lean lean/Lara/Examples.lean lean/Lara.lean
git commit -m "feat(compile): expose oracle-free status preservation"
```

### Task 4: Audit, document, and verify Issue #17 completion

**Files:**

- Modify: `lean/AxCheck.lean:199-216,350-365`
- Modify: `lean/README.md:16-22,60-68`
- Modify: `docs/spec.md:1010-1100`
- Modify: `docs/mechanization-plan.md:180-235`
- Modify: `docs/m1-freeze-checklist.md:83-102`
- Modify: `ara/evidence/status/mechanization_status.md`
- Modify: `ara/logic/claims.md`
- Modify: `ara/trace/exploration_tree.yaml`

**Interfaces:**

- Consumes: the new public theorem names and passing build/audit results.
- Produces: a reproducible proof audit and a status record that result 6 is fully mechanized, while #18 remains the next dependency.

- [ ] **Step 1: Add every new theorem to the axiom audit**

Add these commands in the existing compile and fixture sections of `lean/AxCheck.lean`:

```lean
#print axioms Lara.Compile.hasSupport_disNodup
#print axioms Lara.Compile.containsB_iff
#print axioms Lara.Compile.attackClosureB_iff
#print axioms Lara.Compile.edgeB_iff
#print axioms Lara.Compile.edgeB_faithful
#print axioms Lara.Compile.srcIn_iff_checkedGrounded
#print axioms Lara.Compile.srcStatus_checked
#print axioms Lara.Compile.srcStatus_iff_checked
#print axioms Lara.Examples.checked_edge_fixture_faithful
#print axioms Lara.Examples.edgeB_PEx_eq_edgeBEx
#print axioms Lara.Examples.checked_closure_status
-- faithfulness-guard fixtures (Issue 1 / Issue 3): the containsB-vs-Contains contract
#print axioms Lara.Examples.containsB_dupkey_true
#print axioms Lara.Examples.containsB_dupkey_not_contains
#print axioms Lara.Examples.attackClosureB_rebut
#print axioms Lara.Examples.attackClosureB_badpos
```

- [ ] **Step 2: Run the Lean build and axiom gate**

Run:

```bash
cd lean
lake build
out="$(lake env lean AxCheck.lean)"
printf '%s\n' "$out"
! rg -q 'sorryAx' <<<"$out"
! rg -q '^(axiom|theorem).*' <<<"$out"
```

Expected: `lake build` succeeds and the audit prints no `sorryAx`. Compare all reported axioms with the allowed trio; do not accept a newly introduced axiom name.

- [ ] **Step 3: Run the repository conformance suite**

Run: `cabal test all --test-show-details=direct`

Expected: all existing Haskell properties pass. This change is Lean-only, but the full CI contract requires both suites.

- [ ] **Step 4: Update status documentation and the research ledger**

Make the status changes concrete. **Claim-wording discipline (Issue 5).** What #17 delivers
is *oracle elimination*: it constructively discharges the `Faithful` assumption, making
`srcStatus_iff_checked` (source-to-compiled status preservation, **source-vs-compiled half**)
hold with **no** oracle hypothesis. It does **not** relate an *independent* declarative source
calculus to the compiled AF — `SrcIn`/`SrcOut` are the Prop-level shadow of the *same*
compiled `Edge` closure relation that `edgeB` executes. Word every doc/claim edit to that
precision; do not write an unqualified "result 6 complete" that a `/rigor-reviewer` pass would
flag:

- In `lean/README.md`, change result 6 from “mechanized modulo the executable edge decider” to
  **"source-vs-compiled half complete: the `Faithful` oracle is now constructively supplied by
  `Compile.edgeB_faithful`"**; name the specialized wrappers. State the residual half (#18) plainly.
- In `docs/spec.md`, replace the remaining general-oracle gap with the checker-built closure
  algorithm and the exact `Faithful` theorem, described as eliminating the oracle assumption
  (not as an independent-semantics preservation result); retain #18 as the result-7 blocker.
- In `docs/mechanization-plan.md` and `docs/m1-freeze-checklist.md`, move #17/result 6's
  source-vs-compiled half to complete and make #18 the next M2 tracker child.
- In `ara/evidence/status/mechanization_status.md`, record the exact build and AxCheck commands
  and their pass status.
- In `ara/logic/claims.md` and `ara/trace/exploration_tree.yaml`, advance only the
  source-to-compiled status-preservation claim, phrased as **oracle-free / `Faithful`
  discharged** over the closure-edge relation; do not claim an independent source semantics,
  grounded consistency, or attack completeness.

- [ ] **Step 5: Review the final diff and commit the proof/audit/docs evidence**

Run: `git diff --check && git status --short`

Expected: no whitespace errors; only the Issue #17 Lean, documentation, and ledger files are modified.

```bash
git add lean/AxCheck.lean lean/README.md docs/spec.md docs/mechanization-plan.md \
  docs/m1-freeze-checklist.md ara/evidence/status/mechanization_status.md \
  ara/logic/claims.md ara/trace/exploration_tree.yaml
git commit -m "docs: close result-6 edge-decider gap"
```

## Plan Review

**Spec coverage:** Task 1 decides structural occurrence containment; Task 2 decides declared typed-attack closure, proves `Edge` agreement, and proves out-of-range false through `Faithful.ranged`; Task 3 threads the witness through AF, grounded, and status execution; Task 4 satisfies the no-`sorry`, axiom, Lean-build, Haskell-conformance, documentation, and ledger requirements. Attack completeness and consistency are explicitly excluded and remain #18.

**Type consistency:** The plan uses the existing `CheckedProgram`, `SupportTerm`, `Attack.Attack`, `Grounded.AF`, `Faithful`, `SrcIn`, and `SrcStatus` types. Every wrapper instantiates the existing generic theorem at `edgeB P`; no new raw-checker output type is introduced.

**Placeholder scan:** No deferred implementation steps or unspecified tests remain; each task identifies exact files, public interfaces, focused commands, expected results, and commit boundaries.

---

## Eng Review Outputs (2026-07-25 `/plan-eng-review`)

### What already exists (reused, not rebuilt)

- **`Compile.Edge` / `Contains` / `AttackOcc`** — the frozen §8 relational spec. The plan
  proves the Boolean algorithm equivalent; it never replaces them. ✓
- **Generic oracle-parametric bridge** — `toAF`, `Faithful`, `srcIn_iff_grounded`,
  `srcStatus_correct`, `srcStatus_iff`. Task 3 instantiates these at `edgeB P`; no metatheory
  is duplicated. ✓
- **`edgeBEx` / `edgeBEx_faithful`** — the hand-written witness for `PEx`. Retained as an
  extensional regression oracle via `edgeB_PEx_eq_edgeBEx`. ✓
- **House traversal pattern** — `leaves`/`leavesList`/`leavesDis`, `decEq`/`decEqList`/`decEqDis`
  (`Support.lean`). Issue 2's fix reuses this exact shape for `containsB`. ✓
- **Checker invariant** — `WellFormedInst.dNodup` (`Support.lean:577`). Issue 1's fix lifts it
  via `hasSupport_disNodup` rather than inventing a new well-formedness story. ✓

### NOT in scope (deferred, with rationale)

- **Attack completeness, missing-edge diagnostic, result-7 consistency** — belong to **#18**;
  explicitly excluded by Global Constraints. The N16 bridge here is the source-vs-compiled
  half only.
- **A second, unconditional first-match `containsB` (Codex's Option B)** — rejected: its
  first-match discharge traversal is not structurally decreasing through the nested list
  fields, so it fights Lean 4.32's recursion limit. Revisit only if a future Lean version
  makes filter/dedup-by-key traversal structural.
- **A general `Decidable (Contains v t)` instance** — not needed by #17; `containsB_iff` under
  `DisNodup` suffices. Left as a possible future convenience, not captured as a TODO (see below).
- **Changes to `Backend.uses`/`certDeps`, the Haskell M3 checker, the codec** — untouched by
  constraint.

### Failure modes (new codepaths)

This is a proof artifact: every failure is **loud** at `lake build` / `AxCheck`, never a silent
runtime fault. No critical silent gaps.

| New codepath | Realistic failure | Test covers | Error visible |
|---|---|---|---|
| `containsB`/`containsBList`/`containsBDis` | termination-checker rejects nested recursion | `lake build` (T1) | yes — elaboration error |
| `containsB_iff` (unguarded) | forward direction unprovable under key shadowing | `containsB_dupkey_true` + `_not_contains` (T2/T3) | yes — proof fails / fixture red |
| `edgeB_faithful.ranged` | fragile tactic leaves goal open | `lake build` + `#print axioms` (T4) | yes — proof fails |
| result-6 doc/claim wording | overstated claim survives to publish | `/rigor-reviewer` on `ara/` (T5) | yes — review flag |

### Worktree parallelization

**Sequential implementation, no meaningful parallelization opportunity.** T1→T2→T3 all mutate
`lean/Lara/Compile.lean` and `lean/Lara/Examples.lean`; T4 also touches `Compile.lean`; T5's
doc/claim edits depend on the theorem names existing first. Follow the plan's Task 1→2→3→4
ordering; do not split across worktrees (guaranteed merge conflict on `Compile.lean`).

### Implementation Tasks
Synthesized from this review's findings. Each derives from a specific finding above.

- [ ] **T1 (P1, human: ~1-2h / CC: ~20-30min)** — `Compile.containsB` — define with explicit `containsBList`/`containsBDis` mutual helpers, not a recursive `List.any` lambda
  - Surfaced by: Section 2 Issue 2 — Lean 4.32 cannot recurse through `SupportTerm`'s nested `List` fields (`Support.lean:214-218`)
  - Files: `lean/Lara/Compile.lean`
  - Verify: `cd lean && lake env lean Lara/Examples.lean` elaborates
- [ ] **T2 (P1, human: ~half day / CC: ~30-60min)** — `Compile.containsB_iff` — add `DisNodup` + `hasSupport_disNodup`; guard `containsB_iff`/`attackClosureB_iff`/`edgeB_iff`, discharge from `P.complete`
  - Surfaced by: Section 1 Issue 1 — `containsB_iff` false unconditionally under discharge-key shadowing; invariant is `WellFormedInst.dNodup`
  - Files: `lean/Lara/Compile.lean`
  - Verify: `containsB_dupkey_true` ∧ `containsB_dupkey_not_contains` both compile
- [ ] **T3 (P2, human: ~1-2h / CC: ~20min)** — `Lara.Examples` — full branch-coverage fixtures incl. dup-discharge-key negative guard, rebut, positional some/none, inst self-equal
  - Surfaced by: Section 3 Issue 3 — discharge/rebut/positional branches unexercised
  - Files: `lean/Lara/Examples.lean`
  - Verify: `cd lean && lake env lean Lara/Examples.lean`
- [ ] **T4 (P2, human: ~30min / CC: ~10min)** — `Compile.edgeB_faithful` — explicit `getElem?` case-split in `ranged`; add `edgeB_iff` endpoint-membership derivation
  - Surfaced by: Codex Issue 4 — `ranged` sketch fragile; `Edge` requires both endpoints ∈ args
  - Files: `lean/Lara/Compile.lean`
  - Verify: `lake env lean AxCheck.lean` shows only the allowed axiom trio
- [ ] **T5 (P2, human: ~20min / CC: ~5min)** — docs + `ara/` — word result-6 as oracle elimination over the closure-edge relation, not independent-semantics preservation
  - Surfaced by: Cross-model Issue 5 — "result 6 complete" overstated
  - Files: `lean/README.md`, `docs/spec.md`, `docs/mechanization-plan.md`, `docs/m1-freeze-checklist.md`, `ara/logic/claims.md`, `ara/trace/exploration_tree.yaml`
  - Verify: `/rigor-reviewer ara/` raises no overstated-claim finding

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | `/codex review` | Independent 2nd opinion | 1 | issues_found | 7 raised; 3 confirmed review findings, 3 new (result-6 wording, ranged proof, edgeB_iff membership), 1 reassurance |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | clean | 5 issues, 0 critical gaps — all folded into plan (T1–T5) |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | — (no UI surface) |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | — |

- **CODEX:** outside voice confirmed Issues 1–3, added the result-6 wording caution (Issue 5), the fragile-`ranged` proof and missing `edgeB_iff` endpoint-membership (Issue 4), and reassured on `checkedAF` definitional unfolding + `by decide` reducibility (no action).
- **CROSS-MODEL:** one tension — review recommended Option A (WF-hypothesis guard) for `containsB_iff`; Codex preferred Option B (first-match `containsB`, unconditional theorem). Resolved to **keep A**: B's first-match discharge traversal is not structurally decreasing through `SupportTerm`'s nested list fields, fighting the same Lean 4.32 limit that forces the house helper pattern. All other findings overlap or are complementary.
- **VERDICT:** ENG CLEARED — ready to implement. 5 findings folded into Tasks 1–4 + docs (T1–T5); 0 critical gaps; axiom trio preserved by the `AxCheck` gate.

NO UNRESOLVED DECISIONS
