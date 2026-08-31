# M2b Follow-up: Fixed-Policy Realization Closure — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Issue:** #209 (parent tracker #180; successor to the closed #181).
**Branch:** `theory/m2b-realization-closure`.
**Predecessor record:** [`docs/theory-m2b-complexity-spike.md`](../docs/theory-m2b-complexity-spike.md)
(the INCONCLUSIVE gate, PR #208). The retired, engineering-cleared predecessor plan is
preserved verbatim at git object
`17d07ffec693797b4b39599e787723328fa3f61f:plans/2026-08-29-m2b-restricted-class-complexity.md`;
Phase 2 below restates its post-gate tasks so this plan is self-contained.

**Goal:** Close the family-wide checker equation `checkUnit_formula_ok` that stopped the M2b
realization gate, by packaging compositional checker lemmas for the generated map/flatMap
argument and attack families — then, only on a renewed HARDNESS gate, resume the stopped
compile-image, size, quartic-witness, shared-status, and 3SAT-reduction obligations.

**Architecture:** The fixed context (`m2bSigma`, `m2bPolicy`, `m2bRegistry`, identity canon)
and the finite encodings (`Formula3`, `CarrierCode`) are frozen and untouched. All new work is
proof-side: a numeral-injectivity foundation, a closed-sum leaf vocabulary with a single
injective encode table, per-family lemmas discharging each `Check.Unit.checkUnit_complete`
premise for `rawUnitOfFormula φ`, and the assembled acceptance theorem. The gate is then
re-decided from proof artifacts under the same three-outcome stop rule as before.

**Tech stack:** Lean 4 with the existing `Std` dependency (already used via
`Std.Data.String.ToNat` in `Lara/ND.lean`); no Mathlib; existing `Lara.Check.Unit`,
`Lara.Realizability`, `Lara.Semantics`, `Lara.Grounded` interfaces. No Haskell changes, no
corpus regeneration, no freeze-tag impact anywhere in this plan.

---

## Review status

**Engineering review: PENDING.** This plan lands through a reviewed PR; implementation must
not start before that PR is approved. The predecessor plan's motivation/CEO findings are
inherited as frozen constraints (§1) and are not relitigated here.

| Review | Trigger | Runs | Status | Finding disposition |
|---|---|---:|---|---|
| Eng Review | the plan PR (#209) | 0 | PENDING | — |
| Motivation/CEO review | inherited from predecessor | 1 | FOLDED | §1 constraints 1–6 |
| Design Review | `/plan-design-review` | 0 | — | No UI scope |
| DX Review | `/plan-devex-review` | 0 | — | No public API or onboarding scope |

**Gate status: NOT YET RE-DECIDED.** Task 8 records the renewed outcome in
`docs/theory-m2b-complexity-spike.md`.

---

## 1. Inherited non-negotiables

These carry over from the predecessor plan's review, the spike record, and the crystallized
boundaries (`ara/logic/claims.md#C44`, `#C45`;
`ara/logic/solution/constraints.md`, M2b section). Reintroducing any rejected form requires a
new review.

1. **The fixed context is frozen.** Every theorem uses exactly `canon := id`,
   `m2bSigma`, `m2bPolicy`, `m2bRegistry`. No formula-specific policy, signature, registry,
   axiom, `sorry`, or placeholder. A construction that needs a per-instance policy changes
   the class being studied and is out of scope (C45).
2. **The INCONCLUSIVE record is not evidence.** Nothing in this plan may reinterpret the
   spike as support for hardness or tractability. Only closed proofs move C44/C45.
3. **A restricted-class witness carries class membership.** Tightness and hardness claims
   require the executable checker equation and `StructuredAFIso` under the fixed context —
   `CompilerInvariant` alone is never substituted for realizability.
4. **The universal floor is quadratic, not cubic**; quartic statements are existential
   worst-case results on a realizable family. Documentation must never merge the two
   quantifiers.
5. **Oracle cost and classical input size use separate frozen representations.**
   `CarrierCode.byteSize` is a carrier accounting measure (framing unit + atom-key text +
   matrix cells + query-index text), not a serialized wire length; `Formula3.byteSize` is
   the UTF-8 length of the canonical S-expression.
6. **The stop rule binds again.** Task 8 has the same three outcomes as the predecessor's
   gate. On a second INCONCLUSIVE: record the exact new obstruction in the spike document,
   stop before Phase 2, keep #209 open, claim nothing.

---

## 2. Route decision

**Chosen — Route A: compositional lifting lemmas through `checkUnit_complete`.**
`Check.Unit.checkUnit_complete` (`lean/Lara/Check/Unit.lean`) is the sanctioned completeness
surface: its premises are exactly the raw obligations the spike could not discharge
family-wide (dead end `trace:N257`, staged constraint O108). This plan proves each premise
as its own parameterized lemma family and assembles them once.

**Rejected — Route B: manual `CheckedUnit` construction.** The module header of
`Lara/Check/Unit.lean` states it directly: "Manual proof-level construction of `CheckedUnit`
still requires every invariant." Route B discharges the same obligations without the
executable checker equation that `Realization.checked` requires — strictly more work for a
weaker artifact.

**Rejected — Route C: a different gadget.** Any replacement family faces the same
family-wide obligations under the same fixed policy, discards the merged shape fixture
(`rawUnitOfFormula_shape`) that already pins the intended data, and would need its own
motivation review. Nothing in the spike record indicts the gadget; the missing piece is
proof infrastructure, not the construction.

**Risk assessment for Route A.** The previously unpriced risk — family-wide injectivity of
decimal numerals — is already discharged in this repository: `Lara.ND.decodeNat_repr`
(`lean/Lara/ND.lean:112`) proves `decodeNat (Nat.repr n) = some n` for all `n` via
`Std.Data.String.ToNat`, and injectivity of `Nat.repr` is a two-line corollary (Task 1).
The residual risk concentrates in the `AttackComplete` characterization (Task 6), which is
why it sits behind every cheaper family lemma and directly before the gate.

---

## 3. New frozen decisions (D7–D9)

### D7 — Numeral injectivity comes from a verified decoder round-trip

`natRepr_inj : Nat.repr m = Nat.repr n → m = n` is proved by applying a decoder with a
proven round-trip, never by induction over string representations. The decoder is a local
copy of the two-line `decodeNat` pattern from `Lara.ND` (round-trip provable by
`simp [decodeNat]` with `Std.Data.String.ToNat` imported). It lives in
`lean/Lara/Complexity/Numeral.lean` rather than importing `Lara.ND`, so the complexity spine
does not depend on the natural-deduction backend module (module-ownership seam; the ND
precedent is cited in the module docstring).

### D8 — The gadget moves to the library with a closed-sum leaf vocabulary

`rawUnitOfFormula`, `gammaOfFormula`, `groundOfFormula`, and their private helpers move from
`lean/Lara/Examples/Complexity/Realization.lean` into a new public module
`lean/Lara/Complexity/Gadget.lean`, because the post-gate `reduceCode` and
`Reduction.lean` (library code) must reference them, and library code must not import
`Examples`. The move is definitional-identity: every leaf-id string spelling stays exactly
as the merged shape fixture pins it, and `rawUnitOfFormula_shape` (which stays in the
Examples file) is the regression that proves it.

Per the repo's symbolic-core discipline, the leaf namespace becomes a closed sum type with
one encode table:

```lean
inductive GadgetLeaf where
  | negLit (varIdx : Nat)
  | posLit (varIdx : Nat)
  | occurrence (clauseIndex position : Nat)
  | query
deriving DecidableEq

def GadgetLeaf.encode : GadgetLeaf → LeafId
  | .negLit v => ⟨"literal-negative-" ++ Nat.repr v⟩
  | .posLit v => ⟨"literal-positive-" ++ Nat.repr v⟩
  | .occurrence j p => ⟨"occurrence-" ++ Nat.repr j ++ "-" ++ Nat.repr p⟩
  | .query => ⟨"formula-query"⟩
```

The existing string builders (`negativeLiteralLeafId` etc.) are redefined as
`GadgetLeaf.encode ∘ constructor` so exactly one spelling table exists.

### D9 — The renewed gate

Task 8 re-decides the gate from proof artifacts alone, records exactly one of
`HARDNESS` / `TRACTABILITY CANDIDATE` / `INCONCLUSIVE` in
`docs/theory-m2b-complexity-spike.md` (superseding, not deleting, the 2026-08-30 record),
and only `HARDNESS` unlocks Phase 2. `TRACTABILITY CANDIDATE` still requires an
independently proved structure theorem; a failed lemma is not one (C45).

---

## 4. File structure

### Phase 1 (Tasks 1–8)

- Create `lean/Lara/Complexity/Numeral.lean` — verified decimal round-trip,
  `natRepr_inj`, `numTerm`/atom injectivity corollaries.
- Create `lean/Lara/Complexity/Gadget.lean` — `GadgetLeaf`, the moved formula-indexed
  gadget, the leaf-table lookup spec, and every family lemma (Nodup, sorts, support,
  attacks, `AttackComplete`, ground coverage) through `checkUnit_formula_ok` and
  `acceptedUnitOfFormula`.
- Modify `lean/Lara/Examples/Complexity/Realization.lean` — drop the moved private
  definitions, import `Lara.Complexity.Gadget`, keep the closed fixtures, the negative
  control, and `rawUnitOfFormula_shape` unchanged in statement.
- Modify `lean/Lara.lean` — import the completed `Lara.Complexity.Numeral` and
  `Lara.Complexity.Gadget` only once they are `sorry`-free (spike stop condition).
- Modify `lean/AxCheck.lean` — `#print axioms` rows for every new theorem (mechanization
  discipline: land proofs with the code they enable).
- Modify `docs/theory-m2b-complexity-spike.md` — the renewed gate record (Task 8).

### Phase 2 (Tasks 9–13; HARDNESS only)

- Create `lean/Lara/Complexity.lean` — instrumented grounded kernel and shared status.
- Create `lean/Lara/Examples/Complexity.lean` — lower-bound counterexample and realizable
  quartic family.
- Create `lean/Lara/Complexity/Reduction.lean` — fixed-policy 3SAT reduction and
  correctness (imports `Lara.Complexity.Gadget`, not `Examples`).
- Modify `lean/AxCheck.lean`, `src/Lara/Runtime.hs`, `docs/paper-lean-name-map.md`;
  create `docs/theory-m2b-complexity.md` at closeout; delete this plan only after a
  successful Task 13 closeout. An INCONCLUSIVE Task 8 keeps the plan with a status banner.

---

## 5. Phase 1 tasks

### Task 1: numeral injectivity foundation

**Files:** create `lean/Lara/Complexity/Numeral.lean`; modify `lean/Lara.lean` is deferred
to Task 7 (stop-condition discipline: nothing incomplete gets imported).

- [ ] **Step 1: write the module.**

  ```lean
  import Std.Data.String.ToNat

  namespace Lara.Complexity.Numeral

  /-- Local copy of the `Lara.ND.decodeNat` pattern (module-ownership seam; see D7). -/
  def decodeNat (s : String) : Option Nat := do
    let n ← s.toNat?
    if s = Nat.repr n then some n else none

  @[simp] theorem decodeNat_repr (n : Nat) : decodeNat (Nat.repr n) = some n := by
    simp [decodeNat]

  theorem natRepr_inj {m n : Nat} (h : Nat.repr m = Nat.repr n) : m = n :=
    Option.some.inj ((decodeNat_repr m).symm.trans (h ▸ decodeNat_repr n))

  end Lara.Complexity.Numeral
  ```

- [ ] **Step 2: check the file directly.** Run
  `cd lean && lake env lean Lara/Complexity/Numeral.lean`. Expect success, no output. If
  `simp [decodeNat]` does not close the round-trip in this Std version, prove it through
  the same explicit `String.toNat?_eq_some_ofDigitChars` route
  `Lara.ND.decodeNat_leading_zero_01` already uses; if that also fails, STOP and return to
  review — do not change the numeral representation silently.
- [ ] **Step 3: commit.**

  ```text
  theory(M2b): prove decimal numeral injectivity (#209)

  Plan step 1/13: Numeral foundation
  ```

### Task 2: gadget module with a closed-sum leaf vocabulary

**Files:** create `lean/Lara/Complexity/Gadget.lean`; modify
`lean/Lara/Examples/Complexity/Realization.lean`.

- [ ] **Step 1: move the gadget.** Create `Lara.Complexity.Gadget` importing
  `Lara.Complexity.Encoding` and `Lara.Complexity.Numeral`. Define `GadgetLeaf` and
  `GadgetLeaf.encode` exactly as D8. Move `numTerm`, `literalSign`, `lookupLeaf`,
  `negativeLiteralLeafId`, `positiveLiteralLeafId`, `literalLeafId`, `occurrenceLeafId`,
  `queryLeafId`, the `*Arg` builders, `literalLeafEntries`, `occurrenceEntries`,
  `formulaLeafEntries`, `gammaOfFormula`, `groundOfFormula`, `clauseSubst`,
  `clauseArgument`, `literalArguments`, `clauseArguments`, `formulaArguments`,
  `literalRootAttacks`, `occurrenceAttacks`, `clauseAttacks`, `formulaAttacks`, and
  `rawUnitOfFormula` from the Examples file, unchanged in value, with the leaf-id builders
  now defined through `GadgetLeaf.encode`. Make public what the family lemmas must name;
  keep the rest `private`.
- [ ] **Step 2: prove encode injectivity.**

  ```lean
  theorem GadgetLeaf.encode_inj : Function.Injective GadgetLeaf.encode
  ```

  Case-split both arguments. Same-constructor cases reduce to `natRepr_inj` after
  cancelling the fixed prefixes/separator with `String.append` injectivity on equal-length
  prefixes; for the `occurrence` case, note `Nat.repr` emits no `'-'` character, so the
  separator position is determined — prove the helper
  `theorem repr_no_dash (n : Nat) : ¬ '-' ∈ (Nat.repr n).toList` by strong induction via
  `Nat.toDigits` digit range, or, if that resists core+Std, by round-tripping the split
  through `decodeNat` (both halves decode). Cross-constructor cases are distinct prefixes.
  If this step exceeds a day of effort, STOP and return to review with the exact failing
  case; an unproven `encode_inj` blocks every Nodup lemma downstream.
- [ ] **Step 3: prove the table lookup spec.**

  ```lean
  theorem lookupLeaf_eq_some_of_nodup
      {entries : List (LeafId × Lara.Atom)} {l : LeafId} {a : Lara.Atom}
      (hkeys : (entries.map Prod.fst).Nodup) (hmem : (l, a) ∈ entries) :
      lookupLeaf entries l = some a

  theorem formulaLeafEntries_keys_nodup (φ : Formula3) :
      ((formulaLeafEntries φ).map Prod.fst).Nodup
  ```

  The second uses `encode_inj`, `Formula3.occurringVariables` duplicate-freedom (add
  `theorem occurringVariables_nodup` to `Lara/Complexity/Encoding.lean` if the merged file
  does not already expose it), and `List.zipIdx` index distinctness. Derive the three
  lookup corollaries the later tasks consume:

  ```lean
  theorem gammaOfFormula_negLit (φ : Formula3) {v : Nat}
      (hv : v ∈ φ.occurringVariables) :
      gammaOfFormula φ (negativeLiteralLeafId v) = some (litAtom 0 v)
  theorem gammaOfFormula_posLit (φ : Formula3) {v : Nat}
      (hv : v ∈ φ.occurringVariables) :
      gammaOfFormula φ (positiveLiteralLeafId v) = some (litAtom 1 v)
  theorem gammaOfFormula_occurrence (φ : Formula3) {c : Clause3} {j : Nat}
      {l : Literal} {p : Nat}
      (hc : (c, j) ∈ φ.zipIdx) (hl : (l, p) ∈ c.literals.zipIdx) :
      gammaOfFormula φ (occurrenceLeafId j p) =
        some (occAtom (literalSign l) l.«variable»)
  theorem gammaOfFormula_query (φ : Formula3) :
      gammaOfFormula φ queryLeafId = some queryAtom
  ```

- [ ] **Step 4: prove ground coverage.**

  ```lean
  theorem groundOfFormula_covers (φ : Formula3) :
      Realizability.GroundCoversUsedLeaves (gammaOfFormula φ)
        (groundOfFormula φ) (rawUnitOfFormula φ).args
  ```

  `groundOfFormula` is the `Prod.snd` projection of the same table `gammaOfFormula` reads,
  so every successful lookup's atom is a member by `List.mem_map`.
- [ ] **Step 5: re-point the Examples file and check both.** In
  `Lara/Examples/Complexity/Realization.lean`, delete the moved definitions, import
  `Lara.Complexity.Gadget`, and leave `rawUnitOfFormula_shape` and every closed fixture
  with their statements byte-identical. Run
  `cd lean && lake env lean Lara/Complexity/Gadget.lean` and
  `cd lean && lake env lean Lara/Examples/Complexity/Realization.lean`. Expect success —
  the unchanged shape fixture is the proof the move preserved every spelling.
- [ ] **Step 6: commit.**

  ```text
  theory(M2b): move the formula gadget behind a closed leaf vocabulary (#209)

  Plan step 2/13: Gadget module and leaf-table lemmas
  ```

### Task 3: duplicate-freedom and well-sortedness of the generated unit

**Files:** modify `lean/Lara/Complexity/Gadget.lean`.

- [ ] **Step 1: prove args duplicate-freedom.**

  ```lean
  theorem formulaArguments_nodup (φ : Formula3) :
      (rawUnitOfFormula φ).args.Nodup
  ```

  Prove per-block Nodup (literal leaves via `encode_inj` + `occurringVariables_nodup`;
  clause instances via distinct `J` bindings — `numTerm` injective by `natRepr_inj` — over
  distinct `zipIdx` indices), then pairwise block disjointness (leaf vs `.inst` constructor
  shapes; `queryLeafId` distinct from every literal leaf id by `encode_inj`), then
  `List.Nodup.append`.
- [ ] **Step 2: prove the sorts stage.**

  ```lean
  theorem groundOfFormula_wellSorted (φ : Formula3) :
      Lara.groundWellSorted m2bSigma (groundOfFormula φ) = true
  theorem formulaArguments_wellSorted (φ : Formula3) :
      Lara.argsWellSorted m2bSigma m2bPolicy (rawUnitOfFormula φ).args = true
  theorem signatureStage_formula_none (φ : Formula3) :
      Check.Unit.signatureStage (groundOfFormula φ) (rawUnitOfFormula φ) = none
  ```

  Ground atoms are `litAtom`/`occAtom`/`queryAtom` with `.num` arguments and
  `Sigma.sortOf` maps every `.num` payload to `some .num` without inspecting the string, so
  per-generator lemmas parameterized by the `Nat` payloads close by `simp`; lift over
  `flatMap`/`append` with `List.all_eq_true`. For args: leaves are immediate; the clause
  instance needs `Sigma.ruleParamSorts m2bSigma m2bClauseRule = some env` (closed, by
  `decide`) and `thetaWellSorted` of `clauseSubst j c`, whose seven concrete keys reduce
  structurally for arbitrary numeric payloads. `signatureStage_formula_none` then follows
  by unfolding `signatureStage` with `m2bSigma_wellFormed`, `m2bPolicy_wellSorted`, and the
  two new facts.
- [ ] **Step 3: check and commit.** Run
  `cd lean && lake env lean Lara/Complexity/Gadget.lean`. Expect success. Commit:

  ```text
  theory(M2b): prove family-wide Nodup and sort obligations (#209)

  Plan step 3/13: Structural checker premises
  ```

### Task 4: recursive support for the generated arguments

**Files:** modify `lean/Lara/Complexity/Gadget.lean`.

- [ ] **Step 1: prove leaf support.**

  ```lean
  theorem hasSupport_gadgetLeaf (φ : Formula3) {l : LeafId} {a : Lara.Atom}
      (hlookup : gammaOfFormula φ l = some a) :
      Support.HasSupport id m2bPolicy.ruleLookup (gammaOfFormula φ)
        (Support.certOkOf m2bRegistry) (.leaf l) a []
  ```

  Direct application of the `HasSupport.leaf` constructor.
- [ ] **Step 2: prove clause-instance support.**

  ```lean
  theorem hasSupport_clauseArgument (φ : Formula3) {c : Clause3} {j : Nat}
      (hc : (c, j) ∈ φ.zipIdx) :
      Support.HasSupport id m2bPolicy.ruleLookup (gammaOfFormula φ)
        (Support.certOkOf m2bRegistry) (clauseArgument j c) (clauseAtom j) []
  ```

  Apply `HasSupport.inst` with rule lookup `m2bClauseRuleId ↦ m2bClauseRule` (closed, by
  `decide` on the fixed policy), the exact-domain fact for `clauseSubst` (its seven keys
  are literally the rule's parameter list), empty discharge lists, and the three premise
  matches: instantiating the rule's `occ(Sᵢ, Xᵢ)` patterns under `clauseSubst j c`
  computes — structurally, for arbitrary payloads — to
  `occAtom (literalSign lᵢ) lᵢ.«variable»`, which is each occurrence leaf's conclusion by
  `gammaOfFormula_occurrence`. Package the instantiation computations as standalone `simp`
  lemmas parameterized by the clause data so Task 6 reuses them.
- [ ] **Step 3: assemble the support premise.**

  ```lean
  theorem formulaArguments_supported (φ : Formula3) :
      ∀ w ∈ (rawUnitOfFormula φ).args, ∃ C,
        Support.HasSupport id m2bPolicy.ruleLookup (gammaOfFormula φ)
          (Support.certOkOf m2bRegistry) w C []
  ```

  Case-split membership across the three generated blocks.
- [ ] **Step 4: check and commit.** Run
  `cd lean && lake env lean Lara/Complexity/Gadget.lean`. Expect success. Commit:

  ```text
  theory(M2b): prove recursive support across the generated family (#209)

  Plan step 4/13: Support premises
  ```

### Task 5: typed attacks and endpoint membership

**Files:** modify `lean/Lara/Complexity/Gadget.lean`.

- [ ] **Step 1: prove the three positive attack families.**

  ```lean
  theorem hasAttack_formula (φ : Formula3) :
      ∀ k ∈ (rawUnitOfFormula φ).atts,
        Attack.HasAttack id m2bPolicy.ruleLookup (gammaOfFormula φ)
          (Support.certOkOf m2bRegistry) m2bPolicy.defeat k
  ```

  Three sub-lemmas, one per generator: (a) mutual literal-root undermines fire through the
  `lit(0,X) → lit(1,X)` / `lit(1,X) → lit(0,X)` schema rows; (b) positional undermines
  `[.prem p]` fire through `lit(S,X) → occ(S,X)` between the literal root's conclusion and
  the occurrence subterm's conclusion at that premise path; (c) clause-root undermines of
  `query` fire through `clause(J) → query`. Each `ContraryMatch` instance is a pattern
  match with the payload bound once, so the positive direction closes by `simp` lemmas
  parameterized by `(sign, varIdx, j, p)` — no injectivity needed here. The closed
  directionality theorems in `Lara/Complexity/Context.lean` (`lit_attacks_occ`,
  `clause_attacks_query`, …) stay as regressions; they do not substitute for these
  parameterized versions.
- [ ] **Step 2: prove endpoint membership.**

  ```lean
  theorem formulaAttacks_source_mem (φ : Formula3) :
      ∀ k ∈ (rawUnitOfFormula φ).atts, k.source ∈ (rawUnitOfFormula φ).args
  theorem formulaAttacks_target_mem (φ : Formula3) :
      ∀ k ∈ (rawUnitOfFormula φ).atts, k.target ∈ (rawUnitOfFormula φ).args
  ```

  Pure list bookkeeping over the `flatMap`/`map`/`append` generators: every attack source
  is a literal root, clause instance, or clause root that the matching argument generator
  emits for the same membership witness; every target is a literal root, clause instance,
  or the query leaf.
- [ ] **Step 3: check and commit.** Run
  `cd lean && lake env lean Lara/Complexity/Gadget.lean`. Expect success. Commit:

  ```text
  theory(M2b): type every generated attack and its endpoints (#209)

  Plan step 5/13: Attack premises
  ```

### Task 6: exact attack completeness

**Files:** modify `lean/Lara/Complexity/Gadget.lean`.

This is the highest-risk task; every lemma it needs from Tasks 1–5 exists by now.

- [ ] **Step 1: prove root-conclusion determination.**

  ```lean
  theorem formulaArgument_conclusion (φ : Formula3) {w : SupportTerm} {C : Lara.Atom}
      (hw : w ∈ (rawUnitOfFormula φ).args)
      (hs : Support.HasSupport id m2bPolicy.ruleLookup (gammaOfFormula φ)
        (Support.certOkOf m2bRegistry) w C []) :
      (∃ v ∈ φ.occurringVariables,
          (w = negativeLiteralArg v ∧ C = litAtom 0 v) ∨
          (w = positiveLiteralArg v ∧ C = litAtom 1 v)) ∨
      (∃ c j, (c, j) ∈ φ.zipIdx ∧ w = clauseArgument j c ∧ C = clauseAtom j) ∨
      (w = queryArg ∧ C = queryAtom)
  ```

  Invert `HasSupport` (leaf case: the Γ lookup pins `C`; inst case: the side-condition
  record pins the rule and hence `C = clauseAtom j`).
- [ ] **Step 2: characterize `ContraryMatch` over root conclusions.** Prove the inversion
  lemma: for atoms drawn from `{litAtom s v, clauseAtom j, queryAtom}` (the root
  conclusions of Step 1), `Attack.ContraryMatch id m2bPolicy.defeat p q` holds **iff**
  `(p, q) = (litAtom 0 v, litAtom 1 v)` or `(litAtom 1 v, litAtom 0 v)` for some `v`, or
  `(p, q) = (clauseAtom j, queryAtom)` for some `j`. The forward direction case-splits the
  six schema rows: the `d`/`b`/`a` rows cannot match any gadget predicate key; the
  `lit → occ` row cannot match because `occAtom` is not a root conclusion; the two
  `lit ↔ lit` rows force equal variable payloads **by `natRepr_inj`** (the schema binds
  `X` twice, so the two decimal strings are equal); the `clause → query` row is immediate.
  This step is where numeral injectivity is load-bearing: without it, two distinct
  variables with equal reprs would demand an undeclared attack.
- [ ] **Step 3: prove coverage and assemble.**

  ```lean
  theorem formulaAttacks_complete (φ : Formula3) :
      Compile.AttackComplete id m2bPolicy.ruleLookup (gammaOfFormula φ)
        (Support.certOkOf m2bRegistry) m2bPolicy.defeat
        (rawUnitOfFormula φ).args (rawUnitOfFormula φ).atts
  ```

  For each firing pair from Step 2, exhibit the declared attack (`literalRootAttacks` for
  the mutual pair — membership needs `v ∈ φ.occurringVariables`, which Step 1's
  characterization supplies; the clause-root undermine of `query` for the second family)
  and conclude `Covered`. Pairs where `ConflictAttackable` fails need no witness; do not
  prove it holds where it is not needed.
- [ ] **Step 4: check and commit.** Run
  `cd lean && lake env lean Lara/Complexity/Gadget.lean`. Expect success. Commit:

  ```text
  theory(M2b): prove exact attack completeness for the gadget (#209)

  Plan step 6/13: Attack completeness
  ```

### Task 7: the family-wide checker equation

**Files:** modify `lean/Lara/Complexity/Gadget.lean`, `lean/Lara.lean`,
`lean/AxCheck.lean`.

- [ ] **Step 1: assemble acceptance.**

  ```lean
  theorem checkUnit_formula_accepts (φ : Formula3) :
      ∃ accepted, Check.Unit.checkUnit (gammaOfFormula φ) m2bRegistry
        (groundOfFormula φ) (rawUnitOfFormula φ) = .ok accepted
  ```

  One application of `Check.Unit.checkUnit_complete` with `signatureStage_formula_none`,
  `m2bPolicy_scopesWellFormed`, `m2bPolicy_ruleIds_unique`, `m2bPolicy_noViolation` (via
  `Policy.firstViolation_none_iff`), `formulaArguments_nodup`,
  `formulaArguments_supported`, `hasAttack_formula`, `formulaAttacks_source_mem`,
  `formulaAttacks_target_mem`, and `formulaAttacks_complete`.
- [ ] **Step 2: name the accepted unit and state the plan's headline theorem.**

  ```lean
  def acceptedUnitOfFormula (φ : Formula3) :
      Lara.Unit.CheckedUnit id (gammaOfFormula φ) (Support.certOkOf m2bRegistry) :=
    (Check.Unit.checkUnit (gammaOfFormula φ) m2bRegistry
      (groundOfFormula φ) (rawUnitOfFormula φ)).toOption.get
      (by obtain ⟨accepted, h⟩ := checkUnit_formula_accepts φ; simp [h])

  theorem checkUnit_formula_ok (φ : Formula3) :
      Check.Unit.checkUnit (gammaOfFormula φ) m2bRegistry
        (groundOfFormula φ) (rawUnitOfFormula φ) = .ok (acceptedUnitOfFormula φ) := by
    obtain ⟨accepted, h⟩ := checkUnit_formula_accepts φ
    simpa [acceptedUnitOfFormula, h] using
      congrArg (Option.get · (by simp [h])) (congrArg Except.toOption h)
  ```

  (If the final `simpa` needs massaging, the `Option.get_of_eq_some` pattern from
  `acceptedPathUnit` in the Examples file is the working precedent.)
- [ ] **Step 3: register and gate-import.** Add `import Lara.Complexity.Numeral` and
  `import Lara.Complexity.Gadget` to `lean/Lara.lean`; add an
  `M2b follow-up — realization closure (issue #209)` section to `lean/AxCheck.lean` with
  `#print axioms` for `natRepr_inj`, `GadgetLeaf.encode_inj`,
  `formulaLeafEntries_keys_nodup`, `groundOfFormula_covers`, `formulaArguments_nodup`,
  `signatureStage_formula_none`, `formulaArguments_supported`, `hasAttack_formula`,
  `formulaAttacks_complete`, and `checkUnit_formula_ok`.
- [ ] **Step 4: run the full gates and commit.** Run `cd lean && lake build` (expect all
  jobs, no `sorry`) and `cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh`
  (expect only the standard trio). Commit:

  ```text
  theory(M2b): close the family-wide realization checker equation (#209)

  Plan step 7/13: checkUnit_formula_ok
  ```

### Task 8: compile image, promise, size — and the renewed gate

**Files:** modify `lean/Lara/Complexity/Gadget.lean` (or create
`lean/Lara/Complexity/Reduction.lean` early if the image proofs want their own seam),
`docs/theory-m2b-complexity-spike.md`, and this plan's status banner.

- [ ] **Step 1: prove the compilation image.** Define `reduceCode φ : CarrierCode` listing
  the gadget nodes in declaration order and the intended adjacency matrix, and prove a
  `StructuredAFIso` from `Invariants.compileUnit (acceptedUnitOfFormula φ)` to
  `(reduceCode φ).decode` whose edge relation has exactly the gadget edges — mutual
  literal pairs, satisfying-literal-to-clause edges (positional undermines compile to
  edges on the clause argument), clause-to-query edges — and no closure-generated extras.
- [ ] **Step 2: prove the promise and size obligations.**

  ```lean
  theorem reduce_realizable (φ : Formula3) : M2bPromise (reduceCode φ)
  theorem reduce_nodes (φ : Formula3) :
      (reduceCode φ).nodes.length = 2 * variableCount φ + φ.length + 1
  theorem reduce_byteSize (φ : Formula3) :
      (reduceCode φ).byteSize ≤ 64 * (Formula3.byteSize φ + 1) ^ 2
  ```

  `reduce_realizable` packages the `Realization` record from `checkUnit_formula_ok`,
  `groundOfFormula_covers`, `rawUnitOfFormula_fixedFields`, and Step 1's iso. The constant
  `64` is inherited from the predecessor's engineering-cleared statement; if the proof
  finds it false, return to review — do not silently change the theorem.
- [ ] **Step 3: decide the gate from proof artifacts.** Record exactly one D9 outcome in
  `docs/theory-m2b-complexity-spike.md` (a dated "renewed gate" section that supersedes
  the 2026-08-30 record and preserves it below) and in this plan's status banner. If every
  theorem in Tasks 7–8 exists without `sorry`: record `HARDNESS` and continue to Phase 2.
  Otherwise record the exact obstruction and STOP: keep #209 open, claim nothing, leave
  `lean/Lara.lean` importing only the modules that are complete.
- [ ] **Step 4: run gates, review, commit.** Run `cd lean && lake build` and the axiom
  audit. Dispatch spec and code-quality reviews. Commit:

  ```text
  theory(M2b): decide the renewed realization gate (#209)

  Plan step 8/13: Compile image and gate decision
  ```

---

## 6. Phase 2 tasks (execute only after Task 8 records HARDNESS)

Tasks 9–13 are the predecessor plan's engineering-cleared Tasks 3–7, restated in full with
only the issue number, step numbering, and file seams updated. The frozen decisions D3–D5
they depend on (grounded cost model, decision problems, source/output size) are in the
predecessor text at the named git object and are unchanged.

### Task 9: cost-instrumented grounded kernel with corrected bounds

**Files:** create `lean/Lara/Complexity.lean`; modify `lean/Lara.lean`.

- [ ] **Step 1: implement the instrumented mirrors.** Define `anyAttackerC`,
  `defendedAuxC`, `defendedC`, `stepC`, `iterC`, and `groundedC` with the exact recursive
  structure of `Grounded.defendedB`, `step`, `iter`, and `grounded`. Return
  `result × Nat`; increment only at each `F.attack` call.
- [ ] **Step 2: prove evaluator agreement.**

  ```lean
  theorem anyAttackerC_fst (F : AF) (S : List Arg) (b : Arg) :
      (anyAttackerC F S b).1 = S.any (fun c => F.attack c b)
  theorem defendedC_fst (F : AF) (S : List Arg) (a : Arg) :
      (defendedC F S a).1 = Grounded.defendedB F S a
  theorem stepC_fst (F : AF) (S : List Arg) : (stepC F S).1 = Grounded.step F S
  theorem iterC_fst (F : AF) (k : Nat) : (iterC F k).1 = Grounded.iter F k
  theorem groundedC_fst (F : AF) : (groundedC F).1 = Grounded.grounded F
  ```

- [ ] **Step 3: prove the upper bounds.** Using `Grounded.filter_length_le` for iterate
  length, prove:

  ```lean
  theorem anyAttackerC_cost_le : (anyAttackerC F S b).2 ≤ S.length
  theorem defendedC_cost_le :
      (defendedC F S a).2 ≤ F.args.length * (1 + S.length)
  theorem stepC_cost_le :
      (stepC F S).2 ≤ F.args.length * (F.args.length * (1 + S.length))
  theorem groundedC_cost_le :
      (groundedC F).2 ≤ F.args.length ^ 3 * (1 + F.args.length)
  ```

- [ ] **Step 4: prove the corrected lower bounds.**

  ```lean
  theorem defendedC_cost_ge_one (h : 0 < F.args.length) : 1 ≤ (defendedC F S a).2
  theorem stepC_cost_ge : F.args.length ≤ (stepC F S).2
  theorem groundedC_cost_ge : F.args.length ^ 2 ≤ (groundedC F).2
  ```

  Add the two-node all-attacks evaluation showing grounded cost `4`; this negative
  regression must remain next to the lower theorem.
- [ ] **Step 5: run and commit.** Run `cd lean && lake build`. Commit:

  ```text
  theory(M2b): prove corrected grounded query bounds (#209)

  Plan step 9/13: Grounded query bounds
  ```

### Task 10: fixed-context realizable quartic witness

**Files:** create `lean/Lara/Examples/Complexity.lean`; modify `lean/Lara.lean`.

- [ ] **Step 1: define the three-block carrier.** Define `quarticAF 0` as the empty
  carrier. For `k + 1`, use `3*(k+1)` arguments in declaration order: `k` neutral `g`
  nodes followed by `d`, then `k+1` `b` nodes, then `k+1` `a` nodes. Edges are exactly
  `d → b(i)` and `b(i) → a(j)` for all `i, j < k+1`.
- [ ] **Step 2: build the raw unit under the fixed context.** Use leaf support terms only
  and explicit undermine declarations for every edge. Prove the checker equation, ground
  coverage, and a `StructuredAFIso`. Then prove:

  ```lean
  theorem quartic_realizable (k : Nat) :
      Realizability.Realizable id m2bSigma m2bPolicy m2bRegistry (quarticAF k)
  theorem quartic_size (k : Nat) : (quarticAF k).size = 3 * k
  ```

- [ ] **Step 3: prove the iterate shape.** Prove round one contains exactly the defender
  block and every later round contains the defender and target blocks. The declaration
  order places `d` last in the first block, so every defense of a `b` scans all `k`
  defenders.
- [ ] **Step 4: prove quartic cost.** For `2 ≤ k`:

  ```lean
  theorem quartic_cost_ge (k : Nat) (hk : 2 ≤ k) :
      k ^ 4 ≤ (groundedC (Invariants.eraseAF (quarticAF k))).2
  ```

  Together with `quartic_size` and `groundedC_cost_le`, document this as worst-case Θ(n⁴)
  over the fixed-context realizable class, not as a universal per-instance floor.
- [ ] **Step 5: evaluate and commit.** Evaluate `k = 2, 3, 4` and assert the theorem's
  inequality in Lean. Run `cd lean && lake build`. Commit:

  ```text
  theory(M2b): realize the quartic grounded witness (#209)

  Plan step 10/13: Realizable quartic tightness
  ```

### Task 11: shared carrier-status evaluator

**Files:** modify `lean/Lara/Complexity.lean` and `lean/Lara/Examples/Complexity.lean`.

- [ ] **Step 1: factor labels over one grounded result.** Define
  `labelFromGroundedC F G a : Label × Nat`; count only the attack queries in the `out`
  scan. Prove its first projection equals `Grounded.labelC F a` when
  `G = Grounded.grounded F`.
- [ ] **Step 2: define shared status.** Define `statusSharedC F c : Status × Nat`.
  Preserve `Grounded.statusC` guard order: empty support first, then an `inn` pass, then
  an `undec` pass, then `defeated`. Compute `groundedC F` at most once and only after the
  empty-support guard.
- [ ] **Step 3: prove agreement and the generic internal bound.**

  ```lean
  theorem statusSharedC_fst (F : AF) (c : Claim) :
      (statusSharedC F c).1 = Grounded.statusC F c
  theorem statusSharedC_cost_le (F : AF) (c : Claim) :
      (statusSharedC F c).2 ≤
        F.args.length ^ 3 * (1 + F.args.length) + 2 * c.support.length * F.args.length
  ```

- [ ] **Step 4: expose only the carrier query.** Define
  `carrierStatusC canon F p := statusSharedC (eraseAF F) (claim canon F p)`. Prove
  `Invariants.support` has length at most `F.size`, then prove:

  ```lean
  theorem carrierStatusC_fst :
      (carrierStatusC canon F p).1 = Invariants.status canon F p
  theorem carrierStatusC_cost_le :
      (carrierStatusC canon F p).2 ≤ F.size ^ 3 * (1 + F.size) + 2 * F.size ^ 2
  ```

  This is the paper-citable GroundedStatus upper theorem. Do not cite the generic Claim
  bound as the restricted-class headline.
- [ ] **Step 5: transfer quartic tightness to carrier status.** In
  `lean/Lara/Examples/Complexity.lean`, use the nonempty carrier claim for the unique `d`
  node. Prove that `carrierStatusC` takes the grounded branch and its count includes the
  complete `groundedC` count, then prove:

  ```lean
  theorem carrierStatus_quartic_cost_ge (k : Nat) (hk : 2 ≤ k) :
      k ^ 4 ≤ (carrierStatusC id (quarticAF k) dAtom).2
  ```

  Together with `quartic_size` and `carrierStatusC_cost_le`, this is the tight worst-case
  degree result for the actual carrier-status surface.
- [ ] **Step 6: run and commit.** Run `cd lean && lake build`. Commit:

  ```text
  theory(M2b): share grounded work in carrier status (#209)

  Plan step 11/13: Carrier status query
  ```

### Task 12: fixed-policy 3SAT reduction correctness

**Gate:** requires Task 8 `HARDNESS` and its `reduceCode`, `reduce_realizable`, and
`reduce_byteSize`.

**Files:** create `lean/Lara/Complexity/Reduction.lean`; modify `lean/Lara.lean`.

- [ ] **Step 1: define satisfiability over explicit syntax.** Define a Boolean assignment
  over variable indices, literal evaluation, clause evaluation, and
  `Formula3.Satisfiable`. Add executable positive and negative formulas that exercise
  both signs and repeated variables.
- [ ] **Step 2: characterize conflict-free literal choices.** Prove that any admissible
  extension containing `query` contains no complementary literal pair. Extract the
  induced partial assignment and extend it with `false` for unchosen variables.
- [ ] **Step 3: prove soundness.** From a complete extension containing `query`, use
  defense against every attacking clause argument to obtain a satisfying literal for
  every clause; show the extracted assignment satisfies the formula.
- [ ] **Step 4: prove completeness.** From a satisfying assignment, build the set
  containing `query` and exactly one literal per occurring variable. Prove directly that
  it is complete: chosen literals defend themselves against their complements; they
  defend `query` by attacking at least one occurrence in every clause; unchosen literals
  and clause arguments are not defended. Do not assume an unproved
  admissible-to-complete extension lemma.
- [ ] **Step 5: state the end-to-end theorem.**

  ```lean
  theorem reduce_correct (φ : Formula3) :
      Formula3.Satisfiable φ ↔ FixedCredComplete (reduceCode φ)
  ```

  State adjacent corollaries quoting `reduce_realizable`, `reduce_nodes`, and
  `reduce_byteSize`. Do not state NP-completeness inside Lean; the complexity-class
  bookkeeping remains paper-level and cites these mechanized obligations.
- [ ] **Step 6: add a class-membership negative control.** Define a one-node self-edge
  carrier labelled `g(0)`. Prove it is not realizable under the fixed M2b context:
  `Compile.edge_iff` would require a typed attack, while no contrary schema or exception
  in `m2bPolicy` licenses `g(0) → g(0)`. This prevents the reduction result from being
  presented as a theorem about unrestricted AFs.
- [ ] **Step 7: run and commit.** Run `cd lean && lake build`. Commit:

  ```text
  theory(M2b): reduce 3SAT inside the fixed realizable class (#209)

  Plan step 12/13: Fixed-policy hardness reduction
  ```

### Task 13: registration, documentation, and closeout

**Gate:** execute only after Tasks 1–12 pass both review stages.

**Files:** modify `lean/AxCheck.lean`, `src/Lara/Runtime.hs`,
`docs/paper-lean-name-map.md`; create `docs/theory-m2b-complexity.md`; delete this plan at
successful closeout.

- [ ] **Step 1: register all proof surfaces.** Import completed M2b modules in
  `lean/AxCheck.lean`. Extend the issue-#209 section with `#print axioms` for every
  agreement, bound, realization, size, adequacy, and reduction theorem introduced in
  Tasks 8–12.
- [ ] **Step 2: correct Runtime prose.** Replace the `Runtime.hs` cubic claim with the
  proved facts: universal query cost lies between `n²` and `n³(1+n)`; the fixed-context
  realizable three-block family attains quartic worst-case degree for both grounded
  evaluation and the nonempty carrier-status query. Cite `groundedC_cost_ge`,
  `groundedC_cost_le`, `quartic_realizable`, `quartic_cost_ge`, and
  `carrierStatus_quartic_cost_ge`. Do not claim the production Haskell runtime was
  instrumented.
- [ ] **Step 3: update the paper name map.** Add rows for `carrierStatusC_fst`,
  `carrierStatusC_cost_le`, `carrierStatus_quartic_cost_ge`, `groundedC_cost_le`,
  `groundedC_cost_ge`, `quartic_realizable`, `quartic_cost_ge`, `reduce_realizable`,
  `reduce_byteSize`, `reduce_correct`, and `checkUnit_formula_ok`. Add "Not X" notes:
  `Grounded.deficit_bound` bounds rounds, not queries; generic `statusSharedC_cost_le` is
  internal; `CompilerInvariant` alone is not class membership.
- [ ] **Step 4: write the durable decision record.** In
  `docs/theory-m2b-complexity.md`, record the inherited D1–D6 and new D7–D9 decisions,
  both gate records, the compositional-lemma architecture that closed the realization
  theorem, the distinction between universal quadratic floor and worst-case quartic
  tightness, the shared carrier-status bound, and the exact mechanized/paper-level
  boundary. State explicitly that no general-AF hardness theorem was transferred without
  a fixed-context realization proof.
- [ ] **Step 5: run repository gates.**

  ```text
  make build test semantics-goldens backend-deps-golden update-goldens update-differential
  cd lean && lake build
  cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh
  ```

  Expect every command to pass and the axiom audit to report only the standard trio.
- [ ] **Step 6: close out.** Check #209's acceptance boxes but leave the issue open for
  maintainer review. Re-adjudicate C44/C45 statuses through the research-manager
  epilogue. Delete this plan because the durable record now exists. Commit:

  ```text
  docs(M2b): register restricted-class complexity closure (#209)

  Plan step 13/13: Registration and closeout
  ```

---

## 7. Validation layers

1. **Executable class membership.** Every reduction output and lower-bound witness has a
   `Realization` with an actual `checkUnit = .ok accepted` equation and a
   `StructuredAFIso`; `CompilerInvariant` is never substituted for realizability.
2. **Shape-fixture regression.** `rawUnitOfFormula_shape` stays byte-identical in
   statement across the Task 2 module move; a definitional drift in the gadget fails it.
3. **Instrumented-evaluator agreement.** First-projection theorems tie every cost result
   to the existing grounded evaluator and shared carrier status to `Invariants.status`.
4. **Tight degree with distinct quantifiers.** `groundedC_cost_ge` is a universal
   quadratic floor; `quartic_cost_ge` and `carrierStatus_quartic_cost_ge` are existential
   worst-case results on a fixed-context realizable family. Documentation must not merge
   them.
5. **Finite reduction accounting.** `Formula3.byteSize` tracks encoded byte length;
   `CarrierCode.byteSize` is the frozen carrier accounting measure; the target matrix
   contribution is quadratic; the policy is constant across all instances.
6. **Reduction correctness.** `reduce_correct` is two-sided; `reduce_realizable` and
   `reduce_byteSize` sit adjacent so the paper cannot quote correctness without class
   membership and polynomial output size.
7. **Axiom and regression gates.** All new theorem surfaces pass AxCheck without `sorry`
   and within the standard trio; the two-node all-attacks counterexample remains as a
   regression against the rejected cubic floor.

**Definition of done:** Task 8 records `HARDNESS`; Tasks 1–13 pass spec and quality
review; all validation layers pass; the durable decision record and name map match the
Lean statements; C44/C45 are re-adjudicated; and the PR references #209. A second
`INCONCLUSIVE` at Task 8 is a valid scientific result but is not completion of #209 and
stops this plan before Phase 2 with the obstruction recorded.
