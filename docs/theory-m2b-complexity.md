# M2b restricted-class complexity — decision record

Issue #209 (parent tracker #180; successor to the closed #181).
Branch `theory/m2b-realization-closure`. Gate history:
[`docs/theory-m2b-complexity-spike.md`](theory-m2b-complexity-spike.md).
Paper citation keys: the "M2b restricted-class complexity closure" section of
[`docs/paper-lean-name-map.md`](paper-lean-name-map.md).

This is the durable record of the M2b complexity closure: the frozen
decisions (inherited D1–D6, new D7–D9), both gate decisions, the
compositional-lemma architecture that closed the family-wide realization
theorem, the cost results with their quantifier boundary, and the exact
mechanized/paper-level split. The implementation plan that produced it
(`plans/2026-08-30-m2b-realization-followup.md`) was deleted at closeout; it
is preserved verbatim at git object
`8155ec7:plans/2026-08-30-m2b-realization-followup.md`, so the "Task N"
numbering used below stays recoverable. Its predecessor is preserved at git
object
`17d07ffec693797b4b39599e787723328fa3f61f:plans/2026-08-29-m2b-restricted-class-complexity.md`.
Lean module doc-comments cite this record and issue #209, never the deleted
plans.

## Module inventory

All `sorry`-free, within the standard axiom trio, and registered in
`lean/AxCheck.lean` (issue-#209 section):

- `lean/Lara/Complexity/Numeral.lean` — verified decimal round-trip and
  `natRepr_inj` (D7).
- `lean/Lara/Complexity/Gadget.lean` — the formula-indexed 3SAT gadget
  behind a closed leaf vocabulary (D8), the family-wide
  `checkUnit_complete` premises, and the assembled checker equation
  `checkUnit_formula_ok`.
- `lean/Lara/Complexity/Reduction.lean` — the compile image (`reduceCode`,
  `reduceIso`, `coveredB_gadget`), the frozen promise/size obligations
  (`reduce_realizable`, `reduce_nodes`, `reduce_byteSize`), reduction
  correctness (`reduce_correct` and its quoting corollaries), executable
  fixtures, and the class-membership negative control
  (`selfEdgeCode_not_realizable`).
- `lean/Lara/Complexity.lean` — the cost-instrumented grounded kernel and
  the shared carrier-status evaluator.
- `lean/Lara/Examples/Complexity.lean` — the fixed-context realizable
  quartic witness and the carrier-status transfer.

The formula-independent fixed context (`Lara/Complexity/Context.lean`) and
the finite encodings (`Lara/Complexity/Encoding.lean`) predate this closure
(issue #208) and were frozen and untouched throughout.

## Inherited constraints (D1–D6)

Carried from the predecessor plan's motivation/CEO review, the spike record,
and the crystallized boundaries (`ara/logic/claims.md#C44`, `#C45`;
`ara/logic/solution/constraints.md`, M2b section). Reintroducing any
rejected form requires a new review.

- **D1 — The fixed context is frozen.** Every theorem uses exactly
  `canon := id`, `m2bSigma`, `m2bPolicy`, `m2bRegistry`. No
  formula-specific policy, signature, registry, axiom, `sorry`, or
  placeholder. A construction that needs a per-instance policy changes the
  class being studied and is out of scope (C45).
- **D2 — The INCONCLUSIVE record is not evidence.** Nothing may reinterpret
  the 2026-08-30 spike as support for hardness or tractability. Only closed
  proofs move C44/C45.
- **D3 — A restricted-class witness carries class membership.** Tightness
  and hardness claims require the executable checker equation and a
  `StructuredAFIso` under the fixed context — `CompilerInvariant` alone is
  never substituted for realizability.
- **D4 — The proved universal lower bound is quadratic**; the two-node
  regression refutes only the rejected exact pointwise `n³` inequality at
  `n = 2`. Quartic statements are existential worst-case results on a
  realizable family. Documentation must never merge the two quantifiers.
- **D5 — Oracle cost and classical input size use separate frozen
  representations.** `CarrierCode.byteSize` is a carrier accounting measure
  (framing unit + atom-key text + matrix cells + query-index text), not a
  serialized wire length; `Formula3.byteSize` is the UTF-8 length of the
  canonical S-expression.
- **D6 — The stop rule binds.** The realization gate has three outcomes
  (D9); on INCONCLUSIVE, record the exact obstruction, stop before the
  hardness phase, keep the issue open, claim nothing.

## New frozen decisions (D7–D9)

- **D7 — Numeral injectivity comes from a verified decoder round-trip.**
  `natRepr_inj : Nat.repr m = Nat.repr n → m = n` is proved by applying a
  decoder with a proven round-trip, never by induction over string
  representations. The decoder is a local copy of the two-line `decodeNat`
  pattern from `Lara.ND` (round-trip by `simp [decodeNat]` with
  `Std.Data.String.ToNat` imported). It lives in
  `lean/Lara/Complexity/Numeral.lean` rather than importing `Lara.ND`, so
  the complexity spine does not depend on the natural-deduction backend
  module (module-ownership seam; the ND precedent is cited in the module
  docstring).
- **D8 — The gadget lives in the library behind a closed-sum leaf
  vocabulary.** `rawUnitOfFormula`, `gammaOfFormula`, `groundOfFormula`,
  and their helpers moved from `Lara/Examples/Complexity/Realization.lean`
  into the public `Lara.Complexity.Gadget`, because `reduceCode` and
  `Reduction.lean` (library code) must reference them and library code must
  not import `Examples`. The move is definitional-identity: every leaf-id
  spelling stays exactly as the merged shape fixture pins it, and
  `rawUnitOfFormula_shape` (still in the Examples file, byte-identical in
  statement) is the regression that proves it. Per the repo's symbolic-core
  discipline the leaf namespace is a closed sum type `GadgetLeaf`
  (`negLit`, `posLit`, `occurrence`, `query`) with the single injective
  encode table `GadgetLeaf.encode`; the string builders
  (`negativeLiteralLeafId` etc.) are `GadgetLeaf.encode ∘ constructor`, so
  exactly one spelling table exists.
- **D9 — The renewed gate.** The gate was re-decided from proof artifacts
  alone, recording exactly one of `HARDNESS` / `TRACTABILITY CANDIDATE` /
  `INCONCLUSIVE` in `docs/theory-m2b-complexity-spike.md` (superseding, not
  deleting, the earlier record); only `HARDNESS` unlocked the hardness
  phase. `TRACTABILITY CANDIDATE` would still have required an
  independently proved structure theorem; a failed lemma is not one (C45).

## Gate history

Both records live in full in
[`docs/theory-m2b-complexity-spike.md`](theory-m2b-complexity-spike.md):

1. **2026-08-30 — INCONCLUSIVE** (PR #208). The closed three-node path and
   two-cycle fixtures checked, but the family-wide checker equation
   `checkUnit_formula_ok` was not mechanized: the checker API exposes
   whole-program obligations, and the spike lacked compositional lifting
   lemmas for the mapped/flat-mapped formula lists. All compile-image,
   realizability, and size obligations were therefore not attempted, and
   the record explicitly bars treating itself as evidence (D2).
2. **2026-08-31 — HARDNESS** (this branch, issue #209). Every mandatory
   theorem named by the INCONCLUSIVE record's obstruction section exists
   `sorry`-free under the frozen context: `checkUnit_formula_ok`,
   `reduceIso` with the exact-edge theorem `coveredB_gadget`, and the
   frozen `reduce_realizable` / `reduce_nodes` / `reduce_byteSize` with the
   engineering-cleared constant `64` intact. HARDNESS names the gate
   outcome only — the reduction target family is realizable with
   polynomially bounded carrier accounting; `reduce_correct` came later
   (Task 12) and NP-completeness is not claimed in Lean at all (see the
   boundary below).

## The compositional-lemma architecture (realization closure)

Route A of the follow-up plan: prove each premise of the sanctioned
completeness surface `Check.Unit.checkUnit_complete`
(`lean/Lara/Check/Unit.lean`) as its own parameterized lemma family over
`rawUnitOfFormula φ`, then assemble once. The alternatives — manual
`CheckedUnit` construction (same obligations, weaker artifact, no
executable checker equation) and a replacement gadget (same family-wide
obligations, discards the shape fixture, needs a new motivation review) —
were rejected in review.

The premise-by-premise closure, in dependency order:

1. **Numeral foundation** (`Numeral.lean`): `decodeNat_repr`,
   `natRepr_inj`, `repr_no_dash` (a decimal repr contains no `'-'`, which
   pins the separator in the `occurrence` leaf spelling).
2. **Leaf vocabulary and table lookup** (`Gadget.lean`):
   `GadgetLeaf.encode_inj`, `formulaLeafEntries_keys_nodup`,
   `lookupLeaf_eq_some_of_nodup`, the four `gammaOfFormula_*` lookup
   corollaries, and ground coverage `groundOfFormula_covers`
   (`groundOfFormula` is the `Prod.snd` projection of the same table
   `gammaOfFormula` reads).
3. **Structural premises**: `formulaArguments_nodup` (per-block Nodup +
   pairwise block disjointness), `groundOfFormula_wellSorted`,
   `formulaArguments_wellSorted`, `signatureStage_formula_none`.
4. **Recursive support**: `hasSupport_gadgetLeaf`,
   `hasSupport_clauseArgument` (the fixed clause rule instantiated at
   `clauseSubst j c`, with the premise-conclusion matches packaged as
   reusable `simp` lemmas), assembled into `formulaArguments_supported`.
5. **Typed attacks and endpoints**: `hasAttack_formula` over the three
   generators (mutual literal-root undermines, positional undermines of
   occurrences, clause-root undermines of `query`), plus
   `formulaAttacks_source_mem` / `formulaAttacks_target_mem`.
6. **Exact attack completeness** (`formulaAttacks_complete`, the
   highest-risk step): invert `HasSupport` to pin every root conclusion
   (`formulaArgument_conclusion`), characterize `ContraryMatch` over root
   conclusions (`contraryMatch_rootConclusion_iff`), then exhibit each
   firing pair's declared attack. **Where numeral injectivity actually
   fires**: not in the `ContraryMatch` characterization itself — the two
   `lit ↔ lit` schema rows bind the payload variable once per row, so the
   positive direction is pattern computation — but in the *assembly*, where
   `litAtom_inj` (which is two applications of `natRepr_inj` to the `lit`
   atom's decimal payloads) forces equal variable indices when two root
   conclusions collide. Without it, two distinct variables with equal reprs
   would demand an undeclared attack.
7. **Assembly**: `checkUnit_formula_accepts` (one application of
   `checkUnit_complete` with the nine family lemmas plus the closed policy
   facts), the named accepted unit `acceptedUnitOfFormula`, and the
   headline equation `checkUnit_formula_ok`.

## Cost results and the quantifier boundary

`Lara.Complexity` mirrors `Grounded.defendedB`/`step`/`iter`/`grounded`
with an attack-query counter (`groundedC` etc.), with first-projection
agreement theorems (`*_fst`) tying every bound to the existing evaluator.

- **Short-circuit cost model (frozen).** The counter increments exactly
  once per `F.attack` evaluation, and the mirrors reproduce the
  left-to-right short-circuit evaluation the Boolean connectives actually
  perform (a defense scan stops at its first undefeated attacker; the inner
  attacker scan runs only after `F.attack b a` answered `true`). This is
  not a free choice: the frozen regression
  `groundedC_twoNodeAllAttacks_cost : (groundedC twoNodeAllAttacks).2 = 4`
  — the two-node all-attacks run costs exactly `4 = 2²` — holds only under
  short-circuit counting, and it is the negative regression that refutes
  the rejected exact pointwise cubic inequality at `n = 2`.
- **Universal bounds.** `groundedC_cost_le : cost ≤ n³(1 + n)` and
  `groundedC_cost_ge : n² ≤ cost` for every framework, `n = F.args.length`.
  The pre-existing prose claim that the grounded fixpoint "queries the
  oracle O(n³) times" was corrected in `src/Lara/Runtime.hs` to these
  proved facts; the production Haskell runtime itself is *not*
  instrumented.
- **Worst-case quartic tightness (existential).** The three-block family
  `quarticAF k` (`k−1` neutral `g` nodes then the defender `d`, then `k`
  attacked `b` nodes, then `k` target `a` nodes; edges exactly
  `d → b(i)` and `b(i) → a(j)`) is realizable in the fixed context
  (`quartic_realizable`, with `quartic_size : size = 3k`), and for `2 ≤ k`
  pays at least `k⁴` attack queries (`quartic_cost_ge`), with closed
  evaluations at `k = 2, 3, 4`. Together with `groundedC_cost_le` this is
  worst-case Θ(n⁴) *over the fixed-context realizable class* — never a
  universal per-instance floor (D4).
- **Shared carrier status.** `statusSharedC` computes the grounded
  extension once (only after the empty-support guard, preserving
  `Grounded.statusC`'s observable guard order), and `carrierStatusC` is the
  exposed carrier query over `Invariants.eraseAF`/`Invariants.claim`.
  Agreement: `carrierStatusC_fst = Invariants.status`. **Citation
  discipline**: `carrierStatusC_cost_le : cost ≤ n³(1 + n) + 2n²` (with
  `claim_support_length_le`) is the paper-citable GroundedStatus upper theorem;
  the generic Claim bound `statusSharedC_cost_le` is internal accounting
  and must not be cited as the restricted-class headline. The quartic floor
  transfers to this surface: `carrierStatus_quartic_cost_ge` (the `d`
  claim has nonempty complete support, so the grounded branch runs and is
  fully counted).
- **`Grounded.deficit_bound` bounds rounds, not queries.** It must not be
  quoted as a query-cost result.

## The mechanized / paper-level boundary

Mechanized, and only quotable together (the `reduce_correct_*` corollaries
package them):

- `reduce_correct : Formula3.Satisfiable φ ↔ FixedCredComplete (reduceCode φ)`
  — two-sided reduction correctness, with soundness extracting a satisfying
  assignment from a complete extension containing `query` and completeness
  building the model extension directly (no unproved admissible-to-complete
  lemma);
- `reduce_realizable : M2bPromise (reduceCode φ)` — class membership with
  the executable checker equation and `StructuredAFIso`;
- `reduce_nodes` and `reduce_byteSize` — polynomial output size under the
  frozen D5 measures.

Paper-level only: NP-completeness bookkeeping (encodings, machine model,
membership in NP). It is deliberately not a Lean statement; the paper cites
the mechanized obligations above.

**No general-AF transfer.** No hardness theorem about unrestricted
argumentation frameworks was transferred into an M2b claim without a
fixed-context realization proof. Every reduction output and every
lower-bound witness carries its own `Realization` under the frozen context
(D1, D3), and `selfEdgeCode_not_realizable` — the one-node `g(0)` self-edge
carrier is not `M2bPromise`-realizable because no `m2bPolicy` contrary row
licenses `g(0) → g(0)` — is the negative control that keeps the correctness
theorem a statement about the realizable class, not about all AFs.

## Follow-ups

Proof-side refactoring deferrals (shared id-canon/pattern helpers, the
checkUnit ok-assembly boilerplate, a possible correctness-half split of
`Reduction.lean`) are tracked in issue #211 (referencing #209); they have
no corpus or freeze-tag impact.
