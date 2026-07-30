# Result 9 — backend replacement: eraseCert + stable-argument-id mechanization

> **Outcome (2026-07-30): DONE — `lean/Lara/Erase.lean`, sorry-free, axioms ⊆ trio.**
> During design we found the informal doc proof glosses *intra-program subterm
> sharing*: `containsB` keys on exact structural equality (cert payload included),
> so per-argument erase-equality alone does **not** preserve the AF. The faithful,
> provable statement is **Model A — a uniform injective certificate relabel**
> (`mapAssur f`, `f` injective), which is exactly a backend swap (one payload per
> source step). The originally-sketched `EraseEq` relation below is subsumed by
> the injective-function framing (`mapAssur_eq_iff`). Final theorem:
> `backend_replacement` — relabeled programs share a definitionally equal
> `checkedAF`, hence equal statuses. Node bijection = identity on list positions.
> The doc's non-injective erase-to-`certified` marker is recorded as *not* an
> isomorphism. Purely additive; no wire/Haskell/differential change.

> Target: mechanize spec §9 result 9 / Theorem 2 (`docs/strict-backend-decision.md:274`).
> Status ledger blocker: `ara/evidence/status/mechanization_status.md` result 9
> ("paper-proved; statement-model blocker"), `lean/README.md` result-9 row.
> Standing obligation under the CLAUDE.md mechanization discipline.

## Goal (Theorem 2, verbatim intent)

Source-identical programs whose backend certificates accept the same strict
instances compile to AFs **isomorphic under certificate erasure** and produce
**equal claim statuses**. Formally: given checked programs `P_β`, `P_γ` that are
equal after erasing strict-certificate payloads, and whose certificates accept
the same strict instances, `compile(P_β) ≅ compile(P_γ)` under the node
bijection induced by equal erased skeletons, and every claim has the same
`justified | contested | defeated | gap` status.

## The blocker (verified 2026-07-30)

`CheckedProgram` (`lean/Lara/Compile.lean:471`) identifies a node by the
`SupportTerm` value in `args`, and `DecidableEq SupportTerm`
(`lean/Lara/Support.lean:214-218`) **includes the opaque certificate payload**
(`Assurance.cert β h κ`, `κ : CertRef { payload : SExpr }`,
`lean/Lara/Certificate.lean:52`). So `P_β.args` and `P_γ.args` are distinct
values and no payload-varying node bijection is statable. AF nodes are already
positional (`toAF.args := List.range P.args.length`, `Compile.lean:597`), which
makes the bijection *positional identity* once erasure is length/position
preserving.

## Design decision — relation, not a new wire constructor

Do **not** add an `Assurance.certified` constructor: `Assurance` is on the wire
(`Presentation.lean` codec, byte-exact with Haskell), and a new constructor
would perturb the differential anchor for a proof-only device — forbidden by the
"keep the compiler core symbolic / byte-exact codec" discipline.

Instead introduce erasure as a **structural relation** plus a total
normalization function that never crosses the wire boundary:

- `AssurEraseEq : Assurance → Assurance → Prop` — both `.cert _ _ _`, or equal
  otherwise (`.none=.none`, `.trusted=.trusted`). Decidable.
- `EraseEq : SupportTerm → SupportTerm → Prop` — structural congruence: equal
  `LeafId`; on `.inst` equal `RuleId`, equal `Subst`, `List.Forall2 EraseEq` on
  premises `ws`, positionwise `QuestionId`-eq + `EraseEq` on the discharge map
  `D`, equal hole set `H`, and `AssurEraseEq` on the assurance. This is exactly
  "preserving argument names, rule instances, conclusions, obligations, and
  positions; replacing accepted certificate annotations by `certified`."
- `eraseCert : SupportTerm → SupportTerm` — total, collapses `.cert _ _ _` to a
  fixed canonical `.cert β₀ h₀ κ₀` marker; recurses through `ws`/`D`. Bridge
  lemma `eraseCert s = eraseCert t ↔ EraseEq s t` gives the "erased skeleton"
  reading and idempotence `eraseCert (eraseCert s) = eraseCert s`.

**Stable argument id** = the positional index into `args`. It is well-defined as
the node identity because `EraseEq`/`eraseCert` are order- and length-preserving,
so the induced node bijection is the identity on `Nat` — no relabelling needed.
Document this as the argument-id model; it is the honest content of the
"stable-argument-id compile boundary" the ledger asks for.

## Proof plan (maps to the 5 doc-proof steps)

New file `lean/Lara/Erase.lean` (keep `Compile.lean` under the file-size norm),
imported by `Compile`/`Driver` consumers.

1. **Definitions + equivalence** — `AssurEraseEq`, `EraseEq`, `eraseCert`;
   `EraseEq` refl/symm/trans; `Decidable (EraseEq a b)`; the `eraseCert ↔ EraseEq`
   bridge and idempotence.
2. **Conclusion/obligation invariance (doc step 1–2).** `EraseEq w w' →
   HasSupport … w C O → HasSupport … w' C' O' → C = C' ∧ O = O'`. The cert
   payload is read only through the `CertOk` seam (`AssuranceOk.cert`,
   `Support.lean:533`); conclusions/obligations are functions of `rn/θ/ws`.
   Leverage `hasSupport_unique` (`Support.lean:665`).
3. **Structural checking transport (doc step 1).** Both `P_β`, `P_γ` are given
   `CheckedProgram`s, so completeness is a field — no re-derivation. The
   acceptance hypothesis is `∀ instances, CertOk_β … ↔ CertOk_γ …` on
   corresponding erased terms; used only to line up the `.cert` cases, which
   `EraseEq` already merges.
4. **Edge congruence (doc steps 2–3).** `Contains`, `subterm`/`Pos`,
   `AttackOcc`, `Covered` (`Compile.lean:69,435`) respect `EraseEq` (they never
   inspect `Assurance`). Conclude `Edge`-congruence, then the positional
   `edgeB P_β i j = edgeB P_γ i j` for all in-range `i, j` (equal length from
   `Forall2 EraseEq`). Reuse `edgeB_faithful` (`Compile.lean:649`).
5. **AF equality + grounded congruence (doc step 4).** Congruence lemma:
   two AFs with equal `args` and `attack` agreeing on `args × args` have equal
   `grounded`, hence equal `labelC` (`Grounded.lean:141,404`). Instantiate with
   the two `toAF`s to get pointwise-equal labels. (May need a restricted-domain
   congruence for `grounded`/`iter` since `attack` is a total `Nat→Nat→Bool`.)
6. **Status equality (doc step 5).** `statusC` (`Grounded.lean:516`) is a
   function of `support` index set + `labelC`. Erase-corresponding claims have
   identical positional `support`/`holes`, so statuses are equal. Final theorem
   `backend_replacement`.

## Deliverables / verification

- `lean/Lara/Erase.lean` — definitions + all lemmas + `backend_replacement`,
  `sorry`-free, axioms within `{propext, Classical.choice, Quot.sound}`.
- `AxCheck.lean` — add `#print axioms` for every new public theorem.
- `lean && lake build` green; `lake env lean AxCheck.lean` shows only the trio.
- `scripts/differential.sh` unchanged pass count (no wire/codec touch → anchor
  untouched; this is a Lean-only result, confirm no regression).
- Ledger updates: `ara/evidence/status/mechanization_status.md` result 9 →
  mechanized; `lean/README.md` result-9 row; a `docs/` note if the argument-id
  model warrants recording.

## Risks

- Restricted-domain `grounded` congruence (step 5) is the least-canned lemma —
  `iter`/`step`/`defendedB` fold over `F.args`, so equality on `args × args`
  should suffice, but the induction on the fuel bound may need care.
- `EraseEq` well-founded recursion over nested `List SupportTerm` mirrors the
  existing hand-rolled `SupportTerm.decEq` pattern (`Support.lean:219`); reuse
  that shape to keep the termination proof cheap.
- No Haskell change is required (proof-only). If a reviewer wants Haskell
  conformance evidence, an `eraseCert`/`EraseEq` port is a P3 follow-up, not
  part of soundness.
