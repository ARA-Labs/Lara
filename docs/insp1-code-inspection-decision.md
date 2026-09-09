# `insp@1` — the static code-inspection backend

_Status: settled for language v0.1. Recorded 2026-09-07 (issue #260). This record fixes what an
accepted `insp@1` step certifies, the encoding it certifies it over, and where the conflicts its
family admits are allowed to live. It closes the §5.2 portfolio item that PR #256 marked
designed-but-unshipped; the seam contract itself is unchanged and stays in
`strict-backend-decision.md`._

## 1. Decision

The v0.1 optional adapter portfolio ships a third checker beside `ra@1` and `ord@1`:

```text
insp@1  —  Lara.Strict.Insp  /  lean/Lara/Insp.lean
```

It certifies **structural facts about referenced source**, as a closed four-predicate family over
**declared exhaustive inventories**:

| goal | inventories cited | what it says |
| --- | --- | --- |
| `code_absent(Src, Feat)` | 1 | `Feat` occurs nowhere in `Src` |
| `code_present(Src, Feat)` | 1 | `Feat` occurs in `Src` |
| `code_unique(Src, Feat)` | 1 | `Src`'s inspection found something, and everything it found is `Feat` |
| `code_planned_not_shipped(Plan, Src, Feat)` | 2 | `Feat` is in `Plan`'s inspection and absent from `Src`'s |

The last member is the corpus's own scheme name. M0's C13/C14 study counted `code_inspection`
(merging `plan_vs_shipped_diff`) as 3 of 60 sampled claims — small, but real, and the only measured
strict shape the portfolio had left unshipped.

Certificates:

```text
cert ::= (inspect (prem N))                 -- the one-inventory members
       | (inspectdiff (prem N) (prem M))    -- the plan-vs-shipped diff
```

There is no witness value. The relation is read off the goal predicate, as in `ord@1`; what the
certificate fixes beyond the slots is the **arity** of the step, which is why the two family shapes
get two wire keywords and two flat `SlotSchema`s. An `(inspect …)` payload under a
`code_planned_not_shipped` goal is a rejection, not a re-interpretation.

## 2. What is being certified: the closed-world step

This is the question the whole design turns on, because "static code inspection" sounds like a
*measurement*, and a measurement is not a strict step.

A negative existential over code — *"the shipped module has no repair call site anywhere"* — is not
an observation. It is an **inference from an exhaustive enumeration**: given that the inspection
covered the whole unit and enumerated everything it found, absence follows deductively. That
inference is what `insp@1` replays, and it is the only thing it replays.

The enumeration arrives as an ordinary premise:

```text
inv(Src, finding(f1, finding(f2, no_findings)))
```

read as *"an exhaustive inspection of `Src` found exactly `f1` and `f2`."* The empty inventory
`inv(Src, no_findings)` — inspected, found nothing — is the pure negative-existential case;
`Lara.Insp.relHolds_absent_of_nil` is that one-line theorem, and
`fixtures/corpus/insp-empty-inventory-accept.sexp` is its standing wire anchor.

### 2.1 Why the enumeration is a cons spine and not a variadic node

`Σ` fixes each constructor's arity (spec §2), so `inv(U, f1, …, fn)` is not declarable at all: a
unit's signature would have to name one `inv` per length, and the R2 sort checker could not check
it. The convention is therefore three fixed-arity reserved symbols — `inv`/2, `finding`/2,
`no_findings`/0 — and the enumeration is an ordinary source-level list. This is the same
one-table discipline the wire keywords follow: the concrete spellings live in `Lara.Strict.Insp`'s
`Con` table (Lean: `Lara.Insp.Con`) and nowhere else.

### 2.2 The exactly-one-inventory rule

A consulted premise must contain **exactly one** `inv(…)` node anywhere in its argument terms.
This is `Lara.Strict.Cell.premiseCell`'s "exactly one numeric literal" discipline, for the same
reason: a premise carrying two inventories does not say which one the certificate meant, and
guessing is how a checker becomes unsound quietly. The scan does not stop at the first match, so a
nested `inv` inside a finding is a second node and rejects too.

### 2.3 What it does *not* certify — the factivity firewall, at its sharpest

An accepted certificate does **not** assert that any inventory is faithful to the bytes: that the
inspection really covered the whole module, or that it read the version of the source the claim is
about. Byte-level evidence admission is not part of v0.1 (spec §4.3), so an inventory is an
*evidence declared* leaf like any measurement and stays defeasible — attackable, quarantinable,
admission-governed.

The corpus makes this concrete rather than hypothetical.
`corpus-units/rebench-rust_codecontests/C09` is exactly a `plan_vs_shipped_diff` where the coverage
half is met and the version half is not: `notes.md`, the sole documentary basis for the "planned"
half, ships nowhere in the artifact tree. Its honest verdict is a `gap`, and no certificate changes
that. The worked example `examples/S9` supplies the version attestation C09 could not, so the same
shape reaches `justified` — the two read together are the demonstration that the certificate settles
the inference and not the evidence.

What the adapter *does* remove from the trusted base is narrower and real: the step from an
enumeration to a structural conclusion no longer rests on a trusted policy rule.

## 3. Premise-only slots

`insp@1` rejects any certificate slot `>= nPrem`, the seam-wide rule `ra@1` and `ord@1` already
follow. Here the guard protects the **closed-world premise itself**. On the raw `.sexp` door the
backend theory table is built from the unit's own wire `theories` section and replay preflight never
validates its content, so without the guard an artifact could supply a theory entry asserting *"I
inspected everything and found nothing"* and certify against it — with no leaf, no provenance, no
admission check, and nothing for an attack to land on.

`fixtures/corpus/insp-premise-only-{accept,reject}.sexp` isolate it: both units declare the same
one-entry theory carrying an inventory that would have satisfied the goal, and differ only in
whether the certificate cites the premise or the theory entry.

The Lean side reaches the same acceptance set from the other direction, exactly as the two
arithmetic backends do: `Lara.Driver.buildRegistry` resolves any *known* `insp@1` digest to `[]`, so
`Γ = Δ ++ [] = Δ` and "names a premise" coincides with "is in range of `Γ`". An unknown digest still
fails to resolve, which is a rejection.

## 4. Contraries: where this family differs from `ord@1`

`num_lt`/`num_le` head **no** declared contrary pair, and that is a theorem: comparison goals are
decided against a *shared* ground truth — the numerals in the goal itself — so a sound backend can
never accept two conflicting members (`Lara.Ord.ordModels_excl_of_lt`).

Inspection goals are not like that. They are decided against a **declared** inventory, and two units
may declare different inventories for the same source. `code_absent(S, F)` and `code_present(S, F)`
are therefore genuinely co-acceptable. Both halves are mechanized:

- `Lara.Insp.inspModels_excl_of_same_entry` — two arguments reading the *same* inspection leaf
  cannot both be backed for opposite polarities;
- `Lara.Insp.inspModels_absent_present_sat` — two arguments reading *different* leaves can.

`InspSpec.prop_inspContraryCoAcceptable` is the executable mirror of the second.

This has a direct consequence for policy authors, and it is a Path B consequence, not an `insp@1`
one. Spec §8.1 forbids a strict-reachable conclusion pattern from overlapping either side of a
`contrary` declaration (R12). So a policy may **not** both make `code_absent`/`code_present` strict
conclusions and declare them contrary — that is an R12 rejection at compile time. The conflict
therefore belongs on the **defeasible bridge's** conclusions, one layer up, which is exactly the
layering `examples/S9/insp-v1.policy.lara` uses and the same shape `ord@1`'s S2 uses for a different
reason. Under that restriction every conflict is rebuttable at a defeasible step, which is what
Path B buys.

## 5. Considered and rejected

**One premise per finding plus a separate exhaustiveness premise.** A negative existential would
cite the exhaustiveness premise together with *all* occurrence premises, so the certificate's slot
count would vary with the size of the enumeration. That is not a flat `SlotSchema`, so the
symbolic-slot elaboration pass (`Lara.Elaborate.CertSlots`) could not lower `(prem name)`
references for it, and the wire grammar would stop being a fixed-arity keyword application. The
enumeration belongs in one premise because it is one observation.

**Certifying over source bytes directly.** This is what an author actually wants, and it is
precisely `lara-evidence@0.1` — byte-level evidence admission, gated under issue #78 and explicitly
out of v0.1 (spec §4.3). Building it into a strict backend would have moved a defeasible
measurement into the TCB by the back door. The split taken here is the honest one: the backend owns
the inference, the leaf layer owns the observation, and when byte-level admission ships it
strengthens the leaf without touching this adapter.

**A `code_diff` spelling for the diff member.** Rejected for `code_planned_not_shipped` on the §4.5
naming taste already settled for the scheme vocabulary: the target reader is a Python-literate
domain researcher reading the formalization of their own artifact, so long-and-obvious wins over
short-and-precise-to-insiders.

**Making `code_present` a separate backend, or dropping it.** It carries no closed-world content on
its own — it is plain membership. It stays because it is the positive half that makes the contrary
question above statable and testable, and because the diff member decomposes into it
(`Lara.Insp.inspModels_diff_halves`).

## 6. Evidence

- **Soundness** (spec §9 result 10): `lean/Lara/Insp.lean` — `enc_iff` via `equiv_iff_nf_eq`,
  `inspReplay_iff`, `inspSound`, and the obligation-4 laws `inspUses_covers` / `inspUses_valid` /
  `inspUses_account`, plus the domain theory (`relHolds_absent_of_nil`,
  `relHolds_present_of_unique`, `relHolds_polarity_excl`, `relHolds_unique_absent_excl`,
  `inspModels_diff_halves`, `inspModels_one_witness`, and the two contrary-pair theorems). Every
  one is pinned in `lean/AxCheck.lean`; the audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- **Conformance** (not soundness): `test/InspSpec.hs`, 23 property groups.
- **Golden**: four hand-authored wire anchors under `fixtures/corpus/insp-*.sexp`, plus the worked
  example `examples/S9`. All five are byte-compared across both drivers by
  `scripts/differential.sh`.
- **Mutation**: issue #266's v6 refresh adds S9 and S2 (`ord@1`) together:
  27 verified mutants each, growing the seeded suite 541 → 595 and the measured
  input set 601 → 655. All previous mutant bytes are unchanged. S9's
  `cert-payload-tamper` replaces an `inspect` payload with `mut_corrupt` (R13);
  `cert-theory-swap` changes an `inspectdiff` theory digest (R7 allowlist rejection,
  before backend replay). This covers decoder and allowlist rejection, not every
  semantic recheck branch. `MutationSpec.prop_backendCertificateCoverage` pins
  both backends' measured certificate cases. The clean measurement snapshot,
  class deltas, hashes, and v6 publication procedure are recorded in
  `m5-freeze-checklist.md`. The original S9-only trial in #260 was reverted to
  avoid an unbudgeted freeze cycle; this combined refresh resolves that deferral.

## 7. What this does not settle

Whether an inventory is a good formalization of an inspection is an audit question, not a proof
question — decision doc §7 item 4 exactly. A theorem shows the executable adapter implements
`inspModels`; it cannot show that `inspModels` faithfully represents what a reader means by "the
module has no repair path". That gap closes with evidence admission and human audit, not with a
stronger backend.
