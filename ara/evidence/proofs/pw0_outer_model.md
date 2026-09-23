# PW0 — the possible-world outer-model gate

## Result

An outer *comparison* layer over unchanged
local Lara judgments, mechanized in five modules that only import: no existing
checking, compilation, grounded-labelling, or status definition was modified.

The frame is factored as structure plus valuation. `Lara.PW.Frame` carries
contexts, bridges with source and target, per-context worlds and queries, a
candidate relation `R`, an applicability judgment `accept`, and a bridge-global
partial claim translation. The valuation is a *parameter of satisfaction*
rather than a frame field, which is the design's `M[V := …]` instantiation
stated once instead of duplicating the model. Accepted edges are
`A_b = R_b ∩ accept_b`, fixed per bridge and independent of the formula being
evaluated — the condition that makes the logic normal.

## The theorem set

| Result | Declaration |
|---|---|
| T0 conservativity, both sides | `PW.Instance.t0_cmp`, `t0_src` (both `Iff.rfl`) |
| T1 world-local preservation | `PW.Instance.srcStatus_iff_cmpStatus` |
| T2 typed normality | `PW.sat_K`, `sat_nec`, `sat_dia_iff_not_box_neg`, `sat_box_top`, `sat_box_conj` |
| T2 negative controls (all five stronger frame axioms refuted) | `Examples.PW.sat_T_fails`, `sat_D_fails`, `sat_B_fails`, `sat_5_fails`, `sat_4_fails` |
| T3 uniform-language reduction | `PW.sat_lift` |
| T4 coherence | `PW.sat_congr`, `PW.Instance.sat_src_iff_cmp` |
| T5 tagged comparison | `PW.compare_*`, `mem_compare_profile_iff`, `incomparable_ne_comparable` |
| T5 adequacy | `PW.mem_compare_iff_sat_dia`, `not_sat_dia_of_incomparable`, `Examples.PW.presentsT7`, `presentsOverlapRejected`, `overlap_rejected_no_dia` |
| T7 non-preservation | `Examples.PW.t7_witness`, `t7_support_transported` |

## What makes T1 load-bearing rather than definitional

The two world-local observations are defined independently. `srcStatus` is the
relational, oracle-free `Compile.SrcStatus`, read off `SrcIn`/`SrcOut` with no
compiled framework, no grounded labelling, and no enumeration. `cmpStatus` is
the executable `Grounded.statusC` over `Compile.checkedAF`. Neither is defined
through the other; their agreement is `Compile.srcStatus_iff_checked` — the
existing source-to-compilation preservation chain — instantiated at the world.

T4 is then `sat_congr` at T1 and is honestly an *integration* theorem: a
structural induction whose content is that satisfaction is extensional in the
atomic valuation. The substantive result underneath it is T1.

The asymmetry is visible in the valuation-coherence discharges.
`cmpVal_functional` is `h₁ ▸ h₂` against a total function; `srcVal_functional`
must route through T1 twice, because `SrcStatus` is a relation and nothing in
its type says a query has at most one status.

## T7 — the boundary this record exists to fix

One context whose defeat table declares `q` contrary to `p`; two accepted
worlds. The source admits only the `p` argument and justifies `p`. The target
admits the same `p` argument plus one unattacked `q` attacker carrying the
typed undermine edge the contrary pair forces, and defeats `p`.

```
t7_src_justified : cmpStatus wT7src pA = Status.justified
t7_tgt_defeated  : cmpStatus wT7tgt pA = Status.defeated
```

The support really is transported, not merely present by coincidence — the
supports are the same nonempty index set, and the shared index resolves
through both retained node caches (the structure support indices actually
index) to the same term:

```
t7_support_transported :
    (claimAt wT7src pA).support = [0]
      ∧ (claimAt wT7tgt pA).support = [0]
      ∧ acceptedT7src.nodes[0]?.map (·.term) = some (SupportTerm.leaf l1)
      ∧ acceptedT7tgt.nodes[0]?.map (·.term) = some (SupportTerm.leaf l1)
```

So status preservation needs strictly more than support transport. This fixes
the boundary between T6 (exact checked-support transport) and T8
(conditional status preservation).

The witness exists at all only because the missing-conflict search is
directional: `firstMissingConflict?` (`lean/Lara/Check/Program.lean:279`) tests
`contraryMatchB canon dp source.conclusion target.conclusion` in one direction,
so the contrary pair demands `q → p` and no converse edge. A symmetric
requirement would leave `p` *contested* rather than defeated and the separation
would vanish.

## Gate 3 — incomparability cannot collapse into a local status

Enforced three ways rather than by convention. *Structurally*: `CrossResult`
keeps reasons and profiles in different constructors and
`IncomparabilityReason` contains no `Status`, so no coercion exists to build.
*Behaviorally*: each reason is pinned to exactly its defining condition.
*Semantically*: `not_sat_dia_of_incomparable` shows that with the translation
defined, an incomparable result means the model has no accepted witness at all
— a condition no local status could report — and `overlap_rejected_no_dia`
discharges it at a concrete `Presents`-verified bridge
(`presentsOverlapRejected`), so the semantic arm has a worked instance.

`overlap_local_gap` pins the other half: the local layer *does* answer `gap`
for the source-only claim `s`, and that is the answer the outer layer declines
to transmit, because here `gap` means "outside this field's vocabulary" rather
than "considered and unsupported".

## Adequacy — the executable layer is an implementation, not a lookalike

`crossCompare` takes its candidate list, acceptance test, and status function as
explicit inputs; nothing in its type says the list enumerates `R_b(w, ·)`.
`Presents` states that obligation and `mem_compare_iff_sat_dia` proves the
interface computes the model's `⟨b⟩`. `presentsT7` discharges it at a real Lara
bridge and `t7_dia_via_adequacy` re-derives the witness through `crossCompare`, so
the adequacy theorem has an instance rather than only a statement.

## Verification (2026-09-02, second review round)

```
$ cd lean && lake build
Build completed successfully (127 jobs).                        EXIT: 0

$ cd lean && (set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
Axiom audit passed.                                             EXIT: 0
```

1619 audited declarations across the library, of which 54 are PW0 — every
theorem the five modules declare. The count is load-bearing and is stated here
deliberately: the audit gate was hardened in the same session (trace N274)
after it was found capable of reporting "passed" over a *silently reduced*
set, so a declaration total is quoted alongside the verdict rather than the
verdict alone. No `sorryAx`, no `ofReduceBool`, nothing
outside `propext` / `Classical.choice` / `Quot.sound`. `sat_T_fails`,
`sat_D_fails`, `sat_B_fails`, `sat_5_fails` and four of the T2 laws depend on
no axioms at all; `sat_4_fails` needs only `propext`.

`git diff main --stat` is pure insertion (2699 lines, no deletions); the only
Lean files touched outside the five new modules are `Lara.lean` and
`AxCheck.lean`. That is gate 1's evidence.

## Known limitations of the frozen contract

1. `accept` is an arbitrary `Prop` with no posited connection to any checker,
   certificate, or soundness condition — the name promises more than the model
   supplies. Discharging it is T6.
2. `gap` conflates *out of vocabulary*, *ill-sorted*, *not posed*, and *posed
   but unsupported*, because queries are all of `Atom`. Only the bridge-domain
   case is separated, reported as `translationUndefined`.
3. `Context` fixes the checking environment, not a scientific state: two worlds
   of one context may differ in program, evidence, and attacks. Intended — it
   is what makes `⟨b⟩` non-trivial within a context — but "world of this
   context" must not be read as "this artifact".

Full record: `docs/theory-pw0-outer-model.md`.
