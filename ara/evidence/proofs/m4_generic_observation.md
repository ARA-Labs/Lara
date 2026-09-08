# M4 — contextual observation at an arbitrary ExtensionSemantics (#216)

Branch `theory/m4-generic-ctxequiv`, PR
[#271](https://github.com/ARA-Labs/lara/pull/271). Landing commits 3bc0e65,
40202bc, 02a64fd, 4dc223e, 2f1d28d, 225cac8.

Decision record: `docs/theory-m4-generic-observation.md`.

## What landed

Three new Lean modules, purely additive:

| Module | Public theorems | Contents |
|---|---|---|
| `lean/Lara/Invariants/Observation.lean` | 3 | `observeSem` and its grounded / `gap` regressions |
| `lean/Lara/Context/Observation.lean` | 15 | `Outcome α`, `obsGen`, `obsGen_congr`, `obsSem`, `CtxEquivSem`, the four congruences |
| `lean/Lara/Examples/ContextSemantics.lean` | 19 | the separation and agreement fixtures |

Modified: `lean/Lara.lean` (three imports + M4 index entry), `lean/AxCheck.lean`
(pin block). No existing declaration changed. `git diff main --stat` shows no
modification to `lean/Lara/Semantics.lean`, `lean/Lara/Grounded.lean`,
`lean/Lara/Invariants.lean`, `lean/Lara/Observation.lean`,
`lean/Lara/Context/Fragment.lean`, or `lean/Lara/Context/Equivalence.lean`.

## Gate transcript

Run from `/home/yfhe/ara/lara/.claude/worktrees/expressive-brewing-dahl`,
`PATH="$HOME/.elan/bin:$PATH"`, at commit 225cac8.

```
$ cd lean && lake build
Build completed successfully (154 jobs).

$ python3 scripts/check-axcheck-coverage.py lean/AxCheck.lean \
    lean/Lara/Invariants/Observation.lean lean/Lara/Context/Observation.lean \
    lean/Lara/Examples/ContextSemantics.lean
AxCheck coverage passed (37 declarations).
coverage-exit=0

$ cd lean && set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh
Axiom audit passed.
axioms-exit=0
```

Baseline before the branch: `Build completed successfully (151 jobs).`
(151 → 152 after `Invariants/Observation`, → 153 after `Context/Observation`,
→ 154 after `Examples/ContextSemantics`.)

Build-closure check (the #259 failure mode, checked by hand until that issue
lands) — all three modules produce oleans under `lean/.lake/build/lib/lean/`:

```
lean/.lake/build/lib/lean/Lara/Invariants/Observation.olean
lean/.lake/build/lib/lean/Lara/Context/Observation.olean
lean/.lake/build/lib/lean/Lara/Examples/ContextSemantics.olean
```

Forbidden-axiom scan over the full audit output: `grep -cE "sorryAx|ofReduceBool"`
returned **0**. Every one of the 37 new rows is inside
`{propext, Classical.choice, Quot.sound}`, e.g.

```
'Lara.Context.obsGen_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Context.ctxEquivSem_grounded_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Context.backend_replacement_congruence_sem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Context.liftObservation_inj' depends on axioms: [propext]
'Lara.Examples.ContextSemantics.cycle_link_ok' depends on axioms: [propext]
'Lara.Invariants.observeSem_grounded' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## The congruence, and what it does not assume

```lean
theorem obsGen_congr {α : Type} (g : Invariants.StructuredAF → Atom → α)
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F) (hfix : FixesContext f C) :
    obsGen g reg₁ C F = obsGen g reg₂ C (mapAssurFrag f F)
```

Hypotheses are **exactly** `backend_replacement_congruence`'s
(`lean/Lara/Context/Equivalence.lean:629`). No `AttackExtensional sem.spec`, and
no hypothesis on `sem` or on `g` of any kind. The proof is that proof with
`Invariants.status canon` replaced by `g`, funnelling through
`compileUnit_link_relabel` (`lean/Lara/Context/Equivalence.lean:586`), whose
conclusion is `Invariants.compileUnit acc₂ = Invariants.compileUnit acc₁` — an
equation between carriers.

Contrast: `Lara.Observation.observe_congr` (`lean/Lara/Observation.lean:406`)
does take `(hext : AttackExtensional sem.spec)`, because it moves an observation
between two *distinct* frameworks agreeing pointwise on the carrier.

`backend_replacement_congruence_sem`, `registry_swap_congruence_sem` and
`backend_replacement_congruence_composed_sem` are one-line instantiations of
`obsGen_congr`.

## The separations

Both are `decide`-closed and each carries a disequality conjunct, so a collapse
is a build failure rather than a silent regression.

```lean
theorem obsSem_cycle_stable_ne_grounded :
    obsSem groundedSem registryEx cycleCtx cycleFrag
        = .observed [ClaimObservation.observed Grounded.Status.contested] ∧
      obsSem stableSem registryEx cycleCtx cycleFrag
        = .observed [ClaimObservation.noExtension] ∧
      obsSem groundedSem registryEx cycleCtx cycleFrag
        ≠ obsSem stableSem registryEx cycleCtx cycleFrag

theorem obsSem_sink_preferred_ne_grounded :
    obsSem groundedSem registryEx sinkCtx sinkFrag
        = .observed [ClaimObservation.observed Grounded.Status.contested] ∧
      obsSem preferredSem registryEx sinkCtx sinkFrag
        = .observed [ClaimObservation.observed Grounded.Status.defeated] ∧
      obsSem groundedSem registryEx sinkCtx sinkFrag
        ≠ obsSem preferredSem registryEx sinkCtx sinkFrag
```

The linked three-cycle's carrier is pinned rather than assumed:

```lean
theorem cycle_linked_shape :
    (linkedUnit registryEx cycleCtx cycleFrag).args = [.leaf l2, .leaf l1, .leaf l3] ∧
      (linkedUnit registryEx cycleCtx cycleFrag).atts
        = [ .undermine (.leaf l3) (.leaf l1) []
          , .undermine (.leaf l2) (.leaf l3) []
          , .undermine (.leaf l1) (.leaf l2) [] ]
```

Node order is context arguments first, then fragment arguments; the fragment
declared one of the three attacks (`s ⊣ p`, both endpoints its own, forced by
`SideOk.attack_complete`) and linking's saturation supplied the other two.

Agreement is proved, not assumed: `obsSem_linking_agrees` and
`obsSem_sym_agrees` each pin **all five** mechanized semantics reporting the
same status on the two pre-existing M4 carriers (`ctxEx`/`fragEx` → `defeated`,
`symCtx`/`symFrag` → `contested`). That is what establishes the new fixtures were
necessary rather than convenient.

## Quantified where the ancestor is quantified

`obsSem_gap_uniform`, `obsSem_incompatible_id_clash` and
`obsSem_rejected_signature` are stated over an arbitrary
`sem : ExtensionSemantics` rather than checked at five instances, because
`Semantics.observe_gap` is likewise unquantified in `sem` and because the link
guard and whole-unit checker run before any projection is consulted. `decide`
cannot close a goal with a free `sem`; these go through
`Invariants.observeSem_of_status_gap`, `obsGen_incompatible` and
`obsGen_rejected`.

Scope note, so the quantifier is not over-read: each of the three is quantified
over `sem` but fixed at **one carrier**. `obsSem_gap_uniform` says every
semantics reports `gap` on `Linking.gapFrag` in `Linking.silentSCtx`; it does
not say gap-uniformity holds at an arbitrary link. The carrier-independent
statement is `Invariants.observeSem_of_status_gap`, which these instantiate.

## How the five semantics actually split at the two carriers

Measured after the fact by a scratch probe outside the repository (`lake env
lean` against the built oleans, `by decide`, discarded afterwards). Not shipped
as theorems — the public surface is the one the plan specified — but recorded
here because it says how wide the separations are rather than merely that they
exist.

| Carrier | grounded | complete | preferred | stable | semi-stable |
|---|---|---|---|---|---|
| three-cycle, export `p` | contested | contested | contested | **noExtension** | contested |
| sink, export `s` | contested | contested | **defeated** | **defeated** | **defeated** |

So the cycle isolates `stable` alone, 4-against-1, which is what makes it the
sharp form — the odd one out reaches an arm the other four cannot. The sink
splits the five 2-against-3, so the disagreement it exhibits is not a
single-instance oddity of `preferred`: three of the five mechanized semantics
report `defeated` where the other two report `contested`.

A note on how this was measured, because the first attempt was wrong in an
instructive way. The probe initially opened `Lara.Examples.Linking` but not
`Lara.Examples`, so `registryEx` was unresolved — and with `autoImplicit` on it
was silently auto-bound as an implicit variable rather than reported. Lean
happened to reject that particular file for an unrelated reason
("expected type must not contain free variables"), but a goal that had closed
under such a binding would have been a vacuously general theorem that built and
passed the axiom gate. That is exactly the failure mode
`set_option autoImplicit false` guards against, and it is why all three shipped
modules carry it.

## Machine checks standing in for human eyeballs

- Separations: the disequality conjuncts above.
- `ctxEquivSem_grounded_iff` must stay an `iff` —
  `ctxEquivSem_grounded_negative` consumes `.mp`,
  `ctxEquivSem_grounded_of_ctxEquiv` consumes `.mpr`.
- `obsSem_grounded` must be exercised — `obsSem_linking_grounded` derives the
  grounded reading of the M4 fixture through it and `Linking.obs_defeated`
  rather than re-pinning the value by an independent `rfl`.

## Mutation evidence: the machine checks actually bite

The claims above about eyeball-replacing checks were verified by mutation, not
asserted. Both mutants were applied at commit 3545b98, built, and reverted; the
working tree was confirmed clean afterwards and `lake build` back to 154 jobs.

**Mutant A — collapse a separation.** Rewrote the second conjunct of
`obsSem_cycle_stable_ne_grounded` to read `groundedSem` on both sides, so the
two pinned values agree and the disequality conjunct becomes `x ≠ x`. Build
failed:

```
error: Lara/Examples/ContextSemantics.lean:225:2: Tactic `decide` proved that the proposition
  obsSem groundedSem registryEx cycleCtx cycleFrag =
      Outcome.observed [ClaimObservation.observed Grounded.Status.contested] ∧
    obsSem groundedSem registryEx cycleCtx cycleFrag =
        Outcome.observed [ClaimObservation.observed Grounded.Status.contested] ∧
      obsSem groundedSem registryEx cycleCtx cycleFrag ≠ obsSem groundedSem registryEx cycleCtx cycleFrag
is false
```

Note what this shows: without the third conjunct the mutated statement is two
true equalities and would have *passed*. The disequality is what fails it.

**Mutant B — weaken the `iff`.** Rewrote `ctxEquivSem_grounded_iff`'s conclusion
from `↔` to `→` and dropped the backward branch of its proof. The module itself
still compiled; the fixtures did not, and they failed at **both** consumers:

```
error: Lara/Examples/ContextSemantics.lean:427:94: Invalid field `mp`: ...
error: Lara/Examples/ContextSemantics.lean:440:46: Invalid field `mpr`: ...
```

Line 427 is `ctxEquivSem_grounded_negative` and line 440 is
`ctxEquivSem_grounded_of_ctxEquiv`. Both directions are therefore load-bearing:
the theorem cannot be weakened in either direction without a build failure, and
neither consumer is redundant.

## Open, filed

- [#268](https://github.com/ARA-Labs/lara/issues/268) — the equivalence
  *relations* are not separated; `CtxEquiv → CtxEquivSem sem` is neither proved
  nor refuted.
- [#269](https://github.com/ARA-Labs/lara/issues/269) — instantiate the generic
  congruence on the certificate-bearing `certCtx`/`certFrag` pair.
- [#270](https://github.com/ARA-Labs/lara/issues/270) — prove `Admissible` for a
  disagreeing carrier, so a congruence witness sits where the `sem` quantifier is
  not inert.

---

## Follow-up: the unified type (commit eb6e955)

Everything above records PR #271 as it merged, and is left as it stands. A later
commit on the same branch, `eb6e955`, replaced the two-type design that section
describes. What follows is the delta; where the two disagree, this section is the
landed state.

### What changed

| Before (#271) | After (eb6e955) |
|---|---|
| `Observation` (frozen inductive) **and** `Outcome α` beside it | one `ObservationOf α`; `abbrev Observation := ObservationOf Grounded.Status`; `Outcome` deleted |
| `obsGen`, `obsGen_*`, `obsGen_congr` in `Context/Observation.lean` | in `Context/Equivalence.lean`, beside the theorems they generalize |
| `obs_eq_of_ok`, `backend_replacement_congruence` carry proof bodies; `obsGen_congr` is a second copy of the same script | both are one-line corollaries: `obsGen_eq_of_ok _ hlink h`, `obsGen_congr _ hf hpres hadm hfix` |
| "`obs` is `obsGen` at `g := Invariants.status canon`" asserted in prose | `Lara.Context.obs_eq_obsGen`, closing by `rfl`, pinned in `AxCheck.lean` |
| `Context/Fragment.lean`, `Context/Equivalence.lean` unmodified | both modified; **no statement changed** |

### The premise that became a theorem

```lean
theorem obs_eq_obsGen {canon : String → String} (reg : BackendRegistry canon)
    (C : Context) (F : Fragment) :
    obs reg C F = obsGen (Invariants.status canon) reg C F := rfl
```

This does not typecheck under the two-type design: `obs : Observation` and
`obsGen g : Outcome α` are different types, so no equation between them is
well-formed. The sentence it now proves is the milestone's design premise, and
`docs/theory-m4-generic-observation.md:81` asserted it in prose.

### What it cost the fixtures — nothing

`abbrev` is definitionally transparent, so `decide` reduces through it.
`lean/Lara/Examples/Linking.lean` was **not edited** and its `decide`-closed
`congruence_witness` (`:676`) and `registry_swap_witness` (`:670`) compile
unchanged. The signature-level diff of `Context/Equivalence.lean` is purely
additive — every existing theorem keeps its name, type and implicit-argument
order:

```
$ git diff d250d52 -- lean/Lara/Context/Equivalence.lean | grep -E "^[-+]theorem|^[-+]def "
+def obsGen {α : Type} (g : Invariants.StructuredAF → Atom → α)
+theorem obsGen_incompatible {α : Type} (g : Invariants.StructuredAF → Atom → α)
+theorem obsGen_rejected {α : Type} (g : Invariants.StructuredAF → Atom → α)
+theorem obsGen_eq_of_ok {α : Type} (g : Invariants.StructuredAF → Atom → α)
+theorem obsGen_ext {α : Type} {g₁ g₂ : Invariants.StructuredAF → Atom → α}
+theorem obs_eq_obsGen {canon : String → String} (reg : BackendRegistry canon)
+theorem obsGen_congr {α : Type} (g : Invariants.StructuredAF → Atom → α)
```

### Correction to the sizing above

The duplication removed was **two** proof bodies, not three. `registry_swap_congruence`
was already derived from `backend_replacement_congruence` at `d250d52`
(`git show d250d52:lean/Lara/Context/Equivalence.lean`, `:686`), so the plan's T1
finding ("three proof bodies duplicated across two modules") overcounted by one.

### Gate transcript

Run from `/home/yfhe/ara/lara`, `PATH="$HOME/.elan/bin:$PATH"`, at commit `eb6e955`.

```
$ cd lean && lake build Lara
Build completed successfully (100 jobs).

$ (set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
Axiom audit passed.

$ scripts/check-axcheck-coverage.py lean/AxCheck.lean \
    lean/Lara/Context/Equivalence.lean lean/Lara/Context/Observation.lean \
    lean/Lara/Context/Fragment.lean lean/Lara/Examples/ContextSemantics.lean \
    lean/Lara/Invariants/Observation.lean
AxCheck coverage passed (90 declarations).
```

Axiom profile of the new and relocated theorems, all in the standard trio:

```
'Lara.Context.obs_eq_obsGen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Context.obsGen_eq_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Context.obsGen_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Context.obs_eq_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Context.backend_replacement_congruence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Context.registry_swap_congruence' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The job count differs from the 154 recorded above because that run was from a cold
`.lake` in a worktree carrying `AxCheck.lean`'s dependencies; this one is `lake build
Lara` against the library root on a warm cache. Both are full builds of their target.
