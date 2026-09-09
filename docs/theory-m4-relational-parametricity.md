# Relational Parametricity over Related Backends (issue #215)

**Landed 2026-09-08.** Lean-only, purely additive. No corpus regeneration, no
freeze-tag bump, no Haskell change.

Modules: `lean/Lara/ListRel.lean`, `lean/Lara/Context/Parametricity.lean`.
The only edits outside those two are import lines in `lean/Lara.lean` and the
pin block in `lean/AxCheck.lean`. Every pre-existing Lean declaration is
untouched — in particular `backend_replacement_congruence` keeps its name, its
statement and its proof.

---

## 1. The theorem

M4 Part A's headline, `Lara.Context.backend_replacement_congruence`
(`lean/Lara/Context/Equivalence.lean:820`), quantifies over a **function**
`f : Assurance → Assurance` and relates `F` to `mapAssurFrag f F`. #187's
acceptance criterion reserves the word *parametricity* for a **relational**
quantifier. This is that theorem with the function replaced by a relation:

```lean
theorem obsGen_parametricity {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
    {R : Assurance → Assurance → Prop} {C : Context} {F₁ F₂ : Fragment}
    (hR : RelInj R)
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F₁) (hF : RelFrag R F₁ F₂)
    (hfix : RelFixesContext R C) :
    obsGen g reg₁ C F₁ = obsGen g reg₂ C F₂
```

The four hypotheses, all in `lean/Lara/Context/Parametricity.lean`:

| Hypothesis | What it says | Functional counterpart |
|---|---|---|
| `RelInj R` | `R` reflects and preserves equality on what it relates — it is the graph of a partial injection | `Function.Injective f` |
| `RelPreserving R CertOk₁ CertOk₂` | acceptance transports, **guarded by `R α β`** | `AssurPreserving f`, unguarded |
| `RelFrag R F₁ F₂` | the two fragments agree on Σ, policy, declared leaves, ground atoms, imports and exports, and their args/atts are pointwise `R`-related | `F₂ = mapAssurFrag f F` |
| `RelFixesContext R C` | `R` relates the context's own material to itself | `FixesContext f C` |

Proved once over an arbitrary projection `g`, exactly as `obsGen_congr` is, so
the semantics-parametric form is an instantiation and not a second proof.

### The instances

| Declaration | Conclusion |
|---|---|
| `Context.obsGen_parametricity` | `obsGen g reg₁ C F₁ = obsGen g reg₂ C F₂`, any projection `g` |
| `Context.backend_replacement_parametricity_sem` | `obsSem sem reg₁ C F₁ = obsSem sem reg₂ C F₂`, any `ExtensionSemantics` |
| `Context.backend_replacement_parametricity` | `obs reg₁ C F₁ = obs reg₂ C F₂`, the grounded reading |
| `Context.backend_replacement_parametricity_local` | the same, under an acceptance hypothesis ranging only over `occurrences F` |
| `Context.backend_replacement_parametricity_local_sem` | the occurrence-local form at any `ExtensionSemantics` |
| `Context.backend_replacement_congruence_of_parametricity` | `backend_replacement_congruence`, re-derived as the `graphOf f` instance |
| `Context.congruence_correspondence` | that re-derivation restates the original **exactly** (`rfl`) |

---

## 2. The theorem table: each `_rel` lemma and the functional lemma it mirrors

| Relational | Functional original | Needs from `R` |
|---|---|---|
| `hasSupport_rel` | `hasSupport_mapAssur` (`lean/Lara/EraseTransport.lean:91`) | `RelPreserving` |
| `hasAttack_rel` | `hasAttack_mapAssur` (`lean/Lara/EraseTransport.lean:145`) | `RelPreserving` |
| `relTerm_subterm` | `Erase.mapAssur_subterm` (`lean/Lara/Erase.lean:125`) | nothing |
| `conflictAttackableB_rel` | `conflictAttackableB_mapAssur` (`lean/Lara/Context/Equivalence.lean:113`) | nothing |
| `attackFor_rel` | `attackFor_mapAssur` (`lean/Lara/Context/Equivalence.lean:117`) | nothing |
| `crossAttsFrom_rel` | `crossAttsFrom_map` (`lean/Lara/Context/Equivalence.lean:123`) | nothing |
| `conclusionCache_rel` | `conclusionCache_map` (`lean/Lara/Context/Equivalence.lean:175`) | `RelPreserving` |
| `crossAtts_rel` | `crossAtts_relabel` (`lean/Lara/Context/Equivalence.lean:294`) | `RelPreserving` |
| `dedupList_rel` | `dedupList_map_of_injective` (`lean/Lara/Context/Equivalence.lean:84`) | **`RelInj`** |
| `linkFault_rel`, `linkOk_rel`, `linkGamma_rel`, `linkGround_rel` | `linkFault_mapAssurFrag` etc. (`lean/Lara/Context/Equivalence.lean:74-80`) | nothing |
| `link_rel_commutes` | `link_relabel_commutes` (`lean/Lara/Context/Equivalence.lean:319`) | `RelInj`, `RelPreserving` |
| `termWellSorted_rel`, `argsWellSorted_rel`, `signatureStage_rel` | `termWellSorted_mapAssur`, `argsWellSorted_map`, `signatureStage_map` (`lean/Lara/Context/Equivalence.lean:207-234`) | nothing |
| `attackOcc_rel`, `contains_rel`, `covered_rel` | `attackOcc_mapAssurAtt`, `contains_mapAssur`, `covered_mapAssur` (`lean/Lara/Context/Equivalence.lean:248-268`) | **`RelInj`** (see §3.1) |
| `attackComplete_rel` | `attackComplete_map` (`lean/Lara/Context/Equivalence.lean:357`) | `RelInj`, `RelPreserving` |
| `checkUnit_rel` | `checkUnit_map` (`lean/Lara/Context/Equivalence.lean:395`) | **`RelInj`**, `RelPreserving` |
| `containsB_rel`, `containsBList_rel`, `containsBDis_rel` | `containsB_mapAssur` etc. (`lean/Lara/Erase.lean:150-176`) | **`RelInj`** |
| `attackClosureB_rel` | `attackClosureB_mapAssur` (`lean/Lara/Erase.lean:179`) | **`RelInj`** |
| `coveredB_rel` | `coveredB_relabel` (`lean/Lara/Erase.lean:198`) | **`RelInj`** |
| `nodes_conclusion_rel` | `nodes_conclusion_map` (`lean/Lara/Context/Equivalence.lean:455`) | `RelPreserving` |
| `compileUnit_rel` | `compileUnit_map` (`lean/Lara/Context/Equivalence.lean:500`) | `RelInj`, `RelPreserving` |
| `exists_accepted_rel` | `exists_accepted_relabel` (`lean/Lara/Context/Equivalence.lean:694`) | both |
| `compileUnit_link_rel` | `compileUnit_link_relabel` (`lean/Lara/Context/Equivalence.lean:712`) | both |
| `obsGen_parametricity` | `obsGen_congr` (`lean/Lara/Context/Equivalence.lean:784`) | both |
| `backend_replacement_parametricity_local` | `registry_swap_congruence` (`lean/Lara/Context/Equivalence.lean:879`) | `R := occRel F`, so both are discharged internally — a **trade**, not a strengthening: acceptance weakens to `occurrences F`, but `hC`/`hA` are new (§6) |
| `backend_replacement_parametricity_local_sem` | `registry_swap_congruence_sem` (`lean/Lara/Context/Observation.lean:345`) | ″ |

`Lara.Forall₂` (`lean/Lara/ListRel.lean`) is the pointwise list relation the
development consumes. **Core Lean 4.32.0 has no `List.Forall₂`** — it is a
Mathlib name, and this repository has no Mathlib dependency — so the family and
its nine lemmas are authored locally. Its own module because it has its own
vocabulary (lists, not certificates), its own dependencies (core only), and its
own reason to be read alone: CLAUDE.md's seam test.

`RelTerms`/`RelDis` are *not* `Forall₂` instances. They must be declared in the
same `mutual` block as `RelTerm`, which recurses through `SupportTerm`'s nested
`List` fields (`lean/Lara/Support.lean:60` records the general constraint).
`relTerms_iff_forall₂` bridges the two spellings at their construction sites.

---

## 3. Why `RelInj` is necessary

`RelInj R` says `R` reflects **and** preserves equality on the assurances it
relates. Three consumers force it, and they are not proof-engineering
conveniences — each one is a place where the calculus itself compares terms:

1. **`dedupList`** — the structural merge (`Context/Fragment.lean:68`) decides
   `x ∈ rest`, so a relation collapsing two distinct arguments changes the
   merged argument *list*, hence the node count of the compiled AF.
2. **`coveredB`** (`Compile.lean:441`) — decides `k.source = source`, so a
   collapsing relation adds edges. `Lara/Erase.lean`'s own header already
   records this for the non-injective erase-to-`certified` map: "collapsing
   distinct subterms can merge occurrences and add subargument-closure edges."
3. **`checkUnit_complete`'s `Nodup` premise** on the merged argument list
   (`Check/Unit.lean:234`), discharged here by `nodup_rel`.

This is **witnessed, not asserted**. `Context.relInj_necessary` is
`coveredB_rel` with `hR` deleted and the conclusion negated: it exhibits a
relation, two attack lists, and two source/target pairs satisfying every
remaining hypothesis, on which the two coverage verdicts differ. If a proof of
`coveredB_rel` ever appears to go through without `hR`, one of the two is wrong.

`RelInj` is also **characterized** rather than described:
`relInj_functional` proves `R` is single-valued and `relInj_injective` proves it
is injective. Both halves are load-bearing for §4 and neither is left to prose.

So the honest name for what is proved is **parametricity over partial-bijective
certificate relations**.

### 3.1 Where the relational form costs a hypothesis the functional one did not

`attackOcc_rel` and `contains_rel` carry `RelInj R` where their functional
originals carry nothing. The reason is structural, not incidental: the
functional lemmas may *compute* the image occurrence as `mapAssur f t`, so its
uniqueness is free. A relation supplies no such image, so the occurrence has to
be produced (`attackOcc_rel_exists`) and then pinned to the one the caller
already holds — which is exactly `relTerm_inj`, i.e. `RelInj`. Every call site
already carries `RelInj`, so nothing downstream weakens.

---

## 4. What the relational form buys, and why that is the whole content

This section is the milestone's justification. It is not obvious and it is
easy to overstate, so it is stated in full.

`relInj_functional` shows that `RelInj R` makes `R` a partial **function** as
well as injective. Consequently `RelFrag R F₁ F₂` always exhibits *some* total
injective `f` with `F₂ = mapAssurFrag f F₁` — extend `R` off its domain
arbitrarily and injectively. So every conclusion
`backend_replacement_parametricity` reaches is **already reachable** through the
existing `backend_replacement_congruence` …

> **This step is prose, not proof.** `relInj_functional` is mechanized and gives
> the *partial* function; the extension of a partial injection on `Assurance` to
> a total injective one is a separate construction that no lemma in this
> development supplies. The argument is stated here because it is what motivates
> `backend_replacement_parametricity_local`, and it is flagged rather than
> mechanized because nothing proved depends on it — no theorem takes it as a
> premise. Mechanizing it is **#279**.

… **except** that such an extension `f` must also satisfy `AssurPreserving f`
**globally**, and no such extension need exist. If `certOkOf reg₂` accepts
nothing outside `R`'s range, then any accepted `α` off `R`'s domain has no valid
image, and there is no total injective `f` making the functional theorem apply.

That gap — and nothing else — is what the relational form buys.
`RelPreserving R` is *conditioned on `R α β`*: it obliges only the pairs `R`
actually relates, where `AssurPreserving f` obliges every rule and every
assurance in the type. The gap is exactly the one the codebase already flagged,
twice, in the docstrings of `registry_swap_congruence`
(`lean/Lara/Context/Equivalence.lean:879`) and `registry_swap_congruence_sem`
(`lean/Lara/Context/Observation.lean:345`):

> The hypothesis `hpres` is stated **globally**, over every rule and every
> assurance, rather than over `F`'s certificate occurrences. […] A display of
> this result must therefore say "agrees globally", not "agrees on the
> fragment's occurrences" — the two are different hypotheses and the weaker one
> is not what is proved here.

**The gap is demonstrated, not merely named.** `occRel F` is the identity
relation restricted to `occurrences F`, the assurances the fragment actually
carries; `relInj_occRel` and `relFrag_occRel` discharge the two side
conditions, and

```lean
theorem backend_replacement_parametricity_local
    (hlocal : ∀ r As Cc α, α ∈ occurrences F →
      AssuranceOk (certOkOf reg₁) r As Cc α → AssuranceOk (certOkOf reg₂) r As Cc α)
    (hadm : Admissible reg₁ C F)
    (hC : ∀ α ∈ occursList C.frame.args, α ∈ occurrences F)
    (hA : ∀ α ∈ (C.frame.atts.map occursAtt).flatten, α ∈ occurrences F) :
    obs reg₁ C F = obs reg₂ C F
```

is representation independence under an acceptance hypothesis that ranges over
`F`'s own certificate occurrences and nothing else.
`backend_replacement_parametricity_local_sem` is the same at an arbitrary
`ExtensionSemantics`. Without these two, this milestone would ship a quantifier
shape and demonstrate nothing.

**There is no separate `registry_swap_parametricity`.** The plan proposed one;
its statement is character-for-character `backend_replacement_parametricity_local`
— `registry_swap_congruence` differs from `backend_replacement_congruence` only
by moving no material, and the occurrence-local form already moves no material.
Two names for one theorem would be worse than one, so only one ships. The
occurrence-local *registry swap* at the grounded reading **is**
`backend_replacement_parametricity_local`; at an arbitrary semantics it is
`backend_replacement_parametricity_local_sem`.

---

## 5. Why the grounded fixpoint needed nothing

#215 stated its own sizing risk: *"if it generalizes from 'equal profiles' to
'R-related profiles' without new machinery this is cheap; if the grounded
fixpoint argument needs the equality it is not."*

**It does not.** `compileUnit_rel` concludes an **equation** between
`StructuredAF`s, not a pointwise agreement. `Grounded.statusC` and
`Semantics.observe` are then applied to one and the same framework on both
branches. The relation is erased before any semantics runs. No
grounded-labelling lemma, no `AttackExtensional` hypothesis, and no new fixpoint
machinery appears anywhere in this development — which is the same reason
`obsGen_congr`'s docstring gives for why the generic version was free.

The chain, with the erasure point marked (the same diagram is embedded in
`Parametricity.lean`'s header, so it survives this record):

```
  Layer 0 — the two side conditions
      RelPreserving R
      RelInj R ──► relTerm_inj ──► relAtt_source_inj

  Layer 1 — the judgments transport            [needs RelPreserving]
      hasSupport_rel ──► hasAttack_rel          (not siblings: hasAttack_rel
                                                 calls hasSupport_rel in all
                                                 three of its cases)

  Layer 2 — the saturation                     [needs hasSupport_rel]
      conclusionCache_rel ──► crossAtts_rel

  Layer 3 — the merge and the Bool deciders    [needs relTerm_inj]
      dedupList_rel                             [CONSUMER 1 — dedupList]
      containsB_rel ──► attackClosureB_rel ─┐
      relAtt_source_inj ───────────────────►┴► coveredB_rel
                                                [CONSUMER 2 — coveredB]

  Layer 4 — the linked unit and acceptance
      crossAtts_rel, dedupList_rel        ──► link_rel_commutes
      hasSupport_rel                      ──► attackComplete_rel
      hasSupport_rel, hasAttack_rel,
        attackComplete_rel, relTerm_inj   ──► checkUnit_rel
                                              [CONSUMER 3 — the Nodup premise]

  Layer 5 — the carrier
      link_rel_commutes, checkUnit_rel    ──► exists_accepted_rel
      hasSupport_rel                      ──► nodes_conclusion_rel
      coveredB_rel, nodes_conclusion_rel  ──► compileUnit_rel
      link_rel_commutes, compileUnit_rel  ──► compileUnit_link_rel

  ══════════════════ RELATION ERASED HERE ══════════════════
  `compileUnit_rel` concludes an EQUATION between `StructuredAF`s, so from
  here down both branches run one and the same framework. No fixpoint lemma
  is needed, and none is used.

  Layer 6 — the headline; the single root consumes exists_accepted_rel +
            compileUnit_link_rel, and every other node is an instantiation
      obsGen_parametricity                      (any projection g)
        ├─► backend_replacement_parametricity_sem   (any ExtensionSemantics)
        │     └─► backend_replacement_parametricity_local_sem
        └─► backend_replacement_parametricity     (obs — the obsGen instance at
              │                                    Invariants.status canon;
              │                                    obs_eq_obsGen makes the two
              │                                    result types the same type,
              │                                    so no separate argument is
              │                                    needed)
              ├─► backend_replacement_parametricity_local   (occurrence-local)
              └─► backend_replacement_congruence_of_parametricity  (the
                    └─► congruence_correspondence   functional theorem,
                                                    via graphOf)
```

One bookkeeping difference from the functional development is worth recording.
`linkGamma C (mapAssurFrag f F)` is *definitionally* `linkGamma C F`, so the
functional statements name one Γ throughout. Relationally
`linkGamma C F₂ = linkGamma C F₁` is only a propositional equality
(`linkGamma_rel`), and the accepted unit's **type** mentions Γ — so
`exists_accepted_rel` and `compileUnit_link_rel` rewrite Γ and the ground list
into `F₁`'s form before doing any work. The four `link*_rel` lemmas are `rfl`
functionally and honest rewrites relationally, for the same reason.

---

## 6. How local "local" actually is

`RelFixesContext R C` requires `R` to relate the context's own material to
itself. Combined with `RelInj`, that makes `R` the **identity** on the context's
occurrences: an assurance appearing in both `C` and `F` cannot move.

This is inherited from `FixesContext` and is correct — a backend swap inside a
fragment is not licensed to rename the *context's* certificates, and a statement
that let it would be comparing two different contexts. But it is a real bound on
§4's claim, and it is why `backend_replacement_parametricity_local` carries the
two side hypotheses `hC` and `hA`: the localization is to `F`'s occurrences
*plus* whatever the context also carries, not to `F`'s occurrences alone.

---

## 7. Paper claim boundary

### May claim

- Representation independence over related backends is proved with a
  **relational** quantifier: `R : Assurance → Assurance → Prop`, lifted
  structurally through support terms, attacks and fragments
  (`obsGen_parametricity`).
- It holds at **every** `ExtensionSemantics` in the M2a interface, with no
  additional hypothesis (`backend_replacement_parametricity_sem`), because the
  whole chain factors through the single choke point `obsGen`.
- The acceptance hypothesis can be **localized to the fragment's own
  certificate occurrences** (`backend_replacement_parametricity_local`,
  `_local_sem`) — the localization the docstrings of `registry_swap_congruence`
  and `registry_swap_congruence_sem` name as the hypothesis they do not
  themselves carry, and point at by name (#276). State the trade, not
  a pure upgrade: the localized theorem is **not** strictly stronger than
  `registry_swap_congruence`. It weakens the acceptance hypothesis to
  `α ∈ occurrences F` but **adds** `hC` and `hA`, requiring the context's own
  occurrences to lie inside `occurrences F`. Neither theorem implies the other.
  The honest sentence is "localizes the acceptance hypothesis at the cost of two
  context-containment side conditions", never "strictly stronger".
- The existing functional theorem is **re-derived**, not paralleled:
  `backend_replacement_congruence_of_parametricity` is the `graphOf f`
  instance, and `congruence_correspondence` checks by `rfl` that it restates
  `backend_replacement_congruence` exactly. Nothing in
  `Lara.Context.Equivalence` is now stated more generally than what is proved
  here.
- `RelInj` is *forced by the coverage decider*, not by the proof strategy —
  `relInj_necessary` is the witness at that level: it is `coveredB_rel`'s
  hypotheses minus `hR` with the conclusion negated, so no proof of
  `coveredB_rel` can drop it. The **observational** separation — two fragments
  related by a non-functional `R` whose `obs` differ — is not yet witnessed;
  that upgrade is **#275**. See "Must not claim" below.

### Must not claim

- **Not parametricity over arbitrary relations.** `RelInj` is required, and
  `relInj_necessary` shows why: it is `coveredB_rel` with `hR` deleted and the
  conclusion negated. The honest phrase is "parametricity over
  partial-bijective certificate relations".
- **Not full abstraction.** `RelTerm` is a *structural lifting of a relation on
  certificates*. It is **not** the logical relation over the contrary-visible
  occurrence profile that `docs/theory-m4-contextual-adequacy.md` §7's G1
  describes, and nothing here reopens Part B. #215 landing does **not** amortize
  the G1 freeze.
- **Not unconditional in the context quantifier.** `Admissible reg₁ C F₁` is
  inherited, for the reason `backend_replacement_congruence` records: `obs`
  reports a checker rejection separately from an observed status list, and a
  forward-only acceptance hypothesis lets `reg₂` accept what `reg₁` rejects.
- **Not local to `F` alone.** See §6: `RelFixesContext` plus `RelInj` pin `R` to
  the identity on the context's occurrences too.
- **Not a witnessed observational separation.** `relInj_necessary` is a
  separation at the level of the *coverage decider*, on two hand-built terms. No
  fixture exhibits two fragments related by a genuinely non-functional `R` whose
  observations differ. Deferred: **#275**.
- **Not a family-wide result.** `docs/theory-m4-generic-observation.md:41`
  records four M4 congruences at an arbitrary `sem`. Two now have relational
  companions (`backend_replacement_congruence_sem` →
  `backend_replacement_parametricity_sem`; `registry_swap_congruence_sem` →
  `backend_replacement_parametricity_local_sem`). Two do **not**:
  `backend_replacement_congruence_composed_sem` and
  `whole_program_replacement_sem`. For those the original boundary stands
  unchanged. Deferred: **#277**.
- **Not a fully mechanized strength argument.** §4's step from
  "`R` is a partial function" to "some *total injective* `f` realizes it" is
  prose; `relInj_functional` gives only the partial function. Nothing proved
  depends on it — it motivates
  `backend_replacement_parametricity_local` rather than premising any theorem —
  but it is not a mechanized fact. Deferred: **#279**.
- **Not a Haskell-side result.** No checker, CLI, wire or corpus surface moves.

---

## 8. Verification

- `lake build` clean; `Lara/ListRel.lean` and `Lara/Context/Parametricity.lean`
  are both inside the build closure (a `.olean` exists for each — the #259
  failure mode).
- `scripts/check-axioms.sh` clean: every new declaration depends only on
  `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`
  (which would introduce `Lean.ofReduceBool` and fail the gate), no new axiom.
- `scripts/check-axcheck-coverage.py` clean over both new modules: every
  theorem carries a `#print axioms` line.
- Both new modules carry `set_option autoImplicit false`. This is load-bearing,
  not style: `lean/lakefile.toml` sets no `leanOptions`, so `autoImplicit` is on
  tree-wide, and a bare or mistyped predicate in a hypothesis position would
  auto-bind as an implicit of unknown type and elaborate into a **vacuous**
  theorem that builds clean and passes both CI gates. Neither gate can see that;
  this option is the only thing that can.
