/-
# Theory M4, phase F2 — the semantics parameter is not inert *at the context level*

`Lara.Context.obsSem` (`lean/Lara/Context/Observation.lean:119`) quantifies over
`Semantics.ExtensionSemantics`, and every theorem proved about it holds for all
of them at once. That is exactly the shape a *vacuous* generalization would also
have. Nothing in `Lara/Context/Observation.lean` rules out the reading that the
parameter ranges, as far as contextual observation can tell, over a one-element
set: `obsGen_congr` is indifferent to `g` by construction, `obsSem_grounded`
pins one instance, and the remaining declarations are instantiations of those
two. Under that reading the milestone would have added a binder and no content.

The existing M4 fixtures cannot refute it. `Lara.Examples.Linking`'s carriers
are a two-node chain — `ctxEx`/`fragEx` (`lean/Lara/Examples/Linking.lean:43`
and `:47`), where `q` undermines `p` and nothing attacks `q` — and a two-node
mutual rebut observed at a singleton support, `symCtx`/`symFrag`
(`lean/Lara/Examples/Linking.lean:592`, `:595`). Both are frameworks on which
all five instances of `ExtensionSemantics` agree — checked, not asserted:
`obsSem_linking_agrees` and `obsSem_sym_agrees` below state the agreement at the
two carriers, five conjuncts each. This module supplies the carriers where they
do not agree.

### What is separated, and how sharply

Two fixtures, each a *linked* carrier — assembled across a context/fragment
boundary by `linkedUnit`, not written down as a bare `Grounded.AF`:

* **the three-cycle** (`cycleCtx`/`cycleFrag`): `stableSem` reports
  `ClaimObservation.noExtension` where `groundedSem` reports
  `observed contested`. This is the sharper of the two, because `noExtension` is
  a constructor that *no* grounded observation can produce —
  `Invariants.observeSem_grounded` (`lean/Lara/Invariants/Observation.lean:90`)
  returns `ClaimObservation.observed _` unconditionally, and `liftObservation`
  (`lean/Lara/Context/Observation.lean:171`) only ever emits that constructor.
  So `obsSem` is visibly *wider* than `obs`, not merely differently valued on
  some input.
* **the two-cycle with a sink** (`sinkCtx`/`sinkFrag`): `preferredSem` reports
  `observed defeated` where `groundedSem` reports `observed contested`. Here
  neither side reports `noExtension` — both semantics answer, and the answers
  differ. So the separation is not an artefact of one semantics having nothing
  to say.

Both separations are stated as three-conjunct theorems whose last conjunct is a
disequality between the two `obsSem` calls. That is deliberate: a fixture that
silently collapsed — both semantics agreeing after some future change to the
link, the saturation, or the contrary table — would then break the build rather
than leave a human to notice that two separately pinned values had become equal.

### Their framework-level ancestors, and what is new here

The framework-level separations already exist: `Examples.Semantics.threeCycle`
(`lean/Lara/Examples/Semantics.lean:108`) with
`stableSem_enumerate_threeCycle` (`:185`), and
`Examples.Semantics.twoCycleSink` (`:139`) with
`observe_twoCycleSink_grounded_ne_preferred` (`:333`). Those are hand-written
`AF`s handed straight to `Semantics.observe`. What is new below is that the same
two shapes are *reached through the whole M4 pipeline* — link guard,
cross-boundary attack saturation, whole-unit checker, `Invariants.compileUnit`,
`Invariants.eraseAF` — from material split across a context and a fragment
neither of which contains the cycle on its own. Nothing here re-proves a
property of Dung frameworks; what is checked is that the pipeline delivers the
carrier the separation needs, and that `obsSem` reads it.

### The inert witnesses, named as such

`congruence_witness_sem`, `registry_swap_witness_sem` and
`obsSem_linking_agrees` all sit at `ctxEx`/`fragEx`, where the semantics agree.
The first two are quantified over `sem`, and that quantifier is **inert** there:
they witness that the congruence hypotheses are inhabited and that the
semantics-parametric plumbing type-checks, not that the parameter does any work.
The honest reading of each is written into its own docstring rather than left to
this header.

### Proof budget

Everything closes by `decide`, `rfl`, or a short term, except
`obsSem_gap_uniform` (a case split on the checker) and the two failure-arm
theorems (which must go through `obsSem_incompatible` / `obsSem_rejected`, since
`decide` cannot close a goal with a free `sem`). `native_decide` is not used
anywhere and must not be: it depends on `Lean.ofReduceBool`, which is outside
the standard axiom trio the `AxCheck.lean` gate enforces.

This module is purely additive. It changes no existing declaration, and the only
edit it makes outside itself is one import line in `lean/Lara.lean`.
-/

import Lara.Examples
import Lara.Examples.Linking
import Lara.Context.Observation

set_option autoImplicit false

namespace Lara.Examples.ContextSemantics

open Lara.Support Lara.Attack Lara.Compile Lara.Check Lara.Erase Lara.Semantics
open Lara.Context hiding Context
open Lara.Examples.Linking

/-! ### The three-cycle: `stableSem` reports `noExtension`

A `DefeatPolicy`'s contrary list is a list of **(source-pattern,
target-pattern)** pairs, exactly as `Lara.Examples.dpEx`
(`lean/Lara/Examples.lean:1494`) is: `dpEx = ⟨[(apB, apA)], []⟩` is what makes
the saturated attack `Lara.Examples.kAtk = .undermine (.leaf l2) (.leaf l1) []`
(`lean/Lara/Examples.lean:1466`), and `l2` concludes `q` while `l1` concludes
`p`, so `(apB, apA)` reads *q attacks p*. `cyclePolicy` follows the shape of
`Linking.symPolicy` (`lean/Lara/Examples/Linking.lean:589`), changing only
`unitPolicyEx`'s `defeat` field, and reuses `Linking.apS`
(`lean/Lara/Examples/Linking.lean:739`) for the `s` pattern rather than
introducing a second name for it.

The split. The context declares and asserts `l2` (conclusion `q`); the fragment
declares and asserts `l1` (`p`) and `l3` (`s`). Two of the three edges cross the
boundary and are supplied by `crossAtts` (`lean/Lara/Context/Fragment.lean:207`)
— the mechanism `Linking.crossAtts_nonempty`
(`lean/Lara/Examples/Linking.lean:139`) pins. The third, `s ⊣ p`, has **both
endpoints among the fragment's own arguments**, so the fragment must declare it
itself: `SideOk.attack_complete` (`lean/Lara/Context/Link.lean:631`) obliges a
side to cover every contrary pair internal to it, and
`Linking.hostile_composite_not_sideOk` (`lean/Lara/Examples/Linking.lean:561`)
is the witness that omitting such an attack really does break well-formedness.

The linked carrier, with node indices as `Invariants.eraseAF` assigns them.
Node order in a link is **context arguments first, then fragment arguments**
(`Linking.linked_args`, `lean/Lara/Examples/Linking.lean:145`); the order drawn
below is not assumed but pinned by `cycle_linked_shape`, as is the edge list.

```
              context side   |   fragment side
                             |
       0 = .leaf l2  (q)     |   1 = .leaf l1  (p)      2 = .leaf l3  (s)

              1 ──▶ 0    p ⊣ q   (saturated by crossAtts)
              0 ──▶ 2    q ⊣ s   (saturated by crossAtts)
              2 ──▶ 1    s ⊣ p   (declared by the fragment)

                        ┌───────── 0 ◀───── 1
                        │                   ▲
                        └────────▶ 2 ───────┘
```

Reading the loop off the edges: `1 → 0 → 2 → 1`, the odd cycle. The fragment's
single export is `p`, which is node `1`. -/

/-- `p ⊣ q`, `q ⊣ s`, `s ⊣ p` — the three-cycle as a contrary table. Only
`unitPolicyEx`'s `defeat` field changes; the rule list is untouched, so the R12
obligation (no strict rule whose conclusion touches a contrary side) is
discharged for the same reason it is under `unitPolicyEx`: every rule there is
defeasible. -/
def cyclePolicy : Policy.Policy :=
  { unitPolicyEx with defeat := ⟨[(apA, apB), (apB, apS), (apS, apA)], []⟩ }

/-- `Linking.ctxFrame` under the cyclic policy: it still declares and asserts
`l2` alone. The context contributes exactly one node of the cycle, which is why
neither side contains the cycle by itself. -/
def cycleCtx : Lara.Context.Context := ⟨{ ctxFrame with policy := cyclePolicy }⟩

/-- The other two nodes, plus the one edge whose endpoints are both its own.
Exports `p`, the node the separation is observed at. -/
def cycleFrag : Fragment :=
  { sigma := sigmaEx, policy := cyclePolicy
  , gammaFrag := [(l1, pA), (l3, pC)], ground := [pA, pC]
  , args := [.leaf l1, .leaf l3]
  , atts := [.undermine (.leaf l3) (.leaf l1) []]
  , imports := Interface.closed, exports := [pA] }

/-- The link guard passes. Pinned before the observations so that a fixture
which stopped linking is distinguishable from a separation that collapsed. -/
theorem cycle_link_ok : linkOk cycleCtx cycleFrag = true := by decide

/-- The merged unit is accepted by the executable whole-unit checker, so the
observations below are taken on `ObservationOf.observed` rather than on a rejection.
Same role as `Linking.linked_accepted` (`lean/Lara/Examples/Linking.lean:149`). -/
theorem cycle_accepted :
    (Check.Unit.checkUnit (linkGamma cycleCtx cycleFrag) registryEx
      (linkGround cycleCtx cycleFrag) (linkedUnit registryEx cycleCtx cycleFrag)).isOk
      = true := by decide

/-- **The linked carrier is the odd cycle the diagram above draws.** Both halves
are evaluated rather than assumed: the argument list fixes the node indices, and
the attack list fixes the edges and their direction. The fragment declared one
of the three attacks; saturation supplied the other two, and the order they
appear in is the order `linkedUnit` assembles them — the sides' own attacks
first, then `crossAtts`. -/
theorem cycle_linked_shape :
    (linkedUnit registryEx cycleCtx cycleFrag).args = [.leaf l2, .leaf l1, .leaf l3] ∧
      (linkedUnit registryEx cycleCtx cycleFrag).atts
        = [ .undermine (.leaf l3) (.leaf l1) []
          , .undermine (.leaf l2) (.leaf l3) []
          , .undermine (.leaf l1) (.leaf l2) [] ] :=
  ⟨rfl, rfl⟩

/-- **The sharpest available separation.** On the linked three-cycle,
`groundedSem` observes the exported claim `contested` while `stableSem` observes
`ClaimObservation.noExtension` — there is no stable extension at all, which is
the framework-level fact `Examples.Semantics.stableSem_enumerate_threeCycle`
(`lean/Lara/Examples/Semantics.lean:185`) records for the bare cycle.

Why this is the sharp form. `noExtension` is a constructor the grounded reading
provably cannot reach: `Invariants.observeSem_grounded`
(`lean/Lara/Invariants/Observation.lean:90`) always returns
`ClaimObservation.observed _`, and `liftObservation`
(`lean/Lara/Context/Observation.lean:171`) only produces that constructor too.
So this does not merely show `obsSem` taking two values; it shows `obsSem`
inhabiting an arm of `ObservationOf ClaimObservation` that `liftObservation ∘ obs`
cannot inhabit. The widening of the observed payload from `Grounded.Status` to
`ClaimObservation` is therefore forced by a fixture of this development, not
only by `Semantics.observe`'s signature.

The third conjunct is not redundant bookkeeping. It is what makes a future
collapse of this fixture a build failure rather than a silent regression of two
values that happen to be pinned separately.

What may **not** be concluded: nothing here says the two semantics differ on any
other carrier, and nothing here bears on `ctxEquivSem_grounded_iff`
(`lean/Lara/Context/Observation.lean:281`), which is a statement about
`groundedSem` alone. -/
theorem obsSem_cycle_stable_ne_grounded :
    obsSem groundedSem registryEx cycleCtx cycleFrag
        = .observed [ClaimObservation.observed Grounded.Status.contested] ∧
      obsSem stableSem registryEx cycleCtx cycleFrag
        = .observed [ClaimObservation.noExtension] ∧
      obsSem groundedSem registryEx cycleCtx cycleFrag
        ≠ obsSem stableSem registryEx cycleCtx cycleFrag := by
  decide

/-! ### The sink: two semantics that both answer, and disagree

`p` and `q` rebut each other and both attack `s`. The context declares and
asserts `q`; the fragment declares and asserts `p` and `s`, declares the
same-side `p ⊣ s` edge — required of it by `SideOk.attack_complete`, exactly as
in the cycle above — and exports `s`. The grounded extension is empty, so `s` is
`undec` and observed `contested`; the preferred extensions are `{p}` and `{q}`,
each of which attacks `s`, so `s` is skeptically `defeated`.

The framework-level ancestor is
`Examples.Semantics.observe_twoCycleSink_grounded_ne_preferred`
(`lean/Lara/Examples/Semantics.lean:333`), stated on the hand-written
`twoCycleSink` (`:139`). What is added here is that the same shape arrives
through the link.

Node indices and edges, pinned by `sink_linked_shape`:

```
              context side   |   fragment side
                             |
       0 = .leaf l2  (q)     |   1 = .leaf l1  (p)      2 = .leaf l3  (s)

              1 ──▶ 2    p ⊣ s   (declared by the fragment)
              0 ──▶ 1    q ⊣ p   (saturated by crossAtts)
              0 ──▶ 2    q ⊣ s   (saturated by crossAtts)
              1 ──▶ 0    p ⊣ q   (saturated by crossAtts)

                        0 ◀────▶ 1
                          ╲     ╱
                           ▼   ▼
                             2
```

The export is `s`, node `2` — the sink, attacked by both members of the
two-cycle and attacking nothing. -/

/-- `p ⊣ q`, `q ⊣ p`, `p ⊣ s`, `q ⊣ s`. A superset of `Linking.symPolicy`'s
table (`lean/Lara/Examples/Linking.lean:589`), which has the mutual rebut but no
sink — which is why `Linking.obs_contested` (`:597`) sees no disagreement and
this fixture does. -/
def sinkPolicy : Policy.Policy :=
  { unitPolicyEx with defeat := ⟨[(apA, apB), (apB, apA), (apA, apS), (apB, apS)], []⟩ }

/-- `Linking.ctxFrame` under the sink policy: one member of the two-cycle. -/
def sinkCtx : Lara.Context.Context := ⟨{ ctxFrame with policy := sinkPolicy }⟩

/-- The other member of the two-cycle, the sink, and the one edge internal to
the fragment. Exports the sink's conclusion `s`. -/
def sinkFrag : Fragment :=
  { sigma := sigmaEx, policy := sinkPolicy
  , gammaFrag := [(l1, pA), (l3, pC)], ground := [pA, pC]
  , args := [.leaf l1, .leaf l3]
  , atts := [.undermine (.leaf l1) (.leaf l3) []]
  , imports := Interface.closed, exports := [pC] }

theorem sink_link_ok : linkOk sinkCtx sinkFrag = true := by decide

theorem sink_accepted :
    (Check.Unit.checkUnit (linkGamma sinkCtx sinkFrag) registryEx
      (linkGround sinkCtx sinkFrag) (linkedUnit registryEx sinkCtx sinkFrag)).isOk
      = true := by decide

/-- **The linked carrier is the two-cycle-with-sink the diagram above draws.**
As with `cycle_linked_shape`, both the node order and the edge list are
evaluated rather than asserted. Three of the four attacks were supplied by
saturation; the fragment declared only `p ⊣ s`. -/
theorem sink_linked_shape :
    (linkedUnit registryEx sinkCtx sinkFrag).args = [.leaf l2, .leaf l1, .leaf l3] ∧
      (linkedUnit registryEx sinkCtx sinkFrag).atts
        = [ .undermine (.leaf l1) (.leaf l3) []
          , .undermine (.leaf l2) (.leaf l1) []
          , .undermine (.leaf l2) (.leaf l3) []
          , .undermine (.leaf l1) (.leaf l2) [] ] :=
  ⟨rfl, rfl⟩

/-- **A separation in which both semantics answer.** `groundedSem` observes the
exported sink `contested`, `preferredSem` observes it `defeated`, and the two
differ.

Read this beside `obsSem_cycle_stable_ne_grounded`, which it deliberately does
not duplicate. There, one semantics had nothing to say, and the disagreement
could be attributed to that: a sceptic could grant the `noExtension` arm and
still hold that whenever two semantics *both* produce a status, the status is
the same. This refutes that reading. Neither observation is `noExtension`, both
are `ClaimObservation.observed`, and the wrapped statuses differ. So the
semantics parameter changes the answer, not merely whether there is one.

As above, the disequality conjunct is what turns a collapse of this fixture into
a build failure. -/
theorem obsSem_sink_preferred_ne_grounded :
    obsSem groundedSem registryEx sinkCtx sinkFrag
        = .observed [ClaimObservation.observed Grounded.Status.contested] ∧
      obsSem preferredSem registryEx sinkCtx sinkFrag
        = .observed [ClaimObservation.observed Grounded.Status.defeated] ∧
      obsSem groundedSem registryEx sinkCtx sinkFrag
        ≠ obsSem preferredSem registryEx sinkCtx sinkFrag := by
  decide

/-! ### The congruence hypotheses are inhabited, at every semantics

Without these, `backend_replacement_congruence_sem` and
`registry_swap_congruence_sem` would be conditionals whose premises are not
known to hold of anything, and `CtxEquivSem` would have no witness of any kind.
They are the semantics-parametric counterparts of `Linking.congruence_witness`
(`lean/Lara/Examples/Linking.lean:676`) and `Linking.registry_swap_witness`
(`:670`), and they reuse those witnesses' inputs verbatim:
`Linking.admissible_split` (`:345`), `Linking.assurPreserving_onlyNd` (`:658`),
`Linking.registryOnlyNd` (`:637`), and `fixesContext_id`
(`lean/Lara/Context/Equivalence.lean:857`). -/

/-- **The congruence, instantiated at every semantics at once.**

What this establishes, precisely: the hypotheses of
`backend_replacement_congruence_sem` (`lean/Lara/Context/Observation.lean:317`)
are inhabited, and its conclusion type-checks and is provable at a concrete
link, uniformly in `sem`.

What it does **not** establish, and must not be read as establishing. The `sem`
quantifier is **inert here**. The carrier is `ctxEx`/`fragEx`, the two-node
chain on which all five semantics agree (`obsSem_linking_agrees` below) — so
this theorem would be equally provable if `ExtensionSemantics` had
one inhabitant. The theorems that make the parameter non-trivial are
`obsSem_cycle_stable_ne_grounded` and `obsSem_sink_preferred_ne_grounded`, not
this one.

The assurance-free caveat that `docs/theory-m4-contextual-adequacy.md` §1
records for `Linking.congruence_witness` applies here unchanged and for the same
reason: `fragEx` is a fragment of bare leaves carrying no certificate, so
`mapAssurFrag id` — indeed `mapAssurFrag f` for *every* `f` — is the identity on
it. This is a shape witness. The fixture that exercises a real backend swap is
`Linking.cert_congruence_witness` (`lean/Lara/Examples/Linking.lean:1025`), and
it is grounded-only; no semantics-parametric counterpart of it is claimed
here. -/
theorem congruence_witness_sem (sem : ExtensionSemantics) :
    obsSem sem registryEx ctxEx fragEx
      = obsSem sem registryEx ctxEx (mapAssurFrag id fragEx) :=
  backend_replacement_congruence_sem sem (fun _ _ h => h) (fun _ _ _ _ h => h)
    (admissible_split registryEx) (fixesContext_id ctxEx)

/-- **D6, at every semantics at once.** Two genuinely different registries —
`Linking.registryOnlyNd_ne_registryEx` (`lean/Lara/Examples/Linking.lean:645`)
proves they differ — read the same fragment the same way, under every extension
semantics.

The same two caveats as `congruence_witness_sem` apply verbatim: the `sem`
quantifier is inert at this carrier, and the fragment carries no certificate, so
the acceptance-profile hypothesis is discharged against material that has no
assurance to preserve. The certificate-bearing grounded counterpart is
`Linking.cert_registry_swap_witness` (`lean/Lara/Examples/Linking.lean:909`). -/
theorem registry_swap_witness_sem (sem : ExtensionSemantics) :
    obsSem sem registryOnlyNd ctxEx fragEx = obsSem sem registryEx ctxEx fragEx :=
  registry_swap_congruence_sem sem assurPreserving_onlyNd
    (admissible_split registryOnlyNd)

/-! ### `CtxEquivSem` is false of something -/

/-- **A `CtxEquivSem` negative pair at `stableSem`.** The two fragments export
the same conclusion; `Linking.quietCtx` (`lean/Lara/Examples/Linking.lean:58`)
tells them apart, because `fragEx` supplies an argument for its export and
`Linking.silentFrag` (`:610`) supplies none.

This is the semantics-parametric counterpart of `Linking.ctxEquiv_negative`
(`lean/Lara/Examples/Linking.lean:616`) and exists for the same reason: without
it, "no context distinguishes them" would be a statement about a relation
nothing is known to be false of, and `CtxEquivSem` would be trivially
satisfiable for all anyone could tell.

It is stated at `stableSem` — a non-grounded instance — so that it is not merely
`ctxEquiv_negative` transported through `ctxEquivSem_grounded_iff`. That
transported form is `ctxEquivSem_grounded_negative` below, and it is a different
theorem with a different purpose. -/
theorem ctxEquivSem_negative : ¬ CtxEquivSem stableSem registryEx fragEx silentFrag := by
  intro h
  have hq := h quietCtx
  have hj : obsSem stableSem registryEx quietCtx fragEx
      = .observed [ClaimObservation.observed Grounded.Status.justified] := by decide
  rw [hj] at hq
  exact absurd hq (by decide)

/-! ### Both directions of `ctxEquivSem_grounded_iff` are load-bearing

`ctxEquivSem_grounded_iff` (`lean/Lara/Context/Observation.lean:281`) is stated
as an `iff`, and the milestone requires it to stay one. But nothing in the
development consumed either direction, so weakening it to a one-way implication
— in *either* direction — would have left `lake build` green and both axiom
gates passing. The two theorems below fix that by consuming one direction each.

Their **content is not the point**. The first restates
`Linking.ctxEquiv_negative`; the second restates half of the `iff` it cites.
Neither is a new result and neither is offered as one. Their purpose is
mechanical: each one's proof term mentions `.mp` or `.mpr`, so removing that
direction from `ctxEquivSem_grounded_iff` breaks the build. -/

/-- Consumes the **forward** direction (`.mp`) of `ctxEquivSem_grounded_iff`.

Stated at `groundedSem`, where — unlike `ctxEquivSem_negative` — the answer is
already known from `Linking.ctxEquiv_negative`
(`lean/Lara/Examples/Linking.lean:616`); the derivation *through* the `iff` is
the whole reason the theorem is here. -/
theorem ctxEquivSem_grounded_negative : ¬ CtxEquivSem groundedSem registryEx fragEx silentFrag :=
  fun h => Linking.ctxEquiv_negative ((ctxEquivSem_grounded_iff registryEx fragEx silentFrag).mp h)

/-- Consumes the **backward** direction (`.mpr`) of `ctxEquivSem_grounded_iff`.

Read the scope exactly as `ctxEquivSem_grounded_iff`'s own docstring instructs:
this transports `CtxEquiv` into `CtxEquivSem` **at `groundedSem` only**. It is
not, and must not be cited as, a licence to infer `CtxEquivSem sem reg F₁ F₂`
from `CtxEquiv reg F₁ F₂` for a general `sem`. The two fixtures at the top of
this file are why such an inference would need an argument nobody has made: the
semantics genuinely disagree about `contested` versus `defeated`, and about
whether there is an extension at all. -/
theorem ctxEquivSem_grounded_of_ctxEquiv {F₁ F₂ : Fragment} (h : CtxEquiv registryEx F₁ F₂) :
    CtxEquivSem groundedSem registryEx F₁ F₂ :=
  (ctxEquivSem_grounded_iff registryEx F₁ F₂).mpr h

/-! ### The grounded regression, exercised — and the agreement it sits in -/

/-- **`obsSem_grounded` (`lean/Lara/Context/Observation.lean:235`), used.**

The grounded reading of `Linking`'s acyclic fixture is derived *through* the
regression theorem — `rw [obsSem_grounded, Linking.obs_defeated]` — rather than
recomputed by an independent `rfl`. That matters: `obsSem_grounded` is the
theorem the entire "generalization, not replacement" argument rests on, and
before this nothing in the development consumed it. A regression theorem no
fixture exercises is a regression theorem whose failure mode is invisible.

The right-hand side is left as `liftObservation (.observed [Grounded.Status.defeated])`
rather than unfolded, deliberately: the point is the composite
`liftObservation ∘ obs`, which is what `obsSem_grounded` equates
`obsSem groundedSem` to. `obsSem_linking_agrees` below states the unfolded
value. -/
theorem obsSem_linking_grounded :
    obsSem groundedSem registryEx ctxEx fragEx
      = liftObservation (.observed [Grounded.Status.defeated]) := by
  rw [obsSem_grounded, Linking.obs_defeated]

/-- **Agreement at the acyclic carrier.** All five instances of
`ExtensionSemantics` observe `Linking.fragEx`'s export identically in
`Linking.ctxEx`.

This is not vacuous and it is not in tension with the separations above.
`ctxEx`/`fragEx` is a two-node chain in which `q` undermines `p` and nothing
attacks `q`, so it is well-founded: the grounded extension `{q}` is also the
unique preferred extension and the unique stable one, and every semantics that
respects admissibility must defeat `p` there. Disagreement between semantics is
a property of particular carriers — odd cycles, even cycles with sinks — not a
pervasive instability of `obsSem`. Recording the agreement makes that boundary
explicit, rather than leaving a reader to infer from the separations that
`obsSem` is unpredictable in general.

It is also the precise sense in which the fixtures of `Lara.Examples.Linking`
are undisturbed by this module: read at any of the five semantics, the link they
pin reports what they say it reports.

All five are listed rather than a representative three because this module's
header asserts the agreement, and an asserted fact with no proof behind it is
exactly what `Lara.Examples.Semantics`'s header records having had to promote to
theorems after the fact. `Examples.Semantics.allSemantics_complete`
(`lean/Lara/Examples/Semantics.lean:877`) is what makes "all five" a closed
list. -/
theorem obsSem_linking_agrees :
    obsSem groundedSem registryEx ctxEx fragEx
        = .observed [ClaimObservation.observed Grounded.Status.defeated] ∧
      obsSem preferredSem registryEx ctxEx fragEx
        = .observed [ClaimObservation.observed Grounded.Status.defeated] ∧
      obsSem stableSem registryEx ctxEx fragEx
        = .observed [ClaimObservation.observed Grounded.Status.defeated] ∧
      obsSem completeSem registryEx ctxEx fragEx
        = .observed [ClaimObservation.observed Grounded.Status.defeated] ∧
      obsSem semiStableSem registryEx ctxEx fragEx
        = .observed [ClaimObservation.observed Grounded.Status.defeated] := by
  decide

/-- **Agreement at the other pre-existing M4 carrier.** `Linking.symCtx` and
`Linking.symFrag` (`lean/Lara/Examples/Linking.lean:592`, `:595`) are a mutual
rebut between two leaves, observed at the singleton support of `p`. All five
semantics report `contested` there, so this carrier could not have separated
them either.

This is the second half of the claim this module's header makes about why the
existing fixtures were insufficient, and it is here for the same reason as the
five-way form of `obsSem_linking_agrees`: the header would otherwise be
asserting it. `Linking.obs_contested` (`lean/Lara/Examples/Linking.lean:597`)
pins only the grounded reading.

Why the mutual rebut does *not* separate, whereas `sinkCtx`/`sinkFrag` does:
here the observed claim is supported by a node **inside** the two-cycle, and
every semantics accepts it in some extension and rejects it in another, so the
skeptical reading is `contested` under all of them. The sink fixture observes a
node *outside* the cycle which every preferred extension attacks — that is the
asymmetry the separation needs, and it is why adding a sink was necessary rather
than reusing `symPolicy`. -/
theorem obsSem_sym_agrees :
    obsSem groundedSem registryEx symCtx symFrag
        = .observed [ClaimObservation.observed Grounded.Status.contested] ∧
      obsSem preferredSem registryEx symCtx symFrag
        = .observed [ClaimObservation.observed Grounded.Status.contested] ∧
      obsSem stableSem registryEx symCtx symFrag
        = .observed [ClaimObservation.observed Grounded.Status.contested] ∧
      obsSem completeSem registryEx symCtx symFrag
        = .observed [ClaimObservation.observed Grounded.Status.contested] ∧
      obsSem semiStableSem registryEx symCtx symFrag
        = .observed [ClaimObservation.observed Grounded.Status.contested] := by
  decide

/-! ### `gap` uniformity, quantified over the semantics -/

/-- The `gap` link is accepted by the checker. Private: its only role is to
discharge the impossible branch of `obsSem_gap_uniform`'s case split, and it
carries no claim `Linking.obs_gap` (`lean/Lara/Examples/Linking.lean:187`) does
not already carry. -/
private theorem gap_accepted :
    (Check.Unit.checkUnit (linkGamma silentSCtx gapFrag) registryEx
      (linkGround silentSCtx gapFrag) (linkedUnit registryEx silentSCtx gapFrag)).isOk
      = true := by decide

/-- **`gap` is the one observation no choice of semantics can move**, at the
context level, stated the way `Semantics.observe_gap`
(`lean/Lara/Semantics.lean:1244`) and `Invariants.observeSem_of_status_gap`
(`lean/Lara/Invariants/Observation.lean:128`) state it: **universally quantified
over `sem`, with no hypothesis on it**.

The quantifier is not a stylistic choice. Checking three or five instances by
`decide` would be strictly weaker than the theorem this instantiates, and would
not be evidence for it — `observeSem_of_status_gap` holds for semantics nobody
has written down, and a finite check says nothing about those. This is the
distinction `Invariants.observeSem_of_status_gap`'s docstring draws against
`Examples.Semantics.observe_claimNoSupport_uniform`
(`lean/Lara/Examples/Semantics.lean:385`), which does check five instances at
the framework level.

The proof cannot be `decide`, precisely because `sem` is free. It runs the case
split `obsGen` runs: the checker's rejection branch is refuted by
`gap_accepted`, and on the accepted branch the exported claim's grounded status
is extracted from `Linking.obs_gap` (`lean/Lara/Examples/Linking.lean:187`)
through `obs_eq_of_ok` (`lean/Lara/Context/Equivalence.lean:675`) and handed to
`Invariants.observeSem_of_status_gap`, which is where the semantics-independence
actually lives.

The carrier is `Linking.gapFrag` in `Linking.silentSCtx`
(`lean/Lara/Examples/Linking.lean:174`, `:177`): a fragment exporting `s` with
no argument for it, in a context that declares `l3` but does not assert it. What
may be concluded is only the `gap` arm. The companion fixture
`Linking.obs_gap_flipped` (`:190`) shows that a context which *does* assert `s`
flips the observation, and no analogue of this theorem holds there. -/
theorem obsSem_gap_uniform (sem : ExtensionSemantics) :
    obsSem sem registryEx silentSCtx gapFrag
      = .observed [ClaimObservation.observed Grounded.Status.gap] := by
  cases hchk : Check.Unit.checkUnit (linkGamma silentSCtx gapFrag) registryEx
      (linkGround silentSCtx gapFrag) (linkedUnit registryEx silentSCtx gapFrag) with
  | error e =>
      have hok := gap_accepted
      rw [hchk] at hok
      exact Bool.noConfusion hok
  | ok acc =>
      have hstatus : Invariants.status id (Invariants.compileUnit acc) pC
          = Grounded.Status.gap := by
        have h := (obs_eq_of_ok (by decide) hchk).symm.trans Linking.obs_gap
        simpa [gapFrag, fragEx] using h
      rw [obsSem_eq_of_ok sem (by decide) hchk]
      simp only [gapFrag, fragEx, List.map_cons, List.map_nil]
      exact congrArg (fun x => ObservationOf.observed [x])
        (Invariants.observeSem_of_status_gap sem id (Invariants.compileUnit acc) pC hstatus)

/-! ### The two failure arms, at every semantics

Every fixture above lands on `ObservationOf.observed`. The grounded `Observation`
reaches all three arms — `Linking.obs_incompatible_id_clash`
(`lean/Lara/Examples/Linking.lean:115`) and `Linking.obs_rejected_signature`
(`:129`) are the other two — and the semantics-parametric twins are free,
because the link guard and the whole-unit checker both run *before* any
projection is consulted. That is exactly the content of `obsGen_incompatible`
and `obsGen_rejected` (`lean/Lara/Context/Equivalence.lean:603`, `:621`), and it
is why these must be term proofs through `obsSem_incompatible` /
`obsSem_rejected` rather than `decide`: with `sem` free there is nothing for
`decide` to evaluate, and the point is that there is nothing it *needs* to
evaluate. -/

/-- **The incompatible arm, at every semantics.** Both sides declare `l2`, so
the guard fires with `LinkFault.idClash` and the fault is reported without any
carrier being built. The fault value is `Linking.reject_id_clash`'s
(`lean/Lara/Examples/Linking.lean:76`); what is added is that the report is
independent of `sem`. -/
theorem obsSem_incompatible_id_clash (sem : ExtensionSemantics) :
    obsSem sem registryEx ctxEx Linking.clashFrag = .incompatible (.idClash l2) :=
  obsSem_incompatible sem Linking.reject_id_clash

/-- **The rejected arm, at every semantics.** Both sides share a malformed
signature (`Linking.malformedSigma`, `lean/Lara/Examples/Linking.lean:120`, whose
`sorts` list repeats `"Item"`), so the guard passes —
`Linking.malformed_link_guard_ok` (`:127`) — and the whole-unit checker rejects
at the signature stage. As above, the `UnitError` reported is the one
`Linking.obs_rejected_signature` (`:129`) pins; what is added is uniformity in
`sem`. -/
theorem obsSem_rejected_signature (sem : ExtensionSemantics) :
    obsSem sem registryEx Linking.malformedCtx Linking.malformedFrag
      = .rejected (.signature .malformedSigma) :=
  obsSem_rejected sem (by decide) rfl

end Lara.Examples.ContextSemantics
