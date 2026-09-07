/-
# Theory M4, phase F2 — contextual observation at an arbitrary semantics

`Lara.Context.Equivalence` proves contextual representation independence over
the **grounded** labelling: `Lara.Context.obs` (`lean/Lara/Context/Fragment.lean:440`)
reads `Invariants.status` off the linked carrier, and
`backend_replacement_congruence` (`lean/Lara/Context/Equivalence.lean:629`) says
an injective, acceptance-preserving relabel does not change it. M2a had already
made the choice of argumentation semantics a parameter
(`Lara.Semantics.ExtensionSemantics`), so that asymmetry — a parametric
framework layer sitting under a grounded-only context layer — was an artefact of
the order the milestones landed in, not a fact about the theory. This module
closes it.

### What is parameterized, and what deliberately is not

The obvious move is to duplicate `Observation` and `obs` once per semantics-aware
variant and re-run the congruence proof on the copy. That is rejected here. What
is parameterized instead is the **projection**: `obsGen` takes an arbitrary
`g : Invariants.StructuredAF → Atom → α` where `obs` has
`Invariants.status canon`, and `obsGen_congr` proves the congruence once, for
every `g` at once. `obsSem` is then a *definition*, not a second development:

    obsSem sem reg C F  =  obsGen (Invariants.observeSem sem canon) reg C F

and every semantics-parametric congruence below is a one-line instantiation of
`obsGen_congr`. The reason this works is stated in `obsGen_congr`'s docstring and
is worth naming here too: every M4 congruence routes through
`compileUnit_link_relabel` (`lean/Lara/Context/Equivalence.lean:586`), which
concludes that the two links present the *same* `StructuredAF`. Once the carrier
is literally equal, nothing that reads a function off it can tell the two sides
apart, whatever that function is.

### Why `liftObservation` still exists

Parameterizing the projection removed the need for an embedding on the *proof*
side — `obsGen_congr` never mentions one. It did not remove it on the
**regression** side. `obsSem groundedSem reg C F` lives in
`Outcome ClaimObservation` while `obs reg C F` lives in `Observation`, and those
are different types, so the statement "the grounded instance is the old
observation" cannot be an equation between them as they stand. `liftObservation`
is the injection that makes the two comparable, `obsSem_grounded` is the
coincidence, and `ctxEquivSem_grounded_iff` is the relational form, which needs
`liftObservation_inj` for its forward direction. Recording this honestly: the
embedding is bookkeeping forced by the two result types, and it carries no
mathematical content beyond the injectivity of `List.map` over a constructor.

### The generalization lattice

    Semantics.observe sem  (M2a, framework level: an AF and a Grounded.Claim)
              |
              |  read off an erased carrier (Invariants.eraseAF)
              v
    Invariants.status canon        ---generalized by--->  Invariants.observeSem sem canon
    (grounded, Lara/Invariants.lean:105)                  (Lara/Invariants/Observation.lean:67)
              |                                                   |
              |  read off the *linked* carrier of a context+fragment
              v                                                   v
    Lara.Context.obs               ---generalized by--->  Lara.Context.obsSem
    (Lara/Context/Fragment.lean:440)                      (this module)
              |                                                   |
              |  quantify over all contexts
              v                                                   v
    Lara.Context.CtxEquiv          ---generalized by--->  Lara.Context.CtxEquivSem
    (Lara/Context/Equivalence.lean:516)                   (this module)

Each `--->` arrow is witnessed by a theorem here or in the module named beside
it: `Invariants.observeSem_grounded`, `obsSem_grounded`, and
`ctxEquivSem_grounded_iff` respectively. The arrows go one way only. Nothing
below claims that a fact about the grounded instance lifts to another semantics,
and `ctxEquivSem_grounded_iff` in particular must not be read that way; see its
docstring.

This module is purely additive. It changes no existing declaration, and the only
edit it makes outside itself is one import line in `lean/Lara.lean`.
-/

import Lara.Context.Equivalence
import Lara.Invariants.Observation

set_option autoImplicit false

namespace Lara.Context

open Lara.Support Lara.Attack Lara.Compile Lara.Check Lara.Erase Lara.Semantics

/-! ### The generic outcome

`Lara.Context.Observation` (`lean/Lara/Context/Fragment.lean:428`) is
`Outcome Grounded.Status` in all but name: the same three arms, with the
observed arm's payload fixed. It is left exactly as it is — no existing
declaration changes — and `Outcome` is introduced beside it so the observed
payload can vary. `liftObservation` below relates the two at the one place a
relation is needed. -/

/-- **The externally visible result of placing a fragment in a context, with the
observed payload left open.** The two failure arms carry precisely what
`Observation` carries; only the third is generic.

The arms are kept distinct for the same reason `Observation`'s are: an
incompatible interface and a rejected whole unit are different events, and
collapsing either into "no observations" would make a fragment that cannot be
linked indistinguishable from one that links and exports nothing. -/
inductive Outcome (α : Type) where
  /-- the link guard fired: the interfaces are incompatible -/
  | incompatible : LinkFault → Outcome α
  /-- the link is compatible but the merged unit failed the whole-unit checker -/
  | rejected : Check.Unit.UnitError → Outcome α
  /-- the accepted link's exported conclusions, projected by the caller's `g` -/
  | observed : List α → Outcome α
deriving DecidableEq

/-- **The observation of a link through an arbitrary projection.** The control
flow is `Lara.Context.obs`'s, verbatim (`lean/Lara/Context/Fragment.lean:440`):
guard first, then the whole-unit checker on the linked unit, then — and only
then — read the exported conclusions off the M1 carrier of the accepted unit.
The single difference is that `obs` hard-codes `Invariants.status canon` where
this takes `g`.

`g` receives the *linked* carrier, not the fragment's own: an open fragment has
no framework of its own (D10), and `fragmentCarrier`
(`lean/Lara/Context/Fragment.lean:407`) is the fragment-relative substitute.
What is projected here is always the carrier of the context-plus-fragment unit,
which is what makes the result an *observation* in the contextual sense. -/
def obsGen {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} (reg : BackendRegistry canon)
    (C : Context) (F : Fragment) : Outcome α :=
  match linkFault C F with
  | some fault => .incompatible fault
  | none =>
      match Check.Unit.checkUnit (linkGamma C F) reg (linkGround C F)
          (linkedUnit reg C F) with
      | .ok accepted =>
          .observed (F.exports.map (fun p => g (Invariants.compileUnit accepted) p))
      | .error error => .rejected error

/-- **The incompatible arm is projection-independent by construction.** If the
link guard fires, `obsGen` reports the fault for *every* `g` — the projection is
never consulted, because `linkFault` is matched before the checker runs and long
before any carrier exists to project.

This is worth stating as a theorem rather than leaving to `decide` at each
fixture. `decide` settles the arm for one concrete semantics at a time; this
settles it uniformly, which is what a witness quantified over all of
`ExtensionSemantics` needs (via `obsSem_incompatible`). Nothing here says which
links fault — that is `linkFault`'s business, and this theorem is indifferent to
it. -/
theorem obsGen_incompatible {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} {reg : BackendRegistry canon}
    {C : Context} {F : Fragment} {fault : LinkFault}
    (h : linkFault C F = some fault) :
    obsGen g reg C F = .incompatible fault := by
  simp only [obsGen, h]

/-- **The rejected arm is projection-independent by construction.** A compatible
link whose merged unit the whole-unit checker rejects reports that `UnitError`
for every `g`, for the same structural reason as `obsGen_incompatible`:
`Check.Unit.checkUnit` runs on the linked unit before `Invariants.compileUnit`
is ever applied, so no projection can influence — or observe — the rejection.

The `hlink` hypothesis is `linkFault C F = none` rather than `linkOk C F = true`
because that is the form the definitional match needs; `obsGen_eq_of_ok` takes
the `linkOk` spelling instead and converts, exactly as `obs_eq_of_ok` does
(`lean/Lara/Context/Equivalence.lean:547`). -/
theorem obsGen_rejected {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} {reg : BackendRegistry canon}
    {C : Context} {F : Fragment} {error : Check.Unit.UnitError}
    (hlink : linkFault C F = none)
    (h : Check.Unit.checkUnit (linkGamma C F) reg (linkGround C F)
      (linkedUnit reg C F) = .error error) :
    obsGen g reg C F = .rejected error := by
  simp only [obsGen, hlink, h]

/-- **An accepted link observes through its carrier**, generically. This is
`obs_eq_of_ok` (`lean/Lara/Context/Equivalence.lean:547`) with the projection
left open, and it is proved the same way: `linkOk` is `Option.isNone` of
`linkFault`, so the guard hypothesis rewrites into the shape the match wants,
and the two matches then reduce.

Note the accepted unit `acc` appears in the conclusion. That is not incidental
bookkeeping: the whole-unit checker is what produces the `CheckedUnit` whose node
cache `Invariants.compileUnit` reads, so there is no way to state the observed
arm without naming it. Every congruence below works by producing an `acc` on
each side and then proving the two carriers equal. -/
theorem obsGen_eq_of_ok {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} {reg : BackendRegistry canon}
    {C : Context} {F : Fragment}
    {acc : Lara.Unit.CheckedUnit canon (linkGamma C F) (certOkOf reg)}
    (hlink : linkOk C F = true)
    (h : Check.Unit.checkUnit (linkGamma C F) reg (linkGround C F)
      (linkedUnit reg C F) = .ok acc) :
    obsGen g reg C F
      = .observed (F.exports.map (fun p => g (Invariants.compileUnit acc) p)) := by
  have hfault : linkFault C F = none := by
    simpa only [linkOk, Option.isNone_iff_eq_none] using hlink
  simp only [obsGen, hfault, h]

/-- **Pointwise-equal projections observe identically.** `obsGen` uses `g` only
by applying it, so agreement at every carrier and every atom is enough; there is
no extensionality side condition hiding in the definition.

The intended use is to replace a projection by a definitionally different but
pointwise-equal one — for instance to move between `Invariants.observeSem sem
canon` and a specialization of it — without re-running the guard/checker case
analysis. It is *not* a congruence in the M4 sense: both sides here observe the
same fragment in the same context under the same registry. -/
theorem obsGen_ext {α : Type} {g₁ g₂ : Invariants.StructuredAF → Atom → α}
    {canon : String → String} {reg : BackendRegistry canon}
    {C : Context} {F : Fragment}
    (h : ∀ G p, g₁ G p = g₂ G p) :
    obsGen g₁ reg C F = obsGen g₂ reg C F := by
  have hg : g₁ = g₂ := funext fun G => funext fun p => h G p
  rw [hg]

/-! ### The headline, generically -/

section Headline

variable {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
  {f : Assurance → Assurance} {C : Context} {F : Fragment}

/-- **Contextual representation independence, for every projection at once.**

An injective, acceptance-preserving relabel of a fragment's certificates is
unobservable in every admissible context whose own assurances the relabel fixes
— and *whatever* is read off the resulting carrier. This is
`backend_replacement_congruence` (`lean/Lara/Context/Equivalence.lean:629`) with
`Invariants.status canon` replaced by an arbitrary `g`, and the proof is that
proof unchanged.

**Why the generalization is free.** The argument produces an accepted link on
each side and then appeals to `compileUnit_link_relabel`
(`lean/Lara/Context/Equivalence.lean:586`), whose conclusion is
`Invariants.compileUnit acc₂ = Invariants.compileUnit acc₁` — an equation
between carriers, not a pointwise agreement between them:

      reg₁, F                                  reg₂, mapAssurFrag f F
         |                                              |
         | linkedUnit reg₁ C F                          | linkedUnit reg₂ C (mapAssurFrag f F)
         v                                              v
      checkUnit ... = .ok acc₁                  checkUnit ... = .ok acc₂
         |                                              |
         | Invariants.compileUnit                       | Invariants.compileUnit
         \                                              /
          \____________ compileUnit_link_relabel ______/
                              |
                              v
                    one carrier  G : StructuredAF
                              |
                              |  F.exports.map (fun p => g G p)   -- any g whatsoever
                              v
                        Outcome.observed …

Once the two sides meet at a single `G`, the projection hanging off it is
applied to the same argument on both branches, so it cannot distinguish them.

**Why there is no `AttackExtensional` hypothesis, and why there must not be.**
`Lara.Observation.observe_congr` (`lean/Lara/Observation.lean:406`) does assume
`AttackExtensional sem.spec`, but it is solving a different problem: it moves an
observation between two *distinct* frameworks that merely agree pointwise on the
carrier, and extensionality is what licenses concluding that the extensions
agree. Here the frameworks are equal, so no such licence is needed. A generic
statement that assumed `AttackExtensional` anyway would be strictly weaker than
its grounded ancestor `backend_replacement_congruence`, which assumes nothing of
the kind — and would not deserve to be called its generalization.

The admissibility hypothesis is inherited and is not removable for the reason
`backend_replacement_congruence` records: `obsGen` reports a checker rejection
separately from an observed list, and a forward-only acceptance hypothesis lets
`reg₂` accept what `reg₁` rejects. -/
theorem obsGen_congr {α : Type} (g : Invariants.StructuredAF → Atom → α)
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F) (hfix : FixesContext f C) :
    obsGen g reg₁ C F = obsGen g reg₂ C (mapAssurFrag f F) := by
  obtain ⟨acc₁, h₁⟩ := exists_accepted_of_admissible hadm
  obtain ⟨acc₂, h₂⟩ := exists_accepted_relabel hf hpres hadm hfix h₁
  rw [obsGen_eq_of_ok g hadm.guard h₁,
    obsGen_eq_of_ok g (C := C) (F := mapAssurFrag f F)
      (by rw [linkOk_mapAssurFrag]; exact hadm.guard)
      (by rw [linkGround_mapAssurFrag]; exact h₂)]
  refine congrArg Outcome.observed ?_
  rw [mapAssurFrag_exports]
  exact congrArg (fun G => F.exports.map (fun p => g G p))
    (compileUnit_link_relabel hf hpres hadm hfix h₁ h₂).symm

end Headline

/-! ### The semantics-parametric instance

Everything above is about an arbitrary projection. This is the projection the
milestone exists for: `Invariants.observeSem sem canon`
(`lean/Lara/Invariants/Observation.lean:67`), which runs `Semantics.observe` at
the supplied `sem` on the erased carrier. -/

/-- **The observation of a link at an arbitrary extension semantics.** The
result payload is `ClaimObservation`, not `Grounded.Status`, and the widening is
forced rather than stylistic: a semantics need not have any extension on a given
framework, and `Semantics.observe` answers that case with
`ClaimObservation.noExtension` instead of fabricating a status. See
`Invariants.observeSem`'s docstring for the witness
(`Examples.Semantics.stableSem_enumerate_threeCycle`).

`sem` is an explicit first argument here and on every declaration below that
mentions it. Making it implicit would be inferable in principle from a
fully-elaborated goal, but every call site states the semantics it means, so an
implicit binder would only add `(sem := …)` noise. -/
def obsSem (sem : ExtensionSemantics) {canon : String → String}
    (reg : BackendRegistry canon) (C : Context) (F : Fragment) :
    Outcome ClaimObservation :=
  obsGen (Invariants.observeSem sem canon) reg C F

/-- `obsGen_eq_of_ok` at the semantics projection: an accepted link observes
every exported conclusion through `Invariants.observeSem sem canon` applied to
the linked carrier. -/
theorem obsSem_eq_of_ok (sem : ExtensionSemantics) {canon : String → String}
    {reg : BackendRegistry canon} {C : Context} {F : Fragment}
    {acc : Lara.Unit.CheckedUnit canon (linkGamma C F) (certOkOf reg)}
    (hlink : linkOk C F = true)
    (h : Check.Unit.checkUnit (linkGamma C F) reg (linkGround C F)
      (linkedUnit reg C F) = .ok acc) :
    obsSem sem reg C F
      = .observed (F.exports.map
          (fun p => Invariants.observeSem sem canon (Invariants.compileUnit acc) p)) :=
  obsGen_eq_of_ok (Invariants.observeSem sem canon) hlink h

/-- A faulting link reports its `LinkFault` at every semantics. Because `sem` is
universally quantified in the statement, this witnesses the incompatible arm for
all of `ExtensionSemantics` at once — which no amount of `decide` at concrete
instances can do. -/
theorem obsSem_incompatible (sem : ExtensionSemantics) {canon : String → String}
    {reg : BackendRegistry canon} {C : Context} {F : Fragment} {fault : LinkFault}
    (h : linkFault C F = some fault) :
    obsSem sem reg C F = .incompatible fault :=
  obsGen_incompatible (Invariants.observeSem sem canon) h

/-- A compatible link whose merged unit is rejected reports its `UnitError` at
every semantics, for the same reason as `obsSem_incompatible`: the checker runs
before any carrier exists to observe. -/
theorem obsSem_rejected (sem : ExtensionSemantics) {canon : String → String}
    {reg : BackendRegistry canon} {C : Context} {F : Fragment}
    {error : Check.Unit.UnitError}
    (hlink : linkFault C F = none)
    (h : Check.Unit.checkUnit (linkGamma C F) reg (linkGround C F)
      (linkedUnit reg C F) = .error error) :
    obsSem sem reg C F = .rejected error :=
  obsGen_rejected (Invariants.observeSem sem canon) hlink h

/-! ### The grounded regression -/

/-- **The M4 observation, embedded into the generic one.** The two failure arms
transport unchanged; the observed arm wraps each status in
`ClaimObservation.observed`, which is exactly what `Invariants.observeSem_grounded`
produces (`lean/Lara/Invariants/Observation.lean:90`).

This exists only to make `obs` and `obsSem groundedSem` comparable: they have
different result types, so the coincidence cannot be stated as an equation
without it. It is not part of the congruence argument, which never leaves a
single result type. -/
def liftObservation : Observation → Outcome ClaimObservation
  | .incompatible fault => .incompatible fault
  | .rejected error => .rejected error
  | .observed statuses => .observed (statuses.map ClaimObservation.observed)

/-- `List.map` over a constructor is injective. Proved here by induction rather
than cited: this toolchain carries no Mathlib, and the core `List` map-injectivity
API is not stable enough across releases to depend on for a one-off. -/
private theorem map_observed_inj : ∀ {l₁ l₂ : List Grounded.Status},
    l₁.map ClaimObservation.observed = l₂.map ClaimObservation.observed → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ h; cases l₂ <;> simp_all
  | cons a l ih =>
      intro l₂ h
      cases l₂ with
      | nil => simp at h
      | cons b l₂ =>
          simp only [List.map_cons, List.cons.injEq,
            ClaimObservation.observed.injEq] at h
          rw [h.1, ih h.2]

/-- **The embedding loses nothing.** Needed for the forward direction of
`ctxEquivSem_grounded_iff`: two fragments whose *lifted* observations agree in
every context already had agreeing observations there. -/
theorem liftObservation_inj : Function.Injective liftObservation := by
  intro o₁ o₂ h
  cases o₁ with
  | incompatible a => cases o₂ <;> simp_all [liftObservation]
  | rejected a => cases o₂ <;> simp_all [liftObservation]
  | observed l₁ =>
      cases o₂ with
      | incompatible b => simp only [liftObservation] at h; exact absurd h (by simp)
      | rejected b => simp only [liftObservation] at h; exact absurd h (by simp)
      | observed l₂ =>
          simp only [liftObservation, Outcome.observed.injEq] at h
          exact congrArg Observation.observed (map_observed_inj h)

/-- The observed arm of the regression, isolated so `obsSem_grounded` needs no
list surgery in the middle of a case split. -/
private theorem map_observeSem_grounded {canon : String → String}
    (G : Invariants.StructuredAF) :
    ∀ l : List Atom,
      l.map (fun p => Invariants.observeSem groundedSem canon G p)
        = (l.map (fun p => Invariants.status canon G p)).map ClaimObservation.observed
  | [] => rfl
  | p :: ps => by
      simp only [List.map_cons]
      rw [Invariants.observeSem_grounded, map_observeSem_grounded G ps]

/-- **The grounded instance is the frozen M4 observation.** At `groundedSem`,
`obsSem` is `obs` composed with `liftObservation` — in every context, for every
registry, with **no hypothesis**.

This is what makes the parametric layer a *generalization* rather than a
replacement, and it is the reason no existing file had to change. Every fixture
in `Lara.Examples.Linking` computes `obs`, and every one of them keeps its
meaning verbatim: reading the same link through `obsSem groundedSem` gives the
lifted answer and nothing else.

There is no hypothesis because `Invariants.observeSem_grounded` needs none. That
lemma discharges `Semantics.observe_grounded`'s `F.args.Nodup` obligation
outright against `Invariants.eraseAF`'s definitional `List.range` carrier, so the
obligation never reaches a statement at this level either. -/
theorem obsSem_grounded {canon : String → String} (reg : BackendRegistry canon)
    (C : Context) (F : Fragment) :
    obsSem groundedSem reg C F = liftObservation (obs reg C F) := by
  simp only [obsSem, obsGen, obs]
  cases hfault : linkFault C F with
  | some fault => rfl
  | none =>
      cases hchk : Check.Unit.checkUnit (linkGamma C F) reg (linkGround C F)
          (linkedUnit reg C F) with
      | error e => rfl
      | ok acc =>
          simp only [liftObservation]
          exact congrArg Outcome.observed
            (map_observeSem_grounded (Invariants.compileUnit acc) F.exports)

/-! ### Contextual equivalence at an arbitrary semantics -/

/-- **Contextual equivalence of two fragments under one registry, observed at
`sem`.** The generic companion of `CtxEquiv`
(`lean/Lara/Context/Equivalence.lean:516`): every context must produce the same
detailed outcome, with incompatible links, checker rejections and observed
`ClaimObservation` lists all remaining distinct.

As with `CtxEquiv`, a logical relation characterizing this is Part B, not this
module; nothing here is a full-abstraction result. -/
def CtxEquivSem (sem : ExtensionSemantics) {canon : String → String}
    (reg : BackendRegistry canon) (F₁ F₂ : Fragment) : Prop :=
  ∀ C : Context, obsSem sem reg C F₁ = obsSem sem reg C F₂

/-- **The grounded instance of generic contextual equivalence is M4's, on the
nose** — both directions. The forward direction cancels the embedding with
`liftObservation_inj`; the backward direction rewrites through
`obsSem_grounded`.

**Read the scope narrowly.** This says that at `groundedSem` the two relations
coincide, and therefore that no M4 statement about `CtxEquiv` is weakened,
strengthened, or otherwise disturbed by this module's existence. It says
**nothing** about any other semantics. In particular it does not license
inferring `CtxEquivSem sem reg F₁ F₂` from `CtxEquiv reg F₁ F₂` for a general
`sem`, and must not be cited for that: the grounded and non-grounded readings of
a framework genuinely differ on the `justified`/`defeated`/`contested` arms
(`Lara.Semantics.observe_twoCycle_grounded_ne_preferred`), so such an inference
would need an argument, and no such argument is made here. `gap` is the one
status that does transport, by `Invariants.observeSem_of_status_gap`
(`lean/Lara/Invariants/Observation.lean:128`), and that is a statement about a
single claim, not about equivalence of fragments. -/
theorem ctxEquivSem_grounded_iff {canon : String → String}
    (reg : BackendRegistry canon) (F₁ F₂ : Fragment) :
    CtxEquivSem groundedSem reg F₁ F₂ ↔ CtxEquiv reg F₁ F₂ := by
  constructor
  · intro h C
    refine liftObservation_inj ?_
    rw [← obsSem_grounded reg C F₁, ← obsSem_grounded reg C F₂]
    exact h C
  · intro h C
    rw [obsSem_grounded reg C F₁, obsSem_grounded reg C F₂, h C]

/-! ### The four congruences, at an arbitrary semantics

Each is an instantiation of `obsGen_congr`. They are stated separately rather
than left to callers because the names are the ones the grounded development
already uses, and a reader looking for "the semantics-parametric version of
`backend_replacement_congruence`" should find it by name. -/

section HeadlineSem

variable {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
  {f : Assurance → Assurance} {C : Context} {F : Fragment}

/-- **Contextual representation independence at an arbitrary semantics.** The
semantics-parametric form of `backend_replacement_congruence`
(`lean/Lara/Context/Equivalence.lean:629`), and the milestone's headline.

Its entire proof is `obsGen_congr` at `g := Invariants.observeSem sem canon`.
That brevity is the point: the congruence was never a fact about the grounded
labelling, and this makes that visible rather than asserting it. Read
`obsGen_congr`'s docstring for why no `AttackExtensional` hypothesis appears and
why admissibility cannot be dropped.

Like its grounded ancestor this is **not** parametricity (no relational
quantification over related backends — issue #215) and not full abstraction (no
logical relation — Part B). -/
theorem backend_replacement_congruence_sem (sem : ExtensionSemantics)
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F) (hfix : FixesContext f C) :
    obsSem sem reg₁ C F = obsSem sem reg₂ C (mapAssurFrag f F) :=
  obsGen_congr _ hf hpres hadm hfix

/-- **The acceptance-profile generalization (D6), at an arbitrary semantics.**
No relabel and no injectivity: if every assurance the first registry accepts the
second accepts too, the *same* fragment reads the same way in every admissible
context, under every extension semantics. The semantics-parametric form of
`registry_swap_congruence` (`lean/Lara/Context/Equivalence.lean:686`), obtained
the same way — instantiate the congruence at `f := id` and cancel `mapAssurFrag`.

The hypothesis `hpres` is stated **globally**, over every rule and every
assurance, rather than over `F`'s certificate occurrences. That is inherited
from `hasSupport_mapAssur`, which carries the derivations across and quantifies
globally. A display of this result must therefore say "agrees globally", not
"agrees on the fragment's occurrences" — the two are different hypotheses and
the weaker one is not what is proved here. -/
theorem registry_swap_congruence_sem (sem : ExtensionSemantics)
    (hpres : ∀ (r : Rule) (As : List Atom) (A : Atom) (α : Assurance),
      AssuranceOk (certOkOf reg₁) r As A α → AssuranceOk (certOkOf reg₂) r As A α)
    (hadm : Admissible reg₁ C F) :
    obsSem sem reg₁ C F = obsSem sem reg₂ C F := by
  have h := backend_replacement_congruence_sem (f := id) sem (fun _ _ h => h) hpres hadm
    (fixesContext_id C)
  rwa [mapAssurFrag_id] at h

end HeadlineSem

section ClosureSem

variable {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
  {f : Assurance → Assurance}

/-- **Congruence at an arbitrary semantics is stable under embedding into a
larger context.** The semantics-parametric form of
`backend_replacement_congruence_composed`
(`lean/Lara/Context/Equivalence.lean:778`), with the same reading: the
quantifier over contexts already ranged over composites, since `composedContext`
produces a `Context`; what composition buys is that the quantifier is *closed*,
and `fixesContext_composed` (`lean/Lara/Context/Equivalence.lean:714`) is what
discharges the composite's `FixesContext` obligation from the two halves.

The composite's `Admissible` hypothesis is assumed here rather than assembled;
`admissible_composed` (`lean/Lara/Context/Equivalence.lean:734`) is the lemma
that builds it from the halves plus their cross-coverage, and it applies to this
statement unchanged because admissibility mentions no semantics. -/
theorem backend_replacement_congruence_composed_sem (sem : ExtensionSemantics)
    {C D : Context} {F : Fragment}
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ (composedContext C D) F)
    (hC : FixesContext f C) (hD : FixesContext f D) :
    obsSem sem reg₁ (composedContext C D) F
      = obsSem sem reg₂ (composedContext C D) (mapAssurFrag f F) :=
  backend_replacement_congruence_sem sem hf hpres hadm (fixesContext_composed hC hD)

/-- **Result 9's whole-program statement, at an arbitrary semantics.**

Its grounded twin `whole_program_replacement`
(`lean/Lara/Context/Equivalence.lean:794`) exists to record that it *cites*
`Erase.backend_replacement` (`lean/Lara/Erase.lean:259`) rather than re-deriving
it. The analogous fact here is slightly different and worth stating precisely:
there is no generic ancestor to cite, because `Erase.backend_replacement` is
grounded-specific — its conclusion is an equation between `Grounded.statusC`
values. What this theorem does instead is make the *same one-rewrite appeal*
that `Erase.backend_replacement` itself makes. That proof is literally
`rw [checkedAF_relabel hf hargs hatts]` (`lean/Lara/Erase.lean:267`), and so is
this one.

So this is **not** a re-derivation of result 9 and claims no new content. Its
value is that it makes visible *why* result 9 is independent of the choice of
semantics: the two programs compile to the same `Grounded.AF`
(`Erase.checkedAF_relabel`, `lean/Lara/Erase.lean:243`), and any function of a
framework — `Grounded.statusC`, `Semantics.observe sem`, or anything else —
agrees on equal frameworks. Semantics-independence here is a fact about
compilation, not a fact about the grounded labelling that would have to be
re-proved once per semantics.

**Why it sits in `namespace Lara.Context` while mentioning no `Context`,
`Fragment` or `obsSem`.** For the same reason `whole_program_replacement` does:
it is placed beside the docstring it must be read against. Read alone it looks
like a stray corollary of `Erase.checkedAF_relabel`; read beside its grounded
twin it is the record that the whole-program instance needed no generalization
work. -/
theorem whole_program_replacement_sem (sem : ExtensionSemantics)
    {Pi : RuleId → Option Rule}
    {Gamma : LeafId → Option Atom}
    {CertOk₁ CertOk₂ : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {dp : DefeatPolicy}
    {P₁ : CheckedProgram canon Pi Gamma CertOk₁ dp}
    {P₂ : CheckedProgram canon Pi Gamma CertOk₂ dp}
    (hf : Function.Injective f)
    (hargs : P₂.args = P₁.args.map (mapAssur f))
    (hatts : P₂.atts = P₁.atts.map (mapAssurAtt f))
    (c : Grounded.Claim) :
    Semantics.observe sem (Compile.checkedAF P₁) c
      = Semantics.observe sem (Compile.checkedAF P₂) c := by
  rw [Erase.checkedAF_relabel hf hargs hatts]

end ClosureSem

end Lara.Context
