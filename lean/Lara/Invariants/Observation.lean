/-
# The carrier observation at an arbitrary extension semantics

`Lara.Invariants.status` computes a claim's four-state answer on the M0 carrier
by fixing the grounded semantics: it is `Grounded.statusC` applied to the erased
framework. This module adds the semantics-parametric companion, `observeSem`,
which runs `Semantics.observe` on the same erased framework and the same carrier
claim, at an arbitrary `Semantics.ExtensionSemantics`.

### Why this is a separate module

Nothing here is a different subject from `Lara.Invariants`; the namespace is
shared, exactly as `Lara.Semantics.Sublists` shares `Lara.Semantics` and
`Lara.Invariants.Merge` shares `Lara.Invariants`. The single reason for the
split is the import: this is the one part of the carrier layer that needs
`Lara.Semantics`, and the M0 invariant record has no business acquiring that
dependency. `Lara.Invariants` is the frozen answer to "what object does
compilation produce?", and that answer must not become contingent on the
extension-semantics development — a downstream reader who only wants
`StructuredAF`, `eraseAF`, and `CompilerInvariant` should not have to elaborate
the semantics zoo to get them. The import direction is one-way and acyclic:
`Lara.Semantics` imports only `Lara.Grounded` and `Lara.Semantics.Sublists`,
neither of which reaches `Lara.Invariants`.

### What is here

Four declarations: the definition `observeSem`, its grounded specialization
`observeSem_grounded` (which recovers `status` exactly, with no hypothesis), and
the two `gap` facts — `observeSem_gap` from empty carrier support, and
`observeSem_of_status_gap` from the grounded status itself. Nothing in this
module says anything about the *other* three statuses, which genuinely vary with
the choice of semantics; see `Semantics.observe_gap`'s docstring for the
witnesses.
-/

import Lara.Invariants
import Lara.Semantics

set_option autoImplicit false

namespace Lara.Invariants

open Lara.Semantics

/-! ### The semantics-parametric carrier observation -/

/-- **The carrier observation at an arbitrary extension semantics.** Erase the
carrier to a naked Dung framework, read off the complete-support claim for `p`,
and hand both to `Semantics.observe` at the supplied `sem`.

The result type is `ClaimObservation`, *not* `Grounded.Status`, and that widening
is forced rather than stylistic. A semantics need not have any extension on a
given framework at all: `Examples.Semantics.stableSem_enumerate_threeCycle`
shows `stableSem` enumerating nothing on the bare three-cycle. On an empty
enumeration every `List.all` guard inside `observe` is vacuously `true`, so a
function that insisted on returning a `Status` would have to report the same
claim as both skeptically justified and skeptically defeated. `Semantics.observe`
answers that case with the `ClaimObservation.noExtension` constructor instead of
fabricating a status, and `observeSem` inherits that discipline.

So this **generalizes** `status`; it does not retype it. `observeSem_grounded`
below is the precise sense in which the old function is recovered: at
`groundedSem` the `noExtension` arm provably cannot fire, and what comes back is
`ClaimObservation.observed (status canon F p)` — the same four-state answer,
wrapped. Anything proved about `observeSem` at a general `sem` may therefore be
read as a statement about `status` only after that specialization is applied. -/
def observeSem (sem : ExtensionSemantics) (canon : String → String)
    (F : StructuredAF) (p : Atom) : ClaimObservation :=
  Semantics.observe sem (eraseAF F) (claim canon F p)

/-- **The grounded instance is the frozen carrier status.** At `groundedSem`,
`observeSem` returns exactly `Lara.Invariants.status`, wrapped in the `observed`
constructor. This is what licenses reading the parametric layer as a
generalization of M0's observation rather than a competing definition of it.

Note there is **no hypothesis**. `Semantics.observe_grounded` binds
`F.args.Nodup`, because it needs `groundedSem_singleton` to know the grounded
enumeration is a one-element list. Here the framework is `eraseAF F`, whose
carrier is `List.range F.size` *by definition* (`Lara.Invariants.eraseAF`), so
the obligation is discharged outright by `List.nodup_range` and never reaches the
statement. That is a property of the frozen erasure, not a convenience: every
carrier this development observes is positional, so duplicate arguments are not
representable.

The same discharge is made three times in `Lara.Observation`, for the same
reason and against the same definitional carrier — see the note at
`lean/Lara/Observation.lean:545` explaining that the `List.nodup_range` appeals
lean on `Compile.toAF`'s `List.range` carrier, and the uses at `:666` (the
docstring of `srcObservation_iff_checked`), `:677`, and `:721`. -/
theorem observeSem_grounded (canon : String → String) (F : StructuredAF) (p : Atom) :
    observeSem groundedSem canon F p = ClaimObservation.observed (status canon F p) :=
  Semantics.observe_grounded (F := eraseAF F) List.nodup_range (claim canon F p)

/-- **`gap` at the carrier, from empty support.** `Semantics.observe_gap`
transported to `StructuredAF`: a claim with no supporting node is observed `gap`
under every semantics.

The hypothesis is stated as `support canon F p = []` rather than
`(claim canon F p).support = []` because `Lara.Invariants.claim` builds its
record with `support := support canon F p`, so the two are definitionally the
same proposition and the carrier-level spelling is the one callers have.

What may be concluded is only the `gap` arm. This says nothing about which
claims are unsupported — that is a question about `support`, decided by the node
labelling and the canonicalizer, and this theorem is indifferent to both. -/
theorem observeSem_gap (sem : ExtensionSemantics) (canon : String → String)
    (F : StructuredAF) (p : Atom) (hs : support canon F p = []) :
    observeSem sem canon F p = ClaimObservation.observed Grounded.Status.gap :=
  Semantics.observe_gap sem (eraseAF F) (claim canon F p) hs

/-- **`gap` is the one status no choice of semantics can change**, stated at the
carrier. If the frozen grounded status of `p` is `gap`, then *every*
`ExtensionSemantics` observes `gap` on the same carrier — with no hypothesis on
`sem`, on `F`, or on the enumeration.

The bridge is `Grounded.statusC_gap_iff`, which makes grounded `gap` equivalent
to empty complete support; empty support is then semantics-independent by
`observeSem_gap`. This is exactly why the `gap` guard is tested first inside
`Semantics.observe`: it is decided from the claim alone, before any extension
data is read.

Read the scope narrowly, as `Semantics.observe_gap` instructs. The other three
statuses are witnessed to vary with the semantics (`observe_twoCycle_grounded_ne_preferred`,
`observe_twoCycleSink_grounded_ne_preferred`), so no analogue of this theorem
exists for them. Its intended use is to state gap-uniformity as a theorem
quantified over `sem`, rather than checking it at a finite list of instances the
way `Examples.Semantics.observe_claimNoSupport_uniform` does. -/
theorem observeSem_of_status_gap (sem : ExtensionSemantics) (canon : String → String)
    (F : StructuredAF) (p : Atom) (h : status canon F p = Grounded.Status.gap) :
    observeSem sem canon F p = ClaimObservation.observed Grounded.Status.gap :=
  observeSem_gap sem canon F p
    ((Grounded.statusC_gap_iff (eraseAF F) (claim canon F p)).mp h)

end Lara.Invariants
