# M4 Part B: G0 interface spike (#305)

**Exit decision: re-descoped, 2026-09-09.** The candidate below fails a
same-context copying test: two fragments with matching occurrence profiles
produce different accepted observations. Retaining exact identities avoids
that particular failure, but this spike does not establish a useful independent
logical relation or a characterization of contextual equivalence. G1–G4 are
not entered. No soundness or completeness theorem is added.

This is the written exit of the G0 interface spike.
The M4 contextual-adequacy work closed on September 3,
2026, with Part B **descoped, not deferred**. Its
maintainer close-out
and [durable record, §7](theory-m4-contextual-adequacy.md#7-part-b-descoped-2026-09-03)
authorize reconsideration through a fresh issue and an interface spike.
The relational-parametricity and generic-semantics contextual-equivalence
work has since closed with its
results landed. That trigger justifies running G0; it does not establish the
interface or authorize the theorem phases. The paper's claims and commit IDs
are reported in #305; this spike checks the implementation at `7d0f738`, not
the separate paper checkout.

## Which equivalence would the relation explain?

The existing `CtxEquiv reg F₁ F₂` in
[`Context/Equivalence.lean`](../lean/Lara/Context/Equivalence.lean) means
`∀ C, obs reg C F₁ = obs reg C F₂`. It uses one fixed registry and the same
context on both sides. Its observations include the exact `LinkFault`, the
exact `UnitError`, or the ordered list of grounded export statuses. A relation
on successful attack graphs alone cannot characterize that whole definition.
In particular, two rejected links need not have equal observations.

For the first soundness test, give the candidate its most favorable domain:
fix `canon`, the registry, signature and policy; require equal `gammaFrag`,
imports, ground and ordered exports; compare statuses only when the same
context is admissible for both fragments. This is a proposed restricted target,
not a change to `CtxEquiv`. Failure on an accepted pair already rules out a
characterization of the unrestricted relation.

The G0 reading is grounded `obs`. #216 supplies `obsSem` for other extension
semantics and `obsGen` for an arbitrary carrier projection. Neither makes those
readings interchangeable. For example, an arbitrary projection can read node
count, while grounded export statuses need not reveal it. No claim here ranges
over every projection, possible-world observation, or the additive term-hole
contexts of #217.

## The candidate tested

Call the proposed relation `R_occ` in this record only; it is not a Lean API or
a G1 freeze. For each common import environment in which both sides' support
material checks, compare the following finite profiles by a bijection:

| Part of the profile | What the bijection preserves |
|---|---|
| Declared arguments and their subterm occurrences | Which occurrences are declared roots, equality among occurrences within the fragment, and the containment relation |
| Emitted attacks | Each declared argument's inferred conclusion, hence its contrary matches as a source |
| Received attacks | Occurrence conclusions, leaf/defeasible-root attackability, and rule identity where the policy's exception table can inspect it |
| Internal influence | The declared attacks' source and attacked occurrence incidence, and the resulting closure edges between declared arguments |
| Observed conclusions | Which declared arguments support each export; the list of exports stays fixed |

The profile forgets certificate payloads and other construction details beyond
these fields. It contains all declared arguments, including non-exports, and
all their premise and discharge subterms. It is specified from support and
attack data before linking, without quantifying over contexts or defining a
relation by equality of observations. This is the intended independence from
contextual equivalence.

The environment quantifier is necessary: an open fragment need not have a
standalone checked carrier. `fragmentCarrier` returning `none` is not a license
to give every such fragment the same empty profile. Even this enriched
candidate is insufficient: its equality information stops at the fragment
boundary.

## What happens at the two recorded obstructions?

**Obstruction 1: declared imports miss semantic influence.** The executable
`hidden-feedback` check below uses a fragment with no imports, arguments for
`p` and `q`, an internal attack `q → p`, and only `p` exported. A quiet context
yields `p = defeated`. Asserting `s` in that same context adds the saturated
attack `s → q`, and `p` becomes `justified`. The context changes a non-exported
argument and thereby changes an export. Both outcomes are accepted.

`R_occ` includes `q` and its influence on `p`, so it avoids this specific
imports-only error. Root labels alone still do not suffice: `Compile.Covered`
and `attackClosureB` propagate attacks to arguments containing the attacked
term. This is why the candidate also includes occurrences and containment.
The copying test in the next section exposes the remaining cross-boundary gap.

**Obstruction 2: policies cannot necessarily force labels.**
`Examples.Realizability.noAttack_of_emptyDefeat` and
`compiled_no_edges_of_emptyDefeat` already establish that an accepted unit
under an empty contrary and exception table has no edges. Under grounded
semantics every retained argument is in; an export is justified if supported
and gap otherwise. The `empty-defeat-hidden-node` check adds an unexported
argument while preserving the observed justified export. This is one finite
check, not a proof that the two fragments satisfy unrestricted `CtxEquiv`.

Consequently, a completeness argument cannot turn an arbitrary difference in
occurrence profiles into a forced `in`/`out`/`undec` difference without a
policy hypothesis. The close-out's symmetric-contrary warning also remains:
reciprocal attacks between attackable leaves alone do not supply an out-forcing
gadget. Asymmetry or a suitable strict-rooted attacker, plus freshness relative
to both fragments' pattern matches, must be justified. This is not a claim
that every policy with symmetric contraries has only in/undec arguments;
exceptions and other attack shapes also matter. No `LabelExpressive` contract
is frozen here. The finite assurance extension theorem supplies none of these
policy or gadget obligations.

## Does the relation collapse to decorated identity?

There is a stronger warning than the original profile sketch made explicit:
**certificate decoration can be observed through a copied term even when both
payloads are accepted by the same backend.**

The `same-context-copy` check reuses the sound alias backend from
[`Examples/CertificateCollapse.lean`](../lean/Lara/Examples/CertificateCollapse.lean).
Let `a` and `b` be its distinct accepted payloads. One fragment contains only
`wrapped a`; the other contains only `wrapped b`. Their declaration envelope
is identical. Their isolated occurrence profiles match under the obvious
bijection: the same conclusions, rule identities, containment shape and no
internal attacks. Neither profile has an internal alias collision.

The common context declares `wrapped a`, an attacker, and an undercut of its
own `wrapped a`. These attack endpoints are context-declared, so the example
does not rely on a context illegally naming an undeclared endpoint.

| Fragment inserted in that context | What linking does | Export `p` |
|---|---|---|
| `wrapped a` | Merges with the context's attacked copy | defeated |
| `wrapped b` | Remains distinct; the context's copy alone is attacked | justified |

This accepted separation refutes `R_occ` as a sufficient interface relation.
It does not depend on manufacturing a checker error or on a backend rejecting
one payload. `closure-sees-payload` also checks the exact containment test that
makes the distinction possible. The older `certificate-collapse` witness
checks the complementary danger of merging distinct payloads inside one
fragment: justified changes to defeated there too.

A repair must preserve equality and containment **against context material**,
not just within each fragment. Requiring equality against every literal term
probe immediately retains identity: the probe `u = t₁` distinguishes `t₁`
from any different `t₂`. That is a conservative interface choice, not a proof
that every such probe can be realized as a distinguishing, well-formed context
under every fixed policy. Restricting to realizable, export-relevant probes
could be coarser, but needs the policy and observation analysis the gate has
not supplied. Defining the probes to be all distinguishing contexts would
merely restate contextual equivalence.

The existing transport route makes a different, explicit choice.
`RelFixesContext R C` fixes the context's assurances; with `RelInj R`, a payload
shared with the context cannot move. It excludes this copying counterexample.
`relFrag_exists_injective_fixesContext` in
[`Context/FiniteExtension.lean`](../lean/Lara/Context/FiniteExtension.lean)
already shows that every finite `RelFrag` instance satisfying those hypotheses
is realized by an injective `mapAssurFrag` that fixes the context. This confirms
the decorated-identity **shape of that structural relation**. It proves neither
its completeness for `CtxEquiv` nor global acceptance preservation of the
realizing injection. `closedOccurrences C F` is just the union of assurances
on both sides; it is not a contrary-visible occurrence interface.

The collapse risk is therefore real for conservative structural repairs, but
**universal contextual equivalence = decorated identity is not established**.
The copying case shows that the admissible decorations depend on the context;
the empty-defeat case shows why occurrence distinctions need not produce
status distinctions. Neither permits selecting “characterization instead” as
though the characterization had been established. If a later gate establishes
that equality on a precisely stated policy and context domain, that result
should be presented as a characterization theorem, as #305 requires.

## Why stop here?

| Allowed G0 exit | Assessment |
|---|---|
| Interface fixed | No: the candidate fails an accepted same-context test; the repair is not an independent semantic interface with a fixed domain. |
| Characterization instead | No: finite realization characterizes the structural certificate relation's shape, not contextual equivalence. |
| Re-descoped | Selected: stop before a relation freeze or either theorem direction. |

#215 amortizes transport and finite realization after choosing a certificate
relation. #216 amortizes changing the observation after preserving the carrier.
Neither result needs a complete, context-free decision method for arbitrary
fragment equivalence. The new trigger has been honored by running the gate;
it does not remove the original absence of that consumer.

This is a completed negative G0 result, not a postponed implementation plan.
Any future reopening must state the consuming equivalence problem, its policy
and context domain, and a candidate that survives the copying case. Exact fault
observations must either be covered or explicitly excluded in a separately
named equivalence. The old #187 closure and existing paper claim boundaries
stand.

## Reproduce the finite checks

The following block is the complete exploratory input. It adds no theorem,
axiom or library definition. Extract it to a temporary `.lean` file and run it
from `lean/` with `lake env lean /tmp/lara-305-g0.lean`. Build its existing
imports first if needed:

```sh
lake build Lara.Examples.CertificateCollapse Lara.Context.FiniteExtension Lara.Examples.Realizability
```

The five named results must all be `true`, and Lean must exit successfully.
A `true` result checks the displayed finite case only; it is not a universal
soundness, completeness or contextual-equivalence proof.

```lean
import Lara.Examples.Linking
import Lara.Examples.Realizability
import Lara.Examples.CertificateCollapse
import Lara.Context.FiniteExtension

open Lara Lara.Support Lara.Attack Lara.Compile Lara.Context
open Lara.Examples Lara.Examples.Linking
namespace G0

def chainPolicy : Policy.Policy :=
  { rules := [], defeat := ⟨[(apB, apA), (⟨⟨"s"⟩, .nil⟩, apB)], []⟩ }
def chainFrag : Fragment :=
  { fragEx with
    policy := chainPolicy,
    gammaFrag := [(l1, pA), (l2, pB)], ground := [pA, pB],
    args := [.leaf l1, .leaf l2],
    atts := [.undermine (.leaf l2) (.leaf l1) []] }
def chainQuiet : Context :=
  ⟨{ ctxFrame with
    policy := chainPolicy, gammaFrag := [(l3, pC)],
    ground := [pC], args := [] }⟩
def chainLoud : Context := ⟨{ chainQuiet.frame with args := [.leaf l3] }⟩
#eval ("hidden-feedback", decide (
  chainFrag.imports.leaves = [] ∧ chainFrag.exports = [pA] ∧
  obs registryEx chainQuiet chainFrag = .observed [.defeated] ∧
  obs registryEx chainLoud chainFrag = .observed [.justified]))

def emptyPolicy : Policy.Policy := { rules := [], defeat := ⟨[], []⟩ }
def emptyCtx : Context := ⟨{ chainQuiet.frame with policy := emptyPolicy }⟩
def oneArg : Fragment :=
  { chainFrag with policy := emptyPolicy, args := [.leaf l1], atts := [] }
def twoArgs : Fragment := { oneArg with args := [.leaf l1, .leaf l2] }
#eval ("empty-defeat-hidden-node", decide (
  oneArg.args ≠ twoArgs.args ∧
  obs registryEx emptyCtx oneArg = .observed [.justified] ∧
  obs registryEx emptyCtx twoArgs = .observed [.justified]))
#eval ("certificate-collapse", decide (
  obs CertificateCollapse.registry CertificateCollapse.ctx CertificateCollapse.sourceFrag =
    .observed [.justified] ∧
  obs CertificateCollapse.registry CertificateCollapse.ctx CertificateCollapse.targetFrag =
    .observed [.defeated]))
#eval ("closure-sees-payload", decide (
  containsB (CertificateCollapse.wrapped slot1Cert)
    (CertificateCollapse.wrapped slot1Cert) = true ∧
  containsB (CertificateCollapse.wrapped rejectCert)
    (CertificateCollapse.wrapped slot1Cert) = false))
def copyFrag (k : CertRef) : Fragment :=
  { CertificateCollapse.sourceFrag with
    args := [CertificateCollapse.wrapped k], atts := [] }
def copyCtx : Context :=
  ⟨{ CertificateCollapse.ctx.frame with
    args := [CertificateCollapse.wrapped slot1Cert, .leaf l3],
    atts := [.undercut (.leaf l3) (CertificateCollapse.wrapped slot1Cert) []] }⟩
#eval ("same-context-copy", decide (
  obs CertificateCollapse.registry copyCtx (copyFrag slot1Cert) = .observed [.defeated] ∧
  obs CertificateCollapse.registry copyCtx (copyFrag rejectCert) = .observed [.justified]))
end G0
```
