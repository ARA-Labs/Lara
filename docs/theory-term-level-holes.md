# Term-level critical-question holes

_Durable record, landed 2026-09-09 (theory spine follow-on to
M4). For cold readers: a *critical question* is an obligation a reasoning
scheme imposes — "was the experiment randomized?" — that must be answered by
an argument term in the instance's discharge map; a *hole* is a typed
placeholder standing where such an answer term will be substituted in._

The M4 fragment calculus resolves imported leaf names by extending Γ. That alone
cannot discharge a critical question: its answer is a support term inside an
instance's discharge map. The additive `Lara.Context.Holes` calculus represents
those answer positions explicitly, substitutes context-supplied terms, and then
uses the existing checked linker and observations.

## Syntax and scope

A template is either an embedded core `SupportTerm` or a rule instance with
recursive premise and answer templates. An answer is a template or a named
`HoleId`. Hole identifiers and local `QuestionId`s are different types: two nested
instances can ask the same question while requiring different answers from their
context. Sharing a hole identifier is intentional sharing, and typing requires
its demanded answers to agree through the declared hole signature.

A filling table is a finite list of hole identifiers and **core support terms**.
Holes may occur arbitrarily deeply in the template. Filling values do not contain
new named template holes, so substitution does not recursively chase environment
bindings or require a cycle policy. This is the finite CQ-substitution calculus,
not a recursive module system or arbitrary missing-premise calculus.

Existing core terms embed unchanged, including their ordinary optional questions.
A named template hole is an explicit obligation of this new interface; an old
`H` entry is not automatically promoted to one. The frozen `SupportTerm`, checker,
four-state observation, and `Grounded.Claim.holes` behavior are unchanged.

## Source meaning and typed substitution

`eraseOpen` removes unanswered named-hole entries from the discharge map and
adds their question keys to `H`. It therefore yields a real source support term,
not just a diagnostic list. The source-erasure typing theorem derives its
`HasSupport` judgment. Mandatory questions can make its obligation list nonempty.

Template typing is independent of any actual filling. It checks the original
rule lookup, instantiation, premise types, question partition, assurance, and
answer pattern obligations. `InstMeta` factors the original `InstSide` premises
through argument counts and discharge keys; conversion to the existing judgment
is proved. A named hole receives its demanded answer through the hole signature.

Typed fillings supply independently derived complete support, with conclusions
**equivalent** to the demanded answer atoms. Typed substitution derives support
of the resulting term with the same root conclusion and residual obligations.
The conclusion is not an assumption hidden in a template-validity predicate.
When the template's residual obligations are empty, the substituted term is
complete and can cross the existing compilation boundary.

Partial substitution preserves unresolved holes. Final instantiation rejects a
duplicate filling identifier or a missing hole. Instantiation is structural;
the old checker supplies the detailed rejection for a supplied term that fails
to answer the question or otherwise fails typing.

## Linking and attacks

Hole fragments carry template arguments and template attacks. Instantiation
substitutes both source and target endpoints, including nested question-answer
subterms, before calling the existing linker. Hole contexts carry an old context
frame plus their filling table. Observations retain hole-instantiation failures
separately from the old incompatible, rejected, and observed outcomes.

Substitution can identify distinct templates. Consequently, no theorem assumes
it is injective to transport `Nodup`; the existing linker deduplicates the
**instantiated** argument lists. Filling can also introduce new subarguments and
attack targets. Open-term attack coverage is therefore not claimed to imply
closed-term coverage. Link acceptance and attack completeness keep the explicit
post-substitution attack conditions of the old `SideOk` boundary. Their support
premises are derived from typed substitution.

## Composition and backend transport

Disjoint filling tables compose by concatenation, with duplicate identifiers
rejected. Partial substitution agrees with sequential substitution under the
stated domain condition. Context frame composition retains the original
calculus's compatibility and coverage hypotheses; adding holes does not make
arbitrary contexts composable.

Closed embeddings recover the existing observations. Contextual equivalence
quantifies over hole contexts, and its closed-fragment specialization recovers
the old relation, including shared instantiation failures.

Backend replacement passes through instantiation before invoking the existing
contextual congruence. Fixing a hole context requires fixing certificates in its
**fillings** as well as its frame: those terms become part of the substituted
fragment. Relational transport likewise requires self-related context fillings
and retains `RelInj`. Semantics-parametric observation transport uses the same
compiled carrier argument as M4; this extension does not assert full abstraction.

## Theorem map

All names below are under `Lara.Context.Holes` unless stated otherwise.

| Obligation | Declarations |
|---|---|
| Independent rule metadata | `InstMeta.toInstSide`, `InstMeta.ofInstSide`, `InstMeta.answers_equiv` |
| Supported source and filled term | `eraseOpen_hasSupport`, `instantiate_hasSupport` |
| Structural composition and guard | `subst_append`, `fillingNodup_append`, `instantiateFragment_subst` |
| Old calculus recovered | `obs_closed`, `obsSem_closed`, `ctxEquiv_closed_iff`, `ctxEquivSem_closed_iff` |
| Checked instantiated link | `instantiated_support`, `sideOk_of_typed`, `link_attackComplete`, `link_checked` |
| Context composition | `compose_assoc_defined`, `composed_frame_material_assoc`, `composed_filling_assoc` |
| Backend transport | `instantiate_map`, `instantiateAux_rel`, `backend_replacement_congruence_sem`, `backend_replacement_parametricity_sem` |

Context association has the original calculus's scope: both guarded bracketings
are defined under pairwise compatibility and disjointness; frame material agrees
extensionally and filling concatenation agrees exactly. Raw context-record
equality additionally requires equality of the old composed frame records.

## Validation and contract boundary

`Lara.Examples.TermHoles` supplies the nested repeated-question-name example,
source obligations, typed closure, checked acceptance, rejection cases, composition,
and substituted attack endpoint. Every public theorem is covered by `AxCheck`.

The positive `functional_transport_sem` and `relational_transport_sem` fixtures
apply the actual new wrappers to the nested template and its attack, at arbitrary
semantics and across the wrapped registry. Their material has only leaf/none
assurances, so no certificate moves in that positive instance. Separately,
`certificate_context_not_fixed` uses an independently typed certified filling:
the old frame is fixed by the relabel, but the filling is not. This makes the
extra context-fixing condition substantive.

This closes the term-level CQ-hole obligation retained by M3.
It changes no Haskell code, corpus vector, or freeze tag. The original M4 theorems
remain available; the new layer proves the substitution bridges that make them
applicable to instantiated fragments.
