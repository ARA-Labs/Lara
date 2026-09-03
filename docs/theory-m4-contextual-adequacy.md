# Theory M4 Part A: contextual adequacy of backend replacement

_Status: mechanized on 2026-09-02 for Theory M4 (issue #187, tracker #180),
phases F0–F3 of `plans/2026-09-02-theory-m4-full-abstraction.md`. This document
is the durable claim-boundary record for **Part A**. The design freeze that
released the theorem phases is `docs/theory-m4-context-calculus-decision.md`;
the declaration index is `docs/paper-lean-name-map.md` §M4. Part B (full
abstraction) is **not** entered — §7._

## 1. What Part A proves

**Contextual representation independence.** An injective,
acceptance-preserving relabel of a fragment's certificates is unobservable in
every admissible context whose own assurances the relabel fixes:

```lean
theorem backend_replacement_congruence
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F) (hfix : FixesContext f C) :
    obs reg₁ C F = obs reg₂ C (mapAssurFrag f F)
```

`Lara.Context.backend_replacement_congruence`, `lean/Lara/Context/Equivalence.lean`.

This is what `docs/theory-m3-source-updates.md` §"Scope and Verification"
deferred to M4, and it **extends result 9 along the context quantifier**: `Erase.backend_replacement`
relates two whole programs given as `CheckedProgram`s, this relates a fragment
to its relabeling inside every admissible context. The two are not comparable
as statements — result 9 carries no admissibility hypothesis, and this carries
no arbitrary-program quantifier — which is exactly why result 9 is cited rather
than re-derived below. Result 9 is kept and cited, not re-derived
(`whole_program_replacement`): a corollary route through the congruence would
have to carry an `Admissible` context and would be *weaker*, so the
re-derivation would be a regression dressed as progress.

**The generalization (D6).** `registry_swap_congruence` drops the relabel and
the injectivity entirely: if every assurance the first registry accepts the
second accepts too, the *same* fragment reads the same way in every admissible
context. One precision the plan's phrasing did not carry: the hypothesis is
**global**, not restricted to the fragment's certificate occurrences —
`hasSupport_mapAssur`, which transports the derivations, quantifies over every
rule and assurance.
`Examples.Linking.cert_registry_swap_witness` exhibits a genuinely different
pair of registries at a fragment that **actually carries a certificate**, so
the acceptance hypothesis is discharged on something rather than vacuously.

The same fixture carries the congruence's own witness. `certSwap` wraps every
`nd` certificate payload and `registryWrapped` reads the same registry through
a backend core that unwraps before replaying, so the relabel is injective and
acceptance-preserving *by construction*; `cert_relabel_moves` proves it is not
the identity on the fragment, and `cert_congruence_witness` is the congruence
applied to it. That is result 9's model — a backend swap that renames
certificates — made concrete for the first time in the development, and now
under a context quantifier.

The assurance-free fixtures (`congruence_witness`, `registry_swap_witness`) are
retained as *shape* witnesses only: a fragment of bare leaves has no
certificate, so `mapAssurFrag f` is the identity on it for every `f`. They
exercise the plumbing, not the theorem.

## 2. What "context" means here

A `Fragment` carries Σ, the policy, its declared leaves, its ground atoms, its
arguments and attacks, an **import** interface of leaf identifiers and an
**export** list of observable *conclusions*. A `Context` is the fragment-shaped
material surrounding the hole. `link` is defined where a decidable guard holds
and **saturates**: `Compile.AttackComplete` is an all-pairs condition, so every
cross-boundary contrary conflict onto an attackable target must be represented,
and `crossAtts` emits it. Structurally identical arguments across the boundary
are **merged**, never rejected; `link_merge_status_eq` proves the merge
invisible to every claim's status, and `docs/theory-m4-context-calculus-decision.md`
§3 records why rejecting them would refute any congruence coarser than term-set
equality.

`obs` returns a closed `Observation`: `.incompatible fault` for a guard failure,
`.rejected error` for a compatible linked unit rejected by the checker, and
`.observed statuses` for an accepted link. `CtxEquiv` compares this detailed
outcome in every context, so incompatibility cannot be masked by checker
rejection.

Contexts are closed under `compose` where its guard holds
(`Lara.Context.Compose`), so the congruence's quantifier already ranges over
every composite, and `admissible_composed` assembles a composite's side of the
hypothesis from its two halves.

**One boundary, stated rather than hidden.** `compose` does *not* saturate:
`link` covers the conflicts between the whole context and the fragment, and
nothing ever emits the conflicts *between the two halves*. So
`sideOk_composed` takes the two cross-boundary quadrants as explicit
hypotheses, and a composite of two contexts that attack each other across their
own boundary is not admissible — outside the theorem's quantifier rather than a
counterexample to it. Composition is closed for hygiene
(`linkOk_composed`, `composed_ownIds`) but not for linkability. Giving
`compose` the registry and Γ that saturation needs would change its F0-frozen,
deliberately data-only signature, so the alternatives are tracked as issue
**#229** rather than folded in.

## 3. The admissibility hypothesis is content, not scaffolding

`Admissible reg C F` says: the guard passes, both sides' declared material is
well-formed relative to the **linked** environment (`SideOk`), the linked
program passes stage 2, and the shared policy is well-formed. Nothing in it
mentions the conclusion, and `Examples.Linking.admissible_split` discharges it
on a concrete pair, so it is inhabited rather than decorative.

It cannot simply be dropped. `obs` distinguishes a checker rejection from an
observed status list, and a *forward-only* acceptance hypothesis lets `reg₂`
accept certificates `reg₁` rejects — so an unconditional "for every context"
statement would be **false** unless acceptance is two-way, a strictly stronger
notion of backend replacement than result 9's model. Recording this is part of
the result: the theorem is as strong as the acceptance relation it is given,
and no stronger.

## 4. The surface corollary, and the one thing it lacks

D1 put contexts at the core `Lara.Unit` level and promised a surface
*corollary*. `lean/Lara/Context/Surface.lean` delivers it:
`surface_directAF_relabel` — two accepted surface programs whose elaborated
units are related by an injective relabel present the **same** framework, via
M5's `Lara.Surface.direct_compiled_agree` — and `surface_directAF_link`, the
instance where the two units are the two sides of a link. Everything the
surface layer reports off that framework agrees, for every carrier-local
extension semantics (`Lara.Surface.observe_coherent`).

**What is missing is a worked surface *pair*, and the reason is recorded rather
than papered over.** Every accepted surface fixture in `lean/Lara/Examples/Surface.lean`
is proved by `native_decide`, which M4's axiom discipline (D9) bans: a witness
built on one would import `Lean.ofReduceBool` into the audit and fail
`scripts/check-axioms.sh`. Building a `native_decide`-free accepted surface
fixture is a separate piece of work — the surface checker's evaluation does not
fit kernel `decide` — and it is filed as issue **#227** rather than attempted
here. The corollary itself is sorry-free and inside the standard trio; what is
unavailable is a concrete instance of it.

## 5. The M3 debt: partially discharged

`docs/theory-m3-source-updates.md` retains "contextual adequacy" and names
"holes" among its obligations. Part A discharges contextual adequacy for
**leaf-name openness** — the only openness this calculus can express.

A **term-level** hole (an argument with unresolved critical-question
obligations that the context discharges) is unrepresentable, and not by choice:
`Compile.CheckedProgram.complete` (`Compile.lean:480`) forces an empty
obligation set on every declared argument, and discharges live inside the term
(`D : List (QuestionId × SupportTerm)`), not in a name environment a context
could extend. `Grounded.Claim.holes` is likewise never read by the observation.

So the debt is marked **partially** discharged, and term-level holes are issue
**#217**.

## 6. Paper claim boundary

### May claim

- Backend replacement is a **congruence**: an injective, acceptance-preserving
  relabel of a fragment's certificates is unobservable in every admissible
  well-formed context whose own assurances satisfy `FixesContext`
  (`backend_replacement_congruence`).
- The relabel-free form: two registries, the second accepting everything the
  first accepts, are contextually indistinguishable on the same fragment
  (`registry_swap_congruence`) — the hypothesis is global, not
  occurrence-restricted — witnessed on two genuinely different registries at a
  fragment that actually carries a certificate
  (`Examples.Linking.cert_registry_swap_witness`).
- A composite's linkability is assembled from its halves (`sideOk_composed`,
  `admissible_composed`) — under explicit cross-coverage hypotheses, because
  `compose` does not saturate (#229).
- The calculus is mechanized, not sketched: fragments, interfaces, contexts, a
  **witnessed** link guard with three rejection classes, saturating linking,
  structural merge, context composition and its closure, and acceptance of a
  well-linked composition (`link_checked`).
- Linking's design choices are theorems, not conventions: saturation makes
  `AttackComplete` hold on a link (`link_attackComplete`), and the merge is
  semantically inert (`link_merge_status_eq`). `crossAtts_nonempty` separately
  witnesses a link where saturation adds a real cross-boundary attack.
- The grounded observation is invariant under any node-merging morphism of
  argumentation frameworks (`Lara.Invariants.CarrierMerge.status_eq`) — a
  statement about frameworks, independent of this calculus.
- The result transports to the surface: two surface programs related by the
  relabel present the same framework (`surface_directAF_relabel`).
- M3's contextual-adequacy obligation is discharged for leaf-name openness.

### Must not claim

- **Not parametricity.** There is no relational quantification over related
  backends. #187's acceptance criterion reserves the word for that; the
  relational form is issue **#215**.
- **Not full abstraction.** No logical relation is defined anywhere in Part A,
  and neither direction of a soundness/completeness pair is proved. Part B is
  gated and not entered (§7).
- **Not unconditional in the context quantifier.** The statement is about
  *admissible* contexts (§3). A paper display must carry that hypothesis.
- **Not under contexts changed by the relabel.** `FixesContext f C` requires
  the relabel to fix every assurance in the context's own arguments and
  attacks; a context carrying a moved certificate is outside the theorem.
- **Not a new proof of result 9.** `whole_program_replacement` cites
  `Erase.backend_replacement`; the milestone's progress is the context
  quantifier.
- **Not a statement about term-level holes** (§5), and not about any semantics
  other than grounded — the generic-`ExtensionSemantics` version is issue
  **#216**.
- **Not a claim that contexts are closed under composition for *linkability*.**
  They are closed for hygiene; a composite whose halves attack each other is not
  admissible (#229).
- **Not a claim that a context may redefine the policy or the registry.** The
  policy is a rejection class (R-L3); the registry is a parameter of the
  calculus, so registry redefinition is unrepresentable rather than rejected.
- **Not a Haskell-side result.** M4 adds no checker, CLI, wire or corpus
  surface, so it moves no conformance vector and no performance number (D8).

## 7. Part B: still gated, and why

Part B (a logical relation with soundness and completeness) was **not**
entered. The two obstructions recorded at F0 stand unchanged, and nothing in
Part A weakened them:

1. **The semantic interface is wider than the declared imports.**
   `AttackComplete` is all-pairs and `Compile.Covered` closes under
   subarguments, so a context can attack any fragment argument whose conclusion
   contrary-matches; and grounded labelling is a fixpoint over the *linked* AF,
   so a non-exported boundary argument feeds back into an export. A relation
   over declared imports is refuted; a relation over the full contrary-visible
   occurrence profile risks collapsing into a generalized `Erase.mapAssur`.
2. **Completeness is policy-conditional.** Under `emptyDefeat` no attack types,
   so `logrel_complete` is false without a hypothesis; and since
   `ConflictAttackable` is unconditionally `True` on leaves while rebut
   requires `.defeasible`, a symmetric contrary table forces only
   `{in, undec}`.

Part A is deliberately immune to both: a uniform relabel preserves the whole
occurrence profile, so "what is the interface" never has to be answered.

**#187 stays open.** Part A closes the milestone's committed scope; Part B
remains its optional continuation, to be entered only through its own gate.

## 8. Verification

```sh
cd lean && lake build
(cd lean && set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
bash scripts/test-check-axioms.sh
python3 scripts/test_check_axcheck_coverage.py
python3 scripts/check-axcheck-coverage.py lean/AxCheck.lean \
  lean/Lara/Invariants/Merge.lean lean/Lara/Context/Fragment.lean \
  lean/Lara/Context/Link.lean lean/Lara/Context/Merge.lean \
  lean/Lara/Context/Compose.lean lean/Lara/Context/Equivalence.lean \
  lean/Lara/Context/Surface.lean lean/Lara/Examples/Linking.lean
```

The coverage checker mechanically confirms that all 218 public theorem/lemma
declarations in the M4 modules are listed in `AxCheck.lean`; the axiom audit
then checks them for `sorry` and permits only `propext`, `Classical.choice`, and
`Quot.sound`. No `native_decide` is used. No Haskell conformance vector is
required (D8), and there is no corpus regeneration or freeze-tag bump.

Two mechanical follow-ups the phases surfaced are filed rather than folded in:
**#219** (the `DecidableEq` instances R-L3 needs, derived downstream instead of
at their owning modules), **#220** and **#228** (Γ-transport, `buildGamma`, and
`HasSupport` inversion lemmas that are `private` at their owning modules and
re-proved here). **#226** records the optional `conclusionCache` /
`conflictCache` agreement bridge that no phase needed.
