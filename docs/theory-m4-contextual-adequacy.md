# Theory M4 Part A: contextual adequacy of backend replacement

_Status: mechanized on 2026-09-02 for Theory M4 (issue #187, tracker #180),
phases F0–F3 of the since-deleted plan
`plans/2026-09-02-theory-m4-full-abstraction.md`. This document is the durable
claim-boundary record for **Part A**. The design freeze that released the
theorem phases is `docs/theory-m4-context-calculus-decision.md`; the
declaration index is `docs/paper-lean-name-map.md` §M4. Part B (full
abstraction) is **descoped** — §7._

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

**Stated over the grounded observation, and now also over an arbitrary one.**
Everything above is phrased through `obs`, which reads `Invariants.status` — the
grounded labelling and only that. `Lara.Context.Observation` (issue #216,
`docs/theory-m4-generic-observation.md`) supplies the same results at an
arbitrary `Semantics.ExtensionSemantics`, and does so without weakening them:
the congruences carry no hypothesis beyond the ones stated here, because they
transport along the carrier equality `compileUnit_link_relabel` supplies rather
than along pointwise attack agreement. Part A's own statements are unchanged —
every theorem in this section keeps its name, its type and its
implicit-argument order — and the grounded case is recovered as a theorem,
`obsSem_grounded`, with `ctxEquivSem_grounded_iff` showing the two equivalence
relations coincide on the nose at `groundedSem`.

One Part A *definition* was reshaped to carry the parameter — `Observation`
became an abbreviation of a payload-generic `ObservationOf α` — and two Part A
*proofs* became one-line corollaries of the projection-generic
`obsGen_eq_of_ok` / `obsGen_congr` that now sit beside them in
`Lara/Context/Equivalence.lean`. No statement changed. `obs` itself is unchanged, and
`Lara.Context.obs_eq_obsGen` records by `rfl` that it is the projection-generic
observation at the grounded reading. See `docs/theory-m4-generic-observation.md`
§2.

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
(`linkOk_composed`, `composed_ownIds`) but not for linkability, and that
boundary is a **theorem**, not a paragraph: `Examples.Linking` builds two
contexts each admissible for one fragment (`hostile_left_admissible`,
`hostile_right_admissible`), composes them (`hostile_compose_ok`), shows the
composite passes the guard (`hostile_composite_links`), and proves it is not
admissible (`hostile_composite_not_admissible`, issue #229). Neither half
could have covered the cross-boundary conflict on its own, since a side's
attacks must have both endpoints among its own arguments. Giving `compose` the
registry and Γ that saturation needs would change its F0-frozen, deliberately
data-only signature; the witness is the honest alternative.

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

## 4. The surface corollary, and its worked pair

D1 put contexts at the core `Lara.Unit` level and promised a surface
*corollary*. `lean/Lara/Context/Surface.lean` delivers it:
`surface_directAF_relabel` — two accepted surface programs whose elaborated
units are related by an injective relabel present the **same** framework, via
M5's `Lara.Surface.direct_compiled_agree` — and `surface_directAF_link`, the
instance where the two units are the two sides of a link. Everything the
surface layer reports off that framework agrees, for every carrier-local
extension semantics (`Lara.Surface.observe_coherent`).

**The worked pair is `Lara.Examples.SurfaceTransport.surfaceTransport_directAF_eq`**
(`lean/Lara/Examples/SurfaceTransport.lean`, issue #227). Two accepted surface
programs, differing only in one `nd@1` certificate related by
`Examples.Linking.certSwap`, present the same framework — and the statement is
unconditional, because the two accepted units are produced by
`CoreObligations.checkUnit_complete` rather than assumed.

Two guards keep it from being a tautology, since `f = id` would otherwise
satisfy every hypothesis:

| Guard | Statement |
|---|---|
| `surfaceTransport_relabel_moves` | `output₂.unit.args ≠ output₁.unit.args` |
| `surfaceTransport_inputs_differ` | `input₂ ≠ input₁` |

**The attack-bearing pair is
`Lara.Examples.SurfaceTransportAttack.surfaceTransportAttack_directAF_eq`**
(`lean/Lara/Examples/SurfaceTransportAttack.lean`, issue #258). The #227 pair
above declares no attacks, so both sides of its equality are the one-node,
no-edge framework and `checkedAF_map`'s edge half —
`coveredB_relabel hf P₁.atts source target`, `Context/Surface.lean:53` — is
exercised only on `[]`. The #258 fixture declares three arguments and one
rebut, so that call runs on a one-element list and the four attack-side
`CoreObligations` fields (`attacksTyped`, `sourcesDeclared`,
`targetsDeclared`, `attackComplete`) are real obligations rather than vacuous
ones.

The attack could **not** be sourced at the certified argument, and the reason
is a policy law rather than a proof-engineering limit: `Policy.WellFormed`
(`lean/Lara/Policy.lean:524`) forbids any declared contrary either of whose
sides overlaps a strict-reachable conclusion pattern, and `StrictReachable`
(`:203`) is exactly "conclusion of a declared strict rule". The certified rule
is strict with conclusion `q`, and `HasAttack.rebut` needs a `ContraryMatch`
between the source's and the target's conclusions — so a certified argument
can be neither endpoint of a rebut in a well-formed policy. The fixture
therefore makes the certificate a *premise* of both endpoints: two plain
defeasible rules `q ⊢ s` and `q ⊢ t` over the certified argument, with
`contrary s t`. `mapAssurAtt certSwap` consequently moves the declared attack
and not just the argument list.

Three further guards keep this one honest:

| Guard | Statement |
|---|---|
| `surfaceTransportAttack_atts_nonempty` | `output.unit.atts ≠ []`, both sides |
| `surfaceTransportAttack_relabel_moves_atts` | `output₂.unit.atts ≠ output₁.unit.atts` |
| `surfaceTransportAttack_directAF_edge` | `(directAF _).attack 1 2 = true`, both sides |

Getting there required not using the obvious route. Every accepted surface
fixture in `lean/Lara/Examples/Surface.lean` is proved by `native_decide`, which
M4's axiom discipline (D9) bans: a witness built on one would import
`Lean.ofReduceBool` into the audit and fail `scripts/check-axioms.sh`.

The obstruction is much narrower than "the surface checker's evaluation does not
fit kernel `decide`", and locating it precisely matters, because the narrow
version is tractable where the broad one is not.

The surface *predicates* decide fine, on the full fixture:
`Examples/Surface.lean:283` proves `Supported allFormsInput` by plain `decide`,
and `:295` decides `comparisonsWellFormedB allFormsProgram allFormsPolicy` —
both over the whole all-forms program, both in the axiom ledger. The
reconstruction pass is not the problem either: `reconstructExplicitTerm` and its
mutual partners (`lean/Lara/Surface/Check.lean:296`) compile to `brecOn`
structural recursion, not well-founded recursion, and the kernel unfolds them.

Exactly one function on the path is kernel-opaque: `Lara.NDNamed.lowerFormula`
(`lean/Lara/NDNamed.lean:179`) and its caller `lowerNamedExpr` (`:195`) are
`termination_by sizeOf`, so Lean compiles them to `WellFounded.Nat.fix` and
marks them `@[irreducible]`. No `rfl` or `decide` reduces them, not even on an
`.atom` leaf. They are reached only through certificate-payload lowering —
`lowerAssuranceCertificate` (`Surface/Check.lean:191`) dispatches `nd@1`
payloads to `NDNamed.lowerNamed` — which is why `reconstructArgs` (`:905`) does
not reduce, and why an accepted fixture *carrying a certificate* cannot be
obtained by evaluation.

That dictates the fixture's shape rather than closing it off, and the shape is
what `SurfaceTransport` implements:

- **The certificate is authored in kernel form.** `lowerNamed` scans for a named
  marker and returns the payload unchanged when there is none, so a payload
  written as `NDNamed.encodeCert` never reaches the well-founded pass.
  `NDNamed.lowerNamed_id_of_kernel` (`NDNamed.lean:323`) states exactly this,
  and its `hNat` hypothesis is literally the `Env.startsIdent_nat_false` field.
- **`Checks.program` is hand-built.** `ChecksProgram` (`:895`),
  `ChecksDeclaration` (`:879`) and `ChecksArgument` (`:695`) are relational
  inductives whose constructors — as `ChecksArgument`'s docstring states — never
  mention `reconstructArgument`. The `.inferred` constructor also avoids
  `ReconstructsExplicitTerm`, which is why the fixture's argument uses
  `inferTheta`.
- **`CoreObligations` is hand-built too** (`transport_coreObligations_kernel` /
  `_wrapped`), and the `HasSupport` derivation inside its `supports` field
  follows `Examples.Linking.certArg_checked` field for field. This is forced:
  `certOkOf` on the `nd` core does not reduce in the kernel, so `checkUnit`
  cannot be `decide`d on a certificate-bearing unit and
  `CoreObligations.of_checkUnit_ok` is unusable.
- **Registry acceptance is inherited, not replayed.** The lowered payload is
  definitionally `Examples.slot1Cert`, so `registry_exact_digest_accepts`
  applies to program 1; `certSwap_preserving` carries program 2.

The corollary and its instance are both sorry-free and inside the standard trio.

### The link corollary, witnessed

The stronger sibling `surface_directAF_link` is witnessed by
**`Lara.Examples.SurfaceTransport.surfaceTransport_link_directAF_eq`** (issue
**#255**), on the same fixture. It does not take the argument and attack
correspondence as hypotheses; it *derives* them from `link_relabel_commutes`,
so the work is exhibiting a context and a fragment for which

* `output₁.unit = linkedUnit registryEx linkCtx (linkFrag kernelCoreAssur)`
  (`transport_unit_is_link`) and
* `output₂.unit = linkedUnit registryWrapped linkCtx (mapAssurFrag certSwap
  (linkFrag kernelCoreAssur))` (`transport_unit_wrapped_is_link`),

plus `transportLink_admissible : Admissible registryEx linkCtx (linkFrag
kernelCoreAssur)` and `FixesContext certSwap linkCtx`.

The split is forced rather than chosen. The elaborated unit declares exactly
one core argument, and `linkedUnit`'s argument field is `dedupList (C.frame.args
++ F.args)`, so the fragment owns that argument and the context owns none. What
the context does own is the evidence leaf `l-p`, which the fragment imports —
R-L2 is live (`surfaceTransport_link_imports_nonempty`), so the link is real at
the interface. Non-vacuity is guarded by
`surfaceTransport_link_relabel_moves_args` and
`surfaceTransport_link_relabel_moves`, restating at the fragment what
`surfaceTransport_relabel_moves` states at the unit.

**Two degeneracies, both since closed.** On the fixture above `FixesContext`
holds because the context's argument list is empty, so *that* witness does not
exercise a relabel which has to *avoid* a context's own certificates; and the
fixture declares no attacks, so the attack half of `link_relabel_commutes` is
discharged on empty lists and `crossAtts` saturates to nothing
(`crossAtts_of_ctx_args_nil`). Each has its own witness now, and each is a
separate fixture because closing both at once buys nothing either issue asks
for:

* the attack-bearing fixture is `Lara/Examples/SurfaceTransportAttack.lean`
  (issue **#258**), which closes the edge-free gap for
  `surface_directAF_relabel` above; and
* the context-bearing fixture is the one described next (issue **#264**).

### The link corollary over a context that carries material

**`Lara.Examples.SurfaceTransportContext.surfaceTransportContext_link_directAF_eq`**
(issue **#264**) instantiates the same `surface_directAF_link` with a
**non-empty** `C.frame.args`. The elaborated unit declares two core arguments
and the link splits them across the boundary:

* the context owns `a-ctx`, a plain defeasible `p ⊢ n` carrying `.none`, which
  `certSwap` fixes; and
* the fragment owns `a-cert`, the #227 certified `p ⊢ q`, which `certSwap`
  moves.

So `contextLink_fixesContext` is an equation over material the relabel could
have touched, and `surfaceTransportContext_fixes_is_substantive` records both
halves in one statement: the same `certSwap` is the identity on the context's
argument and is *not* the identity on the fragment's.
`surfaceTransportContext_ctx_args_nonempty` is the regression guard — it pins
`C.frame.args ≠ []` and that the context's argument survives into the linked
unit rather than being deduped away.

One lemma had to be replaced rather than reused. `linkedUnit_of_empty_ctx`
collapses the cross-boundary saturation *because* the context has no arguments,
which is exactly the degeneracy being removed; and with a context argument
present, `crossAtts` builds both conclusion caches, where `conclusionCache`
calls `Check.inferSupport` through `certOkOf` on the `nd` core — which does not
reduce in the kernel. The replacement (`crossAtts_of_no_contraries`) reads the
saturation's *emission guard* instead of its caches: `crossAttsFrom` emits
nothing unless `contraryMatchB` holds, and `contraryMatchB` is
`dp.contraries.any …`, so a policy declaring no contrary saturates to nothing
whatever the caches contain. That is a statement about the policy rather than
about the argument lists, so it survives the context gaining material.

This fixture declares no attacks, which is the #258 degeneracy and not this
one's to close; the no-contraries route above is precisely what keeps it
`native_decide`-free.

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
- The congruence and its three companions hold **under every extension
  semantics in the M2a interface**, with the same hypotheses and no additional
  one (`backend_replacement_congruence_sem`, `registry_swap_congruence_sem`,
  `backend_replacement_congruence_composed_sem`, `whole_program_replacement_sem`;
  issue #216, `docs/theory-m4-generic-observation.md`). The generalization is
  non-trivial: `Examples.ContextSemantics.obsSem_cycle_stable_ne_grounded`
  reaches an observation arm the grounded reading cannot reach, and
  `obsSem_sink_preferred_ne_grounded` has two semantics answer and disagree.

### Must not claim

- **Not parametricity.** *This* theorem quantifies over a function
  `f : Assurance → Assurance`, not a relation. The relational form is
  `Context.backend_replacement_parametricity`
  (`docs/theory-m4-relational-parametricity.md`, #215); it is a separate
  theorem, and `backend_replacement_congruence` keeps its own name and its own
  simpler hypotheses. The relational form is itself bounded: it requires the
  relation to be a partial bijection on certificates (`RelInj`), so it is not
  parametricity over arbitrary relations either. Of the four M4 congruences,
  two have relational companions and two
  (`backend_replacement_congruence_composed_sem`,
  `whole_program_replacement_sem`) have none.
- **Not full abstraction.** No logical relation is defined anywhere in Part A,
  and neither direction of a soundness/completeness pair is proved. Part B is
  descoped (§7).
- **Not unconditional in the context quantifier.** The statement is about
  *admissible* contexts (§3). A paper display must carry that hypothesis.
- **Not under contexts changed by the relabel.** `FixesContext f C` requires
  the relabel to fix every assurance in the context's own arguments and
  attacks; a context carrying a moved certificate is outside the theorem.
- **Not a new proof of result 9.** `whole_program_replacement` cites
  `Erase.backend_replacement`; the milestone's progress is the context
  quantifier.
- **Not a statement about term-level holes** (§5).
- **Not a claim that the equivalence *relations* at different semantics
  separate or coincide.** #216 generalized the observation *functions* and
  separated them at concrete carriers; whether `CtxEquiv reg F₁ F₂` implies
  `CtxEquivSem sem reg F₁ F₂` at a non-grounded `sem` is neither proved nor
  refuted, and is issue **#268**. `ctxEquivSem_grounded_iff` settles the
  grounded instance only.
- **Not a claim that the semantics-parametric congruence witnesses exercise the
  semantics parameter.** `congruence_witness_sem` and `registry_swap_witness_sem`
  sit at `ctxEx`/`fragEx`, where all five semantics agree, so the quantifier is
  inert there; issue **#270** is the carrier that would fix it, and **#269** the
  certificate-bearing instantiation.
- **Not a claim that contexts are closed under composition for *linkability*.**
  They are closed for hygiene; a composite whose halves attack each other is not
  admissible, and `Examples.Linking.hostile_composite_not_admissible` exhibits
  one (#229).
- **Not a claim that a context may redefine the policy or the registry.** The
  policy is a rejection class (R-L3); the registry is a parameter of the
  calculus, so registry redefinition is unrepresentable rather than rejected.
- **Not a Haskell-side result.** M4 adds no checker, CLI, wire or corpus
  surface, so it moves no conformance vector and no performance number (D8).

## 7. Part B: descoped (2026-09-03)

Part B (a logical relation with soundness and completeness — full
abstraction) was **not entered, and is now descoped by maintainer decision**
rather than deferred. This section is the durable record of why, and of the
design that a future reopening would start from; the working plan that carried
it (`plans/2026-09-02-theory-m4-full-abstraction.md`) is deleted per the
repository's plan discipline.

### The two obstructions, recorded at F0 and unchanged by Part A

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

### Why descope rather than run the gate

- **No consumer.** The result the system's story needs — backend
  interchangeability under every admissible context — is Part A. Full
  abstraction adds a context-free *proof method* for arbitrary fragment
  equivalences, and no obligation in the development or the paper uses one.
- **The tautology risk is structural, not incidental.** Full abstraction is
  informative when the logical relation is coarser than syntax. Lara's
  contexts are close to maximally discriminating (obstruction 1), which pushes
  contextual equivalence toward syntactic identity up to contrary-invisible
  decoration — i.e. toward `Erase.mapAssur` generalized. A full-abstraction
  theorem with a near-syntactic relation would be true but empty.
- **It was the tracker's named drop.** #180 lists this as the highest-effort
  item with an explicit drop policy ("the first item removed if schedule or
  page pressure threatens mechanization quality"); the completeness gadget
  alone is priced against M2b's ~3,000-line checked-family construction
  (`Complexity/Gadget.lean`, `Complexity/Reduction.lean`), parameterized here
  by arbitrary interface labellings.

The paper claims Part A under its honest name (contextual representation
independence, §6) and states full abstraction as not attempted, with the
`emptyDefeat` and symmetric-contrary boundary facts as content.

### Retained design, for a reopening

A future attempt should start here, not from scratch:

- **Phasing.** G0: an unlanded soundness spike answering the interface
  question (is a sound relation more than `Erase.mapAssur` generalized?);
  G1: freeze `LogRel` over the contrary-visible occurrence profile, emitted
  and observed sides separated, with a dated freeze record and amendment
  procedure; G2: soundness by grounded-fixpoint induction over the linked AF
  (M2a carrier-boundedness lemmas); G3: completeness by contrapositive via
  `checkUnit_complete` plus a `ground_covers` obligation — **not**
  `Realizability.Realizable`, whose `compiled_iso` targets a given whole-unit
  `StructuredAF`, precisely the unknown; G4: closeout. Stop rule: if
  completeness stalls beyond the expressiveness hypothesis, keep G2 as
  *adequacy of the logical relation* — do not rename it full abstraction.
- **`LabelExpressive`, the completeness hypothesis.** Forcing `out` needs an
  asymmetric contrary pair or a strict-rooted attacker (`ConflictAttackable`
  is unconditionally `True` on leaves; rebut needs `.defeasible`); a purely
  symmetric contrary table forces only `{in, undec}`. Contraries are
  *patterns* with universally quantified variables, so a "fresh" atom on the
  same predicate still matches and causes collateral attacks — every forcing
  gadget carries an explicit freshness side-condition relative to atoms unused
  by *both* fragments. Positive witness: `m2bPolicy`'s asymmetry
  (`Complexity/Context.lean`). Negative witness: `emptyDefeat`, seeded by
  `Examples/Realizability.lean`'s `oneSelfEdge_not_realizable`.
- **Reopening triggers.** #215 (relational parametricity) landed without
  reopening this gate: `RelTerm` lifts a relation on *certificates*
  structurally and is not the interface relation G1 would freeze, so it
  amortized nothing here. #216 likewise: it generalized the observation
  *functions* over `sem` and the payload over `α`, and defined no relation
  between fragments at all — `LogRel` appears nowhere in `lean/`, as
  `docs/theory-m4-generic-observation.md` §7 records. Absent a consumer that
  needs a relation over the contrary-visible occurrence profile, the descope
  stands.

**#187 is closed on Part A** with this boundary recorded; reopening goes
through a fresh issue citing this section and answering G0's interface
question first.

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

The coverage checker mechanically confirms that all 224 public theorem/lemma
declarations in the M4 modules are listed in `AxCheck.lean`; the axiom audit
then checks them for `sorry` and permits only `propext`, `Classical.choice`, and
`Quot.sound`. No `native_decide` is used. No Haskell conformance vector is
required (D8), and there is no corpus regeneration or freeze-tag bump.

The follow-ups the phases surfaced were filed rather than folded in, and then
cleared in one pass after Part A closed: **#219** (the `DecidableEq` instances
R-L3 needs now derive at their owning structures), **#220** and **#228** (the
Γ-transport, `buildGamma`, and `HasSupport` inversion lemmas are public at
`Lara/Support.lean`, `Lara/Attack.lean`, and `Lara/Admission.lean`, and the
private re-proofs in `Lara/Update.lean`, `Lara/Consistency.lean`, and
`Lara/Context/Link.lean` are gone), **#226** (the `conclusionCache` /
`conflictCache` agreement bridge is `Context.conclusionCache_eq_conflictCache`
and `Context.link_cache_bridge`), and **#229** (the composition boundary is
witnessed, §2). **#222** was closed without change: the list helpers it named
never landed in `Lara/Context/Compose.lean`. **#227** (a `native_decide`-free
surface fixture, §4) landed as `Lara/Examples/SurfaceTransport.lean`, and
**#258** (the same witness with a non-empty attack set, §4) as
`Lara/Examples/SurfaceTransportAttack.lean`. **#264** (the link witness over a
context that declares an argument of its own, §4) landed as
`Lara/Examples/SurfaceTransportContext.lean`.
