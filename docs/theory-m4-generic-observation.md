# Generic-`ExtensionSemantics` Contextual Observation (issue #216)

**Landed 2026-09-07.** Lean-only, purely additive. No corpus regeneration, no
freeze-tag bump, no Haskell change — the runtime evaluator stays grounded, per
`lean/Lara.lean`'s M2a index entry.

Modules: `lean/Lara/Invariants/Observation.lean`,
`lean/Lara/Context/Observation.lean`, `lean/Lara/Examples/ContextSemantics.lean`.

_The gap this closes, in one sentence: M2a made the argumentation semantics a
parameter, but the M4 contextual theorems were still stated only at the
grounded instance — this issue restates them over an arbitrary
`ExtensionSemantics`, removing the asymmetry._

---

## 1. What this closes

M2a (#185, `docs/theory-m2a-observation.md`) made the choice of argumentation
semantics an object rather than a hardcoded assumption: `ExtensionSemantics`,
five instances, ten pairwise separations, and a claim-level observation
`Semantics.observe : ExtensionSemantics → AF → Grounded.Claim → ClaimObservation`.

M4 Part A (#187, `docs/theory-m4-contextual-adequacy.md`) then built the context
calculus on top of the **grounded** status and nothing else. `Lara.Context.obs`
reads `Invariants.status`, which is `Grounded.statusC` of the erased carrier;
`Lara.Context.CtxEquiv` quantifies over contexts at that one reading. So the
repository declared a semantics parameter and then stated its *contextual*
theorems at exactly one instance of it, while quantifying over the parameter only
at the framework level. That asymmetry was an artefact of the order the
milestones landed in, not a fact about the theory.

It is now closed. The new declarations:

| Declaration | Module | What it is |
|---|---|---|
| `Invariants.observeSem` | `Lara/Invariants/Observation.lean` | `Invariants.status` at an arbitrary `sem` |
| `Invariants.observeSem_grounded` | ″ | the grounded instance is `status`, no hypothesis |
| `Invariants.observeSem_gap`, `observeSem_of_status_gap` | ″ | `gap` is semantics-independent at the carrier |
| `Context.ObservationOf α` | `Lara/Context/Fragment.lean` | `Observation` with its payload left open; `Observation` is an abbreviation of it at `Grounded.Status` |
| `Context.obsGen`, `obsGen_incompatible`, `obsGen_rejected`, `obsGen_eq_of_ok` | `Lara/Context/Equivalence.lean` | `obs` with the *projection* left open, and its three link arms |
| `Context.obs_eq_obsGen` | ″ | `obs` **is** `obsGen` at the grounded projection, by `rfl` |
| `Context.obsGen_congr` | ″ | contextual representation independence, for every projection at once |
| `Context.obsSem`, `Context.CtxEquivSem` | `Lara/Context/Observation.lean` | the semantics-parametric instances |
| `Context.obsSem_grounded`, `ctxEquivSem_grounded_iff` | ″ | the grounded regressions |
| `backend_replacement_congruence_sem`, `registry_swap_congruence_sem`, `backend_replacement_congruence_composed_sem`, `whole_program_replacement_sem` | ″ | the four M4 congruences at an arbitrary `sem` |
| `Examples.ContextSemantics.*` | `Lara/Examples/ContextSemantics.lean` | the fixtures that make the parameter non-trivial at the context level |

Every existing *statement* is untouched. `obs`, `CtxEquiv`, `obs_eq_of_ok`,
`backend_replacement_congruence`, `registry_swap_congruence`,
`backend_replacement_congruence_composed` and `whole_program_replacement` keep
their names, their types and their implicit-argument order, and
`Lara/Invariants.lean`, `Lara/Observation.lean`, `Lara/Semantics.lean` and
`Lara/Grounded.lean` are byte-for-byte unchanged.

One grounded *definition* did change shape, and §2 explains why:
`Lara/Context/Fragment.lean`'s `Observation` inductive became the payload-generic
`ObservationOf α`, with `Observation` an abbreviation of it. Alongside it
`Lara/Context/Equivalence.lean` gained the projection layer, which turned the
*proofs* of `obs_eq_of_ok` and `backend_replacement_congruence` into one-line
corollaries. Neither edit changes what any existing theorem says.

### The generalization lattice

```
Semantics.observe sem            (M2a, framework level: an AF and a Grounded.Claim)
          |
          |  read off an erased carrier (Invariants.eraseAF)
          v
Invariants.status canon   ---generalized by--->  Invariants.observeSem sem canon
          |                                              |
          |  read off the *linked* carrier of a context + fragment
          v                                              v
Lara.Context.obs          ---generalized by--->  Lara.Context.obsSem sem
          |                                              |
          |  quantify over all contexts
          v                                              v
Lara.Context.CtxEquiv     ---generalized by--->  Lara.Context.CtxEquivSem sem
```

Each arrow is witnessed by a theorem — `observeSem_grounded`, `obsSem_grounded`,
`ctxEquivSem_grounded_iff` — and each arrow goes one way only. §4 is the boundary
that says what the arrows do *not* license.

---

## 2. The projection is what is parameterized, and why that matters

The obvious implementation duplicates `Observation` and `obs` into a
semantics-aware copy and re-runs the four congruence proofs on the copy. That was
the first draft and it was rejected in eng review. What is parameterized instead
is the **projection**:

```lean
def obsGen {α : Type} (g : Invariants.StructuredAF → Atom → α) {canon : String → String}
    (reg : BackendRegistry canon) (C : Context) (F : Fragment) : ObservationOf α
```

`obs` is `obsGen` at `g := Invariants.status canon`; `obsSem sem` is *defined* as
`obsGen (Invariants.observeSem sem canon)`. The congruence is then proved once,
in `obsGen_congr`, and each of the four semantics-parametric congruences is a
one-line instantiation of it.

This is not only economy. Proving the congruence for an arbitrary `g` states, as
a theorem rather than as a remark, the fact §3 explains: the congruence was never
a fact about the grounded labelling. A development that copied the proof four
times would have the same theorems and would leave that fact as a comment.

### Why the projection layer sits in the grounded modules

`obsGen` mentions no semantics and needs no import `Equivalence.lean` did not
already have. It is therefore placed **beside the theorems it generalizes**,
not beside the semantics that instantiate it, and the payload-generic
`ObservationOf α` replaced `Fragment.lean`'s three-armed `Observation` inductive
rather than being introduced as a second type next to it. Two things follow, and
neither is available under the alternative:

1. **`obs` is `obsGen` at the grounded projection — as a theorem, by `rfl`.**
   The sentence "`obs` is `obsGen` at `g := Invariants.status canon`" is the
   design premise of this whole milestone, and with two distinct result types it
   could only be *asserted in prose*: `obs : Observation` and `obsGen g : Outcome
   α` are not comparable, so no equation between them typechecks. With one type
   the premise is `Lara.Context.obs_eq_obsGen`, and it closes by `rfl`. A design
   premise that the kernel checks is worth more than one a reader has to take on
   trust.
2. **The grounded theorems are corollaries, not copies.** `obs_eq_of_ok` is
   `obsGen_eq_of_ok _ hlink h` and `backend_replacement_congruence` is
   `obsGen_congr _ hf hpres hadm hfix`, each a single line. Under the two-type
   design `obsGen_congr` was `backend_replacement_congruence`'s proof transcribed
   with `Invariants.status canon` replaced by `g` — the same `obtain`/`rw`/
   `congrArg` script standing twice in the tree, so that a change to the
   argument would have had to be made in both places or silently hold in only
   one.

The cost is that this is not a purely additive change: `Fragment.lean` and
`Equivalence.lean` are edited. No existing statement moves — every grounded
theorem keeps its name, its type and its implicit-argument order, and
`Examples/Linking.lean`'s `congruence_witness` and `registry_swap_witness`
compile unchanged, which is the load-bearing check that it did.

### Why `liftObservation` still exists

Unifying the container did **not** remove `liftObservation`, because the two
*payloads* still differ. `obsSem groundedSem reg C F` lives in
`ObservationOf ClaimObservation` while `obs reg C F` lives in
`ObservationOf Grounded.Status`, so the statement "the grounded instance is the
old observation" is still not an equation between them as they stand.
`liftObservation` is the injection that makes them comparable and
`liftObservation_inj` is what the forward direction of §3's `iff` needs. It is
bookkeeping forced by `Grounded.Status` against `ClaimObservation` — not by the
container, which is now shared — and it carries no mathematical content beyond
the injectivity of `List.map` over a constructor. Recording that here so it is
not mistaken for a design element.

---

## 3. Why the congruence needed no new hypotheses

This is the finding most worth recording, because the issue's own cost estimate
expected otherwise.

Every M4 congruence funnels through one carrier-equality lemma:

```lean
-- lean/Lara/Context/Equivalence.lean:723
theorem compileUnit_link_relabel … : Invariants.compileUnit acc₂ = Invariants.compileUnit acc₁
```

Its conclusion is an **equation between carriers**, not a pointwise agreement
between them. Once the two sides meet at a single `G : StructuredAF`, the
projection hanging off it is applied to the same argument on both branches, so it
cannot distinguish them — whatever the projection is:

```
   reg₁, F                                  reg₂, mapAssurFrag f F
      |                                              |
      | linkedUnit + checkUnit                       | linkedUnit + checkUnit
      v                                              v
   .ok acc₁                                       .ok acc₂
      \                                              /
       \______ compileUnit_link_relabel _____________/
                            |
                            v
                  one carrier  G : StructuredAF
                            |
                            |  F.exports.map (fun p => g G p)   -- any g whatsoever
                            v
                      ObservationOf.observed …
```

So `obsGen_congr` is `backend_replacement_congruence`'s proof with
`Invariants.status canon` replaced by `g`, and — the point — with **no new
hypothesis**. In particular there is no `AttackExtensional sem.spec`.

That absence is load-bearing, not incidental. `Lara.Observation.observe_congr`
(`lean/Lara/Observation.lean:406`) *does* assume `AttackExtensional`, but it is
solving a different problem: it moves an observation between two **distinct**
frameworks that merely agree pointwise on the carrier, and extensionality is what
licenses concluding the extensions agree. Here the frameworks are equal, so no
such licence is needed. A generic result that assumed `AttackExtensional` anyway
would be **strictly weaker** than its grounded ancestor
`backend_replacement_congruence`, which assumes nothing of the kind, and would
not deserve to be called its generalization. A reader who expects the generic
version to be harder should be told why it is not.

The admissibility hypothesis is inherited unchanged and is not removable, for the
reason `docs/theory-m4-contextual-adequacy.md` §3 gives: `obsGen` records a
checker rejection separately from an observed list, and a forward-only acceptance
hypothesis lets `reg₂` accept what `reg₁` rejects.

### The `Nodup` obligation discharges unconditionally

`ExtensionSemantics.sound` and `Semantics.observe_grounded` carry `F.args.Nodup`.
In `observeSem_grounded` the framework is `Invariants.eraseAF F`, whose carrier is
`List.range F.size` **by definition**, so `List.nodup_range` closes the obligation
outright and it never reaches the statement. This is the same discharge
`Lara.Observation` already makes three times against `Compile.toAF`'s carrier —
see the note at `lean/Lara/Observation.lean:545` and the uses at `:666`, `:677`,
`:721`. It is a property of the frozen erasure, not a convenience: every carrier
this development observes is positional, so duplicate arguments are not
representable.

---

## 4. The grounded regression is a coincidence of relations, not an implication

```lean
theorem ctxEquivSem_grounded_iff (reg) (F₁ F₂) :
    CtxEquivSem groundedSem reg F₁ F₂ ↔ CtxEquiv reg F₁ F₂
```

It is an `iff`, in both directions, so grounded generic equivalence and M4's
`CtxEquiv` are **the same relation**. Nothing M4 states about `CtxEquiv` is
weakened, strengthened, or otherwise disturbed by this milestone's existence.

Read the scope narrowly. This settles the **grounded instance** and nothing else.
It does not say — and must not be cited as saying — that `CtxEquiv reg F₁ F₂`
implies `CtxEquivSem sem reg F₁ F₂` at any other semantics.

### The boundary: function witnesses and the all-context counterexample

The separations this milestone proves are between observation **functions** at a
concrete context and fragment:

* `obsSem_cycle_stable_ne_grounded` — on a linked three-cycle, `stableSem`
  observes `ClaimObservation.noExtension` while `groundedSem` observes
  `contested`;
* `obsSem_sink_preferred_ne_grounded` — on a linked sink, `groundedSem` observes
  `contested` and `preferredSem` observes `defeated`.

Those witnesses do **not** separate the observation **relations**. A relation
counterexample requires two fragments grounded-equivalent in *every* context,
not just one grounded-indistinguishable fixture. The unbounded context quantifier
prevents the fixture-style `decide` proof; it is not an undecidability theorem.

Follow-up **#268** supplies the missing universal argument in
`Lara.Examples.ContextualSeparation`. The two fragments share every field except
the single exported atom. Both own leaf support, and the fixed policy permits no
attacks. Their link guards and checker inputs are identical, so every incompatible
or rejected observation agrees. For any accepted context, both exported atoms
have unattacked checked support and are grounded-justified. This proves
`grounded_ctxEquiv` over **all** contexts, including failing ones.

The adequate semantics family `singletonSem a` retains exactly the carrier
sublists equal to `[a]`. At a concrete accepted empty context, selecting one
supporting position distinguishes the exported atoms. The theorem
`singleton_not_ctxEquivSem` uses that context; `counterexample` packages the
existential witness and `grounded_does_not_imply_semantic` refutes the implication
quantified over arbitrary `ExtensionSemantics`.

**Scope:** the interface requires an adequate enumerator, not that its extensions
are complete, maximal, or invariant under argument renaming. The selector is a
valid instance of that interface. This refutes the unrestricted implication;
it does not prove separation at complete, preferred, stable, or semi-stable
semantics, nor an implication restricted to identical export lists. The current
`CtxEquiv` definition imposes no identical-exports premise. The grounded
instance still coincides by `ctxEquivSem_grounded_iff`.

What *is* known about `CtxEquivSem` beyond its definition:
`ctxEquivSem_negative` exhibits a pair it is false of at `stableSem` — a
non-grounded instance, so it is not merely `Linking.ctxEquiv_negative` transported
through the `iff`.

`ctxEquivSem_semantic_negative` strengthens the evidence requested in
[#273](https://github.com/ARA-Labs/lara/issues/273): an empty context distinguishes
`fullCycleFrag` from `singletonCycleFrag` under the same cyclic policy, with
identical exports `[pA]`. Both links pass the guard and whole-unit checker
(`semantic_negative_link_ok`, `semantic_negative_accepted`). The former reuses
#270's complete directed cycle; the latter supplies one unattacked argument.
`obsSem_semantic_negative` pins both outer constructors to `.observed`, with
payloads `noExtension` and `observed justified`, and proves their disequality.
`obsSem_semantic_negative_grounded` also pins the cycle's grounded payload to
`observed contested`, so the semantics choice matters at this witness. This
closes #273; the separate all-context argument above resolves the unrestricted
implication from #268.

The certificate-bearing instantiations requested in
[#269](https://github.com/ARA-Labs/lara/issues/269) are now proved as
`cert_congruence_witness_sem` and `cert_registry_swap_witness_sem`. The admissible disagreeing
carrier requested in [#270](https://github.com/ARA-Labs/lara/issues/270) is now
proved: `cycle_admissible` establishes `Admissible reg cycleCtx cycleFrag` for
every registry, and `congruence_witness_sem` uses it. §6 records the remaining
limitation.

---

## 5. Non-triviality: what the fixtures had to establish, and how

If the milestone had shipped only generic definitions plus a grounded regression,
a reviewer could ask the question that motivated #216 one level up: you
generalized the observation, but did you show the generalization observes
anything new?

There was no context-level fixture on which two semantics disagree.
`Examples.Linking`'s carriers are a two-node chain (`ctxEx`/`fragEx`) and a mutual
rebut observed at a singleton support (`symCtx`/`symFrag`), and all five semantics
agree on both — now stated as theorems rather than asserted, in
`obsSem_linking_agrees` and `obsSem_sym_agrees`, each listing all five instances
because `Examples.Semantics.allSemantics_complete` is what makes "all five" a
closed list.

So the fixtures were built. Both reuse the `Examples.Linking` vocabulary
(`sigmaEx`, `unitPolicyEx`, `registryEx`, the leaves `l1 l2 l3`, the patterns
`apA`, `apB`, and `Linking.apS`), changing only the `defeat` field, in the shape
`Linking.symPolicy` established. The split is forced by `SideOk.attack_complete`:
a side must declare an attack for every contrary pair among its **own** arguments,
while cross-boundary conflicts are saturated automatically by `crossAtts`. So the
pair needing a declared edge goes inside the fragment and the link supplies the
rest.

**The three-cycle** (`p ⊣ q`, `q ⊣ s`, `s ⊣ p`; context declares `q`, fragment
declares `p` and `s` and the `s ⊣ p` edge, exports `p`) is the sharper of the two.
`noExtension` is a constructor the grounded reading provably cannot reach:
`observeSem_grounded` always returns `ClaimObservation.observed _`, and
`liftObservation` only produces that constructor. So this does not merely show
`obsSem` taking two values — it shows `obsSem` inhabiting an arm of
`ObservationOf ClaimObservation` that `liftObservation ∘ obs` cannot inhabit. The
widening of the observed payload from `Grounded.Status` to `ClaimObservation` is
therefore forced by a fixture of this development, not only by
`Semantics.observe`'s signature.

**The sink** (`p ⊣ q`, `q ⊣ p`, both attacking `s`; fragment exports `s`) answers
the sceptic who grants the `noExtension` arm and argues that whenever both
semantics *do* answer they answer the same. Neither side reports `noExtension`;
both answer, and they disagree. It is also why reusing `symPolicy` would not have
worked: there the observed claim is supported by a node *inside* the two-cycle, so
the skeptical reading is `contested` under every semantics. The sink observes a
node *outside* the cycle that every preferred extension attacks, and that
asymmetry is what the separation needs.

Each separation carries a **disequality conjunct**, so a future collapse of a
fixture is a build failure rather than a silent regression of two values that
happen to be pinned separately. Both carriers are pinned first
(`cycle_link_ok`/`cycle_accepted`/`cycle_linked_shape` and the sink's
counterparts), so a fixture that stops linking is distinguishable from a
separation that collapsed.

### Machine checks standing in for human eyeballs

Three acceptance criteria that would otherwise be enforced by someone reading a
signature are enforced by the build instead:

* `ctxEquivSem_grounded_iff` must stay an `iff`.
  `ctxEquivSem_grounded_negative` consumes `.mp` and
  `ctxEquivSem_grounded_of_ctxEquiv` consumes `.mpr`, so weakening it in either
  direction breaks the build. Neither theorem claims new content; each exists to
  *consume* a direction.
* The separations must actually separate — the disequality conjuncts above.
* `obsSem_grounded` must be exercised, not merely stated. `obsSem_linking_grounded`
  derives the grounded reading of the M4 fixture *through* it and
  `Linking.obs_defeated`, rather than re-pinning the value by an independent
  `rfl`.

### Quantified where the ancestor is quantified

Three results are stated over an arbitrary `sem` rather than checked at
instances, because the theorems they instantiate are:

* `obsSem_gap_uniform` — `Semantics.observe_gap` is universally quantified over
  `sem` with no hypothesis on it, so a five-instance check would be strictly
  weaker than the theorem it claims to instantiate, and would say nothing about
  semantics nobody has written down. The proof runs `obsGen`'s case split and
  routes through `Invariants.observeSem_of_status_gap`, which is where the
  semantics-independence actually lives.
* `obsSem_incompatible_id_clash` and `obsSem_rejected_signature` — the link guard
  and the whole-unit checker both fire *before* any projection is consulted, which
  is the content of `obsGen_incompatible` / `obsGen_rejected`. `decide` cannot
  close a goal with a free `sem`, and the point is that there is nothing it needs
  to evaluate.

---

## 6. Congruence on the three-cycle and a certified fragment

`congruence_witness_sem` now instantiates the generic congruence on
`cycleCtx`/`cycleFrag`. `cycle_admissible` proves both sides well-formed against
any registry. The context has no internal contrary pair; the fragment's only
internal pair, `s ⊣ p`, is covered by its declared undermine attack. Support
uniqueness reduces attack completeness to the four pairs of fragment arguments.

This is the same carrier where `obsSem_cycle_stable_ne_grounded` separates the
observations: grounded reports `observed contested`, while stable reports
`noExtension`. Thus the congruence holds uniformly in `sem` at a carrier where
the choice of semantics changes the observed value. This closes #270.

`registry_swap_witness_sem` still uses the two-node `ctxEx`/`fragEx` chain,
where all five semantics agree. Its semantics quantifier remains inert.

The assurance-free caveat from `docs/theory-m4-contextual-adequacy.md` §1 still
applies to both witnesses: `cycleFrag` and `fragEx` carry no certificates, so
`mapAssurFrag f` is the identity on them for every `f`. Neither exercises a real
certificate replacement.

`cert_congruence_witness_sem` now instantiates
`backend_replacement_congruence_sem` on `Linking.certCtx`/`certFrag` with
`certSwap` and `registryWrapped`. It reuses `certSwap_injective`,
`certSwap_preserving`, `certAdmissible`, and the grounded witness's fixed-context
proof unchanged. In particular, the certificate-dependent admissibility proof
transfers directly: it requires no premise about semantics.
`Linking.cert_relabel_moves` proves this relabel actually changes the fragment.

`cert_registry_swap_witness_sem` instantiates `registry_swap_congruence_sem` on
the same certified carrier, from `registryEx` to `registryPlus`, using the
same global assurance-preservation argument as `Linking.cert_registry_swap_witness`
and the same `certAdmissible`. This is the D6 form: the certificate stays
unchanged while the registry accepts strictly more.

Both theorems quantify over arbitrary `sem : ExtensionSemantics` and are pinned
in `AxCheck.lean`. This closes #269's certificate-bearing witness gap. It does
not establish that the semantics quantifier is non-inert at this certified
carrier; the three-cycle supplies semantics separation separately.

---

## 7. Paper claim boundary

### May claim

- The contextual representation-independence result holds **under every extension
  semantics in the M2a interface**, with the admissibility and `FixesContext`
  hypotheses named exactly as the grounded version requires them
  (`backend_replacement_congruence_sem`); likewise the acceptance-profile form
  (`registry_swap_congruence_sem`, whose hypothesis is **global**, not restricted
  to the fragment's certificate occurrences), the composed form
  (`backend_replacement_congruence_composed_sem`), and the whole-program form
  (`whole_program_replacement_sem`).
- The congruence requires **no additional hypothesis** at the generic instance —
  in particular no `AttackExtensional` — because it transports along carrier
  equality rather than pointwise attack agreement (§3).
- The generalization is **non-trivial**: two context-level separations, one of
  which reaches an observation arm the grounded reading cannot reach
  (`obsSem_cycle_stable_ne_grounded`, `obsSem_sink_preferred_ne_grounded`).
- The grounded case is **recovered as a theorem**, not by editing the grounded
  definitions, and the relational form is an `iff`
  (`obsSem_grounded`, `ctxEquivSem_grounded_iff`).
- `gap` is semantics-independent at the context level, quantified over `sem`
  (`obsSem_gap_uniform`).

### Must not claim

- **Not parametricity over arbitrary relations.** All four functional
  congruences now have relational companions in
  `lean/Lara/Context/Parametricity.lean` (#215, #277):

  | Functional theorem | Relational companion |
  |---|---|
  | `backend_replacement_congruence_sem` | `backend_replacement_parametricity_sem` |
  | `registry_swap_congruence_sem` | `backend_replacement_parametricity_local_sem` |
  | `backend_replacement_congruence_composed_sem` | `backend_replacement_parametricity_composed_sem` |
  | `whole_program_replacement_sem` | `whole_program_parametricity_sem` |

  `RelInj` still restricts the relation to a partial bijection. The
  fragment-local registry companion remains a trade: it weakens acceptance to
  `occurrences F` but adds the two context-containment hypotheses. The new
  `whole_program_parametricity_local_sem` instead obliges acceptance on
  `closedOccurrences C F`, the union of both sides, without containment.
  The checked-program companion uses `checkedAF_rel` without `Admissible` or
  `RelPreserving`, preserving the original whole-program contract; the composed
  and closed-link companions factor through `obsGen_parametricity`.
  See `docs/theory-m4-relational-parametricity.md` §8 for this distinction.
  Remaining work: **#275** (observational `RelInj` witness) and **#279**
  (the total-injective-extension step).
- **Not full abstraction.** No logical relation. M4 Part B was descoped on
  2026-09-03 (`docs/theory-m4-contextual-adequacy.md` §7), so the issue's `LogRel`
  conjunct is vacuous and was not attempted.
- **The relation counterexample has an explicit scope.** #268 refutes grounded
  equivalence implying equivalence at *every* `ExtensionSemantics`, using the
  adequate singleton-selector family and an all-context grounded proof (§4).
  It makes no separation claim for the four standard non-grounded semantics.
- **Not a single witness combining a genuine certificate relabel with semantics
  separation.** The certified witnesses exercise a real certificate uniformly
  in `sem`; the three-cycle exercises semantics separation with bare leaves (§6).
- **Not a runtime consequence.** The Haskell evaluator stays grounded; this
  milestone moves no conformance vector, no corpus, and no performance number.

---

## 8. Verification

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd lean && lake build
python3 scripts/check-axcheck-coverage.py lean/AxCheck.lean \
  lean/Lara/Invariants/Observation.lean lean/Lara/Context/Observation.lean \
  lean/Lara/Examples/ContextSemantics.lean
(cd lean && set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
```

Results on the landing commit:

* `lake build` — 154 jobs, exit 0. All three new modules produce oleans under
  `lean/.lake/build/lib/lean/`, which is the #259 failure mode checked by hand
  until that issue lands.
* Coverage — passed, **37 declarations** pinned in `AxCheck.lean` (3 in
  `Invariants.Observation`, 15 in `Context.Observation`, 19 in
  `Examples.ContextSemantics`).
* Axiom audit — passed. Every new declaration is inside
  `{propext, Classical.choice, Quot.sound}`. No `sorryAx`, so no `sorry`
  survived; no `Lean.ofReduceBool`, so no `native_decide` survived. Every fixture
  closes by `decide`, `rfl`, or a term proof.
