# Generic-`ExtensionSemantics` Contextual Observation (issue #216)

**Landed 2026-09-07.** Lean-only, purely additive. No corpus regeneration, no
freeze-tag bump, no Haskell change — the runtime evaluator stays grounded, per
`lean/Lara.lean`'s M2a index entry.

Modules: `lean/Lara/Invariants/Observation.lean`,
`lean/Lara/Context/Observation.lean`, `lean/Lara/Examples/ContextSemantics.lean`.

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
| `Context.Outcome α`, `Context.obsGen` | `Lara/Context/Observation.lean` | `Observation`/`obs` with the *projection* left open |
| `Context.obsGen_congr` | ″ | contextual representation independence, for every projection at once |
| `Context.obsSem`, `Context.CtxEquivSem` | ″ | the semantics-parametric instances |
| `Context.obsSem_grounded`, `ctxEquivSem_grounded_iff` | ″ | the grounded regressions |
| `backend_replacement_congruence_sem`, `registry_swap_congruence_sem`, `backend_replacement_congruence_composed_sem`, `whole_program_replacement_sem` | ″ | the four M4 congruences at an arbitrary `sem` |
| `Examples.ContextSemantics.*` | `Lara/Examples/ContextSemantics.lean` | the fixtures that make the parameter non-trivial at the context level |

Every existing declaration is untouched. `Lara/Context/Fragment.lean`,
`Lara/Context/Equivalence.lean`, `Lara/Invariants.lean`, `Lara/Observation.lean`,
`Lara/Semantics.lean` and `Lara/Grounded.lean` are byte-for-byte unchanged on
this branch; the only edits outside the three new modules are import lines and
the M4 index comment in `lean/Lara.lean`, and the pin block in `lean/AxCheck.lean`.

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
    (reg : BackendRegistry canon) (C : Context) (F : Fragment) : Outcome α
```

`obs` is `obsGen` at `g := Invariants.status canon`; `obsSem sem` is *defined* as
`obsGen (Invariants.observeSem sem canon)`. The congruence is then proved once,
in `obsGen_congr`, and each of the four semantics-parametric congruences is a
one-line instantiation of it.

This is not only economy. Proving the congruence for an arbitrary `g` states, as
a theorem rather than as a remark, the fact §3 explains: the congruence was never
a fact about the grounded labelling. A development that copied the proof four
times would have the same theorems and would leave that fact as a comment.

The one piece of machinery the redesign did **not** remove is `liftObservation`.
`obsSem groundedSem reg C F` lives in `Outcome ClaimObservation` while
`obs reg C F` lives in `Observation`, so the statement "the grounded instance is
the old observation" cannot be an equation between them as they stand.
`liftObservation` is the injection that makes them comparable and
`liftObservation_inj` is what the forward direction of §3's `iff` needs. It is
bookkeeping forced by the two result types and carries no mathematical content
beyond the injectivity of `List.map` over a constructor. Recording that here so
it is not mistaken for a design element.

---

## 3. Why the congruence needed no new hypotheses

This is the finding most worth recording, because the issue's own cost estimate
expected otherwise.

Every M4 congruence funnels through one carrier-equality lemma:

```lean
-- lean/Lara/Context/Equivalence.lean:586
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
                      Outcome.observed …
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

### The boundary: functions separate, relations are open

The separations this milestone proves are between observation **functions** at a
concrete context and fragment:

* `obsSem_cycle_stable_ne_grounded` — on a linked three-cycle, `stableSem`
  observes `ClaimObservation.noExtension` while `groundedSem` observes
  `contested`;
* `obsSem_sink_preferred_ne_grounded` — on a linked sink, `groundedSem` observes
  `contested` and `preferredSem` observes `defeated`.

They do **not** separate the observation **relations**. `CtxEquiv` quantifies over
*all* contexts, so neither `CtxEquiv reg F₁ F₂ → CtxEquivSem sem reg F₁ F₂` nor
its refutation is reachable by `decide`: refuting it needs two fragments provably
grounded-equivalent in *every* context, which is a universally quantified argument
over an unbounded context space, not a fixture. Whether the implication holds is
**not proved and not refuted** here. It is filed as
[#268](https://github.com/ARA-Labs/lara/issues/268).

What *is* known about `CtxEquivSem` beyond its definition:
`ctxEquivSem_negative` exhibits a pair it is false of at `stableSem` — a
non-grounded instance, so it is not merely `Linking.ctxEquiv_negative` transported
through the `iff`.

Also open, and filed:
[#269](https://github.com/ARA-Labs/lara/issues/269) (instantiate the generic
congruence on the certificate-bearing `certCtx`/`certFrag` pair) and
[#270](https://github.com/ARA-Labs/lara/issues/270) (prove
`Admissible registryEx cycleCtx cycleFrag`, so the congruence witness sits at a
carrier where the semantics parameter is not inert). §6 explains why those two
gaps matter.

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
`Outcome ClaimObservation` that `liftObservation ∘ obs` cannot inhabit. The
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

## 6. The limitation the witnesses carry

`congruence_witness_sem` and `registry_swap_witness_sem` establish that the
headline's hypotheses are inhabited and its conclusion provable at a concrete
link, uniformly in `sem`. They establish nothing more, and the modules say so.

The `sem` quantifier is **inert** at their carrier: `ctxEx`/`fragEx` is the
two-node chain on which all five semantics agree, so those theorems would be
equally provable if `ExtensionSemantics` had one inhabitant. The theorems that
make the parameter non-trivial are the two separations, not these.

The assurance-free caveat that `docs/theory-m4-contextual-adequacy.md` §1 records
for `Linking.congruence_witness` applies unchanged: `fragEx` carries no
certificate, so `mapAssurFrag f` is the identity on it for *every* `f`. These are
shape witnesses. The fixture that exercises a real backend swap is
`Linking.cert_congruence_witness`, and it is grounded-only; no
semantics-parametric counterpart of it is claimed. Both gaps are filed —
#269 for the certificate-bearing instantiation, #270 for an admissible
disagreeing carrier.

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

- **Not parametricity.** No relational quantification over related backends;
  that is issue **#215**, untouched here.
- **Not full abstraction.** No logical relation. M4 Part B was descoped on
  2026-09-03 (`docs/theory-m4-contextual-adequacy.md` §7), so the issue's `LogRel`
  conjunct is vacuous and was not attempted.
- **Not a claim that the equivalence *relations* separate or coincide at any
  non-grounded instance.** The separations are between observation functions at a
  concrete context and fragment (§4). The natural reading of
  "semantics-parametric contextual equivalence" as a statement about the relations
  is exactly what is **not** proved — #268.
- **Not a claim that the congruence witnesses exercise the semantics parameter.**
  They sit at a carrier where it is inert (§6).
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
