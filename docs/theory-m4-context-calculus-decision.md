# Theory M4 phase F0: the frozen context calculus

_Status: frozen on 2026-09-02 for Theory M4, phase
F0 of the since-deleted plan
`plans/2026-09-02-theory-m4-full-abstraction.md`. This document records
what F0 froze, why each choice is forced by the existing carrier rather than
chosen for convenience, what F0 deliberately did not do, and the gate outcome
that releases the theorem phases._

The theorem this milestone aims at, in plain terms: relabeling how a backend
marks its certificates — without changing what it accepts — cannot be
observed by any surrounding program; no admissible context can tell the
original fragment and the relabeled one apart.

F0 is a design freeze, not a theorem phase. Its deliverable is a set of
**compiling Lean definitions** (`lean/Lara/Context/Fragment.lean`) plus this
record. Nothing here is proved; the obligations these definitions create are
discharged in F1 (`Lara.Context.Link`, `Lara.Context.Compose`) and F2
(`Lara.Context.Equivalence`).

## 1. What the milestone claims, and what it does not

Part A — committed — proves **contextual representation independence**: an
injective, acceptance-preserving relabel of a fragment's certificates is
unobservable in every admissible context whose own assurances the relabel
fixes. That is the statement `docs/theory-m3-source-updates.md` §"Scope and
Verification" deferred to M4. It **extends result 9 along the context
quantifier**, but the statements are incomparable: `Lara.Erase.backend_replacement`
ranges over arbitrary checked whole programs and carries no admissibility
hypothesis, while the congruence ranges over admissible fragment contexts.

It is **not** parametricity, and the paper must not call it that: per M4's
acceptance criterion, "parametricity" is reserved for a relational
quantification over related backends, which is the relational-parametricity
record's future work. It is
also not full abstraction — no logical relation is defined in Part A (D5).

Part B — full abstraction — is optional and separately gated. Section 7 records
the two obstructions that keep it uncommitted.

## 2. The carrier, and why each field exists

`Lara.Context.Fragment` carries `sigma`, `policy`, `gammaFrag`, `ground`,
`args`, `atts`, `imports`, `exports`. Every field is forced by something in the
frozen core:

| Field | Forced by |
|---|---|
| `sigma`, `policy` | Both are `Lara.Unit` fields, and R-L3 must retain the two disagreeing values, so they are compared structurally at the guard (§3). |
| `gammaFrag` | `Lara.Unit` has **no Γ field**; Γ indexes `Unit.CheckedUnit`. Γ is what the two sides contribute, so `link` returns `Lara.Unit × (LeafId → Option Atom)` and builds Γ with `Admission.buildGamma` (D2). |
| `ground` | `Check.Unit.checkUnit` takes a `ground : List Atom` and sorts it (`Lara.groundWellSorted`, `Check/Unit.lean:132`). A fragment that contributed arguments but no ground atoms could not be checked. |
| `args`, `atts` | The declared material `Compile.CheckedProgram` is built from. |
| `imports` | Leaf-name openness (D12, §6). |
| `exports` | Observable **conclusions**, not pinned claims (D4, §5). |

`Lara.Context.Context` wraps one `Fragment` as the material surrounding the
hole. Contexts are fragment-shaped on purpose: it is what makes `compose`
(D11) definable, and congruence is unstateable without composition.

**Fixed across linking: `canon`, Σ, the policy (including `defeat`), and the
backend registry.** Σ and the policy are fragment fields and their agreement is
enforced by the guard. `canon` and the registry are *parameters* of `link`,
`crossAtts`, `fragmentAF`, and `obs` — a context is data, not a checker
invocation, so it cannot supply a different registry, and "registry mismatch"
is unrepresentable rather than rejected. Γ is **not** fixed: it is exactly what
the two sides contribute, and `Lara.Update`'s Γ-extension transport
(`Lara/Update.lean:281-286`) carries derivations into the linked Γ.

## 3. Rejection classes (D3)

`linkOk` is decidable and total: it is the `isNone` projection of named fault
functions returning `Option LinkFault`. Each one-sided fault retains its side
and leaf, and each R-L3 fault retains both disagreeing values. F1 can therefore
give each function its own characterization lemma (the
`Policy.firstDuplicateRuleId?_none_iff` pattern) rather than forcing proofs
through `decide` over a pair scan. `native_decide` is banned (D9).

| Class | Component | Behavior |
|---|---|---|
| R-L1 duplicate or shared identifier | `idHygieneFault` via `firstDup?` / `firstShared?` | reject with side/identifier |
| R-L2 unsatisfied import | `firstMissing?` | reject with importing side/identifier |
| R-L3 Σ / policy mismatch | `sigmaPolicyFault` | reject with both values |
| duplicate **support term** across the boundary | `dedupList` | **merge** |

The last row is the one that is not a rejection, and the reason is that
rejecting it would refute the theorem being proved. `SupportTerm` equality is
structural, so a context argument built only from imported leaf identifiers can
be structurally identical to a fragment argument — hygiene on *identifiers*
does not prevent term collision. If term collision rejected the link, then for
`F₁` containing a term `t ∉ F₂.args`, the context that declares `t` would link
with `F₂` and be rejected against `F₁`, so `F₁` and `F₂` would be
distinguishable by a context that reads nothing about them. Contextual
equivalence would collapse to term-set equality and no congruence coarser than
syntax could hold. Merging is semantically inert — identical terms have
identical edge sets (`Compile.lean:43-46`) — and F1 proves it status-preserving
rather than asserting it.

## 4. Saturation is forced, not chosen (D2)

`Compile.AttackComplete` (`Compile.lean:515`) is an **all-pairs** condition over
the declared arguments, and it is a *premise* of
`Check.Unit.checkUnit_complete` (`Check/Unit.lean:236`, premise at `:251`). A `link` that merely
concatenated `C.atts ++ F.atts` would leave every cross-boundary contrary
conflict uncovered, `hattackComplete` would be unsatisfiable on exactly the
interesting links, and the calculus would only ever accept programs whose two
halves cannot interact. So `link` emits `crossAtts`.

`crossAtts` enumerates the cross pairs whose cached conclusions satisfy
`Attack.contraryMatchB` onto a `Compile.conflictAttackableB` target, in both
directions, and emits one attack per pair in the shape the target admits:

* a `.leaf` target is **undermined** at the root position — `HasAttack.undermine`
  reads `Gamma l`, which the linked Γ supplies;
* an `.inst` target is **rebutted** — `HasAttack.rebut` reads the root rule's
  instantiated conclusion, which `Support.InstSide.concl` supplies, and
  requires `r.mode = .defeasible`, which is exactly what
  `conflictAttackableB` returns true on for an instance.

Both shapes place the attacked occurrence at the target itself, so
`Compile.Covered` holds through `Compile.contains_refl`.

A consequence worth stating plainly, because Part B's constructions depend on
it: **a context cannot withhold a cross-boundary attack.** If a context
argument's conclusion contrary-matches an attackable fragment occurrence, the
link emits the edge whether or not the context "wants" it. Contexts are less
free than they look.

### The conclusion cache, and one thing it is not

`link` runs *before* checking, so it cannot read conclusions off
`Unit.CheckedUnit.nodes` — that cache exists only once the linked program has
been accepted. `Lara.Context.conclusionCache` therefore infers conclusions with
the checker's own `Check.inferSupport`, whose `inferSupport_sound` /
`inferSupport_complete` pair (`Check/SupportProof.lean:380,509`) makes the cache
exactly the graph of `HasSupport … w C []` on the terms that have one.

`Lara.Context.conclusionCache` and `Lara.Check.conflictCache` compute the same
idea at two different times — before checking under the hypothetical linked Γ,
and after acceptance off `CheckedUnit.nodes` — and F0 left their agreement as a
forward-looking obligation (the **cache-agreement bridge**). F1 did not need it —
`mem_conclusionCache` and `conclusionCache_sound` are the inverses the
saturation proofs consume — and the M4 debt clearance closed it: on any
accepted unit the inferred cache over the program's arguments *is* the
`(term, conclusion)` projection of the conflict cache
(`Context.conclusionCache_eq_conflictCache`, via
`Check.conflictCache_conclusions`), and on an accepted link each side's
saturation cache is the restriction of the checker's cache to that side's
arguments (`Context.link_cache_bridge`). The saturation `link` performs is the
one the checker would have computed.

## 5. Observation: exports are conclusions (D4)

`Grounded.Claim` holds argument *positions*, not a proposition, and `statusC`
returns `gap` exactly when the complete support list is empty
(`Grounded.statusC_gap_iff`). So a claim pinned at fragment-definition time
would be blind to the most characteristic thing a context does: **supply
support for an exported conclusion and flip its status out of `gap`.** Exports
are therefore `List Atom`, and `obs` rebuilds the claim from the *linked*
program's checked-node cache, through the M1 carrier
(`Invariants.compileUnit` / `Invariants.status`), whose `status_compileUnit`
already ties that reading back to `Grounded.statusC (Compile.checkedAF …)`.

Grounded only. Generalizing the observation to an arbitrary
`Semantics.ExtensionSemantics` is deliberately out of scope: M2a's
`not_observe_congr_of_unbounded_support` shows observation transport fails
without carrier-boundedness, and importing that discipline generically would
enlarge M4 rather than close it.

## 6. Original D12: leaf-name openness

`docs/theory-m3-source-updates.md` names "holes" among the retained
obligations. A **term-level** hole — an argument with unresolved
critical-question obligations (`HasSupport … w C O`, `O ≠ []`) discharged by
the context — is unrepresentable in this calculus, and not by choice:
`Compile.CheckedProgram.complete` (`Compile.lean:480`) forces `O = []` on every
declared argument, and discharges live *inside* the term (`D : List (QuestionId
× SupportTerm)`), not in a name environment a context could extend.
`Grounded.Claim.holes` is likewise never read by the observation of §5.

Consequence for the original closeout: M3's contextual-adequacy debt was
discharged **partially**, with term-level holes retained.

**Follow-up:** the additive `Lara.Context.Holes` layer now represents
named CQ-answer templates and proves typed substitution before this complete
program boundary. It preserves D12's original calculus through a closed
embedding; it does not weaken `CheckedProgram.complete`. See
`docs/theory-term-level-holes.md` for source erasure, typed fillings, attack
instantiation, composition, and backend transport. The separately gated
full-abstraction work remains outside this result.

Consequence for the carrier: an open fragment has **no** `CheckedProgram`
(D10). A fragment mentioning an imported leaf has no `HasSupport` derivation
until the environment supplies it. Everything said about a fragment *alone*
therefore goes through `fragmentAF : … → Fragment → ImportEnv → List Atom →
Option Grounded.AF`. "Checked fragment" always means *relative to an import
environment*.

`Realizability.Realizable` is explicitly **not** the construction target for
any later phase: its `compiled_iso` (`Lara/Realizability.lean:167`) targets a
*given* `StructuredAF`, which in a context construction is precisely the
unknown.

## 7. Why Part B is gated separately

Two obstructions are visible in the frozen core, before any Part B work starts.

**(1) The semantic interface is wider than the declared imports.**
`AttackComplete` is all-pairs and `Compile.Covered` closes under subarguments,
so a context can attack *any* fragment argument whose conclusion
contrary-matches an attackable occurrence — declared import or not. And
grounded labelling is a fixpoint over the *linked* AF, so a non-exported
boundary argument feeds back into an export. A logical relation stated over the
declared imports is therefore refuted on both sides. A relation stated over the
full contrary-visible occurrence profile is not refuted, but risks collapsing
into a generalized `Erase.mapAssur` — the tautology trap arriving through the
interface rather than through the quantifier. Which of those two it is, is the
question Part B's entry gate exists to answer.

**(2) Completeness is policy-conditional.** Under `emptyDefeat` no attack
types at all, every compiled AF is edgeless, and no context can force an import
label — so a `logrel_complete` without a hypothesis is *false*. It is worse
than that degenerate case: `Compile.ConflictAttackable` is unconditionally
`True` on leaves (`Compile.lean:407`) while `HasAttack.rebut` requires
`r.mode = .defeasible` (`Lara/Attack.lean:550`), so a purely symmetric contrary
table can force only `{in, undec}`. Contraries are also *patterns* with
universally quantified variables (`Lara/Attack.lean:85`), so a "fresh" atom on the
same predicate still matches and causes collateral attacks.

**`LabelExpressive` (sketch only — defined and discharged in Part B, if Part B
runs).** The completeness hypothesis belongs on the **policy**, not on the
context quantifier: the policy must supply, for the atoms a forcing gadget
uses, either an asymmetric contrary pair or a strict-rooted attacker, relative
to atoms unused by both fragments. Intended positive witness: `m2bPolicy`'s
asymmetry (`Complexity/Context.lean:148,177` — `d_attacks_b` with
`b_does_not_attack_d`). Intended negative witness: `emptyDefeat`, seeded by
`Examples/Realizability.lean:80` (`oneSelfEdge_not_realizable`).

Neither obstruction touches Part A: a uniform relabel preserves the whole
occurrence profile, so Part A never has to answer "what is the semantic
interface".

## 8. Checks recorded at F0

**Blocked-by check (possible worlds).** M4 is blocked by the PW wrapper spike
only *if* possible-world observations become observable program behavior. They
have not. PW0 and PW-T6 have since landed, and
`docs/theory-pw0-outer-model.md` states the boundary explicitly: PW "adds an
outer comparison layer over **unchanged** local Lara judgments. No local
checking, compilation, grounded labelling, or status behavior was redefined."
The observation vocabulary M4 quantifies over is the M2a claim-status interface
(`Grounded.statusC` through `Invariants.status`), which PW does not touch. M4
is not blocked.

**D1 — the plan ordering.** The theory-depth plan orders "M5 defines the
surface calculus before M4 quantifies over source contexts". F0 reads that as
satisfied by a surface *corollary*: contexts live at the core `Lara.Unit` level,
and M5's preservation/reflection supplies the transport statement at F3.
Quantifying primarily over surface contexts would entangle the congruence with
M5's elaboration guards for no gain in strength.

**D8 — no Haskell conformance vector.** M4 adds no checker, CLI, wire, or
corpus surface. `link` is a Lean-side operation with no surface syntax, so a
`lara check` vector would have to hand-write an already-linked program — which
tests the checker, not the calculus. None required. No corpus regeneration, no
freeze-tag bump; `docs/performance.md`'s numbers cannot move because no Haskell
code changes.

**Precedent consulted.** The argumentation literature's input/output and
decomposability analysis — Baroni, Boella, Cerutti, Giacomin, van der Torre,
Villata, *On the input/output behavior of argumentation frameworks*, Artificial
Intelligence 217 (2014) 144–197 — is the closest prior art for the question
"is a fragment's behavior in every context determined by an interface
summary?", and it is read here as **design guidance only**. Nothing from it is
cited as a proof substitute: every statement M4 makes is re-proved over this
development's own carrier, whose arguments are structured support terms with
certificate-bearing assurances rather than abstract nodes, and whose edges are
generated by a checker rather than given.

## 9. What F0 deliberately did not do

- No theorems. Not one. F0's Lean is definitions that compile.
- No `AxCheck.lean` entries — there is nothing to audit yet.
- No `Examples/Context.lean`. Witnesses land with the phase whose theorems they
  make non-vacuous.
- No `LogRel`, no `LabelExpressive` definition (§7 is a sketch, on purpose).

## 10. Deferrals recorded here (all discharged)

Both F0 deferrals were closed by the M4 debt clearance that followed Part A;
they are kept here because the record explains *why* F0 chose to defer.

- **The `DecidableEq` instances** (closed) — the five `DecidableEq` instances R-L3 needs
  (`Support.Question`, `Support.Rule`, `Attack.DefeatPolicy`,
  `Policy.RuleDecl`, `Policy.Policy`) were derived at the head of
  `lean/Lara/Context/Fragment.lean` because M4 was additive to a frozen core.
  They now live as `deriving DecidableEq` clauses on the structures themselves,
  so visibility no longer depends on the import path.
- **The cache-agreement bridge** (closed) — §4: proved as
  `Context.conclusionCache_eq_conflictCache` and `Context.link_cache_bridge`.

## 11. Gate

**PROCEED.** The F0 definitions compile, and the three obligations F1 must
discharge each have an identified route through existing machinery:

- `link_attackComplete` — `contraryMatchB_iff` (`Lara/Attack.lean:506`) and
  `conflictAttackableB_iff` (`Compile.lean:420`) invert the two Boolean guards;
  `inferSupport_complete` puts every complete argument in the cache, so no
  forced pair is missed.
- typing of the emitted attacks — `HasAttack.rebut` from
  `InstSide.rule`/`InstSide.concl` plus the defeasibility that
  `conflictAttackableB` returns; `HasAttack.undermine` from the leaf case of
  `HasSupport`, whose Γ lookup the linked Γ supplies.
- `link_checked` — `Check.Unit.checkUnit_complete`, with `hargs` from
  `dedup`'s `Nodup` and `hsource`/`htarget` from cache membership being
  argument membership.

Neither RESHAPE nor STOP is warranted: nothing in the audit contradicts the
plan's Part A shape, and the Part A/Part B split already absorbs the risk that
Part B is unreachable.
