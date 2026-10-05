# Located-gap decision record (`lara-core@0.3`)

_Status: frozen core contract, 2026-10-04. This record moves the core from
`lara-core@0.2` to `lara-core@0.3`. It changes which units are accepted, adds
one optional section to the verdict grammar, and changes the replay identity.
It does not change the four core statuses, the grounded labelling, support-term
typing (spec §6.1), attack typing (spec §7.1), or any R-class or named kind
other than retiring the named `incomplete-argument` kind. `docs/spec.md` §4.3, §4.4, §8, §10 and §10.1
state the normative rules; this record keeps the reasons and the rejected
alternatives. Amended 2026-10-05 by D12, before `@0.3` shipped: hole rows
locate each obligation at its rule occurrences._

Background for cold readers: an *argument* is a declared support term for a
claim. A defeasible step must answer each of its rule's *critical questions*,
either by discharging it with evidence or by leaving it explicitly *open*. An
open **mandatory** question is an unresolved obligation. Up to `lara-core@0.2`
a unit containing an argument with an unresolved obligation was rejected
whole; an author who could not answer a question had to delete the argument,
and the verdict then said only that the claim had no support. This record
makes the checker accept such a unit and report the incomplete argument, with
the questions it leaves open, as a *located gap*.

## 1. The judgment

A **hole** is a declared argument that type-checks under spec §6.1 with a nonempty
root obligation set:

```text
Sigma; Pi; Gamma; R |- a : supports(p_a) ▷ O      O ≠ ∅
```

`O` is the mandatory, transitive set: it contains every mandatory question left
open in `a` itself or in any premise or discharge subterm, because spec §6.1 unions
obligations upward (`collectObligations` in `lean/Lara/Support.lean`). An open
**optional** question contributes no obligation and never makes a hole. A term
whose support inference fails is not a hole; it is a rejection (step 2 below;
§7 below, "Treat inference failure as incompleteness").

Two older uses of "hole" are different notions. The open set `H` of a rule
instance (spec §6.1, written `{o*}` and spelled `open q`) lists the questions
that instance leaves open, optional ones included; a located hole is a whole
declared argument, and it may contain no `open` of its own when its obligation
comes from a subterm. The template holes of `Lara.Context.Holes` are answer
positions that a context fills, and they never reach this judgment.

An accepted unit's checked declarations split once into two disjoint lists:

```text
Args(P)  = { a declared | |- a : supports(p_a) ▷ ∅ }    -- complete: AF nodes
Holes(P) = { a declared | |- a : supports(p_a) ▷ O, O ≠ ∅ }  -- located gaps
```

The two lists cover every checked declaration, keep declaration order, and keep
the conclusion and obligation set the support stage cached. Compilation and
reporting read that cache; neither re-runs support inference.

Everything that rejected a unit before program checking is unchanged: codec
and replay errors, source and admission rejections, `duplicate-rule`, R2 and
R12. Within program checking, in the fixed stage order of spec §8.2, a unit is
accepted iff:

1. no two declared arguments are equal;
2. every declared argument type-checks under spec §6.1, complete or hole — every
   R-class of that judgment, R5 question accounting included, still rejects;
3. every declared attack type-checks under spec §7.1, whatever its source and
   target are;
4. every conflict that the policy's contraries license between two complete
   arguments is covered by an attack whose source is complete
   (`missing-conflict` otherwise).

The only change is that a nonempty root obligation set no longer fails
step 2.

Only complete arguments become AF nodes. An attack produces closure edges only
when its source is complete, and then onto every complete argument that
contains the attacked occurrence (spec §8). Claim status is unchanged in form: a
claim with empty complete support is `gap`. A claim with complete support takes
its status from the labels, and any holes concluding the same proposition are
reported beside it as incomplete alternatives.

## 2. Decisions

**D1 — `lara-core@0.3`, hard cutover.** The replay identity's core component
becomes `lara-core@0.3`. The decoder accepts exactly that version and refuses
`lara-core@0.2` inputs as an R14 codec error, as `@0.2` refused `@0.1`. A unit
none of whose declared arguments is a hole, retained or quarantined, gets the
same labels, edges and statuses under `@0.3`; only the core version component
of its verdict changes. A unit accepted under `@0.2` has no retained hole, but
it may have quarantined one. `@0.2` counted such a hole as a node of the
conservative-reporting reference framework; `@0.3` does not (D7), so its
outgoing attacks no longer cause `evidence-blocked`, while labels and edges
are unchanged. The version moves in the same change as the driver and wire
work, before the committed fixtures are regenerated.

**D2 — An optional `holes` section, not a status.** An accepted verdict gains
an optional, nonempty `(holes ...)` section after `conditional` (§4 below). A
hole is neither a fifth core status, nor a public status, nor an AF label.
`gap` keeps the meaning it always had: no complete support.

**D3 — Retire `incomplete-argument`.** The named rejection kind, its error
constructors in both runtimes, its wire tag, its renderers and its mutation
expectations are removed. R5 question accounting is unchanged: a declared
question in neither the discharge map nor the open set `H`, or a discharge or
an `open` naming an undeclared question, still rejects.

**D4 — Attacks sourced at a hole are checked, then inert.** A declared attack
whose source is a hole must still type under spec §7.1; an ill-typed one rejects
the unit with its R-class, as before. A well-typed one contributes no AF edge.
The hole's report lists it by its original attack declaration index.

**D5 — Three index spaces, with explicit maps.** Holes are reported by
original declaration index, `ArgId`, and exact mandatory root obligations.
Labels, edges and complete support use compact AF indices. See §3 below.

**D6 — Attacks targeting a hole are kept.** An attack from a complete source
onto an occurrence inside a hole is not discarded. If the attacked occurrence
is a complete subterm that also occurs in a complete argument, the closure edge
onto that complete argument is produced. A rebut of the hole's root adds no
edge onto a complete wrapper of it, because a wrapper inherits the hole's
mandatory obligations and is therefore itself a hole.

**D7 — Conservative reporting compares against complete declared arguments.**
The reference framework of spec §4.3 excludes typed holes. It keeps
quarantined declarations whose support inference fails under the full declared
`Gamma` as conservative nodes. The checked framework holds only the retained
complete nodes. Raw declared attacks and their endpoint alignment are kept.
See §5 below.

**D8 — The surface classifies by the core obligation set.** A `.lara` argument
is a hole exactly when its core obligation set is nonempty, mandatory and
transitive. Questions authored at an argument's root, optional ones included,
remain separate diagnostic data and do not decide hole-hood. A surface claim
selects its alternatives, holes as well as complete support, by authored claim
id; outside the derived-support role a selected hole always concludes the
claim's formal, but where claims share an equivalent formal the id selection
can miss alternatives that the core's conclusion-equivalence selection
includes.

**D9 — Composition results cover holes.** Linking, composition and
contextual-equivalence results are stated over `SideOkHoles`
(`lean/Lara/Context/Link.lean`, issue #13): each declared argument of a side
must type, as a complete argument or as a hole. The hole-free `SideOk`
theorems (`link_checked`, `link_accepted_raw`, `batch_checked`,
`linkedUnitOf_checked`) are now corollaries. `link_checked_holes` accepts the
link. `link_accepted_holes` (`lean/Lara/Context/LinkHoles.lean`) says what the
accepted link is. Its AF arguments are the sides' merged complete arguments,
and its holes are the sides' merged holes. Its compiled attacks are each side's
live attacks, then the saturation. `link_classify`, `link_hole_report` and
`link_side_hole_reported` show that a declaration keeps its side's
classification, conclusion and obligation set. `link_hole_source_inert` (D4)
and `link_shared_occurrence_edge` (D6) carry the attack rules through the link.
`crossAtts_endpoints_complete` says the saturation never touches a hole.
`Admissible` now takes `SideOkHoles` sides, so every congruence stated over it
covers fragments and contexts with holes: backend replacement, registry swap,
relational parametricity and `surface_directAF_link`. `obsGen_hole_blind`
bounds what holes can change: two fragments with the same interface, the same
complete arguments and the same live attacks are observed alike in every
context admissible for both. Its live-attack premise is needed: deleting a
hole together with an attack aimed inside it can remove the only cover of a
conflict, so the link is rejected
(`Lara.Examples.LinkHoles.hole_erasure_observable`). The map layer has
matching statements: `batch_checked_holes`, `batch_hole_report` and
`linkedUnitOf_hole_report`. General acceptance and arbitrary-obligation
transport are preserved. Possible-world status results
remain about complete support; they do not claim a correspondence between hole
reports. The hole term ledger is part of the duplicate-world identity in both
runtimes, so two worlds that differ only in their holes are not merged.

**D10 — No separate surface rejection or warning for holes.** After admission
the surface and the core report the same incomplete alternatives. The surface's
existing diagnostics for authored questions are unchanged and stay distinct.

**D11 — Completion is additive, in place, or atomic.** An author completes a
gap in one of three ways. Additively: add fresh admitted leaves as needed, then
a distinct complete term under a fresh id; the old hole and the raw attacks stay
declared. In place: discharge the hole's open question under its own id
(`dischargeOpen`, D13). Atomically: apply leaves, instances or discharges and
the attacks they need as one batch that is admitted and checked once
(`atomic`, D14). The individually rechecked additive sequence is not
universally accepted: the new complete term goes through ordinary
attack-completeness checking, so if it licenses an outgoing conflict with no
covering attack, `addInstance` can reject before a later `addAttack` could
supply the cover. The atomic batch closes that gap. Updates are source-level
and not on the verdict wire, so none of this changes the core contract. See §6
and §6a below.

**D12 — Each obligation is located at its rule occurrences (issue #16).** A
hole row reports every root obligation together with its *sites*: the
positions, inside the hole's own support term, of the rule instances that leave
the question open with the question mandatory for their rule. These are
exactly the occurrences that contribute the question to the root obligation
set, so an obligation inherited through a premise or a discharge points at the
step that needs the answer instead of at the wrapper argument. The row becomes
`(obligation ID POS+)` inside `obligations` (§4 below); `POS` is the attack
position encoding of spec §7, relative to the hole's root term.

- *No version bump.* `lara-core@0.3` has not shipped (no release or tag
  carries it), so the `@0.3` hole row is amended in place rather than moved to
  a new core version or given an additive optional field. A consumer that
  read the bare-id `@0.3` rows from a development build fails to decode the
  new rows rather than misreading them.
- *Order and content.* The obligation list keeps exactly the content and the
  order it had: the core's deduplicated union order. A row's sites follow the
  traversal `collectObligations` uses — premise subterms in index order, then
  discharge subterms in discharge-map order, then the instance itself
  (post-order) — and are distinct.
- *Computed from the cache.* Sites are read off the checked hole's term and the
  rule lookup (`Lara.Check.openSites`, Haskell `Lara.SupportTerm.openSites`);
  no driver re-runs support inference for them (§7, "Re-infer completeness
  while compiling").
- *Mechanized.* `lean/Lara/Check/HoleSites.lean` proves soundness
  (`openSites_sound`: every site is a rule occurrence leaving the question
  open, mandatory for its rule), completeness (`openSites_complete`, with no
  typing premise), that the questions with a site are exactly the root
  obligations (`mem_obligations_iff_sites`), and that no site repeats under
  typing (`openSites_nodup`, `sitesFor_nodup`). `obligationSites_adequate`
  packages these per row and `Lara.Driver.holeRows_obligations` ties every
  emitted row to them.
- *Map layer unchanged.* `map-verdict@2` hole rows stay
  `(hole ALIAS ARG-ID (obligations ID+))`. Sites are reported by the core
  verdict only; a map consumer that needs them runs the member's unit through
  the core driver.
- *Surface.* On the `.lara` path a site is a core position relative to the
  lowered term, the same convention as attack positions. The surface's own
  diagnostics and the surface-conformance contract are unchanged.

## 3. Index convention

Three index spaces appear in verdicts and their reports:

| Space | Ranges over | Used by |
| --- | --- | --- |
| original declaration index | the supplied unit's argument (or attack) declarations, before admission | hole rows, hole attack lists |
| checked (local) declaration index | the post-admission unit `checkUnit` checks | rejection constituents, as today |
| AF index | the complete nodes of the checked unit, in declaration order | `labels`, `edges`, complete support |

Positions computed by the core are local to the exact post-admission unit it
checked. The maps between the spaces are:

- admission's retained-argument map (checked declaration → original
  declaration) and retained-attack map (checked attack → original attack),
  reused unchanged;
- one new map, complete node → checked declaration, produced by the partition
  of §1 above.

The driver composes these to report each hole at its original position. With
no quarantine the first two maps are identities; with no holes the third is.
Rejection constituents keep their existing local declaration ids; AF label ids
are a separate numbering and are never used to address a declaration.

On the raw `.sexp` path, "original" means the order of the `args` and
`attacks` sections of the supplied unit. On the `.lara` path it means the
expanded and lowered declaration ledger before admission. Arguments the
elaborator generates carry authored-or-generated provenance and are never
presented as authored `.lara` declaration positions.

A quarantined declaration stays in the admission audit and is absent from the
accepted hole report, whether or not it would have been a hole.

## 4. Wire: the `holes` section

The accepted verdict grammar becomes:

```text
VERDICT ::= (verdict REPLAY-ID accept
              (labels (NAT LABEL)*)
              (edges (NAT NAT)*)
              (statuses (status ATOM STATUS)*)
              CONDITIONAL-SEC? HOLES-SEC?)
HOLES-SEC ::= (holes HOLE+)
HOLE ::= (arg NAT ID (obligations OBL+) (attacks NAT*))
OBL  ::= (obligation ID POS+)
POS  ::= (pos ((prem NAT) | (ques ID))*)
```

- The hole's `NAT` is its original argument declaration index; `ID` is its
  `ArgId`.
- `obligations` lists the hole's exact mandatory root obligations, in the
  core's deterministic deduplicated union order. That is the order
  `collectObligations` builds: premise obligations, then discharge obligations,
  then the instance's own open mandatory questions, each question kept at its
  last occurrence.
- Each `OBL` names one obligation and its sites (D12): every position, relative
  to the hole's root term and in the attack position encoding of spec §7, of a
  rule instance that leaves the question open with the question mandatory for
  its rule. `(pos)` is the hole's root. Sites follow the `collectObligations`
  traversal (premises in index order, then discharges in discharge-map order,
  then the instance itself) and are distinct.
- `attacks` lists the original declaration indices of the surviving,
  successfully typed raw attacks whose source is this hole. It uses raw
  endpoint alignment and is taken before live-source filtering. An empty
  `(attacks)` is canonical.
- Holes appear in original argument order. Every surviving hole is emitted,
  even when no query names its conclusion. Identifiers use the existing atom
  printer, including quoting and Unicode.
- The section is omitted when there are no holes, so a verdict for a unit
  with no hole among its declarations is byte-identical to its `@0.2` form
  apart from the core version.
- A claim report selects its incomplete alternatives by conclusion
  equivalence. That selection does not change the global hole list.

A standalone verdict decoder checks row shape, canonical naturals, nonempty
obligation lists, unique obligation ids within a row, a nonempty site list per
obligation, no repeated site within an obligation, unique hole indices, unique
hole ids, and the fixed section order. It does not bound hole indices by the number of AF labels: a hole index
is a declaration position, not a node. Agreement between a hole's index and its
id, and validity of its attack references, depend on the supplied input and its
admission maps, so only a decoder that holds the input can check them.

### Map layer (`map-verdict@2`)

A multi-artifact map (spec §12) links its members into one unit and runs the
ordinary checker on it, so a member's hole is a hole of the linked unit and the
map accepts it. The composite verdict moved to `map-verdict@2` for this
(`docs/multi-artifact-composition-decision.md` D14):

- `nodes`, `labels` and `edges` share the AF index space; a node's index is
  reached through the checked unit's AF-to-declaration map, never the linked
  declaration position.
- An optional, nonempty trailing `(holes (hole ALIAS ARG-ID (obligations ID+))+)`
  section reports every handle whose linked argument is a hole, by member alias
  and member-local argument id, with the exact obligations in core order, in
  the same member-then-declaration order as `nodes`. It carries no index, no
  attack list and no obligation sites (D12).
- The cross-member saturation generates no attack sourced at or aimed at a hole
  (D4, D6); `Lara.Map.crossPairs_endpoints_complete` states it, and
  `batch_generated_live` ties it to the accepted linked unit.

The map driver's acceptance of linked units with holes is covered by the
hole-aware linking results of D9: `linkMembers_checked_holes` accepts members
with holes, and `batch_hole_report` / `Driver.linkedUnitOf_hole_report` show
that each map hole row is a member's own hole with that member's own
conclusion and obligations.

## 5. Conservative reporting with holes

Spec §4.3 publishes `evidence-blocked` for a queried claim whose complete
support could have been changed by quarantine. With holes the two frameworks
of that rule are fixed as follows, all in original declaration index space.

**Reference carrier `D`.** The original declarations classified, under the
full declared `Gamma`, as either complete or *unclassified*. A declaration is
unclassified when its support inference fails, as happens to a quarantined
declaration with a missing leaf or rule or an invalid assurance. Typed holes
are excluded. Retained declarations reuse the checked cache: the checked
`Gamma` agrees with the declared one on every leaf a retained term uses, so
their classification is already known. Each quarantined declaration is
inferred at most once for this classification. No `Gamma`-independent
structural classifier is introduced.

**Checked carrier `K`.** The retained complete declarations. `K ⊆ D`.

**Frameworks.** `G` has carrier `D` and the closure edges of the raw declared
attacks between members of `D`. `F` has carrier `K` and the closure edges of
the retained attacks between members of `K`.

**Seed and blocked set.**

```text
seed = (D \ K) ∪ { j ∈ K | ∃ i ∈ K. G.attack i j ∧ ¬ F.attack i j }
B    = forward closure of seed along G's edges, over D only
```

A queried claim with a complete retained support argument in `B` reports
`evidence-blocked`. Its four-state label moves to `conditional` as before.

Three consequences are stated as acceptance cases:

- Holes and the attacks they source can neither seed nor propagate blocking:
  holes are not in `D`, and their attacks have no edge in `G`.
- An attack from a retained complete source onto an occurrence inside a hole,
  dropped because quarantine removed the hole, can still seed a retained
  complete argument that contains the same occurrence. `G` has that closure
  edge and `F` lost it.
- Quarantining a hole alone, when no such dropped closure edge exists, blocks
  nothing.

An unclassified quarantined term stays a node even when it has a raw outgoing
attack onto complete support. That keeps the conservative block, and the term
is never reported as a typed hole. The stronger statement that `D` is exactly
the complete declared arguments holds only under a full-declared
support-typing premise, and is proved only under it.

The nonpromotion theorem keeps its shape: a publicly `justified` claim is
`justified` in `G`. The fast path (nothing quarantined) still blocks nothing,
so a clean unit with holes never reports `evidence-blocked`.

## 6. Source updates and completion

Adding a hole is inert only when the complete terms, their typing context, and
the closure coverage between complete terms stay fixed. The unconditional claim
is false because of D6: adding an attack onto an occurrence inside a hole can
add an edge onto an existing complete argument, and removing a hole can remove
such an attack at the raw endpoint boundary. The invariance results are
therefore stated under unchanged complete-to-complete coverage, or for a fresh
`addInstance` of a hole with the attacks unchanged; the latter leaves every
core status unchanged and adds a diagnostic.

Completion follows D11. A fresh complete alternative is checked like any other
`addInstance`; the old hole persists and is still reported. As a sequence of
individually rechecked updates this is not complete: `addInstance` of a
complete term that needs an outgoing attack rejects, and the `addAttack` that
would cover it rejects first because its source is not yet declared
(`Examples.UpdateCompletion.sequential_completion_fails`). Completion is no
longer only additive. An atomic batch performs the whole completion and checks
the completed program once, so whenever that program is accepted the batch is
(`atomic_completion_complete`). An in-place discharge rewrites the hole itself:
the old hole leaves the report when the discharge completes it, and every other
hole stays (`dischargeOpen_hole_becomes_node`, `dischargeOpen_others_persist`).
§6a records both designs.

## 6a. Update vocabulary for completion

Both decisions below are source-update decisions
(`docs/theory-m3-source-updates.md`). Updates are not on the verdict wire, so
neither changes `lara-core@0.3`, the replay identity, any committed verdict, or
the evaluation freeze.

**D13 — Discharge a located hole in place (`dischargeOpen`, issue #14).**
`dischargeOpen name π q v` answers the open question `q` of the rule occurrence
at position `π` (spec §7, `π ::= ε | π.i | π.q`) inside the declared argument
`name`, with the discharge term `v`.

- *Precondition* (`DischargeOpen`, decided by `dischargeOpenB`): the name
  resolves, through the first-match lookup raw attack endpoints use, to a term
  whose occurrence at `π` is a rule instance with `q` in its open set `H`. The
  precondition is syntactic. Whether `v` answers `q`'s pattern, and whether the
  result is typed, are left to the checker, as for every other update.
- *Effect*: at that occurrence `q` leaves `H` and `(q, v)` is **appended** to
  the discharge map (`Discharge.dischargeAt`). The row keeps its name and its
  declaration index, the raw attacks are untouched, and admission and
  `checkUnit` then rerun on the edited source.
- *Why append*: `lookupDis` reads the first matching entry, so appending leaves
  every discharge lookup that succeeded before unchanged. Every position that
  was defined in the old term stays defined and addresses an occurrence of the
  same kind (the same leaf, or the same rule and substitution); off the
  root-to-`π` path it is the identical subterm (`subterm_dischargeAt_old`). On
  a typed term `q` had no discharge (`D ⊎ H` is a partition), so `π.q` is a new
  position and addresses `v` (`subterm_dischargeAt_new`). Raw attack identities
  and raw endpoint alignment are therefore preserved: each raw attack resolves
  at the same index, kind and position, with the new term at the endpoints that
  name the discharged argument (`resolveAttacks_dischargeRows`,
  `dischargeOpen_resolved`).
- *Metatheory*: the conclusion is unchanged (`dischargeAt_conclusion`). The
  rewritten term types whenever the old one did and `v` answers the question
  (`dischargeAt_hasSupport`). Its obligations are exactly the old open mandatory
  questions away from `π`, those still open at `π`, and `v`'s obligations
  (`dischargeAt_obligations_iff`, built on the occurrence characterization
  `mem_obligations_iff`). Discharging the only open mandatory question, at its
  only open occurrence, with a complete term yields a complete term
  (`dischargeAt_complete`). Through the pipeline, every hole and complete
  argument other than the discharged one persists in both directions
  (`dischargeOpen_others_persist`). A retained hole discharged to completion by
  a term that uses no quarantined leaf becomes an AF node, leaves the hole
  report under both its old and its new term, and moves every claim equivalent
  to its conclusion out of `gap` under every extension semantics
  (`dischargeOpen_hole_becomes_node`).
- *Not claimed*: no status matrix and no gap-monotonicity theorem. The site may
  hold an *optional* open question of a complete argument; then an AF node's
  term changes, and if `v` is itself incomplete the node becomes a hole and its
  claim can enter `gap`. Even a hole-to-hole discharge can change an edge: an
  attack from a complete source onto a position on the root-to-`π` path now
  addresses the rewritten occurrence (D6).

**D14 — Atomic multi-edit completion (`atomic`, issue #11).** `atomic edits`
applies a list of raw edits — `addLeaf`, `addInstance`, `addAttack` and
`dischargeOpen` (`AtomicEdit`, a separate type, so a batch cannot nest) — in
order, then runs admission and `checkUnit` exactly once on the final raw state.

- *Per-edit checks*: each edit's syntactic side condition is checked against
  the state the earlier edits produced, so an attack may name an instance added
  earlier in the same batch, but not a later one. The first failing edit rejects
  the batch with `batchEdit index reason`.
- *All or nothing*: the batch is accepted exactly when its raw edits apply and
  the final raw state is `Accepted`, and it then returns that state
  (`applyUpdate_atomic_ok_iff`). A rejected batch returns no state, and the
  caller keeps the source (`applyOrKeep`, `atomic_partial_rejected`).
- *Completeness of completion*: if the program obtained by adding fresh leaves,
  fresh instances (or an in-place discharge) and the attacks they need is
  accepted, the corresponding batch is accepted and yields exactly that program
  (`atomic_completion_complete`, `atomic_discharge_completion_complete`). No
  intermediate state is checked, which is what the sequential route lacks.
- *Identities*: every successful batch keeps every raw attack and every
  argument name at its declaration index. A batch without discharge keeps every
  argument row (`applyBatchFrom_prefix`). If its new leaves are admitted, it
  also keeps the source's complete arguments and reported holes as prefixes of
  the target's (`atomic_additive_checked_prefix`).
- *Why no `tighten`*: tightening never completes a gap. Leaving it out keeps
  every batch without discharge inside the additive metatheory.

**Rejected alternatives.**

- *Nest `SourceUpdate` inside `atomic`.* A nested inductive allows batches of
  batches and complicates every induction for no expressive gain.
- *Check every intermediate state of a batch.* That is the sequential route
  again, and it fails on the same counterexample.
- *Delete the hole and re-add the completed term under the same id.* There is
  no removal update, and a delete-then-add sequence passes through a state in
  which the attacks naming the id do not resolve. Rewriting the row in place
  keeps the id, the index and every raw attack.
- *Prepend the discharge, or keep the discharge map sorted.* On an ill-formed
  raw term either can shadow an earlier entry with the same key and move an
  existing position. Appending provably preserves every old position.

The Haskell mirror (`src/Lara/Update.hs`) carries both constructors, the site
decider, the rewrite and the raw stage of a batch, and `make
update-differential` diffs them exhaustively against Lean. Batch acceptance is
Lean-only, like `applyUpdate`. The update golden prints the completion
witnesses (`Examples.UpdateCompletion.completionWitnessReport`); no transition
matrix is computed for the two new constructors.

## 7. Rejected alternatives

**Keep rejecting (the `@0.2` contract).** Rejection was a v0.1 scope decision,
not a soundness requirement (`docs/evidence-admission-decision.md` §6). It
forced an honest author to delete the argument, so the verdict could say a
claim had no support but not which question was missing. It also let the
earliest incomplete argument mask any later support or attack defect in the
same unit. The status function of spec §8 was already stated over
`holes(P, p)`, and `statusC` already yields `gap` exactly on empty complete
support (`statusC_gap_iff` in `lean/Lara/Grounded.lean`), so accepting holes
needs no new status.

**Drop attacks that target a hole.** This would discard a typed attack on a
complete subterm merely because the subterm also occurs inside a hole, and lose
the closure edge onto complete arguments that share it. Spec §8 closes attacks
under subarguments for exactly this case.

**Make holes nodes of the nonpromotion reference framework.** Counterexample:
let claim `c` have one complete support `a`, and let an unattacked hole `h`
carry a typed attack onto `a`. In the checked framework the attack is inert
(D4), so `a` is `in` and `c` is `justified`. In a reference framework with `h`
as a node, `h` is `in`, `a` is `out`, and `c` is `defeated`. Nonpromotion would
then fail on a unit with nothing quarantined, or would require blocking `c` and
so make a clean unit report `evidence-blocked`. Holes are not nodes of any
accepted framework, so they are not nodes of the reference framework.

**Treat inference failure as incompleteness.** The prototype classified any
term whose inference failed as a hole. On the retained core path such a term
is a rejection, and reporting it as a hole would accept ill-typed arguments.
Only on the quarantined side, where no rejection is possible, are such terms
kept, and there they are conservative nodes (§5 above), never holes.

**Re-infer completeness while compiling.** Recomputing completeness with
support inference duplicated the checker's work and made kernel-evaluated
examples time out. The partition is taken once from the checked cache.

**Report a hole as a status or a label.** A fifth status would change the
four-state vocabulary, and a label would put a non-node into the framework.
The located report is diagnostic data beside the unchanged status.

## 8. Non-goals and cost

The follow-ups this record first deferred have landed with it. Hole rows
locate each open obligation at its rule occurrences (D12, issue #16); the map
layer still reports obligations without sites. Linking and composition cover
units with holes (D9, issue #13). In-place discharge (issue #14) and atomic
multi-edit completion (issue #11) are source updates, recorded in §6a. The
frozen `corpus-units` declare their incomplete arguments as located holes
(`corpus-units/LOWERING.md`, issue #15).

The version bump changes every committed verdict and check-input byte that
carries the replay identity. The cutover therefore regenerates the mutation
suite, corpus fixtures, worked examples and freeze bundles, and cuts a new
evaluation freeze with a full axis-(c) re-run.
