# B0 Heterogeneous Backend Compositionality

_Status: settled record (2026-08-29). For cold readers: a *backend* is one of
the external checkers that re-verify strict certificates (`nd@1`, `ra@1`,
`ord@1`, `insp@1`); when one program mixes several, the proofs need a
firewall guaranteeing no backend's acceptance can leak influence into
another's._

Milestone B0 (issue #182, tracker #180). This record holds what B0 froze: the
occurrence vocabulary, the firewall theorem, the two accounting laws, the
claim boundary the paper must respect, and the scope decisions taken along the
way — including one the implementation re-opened on evidence.

Mechanized in `lean/Lara/BackendComposition.lean` (abstract) and
`lean/Lara/Examples/BackendComposition.lean` (worked witness); the executable
conformance half is `src/Lara/Strict/Deps.hs` and `test/StrictSpec.hs`. Every
theorem named here is covered by `lean/AxCheck.lean`, sorry-free, on the
standard trio `propext` / `Classical.choice` / `Quot.sound`.

## What B0 Actually Was

Most of what #182 asked for was already mechanized before the milestone
started, and recognizing that changed its shape. `certOkOf`
(`Lara/Support.lean`) already resolves each `BackendId` to its own
`RegisteredBackend`, each carrying its own `core : Strict.Backend canon` with
its own private `core.Form`; heterogeneity was already *structural*, because
nothing anywhere forced two occurrences to share a formula type.
`cert_node_accounted` and `cert_steps_accounted` already lifted per-instance
strict soundness through `HasSupport` with the backend record bound in a
per-node existential. `mem_certDeps_step` and `certStep_deps_subset` were
already the two directions of the dependency union.

What was missing is that no theorem *stated* heterogeneity. Every existing
result quantified one occurrence at a time. The property was true and unstated
— and an unstated property is one a later refactor can silently break, which
is precisely what M4 (#187) must not discover.

So B0 is mostly consolidation, plus one genuinely new theorem (the firewall),
plus the repair of a live gap on the Haskell side that the survey did not
expect.

## Frozen Definitions

| Object | Declaration | What it fixes |
|---|---|---|
| Certified occurrence | `CertOccurrence`, `.node`, `OccursIn` | The eight-binder node pattern of `CertStepIn`, bundled as a statement surface |
| Named identities | `usedBackends`, `usedBackendsList`, `usedBackendsDis` | Which backends a term *names*, source-visibly |
| Occurrence-local consequence | `OccurrenceConsequence` | What one occurrence's backend establishes, with its formula type bound inside |

### `CertOccurrence` derives rather than stores (deviation from the paper plan)

The paper plan's `CertOccurrence` field list includes the instantiated premise
conclusions and the source conclusion. The mechanization does **not** store
them. They are not part of the node's syntax — they are recovered from the rule
and the substitution (`instAPats θ r.premises`, `instAPat θ r.concl`) and exist
only relative to a typing derivation. Storing them would let a caller forge an
occurrence whose recorded premises disagree with the ones its rule actually
instantiates.

The mechanization wins; the paper plan is to be revised to the derived-fields
phrasing. Tracked as EYH0602/lara-paper#2.

### `OccurrenceConsequence` and where heterogeneity lives

```lean
def OccurrenceConsequence {canon : String → String} (reg : BackendRegistry canon)
    (β : BackendId) (hd : Digest) (κ : CertRef) (As : List Atom) (C : Atom) : Prop :=
  ∃ registered T, reg β = some registered ∧ registered.resolveTheory hd = some T ∧
    registered.core.modelsFull
      (Strict.selectSlots (As.map registered.core.enc ++ T) (registered.core.uses κ))
      (registered.core.enc C)
```

`registered.core.Form` is bound by the `∃`. The formula type, the theory data,
and the consequence relation are all projections of a witness this proposition
introduces and discharges; each existential closes before the next opens. So
conjoining two occurrences' consequences introduces **no binder requiring them
to share a formula type, a theory, or a consequence relation**.

That is the claim, and it is a claim about the *absence of a relating binder*
— not an assertion that the two are disjoint. A registry is an arbitrary
function `BackendId → Option (RegisteredBackend canon)`; nothing stops it
mapping two identities to the same core, in which case the two formula types
*are* equal. Type disjointness is neither provable nor intended. Heterogeneity
here means the composition is *unconstrained*, not that the parts are
*distinct*.

Two binders **are** shared across the conjuncts, and saying so is what keeps
the sentence above from compressing into the false "nothing is shared": the
registry `reg` and the source canonicalizer `canon` that every `Backend canon`
is indexed by. Both are source-side. Neither relates the backends' internal
mathematics, so the three enumerated items remain unshared. Sharing `canon` is
in fact what the composition *needs* — it is what makes two backends'
conclusions comparable as claims about the same source.

This distinction is load-bearing for the paper. A display that reads
"different backends have different formula types" would be false.

## The Firewall

The one new theorem of the milestone, in two halves:

- `prem_subterm_swap` — replacing a premise subterm with any term of the same
  conclusion and obligations preserves the parent's typing.
- `dis_subterm_swap` — the same at a discharge slot, with the question key
  carried across by `map_fst_set_of_getElem?`.

Neither statement mentions a backend, and that is the content: the replacement
may be certified by a different registered identity over a different private
formula type under a different theory, and no side condition of the parent can
express the difference. Naming the two backends is a corollary
(`mixed_swap`, `mixed_dis_swap`), not the theorem.

**Why it is cheap, and how that is verified mechanically.** `InstSide` reaches
`ws` only through three length fields — `lenAs`, `lenCs`, `lenOs` — and
`List.set` preserves length. The check is not a reading of the structure: the
premise half's proof is `refine .inst { hside with lenAs := …, lenCs := …,
lenOs := … }`, and *that elaborating* is Lean confirming those three fields are
the only place `InstSide` mentions `ws`. The discharge half touches more —
lengths, `ans`, and the four fields reading `D.map Prod.fst` — so its surviving
side conditions are written out one by one rather than inherited, because which
fields survive is the point of the theorem.

## The Accounting Laws

- `certDeps_eq_union` — certificate dependencies are exactly the union of the
  occurrence-local backend reports. Each `stepDeps o.node` is computed by
  `o.β`'s own core, so this is a union over heterogeneous reporters, not a
  report from a shared one. The collection law survives heterogeneity because
  it never had to look inside a backend to hold.
- `hetero_occurrences_accounted` — **the B0 headline.** Every certified
  occurrence of a typed term is accounted by *its own* registered core. It
  carries the acceptance conjunct the paper's target theorem states ("its local
  checker accepts its certificate") as a conjunct separate from the
  consequence: acceptance is the checkable fact a verifier re-runs, consequence
  is the semantic fact it buys.
- `usedBackends_accounted` — the syntactic identity list is exactly the set of
  logics the term's correctness rests on. Read as an audit: for each `β` a
  reviewer scans out of a term, it names the occurrence to inspect, the
  certificate to re-check, and the digest fixing which axioms that check may
  consult.

All three are derivations from the pre-existing `Lara/Support.lean` results
(design decision D4 — repackage, do not re-prove). No new induction was needed
anywhere, which was the intended signal that the repackaging was the right
shape.

## The Haskell Gap B0 Repaired

The survey found a live defect outside B0's stated scope. `strictCheck` — the
only constructor of the sealed `StrictJudgment`, and the only thing retaining
`sjDependencies` — is called from `test/` and from nowhere in `src/`. The
production checker reaches backends through `buildCertOk`, which called
`runBackend` and **discarded the dependency report**. Lean proved `certDeps`
accounts for every certified occurrence; the shipped checker accounted for none
of them.

Building a term-level collector on `strictCheck` would have produced a
conformance vector that passes while the shipped checker still accounts
nothing. So:

- `CertOutcome.CertAccepted` now carries the `Set Dependency` the adapter
  already returns. The acceptance projection `certAccepted` stays a `Bool`,
  which is the invariant that makes the widening safe — no checked-graph
  decision, and therefore no soundness statement, can start depending on
  dependency data.
- `Lara.Strict.Deps.certDeps` collects the term-level report, tagging each
  step with its own backend as it walks. Identity is tagged with
  `St.BackendId` (name *and* version), not the AST's name-only id, so two
  same-name different-version backends cannot collide into one
  indistinguishable report.

*Surfacing* the retained reports to shipped consumers is deliberately out of
B0's scope and is tracked as **#204**. Retention alone is the prerequisite
everything downstream needs.

## Scope Decisions

### S1 — the Lean child backend: re-opened and re-decided

**Original decision (plan review, 2026-08-29):** hand-prove per-literal string
lemmas so a real `ord@1` numeric certificate would be *accepted* inside the
Lean kernel, in the style of `Lara.ND.decodeNat_repr`, giving a genuinely
worked mixed acceptance over shipped backends only. The plan attached an
explicit budget escape hatch: "if it exceeds a day, stop and re-open S1 rather
than weakening the lemma statements."

**The escape hatch fired.** Measured during implementation:

- `ord@1` acceptance routes through `Cell.parseDecimal` → `parseUnsigned` →
  `String.splitOn`, and through `parseCanonInt` → `String.startsWith`.
- Under Lean 4.32's Slice-based `String` API, `String.splitOn`,
  `String.startsWith` and `String.endsWith` are **kernel-opaque**. On literal
  goals such as `"28".splitOn "." = ["28"]`, `rfl`, `decide`, `simp`, `exact?`
  and `grind` all fail; unfolding `String.splitOnAux` diverges to max recursion
  depth.
- `native_decide` would close the gap and is forbidden — the axiom gate admits
  only the standard trio, and `native_decide` adds `Lean.ofReduceBool`. It
  appears nowhere in `lean/`. (The ARA trace records it being *removed* from
  audited proof dependencies in July for exactly this reason.)
- `unseal String.splitOnAux` was also tried, on the theory that the obstruction
  is the irreducibility well-founded recursion introduces and that stripping it
  would let the literal reduce. It does not: the goal fails identically under
  `rfl` and `decide` with the seal removed. The obstruction is not (only) WF
  sealing but `String.Pos` byte arithmetic over an opaque primitive, so the
  cheapest available escape route is closed too.
- What *does* reduce per-literal: `String.toNat?` (via
  `String.toNat?_eq_some_ofDigitChars`, the existing
  `Lara.ND.decodeNat_leading_zero_01` treatment), string-literal equality,
  `String.toList`, `String.length`. Note also
  `Lara.NDNamed.parseCanonNat_repr` — `parseCanonNat (Nat.repr n) = some n`,
  proved generically rather than per-literal, currently `private`. Anyone
  revisiting this should start from it rather than rebuilding it.

So the literal reading of S1 requires hand-building unfolding lemmas for two
freshly redesigned core primitives, with no precedent in this repo and no
library support — far beyond the budgeted day, and possibly a dead end.

**Revised decision: the split witness.**

- **Shipped `nd@1` and `ord@1` carry the syntactic and resolution facts.**
  `mixed_usedBackends` and `mixed_registrations_distinct` need no acceptance:
  which identities a term names is readable from the term alone, and
  registration is a registry lookup.
- **A fixture core carries the typed facts.** `mixed_swap` and
  `mixed_dis_swap` need a genuinely typed child, and typing a certificate node
  requires its acceptance to hold in-kernel. The child is `fixCore`, a minimal
  `Strict.Backend` whose every field is genuinely proved and whose `uses`
  reports a real slot rather than nothing — an empty report would discharge
  `uses_covers` / `uses_valid` / `uses_account` vacuously and the fixture would
  prove nothing about the accounting laws it exists to exercise. What sits
  *above* that child differs between the two halves, and only the premise half
  witnesses a swap under a shipped parent:
  - For `mixed_swap` the *parent* is the real `nd@1`, via the already-worked
    `registry_success_bridge`, and the swapped term names both identities
    (`usedBackends mixedSwapTerm = [ndId, fixId]`).
  - For `mixed_dis_swap` the *parent* is an unassured defeasible `ruleMix`
    node, not `nd@1` — `strictNoQ` forces `D = []` on strict nodes, so a
    certified node in a discharge position needs a defeasible ancestor. `nd@1`
    is the *replaced child* here, so `usedBackends disParent = [ndId]` and
    `usedBackends disSwapTerm = [fixId]`: the swap crosses a backend boundary,
    but the post-swap term is homogeneous. The discharge-side firewall is
    therefore witnessed against a shipped backend only as the term being
    swapped *out*, not as the parent that survives the swap.
- **The cross-language golden uses shipped backends on both sides**, and this
  is the part the acceptance blocker does *not* touch. `certDeps` needs only
  resolution and `Backend.uses`; `ord@1`'s `ordUses` routes through
  `decodeCert` → `decodeSlot` → `parseCanonNat` → `String.toNat?`, which is
  per-literal provable. So the one artifact where both languages compute the
  same thing over the same two shipped backends is unaffected.
- **The worked mixed `nd@1`/`ord@1` acceptance vector lives in Haskell**
  (`test/StrictSpec.hs`), running on the shipped `inferSupport` /
  `buildCertOk` path.

This is not a new concession. Lean's `ord@1` and `ra@1` results have stopped at
the resolution layer for exactly this reason since before B0 — see the block
comment at `Lara/Examples.lean:368-376`, which says so in as many words. A
later reader should not "fix" it back without first checking whether the core
`String` API has gained the reduction lemmas.

`mixed_registrations_distinct` is proved through a **non-dependent projection**
— the resolved theory's *length* — because the theory data itself has type
`List r.core.Form` and cannot be compared across records.

### S2 — cross-language conformance mechanism

**Decided: `update-goldens`-style golden only.** Lean emits the mixed term's
`certDeps`, a committed golden pins it, a Haskell test asserts the same list.
The alternative of also adding a mixed corpus fixture to ride
`scripts/differential.sh` was considered and declined; the differential harness
is not extended for B0.

### S3 — the leakage example

**Decided: an inexpressible Lean leakage example satisfies the criterion.**

In Lean a parent *cannot* attempt to inspect a child's formula: `Assurance`
carries only `(β, hd, κ)`, and there is no syntax anywhere in the AST naming
another backend's `Form`. The attempt is not ill-typed — it is
**inexpressible**, so there is no Lean term to reject. The honest Lean
deliverable is the positive opacity theorem (the firewall) plus this
non-expressibility note.

At the Haskell wire level the attempt *is* expressible, because the wire form
is untyped: an `nd@1` certificate whose payload embeds an `ord@1` sub-payload is
a real `SExpr` that `nd@1`'s decoder rejects. That vector
(`prop_crossBackendPayloadRejected`) runs through `buildCertOk`, not
`strictCheck` — a firewall vector that never runs on the shipped path checks
the wrong checker.

The `Assurance`-extension alternative was rejected: it would put a non-source
construct in the frozen core to serve a test.

## Paper Claim Boundary

### May claim

- One checked support term may carry certified strict instances from different
  registered backends, each accounted in its own logic, with no shared backend
  logic introduced — `hetero_occurrences_accounted`.
- Certificate dependencies are exactly the union of the occurrence-local
  backend reports — `certDeps_eq_union`.
- A premise or discharge subterm may be replaced by any term of the same
  conclusion and obligations without disturbing the parent's typing, and the
  replacement may be certified by a different identity — `prem_subterm_swap`,
  `dis_subterm_swap`, instantiated at `mixed_swap` / `mixed_dis_swap`.
- The set of backend identities a term names is source-visible, and every name
  in it is registered and discharges an occurrence — `usedBackends_accounted`.
- Backend identity is quantified independently at each occurrence — the
  existential in `OccurrenceConsequence` binds `core.Form`.

### Must not claim

- **That Lean rejects a backend-leakage program.** It cannot be written; there
  is nothing to reject. The Lean content is the positive firewall theorem plus
  the non-expressibility note. The rejection artifact is the Haskell wire
  vector.
- **That different registered identities have different formula types.** Not
  provable, not stated, and not true in general — a registry may map two
  identities to one core. What is claimed is the absence of a binder relating
  them.
- **That this is parametricity.** It quantifies over registered identities, not
  relationally over related backends. This is the same distinction #187 draws.
- **That the shipped Haskell checker surfaces dependency reports.** It retains
  them; production `inferSupport` still reads only the acceptance projection.
  Surfacing is #204.
- **That the Lean mixed witness uses two shipped backends in its typed
  results.** `mixed_swap` and `mixed_dis_swap` use `nd@1` plus a fixture core;
  only the syntactic, resolution, and `certDeps` results use `nd@1` + `ord@1`.

## Verification

- `cd lean && lake build`
- `(cd lean && set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)`
- `bash scripts/test-check-axioms.sh`
- `cabal test lara-test --test-show-details=direct`
- `make presentation-parity && make semantics-goldens && make update-goldens`
- `make backend-deps-golden`
- `bash scripts/differential.sh`
- `bash scripts/admission-differential.sh`

**CI caveat.** GitHub Actions has been billing-blocked on the ARA-Labs org
since 2026-08-25; the last green run on `main` is `156cf10`. Tracker #180's
shared gate requires "CI reports no unproved obligations or unexpected axioms".
Until billing is restored that line is satisfied by the local stack above and
by nothing else.
