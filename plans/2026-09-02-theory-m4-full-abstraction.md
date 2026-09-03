# Theory M4: Contextual Adequacy of Backend Replacement — Plan

> **STATUS (2026-09-02): PART A IS EXECUTED AND LANDED. PART B REMAINS.**
> Phases F0–F3 are done and mechanized — the carrier
> (`docs/theory-m4-context-calculus-decision.md`), the linking calculus, the
> congruence headline, and the closeout
> (`docs/theory-m4-contextual-adequacy.md`, `docs/paper-lean-name-map.md` §M4).
> This plan is retained **only** for its Part B half: phases G0–G4, the
> `LabelExpressive` design, and the entry gate. Everything in the Part A
> sections below is historical — the durable records are the two `docs/` files,
> which is where a reader should go. Remaining tasks: **G0–G4 only**, plus the
> one Part A item that was deliberately not done — a worked surface *pair*
> witness, which every existing surface fixture blocks by resting on
> `native_decide` (closeout record §4, issue **#227**).

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan phase-by-phase.
> Steps use checkbox (`- [ ]`) syntax for tracking. **Phase F0 gates all theorem work, and
> Part B is gated separately after Part A closes.**

**Issue:** #187 (parent tracker #180). Canonical scope:
[M4 in the theory-depth plan](https://github.com/EYH0602/lara-paper/blob/main/plan/theory-depth-plan.md#m4-full-abstraction-and-backend-representation-independence).
That plan lives in the `lara-paper` repository, not here.
**Branch:** `theory/m4-context-calculus` (F0), then one branch per phase.
**Predecessors consumed:** B0 (#182, `docs/theory-b0-backend-compositionality.md`),
M5 (`docs/theory-m5-surface-calculus.md`, PR #213), M3 (`docs/theory-m3-source-updates.md`
§"Scope and Verification" — the contextual-adequacy obligation explicitly deferred to M4),
result 9 (`lean/Lara/Erase.lean`, `lean/Lara/EraseTransport.lean`).

**Goal (Part A, committed):** build the fragment/linking calculus and prove that backend
replacement is a **congruence** — an injective, acceptance-preserving relabel of a fragment
is unobservable in every admissible context whose own assurances it fixes. This is the
statement M3's deferred contextual-adequacy obligation and #187's headline actually need,
and it is reachable from `Erase.coveredB_relabel` / `edgeB_relabel` plus one
saturation-commutation lemma.

**Goal (Part B, optional, separately gated):** upgrade to full abstraction — fix a logical
relation independently, prove soundness, and prove completeness under an explicit
policy-expressiveness hypothesis. Part B is *not* committed: it is entered only if Part A
lands and its own gate says the relation is reachable in a non-tautological form.

**Architecture:** All new work is Lean-side over the frozen core carrier (`Lara.Unit`,
`Lara.Compile.CheckedProgram`, `Lara.Grounded.statusC`, the M2a observation discipline).
Contexts live at the core `Unit` level; the M5 surface calculus supplies a surface-transport
corollary, not the quantification domain. No Haskell checker changes, no corpus
regeneration, no freeze-tag impact. New modules under `lean/Lara/Context/`, witnesses in
`lean/Lara/Examples/Linking.lean`.

**Tech stack:** Lean 4, `Std` only (no Mathlib), standard axiom trio, `AxCheck.lean`
coverage, sorry-free at every phase boundary. No Haskell conformance vector (D8).

---

## Review status

**Engineering review: COMPLETE (2026-09-02).** 13 issues found in the four review sections;
an independent outside-voice pass found 8 more, five of which contradicted review decisions
and were resolved in the user's favour. All 18 decisions are folded. **The milestone was
restructured as a result:** congruence is now the committed headline and full abstraction is
an optional, separately gated continuation.

| Review | Trigger | Runs | Status |
|---|---|---:|---|
| Eng review | the plan PR | 1 | CLEAR — 13 issues, all folded |
| Outside voice | post-review challenge | 1 | CLEAR — 8 findings, all folded; drove the restructure |
| Motivation/CEO review | this document §1 | 0 | RECOMMENDED — the Part A/Part B split is a paper-scope call |
| Design review | — | — | No UI scope |
| DX review | — | — | No public API/onboarding scope |

**F0 gate: PROCEED (2026-09-02) — recorded in `docs/theory-m4-context-calculus-decision.md`.**

---

## 1. Motivation

### Why M4, and why now

M4 is the final open item on the POPL 2028 core mechanization spine (#180). The tracker's
execution order is explicit: "M4 closes the development after B0 and M5." Both prerequisites
are closed — B0 froze heterogeneous backend compositionality, M5 verified the surface
calculus and elaboration (PR #213). Every other spine milestone (M0–M3, M2b realization
closure #212) is landed. The only alternatives to starting M4 are the future-work
possible-world track (#189–#193) and polish issues (#196–#198, #204), none of which the
paper's core claims need.

### What Part A buys that the existing results do not

Every interchangeability result we currently have is **whole-program and syntactic**:

- **Result 9** (`Erase.backend_replacement`): an injective, acceptance-preserving assurance
  relabel of one entire `CheckedProgram` preserves every claim's four-state status. The
  quantifier is over relabelings of a fixed program, not over contexts. Its proof is
  `rw [checkedAF_relabel …]` — the compiled AFs are *definitionally equal*.
- **B0's firewall** (`prem_subterm_swap` / `dis_subterm_swap`): a subterm with the same
  conclusion and obligations can be swapped without disturbing the *parent's typing*. It
  says nothing about observable status, and nothing about arbitrary enclosing programs.
- **M3's update matrices**: one-step edits of one program. M3's own record states the debt:
  "M3 also does not prove contextual adequacy. Theory M4 (issue #187) retains that
  obligation."

Nothing in `lean/` defines a fragment, a hole, linking, or a context. Part A closes that:
it defines the calculus and lifts result 9 from "in this program" to "**in every compatible
well-formed context**". That is the contextual-adequacy statement M3 deferred, and it is
what the paper needs to claim that the backend boundary is a real abstraction boundary.

### Why Part A is reachable and Part B is not yet

The congruence direction goes through `Erase.coveredB_relabel` / `edgeB_relabel`
(`Erase.lean:198,223`): a uniform injective relabel preserves the entire occurrence profile,
so it commutes with the linking saturation and the linked AFs stay definitionally equal.
No logical relation, no realization gadgets, no completeness argument.

Full abstraction needs strictly more, and two obstructions are already visible in the repo:

1. **The semantic interface is not the declared imports.** `Compile.AttackComplete`
   (`Compile.lean:515`) is all-pairs, and `Covered` closes under subarguments
   (`Compile.lean:505`), so a context can attack *any* fragment argument whose conclusion
   contrary-matches an attackable occurrence — declared import or not. A relation stated
   over declared imports is refuted; a relation stated over the full contrary-visible
   occurrence profile risks collapsing into a generalized `Erase.mapAssur`, which is the
   tracker's tautology trap arriving through the interface rather than the quantifier
   (§6 R1, R6).
2. **Completeness is policy-conditional.** Under `emptyDefeat` no attack types, every
   compiled AF is edgeless (`compiled_no_edges_of_emptyDefeat`), and no context can force an
   import label — so `logrel_complete` is *false* without a hypothesis. It is worse than
   that degenerate case: `ConflictAttackable` is unconditionally `True` on leaves
   (`Compile.lean:407`) while rebut requires `r.mode = .defeasible` (`Attack.lean:592`), so a
   purely symmetric contrary table can force only `{in, undec}` (§6 R2, R7).

Neither obstruction blocks Part A. Both are exactly why Part B is optional and separately
gated: this is the tracker's named highest-effort item with an explicit drop policy ("the
first item removed if schedule or page pressure threatens mechanization quality"), and the
restructure turns that drop from a milestone failure into a graceful downgrade with a real
theorem already banked.

### The naming discipline is part of the deliverable

Per #187's acceptance: the backend theorem is called **parametricity** only if it quantifies
relationally over related backends; otherwise the paper says **representation independence**.
B0's record already draws this line ("Must not claim … that this is parametricity"). Part A
delivers *contextual* representation independence. Part B, if it lands, delivers full
abstraction. Neither is parametricity, and neither is described as such.

### Blocked-by check: the possible-world caveat

#187 adds: blocked by the PW wrapper spike *if* possible-world observations become
observable program behavior. They have not: the PW track (#189–#193) is labelled
future-work, nothing from it is merged, and the observation vocabulary in `lean/` is the
M2a claim-status interface (`Lara.Observation`, `Grounded.statusC`). F0 records this check.

---

## 2. Current-state audit (verified in-repo 2026-09-02)

| Asset | Where | Role |
|---|---|---|
| Core carrier `Unit` = Σ + policy + `args` + `atts` (**no Γ field**); `CheckedUnit canon Γ CertOk`; `checkUnit` + `checkUnit_complete` (takes a `ground : List Atom`) | `lean/Lara/Unit.lean`, `Check/Unit.lean:130,132,227,230` | Fragments decompose this. Γ is an *index*, not a field, so `link` returns `Unit × Γ` (D2); `Fragment` needs a `ground` field (D10) |
| `AttackComplete` — an **all-pairs** closure condition and a `checkUnit_complete` hypothesis; `Covered` closes under subarguments | `Compile.lean:505,515`, `Check/Unit.lean:242` | Why `link` **saturates** (D2), and why the semantic interface is the contrary-visible occurrence profile, not the declared imports (§6 R6) |
| `CheckedProgram.complete : ∀ w ∈ args, ∃ C, HasSupport … w C []`; leaf case needs `Gamma l = some p` | `Compile.lean:480` | **An open fragment has no `CheckedProgram`.** Forces `fragmentAF : Fragment → ImportEnv → Option AF` (D10) |
| `CheckedProgram.nodup : args.Nodup`; `checkUnit_complete`'s `hargs` | `Compile.lean:477`, `Check/Unit.lean:234` | Structural term equality, so `link` **dedupes** rather than rejects (D3) |
| `CheckedUnit.nodes` conclusion cache + `nodes_terms`; `CheckedNode.conclusion` | `Unit.lean`, `Compile.lean:493` | `crossAtts` reads cached conclusions, relative to an import environment. `Unit.lean`: "No support re-inference is needed downstream" |
| **Relabel machinery**: `coveredB_relabel`, `edgeB_relabel`, `checkedAF_relabel`, `mapAssur` | `Erase.lean:39,198,223,243` | **Part A's engine.** F2's congruence is these plus saturation commutation |
| Result 9 + its non-vacuity discipline | `Erase.lean:259`, `EraseTransport.lean:11,214` | The whole-program special case; and the precedent that a theorem ships with a by-construction non-vacuity witness |
| **Γ extension transport**: `HasSupport`/`HasAttack` weakening under `hext`, `buildGamma_append_*` | `Update.lean:284-348,510-522` | F1's Γ-merge transport. Already proved; do not rebuild |
| `Admission.buildGamma : List (LeafId × Atom) → LeafId → Option Atom` | used at `Update.lean:39` | The canonical Γ builder `gammaFrag` feeds |
| Four-state `statusC` (`gap` iff support empty), `Claim` holds **argument lists**, `Claim.holes` | `Grounded.lean:495,501,516` | Exports are conclusions, claim rebuilt post-link (D4). `holes` is never used by D4 — see the M3 partial discharge (D12) |
| M2a observation transport, carrier-boundedness, `not_observe_congr_of_unbounded_support` | `Observation.lean:454,650` | Stating observations without reading attacks off-carrier |
| B0 occurrence vocabulary, firewall, accounting laws, frozen registry | `BackendComposition.lean` | "A compatible context may not redefine the registry" |
| `Realizability.Realization` / `Realizable` — but `compiled_iso` targets the **whole unit's** `StructuredAF` | `Realizability.lean:153,167,212` | **Not directly usable for Part B's context construction** (the target AF is the unknown). Only the structure-with-trivial-iso is, degenerating to `checkUnit_complete` + a ground obligation (D10) |
| `oneSelfEdge_not_realizable` — realization fails under `emptyDefeat` | `Examples/Realizability.lean:80` | Seeds the `LabelExpressive` negative witness (D7) |
| `m2bPolicy` asymmetry: `d_attacks_b` / `b_does_not_attack_d` | `Complexity/Context.lean:148,177` | The intended **positive** `LabelExpressive` witness (D7) |
| Contraries are **patterns** with universally quantified variables; `ConflictAttackable` is `True` on leaves; rebut needs `.defeasible` | `Attack.lean:85,552,564,592`, `Compile.lean:405,407` | Why "fresh" atoms cause collateral attacks and why symmetric tables force only `{in, undec}` (§6 R7) |
| M2b checked-family construction precedent, ~3,000 lines for one formula-indexed family | `Complexity/Gadget.lean`, `Complexity/Reduction.lean` | The cost anchor for any realization gadget (Part B) |
| Decidable-check characterization pattern | `Policy.firstDuplicateRuleId?_none_iff` etc., used at `Check/Unit.lean:243,253` | The `linkOk` characterization-lemma pattern (D3) |
| M5 surface calculus + verified elaboration | `lean/Lara/Surface/*` | Surface-transport corollary |
| Library root + curated "Currently mechanized" index | `lean/Lara.lean` | Import line per phase; prose index entry at closeout |

Open issues that touch M4: **#184 (M1 image characterization)** is still open; it bears on
Part B's realization work only, not on Part A. #204 is orthogonal.

---

## 3. Design decisions to freeze in F0

- **D1 — contexts live at the core `Unit` level.** Quantifying over surface contexts would
  entangle the result with M5's elaboration guards. M5's preservation + reflection gives a
  *surface corollary* instead. The theory-depth plan's ordering ("M5 defines the surface
  calculus before M4 quantifies over source contexts") is honored by that corollary.

- **D2 — fragment shape, and linking as a *saturating* operation.** A fragment carries its
  own Γ-part, its `ground` list (D10), rule *instances* and attacks, an **import** interface
  and an **export** interface of observable *conclusions*:

  ```lean
  structure Fragment where
    gammaFrag : List (LeafId × Atom)   -- leaves this fragment declares
    ground    : List Atom              -- checkUnit requires it (Check/Unit.lean:132)
    args      : List Support.SupportTerm
    atts      : List Attack.Attack
    imports   : Interface               -- ids the context must supply
    exports   : List Atom               -- observable exported CONCLUSIONS

  def link : Context → Fragment →
             Option (Lara.Unit × (LeafId → Option Atom))
  ```

  `link` is partial, defined only under hygiene, and it **saturates and dedupes**:

  ```
  Γ    := Admission.buildGamma (C.gammaFrag ++ F.gammaFrag)
  args := dedup (C.args ++ F.args)                 -- structural merge, D3
  atts := C.atts ++ F.atts ++ crossAtts C F        -- saturation
  ```

  `crossAtts C F` enumerates cross-boundary pairs whose conclusions satisfy
  `Attack.ContraryMatch canon dp` with a `ConflictAttackable` target. Without it the linked
  program fails `Compile.AttackComplete` (an all-pairs condition) and `checkUnit_complete`'s
  `hattackComplete` premise is unsatisfiable. **Fixed across linking: `canon`, Σ, the policy
  (including `defeat`), the backend registry** (#187: contexts "may add fresh evidence,
  attacks, and rule instances but may not redefine the fixed policy or registry"). **Γ is
  not fixed** — it is what fragments contribute, transported by `Update.lean:284-348`.

- **D3 — hygiene, dedupe, and rejection.** Identifier namespaces are disjoint except at
  declared imports; a decidable `linkOk` guards `link`. Because `SupportTerm` equality is
  *structural*, identifier disjointness does not prevent term collision — a context argument
  built only from imported leaf ids can be structurally identical to a fragment argument.
  **Duplicate terms are merged, not rejected.** Rejecting them would make contextual
  equivalence syntax-sensitive and refute every congruence coarser than term-set equality:
  given `F₁` containing `t ∉ F₂.args`, the context declaring `t` would link with `F₂` and be
  rejected against `F₁`. Merging is semantically harmless (identical terms have identical
  edge sets, `Compile.lean:45-47`) but F1 proves it status-preserving.

  | Class | Behavior |
  |---|---|
  | R-L1 duplicate identifier outside the import interface | reject, witness |
  | R-L2 unsatisfied import | reject, witness |
  | R-L3 Σ / policy / registry mismatch | reject, witness |
  | duplicate support term across the boundary | **merge**, with a status-preservation lemma |

  F1 ships `linkOk_eq_true_iff`-style characterization lemmas (the
  `Policy.firstDuplicateRuleId?_none_iff` pattern, `Check/Unit.lean:243,253`) so proofs and
  witnesses discharge by lemma rather than whole-predicate `decide` — `native_decide` is
  banned (D9) and `linkOk` scans pairs.

- **D4 — observation.** Exports are **conclusions** (`List Atom`); the `Grounded.Claim` for
  each is rebuilt from the *linked* program's checked nodes before `statusC` is applied.
  `Grounded.Claim` holds argument *lists*, not a proposition, and `statusC` returns `gap`
  exactly when support is empty (`statusC_gap_iff`), so a context that supplies support for
  an exported conclusion flips the observation; pinning claims at fragment-definition time
  would make that invisible. Stated through the M2a boundedness discipline. Grounded only;
  no `ExtensionSemantics` generalization.

- **D5 — Part A needs no logical relation.** The committed theorem is a congruence over the
  *relabel* relation, not over a semantic relation. `LogRel` is deferred to Part B, and its
  design is reopened there because the declared-import formulation is refuted (§6 R6).

- **D6 — the backend result is the acceptance-profile generalization, not result 9.**
  F2's theorem: two registries with equal *acceptance profiles* on a fragment's certificate
  occurrences yield contextually indistinguishable fragments. No injectivity, no relabel.
  `Erase.backend_replacement` is a *sanity instance*, and the plan records explicitly that
  the corollary route to it is weaker than its existing two-line
  `rw [checkedAF_relabel …]` proof, so nobody mistakes it for progress (#187 boundary: "Do
  not restate the existing replacement theorem under a stronger name").

- **D7 — `LabelExpressive`, Part B's completeness hypothesis (defined in Part B, sketched
  here).** Completeness is false without a condition on the policy. Beyond `emptyDefeat`,
  forcing `out` needs the policy to supply either an asymmetric contrary pair or a
  strict-rooted attacker, since `ConflictAttackable` is unconditionally `True` on leaves
  and rebut needs `.defeasible`; a purely symmetric contrary table forces only
  `{in, undec}`. Contraries are also *patterns* with universally quantified variables, so a
  "fresh" atom on the same predicate still matches and forces collateral attacks — the
  forcing gadget's correctness is relative to atoms unused by *both* fragments, an explicit
  freshness side-condition. Positive witness: `m2bPolicy`'s asymmetry
  (`Complexity/Context.lean:148,177`). Negative witness: `emptyDefeat`, seeded by
  `Examples/Realizability.lean:80`.

- **D8 — no Haskell conformance vector.** M4 adds no checker, CLI, wire, or corpus surface
  (§7). `link` is a Lean-side operation with no surface syntax, so a `lara check` vector
  would hand-write an already-linked program, testing the checker rather than the calculus.
  F0 records "none required" *with this reason*.

- **D9 — axiom and proof discipline.** Standard trio only, no `native_decide`, sorry-free at
  every phase boundary, `AxCheck.lean` extended with every new theorem, `lean/Lara.lean`
  import line added in the phase that creates each module, name-map entries at closeout.

- **D10 — the fragment carrier.** An open fragment has **no** `CheckedProgram`:
  `Compile.lean:480` requires closed support, and a fragment referencing imported leaf ids
  has no `HasSupport` derivation. F1 therefore delivers
  `fragmentAF : Fragment → ImportEnv → Option AF` (a compile under a hypothetical Γ
  extension) plus re-indexing transport into the linked program's positional
  `Grounded.Arg = Nat` (`Compile.lean:597`). "Checked fragment" always means *relative to an
  import environment*. `Realizability.Realization` is **not** the construction target for
  Part B: its `compiled_iso` targets the whole unit's `StructuredAF`
  (`Realizability.lean:167`), which is precisely the unknown; Part B uses
  `checkUnit_complete` plus the `ground_covers` obligation directly.

- **D11 — context composition.** Congruence is unstateable without
  `compose : Context → Context → Option Context`, with its own hygiene and associativity.
  F1 delivers it. (With contexts closed under composition, congruence for an equivalence is
  short — the content is in the operator, which is where the cost sits.)

- **D12 — M4's openness is leaf-name openness only.** `docs/theory-m3-source-updates.md:313`
  names "holes" among the retained obligations. A term-level hole — an argument with
  unresolved critical-question obligations (`HasSupport … w C O`, `O ≠ []`) that the context
  discharges — is unrepresentable here: `Compile.lean:480` forces `O = []` on every declared
  argument, and discharges live inside the term (`D : List (QuestionId × SupportTerm)`), not
  in a name environment. `Grounded.Claim.holes` is likewise unused by D4. Closeout therefore
  marks the M3 contextual-adequacy debt **partially** discharged, and term-level holes get
  their own issue.

---

## 4. Diagrams

### 4.1 The linking pipeline

```
FIXED ACROSS LINKING: canon, Σ, policy (incl. defeat), backend registry
NOT fixed: Γ — fragments contribute it, Update.lean:284-348 transports it

  Context C                                     Fragment F
  ├ gammaFrag, ground                           ├ gammaFrag, ground
  ├ args, atts                                  ├ args, atts
  ├ hole : the □                                ├ imports : Interface
  └ imports / exports                           └ exports : List Atom
                    │                         │
                    v                         v
              ┌────────────────────────────────────┐
              │  linkOk  (decidable)               │
              ├────────────────────────────────────┤
              │  R-L1 duplicate identifier         │──► reject (side + identifier)
              │  R-L2 unsatisfied import           │──► reject (side + identifier)
              │  R-L3 Σ / policy mismatch          │──► reject (both values)
              └──────────────┬─────────────────────┘
                             │ true
                             v
  ┌──────────────────────────────────────────────────────────────────────┐
  │ link                                                                 │
  │   Γ    := Admission.buildGamma (C.gammaFrag ++ F.gammaFrag)          │
  │   args := dedup (C.args ++ F.args)          ◄── MERGE, not reject.   │
  │           Rejecting term collisions would make CtxEquiv syntax-      │
  │           sensitive and refute congruence (D3).                      │
  │   atts := C.atts ++ F.atts ++ crossAtts C F ◄── SATURATION.          │
  │           Without it the linked unit fails Compile.AttackComplete    │
  │           (ALL-PAIRS) and checkUnit_complete does not apply.         │
  └──────────────────────────────┬───────────────────────────────────────┘
                                 v   Lara.Unit × Γ
                  checkUnit Γ reg ground  /  checkUnit_complete
                                 v
                     CheckedUnit canon Γ (certOkOf reg)
                                 v   Erase.checkedAF
                            Grounded.AF
                                 v   per exported ATOM p: claimFor linked p
                                     (support recomputed from the LINKED nodes,
                                      so a context-supplied gap-flip is visible)
                                 v   Grounded.statusC
                          obs : Observation

  NOTE (D10): an OPEN fragment has no CheckedProgram of its own —
  Compile.lean:480 forces closed support. Anything said about a fragment
  alone goes through fragmentAF : Fragment → ImportEnv → Option AF.
```

### 4.2 Part A — the congruence theorem

```
        F                              mapAssurFrag f F          (f injective,
        │                                      │                  acceptance-
        │  link C ·                            │  link C ·        preserving)
        v                                      v
   linked unit L₁  ───── relabel by f ─────►  linked unit L₂
        │                                      │
        │  saturation COMMUTES with relabel:   │
        │  f preserves conclusions, so         │
        │  ContraryMatch and ConflictAttackable│
        │  are invariant, so crossAtts C F     │
        │  maps onto crossAtts C (relabel F)   │  ◄── THE ONE NEW LEMMA
        v                                      v
   checkedAF L₁  ═════ definitionally equal ═══ checkedAF L₂
        │              (Erase.checkedAF_relabel, built on
        │               coveredB_relabel / edgeB_relabel)
        v                                      v
      obs L₁            =                    obs L₂     for every admissible C fixed by f

  Immune to the interface problem (§6 R6): a uniform relabel preserves the whole
  occurrence profile, so "what is the semantic interface" never has to be answered.
```

### 4.3 Part B — the two directions, and why they are gated

```
      LogRel F₁ F₂                                    CtxEquiv F₁ F₂
 (must be fragment-local, no context             (∀ C,
  quantifier — that is what keeps R1 shut)        obs C F₁ = obs C F₂)
            │                                                │
            │        logrel_sound                            │
            ├───────────────────────────────────────────────►│
            │  BUT: over DECLARED imports this is REFUTED.   │
            │  AttackComplete is all-pairs + Covered closes  │
            │  under subarguments, so a context can attack   │
            │  a NON-import fragment argument. And grounded  │
            │  is a fixpoint over the LINKED AF, so a        │
            │  non-EXPORTED boundary argument feeds back     │
            │  into an export. Interface must be the whole   │
            │  contrary-visible occurrence profile, both     │
            │  emitted and observed sides.  ── §6 R6         │
            │                                                │
            │        logrel_complete                         │
            │◄───────────────────────────────────────────────┤
            │  REQUIRES LabelExpressive policy (D7):         │
            │    emptyDefeat        → no attack types at all │
            │    symmetric contraries → only {in, undec}     │
            │    pattern contraries → collateral attacks     │
            │  Positive witness: m2bPolicy asymmetry         │
            │  Negative witness: emptyDefeat                 │

  WIDENING RISK: an interface = full occurrence profile makes LogRel roughly
  "same terms modulo contrary-invisible decorations" ≈ Erase.mapAssur
  generalized — R1's tautology trap arriving through the INTERFACE rather
  than the quantifier. This is what the Part B gate exists to test.
```

---

## 5. Phases

Every phase: `lean/Lara.lean` gains the import line for any module it creates (otherwise
`lake build` does not cover it), `AxCheck.lean` gains one entry per new theorem, and the
phase's witnesses land in `lean/Lara/Examples/Linking.lean` (the convention held by
`Examples/{AttackCompleteness,BackendComposition,Realizability,Update,Surface}.lean`).

---

## PART A — committed

### Phase F0 — design-freeze spike (gates everything)

*Deliverable:* `docs/theory-m4-context-calculus-decision.md` + compiling Lean *definitions*
(no theorems) in `lean/Lara/Context/Fragment.lean`.

- [x] Record the PW non-blocking check (§1) and the D1 reading of the plan ordering.
- [x] Freeze D1–D4 and D8–D12 as compiling Lean definitions: `Fragment` (with `ground`),
      `Interface`, `Context`, `compose`, `linkOk`, `link` (saturation + dedupe), `fragmentAF`,
      `obs`.
- [x] Record the Part A / Part B split and its rationale (the two obstructions in §1).
- [x] Sketch `LabelExpressive` (D7) and name `m2bPolicy` as its intended positive witness —
      *definition and discharge both belong to Part B*, but F0 records the shape so Part B's
      gate has something to test.
- [x] Consult the AF-decomposability precedent (Baroni et al. 2014; grounded transparency)
      and record which statements we import as *design guidance* (nothing cited as a proof
      substitute — everything re-proved over our carrier).
- [x] Record D8 (no Haskell conformance vector) with its reason.
- [x] **Gate (three outcomes, M2b-style):** PROCEED / RESHAPE (record obstruction, revise,
      re-review) / STOP (invoke the tracker drop policy, record it, close nothing silently).

### Phase F1 — context calculus mechanized

*Modules:* `lean/Lara/Context/Link.lean`.

- [x] `Fragment`, `Interface`, `Context`, `linkOk` (decidable), `link`, `crossAtts`, `dedup`,
      freshness/hygiene lemmas.
- [x] **`compose : Context → Context → Option Context`** with hygiene and associativity
      (D11). Congruence is unstateable without it.
- [x] **`fragmentAF : Fragment → ImportEnv → Option AF`** plus re-indexing transport into the
      linked program's positional `Grounded.Arg = Nat` (D10).
- [x] `linkOk` characterization lemmas (`linkOk_eq_true_iff` and per-class variants).
- [x] **Saturation correctness:** `link_attackComplete` — the linked `atts` satisfy
      `Compile.AttackComplete` for the linked `args`.
- [x] **Dedupe correctness:** merging structurally identical terms preserves every claim's
      status (identical terms have identical edge sets, `Compile.lean:45-47`).
- [x] **Γ transport:** the linked Γ extends both fragment Γs and derivations transport, via
      `Update.lean:284-348` and `buildGamma_append_*`.
- [x] **Linking respects checking:** `link_checked` — a well-linked composition yields a
      `CheckedUnit`, via `checkUnit_complete` (reusing the #212 compositional lemma style,
      not manual `CheckedUnit` construction — the rejected Route B of that plan).
- [x] Witnesses: one per ill-linked class (R-L1..R-L3); a term-merge example; **a link that
      SUCCEEDS** (without it `link_checked` is vacuous — the obligation `EraseTransport.lean:11`
      discharges for result 9); **a `crossAtts`-nonempty example** (a `crossAtts` returning
      `[]` would still typecheck); a `ContraryMatch`-but-not-`ConflictAttackable` example;
      a `compose` associativity example.
- [x] `lean/Lara.lean` import; `AxCheck.lean`; commit.

### Phase F2 — contextual adequacy of backend replacement (the headline)

*Modules:* `lean/Lara/Context/Equivalence.lean`.

- [x] `obs` as a closed outcome over incompatibility, checker rejection, or exported statuses
      (D4); `CtxEquiv F₁ F₂ : Prop` compares that detailed outcome in every context.
- [x] **`link_relabel_commutes`** — the one new lemma: an injective, acceptance-preserving
      relabel `f` preserves conclusions, hence `ContraryMatch` and `ConflictAttackable`,
      hence `crossAtts C F` maps onto `crossAtts C (mapAssurFrag f F)`.
- [x] **`backend_replacement_congruence`** — for every admissible context `C` satisfying
      `FixesContext f C`, `obs C F = obs C (mapAssurFrag f F)`. Via
      `link_relabel_commutes` plus `Erase.coveredB_relabel` / `edgeB_relabel` /
      `checkedAF_relabel`.
- [x] **Generalization (D6):** two registries with equal acceptance profiles on the
      fragment's certificate occurrences give the same conclusion, with no injectivity and no
      relabel. **Witness: a pair that is NOT an injective relabel** — without it this
      collapses into result 9 and adds nothing.
- [x] **Congruence under composition:** the result is stable under embedding into any larger
      context, via `compose` associativity and hygiene transport (D11).
- [x] Witnesses: all four `statusC` outcomes reachable through `obs`; the **gap-flip** (a
      context supplying support for an export, `gap → justified`); distinct incompatible
      and checker-rejected observations; a `CtxEquiv` **negative** pair with its
      distinguishing context; and an accepted empty-exports observation (`.observed []`).
- [x] State `Erase.backend_replacement` as a sanity instance, with an explicit note that the
      corollary route is weaker than its existing `rw [checkedAF_relabel …]` proof, so nobody
      mistakes the re-derivation for progress.

### Phase F3 — Part A closeout

- [x] Surface-transport corollary via M5 preservation/reflection (D1). **The corollary is
      landed (`Lara.Context.surface_directAF_relabel`/`_link`); the worked surface *pair*
      witness is NOT — every accepted surface fixture rests on `native_decide`, which D9
      bans. Recorded in the closeout record §4 and filed as issue #227.**
- [x] **Naming audit:** the theorem is *contextual representation independence*. Not
      parametricity (no relational quantifier over backends). Not full abstraction (no
      logical relation, no completeness). Every doc and paper pointer uses the precise name.
- [x] `docs/theory-m4-contextual-adequacy.md`: durable claim-boundary record (May claim /
      Must-not-claim table, B0-style), including the M3 contextual-adequacy debt marked
      **partially** discharged (D12: leaf-name openness only) and a pointer to #217.
- [x] `docs/paper-lean-name-map.md` entries for every stable declaration the paper needs.
- [x] `lean/Lara.lean` "Currently mechanized" prose entry.
- [x] `AxCheck.lean` final sweep.
- [x] Update #187 and #180 with Part A closed; **do not close #187** if Part B is still live.

---

## PART B — optional, separately gated

**Entry gate.** Part B is entered only after Part A lands *and* a recorded decision says the
logical relation is reachable in a non-tautological form. The gate's job is to answer §6 R6:
does an interface wide enough to be sound (the full contrary-visible occurrence profile,
emitted *and* observed sides separated) still yield a relation that is more than
`Erase.mapAssur` generalized? If the honest answer is no, Part B does not start and #187
closes on Part A with the boundary recorded.

### Phase G0 — soundness spike (unlanded, unclaimed)

- [ ] Explore the soundness argument over a candidate interface **before** freezing the
      relation. Nothing here is landed and nothing is claimed. #187's acceptance criterion is
      that the relation not be reverse-engineered *from the theorem*, not that no exploration
      precede it — and freezing at minimum information is what makes an honest discovery
      during soundness procedurally indistinguishable from failure.
- [ ] Output: a written recommendation for the interface definition, with the collapse risk
      assessed against `Erase.mapAssur`.

### Phase G1 — the logical relation, frozen

- [ ] Define `LogRel F₁ F₂` over the **contrary-visible occurrence profile**, with emitted
      and observed sides separated, and with D5(c)'s acceptance clause resolved (either
      context-quantified, which reopens R1, or accompanied by a proof that link-definedness
      is determined by the import environment).
- [ ] Define `LabelExpressive` (D7).
- [ ] **Freeze record with an amendment procedure.** A dated entry states the relation is
      fixed before either direction is attempted (#187). A later change does **not**
      silently void prior work: it requires a recorded, reviewed amendment naming what
      changed, why, and which prior results survive. The amendment path exists so an honest
      G2 discovery is a documented revision, not a procedural failure.
- [ ] Sanity theorems: `LogRel` is an equivalence on same-interface fragments; reflexivity
      witness; **a same-interface pair on which `LogRel` FAILS** (else both directions are
      vacuous).

### Phase G2 — soundness

- [ ] `logrel_sound : LogRel F₁ F₂ → CtxEquiv F₁ F₂` — grounded-fixpoint induction over the
      linked AF, reusing M2a's carrier-boundedness lemmas.
- [ ] Witness: instantiated on a worked pair with a nontrivial context.

### Phase G3 — completeness (own gate)

- [ ] `logrel_complete : LabelExpressive … → CtxEquiv F₁ F₂ → LogRel F₁ F₂` —
      contrapositive: from a separating interface labelling, construct a well-formed Lara
      context realizing it via `checkUnit_complete` plus the `ground_covers` obligation
      (**not** `Realizability.Realizable`, whose given-target shape does not fit — D10).
- [ ] Forcing sub-lemmas: `in` (unattacked support), `out` (needs an asymmetric contrary
      pair or a strict-rooted attacker — see D7), `undec` (fresh 2-cycle, the `examples/B`
      pattern), each with the explicit freshness side-condition that the forcing atoms are
      unused by *both* fragments, so pattern contraries do not cause collateral attacks.
- [ ] **`LabelExpressive` discharge** for `m2bPolicy` and the `examples/A`/`examples/B`
      policies. Without a positive witness the theorem has an unverified-nonempty hypothesis.
- [ ] **Boundary counterexamples:** `¬ LabelExpressive emptyDefeat` with an explicit
      `CtxEquiv`-but-not-`LogRel` pair, and a symmetric-contrary policy forcing only
      `{in, undec}`. These are deliverables, not failures.
- [ ] **Cost anchor:** M2b's checked-family construction is ~3,000 lines
      (`Complexity/Gadget.lean`, `Complexity/Reduction.lean`) for one formula-indexed family;
      this needs one parameterized by arbitrary interface labellings. Price accordingly.
- [ ] **Stop rule:** if completeness stalls beyond `LabelExpressive`, record the obstruction
      precisely, keep G2 under the honest name *adequacy of the logical relation*, do not
      rename it full abstraction, and take the outcome back through the gate.

### Phase G4 — Part B closeout

- [ ] Naming audit; `docs/theory-m4-full-abstraction.md`; name-map entries; `lean/Lara.lean`
      index; `AxCheck.lean` sweep; close #187 against the tracker's shared completion gate;
      update #180.

---

## 6. Risks

- **R1 — the logical relation collapses into the tautology trap (Part B).** Mitigated by
  keeping the relation context-quantifier-free, putting the completeness condition on the
  *policy* (D7), and gating Part B on G0's collapse assessment.
- **R2 — completeness needs realization power the fixed policy may not have.**
  `Examples/Realizability.lean:80` already proves realization fails under `emptyDefeat`, and
  the only *positive* realizability results in-repo are for the purpose-built M2b family.
  Realization power is policy-dependent; `LabelExpressive` carries that fact honestly.
- **R3 — grounded non-compositionality off the interface.** M2a proved observation transport
  fails without carrier-boundedness (`not_observe_congr_of_unbounded_support`). All
  statements inherit that discipline from the start.
- **R4 — saturation makes contexts less free than they look.** A context cannot *withhold* a
  cross-boundary attack: if its argument's conclusion contrary-matches an attackable
  fragment occurrence, `link` emits the edge. Part B's constructions must choose atoms
  matching *exactly* the intended occurrences.
- **R5 — effort.** M4 is the tracker's named highest-effort item. The Part A / Part B split
  is the mitigation: Part A is a complete, claimable theorem reachable from existing relabel
  machinery plus one lemma, so invoking the drop policy is a graceful downgrade rather than a
  milestone failure.
- **R6 — the semantic interface is wider than the declared imports (Part B, blocking).**
  `AttackComplete` is all-pairs and `Covered` closes under subarguments, so a context can
  attack any fragment argument whose conclusion contrary-matches — declared import or not.
  And grounded is a fixpoint over the *linked* AF, so a non-exported boundary argument feeds
  back into an export. A relation over declared imports is refuted on both sides; a relation
  over the full occurrence profile risks being `Erase.mapAssur` generalized. **This is the
  question the Part B entry gate exists to answer, and it is why Part B is not committed.**
- **R7 — symmetric contrary tables force only `{in, undec}`.** `ConflictAttackable` is
  unconditionally `True` on leaves (`Compile.lean:407`) while rebut requires
  `r.mode = .defeasible` (`Attack.lean:592`), so `out`-forcing needs policy asymmetry.
  Contraries are also patterns with universally quantified variables (`Attack.lean:85`), so
  "fresh" atoms on the same predicate cause collateral attacks. Both are D7 side-conditions,
  named up front rather than discovered mid-proof.

## 7. Out of scope

- Possible-world observations, approximation bridges, epistemic modalities (#189–#193).
- Generic-`ExtensionSemantics` contextual equivalence (grounded only) — **#216**.
- Relational quantification over related backends (true parametricity) — **#215**.
- **Term-level holes** (arguments with unresolved critical-question obligations discharged by
  the context) — unrepresentable under `Compile.lean:480`; **#217** (D12).
- Any Haskell checker/CLI feature; update-sequence algebra (M3 non-goals stand).
- Surface-level *primary* quantification (D1; surface appears only as a corollary).
- Haskell conformance vectors (D8 — "none required", with the reason recorded).

## 8. Verification (every phase)

```sh
cd lean && lake build
(cd lean && set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
bash scripts/test-check-axioms.sh
```

No `cabal test lara-test` run is required (D8). `docs/performance.md` measures the Haskell
checker bench; M4 adds no checker code, so it cannot move those numbers or the paper's
performance table.

**CI caveat carried from B0:** GitHub Actions is billing-blocked on the org; until restored,
the tracker's CI line is satisfied by the local stack above and by nothing else.

## 9. What already exists (reuse, do not rebuild)

| Sub-problem | Existing asset | Use |
|---|---|---|
| **Relabel invariance of the compiled AF** | `Erase.coveredB_relabel`, `edgeB_relabel`, `checkedAF_relabel` | **Part A's engine**; F2 adds only saturation commutation |
| Γ extension transport | `Update.lean:284-348`, `buildGamma_append_*` | F1 Γ-merge |
| Building Γ from a leaf list | `Admission.buildGamma` | `gammaFrag` feeds it |
| Argument conclusions without re-inference | `CheckedUnit.nodes`, `CheckedNode.conclusion` | `crossAtts`, relative to an import env |
| Dedupe rationale | `Compile.lean:45-47` (identical terms, identical edge sets) | D3's merge lemma |
| Decidable-check characterization pattern | `Policy.firstDuplicateRuleId?_none_iff` etc. | `linkOk` lemmas |
| Non-vacuity-by-construction discipline | `EraseTransport.lean:11` | The successful-link witness obligation |
| Milestone witness-module convention | `Examples/{AttackCompleteness,BackendComposition,Realizability,Update,Surface}.lean` | `Examples/Linking.lean` |
| Status observation | `Grounded.statusC`, `statusC_gap_iff` | D4's `obs` |
| Policy asymmetry, positive `LabelExpressive` witness | `Complexity/Context.lean:148,177` | Part B G3 |
| Realization failure under a degenerate policy | `Examples/Realizability.lean:80` | Part B G3 negative witness |
| Checked-family construction cost anchor | `Complexity/Gadget.lean`, `Complexity/Reduction.lean` (~3,000 lines) | Part B G3 pricing |

**Explicitly NOT reused:** `Realizability.Realizable`. Its `compiled_iso` targets a *given*
`StructuredAF` (`Realizability.lean:167`), but Part B's construction has the target AF as
its unknown. G3 uses `checkUnit_complete` plus `ground_covers` directly.

## 10. Implementation Tasks

Synthesized from the engineering review and the outside-voice pass.

- [x] **T1 (P1, human: ~1d / CC: ~1 session)** — `Context/Link.lean` — `link` saturates cross-boundary attacks
  - Surfaced by: Architecture issue 1 — `Compile.lean:515` `AttackComplete` is all-pairs
  - Verify: `link_attackComplete`; `crossAtts`-nonempty witness
- [x] **T2 (P1, human: ~4h / CC: ~30min)** — `Context/Fragment.lean` — `link` returns `Unit × Γ`; Γ via `buildGamma`
  - Surfaced by: Architecture issue 2 — `Unit.lean` has no Γ field; `CheckedUnit` is Γ-indexed
- [x] **T3 (P1, human: ~1d / CC: ~1 session)** — `Context/Link.lean` — `fragmentAF` + `Fragment.ground`
  - Surfaced by: Outside voice 3 — `Compile.lean:480` means an open fragment has no `CheckedProgram`
  - Verify: `fragmentAF` re-indexing transport into positional `Grounded.Arg`
- [x] **T4 (P1, human: ~4h / CC: ~30min)** — `Context/Link.lean` — dedupe duplicate terms, prove status-preserving
  - Surfaced by: Outside voice 4 — rejection refutes any congruence coarser than term-set equality
- [x] **T5 (P1, human: ~1d / CC: ~1 session)** — `Context/Equivalence.lean` — `link_relabel_commutes` + `backend_replacement_congruence`
  - Surfaced by: Outside voice 8 — the reachable headline; `Erase.lean:198,223`
  - Verify: non-relabel acceptance-profile witness so D6 does not collapse into result 9
- [x] **T6 (P1, human: ~1d / CC: ~1 session)** — `Context/Link.lean` — `compose : Context → Context → Option Context`
  - Surfaced by: Outside voice 7b — congruence is unstateable without it
- [x] **T7 (P2, human: ~4h / CC: ~30min)** — `Context/Equivalence.lean` — exports are `List Atom`, claims rebuilt post-link
  - Surfaced by: Architecture issue 3 — `Grounded.lean:495` `Claim` holds arg lists
  - Verify: gap-flip witness
- [x] **T8 (P2, human: ~3h / CC: ~30min)** — `Context/*` — `crossAtts` reads cached conclusions per import env
  - Surfaced by: Performance issue 12, amended by outside voice 3
- [x] **T9 (P2, human: ~2h / CC: ~20min)** — `Context/Link.lean` — `linkOk` characterization lemmas
  - Surfaced by: Performance issue 13 — `native_decide` banned, `linkOk` scans pairs
- [x] **T10 (P2, human: ~1d / CC: ~1 session per phase)** — `Examples/Linking.lean` — full witness coverage
  - Surfaced by: Test review issue 9 — four critical vacuity gaps
- [ ] **T11 (P2, human: ~2h / CC: ~15min)** — plan/docs — Part B entry gate + G1 amendment procedure
  - Surfaced by: Outside voice 7a — freezing at minimum information is a one-way door
- [x] **T12 (P3, human: ~30min / CC: ~5min)** — `lean/Lara.lean` — import per phase, index prose at closeout
  - Surfaced by: Code quality issue 7
- [x] **T13 (P3, human: ~1h / CC: ~10min)** — `docs/` — M3 debt marked partially discharged
  - Surfaced by: Outside voice 5 — `Compile.lean:480` makes term-level holes unrepresentable

## 11. Worktree parallelization strategy

| Step | Modules touched | Depends on |
|---|---|---|
| F0 definitions | `lean/Lara/Context/` | — |
| F1 calculus (link, compose, fragmentAF) | `lean/Lara/Context/`, `Examples/`, `Lara.lean` | F0 |
| F2 congruence + generalization | `lean/Lara/Context/`, `Examples/` | F1 |
| F3 Part A closeout | `docs/`, `Lara.lean` | F2 |
| G0 spike | — (unlanded) | F3 |
| G1–G4 | `lean/Lara/Context/`, `Examples/`, `docs/` | gate after G0 |

**Mostly sequential.** Every phase touches `lean/Lara/Context/` and
`lean/Lara/Examples/Linking.lean`, and each phase's theorems depend on the previous phase's
definitions. Two parallel seams exist:

- **Lane A / Lane B inside F1:** `compose` (D11) and `fragmentAF` (D10) are independent of
  each other once `Fragment` and `Context` are frozen in F0. Run them as two worktrees, merge
  before `link_checked`.
- **Three lanes inside G3:** the `LabelExpressive` discharge for `m2bPolicy`,
  `examples/A`, and `examples/B` are independent once `LabelExpressive` is defined in G1.

Conflict flag: both F1 lanes touch `lean/Lara/Context/Link.lean`. Split the file
(`Link.lean` / `Compose.lean`) before parallelizing, or run them sequentially.

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | `/codex review` | Independent 2nd opinion | 0 | — | — |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | CLEAR (PLAN) | 21 issues, 4 critical vacuity gaps, all folded |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | No UI scope |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | No public API scope |

**OUTSIDE VOICE:** Codex derailed into reading skill definitions and produced no review; the
Claude subagent fallback ran clean and returned 8 findings, all folded. Five contradicted
review decisions and were resolved in the user's favour: duplicate terms must be **merged**
not rejected (rejection refutes any congruence coarser than term-set equality); an open
fragment has **no** `CheckedProgram` so `fragmentAF` is required and
`Realizability.Realizable` is not the construction target; `Context ∘ Context` composition is
missing and congruence is unstateable without it; the F3 freeze was a genuine one-way door;
and the semantic interface is the contrary-visible occurrence profile, not the declared
imports, which refutes `logrel_sound` as originally stated.

**CROSS-MODEL:** Not applicable — Codex produced no findings. The single-model outside voice
drove the restructure; its premises were re-verified against `Compile.lean:405,407,480,505,515`,
`Attack.lean:85,552,564,592`, `Erase.lean:198,223`, and `Realizability.lean:167` before any
decision was taken.

**VERDICT:** ENG CLEARED — ready to implement Part A. CEO review recommended but not blocking:
the Part A / Part B split is a paper-scope judgment (does contextual representation
independence satisfy #187 and POPL 2028 without full abstraction?) that the repository cannot
answer.

NO UNRESOLVED DECISIONS
