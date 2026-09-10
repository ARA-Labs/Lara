# `rit` and LARA: verified comparison and design lessons

_Status: engineering and research note, rewritten 2026-08-04. Evidence snapshot: the supplied
28-page `rit.pdf`; `../rit` on clean branch `benchmarks-integration` at commit `24a6140`; LARA at
commit `c05412a`. “Paper” below means the design and results claimed in `rit.pdf`. “Current source”
means the executable path in those repository snapshots. This distinction matters because the paper,
CLI, and Python API currently enforce different contracts._

_Update 2026-08-05: `policy-admission-calculus-decision.md` freezes the repair described below.
Its runtime program and companion Lean metatheory program are separate from the byte-level
`lara-evidence@0.1` work under issue #78, which remains gated._

For cold readers: `rit` is a sibling project, a Lean-kernel-based research
integrity tool that attests numeric facts extracted from experiment logs
(sha256-pinned) and aggregates them through an AND/OR claim DAG. This note
compares it against LARA and answers what each should borrow from the other.

## 1. Answer first

Yes. The most useful idea LARA should borrow is **executable grounding for evidence leaves**:
content-address the evidence bytes, pin a versioned extractor or other leaf checker, replay it before
argument checking, and report exactly which bytes and checker produced the admitted leaf.

The second reusable idea is **externally witnessed registration**: bind a formal target or analysis plan to a content digest before an experiment, retain failures as inert records, and cite the witness receipt from later snapshots. A local Git log establishes ancestry, not wall-clock priority; it is not preregistration. This remains process metadata outside LARA’s argumentation semantics, and existing services should be used before building a LARA-specific history service.

LARA should not adopt `rit`’s analytical move as its organizing principle: narrowing research claims
to Lean-checkable arithmetic. That mechanism is valuable for numeric subclaims, but it does not
decide whether an experiment supports a scientific claim. LARA’s reason to exist remains the formal
argumentation layer: named support schemes, explicit critical questions, typed defeat, and
policy-relative status. A good composition is:

> `rit`-style checkers establish **what the bytes say**; LARA establishes **what those checked facts
> are allowed to support, what remains open, and what defeats the support**.

After enforcing the current admission policy at the presentation boundary, the first new capability
should be a real leaf-certificate seam. Today `certified` is vocabulary; it is not yet an end-to-end
replay path in the presentation checker.

Prior art narrows the novelty claim. SACM already organizes auditable claims, arguments, and evidence; ASPIC+ already gives strict/defeasible rules and typed attack locations; Micropublications and Evidence Graphs model scientific claims, data, methods, support, and challenge; PROV-O and Workflow Run RO-Crate model entity/activity/agent and workflow-run provenance. LARA's contribution must therefore remain its executable typed certificate language, checked compilation, replay identity, and structured-argumentation guarantees. Byte admission is a secondary assurance boundary unless real-artifact evaluation proves otherwise.

## 2. What each system is

### `rit` paper

The paper proposes a zero-trust research ledger with four main ideas:

1. split assertions into empirical groundings and analytical propositions;
2. re-extract empirical values from hash-locked evidence;
3. check analytical propositions with Lean 4;
4. accumulate claims in a content-addressed Claim Flow Graph, with open goals, disputes, revisions,
   and pre-registered “Turn 0” blueprints.

The paper’s strongest practical insight is not Curry–Howard. It is the refusal rule: if a value cannot
be re-derived from available evidence, the system should remain open or reject rather than let an LLM
guess. Table 6’s completed cell reports a 26-point uplift on PRL-Bench and zero degradation of
previously correct answers; the following prose calls the PRL-Bench gain “+31,” an internal numeric
inconsistency. The evidence is still preliminary: RQ3 is explicitly design-only, RQ4 has one completed
paper/prover cell (FTRL, 27% resolved), most model-pair cells are blank, and the PaperBench-E
pass-rate columns are labelled illustrative.

### `rit` current source

There are two materially different executable surfaces:

- The Git-shaped CLI in `src/rit.py` exposes `claim`, `add`, `commit`, `verify`, `inspect`, and `push`.
  `cmd_commit` compiles staged Lean files and archives the compiler output, but deliberately **does not
  block the commit**. `cmd_verify` recompiles tracked Lean files and compares the new report with
  `.rit/compile.log`; it does not replay the grounding manifest or require compilation to succeed. A
  fresh failing report that byte-matches an archived failing report is printed as `CLEAN` and exits
  successfully. This command checks report integrity and reproducibility, not proof validity.
- The stronger Python API in `src/rit/action/push.py:push` binds facts to evidence, checks same-label
  collisions, emits a self-contained Lean proof, calls `admit.gate`, commits an accepted event, and
  machine-settles a referenced open claim. Its logical gate is strict; its empirical guarantee is
  conditional: L2 declarative extractors replay, while accepted L1 callable values are later taken on
  trust. `action.audit` reruns the same gate and checks declared claim dependencies for cycles.

The paper’s “strict `rit commit` gate” therefore corresponds most closely to the programmatic
`action.push(..., gate=True)` path—not to the current CLI command named `rit commit`—with the L1
grounding caveat above.

### LARA current language

LARA is a snapshot language for policy-relative argument checking. A program declares:

- a natural-language claim and an adjacent formal target;
- evidence leaves with kind, provenance, and source references;
- strict or defeasible support-scheme instances;
- explicit critical-question discharges and holes;
- typed rebut, undercut, and undermine attacks; and
- claims whose four-state status is requested.

The checker validates support terms and strict certificates, compiles complete arguments to a Dung
framework, and computes `justified`, `gap`, `contested`, or `defeated` under grounded semantics. It
already has a closed strict-backend registry, exact dependency reporting for accepted strict
certificates, a natural-deduction backend, and an exact-rational table-recheck backend.

LARA does **not** establish empirical truth. More concretely, the current presentation path in
`Lara.Elaborate` constructs `Gamma` with an all-admit default; `Unit` retains only `(LeafId, Prop)` and
drops leaf kind, provenance, and source references before the core checker; and
`Replay.sourceCheckInput` carries the declared artifact digest into replay identity without resolving
or hashing the referenced artifact. These are the exact seams where `rit`’s grounding discipline is
useful.

Open obligations are not a second conformance defect. The term judgment records an obligation set
and only complete terms can become graph nodes, but the frozen `lara-core@0.1` executable contract
rejects a submitted open-obligation argument as `IncompleteArgument`. The M5 lowering convention
therefore represents an accepted `gap` by declaring no support argument; `Lara.Reporting` can still
locate holes on the reject path. Accepting a complete sibling while retaining an incomplete
alternative would be a useful `lara-core@0.2` extension, not a v0.1 bug fix.

## 3. Side-by-side comparison

| Dimension | `rit` paper | `rit` current source | LARA current source |
| --- | --- | --- | --- |
| Primary object | append-only Claim Flow Graph | Git history + self-contained Lean files + grounding manifest + declared claims | one artifact snapshot plus a versioned policy and replay identity |
| Main guarantee | admitted facts re-extract; propositions kernel-check; graph remains consistent | `action.push(..., gate=True)` kernel-checks proofs and replays L2 groundings, but trusts stored L1 values; CLI `commit` is non-blocking | argument structure, strict certificates, typed attacks, compiled status |
| World-facing boundary | hash-locked bytes, extractor, code state | L2 declarative extractors replay; L1 callables are accepted but not re-derivable | leaf proposition, provenance, opaque source refs; no byte replay in the core path |
| Analytical logic | Lean 4, mainly decidable arithmetic in the implemented path | one self-contained Lean compilation per proof file | backend-parametric strict seam (`nd@1`, `ra@1`) |
| Evidence-to-claim inference | usually narrowed to an arithmetic proposition | outside the kernel; claim settlement matches proved propositions to declared goals | explicit named defeasible scheme with critical questions |
| Non-monotonicity | revisions/disputes in the proposed ledger | collisions and rejected pushes attempt a best-effort inert `conflict` event; no active grounded defeat | first-class typed attacks and grounded argumentation semantics |
| Incompleteness | `OPEN` / honest reject | open claims plus rejected or ungated events | `gap` when no complete support is submitted; a submitted open-obligation argument honestly rejects under frozen v0.1, with holes available to reporting |
| Conflict handling | kernel contradiction, perspective refs, boundary-limit theorem | active push path checks same label/different value; contradiction helper is not in admission | declared contraries, typed attacks, duplicate-report quarantine, `contested`/`defeated` |
| Dependency source | theorem dependencies in the proposed CFG | grounding dependencies come from `#print axioms`; claim dependencies remain declared | support-term leaves are structural; backend dependencies are checker-reported and validated |
| History | foundational, append-only | Git-backed events, including `open`, `advance`, `settle`, `conflict`, `revert` | not a core construct; trajectories are represented by separate versioned snapshots |
| Trusted policy | extractor semantics, Lean/kernel configuration, collision policy | extractor code/spec, Python gate, Lean toolchain, declared claim edges | proposition signature, claim-support policy, backend registry/theories, checker |

The systems are complementary, not instances of one architecture. Both distrust the producer, but they
validate different relations:

```text
rit-style grounding:  evidence bytes --extractor/checker--> observed value
LARA support:          admitted leaves --named schemes/attacks--> claim status
```

Neither relation implies the other. A correctly extracted number can support a badly designed
comparison. A well-typed and undefeated LARA argument can rest on a fabricated leaf if the leaf was
only declared.

## 4. One example, with the guarantee boundary visible

Claim: “Method M improves accuracy on distribution D.”

A `rit`-style grounding can establish:

```text
sha256(table.csv) = h
extract(table.csv, row=mean, column=accuracy) = 0.784
0.784 > 0.771
```

That is valuable. It rules out a fabricated number and arithmetic drift. It does not establish that
0.771 is the correct baseline, that protocols were matched, that variance is acceptable, or that D is
the intended deployment distribution.

LARA represents those remaining steps explicitly:

```text
reports(exp, effect(M, accuracy, D, positive))
matched_protocol(exp)
adequate_power(exp)
---------------------------------------------- controlled_comparison
improves(M, accuracy, D)
```

An environment mismatch can undercut the rule instance; contrary measurement evidence can rebut its
conclusion; and an unreported variance check remains a located hole. The useful composition is to make
the first leaf a replay-checked leaf, then let the existing support and defeat calculus do the rest.

## 5. Paper claims versus the current `rit` implementation

This table is not a dismissal of the paper. It identifies which ideas are implemented enough to reuse
now and which are still design input.

| Paper/design claim | Current-source finding | Reuse status for LARA |
| --- | --- | --- |
| `rit commit` is a strict empirical + logical admission gate | `src/rit.py:cmd_commit` records Lean output and commits even on compile failure; `action.push` is the closest gated API, subject to its trusted-L1 caveat | copy the strict API contract, not the current CLI behavior |
| every receiver rechecks proofs and empirical groundings | `cmd_verify` checks report identity only and can report `CLEAN` for a reproducible compile failure; `action.audit` checks Lean, L2 groundings, cycles, and ungated events but accepts trusted L1 values | use one command whose name and behavior both mean successful full replay |
| the repository is checked as one Lean environment | `admit.check_proofs` invokes Lean separately for every `proofs/*.lean` file | do not infer cross-proof guarantees from admission |
| claim edges are theorem dependencies | `formal.uses.used_constants` is a TODO returning `[]`; `claim_deps` are declared | do not borrow this graph until dependencies are kernel-derived or structurally explicit |
| all empirical numbers re-extract | `grounding.bind` creates L1 or L2; `reextract` accepts L1 while stating the value is taken on trust | require replay for a LARA `certified` leaf; never label trusted input as rechecked |
| K-tier and L3 shrink the trust base | the active `bind` path emits only L1/L2; K/L3 are vocabulary/helpers, not reachable outcomes | treat K/L3 as future checker capabilities, not implemented evidence |
| Turn-0 blueprints prevent target drift | no active implementation under `src/rit` | borrow only an external registration-receipt contract; do not build a bespoke event envelope in this paper cycle |
| perspective refs and boundary-limit theorems resolve disputes | current active path records a `conflict` event and refuses a same-label collision; the paper’s perspective protocol is not wired | borrow inert conflict receipts first; keep LARA’s typed defeat semantics |
| contradiction is enforced at admission | `gate.entail.contradicts` exists, but `admit.gate` checks only proof files and groundings | do not cite contradiction-free graph admission as a shipping guarantee |
| failed attempts remain useful research knowledge | `_document_conflict` attempts to commit rejected/colliding attempts as inert events, but persistence is best-effort and failures are swallowed | borrow guaranteed, transactional failure receipts without letting them affect verdicts |

Two source-level points do hold strongly and are worth preserving:

1. `action.push(..., gate=True)` is transactional at the verdict boundary: a failed gate removes the
   generated proof and grounding-manifest changes before any `advance` event can settle a claim.
2. When `_document_conflict` succeeds, it separates **recording** a failed attempt from **accepting**
   it. `derive` reads only `advance` events for settlement, so a recorded failure receipt cannot turn
   a claim green. The current implementation does not guarantee that the receipt itself persists.

## 6. What LARA already gets right

### 6.1 It formalizes the inference `rit` leaves implicit

Converting “M improves” to `0.784 > 0.771` is not a neutral translation. It assumes metric validity,
baseline comparability, protocol parity, and scope. `rit` checks the numeric shadow after this
narrowing. LARA names the narrowing as a scheme instance and exposes its critical questions.

### 6.2 It distinguishes absence, defeat, and unresolved conflict

At the language-semantics level, `gap`, `defeated`, and `contested` are different outcomes:

- missing complete support produces `gap`;
- a complete support argument labelled `out` produces `defeated`;
- grounded `undec` produces `contested`.

The current executable path realizes all three outcomes for accepted units. Under the frozen v0.1
input contract, an explicitly submitted incomplete argument rejects rather than participating in an
accepted status computation; accepted corpus gaps are encoded by submitting no support argument.
Retaining incomplete alternatives beside complete ones would require a separately versioned
semantics change.

A rejected extractor should not automatically become a counter-argument. It is missing reliable
support unless someone constructs a checked contrary argument. LARA’s typing discipline preserves
that distinction.

### 6.3 Dependencies are part of term structure

A LARA support term contains its premise and discharge subterms. Its leaf dependency set is therefore
structural, not a separately declared graph. Strict backends report their consulted premise/theory
slots through the certificate seam. This is safer than building the roll-up over self-reported edges.

### 6.4 The formal target is already adjacent to the prose claim

The previous version of this note asked LARA to add a formal target next to claim text. That work is
already complete:

```lara
claim c1
  nl      = "Method M improves accuracy on distribution D"
  formal  = improves(M, accuracy, D)
  binding = { author = alice, audit-status = reviewed }
```

The remaining issue is not visibility. It is that the NL-to-formal binding remains unverified, as it
must, and needs independent audit.

## 7. What LARA should borrow

### Prerequisite — enforce the existing presentation admission policy

The frozen source contract is `policy-admission-calculus-decision.md`. Lookup uses the exact
`(LeafKind, Provenance)` key and defaults unmatched or omitted rows to `admit`; duplicate admission
keys and duplicate `LeafId`s are source invalidity. The boundary order is source invalidity, policy
R8, replay R13, duplicate-group R9, then core rejection. R8 is a valid source judgment distinct from
group R9 and core R1: it selects the first leaf in source declaration order whose exact key matches a
`reject` row and uses CLI exit 1, empty stdout, and exactly one deterministic stderr line identifying
the leaf id, kind, provenance, and matched admission row. Source invalidity uses exit 2/empty stdout;
replay/group/accepted/core-rejection paths retain core-verdict stdout.

Group consistency reads declared leaves before removal. Policy and group quarantine seeds are
unioned once, and one combined prune removes leaves, **every dependent argument** (including leaves
nested in premises and discharges), and attacks with a removed raw endpoint before the conditional
`checkUnit` run. Removing only `Gamma(l)` is wrong: a surviving occurrence would become an R1
whole-program rejection, not quarantine or a route to gap. Blocked reporting comes from that same
prune.

The runtime threads an opaque source carrier binding replay identity, the full declared unit, the
policy seed, the combined prune, and a canonical audit. The audit is in leaf declaration order;
`PolicyQuarantine` precedes every causing `GroupQuarantine`, group causes occur once in group order,
removed arguments/attacks follow declaration order, and each removed leaf has one nonempty cause row.

Deletion is not a sound final status policy. Removing an unavailable attacker can improve a grounded label. Compute a conservative quarantine-relevance component on the declared presentation graph and report `evidence-blocked` for every affected root; preserve the smaller graph's core label only as a conditional diagnostic. Unrelated roots keep their normal status. A future version may use explicit incomplete-argumentation semantics to reduce overblocking.

Do not bundle open-obligation semantics into that repair. `IncompleteArgument` is the frozen v0.1
contract, and `corpus-units/LOWERING.md` deliberately represents accepted gaps with no submitted
argument. If accepted partial alternatives become a requirement, design them as `lara-core@0.2` and
refreeze the wire, proofs, corpus, mutations, measurements, and replay bundle separately.

The leaf-certificate seam below should extend the repaired admission boundary, not create a second
parallel path. It is gated under issue #78 and is not part of the policy-admission runtime or
metatheory program.

### Priority 0 — add a leaf-certificate replay seam

This is the highest-value language change. It closes the current gap between `kind = certified` and an
actually replayed evidence check.

The seam should parallel `strictCheck` but remain separate because it validates a different relation:

```text
leafCheck(delta@version,
          leafProposition,
          kappa)
  -> accept { checkedProposition, capabilities }
   | quarantine { locatedDiagnostic }
   | reject { locatedError }

runLeafCheck(snapshot, sourceRefs, leafCheck)
  -> outcome { runnerGeneratedEvidenceDeps, checkerIdentity, canonicalPayload }
```

Required properties:

1. **Closed registration.** An artifact selects a checker/version; it cannot upload executable verifier code.
2. **Content identity.** Every consulted evidence object and extractor/spec is digest-addressed.
3. **Deterministic replay.** Equal input bytes and checker identity produce equal results and diagnostics.
4. **Dependency accountability by construction.** Checker code obtains bytes only through an access API that records reads; the runner, not the checker, emits every evidence-object dependency.
5. **Conservative unavailability.** Quarantined evidence cannot make a public claim status stronger by deleting an attacker.
6. **Narrow guarantee.** Acceptance means the proposition was derived from those bytes according to that checker. It does not mean the experiment was well designed, the mapping is scientifically faithful, or the claim is true.
7. **Replay identity.** Selected leaf-checker versions, canonical payloads, and runner-resolved evidence digests appear in the verdict identity.

A possible presentation extension, not a frozen syntax proposal:

```lara
leaf e1 : reports(exp_3, effect(M, accuracy, D, positive))
  kind         = certified
  provenance   = checker(table-extract, 1)
  refs         = [evidence/table_2.csv#row=mean]
  verification = cert(table-extract@1, sha256:..., (column accuracy))
```

Until this exists, `certified` should be described as an admission annotation, not proof that LARA
replayed the referenced evidence.

### Priority 1 — represent grounding strength as capabilities, not one total rank

Borrow RIT’s distinctions, but not its automatic tier winner:

```text
asserted
cited
hash-locked
re-extracted
re-executed
kernel-replayed
```

These properties are not a universal epistemic ordering. Re-execution can be noisy; a kernel-checked
extractor can still extract the wrong field; independent replication and source attribution are
orthogonal. Record a capability set in the leaf verdict and let the versioned LARA policy decide what
is admissible for a particular scheme. Never let “higher tier wins” silently replace a typed rebut,
undercut, or undermine.

### Deferred protocol — cite external registration receipts, not a bespoke event log

An unsupported LARA claim already yields `gap`; adding another `open` status would be redundant. The useful part of RIT’s Turn-0 idea is a small external receipt containing a provider, immutable record ID, registered content digest, witness-issued time, and witness proof.

Use exact labels:

- `preregistered` only when a verified external immutable timestamp covers the goal or analysis-plan digest before the attempt;
- `prior-in-checkpoint-history` when content-addressed ancestry proves only that the goal precedes the attempt in that history;
- `post-hoc` when the goal and attempt first appear together or the goal follows the attempt.

The receipt is not a new LARA status and never enters `Gamma` or the AF. OSF-style time-stamped, read-only registrations are the reference model. Do not build a LARA event-log schema, validator, or Git backend unless evaluation identifies a workflow that existing registration services plus a digest receipt cannot express.

### Priority 1 — persist canonical rejection reports

A checker rejection often contains research knowledge: an extractor found a different value, a strict certificate failed, or an attempted support term left a mandatory question open. Preserve a report with:

- proposed construct and target;
- exact replay identity;
- evidence/checker dependencies available before failure;
- located diagnostic;
- source snapshot identity and, if one exists, an external registration receipt.

Reports must be **inert by construction**: they do not enter `Gamma`, the compiled AF, or claim status. An author may later cite one when constructing a regular negative-result claim or a typed attack. This copies the useful separation in `rit`’s `conflict` events without requiring a bespoke event log or confusing failure to verify with evidence of falsity.

### Priority 2 — expose an inspection and repair interface

RIT’s Git-shaped surface is more useful to agents than a checker that only emits a verdict. LARA
should add read-only tooling such as:

```text
lara inspect claim c1       # complete/incomplete supports, labels, attackers, holes
lara inspect leaf e1        # refs, checker replay, evidence digests, capabilities
lara explain verdict.json   # dependency cone and first decisive reason
lara diff old new           # which leaves/arguments/attacks changed each status
lara verify-artifact        # resolve digest, refs, and leaf certificates, then run full check
```

The commands should consume the same checked result as `lara check`, never reimplement semantics.
Diagnostics should remain stable and machine-readable so an agent can repair one located failure and
retry.

### Priority 2 — add stable measurand identities for cross-snapshot collision detection

LARA’s duplicate-report groups handle declared duplicates within one snapshot. RIT shows the value of
a stable identity for “the same measured cell” across revisions and agents. Add this to the event or
evidence layer, not to the argument kernel:

- a measurand key identifies the metric, scope, run/config, and selector;
- two different values for one key produce a conflict receipt;
- the key declaration is audited because measurand identity is itself an untrusted modeling choice;
- resolution requires explicit revision, new conditions, or a typed argument—not automatic overwrite.

## 8. What LARA should not borrow

1. **Do not make Lean the universal research kernel.** Keep Lean/RA/code checkers behind narrow
   registered seams. The argumentation core is the contribution.
2. **Do not collapse support into numeric entailment.** Numeric checks are strict substeps; the
   evidence-to-scientific-claim step remains defeasible.
3. **Do not use a scalar evidence tier as defeat semantics.** Evidence quality informs admission and
   schemes; typed attacks decide defeat.
4. **Do not accept declared graph edges as verified dependencies.** LARA’s structural support terms
   and checked backend dependency reports are stronger.
5. **Do not reject every contradiction from history.** Scientific disagreement is often the object to
   represent. Reject malformed programs, but preserve well-typed competing arguments and report
   `contested` or `defeated`.
6. **Do not put Git history or registration logic inside the frozen calculus.** External registration receipts may be cited by ordinary snapshots; local Git ancestry alone is not preregistration.
7. **Do not call trusted leaves “rechecked.”** A declared hash, provenance tag, or L1 callable is not
   byte-to-value replay.

## 9. Recommended implementation order

| Order | Change | Layer | Observable acceptance criterion |
| --- | --- | --- | --- |
| 0 | enforce the frozen source admission contract without changing `lara-core@0.1` | source boundary + driver/reporting | default-admit lookup; source/R8/R13/R9/core precedence; one policy+group prune and canonical audit; affected roots report `evidence-blocked`; all-admit inputs preserve current core bytes |
| 1 | inventory original artifact formats and freeze the evaluation contract | corpus/evaluation | at least two artifacts, ten leaves, two claim families, and two checker families are feasible without hand-authored assertion files |
| 2 | leaf-certificate checker interface plus closed deterministic checkers | new versioned evidence seam | altering bytes, selector, claimed value, checker version, or certificate rejects before support checking |
| 3 | traced artifact resolver and replay identity | decode/replay boundary | every object read is runner-reported; missing or changed objects fail preflight; equal identities replay byte-identically |
| 4 | conservative quarantine reporting | source reporting | a quarantined sole attacker cannot improve the public target status; unrelated roots retain normal status |
| 5 | capability reporting and `inspect` / full `verify-artifact` | policy + CLI/reporting | output separates byte checking, conditional core status, public status, and semantic-faithfulness limits |
| 6 | external registration-receipt contract only | documentation/protocol boundary | local Git order is never labelled preregistration; no history service enters the paper's TCB |

Do not modify `lara-core@0.1` merely to copy vocabulary. The byte-level evidence seam remains gated
under #78 and should be built only if the corpus inventory passes the frozen coverage gate. Evaluate
payload-to-result and proposition-to-result faithfulness with the proposal's two-annotator protocol.
Evidence admission is at most a secondary contribution; the structured-argumentation calculus
remains the paper's center.

## 10. Bottom line

The old comparison overemphasized which project was more “formal.” The useful distinction is simpler:

- `rit` is strongest at **local, byte-bound verification of a numeric fact** and at the workflow idea
  of immutable goals and attempts.
- LARA is strongest at **composing heterogeneous evidence into defeasible research arguments** and
  explaining gaps, conflicts, defeat, and reinstatement.

LARA becomes materially more useful when these strengths are composed. A claim should be able to say:

1. this leaf was re-derived from these exact bytes by this exact checker;
2. every object the checker read is in the replay identity;
3. this strict arithmetic/code step replayed under this backend;
4. this defeasible scheme licenses the scientific inference subject to these critical questions;
5. these typed attacks survive or defeat the argument under grounded semantics;
6. no unavailable evidence silently strengthened the public result; and
7. if a preregistration claim is made, this external witness fixed the registered digest before the attempt.

That is a stronger and more honest language than either “the Lean file compiles” or “the argument is well typed” alone. Items 1–2 certify transcription, items 3–6 certify policy-relative argument structure and reporting safety, and item 7 certifies only externally witnessed chronology. None alone proves empirical truth.

## 11. Source map

### `rit` paper

- `rit.pdf` §§3–4: Hume split, grounding tiers, Claim Flow Graph, disputes, Turn-0 blueprint, stated
  verification properties.
- `rit.pdf` §§5–7 and appendices: evaluation status, honest-reject behavior, limitations, red-team
  results, and future L3/Mathlib work.

### `rit` current source (`24a6140`)

- `../rit/src/rit.py`: `cmd_commit`, `cmd_verify`, `cmd_inspect`.
- `../rit/src/rit/action/push.py`: `push`, `_document_conflict`, transactional gate path.
- `../rit/src/rit/admit/__init__.py`: `_check_one`, `check_proofs`, `gate`.
- `../rit/src/rit/action/audit.py`: full API audit, cycle check, ungated-event check.
- `../rit/src/rit/grounding/__init__.py`: `bind`, `reextract`, `collision`, active L1/L2 behavior.
- `../rit/src/rit/formal/uses.py`: authoritative grounding dependencies; pending claim dependencies.
- `../rit/src/rit/derive/__init__.py`: open/settled derivation and weakest-link grade.
- `../rit/src/rit/gate/entail.py`: contradiction helper outside the active admission path.
- `../rit/src/tests/test_actions.py`: executable contract for the programmatic API.

### LARA current source (`c05412a`)

- `docs/spec.md`: frozen claim-support calculus, attack typing, grounded status, replay identity, and
  lowering boundary.
- `docs/lara-surface-grammar.md`: current presentation syntax.
- `src/Lara/Elaborate.hs`: presentation lowering and the current all-admit leaf context.
- `src/Lara/AST.hs`: presentation leaves versus checker-boundary `Unit`.
- `src/Lara/Replay.hs`: replay identity construction and preflight.
- `src/Lara/Strict.hs`, `src/Lara/Strict/ND.hs`, `src/Lara/Strict/RA.hs`: strict certificate seam and
  shipped backends.
- `src/Lara/SupportTerm.hs`, `src/Lara/Check.hs`, and `src/Lara/Driver.hs`: missing-leaf and
  open-obligation rejection, duplicate-group quarantine filtering, and the production boundary.
- `src/Lara/Compile.hs`, `src/Lara/Grounded.hs`, `src/Lara/Reporting.hs`: compilation, status, and
  diagnostics.
- `examples/running-example/` and `examples/rebuttal-replay/`: gap, defeat, reinstatement, and
  multi-snapshot behavior.

### External research anchors

- Dung (1995), grounded argumentation and non-monotonic acceptance: <https://www.cs.ait.ac.th/~dung/Site/Publications_files/n-games.pdf>
- Modgil and Prakken (2014), ASPIC+ structured argumentation: <https://doi.org/10.1080/19462166.2013.869766>
- Mailly (2024), grounded semantics for incomplete argumentation frameworks: <https://doi.org/10.1016/j.ijar.2024.109282>
- Clark, Ciccarese, and Goble (2014), Micropublications: <https://doi.org/10.1186/2041-1480-5-28>
- Al Manir et al. (2021), Evidence Graphs: <https://doi.org/10.1101/2021.03.29.437561>
- OMG SACM 2.3: <https://www.omg.org/spec/SACM/2.3/About-SACM>
- W3C PROV-O: <https://www.w3.org/TR/prov-o/>
- Workflow Run RO-Crate: <https://doi.org/10.1371/journal.pone.0309210>
- OSF registrations and preregistrations: <https://help.osf.io/article/330-welcome-to-registrations>
