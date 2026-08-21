# Replay bundles — format specification (`lara-replay-bundle@1`)

A **replay bundle** is a hermetic directory under `bundles/` that retains every
untrusted output of the M4b elaborator pipeline, so the run can be re-checked
later with only the bundle directory and the `lara` binary (review 1A). This
document is the complete format contract: directory layout, every filename, the
manifest and provenance schemas, the source-trace schema, the derivation rules
the elaborator must follow, and the canonicalization rules that make every byte
a function of the source and the trusted inputs only (reviews 2A/T4/T8).

This spec is written at task **B0** of the M4b walking skeleton
(`plans/research-proposal.md` §7, M4) and is binding on B1 (elaborator), B2
(replay), and B3 (golden + CI). The only
bundle today is `bundles/walking-skeleton/` (§2).

## 1. Decisions confirmed and scope honesty

- **D3 — deterministic harness first: CONFIRMED.** The producer is a
  deterministic Python script (PyYAML only, no live model, no network, no
  randomness, no wall-clock). Every derivation in §4 is a pure function of
  `source.yaml` and the trusted policy. LLM lowering and the `Lara.Json`
  surface are deferred to #30, gated on the D3 flip. Producer determinism is a
  *tested* property: B3's golden byte-diffs freshly emitted `emitted.lara` and
  `provenance.json` against the committed ones (review T5).
- **Task coverage (T1/T2), honestly stated.** The source exercises spec §11
  tasks **1–4 and 6** for real (§4 below). Task **5** (strict-backend /
  theory / certificate selection) is spec-conditional ("where a strict instance
  is certified") and **N/A** here: the frozen frontend has no support-term
  assurance syntax (`Lara.Syntax` forces `AssuranceNone`), the policy is
  all-defeasible, and the declared `nd@1` backend is inert. Strict-cert
  frontend work is issue #37. Task **2** is exercised as leaf extraction +
  source binding; the §4.3 duplicate-report situation (one measurand cell
  reported in two places) is **logged in provenance only** — no implementation
  layer carries duplicate-report groups (issue #38).
- **Hole lowering (verified against the TCB).** An argument with an open
  mandatory critical question is a whole-unit checker **rejection**
  (`Lara.Check.checkArguments` → `PEIncompleteArgument`, src/Lara/Check.hs;
  see also the E2 header comment), not an accept-with-holes. The B1 gate
  requires the emitted `.lara` to be *accepted*. The elaborator therefore
  lowers an explicit hole (§11 task 4) by **not emitting the incomplete
  argument** — the E2 mechanism: the claim's complete-support set is empty and
  `statusC` reports `gap`. The hole decision (which questions, why, from which
  source node) is recorded in the provenance log (§7). This is the only
  acceptance-compatible reading of "explicit hole creation" on the frozen
  frontend; the alternative (emit an `open` line) yields a reject verdict and
  fails the B1 gate.

## 2. Directory layout

Exactly one skeleton exists at B0: **`walking-skeleton`** — the M4b walking
skeleton, named after the milestone it closes (one structured source lowered
end to end, no hand-authored certificate).

```
bundles/walking-skeleton/
├─ source.yaml                  input trace (B0, hand-authored, T6 ceiling)   [committed at B0]
├─ empirical-v1.policy.lara     COPIED trusted policy (1A)                    [B1]
├─ emitted.lara                 elaborator output — the machine-produced cert [B1]
├─ provenance.json              per-§11-task derivation log, canonicalized    [B1]
├─ emitted.core.sexp            derived wire anchor (parse→elaborate→encode)  [B2]
├─ verdict.txt                  frozen `lara check` stdout bytes              [B2]
└─ manifest.json                trusted-input sha256s + identities, canon.    [B2]
```

No other files may appear in a bundle directory. File ownership:

| File | Producer | When |
| --- | --- | --- |
| `source.yaml` | human (B0) | committed before elaborator code lands (B0 gate) |
| `empirical-v1.policy.lara` | `elaborator/elaborate.py` (B1) | copied byte-for-byte from the canonical policy (§4.0) |
| `emitted.lara` | `elaborator/elaborate.py` (B1) | derivation rules §4 |
| `provenance.json` | `elaborator/elaborate.py` (B1) | schema §7 |
| `emitted.core.sexp` | B2 bundle writer | derivation §5 |
| `verdict.txt` | B2 bundle writer | derivation §5 |
| `manifest.json` | B2 bundle writer | schema §6 |

B1 writes its three files **transactionally** (review T9): stage in a temp
directory inside `bundles/walking-skeleton/`, rename into place only on full
success; a failed run leaves no partial or stale content.

## 3. Source format (`ara-mini-trace@1`)

`source.yaml` is a UTF-8 YAML 1.2 file with two top-level keys, `meta` and
`tree`. It follows the `ara/trace/*.yaml` flavor (nested tree, typed nodes, NL
narratives) at miniature scale.

```yaml
meta:
  format: ara-mini-trace@1           # source-format version id (exact string)
  artifact:
    id: <atom>                       # emitted `artifact <id> at …` header
    digest: "<digest string>"        # emitted verbatim after `at`
  policy: <policy id>                # trusted-input REFERENCE by id (instantiate, never define)

tree:
  - id: <node id>
    type: question | claim | experiment | dead_end
    title: "<NL>"
    children: [ <node>* ]            # nesting = "bears on / belongs to"
```

Node-type payloads:

- **`claim`** — the §11-task-1 input. Fields: `text` (NL claim string,
  emitted verbatim as the claim's `nl`), `subject: {method, quality,
  distribution}` (the claim's recorded topic — research metadata, three atoms
  matching `[a-z][a-z0-9_]*`), `stance: improvement` (the claim's polarity as
  stated), `author` (free string), `reviewed` (bool → `audit-status`).
- **`experiment`** — fields: `title`, `summary` (NL), optional
  `evidence_cells` (list).
- **`dead_end`** — fields: `title`, `narrative` (NL), optional
  `evidence_cells`. A dead end may produce evidence (support), counter-evidence
  (attack), or nothing logical (spec §7 conventions).
- **`question`** — fields: `title` only; structural root.

**Evidence cell** (the §11-task-2 input):

```yaml
- id: <cell id>
  topic: <controlled vocabulary, below>
  what: "<NL description of the cell>"
  value: "<display value, optional>"   # audit display only; never reaches emitted.lara
  recorded: run-output | paper-text
  refs: [ "<artifact-relative ref>"* ] # e.g. evidence/ow_table1.csv#row=mean
```

Controlled `topic` vocabulary (evidential *content*, research level — the
formal atoms are derived from it, never written here):

| topic | meaning |
| --- | --- |
| `positive-effect-report` | a result cell reporting a positive effect of the subject method |
| `randomization` | documentation of randomized allocation |
| `power` | documentation of an adequate-power analysis |
| `generalization` | attestation that the effect generalizes |
| `distribution-shift` | finding that the evaluation distribution shifted |
| `generalization-failure` | result cell showing the effect does not generalize |

**T6 ceiling.** The source contains research-level objects only. It MUST NOT
contain: formal propositions or atoms, policy rule ids, critical-question ids,
discharge or hole decisions, attack kinds or attack declarations, assurance or
certificate content. `subject`/`stance`/`topic`/`recorded` are the claim's and
evidence's *recorded research metadata*; predicate selection, arity, atom
identity, scheme selection, question binding, hole creation, and attack typing
are all derived by the elaborator (§4) and logged (§7). Node and cell ids match
`[a-z][a-z0-9_]*` so emitted identifiers derive without sanitization.

## 4. Derivation contract (binding on B1)

The elaborator reads `source.yaml` + the trusted policy **read-only**,
references trusted inputs by id, and defines none of them (spec §4/§5/§11).
Everything below is pinned; B1 has no design latitude.

### 4.0 Trusted policy copy (1A)

Copy `examples/E1/empirical-v1.policy.lara` (the canonical copy; all seven
`examples/*/empirical-v1.policy.lara` are byte-identical, md5
`ff2b17952d85756bec75da4811788724` — the E1↔bundle pair of that identity is
enforced by `test/walking-skeleton-golden.sh`, so this citation is
informative, not the check) to `bundles/walking-skeleton/empirical-v1.policy.lara`.
The name is forced by the checker's co-located policy resolution
(`policy empirical-v1` in `emitted.lara` resolves to
`empirical-v1.policy.lara` in the same directory — app/Main.hs D-Arch-2),
which is what makes the bundle hermetic.

### 4.1 Emitted header (fixed)

```
artifact <meta.artifact.id> at <meta.artifact.digest>
policy <meta.policy>
use backends [nd@1]
```

`nd@1` is the sole registered reference backend; it is inert for this
all-defeasible source and is recorded in the manifest (§6).

### 4.2 Per-§11-task derivations

**Task 1 — NL proposition formalization.** Each `claim` node emits one claim
declaration. `formal` is derived: predicate `improves` (from
`stance: improvement`) applied to `(subject.method, subject.quality,
subject.distribution)`. `nl` = `text` verbatim. `binding.author` = `author`;
`binding.audit-status` = `reviewed` if `reviewed: true` else `unreviewed`.
Claim id: node id `claim_<X>` → `c_<X>`.

**Task 2 — evidence-leaf extraction + source binding.** Each evidence cell
emits exactly one leaf, at the M0 default grain (per-result-cell). Cell id
`cell_<Y>` → leaf `e_<Y>`. Proposition derived from `topic` and the enclosing
claim's subject + the experiment the cell binds. A cell nested under an
experiment binds that experiment (`exp_<Z>` → constant `exp_<Z>`). A cell
nested under a `dead_end` (not under an experiment) binds its claim context's
supporting experiment — the unique experiment node of that claim carrying a
`positive-effect-report` cell (the experiment task 3 instantiates the scheme
over). A source where a dead-end-nested cell has zero or multiple candidate
supporting experiments is malformed (6A):

| topic | derived proposition |
| --- | --- |
| `positive-effect-report` | `reports(exp_Z, effect(M, Q, D, positive))` |
| `randomization` | `randomized(exp_Z)` |
| `power` | `powered(exp_Z)` |
| `generalization` | `generalizes(M, Q, D)` |
| `distribution-shift` | `distribution_shift(M, Q, D)` |
| `generalization-failure` | `not_generalizes(M, Q, D)` |

`kind`/`provenance` derived from `recorded`: `run-output` →
`kind = observed`, `provenance = ai-executed`; `paper-text` →
`kind = attested`, `provenance = user`. `refs` = the cell's `refs`, in source
document order. A cell with more than one ref is the §4.3 duplicate-report
situation: one leaf carries all locations, and the situation is logged in
provenance (§7) — no group construct exists in any implementation layer (T2).

**Task 3 — inference-scheme selection and instantiation.** For each `claim`
with a descendant `experiment` carrying a `positive-effect-report` cell:
select from the trusted policy the (unique) defeasible rule whose premise
pattern is a positive effect report and whose conclusion matches the task-1
predicate — selection is by premise/conclusion shape read from the policy,
never by an id written in the source. Instantiate with the substitution
`(M, Q, D, Exp)` = (subject.method, subject.quality, subject.distribution,
experiment constant), in rule parameter order. Premise reconstruction follows
the M4a surface convention (`by <rule>(M, Q, D, Exp)` with implicit premise
leaves, as in examples/E1–E3). Arg id: experiment id `exp_<Z>` → `a_<Z>`.

**Task 4 — critical-question discharge or explicit hole creation.** For each
instantiated rule, every declared question is accounted for in policy
declaration order: if the trace holds a cell whose topic answers the
question's answer pattern (`randomization` → `randomized(Exp)`, `power` →
`powered(Exp)`, `generalization` → `generalizes(M, Q, D)`), emit
`discharge <question> with <leaf>`; otherwise the question is an **explicit
hole**, lowered per §1 (hole lowering): the incomplete argument is **not
emitted**, the claim's complete-support set stays empty (→ `gap`), and the
hole is logged in provenance with question ids, the responsible source node,
and rationale. (A surface `open` line is a checker rejection on the frozen
frontend — verified §1 — so it is never emitted.)

**Task 5 — strict-backend / theory / certificate selection.** N/A (T1): no
strict instance is certified; `Lara.Syntax` forces `AssuranceNone`. Logged as
`not-applicable` in provenance.

**Task 6 — typed-attack extraction over the whole trace.** Walk every
`experiment` and `dead_end` node in the trace (not only dead ends). Each
evidence cell is classified by matching its derived proposition against the
trusted policy, and lowered per its evidential role:

- derived proposition matches a policy **`exception`** of a rule instantiated
  in the node’s claim context (same `(M, Q, D)`) → **undercut**. Emit the
  attacker `arg d_<Y> : challenges(<q>(<a_target>)) by leaf(e_<Y>)` followed by
  `undercut d_<Y> <a_target>.rule`, where `e_<Y>` is the cell's leaf and
  `<a_target>` the attacked argument. (`challenges(…)` is presentation-intent
  only — docs/lara-surface-grammar.md §6; for this policy the
  `distribution_shift` exception attaches to the `external_validity` question,
  exactly the E3 shape.)
- derived proposition is a declared **`contrary`** of a discharge leaf's
  proposition in its claim context → **undermine**. Emit
  `arg d_<Y> : challenges(<e_target>) by leaf(e_<Y>)` followed by
  `undermine d_<Y> <a_target>.<question>.leaf` (the E3 shape).
- cell answers a premise or question in its context → **support** (ordinary
  task-2 leaf; a dead end that lowers to support, e.g. `dd_ow_power`).
- otherwise → **no lowering**; logged with role `none`. A dead end that only
  documents unmet questions (e.g. `dd_me_pool`) routes to the task-4 hole,
  never to an attack (spec §7: unmet mandatory CQs route to holes).

Attack licensing is always a policy declaration (`exception` / `contrary`)
matched by the elaborator — attacks are never declared in the source.

### 4.3 Emitted `.lara` layout (pinned order)

1. The fixed header (§4.1).
2. Per claim context, in source tree order: the `claim` declaration, then its
   leaves — ALL cells of the claim subtree, including attack-source cells, in
   tree-walk order (an experiment's cells before its sibling dead ends'
   cells; the E3 precedent) — then its support `arg` (if task 4 assembled
   one) with discharge lines in policy question order.
3. Attacker args and attack declarations, in source tree order of the nodes
   that produced them. No leaves here: attack-source leaves are already
   emitted in their claim context per item 2.
4. `status <claim id>` lines, one per claim, in source tree order.

Comments are allowed (source-node back-references recommended for audit) but
MUST NOT carry timestamps, absolute paths, or environment-specific content.
Exactly one trailing LF. The committed `emitted.lara` is the byte-golden for
review T5.

## 5. Derived artifacts (binding on B2)

- **`emitted.core.sexp`** — derived by the exact M4a path
  (`scripts/gen-worked-examples.hs`, given a minimal bundle-input mode in B2;
  B3 wires that mode into the differential glob and CI):
  parse `emitted.lara` + the co-located policy copy with `Lara.Syntax`, lower
  with `Lara.Elaborate.elaborate`, serialize with
  `Lara.Wire.printSExpr . Lara.Wire.encodeUnit`, plus a single trailing LF.
  This is the Haskell↔Lean differential anchor; B3 extends
  `scripts/differential.sh`'s fixture glob to `bundles/` (review 2A).
- **`verdict.txt`** — the frozen verdict: exact stdout bytes of
  `lara check emitted.lara` run **with the bundle directory as cwd** (so the
  co-located policy copy is the resolved policy — replay needs only the bundle
  and the binary, 1A). The bytes equal the `.core.sexp` path's by the Main.hs
  driver contract. The expected exit code (0 = accept) is recorded in the
  manifest. Replay (B2): verify manifest hashes (mismatch = hard error, D4) →
  compare checker-source revision (drift = loud warning, T4) → re-run
  `lara check emitted.lara` in the bundle → byte-diff stdout against
  `verdict.txt` and compare exit codes.

## 6. `manifest.json` schema

Canonicalized JSON (§8). Every field required unless noted:

```json
{
  "format": "lara-replay-bundle@1",
  "skeleton": "walking-skeleton",
  "lara-core": "0.1",
  "artifacts": {
    "core-sexp": "emitted.core.sexp",
    "emitted-lara": "emitted.lara",
    "policy-copy": "empirical-v1.policy.lara",
    "provenance": "provenance.json",
    "source": "source.yaml",
    "verdict": "verdict.txt"
  },
  "trusted-inputs": {
    "policy": {
      "id": "empirical-v1",
      "sha256": "<64 lowercase hex of the bundle's policy copy>",
      "copied-from": "examples/E1/empirical-v1.policy.lara"
    },
    "backends": ["nd@1"],
    "theories": []
  },
  "checker-source-revision": "<40 lowercase hex>",
  "producer-toolchain": {
    "elaborator": "elaborator/elaborate.py",
    "python": "<X.Y.Z>",
    "pyyaml": "<X.Y.Z>",
    "uv": "<X.Y.Z>"
  },
  "frozen-verdict": { "exit-code": 0 }
}
```

Field semantics:

- **`trusted-inputs.policy.sha256`** — hash of the bundle's *own copy*. Replay
  recomputes it; mismatch is a **hard error** (D4). `copied-from` is
  repo-relative audit metadata enabling B3's authenticity check (T7: the copy
  must be byte-identical to the canonical policy; a self-consistent but
  substituted bundle fails).
- **`trusted-inputs.theories`** — one entry per policy-allowlisted theory
  digest the checker consumes: `{"backend": "<beta@version>", "theory":
  "<id>", "sha256": "<hex>"}`. The theory registry is currently empty, so the
  array is empty — the manifest hashes what the checker consumes, not the
  spec's idealized tuple.
- **`checker-source-revision`** — output of
  `git log -1 --format=%H -- src/ app/ lean/ lara.cabal cabal.project`
  at freeze time (the `lean/` path carries the toolchain + lake manifest).
  Audit metadata, not a binary-reproducibility identity (GHC/dependency-store
  pinning is out of scope). Drift at replay is a **loud warning**; replay
  proceeds and the verdict byte-diff decides (T4). (At B0 this is
  `f1a255c380b650a8bde819ba94b65f5dd3ebdf7f`; B2 recomputes at freeze.)
- **`producer-toolchain`** — the pinned versions from the elaborator's PEP 723
  header and the environment that produced the bundle (T8): `python`
  (`requires-python`), `pyyaml` (pinned dependency), `uv` (installer).
- **`lara-core`** — the frozen core version id (`0.1`, spec §2.1).
- **`frozen-verdict.exit-code`** — expected process exit code of the replayed
  check (0 = accept, 1 = reject, 2 = decode-boundary error).

The manifest carries no wall-clock timestamps and no absolute paths. The spec
§2.1 verdict-carried replay tuple is issue #36; the bundle manifest is the M4b
audit identity.

## 7. `provenance.json` schema

Canonicalized JSON (§8). One entry per §11 task, keys `task-1-…` … `task-6-…`
(lexicographic sort order is the natural task order). Every derivation the
elaborator performed is logged with its source-node linkage — this is what
makes "no hand-authored certificate" auditable.

```json
{
  "format": "lara-elaborator-provenance@1",
  "policy": "empirical-v1",
  "source": "source.yaml",
  "task-1-formalization": [
    { "source-node": "claim_ow", "claim": "c_ow", "nl": "<verbatim>",
      "formal": "improves(kv_quant, latency, openweb)",
      "binding": { "author": "alice", "audit-status": "reviewed" } }
  ],
  "task-2-leaf-extraction": [
    { "source-cell": "cell_ow_mean", "leaf": "e_ow_mean",
      "proposition": "reports(exp_ow, effect(kv_quant, latency, openweb, positive))",
      "kind": "observed", "provenance": "ai-executed",
      "refs": ["evidence/ow_table1.csv#row=mean", "paper.md#abstract"],
      "grain": "result-cell",
      "duplicate-report": { "locations": ["evidence/ow_table1.csv#row=mean", "paper.md#abstract"] } }
  ],
  "task-3-scheme-selection": [
    { "source-node": "exp_ow", "arg": "a_ow", "rule": "controlled_experiment",
      "substitution": [["M", "kv_quant"], ["Q", "latency"], ["D", "openweb"], ["Exp", "exp_ow"]],
      "premise-leaves": ["e_ow_mean"] }
  ],
  "task-4-question-accounting": [
    { "arg": "a_ow", "question": "randomization", "decision": "discharge",
      "with": "e_ow_rand", "source-cell": "cell_ow_rand" },
    { "claim": "c_me", "question": "adequate_power", "decision": "hole",
      "source-node": "dd_me_pool",
      "lowered": "gap",
      "reason": "no evidence cell answers the question; the frozen frontend rejects surface holes (PEIncompleteArgument), so the incomplete argument is not emitted and the claim's complete support is empty" }
  ],
  "task-5-strict-selection": {
    "status": "not-applicable",
    "reason": "defeasible source; Lara.Syntax forces assurance = none (T1); no strict instance is certified"
  },
  "task-6-attack-extraction": [
    { "source-node": "dd_cp_shift", "role": "attack",
      "attack": { "kind": "undercut", "attacker": "d_cp_shift", "target": "a_cp.rule" },
      "policy-basis": "exception controlled_experiment : distribution_shift(M, Q, D)" },
    { "source-node": "dd_ow_power", "role": "support", "leaf": "e_ow_power" },
    { "source-node": "dd_me_pool", "role": "none",
      "note": "documents unmet questions; routed to task-4 hole, never an attack (spec §7)" }
  ]
}
```

Schema rules: `duplicate-report` is `null` unless the cell has more than one
ref location. `substitution` pairs are in **rule parameter order** (arrays,
not objects). `decision` is `discharge` (with `with` + `source-cell`) or
`hole` (with `source-node`, `lowered`, `reason`). `role` is `attack`
(with `attack` + `policy-basis`), `support` (with `leaf`), or `none`
(with `note`). The log contains no timestamps, no absolute paths, and no
content not derivable from `source.yaml` + the trusted policy.

## 8. Canonicalization rules (byte-identity)

Every bundle file is a pure function of `source.yaml` and the trusted inputs:

- **C1 — text encoding.** UTF-8, LF line endings, exactly one trailing LF per
  file.
- **C2 — JSON.** `json.dumps(obj, sort_keys=True, indent=2, ensure_ascii=True)`
  plus one trailing `\n`. All object keys sorted recursively; arrays keep
  their pinned semantic order (source document order, rule parameter order, or
  claim tree order — never an unordered dump).
- **C3 — no environment leakage.** No wall-clock timestamps, no absolute
  paths, no user/host names in any bundle file. The only paths are
  bundle-relative filenames and the repo-relative `copied-from` audit field.
- **C4 — pinned emission order.** `emitted.lara` follows §4.3; provenance and
  manifest serialize per C2 (all object keys sorted recursively — the §6/§7
  examples are shown in semantic order for readability, NOT emission order);
  verdict and `.core.sexp` bytes are fixed by the frozen codecs.
- **C5 — replay compares bytes.** Any byte difference in a re-emitted
  `emitted.lara` / `provenance.json` (T5 golden) or a replayed verdict (B2
  gate) is a failure, never silently re-blessed.

## 9. Expected outcome (oracle for B1–B3)

For the committed `walking-skeleton` source, the emitted `.lara` checks
**accept** (exit 0) with claim statuses: `c_ow` → **justified** (complete
argument, no attackers), `c_cp` → **defeated** (complete argument, undercut by
the distribution shift and undermined at its external-validity leaf — both
attackers derived from trace nodes), `c_me` → **gap** (empty complete support;
the unmet power and external-validity questions are the task-4 holes logged in
provenance). No rebut pair arises: all claim/attack atoms live in disjoint
`(method, quality, distribution)` contexts, and no `not_improves` argument is
ever assembled.
