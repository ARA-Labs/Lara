# RIT-Informed Evidence Admission and Research-History Plan

> **For agentic workers:** REQUIRED SUB-SKILL: use `subagent-driven-development` or `executing-plans` to execute this plan task by task. Work in an isolated worktree. Do not combine the calculus and protocol tracks into one implementation commit.

**Goal:** Borrow RIT's strongest reusable ideas without turning LARA into a second arithmetic verifier: add a small evidence-admission subcalculus that can justify how byte-addressed evidence becomes a LARA leaf, preserve LARA's argumentation semantics as the scientific contribution, and keep goal/attempt history outside the frozen support calculus.

**Recommendation:** Treat only the evidence-admission judgment and its composition theorems as calculus work. Treat artifact hashing, concrete extractors, receipts, and append-only goal history as implementation/protocol work. First repair the one demonstrated source conformance defect: `Lara.Elaborate` currently ignores `policyAdmission`. Do not relabel the frozen `IncompleteArgument` gate as a bug; accepted partial alternatives would be a separate `lara-core@0.2` design.

**Architecture:** Use a two-boundary design. Boundary 1 checks a closed, versioned leaf checker against a hash-pinned artifact snapshot and returns `admit`, `quarantine`, or `reject` plus a dependency report. Boundary 2 is the existing LARA support/attack/status checker over the admitted leaf context. The core does not infer that evidence is scientifically adequate merely because a byte extractor succeeded; a support scheme and its critical questions still decide whether an admitted leaf may support a claim. Goal and attempt history remains an external event protocol whose trusted-checkpoint rule is enforced before a run starts.

**Versioning:** Preserve the frozen `lara-core@0.1` checker, wire grammar, fixtures, and proof statements. Add evidence admission as an independently versioned source layer, `lara-evidence@0.1`, so concrete checker evolution does not silently change the argumentation calculus. Any future change that admits open-obligation alternatives requires a separate `lara-core@0.2` decision, implementation plan, and full refreeze.

**Tech stack:** Haskell/GHC 2021, Lean 4.32.0, canonical S-expressions, canonical JSON reports, SHA-256 manifests, QuickCheck, byte-exact Haskell/Lean differential tests.

---

## 1. What contributes to the calculus

| RIT lesson | LARA placement | Calculus contribution? | Reason |
|---|---|---:|---|
| Re-extract a claim input from immutable bytes | Evidence-admission judgment before `Gamma` construction | **Yes** | It defines the previously implicit world-to-leaf boundary and composes with the existing support judgment. |
| Distinguish accepted, unavailable, and malformed evidence | `admit` / `quarantine` / `reject` outcome algebra | **Yes** | The outcome changes whether a leaf may enter the checking context without turning every missing measurement into whole-program failure. |
| Record exact checker, selector, source digest, and dependencies | Evidence dependency judgment/report | **Yes, abstractly** | The calculus can state which checked premises an admitted leaf depends on. Concrete hashing and parsing stay outside the proof kernel. |
| SHA-256 manifests and concrete table/log extractors | Artifact resolver and closed checker registry | No | These are trusted implementations of the abstract judgment, not argumentation rules. |
| Goal before attempt; immutable attempt history; failure receipts | External event protocol | No | This establishes temporal integrity and auditability, not support, attack, or grounded status. |
| Scalar grounding tiers as automatic winners | Nowhere in the defeat calculus | **No** | A trust tier is not a scientific defeat relation. Provenance remains admission metadata unless a named policy gives it semantics. |
| Lean arithmetic as the organizing principle | Optional strict or leaf-checker backend | **No** | It helps with narrow decidable subclaims but does not replace schemes, critical questions, typed defeat, or policy-relative status. |

The paper-level claim should be narrow:

> LARA composes a deterministic evidence-admission judgment with a structured-argumentation judgment. The first establishes that a leaf is the exact output of a named checker over pinned bytes and a pinned mapping payload; the second establishes what that leaf is permitted to support and how defeaters affect the result.

This is not justification semantics and not a truth theorem. Possible-world/justification semantics remain related semantic extensions; they must not be conflated with byte extraction.

---

## 2. Global invariants

1. `lara-core@0.1` retains its existing proposition, rule, support-term, typed-attack, grounded-labelling, four-status, and `IncompleteArgument` rejection behavior.
2. A concrete leaf checker is selected from a closed registry. Artifact input never supplies executable checker code.
3. Every admitted certified leaf has one exact checker identity, one canonical payload, at least one source reference, and a dependency report.
4. `quarantine` removes the leaf and every dependent argument/attack before core checking. It is not a successful leaf judgment and not a whole-program rejection.
5. `reject` is reserved for malformed or integrity-violating input: digest mismatch, path escape, unknown checker, malformed payload, ambiguous row selection, or policy-mandated escalation.
6. Under frozen v0.1, a submitted argument with an open mandatory obligation is rejected as `IncompleteArgument`; a source claim is a `gap` only when it has no complete submitted support argument. Accepting partial alternatives is explicitly outside this plan.
7. A raw core `.sexp` verdict is relative to the supplied `Gamma`. It must not be reported as byte-evidence-checked. The full `.lara` artifact path reports both evidence and core identities.
8. Hashes, checker versions, canonical payloads, and the evidence report digest are replay identity. A changed dependency is a different run, not a replay of the old run.
9. Goal/attempt history stays outside `lara-core`; it cannot create support, attacks, or statuses.
10. No accepted run may be partially persisted. Evidence report, core verdict, and event receipt publish transactionally.

---

## Task 1: Freeze the boundary and paper claim

**Files**
- Create: `docs/evidence-admission-decision.md`
- Modify: `docs/spec.md`
- Modify: `docs/lara-surface-grammar.md`
- Modify: `plans/research-proposal.md`
- Modify: `docs/comparison-rit-lara.md`

**Step 1: Write the formal boundary**

Add these judgments to the decision record and spec:

```text
A ; Pi |- leaf l ⇓ admit(J, D)
A ; Pi |- leaf l ⇓ quarantine(d)
A ; Pi |- leaf l ⇓ reject(e)

admitPi(A, L) = (Gamma_checked, Q, E)
Gamma_checked = { l : p | l in L and l ⇓ admit(J, D) }
```

Where:
- `A` is an immutable artifact snapshot resolved from a canonical manifest.
- `Pi` is the policy, including the closed checker registry and escalation rules.
- `J` is a sealed successful leaf judgment.
- `D` is the exact dependency report.
- `Q` is the quarantined-leaf set with located diagnostics.
- `E` is empty on success and contains one deterministic rejection on failure.

Define program acceptance as composition, not as a new defeat rule:

```text
verify(A, Pi, P) =
  reject e                         if admitPi(A, leaves(P)) rejects with e
  coreCheck(P[Gamma := Gamma_checked]) otherwise
```

The source report retains `Q`. It may also explain open obligations on a rejected input, but under `lara-core@0.1` a submitted incomplete argument produces `IncompleteArgument`; it is never silently treated as an accepted AF alternative.

**Step 2: Freeze the outcome join**

For multiple references/checks on one leaf, use the most restrictive outcome:

```text
admit < quarantine < reject
```

Run every independently safe check needed for a deterministic report. Reject manifest/path integrity failures before opening artifact objects. The leaf outcome is the maximum of the completed checks. At program level, any `reject` rejects the source artifact; otherwise all quarantined leaves are removed transitively.

**Step 3: State the claim boundary explicitly**

Add three negative guarantees to the spec and paper plan:

- Evidence admission does not prove the leaf proposition true in the world.
- Evidence admission does not prove that the proposition supports a downstream claim.
- Grounded argument status does not upgrade extractor soundness or policy adequacy.

**Step 4: Freeze source syntax**

Extend policy syntax with a selected leaf-checker set and presentation leaves with one optional verification record:

```text
use leaf-checkers [tsv-row@1]
```

```text
verification = cert(tsv-row, 1,
  (tsv-row (ref 0) (key run_id exp_3)
           (columns system metric split value)
           (predicate observed)))
```

Rules:
- The executable registry is closed in code; `use leaf-checkers` selects an allowed subset and cannot name executable paths.
- A verification record rejects unless its exact checker identity is selected by policy.
- `kind = certified` requires `verification` and `provenance = checker(tsv-row, 1)`.
- Other leaf kinds reject a `verification` field.
- Checker identity in provenance and verification must match exactly.
- The payload is opaque to the surface parser and interpreted only by the selected closed checker.

**Step 5: Review before code**

Acceptance criteria:
- The decision record distinguishes extraction soundness from scientific justification.
- The three outcomes have one deterministic join and one program-level composition rule.
- The raw-core and full-artifact guarantees are visibly different.
- The document explicitly says that RIT-style history is not part of the calculus.

**Commit**

```bash
git add docs/evidence-admission-decision.md docs/spec.md docs/lara-surface-grammar.md plans/research-proposal.md docs/comparison-rit-lara.md
git commit -m "docs: freeze evidence admission boundary"
```

---

## Task 2: Repair source admission conformance without changing `lara-core@0.1`

**Files**
- Create: `src/Lara/Admission.hs`
- Modify: `lara.cabal`
- Modify: `src/Lara/Elaborate.hs`
- Modify: `src/Lara/Driver.hs`
- Modify: `src/Lara/Reporting.hs`
- Modify: `test/ElaborateSpec.hs`
- Modify: `test/ReportingSpec.hs`
- Modify: `test/CliSpec.hs`
- Modify: `docs/spec.md`
- Modify: `docs/comparison-rit-lara.md`

**Step 1: Add failing source-admission tests**

Add source-level tests proving:

1. `(Observed, AiExecuted) -> quarantine` excludes that leaf.
2. Every argument containing the leaf is excluded, including nested subarguments.
3. Every attack whose source or target argument is excluded is excluded.
4. An unrelated complete argument remains in the emitted core `Unit`.
5. `reject` stops source checking before `checkUnit`.
6. An all-`admit` program emits exactly the current `lara-core@0.1` input and verdict bytes.
7. A raw `.sexp` with a missing leaf still rejects under the unchanged core contract.

The first five tests must fail against the current all-declared `gamma` construction in `Lara.Elaborate.elaborate`.

**Step 2: Implement one source admission pass**

Replace the unconditional presentation environment with a total pass over every declared leaf. Run it before duplicate-report group handling and support checking. Compute argument dependencies with the existing structural `leaves(w)` function; retain an argument iff every dependency is admitted. Retain an attack iff both endpoints are retained. Never remove only the `Gamma` entry: that produces a later `R1 MissingLeaf` rejection and is not quarantine.

Use one result type shared by elaboration and reporting:

```haskell
data AdmissionDiagnostic = AdmissionDiagnostic
  { admissionLeaf       :: LeafId
  , admissionKind       :: LeafKind
  , admissionProvenance :: Provenance
  , admissionOutcome    :: Admission
  }

data AdmissionResult = AdmissionResult
  { admittedLeaves      :: Map LeafId Prop
  , quarantinedLeaves   :: Map LeafId AdmissionDiagnostic
  , retainedArguments   :: Set ArgId
  , retainedAttacks     :: [Attack]
  }
```

`Lara.Admission` is pure. It receives the policy table and parsed presentation program; it performs no filesystem access and does not know about concrete evidence checkers yet.

**Step 3: Preserve and document the v0.1 hole contract**

Do not change `checkArguments`, `PEIncompleteArgument`, the core wire rejection, Lean, or frozen fixtures in this task. Keep these distinctions explicit:

- a submitted open-obligation argument is an honest whole-unit rejection under `lara-core@0.1`;
- `Lara.Reporting` may explain its located holes on the reject path;
- an accepted `gap` is represented by no complete support argument, matching `corpus-units/LOWERING.md` and trace decision N93;
- admitting a complete sibling while retaining an incomplete diagnostic would be useful, but it is a future v0.2 semantics change, not a conformance repair.

Update the comparison and spec wording where they currently imply that accepted partial alternatives are already required by v0.1.

**Step 4: Preserve source diagnostics**

The combined source report records each quarantined leaf and every pruned argument/attack. A query that loses all complete support through quarantine reports `gap`; the report must explain the quarantine chain. `reject` reports the first deterministic admission error and never invokes the core checker.

**Verification**

```bash
cabal test
(cd lean && lake build)
./scripts/check-axioms.sh
./scripts/differential.sh
./scripts/replay.sh
./scripts/test-replay-tamper.sh
```

Acceptance criteria:
- No `.lara` source path silently treats every declared leaf as admitted.
- Quarantine cannot surface later as `MissingLeaf`.
- All-admit source artifacts preserve current `lara-core@0.1` core bytes.
- Raw `.sexp`, open-obligation, Haskell/Lean differential, replay, and AxCheck behavior are unchanged.
- The documentation no longer calls the frozen open-obligation rejection an implementation mismatch.

**Commit**

```bash
git add src/Lara/Admission.hs src/Lara/Elaborate.hs src/Lara/Driver.hs src/Lara/Reporting.hs test/ElaborateSpec.hs test/ReportingSpec.hs test/CliSpec.hs lara.cabal docs/spec.md docs/comparison-rit-lara.md
git commit -m "fix: enforce source leaf admission policy"
```

---

## Task 3: Mechanize the abstract evidence-admission calculus

**Files**
- Create: `src/Lara/Evidence.hs`
- Create: `lean/Lara/Evidence.lean`
- Create: `test/EvidenceSpec.hs`
- Modify: `lara.cabal`
- Modify: `lean/lakefile.toml` only if the module list is explicit
- Modify: `lean/AxCheck.lean`
- Modify: `docs/spec.md`

**Step 1: Implement the pure Haskell model**

Use types with no filesystem or process access:

```haskell
newtype EvidenceVersion = EvidenceVersion String
newtype LeafCheckerId = LeafCheckerId String

newtype LeafJudgment = LeafJudgment PrivateJudgment

data EvidenceDependency = EvidenceDependency
  { dependencyObject  :: Digest
  , dependencyRef     :: SourceRef
  , dependencyChecker :: LeafCheckerId
  , dependencyVersion :: Int
  , dependencyPayload :: SExpr
  }

data EvidenceDiagnostic = EvidenceDiagnostic
  { diagnosticLeaf    :: LeafId
  , diagnosticChecker :: LeafCheckerId
  , diagnosticError   :: EvidenceError
  }

data EvidenceOutcome
  = EvidenceAdmit LeafJudgment [EvidenceDependency]
  | EvidenceQuarantine EvidenceDiagnostic
  | EvidenceReject EvidenceError
```

Keep the `LeafJudgment` constructor private. Only a registered checker can create it.

**Step 2: Define the abstract Lean relation**

Model artifact objects, checker identities, payloads, and successful judgments abstractly. Do not formalize SHA-256 in the calculus. Define `Outcome.join`, `admitLeaves`, and composition with `Compile.checkedAF`.

**Step 3: Prove the calculus properties**

Add theorem declarations and proofs for:

1. `evidence_outcome_deterministic`: fixed snapshot, policy, checker registry, and leaf have one outcome.
2. `admitted_certified_has_judgment`: every certified leaf in the resulting `Gamma` has a successful judgment from the declared checker/version.
3. `quarantined_not_in_gamma`: quarantined leaves are absent from `Gamma`.
4. `quarantined_dependency_exclusion`: no compiled argument depends on a quarantined leaf.
5. `accepted_core_inputs_complete`: every argument in an accepted `lara-core@0.1` unit has an empty mandatory-obligation set.
6. `admission_replacement`: equal admitted contexts and equal retained programs produce equal grounded statuses, independent of how concrete evidence was stored.
7. `more_restrictive_outcome_monotone`: replacing an outcome by a more restrictive one cannot add a leaf or AF node.

Do **not** claim that admission monotonicity implies consequence-level monotonicity; LARA remains non-monotonic after AF construction.

**Step 4: Add Haskell property tests**

Generate small leaf/outcome/dependency structures and check the executable counterparts of the seven properties. Include duplicate checker IDs, mismatched versions, empty references, and mixed admit/quarantine/reject lists.

**Verification**

```bash
cabal test
(cd lean && lake build)
./scripts/check-axioms.sh
```

Acceptance criteria:
- The Haskell model has no IO entry point and no exported judgment constructor.
- Lean proofs use only the project's allowed axiom set.
- Every theorem is about extraction/admission composition, not empirical truth.

**Commit**

```bash
git add src/Lara/Evidence.hs lean/Lara/Evidence.lean lean/AxCheck.lean lean/lakefile.toml test/EvidenceSpec.hs lara.cabal docs/spec.md
git commit -m "feat: add evidence admission calculus"
```

---

## Task 4: Implement one closed concrete checker, `tsv-row@1`

**Files**
- Create: `src/Lara/Evidence/Registry.hs`
- Create: `src/Lara/Evidence/TSVRow.hs`
- Create: `src/Lara/ArtifactManifest.hs`
- Create: `test/ArtifactManifestSpec.hs`
- Create: `test/TSVRowSpec.hs`
- Create: `fixtures/evidence/tsv-row-valid/`
- Create: `fixtures/evidence/tsv-row-mutants/`
- Modify: `lara.cabal`
- Modify: `docs/evidence-admission-decision.md`

**Step 1: Define the manifest contract**

Use one canonical S-expression manifest outside the set it hashes:

```text
(artifact-manifest 1
  (object evidence/results.tsv SHA256 BYTE_LENGTH)
  ...)
```
Add `bytestring`, `text`, and `cryptohash-sha256` to the library dependencies. Use `Crypto.Hash.SHA256.hash`; do not call `shasum`, `sha256sum`, OpenSSL, or another process.

Rules:
- paths are relative normalized POSIX paths encoded as UTF-8;
- absolute paths, empty segments, `.`/`..`, duplicate paths, symlinks, and NUL are rejected;
- objects are sorted by unsigned UTF-8 path bytes in canonical form;
- object digests are `sha256:` plus exactly 64 lowercase hexadecimal characters; byte lengths are canonical nonnegative decimals;
- each captured file's byte length and SHA-256 must match its manifest row;
- the artifact identity is SHA-256 of the canonical manifest bytes, and the resolver rejects unless it equals `programDigest`;
- only manifest-listed objects may satisfy `SourceRef`s.


**Step 2: Define `tsv-row@1` exactly**

Accepted bytes:
- UTF-8 without BOM;
- LF line endings only;
- one nonempty header row;
- tab delimiter;
- no quoting, embedded tabs, or embedded newlines;
- unique header names;
- every data row has exactly the header width.

Payload:

```text
(tsv-row
  (ref NAT)
  (key COLUMN TERM)
  (columns COLUMN*)
  (predicate PRED))
```

Semantics:
1. Resolve `leafRefs[NAT]` to one manifest object; fragments are forbidden because the payload owns selection.
2. Parse `TERM` and every selected cell as canonical LARA ground terms.
3. Select exactly one row whose `COLUMN` term is identical to `TERM` after `nfTerm`.
4. Construct `Prop PRED selectedTerms` in the listed column order.
5. Admit only if the constructed proposition is equivalent to `leafProp` under `(===)`.
6. Return dependencies containing object digest, source ref, checker/version, and canonical payload.
7. Zero rows, multiple rows, malformed terms, missing columns, or proposition mismatch reject with distinct located errors.

The checker proves exact structural transcription under the declared payload. It does not prove that column names have the intended scientific meaning, that the chosen predicate is a faithful model, or that the table was produced by a valid experiment.

**Step 3: Build the closed registry**

Register exactly `(tsv-row, 1)`. Duplicate registrations fail registry construction. Unknown name/version rejects before payload parsing. No dynamic loading, executable path, shell command, or source-provided module name is allowed.

**Step 4: Add mutation tests**

Starting from one valid fixture, mutate independently:
- object byte;
- manifest digest;
- byte length;
- path traversal;
- symlink;
- checker version;
- payload key;
- payload column order;
- duplicate matching row;
- leaf proposition;
- UTF-8 and line ending validity.

Every mutant must reject before core checking. The valid fixture must return the exact same dependency report on repeated runs.

**Verification**

```bash
cabal test
```

Acceptance criteria:
- The valid fixture admits exactly one leaf and records every consumed input.
- Every named mutant rejects in the evidence layer.
- The checker executes no external command and reads no unmanifested file.

**Commit**

```bash
git add src/Lara/Evidence/Registry.hs src/Lara/Evidence/TSVRow.hs src/Lara/ArtifactManifest.hs test/ArtifactManifestSpec.hs test/TSVRowSpec.hs fixtures/evidence/tsv-row-valid fixtures/evidence/tsv-row-mutants lara.cabal docs/evidence-admission-decision.md
git commit -m "feat: add manifest-backed TSV leaf checker"
```

---

## Task 5: Integrate evidence checking without overstating raw-core guarantees

**Files**
- Modify: `lara.cabal`
- Modify: `src/Lara/AST.hs`
- Modify: `src/Lara/Syntax.hs`
- Modify: `src/Lara/Elaborate.hs`
- Modify: `src/Lara/Replay.hs`
- Modify: `src/Lara/ExpectedJson.hs`
- Modify: `src/Lara/Driver.hs`
- Modify: `app/Main.hs`
- Modify: `test/SyntaxSpec.hs`
- Modify: `test/ElaborateSpec.hs`
- Modify: `test/CliSpec.hs`
- Modify: `test/ReplaySpec.hs`
- Create: `test/EvidenceIntegrationSpec.hs`
- Modify: `examples/running-example/` with one manifest-backed measured leaf
- Modify: `scripts/replay.sh`
- Modify: `scripts/test-replay-tamper.sh`

**Step 1: Add presentation-only verification data**

Add `LeafVerification` to the presentation AST; do not add checker payloads to the core `Unit` leaf map. Validate certified/provenance/verification consistency during elaboration.

**Step 2: Run evidence admission before core input construction**

The `.lara` path performs:

```text
parse source
→ validate program/policy/replay identity
→ resolve manifest
→ run closed leaf checkers
→ apply admit/quarantine/reject
→ lower retained program to Unit
→ run lara-core@0.1
→ emit one combined report transactionally
```

A source artifact rejected by evidence admission must not invoke `runCheck`.

**Step 3: Separate guarantee labels**

Reports must carry:

```text
(core lara-core@0.1)
(evidence declared | (checked lara-evidence@0.1 REPORT_SHA256))
```

Rules:
- `.lara` plus a validated manifest may produce `evidence checked`.
- raw `.sexp` always produces `evidence declared` because the core checker receives `Gamma`, not artifact bytes.
- the decoder rejects any raw `.sexp` that claims `evidence checked`.
- CLI prose and JSON must not call `evidence declared` a full artifact verification.

Keep Haskell/Lean differential comparison on the core verdict. Compare the evidence report separately against canonical golden bytes; do not pretend Lean independently rehashed the artifact.

**Step 4: Extend replay identity**

The full-artifact report identity includes:
- core version;
- evidence version;
- policy ID;
- strict backend identities;
- selected leaf-checker identities;
- theory digests;
- artifact-manifest digest;
- evidence-report digest.

Replay re-runs evidence admission and requires exact combined-report bytes. A changed object, manifest, checker version, payload, policy, or retained program must fail replay before accepting the old verdict.

**Step 5: Make publication transactional**

Capture each manifest object into an immutable in-memory snapshot and run all leaf checkers against those captured bytes; never reopen a path during the run. Build the evidence report, core verdict, and combined JSON inside one temporary sibling directory. After every file is closed and validated, atomically rename that directory to a new content-addressed final directory named by the combined-report digest. Never overwrite an existing run directory. On rejection, emit one canonical rejection report and remove the temporary directory, leaving no accepted partial output.

**Verification**

```bash
cabal test
(cd lean && lake build)
./scripts/check-axioms.sh
./scripts/differential.sh
./scripts/replay.sh
./scripts/test-replay-tamper.sh
```

Smoke scenarios:
1. Verify the manifest-backed running example and observe `evidence checked` plus the expected claim status.
2. Change one table byte and observe evidence rejection before core invocation.
3. Feed the emitted raw core `.sexp` directly and observe `evidence declared`, never `checked`.
4. Restore the byte and replay the original combined report exactly.

**Commit**

```bash
git add src/Lara/AST.hs src/Lara/Syntax.hs src/Lara/Elaborate.hs src/Lara/Replay.hs src/Lara/ExpectedJson.hs src/Lara/Driver.hs app/Main.hs test/SyntaxSpec.hs test/ElaborateSpec.hs test/CliSpec.hs test/ReplaySpec.hs test/EvidenceIntegrationSpec.hs examples/running-example scripts/replay.sh scripts/test-replay-tamper.sh lara.cabal
git commit -m "feat: compose evidence and core verification"
```

---

## Task 6: Specify and validate RIT-style goal and attempt history as an external protocol

**Files**
- Create: `docs/goal-attempt-protocol.md`
- Create: `schemas/goal-attempt-v1.schema.json`
- Create: `src/Lara/Protocol/GoalAttempt.hs`
- Create: `test/GoalAttemptProtocolSpec.hs`
- Create: fixtures under `fixtures/goal-attempt/`
- Modify: `lara.cabal`
- Modify: `docs/comparison-rit-lara.md`
- Modify: `plans/research-proposal.md`

**Step 1: Define the event envelope**

Use canonical JSON records with `version = "goal-attempt@1"` and one of these exact event payloads:

```text
goal-registered:  event_id, goal_id, goal_digest, parent_checkpoint, timestamp
attempt-started:  event_id, attempt_id, goal_id, base_checkpoint, timestamp
attempt-finished: event_id, attempt_id, result_digest, verdict_digest, timestamp
attempt-rejected: event_id, attempt_id, reason_digest, timestamp
goal-revised:     event_id, old_goal_id, new_goal_id, reason_digest, timestamp
```

The schema requires exactly the fields for the selected event type and rejects unknown fields. `event_id` is the SHA-256 of the canonical event payload excluding `event_id`; other IDs and digests are content addressed. Timestamps order presentation but never establish integrity.


**Step 2: Enforce the trusted-checkpoint rule**

An attempt is pre-registered only if its goal event exists in a trusted checkpoint that predates `attempt-started`. Appending an uncommitted goal and attempt together is explicitly marked `post-hoc`; it is not allowed to satisfy pre-registration.

Git may store checkpoints, but Git history is one protocol backend, not part of LARA's calculus or trusted core.

**Step 3: Preserve failures without affecting statuses**

Rejected attempts and receipts are append-only audit data. They become LARA evidence or defeaters only when a later artifact explicitly cites them through a leaf and a policy scheme.

**Step 4: Implement a backend-independent validator**

`Lara.Protocol.GoalAttempt` parses canonical event records and exposes:

```haskell
validateEventLog
  :: TrustedCheckpoint
  -> [Event]
  -> Either ProtocolError ValidatedEventLog
```

`TrustedCheckpoint` supplies the set and order of immutable checkpoint IDs; the validator does not call Git. It checks schema/version, event digests, unique event/goal/attempt IDs, parentage, lifecycle order, and the trusted-checkpoint rule.

Add conformance fixtures and tests for:
- valid pre-registered attempt;
- goal and attempt in the same checkpoint;
- goal revision after attempt start;
- duplicated event ID;
- missing parent checkpoint;
- tampered event payload;
- failed attempt retained after later success.

Acceptance criteria:
- Same-checkpoint registration cannot claim pre-registration.
- No event automatically changes a LARA claim status.
- The validator has no import path to `Lara.Check`, `Lara.Compile`, or `Lara.Grounded`.
- The same event log can be validated over Git or another content-addressed checkpoint backend.

**Commit**

```bash
git add docs/goal-attempt-protocol.md schemas/goal-attempt-v1.schema.json src/Lara/Protocol/GoalAttempt.hs test/GoalAttemptProtocolSpec.hs fixtures/goal-attempt lara.cabal docs/comparison-rit-lara.md plans/research-proposal.md
git commit -m "feat: validate goal and attempt protocol"
```

---

## Task 7: Evaluate before promoting either extension into the paper's main claim

**Files**
- Create: `scripts/measure-evidence-admission.hs`
- Create: `ara/evidence/status/evidence_admission_status.md`
- Create: `ara/evidence/results/evidence_admission_results.json`
- Create: `docs/evidence-admission-measurement-contract.md`
- Modify: `plans/research-proposal.md`
- Do not edit external paper source in this task; record the promotion decision and exact claim delta in `ara/evidence/status/evidence_admission_status.md`

**Step 1: Freeze the measurement contract before running it**

Measure on the existing deterministic corpus:
- total leaves;
- certified leaves eligible for a closed checker;
- successfully admitted leaves;
- quarantined and rejected leaves by reason;
- claims whose status changes between declared-leaf and checked-leaf modes;
- evidence-layer runtime and report bytes;
- added trusted Haskell LOC and mechanized Lean LOC;
- tamper mutants detected before core checking.

Do not use LLM judging for these measurements.

**Step 2: Run two ablations**

1. **Declared-leaf baseline:** current support calculus with all policy-admitted leaves trusted at the world boundary.
2. **Checked-leaf treatment:** identical programs and policies after `lara-evidence@0.1` admission.

A status change is evidence about the value of the boundary, not evidence that the resulting scientific claim is true.

**Step 3: Apply the promotion gate**

Promote evidence admission into the paper's main technical contribution only if all are true:
- at least one real corpus example uses an original experiment output rather than a hand-authored assertion file;
- every declared tamper mutant is rejected before core checking;
- the dependency report is sufficient to reproduce the admitted proposition exactly;
- the Haskell/Lean core remains byte-exact after admission;
- the added TCB and guarantee split are reported honestly;
- the calculus theorem is used by the implementation/evaluation story rather than appearing as an isolated formal ornament.

Otherwise present evidence admission as a bounded extension/future-work result and keep the paper centered on structured argumentation.

Promote goal/attempt history only as a separate protocol result. It does not become a calculus contribution even if its implementation succeeds.

**Step 4: Run the final project gate**

```bash
cabal test
(cd lean && lake build)
./scripts/check-axioms.sh
./scripts/differential.sh
./scripts/replay.sh
./scripts/test-replay-tamper.sh
python3 scripts/test_freeze_bundle.py
```

Then verify that no later change touched `src/`, `app/`, `lean/`, `lara.cabal`, `cabal.project`, evidence checker sources, or manifest rules. If one did, regenerate measurements and the frozen bundle.

**Commit**

```bash
git add scripts/measure-evidence-admission.hs ara/evidence/status/evidence_admission_status.md ara/evidence/results/evidence_admission_results.json docs/evidence-admission-measurement-contract.md plans/research-proposal.md
git commit -m "eval: measure evidence admission boundary"
```

---

## 3. Recommended execution order

1. **Do Task 1 now.** It resolves the conceptual question before code changes.
2. **Do Task 2 before the paper artifact is frozen.** It repairs the current all-admit presentation lowering while preserving the frozen core and its honest open-obligation rejection.
3. **Do Tasks 3–5 as one evidence-admission milestone.** They are the only RIT-derived work that can strengthen LARA's calculus story.
4. **Run Task 7 immediately after Task 5.** Let corpus coverage and tamper results decide paper promotion.
5. **Do Task 6 after the evidence milestone or in a separate branch.** It improves research-process integrity but should not delay or dilute the argumentation paper.

## 4. Explicit non-goals

- Reproduce RIT's full Claim Flow Graph inside LARA.
- Replace LARA schemes and attacks with Lean arithmetic.
- Let trust tiers automatically defeat lower-tier evidence.
- Treat Git commit order as logical validity.
- Claim that a successful extractor proves empirical truth.
- Add dynamic checker plugins or arbitrary shell extractors.
- Make raw `.sexp` inputs claim full byte-evidence verification.
- Mix evidence admission and goal-history events into one versioned layer.
