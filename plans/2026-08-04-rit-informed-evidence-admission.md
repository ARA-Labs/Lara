# RIT-Informed Evidence Admission and Research-History Plan

> **Status (2026-08-19): gated — kept for its unexecuted tasks.** The approved
> subset is done and its durable output is
> `docs/evidence-admission-decision.md` (which supersedes this plan's Task 1
> pseudocode on composition) and `docs/registration-receipt-contract.md`.
> Tasks 3–5 and 7 remain unexecuted and gated behind the inventory gate in
> issue #78; this file is the only place their design is written down.

> **Approved scope (see roadmap tracker #78):** Task 1 (reduced to
> `docs/evidence-admission-decision.md` + one spec pointer), Task 2 (landed as
> issues #76/#77), and Task 6 (reduced to
> `docs/registration-receipt-contract.md`, documentation only). Tasks 3–5 and 7
> are gated on the corpus inventory and explicit researcher approval — **do not
> execute**.

> **For agentic workers:** REQUIRED SUB-SKILL: use `subagent-driven-development` or `executing-plans` to execute this plan task by task. Work in an isolated worktree. Do not combine the calculus and protocol tracks into one implementation commit.

> **2026-08-05 program split.** This document is the older evidence-admission sketch. Its
> presentation-policy repair is now governed by
> [`docs/policy-admission-calculus-decision.md`](../docs/policy-admission-calculus-decision.md),
> which landed in PR #81 (runtime `src/Lara/Admission*`, mechanization
> `lean/Lara/Admission.lean`, differential `scripts/admission-differential.sh`);
> the two implementation plans behind it were retired at close-out.
> That work preserves `lara-core@0.1`; it does not authorize the byte-level
> `lara-evidence@0.1` work tracked by issue #78, which remains gated and out of scope.

**Goal:** Borrow RIT's strongest reusable ideas without turning LARA into a second arithmetic verifier: add a small evidence-admission subcalculus that can justify how byte-addressed evidence becomes a LARA leaf, preserve LARA's argumentation semantics as the scientific contribution, and keep goal/attempt history outside the frozen support calculus.

**Recommendation:** Keep the evidence-admission boundary, but do not treat graph pruning as ordinary successful verification and do not present the admission layer itself as the paper's novelty. First repair the demonstrated source conformance defect: `Lara.Elaborate` currently ignores `policyAdmission`. Then prototype a closed leaf-certificate seam whose public result is conservative under unavailable evidence. Treat the composition theorem and real-artifact evaluation as a promotion gate. Defer a custom goal/attempt service; use an external registration/checkpoint interface unless evidence shows that a LARA-specific validator is needed. Do not relabel the frozen `IncompleteArgument` gate as a bug; accepted partial alternatives would be a separate `lara-core@0.2` design.

**Architecture:** Use a two-boundary design. Boundary 1 checks a closed, versioned leaf checker against a hash-pinned artifact snapshot and returns `admit`, `quarantine`, or `reject` plus a dependency report. Boundary 2 is the existing LARA support/attack/status checker over the admitted leaf context. A quarantined node is unavailable, not false: if it lies in a root's quarantine-relevance component, the source-level result is `evidence-blocked` and any core label is retained only as a conditional diagnostic. This prevents missing evidence from making a claim look stronger by deleting an attacker. The core does not infer that evidence is scientifically adequate merely because a byte extractor succeeded; a support scheme and its critical questions still decide whether an admitted leaf may support a claim. Goal and attempt history remains an external event protocol whose trusted-checkpoint rule is enforced before a run starts.

**Versioning:** Preserve the frozen `lara-core@0.1` checker, wire grammar, fixtures, and proof statements. Add evidence admission as an independently versioned source layer, `lara-evidence@0.1`, so concrete checker evolution does not silently change the argumentation calculus. Any future change that admits open-obligation alternatives requires a separate `lara-core@0.2` decision, implementation plan, and full refreeze.

**Tech stack:** Haskell/GHC 2021, Lean 4.32.0, canonical S-expressions, canonical JSON reports, SHA-256 manifests, QuickCheck, byte-exact Haskell/Lean differential tests.

---
## 0. Research review and course correction

The architecture is defensible, but only after four corrections:

1. **Evidence admission is an assurance boundary, not a new argumentation semantics.** SACM already treats assurance cases as auditable claims, arguments, and evidence; ASPIC+ already supplies strict/defeasible rules, explicit preferences, and premise/rule/conclusion attacks. LARA's plausible novelty remains the executable, typed, replayable certificate language and its checked compilation to grounded status—not the fact that evidence is attached to claims.
2. **Quarantine cannot mean “delete and report the smaller graph normally.”** Dung semantics is non-monotonic across graph changes. Removing an unavailable attacking argument can change a target from `defeated` or `contested` to `justified`. Work on incomplete argumentation frameworks treats uncertain arguments and attacks explicitly rather than assuming their absence. For `lara-evidence@0.1`, use a conservative outer `evidence-blocked` result for every root in a declared-graph component touched by quarantine; keep `lara-core@0.1` unchanged. A less conservative direct or completion-based incomplete-AF semantics is future research.
3. **Dependency reports must be generated by the checker capability, not trusted from checker output.** A registered checker receives object bytes only through a read API that records every object access. The runner constructs the dependency report. Otherwise a buggy checker can consume an object and omit it from replay identity.
4. **Integrity and scientific provenance are different layers.** The canonical manifest establishes byte identity. It does not replace PROV-O's entity/activity/agent model or Workflow Run RO-Crate's workflow-run packaging, and exact transcription does not establish semantic adequacy. Keep the v0.1 manifest small, but expose stable object identifiers and roles so a later RO-Crate/PROV adapter can map them without changing the calculus.

The goal/attempt proposal is useful process tooling, not a LARA language contribution. A Git ancestor relation proves checkpoint-relative order, not wall-clock priority. Call a record “preregistered” only when the checkpoint is witnessed by an external immutable, time-stamped service; otherwise report `prior-in-checkpoint-history`. OSF registrations are a concrete model: a preregistration is a time-stamped, read-only plan posted before data collection or analysis.

Research anchors:

- Dung, *On the Acceptability of Arguments and its Fundamental Role in Nonmonotonic Reasoning, Logic Programming and n-Person Games* (1995): <https://www.cs.ait.ac.th/~dung/Site/Publications_files/n-games.pdf>
- Modgil and Prakken, *The ASPIC+ Framework for Structured Argumentation: A Tutorial* (2014): <https://doi.org/10.1080/19462166.2013.869766>
- Mailly, *Grounded Semantics and Principle-Based Analysis for Incomplete Argumentation Frameworks* (2024): <https://doi.org/10.1016/j.ijar.2024.109282>
- Clark, Ciccarese, and Goble, *Micropublications* (2014): <https://doi.org/10.1186/2041-1480-5-28>
- Al Manir et al., *Evidence Graphs* (2021): <https://doi.org/10.1101/2021.03.29.437561>
- OMG Structured Assurance Case Metamodel 2.3: <https://www.omg.org/spec/SACM/2.3/About-SACM>
- W3C PROV-O: <https://www.w3.org/TR/prov-o/>
- Workflow Run RO-Crate: <https://doi.org/10.1371/journal.pone.0309210>
- OSF registrations and preregistrations: <https://help.osf.io/article/330-welcome-to-registrations>

---


## 1. What contributes to the calculus

| RIT lesson | LARA placement | Calculus contribution? | Reason |
|---|---|---:|---|
| Re-extract a claim input from immutable bytes | Evidence-admission judgment before `Gamma` construction | **Yes** | It defines the previously implicit world-to-leaf boundary and composes with the existing support judgment. |
| Distinguish accepted, unavailable, and malformed evidence | `admit` / `quarantine` / `reject` outcome algebra | **Yes** | The outcome changes whether a leaf may enter the checking context without turning every missing measurement into whole-program failure. |
| Record exact checker, selector, source digest, and dependencies | Evidence dependency judgment/report | **Yes, abstractly** | The calculus can state which checked premises an admitted leaf depends on. Concrete hashing and parsing stay outside the proof kernel. |
| SHA-256 manifests and concrete table/log extractors | Artifact resolver and closed checker registry | No | These are trusted implementations of the abstract judgment, not argumentation rules. |
| Goal before attempt; immutable attempt history; failure receipts | External registration receipt / process tooling | No | This establishes temporal integrity and auditability only when an external witness is trusted; it does not define support, attack, or grounded status. |
| Scalar grounding tiers as automatic winners | Nowhere in the defeat calculus | **No** | A trust tier is not a scientific defeat relation. Provenance remains admission metadata unless a named policy gives it semantics. |
| Lean arithmetic as the organizing principle | Optional strict or leaf-checker backend | **No** | It helps with narrow decidable subclaims but does not replace schemes, critical questions, typed defeat, or policy-relative status. |

The paper-level claim should be narrow:

> LARA composes a deterministic evidence-admission judgment with a structured-argumentation judgment. The first establishes that a leaf is the exact output of a named checker over pinned bytes and a pinned mapping payload; the second establishes what that leaf is permitted to support and how defeaters affect the result.

This is not justification semantics and not a truth theorem. Possible-world/justification semantics remain related semantic extensions; they must not be conflated with byte extraction.

---

## 2. Global invariants

1. `lara-core@0.1` retains its existing proposition, rule, support-term, typed-attack, grounded-labelling, four-status, and `IncompleteArgument` rejection behavior.
2. A concrete leaf checker is selected from a closed registry. Artifact input never supplies executable checker code.
3. Every admitted certified leaf has one exact checker identity, one canonical payload, at least one source reference, and a runner-generated dependency report containing every object the checker read.
4. `quarantine` contributes a removal seed. After group consistency has read the full declared leaf set, policy and group seeds are unioned once; one prune removes the leaves, every dependent argument (including dependencies nested in premises and discharges), and every attack with a removed raw endpoint before core checking. It is not evidence that the removed material is false. Every root selected by blocked reporting from that same prune receives the outer result `evidence-blocked`; its core label is conditional and must not be presented as the final checked claim status.
5. `reject` is reserved for malformed or integrity-violating input: digest mismatch, path escape, unknown checker, malformed payload, ambiguous row selection, or policy-mandated escalation.
6. Under frozen v0.1, a submitted argument with an open mandatory obligation is rejected as `IncompleteArgument`; a source claim is a `gap` only when it has no complete submitted support argument. Accepting partial alternatives is explicitly outside this plan.
7. A raw core `.sexp` verdict is relative to the supplied `Gamma`. It must not be reported as byte-evidence-checked. The full `.lara` artifact path reports both evidence and core identities.
8. Hashes, checker versions, canonical payloads, the complete runner-generated dependency set, and the evidence report digest are replay identity. A changed dependency is a different run, not a replay of the old run.
9. Goal/attempt history stays outside `lara-core`; it cannot create support, attacks, or statuses.
10. No accepted run may be partially persisted. Evidence report, core verdict, and combined report publish transactionally.
11. “Preregistered” requires an externally witnessed immutable timestamp. A locally ordered checkpoint without such a witness is only `prior-in-checkpoint-history`.

---

## Task 1: Freeze the boundary and paper claim

> **GATED — do not execute from this sketch.** This task proposes the byte-level
> `lara-evidence@0.1` layer under #78. Its composition pseudocode below is archival, not a runtime
> API: if #78 is later ungated, it must be redesigned around the frozen opaque source carrier and
> canonical multi-cause audit rather than passing `Q`, retained structures, or `affectedRoots`
> independently.

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

admitPi(A, L) = Reject(e) | Admitted(Gamma_checked, Q)
Gamma_checked = { l : p | l in L and l ⇓ admit(J, D) }
```

Where:
- `A` is an immutable artifact snapshot resolved from a canonical manifest.
- `Pi` is the policy, including the closed checker registry and escalation rules.
- `J` is a sealed successful leaf judgment.
- `D` is the exact dependency report.
- `Q` is the quarantined-leaf set with located diagnostics.
- `e` is the first deterministic whole-program rejection, if one exists.

Define program acceptance as composition, not as a new defeat rule:

```text
verify(A, Pi, P) =
  case admitPi(A, leaves(P)) of
    Reject e -> reject e
    Admitted(Gamma_checked, Q) ->
      let P_checked = pruneQuarantined(P, Q)
          U_checked = lower(P_checked, Gamma_checked)
      in sourceReport(coreCheck(U_checked), Q, affectedRoots(P, Q))

publicStatus(root) =
  evidence-blocked                              if root in affectedRoots(P, Q)
  conditionalCoreStatus(root)                   otherwise
```

`pruneQuarantined(P, Q)` removes every quarantined leaf, every argument whose transitive support term contains one, and every attack with a removed endpoint; the lowered core unit therefore contains exactly `Gamma_checked`, the retained arguments, and the retained attacks. `affectedRoots(P, Q)` is computed on the declared presentation graph before this pruning. It is the set of roots in an undirected component that reaches a quarantined leaf through leaf containment, subargument/parent links, support-root links, or attack endpoints. This intentionally conservative v0.1 rule prevents evidence loss from improving a public status. The report retains the core label as a conditional diagnostic and retains `Q`. It may also explain open obligations on a rejected input, but under `lara-core@0.1` a submitted incomplete argument produces `IncompleteArgument`; it is never silently treated as an accepted AF alternative.

**Step 2: Freeze the outcome join**

For multiple references/checks on one leaf, use the most restrictive outcome:

```text
admit < quarantine < reject
```

Run every independently safe check needed for a deterministic report. Reject manifest/path integrity failures before opening artifact objects. The leaf outcome is the maximum of the completed checks. At program level, any `reject` rejects the source artifact; otherwise all quarantined leaves are removed transitively for the conditional core run and every affected public root is labelled `evidence-blocked`.

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
- The quarantine-relevance rule prevents a missing attacker from improving a public claim status.
- The raw-core, conditional-core, and full-artifact guarantees are visibly different.
- The document explicitly says that RIT-style history is not part of the calculus.

**Commit**

```bash
git add docs/evidence-admission-decision.md docs/spec.md docs/lara-surface-grammar.md plans/research-proposal.md docs/comparison-rit-lara.md
git commit -m "docs: freeze evidence admission boundary"
```

---

## Task 2: Repair source admission conformance without changing `lara-core@0.1`

> **SUPERSEDED — do not execute this task from this document.** Use the 2026-08-05 runtime plan and
> companion metatheory plan linked at the top. They require the opaque source carrier and canonical
> multi-cause audit; any conflicting file list, API sketch, test list, or commit recipe below is
> historical only.

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
8. Quarantining the only attacker of a root cannot improve its public result to `justified`; it returns `evidence-blocked` and records the conditional core label separately.
9. A root outside every quarantine-relevance component retains its ordinary core status.

The first five tests must fail against the current all-declared `gamma` construction in `Lara.Elaborate.elaborate`. Test 8 must use a graph where naïve deletion demonstrably changes the grounded label.

**Step 2: Implement one source admission pass**

Replace the unconditional presentation environment with a total pass over every declared leaf. Exact
`(LeafKind, Provenance)` lookup defaults omitted/unmatched rows to `admit`; duplicate admission keys
and duplicate `LeafId` declarations are source invalidity. Evaluate duplicate-report consistency on
the full declared leaf set, then union policy- and group-quarantine seeds once. Compute argument
dependencies with the existing structural `leaves(w)` function (including premises and discharges);
retain an argument iff every dependency is admitted, and retain an attack iff neither raw endpoint
was removed. Never remove only the `Gamma` entry: that produces a later core R1 `MissingLeaf`
rejection and is not quarantine or a route to gap. Source R8, group R9, and core R1 remain distinct;
the complete precedence, CLI exception, hidden carrier, and canonical audit are fixed by the
2026-08-05 decision linked above.

**Superseded API note (2026-08-05).** Do not implement the formerly proposed public
`AdmissionResult` shared by elaboration and reporting. Independently exposed admitted-leaf maps,
retained structures, and affected-root sets would let callers assemble inconsistent projections and
bypass the canonical multi-cause audit. The runtime program instead requires an opaque source carrier
whose sole smart constructor binds replay identity, the full declared unit, the policy seed, the one
combined policy-plus-group prune, and the canonical audit. Reporting receives only projections from
that carrier; it cannot construct or recompute retained leaves/arguments/attacks, affected roots, or
audit rows. `Lara.Admission` may remain pure and perform no filesystem access, but purity does not
relax the carrier invariant.

**Step 3: Preserve and document the v0.1 hole contract**

Do not change `checkArguments`, `PEIncompleteArgument`, the core wire rejection, Lean, or frozen fixtures in this task. Keep these distinctions explicit:

- a submitted open-obligation argument is an honest whole-unit rejection under `lara-core@0.1`;
- `Lara.Reporting` may explain its located holes on the reject path;
- an accepted `gap` is represented by no complete support argument, matching `corpus-units/LOWERING.md` and trace decision N93;
- admitting a complete sibling while retaining an incomplete diagnostic would be useful, but it is a future v0.2 semantics change, not a conformance repair.

Update the comparison and spec wording where they currently imply that accepted partial alternatives are already required by v0.1.

**Step 4: Preserve source diagnostics**

The carrier's canonical audit records one row per quarantined leaf with every policy/group cause,
then every pruned argument and attack in declaration order. A query selected by blocked reporting
from that same prune reports `evidence-blocked`; it may retain the pruned graph's `gap`, `justified`,
`contested`, or `defeated` label only as a conditional diagnostic. Policy R8 selects the first leaf
in source declaration order whose exact key matches a `reject` row, never invokes the core checker,
and emits exactly one deterministic stderr line identifying the leaf id, kind, provenance, and
matched admission row.

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
- Quarantine cannot improve a public claim status by removing an attacker.
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
newtype CheckerM a = CheckerM (ExceptT EvidenceError (State DependencyLog) a)

readObject :: SourceRef -> CheckerM ByteString
runChecker :: Snapshot -> CheckerM LeafJudgment -> (Either EvidenceError LeafJudgment, DependencyLog)

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

Keep the `LeafJudgment` and `CheckerM` constructors private. A registered checker can inspect object bytes only through `readObject`; the runner—not checker code—deduplicates and emits the dependency log. `ExceptT` is outside `State`, so `runChecker` preserves the read trace even when checking fails; rejection reports may therefore identify every object consumed before the error. Constructor privacy is an API invariant, not a security proof; the checker registry remains in the trusted computing base.

**Step 2: Define the abstract Lean function**

Model artifact objects, checker identities, payloads, read traces, and successful judgments abstractly. Do not formalize SHA-256 in the calculus. A registry maps a checker identity to a total deterministic function, not an unconstrained relation; if relational notation is retained for the paper, state functionality as an explicit premise. Define `Outcome.join`, `admitLeaves`, quarantine relevance, and composition with `Compile.checkedAF`.

**Step 3: Prove the calculus properties**

Add theorem declarations and proofs for:

1. `evidence_outcome_deterministic`: a fixed snapshot, policy, checker registry, and leaf have one outcome because registered checking is functional.
2. `dependency_trace_complete`: every object made available to a checker through `readObject` occurs in the runner-generated dependency report.
3. `admitted_certified_has_judgment`: every certified leaf in the resulting `Gamma` has a successful judgment from the declared checker/version.
4. `quarantined_not_in_gamma`: quarantined leaves are absent from `Gamma`.
5. `quarantined_dependency_exclusion`: no compiled argument depends on a quarantined leaf.
6. `accepted_core_inputs_complete`: every argument in an accepted `lara-core@0.1` unit has an empty mandatory-obligation set.
7. `quarantine_public_nonpromotion`: a publicly reported `justified` root is not in the quarantine-relevance closure and has conditional core status `justified`.
8. `all_admit_identity`: when every leaf is admitted, evidence composition produces the same core input and verdict as the frozen source path.
9. `admission_replacement`: equal admitted contexts and equal retained programs produce equal conditional grounded statuses, independent of concrete evidence storage.
10. `more_restrictive_outcome_node_monotone`: replacing an outcome by a more restrictive one cannot add a leaf or AF node.

Do **not** claim that node monotonicity implies consequence-level monotonicity; LARA remains non-monotonic across AF changes. `quarantine_public_nonpromotion`, not graph pruning, is the safety result needed for public reporting.

**Step 4: Add Haskell property tests**

Generate small leaf/outcome/dependency structures and check the executable counterparts of the ten properties. Include duplicate checker IDs, mismatched versions, empty references, a checker that reads two objects, mixed admit/quarantine/reject lists, and a quarantined sole attacker whose deletion would improve the conditional core label.

**Verification**

```bash
cabal test
(cd lean && lake build)
./scripts/check-axioms.sh
```

Acceptance criteria:
- The Haskell model has no IO entry point and exports neither the judgment nor checker-monad constructor.
- A checker that reads an object cannot omit it from the runner-generated dependency report.
- Lean proofs use only the project's allowed axiom set.
- Every theorem is about extraction/admission composition or conservative reporting, not empirical truth.

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
  (object data evidence/results.tsv SHA256 BYTE_LENGTH)
  ...)
```
Add `bytestring`, `text`, and `cryptohash-sha256` to the library dependencies. Use `Crypto.Hash.SHA256.hash`; do not call `shasum`, `sha256sum`, OpenSSL, or another process.

Rules:
- object role is one of `data`, `code`, `config`, `method`, `environment`, or `other`; it is descriptive metadata, not a truth guarantee;
- paths are relative normalized POSIX paths encoded as UTF-8;
- absolute paths, empty segments, `.`/`..`, duplicate paths, symlinks, and NUL are rejected;
- objects are sorted by unsigned UTF-8 path bytes in canonical form;
- object digests are `sha256:` plus exactly 64 lowercase hexadecimal characters; byte lengths are canonical nonnegative decimals;
- each captured file's byte length and SHA-256 must match its manifest row;
- the artifact identity is SHA-256 of the canonical manifest bytes, and the resolver rejects unless it equals `programDigest`;
- only manifest-listed objects may satisfy `SourceRef`s;
- stable object path, digest, and role are emitted so a provenance exporter can map them to PROV/RO-Crate later without making either vocabulary part of `lara-core`.


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
2. Read the object through `readObject`; the runner records the access.
3. Parse `TERM` and every selected cell as canonical LARA ground terms.
4. Select exactly one row whose `COLUMN` term is identical to `TERM` after `nfTerm`.
5. Construct `Prop PRED selectedTerms` in the listed column order.
6. Admit only if the constructed proposition is equivalent to `leafProp` under `(===)`.
7. The runner emits the dependency containing role, object digest, source ref, checker/version, and canonical payload.
8. Zero rows, multiple rows, malformed terms, missing columns, or proposition mismatch reject with distinct located errors.

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

Every mutant must reject before core checking. The valid fixture must return the exact same runner-generated dependency report on repeated runs. Add a harness test in which checker code reads an extra object: the extra object must appear in the report without checker cooperation.

**Verification**

```bash
cabal test
```

Acceptance criteria:
- The valid fixture admits exactly one leaf and records every consumed input.
- Every named mutant rejects in the evidence layer.
- The checker executes no external command, reads no unmanifested file, and cannot self-report an incomplete dependency set.
- Manifest roles remain non-authoritative metadata and do not affect admission or grounded status.

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
→ run closed leaf checkers with traced object access
→ apply admit/quarantine/reject
→ compute quarantine relevance on the declared graph
→ lower retained program to Unit
→ run lara-core@0.1 for the conditional core verdict
→ overlay evidence-blocked on affected public roots
→ emit one combined report transactionally
```

A source artifact rejected by evidence admission must not invoke `runCheck`.

**Step 3: Separate guarantee labels**

Reports must carry:

```text
(core lara-core@0.1)
(evidence declared
  | (checked lara-evidence@0.1 REPORT_SHA256
       (availability complete | (blocked ROOT_ID*))))
```

Rules:
- `.lara` plus a validated manifest may produce `evidence checked`; affected roots additionally carry `availability blocked`.
- `evidence-blocked` is the public result for an affected root; its core label is explicitly `conditional-core-status`.
- raw `.sexp` always produces `evidence declared` because the core checker receives `Gamma`, not artifact bytes.
- the decoder rejects any raw `.sexp` that claims `evidence checked`.
- CLI prose and JSON must not call `evidence declared` a full artifact verification or present a conditional core label as final.

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
1. Verify the manifest-backed running example and observe `evidence checked`, `availability complete`, and the expected claim status.
2. Quarantine the sole attacker in a fixture and observe `evidence-blocked`, never an improved public `justified`, while the conditional core label is preserved separately.
3. Change one table byte and observe evidence rejection before core invocation.
4. Feed the emitted raw core `.sexp` directly and observe `evidence declared`, never `checked`.
5. Restore the byte and replay the original combined report exactly.

**Commit**

```bash
git add src/Lara/AST.hs src/Lara/Syntax.hs src/Lara/Elaborate.hs src/Lara/Replay.hs src/Lara/ExpectedJson.hs src/Lara/Driver.hs app/Main.hs test/SyntaxSpec.hs test/ElaborateSpec.hs test/CliSpec.hs test/ReplaySpec.hs test/EvidenceIntegrationSpec.hs examples/running-example scripts/replay.sh scripts/test-replay-tamper.sh lara.cabal
git commit -m "feat: compose evidence and core verification"
```

---

## Task 6: Document an external registration-receipt seam; defer a custom history service

**Files**
- Create: `docs/registration-receipt-contract.md`
- Modify: `docs/comparison-rit-lara.md`
- Modify: `plans/research-proposal.md`

**Step 1: Define the minimal external receipt**

Document a backend-neutral receipt:

```text
registration-receipt:
  provider
  immutable-record-id
  registered-content-digest
  witness-issued-at
  witness-proof
```

The receipt says that an external witness fixed a content digest at a time. It does not enter `Gamma`, create an attack, or affect grounded status. LARA may cite the registered object later through the ordinary leaf-and-policy path.

**Step 2: Use precise labels**

- `preregistered`: the goal/analysis plan digest is covered by a verified external immutable timestamp that predates the attempt.
- `prior-in-checkpoint-history`: the goal is an ancestor of the attempt in a content-addressed history, but no external time witness was verified.
- `post-hoc`: the goal and attempt first appear together or the goal follows the attempt.

Git ancestry may establish the second label. Git author/committer timestamps alone must not establish the first. OSF or an equivalent immutable registration service is the reference model; do not add a network dependency to `lara-core`.

**Step 3: Apply a build/no-build gate**

Do not create a LARA event-log schema, validator, or Git backend in this milestone. Reconsider a separate protocol package only if evaluation identifies a workflow that existing registration services plus a content-digest receipt cannot express. Such a package requires its own threat model for witness authenticity, key rotation, clock semantics, history rewrite, and availability.

Acceptance criteria:
- The documentation never equates local Git order with preregistration.
- Registration receipts remain outside the calculus and trusted core.
- No goal or attempt event automatically changes a LARA claim status.
- Task 6 adds no Haskell module, schema, or runtime dependency.

**Commit**

```bash
git add docs/registration-receipt-contract.md docs/comparison-rit-lara.md plans/research-proposal.md
git commit -m "docs: define external registration receipt seam"
```

---

## Task 7: Evaluate before promoting evidence admission into the paper's main claim

**Files**
- Create: `scripts/measure-evidence-admission.hs`
- Create: `ara/evidence/status/evidence_admission_status.md`
- Create: `ara/evidence/results/evidence_admission_results.json`
- Create: `docs/evidence-admission-measurement-contract.md`
- Modify: `plans/research-proposal.md`
- Do not edit external paper source in this task; record the promotion decision and exact claim delta in `ara/evidence/status/evidence_admission_status.md`

**Step 1: Freeze the measurement contract before running it**

Measure on the existing deterministic corpus:
- total leaves, papers/artifact packages, and claim families;
- certified leaves eligible for each closed checker family;
- successfully admitted leaves;
- quarantined and rejected leaves by reason;
- roots in quarantine-relevance components;
- conditional core-status changes under naïve pruning, including favorable changes that public reporting suppresses;
- evidence-layer runtime and report bytes;
- added trusted Haskell LOC and mechanized Lean LOC;
- tamper mutants detected before core checking;
- dependency-trace completeness mutants;
- independent human judgments of whether each payload selects the intended result and whether the resulting proposition faithfully states that result.

Use the proposal's existing two-annotator/adjudication protocol for semantic-faithfulness judgments. Do not use LLM judging for these measurements.

**Step 2: Run three ablations**

1. **Declared-leaf baseline:** current support calculus with all policy-admitted leaves trusted at the world boundary.
2. **Naïve-pruned diagnostic:** the smaller core graph after quarantine, retained only to quantify how deletion changes grounded labels.
3. **Conservative checked treatment:** identical admitted graph, with `evidence-blocked` over every quarantine-affected public root.

A status change is evidence about the boundary's operational effect, not evidence that the resulting scientific claim is true. A favorable naïve-pruning transition is a hazard caught by the conservative layer, not a success.

**Step 3: Apply the promotion gate**

Evidence admission remains a bounded implementation extension unless all are true:
- at least two independently produced artifact packages, ten certified leaves, two claim families, and two closed checker families use original outputs rather than hand-authored assertion files;
- every declared tamper and incomplete-dependency mutant is rejected or recorded before core checking;
- no quarantine-affected root receives an unqualified public core status;
- the dependency report is sufficient to reproduce every admitted proposition exactly;
- payload-to-result and proposition-to-result mappings pass the frozen two-annotator semantic-faithfulness protocol;
- the Haskell/Lean core remains byte-exact after admission;
- the added TCB and guarantee split are reported honestly;
- at least one non-definitional composition/safety theorem is used by the implementation and evaluation rather than appearing as an isolated formal ornament.

Meeting this gate permits evidence admission to be presented as a secondary technical contribution. The paper's main contribution remains LARA's structured-argumentation language unless the argumentation evaluation independently fails. Failing the gate means report evidence admission as bounded tooling or future work, not as novelty.

Registration receipts remain process metadata regardless of their evaluation; they do not become a calculus contribution.

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

1. **Do Task 1 now.** It resolves the conceptual and reporting-safety questions before code changes.
2. **Do Task 2 before the paper artifact is frozen.** It repairs the current all-admit presentation lowering while preserving the frozen core and its honest open-obligation rejection.
3. **Inventory real artifact formats before Task 3.** If the corpus cannot support the Task 7 coverage gate, stop after Task 2 and present evidence checking as future work.
4. **Do Tasks 3–5 as one evidence-admission milestone only after the inventory passes.** These tasks add a secondary assurance boundary; they do not replace the argumentation contribution.
5. **Run Task 7 immediately after Task 5.** Let coverage, semantic-faithfulness, quarantine-hazard, dependency, and tamper results decide promotion.
6. **Do Task 6 as documentation only.** Do not build a custom history service in this paper cycle.

## 4. Explicit non-goals

- Reproduce RIT's full Claim Flow Graph inside LARA.
- Replace LARA schemes and attacks with Lean arithmetic.
- Present evidence admission as a substitute for argumentation semantics.
- Treat quarantined evidence as false or silently publish a status improved by deletion.
- Let trust tiers or manifest roles automatically defeat lower-tier evidence.
- Treat Git commit order or local timestamps as preregistration.
- Claim that a successful extractor proves empirical truth or semantic faithfulness.
- Add dynamic checker plugins or arbitrary shell extractors.
- Make raw `.sexp` inputs claim full byte-evidence verification.
- Build a bespoke goal/attempt service without a demonstrated gap in existing registration systems.
- Mix evidence admission and registration receipts into one versioned layer.
