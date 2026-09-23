# Evidence-admission gated tasks (`lara-evidence@0.1` — not planned)

_Status: archival design record. The roadmap's evidence-admission scope
decision closed 2026-08-26 as **not planned**: "The approved scope is
complete. The remaining `lara-evidence@0.1` work is not planned; its design
remains preserved in the repository." This document is that preserved design.
It replaces `plans/2026-08-04-rit-informed-evidence-admission.md` Tasks 3, 4,
5, and 7, which were deleted 2026-09-09 once nothing under them remained live
— the plan's Task 1/2/6 output already landed as
`docs/evidence-admission-decision.md`, `docs/registration-receipt-contract.md`.
Read this as "if the inventory gate below is ever met and
a researcher explicitly approves the work," not as scheduled work._

The design boundary, judgment forms, outcome join, and negative guarantees
this layer would have to respect are already frozen in
`docs/evidence-admission-decision.md`. This document preserves the deeper
implementation sketch for the four tasks that stayed gated: mechanizing the
abstract calculus, one concrete checker, integration, and the promotion gate.

## Inventory gate (unchanged from `docs/evidence-admission-decision.md` §7)

No evidence-layer code is written before this inventory passes; failing it
closes the work unbuilt, which is an acceptable outcome:

- at least two independently produced artifact packages whose original
  outputs (not hand-authored assertion files) can back Lara leaves;
- at least ten certified leaves across at least two claim families;
- at least two closed leaf-checker families with deterministic,
  byte-addressed extraction.

## Task 3 sketch: mechanize the abstract evidence-admission calculus

A pure Haskell model with no filesystem or process access:

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

data EvidenceOutcome
  = EvidenceAdmit LeafJudgment [EvidenceDependency]
  | EvidenceQuarantine EvidenceDiagnostic
  | EvidenceReject EvidenceError
```

`LeafJudgment` and `CheckerM` constructors stay private; a registered checker
can inspect object bytes only through `readObject`, and the runner — not
checker code — deduplicates and emits the dependency log, so a buggy checker
cannot omit a consumed object from replay identity.

The paired Lean model defines `Outcome.join`, `admitLeaves`, quarantine
relevance, and composition with `Compile.checkedAF` abstractly (no SHA-256 in
the calculus), and proves ten properties: outcome determinism; dependency-trace
completeness; every admitted certified leaf has a successful judgment from the
declared checker/version; quarantined leaves are absent from `Gamma`; no
compiled argument depends on a quarantined leaf; every accepted
`lara-core@0.1` argument has an empty mandatory-obligation set;
`quarantine_public_nonpromotion` (the safety result needed for public
reporting, distinct from graph-pruning monotonicity, which does not hold);
an all-admit run reproduces frozen `lara-core@0.1` bytes exactly;
admission-replacement independence from concrete evidence storage; and that
replacing an outcome with a more restrictive one cannot add a leaf or AF node.

## Task 4 sketch: one closed concrete checker, `tsv-row@1`

A canonical S-expression artifact manifest, hashed with `Crypto.Hash.SHA256`
(no shelling out to `sha256sum`/OpenSSL), listing objects by role
(`data`/`code`/`config`/`method`/`environment`/`other`), normalized relative
POSIX path, and `sha256:`-prefixed digest; only manifest-listed objects can
satisfy a `SourceRef`.

The checker payload:

```text
(tsv-row
  (ref NAT)
  (key COLUMN TERM)
  (columns COLUMN*)
  (predicate PRED))
```

Semantics: resolve `leafRefs[NAT]` to one manifest object, read it through the
traced `readObject`, parse `TERM` and every selected cell as canonical Lara
ground terms, select exactly one row whose `COLUMN` term is identical to
`TERM` after normalization, construct `Prop PRED selectedTerms` in column
order, and admit only if that proposition is equivalent to `leafProp`. Zero
rows, multiple matching rows, malformed terms, missing columns, or a
proposition mismatch each reject with a distinct located error. This proves
exact structural transcription under the declared payload — nothing about
whether the column names carry the intended scientific meaning or whether the
table came from a valid experiment.

Mutation coverage (each must reject before core checking): object byte,
manifest digest, byte length, path traversal, symlink, checker version,
payload key, payload column order, duplicate matching row, leaf proposition,
and UTF-8/line-ending validity — plus a harness proving an extra object read
by checker code still appears in the runner-generated dependency report.

## Task 5 sketch: integration without overstating raw-core guarantees

Pipeline order on the `.lara` path:

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

A rejected source artifact must never invoke `runCheck`. Reports carry
separate guarantee labels (`core lara-core@0.1` vs. `evidence declared` vs.
`evidence checked ... availability complete|blocked`), and the decoder rejects
any raw `.sexp` claiming `evidence checked` — that path only ever produces
`evidence declared` because the core checker receives `Gamma`, never artifact
bytes. Replay identity extends to cover core version, evidence version,
policy ID, strict backend identities, selected leaf-checker identities, theory
digests, artifact-manifest digest, and evidence-report digest. Publication is
transactional: capture manifest objects into an immutable snapshot, build the
evidence report/core verdict/combined JSON in a temporary sibling directory,
then atomically rename to a content-addressed final directory; never overwrite
an existing run directory, and leave no accepted partial output on rejection.

## Task 7 sketch: the promotion gate

Evidence admission stays a bounded implementation extension — never promoted
to a paper-level contribution — unless all of the following hold:

- at least two independently produced artifact packages, ten certified
  leaves, two claim families, and two closed checker families use original
  outputs rather than hand-authored assertion files;
- every declared tamper and incomplete-dependency mutant is rejected or
  recorded before core checking;
- no quarantine-affected root receives an unqualified public core status;
- the dependency report is sufficient to reproduce every admitted
  proposition exactly;
- payload-to-result and proposition-to-result mappings pass a frozen
  two-annotator semantic-faithfulness protocol (no LLM judging);
- the Haskell/Lean core remains byte-exact after admission;
- the added trusted-computing-base and guarantee split are reported
  honestly;
- at least one non-definitional composition/safety theorem is used by the
  implementation and evaluation, not left as an isolated formal ornament.

Measurement runs three ablations before applying the gate: the declared-leaf
baseline (today's calculus, all policy-admitted leaves trusted at the world
boundary); a naïve-pruned diagnostic (the smaller graph after quarantine,
kept only to quantify how deletion changes grounded labels — a favorable
transition here is a hazard the conservative layer must catch, not a
success); and the conservative checked treatment (`evidence-blocked` over
every quarantine-affected public root). Failing the gate means evidence
admission is reported as bounded tooling or future work, never as novelty.

## Explicit non-goals (unchanged)

- Reproduce RIT's full Claim Flow Graph inside Lara.
- Replace Lara schemes and attacks with Lean arithmetic.
- Present evidence admission as a substitute for argumentation semantics.
- Treat quarantined evidence as false, or silently publish a status improved
  by deletion.
- Let trust tiers or manifest roles automatically defeat lower-tier evidence.
- Treat Git commit order or local timestamps as preregistration.
- Claim that a successful extractor proves empirical truth or semantic
  faithfulness.
- Add dynamic checker plugins or arbitrary shell extractors.
- Make raw `.sexp` inputs claim full byte-evidence verification.
- Build a bespoke goal/attempt service without a demonstrated gap in existing
  registration systems.
- Mix evidence admission and registration receipts into one versioned layer.
