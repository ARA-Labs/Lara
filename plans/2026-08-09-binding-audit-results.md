# Blinded Binding-Audit Results Implementation Plan

> **Status (2026-08-19): half-executed — kept for the unexecuted half.**
> Tasks 1–4 landed in PR #96: the subject projection, the strict TSV codec and
> sealed-judgment validators, the blinded packet (`scripts/binding-audit.hs
> prepare|validate|summarize`), and the canonical summary renderer are all in
> the tree with tests. Tasks 5–8 have **not** run: no second-author judgments
> have been collected, so `measurements/binding-audit/` holds only
> `worklist.tsv` — there is no `results.tsv`, `object-results.tsv`,
> `summary.json`, or method `README.md`, and no paper text cites the audit.
> Issue #87 was closed on the pipeline, not on the audit. Execute Tasks 5–8 to
> finish it; nothing else in this plan is outstanding.

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Complete issue #87 Steps 1–3 with a status-blind second-author audit, mechanically validated human judgments, deterministic post-seal cross-tabs, committed results, and paper text sourced from generated numbers.

**Architecture:** Preserve the existing 38-row status-free worklist. Extend the claim-support reporting projection with one checked strict-step subject and three raw-ID-aligned typed-attack subjects, then add a separate `Lara.BindingAudit` pipeline with `prepare`, `validate`, and `summarize` modes. `prepare` creates a detached review packet; `validate` checks completed human files without inspecting statuses; `summarize` repeats validation, joins requested-claim statuses only in memory, and atomically writes canonical `summary.json` without modifying any judgment.

**Tech Stack:** GHC2021 Haskell, Cabal, QuickCheck, strict `ByteString` repository IO with explicit UTF-8 decode/encode at parser/renderer boundaries, the existing hand-rolled `Lara.ExpectedJson` renderer, manifest-driven `Lara.ClaimSupport.Load`, same-directory `Lara.AtomicWrite.atomicWriteWith`, Lean 4 verification gates, shell reproducibility scripts, and the external LaTeX paper checkout.

```text
CHECKED CORPUS + SURFACE
          |
          v
   manifest-ordered UnitRecord
      | status-free rows/subjects                    | requested statuses
      v                                              | (never forced by validate)
prepare <detached-dir>                               |
      | exactly 3 files, no status                   |
      v                                              |
SECOND-AUTHOR REVIEW                                 |
      | completed 38 + 4 judgments                   |
      v                                              |
validate <packet-dir> -- writes nothing              |
      |                                              |
      v                                              |
SEAL JUDGMENT COMMIT  <------------------------------+
      |
      v
summarize -- revalidate, join statuses in memory, hash exact inputs
      |
      v
atomic summary.json -> named JSON paths -> external paper
```

`Lara.BindingAudit` should carry a compact version of this diagram beside the
three orchestration entry points. The status-join edge and artifact write
ownership are maintained invariants, not just delivery sequencing.

## Global Constraints

- The approved design is `docs/superpowers/specs/2026-08-09-binding-audit-results-design.md`.
- `measurements/binding-audit/worklist.tsv` remains byte-unchanged and status-free.
- Audit all 38 leaves; sampling is prohibited.
- Human classifications are exactly `faithful`, `unfaithful`, or `underdetermined`.
- Every judgment has a nonempty justification; `unfaithful` has a substantive divergence note; the other classes use exactly `-`.
- The one strict step and three typed attacks are audited separately from the 38 leaf bindings.
- Typed-attack identity uses raw `ArgId` endpoints aligned with checked semantic attacks. Never identify attacks by term equality or re-resolve them after filtering.
- Checker statuses enter only after both human result files are complete and sealed.
- The status cross-tab uses each unit's single requested-claim status; it does not invent a status for an intermediate claim.
- Do not change corpus units, fixtures, `measurements/frozen/`, checker behavior, Lean semantics, core/wire bytes, replay bundles, or freeze tags.
- A failed command must leave the prior complete `summary.json` intact and must never modify human judgment files. Worklist/result copies and Git identities operate on strict bytes; text is decoded as UTF-8 only for validation.
- The human handoff after Task 4 is blocking. Tasks 5–8 cannot complete until the second author returns actual judgments.

## File Structure

| Path | Responsibility |
| --- | --- |
| `src/Lara/BindingAudit/Types.hs` | Leaf dependency-free closed types shared by claim-support projection and analyzer. |
| `src/Lara/BindingAudit/Tsv.hs` | One strict escaped-TSV document codec plus the single typed `SourceRef` cell codec used by worklist, templates, and result parsers. |
| `src/Lara/BindingAudit.hs` | Prefix-free audit errors, UTF-8 byte/text boundaries, template rendering, judgment parsing/validation, worklist freshness, IO dependencies, joins, aggregation, summary JSON, and packet/summary IO. |
| `src/Lara/ClaimSupport.hs` | Extend `UnitRecord` with the checked strict-step and raw-aligned typed-attack subjects; preserve all existing report bytes. |
| `src/Lara/Syntax.hs` | Export the existing canonical argument printer needed for strict-step audit text. |
| `src/Lara/ExpectedJson.hs` | Export the existing canonical checked-attack renderer instead of adding another attack spelling table. |
| `scripts/binding-audit.hs` | Thin CLI dispatch for `prepare <output-dir>`, `validate <packet-dir>`, and `summarize`. |
| `test/BindingAuditSpec.hs` | Focused pure and IO contracts for subjects, TSV, packets, validation, joins, summary, and freshness. |
| `test/ClaimSupportSpec.hs` | Existing frozen denominator/report-byte guards plus the corpus subject projection checks. |
| `test/Spec.hs` | Register `bindingAuditSpecProps`. |
| `lara.cabal` | Expose the three new library modules and register the new test module. |
| `measurements/binding-audit/results.tsv` | Sealed 38-row second-author leaf judgments. Added only after the handoff. |
| `measurements/binding-audit/object-results.tsv` | Sealed four-row strict-step/attack judgments. Added only after the handoff. |
| `measurements/binding-audit/summary.json` | Canonical analyzer output, including splits and post-seal status cross-tab. |
| `measurements/binding-audit/README.md` | Auditor, date, definitions, blinding boundary, method, and reproduction command. |
| `/Users/yfhe/overleaf/ara/lara/src/evaluation.tex` | Report audit denominator, rates, splits, and justified/unfaithful result. |
| `/Users/yfhe/overleaf/ara/lara/src/language.tex` | Cross-reference the completed audit from `sec:leaves`. |

---

### Task 1: Derive the four non-leaf audit subjects from checked records

**Files:**
- Create: `src/Lara/BindingAudit/Types.hs`
- Modify: `src/Lara/ClaimSupport.hs:155-240,298-423`
- Modify: `src/Lara/Syntax.hs:74-98,1619-1674`
- Modify: `src/Lara/ExpectedJson.hs:35-45,599-603`
- Modify: `lara.cabal:54-72`
- Test: `test/ClaimSupportSpec.hs:31-84`

**Interfaces:**
- Produces: `AuditSubjectId`, `AuditSubjectType`, `AuditSubject`, `urBindingAuditSubjects`.
- Produces: exported `printArg :: Arg -> [String]` and `renderAttack :: Attack -> String` by exposing the existing implementations, not copying them.
- Consumes later: Task 2 template rendering and Task 4 summary aggregation.

- [ ] **Step 1: Add failing corpus and synthetic subject properties**

Add registrations to `claimSupportSpecProps`:

```haskell
, ("claim-support: binding-audit non-leaf subjects are exactly 1 strict + 3 attacks", quickCheckResult prop_bindingAuditSubjects)
, ("claim-support: binding-audit attack subjects retain raw endpoints", quickCheckResult prop_bindingAuditSubjectEndpoints)
```

The corpus property must load the frozen records and assert this exact ordered identity:

```haskell
expectedSubjects =
  [ ("adaptive-pruning.C04:strict:a1", AuditStrictStep)
  , ("fre.C04:attack:undercut:d1:a1:rule", AuditTypedAttack)
  , ("test-time-model-adaptation.C04:attack:undercut:d1:a1:rule", AuditTypedAttack)
  , ("rebench-triton_cumsum.C09:attack:undercut:d1:a1:rule", AuditTypedAttack)
  ]
```

These raw IDs are pinned by the current surface units: all three attacks are
`undercut d1 a1.rule`. The order is the global manifest order already enforced
by the 38-row worklist: the adaptive-pruning strict subject, then the `fre`,
`test-time-model-adaptation`, and `rebench-triton_cumsum` attack subjects. Do
not sort subjects by ID or move rebench ahead of test-time adaptation.

The synthetic endpoint property must construct two attacks whose source/target arguments have structurally equal support terms but distinct `ArgId`s, then assert the subject IDs and `formal_object` strings preserve the two distinct endpoint pairs.
The strict-subject property must also construct a surface argument whose
`ArgId` matches the checked argument but whose `argTerm` differs. Subject
derivation must hard-fail before rendering; an identifier match alone does not
make the displayed formal object checked.

- [ ] **Step 2: Run the focused suite and observe the missing projection**

Run:

```bash
cabal test lara-test --test-show-details=direct
```

Expected: compilation fails because `urBindingAuditSubjects` and the new types do not exist.

- [ ] **Step 3: Add dependency-free audit subject types**

Create `src/Lara/BindingAudit/Types.hs`:

```haskell
module Lara.BindingAudit.Types
  ( AuditSubjectId (..)
  , AuditSubjectType (..)
  , AuditSubject (..)
  ) where

import Lara.AST (SourceRef)

newtype AuditSubjectId = AuditSubjectId String
  deriving (Eq, Ord, Show)

data AuditSubjectType
  = AuditStrictStep
  | AuditTypedAttack
  deriving (Eq, Ord, Show)

data AuditSubject = AuditSubject
  { auditSubjectId :: AuditSubjectId
  , auditSubjectType :: AuditSubjectType
  , auditSubjectFormalObject :: String
  , auditSubjectProseContext :: String
  , auditSubjectRefs :: [SourceRef]
  }
  deriving (Eq, Show)
```

Keep strings at this reporting boundary only. The identifier and closed type remain distinct types so subject IDs and vocabulary cannot be swapped silently.

- [ ] **Step 4: Export the existing canonical printers**

Add `printArg` to `Lara.Syntax`'s export list. Add `renderAttack` to `Lara.ExpectedJson`'s export list. Do not modify either function body or the bytes of any existing report.

- [ ] **Step 5: Extend `UnitRecord` and derive subjects in `computeUnit`**

Add:

```haskell
, urBindingAuditSubjects :: [AuditSubject]
```

Populate it with strict subjects followed by typed attacks within each manifest record:

```haskell
urBindingAuditSubjects = strictAuditSubjects ++ attackAuditSubjects
```

Use checked `loadBearingArgs` for the strict denominator and checked `unitAttacks unit` for attack identity. Match only by raw `ArgId` into the surface declarations to obtain human prose and refs. Before rendering a strict subject, require the surface argument's `argTerm` to equal the checked core `SupportTerm`; use the same contextual hard-error discipline as the existing surface/core leaf proposition check. A strict subject renders the complete canonical surface argument with `unlines (printArg surfaceArg)`, uses the supported claim's `claimNl`, and unions refs from its rooted leaves in first-occurrence order. An attack subject renders the checked `Attack` via `renderAttack`, identifies its target claim through the already-checked raw target `ArgId`, uses that claim's NL plus the source challenge expression as prose context, and carries source-leaf refs.

Generate stable IDs with one helper:

```haskell
strictSubjectId unitName (ArgId aid) =
  AuditSubjectId (unitName ++ ":strict:" ++ aid)

attackSubjectId unitName attack =
  AuditSubjectId
    (unitName ++ ":attack:" ++ attackKind attack ++ ":"
      ++ rawAttackSource attack ++ ":" ++ rawAttackTarget attack
      ++ ":" ++ rawAttackPosition attack)
```

Use the same hard-error discipline as the leaf worklist for missing, duplicate, derived, challenge, or mismatched surface context. Do not collapse subjects with `nub` on semantic values.

- [ ] **Step 6: Run the tests and existing byte guards**

Run:

```bash
cabal test lara-test --test-show-details=direct
cabal exec -- runghc scripts/claim-support.hs
```

Expected: all tests pass; `measurements/binding-audit/worklist.tsv` and the existing claim-support JSON/TSV remain byte-identical.

- [ ] **Step 7: Commit the subject projection**

```bash
git add src/Lara/BindingAudit/Types.hs src/Lara/ClaimSupport.hs src/Lara/Syntax.hs src/Lara/ExpectedJson.hs test/ClaimSupportSpec.hs lara.cabal
git commit -m "feat(audit): derive strict and attack subjects"
```

---

### Task 2: Add one strict TSV codec and sealed judgment validators

**Files:**
- Create: `src/Lara/BindingAudit/Tsv.hs`
- Create: `src/Lara/BindingAudit.hs`
- Modify: `src/Lara/ClaimSupport.hs:500-576`
- Modify: `lara.cabal:54-72,94-120`
- Create: `test/BindingAuditSpec.hs`
- Modify: `test/Spec.hs:194-217`

**Interfaces:**
- Produces from `Lara.BindingAudit.Tsv`: `renderTsvRow`, `parseTsv`, `TsvError`, `renderRefsCell`, `parseRefsCell`, and `RefCellError`.
- Produces from `Lara.BindingAudit`: `AuditClassification`, `LeafJudgment`, `ObjectJudgment`, `AuditError`, `auditErrorMessage`, `decodeAuditUtf8`, `validateWorklist`, `renderLeafTemplate`, `renderObjectTemplate`, `parseLeafJudgments`, `parseObjectJudgments`, `validateLeafJudgments`, `validateObjectJudgments`.
- Consumes: `BindingAuditRow`, `AuditSubject`, `UnitRecord` from Task 1. Library error text is contextual but does not include the CLI's `binding-audit:` prefix.

- [ ] **Step 1: Register a new focused test module with failing contracts**

Create `test/BindingAuditSpec.hs` exporting:

```haskell
module BindingAuditSpec (bindingAuditSpecProps) where

bindingAuditSpecProps :: [(String, IO Result)]
```

Register it in `test/Spec.hs` after `claimSupportSpecProps`. Add properties for:

- all four escaped characters round-trip (`\\`, tab, CR, LF);
- malformed escape, wrong column count, and embedded raw tab rejection;
- exact leaf template keys in worklist order;
- exact four-object template keys in record order;
- all three classification values;
- invalid enum rejection;
- missing, duplicate, unknown, and reordered keys;
- blank justification rejection;
- missing unfaithful divergence rejection;
- non-`-` divergence on faithful/underdetermined rejection.
- exact header rejection for both result schemas;
- strict LF documents with exactly one final newline; reject CRLF, missing or
  extra final newlines, and blank rows;
- whitespace-only justification and divergence rejection;
- all accepted and reserved `refs` cell forms round-trip through the shared
  typed codec;
- unknown object `subject_type` rejection.
- invalid UTF-8 rejection before any judgment validation or output write.

Use literal fixture rows in tests. Do not assert source text or implementation details; every case must distinguish an observable accepted/rejected file contract.

- [ ] **Step 2: Run the focused suite and verify it fails to compile**

Run:

```bash
cabal test lara-test --test-show-details=direct
```

Expected: compilation fails because `Lara.BindingAudit` and `Lara.BindingAudit.Tsv` are missing.

- [ ] **Step 3: Implement the shared strict TSV and refs codecs and preserve worklist bytes**

Create `Lara.BindingAudit.Tsv` with closed `TsvError` and `RefCellError`
types. `renderTsvRow` escapes `\\`, tab, CR, and LF in every cell and joins
cells with literal tabs. `parseTsv expectedColumns` parses a complete canonical
document: LF separators, exactly one final LF, no CR, no blank rows, no unknown
or trailing escape, and exactly `expectedColumns` cells per row.

`renderRefsCell` and `parseRefsCell` are the only typed `[SourceRef]` codec:
comma-separated refs, `-` for empty, and rejection of a ref containing comma
or equal to the reserved `-`. Higher layers add file role, row, and key
context to codec errors.

Refactor `bindingAuditTsv` row emission to call `renderTsvRow` and the shared
refs renderer. Preserve the existing contextual hard error for an invalid
worklist ref. The committed worklist freshness property must prove the
refactor is byte-preserving.

- [ ] **Step 4: Implement closed judgment types and parsers**

In `Lara.BindingAudit` define:

```haskell
data AuditClassification = Faithful | Unfaithful | Underdetermined
  deriving (Eq, Ord, Show)

data LeafJudgment = LeafJudgment
  { leafJudgmentUnit :: String
  , leafJudgmentLeafId :: LeafId
  , leafJudgmentClassification :: AuditClassification
  , leafJudgmentJustification :: String
  , leafJudgmentDivergence :: Maybe String
  }

data ObjectJudgment = ObjectJudgment
  { objectJudgmentSubject :: AuditSubjectId
  , objectJudgmentUnit :: String
  , objectJudgmentType :: AuditSubjectType
  , objectJudgmentFormalObject :: String
  , objectJudgmentProseContext :: String
  , objectJudgmentRefs :: [SourceRef]
  , objectJudgmentClassification :: AuditClassification
  , objectJudgmentJustification :: String
  , objectJudgmentDivergence :: Maybe String
  }
```

Use a structured `AuditError` sum for header mismatch, document/row/key problems, invalid class or subject type, blank human fields, generated-field drift, worklist drift, and divergence invariant failures. `auditErrorMessage :: AuditError -> String` includes file role plus 1-based row number and key when available, but never adds `binding-audit:`; the CLI owns that prefix exactly once. Treat a field as blank after trimming Unicode whitespace. An `unfaithful` divergence is trimmed, nonempty, and not `-`; faithful/underdetermined rows require exactly `-`.

- [ ] **Step 5: Implement deterministic templates and exact validators**

`renderLeafTemplate records` emits the fixed leaf-results header and `(unit, leaf_id)` keys with three empty human cells. `renderObjectTemplate records` emits the fixed object-results header, all generated subject fields, and three empty human cells.

Validation compares complete ordered key sequences, not sets:

```haskell
validateLeafJudgments
  :: [UnitRecord]
  -> [LeafJudgment]
  -> Either AuditError [LeafJudgment]

validateObjectJudgments
  :: [UnitRecord]
  -> [ObjectJudgment]
  -> Either AuditError [ObjectJudgment]
```

For object rows, parse and compare every generated field (`subject_id`, unit, type, formal object, prose context, refs) before accepting the three human fields. This prevents a returned packet from silently editing the audit question.

- [ ] **Step 6: Run the focused and full Haskell tests**

Run:

```bash
cabal test lara-test --test-show-details=direct
cabal exec -- runghc scripts/claim-support.hs
```

Expected: all tests pass; the worklist freshness guard remains green.

- [ ] **Step 7: Commit the TSV and validation layer**

```bash
git add src/Lara/BindingAudit/Tsv.hs src/Lara/BindingAudit.hs src/Lara/ClaimSupport.hs test/BindingAuditSpec.hs test/Spec.hs lara.cabal
git commit -m "feat(audit): validate sealed binding judgments"
```

---

### Task 3: Build and structurally validate the status-free review packet

**Files:**
- Modify: `src/Lara/BindingAudit.hs`
- Create: `scripts/binding-audit.hs`
- Modify: `test/BindingAuditSpec.hs`

**Interfaces:**
- Produces: `AuditIO`, `productionAuditIO`, `validatePacketDestination`, `prepareAuditPacket`, `prepareAuditPacketWith`, and `validateAuditPacket`.
- `AuditIO` reads and writes strict `ByteString`s, atomically writes strict summary bytes through `atomicWriteWith`/`Data.ByteString.hPut`, discovers the object format, and hashes exact input bytes. Production wrappers use fixed repository behavior; tests inject deterministic failures without changing process cwd.
- CLI: `prepare <output-dir>` and `validate <packet-dir>`.
- Consumes: UTF-8 template encoders, `validateWorklist`, and manifest records from Tasks 1–2.

- [ ] **Step 1: Add failing packet IO and status-isolation properties**

Use a temporary parent directory and test:

1. absent destination creates exactly `worklist.tsv`, `results.tsv`, and `object-results.tsv`;
2. packet `worklist.tsv` bytes exactly equal the committed input bytes;
3. a stale committed worklist rejects in `prepare` before destination creation;
4. leaf template has 38 ordered data rows and no status field;
5. object template has four ordered data rows and no status field;
6. an existing empty destination is rejected;
7. an existing nonempty destination is rejected without changing its contents;
8. relative, absolute, `..`, and symlink-parent aliases under the canonical committed `measurements/binding-audit` directory are rejected before creation;
9. a rendering failure creates no destination directory;
10. injected failure while writing each of the three packet files removes the newly created partial destination and preserves the original exception;
11. a completed valid packet passes `validateAuditPacket` and writes nothing;
12. malformed class, justification, divergence, generated field, key, header, document grammar, or order fails validation;
13. stale committed worklist bytes reject in `validate`;
14. validation does not force `urStatuses`.
15. invalid UTF-8 in any packet file rejects before validation and writes nothing.
Prove item 14 with otherwise-valid synthetic records whose status field is a
bottom:

```haskell
statusBlindRecord = syntheticRecord {urStatuses = error "status forced during blind validation"}
```

`validateAuditPacket` must return successfully on completed judgments derived
from `statusBlindRecord`. The no-status checks parse headers and fields; they do
not search source text.

- [ ] **Step 2: Run the focused test and verify failure**

```bash
cabal test lara-test --test-show-details=direct
```

Expected: failure because `prepareAuditPacket` and `validateAuditPacket` are
missing.

- [ ] **Step 3: Implement fail-closed packet creation**

`prepareAuditPacket` is the production wrapper over
`prepareAuditPacketWith productionAuditIO`. The lower-level function:

1. canonicalizes the existing destination parent and the committed
   `measurements/binding-audit` directory, then rejects component-wise
   containment, including symlink aliases;
2. rejects any existing destination;
3. calls `validateWorklist records worklistBytes`, which compares the exact bytes to `encodeUtf8 (bindingAuditTsv records)`;
4. renders all generated text, encodes it once as UTF-8, and fully forces all three strict byte outputs before creation;
5. creates the destination exactly once and writes the three named byte strings through the injected ordinary writer;
6. on any write failure, removes only the newly created destination, ignores
   cleanup failures so they cannot mask the original exception, and rethrows
   that original exception.

The destination is detached human-workflow output rather than a replaceable
generated artifact, so retain atomic no-clobber `createDirectory` semantics
instead of replacing an existing directory with `renameDirectory`.

- [ ] **Step 4: Implement status-free structural validation**

```haskell
validateAuditPacket :: FilePath -> [UnitRecord] -> IO ()
validateAuditPacket packetDir records = do
  submittedWorklist <- readAuditBytes (packetDir </> "worklist.tsv")
  leafInput <- readAuditBytes (packetDir </> "results.tsv")
  objectInput <- readAuditBytes (packetDir </> "object-results.tsv")
  expectedWorklist <- readAuditBytes bindingAuditPath
  _ <- either throwAuditError pure (validateWorklist records expectedWorklist)
  unless (submittedWorklist == expectedWorklist)
    (ioError (userError "packet worklist differs from committed worklist"))
  leafBytes <- either throwAuditError pure (decodeAuditUtf8 LeafResults leafInput)
  objectBytes <- either throwAuditError pure (decodeAuditUtf8 ObjectResults objectInput)
  leafRows <- either throwAuditError pure (parseLeafJudgments leafBytes)
  objectRows <- either throwAuditError pure (parseObjectJudgments objectBytes)
  _ <- either throwAuditError pure (validateLeafJudgments records leafRows)
  _ <- either throwAuditError pure (validateObjectJudgments records objectRows)
  pure ()
```

Calling `validateWorklist` before comparing the submitted packet copy makes
`validate` reject both a tampered packet copy and a stale committed denominator
without forcing `urStatuses`.

The validator may use record subjects and leaf metadata, but no expression in
this call path may pattern-match on or force `urStatuses`. It emits no summary,
count, or verdict and writes no file.

- [ ] **Step 5: Add the thin CLI with exact usage and process-level contracts**

`scripts/binding-audit.hs` parses only:

```text
binding-audit.hs prepare <output-dir>
binding-audit.hs validate <packet-dir>
binding-audit.hs summarize
```

All three modes call `loadRecords` with the same manifest/policy constants as
`claim-support.hs`. `validate` then calls only `validateAuditPacket`. Normalize
all usage, structured audit, IO, and Git failures at dispatch and add
`binding-audit:` exactly once on stderr before exiting nonzero.

Add process-level tests for invalid argv and exact three-line usage, a forbidden
prepare destination, malformed validate input, and one successful mode. Assert
exit code plus stdout/stderr channels; library-only tests are insufficient for
the operator-facing command contract.

- [ ] **Step 6: Smoke-test packet determinism**

```bash
packet_a=$(mktemp -d)/packet
packet_b=$(mktemp -d)/packet
cabal exec -- runghc scripts/binding-audit.hs prepare "$packet_a"
cabal exec -- runghc scripts/binding-audit.hs prepare "$packet_b"
cmp "$packet_a/worklist.tsv" "$packet_b/worklist.tsv"
cmp "$packet_a/results.tsv" "$packet_b/results.tsv"
cmp "$packet_a/object-results.tsv" "$packet_b/object-results.tsv"
```

Expected: all `cmp` commands exit 0; each packet contains exactly three files.
The empty templates intentionally fail `validate`; only completed judgment
files can pass that mode.

- [ ] **Step 7: Commit the packet and validator command**

```bash
git add src/Lara/BindingAudit.hs scripts/binding-audit.hs test/BindingAuditSpec.hs
git commit -m "feat(audit): prepare and validate blinded packets"
```

---

### Task 4: Add post-seal joins and canonical summary generation

**Files:**
- Modify: `src/Lara/BindingAudit.hs`
- Modify: `scripts/binding-audit.hs`
- Modify: `test/BindingAuditSpec.hs`
- Modify: `lara.cabal`

**Interfaces:**
- Produces: `AuditCounts`, `AuditSummary`, `InputIdentity`, `summarizeAudit`, `renderAuditSummary`, `summarizeAuditFiles`.
- CLI: `cabal exec -- runghc scripts/binding-audit.hs summarize`.
- Consumes: exact strict bytes for the committed worklist/result files, validated UTF-8 judgment text, and manifest records from Tasks 1–3.

- [ ] **Step 1: Add failing pure aggregation tests**

Construct synthetic records covering `Attested`, `Observed`,
paper-anchored/unanchored, and every requested status (`Justified`, `Gap`,
`Defeated`, `Contested`). Include all three audit classifications and at least
one legitimate zero-count bucket. Assert:

- total counts sum to the denominator;
- kind splits sum to their exact parent counts;
- paper-anchor counts include only `lfPaperAnchored` rows;
- the justified/unfaithful cell counts only unfaithful rows whose unit's sole requested status is `Justified`;
- all four status keys render in fixed order even when a bucket is zero;
- zero or multiple requested statuses reject with the unit name;
- duplicate unit names reject before map construction can overwrite one;
- object counts are separate and sum to one strict plus three attacks.

Add an exact JSON golden for the synthetic summary.

- [ ] **Step 2: Add failing summarize IO tests**

Use temporary paths through `AuditIO` to assert:

- valid sealed files replace `summary.json` with exact bytes;
- stale worklist or malformed results leave an existing summary byte-unchanged;
- injected atomic-write failure leaves the prior destination and removes temp residue;
- input identity records the repository object-format name and `git hash-object --stdin` digest of the exact worklist, leaf-results, and object-results bytes;
- nonzero and malformed object-format output reject before writing;
- nonzero and malformed hash output for each named input reject before writing and identify that input.
- invalid UTF-8 in any input rejects before identity calculation and leaves the prior summary unchanged;

- [ ] **Step 3: Implement summary types and pure join**

Define:

```haskell
data AuditCounts = AuditCounts
  { countAudited :: Int
  , countFaithful :: Int
  , countUnfaithful :: Int
  , countUnderdetermined :: Int
  }

data AuditSummary = AuditSummary
  { summaryLeaves :: AuditCounts
  , summaryByKind :: [(LeafKind, AuditCounts)]
  , summaryPaperAnchored :: AuditCounts
  , summaryByStatus :: [(Status, AuditCounts)]
  , summaryObjects :: [(AuditSubjectType, AuditCounts)]
  }
```

`summarizeAudit` first runs the worklist and both judgment validators, then builds a unit-name map from records. Reject duplicate unit names and any unit whose `urStatuses` is not a singleton. Fold in manifest/result order and render keys in a fixed order: totals, `attested`, `observed`, paper-anchored, `justified`, `gap`, `defeated`, `contested`, strict-step, typed-attack. Render every fixed bucket even when all its counts are zero.

- [ ] **Step 4: Render canonical summary JSON**

Use `Lara.ExpectedJson.JValue` and `renderJson`; do not add `aeson` to the library. Include:

```json
{
  "schema": "lara-binding-audit@0.1",
  "corpus": {
    "freeze": "m5-freeze-v2",
    "units": 60
  },
  "inputs": {
    "object-format": "sha1",
    "worklist": "<git hash-object digest>",
    "leaf-results": "<git hash-object digest>",
    "object-results": "<git hash-object digest>"
  },
  "leaves": {},
  "by-kind": {},
  "paper-anchored": {},
  "by-requested-status": {},
  "objects": {}
}
```

The example digest values are illustrative only. Production obtains the object format from `git rev-parse --show-object-format` and feeds each strict input `ByteString` directly to `git hash-object --stdin`; it never hashes a decoded/re-encoded `String`. Tests compare values produced by the same Git commands, not hard-coded SHA-1.

- [ ] **Step 5: Implement `summarize` IO and atomic replacement**

Use fixed committed paths exported once from `Lara.BindingAudit`:

```haskell
leafResultsPath = "measurements/binding-audit/results.tsv"
objectResultsPath = "measurements/binding-audit/object-results.tsv"
summaryPath = "measurements/binding-audit/summary.json"
```

`summarizeAuditFiles` wraps `summarizeAuditFilesWith productionAuditIO`.
The injected implementation:

1. reads the worklist and both sealed result files as strict `ByteString`s;
2. validates the exact worklist bytes against
   `encodeUtf8 (bindingAuditTsv records)`;
3. decodes result text with `decodeUtf8'`, rejecting invalid UTF-8 before any
   identity or write;
4. validates judgments, then hashes the original raw byte strings;
5. fully forces `encodeUtf8 (renderAuditSummary summary)`; and
6. calls the injected atomic byte writer only after every prior step succeeds.

Production implements the final write with
`atomicWriteWith summaryPath (Data.ByteString.hPut summaryBytes)`. Add
`bytestring` and `process` to the library `build-depends` in `lara.cabal`; do
not thicken the script with encoding, hashing, or identity logic.

Every script failure is normalized and prefixed exactly once at the CLI
boundary. No failure path writes the worklist or either human judgment file.

- [ ] **Step 6: Run tests with synthetic sealed data**

Run:

```bash
cabal build all
cabal test all --test-show-details=direct
```

Expected: all tests pass without requiring real `results.tsv` or `object-results.tsv` in the repository. The committed-summary freshness test is deliberately deferred until Task 6, after the human handoff.

- [ ] **Step 7: Commit the analyzer**

```bash
git add src/Lara/BindingAudit.hs scripts/binding-audit.hs test/BindingAuditSpec.hs
git commit -m "feat(audit): summarize sealed binding results"
```

---

### Task 5: Execute and seal the second-author audit

**Files:**
- Create after handoff: `measurements/binding-audit/results.tsv`
- Create after handoff: `measurements/binding-audit/object-results.tsv`
- Verify unchanged: `measurements/binding-audit/worklist.tsv`

**Interfaces:**
- Consumes: detached packet from Task 3 and the human protocol in the approved design.
- Produces: the two immutable human-input files required by Task 4 `summarize`.

- [ ] **Step 1: Build the packet from the reviewed tooling commit**

From a clean tree, run:

```bash
packet_parent=$(mktemp -d)
packet="$packet_parent/binding-audit-review"
cabal exec -- runghc scripts/binding-audit.hs prepare "$packet"
```

Record the tooling commit and the three packet file hashes in the handoff message. Do not include `expected.json`, claim-support aggregate outputs, or any status-bearing file.

- [ ] **Step 2: Give the second author the exact audit protocol**

The auditor completes all 38 leaf rows and four object rows. They compare formal object to prose/source rationale, not scientific truth. They may use `corpus-units/LOWERING.md`, cited M0 annotations, and header lowering rationale, but must not inspect checker verdicts, `expected.json`, aggregate status outputs, or expected-verdict footers before sealing. The Family-10 spelling `50` versus `50.0` is documented canonicalization, not by itself an unfaithful binding.

- [ ] **Step 3: Receive the completed packet without normalization**

Copy the returned `results.tsv` and `object-results.tsv` bytes into `measurements/binding-audit/`. Do not sort, reformat, rewrite justifications, or add status columns.

- [ ] **Step 4: Run status-free structural validation**

Inspect the headers and confirm neither file contains a verdict/status field.
Compare the generated columns against the packet copies; only the three human
columns may differ:

```bash
cmp <(cut -f1-2 "$packet/results.tsv") \
    <(cut -f1-2 measurements/binding-audit/results.tsv)
cmp <(cut -f1-6 "$packet/object-results.tsv") \
    <(cut -f1-6 measurements/binding-audit/object-results.tsv)
cabal exec -- runghc scripts/binding-audit.hs validate measurements/binding-audit
```

Expected: all commands exit 0; validation accepts exactly 38 leaf rows and four
object rows, emits no status or count, writes no file, and does not create
`summary.json`. If validation fails, return only the contextual structural error
to the auditor; never edit their classification or justification.

- [ ] **Step 5: Commit the structurally valid judgments before any status join**

```bash
git add measurements/binding-audit/results.tsv measurements/binding-audit/object-results.tsv
git commit -m "docs(audit): record blinded binding judgments"
```

The commit message and body must name the auditor and audit date supplied with
the returned packet. Do not include generated summary bytes in this sealing
commit; that separation proves the judgments were complete and structurally
valid before the status join.

---

### Task 6: Commit the deterministic summary, method record, and freshness guard

**Files:**
- Create: `measurements/binding-audit/summary.json`
- Create: `measurements/binding-audit/README.md`
- Modify: `test/BindingAuditSpec.hs`
- Modify: `docs/m5-freeze-checklist.md:103-113`

**Interfaces:**
- Consumes: sealed human commits from Task 5.
- Produces: paper-facing generated counts and a permanent reproduction contract.

- [ ] **Step 1: Add the failing committed-summary freshness property**

Register:

```haskell
, ("binding-audit: committed summary is fresh", quickCheckResult prop_bindingAuditSummaryFresh)
```

The property loads records and exact committed result bytes, validates them, recomputes input identities and `summary.json`, then compares exact bytes with `measurements/binding-audit/summary.json`. Before generation, expected failure is a missing or stale summary.

- [ ] **Step 2: Generate the summary and make the freshness test pass**

Run:

```bash
cabal exec -- runghc scripts/binding-audit.hs summarize
cabal test lara-test --test-show-details=direct
```

Expected: the freshness property passes; headline leaf counts sum to 38; strict object count sums to 1; attack object count sums to 3; kind split denominators remain 20/18; paper-anchored denominator remains 15.

- [ ] **Step 3: Write the method README from observed audit metadata**

Create `measurements/binding-audit/README.md` with:

- auditor name and ISO audit date from the returned packet;
- tooling commit and sealed-judgment commit;
- exact three classification definitions;
- the blinding boundary and excluded files;
- permitted reference material;
- the sealing rule and correction policy;
- `prepare`, `validate`, and `summarize` reproduction commands;
- a statement that scientific truth and experimental quality were out of scope;
- links to `worklist.tsv`, `results.tsv`, `object-results.tsv`, and `summary.json`.

Do not copy headline counts into prose. Point readers to named `summary.json` fields so there is one numeric source.

- [ ] **Step 4: Update the freeze checklist without changing frozen anchors**

Document that `measurements/binding-audit/{worklist.tsv,results.tsv,object-results.tsv,summary.json,README.md}` are committed audit artifacts outside `measurements/frozen/`; `claim-support.hs` owns only the worklist; `binding-audit.hs summarize` owns the summary; the human result files are never generated or rewritten.

- [ ] **Step 5: Prove summary idempotence**

Run:

```bash
first=$(shasum -a 256 measurements/binding-audit/summary.json)
cabal exec -- runghc scripts/binding-audit.hs summarize
second=$(shasum -a 256 measurements/binding-audit/summary.json)
test "$first" = "$second"
```

Expected: exit 0 and identical hashes.

- [ ] **Step 6: Commit generated reporting artifacts**

```bash
git add measurements/binding-audit/summary.json measurements/binding-audit/README.md test/BindingAuditSpec.hs docs/m5-freeze-checklist.md
git commit -m "feat(audit): report binding faithfulness results"
```

---

### Task 7: Report the audit in the paper

**Files:**
- Modify external: `/Users/yfhe/overleaf/ara/lara/src/evaluation.tex:11-15,170-192,235-243`
- Modify external: `/Users/yfhe/overleaf/ara/lara/src/language.tex:34-45`

**Interfaces:**
- Consumes: exact fields from committed `measurements/binding-audit/summary.json` and method facts from `README.md`.
- Produces: paper claims cross-referenced to the untrusted-binding boundary.

- [ ] **Step 1: Extract the exact paper-facing values from `summary.json`**

Record, without recomputation:

- total leaf denominator and three classifications;
- `attested` and `observed` splits;
- paper-anchored subset split;
- unfaithful-under-justified count;
- strict-step classification;
- typed-attack classification counts.

Every number inserted into TeX must correspond to one named JSON path.

- [ ] **Step 2: Update the evaluation framing and claim-support paragraph**

At `evaluation.tex:11-15`, replace the statement that no result below depends on the unchecked binding with the completed-audit boundary: the checker still does not certify binding faithfulness, while the evaluation now reports an exhaustive second-author audit.

After the 38-leaf denominator at `evaluation.tex:170-192`, add one compact paragraph containing the exact total, class split, kind split, paper-anchored split, and justified/unfaithful result. Report nonzero unfaithful cases plainly; do not soften them or rewrite corpus units.

At the Limitations paragraph, replace “human review pending” only for the binding audit. Preserve the separate single-annotator limitation for inference-scheme/CQ/strict-certifier corpus annotation.

- [ ] **Step 3: Cross-reference the audit from `sec:leaves`**

At `language.tex:34-45`, retain the statement that the binding is untrusted and never a checker obligation, then add an `\autoref{sec:evaluation}` reference to the exhaustive audit. Do not imply that a faithful classification is a theorem or certificate.

- [ ] **Step 4: Compile and inspect the paper**

Run from `/Users/yfhe/overleaf/ara/lara`:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Expected: exit 0, no new undefined references, and no new overfull boxes in edited paragraphs. Use `pdftotext build/main.pdf -` to confirm every inserted headline number appears in the PDF and matches `summary.json`.

- [ ] **Step 5: Commit the paper update separately**

```bash
git add src/evaluation.tex src/language.tex
git commit -m "docs: report blinded binding audit"
```

Record this external paper commit in the LARA PR body and issue #87 completion comment.

---

### Task 8: Run the full release gate and close the audit tracker

**Files:**
- Modify only if required by the qualifying experiment result: `ara/trace/`, `ara/staging/`, and current `ara/logic/` entries under the updated `CLAUDE.md` policy.
- No source or artifact changes are planned in this task.

**Interfaces:**
- Consumes: completed repository and paper commits.
- Produces: end-to-end verification evidence and issue #87 closure.

- [ ] **Step 1: Run build, tests, packet, and summary determinism**

```bash
cabal build all
cabal test all --test-show-details=direct
cabal exec -- runghc scripts/claim-support.hs
packet_a=$(mktemp -d)/packet
packet_b=$(mktemp -d)/packet
cabal exec -- runghc scripts/binding-audit.hs prepare "$packet_a"
cabal exec -- runghc scripts/binding-audit.hs prepare "$packet_b"
cmp "$packet_a/worklist.tsv" "$packet_b/worklist.tsv"
cmp "$packet_a/results.tsv" "$packet_b/results.tsv"
cmp "$packet_a/object-results.tsv" "$packet_b/object-results.tsv"
cabal exec -- runghc scripts/binding-audit.hs validate measurements/binding-audit
summary_before=$(shasum -a 256 measurements/binding-audit/summary.json)
cabal exec -- runghc scripts/binding-audit.hs summarize
summary_after=$(shasum -a 256 measurements/binding-audit/summary.json)
test "$summary_before" = "$summary_after"
```

Expected: all commands exit 0; committed judgments pass status-free validation,
and worklist, packets, and summary are byte-deterministic.

- [ ] **Step 2: Run Lean, axiom, differential, admission, replay, and freeze gates**

```bash
(cd lean && lake build)
(cd lean && lake env lean AxCheck.lean) | scripts/check-axioms.sh
bash scripts/differential.sh
bash scripts/admission-differential.sh
bash scripts/test-replay-tamper.sh
python3 scripts/test_freeze_bundle.py -v
```

Expected: Lean is sorry-free within the standard axiom trio; all differential/admission cases agree; replay tampering is rejected; freeze-bundle tests pass.

- [ ] **Step 3: Prove protected inputs and frozen artifacts did not move**

Compare the branch against its merge base and require empty diffs for:

```text
corpus-units/
fixtures/
measurements/frozen/
lean/
src/Lara/Check.hs
src/Lara/Wire.hs
src/Lara/Replay.hs
bundles/
```

Any nonempty protected diff is a stop condition, not a reason to refresh the freeze.

- [ ] **Step 4: Rebuild and verify the external paper**

```bash
cd /Users/yfhe/overleaf/ara/lara
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Verify each reported audit number against the committed `summary.json` paths recorded in Task 7.

- [ ] **Step 5: Run the qualifying experiment ARA epilogue**

Because this work records a completed audit experiment and paper-facing findings, run `/research-manager` once after all judgments and counts are final. Record the audit execution/result and paper commit; do not create ARA entries for routine review fixes or PR mechanics.

- [ ] **Step 6: Commit any qualifying ARA update**

If `/research-manager` produced an experiment/result update, commit only those generated ARA files:

```bash
git add ara/
git commit -m "docs(ara): record binding audit results"
```

If it correctly produces no changes, do not create an empty commit.

- [ ] **Step 7: Open the PR and close issue #87 only when every checkbox is factual**

The PR body must state:

- 38/38 leaf judgments and 4/4 object judgments complete;
- exact class totals and justified/unfaithful count from `summary.json`;
- audit was sealed before status join;
- worklist and protected frozen inputs are unchanged;
- repository and paper commit IDs;
- full gate outputs.

Reopen issue #87 before linking the PR if it remains auto-closed from Step 0. Close it only after `results.tsv`, `object-results.tsv`, `summary.json`, `README.md`, paper text, and all gates are present.


## NOT in scope

- Publishing `binding-audit.hs` as a standalone binary or package: it is a
  repository maintenance command invoked through Cabal.
- Repairing any unfaithful or underdetermined corpus binding: the frozen audit
  records findings; repairs require a separately versioned follow-up.
- Accepting CRLF or optional-final-newline TSV variants: sealed audit inputs use
  one canonical LF byte grammar.
- Caching, streaming, batching Git hashes, or indexing 60 records: no measured
  performance problem exists at the fixed corpus scale.
- Parallel implementation across Tasks 1–4: they share `ClaimSupport`,
  `BindingAudit`, Cabal registration, and one test module, so sequencing is
  safer than worktree merge conflict.

## What already exists

| Existing code/flow | Reuse in this plan |
| --- | --- |
| `Lara.ClaimSupport.computeUnit` and `bindingAuditTsv` | Keep the checked 38-row denominator and exact manifest order; extend the same projection instead of building a second loader. |
| `Lara.ClaimSupport.Load.loadRecords` | Reuse the single manifest/policy/checker path in every CLI mode. |
| `Lara.ExpectedJson.JValue`, `renderJson`, and `renderAttack` | Reuse canonical JSON and attack spelling; add no `aeson` or second attack renderer. |
| `Lara.AtomicWrite.atomicWriteFile` | Reuse same-directory summary replacement and its failure-preserves-old-file contract. |
| `ClaimSupportSpec` worklist freshness and atomic-write properties | Preserve byte guards; add runtime freshness and audit-orchestration coverage rather than duplicating primitive tests. |
| Existing CI Haskell, Lean, differential, admission, replay/tamper, freeze, and axiom jobs | Keep the release boundary; new focused tests make the audit contracts part of `cabal test all`. |

## Failure Modes

| Code path | Realistic failure | Test | Handling / operator-visible result |
| --- | --- | --- | --- |
| strict/attack subject derivation | surface and checked core drift, or raw endpoints alias by equal terms | synthetic parity and distinct-`ArgId` properties | contextual hard error before packet rendering |
| TSV/refs parsing | editor emits CRLF, blank row, malformed escape, reserved ref, or whitespace-only judgment | strict document and typed refs matrix | row/key error; judgment bytes never rewritten |
| worklist identity | committed denominator is stale relative to records | mismatch case in all three modes | fail before packet creation or summary replacement |
| packet path validation | relative or symlink alias points under committed audit directory | canonical containment matrix | reject before any directory creation |
| packet creation | disk/permission failure on file 1, 2, or 3 | injected failure at each write | remove only newly created partial destination; preserve original exception |
| blind validation | future code accidentally forces statuses | `urStatuses = error` record | test fails; successful command emits no status/count and writes nothing |
| status join | duplicate unit or zero/multiple requested statuses | complete synthetic map/status matrix | contextual reject before aggregation |
| Git identity | Git exits nonzero or returns malformed format/digest | injected command-result matrix | named input error before atomic writer |
| summary replacement | rendering or temporary write fails | forced-render and injected atomic-write cases | prior complete summary remains byte-identical; no temp residue |
| CLI dispatch | invalid argv or mixed prefix ownership | process-level usage/error tests | exact stderr, nonzero exit, one `binding-audit:` prefix |
| paper reporting | TeX number is copied from the wrong field | JSON-path extraction record plus PDF text check | compile/reconciliation gate blocks paper commit |

No failure mode is silent, untested, and unhandled after the accepted review
changes.

## Worktree Parallelization

Sequential implementation, no safe parallelization opportunity before the
human handoff.

| Step | Modules touched | Depends on |
| --- | --- | --- |
| Subject projection | `Lara.ClaimSupport`, audit types, printers, tests | — |
| TSV and validators | audit codec/analyzer, `Lara.ClaimSupport`, tests | Subject projection |
| Packet and CLI | audit analyzer, script, tests | TSV and validators |
| Summary analyzer | audit analyzer, Cabal, script, tests | Packet and CLI |
| Human seal | audit measurements | Reviewed tooling commit and second author |
| Summary/method | audit measurements, docs, tests | Human seal |
| Paper | external TeX checkout | Committed summary/method |
| Release gate | repository, external paper, optional ARA epilogue | All prior steps |

Lane A is the entire repository tooling sequence through the human seal. The
external paper update begins only after canonical summary fields exist. Task 8
then verifies both repositories. Splitting earlier worktrees would create
conflicts in `Lara.BindingAudit` and `BindingAuditSpec` without shortening the
dependency chain.

## Deferred-work disposition

No new deferred follow-up is warranted. Every review finding is required for
this branch's evidence, determinism, or failure contract and is integrated
below; no other tracked follow-up bears on issue #87. (This section originally
named `TODOS.md`, the in-repo backlog file retired on 2026-08-19 in favour of
GitHub issues.)

## Implementation Tasks

Synthesized from this engineering review. These harden the existing Tasks 1–4;
they do not expand the audit denominator or paper scope.

- [ ] **T1 (P1, human: ~10 min / CC: ~2 min)** — Cabal — add the library `bytestring` and `process` dependencies in Task 4.
  - Surfaced by: Architecture Issue 1 and Exact-Byte Issue 14.
  - Files: `lara.cabal`.
  - Verify: `cabal build all`.
- [ ] **T2 (P1, human: ~45 min / CC: ~8 min)** — Packet boundary — canonicalize destination parents and reject relative, absolute, traversal, and symlink aliases under committed audit storage.
  - Surfaced by: Architecture Issue 2.
  - Files: `src/Lara/BindingAudit.hs`, `test/BindingAuditSpec.hs`.
  - Verify: focused canonical-containment properties.
- [ ] **T3 (P1, human: ~45 min / CC: ~8 min)** — Subject projection — require strict surface/core support-term parity before rendering.
  - Surfaced by: Architecture Issue 3 and the existing leaf parity guard.
  - Files: `src/Lara/ClaimSupport.hs`, `test/ClaimSupportSpec.hs`.
  - Verify: synthetic same-ID/different-term rejection property.
- [ ] **T4 (P2, human: ~25 min / CC: ~5 min)** — Documentation — add and maintain the audit state/data-flow diagram.
  - Surfaced by: Architecture Issue 4.
  - Files: this plan, `src/Lara/BindingAudit.hs`.
  - Verify: review diagram against the three mode implementations.
- [ ] **T5 (P1, human: ~45 min / CC: ~8 min)** — TSV refs — extract one typed refs cell renderer/parser and reuse it in both schemas.
  - Surfaced by: Code Quality Issue 5.
  - Files: `src/Lara/BindingAudit/Tsv.hs`, `src/Lara/ClaimSupport.hs`, `test/BindingAuditSpec.hs`.
  - Verify: refs round-trip/reserved-value properties and unchanged worklist bytes.
- [ ] **T6 (P1, human: ~1 h / CC: ~10 min)** — TSV documents — enforce the canonical LF/final-newline grammar and trimmed human fields.
  - Surfaced by: Code Quality Issue 6.
  - Files: `src/Lara/BindingAudit/Tsv.hs`, `src/Lara/BindingAudit.hs`, `test/BindingAuditSpec.hs`.
  - Verify: line-ending, blank-row, escape, whitespace, and sentinel matrix.
- [ ] **T7 (P1, human: ~1.5 h / CC: ~15 min)** — IO orchestration — add `AuditIO` and fixed production wrappers.
  - Surfaced by: Code Quality Issue 7.
  - Files: `src/Lara/BindingAudit.hs`, `test/BindingAuditSpec.hs`.
  - Verify: temp-path orchestration and injected writer/identity failures without cwd mutation.
- [ ] **T8 (P2, human: ~20 min / CC: ~4 min)** — Diagnostics — make the CLI the sole `binding-audit:` prefix owner.
  - Surfaced by: Code Quality Issue 8.
  - Files: `src/Lara/BindingAudit.hs`, `scripts/binding-audit.hs`, `test/BindingAuditSpec.hs`.
  - Verify: exact process stderr contains one prefix.
- [ ] **T9 (P1, human: ~1 h / CC: ~10 min)** — Worklist identity — validate exact renderer equality in prepare, validate, and summarize.
  - Surfaced by: Test Issue 9 and approved-design mismatch rejection.
  - Files: `src/Lara/BindingAudit.hs`, `test/BindingAuditSpec.hs`.
  - Verify: stale-worklist rejection in all modes before output.
- [ ] **T10 (P1, human: ~1 h / CC: ~10 min)** — Packet transaction — inject write failures at each of the three packet files.
  - Surfaced by: Test Issue 10.
  - Files: `src/Lara/BindingAudit.hs`, `test/BindingAuditSpec.hs`.
  - Verify: no destination remains and the original exception survives in all three cases.
- [ ] **T11 (P1, human: ~1.5 h / CC: ~15 min)** — CLI — add process-level dispatch, channel, and exit-code tests.
  - Surfaced by: Test Issue 11.
  - Files: `scripts/binding-audit.hs`, `test/BindingAuditSpec.hs`.
  - Verify: invalid usage, forbidden destination, malformed validation, and success cases.
- [ ] **T12 (P1, human: ~45 min / CC: ~8 min)** — Aggregation — cover all four statuses, zero buckets, fixed ordering, and duplicate units.
  - Surfaced by: Test Issue 12.
  - Files: `src/Lara/BindingAudit.hs`, `test/BindingAuditSpec.hs`.
  - Verify: pure aggregation matrix and exact JSON golden.
- [ ] **T13 (P1, human: ~1 h / CC: ~10 min)** — Input identity — reject nonzero and malformed Git results for every identity operation.
  - Surfaced by: Test Issue 13.
  - Files: `src/Lara/BindingAudit.hs`, `test/BindingAuditSpec.hs`.
  - Verify: named errors and unchanged prior summary for every injected failure.
- [ ] **T14 (P1, human: ~1.5 h / CC: ~15 min)** — Exact-byte IO — read, copy, hash, and atomically write strict bytes with explicit UTF-8 validation.
  - Surfaced by: Exact-Byte Issue 14 and the sealed-input identity contract.
  - Files: `src/Lara/BindingAudit.hs`, `lara.cabal`, `test/BindingAuditSpec.hs`.
  - Verify: invalid-UTF-8 rejection, raw-byte Git hash equality, byte-identical packet copy, and atomic binary summary replacement.

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | Not required for this evidence-tooling plan |
| Codex Review | `/codex review` | Independent 2nd opinion | 0 | UNAVAILABLE | Codex and the read-only fallback both timed out; no outside finding was incorporated |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 2 | CLEAR | Latest record: 14 issues found, 14 decisions folded, 0 critical gaps |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | No UI scope |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | Not required |

- **VERDICT:** ENG CLEARED — ready to implement through Task 4, then stop at the human handoff.

NO UNRESOLVED DECISIONS