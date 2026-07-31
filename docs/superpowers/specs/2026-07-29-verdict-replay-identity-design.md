# Verdict-Carried Replay Identity

Status: approved on 2026-07-29.

## Goal

Every checker verdict, accepted or rejected, carries the frozen replay identity
from `docs/spec.md` §2.1:

```text
(lara-core@0.1,
 policy id @ version,
 [backend@version*],
 {theory digests},
 artifact digest)
```

The Haskell and Lean drivers must emit this identity byte-for-byte identically.
The identity must also travel through the committed `.sexp` differential
anchors, worked-example JSON reports, and replay bundles.

## Non-goals

- Do not add presentation metadata to the semantic `Unit` type.
- Do not change the `.lara` grammar. A `PolicyId` such as `empirical-v1` is the
  complete versioned policy atom and is carried verbatim; no suffix is parsed or
  inferred.
- Do not recompute artifact or policy digests in the checker. A `.lara` run gets
  its identity from the parsed program and policy. A raw `.sexp` run treats its
  validated envelope as trusted run metadata. Replay bundles continue to verify
  copied inputs separately through `manifest.json`.
- Do not add compatibility support for identity-free `.sexp` files or verdicts.

## Architecture

### Domain types

Add a small `Lara.Replay` module containing report-boundary metadata, separate
from the source and checker AST:

```haskell
data CoreVersion = LaraCoreV01

data ReplayId = ReplayId
  { replayCore       :: CoreVersion
  , replayPolicy     :: PolicyId
  , replayBackends   :: [(BackendId, String)]
  , replayTheories   :: [TheoryDigest]
  , replayArtifact   :: Digest
  }

data CheckInput = CheckInput
  { checkReplayId :: ReplayId
  , checkUnit     :: Unit
  }
```

Constructors are mediated by validating smart constructors. The module exposes
selectors and source construction, but callers cannot create an incoherent
`CheckInput` accidentally.

`ReplayId.replayTheories` is sorted lexicographically by Unicode scalar value
and duplicate-free, implementing the specification's theory-digest set with an
ordering that Haskell and Lean define identically.
Backend selections remain in the source program's declared order because the specification models
them as a list.

### Checker result type

Replace the current identity-free sum with a common wrapper:

```haskell
data Verdict = Verdict ReplayId Outcome

data Outcome
  = Accept
      { verdictLabels   :: [(Int, Label)]
      , verdictEdges    :: [(Int, Int)]
      , verdictStatuses :: [(Prop, Status)]
      }
  | Reject Rejection
```

The only exported whole-run entry point becomes:

```haskell
runCheck :: CheckInput -> Verdict
```

This shape makes it impossible for either an accept or reject verdict to omit
identity. The semantic `checkUnit` API remains unchanged.

Lean mirrors these report-boundary structures inside `Lara.Driver`; no theorem
or semantic core type changes.

## Source Construction

For a successfully parsed and elaborated `.lara` program, construct the replay
identity as follows:

| Replay component | Source |
| --- | --- |
| core | closed constant `lara-core@0.1` |
| policy | `programPolicy`, after the existing equality check against `policyId` |
| backends | `programBackends`, preserving declaration order and version atoms |
| theories | keys of `policyTheories`, sorted lexicographically |
| artifact | `programDigest` |

The smart constructor then checks that the elaborated `Unit` carries exactly the
same theory-digest set. This catches accidental use of an unrelated
`TheoryRegistry` during elaboration.

The artifact name is not part of replay identity and is not carried.

## Wire Contract

### Checker input

The CLI and executable-semantics drivers no longer accept a bare top-level
`unit` form. They accept one canonical envelope:

```text
(check-input
  (replay-id
    (core lara-core@0.1)
    (policy empirical-v1)
    (backends (backend nd 1))
    (theories sha256:strict-v1-theory-0)
    (artifact sha256:artifact-0))
  (unit (policy (rules) (contraries) (exceptions))
        (theories (theory sha256:strict-v1-theory-0))))
```

The existing `encodeUnit` and `decodeUnit` functions remain as low-level core
AST codecs and proof/conformance anchors. New `encodeCheckInput`,
`decodeCheckInput`, and `decodeCheckInputFile` functions own executable input.
The old whole-file `decodeUnitFile` API is removed rather than retained as a
shim.

### Verdict

The replay identity is the first common verdict field:

```text
(verdict
  (replay-id
    (core lara-core@0.1)
    (policy empirical-v1)
    (backends (backend nd 1))
    (theories)
    (artifact sha256:artifact-0))
  accept
  (labels (0 in))
  (edges)
  (statuses (status (atom p) justified)))
```

```text
(verdict
  (replay-id
    (core lara-core@0.1)
    (policy empirical-v1)
    (backends (backend nd 1))
    (theories)
    (artifact sha256:artifact-0))
  reject
  R13)
```

Field and section order is fixed. All identity fields use the existing canonical
S-expression atom printer. The Haskell closed `Tag` sum and Lean tag table gain
matching entries for `check-input`, `replay-id`, `core`, `backends`, `backend`,
and `artifact`.

Identity-free verdicts and inputs are malformed `lara-core@0.1` wire values and
fail as R14 codec errors.

## Validation and Errors

Validation is split according to whether a trustworthy replay identity is
available.

### R14 codec failures: no verdict

Both Haskell and Lean reject the input before checker invocation when:

- the envelope or replay-id shape, field count, or field order is wrong;
- the core atom is not exactly `lara-core@0.1`;
- the replay theory list is not sorted or contains duplicates;
- the embedded unit theory table contains duplicate digest keys; or
- the replay theory set differs from the embedded unit theory table.

Duplicate theory keys are rejected because both current registries use
first-match lookup. Without this check, two differently ordered tables could
share one set-valued identity but replay differently.

### R13 checker verdicts: identity is printed

After the envelope establishes a valid identity, `runCheck` returns an
identity-carrying R13 rejection when:

- a selected backend id/version is absent from the closed runtime registry;
- the selected backend list contains a duplicate id/version pair; or
- a submitted certificate uses a backend id/version absent from the selected
  backend list.

The current closed registry contains only `nd@1`; both drivers derive this fact
from their existing ND backend registration rather than from duplicated string
literals.

Preflight checks use one fixed order in both implementations: first duplicate
selected pairs, then unknown selected pairs, then the first unselected
certificate in argument/depth-first support-term order. This keeps the R13
result deterministic when malformed inputs violate more than one condition.

All existing checker rejection classes continue to carry the same replay
identity and exit with code 1. Parse, envelope, and elaboration failures still
exit with code 2 and no stdout because no checker verdict exists.

## JSON Report Contract

Each worked-example `expected.json` gains a leading structured member:

```json
{
  "replay-id": {
    "core": "lara-core@0.1",
    "policy": "empirical-v1",
    "backends": ["nd@1"],
    "theories": [],
    "artifact": "sha256:artifact-0"
  },
  "verdict-class": "accept",
  "located-diagnostic": {}
}
```

`expectedJson` takes `CheckInput`, not `Unit`, and obtains the verdict through
`runCheck`. Existing `UnitError` diagnostics remain unchanged. For a replay
preflight R13, the JSON uses stage `backend`: duplicate or unknown selections
locate the policy, while an unselected certificate locates its outer argument.
The diagnostic also names the offending `backend@version` and one of the closed
reason atoms `duplicate-selection`, `unknown-selection`, or
`certificate-backend-not-selected`.

## Fixtures and Bundles

- Worked-example inputs derive `CheckInput` from their parsed `Program`, parsed
  `Policy`, and elaborated `Unit`. Their `.core.sexp`, `expected.json`, and pinned
  verdict strings are regenerated together.
- Synthetic checker fixtures receive explicit fixture replay identities in the
  corpus generator. Metadata is part of each fixture's provenance, not inferred
  from checker state.
- Hand-authored inline test units use one shared validating test constructor.
- `bundles/walking-skeleton/emitted.core.sexp` is regenerated through the same
  source constructor. `verdict.txt` therefore carries replay identity.
- The bundle is refrozen after the checker change so `manifest.json` records the
  new checker-source revision and artifact hashes.

The replay script continues to reject manifest or artifact tampering before
checker invocation, then compares the newly produced verdict against
`verdict.txt` byte-for-byte. The verdict comparison now also detects replay
identity drift.

## Test Strategy

### Haskell unit and property tests

- Golden and round-trip tests for `ReplayId`, `CheckInput`, and both verdict
  outcomes.
- Malformed matrices for missing/extra/reordered identity fields, unsupported
  core versions, malformed identity atoms, unsorted or duplicate theory lists,
  duplicate unit theory keys, and theory-set mismatch.
- R13 tests for unknown and duplicate selected backends and certificates whose
  backend/version is not selected.
- Source-construction tests proving that the policy atom is preserved verbatim,
  backend order is preserved, theories are sorted, and the program artifact
  digest is copied.
- A regression asserting that every accepted and rejected `Verdict` encoding
  contains exactly one replay identity.

### End-to-end tests

- `.lara` and its generated `.core.sexp` produce byte-identical verdicts.
- Every committed differential fixture is canonical after re-encoding its full
  `CheckInput`.
- Haskell and Lean drivers agree byte-for-byte on every accept and reject anchor.
- Worked-example `expected.json` freshness remains byte-exact.
- Bundle replay and existing tamper cases pass after refreezing.

### Required verification

Run, in order:

1. targeted wire, driver, CLI, expected-JSON, and differential tests;
2. `cabal test`;
3. `cd lean && lake build`;
4. `cd lean && lake env lean AxCheck.lean` and confirm no `sorryAx`;
5. `bash scripts/differential.sh`;
6. bundle freezer unit tests, replay, and tamper tests.

## Acceptance Criteria

- Every Haskell and Lean checker verdict contains the five replay-id components.
- Accept and every checker rejection class carry identity by construction.
- Bare Unit files and identity-free verdicts are rejected as obsolete wire
  forms.
- The `.lara` policy atom is copied exactly; no policy-version suffix heuristic
  exists.
- Duplicate theory keys cannot reach either backend registry.
- Unknown or duplicate selected backends and unselected certificate backends
  produce identity-carrying R13 verdicts.
- The semantic `Unit`, checker judgments, and Lean theorem statements are
  unchanged.
- All regenerated fixtures, goldens, JSON reports, and replay-bundle artifacts
  are byte-exact and fresh.
- Haskell/Lean differential, Haskell suite, Lean build/AxCheck, and bundle replay
  gates pass.
