# Verdict-Carried Replay Identity Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make every Haskell and Lean checker verdict carry the exact frozen replay identity required by spec §2.1, including rejects and raw `.sexp` runs.

**Architecture:** Keep the semantic `Unit` unchanged. Add a validated `CheckInput = ReplayId + Unit` report envelope, make `Verdict = ReplayId + Outcome`, derive source identities from `Program` and `Policy`, and mirror the envelope plus validation in the Lean executable driver. Regenerate every wire/report anchor and refreeze the walking-skeleton bundle after both drivers agree.

**Tech Stack:** Haskell/GHC 2021, Cabal, QuickCheck, Lean 4.32.0, canonical S-expressions, hand-rolled canonical JSON, Python 3 replay freezer, Bash differential/replay gates.

## Global Constraints

- Preserve `Lara.AST.Unit`, `Lara.Check.checkUnit`, all checker judgments, and all Lean theorem statements unchanged.
- Use a clean wire cutover: no identity-free `.sexp` or verdict compatibility path, alias, or deprecated decoder.
- Carry `programPolicy` verbatim as the complete versioned policy atom; never split suffixes such as `-v1`.
- Carry `programBackends` in declared order. Canonicalize theory digests as a Unicode-scalar-lexicographically sorted, duplicate-free set using the same explicit comparator in both drivers.
- Reject duplicate unit theory keys and replay/unit theory mismatch as R14 before checker invocation.
- After identity is established, map duplicate selected backends, unknown selected backends, and unselected certificate backends to an identity-carrying R13 verdict.
- Use the same preflight precedence in both drivers: duplicate selection, unknown selection, then first unselected certificate in argument/depth-first order.
- Derive the only supported backend from the existing ND registration (`nd@1`), not a second free string constant.
- Preserve exit codes: accept `0`; checker reject, including replay preflight R13, `1`; parse/codec/elaboration failure `2` with no stdout.
- Add no package dependency. Reuse the current S-expression and JSON printers.
- Generated fixtures are changed through their generators. The two original root fixtures may only gain the validated envelope; their embedded Unit bytes stay unchanged.
- Refreeze the walking-skeleton only after every change under `src/`, `app/`, `lean/`, `lara.cabal`, or `cabal.project` is committed. Any later checker-identity edit requires another refreeze.
- Source design: `docs/superpowers/specs/2026-07-29-verdict-replay-identity-design.md`.

## File Structure

**Create**

- `src/Lara/Replay.hs` — replay identity types, source construction, structural coherence, closed-registry preflight.
- `test/ReplaySpec.hs` — identity construction/coherence/preflight properties.
- `test/TestReplay.hs` — one validating identity helper for Unit-focused tests.

**Modify: Haskell implementation**

- `lara.cabal` — expose `Lara.Replay`; register `ReplaySpec` and `TestReplay`.
- `src/Lara/Wire.hs` — check-input/replay-id codecs, closed tags, identity-bearing verdict codec; remove whole-file Unit decoder.
- `src/Lara/Driver.hs` — replace `runUnit` with `runCheck`; wrap all outcomes in replay identity; run replay preflight first.
- `src/Lara/ExpectedJson.hs` — consume `CheckInput`, print replay identity, render replay-preflight R13 diagnostics.
- `app/Main.hs` — decode `CheckInput` on `.sexp`; construct it from parsed `.lara` metadata.

**Modify: Haskell tests and generators**

- `test/Spec.hs`
- `test/WireSpec.hs`
- `test/CheckSpec.hs`
- `test/ElaborateSpec.hs`
- `test/WorkedExamplesSpec.hs`
- `test/DifferentialSpec.hs`
- `test/RuntimeSpec.hs`
- `test/CliSpec.hs`
- `scripts/gen-corpus.hs`
- `scripts/gen-worked-examples.hs`

**Regenerate**

- `fixtures/corpus/*.sexp`
- `fixtures/covered-self-edge.sexp`
- `fixtures/missing-self-edge.sexp`
- `examples/{A,B,E1,E2,E3,R1,R2,R3,S1}/example.core.sexp`
- `examples/{A,B,E1,E2,E3,R1,R2,R3,S1}/expected.json`
- `bundles/walking-skeleton/emitted.core.sexp`

**Modify: Lean executable semantics**

- `lean/Lara/Driver.lean` — mirrored envelope parser, validation, preflight, and verdict replay-id encoder.

**Modify/refreeze: replay bundle**

- `scripts/test-replay-tamper.sh` — prove untrusted artifact-digest drift changes the verdict.
- `bundles/walking-skeleton/verdict.txt`
- `bundles/walking-skeleton/manifest.json`

---

### Task 1: Validated Replay Domain Model

**Files:**
- Create: `src/Lara/Replay.hs`
- Create: `test/ReplaySpec.hs`
- Create: `test/TestReplay.hs`
- Modify: `lara.cabal:20-53,64-88`
- Modify: `test/Spec.hs:25-35,170-192`

**Interfaces:**
- Consumes: `Program`, `Policy`, `Unit`, `SupportTerm`, `Assurance`, `BackendId`, `TheoryDigest`, `Digest`, and the existing ND backend registration.
- Produces:

```haskell
data CoreVersion = LaraCoreV01

data ReplayId -- constructor hidden
replayCore :: ReplayId -> CoreVersion
replayPolicy :: ReplayId -> PolicyId
replayBackends :: ReplayId -> [(BackendId, String)]
replayTheories :: ReplayId -> [TheoryDigest]
replayArtifact :: ReplayId -> Digest

data CheckInput -- constructor hidden
inputReplayId :: CheckInput -> ReplayId
inputUnit :: CheckInput -> Unit

data ReplayError
  = NonCanonicalTheoryDigests [TheoryDigest]
  | DuplicateUnitTheory TheoryDigest
  | TheoryIdentityMismatch [TheoryDigest] [TheoryDigest]
  | ReplayPolicyMismatch PolicyId PolicyId

data ReplayFailure
  = DuplicateSelectedBackend BackendId String
  | UnknownSelectedBackend BackendId String
  | CertificateBackendNotSelected Int ArgId BackendId Int

mkReplayId
  :: CoreVersion
  -> PolicyId
  -> [(BackendId, String)]
  -> [TheoryDigest]
  -> Digest
  -> Either ReplayError ReplayId
mkCheckInput :: ReplayId -> Unit -> Either ReplayError CheckInput
sourceCheckInput :: Program -> Policy -> Unit -> Either ReplayError CheckInput
runtimeReplayFailure :: CheckInput -> Maybe ReplayFailure
replayErrorMessage :: ReplayError -> String
```

- `mkReplayId` requires a canonical sorted/unique theory list but intentionally permits duplicate/unknown backend selections so `runCheck` can emit R13 with identity.
- `sourceCheckInput` sorts policy theory keys before calling `mkReplayId`, checks `programPolicy == policyId`, then calls `mkCheckInput`.
- `runtimeReplayFailure` derives the supported pair from `Lara.Strict.ND.ndBackendId` and uses the fixed duplicate → unknown → unselected-certificate precedence.

- [ ] **Step 1: Register failing replay-model tests**

Add `ReplaySpec` and `TestReplay` to `lara.cabal`, import `replaySpecProps` in `test/Spec.hs`, and append it before the wire properties. Define concrete minimal values in `test/ReplaySpec.hs`:

```haskell
emptyUnit :: Unit
emptyUnit = Unit [] [] [] [] [] [] [] []

sourceProgram :: Program
sourceProgram =
  Program
    { programArtifact = "fixture"
    , programDigest = Digest "sha256:artifact-0"
    , programPolicy = PolicyId "empirical-v1"
    , programBackends = [(BackendId "nd", "1")]
    , programDecls = []
    }

sourcePolicy :: Policy
sourcePolicy =
  Policy
    { policyId = PolicyId "empirical-v1"
    , policyRules = []
    , policyContraries = []
    , policyExceptions = []
    , policyAdmission = []
    , policyTheories =
        [ (TheoryDigest "sha256:z", [])
        , (TheoryDigest "sha256:a", [])
        ]
    }
```

Add properties that assert:

```haskell
fmap
  (\i ->
    ( replayCore (inputReplayId i)
    , replayPolicy (inputReplayId i)
    , replayBackends (inputReplayId i)
    , replayTheories (inputReplayId i)
    , replayArtifact (inputReplayId i)
    ))
  (sourceCheckInput sourceProgram sourcePolicy
    (emptyUnit {unitTheories = policyTheories sourcePolicy}))
  == Right
      ( LaraCoreV01
      , PolicyId "empirical-v1"
      , [(BackendId "nd", "1")]
      , [TheoryDigest "sha256:a", TheoryDigest "sha256:z"]
      , Digest "sha256:artifact-0"
      )
```

Also pin `ReplayPolicyMismatch`, a duplicate unit theory key, a replay/unit theory mismatch, duplicate selected backend preflight, unknown selected backend preflight, and a nested certificate whose `nd@1` pair is absent. For the last case, put the certificate inside a premise of the first outer argument and assert `CertificateBackendNotSelected 0 (ArgId "outer") (BackendId "nd") 1`.

- [ ] **Step 2: Run the suite and confirm the new contract is absent**

Run:

```bash
cabal test
```

Expected: compilation fails because `Lara.Replay`, its exported types, and `replaySpecProps` do not exist.

- [ ] **Step 3: Implement `Lara.Replay` and the shared test helper**

Implement the types and smart constructors with hidden constructors. Replay
atoms remain ordinary wire atoms; `.lara` lexical validation stays in
`Lara.Syntax`, and the replay layer must not narrow the existing Unicode-capable
identifier grammar.

Define one explicit code-point comparator so Haskell and Lean cannot inherit
different library `String` orderings:

```haskell
compareCodePointString a b = compare (map ord a) (map ord b)

compareTheoryDigest (TheoryDigest a) (TheoryDigest b) =
  compareCodePointString a b

canonicalTheories hs =
  and (zipWith (\a b -> compareTheoryDigest a b == LT) hs (drop 1 hs))
```

Use `sortBy compareTheoryDigest` for source construction. The strict adjacent
comparison makes the accepted representation both sorted and duplicate-free.
Preserve the original Unit theory table after validating its keys.

Traverse every `SRule` in outer argument order. At each node, visit its assurance first, then premises left-to-right, then discharges left-to-right. Record the outer argument index/id for the first unselected certificate. `AssuranceNone` and `AssuranceTrusted` contribute no backend pair.

In `test/TestReplay.hs`, expose:

```haskell
testReplayId :: Unit -> ReplayId
testCheckInput :: Unit -> CheckInput
```

Use policy `conformance-v1`, selected backend `nd@1`, sorted `unitTheories` keys, and artifact `sha256:conformance-corpus-v1`. Fail loudly with `error` if a test Unit violates the smart constructor; never bypass the hidden constructors.

- [ ] **Step 4: Run the full Haskell suite**

Run:

```bash
cabal test
```

Expected: all existing tests plus the new replay-model properties pass; no existing runtime behavior changes yet.

- [ ] **Step 5: Commit the replay domain model**

```bash
git add lara.cabal src/Lara/Replay.hs test/ReplaySpec.hs test/TestReplay.hs test/Spec.hs
git commit -m "feat: add validated replay identity model"
```

---

### Task 2: Haskell Wire, Driver, Reports, and Anchors

**Files:**
- Modify: `src/Lara/Wire.hs:3-114,245-309,714-885,895-1026`
- Modify: `src/Lara/Driver.hs:1-80`
- Modify: `src/Lara/ExpectedJson.hs:1-220`
- Modify: `app/Main.hs:1-148`
- Modify: `test/WireSpec.hs:1-22,354-687`
- Modify: `test/CheckSpec.hs:29-99`
- Modify: `test/ElaborateSpec.hs`
- Modify: `test/WorkedExamplesSpec.hs`
- Modify: `test/DifferentialSpec.hs:1-185,240-264`
- Modify: `test/RuntimeSpec.hs:15-165`
- Modify: `test/CliSpec.hs`
- Modify: `scripts/gen-corpus.hs:1-8,26-27,355-390`
- Modify: `scripts/gen-worked-examples.hs:1-104`
- Regenerate all Haskell fixtures/reports listed in File Structure.

**Interfaces:**
- Consumes from Task 1: `ReplayId`, `CheckInput`, `sourceCheckInput`, `mkReplayId`, `mkCheckInput`, `runtimeReplayFailure`, and selectors.
- Produces:

```haskell
data Outcome
  = Accept
      { verdictLabels :: [(Int, Label)]
      , verdictEdges :: [(Int, Int)]
      , verdictStatuses :: [(Prop, Status)]
      }
  | Reject Rejection

data Verdict = Verdict
  { verdictReplayId :: ReplayId
  , verdictOutcome :: Outcome
  }

encodeReplayId :: ReplayId -> SExpr
decodeReplayId :: SExpr -> Either WireError ReplayId
encodeCheckInput :: CheckInput -> SExpr
decodeCheckInput :: SExpr -> Either WireError CheckInput
decodeCheckInputFile :: String -> Either WireError CheckInput
encodeVerdict :: Verdict -> SExpr
decodeVerdict :: SExpr -> Either WireError Verdict
runCheck :: CheckInput -> Verdict
expectedJson :: CheckInput -> String
```

- Removes exported `decodeUnitFile` and `runUnit` with all callers migrated in the same task.
- Retains low-level `encodeUnit :: Unit -> SExpr` and `decodeUnit :: SExpr -> Either WireError Unit`.

- [ ] **Step 1: Write failing check-input and verdict codec tests**

In `test/WireSpec.hs`, keep the existing Unit golden as a low-level `decodeUnit (encodeUnit unit)` test. Replace whole-file Unit assertions with `parseSExpr text >>= decodeUnit` through a small test helper.

Add exact replay and envelope goldens:

```haskell
goldenReplayText =
  "(replay-id (core lara-core@0.1) (policy empirical-v1) "
    ++ "(backends (backend nd 1)) "
    ++ "(theories sha256:theory-a) "
    ++ "(artifact sha256:artifact-0))"

goldenCheckInputText =
  "(check-input " ++ goldenReplayText ++ " " ++ goldenUnitText ++ ")"

goldenAcceptText =
  "(verdict " ++ goldenReplayText
    ++ " accept (labels (0 in)) (edges) "
    ++ "(statuses (status (atom p) justified)))"

goldenRejectText =
  "(verdict " ++ goldenReplayText ++ " reject R13)"
```

Assert parse/decode/encode round trips for `ReplayId`, `CheckInput`, and both verdict outcomes. Add malformed cases for every replay-id field one-short/one-long, wrong section order, `lara-core@0.2`, non-atom field payloads, unsorted theories, duplicate replay theories, duplicate Unit theory keys, and replay/unit theory mismatch. Assert a bare `(unit)` and identity-free `(verdict reject R1)` fail the whole-run decoders.

Update `test/CheckSpec.hs` to wrap its inline Unit strings with `testCheckInput`; add exact assertions that an ordinary R1 and a replay-preflight R13 both encode exactly one section whose head atom is `replay-id`.

- [ ] **Step 2: Run the suite and observe the clean-cutover failures**

Run:

```bash
cabal test
```

Expected: failures identify missing check-input/replay-id tags, codecs, `Outcome`, `runCheck`, and identity-bearing JSON.

- [ ] **Step 3: Implement the Haskell wire codec**

Add closed tags and exact spellings:

```haskell
TCheckInput | TReplayId | TCore | TBackends | TBackend | TArtifact
```

Reuse existing `TPolicy` and `TTheories`. Encode replay fields in the exact design order. Decode by exact arity and order; parse the core atom only as `LaraCoreV01`; call `mkReplayId`, then call `mkCheckInput` after decoding the nested Unit. Convert every `ReplayError` to a located `WireError` under `replay-id`, `check-input`, or `unit theories`.

Replace the verdict sum with the wrapper and outcome. The encoder shape is:

```haskell
encodeLabel :: Label -> SExpr
encodeLabel label =
  SAtom . tagToString $ case label of
    LIn -> TIn
    LOut -> TOut
    LUndec -> TUndec

encodeStatusValue :: Status -> SExpr
encodeStatusValue status =
  SAtom . tagToString $ case status of
    Gap -> TGap
    Justified -> TJustified
    Contested -> TContested
    Defeated -> TDefeated
encodeVerdict (Verdict rid outcome) =
  case outcome of
    Reject r ->
      tagged TVerdict [encodeReplayId rid, SAtom "reject", encodeRejection r]
    Accept labels edges statuses ->
      tagged
        TVerdict
        [ encodeReplayId rid
        , SAtom "accept"
        , tagged TLabels
            [ SList [SAtom (show i), encodeLabel label]
            | (i, label) <- labels
            ]
        , tagged TEdges
            [SList [SAtom (show i), SAtom (show j)] | (i, j) <- edges]
        , tagged TStatuses
            [tagged TStatus [encodeAtom prop, encodeStatusValue status]
            | (prop, status) <- statuses
            ]
        ]
```

The decoder must require exactly one replay-id before `accept` or `reject` and reject all old forms.

- [ ] **Step 4: Cut the Haskell driver and CLI over to `CheckInput`**

In `Lara.Driver`, implement:

```haskell
runCheck input =
  let rid = inputReplayId input
      unit = inputUnit input
   in Verdict rid $
        case runtimeReplayFailure input of
          Just _ -> Reject (RejectClass R13)
          Nothing ->
            case checkUnit (buildGamma (unitLeaves unit))
                 (buildCertOk (unitTheories unit)) unit of
              Left err -> Reject (rejectionOf err)
              Right accepted -> buildAccept unit accepted
```

Make `buildAccept` return `Outcome`, not `Verdict`. Remove `runUnit`.

In `app/Main.hs`:

```haskell
-- .sexp
Right input -> emitVerdict (runCheck input)

-- .lara, after elaborate succeeds
case sourceCheckInput prog pol unit of
  Left err -> die2 ("lara: replay identity error: " ++ replayErrorMessage err)
  Right input -> emitVerdict (runCheck input)
```

`emitVerdict` branches on `verdictOutcome`. Update module comments to state that `.sexp` contains a check-input envelope, not a bare Unit.

- [ ] **Step 5: Add replay identity to JSON and handle preflight diagnostics**

Change `expectedJson`/`expectedJsonValue` to accept `CheckInput`. Emit the leading object exactly:

```haskell
replayIdValue rid =
  JObject
    [ ("core", JString "lara-core@0.1")
    , ("policy", JString policy)
    , ("backends", JArray (map (JString . renderBackendRef) backends))
    , ("theories", JArray (map (JString . renderTheoryDigest) theories))
    , ("artifact", JString artifact)
    ]
```

For `runtimeReplayFailure input = Just failure`, emit class `reject R13`, stage `backend`, and:

```text
DuplicateSelectedBackend      -> policy / duplicate-selection
UnknownSelectedBackend        -> policy / unknown-selection
CertificateBackendNotSelected -> outer argument / certificate-backend-not-selected
```

Include the offending `backend@version`. For ordinary `UnitError`, preserve the current `locate` output byte-for-byte below the new replay-id member.

Add one synthetic expected-JSON property for each replay preflight reason so the `Right _ -> JNull` fallback cannot hide an accepted Unit behind an R13 verdict.

- [ ] **Step 6: Migrate all Haskell callers atomically**

Before editing exported callsites, use LSP references on `runUnit`, `decodeUnitFile`, `VAccept`, and `VReject`; migrate every returned reference. Apply these patterns:

```haskell
-- Unit-focused tests
runCheck (testCheckInput unit)

-- source tests
sourceCheckInput prog pol unit >>= Right . runCheck

-- fixture tests
case decodeCheckInputFile bytes of
  Left e -> counterexample ("codec: " ++ show e) (property False)
  Right input -> property (runCheck input == expectedVerdict)

-- direct checker comparison
let unit = inputUnit input
in checkUnit (buildGamma (unitLeaves unit)) (buildCertOk (unitTheories unit)) unit
```

Pattern-match `Verdict _ (Reject r)` and `Verdict _ Accept{}`. Update comments that describe the old bare-Unit executable boundary.

In `test/DifferentialSpec.hs`, retain explicit outcome tails such as:

```haskell
"accept (labels (0 in)) (edges) (statuses (status (atom p) justified))"
"reject R13"
```

Build the expected full verdict with the decoded fixture identity:

```haskell
expectedVerdictText input outcomeTail =
  "(verdict "
    ++ printSExpr (encodeReplayId (inputReplayId input))
    ++ " " ++ outcomeTail ++ ")"
```

This keeps outcome goldens independent while asserting `runCheck` returns the exact identity carried by each canonical anchor.

- [ ] **Step 7: Update generators and regenerate all Haskell anchors**

In `scripts/gen-corpus.hs`, wrap every generated Unit with the same constants used by `test/TestReplay.hs`: policy `conformance-v1`, selected backend `nd@1`, sorted Unit theory keys, artifact `sha256:conformance-corpus-v1`. The script must call `mkReplayId` and `mkCheckInput` and fail on `Left`; it cannot import a module under `test/` or access hidden constructors.

In `scripts/gen-worked-examples.hs`, make the loader return `CheckInput`:

```haskell
case elaborate defeasibleSuiteSigma (registryOf pol) prog pol of
  Left e -> fail (artifactPath ++ ": elaborate: " ++ elabErrorMessage e)
  Right unit ->
    either (fail . replayErrorMessage) pure (sourceCheckInput prog pol unit)
```

Write `encodeCheckInput input` and `expectedJson input`.

Run:

```bash
cabal exec -- runghc scripts/gen-corpus.hs
cabal exec -- runghc scripts/gen-worked-examples.hs
cabal exec -- runghc scripts/gen-worked-examples.hs --bundle bundles/walking-skeleton
```

Wrap `fixtures/covered-self-edge.sexp` and `fixtures/missing-self-edge.sexp` with the same conformance replay-id and leave each existing nested Unit text unchanged.

- [ ] **Step 8: Verify Haskell end to end**

Run:

```bash
cabal test
cabal run exe:lara -- check examples/S1/example.lara
cabal run exe:lara -- check examples/S1/example.core.sexp
cabal run exe:lara -- check fixtures/corpus/reject-r1.sexp
```

Expected:

- the full Haskell suite passes;
- both S1 commands print identical identity-bearing accept verdicts and exit `0`;
- the R1 fixture prints an identity-bearing reject verdict and exits `1`;
- every `example.core.sexp` and `expected.json` freshness assertion passes.

- [ ] **Step 9: Commit the Haskell cutover and regenerated anchors**

```bash
git add app/Main.hs src/Lara/Wire.hs src/Lara/Driver.hs src/Lara/ExpectedJson.hs \
  test scripts/gen-corpus.hs scripts/gen-worked-examples.hs fixtures examples \
  bundles/walking-skeleton/emitted.core.sexp
git commit -m "feat: carry replay identity through checker verdicts"
```

---

### Task 3: Lean Driver Parity

**Files:**
- Modify: `lean/Lara/Driver.lean:1-35,60-110,320-385,610-665,667-776`

**Interfaces:**
- Consumes: Task 2's exact check-input and verdict grammar.
- Produces: byte-identical Lean decoding, validation, R13 preflight, and replay-id verdict encoding. No `Lara` library or theorem interface changes.

- [ ] **Step 1: Run the differential and capture the expected incompatibility**

Run:

```bash
bash scripts/differential.sh
```

Expected: Haskell accepts the new check-input anchors, while the old Lean driver exits `2` with a codec error; the harness reports mismatches rather than a false pass.

- [ ] **Step 2: Add the mirrored Lean boundary types and tags**

Extend `Tag`/`tagToString` with the same six spellings. Add boundary-only structures:

```lean
structure ReplayId where
  policy : String
  backends : List (String × String)
  theories : List String
  artifact : String

structure CheckInput where
  replayId : ReplayId
  decoded : Decoded
```

Add the comparator and insertion sort beside those structures:

```lean
def compareCharLists : List Char → List Char → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | a :: as, b :: bs =>
      if a.toNat < b.toNat then .lt
      else if b.toNat < a.toNat then .gt
      else compareCharLists as bs

def compareCodePointString (a b : String) : Ordering :=
  compareCharLists a.toList b.toList

def insertCodePointString (s : String) : List String → List String
  | [] => [s]
  | x :: xs =>
      if compareCodePointString s x == .lt then s :: x :: xs
      else x :: insertCodePointString s xs

def sortCodePointStrings (xs : List String) : List String :=
  xs.foldr insertCodePointString []

def strictlySortedStrings : List String → Bool
  | [] | [_] => true
  | a :: b :: rest =>
      compareCodePointString a b == .lt &&
        strictlySortedStrings (b :: rest)
```



- [ ] **Step 3: Decode and validate the check-input envelope**


Define these helpers immediately before the decoders:

```lean
def decodeReplayBackend (e : Sx) : Except String (String × String) :=
  match e with
  | .list [.atom k, .atom name, .atom version] =>
      if k == tagToString .backend then .ok (name, version)
      else .error "replay backend: expected backend tag"
  | _ => .error "replay backend: malformed backend"

def validateReplayId (policy : String) (backends : List (String × String))
    (theories : List String) (artifact : String) : Except String ReplayId :=
  if strictlySortedStrings theories then
    .ok { policy := policy, backends := backends,
      theories := theories, artifact := artifact }
  else .error "replay-id: theories must be strictly sorted"

def validateTheoryIdentity (rid : ReplayId) (decoded : Decoded) :
    Except String _root_.Unit :=
  let keys := decoded.theories.map (fun entry =>
    match entry.1 with | ⟨s⟩ => s)
  match firstDup keys [] with
  | some digest => .error ("unit theories: duplicate digest: " ++ digest)
  | none =>
      if sortCodePointStrings keys == rid.theories then .ok ()
      else .error "check-input: replay theories differ from unit theories"
```

`decodeReplayBackend` accepts exactly `(backend ATOM ATOM)`.
`validateReplayId` enforces strict code-point ordering of theories.
`validateTheoryIdentity` rejects duplicate Unit theory keys and unequal sorted
keys.

```lean
def decodeReplayId (e : Sx) : Except String ReplayId :=
  match e with
  | .list [.atom replayTag,
      .list [.atom coreTag, .atom core],
      .list [.atom policyTag, .atom policy],
      .list (.atom backendsTag :: backends),
      .list (.atom theoriesTag :: theories),
      .list [.atom artifactTag, .atom artifact]] => do
      let _ ←
        if replayTag != tagToString .replayId ||
            coreTag != tagToString .core ||
            policyTag != tagToString .policy ||
            backendsTag != tagToString .backends ||
            theoriesTag != tagToString .theories ||
            artifactTag != tagToString .artifact then
          (.error "replay-id: wrong field order" : Except String _root_.Unit)
        else .ok ()
      let _ ←
        if core != "lara-core@0.1" then
          (.error "replay-id: unsupported core version" : Except String _root_.Unit)
        else .ok ()
      let refs ← backends.mapM decodeReplayBackend
      let digests ← theories.mapM (sxAtom "replay theory")
      validateReplayId policy refs digests artifact
  | _ => .error "replay-id: malformed replay identity"

def decodeCheckInput (e : Sx) : Except String CheckInput :=
  match e with
  | .list [.atom k, ridS, unitS] =>
      if k != tagToString .checkInput then
        .error "check-input: expected check-input tag"
      else do
        let rid ← decodeReplayId ridS
        let decoded ← decodeUnit unitS
        validateTheoryIdentity rid decoded
        .ok { replayId := rid, decoded := decoded }
  | _ => .error "check-input: malformed check input"
```

Require exact replay-id field order and `lara-core@0.1`. Require theory strings to be already Unicode-scalar-lexicographically sorted and duplicate-free. After `decodeUnit`, reject duplicate Unit theory keys and require their sorted keys to equal `ReplayId.theories`.

Keep `decodeUnit` as the nested semantic decoder. Change `runOnContents` to call `decodeCheckInput`, not `decodeUnit` directly.

- [ ] **Step 4: Mirror runtime backend preflight**

Derive the supported backend pair from `ndBackendId`. Implement these pure checks in order:

```lean
first duplicate replayId.backends
first selected pair unequal to ndBackendId name/version
first Assurance.cert pair absent from replayId.backends
```

Traverse outer arguments in list order; inside each `SupportTerm.inst`, visit the node's assurance, then premises left-to-right, then discharges left-to-right. This must match the Haskell traversal selected in Task 1. If any check fails, print `(verdict <replay-id> reject R13)` and exit `1` before `checkUnit`.

- [ ] **Step 5: Add replay identity to both Lean verdict encoders**

Implement:

```lean
def encodeReplayId (rid : ReplayId) : Sx :=
  .list
    [ .atom (tagToString .replayId)
    , .list [.atom (tagToString .core), .atom "lara-core@0.1"]
    , .list [.atom (tagToString .policy), .atom rid.policy]
    , .list (.atom (tagToString .backends) ::
        rid.backends.map (fun bv =>
          .list [.atom (tagToString .backend), .atom bv.1, .atom bv.2]))
    , .list (.atom (tagToString .theories) :: rid.theories.map .atom)
    , .list [.atom (tagToString .artifact), .atom rid.artifact]
    ]

def encodeReject (rid : ReplayId) (cls : String) : Sx :=
  .list [.atom (tagToString .verdict), encodeReplayId rid,
    .atom (tagToString .reject), .atom cls]

def encodeAccept (rid : ReplayId) (labels : List (Nat × Label))
    (edges : List (Nat × Nat)) (statuses : List (Atom × Status)) : Sx :=
  .list
    [ .atom (tagToString .verdict)
    , encodeReplayId rid
    , .atom (tagToString .accept)
    , .list (.atom (tagToString .labels) ::
        labels.map (fun le => .list [sxNat le.1, .atom (labelStr le.2)]))
    , .list (.atom (tagToString .edges) ::
        edges.map (fun ij => .list [sxNat ij.1, sxNat ij.2]))
    , .list (.atom (tagToString .statuses) ::
        statuses.map (fun ps =>
          .list [.atom (tagToString .status), encodeAtom ps.1,
            .atom (statusStr ps.2)]))
    ]
```

Thread `rid` through `buildAccept` and every checker rejection. Update the module contract comment from “reads one wire unit” to “reads one check-input envelope”.

- [ ] **Step 6: Build and run the full byte differential**

Run:

```bash
cd lean && lake build
cd lean && lake env lean AxCheck.lean
bash scripts/differential.sh
```

Expected:

- `lake build` completes;
- `AxCheck.lean` reports no `sorryAx` and no nonstandard axiom;
- differential summary has `fail=0` and a positive `pass` count, with matching stdout and exit codes for every discovered anchor.

Also run a direct reject anchor:

```bash
lean/.lake/build/bin/lara-driver fixtures/corpus/reject-r13.sexp
```

Expected: exit `1` and one replay-id-bearing R13 verdict.

- [ ] **Step 7: Commit Lean parity**

```bash
git add lean/Lara/Driver.lean
git commit -m "feat: mirror replay identity in Lean driver"
```

---

### Task 4: Bundle Refreeze and Replay Proof

**Files:**
- Modify: `scripts/test-replay-tamper.sh`
- Regenerate: `bundles/walking-skeleton/emitted.core.sexp`
- Regenerate: `bundles/walking-skeleton/verdict.txt`
- Regenerate: `bundles/walking-skeleton/manifest.json`

**Interfaces:**
- Consumes: committed Haskell and Lean checker identity from Tasks 2-3.
- Produces: a transactionally refrozen bundle whose verdict carries replay identity and whose manifest points at the final checker-source revision.

- [ ] **Step 1: Prove the old frozen verdict is stale**

Run:

```bash
scripts/replay.sh bundles/walking-skeleton
```

Expected: exit `1`; the freshly generated identity-bearing verdict differs from the pre-issue-36 `verdict.txt`. A checker-source warning may also appear, but replay must not report success.

- [ ] **Step 2: Add an artifact-identity drift tamper case**

Extend `scripts/test-replay-tamper.sh` with a fresh copy of the valid bundle. Change only the digest on the line whose first token is `artifact` by appending `-drift`; do not change the policy, manifest, or frozen verdict. Run replay with the real Haskell checker and assert:

```text
exit = 1
stderr names verdict byte mismatch
stdout is empty
```

This case is distinct from policy hash tampering: `emitted.lara` is an untrusted artifact, so manifest validation succeeds, the checker runs, and verdict-carried replay identity detects drift.

- [ ] **Step 3: Run the new tamper test and observe the stale-bundle failure**

Run:

```bash
bash scripts/test-replay-tamper.sh
```

Expected: the new identity-drift case fails against the old frozen verdict/setup, proving the test exercises the new contract.

- [ ] **Step 4: Refreeze with the final checker revision**

Confirm no uncommitted checker-identity file under the `CHECKER_PATHS` set remains, then run:

```bash
python3 scripts/test_freeze_bundle.py
python3 scripts/freeze-bundle.py bundles/walking-skeleton
```

Expected: the freezer regenerates `emitted.core.sexp`, `verdict.txt`, and canonical `manifest.json` transactionally. `verdict.txt` contains one replay-id. `manifest.json` has the checker-source revision of Task 3's committed checker and unchanged pinned producer toolchain values.

- [ ] **Step 5: Run replay, tamper, and complete verification gates**

Run:

```bash
scripts/replay.sh bundles/walking-skeleton
bash scripts/test-replay-tamper.sh
cabal test
cd lean && lake build
cd lean && lake env lean AxCheck.lean
bash scripts/differential.sh
```

Expected:

- bundle replay matches frozen stdout and exit code;
- policy tamper still fails before checker invocation;
- artifact-digest drift invokes the checker and then fails on verdict bytes;
- Haskell suite passes;
- Lean build and axiom audit pass with no `sorryAx`;
- differential summary has `fail=0` and a positive `pass` count.

Run the actual user paths once more:

```bash
cabal run exe:lara -- check examples/A/example.lara
cabal run exe:lara -- check examples/A/example.core.sexp
```

Expected: byte-identical replay-id-bearing accept verdicts.

- [ ] **Step 6: Commit the frozen replay artifacts**

```bash
git add scripts/test-replay-tamper.sh bundles/walking-skeleton/emitted.core.sexp \
  bundles/walking-skeleton/verdict.txt bundles/walking-skeleton/manifest.json
git commit -m "test: refreeze replay bundle with verdict identity"
```

The implementation is complete only if no later commit changes `src/`, `app/`, `lean/`, `lara.cabal`, or `cabal.project`. If one does, rerun Steps 4-6 so the manifest revision and verdict are fresh.
