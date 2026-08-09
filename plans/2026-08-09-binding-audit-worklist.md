# Binding-audit worklist implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use `subagent-driven-development` (recommended) or `executing-plans` to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extend the existing claim-support reporting pass to generate a deterministic, role-aware TSV worklist for the exhaustive audit of the frozen corpus's 38 load-bearing leaves required by issue #87 Step 0.

**Architecture:** Keep the checker and frozen corpus unchanged. `Lara.ClaimSupport.computeUnit` already identifies load-bearing leaf IDs from `in`-labelled arguments; extend that same projection with a `BindingAuditRow` carrying the surface leaf and the claim context in which the leaf is used. Derive attack roles and target argument IDs from the existing checked `unitAttacks` graph, while taking human-facing leaf and claim data from the parsed `.lara` program. A pure renderer emits manifest-ordered TSV, and `scripts/claim-support.hs` atomically replaces the committed worklist beside—never inside—the frozen measurements.

**Data flow:**

```text
corpus-units/MANIFEST.tsv
          |
          v
      loadRecords
          |
          +--> checked core: runCheck labels + unitArgs + unitAttacks
          |
          `--> parsed .lara: Leaf + Arg conclusion + Claim id/nl
                              |
                              v
                         computeUnit
                              |
                  existing loadBearingLeafIds
                              |
              core attack endpoints choose role/target
                              |
                surface lookups supply audit context
                              |
             exactly one distinct (role, claim_id)
                              |
                              v
                  urBindingAuditRows (same order)
                              |
                              v
             bindingAuditTsv -> atomic worklist.tsv
```

**Tech stack:** Haskell/GHC 2021, the existing `Lara.AST`/`Lara.ClaimSupport` reporting path, QuickCheck integration properties, canonical `.lara` printing, TSV.

**Issue:** [#87 — Binding audit over the 38 load-bearing leaves](https://github.com/EYH0602/lara/issues/87), Step 0 only.

## Global constraints

- Preserve the current denominator exactly: 38 unique `(unit, leaf_id)` rows, with 20 `attested` and 18 `observed` leaves.
- Preserve the current definition of load-bearing: leaves referenced by `in`-labelled support terms, deduplicated in first dependency occurrence order within each manifest-ordered unit.
- Use role-aware claim context, as decided on 2026-08-09:
  - `support`: the immediate declared claim named by the load-bearing argument;
  - `attack`: the declared claim supported by the argument targeted by the load-bearing attack source.
- Require exactly one distinct `(role, claim_id)` context for every worklist leaf. Missing or ambiguous context is corpus/reporting drift and must fail loudly; never pick one silently.
- Rely on the existing `CorpusUnitsSpec` byte-exact `parse + elaborate + encode == committed core` property for the core/surface join; do not duplicate a partial claim-formal validator inside reporting.
- Emit exactly these columns, in order: `unit`, `leaf_id`, `formal_target`, `role`, `claim_id`, `claim_nl`, `kind`, `provenance`, `refs`.
- Order rows by `corpus-units/MANIFEST.tsv`, then by the existing first-occurrence order of `urLoadBearing` within a unit. Do not sort by rendered text.
- Render `formal_target` with the canonical `.lara` proposition printer, not `Show` and not the core S-expression codec.
- Escape backslash, tab, carriage return, and newline in every TSV cell as `\\`, `\t`, `\r`, and `\n`. Join refs with commas; commas cannot occur in a parsed `SourceRef` (`Lara.Syntax.isSourceRefChar`). Render an empty refs list as `-`.
- Create `measurements/binding-audit/worklist.tsv`. Do not create `results.tsv` or `README.md`; those belong to #87 Steps 1–3 after the human audit.
- Do not modify `corpus-units/`, `fixtures/`, `measurements/frozen/`, any `.core.sexp`, checker behavior, wire bytes, Lean, replay identity, or paper text.
- Keep the existing `measurements/claim-support.{json,tsv}` formats byte-compatible. Their existing frozen freshness property remains the regression guard.
- Add no dependency and no separate executable. The existing command remains:

  ```bash
  cabal exec -- runghc scripts/claim-support.hs
  ```

- Fully traverse the rendered JSON, aggregate TSV, and worklist TSV before the first filesystem write so a pure row/context failure cannot leave earlier outputs changed.
- Atomically replace only `measurements/binding-audit/worklist.tsv` with a same-directory temporary file and rename. Keep the existing no-argument, three-output command; add no worklist-only mode.

---

## File map

| File | Responsibility | Change |
|---|---|---|
| `src/Lara/ClaimSupport.hs` | Shared pure claim-support projection and renderers | Add the closed audit-role type, audit row type, checked-attack context derivation, deterministic TSV renderer, and update ownership comments. |
| `src/Lara/Syntax.hs` | Canonical `.lara` printer | Export the existing `printProp`; do not add a second proposition renderer. |
| `scripts/claim-support.hs` | Manifest-driven reporting command | Force all renderings before writes, create `measurements/binding-audit/`, and atomically replace `worklist.tsv` from the same records used by the existing reports. |
| `test/ClaimSupportSpec.hs` | Frozen reporting regression suite | Pin exact ordered row identity, every role-aware context and drift failure, counts, TSV shape/escaping/ref validation, and committed-worklist freshness. |
| `measurements/binding-audit/worklist.tsv` | Generated audit input | Add the 38-row deterministic worklist; no human classifications. |

No new module is justified: the worklist is another projection of the records already owned by `Lara.ClaimSupport`, and splitting it would duplicate the load-bearing calculation or create a one-function wrapper.

---

### Task 1: Derive role-aware audit rows from the existing load-bearing projection

**Files:**
- Modify: `src/Lara/ClaimSupport.hs:36-82,139-262`
- Test: `test/ClaimSupportSpec.hs:16-117`

**Interfaces:**
- Produces:

  ```haskell
  data BindingAuditRole = AuditSupport | AuditAttack
    deriving (Eq, Ord, Show)

  data BindingAuditRow = BindingAuditRow
    { barUnit :: String
    , barLeafId :: LeafId
    , barFormalTarget :: Prop
    , barRole :: BindingAuditRole
    , barClaimId :: PropId
    , barClaimNl :: String
    , barKind :: LeafKind
    , barProvenance :: Provenance
    , barRefs :: [SourceRef]
    }
    deriving (Eq, Show)
  ```

- Extends `UnitRecord` with:

  ```haskell
  urBindingAuditRows :: [BindingAuditRow]
  ```

- Keeps `urLoadBearing :: [LeafFact]` unchanged so existing aggregate and frozen render paths cannot drift.

- [ ] **Step 1: Add failing corpus properties for row identity and role-aware context**

Add the new properties to `claimSupportSpecProps`:

```haskell
, ("claim-support: binding-audit rows preserve the frozen 38-leaf denominator", quickCheckResult prop_bindingAuditRows)
, ("claim-support: binding-audit rows carry role-aware claim context", quickCheckResult prop_bindingAuditContexts)
```

Implement the tests against `loadRecords`:

```haskell
prop_bindingAuditRows :: Property
prop_bindingAuditRows = once $ ioProperty $ do
  records <- loadRecords manifestPath policyPath
  let rows = concatMap urBindingAuditRows records
      keys = [(barUnit r, barLeafId r) | r <- rows]
      expectedKeys =
        [ (urName record, lfId leaf)
        | record <- records
        , leaf <- urLoadBearing record
        ]
      countKind k = length [() | r <- rows, barKind r == k]
  pure $
    conjoin
      [ counterexample "worklist rows" (length rows === 38)
      , counterexample "ordered unit/leaf keys" (keys === expectedKeys)
      , counterexample "unique unit/leaf keys" (length (nub keys) === 38)
      , counterexample "attested rows" (countKind Attested === 20)
      , counterexample "observed rows" (countKind Observed === 18)
      , counterexample "provenance" (property (all ((== AiExecuted) . barProvenance) rows))
      ]

prop_bindingAuditContexts :: Property
prop_bindingAuditContexts = once $ ioProperty $ do
  rows <- concatMap urBindingAuditRows <$> loadRecords manifestPath policyPath
  let row unit lid =
        case [r | r <- rows, barUnit r == unit, barLeafId r == LeafId lid] of
          [r] -> r
          rs -> error ("claim-support test: expected one " ++ unit ++ "/" ++ lid ++ " row, got " ++ show (length rs))
      strictCell = row "adaptive-pruning.C04" "e4"
      attackContexts =
        [ (barUnit r, barLeafId r, barClaimId r)
        | r <- rows
        , barRole r == AuditAttack
        ]
      expectedAttackContexts =
        [ ("fre.C04", LeafId "u1", PropId "c04")
        , ("rebench-triton_cumsum.C09", LeafId "u1", PropId "c09")
        , ("test-time-model-adaptation.C04", LeafId "u1", PropId "c04")
        ]
  pure $
    conjoin
      [ counterexample "strict subclaim role" (barRole strictCell === AuditSupport)
      , counterexample "strict subclaim id" (barClaimId strictCell === PropId "c04a")
      , counterexample "all attack contexts" (attackContexts === expectedAttackContexts)
      ]
```

Add a table-driven `prop_bindingAuditContextFailures` using a compact synthetic
`CheckInput` / `Verdict` / `Program` fixture around the exported `computeUnit`.
Each case must force `urBindingAuditRows` and assert the stable error prefix for
one new fail-loud arm:

- missing declared claim;
- duplicate declared claim;
- missing surface argument;
- duplicate surface argument;
- load-bearing `SupportsDerived` source;
- load-bearing `Challenges` source with no typed attack;
- attacked `SupportsDerived` target;
- attacked `Challenges` target;
- more than one distinct `(role, claim_id)` context for one leaf.

Do not export private context helpers for tests.

Update imports with `nub`, `LeafId (..)`, and `PropId (..)`.

- [ ] **Step 2: Run the test suite and confirm the new contract fails before implementation**

Run:

```bash
cabal test lara-test --test-show-details=direct
```

Expected: compilation fails because `urBindingAuditRows`, `BindingAuditRow`, `AuditSupport`, and `AuditAttack` do not exist.

- [ ] **Step 3: Add the audit model without changing existing aggregate fields**

Export `BindingAuditRole (..)` and `BindingAuditRow (..)` from `Lara.ClaimSupport`. Import `Claim (..)`, `PropId (..)`, and the existing `Attack (..)` constructors from `Lara.AST`, and import `Prop` from `Lara.Prop`.

Update the `Lara.ClaimSupport` module header, `UnitRecord` Haddock, and rendering-section comment so they name the binding-audit projection alongside the existing four-number report.

Add the two data declarations shown in **Interfaces**, then append `urBindingAuditRows` to `UnitRecord`.

In `computeUnit`, derive rows from the existing `loadBearingArgs`,
`loadBearingLeafIds`, and `attacks = unitAttacks unit`. Use checked core attack
endpoints because they belong to the same graph that produced `labels`; use
surface declarations only for the human-facing claim and leaf fields:

```haskell
surfaceClaims = [c | DeclClaim c <- programDecls prog]

claimById cid =
  case [c | c <- surfaceClaims, claimId c == cid] of
    [c] -> c
    [] -> error ("claim-support: claim " ++ show cid ++ " missing from " ++ name)
    _ -> error ("claim-support: duplicate claim " ++ show cid ++ " in " ++ name)

surfaceArgById aid =
  case [a | a <- surfaceArgs, argId a == aid] of
    [a] -> a
    [] -> error ("claim-support: argument " ++ show aid ++ " missing from surface decls in unit " ++ name)
    _ -> error ("claim-support: duplicate argument " ++ show aid ++ " in unit " ++ name)

attackTargets aid =
  nub
    [ attackTarget attack
    | attack <- attacks
    , attackSrc attack == aid
    ]

attackTarget attack = case attack of
  Rebut _ target -> target
  Undercut _ target _ -> target
  Undermine _ target _ -> target
```

Use a private context type so a leaf can collect contexts from every load-bearing argument that mentions it before enforcing uniqueness:

```haskell
data AuditContext = AuditContext BindingAuditRole Claim
  deriving (Eq, Show)
```

Context rules:

```haskell
contextsForArg aid =
  case nub (attackTargets aid) of
    [] ->
      case argConcl (surfaceArgById aid) of
        SupportsClaim cid -> [AuditContext AuditSupport (claimById cid)]
        SupportsDerived cid ->
          error ("claim-support: load-bearing derived claim " ++ show cid ++ " has no nl context in " ++ name)
        Challenges _ ->
          error ("claim-support: load-bearing challenge " ++ show aid ++ " has no typed attack in " ++ name)
    targets ->
      [ AuditContext AuditAttack (targetClaim target)
      | target <- targets
      ]

targetClaim target =
  case argConcl (surfaceArgById target) of
    SupportsClaim cid -> claimById cid
    SupportsDerived cid ->
      error ("claim-support: attacked derived claim " ++ show cid ++ " has no nl context in " ++ name)
    Challenges _ ->
      error ("claim-support: attack target " ++ show target ++ " is not a claim support in " ++ name)
```

For each `loadBearingLeafId`, collect contexts from every `(ArgId, SupportTerm)` in `loadBearingArgs` whose `leaves` contains that ID. Deduplicate equal contexts with `nub`; accept exactly one and hard-error on zero or more than one. Build the row from the corresponding surface `Leaf`:

```haskell
bindingAuditRow lid =
  let leaf = requireLeaf lid
      contexts =
        nub
          [ context
          | (aid, term) <- loadBearingArgs
          , lid `elem` leaves term
          , context <- contextsForArg aid
          ]
      AuditContext role claim =
        case contexts of
          [context] -> context
          [] -> error ("claim-support: load-bearing leaf " ++ show lid ++ " has no claim context in " ++ name)
          _ -> error ("claim-support: load-bearing leaf " ++ show lid ++ " has ambiguous claim context in " ++ name)
   in BindingAuditRow
        { barUnit = name
        , barLeafId = lid
        , barFormalTarget = leafProp leaf
        , barRole = role
        , barClaimId = claimId claim
        , barClaimNl = claimNl claim
        , barKind = leafKind leaf
        , barProvenance = leafProvenance leaf
        , barRefs = leafRefs leaf
        }
```

Factor the current `leafById` case into `requireLeaf`; both `leafFact` and `bindingAuditRow` must use it. Set:

```haskell
urBindingAuditRows = map bindingAuditRow loadBearingLeafIds
```

Do not change `loadBearingLeafIds`, `urLoadBearing`, `aggregate`, `claimSupportJson`, or `claimSupportTsv`.

- [ ] **Step 4: Run the tests and confirm row derivation passes**

Run:

```bash
cabal test lara-test --test-show-details=direct
```

Expected: PASS, including the exact ordered 38-row identity, 20/18 split,
all three attack contexts, the `c04a` support context, and every table-driven
missing/duplicate/derived/challenge/ambiguous drift failure. The existing frozen
JSON/TSV re-diff must remain green.

- [ ] **Step 5: Commit the role-aware projection**

```bash
git add src/Lara/ClaimSupport.hs test/ClaimSupportSpec.hs
git commit -m "feat(audit): derive binding worklist rows"
```

---

### Task 2: Render the deterministic worklist TSV

**Files:**
- Modify: `src/Lara/Syntax.hs:74-97,1785-1794`
- Modify: `src/Lara/ClaimSupport.hs:36-51,424-479`
- Test: `test/ClaimSupportSpec.hs:35-117`

**Interfaces:**
- Reuses the existing `Lara.Syntax.printProp :: Prop -> String` by exporting it.
- Produces:

  ```haskell
  bindingAuditTsvHeader :: String
  bindingAuditTsv :: [UnitRecord] -> String
  ```

- TSV rows consume only `urBindingAuditRows`; no checker or loader API changes.

- [ ] **Step 1: Add a failing renderer property**

Register:

```haskell
, ("claim-support: binding-audit TSV is canonical and rectangular", quickCheckResult prop_bindingAuditTsv)
```

Add:

```haskell
prop_bindingAuditTsv :: Property
prop_bindingAuditTsv = once $ ioProperty $ do
  records <- loadRecords manifestPath policyPath
  let rendered = bindingAuditTsv records
      renderedLines = lines rendered
      cells = map splitOnTab renderedLines
      syntheticRow =
        BindingAuditRow
          { barUnit = "unit\tone"
          , barLeafId = LeafId "e1"
          , barFormalTarget = Prop (Pred "p") []
          , barRole = AuditSupport
          , barClaimId = PropId "c1"
          , barClaimNl = "line one\nline two\\tail"
          , barKind = Observed
          , barProvenance = AiExecuted
          , barRefs = [SourceRef "trace/a|b", SourceRef "Table-1"]
          }
      syntheticRecord =
        UnitRecord
          { urName = "synthetic"
          , urStatuses = []
          , urLoadBearing = []
          , urAllLeaves = []
          , urTypedAttacks = 0
          , urDeadEndAttacks = 0
          , urStrictSteps = 0
          , urStrictCertified = 0
          , urStrictFlavored = False
          , urBindingAuditRows = [syntheticRow]
          }
      syntheticDataLine = last (lines (bindingAuditTsv [syntheticRecord]))
  pure $
    conjoin
      [ counterexample "header" (head renderedLines === bindingAuditTsvHeader)
      , counterexample "header columns" (length (head cells) === 9)
      , counterexample "data rows" (length (tail renderedLines) === 38)
      , counterexample "rectangular rows" (property (all ((== 9) . length) (tail cells)))
      , counterexample "canonical final newline" (property (not (null rendered) && last rendered == '\n'))
      , counterexample
          "TSV escaping and comma-delimited refs"
          ( syntheticDataLine
              === "unit\\tone\te1\tp\tsupport\tc1\tline one\\nline two\\\\tail\tobserved\tai-executed\ttrace/a|b,Table-1"
          )
      ]

Add a second synthetic row whose `claim_nl` contains `\r` and whose refs list is
empty. Assert that the physical TSV line contains `\\r` and ends in `\t-`.
Also add negative renderer cases for `SourceRef "a,b"` and the reserved
`SourceRef "-"`; force the rendered output and require a fail-loud error rather
than ambiguous refs bytes.

Update the test imports with `Pred (..)` and `Prop (..)` from `Lara.Prop`.

Add a small local `splitOnTab` helper that preserves empty cells:

```haskell
splitOnTab :: String -> [String]
splitOnTab [] = [""]
splitOnTab xs =
  case break (== '\t') xs of
    (cell, []) -> [cell]
    (cell, _ : rest) -> cell : splitOnTab rest
```

- [ ] **Step 2: Run the suite and verify the renderer contract fails**

Run:

```bash
cabal test lara-test --test-show-details=direct
```

Expected: compilation fails because `bindingAuditTsv` and `bindingAuditTsvHeader` do not exist.

- [ ] **Step 3: Export the canonical proposition printer**

Add `printProp` to the `Lara.Syntax` export list under canonical printing. Do not move, copy, or rewrite its implementation at `src/Lara/Syntax.hs:1785-1794`.

Import `printProp` into `Lara.ClaimSupport`. This keeps the worklist's `formal_target` spelling identical to canonical `.lara` source and prevents a second rendering convention.

- [ ] **Step 4: Implement the TSV renderer**

Export `bindingAuditTsvHeader` and `bindingAuditTsv` from `Lara.ClaimSupport`.

```haskell
bindingAuditTsvHeader :: String
bindingAuditTsvHeader =
  intercalateTab
    [ "unit"
    , "leaf_id"
    , "formal_target"
    , "role"
    , "claim_id"
    , "claim_nl"
    , "kind"
    , "provenance"
    , "refs"
    ]

bindingAuditTsv :: [UnitRecord] -> String
bindingAuditTsv records =
  unlines (bindingAuditTsvHeader : map row (concatMap urBindingAuditRows records))
  where
    row r =
      intercalateTab
        ( map
            escapeTsvCell
            [ barUnit r
            , let LeafId lid = barLeafId r in lid
            , printProp (barFormalTarget r)
            , auditRoleStr (barRole r)
            , let PropId cid = barClaimId r in cid
            , barClaimNl r
            , kindStr (barKind r)
            , provStr (barProvenance r)
            , refsCell (barRefs r)
            ]
        )

refsCell [] = "-"
refsCell refs
  | any invalidRef refs =
      error "claim-support: binding-audit ref contains comma or reserved '-'"
  | otherwise = intercalateComma [ref | SourceRef ref <- refs]
  where
    invalidRef (SourceRef ref) = ',' `elem` ref || ref == "-"

auditRoleStr :: BindingAuditRole -> String
auditRoleStr AuditSupport = "support"
auditRoleStr AuditAttack = "attack"

escapeTsvCell :: String -> String
escapeTsvCell = concatMap escape
  where
    escape '\\' = "\\\\"
    escape '\t' = "\\t"
    escape '\r' = "\\r"
    escape '\n' = "\\n"
    escape c = [c]
```

Add a private `intercalateComma` alongside the existing `intercalateTab`, or use `Data.List.intercalate` consistently for both. Do not use `Show` for `Prop`, IDs, roles, kinds, provenance, or refs.

- [ ] **Step 5: Run the suite and confirm canonical rendering passes**

Run:

```bash
cabal test lara-test --test-show-details=direct
```

Expected: PASS. The new renderer has one header plus 38 nine-column rows and a
final newline; `\\`, `\t`, `\r`, `\n`, nonempty refs, empty refs, and invalid
refs are covered; all pre-existing tests remain green.

- [ ] **Step 6: Commit the renderer**

```bash
git add src/Lara/Syntax.hs src/Lara/ClaimSupport.hs test/ClaimSupportSpec.hs
git commit -m "feat(audit): render binding worklist"
```

---

### Task 3: Wire generation and pin the committed worklist

**Files:**
- Modify: `scripts/claim-support.hs:1-60`
- Modify: `test/ClaimSupportSpec.hs:29-40,98-117`
- Create: `measurements/binding-audit/worklist.tsv`

**Interfaces:**
- The existing no-argument command writes all three reporting products:
  - `measurements/claim-support.json`
  - `measurements/claim-support.tsv`
  - `measurements/binding-audit/worklist.tsv`
- `bindingAuditTsv records` remains the sole source of worklist bytes in both the command and freshness test.

- [ ] **Step 1: Add the failing committed-worklist freshness property**

Add:

```haskell
bindingAuditPath :: FilePath
bindingAuditPath = "measurements/binding-audit/worklist.tsv"
```

Register:

```haskell
, ("claim-support: binding-audit worklist is fresh", quickCheckResult prop_bindingAuditFresh)
```

Implement:

```haskell
prop_bindingAuditFresh :: Property
prop_bindingAuditFresh = once $ ioProperty $ do
  records <- loadRecords manifestPath policyPath
  committed <- readFile bindingAuditPath
  pure $
    counterexample
      "measurements/binding-audit/worklist.tsv differs from fresh rendering"
      (bindingAuditTsv records === committed)
```

- [ ] **Step 2: Run the suite and confirm the missing artifact fails**

Run:

```bash
cabal test lara-test --test-show-details=direct
```

Expected: FAIL because `measurements/binding-audit/worklist.tsv` does not exist.

- [ ] **Step 3: Extend the reporting command**

Update the module comment to name the new output. Import `bindingAuditTsv` with
the existing renderers. Bind all three rendered strings, then use
`Control.Exception.evaluate` to traverse their lengths before creating or
writing any destination:

```haskell
let jsonBytes = claimSupportJson env report records
    aggregateTsvBytes = claimSupportTsv records
    worklistBytes = bindingAuditTsv records
_ <- evaluate (length jsonBytes + length aggregateTsvBytes + length worklistBytes)
```

Create `measurements/binding-audit/`, write the two existing aggregate outputs
as before, and atomically replace the worklist through a same-directory
temporary file:

```haskell
writeFile "measurements/claim-support.json" jsonBytes
writeFile "measurements/claim-support.tsv" aggregateTsvBytes
atomicWriteFile "measurements/binding-audit" ".worklist.tsv.tmp"
  "measurements/binding-audit/worklist.tsv" worklistBytes
```

Implement `atomicWriteFile` locally with `openTempFile`, `hPutStr`, `hClose`,
`renameFile`, and `bracketOnError`; its error cleanup closes the handle and
removes the temporary path. Add no package dependency and no command-line mode.

Update the success message so it names both the aggregate pair and the worklist.
Do not add a second manifest read, policy parse, checker run, or executable.

- [ ] **Step 4: Generate the worklist without destroying pre-existing edits**

First require both known aggregate outputs to be clean in the index and worktree:

```bash
git diff --quiet -- measurements/claim-support.json measurements/claim-support.tsv
git diff --cached --quiet -- measurements/claim-support.json measurements/claim-support.tsv
cabal exec -- runghc scripts/claim-support.hs
```

Keep the generated `measurements/binding-audit/worklist.tsv`. The command also
rewrites the two existing non-frozen aggregate outputs with the current
environment block. Because the two preflight checks proved those paths had no
user changes, discard only those known generator side effects:

```bash
git restore -- measurements/claim-support.json measurements/claim-support.tsv
```

Do not restore, regenerate, or edit anything under `measurements/frozen/`.

- [ ] **Step 5: Run focused acceptance checks**

Run:

```bash
cabal test lara-test --test-show-details=direct
```

Expected: PASS, including:

- 38 unique worklist rows;
- 20 `attested`, 18 `observed`;
- `adaptive-pruning.C04/e4` is `support` for `c04a`;
- `test-time-model-adaptation.C04/u1` is `attack` against `c04`;
- committed worklist bytes equal a fresh pure rendering;
- existing frozen claim-support JSON/TSV remain byte-identical.

- [ ] **Step 6: Commit the generator and artifact**

```bash
git add scripts/claim-support.hs test/ClaimSupportSpec.hs measurements/binding-audit/worklist.tsv
git commit -m "feat(audit): generate binding worklist"
```

---

### Task 4: Run the PR gate and inspect the human audit input

**Files:**
- Verify only; no planned modifications.

**Interfaces:**
- Consumes the committed generator, tests, and worklist from Tasks 1–3.
- Produces evidence that the reporting-only change is ready for review without moving frozen anchors.

- [ ] **Step 1: Build with all warnings enabled by the package configuration**

Run:

```bash
cabal build all
```

Expected: exit 0 with zero GHC warnings.

- [ ] **Step 2: Run the full Haskell suite**

Run:

```bash
cabal test all --test-show-details=direct
```

Expected: all test suites pass, including the existing corpus, replay, mutation, admission, and frozen-report guards.

- [ ] **Step 3: Re-run the generator and prove worklist idempotence**

Require the two restorable outputs to be clean before generation:

```bash
git diff --quiet -- measurements/claim-support.json measurements/claim-support.tsv
git diff --cached --quiet -- measurements/claim-support.json measurements/claim-support.tsv
cabal exec -- runghc scripts/claim-support.hs
git restore -- measurements/claim-support.json measurements/claim-support.tsv
git diff --exit-code -- measurements/binding-audit/worklist.tsv measurements/frozen
```

Expected: both preflights and the generator exit 0, and the final command prints
no diff. The restoration is safe because the preflight proved the two
environment-bearing outputs were clean immediately before generation.

- [ ] **Step 4: Review the committed worklist as an auditor will see it**

Check these observable properties directly in `measurements/binding-audit/worklist.tsv`:

- header contains the nine specified columns in the specified order;
- every row has a concrete `formal_target`, `role`, `claim_id`, and `claim_nl`;
- the three defeated units' load-bearing attack roots are marked `attack`;
- the C04 strict subclaim cells name `c04a`, not the unit's unrelated statused headline;
- no classification column or audit judgment is present.

- [ ] **Step 5: Confirm the exact branch scope**

Compare every `main...HEAD` path against this reviewed allowlist:

```text
ara/logic/solution/constraints.md
ara/staging/observations.yaml
ara/trace/exploration_tree.yaml
ara/trace/pm_reasoning_log.yaml
ara/trace/sessions/2026-08-09_001.yaml
ara/trace/sessions/session_index.yaml
measurements/binding-audit/worklist.tsv
plans/2026-08-09-binding-audit-worklist.md
scripts/claim-support.hs
src/Lara/ClaimSupport.hs
src/Lara/Syntax.hs
test/ClaimSupportSpec.hs
```

Use `git diff --name-only main...HEAD` and fail if `comm -23` finds any path not
in that exact sorted allowlist. Also retain:

```bash
git diff --exit-code main...HEAD -- corpus-units fixtures measurements/frozen lean
```

Expected: the whitelist difference and protected-directory diff are both empty.
This PR is reporting-only and does not require a Lean build, axiom audit,
external Haskell↔Lean differential, replay-tamper run, or refreeze because none
of their inputs or implementations changed.

---

## Acceptance criteria

- `cabal exec -- runghc scripts/claim-support.hs` creates `measurements/binding-audit/worklist.tsv` from the manifest-driven records already used by claim-support reporting.
- The committed worklist has one header and exactly 38 unique data rows.
- Kind split is exactly 20 `attested` / 18 `observed`; provenance is 38 `ai-executed`.
- Each row carries one explicit role-aware claim context; no load-bearing leaf has missing or ambiguous context.
- Support leaves name their immediate declared claim; attack-source leaves name the attacked declared claim.
- The output is deterministic in manifest/dependency order and canonical in proposition rendering and TSV escaping.
- The ordered `(unit, leaf_id)` sequence equals the existing manifest-ordered `urLoadBearing` sequence exactly.
- The exact attack-context set is the three defeated-unit roots targeting `fre.C04/c04`, `rebench-triton_cumsum.C09/c09`, and `test-time-model-adaptation.C04/c04`.
- Every new reachable missing/duplicate/derived/challenge/ambiguous context error arm has a synthetic negative test.
- Renderer tests cover `\\`, `\t`, `\r`, `\n`, nonempty refs, empty refs, and rejection of comma/reserved-`-` refs.
- Pure renderings are fully traversed before any write, and the worklist destination is replaced atomically.
- The committed worklist freshness test compares exact bytes to `bindingAuditTsv records`.
- Existing `measurements/frozen/claim-support.{json,tsv}` freshness remains green.
- `corpus-units/`, `fixtures/`, `measurements/frozen/`, Lean, core/wire bytes, and checker behavior are unchanged.
- `cabal build all` is warning-free and `cabal test all --test-show-details=direct` passes.

## NOT in scope

- Performing or recording any faithful / unfaithful / underdetermined judgment.
- Writing `measurements/binding-audit/results.tsv` or `README.md`.
- Joining checker verdicts into the worklist; the audit must remain blind to status.
- Auditing the one strict step or three typed attacks themselves; #87 Step 2 handles those after the leaf audit.
- Updating the external Overleaf paper.
- Changing the frozen corpus, measurements, checker, Lean development, wire format, replay bundle, or freeze tag.
- Adding a worklist-only command mode or a separate generator; one manifest-driven pass owns all three outputs.
- Duplicating the byte-exact corpus source/core freshness check inside `computeUnit`.
- Generalizing atomic writes across unrelated repository generators; this PR hardens only the new human audit input.

---

## What already exists

| Sub-problem | Existing code / guard | Reuse decision |
|---|---|---|
| Manifest order and unit loading | `Lara.ClaimSupport.Load.loadRecords` | Reuse unchanged; no second discovery or checker pass. |
| Load-bearing denominator and first occurrence | `computeUnit`'s `loadBearingArgs`, `loadBearingLeafIds`, and `urLoadBearing` | Derive rows from the same sequence and test exact ordered key equality. |
| Checked attack endpoints | `unitAttacks`, `attackSrc`, and raw `ArgId` endpoints in `Lara.AST.Attack` | Reuse the checked graph; do not build a parallel surface-attack table. |
| Human-facing leaf and claim fields | Parsed `Program` declarations | Join by raw IDs after the repository's byte-exact corpus freshness guard. |
| Canonical proposition spelling | `Lara.Syntax.printProp` | Export and reuse the existing printer; no second codec. |
| Frozen aggregate compatibility | `prop_frozenDeliverable` | Keep the existing JSON/TSV renderers unchanged and byte-re-diff them. |
| Reporting command | `scripts/claim-support.hs` | Extend the same no-argument command and loaded record set. |

## Failure modes

| Failure | Handling | Test / evidence | User-visible result |
|---|---|---|---|
| Missing, duplicate, derived, challenge, or ambiguous claim context | Hard error before any write after forced rendering | Table-driven synthetic `computeUnit` failures | Command exits nonzero with a `claim-support:` error; no destination changed by the pure failure. |
| Surface/core drift | Existing full-corpus parse/elaborate/encode byte freshness property | `CorpusUnitsSpec.prop_corpusUnitsFresh` in `cabal test all` | Full PR gate fails before the worklist is accepted. |
| Invalid comma or reserved `-` ref | Renderer hard error | Negative renderer cases | No ambiguous refs cell is emitted. |
| Interrupt or write failure while replacing worklist | Same-directory temporary file plus rename | Successful idempotence/freshness gate; destination remains the previous complete file until rename | Command fails; the committed worklist is never partially overwritten. |
| Pre-existing user edits to aggregate outputs | Staged and unstaged cleanliness preflight | Both preflight commands must exit 0 | Workflow aborts before generation instead of restoring user work. |
| Accidental out-of-scope edit | Exact path allowlist plus protected-directory diff | Task 4 scope gate | PR gate fails with the unexpected path. |

No failure mode is both silent and unhandled. Pure derivation and serialization failures are tested directly; interruption safety is covered by the atomic-write design and successful idempotence/freshness checks.

## Parallelization strategy

Sequential implementation, no parallelization opportunity. Tasks 1–3 all
modify `Lara.ClaimSupport` and `ClaimSupportSpec`, and each consumes the
interface and tests from the preceding task. Task 4 is the final verification
barrier after the generated artifact is committed.

## Implementation Tasks

Synthesized from this review's findings. Each task is already folded into the
detailed plan above.

- [ ] **T1 (P1, human: ~1h / CC: ~10min)** — Context projection — Use checked `unitAttacks` endpoints, explicit `PropId (..)`, and accurate module ownership comments.
  - Surfaced by: Architecture and code quality review, issues 1–4.
  - Files: `src/Lara/ClaimSupport.hs`
  - Verify: `cabal test lara-test --test-show-details=direct`
- [ ] **T2 (P1, human: ~2h / CC: ~20min)** — Corpus invariants — Pin exact ordered keys, all three attack contexts, and every fail-loud context branch.
  - Surfaced by: Test review, issues 5–7 and outside issue 14.
  - Files: `test/ClaimSupportSpec.hs`
  - Verify: `cabal test lara-test --test-show-details=direct`
- [ ] **T3 (P2, human: ~45min / CC: ~8min)** — TSV contract — Cover every escape, empty refs, and reject ambiguous ref values.
  - Surfaced by: Test review issue 8 and outside issue 15.
  - Files: `src/Lara/ClaimSupport.hs`, `test/ClaimSupportSpec.hs`
  - Verify: `cabal test lara-test --test-show-details=direct`
- [ ] **T4 (P1, human: ~1h / CC: ~10min)** — Safe generation — Force all renderings, atomically replace the worklist, and preflight restorable outputs.
  - Surfaced by: Operations issue 9 and outside issues 12–13.
  - Files: `scripts/claim-support.hs`
  - Verify: run the generator twice and prove worklist idempotence.
- [ ] **T5 (P2, human: ~30min / CC: ~5min)** — Scope proof — Enforce the exact reviewed branch path allowlist.
  - Surfaced by: Outside issue 16.
  - Files: plan verification commands only.
  - Verify: the allowlist difference and protected-directory diff are empty.


## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | Not run; this is a bounded reporting-only change. |
| Codex Review | `/codex review` | Independent 2nd opinion | 1 | ISSUES FOUND | 7 findings: 5 folded, 2 rejected with explicit rationale. |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | CLEAR | 9 issues, 0 critical gaps, all accepted decisions folded. |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | Not applicable; no UI scope. |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | Not required for the existing reporting command. |

- **CODEX:** Found restore safety, lazy write ordering, exhaustive negative coverage, refs validation, and scope-whitelist gaps; all five are folded.
- **CROSS-MODEL:** Both reviews agreed on fail-loud derivation and safe generation. Local claim-formal revalidation and a worklist-only CLI mode were rejected in favor of the existing byte-exact corpus freshness guard and single manifest-driven command.
- **VERDICT:** ENG CLEARED — ready to implement.

NO UNRESOLVED DECISIONS