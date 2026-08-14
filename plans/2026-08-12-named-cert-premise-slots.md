# lara-syntax@0.6 Named Certificate Premise Slots Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use `subagent-driven-development` (recommended) or `executing-plans` to implement this plan task-by-task. Use `test-driven-development` for every behavior change and `verification-before-completion` before reporting completion. Track each checkbox as work proceeds.
>
> **Status:** DESIGN PROPOSED — resolves the #105 design blocker. Do not execute until the researcher approves the design decisions in §3 (in particular D1, the nd@1 exclusion, and D9, the `lara-syntax@0.6` version bump).

**Goal:** Let a hand-authored `ord@1` or `ra@1` certificate cite a premise by source name — `(prem e4)` instead of `(prem 0)` — and lower it to the byte-identical numeric payload before the checker, failing unknown, ambiguous, duplicate, or non-premise references at elaboration time instead of replay time.

**Architecture:** `Cert` stays an opaque backend-owned S-expression: the elaborator never learns any backend's grammar. Instead, each *flat-payload* backend exports one `SlotSchema` datum — its payload head keyword, arity, and which argument positions are premise references — and a new closed presentation-side registry (`Lara.Elaborate.CertSlots`) rewrites exactly those positions, resolving names against the argument's already-resolved premise sequence with the `lara-syntax@0.5` reference namespace and collision policy. Payloads with no matching schema (including every `nd@1` certificate) pass through byte-identical. The wire `Unit` always carries numeric slots, so `.core.sexp` behavior, replay identity, checker acceptance, and frozen artifact bytes are all unchanged.

**Tech stack:** Haskell/GHC 9.6+, hspec + QuickCheck, Lean 4.32.0/Lake, the existing `Lara.Strict.Cell` wire sub-grammar, `Lara.Elaborate.Internal`, `AxCheck.lean`, presentation-parity tooling, and the differential/replay gates.

## Global Constraints

- No frozen byte changes: `corpus-units/`, `fixtures/`, `measurements/frozen/`, `bundles/`, `examples/*.core.sexp`, and committed goldens must be byte-identical after every task (`git status` clean outside the files this plan names).
- No change to checker acceptance, canonical backend payloads, replay identity, or raw `.core.sexp` behavior. Pre-checker tamper rejection is preserved.
- Lean proofs stay `sorry`-free within the standard axiom trio (`propext`, `Classical.choice`, `Quot.sound`); `AxCheck.lean` covers every new theorem.
- Closed sum types and one spelling table per vocabulary (project `CLAUDE.md`): backend head keywords are reused from each backend's existing `tagToString` table, never re-spelled as fresh string literals.
- `make presentation-parity` must keep reporting PASS; this plan adds **no** presentation-AST constructors, so the row count stays at its current value (73).
- Conventional Commits; one reviewable PR for the whole track, committed task by task. The `resolveArgRef`→`refMatches` refactor and the Task 6 Step 3b staleness fixes each land as their **own** standalone commits inside the PR (never folded into a feature commit), so every diff stays independently reviewable.

---

## 1. Background

A strict `.lara` argument may carry an opaque certificate. The surface line (grammar App. A.1) is:

```lara
arg a1 : supports(c04a) by rational_drop_recheck(kurtosis_salience, apt_llama2_7b, openllm_avg, e03, 50, 38.1, 0.238, 0.05)
  assurance = cert(ra@1, sha256:corpus-v1-ra-theory-0, (radrop (prem 0) (prem 1) (frac 119 500)))
```

(`corpus-units/adaptive-pruning/C04/unit.lara:91-92` — the one hand-authored certificate in the frozen corpus.)

The payload after the second comma is captured verbatim by `Lara.Syntax.sexpLitP` (`src/Lara/Syntax.hs:1591`) as a raw `SExpr` and stored in `Cert.certPayload` (`src/Lara/AST.hs:496-502`), whose Haddock says "this type never inspects it." Only the named backend decodes it at check/replay time, through the closed registry seam in `src/Lara/Strict.hs` (`strictCheck`, `Registry`, LCF-sealed `StrictJudgment`).

The three registered backends have these payload grammars:

| backend | payload grammar | premise references |
|---|---|---|
| `ord@1` | `(ordcmp (prem N) (prem M))` — `src/Lara/Strict/Ord.hs:143` | positions 0 and 1, flat |
| `ra@1` | `(radrop (prem N) (prem M) (frac P Q))` — `src/Lara/Strict/RA.hs:15` | positions 0 and 1, flat; position 2 is a witness fraction |
| `nd@1` | `(hyp N) \| (lam FORMULA CERT) \| (app CERT CERT) \| (abort FORMULA CERT)` — `src/Lara/Strict/ND.hs:319` | de Bruijn indices; `hyp i` counts locally bound `lam` assumptions first (innermost first, `src/Lara/Strict/ND.hs:264-290`), then the free context — premises, then theory entries (`:396`, `:412-414`) — shifting under binders |

The `(prem N)` sub-grammar is shared and lives in exactly one place: `Lara.Strict.Cell` (`Tag`/`tagToString`/`decodeSlot`, `src/Lara/Strict/Cell.hs:70-93`), with `parseCanonicalNat` defining canonical slot numerals (digits only, no leading zeros).

Premise slot order is fixed by the rule's declared premise order: `resolvePremises` (`src/Lara/Elaborate/Internal.hs:545-573`) maps `rulePremises` in order to a resolved `[SupportTerm]`, and `strictCheck`'s premise list fixes the 0-based `PremiseSlot` indices (`src/Lara/Strict.hs:186`). Both elaboration paths end with the resolved premise list in hand before assurance is attached:

- explicit path: `elabTerm`'s `SRule` case, `src/Lara/Elaborate/Internal.hs:440-457` ("lower assurance verbatim");
- inferred path (`lara-syntax@0.5` `by r from [...]`): `elabInstantiation`'s `InferTheta` case, `src/Lara/Elaborate/Internal.hs:420-424`.

Prior art this plan builds on:

- `lara-syntax@0.4` (PR #103) deliberately restricted value substitution to typed `Term` fields — `Lara.Elaborate.ValueBinding` contains zero references to `Cert`. That boundary is the design constraint, not an omission.
- `lara-syntax@0.5` (PR #106) established the reference namespace and collision policy this plan reuses: `resolveArgRef` (`src/Lara/Elaborate/Internal.hs:459-488`) resolves a bare name against declared leaves and prior arguments, with a leaf/argument collision a hard `ThetaReferenceAmbiguous` error.
- `rulePremiseLabels` (`src/Lara/AST.hs:328`) is the precedent for presentation-only data that provably never reaches the wire.

## 2. Motivation

Numeric slots make the author recover backend slot order from policy declarations. The trap is live in the tree: `ord-v1` puts the **baseline** cell in slot 0 (`examples/S2/ord-v1.policy.lara:63`) while `ord-ppl-v1` puts the **system** cell in slot 0 (`examples/S5/ord-ppl-v1.policy.lara:65-66`) — deliberate mirror images. An author who transposes two indices learns about it only at replay, as an opaque R13 backend rejection, the worst place for a spelling-level mistake to surface (#105: "a swap reaches replay as an R13 rejection rather than a source-level name error").

The fix cannot be a generic substitution pass over certificate payloads — that would make `Lara.Elaborate` understand backend grammars and violate the opaque-`Cert` layer contract. #105 requires a presentation layer above `Cert` that lowers symbolic references to the backend's canonical numeric payload while keeping backend extensibility closed and deterministic.

## 3. Design decisions

This section is the resolution of #105's "required decision before implementation." Each decision is numbered for review.

**D1 — Supported backends: `ord@1` and `ra@1`. `nd@1` is excluded.**
`ord@1` and `ra@1` payloads are single flat head applications with premise references at fixed argument positions — a name is a stable notion there. `nd@1` payloads are recursive de Bruijn proof terms: `hyp i` shifts under `lam` binders and conflates premise slots with theory entries by offset (`src/Lara/Strict/ND.hs:412-414`), so "the premise named `e4`" is not well-defined at a fixed payload position without teaching the presentation layer the full ND grammar and binder discipline. `nd@1` certificates therefore pass through byte-identical, keep numeric `hyp` indices, and are recorded as future work (a de Bruijn-aware named form is a separate design). This satisfies #105's "which backends and certificate constructors admit named slots" with an explicit, closed answer.

*Future-work pointer:* when a named `nd@1` form is designed, start from Lean 4's kernel/surface split rather than inventing new machinery — the kernel term stays de Bruijn (`hyp i`), the presentation writes named binders (`(lam h FORMULA CERT)` with `h` bound in `CERT`, and premise/theory slots cited by source name), and the elaborator owns the index shifting, exactly as Lean's elaborator lowers `fun h => … h …` to bound-variable indices. The locally-nameless literature covers the metatheory of that lowering.

**D2 — The schema, not the grammar, crosses the layer boundary.**
A new datum in `Lara.Strict.Cell` (the existing shared home of the `(prem N)` sub-grammar):

```haskell
data SlotSchema = SlotSchema
  { ssBackend :: BackendId  -- Lara.Strict.BackendId: name + version
  , ssHead :: String        -- payload head keyword, from the backend's tag table
  , ssArity :: Int          -- argument count after the head
  , ssRefSlots :: [Int]     -- 0-based argument positions that are premise references
  }
```

Each supported backend exports its own schema value built from its own spelling tables (`Ord.slotSchema` uses `tagToString TOrdcmp` and `ordBackendId`; `RA.slotSchema` likewise). The closed aggregate list lives in the new `Lara.Elaborate.CertSlots`. The elaborator is generic over `SlotSchema`; it never pattern-matches a backend grammar beyond "head keyword + arity + positions." Extensibility stays closed and deterministic: adding a backend to the presentation layer means exporting one schema value and appending it to one list, both in code, never from an artifact.

**D3 — Symbolic form and namespace.**
At a declared reference position, a payload node `(prem s)` is *symbolic* iff `s` is not a canonical natural (`parseCanonicalNat s == Nothing`). Symbolic names resolve in the `lara-syntax@0.5` reference namespace: declared leaves ∪ prior arguments, with a leaf/argument collision a **hard error** — deliberately aligned with `resolveArgRef`, not with `resolveDischarges`' silent leaf preference (that inconsistency is the separate TODOS item "Discharge-witness namespace shadowing," untouched here).

*Alternative considered — rule premise labels (deferred).* `premiseLabelIndex` (`src/Lara/Elaborate/Internal.hs:315`) already maps a rule's declared premise labels to slot indices, and a label names the backend slot directly — it would even cover the D4 multi-slot case where this design falls back to numerals. Deferred for `lara-syntax@0.6` because: labels are optional (`rulePremiseLabels :: [Maybe PremiseLabel]`), so they cannot be the universal namespace; #105 frames the requirement as source leaf/prior-argument names; and a second symbolic class would need its own collision policy against leaves and priors, growing exactly the resolution surface this feature is supposed to keep predictable. Premise-label citation remains a natural future `lara-syntax@0.x` extension — record it in Appendix E's future-work note alongside D1's nd@1 pointer.

**D4 — Name → slot mapping.**
A resolved referent (a leaf's `SLeaf` or a prior argument's elaborated term) is located in the argument's resolved premise sequence by term equality. Exactly one occupied slot → that 0-based index. Zero slots → error (the referent is real but not among this argument's premises). Two or more slots (the same leaf feeding two premises) → error; the author must cite numeric slots there. This maps names to "the exact premise sequence consulted by replay" (#105) because that sequence *is* the resolved premise list handed to `strictCheck`.

*Representation rule:* `locate` must match whatever representation the author's spelling actually put in the resolved premise sequence. Task 3 verifies `elabTerm`'s `SLeaf` case: if the **explicit** spelling stores a prior-argument premise as its bare `SLeaf` spelling rather than the argument's elaborated term, the resolver must locate that representation too — a citation must never succeed under `by r from […]` and fail with a spurious `CertSlotNotAPremise` under the explicit spelling of the same argument. The explicit/inferred twin tests prove both spellings lower identically.

**D5 — Mixed symbolic/numeric forms are legal.**
Each reference position lowers independently. `(radrop (prem e4) (prem 1) (frac 119 500))` is well-formed if `e4` resolves to slot 0's premise.

**D6 — Declared references lower; backend-owned nodes pass through byte-identical.**
At a matched schema, only declared reference positions are interpreted.
Canonical numeric slots, non-`(prem …)` nodes at reference positions, and
every non-reference position remain backend-owned and reach replay unchanged.
This includes symbolic-looking `(prem s)` nodes outside the declared positions.
A head-keyword or arity mismatch under a **schema'd** backend also passes
through unless the payload contains a symbolic `(prem s)` anywhere. No
declared reference positions exist under a mismatch, so such a spelling cannot
be lowered; it fails at elaboration as `CertSlotSchemaMismatch`. Detection is
a generic sub-tree scan, and the elaborator still learns no backend grammar.
Every accepted frozen artifact still lowers to itself. Rejection paths move
only for spelling mistakes at declared positions and symbolic references in
schema-mismatched payloads.

**D7 — Round-trip preserves the authored presentation, with zero parser changes.**
`sexpLitP` already accepts `(prem e4)` — an identifier is a valid `SExpr` atom — and the printer (`src/Lara/Syntax.hs:1853`) prints the stored payload verbatim. The surface AST keeps the authored spelling; lowering happens only in elaboration. `parse ∘ print = id` on the presentation holds with no grammar change.

**D8 — Lowering site and invariants.**
One helper runs at both elaboration sites *after* premise resolution: the
explicit `SRule` case and the `InferTheta` case. Every schema-declared
reference position in the wire `Unit` therefore carries a numeric slot.
Symbolic and numeric authoring of the same argument produce byte-identical
`Cert` payloads and encoded `Unit`s (Task 4 proves this; Task 5 mechanizes the
payload half). Nodes outside declared positions remain backend-owned, so the
raw-door and tamper contracts are unchanged.

*Recursion:* the explicit site is recursive. `elabTerm` maps itself over
explicit premises, and a nested `SRule` premise may carry its own
`AssuranceCert` at the AST level. Lowering applies at every `SRule` depth,
resolving declared reference positions against that node's own resolved
premise list and attributing diagnostics to the enclosing argument's `ArgId`.
Task 3 pins this behavior with an AST-level fixture because the surface grammar
cannot yet express a nested assurance.

```
authored .lara                          elaboration (Lara.Elaborate.Internal)
──────────────                          ─────────────────────────────────────
assurance = cert(ord@1, sha256:…,       explicit SRule case      InferTheta case
  (ordcmp (prem e4) (prem 1)))          (Internal.hs:440)        (Internal.hs:420)
        │                                     │                        │
   sexpLitP (Syntax.hs:1591)                  └── prems resolved ──────┘
        │  verbatim capture                              │
        ▼                                                ▼
  Cert{certPayload :: SExpr}  ─────────────────▶  lowerArgCert
  (opaque, backend-owned)                         (AssuranceCert only;
                                                   None/Trusted pass through)
                                                         │
                                                         ▼
                                        lowerCertPayload + certSlotResolver
                                          │ no schema match, no symbolic (prem s)
                                          │ (nd@1, unknown backend, ────▶ payload byte-identical
                                          │  wrong head/arity)            (reaches backend as today)
                                          │ schema'd backend, mismatched payload
                                          │  WITH symbolic (prem s) ─▶ Left CertSlotSchemaMismatch
                                          │ (prem s), s symbolic ─▶ resolve s vs leaves∪priors,
                                          │     │                   locate in resolved prems
                                          │     ├ ok ────▶ rewrite to (prem N)
                                          │     └ fail ──▶ Left CertSlot* (ElabError,
                                          ▼                rejected before the checker)
                                    Unit: declared references numeric;
                                          other payload nodes backend-owned
                                                         │
                                                         ▼
                                 encode (.core.sexp) → replay → strictCheck (Strict.hs:180)
                                 bytes identical to hand-numeric authoring (Task 4/Task 5)
```

The same diagram ships in the `Lara.Elaborate.CertSlots` module haddock (Task 2), so the layer story travels with the code that must preserve it.

**D9 — Presentation version: `lara-syntax@0.6`.**
New authoring capability on the verified surface → version bump, documented as Appendix E of `docs/lara-surface-grammar.md` (the @0.4/@0.5 precedent), with the `docs/spec.md` and `docs/mechanization-plan.md` presentation-version pointers updated. The frozen `lara-core@0.2` boundary is untouched.

**D10 — Mechanization scope.**
The payload rewrite is frozen, corpus-independent math once D1–D6 are fixed, so per the mechanization discipline it lands in Lean alongside the Haskell: `lean/Lara/CertSlots.lean` defines the schemas and `lowerPayload` over an abstract resolver `ρ : String → Option Nat`, with two theorems — identity on non-symbolic payloads (byte preservation) and symbolic-equals-hand-written-numeric (the #105 verification target). Name *resolution* (leaf/prior lookup against `Env`) is elaborator logic covered by Haskell tests, the same cut result 12 makes. The presentation-parity guard is unaffected: no AST shape changes, and the guard's documented `Cert` native-payload exemption stands.

### Error family (D6 diagnostics)

Six new `ElabError` constructors carry the backend identity, version, and
reference as structured values. The renderer alone constructs the backend
spelling `name ++ "@" ++ show version`:

| constructor | rendering |
|---|---|
| `CertSlotUnresolved ArgId BackendId Int ArgRef` | `arg 'A': certificate 'B' premise reference 'N' names neither a declared leaf nor prior argument` |
| `CertSlotAmbiguous ArgId BackendId Int ArgRef` | `arg 'A': certificate 'B' premise reference 'N' is ambiguous between a declared leaf and a prior argument` |
| `CertSlotNotAPremise ArgId BackendId Int ArgRef` | `arg 'A': certificate 'B' premise reference 'N' does not resolve to any of this argument's premise slots` |
| `CertSlotMultiSlot ArgId BackendId Int ArgRef Int Int` | `arg 'A': certificate 'B' premise reference 'N' occupies premise slots I and J; cite a numeric slot` |
| `CertSlotNonCanonicalNumeral ArgId BackendId Int ArgRef` | `arg 'A': certificate 'B' premise reference 'N' is not a canonical slot numeral (use unsigned decimal with no leading zeros); write the canonical numeral or a source name` |
| `CertSlotSchemaMismatch ArgId BackendId Int ArgRef` | `arg 'A': certificate 'B' payload does not match the backend's premise-reference schema but contains symbolic premise reference 'N'` |

## 4. File map

| file | change |
|---|---|
| `src/Lara/Strict/Cell.hs` | Add `SlotSchema` (+ export). ~25 lines. |
| `src/Lara/Strict/Ord.hs` | Export `slotSchema :: SlotSchema`. ~8 lines. |
| `src/Lara/Strict/RA.hs` | Export `slotSchema :: SlotSchema`. ~8 lines. |
| `src/Lara/Elaborate/CertSlots.hs` | **New.** Closed schema registry + pure `lowerCertPayload` incl. the D6 dead-wire scan. ~150 lines. |
| `src/Lara/Elaborate/Error.hs` | Six `CertSlot*` constructors + renderings (D6 table). |
| `src/Lara/AST.hs` | `Cert`/`certPayload` opacity Haddock amended with the presentation-lowering carve-out (OV-5). |
| `src/Lara/Elaborate/Internal.hs` | Shared `refMatches` helper (also adopted by `resolveArgRef`), `certSlotResolver`, `lowerArgCert`, wiring at the two sites. ~55 lines. |
| `lara.cabal` | Register `Lara.Elaborate.CertSlots`; register `CertSlotsSpec`. |
| `test/CertSlotsSpec.hs` | **New.** Unit + property + end-to-end twins. |
| `test/Spec.hs` | Register `CertSlotsSpec`. |
| `examples/S6/` (or next free S-number) | **New.** Symbolic worked example: policy + program + `.core.sexp` golden (Task 4b). |
| `src/Lara/WorkedExamples.hs` | Registry entry for the symbolic example (Task 4b). |
| `lean/Lara/CertSlots.lean` | **New.** Schemas, `lowerPayload` (incl. dead-wire rule), `#guard` vectors, two theorems. |
| `lean/AxCheck.lean` | `#print axioms` entries for the new theorems (verified home; run via `lake env lean AxCheck.lean`). |
| `docs/lara-surface-grammar.md` | Header → `lara-syntax@0.6`; Appendix E. |
| `docs/spec.md`, `docs/mechanization-plan.md` | Presentation-version pointer bumps. |
| `docs/rejection-surface.md` | Moved-rejection-site note only (source-boundary door + R13 row); the `CertSlot*` family list lives in Appendix E. |
| `lean/Lara.lean` | `import Lara.CertSlots` root registration (Task 5). The "72-row" → 73 staleness fix at `:13` is owned by Task 6 Step 3b only. |
| `TODOS.md` | Move the #105 entry to Completed at close-out; bundled staleness fix "72 rows" → 73 in the parity-guard completed entry (Task 6 Step 3b). |

Not touched: `Lara.Syntax` (parser/printer), `Lara.Wire`, `Lara.Check`, `Lara.Replay`, all `Lara.Strict` decoders and `runBackend`s, `Lara.Elaborate.ValueBinding`, everything under `corpus-units/`, `fixtures/`, `measurements/`, `bundles/`, `examples/`.

---

## 5. Tasks

### Task 1: `SlotSchema` in the shared wire-convention module, exported by each flat backend

**Files:**
- Modify: `src/Lara/Strict/Cell.hs` (type + export)
- Modify: `src/Lara/Strict/Ord.hs`, `src/Lara/Strict/RA.hs` (schema values + exports)
- Test: `test/CertSlotsSpec.hs` (new), `test/Spec.hs`, `lara.cabal`

**Interfaces:**
- Produces: `Lara.Strict.Cell.SlotSchema (..)` with fields `ssBackend :: Lara.Strict.BackendId`, `ssHead :: String`, `ssArity :: Int`, `ssRefSlots :: [Int]`; `Lara.Strict.Ord.slotSchema :: SlotSchema`; `Lara.Strict.RA.slotSchema :: SlotSchema`.

- [ ] **Step 1: Write the failing test.** Create `test/CertSlotsSpec.hs` with schema well-formedness assertions; register the module in `test/Spec.hs` and in the test-suite stanza of `lara.cabal` exactly as `ThetaInferenceSpec` is registered.

```haskell
module CertSlotsSpec (spec) where

import Test.Hspec
import Lara.Strict (BackendId (..))
import Lara.Strict.Cell (SlotSchema (..))
import qualified Lara.Strict.Ord as Ord
import qualified Lara.Strict.RA as RA

spec :: Spec
spec = describe "SlotSchema" $ do
  it "ord@1 schema matches the ordcmp wire grammar" $ do
    ssBackend Ord.slotSchema `shouldBe` BackendId "ord" 1
    ssHead Ord.slotSchema `shouldBe` "ordcmp"
    ssArity Ord.slotSchema `shouldBe` 2
    ssRefSlots Ord.slotSchema `shouldBe` [0, 1]
  it "ra@1 schema matches the radrop wire grammar" $ do
    ssBackend RA.slotSchema `shouldBe` BackendId "ra" 1
    ssHead RA.slotSchema `shouldBe` "radrop"
    ssArity RA.slotSchema `shouldBe` 3
    ssRefSlots RA.slotSchema `shouldBe` [0, 1]
  it "every declared reference slot is inside the payload arity" $
    mapM_
      (\s -> all (< ssArity s) (ssRefSlots s) `shouldBe` True)
      [Ord.slotSchema, RA.slotSchema]
```

(If `Lara.Strict.BackendId` is constructed with record syntax in the tree, spell the expected values the same way.)

- [ ] **Step 2: Run to verify failure.** `cabal test --test-options='--match SlotSchema'` — expected: compile failure, `SlotSchema` not in scope.

- [ ] **Step 3: Implement.** In `src/Lara/Strict/Cell.hs`, after the `decodeSlot` block, add and export:

```haskell
-- | Where premise slot references sit in one backend's certificate payload:
-- presentation-layer data about a __flat__ wire grammar (a single head-keyword
-- application of fixed arity with references at fixed argument positions).
-- A backend whose payload is not of this shape — nd\@1's recursive de Bruijn
-- proof terms, whose @hyp@ indices shift under binders and conflate premise
-- and theory slots by offset — simply exports no schema, and its payloads
-- pass through the presentation lowering byte-identical.
data SlotSchema = SlotSchema
  { ssBackend :: BackendId -- ^ which registered backend this schema presents
  , ssHead :: String -- ^ payload head keyword, from the backend's tag table
  , ssArity :: Int -- ^ argument count after the head
  , ssRefSlots :: [Int] -- ^ 0-based argument positions that are premise refs
  }
  deriving (Eq, Show)
```

Import `BackendId` from `Lara.Strict` (the module already imports `SExpr` from there). In `src/Lara/Strict/Ord.hs`, next to `ordBackendId` (`src/Lara/Strict/Ord.hs:215`):

```haskell
-- | The @ord\@1@ premise-reference schema: @(ordcmp (prem N) (prem M))@,
-- both positions premise references. Spellings come from this module's own
-- tag table and identity — the schema introduces no new strings.
slotSchema :: SlotSchema
slotSchema =
  SlotSchema
    { ssBackend = ordBackendId
    , ssHead = tagToString TOrdcmp
    , ssArity = 2
    , ssRefSlots = [0, 1]
    }
```

In `src/Lara/Strict/RA.hs`, the same shape against its own `raBackendId`-equivalent and tag table: head `tagToString TRadrop`, arity 3, refs `[0, 1]`. Export `slotSchema` from both modules and `SlotSchema (..)` from `Cell`.

- [ ] **Step 4: Run to verify pass.** `cabal test --test-options='--match SlotSchema'` — expected: PASS.

- [ ] **Step 5: Commit.** `git add -A && git commit -m "feat(strict): declare flat-payload premise-reference schemas (ord@1, ra@1)"`

### Task 2: the pure lowering pass — `Lara.Elaborate.CertSlots`

**Files:**
- Create: `src/Lara/Elaborate/CertSlots.hs`
- Modify: `lara.cabal` (register module)
- Test: `test/CertSlotsSpec.hs`

**Interfaces:**
- Consumes: Task 1's `SlotSchema`, `Ord.slotSchema`, `RA.slotSchema`; `Lara.Strict.Cell.parseCanonicalNat`, `.Tag (TPrem)`, `.tagToString`; `Lara.AST.Cert (..)`, `Lara.AST.BackendId (..)` (the name-only presentation newtype, distinct from `Lara.Strict.BackendId`).
- Produces:

```haskell
data SlotRefError
  = SlotNameUnresolved
  | SlotNameAmbiguous
  | SlotNameNotAPremise
  | SlotNameMultiSlot Int Int
  | SlotNonCanonicalNumeral -- ^ cannot begin a source identifier, e.g. @007@ or @-1@ (OV-8)
  | SlotSchemaMismatch -- ^ symbolic name in a schema-mismatched payload (OV-3)
  deriving (Eq, Show)

slotSchemas :: [SlotSchema]

lowerCertPayload
  :: (String -> Either SlotRefError Int) -- ^ name -> 0-based premise slot
  -> Cert
  -> Either (String, SlotRefError) Cert -- ^ Left: (offending name, why)
```

- [ ] **Step 1: Write the failing tests** in `test/CertSlotsSpec.hs`. Use a fixed test resolver:

```haskell
  describe "lowerCertPayload" $ do
    let res "e1" = Right 0
        res "e2" = Right 1
        res "dup" = Left (SlotNameMultiSlot 0 1)
        res "off" = Left SlotNameNotAPremise
        res "both" = Left SlotNameAmbiguous
        res _ = Left SlotNameUnresolved
        ord p = Cert (BackendId "ord") 1 (TheoryDigest "sha256:t") p
        prem s = SList [SAtom "prem", SAtom s]

    it "lowers symbolic ord refs to numeric slots" $
      lowerCertPayload res (ord (SList [SAtom "ordcmp", prem "e1", prem "e2"]))
        `shouldBe` Right (ord (SList [SAtom "ordcmp", prem "0", prem "1"]))

    it "accepts mixed symbolic/numeric positions" $
      lowerCertPayload res (ord (SList [SAtom "ordcmp", prem "e1", prem "1"]))
        `shouldBe` Right (ord (SList [SAtom "ordcmp", prem "0", prem "1"]))

    it "leaves numeric payloads untouched" $ do
      let p = ord (SList [SAtom "ordcmp", prem "0", prem "1"])
      lowerCertPayload res p `shouldBe` Right p

    it "rejects non-canonical numerals with the dedicated error (moves R13 forward)" $ do
      lowerCertPayload res (ord (SList [SAtom "ordcmp", prem "007", prem "1"]))
        `shouldBe` Left ("007", SlotNonCanonicalNumeral)
      lowerCertPayload res (ord (SList [SAtom "ordcmp", prem "00", prem "1"]))
        `shouldBe` Left ("00", SlotNonCanonicalNumeral)

    it "reports each resolver failure with the offending name" $ do
      lowerCertPayload res (ord (SList [SAtom "ordcmp", prem "nope", prem "1"]))
        `shouldBe` Left ("nope", SlotNameUnresolved)
      lowerCertPayload res (ord (SList [SAtom "ordcmp", prem "both", prem "1"]))
        `shouldBe` Left ("both", SlotNameAmbiguous)
      lowerCertPayload res (ord (SList [SAtom "ordcmp", prem "off", prem "1"]))
        `shouldBe` Left ("off", SlotNameNotAPremise)
      lowerCertPayload res (ord (SList [SAtom "ordcmp", prem "dup", prem "1"]))
        `shouldBe` Left ("dup", SlotNameMultiSlot 0 1)

    it "passes ra@1 witness fractions through while lowering its two refs" $ do
      let ra p = Cert (BackendId "ra") 1 (TheoryDigest "sha256:t") p
          frac = SList [SAtom "frac", SAtom "119", SAtom "500"]
      lowerCertPayload res (ra (SList [SAtom "radrop", prem "e1", prem "e2", frac]))
        `shouldBe` Right (ra (SList [SAtom "radrop", prem "0", prem "1", frac]))

    it "passes schema-less and symbolic-free mismatched payloads through byte-identical" $ do
      -- nd@1 has no schema; unknown backends have no schema; wrong head or
      -- arity under a schema'd backend passes through ONLY when no symbolic
      -- (prem s) occurs anywhere (D6 dead-wire rule).
      let nd = Cert (BackendId "nd") 1 (TheoryDigest "sha256:t")
                 (SList [SAtom "app", SList [SAtom "hyp", SAtom "0"], SList [SAtom "hyp", SAtom "1"]])
          wrongHeadNumeric = ord (SList [SAtom "ordcmp2", prem "0", prem "1"])
          wrongArityNumeric = ord (SList [SAtom "ordcmp", prem "0"])
          notAList = ord (SAtom "opaque")
      mapM_ (\c -> lowerCertPayload res c `shouldBe` Right c)
        [nd, wrongHeadNumeric, wrongArityNumeric, notAList]

    it "rejects symbolic names inside schema-mismatched payloads of a schema'd backend" $ do
      -- A symbolic name is never valid wire, so pass-through is never
      -- correct here (D6 / OV-3); nd@1 and unknown backends stay exempt.
      let wrongHeadSym = ord (SList [SAtom "ordcmp2", prem "e1", prem "e2"])
          wrongArraySym = ord (SList [SAtom "ordcmp", prem "e1"])
          nestedSym = ord (SList [SAtom "ordcmp2", SList [SAtom "wrap", prem "e9"]])
      lowerCertPayload res wrongHeadSym `shouldBe` Left ("e1", SlotSchemaMismatch)
      lowerCertPayload res wrongArraySym `shouldBe` Left ("e1", SlotSchemaMismatch)
      lowerCertPayload res nestedSym `shouldBe` Left ("e9", SlotSchemaMismatch)
      let ndSym = Cert (BackendId "nd") 1 (TheoryDigest "sha256:t")
                    (SList [SAtom "app", SList [SAtom "hyp", SAtom "0"], prem "x"])
      lowerCertPayload res ndSym `shouldBe` Right ndSym -- no schema for nd@1 at all

    it "leaves a non-(prem …) node at a reference position for the backend" $ do
      let odd' = ord (SList [SAtom "ordcmp", SAtom "junk", prem "1"])
      lowerCertPayload res odd' `shouldBe` Right odd'

    it "never rewrites AssuranceNone/AssuranceTrusted paths (type-level: takes Cert only)" $
      True `shouldBe` True -- documented: the wrapper in Task 3 owns that dispatch
```

Add a QuickCheck property with a bounded `SExpr` generator `boundedSExpr :: Gen SExpr` defined in the test (max depth 3, atoms drawn from `["prem","ordcmp","radrop","frac","0","1","2","007","x"]`) — use `forAll`, **not** `property $ \p ->`, which would require an orphan `Arbitrary SExpr` instance:

```haskell
    it "is the identity on any payload containing no symbolic (prem s) anywhere" $
      forAll boundedSExpr $ \p ->
        let c = Cert (BackendId "ord") 1 (TheoryDigest "sha256:t") p
         in noSymbolicRef p ==> lowerCertPayload res c === Right c
```

where `noSymbolicRef` is the generic scan (no `(prem s)` sub-tree with non-canonical `s` anywhere) — under the D6 dead-wire rule this is exactly the pass-through hypothesis for a schema'd backend, and it is deliberately *not* a mirror of the implementation's schema-position walk.

- [ ] **Step 2: Run to verify failure.** `cabal test --test-options='--match lowerCertPayload'` — compile failure: module missing.

- [ ] **Step 3: Implement** `src/Lara/Elaborate/CertSlots.hs`:

```haskell
-- | The presentation layer above the opaque certificate (#105,
-- lara-syntax@0.6). 'Cert' payloads stay backend-owned S-expressions; this
-- pass rewrites __only__ the premise-reference positions each flat backend
-- declares in its 'SlotSchema', lowering symbolic source names to the
-- backend's canonical 0-based numeric slots. Payloads with no matching
-- schema pass through byte-identical, so every frozen artifact and every
-- existing rejection path is preserved.
--
-- (Reproduce the D8 lowering-pipeline ASCII diagram from the plan here
-- verbatim — authored payload → elaboration sites → lowerCertPayload with
-- pass-through and CertSlot* exits → numeric wire Unit → strictCheck — so
-- the layer story travels with this module.)
module Lara.Elaborate.CertSlots
  ( SlotRefError (..)
  , slotSchemas
  , lowerCertPayload
  ) where

import Control.Monad (zipWithM)

import Lara.AST (BackendId (..), Cert (..))
import Lara.Strict (SExpr (..))
import qualified Lara.Strict as Strict
import Lara.Strict.Cell (SlotSchema (..), Tag (TPrem), parseCanonicalNat, tagToString)
import qualified Lara.Strict.Ord as Ord
import qualified Lara.Strict.RA as RA

-- | Why one symbolic premise reference failed to lower (rendered with its
-- argument context by "Lara.Elaborate.Error").
data SlotRefError
  = SlotNameUnresolved
  | SlotNameAmbiguous
  | SlotNameNotAPremise
  | SlotNameMultiSlot Int Int
  deriving (Eq, Show)

-- | The closed presentation-side schema registry. nd@1 exports no schema:
-- its recursive de Bruijn payload has no fixed premise-reference positions.
slotSchemas :: [SlotSchema]
slotSchemas = [Ord.slotSchema, RA.slotSchema]

-- | Lower the symbolic premise references of one certificate, or return it
-- untouched when no schema matches (unknown backend, head, or arity).
lowerCertPayload
  :: (String -> Either SlotRefError Int)
  -> Cert
  -> Either (String, SlotRefError) Cert
lowerCertPayload resolve cert@(Cert (BackendId b) v _ payload) =
  case matchSchema b v payload of
    Nothing
      -- D6 dead-wire rule: under a schema'd backend, a symbolic name in a
      -- payload that fails schema match can never be valid wire — reject it
      -- at elaboration instead of leaking a guaranteed R13 to replay.
      | backendHasSchema b v
      , Just s <- firstSymbolicRef payload ->
          Left (s, SlotSchemaMismatch)
      | otherwise -> Right cert
    Just (schema, h, args) -> do
      args' <- zipWithM (lowerAt schema resolve) [0 ..] args
      pure cert {certPayload = SList (SAtom h : args')}

-- | Does any registered schema present this backend\@version at all?
backendHasSchema :: String -> Int -> Bool
backendHasSchema b v =
  any
    ( \s ->
        Strict.backendName (ssBackend s) == b
          && Strict.backendVersion (ssBackend s) == v
    )
    slotSchemas

-- | The first symbolic @(prem s)@ anywhere in a payload — a generic
-- sub-tree scan, no backend grammar knowledge.
firstSymbolicRef :: SExpr -> Maybe String
firstSymbolicRef e = case e of
  SList [SAtom k, SAtom s]
    | k == tagToString TPrem, Nothing <- parseCanonicalNat s -> Just s
  SList es -> foldr ((<|>) . firstSymbolicRef) Nothing es
  _ -> Nothing

-- | The schema whose backend identity, head keyword, and arity all match —
-- anything less specific is not presented and passes through.
matchSchema :: String -> Int -> SExpr -> Maybe (SlotSchema, String, [SExpr])
matchSchema b v (SList (SAtom h : args)) =
  case [ s | s <- slotSchemas
       , Strict.backendName (ssBackend s) == b
       , Strict.backendVersion (ssBackend s) == v
       , ssHead s == h
       , ssArity s == length args
       ] of
    [s] -> Just (s, h, args)
    _ -> Nothing
matchSchema _ _ _ = Nothing

-- | Rewrite one payload argument: only a @(prem s)@ with non-canonical @s@
-- at a declared reference position is symbolic; everything else is the
-- backend's to accept or reject, byte-identical.
lowerAt
  :: SlotSchema
  -> (String -> Either SlotRefError Int)
  -> Int
  -> SExpr
  -> Either (String, SlotRefError) SExpr
lowerAt schema resolve i e
  | i `elem` ssRefSlots schema
  , SList [SAtom k, SAtom s] <- e
  , k == tagToString TPrem
  , Nothing <- parseCanonicalNat s =
      if not (startsSourceIdentifier s)
        then Left (s, SlotNonCanonicalNumeral)
        else case resolve s of
          Right slot -> Right (SList [SAtom k, SAtom (show slot)])
          Left err -> Left (s, err)
  | otherwise = Right e

startsSourceIdentifier :: String -> Bool
startsSourceIdentifier (c : _) = isAlpha c || c == '_'
startsSourceIdentifier [] = False
```

(Imports: `Control.Applicative ((<|>))`, `Data.Char (isAlpha)` join the list
shown above.) Register `Lara.Elaborate.CertSlots` in the library stanza of
`lara.cabal`.

- [ ] **Step 4: Run to verify pass.** `cabal test --test-options='--match lowerCertPayload'` and `--match SlotSchema` — PASS.

- [ ] **Step 5: Commit.** `git commit -am "feat(elaborate): pure symbolic-slot lowering above the opaque Cert (#105)"`

### Task 3: errors, resolver, and elaborator wiring

**Files:**
- Modify: `src/Lara/Elaborate/Error.hs` (constructors after `ThetaParameterUnbound`, renderings after `src/Lara/Elaborate/Error.hs:246`)
- Modify: `src/Lara/Elaborate/Internal.hs` (resolver + wrapper + the two call sites)
- Test: `test/CertSlotsSpec.hs`

**Interfaces:**
- Consumes: Task 2's `lowerCertPayload`, `SlotRefError (..)`.
- Produces: the six `ElabError` constructors of the D6 table (`CertSlotUnresolved`, `CertSlotAmbiguous`, `CertSlotNotAPremise`, `CertSlotMultiSlot`, `CertSlotNonCanonicalNumeral`, `CertSlotSchemaMismatch`); shared namespace-lookup helper `refMatches`; internal `certSlotResolver` and `lowerArgCert` (`Lara.Elaborate.Internal` is itself the sanctioned test escape hatch, `Internal.hs:15-21`); the amended `Cert`/`certPayload` opacity Haddock in `src/Lara/AST.hs`.

- [ ] **Step 1: Write the failing rendering tests** (exact stable strings, `ThetaInferenceSpec.hs:475` pattern):

```haskell
  describe "CertSlot error family (D6)" $ do
    it "renders the four stable messages" $ do
      elabErrorMessage
        (CertSlotUnresolved (ArgId "a1") (BackendId "ord") 1 (ArgRef "e4"))
        `shouldBe` "arg 'a1': certificate 'ord@1' premise reference 'e4' names neither a declared leaf nor prior argument"
      elabErrorMessage
        (CertSlotAmbiguous (ArgId "a1") (BackendId "ord") 1 (ArgRef "x"))
        `shouldBe` "arg 'a1': certificate 'ord@1' premise reference 'x' is ambiguous between a declared leaf and a prior argument"
      elabErrorMessage
        (CertSlotNotAPremise (ArgId "a1") (BackendId "ra") 1 (ArgRef "e3"))
        `shouldBe` "arg 'a1': certificate 'ra@1' premise reference 'e3' does not resolve to any of this argument's premise slots"
      elabErrorMessage
        (CertSlotMultiSlot (ArgId "a1") (BackendId "ord") 1 (ArgRef "e1") 0 1)
        `shouldBe` "arg 'a1': certificate 'ord@1' premise reference 'e1' occupies premise slots 0 and 1; cite a numeric slot"
      elabErrorMessage
        (CertSlotNonCanonicalNumeral (ArgId "a1") (BackendId "ord") 1 (ArgRef "007"))
        `shouldBe` "arg 'a1': certificate 'ord@1' premise reference '007' is not a canonical slot numeral (use unsigned decimal with no leading zeros); write the canonical numeral or a source name"
      elabErrorMessage
        (CertSlotSchemaMismatch (ArgId "a1") (BackendId "ord") 1 (ArgRef "e4"))
        `shouldBe` "arg 'a1': certificate 'ord@1' payload does not match the backend's premise-reference schema but contains symbolic premise reference 'e4'"
```

(Use the module's actual renderer name — the function `ThetaInferenceSpec` calls `elabErrorMessage` on; keep whatever it is spelled there.)

Then write failing *behavioral* tests that drive the errors through real elaboration. Build a minimal in-test policy + program pair the way `ThetaInferenceSpec` builds its fixtures (inline sources through the public parse + elaborate entry points), with a strict rule certified by `ord@1` over two leaf premises `e1`, `e2`:

- symbolic twin elaborates and its `Unit` equals the numeric twin's `Unit` (full structural equality) — this is the elaboration-level half of the byte-identity gate;
- `(prem e9)` (undeclared) → `CertSlotUnresolved`;
- a program declaring both `leaf x` and a prior `arg x` with `(prem x)` in a later argument's certificate → `CertSlotAmbiguous`;
- `(prem e3)` where `e3` is declared but not a premise of this rule instance → `CertSlotNotAPremise`;
- a rule with the same leaf resolving two premise slots and `(prem e1)` → `CertSlotMultiSlot`;
- **prior-argument success path, both spellings (D4 representation rule):** a certificate in a later argument citing a *prior argument's* name (`(prem a1)`) lowers to that argument's premise slot — authored once via `by r from [a1, …]` and once via the explicit spelling; both must lower identically (this task first verifies `elabTerm`'s `SLeaf` case to learn which representation the explicit path stores, and `locate` matches it);
- `(prem 007)` in a well-formed payload → `CertSlotNonCanonicalNumeral`;
- a symbolic name inside a wrong-arity `ord@1` payload (`(ordcmp (prem e4))`) → `CertSlotSchemaMismatch` (D6 dead-wire rule, driven through real elaboration);
- **nested certificate (D8 recursion):** verify whether the surface grammar can express an assurance on a nested premise term; if yes, a nested symbolic cert lowers against the *nested* rule's premise list with the enclosing `ArgId` in the diagnostic; if no, record the reachability note and pin the recursive behavior with an AST-level fixture through the elaborator entry point;
- the inferred-theta spelling `by r from [e1, e2]` with a symbolic certificate lowers identically to the explicit spelling (covers the `InferTheta` site);
- **InferTheta-site error path:** an unresolved symbolic name (`(prem e9)`) authored via the inferred spelling `by r from [e1, e2]` fails with the `CertSlotUnresolved` rendering — pins that the `InferTheta` wiring site enforces the error contract, not just success identity (a dropped `lowerArgCert` call there would otherwise surface only as a replay R13).

- [ ] **Step 2: Run to verify failure.** `cabal test --test-options='--match CertSlot'` — compile failure: constructors missing.

- [ ] **Step 3: Implement.** In `Error.hs` add the four constructors and the renderings exactly as tested. In `Internal.hs` add:

```haskell
-- | The one namespace lookup shared by @0.5 theta references
-- ('resolveArgRef') and #105 certificate slot references: which declared
-- leaves and which prior arguments carry this name. Callers own their own
-- collision policy and error family — this helper only answers the lookup,
-- so the namespace rule has exactly one home when the discharge-shadowing
-- TODO later unifies collision policy.
refMatches
  :: Env
  -> [(ArgId, SupportTerm)]
  -> String
  -> ([(LeafId, Prop)], [(ArgId, SupportTerm)])
refMatches env priors name =
  ( [lp | lp@(LeafId n, _) <- envGamma env, n == name]
  , [at | at@(ArgId a, _) <- priors, a == name]
  )

-- | Name -> premise-slot resolution for certificate references (#105): the
-- @0.5 reference namespace — declared leaves and prior arguments, collision
-- a hard error — located against this argument's resolved premise sequence
-- by term equality. The premise sequence is exactly the list replay hands
-- to the strict backend, so a resolved index is a replay slot by definition.
certSlotResolver
  :: Env
  -> [(ArgId, SupportTerm)]
  -> [SupportTerm]
  -> String
  -> Either SlotRefError Int
certSlotResolver env priors prems name =
  case refMatches env priors name of
    ([(lid, _)], []) -> locate (SLeaf lid)
    ([], [(_, t)]) -> locate t
    ([], []) -> Left SlotNameUnresolved
    _ -> Left SlotNameAmbiguous
  where
    locate t =
      case [i | (i, p) <- zip [0 ..] prems, p == t] of
        [i] -> Right i
        [] -> Left SlotNameNotAPremise
        (i : j : _) -> Left (SlotNameMultiSlot i j)

-- | Lower an argument's assurance after its premises are resolved. Non-cert
-- assurances and schema-less payloads pass through untouched.
lowerArgCert
  :: Env
  -> [(ArgId, SupportTerm)]
  -> ArgId
  -> [SupportTerm]
  -> Assurance
  -> Either ElabError Assurance
lowerArgCert env priors aid prems assurance =
  case assurance of
    AssuranceCert cert ->
      case lowerCertPayload (certSlotResolver env priors prems) cert of
        Right cert' -> Right (AssuranceCert cert')
        Left (name, err) ->
          let backend = certBackend cert
              version = certVersion cert
              ref = ArgRef name
           in Left $ case err of
                SlotNameUnresolved -> CertSlotUnresolved aid backend version ref
                SlotNameAmbiguous -> CertSlotAmbiguous aid backend version ref
                SlotNameNotAPremise -> CertSlotNotAPremise aid backend version ref
                SlotNameMultiSlot i j -> CertSlotMultiSlot aid backend version ref i j
                SlotNonCanonicalNumeral -> CertSlotNonCanonicalNumeral aid backend version ref
                SlotSchemaMismatch -> CertSlotSchemaMismatch aid backend version ref
    other -> Right other
```

Also in this step (OV-5): amend the `Cert`/`certPayload` Haddock in `src/Lara/AST.hs` — the payload remains backend-owned and wire-opaque; the single sanctioned exception is the `lara-syntax@0.6` presentation lowering (`Lara.Elaborate.CertSlots`, #105), which rewrites only schema-declared premise-reference positions before the wire. "This type never inspects it" must not survive this PR unqualified.

Refactor `resolveArgRef`'s `where`-block (`Internal.hs:478-488`) onto `refMatches` in the same commit — a behavior-neutral rewrite of its `leafMatches`/`argMatches` comprehensions (the existing `ThetaInferenceSpec` exact-string tests pin every `ThetaReference*` message, so the whole suite is the regression net). Do **not** change its collision policy or error constructors.

Wire both sites (`Internal.hs:420-424` and `:440-457`):

```haskell
  -- InferTheta case
    (theta, prems) <- inferTheta env priors aid rule refs
    disch <- resolveArgDischarges env priors aid shallowDisch
    assurance' <- lowerArgCert env priors aid prems assurance
    pure (SRule r theta prems disch holes assurance')
```

```haskell
  -- explicit SRule case: after the existing (theta, prems) and disch bindings
    assurance' <- lowerArgCert env priors aid prems assurance
    pure (SRule r theta prems disch holes assurance')
```

(In the explicit case the premise list is the `prems` component of the existing `(theta, prems)` binding — the names in the tree today are `theta`/`prems'` inside a `do`; keep the tree's actual binding names.)

- [ ] **Step 4: Run to verify pass.** `cabal test --test-options='--match CertSlot'` — PASS. Then the **whole** suite: `cabal test` — PASS (no existing spec may observe a changed byte or message).

- [ ] **Step 5: Commit.** `git commit -am "feat(elaborate): resolve named certificate premise slots before the checker (#105)"`

### Task 4: end-to-end twins, replay/tamper, and the frozen-byte gate

**Files:**
- Test: `test/CertSlotsSpec.hs` (extend)

**Interfaces:**
- Consumes: the public compile pipeline the worked-example tests use (parse policy + program → elaborate → `Lara.Wire` unit encoding → check/replay). Follow `WorkedExamplesSpec`/`ReplaySpec` for the exact entry points.

- [ ] **Step 1: Write the failing tests.**

1. **Byte-identity, both backends.** For the ord@1 fixture pair from Task 3 and an analogous ra@1 pair (strict rule certified `ra@1` with theory `sha256:corpus-v1-ra-theory-0`, payload twins `(radrop (prem 0) (prem 1) (frac 119 500))` vs `(radrop (prem eA) (prem eB) (frac 119 500))`): encode both elaborated units with the wire encoder and assert the encoded bytes are **equal** (`shouldBe` on the encoded `String`/`ByteString`). This is #105's verification target verbatim: "symbolic and numeric authoring surfaces lower to byte-identical `Cert` payloads and units."
2. **Verdict identity.** Run the checker on both twins' units; assert equal verdicts.
3. **Replay/tamper unchanged.** Feed the symbolic twin through the same replay/tamper harness the `#57` cert tests use (see `ReplaySpec` / the cert-tamper cases referenced from `CheckSpec`): replay of the lowered unit succeeds; a tampered payload byte still rejects before checker execution.
4. **nd@1 untouched.** An nd@1-certified fixture whose payload contains `(hyp 0)` (and, adversarially, a spurious `(prem x)` list nested inside an `app`) elaborates with `certPayload` **unchanged**, and its rejection/acceptance is byte-for-byte what the pre-change pipeline produced.
5. **Printer round-trip.** `parse (print program) == program` for the symbolic twin (reuse the round-trip helper `SyntaxSpec` uses), pinning D7.

- [ ] **Step 2: Run to verify failure, then pass.** These should pass immediately if Tasks 2–3 are correct; a failure here is a real defect — fix the implementation, never the assertion.

- [ ] **Step 3: Frozen-byte gate.** Run:

```bash
cabal test
git status --porcelain corpus-units fixtures measurements bundles examples
```

Expected: full suite PASS; `git status` output empty.

- [ ] **Step 4: Commit.** `git commit -am "test(elaborate): byte-identity, replay, and pass-through gates for named cert slots"`

### Task 4b: symbolic worked example (dogfood + standing byte-identity witness)

**Files:**
- Create: a new worked-example directory in the S-series style (e.g. `examples/S6/`, or the next free S-number) — policy + program `.lara` sources authored **with the symbolic spelling** (`(prem <name>)` in an `ord@1` certificate), plus its committed `.core.sexp` golden
- Modify: `src/Lara/WorkedExamples.hs` (registry entry; shared verbatim with `scripts/gen-worked-examples.hs`)

**Purpose (OV-1):** after this task, the repo contains a living `.lara` author of the new syntax outside test fixtures. The committed golden is a *standing* byte-identity witness: its `.core.sexp` must be byte-equal to what the numeric spelling of the same argument produces, so `WorkedExamplesSpec`'s freshness check re-proves the #105 target on every CI run.

- [ ] **Step 1:** Author the example (small: one strict rule, two leaf premises, one `ord@1` cert citing both by name). Verify the numeric twin locally produces the identical `.core.sexp` before committing the golden.
- [ ] **Step 2:** Register it in `Lara.WorkedExamples`; run the gen script the way the existing examples are maintained; `cabal test --test-options='--match WorkedExamples'` — PASS, golden fresh.
- [ ] **Step 3:** Confirm the frozen dirs are untouched: this is purely additive (`git status --porcelain corpus-units fixtures measurements bundles` empty; the new `examples/` entries are new files only).
- [ ] **Step 4: Commit.** `git commit -m "feat(examples): symbolic named-slot worked example (lara-syntax@0.6 dogfood)"`

### Task 5: Lean mechanization

**Files:**
- Create: `lean/Lara/CertSlots.lean`
- Modify: the Lean root import list (wherever `Lara/Ord.lean` is imported) and the repo's `AxCheck` file
- Verify with: `lake build` (in `lean/`), `bash scripts/check-axioms.sh`, `make presentation-parity`

**Interfaces:**
- Consumes: `Lara.Certificate.SExpr` (`lean/Lara/Certificate.lean:14`), the canonical-nat parser in `lean/Lara/Cell.lean`, and the `prem`/`ordcmp`/`radrop` spelling constants already mechanized in `Cell.lean`/`Ord.lean`/`RA.lean` — reuse them; introduce no duplicate spelling.
- Produces: `SlotSchema`, `ordSlotSchema`, `raSlotSchema`, `slotSchemas`, `lowerPayload`, theorems `lower_id_of_no_symbolic` and `lower_eq_numeric_subst`.

- [ ] **Step 1: Definitions**, mirroring Task 2 over an abstract resolver:

```lean
structure SlotSchema where
  backendName : String
  backendVersion : Nat
  head : String
  arity : Nat
  refSlots : List Nat
deriving Repr

def ordSlotSchema : SlotSchema := ⟨"ord", 1, "ordcmp", 2, [0, 1]⟩
def raSlotSchema : SlotSchema := ⟨"ra", 1, "radrop", 3, [0, 1]⟩
def slotSchemas : List SlotSchema := [ordSlotSchema, raSlotSchema]

/-- Rewrite one payload argument (Task 2's `lowerAt`): only a symbolic
`(prem s)` at a declared reference position is touched. -/
def lowerAt (ρ : String → Option Nat) (schema : SlotSchema) (i : Nat) :
    SExpr → Option SExpr
  | e@(.list [.atom k, .atom s]) =>
      if i ∈ schema.refSlots ∧ k = Cell.Tag.prem.toString ∧ (parseCanonNat s).isNone then
        (ρ s).map fun slot => .list [.atom k, .atom (toString slot)]
      else some e
  | e => some e

def lowerPayload (ρ : String → Option Nat) (bname : String) (bver : Nat) :
    SExpr → Option SExpr
  | p@(.list (.atom h :: args)) =>
      match slotSchemas.find? fun s =>
          s.backendName = bname ∧ s.backendVersion = bver
            ∧ s.head = h ∧ s.arity = args.length with
      | some s =>
          (args.mapIdxM (lowerAt ρ s)).map fun args' => .list (.atom h :: args')
      | none => some p
  | p => some p
```

(Verified spellings: the canonical-nat parser is `Lara.Cell.parseCanonNat` (`lean/Lara/Cell.lean:41`), not `parseCanonicalNat`; `SExpr` is `Lara.Support.SExpr` (`lean/Lara/Certificate.lean:14`) — import it the way `Cell.lean:27` does, `open Lara.Support (SExpr)`. Spell `prem` only via `Cell.Tag.toString .prem` — `Cell.lean:10-12` mandates the single spelling home, so **no** `"prem"` string literal may appear in `CertSlots.lean`; likewise take `ordcmp`/`radrop` from `Ord.lean`/`RA.lean`'s `Tag.toString` tables rather than the literals shown in the sketch above. `deriving DecidableEq` on `SlotSchema` only if Lean 4.32 synthesizes it — `Repr` suffices for the theorems. Adjust `find?`'s predicate to `Bool` with `decide`/`&&` as the toolchain requires.)

- [ ] **Step 2: Theorems.** Define the structural predicate and prove:

```lean
/-- No reference position of a matched schema holds a symbolic `(prem s)`. -/
def NoSymbolicRef (bname : String) (bver : Nat) : SExpr → Prop := ...
  -- match the same structure as lowerPayload; at each declared position,
  -- the element is either not `(prem s)`, or `s` parses as a canonical nat.

/-- Byte preservation: the pass is the identity on every payload the frozen
corpus can contain (numeric slots, schema-less backends, malformed shapes). -/
theorem lower_id_of_no_symbolic
    (ρ : String → Option Nat) (bname : String) (bver : Nat) (p : SExpr)
    (h : NoSymbolicRef bname bver p) :
    lowerPayload ρ bname bver p = some p := ...

/-- The #105 verification target: lowering a symbolic payload equals the
numeric payload obtained by substituting every resolved name first. -/
theorem lower_eq_numeric_subst
    (ρ : String → Option Nat) (bname : String) (bver : Nat) (p q : SExpr)
    (h : SymNumericSubst ρ bname bver p q) :
    lowerPayload ρ bname bver p = some q := ...
```

where `SymNumericSubst ρ bname bver p q` is defined **independently and declaratively** (OV-4) — *not* by mirroring `lowerPayload`'s control flow, which would make the theorem near-circular (a function agreeing with its own restatement). State it positionally: for the schema matched by `(bname, bver, head, arity)`, `q` has the same head and argument count as `p`, every argument at a non-reference position is **equal**, and every declared reference position holding a symbolic `(prem s)` in `p` holds `(prem (toString n))` in `q` where `ρ s = some n` (all other reference-position shapes equal). Quantify over positions and sub-term equality; the theorem then genuinely specifies the pass. Proofs are by `List` induction over the argument vector against this relation; no new axioms. Mirror the D6 dead-wire rule too: `lowerPayload` returns `none` when the backend is schema'd, the payload fails schema match, and a symbolic `(prem s)` occurs anywhere — and `NoSymbolicRef` gains the corresponding second arm (schema'd-but-unmatched payloads must contain no symbolic `(prem s)` anywhere) so `lower_id_of_no_symbolic` keeps exactly the shape of the frozen-corpus hypothesis.

- [ ] **Step 2b: Conformance vectors (Haskell ↔ Lean drift guard).** The theorems constrain only the Lean mirror; nothing else ever runs both implementations on the same inputs (`scripts/differential.sh` covers the wire codec, not this pass). Add ~6 shared vectors with a fixed resolver `ρ` (`"e1" ↦ 0`, `"e2" ↦ 1`, else `none`): symbolic ord, mixed symbolic/numeric, ra with `frac` witness, nd@1 pass-through, wrong-arity pass-through, numeric identity. Assert them in `CertSlots.lean` via `#guard lowerPayload ρ … = some …` (build-time, no new gate) and mirror the same expectations as hspec cases in `CertSlotsSpec.hs` (most already exist from Task 2 — tag them as the vector set). Definitional drift between the mirrors then breaks `lake build` or `cabal test` immediately. D10's cut is untouched: vectors use a fixed `ρ`, no `Env` modeling.
- [ ] **Step 3: Register.** Import `Lara.CertSlots` from the Lean root (`lean/Lara.lean`); add `#print axioms` entries for both theorems to `lean/AxCheck.lean`, following its existing commented-block entry format (e.g. `AxCheck.lean:353-355`).

- [ ] **Step 4: Verify.** From `lean/`: `lake build` — no `sorry`, no errors. Then the axiom audit — `AxCheck.lean` is **not** a lake target, so `lake build` alone never runs it; the pinned gate (m5 checklist :110) is `cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh` — standard trio only. Then `make presentation-parity` — `PASS (73 rows)` unchanged (this plan adds no presentation-AST shape; the guard's `Cert` native-payload exemption stands).

- [ ] **Step 5: Commit.** `git commit -am "feat(lean): mechanize named-slot lowering with byte-preservation and substitution theorems"`

### Task 6: documentation and version bump

**Files:**
- Modify: `docs/lara-surface-grammar.md`, `docs/spec.md`, `docs/mechanization-plan.md`, `docs/rejection-surface.md`

- [ ] **Step 1: Grammar.** In `docs/lara-surface-grammar.md`: bump the header (`# LARA surface grammar — frozen (\`lara-syntax@0.6\`)`), the §intro version references (`:20`, `:33`), and add **Appendix E — `lara-syntax@0.6` (named certificate premise slots, 2026-08-12)** after Appendix D, containing: the symbolic form (`(prem ident)` at the declared reference positions of `ord@1`/`ra@1` payloads only), the D3 namespace and collision policy (with a cross-reference to Appendix D's reference grammar), the D4 slot mapping (incl. the representation rule), D5 mixed forms, D6 pass-through with the dead-wire rule and the moved rejection site, the six stable error messages from §3, the D8 recursion semantics, the D1 nd@1 exclusion with its de Bruijn rationale, and the D3 considered-and-deferred premise-label alternative (`premiseLabelIndex`) as a future-work note beside the nd@1 pointer.
- [ ] **Step 2: Pointers.** `docs/spec.md:144` (`lara-syntax@0.5` → `@0.6`) and the `docs/mechanization-plan.md` result-12 row (`at lara-syntax@0.5` → `@0.6`; note the `Cert` payload exemption is unchanged and that `lean/Lara/CertSlots.lean` mechanizes the new lowering separately from the codec).
- [ ] **Step 3: Rejection surface.** The `CertSlot*` family list's **normative home is Appendix E** (Step 1), following the `ThetaReference*` precedent — elaborator families live in `docs/lara-surface-grammar.md` Appendix D.3, and `docs/rejection-surface.md` documents only checker classes R1–R14 plus the generic source-boundary door. In `docs/rejection-surface.md`, add **only** a note (at the source-boundary door §1 and the R13 row) that a malformed non-canonical slot numeral under a matching schema now rejects at elaboration rather than replay, acceptance unchanged, with a cross-reference to Appendix E.
- [ ] **Step 3b: Parity-count staleness (bundled two-line fix).** Correct the stale "72-row" prose to 73 at `lean/Lara.lean:13` and in `TODOS.md`'s completed "AST ↔ Presentation.lean parity guard" entry (locate by `grep -n "72 rows" TODOS.md` — line numbers drift) — both `shapeRows` inventories are 73 rows (verified 2026-08-13: `lean/Lara/PresentationParity.lean:389-468`, `scripts/presentation-shape.hs:571-658`), and this PR's own gate output asserts `PASS (73 rows)`.
- [ ] **Step 4: Verify.** `grep -rn "lara-syntax@0.5" docs/ src/ test/` — remaining hits must be intentionally historical (appendix headers, changelog-style prose), none normative. `cabal test` still green.
- [ ] **Step 5: Commit.** `git commit -am "docs: lara-syntax@0.6 — named certificate premise slots (Appendix E)"`

### Task 7: close-out gates and PR

- [ ] **Step 1: Full gates from a clean tree.**

```bash
cabal test
(cd lean && lake build)
(cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
make presentation-parity
bash scripts/differential.sh
bash scripts/test-replay-tamper.sh
git status --porcelain corpus-units fixtures measurements bundles examples
```

All green; the `git status` line prints nothing. (Script names verified against the tree and `docs/m5-freeze-checklist.md` :99-112; note the axiom audit must be piped through `lake env lean AxCheck.lean` — `AxCheck.lean` is not a lake target.)

- [ ] **Step 2: TODOS.** Move the `### #105 / Named certificate premise slots (open)` entry (`TODOS.md:253`) to Completed with the evidence summary (byte-identity twins, error family, Lean theorems, parity row count).
- [ ] **Step 3: PR.** Branch `named-cert-premise-slots`, PR titled `feat: named certificate premise slots above opaque Cert — lara-syntax@0.6 (#105)`, body citing this plan, the D1 exclusion, and the gate outputs. Do not merge without hosted Haskell + Lean CI green.

---

## 6. Acceptance criteria (mapped to #105's verification target)

| #105 requirement | where proven |
|---|---|
| symbolic and numeric authoring lower to byte-identical `Cert` payloads and units | Task 4 test 1 (both backends), Task 5 `lower_eq_numeric_subst` |
| retain replay/tamper behavior | Task 4 test 3 |
| cover each supported backend | Task 4 tests 1–2 run for `ord@1` and `ra@1`; Task 4 test 4 pins the `nd@1` exclusion |
| unknown/ambiguous/duplicate/non-premise references fail before the checker | Task 3 behavioral tests, six stable D6 families — unconditionally for schema'd backends (dead-wire rule) incl. the dedicated non-canonical-numeral diagnostic |
| parser/printer round-trip preserves the authored presentation | Task 4 test 5 (zero parser changes, D7) |
| backend extensibility stays closed and deterministic | D2: schemas are code-only values in one closed list; Task 1 tests pin them |
| Haskell/Lean presentation parity synchronized | Task 5: parity guard unchanged at 73 rows; lowering mechanized with `AxCheck` coverage; Step 2b `#guard`/hspec conformance vectors pin the two mirrors to each other |
| no change to checker acceptance, canonical payloads, replay identity, raw `.core.sexp`, frozen bytes | D6/D8 by construction; Task 4 step 3 and Task 7 step 1 gates |

## 7. Explicit non-goals

- Named references inside `nd@1` proof terms (D1; future work with its own binder-aware design — see D1's future-work pointer: follow Lean 4's named-binder-to-de-Bruijn elaboration, don't redesign it).
- Any change to `Lara.Syntax`'s grammar, the wire codec, backend decoders, or the checker.
- Unifying the discharge-witness shadowing policy (separate TODOS item; depends on this plan only in that D3 adds a third position following the `@0.5` policy, sharpening that item's motivation). When that breaking change is executed, treat the presentation-version bump the way Rust treats an edition, not as a bare version increment: ship it with a corpus sweep that inventories affected `discharge` lines, an automatic rewriter that disambiguates them to the explicit spelling, and a deprecation/warning cycle before the silent-preference behavior is removed. `lara-syntax@0.x` over the frozen `lara-core` boundary is structurally the Rust-editions-over-stable-core model, and breaking surface changes should inherit its migration discipline.
- Rewriting the frozen `corpus-units/adaptive-pruning/C04` source to the symbolic spelling (frozen bytes). The in-tree symbolic author is instead the **new, additive** worked example of Task 4b.
- Enriching the R13/backend replay rejection to render the slot→source-premise mapping (the outside voice's complementary diagnostic-side idea, OV-2) — backend-agnostic value incl. `nd@1` and numeric authors, but it touches `Lara.Strict` rendering this plan deliberately leaves alone; captured as its own TODOS entry at review close-out.
- New mutation operators over symbolic spellings (the mutation suite is frozen at `m5-freeze-v4`).

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | `/codex review` | Independent 2nd opinion | 0 | — | — |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | CLEAR (PLAN, 2026-08-13) | 16 issues, 0 critical gaps — all folded into this plan |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | — |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | — |
| Outside Voice | (auto, Claude subagent) | Cross-model challenge | 1 | ran (Codex timed out → Claude fallback) | 9 findings: 8 accepted (OV-1,3,4,5,6,7,8,9), 1 kept-as-planned with TODO (OV-2) |

**CROSS-MODEL:** The outside voice overturned two of this review's own assessments (D6 pass-through "safe by construction" → dead-wire rule added; Task 5 credited as the verification target → SymNumericSubst made independent) and its strategic challenge (diagnostic-side naming) was adjudicated as a complementary TODO, not a rival. All nine findings were user-decided individually.

**VERDICT:** ENG CLEARED — ready to implement (scope accepted as planned; 16 findings resolved and folded task-by-task: dead-wire rule, representation rule, recursion semantics, independent substitution relation, sixth+fifth error constructors, refMatches DRY seam, conformance vectors, symbolic worked example Task 4b, Cert Haddock carve-out, citation corrections, staleness fixes).

NO UNRESOLVED DECISIONS
