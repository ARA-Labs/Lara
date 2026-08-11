# Result 12 Presentation Parity Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the explicit result-12 gap by making Lean's structured presentation model cover the complete live Haskell `Program`/`Policy` surface, then install a compiler-checked cross-language shape guard that prevents silent drift.

**Architecture:** Reuse the already-mechanized `Lara.Sigma` types inside `Lara.Presentation`; do not create a second Lean signature model. Extend the private structured `Sx` codec and its round-trip proofs for `policySigma`, arbitrary sorts, and optional polarity. Protect the boundary with compiler-checked Haskell and Lean shape witnesses that emit one normalized inventory, plus a `GHC.Generics` arity tripwire tying every Haskell inventory row to its type's real shape; a shell gate builds both runtimes itself and compares the outputs in local builds and CI.

**Tech Stack:** Haskell/GHC 9.6+ with `cabal exec -- runghc`, Lean 4.32.0 with Lake, POSIX shell, existing `Sx` structured codec, GitHub Actions.

## Global Constraints

- Preserve `lara-core@0.2` and `lara-syntax@0.3`; this task changes no public syntax or checker-boundary encoding.
- Reuse `Lara.Sigma.TermSort`, `Lara.Sigma.ConSig`, `Lara.Sigma.PredSig`, and `Lara.Sigma.Sigma` in the presentation model. A parallel presentation-only sort/signature vocabulary is prohibited.
- Do not modify `Unit`, `.core.sexp`, `Lara.Wire`, `checkUnit`, strict backends, corpus units, generated mutants, replay bundles, examples, or `measurements/frozen/`.
- Keep result 12 calibrated: Lean proves round-trip for the structured AST codec; Haskell QuickCheck tests the concrete `.lara` parser/printer. Neither result proves the Haskell parser correct.
- Every new Lean theorem must appear in `lean/AxCheck.lean` and pass the standard-axiom audit.
- The parity guard must fail on an omitted `Policy` field or `Decl` constructor, must reject empty output from either runtime, and must compare exact ordered inventories.
- The guard's scope is the complete surface-reachable shape listed in §2 below, not only `Policy`, `Measurand`, and `Sigma`.
- Preserve the annotated `m5-freeze-v4` tag and every frozen input/output byte.

---

## 1. Decisions Locked by This Plan

### D1. Reuse the semantic Sigma object

`lean/Lara/Sigma.lean` already mirrors `src/Lara/Sigma.hs` and supplies the exact three types missing from `Lara.Presentation`: built-in/declared sorts, constructor signatures, predicate signatures, and the aggregate signature. `Lara.Presentation` imports `Lara.Sigma` and introduces only local abbreviations:

```lean
-- `Sort` is a Lean keyword (the universe of types) — the identifier is never
-- `Sort` in Lean code; only the normalized inventory row label spells "Sort".
-- Same collision Lara.Sigma already resolved (Sigma.lean:50).
abbrev TermSort := Lara.Sigma.TermSort
abbrev ConSig := Lara.Sigma.ConSig
abbrev PredSig := Lara.Sigma.PredSig
abbrev Sigma := Lara.Sigma.Sigma
```

The presentation codec owns serializers for those reused types because result 12 is about lossless structured serialization, not Sigma well-formedness.

`ConSig`, `PredSig`, and `Sigma` gain additive `deriving DecidableEq` clauses in `lean/Lara/Sigma.lean` (they have none today, and the new `Policy`'s `deriving DecidableEq` requires them). Those three clauses are the only permitted change to that file.

### D2. Keep the codec private and structured

The new tags are internal to `Lara.Presentation.Sx`:

```text
sort-num | sort-str | sort-decl
con-sig | pred-sig | sigma
```

They do not alter `.lara`, `.core.sexp`, replay identity, or the checker wire. The Haskell concrete parser remains the production conformance path.

### D3. Make polarity optional in Lean

Lean's model becomes field-for-field equivalent to Haskell (up to the two documented representation exemptions in D5: the `SortName` erasure and `Cert`'s native-payload types):

```lean
structure Measurand where
  mk :: (id : MeasurandId) (sort : TermSort) (polarity : Option Polarity)
```

The structured codec uses the existing generic `sxOpt`/`unOpt` pair. Polarity's `Num`-gated well-formedness remains an elaborator/parser obligation; the round-trip model preserves values and does not validate them.

### D4. Guard shape with compiler witnesses plus an exact inventory

The guard does not parse Haskell or Lean source text. Each runtime contains:

1. exact constructor type witnesses for every record field and payload-carrying sum arm;
2. exhaustive eliminators for sums, compiled with incomplete-pattern failures enabled, binding every constructor argument at full positional arity (`SRule _ _ _ _ _ _`, never a record wildcard or whole-payload catch-all) so a new constructor or payload-arity change also breaks compilation;
3. explicit type-equality anchors for aliases and anonymous association-list entry shapes;
4. the same normalized ordered inventory rows;
5. a shape tripwire on each side. Haskell derives row counts and named selector order from `GHC.Generics`; Lean uses `Lean.Meta` for structure fields, constructors, alias definitional equality, and the `Discharges.cons` payload arity. Named record labels are normalized and compared in declaration order. Positional constructors have no selector names: exact signatures pin their arity and positional type sequence, but semantic labels and swaps among same-typed positions remain assertions. Either tripwire fails before printing when its real declaration disagrees with the row.

```text
Haskell types ──cabal build──▶ presentation-shape.hs ──┐  witnesses: compile-time
 (Lara.AST,                    (witnesses + shape      │  tripwire: rows ==
  Lara.Sigma)                   tripwire + shapeRows)  ▼            real shape
                                                 haskell.tsv ──┐
                                                               ├─ diff -u ─▶ PASS/FAIL
                                                   lean.tsv ───┘
 Lean types  ──lake build───▶ presentation-shape ──────▲
  (Lara.Presentation)          (lean_exe: witnesses + shapeRows)
```

A field/constructor change first breaks a compiler witness. The tripwire then forces the Haskell inventory row to change with the type — "update the witness, forget the row" cannot pass the gate — and a changed Haskell row fails the diff until Lean's type, witness, and row follow. After the change is intentionally mirrored, the Haskell and Lean inventory outputs must again match exactly. This avoids a regex source scanner and avoids adding GHC API, Template Haskell, or external parser dependencies (`GHC.Generics` with standalone deriving in the witness executable is none of these).

### D5. One guard scope

The ordered inventory covers these exact categories:

- Identifier/newtype layer: `PropId`, `QuestionId`, `LeafId`, `RuleId`, `ArgId`, `ObligationId`, `BackendId`, `PolicyId`, `Param`, `SourceRef`, `TheoryDigest`, `Digest`, `GroupId`, `MeasurandId`, `DatasetId`, `PremiseLabel`. Haskell's `SortName` is additionally witnessed (`String -> SortName`) but deliberately has no inventory row: Lean's reused `Sigma` carries declared sorts as `List String`, so the newtype normalizes to a bare string. This erasure is stated in both witness-file headers.
- Imported semantic mapping: Haskell `FunSym`, `Pred`, `Term`, and `Prop` correspond losslessly to Lean's string-headed `Term`/`Atom` core. The guard names the normalized types `FunSym`, `Pred`, `Term`, and `Prop`; this does not introduce presentation duplicates.
- Closed/sum layer: `LeafKind`, `Provenance`, `AuditStatus`, `Mode`, `Necessity`, `Admission`, `GroupConflictMode`, `Polarity`, `Relation`, `Sort`, `Pat`, `Assurance`, `SupportTerm`, `Step`, `Attack`, `SurfaceStep`, `SurfaceAttack`, `ChallengeTarget`, `ArgConcl`, `Decl`.
- Record layer: `AtomPat`, `Leaf`, `Binding`, `Claim`, `Question`, `CertRef`, `Rule`, `Contrary`, `Exception`, `DupGroup`, `ConSig`, `PredSig`, `Sigma`, `Measurand`, `ComparisonScheme`, `Policy`, `Cert`, `SRule`, `Arg`, `ComparisonClaim`, `Comparison`, `Program`. `SRule` is `SupportTerm`'s rule-arm record (`src/Lara/AST.hs:533-541`); its six fields are guarded at the same depth as every named record so the support-term algebra cannot silently grow a field.
- Named aliases used by fields: `AdmissionEntry`, `TheoryEntry`, `BackendEntry`, `Subst`, `DischargeEntry`, `Position`.

The exact normalized rows are:

```text
PropId	val
QuestionId	val
LeafId	val
RuleId	val
ArgId	val
ObligationId	val
BackendId	val
PolicyId	val
Param	val
SourceRef	val
TheoryDigest	val
Digest	val
GroupId	val
MeasurandId	val
DatasetId	val
PremiseLabel	val
FunSym	val
Pred	val
Term	num	str	con
Prop	pred	args
LeafKind	observed	attested	assumed	certified
Provenance	user	ai-executed	checker(name,version)
AuditStatus	unreviewed	reviewed	disputed
Mode	strict	defeasible
Necessity	mandatory	optional
Admission	admit	quarantine	reject
GroupConflictMode	quarantine-on-conflict	reject-on-conflict
Polarity	higher-is-better	lower-is-better
Relation	strictly-better	at-least-as-good
Sort	num	str	decl
Pat	var	lit	con
Assurance	none	trusted	cert
SupportTerm	leaf	rule
Step	premise	question
Attack	rebut	undercut	undermine
SurfaceStep	index	name
SurfaceAttack	rebut	undercut	undermine
ChallengeTarget	question	leaf
ArgConcl	supports-claim	supports-derived	challenges
Decl	leaf	claim	arg	attack	status	group	comparison
AtomPat	pred	args
Leaf	id	prop	kind	provenance	refs
Binding	author	rationale	audit-status
Claim	id	nl	formal	binding
Question	id	answer	necessity
CertRef	backend	version	theory
Rule	id	params	mode	premises	premise-labels	conclusion	allow-trusted	certifiers	questions
Contrary	left	right
Exception	rule	atom
DupGroup	id	members
ConSig	sym	args	result
PredSig	sym	args
Sigma	sorts	cons	preds
Measurand	id	sort	polarity
ComparisonScheme	relation	polarity	recheck	bridge
Policy	id	sigma	rules	contraries	exceptions	admission	theories	group-mode	measurands	comparison-schemes
Cert	backend	version	theory	payload
SRule	rule	subst	premises	discharge	holes	assurance
Arg	id	conclusion	term
ComparisonClaim	id	nl-raw	binding
Comparison	conclusion	measurand	dataset	relation	recheck-arg	bridge-arg	result	baseline	binding	claim	supports
Program	artifact	digest	policy	backends	decls
AdmissionEntry	key:(LeafKind,Provenance)	value:Admission
TheoryEntry	digest:TheoryDigest	atoms:List Prop
BackendEntry	backend:BackendId	version:String
Subst	entries:List (Param,Term)
DischargeEntry	question:QuestionId	term:SupportTerm
Position	steps:List Step
```

Rows use semantic labels rather than language-specific selector spellings. The order above is part of the comparison contract. In particular the `Sort` row keeps the normalized label `Sort` even though the Lean identifier is `TermSort` (keyword collision) — labels are strings, never identifiers.

Calibration of what the guard checks: it compares constructor/field **names and arities** (shape). Field **types** are pinned per-language by the compiler witnesses and are not cross-checked; cross-language value agreement rests on the codec round-trip proofs and the differential suites. Row labels are normalized documentation in declaration order, verified by review, not by the gate. Two named representation exemptions, stated in both witness-file headers: (1) `SortName` normalizes to a bare string (Lean's `Sigma.sorts : List String`); (2) `Cert`'s `payload` is carried as each language's native S-expression type (Haskell `SExpr`, Lean `Sx`) and is exempt from shape comparison — a deliberate, pre-existing divergence this plan documents rather than resolves. The `Attack`/`Step`/`Position` rows are retained because `Lara.Presentation` models the resolved attack layer even though the elaborator, not the surface parser, produces resolved `Attack` values.

### D6. Claim closure follows verification

Only after the complete Lean build, axiom audit, parity gate, Haskell suite, and differential gates pass may documentation change result 12 from “structured subset mechanized” to “structured presentation AST mechanized.” The text must retain the structured-codec/concrete-parser distinction.

---

## 2. File Map

### Create

- `lean/Lara/PresentationParity.lean` — Lean constructor/exhaustiveness witnesses and normalized shape inventory.
- `lean/Lara/PresentationParityMain.lean` — minimal `IO` entry point that prints Lean's inventory.
- `scripts/presentation-shape.hs` — Haskell constructor/exhaustiveness witnesses and normalized shape inventory.
- `scripts/check-presentation-parity.sh` — non-empty exact comparison gate.

### Modify

- `lean/Lara/Presentation.lean` — reuse Sigma types; add sort/signature codecs; update `Measurand`, `Policy`, proofs, and scope prose.
- `lean/Lara/Sigma.lean` — additive `deriving DecidableEq` on `ConSig`, `PredSig`, `Sigma`; nothing else.
- `lean/lakefile.toml` — declare the `presentation-shape` `lean_exe` (root `Lara.PresentationParityMain`), following the `lara-driver` pattern.
- `lean/Lara.lean` — keep `Lara.PresentationParity` out of the proof-library root; the standalone executable imports the meta module directly.
- `lean/AxCheck.lean` — audit every new round-trip theorem and remove the retired `un_MeasurandSort` entry.
- `Makefile` — add `presentation-parity` target.
- `.github/workflows/ci.yml` — run the parity gate after the Haskell build.
- `docs/mechanization-plan.md` — close the bounded result-12 gap with calibrated wording.
- `docs/spec.md` — remove the stale `policySigma`/optional-polarity exception.
- `docs/lara-surface-grammar.md` — state that the structured Lean model covers the live surface.
- `lean/README.md` — mark full structured AST coverage while preserving the proof-strength caveat.
- `TODOS.md` — move the parity guard entry from the open P2 backlog to Completed.
- `plans/2026-08-10-sorts-in-checker.md` — append a post-closeout note resolving the deferred D9 presentation re-sync.
- `ara/trace/exploration_tree.yaml`, `ara/trace/pm_reasoning_log.yaml`, `ara/trace/sessions/2026-08-10_001.yaml`, `ara/trace/sessions/session_index.yaml` — record implementation, verification, and the result-12 closure decision.

---

## Execution Setup

After this plan is reviewed and merged, execute it from an isolated worktree based on the then-current `origin/main`, not from the plan branch:

```bash
git fetch origin --prune --tags
git worktree add .worktrees/result-12-presentation-parity \
  -b feature/result-12-presentation-parity origin/main
```

Before Task 1, confirm the new worktree is clean and that `m5-freeze-v4` still resolves to `f4327b4`. If `origin/main` has changed any file named in §2 since the plan was reviewed, re-read that file and tighten line anchors before editing; preserve the decisions and acceptance criteria unless new evidence requires a reviewed plan amendment.

---

### Task 1: Port the complete live Policy shape into Lean and prove round-trip

**Files:**
- Create: `lean/Lara/PresentationParity.lean`
- Modify: `lean/Lara/Presentation.lean:1-107,300-435,912-985,1296-1307`
- Modify: `lean/Lara/Sigma.lean` (three additive `deriving DecidableEq` clauses only)
- Modify: `lean/Lara.lean:64-66`
- Modify: `lean/AxCheck.lean:144-233`

**Interfaces:**
- Consumes: `Lara.Sigma.TermSort`, `Lara.Sigma.ConSig`, `Lara.Sigma.PredSig`, `Lara.Sigma.Sigma`.
- Produces: `Lara.Presentation.TermSort`, `ConSig`, `PredSig`, `Sigma`; `sxTermSort`/`unTermSort`; `sxConSig`/`unConSig`; `sxPredSig`/`unPredSig`; `sxSigma`/`unSigma`; `Measurand` with `Option Polarity`; `Policy` with `sigma` as its second field; unchanged theorem names `parse_printProgram` and `parse_printPolicy`.

- [ ] **Step 1: Add desired-shape witnesses before changing `Presentation.lean`**

Create `lean/Lara/PresentationParity.lean` with the two load-bearing constructor signatures first:

```lean
import Lara.Presentation

namespace Lara.PresentationParity

open Lara.Presentation

-- These exact signatures make the current pre-fix model fail to compile.
def measurandCtor : MeasurandId → TermSort → Option Polarity → Measurand := Measurand.mk

def policyCtor :
    PolicyId → Sigma → List Rule → List Contrary → List Exception →
    List AdmissionEntry → List TheoryEntry → GroupConflictMode →
    List Measurand → List ComparisonScheme → Policy := Policy.mk

end Lara.PresentationParity
```

Keep the meta-level guard out of `lean/Lara.lean`; after the witness parses, wire it through the standalone `presentation-shape` executable and include that executable in Lake's default targets.

- [ ] **Step 2: Run the desired-shape witness and confirm the current gap**

Run:

```bash
cd lean
lake env lean Lara/PresentationParity.lean
```

Expected: compilation failure — the first reported errors are the unknown `TermSort`/`Sigma` identifiers, which is all one run observes (elaboration stops before exercising the `Measurand.mk` and `Policy.mk` witnesses; their individual sensitivity is separately proven by Task 2 Step 6's mutation matrix). This is the red half of the parity repair.

- [ ] **Step 3: Reuse Sigma types and add lossless codecs**

First add the three additive `deriving DecidableEq` clauses to `ConSig`, `PredSig`, and `Sigma` in `lean/Lara/Sigma.lean` — the new `Policy`'s `deriving DecidableEq` requires them and they do not exist today (only `TermSort` derives it).

Then change `lean/Lara/Presentation.lean` to import `Lara.Sigma` and add the aliases and codecs. `Sort` is a Lean keyword, so the alias and every identifier spell `TermSort`; only the inventory row label is "Sort". The implementation shape is:

```lean
abbrev TermSort := Lara.Sigma.TermSort
abbrev ConSig := Lara.Sigma.ConSig
abbrev PredSig := Lara.Sigma.PredSig
abbrev Sigma := Lara.Sigma.Sigma

def sxTermSort : TermSort → Sx
  | .num => .node "sort-num" .nil
  | .str => .node "sort-str" .nil
  | .decl n => .node "sort-decl" (.cons (.str n) .nil)

def unTermSort : Sx → Option TermSort
  | .node "sort-num" .nil => some .num
  | .node "sort-str" .nil => some .str
  | .node "sort-decl" (.cons (.str n) .nil) => some (.decl n)
  | _ => none

@[simp] theorem un_TermSort (s : TermSort) : unTermSort (sxTermSort s) = some s := by
  cases s <;> rfl

@[simp] theorem un_sxList_TermSort (xs : List TermSort) :
    unSxList unTermSort (sxList sxTermSort xs) = some xs :=
  unSxList_sxList un_TermSort xs
```

Add `sxConSig`/`unConSig`, `sxPredSig`/`unPredSig`, and `sxSigma`/`unSigma` with the fixed tags from D2. Each record gets a direct constructor proof and each list field gets an `unSxList_sxList` specialization:

```lean
@[simp] theorem un_sxConSig (c : ConSig) : unConSig (sxConSig c) = some c := by
  cases c with | mk sym args result => simp [sxConSig, unConSig]

@[simp] theorem un_sxPredSig (p : PredSig) : unPredSig (sxPredSig p) = some p := by
  cases p with | mk sym args => simp [sxPredSig, unPredSig]

@[simp] theorem un_sxSigma (sg : Sigma) : unSigma (sxSigma sg) = some sg := by
  cases sg with | mk sorts cons preds => simp [sxSigma, unSigma]
```

Encode `ConSym`/`PredSym` through their `.name : String` field and reconstruct their distinct newtypes; do not collapse the two symbol types into one alias.

- [ ] **Step 4: Replace `MeasurandSort` and mandatory polarity**

Delete `MeasurandSort`, `MeasurandSort.sx`, `unMeasurandSort`, and `un_MeasurandSort`. Replace the record and codec with:

```lean
structure Measurand where
  mk :: (id : MeasurandId) (sort : TermSort) (polarity : Option Polarity)
  deriving DecidableEq

@[simp] theorem un_sxOpt_Polarity (o : Option Polarity) :
    unOpt unPolarity (sxOpt Polarity.sx o) = some o :=
  unOpt_sxOpt un_Polarity o
```

`sxMeasurand` must call `sxTermSort` and `sxOpt Polarity.sx`; `unMeasurand` must call `unTermSort` and `unOpt unPolarity`. Keep `un_sxMeasurand` and `un_sxList_Measurand` theorem names.

- [ ] **Step 5: Add Sigma to Policy and update the top-level proof**

Make `sigma` the second `Policy` field, matching Haskell `policySigma`:

```lean
structure Policy where
  mk ::
  (id : PolicyId) (sigma : Sigma)
  (rules : List Rule) (contraries : List Contrary)
  (exceptions : List Exception) (admission : List AdmissionEntry)
  (theories : List TheoryEntry) (groupMode : GroupConflictMode)
  (measurands : List Measurand) (comparisonSchemes : List ComparisonScheme)
  deriving DecidableEq
```

Insert `sxSigma p.sigma` immediately after `p.id.sx` in `printPolicy`; parse it in the same position with `unSigma`; pass it as the second `Policy.mk` argument. Update the proof to name every field:

```lean
theorem parse_printPolicy (q : Policy) : parsePolicy (printPolicy q) = some q := by
  cases q with
  | mk i sg rs cs es am th gm ms sch => simp [printPolicy, parsePolicy]
```

Do not change `printProgram`, `parseProgram`, or `parse_printProgram` except for formatting forced by imports.

- [ ] **Step 6: Update the module's scope contract**

In `lean/Lara/Presentation.lean`:

- replace “structured subset” with “complete live presentation `Program`/`Policy` shape at `lara-syntax@0.3`”;
- add `Sort`, `ConSig`, `PredSig`, and `Sigma` to the scope list;
- remove `MeasurandSort` from the enum list;
- delete the two deviation bullets for `policySigma` and mandatory `Num` polarity;
- preserve the explicit statement that the theorem does not prove the concrete Haskell parser.

- [ ] **Step 7: Audit every new theorem**

In `lean/AxCheck.lean`, remove:

```lean
#print axioms Lara.Presentation.un_MeasurandSort
```

Add:

```lean
#print axioms Lara.Presentation.un_TermSort
#print axioms Lara.Presentation.un_sxList_TermSort
#print axioms Lara.Presentation.un_sxConSig
#print axioms Lara.Presentation.un_sxList_ConSig
#print axioms Lara.Presentation.un_sxPredSig
#print axioms Lara.Presentation.un_sxList_PredSig
#print axioms Lara.Presentation.un_sxSigma
#print axioms Lara.Presentation.un_sxOpt_Polarity
```

Keep the existing audits for `un_sxMeasurand`, `un_sxList_Measurand`, `parse_printPolicy`, and `parse_printProgram`.

- [ ] **Step 8: Run the Lean gates**

Run:

```bash
cd lean
lake build
lake env lean Lara/PresentationParity.lean
lake env lean AxCheck.lean | ../scripts/check-axioms.sh
```

Expected: all commands exit 0; the axiom checker reports no `sorryAx` and nothing outside `propext`, `Classical.choice`, and `Quot.sound`.

- [ ] **Step 9: Commit the parity model**

```bash
git add lean/Lara/Presentation.lean lean/Lara/Sigma.lean lean/Lara/PresentationParity.lean lean/Lara.lean lean/AxCheck.lean
git commit -m "feat(lean): close presentation AST parity"
```

---

### Task 2: Install the cross-language presentation-shape guard

**Files:**
- Create: `scripts/presentation-shape.hs`
- Create: `lean/Lara/PresentationParityMain.lean`
- Create: `scripts/check-presentation-parity.sh`
- Modify: `lean/Lara/PresentationParity.lean`
- Modify: `lean/lakefile.toml` (the `presentation-shape` `lean_exe` stanza only)
- Modify: `Makefile:4-25`
- Modify: `.github/workflows/ci.yml:73-79`

**Interfaces:**
- Consumes: complete Haskell `Lara.AST`/`Lara.Sigma` surface; complete Lean `Lara.Presentation` surface.
- Produces: byte-identical UTF-8 TSV on stdout from both runtimes; the compiled `lean_exe` `presentation-shape`; the Haskell arity tripwire; `make presentation-parity`; CI gate “Haskell-Lean presentation AST parity”.

- [ ] **Step 1: Add exact Haskell compiler witnesses**

Create `scripts/presentation-shape.hs` with strict warning gates:

```haskell
{-# OPTIONS_GHC -Wall -Werror=missing-fields -Werror=incomplete-patterns #-}

module Main (main) where

import Lara.AST
import Lara.Sigma
```

For every identifier/newtype, imported product, and record in D5, define an exact constructor signature. Define exhaustive eliminators for imported `Term` and every D5 sum. The load-bearing changed records must be exactly:

```haskell
measurandCtor :: MeasurandId -> Sort -> Maybe Polarity -> Measurand
measurandCtor = Measurand

policyCtor ::
  PolicyId -> Sigma -> [Rule] -> [Contrary] -> [Exception] ->
  [((LeafKind, Provenance), Admission)] -> [(TheoryDigest, [Lara.Prop.Prop])] ->
  GroupConflictMode -> [Measurand] -> [ComparisonScheme] -> Policy
policyCtor = Policy

programCtor :: String -> Digest -> PolicyId -> [(BackendId, String)] -> [Decl] -> Program
programCtor = Program
```

Import `Lara.Prop` qualified for `FunSym`, `Pred`, `Term`, `Prop`, and the theory-entry signature. Add exact `String -> <newtype>` witnesses for all 16 identifiers plus `String -> SortName` (witnessed, row-erased — see D5), `String -> FunSym`, `String -> Pred`, and `Pred -> [Term] -> Prop`. Prefix unused witness names with `_` or collect them in one strict `witnesses` function so `-Wall` stays clean. The file header states the guard pipeline diagram from D4 and both D5 representation exemptions (`SortName` erasure; `Cert` native payload).

For every sum in D5, define one exhaustive eliminator. Include imported `Term`'s numeric, string, and constructor arms. `Decl` must include all seven arms:

```haskell
declTag :: Decl -> String
declTag decl = case decl of
  DeclLeaf _ -> "leaf"
  DeclClaim _ -> "claim"
  DeclArg _ -> "arg"
  DeclAttack _ -> "attack"
  DeclStatus _ -> "status"
  DeclGroup _ -> "group"
  DeclComparison _ -> "comparison"
```

Use the same exhaustive shape for `Term`, `LeafKind`, `Provenance`, `AuditStatus`, `Mode`, `Necessity`, `Admission`, `GroupConflictMode`, `Polarity`, `Relation`, `Sort`, `Pat`, `Assurance`, `SupportTerm`, `Step`, `Attack`, `SurfaceStep`, `SurfaceAttack`, `ChallengeTarget`, and `ArgConcl`. Every eliminator arm binds its constructor arguments at full positional arity (`Checker _ _`, `SRule _ _ _ _ _ _`) — never a record wildcard (`SRule {}`) or whole-arm catch-all — so adding a payload argument breaks compilation. `SRule` additionally gets its own record constructor witness like every D5 record.

- [ ] **Step 2: Emit the normalized ordered Haskell inventory**

Define one `shapeRows :: [(String, [String])]` in the exact D5 category order. Every D5 type must occur exactly once. Render without locale-sensitive formatting:

```haskell
renderRow :: (String, [String]) -> String
renderRow (name, parts) = intercalate "\t" (name : parts)

main :: IO ()
main = putStr (unlines (map renderRow shapeRows))
```

Then wire the D4 shape tripwire: standalone-derive `Generic` for every D5 record and sum (`{-# LANGUAGE StandaloneDeriving, DeriveGeneric #-}`; `deriving instance Generic Policy`, etc. — orphan instances are acceptable in this executable leaf). Before printing, assert per row that its part count equals the type's real shape and compare normalized `Selector` metadata for every named record field. Anonymous tuple rows use their tuple `Generic` instances; `Subst` and `Position` use exact type-equality witnesses plus their one-part normalized rows. On mismatch, print the offending row name and exit nonzero.

The four anchor rows must equal D5 verbatim. The aliases use these rows:

```text
AdmissionEntry\tkey:(LeafKind,Provenance)\tvalue:Admission
TheoryEntry\tdigest:TheoryDigest\tatoms:List Prop
BackendEntry\tbackend:BackendId\tversion:String
Subst\tentries:List (Param,Term)
Position\tsteps:List Step
```

- [ ] **Step 3: Complete the Lean witnesses and emit the same inventory**

Expand `lean/Lara/PresentationParity.lean` so every D5 identifier, imported mapping, and record has an exact constructor witness and every D5/imported sum has an exhaustive tag function. Witness Lean `Term`'s three arms and `Atom.mk : String → Terms → Atom` against the normalized Haskell `Term`/`Prop` rows. Lean's exhaustiveness checker must reject a new constructor automatically.

Define the same normalized rows and renderer:

```lean
def shapeRows : List (String × List String) := [
  ("Measurand", ["id", "sort", "polarity"]),
  ("Policy", ["id", "sigma", "rules", "contraries", "exceptions", "admission",
              "theories", "group-mode", "measurands", "comparison-schemes"]),
  ("Decl", ["leaf", "claim", "arg", "attack", "status", "group", "comparison"]),
  ("Program", ["artifact", "digest", "policy", "backends", "decls"])
  -- The final file contains every D5 row in the declared category order.
]

def renderShape : String :=
  String.intercalate "\n" (shapeRows.map fun row =>
    String.intercalate "\t" (row.1 :: row.2)) ++ "\n"
```

The implementation must expand the displayed list to the complete D5 inventory; the comment shown above is explanatory and is not a permitted final-file placeholder.

Then wire the Lean half of the D4 shape tripwire: a short `Lean.Meta` elaboration-time check in `PresentationParity.lean` (no new dependencies — core meta API) that checks structure field counts and normalized names, inductive constructor counts, alias definitional equality against independent expected shapes, and the payload arity of `Discharges.cons`. It fails compilation naming the offending row on mismatch. The module header states the same two D5 representation exemptions as the Haskell witness file.

Create `lean/Lara/PresentationParityMain.lean`:

```lean
import Lara.PresentationParity

def main : IO Unit :=
  IO.print Lara.PresentationParity.renderShape
```

Declare the executable in `lean/lakefile.toml`, following the `lara-driver`/`admission-driver` pattern:

```toml
[[lean_exe]]
name = "presentation-shape"
root = "Lara.PresentationParityMain"
```

- [ ] **Step 4: Write the exact comparison gate**

Create `scripts/check-presentation-parity.sh`. The script builds both runtimes itself, exactly like `scripts/differential.sh:81` — never compare stale or missing artifacts (a stale `.lake` cache producing a false PASS is the worst failure a guard can have):

```bash
#!/usr/bin/env bash
set -euo pipefail

# Cross-language presentation-shape parity gate (guard pipeline — see plan D4):
#
#  Haskell types ──cabal build──▶ presentation-shape.hs ──┐  witnesses: compile-time
#   (Lara.AST,                    (witnesses + arity      │  tripwire:  row parts ==
#    Lara.Sigma)                   tripwire + shapeRows)  ▼              real shape
#                                                  haskell.tsv ──┐
#                                                                ├─ diff -u ─▶ PASS/FAIL
#                                                    lean.tsv ───┘
#   Lean types  ──lake build───▶ presentation-shape ──────▲
#    (Lara.Presentation)          (lean_exe: witnesses + shapeRows)
#
# SortName is witnessed but row-erased (Lean's Sigma carries List String).

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

cd "$repo_root"

if ! cabal build lib:lara > "$tmp_dir/cabal-build.log" 2>&1; then
  echo "presentation parity: FAIL: cabal build lib:lara" >&2
  cat "$tmp_dir/cabal-build.log" >&2
  exit 1
fi
if ! (cd lean && lake build presentation-shape) > "$tmp_dir/lake-build.log" 2>&1; then
  echo "presentation parity: FAIL: lake build presentation-shape" >&2
  cat "$tmp_dir/lake-build.log" >&2
  exit 1
fi

lean_bin="lean/.lake/build/bin/presentation-shape"
[ -x "$lean_bin" ] || { echo "presentation parity: no Lean binary at $lean_bin" >&2; exit 1; }

cabal exec -- runghc scripts/presentation-shape.hs > "$tmp_dir/haskell.tsv"
"$lean_bin" > "$tmp_dir/lean.tsv"

for output in "$tmp_dir/haskell.tsv" "$tmp_dir/lean.tsv"; do
  test -s "$output" || { echo "presentation parity: empty inventory: $output" >&2; exit 1; }
done

diff -u "$tmp_dir/haskell.tsv" "$tmp_dir/lean.tsv"
printf 'presentation parity: PASS (%s rows)\n' "$(wc -l < "$tmp_dir/haskell.tsv" | tr -d ' ')"
```

The script must return nonzero on build failure, compiler-witness failure, arity-tripwire failure, empty output, row-order drift, field drift, or constructor drift.

- [ ] **Step 5: Run the guard and verify the positive path**

Run:

```bash
bash scripts/check-presentation-parity.sh
```

Expected: `presentation parity: PASS (<count> rows)` with a nonzero count equal to the complete D5 inventory.

- [ ] **Step 6: Prove mutation sensitivity — all five guard failure classes plus the tripwire**

Every claimed failure mode must be observed, not assumed. Each mutation is temporary; restore the exact original text and re-run the full guard to PASS before the next mutation.

1. **Field drift.** Remove `sigma` from Lean's normalized `Policy` row, leaving Haskell unchanged. Run `bash scripts/check-presentation-parity.sh`. Expected: nonzero exit with a unified diff showing `sigma` missing from Lean's `Policy` row.
2. **Row-order drift.** Swap two adjacent rows in Lean's `shapeRows` (e.g. `ConSig` and `PredSig`). Run the guard. Expected: nonzero exit with a reordering diff — D5's order is part of the comparison contract.
3. **Haskell witness break.** Remove the `DeclComparison` arm from Haskell's `declTag`. Run `cabal exec -- runghc scripts/presentation-shape.hs`. Expected: compilation failure from `-Werror=incomplete-patterns`.
4. **Lean witness break.** Remove one arm from Lean's `Decl` tag function in `PresentationParity.lean`. Run `cd lean && lake build presentation-shape`. Expected: compilation failure from the exhaustiveness checker — this observes the "Lean rejects a new constructor automatically" claim instead of trusting it.
5. **Empty inventory.** Temporarily make `lean/Lara/PresentationParityMain.lean` print the empty string. Run the guard. Expected: nonzero exit with `presentation parity: empty inventory` — this observes the Global Constraints requirement that empty output from either runtime is rejected.
6. **Haskell arity tripwire.** Add a fake part to Haskell's `Measurand` row (no type change). Run `cabal exec -- runghc scripts/presentation-shape.hs`. Expected: nonzero exit naming the `Measurand` row — the tripwire, not the diff, catches a row/type mismatch.
7. **Lean arity tripwire.** Add a fake part to Lean's `Measurand` row (no type change). Run `cd lean && lake build presentation-shape`. Expected: compilation failure naming the `Measurand` row from the `Lean.Meta` check.

After all seven restorations, run the full guard once more; expected PASS.

- [ ] **Step 7: Wire the local and hosted gates**

In `Makefile`, add `presentation-parity` to `.PHONY` and add:

```make
presentation-parity:
	bash scripts/check-presentation-parity.sh
```

In `.github/workflows/ci.yml`, immediately after the `Test` step (so a cold `lake build` inside the gate never delays Haskell test signal, matching the job's convention of running Lean-dependent gates after the Haskell suite), add:

```yaml
      - name: Haskell-Lean presentation AST parity
        run: make presentation-parity
```

The Haskell job already installs Lean and restores `lean/.lake`, so no setup step or second workflow job is needed. Because the gate script builds both runtimes itself, cache state (cold or stale) can delay it but never falsify it.

- [ ] **Step 8: Run targeted gates**

Run:

```bash
make presentation-parity
cabal test all --test-show-details=direct
cd lean && lake build
```

Expected: all commands exit 0.

- [ ] **Step 9: Commit the guard**

```bash
git add scripts/presentation-shape.hs lean/Lara/PresentationParity.lean lean/Lara/PresentationParityMain.lean lean/lakefile.toml scripts/check-presentation-parity.sh Makefile .github/workflows/ci.yml
git commit -m "test(parity): guard presentation AST shape"
```

---

### Task 3: Close the project record and run the full acceptance gate

**Files:**
- Modify: `docs/mechanization-plan.md:54-56`
- Modify: `docs/spec.md:143-149`
- Modify: `docs/lara-surface-grammar.md:21-28`
- Modify: `lean/README.md:23`
- Modify: `TODOS.md:228-253` and Completed section
- Modify: `plans/2026-08-10-sorts-in-checker.md:697-711` by appending a post-closeout resolution
- Modify: ARA trace/session files selected by the research-manager epilogue

**Interfaces:**
- Consumes: green Task 1 Lean proof and green Task 2 parity guard.
- Produces: calibrated result-12 status, no stale partial-parity claim, and a complete implementation/verification trace.

- [ ] **Step 1: Update result-12 claims without overstating proof strength**

Use this meaning consistently:

```text
Lean mechanizes parse ∘ print = id for the complete live structured Program/Policy AST at lara-syntax@0.3, including policySigma and optional measurand polarity. Haskell QuickCheck separately covers the concrete .lara parser/printer. The Lean theorem is an AST-shape anchor, not a correctness proof for the Haskell concrete parser. The parity guard compares normalized shape inventories between the two models. Exact compiler witnesses pin record fields, sum payloads, aliases, and anonymous entry types; tripwires compare named record selectors in order. Positional constructors have no selector names, so exact signatures pin their arity and positional type sequence while semantic labels and same-typed swaps remain assertions. The two documented representation exemptions (SortName erasure; Cert native payload) are stated wherever complete coverage is claimed.
```

Apply it to:

- `docs/mechanization-plan.md` result 12: change status to **mechanized structured presentation codec (+ current Haskell conformance)**.
- `docs/spec.md` §2.1: replace the tracked-gap sentence with the complete-coverage statement and name the parity guard.
- `docs/lara-surface-grammar.md` versioning paragraph: remove the missing-field caveat and cite `scripts/check-presentation-parity.sh`.
- `lean/README.md` result 12 row: change ◐ to ✅ while retaining the structured/concrete distinction.

Do not change the result-12 theorem statement in `docs/spec.md` §9 and do not claim concrete-parser verification.

- [ ] **Step 2: Close the backlog and historical deferral cleanly**

Move `TODOS.md`'s “AST ↔ Presentation.lean parity guard” block into Completed. Record:

- the Lean mirror now carries `policySigma` and `Sort × Option Polarity` measurands;
- both compilers enforce their own shape witnesses;
- `scripts/check-presentation-parity.sh` compares exact normalized inventories in CI;
- future deliberate divergence must update both inventories in one reviewed change.

Do not rewrite the historical deferred bullet in `plans/2026-08-10-sorts-in-checker.md` §13. Append a dated post-closeout paragraph stating that this plan resolves that deferred item and naming the implementation commits.

- [ ] **Step 3: Scan for stale live claims**

Use the harness `grep` tool, not a shell search:

```text
pattern: does not yet (include|model).*policySigma|structured subset mechanized|optional[- ]polarity.*gap|result-12 gap
paths: docs;lean/README.md;TODOS.md;plans/2026-08-10-sorts-in-checker.md
```

Expected: no live statement claims that `policySigma` or optional polarity remain missing. Historical plan text may remain only when immediately followed by the post-closeout resolution; do not rewrite append-only ARA history.

- [ ] **Step 4: Record the implementation in the ARA epilogue**

Record direct journey facts for:

- the user-approved parity closure;
- the initial witness failure against the old Lean shape;
- the completed Lean round-trip and axiom audit;
- the guard's positive and mutation-negative results;
- the no-frozen-byte boundary.

Keep any general claim about compiler witnesses preventing cross-language drift staged unless the researcher explicitly affirms it or a later artifact depends on it.

- [ ] **Step 5: Run the full acceptance gate**

Run from the repository root:

```bash
make presentation-parity
cabal test all --test-show-details=direct
(cd lean && lake build)
(cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
bash scripts/differential.sh
bash scripts/admission-differential.sh
git diff --exit-code origin/main -- corpus-units fixtures measurements/frozen bundles examples
```

Expected:

- parity inventory comparison passes and reports a nonzero row count;
- Haskell tests pass;
- Lean builds;
- the axiom audit reports no `sorryAx` and only the standard trio;
- both differential suites report zero failures;
- the frozen-input/output diff is empty.

- [ ] **Step 6: Review the final boundary**

Confirm the final diff contains no change under:

```text
src/Lara/AST.hs
src/Lara/Sigma.hs
src/Lara/Wire.hs
src/Lara/Check.hs
lean/Lara/Unit.lean
lean/Lara/Check/
corpus-units/
fixtures/
measurements/frozen/
bundles/
examples/
```

A change in any listed path is scope expansion and must be removed or separately approved.

Two reviewed exceptions outside that list: `lean/Lara/Sigma.lean` carries exactly the three additive `deriving DecidableEq` clauses from Task 1, and `lean/lakefile.toml` carries exactly the `presentation-shape` `lean_exe` stanza from Task 2 — nothing else in either file.

- [ ] **Step 7: Commit the project record**

```bash
git add docs/mechanization-plan.md docs/spec.md docs/lara-surface-grammar.md lean/README.md TODOS.md plans/2026-08-10-sorts-in-checker.md ara/
git commit -m "docs(mechanization): close result 12 parity gap"
```

- [ ] **Step 8: Push and open the implementation PR**

```bash
git push -u origin feature/result-12-presentation-parity
```

Open a PR whose verification section lists the exact Task 3 gate outputs and whose scope statement says: “structured presentation model and parity guard only; no core, wire, corpus, example, replay, or frozen-measurement byte changed.”

---

## 3. Acceptance Criteria

The implementation is complete only when all of the following are observed:

1. `Lara.Presentation.Policy` has every live Haskell `Policy` field, including Sigma in the same semantic position.
2. `Lara.Presentation.Measurand` carries the reused `Lara.Sigma.TermSort` (normalized row label `Sort`) plus `Option Polarity`.
3. Sort, constructor-signature, predicate-signature, Sigma, Measurand, Policy, and Program structured codecs round-trip in Lean.
4. Every new theorem is present in `AxCheck.lean`; the audit remains within the standard axiom trio.
5. The Haskell and Lean shape producers emit identical, non-empty inventories covering every D5 type (including `SRule` and `DischargeEntry`), and both arity tripwires — Haskell `GHC.Generics` at runtime, Lean `Lean.Meta` at elaboration — tie every row's part count to its type's real shape.
6. The guard demonstrably fails in all seven Step 6 mutation classes: field drift, row-order drift, Haskell witness break, Lean witness break, empty inventory, Haskell tripwire mismatch, and Lean tripwire mismatch.
7. `make presentation-parity` runs in GitHub Actions on every PR and main push.
8. Documentation no longer reports `policySigma` or optional polarity as a live result-12 gap.
9. The production Haskell AST/parser, core/wire/checker, corpus, examples, replay bundles, and frozen measurements are byte-unchanged.
10. Full Haskell, Lean, axiom, differential, and admission-differential gates pass.

## 4. Explicit Non-goals

- Proving the Haskell concrete `.lara` parser correct in Lean.
- Sharing a concrete codec implementation between Haskell and Lean.
- Changing the public presentation grammar or adding `lara-syntax@0.4`.
- Changing `lara-core@0.2`, `Unit`, Sigma well-formedness, R2, or result 13.
- Implementing #88b/D7 (`let` bindings, binding interpolation, named certificate slots).
- Refactoring `Lara.Presentation` into smaller files during the parity repair.
- Introducing Template Haskell, GHC API dependencies, tree-sitter, regex source parsing, or generated source files. (Standalone-derived `GHC.Generics` inside the witness executable is none of these and is permitted for the arity tripwire.)
- Re-freezing M5 or cutting a new freeze tag.

## 5. Commit Sequence

1. `feat(lean): close presentation AST parity`
2. `test(parity): guard presentation AST shape`
3. `docs(mechanization): close result 12 parity gap`

Each commit must pass the targeted gate named in its task. The final PR must pass the complete Task 3 gate before review.

## 6. Eng-Review Amendment Log (2026-08-11)

Decisions accepted during `/plan-eng-review`; each is already folded into the sections above.

- **1A** — `Sort` is a Lean keyword: all Lean identifiers spell `TermSort` (`sxTermSort`/`unTermSort`, theorems `un_TermSort`/`un_sxList_TermSort`); the inventory row label stays `Sort`.
- **2B** — the guard follows the `differential.sh` pattern: `presentation-shape` is a `[[lean_exe]]` in `lean/lakefile.toml`, and the gate script builds both runtimes itself so stale or missing artifacts can never produce a false PASS.
- **3A** — `GHC.Generics` arity tripwire in `presentation-shape.hs`: each inventory row's part count is asserted against the type's real constructor/field count, closing the "update the witness, forget the row" loophole.
- **4B** — Haskell's `SortName` newtype is witnessed but row-erased; the erasure (Lean's `Sigma.sorts : List String`) is documented in D5 and both witness headers.
- **5A** — additive `deriving DecidableEq` on `ConSig`/`PredSig`/`Sigma` in `lean/Lara/Sigma.lean` (required by `Policy`'s deriving; the only change to that file).
- **6A** — the guard pipeline ASCII diagram lives in D4 and in the gate script's header.
- **7A** — the PASS row count strips `wc` padding (`| tr -d ' '`).
- **8A** — Task 2 Step 6 exercises all five guard failure classes plus the tripwire; every claimed failure mode is observed, not assumed.

Outside-voice (independent second review, Claude subagent after Codex timeout) findings accepted 2026-08-11; each folded into the sections above.

- **OV1** — the guard extends one level down: `SRule` (six fields) and the `DischargeEntry` alias join D5 with witnesses and rows; all sum eliminators bind constructor arguments at full positional arity so payload-arity changes break compilation; the elaborator-produced `Attack`/`Step`/`Position` rows are annotated as modeled-but-not-parser-produced.
- **OV2** — the arity tripwire is symmetric: Lean gains a `Lean.Meta` elaboration-time row/type check mirroring the Haskell `GHC.Generics` one; mutation class 7 observes it firing.
- **OV3 + OV6 + PR-review follow-up** — calibrated claim: exact signatures pin record field and sum-payload types; alias/entry rows have explicit anchors; named record labels are tripwire-verified in declaration order. Positional semantic labels and swaps among same-typed positions remain assertions because those constructors expose no selector names.
- **OV4** — the pre-existing `Cert.payload` divergence (Haskell `SExpr` vs Lean `Sx`) is a named representation exemption in D5, both witness headers, and the closure wording — documented, not resolved.
- **OV5** — cross-model tension resolved: keep hand rows + dual tripwires (3A-as-amended) over full Generic derivation with a golden TSV; the normalizer's special-case table would relocate the transcription surface, not remove it.
- **OV7** — the CI gate moves to immediately after `Test` so a cold `lake build` never delays Haskell test signal.
- **OV8** — Task 1 Step 2's red-run expectation is calibrated to what one compilation observes; per-witness sensitivity is evidenced by the Step 6 matrix.

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | `/codex review` | Independent 2nd opinion | 0 | — | — |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | CLEAR (PLAN) | 10 issues, 0 critical gaps |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | — |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | — |

Outside voice: 1 run (Claude subagent; Codex timed out) — 8 findings, all resolved by user decision (OV1–OV4, OV7, OV8 accepted; OV5 rejected in favor of 3A-as-amended; OV6 folded into OV3).

**CROSS-MODEL:** One tension — full Generic inventory derivation vs hand rows + tripwires. Resolved: hand rows with dual compiler-bound arity tripwires (user decision OV5-B).

**VERDICT:** ENG CLEARED — ready to implement. Scope accepted as-is (Step 0, 17 files: 6 code + build/CI + mandatory closeout). All 8 in-review decisions (1A, 2B, 3A, 4B, 5A, 6A, 7A, 8A) and all 8 outside-voice resolutions folded into the plan body.

NO UNRESOLVED DECISIONS
