# Issue #16 Executable Support and Attack Checkers Implementation Plan

> **Status: complete — closed by PR #21.**

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `executing-plans` to implement this plan task by task.

**Goal:** Replace manually constructed Lean proofs of support and attack
well-formedness with total executable checkers, then prove that checker success is
equivalent to the frozen `HasSupport` and `HasAttack` relations.

**Architecture:** Preserve the frozen relations as the specification. Add an
executable layer beside them: a decidable backend replay seam, a recursive support
inference function, finite first-order matching for declared contraries and
exceptions, a positional attack checker, and a program checker that returns a
proof-bearing `Compile.CheckedProgram`. Every algorithm receives both soundness and
completeness theorems. The source calculus continues to treat certificates as
opaque symbolic data; only registered backends decode them.

**Tech Stack:** Lean 4.32 core library, the existing Haskell strict-backend
implementation as the conformance anchor, Lake, Cabal/QuickCheck, and the
`AxCheck.lean` no-`sorry`/standard-axiom gate.

**Tracker:** GitHub issue #16, child of M2 tracker #15. This plan stops before the
checker-built `Compile.Faithful` edge oracle (#17) and attack-completeness/result-7
work (#18).

## Definition of Done

- A raw support term is checked by a total function that returns its unique
  conclusion and obligation set or a located rejection.
- A raw rebut, undercut, or undermine declaration is checked by a total function
  or rejected at the declaration.
- The support checker is sound and complete for `HasSupport`.
- The attack checker is sound and complete for `HasAttack`.
- Raw argument and attack lists produce a proof-bearing `CheckedProgram` only when
  every argument is complete, every endpoint is declared, and every attack types.
- The ND backend is replayed by executable certificate decoding plus `ND.infer`;
  its source encoding preserves the full normalized atom, and no Lean `repr`
  string parsing is placed in the trusted symbolic core.
- Relevant rejection paths R1, R3-R7, R10-R11, and R13 have executable fixtures.
- All new theorems are listed in `lean/AxCheck.lean`, contain no `sorry`, and use
  only the standard axiom trio.
- `lake build`, the standalone axiom audit, and all existing Haskell property tests
  pass.

## Global Constraints

- `HasSupport` and `HasAttack` remain the frozen declarative definitions. Algorithms
  must be proved against them, not replace or weaken them.
- `Strict.Backend.models` remains mathematical and may stay `Prop`-valued. Only
  exact certificate replay must become executable.
- Backend formulas and proof terms never cross the strict-backend seam.
- The concrete ND source encoder is normalization-faithful: it must not collapse
  atoms that share a predicate but differ in their argument terms.
- Certificate payloads remain opaque to `Lara.Support` and `Lara.Attack`.
- Use closed sum types and namespace-specific identifiers in the core. Raw strings
  stay at the wire/decode boundary.
- Implement each checker once as `Except` with its typed error surface. Do not
  add a parallel `Option`-only checker core that would duplicate validation
  order, adequacy proofs, or R-class routing.
- Do not add `Backend.uses` or finish `certDeps`; that is the next ordered M2 item.
- Do not add certificate-erased argument identity; result 9 remains separate.
- Do not construct the general `Compile.Faithful` oracle in this issue.
- Do not add the result-7 attack-completeness invariant in this issue.
- Do not build the Haskell M3 policy/support/attack checker or JSON codec here.

## Target Flow

```text
CertRef payload
      |
      v
registered Backend.replay ---- replay_iff ---- Backend.accepts ---- sound ---- models
      |
      v
inferSupport : SupportTerm -> Except CheckError SupportResult
      |                         |
      |                         +---- inferSupport_sound / inferSupport_complete
      v
checkAttack : Attack -> Except CheckError Unit
      |                         |
      |                         +---- checkAttack_sound / checkAttack_complete
      v
checkProgram : args -> attacks -> Except ProgramError CheckedProgram
```

The executable checker modules follow the same one-way dependency graph:

```text
Lara.Check.Support
        |
        v
Lara.Check.Attack
        |
        v
Lara.Check.Program

Lara.Check imports and re-exports the three public surfaces.
```

---

### Task 1: Make the Certificate and Backend Seam Executable

**Files:**

- Modify: `lean/Lara/Certificate.lean`
- Modify: `lean/Lara/Strict.lean`
- Modify: `lean/Lara/Support.lean`
- Modify: `lean/Lara/Examples.lean`
- Modify: `lean/AxCheck.lean`

**Interfaces:**

- Consumes: opaque `CertRef`, abstract `Strict.Backend`, and
  `Support.certOkOf`
- Produces: a backend-first registry, executable replay with an adequacy theorem,
  and the retained proposition-level acceptance relation and soundness theorem

- [ ] **Step 1: Mirror the symbolic certificate wire representation**

Add the closed symbolic S-expression used by `src/Lara/Strict.hs`:

```lean
inductive SExpr where
  | atom : String -> SExpr
  | list : List SExpr -> SExpr

structure CertRef where
  payload : SExpr
```

Bring Lean backend identity into conformance with Haskell at the same seam:

```lean
structure BackendId where
  name    : String
  version : Nat
```

Update the ND fixture to use the exact symbolic identity `nd@1`. Backend name
alone is not an identity; a version mismatch must fail the outer registry
lookup.

Lean 4.32 cannot derive `DecidableEq` through the nested `List SExpr`.
Implement mutually recursive structural equality decisions for `SExpr` and
`List SExpr` (using an explicit `sizeOf` termination measure if needed), expose
the `DecidableEq SExpr` instance, and then derive or define `CertRef` equality
from it. Preserve the `List`-based public representation; do not introduce a
second wire-list AST solely for derivation.

Do not add a textual reader. `Certificate.lean` models the value after the wire
decoder, matching the existing Haskell seam. `Support` continues to pass the
payload through without inspecting it.

- [ ] **Step 2: Split mathematical acceptance from executable replay**

Index `Strict.Backend` by the source canonicalizer and evolve it to expose:

```lean
structure Strict.Backend (canon : String -> String) where
Form       : Type
enc        : SourceProp -> Form
enc_iff    : ∀ p q, enc p = enc q <-> equiv canon p q
accepts   : CertRef -> List Form -> Form -> Prop
replay    : CertRef -> List Form -> Form -> Bool
replay_iff :
  replay kappa delta phi = true <-> accepts kappa delta phi
sound     :
  accepts kappa delta phi -> models delta phi
```

Keep `StrictJudgment.accepted` proposition-level so the existing soundness and
non-factivity proofs continue to state mathematical facts. Use `replay_iff` when
constructing a judgment from raw data.

- [ ] **Step 3: Add an executable registry-side certificate check**

Represent registration in two stages so lookup failures retain their meaning:

```lean
structure RegisteredBackend (canon : String -> String) where
  resolve : Digest -> Option (Strict.Backend canon)

abbrev BackendRegistry (canon : String -> String) :=
  BackendId -> Option (RegisteredBackend canon)
```

A missing outer entry means that the backend identifier is not registered. A
present backend whose `resolve` returns `none` means that the digest is unknown
to that backend. Each resolved `Strict.Backend` is specialized to the selected
theory: its `accepts` and `replay` close over the fixed theory entries and check
the encoded source premises followed by those entries, matching Haskell's
`premises ++ theoryForms` free-context order. The caller cannot supply or alter
the theory contents.

Refactor `certOkOf` to use this backend-first registry while keeping it as the
relational acceptance predicate used by the frozen support judgment. Add an
executable sibling, for example:

```lean
def certOkBOf
    (reg : BackendRegistry canon)
    (beta : BackendId) (h : Digest) (kappa : CertRef)
    (As : List Atom) (C : Atom) : Bool
```

Prove:

```lean
certOkBOf reg beta h kappa As C = true
  <-> certOkOf reg beta h kappa As C
```

The proof must cover the outer backend lookup, the inner digest resolution, and
backend acceptance. Do not encode the registry as
`BackendId -> Digest -> Option Strict.Backend`: that representation cannot
distinguish an unregistered backend from an unknown digest.

The `canon` index is a coherence boundary, not documentation: a registry built
for one normalization policy must not type-check as an argument to a support
checker using another policy.

- [ ] **Step 4: Repair fixtures and audit existing theorems**

Convert existing certificate fixtures from `toString (repr e)` to symbolic
S-expressions. Re-run the existing strict-step soundness and non-factivity
theorems unchanged at their public statements.

Add an isolated executable registry matrix:

- the registered backend resolves the exact digest, then replay accepts;
- the registered backend resolves the exact digest, then replay rejects;
- the backend identifier is absent;
- the backend name is present only at a different version;
- the backend is present but the digest is unknown.

Assert the Boolean result and exercise `certOkBOf_iff` on both successful and
missing lookup paths so registry routing is pinned independently of the support
checker. For ND, register at least two digest fixtures with distinct fixed theory
lists and prove replay observes the selected list in
`premises ++ theoryForms` order.

- [ ] **Step 5: Verify the seam**

Run:

```bash
cd lean
lake build
lake env lean AxCheck.lean
```

Expected: the existing theorem surface still checks, and every new replay bridge
theorem is audited.

- [ ] **Step 6: Commit the seam**

```bash
git add lean/Lara/Certificate.lean lean/Lara/Strict.lean \
  lean/Lara/Support.lean lean/Lara/Examples.lean lean/AxCheck.lean
git commit -m "feat(lean): make strict backend replay executable"
```

---

### Task 2: Implement and Prove the Executable ND Replay Adapter

**Files:**

- Modify: `lean/Lara/ND.lean`
- Modify: `lean/Lara/Strict.lean`
- Modify: `lean/Lara/Examples.lean`
- Modify: `lean/AxCheck.lean`
- Modify: `src/Lara/Strict/ND.hs`
- Modify: `test/StrictSpec.hs`

**Interfaces:**

- Consumes: symbolic `SExpr`, the source canonicalizer, `ND.Formula`, `ND.Cert`,
  and the already-proved `ND.infer` algorithm
- Produces: a concrete `ndBackend.replay` proved equivalent to ND certificate
  acceptance, with a source encoding proved faithful to normalized atom identity

- [ ] **Step 1: Port the closed ND decoders**

Port the existing Haskell `decodeFormula` and `decodeCert` grammar into Lean as
total `Option` or `Except` functions over symbolic `SExpr`. Keep the tag
vocabulary closed and centralized.

Cover:

- atom, false, and implication formulas;
- hypothesis indices;
- lambda, application, and abort certificates;
- malformed tags, arities, and natural-number atoms.

- [ ] **Step 2: Make the ND source encoding normalization-faithful**

Replace the current predicate-only `ndEnc`, which collapses `p(a)` and `p(b)`,
with an explicit canonical serialization of the complete `nf canon` atom. Keep
the serialization inside the registered backend boundary, parameterize the
concrete ND backend by the same source canonicalizer used by checking, and prove:

```lean
ndEnc canon p = ndEnc canon q <-> equiv canon p q
```

Do not use `repr` as a wire parser or rely on an unproved injectivity claim for
generated display output. The serializer must cover numeric literals, string
literals, constructors, predicate names, arities, and argument order without
collisions.

Make the serialization a concrete Lean/Haskell wire contract rather than an
informal “canonical” renderer:

- use distinct tags for atom, numeric literal, string literal, constructor, and
  term-list boundaries;
- encode every source string as its UTF-8 byte length in canonical decimal,
  followed by `:`, followed by the exact UTF-8 payload;
- frame child counts before recursively encoded children, so nullary and nested
  constructors and argument order are unambiguous;
- reject non-canonical lengths, truncated payloads, trailing bytes, unknown tags,
  and child-count mismatches in the decoder.

Define `encodeAtomKey` and `decodeAtomKey` in Lean and prove:

```lean
decodeAtomKey (encodeAtomKey a) = some a
```

Derive `encodeAtomKey` injectivity from this left inverse, then use that result
to prove `ndEnc canon p = ndEnc canon q <-> equiv canon p q`. Port the identical
tag/framing format to `src/Lara/Strict/ND.hs`; `encodeND` must no longer use
`show . nf`.

- [ ] **Step 3: Define executable ND replay**

Decode the submitted certificate, run `ND.infer` against the free context, and
accept only when the inferred conclusion equals the requested goal:

```lean
def ndReplay (kappa : CertRef) (delta : List ND.Formula)
    (phi : ND.Formula) : Bool
```

Do not search existentially for a certificate and do not parse `repr`.

- [ ] **Step 4: Connect replay to the acceptance relation**

Define `ndAccepts` using successful symbolic decoding plus `ND.HasType`. Prove:

```lean
ndReplay kappa delta phi = true <-> ndAccepts kappa delta phi
```

Use `ND.infer_sound`, `ND.infer_complete`, and type uniqueness rather than
reproving the natural-deduction metatheory.

- [ ] **Step 5: Rebuild the concrete backend**

Instantiate all `Backend` fields for `ndBackend`, then confirm:

- `strict_step_sound` still consumes proposition-level acceptance;
- raw replay can construct `StrictJudgment`;
- the non-factivity witness uses the symbolic `hyp 0` certificate;
- malformed and goal-mismatched certificates return `false`.

- [ ] **Step 6: Add decoder/replay and encoding regressions**

Add executable examples for:

- accepted identity;
- malformed certificate;
- out-of-range hypothesis;
- inferred-goal mismatch;
- valid nested lambda/application;
- exact certificate payload sensitivity.
- distinct argument-bearing source atoms such as `p(a)` and `p(b)` remain
  distinct after ND encoding;
- canonically equivalent numeric literals receive equal ND encodings.

Add shared golden vectors to the Lean executable examples and
`test/StrictSpec.hs`, including empty strings, delimiters inside strings,
non-ASCII UTF-8, nullary and nested constructors, differing arities, and
reordered arguments. Each implementation must produce the same exact atom-key
bytes for every vector. Retain the Haskell normalization-fidelity QuickCheck
property, now backed by the explicit serializer instead of derived `Show`.

Treat the closed grammar and `ND.infer` cases as a finite branch matrix, not a
representative sample. Add:

- successful decoding for `atom`, `false`, `imp`, `hyp`, `lam`, `app`, and
  `abort`;
- universal rejection lemmas for each fixed-arity formula/certificate tag:
  whenever the supplied child-list length differs from that tag's expected
  arity, decoding fails;
- a universal unknown-tag rejection lemma, plus representative unknown-tag and
  one-shorter/one-longer fixtures for every constructor;
- rejection of empty, negative, and non-numeric hypothesis indices;
- replay rejection when an application function is not an implication, when
  its argument type mismatches, or when either child inference fails;
- successful falsum elimination and rejection of `abort` applied to a
  non-`false` proof;
- inferred-goal mismatch after otherwise successful inference.

Add a general malformed-index property for strings outside the canonical
natural-number grammar, with representative empty, negative, leading-zero, and
non-numeric fixtures. Each fixture should assert the exact decoded value or
final Boolean result; the universal lemmas, rather than an impossible infinite
fixture enumeration, discharge the full wrong-arity/index claims.

- [ ] **Step 7: Verify and commit**

Run:

```bash
cd lean
lake build
lake env lean AxCheck.lean
```

Then commit:

```bash
git add lean/Lara/ND.lean lean/Lara/Strict.lean \
  lean/Lara/Examples.lean lean/AxCheck.lean \
  src/Lara/Strict/ND.hs test/StrictSpec.hs
git commit -m "feat(lean): replay ND certificates through infer"
```

---

### Task 3: Implement the Executable Support-Term Checker

**Files:**

- Add: `lean/Lara/Check/Support.lean`
- Add: `lean/Lara/Check.lean` as the checker re-export module
- Modify: `lean/Lara/Support.lean`
- Modify: `lean/Lara/Examples.lean`
- Modify: `lean/Lara.lean`
- Modify: `lean/AxCheck.lean`

**Interfaces:**

- Consumes: `Pi`, `Gamma`, the backend-first `BackendRegistry canon`,
  `SupportTerm`, `certOkBOf`, pattern instantiation, and obligation collection
- Produces: a unique `SupportResult` or a typed/located `CheckError`

- [ ] **Step 1: Define checker results, locations, and errors**

Introduce a small symbolic checker surface:

```lean
structure SupportResult where
  conclusion  : Atom
  obligations : List QuestionId

structure CheckedSupport ... where
  term   : SupportTerm
  result : SupportResult
  valid :
    HasSupport canon Pi Gamma (certOkOf reg)
      term result.conclusion result.obligations

inductive CheckLoc where
  | root
  | premise : CheckLoc -> Nat -> CheckLoc
  | question : CheckLoc -> QuestionId -> CheckLoc

inductive CheckError where
  | r1Reference ...
  | r3Substitution ...
  | r4Premise ...
  | r5QuestionAccounting ...
  | r6Discharge ...
  | r7Assurance ...
  | r10AttackPosition ...
  | r11AttackRelation ...
  | r13Backend ...
```

Spell out every constructor payload in the implementation; do not retain
ellipses or a generic string reason. Support-side errors carry `CheckLoc`.
Attack-position errors carry the requested `Attack.Pos`, the attack kind, and a
closed symbolic reason distinguishing undefined position from wrong occurrence
kind. Attack-relation errors use a closed reason distinguishing strict target,
missing contrary, and missing exception. Reference, substitution, question,
assurance, and backend errors likewise retain the namespace-specific identifier
and the symbolic values needed to explain the failure.

Define a total projection:

```lean
def CheckError.rejectClass : CheckError -> RejectClass
```

whose equations pin the constructors above to R1, R3-R7, R10-R11, and R13.
Detailed human prose remains M3 `Lara.Diagnostics`; this Lean layer provides
stable symbolic payloads, not strings. Constructor choice, rather than a
separately supplied class field, must make class/detail mismatches impossible.

- [ ] **Step 2: Add thin executable side-condition helpers**

Reuse Lean's decidable propositions, `List.all`/`List.any`, and the existing
proved list helpers in `Lara.Support` for generic membership, `Nodup`, subset,
and equality checks. Do not build a parallel list-validation library.

Add named domain helpers only where they encode checker meaning, preserve the
specified deterministic failure order/location, or supply an `_iff` theorem
reused by multiple branches. Cover:

- duplicate-free substitution keys;
- exact substitution-domain equality;
- listwise normalized atom equivalence;
- question-key uniqueness, cover, disjointness, and no-junk checks;
- strict-rule no-question restrictions;
- assurance mode, allowlist, and backend replay checks.

Each nontrivial domain helper needs an `_iff` theorem connecting it to the
corresponding `InstSide` field. Direct uses of Lean or existing helpers should
reuse their existing adequacy lemmas rather than wrap and reprove them.

- [ ] **Step 3: Implement recursive support inference**

Define:

```lean
def inferSupport
    (canon : String -> String)
    (Pi : RuleId -> Option Rule)
    (Gamma : LeafId -> Option Atom)
    (reg : BackendRegistry canon) :
    CheckLoc -> SupportTerm -> Except CheckError SupportResult
```

For a leaf, resolve `Gamma` and return no obligations. For an instance:

1. resolve the policy rule;
2. validate the explicit substitution;
3. instantiate premise and conclusion patterns;
4. recursively infer premise and discharge terms;
5. compare inferred conclusions with premise/answer patterns under `equiv`;
6. validate `D`/`H` question accounting;
7. validate the assurance, including exact backend replay;
8. return `collectObligations`.

Compute `Cs`, `Os`, `DCs`, and `DOs` directly from recursive results so the list
length invariants follow from construction.

- [ ] **Step 4: Prove support-checker soundness**

Prove:

```lean
inferSupport canon Pi Gamma reg loc w = .ok result
  -> HasSupport canon Pi Gamma (certOkOf reg)
       w result.conclusion result.obligations
```

Build the `InstSide` witness from helper adequacy theorems and recursive
induction hypotheses.

- [ ] **Step 5: Prove support-checker completeness**

Prove:

```lean
HasSupport canon Pi Gamma (certOkOf reg) w C O
  -> inferSupport canon Pi Gamma reg loc w =
       .ok { conclusion := C, obligations := O }
```

Use `certOkBOf_iff`, the derivation's `InstSide` fields, and recursive
completeness. The theorem must establish exact output equality, not merely
`isOk`, so it discharges the executable half of support determinism.

- [ ] **Step 6: Add support fixtures**

Turn existing relational examples into algorithm assertions:

- declared leaf;
- mixed mandatory/optional holes;
- nested obligation propagation;
- discharge propagation;
- repeated-obligation deduplication;
- missing question;
- overlapping `D`/`H`;
- premise mismatch;
- discharge mismatch;
- invalid assurance;
- backend rejection.

Treat the eight validation stages as a table-driven branch matrix. Add fixtures
for:

- missing leaf and missing rule references;
- duplicate substitution keys, missing domain keys, extra domain keys, premise
  pattern instantiation failure, and conclusion pattern instantiation failure;
- too few and too many premise terms, plus an equal-length premise conclusion
  mismatch;
- duplicate discharge keys, duplicate hole keys, a missing declared question,
  overlapping discharge/hole keys, and undeclared keys on either side;
- discharge answer instantiation failure and discharge conclusion mismatch;
- a strict rule carrying a discharge or hole;
- successful defeasible `.none`, allowed strict `.trusted`, and allowlisted
  strict `.cert` assurances;
- assurance failures for the wrong rule mode, disallowed trusted mode,
  unallowlisted certifier, missing backend, wrong digest, and replay rejection.

For every negative row, assert the exact `RejectClass`, `CheckLoc`, closed reason,
and symbolic payload. Where more than one field is malformed, add focused
precedence fixtures that pin the documented validation order.

- [ ] **Step 7: Verify and commit**

Run:

```bash
cd lean
lake build
lake env lean AxCheck.lean
```

Then commit:

```bash
git add lean/Lara/Check/Support.lean lean/Lara/Check.lean \
  lean/Lara/Support.lean \
  lean/Lara/Examples.lean lean/Lara.lean lean/AxCheck.lean
git commit -m "feat(lean): add executable support-term checker"
```

---

### Task 4: Decide Contrary Matching and Implement the Attack Checker

**Files:**

- Modify: `lean/Lara/Attack.lean`
- Add: `lean/Lara/Check/Attack.lean`
- Modify: `lean/Lara/Check.lean`
- Modify: `lean/Lara/Examples.lean`
- Modify: `lean/AxCheck.lean`

**Interfaces:**

- Consumes: finite declared contrary/exception lists, ground target atoms,
  explicit target positions, and `inferSupport`
- Produces: executable `ContraryMatch`/exception decisions and an attack checker
  equivalent to `HasAttack`

- [ ] **Step 1: Implement shared-substitution ground matching**

`ContraryMatch` currently existentially quantifies over a shared substitution.
Implement a finite first-order matcher that:

- matches variables, literals, constructors, predicate symbols, and arities;
- stores raw ground terms in the substitution;
- at each equality boundary, compares `nfTerm canon lhs` with
  `nfTerm canon rhs` exactly once, consistently with `equiv`;
- threads one substitution through both sides of a contrary declaration;
- enforces repeated-variable equality;
- iterates over the finite `DefeatPolicy.contraries` list.

Do not reuse `Policy.aPatMayOverlap`: that relation is deliberately conservative
for the Path-B safety validator, while attack typing requires exact ground-instance
matching. Do not store normalized substitutions and normalize them again later;
the public canonicalizer type carries no idempotence law.

- [ ] **Step 2: Prove contrary-matcher adequacy**

Define `contraryMatchB` and prove:

```lean
contraryMatchB canon dp p q = true
  <-> ContraryMatch canon dp p q
```

Include regressions for shared variables, repeated variables, constructor/arity
mismatches, and canonicalized numeric literals. Also use a deliberately
non-idempotent `String -> String` canonicalizer in a repeated-variable fixture,
so the adequacy proof and implementation cannot silently depend on
`canon (canon x) = canon x`.

- [ ] **Step 3: Implement finite exception matching**

For undercuts, iterate over `dp.exceptions`, select entries for the target rule,
instantiate the exception pattern using the target's explicit `theta`, and compare
the result to the attacker's inferred conclusion. Prove equivalence to the
existential premises of `HasAttack.undercut`.

- [ ] **Step 4: Implement positional attack checking**

Define:

```lean
def checkAttackWithSource ... (k : Attack)
    (source : CheckedSupport ...)
    (hsource : source.term = k.source) : Except CheckError Unit

def checkAttack ... (k : Attack) : Except CheckError Unit
```

`checkAttackWithSource` is the shared core. It consumes an already checked source
result, its erased proof, and evidence that the cached term is this attack's
source. It rewrites through `hsource` using one named transport lemma, then
branches by attack constructor and inspects only the target occurrence required
by the frozen local rules. Public `checkAttack` calls `inferSupport` once,
packages a `CheckedSupport` whose owned `term` is `k.source`, and delegates with
`rfl`.

This keeps the standalone API self-contained while allowing `checkProgram` to
reuse argument checks.

Constructor-specific checks:

- rebut: target root is a defeasible instance and conclusions match a declared
  contrary;
- undercut: `subterm u pi` is a defeasible instance and its instantiated
  exception equals the source conclusion;
- undermine: `subterm u pi` is a declared leaf and its proposition matches a
  declared contrary.

Return R10 for undefined/wrong-kind positions and R11 for strict targets or
missing contrary/exception relations.

- [ ] **Step 5: Prove attack-checker soundness and completeness**

Prove both directions:

```lean
checkAttack ... k = .ok () -> HasAttack ... k
HasAttack ... k -> checkAttack ... k = .ok ()
```

Use `inferSupport_sound`/`inferSupport_complete`,
`contraryMatchB_iff`, exception adequacy, and direct computation of `subterm`.

- [ ] **Step 6: Add attack fixtures**

Exercise:

- successful rebut, nested undercut, and mixed-path undermine;
- strict-root rebut rejection;
- strict-occurrence undercut rejection;
- missing/out-of-range positions;
- wrong occurrence kind;
- undeclared contrary;
- undeclared exception;
- source support failure.

Complete the finite constructor matrix:

- rebut: missing target rule and failed target-conclusion instantiation;
- undercut: missing target rule, failed exception instantiation, strict
  occurrence, absent exception, and instantiated-exception mismatch;
- undermine: target occurrence names an undeclared leaf;
- all constructors: source support failure propagates without inspecting the
  target branch.

Every negative fixture must assert the exact R-class, requested attack position
where applicable, outer attack declaration location when run through
`checkProgram`, and closed symbolic reason.

- [ ] **Step 7: Verify and commit**

Run:

```bash
cd lean
lake build
lake env lean AxCheck.lean
```

Then commit:

```bash
git add lean/Lara/Attack.lean lean/Lara/Check/Attack.lean \
  lean/Lara/Check.lean \
  lean/Lara/Examples.lean lean/AxCheck.lean
git commit -m "feat(lean): add executable positional attack checker"
```

---

### Task 5: Construct Proof-Bearing Checked Programs

**Files:**

- Modify: `lean/Lara/Support.lean`
- Modify: `lean/Lara/Compile.lean`
- Add: `lean/Lara/Check/Program.lean`
- Modify: `lean/Lara/Check.lean`
- Modify: `lean/Lara/Examples.lean`
- Modify: `lean/AxCheck.lean`

**Interfaces:**

- Consumes: raw argument and attack lists plus the support/attack checkers
- Produces: `Except ProgramError (Compile.CheckedProgram ...)`, keeping
  valid-but-incomplete arguments distinct from frozen R-class rejections

- [ ] **Step 1: Define program-boundary outcomes**

Keep frozen checker rejections separate from compile-boundary exclusions:

```lean
inductive DeclLoc where
  | argument : Nat -> DeclLoc
  | attack : Nat -> DeclLoc

inductive ProgramError where
  | rejection : DeclLoc -> CheckError -> ProgramError
  | duplicateArgument : Nat -> Nat -> ProgramError
  | incompleteArgument : Nat -> List QuestionId -> ProgramError
```

The natural-number payloads locate declarations in the raw `args` list. An
`incompleteArgument` is not an R-class rejection: it preserves the open
obligations so the surrounding raw-program layer can route the claim to `gap`.
Support or attack checking failures are wrapped with `rejection`, whose
`DeclLoc` identifies the outer raw declaration while the nested `CheckLoc` or
attack position identifies the structural occurrence within it.

- [ ] **Step 2: Make support terms executable collection keys**

Lean 4.32 likewise cannot derive `DecidableEq` for `SupportTerm` through its
nested `List SupportTerm` and discharge lists. Implement a manual terminating
structural decision together with the required list/pair equality helpers, then
expose `DecidableEq SupportTerm`. Keep equality structural and
certificate-sensitive; the certificate-erased equality required by result 9 is
explicitly later work. Add direct equality regressions for nested premise and
discharge terms and for terms differing only in certificate payload.

- [ ] **Step 3: Strengthen the compile-boundary postcondition**

Extend `CheckedProgram` with endpoint-membership evidence:

```lean
source_declared :
  forall k, k ∈ atts -> k.source ∈ args
target_declared :
  forall k, k ∈ atts -> k.target ∈ args
```

This enforces spec R1 at the checker boundary. Without it, a well-typed attack
whose endpoint is absent from `args` is silently omitted by `Compile.Edge`.

Update existing compile theorems and fixtures without changing the frozen edge
definition. Do not add the #18 attack-completeness postcondition here.

- [ ] **Step 4: Implement program checking**

Define:

```lean
def checkProgram ... (args : List SupportTerm) (atts : List Attack) :
    Except ProgramError (Compile.CheckedProgram ...)
```

It must:

- report structurally duplicate arguments with both declaration indices;
- infer every argument once, retain an ordinary index-aligned
  `List (CheckedSupport ...)` whose entries own their `term`, and
  require `obligations = []`;
- reject attacks whose source or target is not declared;
- resolve each attack source to its retained checked argument and run
  `checkAttackWithSource`, never recursively re-infer an already checked source;
- construct all `CheckedProgram` proof fields from the checker soundness theorems.

Define a checked-cache lookup helper with a theorem exposing
`entry.term = requestedTerm` whenever lookup succeeds. Use that equality with
the single attack-source transport lemma; do not use unchecked casts or rebuild
the support derivation. Prove that the cache list remains positionally aligned
with `args`, and use the no-duplicates check to make source lookup unambiguous.

An argument with open mandatory obligations is incomplete and excluded from
`Args(P)` according to the frozen compile boundary. The surrounding raw-program
layer may route that claim to `gap`; this constructor must not compile it as a
complete AF node.

- [ ] **Step 5: Prove program-checker adequacy**

Prove:

- success exposes every `CheckedProgram` invariant;
- any raw lists satisfying the strengthened relational boundary are accepted;
- every accepted attack endpoint is present;
- no incomplete argument becomes an AF node.

- [ ] **Step 6: Add program fixtures**

Check the existing `PEx` fixture through `checkProgram` rather than constructing
all fields manually. Add rejections for:

- duplicate argument terms;
- incomplete arguments;
- undeclared attack source;
- undeclared attack target;
- individually ill-typed attacks.

Assert the exact `ProgramError` constructor and declaration index payload for
duplicate and incomplete arguments; incomplete fixtures must not return
`.rejection`. For every rejection fixture, assert the exact `RejectClass`, outer
`DeclLoc`, inner `CheckLoc` or attack position, and closed symbolic reason.

Complete the raw-list boundary matrix with:

- empty program success;
- one complete argument with no attacks;
- the full `PEx` success path;
- two structurally distinct arguments that differ only in certificate payload;
- deterministic reporting of the first duplicate index pair;
- incomplete arguments retaining their exact open-obligation list;
- deterministic first failure across multiple arguments and across multiple
  attacks;
- exact wrapping of support/attack `CheckError` values with the outer argument
  or attack declaration index.

Include a many-attacks/one-source fixture that exercises the cached program path.
The implementation review must confirm `checkProgram` contains no call to public
`checkAttack` or second call to `inferSupport` for an attack source.

- [ ] **Step 7: Verify and commit**

Run:

```bash
cd lean
lake build
lake env lean AxCheck.lean
```

Then commit:

```bash
git add lean/Lara/Support.lean lean/Lara/Compile.lean \
  lean/Lara/Check/Program.lean lean/Lara/Check.lean \
  lean/Lara/Examples.lean lean/AxCheck.lean
git commit -m "feat(lean): construct checked programs from raw declarations"
```

---

### Task 6: Close Result 1, Reconcile Documentation, and Run All Gates

**Files:**

- Modify: `lean/Lara.lean`
- Modify: `lean/README.md`
- Modify: `README.md`
- Modify: `docs/spec.md`
- Modify: `docs/m1-freeze-checklist.md`
- Modify: `docs/mechanization-plan.md`
- Modify: `ara/evidence/status/mechanization_status.md`
- Modify: `ara/logic/claims.md`
- Modify: `ara/logic/solution/mechanization.md`
- Modify: `ara/trace/` session/observation files as required by the research
  manager

**Interfaces:**

- Consumes: completed executable checkers and their theorem suite
- Produces: an honest result-1 status and a clean handoff to issues #17 and #18

- [ ] **Step 1: Audit the complete theorem surface**

List every new nontrivial helper and public theorem in `AxCheck.lean`. Run:

```bash
cd lean
lake build
lake env lean AxCheck.lean | tee /tmp/lara-issue-16-axcheck.txt
if grep -q "sorryAx" /tmp/lara-issue-16-axcheck.txt; then
  exit 1
fi
```

Review the full output for axioms outside `propext`, `Classical.choice`, and
`Quot.sound`.

- [ ] **Step 2: Run Haskell conformance gates**

Run:

```bash
cabal build all
cabal test all --test-show-details=direct
```

The only Haskell production change in this issue is the ND atom-key serializer;
no Haskell M3 support/attack checker is added. These tests ensure the Lean seam
and Haskell adapter share the same exact normalized-atom encoding.

- [ ] **Step 3: Update status without overclaiming**

Record:

- result 1: executable support/program/positional-attack checking mechanized;
- result 6: still waits on the general checker-built `Compile.Faithful` edge
  decider in #17;
- result 7: validator done, status consistency still waits on attack completeness
  in #18;
- result 3 certificate half and result 9 remain separate.

Do not call the Haskell M3 checker implemented.

- [ ] **Step 4: Capture the research session**

Use the repository's research-manager workflow to record:

- the executable-vs-relational checker bridge;
- the certificate representation decision;
- the exact contrary-matching algorithm and adequacy result;
- defects or dead ends found during mechanization;
- the remaining #17/#18 boundaries.

- [ ] **Step 5: Review repository integrity**

Run:

```bash
git diff --check
git status --short
git diff --stat origin/main...HEAD
git log --oneline --decorate origin/main..HEAD
```

Expected: only issue #16 implementation, proof, fixture, and status files changed;
no #17/#18 theorem is claimed.

- [ ] **Step 6: Commit the status reconciliation**

Stage only the reviewed status/documentation/ARA files and commit:

```bash
git commit -m "docs(m2): record executable checker mechanization"
```

## Final Acceptance Checklist

- [ ] `Backend.replay` is executable and proved equivalent to acceptance.
- [ ] ND decoding and replay use symbolic `SExpr` plus `ND.infer`.
- [ ] ND source encoding preserves exactly the full normalized source atom.
- [ ] `inferSupport` is total, sound, complete, and returns exact outputs.
- [ ] `ContraryMatch` has an exact executable ground matcher.
- [ ] `checkAttack` is total, sound, and complete for all three attack kinds.
- [ ] `checkProgram` returns a strengthened proof-bearing `CheckedProgram`.
- [ ] Program-boundary duplicate/incomplete outcomes remain distinct from
      frozen R-class checker rejections.
- [ ] Relevant R-class errors retain symbolic class and location.
- [ ] Positive and negative fixtures cover every checker branch in scope.
- [ ] Every new theorem is audited; no `sorryAx`; standard trio only.
- [ ] Lean and Haskell gates pass.
- [ ] Result-1 status is updated without claiming #17 or #18 complete.

## What Already Exists

| Existing surface | Reuse decision |
|---|---|
| `src/Lara/Strict.hs` and `src/Lara/Strict/ND.hs` | Keep as the executable conformance anchor. Change only backend identity/theory-aligned atom-key serialization, not the Haskell M3 checker boundary. |
| `lean/Lara/ND.lean` | Reuse `ND.infer`, `infer_sound`, `infer_complete`, type uniqueness, and Boolean semantics. Add symbolic decoding and replay around them. |
| `lean/Lara/Strict.lean` | Preserve proposition-level `models`, soundness, non-factivity, and public theorem intent. Strengthen the backend type and add replay. |
| `lean/Lara/Support.lean` | Preserve `HasSupport`, `InstSide`, `collectObligations`, list membership/uniqueness helpers, and the frozen `certOkOf` role. Add executable siblings rather than a second specification. |
| `lean/Lara/Attack.lean` | Preserve `HasAttack`, `ContraryMatch`, attack positions, and `subterm`. Add exact finite decision procedures beside them. |
| `lean/Lara/Compile.lean` | Preserve AF compilation and extend `CheckedProgram` only with endpoint-membership evidence needed at the raw-program boundary. |
| `Policy.aPatMayOverlap` | Intentionally do not reuse it: conservative policy-overlap validation is not exact ground contrary matching. |
| Lake, `AxCheck.lean`, Cabal, and QuickCheck | Reuse the established build, proof-audit, and Haskell property gates. No new test framework or distribution artifact is introduced. |

## NOT in Scope

- The general checker-built `Compile.Faithful` edge oracle remains issue #17;
  this plan only strengthens the raw-program boundary it will consume.
- Attack completeness and result-7 status consistency remain issue #18; this
  plan checks declared positional attacks but does not prove all semantic
  attacks were declared.
- `Backend.uses` and `certDeps` remain the next certificate-dependency item; the
  selected theory affects replay here, but exact dependency reporting is not
  added.
- Certificate-erased argument identity remains result 9; duplicate detection in
  this issue is deliberately structural and certificate-sensitive.
- The result-3 certificate half is not closed by executable replay alone.
- A Haskell M3 policy/support/attack checker and JSON codec are not added. The
  Haskell production edit is limited to the shared ND atom-key serializer.
- A textual S-expression reader is not added; `Certificate.lean` receives the
  already-decoded symbolic wire value.
- No new binary, package, container, or publish pipeline is introduced, so
  distribution work is not applicable.

## Failure Modes and Coverage

| Code path | Realistic failure | Test | Handling and visibility |
|---|---|---|---|
| Backend registry | Unknown backend, version, or theory digest | Exact registry matrix | Typed R13 rejection distinguishes outer identity lookup, inner digest resolution, and replay rejection. |
| Certificate decode/replay | Malformed tag, arity, index, proof term, or goal | Universal decoder lemmas plus constructor/inference fixtures | Total decoder/replay returns rejection; no parser exception or silent acceptance. |
| ND atom encoding | Two source atoms collide or Lean/Haskell drift | Left-inverse/injectivity proofs, golden vectors, QuickCheck | Build/test failure blocks the change before a certificate can be misinterpreted. |
| Support inference | Bad reference, substitution, premise, question accounting, discharge, or assurance | Eight-stage branch matrix with precedence cases | Located `CheckError` exposes exact R-class and symbolic payload. |
| Contrary matching | Shared/repeated variables compare under an invalid idempotence assumption | Adequacy theorem and non-idempotent-canonicalizer fixture | Raw substitutions and one normalization boundary produce an explicit R11 result. |
| Attack checking | Missing position, wrong occurrence kind, strict target, missing contrary/exception | Per-constructor attack matrix | R10/R11 includes the requested position and closed symbolic reason. |
| Program checking | Duplicate, incomplete, undeclared endpoint, or ill-typed attack | Raw-list matrix and exact wrapping assertions | `ProgramError` separates incomplete/gap routing from frozen checker rejection. |
| Checked-source reuse | Many attacks trigger repeated support inference or reuse the wrong cached term | Many-attacks/one-source fixture and cache lookup theorem | Owned-term cache plus equality transport reuses one proof; lookup failure is explicit. |

No reviewed failure mode is both untested and unhandled; critical silent gaps:
zero.

## Worktree Parallelization

| Lane | Work | Modules | Depends on |
|---|---|---|---|
| A | Tasks 1-5, then Lean/docs portion of Task 6 | `lean/Lara/`, `docs/`, `ara/` | Sequential: each checker consumes the prior theorem surface |
| B | Haskell half of Task 2: shared atom-key serializer and golden/property tests | `src/Lara/Strict/`, `test/` | The frozen framing contract in this plan |
| Gate | Final Task 6 build, audit, and status reconciliation | repository-wide gates | Lanes A and B merged |

Launch Lane B in parallel with Lane A's Task 1. Merge Lane B before the Lean ND
adapter's cross-language golden-vector check, then continue Lane A sequentially.
The lanes do not share modules. Do not split the Lean tasks across worktrees:
they repeatedly touch `Strict.lean`, `Support.lean`, `Examples.lean`, and
`AxCheck.lean`, so the merge cost exceeds the concurrency benefit.

Keep the existing top-level flow diagram current. Add short inline ASCII pipeline
comments beside the backend-first lookup in `lean/Lara/Strict.lean` and the
checked-argument cache/attack lookup in `lean/Lara/Check/Program.lean`; these are
the two non-obvious flows future maintainers must preserve.

## TODOS.md Updates

No new TODO candidates emerged. Issues #17 and #18 already track the genuine
follow-on work, while result 3, result 9, `certDeps`, and the Haskell M3 checker
are existing roadmap boundaries rather than newly discovered tasks.

## Implementation Tasks

Synthesized from this review's findings. Each task derives from a specific
finding above. Run with Claude Code or Codex; checkbox as you ship.

- [ ] **T1 (P1, human: ~4h / CC: ~30min)** — strict seam — Make registry identity and normalization coherence structural
  - Surfaced by: Architecture and outside review — pair-indexed lookup hid backend-vs-digest failures and did not tie a registry to its canonicalizer.
  - Files: `lean/Lara/Certificate.lean`, `lean/Lara/Strict.lean`, `lean/Lara/Support.lean`
  - Verify: `cd lean && lake build && lake env lean AxCheck.lean`
- [ ] **T2 (P1, human: ~6h / CC: ~45min)** — ND wire — Implement one injective Lean/Haskell atom-key format
  - Surfaced by: Architecture and outside review — display-based serialization had no explicit injectivity or cross-language contract.
  - Files: `lean/Lara/ND.lean`, `src/Lara/Strict/ND.hs`, `test/StrictSpec.hs`, `lean/Lara/Examples.lean`
  - Verify: `cd lean && lake build && lake env lean AxCheck.lean`, then `cabal test all --test-show-details=direct`
- [ ] **T3 (P1, human: ~4h / CC: ~30min)** — checker surface — Split checker modules and define exact typed diagnostics
  - Surfaced by: Code Quality review — one checker module and generic errors would couple unrelated recursion and permit R-class/detail drift.
  - Files: `lean/Lara/Check/Support.lean`, `lean/Lara/Check/Attack.lean`, `lean/Lara/Check/Program.lean`, `lean/Lara/Check.lean`
  - Verify: `cd lean && lake build`
- [ ] **T4 (P1, human: ~8h / CC: ~60min)** — support checking — Implement one `Except`-first support inference path with full branch proofs
  - Surfaced by: Code Quality and Test review — exact validation order, soundness/completeness, and every support rejection branch need one source of truth.
  - Files: `lean/Lara/Check/Support.lean`, `lean/Lara/Support.lean`, `lean/Lara/Examples.lean`, `lean/AxCheck.lean`
  - Verify: `cd lean && lake build && lake env lean AxCheck.lean`
- [ ] **T5 (P1, human: ~6h / CC: ~45min)** — attack checking — Prove exact matching without assuming canonicalizer idempotence
  - Surfaced by: Code Quality, Test, and outside review — normalized substitution storage could invalidate repeated-variable matching.
  - Files: `lean/Lara/Attack.lean`, `lean/Lara/Check/Attack.lean`, `lean/Lara/Examples.lean`, `lean/AxCheck.lean`
  - Verify: `cd lean && lake build && lake env lean AxCheck.lean`
- [ ] **T6 (P1, human: ~6h / CC: ~45min)** — program checking — Cache owned checked terms and preserve compile-boundary outcomes
  - Surfaced by: Performance and outside review — indexed evidence was underspecified for lists and public attack checking would repeat inference.
  - Files: `lean/Lara/Support.lean`, `lean/Lara/Compile.lean`, `lean/Lara/Check/Program.lean`, `lean/Lara/Examples.lean`
  - Verify: `cd lean && lake build && lake env lean AxCheck.lean`
- [ ] **T7 (P1, human: ~4h / CC: ~30min)** — coverage — Complete universal decoder lemmas and all finite checker matrices
  - Surfaced by: Test and outside review — “every wrong arity” was infinite as fixtures, while several negative branches lacked explicit cases.
  - Files: `lean/Lara/Examples.lean`, `lean/AxCheck.lean`, `test/StrictSpec.hs`
  - Verify: `cd lean && lake build && lake env lean AxCheck.lean`, then `cabal test all --test-show-details=direct`
- [ ] **T8 (P2, human: ~2h / CC: ~15min)** — status and gates — Reconcile result claims after all executable checks pass
  - Surfaced by: Scope review — result 1 can advance without overclaiming the separately tracked #17/#18 work.
  - Files: `docs/`, `ara/evidence/status/`, `ara/logic/`, `ara/trace/`
  - Verify: run every Task 6 gate and inspect `git diff --stat origin/main...HEAD`

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | NOT RUN | Standard scope challenge completed in this review |
| Codex Review | `/codex review` | Independent 2nd opinion | 1 | ISSUES RESOLVED | 9 findings, 9/9 explicitly decided |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | CLEAR (PLAN) | 11 section issues, 0 critical gaps |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | NOT APPLICABLE | No UI or visual scope |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | NOT RUN | No new developer-facing product surface |

**CODEX:** Found registry ambiguity, cross-language identity/serialization gaps,
canonicalizer assumptions, dependent-cache ambiguity, and an impossible finite
arity-test requirement; eight changes were folded into the plan and the
Option-core staging recommendation was explicitly rejected.

**CROSS-MODEL:** Both reviews agreed the frozen relations should remain the
specification and that exact branch/error coverage is required. The outside
review materially strengthened the registry, serializer, matcher, and cache
interfaces without changing the accepted six-task product scope.

**VERDICT:** ENG CLEARED — ready to implement.

NO UNRESOLVED DECISIONS
