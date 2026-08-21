# Named Certificate Authoring (#131 premise labels, #132 named nd@1) Implementation Plan

> **STATUS (2026-08-21): Part A landed; Part B is the remaining work.**
> Tasks A1–A4 are complete and shipped as `lara-syntax@0.8` (grammar Appendix G,
> `examples/S7/`, #131). Everything durable from Part A now lives in `docs/`, so
> only Part B (Tasks B1–B6, `lara-syntax@0.9`, #132) is still executable from
> this file. Delete the file once Part B lands, moving anything durable into
> `docs/` first.
>
> One deviation from Part A as written, recorded here rather than only in the
> commit: Task A2's end-to-end message pin went into `test/CliSpec.hs` rather
> than `test/ElaborateSpec.hs`, because that is where this repo's exact-stderr
> rejection pins live and it exercises the whole `.lara` door.

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking. Work on branch
> `feat/131-132-named-certificate-authoring` (Part A) and continue on it after Part A merges
> (Part B). Do not combine Part A and Part B into one PR.

**Goal:** Complete symbolic premise citation across all three strict backends and add named
local binders for `nd@1`: certificate premise references may cite a rule's declared premise
**label** (`lara-syntax@0.8`, closes #131), and `nd@1` proof terms gain a named presentation
form — named `lam` binders, `(prem …)` / `(thy …)` references — elaborator-lowered to the
frozen de Bruijn kernel grammar (`lara-syntax@0.9`, closes #132). Formula annotations remain
opaque encoded atom keys and theory entries remain numeric, so this is *not* full named
authoring of ND certificates; that boundary is deliberate (decision 5 and Task B4's follow-up
issue).

**Architecture:** Both features are presentation-only lowering passes in the validated-not-verified
elaborator, exactly like `lara-syntax@0.6` (#105): zero lexer/parser changes (the verbatim
`sexpLitP` payload capture already admits every new spelling), zero `lara-core@0.2` / wire /
checker / backend changes, and byte-identity with the numeric spelling as the headline theorem.
Part A extends the existing resolver (`certSlotResolver`) with a third name class backed by the
already-tested `premiseLabelIndex`. Part B adds a new recursive lowering pass for `nd@1`
(`Lara.Elaborate.NDNamed`) that owns the binder discipline, plus its own Lean mechanization.

**Tech Stack:** GHC2021 Haskell + Cabal + QuickCheck (`test/CertSlotsSpec.hs`,
`test/ElaborateSpec.hs`, new `test/NDNamedSpec.hs`), Lean 4 (`lean/Lara/CertSlots.lean`
precedent, new `lean/Lara/NDNamed.lean`, `lean/AxCheck.lean` gate), committed worked-example
goldens (`examples/S7`, `examples/S8` on the S6 pattern).

**Spec:** GitHub issues #131 and #132; `docs/lara-surface-grammar.md` Appendix E (esp. E.7,
which records both designs' starting points); `src/Lara/Strict/ND.hs` module header (the frozen
kernel grammar).

## Global Constraints

- No wire, `.core.sexp`, `expected.json`, checker-judgment, strict-backend, or replay change.
  Every frozen artifact must lower to itself byte-identically (conservativity is a theorem in
  each part, not a hope).
- No lexer or parser rule changes. The payload's `SExpr` tree and authored *atom spellings*
  survive parse/print — `parse (print (parse f)) == parse f` must keep holding — but payload
  trivia and formatting are canonicalized by `printSExpr`, as today (`sexpLitP` decodes to
  `SExpr`, `test/SyntaxSpec.hs` header disclaims byte-level round-trip). Byte-identity claims
  in this plan are always about the **lowered Unit / `.core.sexp`**, never the authored
  `.lara` bytes.
- Concrete spellings live in exactly one place: `prem` comes from `Lara.Strict.Cell.Tag`,
  `hyp`/`lam`/`app`/`abort` from `Lara.Strict.ND.Tag`; the one new keyword (`thy`) gets its own
  closed table in its one home. No string literal respells a wire keyword (project CLAUDE.md,
  "Keep the compiler core symbolic").
- Lean proofs stay `sorry`-free within the axiom trio (`propext`, `Classical.choice`,
  `Quot.sound`); `lean/AxCheck.lean` covers every new theorem; run `scripts/check-axioms.sh`.
- Haskell files stay within ~200–400 lines; split rather than grow.
- Conventional Commits (`feat(syntax): …`, `test(syntax): …`, `docs: …`).
- Two presentation-version bumps: Part A is `lara-syntax@0.8` (Appendix G), Part B is
  `lara-syntax@0.9` (Appendix H). #131's issue text asks for its own bump; keeping the small
  S–M feature unhostage to the L feature is the point of the split.

## Design decisions (settled here; flip only with researcher approval)

1. **Labels reuse the `(prem s)` spelling** — no new head keyword. A name now resolves in
   *three* classes: rule premise label ∪ declared leaves ∪ prior arguments.
2. **Cross-class collision is a hard error, even when referents agree.** A name that is both a
   premise label and a leaf/prior is `CertSlotLabelAmbiguous`, mirroring the one collision
   policy of `@0.6`/`@0.7` (E.2, F.4): never silently one of them. Rationale: predictability
   beats convenience; an agreeing-referent carve-out would be the first conditional rule in an
   otherwise uniform policy.
3. **nd@1 named references are head-separated namespaces**: `(hyp x)` resolves *only* enclosing
   named binders; `(prem s)` resolves *only* premise slots (numeral | leaf/prior | label — the
   shared resolver from Part A); `(thy N)` resolves *only* theory entries, numerically. This
   dissolves E.7's collision-policy worry by construction — no two classes ever compete for one
   syntactic position.
4. **Binder shadowing is rejected** (`(lam x _ (lam x _ …))` is an error). Lean allows
   shadowing; we don't, because a shadowed name silently changes which index a reference lowers
   to, and `@0.7`'s whole theme is that the surface never silently means something else.
   Relaxing later is additive; tightening later would be breaking.
5. **Theory entries are cited numerically only** (`(thy N)`). Theory declarations
   (`theory digest = [prop, …]`) give entries no source names; inventing a naming scheme for
   them is out of scope (worth a follow-up issue if authors ever want it).
6. **`(prem N)` numeric is legal in nd@1's named form and is slot-stable**: it lowers to
   `hyp (depth + N)`, so even a fully numeric author never hand-shifts indices under binders
   again. `N ≥ nPrem` is an elaboration error (`CertNdPremOutOfRange`), never a silent slide
   into the theory offsets.
7. **The nd@1 pass lives in `Lara.Elaborate.NDNamed`**, not under `Lara.Strict`. It needs
   `isIdentStart` (surface) and `SlotRefError` (elaborate), which the Strict layer must not
   import. Wire spellings are still imported from the backend's own tag tables, so the concrete
   grammar has one home. E.7 already concedes this feature "teach[es] the presentation layer
   the full ND grammar" — that is its recorded cost.
8. **Dead-wire rule extends to nd@1**: a named spelling (`(prem …)`, `(thy …)`,
   `(hyp <ident>)`, arity-3 `lam`) that survives lowering — because it sits in a formula
   position or inside a non-grammar subtree — is an elaboration error (`CertNdResidualNamed`),
   never handed to the backend. Marker-free junk still passes through to R13 exactly as today.

## Background & motivation (why these two, why together)

`lara-syntax@0.6` gave `ord@1`/`ra@1` certificates symbolic premise slots but had to exclude
`nd@1`: its `hyp i` counts local `lam` binders first, then premises, then theory entries by
offset, so no fixed payload position names a premise (E.7). Hand-shifting de Bruijn indices
under binders is the most author-hostile spelling left on the surface (#132). Separately, `@0.6`
resolves names by *locating the referent's term in the premise list*, which hard-errors when one
leaf feeds two premises (`CertSlotMultiSlot`) — the one case names cannot express. A rule's
declared premise **labels** name the slots themselves (`premiseLabelIndex`,
`src/Lara/Elaborate/Internal.hs:316`), covering exactly that gap with an existing, tested
mechanism (#131).

They are one project because they share one resolution surface: Part A grows the resolver that
Part B's `(prem s)` references then reuse verbatim. Landing #131 first means nd@1's named form
is born with the complete namespace (leaf ∪ prior ∪ label) instead of needing a follow-up.

Author-visible before/after (S8's shape):

```text
# @0.7 (today): the author computes 1 + slot because a binder is open
assurance = cert(nd@1, sha256:strict-v1-theory-0, (app (lam <KEY_A> (hyp 2)) (hyp 0)))

# @0.9: names, no arithmetic
assurance = cert(nd@1, sha256:strict-v1-theory-0, (app (lam h <KEY_A> (prem b_leaf)) (prem a_leaf)))
```

---

# Part A — `lara-syntax@0.8`: premise-label citation (#131) — LANDED

### Task A1: Resolver third class + error plumbing

**Files:**
- Modify: `src/Lara/Elaborate/CertSlots.hs` (add `SlotNameLabelAmbiguous` to `SlotRefError`)
- Modify: `src/Lara/Elaborate/Internal.hs:497-570` (`certSlotResolver`, `lowerArgCert`,
  `certSlotError` gain the `Rule`; call sites at `:427` and `:465` already have `rule` bound)
- Modify: `src/Lara/Elaborate/Error.hs` (new `CertSlotLabelAmbiguous`; `CertSlotUnresolved`
  gains `RuleId`; two renderer templates)
- Test: `test/CertSlotsSpec.hs`

**Interfaces:**
- Consumes: `premiseLabelIndex :: Rule -> String -> Maybe Int` (`Internal.hs:316`, unchanged);
  `refMatches` (`Internal.hs:486`, unchanged).
- Produces: `certSlotResolver :: Env -> Rule -> [(ArgId, SupportTerm)] -> [SupportTerm] -> String -> Either SlotRefError Int`;
  `lowerArgCert :: Env -> Rule -> [(ArgId, SupportTerm)] -> ArgId -> [SupportTerm] -> Assurance -> Either ElabError Assurance`;
  `ElabError` constructors `CertSlotLabelAmbiguous ArgId BackendId Int ArgRef RuleId` and
  `CertSlotUnresolved ArgId BackendId Int ArgRef RuleId`. Part B calls `certSlotResolver`
  with this exact signature.

- [x] **Step 1: Write the failing tests** (model on CertSlotsSpec's existing parse+elaborate
  fixtures; reuse its S6-style in-memory program/policy pair, adding labels to the rule's
  premise list — surface form `premises = [ base: reports(...), new: reports(...) ]`, App B.4):

```haskell
-- | A label citation lowers to the numeric twin's exact Unit (byte-identity).
prop_labelCitationLowersToNumericTwin :: Property
prop_labelCitationLowersToNumericTwin = once $
  elabUnit (fixtureWithCert "(ordcmp (prem base) (prem new))")
    === elabUnit (fixtureWithCert "(ordcmp (prem 0) (prem 1))")

-- | One leaf feeding two premises: label citation succeeds where the leaf
-- name is CertSlotMultiSlot (the @0.6-impossible case, issue #131's headline).
prop_labelResolvesMultiSlot :: Property
prop_labelResolvesMultiSlot = once $
  isRight (elabUnit (multiSlotFixture "(ordcmp (prem left) (prem right))"))
    .&&. errorHas "occupies premise slots 0 and 1"
           (elabUnit (multiSlotFixture "(ordcmp (prem same_cell) (prem 1))"))

-- | A name that is both a label and a declared leaf is a hard error, even
-- though both would resolve (decision 2).
prop_labelLeafCollisionIsHardError :: Property
prop_labelLeafCollisionIsHardError = once $
  errorHas "is ambiguous between rule 'lt_recheck' premise label and a declared leaf or prior argument"
    (elabUnit (collisionFixture "(ordcmp (prem base_cell) (prem 1))"))

-- | Unresolved message now names the rule and the label class.
prop_unresolvedNamesAllThreeClasses :: Property
prop_unresolvedNamesAllThreeClasses = once $
  errorHas "names neither a premise label of rule 'lt_recheck', a declared leaf, nor a prior argument"
    (elabUnit (fixtureWithCert "(ordcmp (prem no_such) (prem 1))"))
```

  `fixtureWithCert` / `multiSlotFixture` / `collisionFixture` are new local helpers built the
  way the file's existing second-half fixtures build program+policy sources; `multiSlotFixture`
  labels the rule `[ left: p, right: p ]` with both premises matched by one leaf `same_cell`;
  `collisionFixture` names a leaf `base_cell` AND labels a premise `base_cell`. Register the
  four props in the file's export group.

- [x] **Step 2: Run to verify they fail**: `cabal test lara-test --test-options='-m CertSlots'`
  (or the suite's prop-group runner; match how `Spec.hs` wires `certSlotsSpecProps`).
  Expected: compile failure on missing helpers first, then assertion failures.

- [x] **Step 3: Implement.** `CertSlots.hs` — extend the resolver-verdict group of
  `SlotRefError`:

```haskell
  | -- | the name is both a rule premise label and a declared leaf or prior
    -- argument (lara-syntax@0.8, #131): never silently either class.
    SlotNameLabelAmbiguous
```

  `Internal.hs` — thread the rule; labels are consulted first-class, not as fallback:

```haskell
certSlotResolver
  :: Env -> Rule -> [(ArgId, SupportTerm)] -> [SupportTerm] -> String
  -> Either SlotRefError Int
certSlotResolver env rule priors prems name =
  case (premiseLabelIndex rule name, refMatches env priors name) of
    (Just i, ([], []))
      | i < length prems -> Right i
      | otherwise -> Left SlotNameNotAPremise -- authored premise list shorter than the rule's
    (Just _, _) -> Left SlotNameLabelAmbiguous
    (Nothing, ([(leafId, _)], [])) -> locate [SLeaf leafId]
    (Nothing, ([], [(_, term)])) -> locate [term, SLeaf (LeafId name)]
    (Nothing, ([], [])) -> Left SlotNameUnresolved
    (Nothing, _) -> Left SlotNameAmbiguous
  where
    locate candidates =
      case [i | (i, p) <- zip [0 ..] prems, p `elem` candidates] of
        [i] -> Right i
        [] -> Left SlotNameNotAPremise
        (i : j : _) -> Left (SlotNameMultiSlot i j)
```

  `lowerArgCert` gains `Rule` between `Env` and priors; both call sites pass the `rule`
  already in scope (`elabInstantiation` line 427, `elabTerm` line 465). `certSlotError`
  gains a `RuleId` parameter and maps the two changed/new verdicts:

```haskell
  SlotNameUnresolved -> CertSlotUnresolved aid backend version ref rid
  SlotNameLabelAmbiguous -> CertSlotLabelAmbiguous aid backend version ref rid
```

  `Error.hs` — constructors (extend the `@0.6` family block, `Error.hs:57-74`) and templates
  (renderer block at `Error.hs:280-295`):

```haskell
  CertSlotUnresolved a b v n (RuleId r) ->
    certSlotPrefix a b v n ++ "names neither a premise label of rule '" ++ r
      ++ "', a declared leaf, nor a prior argument"
  CertSlotLabelAmbiguous a b v n (RuleId r) ->
    certSlotPrefix a b v n ++ "is ambiguous between rule '" ++ r
      ++ "' premise label and a declared leaf or prior argument"
```

- [x] **Step 4: Run the full suite**: `cabal test`. The four new props pass; every existing
  prop stays green (the unlabelled-rule path is bitwise the old behavior:
  `premiseLabelIndex` returns `Nothing` when `rulePremiseLabels` is empty).

- [x] **Step 5: Commit**:
  `git commit -m "feat(syntax): premise-label certificate citation (lara-syntax@0.8, #131)"`

### Task A2: Recursion + regression pins

**Files:**
- Test: `test/CertSlotsSpec.hs` (extend the existing AST-level recursion pin), `test/ElaborateSpec.hs`

**Interfaces:** consumes Task A1's signatures only.

- [x] **Step 1: Write the tests.** (a) Extend the E.6 recursion pin (the existing
  hand-built-AST nested-assurance test in CertSlotsSpec): a nested instance's certificate
  citing a *label of the nested rule* lowers against the nested premise list, and a label of
  the outer rule is `CertSlotUnresolved` there. (b) In ElaborateSpec, pin that the changed
  unresolved message appears verbatim in one end-to-end rejection (guards the E.5→G template
  migration). (c) A QuickCheck property: for any fixture rule with no labels, elaboration of
  a symbolic-citing program is *unchanged* by Task A1 (compare against a golden captured from
  the numeric spelling — the existing byte-identity props already imply this; add only if not
  already covered, else skip with a comment naming the covering prop).

- [x] **Step 2: Run to verify the new tests fail / pass appropriately**, then `cabal test`.

- [x] **Step 3: Commit**: `git commit -m "test(syntax): label-citation recursion and message pins (#131)"`

### Task A3: Worked example S7 (committed byte-identity witness)

**Files:**
- Create: `examples/S7/example.lara`, `examples/S7/ord-labeled-v1.policy.lara`,
  `examples/S7/example.core.sexp`, `examples/S7/expected.json`
- Modify: `examples/README.md` (table row + notes section), `test/WorkedExamplesSpec.hs`
  (add `prop_S7` on the `prop_S6` pattern, `WorkedExamplesSpec.hs:426-443`),
  `test/DifferentialSpec.hs` (golden-freshness table entry, `DifferentialSpec.hs:335-340`)

**Interfaces:** none new; consumes the S6 example pattern verbatim.

- [x] **Step 1: Author the policy** — copy `examples/S6/ord-named-v1.policy.lara`, rename the
  policy `ord-labeled-v1` and the digest `sha256:ord-labeled-v1-theory-0`, label
  `lt_recheck`'s premises:

```text
rule lt_recheck(S, B, Q, D, Exp, Sv, Bv)
  mode       = strict
  premises   = [ base: reports(Exp, score_cell(B, Q, D, Bv)),
                 new:  reports(Exp, score_cell(S, Q, D, Sv)) ]
  conclusion = num_lt(Bv, Sv)
  allow-trusted = false
  certifiers = [ (ord@1, sha256:ord-labeled-v1-theory-0) ]
```

  and add a second rule demonstrating the multi-slot case labels exist for:

```text
rule le_reflex(S1, S2, Q, D, Exp, Lv, Rv)
  mode       = strict
  premises   = [ left:  reports(Exp, score_cell(S1, Q, D, Lv)),
                 right: reports(Exp, score_cell(S2, Q, D, Rv)) ]
  conclusion = num_le(Lv, Rv)
  allow-trusted = false
  certifiers = [ (ord@1, sha256:ord-labeled-v1-theory-0) ]
```

- [x] **Step 2: Author the artifact** — S6's artifact with two claims: `c1` as in S6 but the
  certificate cites labels `(ordcmp (prem base) (prem new))`; `c2` = `num_le(0.71, 0.71)`
  supported `by le_reflex from [base_cell, base_cell]` with certificate
  `(ordcmp (prem left) (prem right))` — the same leaf occupying both slots, citable **only**
  because labels name the slots (the `@0.6` `CertSlotMultiSlot` dead end, spelled out in the
  file's header comment the way S6's header narrates #105). Run `scripts/infer-sigma.hs` for
  the signature block as S6's policy documents.

- [x] **Step 3: Generate + verify the goldens.** Produce `example.core.sexp`/`expected.json`
  the same way S6's were produced (see `test/WorkedExamplesSpec.hs` `runExample` and the
  freshness check in DifferentialSpec — the committed golden must equal the numeric twin's
  bytes; verify by temporarily switching the certificates to `(prem 0)`/`(prem 1)` and
  diffing the regenerated `.core.sexp`). Wire `prop_S7` + the DifferentialSpec row; run
  `cabal test`.

- [x] **Step 4: Commit**: `git commit -m "feat(examples): S7 premise-label citation worked example (#131)"`

### Task A4: Docs — Appendix G, rejection surface, Lean no-change note

**Files:**
- Modify: `docs/lara-surface-grammar.md` (new Appendix G; E.2/E.3/E.5/E.7 cross-ref banners),
  `docs/rejection-surface.md` (§1.2: the new/changed elaboration rejections)
- Verify-only: `lean/Lara/CertSlots.lean`, `scripts/check-axioms.sh`,
  `scripts/check-presentation-parity.sh`

**Interfaces:** none.

- [x] **Step 1: Write Appendix G** (`## Appendix G — lara-syntax@0.8 (premise-label
  citation, <landing date>)`) containing, in the house appendix voice: scope (additive, no
  lexer/parser change, no kernel change); the three-class namespace and resolution rule (the
  Task A1 code's semantics in prose); the hard collision policy including the
  agreeing-referent case, with decision 2's rationale; the multi-slot resolution it enables
  (supersedes E.3's "cite a numeric slot there" as the only fallback — labels are the other
  exit); the **updated normative template list** (all seven `CertSlot*` messages, two changed
  from E.5, which gets a "superseded by Appendix G" banner on the list only); the Lean note —
  `lean/Lara/CertSlots.lean` parameterizes over an abstract resolver
  `ρ : String → Option Nat`, so `lower_id_of_no_symbolic` and `lower_eq_numeric_subst` hold
  verbatim over the label-extended resolver and **no Lean change is owed** (the `@0.7` F.1
  precedent for stating this); the S7 pointer as the standing byte-identity witness.
- [x] **Step 2: Update E.7's second bullet** with a `*Resolved at @0.8:*` banner (E.2's
  existing `*Resolved at @0.7:*` is the pattern), and add the two rejection-surface rows
  (label collision; the reworded unresolved message).
- [x] **Step 3: Verify the claims**: `lake build` (in `lean/`), `scripts/check-axioms.sh`,
  `scripts/check-presentation-parity.sh`, full `cabal test`. All must pass with no Lean edit.
- [x] **Step 4: Commit**: `git commit -m "docs(syntax): Appendix G — lara-syntax@0.8 premise-label citation (#131)"`
- [x] **Step 5: Open PR for Part A** (`gh pr create`), title
  `lara-syntax@0.8: premise-label certificate citation (#131)`, body citing Appendix G and
  `Closes #131`. Merge before starting Part B.

---

# Part B — `lara-syntax@0.9`: named nd@1 proof terms (#132)

### Task B1: `Lara.Elaborate.NDNamed` — the lowering pass (TDD, pure layer)

**Files:**
- Create: `src/Lara/Elaborate/NDNamed.hs` (~250 lines with haddocks)
- Create: `test/NDNamedSpec.hs`; register in `test/Spec.hs` and the cabal test-suite module list
- Modify: `lara.cabal` (exposed module + test module)

**Interfaces:**
- Consumes: `Lara.Strict.ND` (`Tag (..)`, `tagToString`, `parseTag`, `ndBackendId`),
  `Lara.Strict.Cell` (`Tag (TPrem)`, `tagToString`, `parseCanonicalNat`),
  `Lara.Syntax (isIdentStart)`, `Lara.Elaborate.CertSlots (SlotRefError (..))`.
- Produces (Task B2 relies on these exact names):

```haskell
data NamedRefError
  = NamedPremSlot SlotRefError -- (prem s): shared-resolver failure, incl. non-canonical numeral
  | NamedPremOutOfRange Integer Int -- (prem N): the numeral, nPrem
  | NamedBinderUnbound      -- (hyp x): no enclosing named binder x
  | NamedBinderShadowed     -- (lam x _ _) under an enclosing named binder x
  | NamedMalformedBinder    -- arity-3 lam whose binder atom cannot start an identifier
  | NamedNonCanonicalIndex  -- hyp atom neither numeral nor identifier; thy atom not a numeral
  | NamedResidual           -- named spelling where the nd@1 grammar gives it no meaning
  deriving (Eq, Show)

-- | The one home of the named-form theory-reference keyword.
data NamedTag = NTThy deriving (Eq, Ord, Show, Enum, Bounded)
namedTagToString :: NamedTag -> String   -- NTThy -> "thy"

lowerNamedPayload
  :: (String -> Either SlotRefError Int) -- ^ premise resolver (Part A's certSlotResolver, partially applied)
  -> Int                                 -- ^ nPrem: this instance's premise count
  -> SExpr
  -> Either (String, NamedRefError) SExpr
```

- [ ] **Step 1: Write the failing unit tests first** (pure, fixture resolver — mirror
  CertSlotsSpec's first half; build kernel payloads through the ND `Tag` table, never string
  literals). The conformance vectors, with `ρ = [("a",0),("b",1)]`, `nPrem = 2`:

| # | input | expected |
|---|---|---|
| 1 | `(hyp 0)` | unchanged (kernel conservativity) |
| 2 | `(prem 1)` at depth 0 | `(hyp 1)` |
| 3 | `(lam <F> (prem b))` | `(lam <F> (hyp 2))` — shift under an anonymous kernel binder |
| 4 | `(app (lam h <F> (hyp h)) (prem a))` | `(app (lam <F> (hyp 0)) (hyp 0))` |
| 5 | `(lam h <F> (lam k <G> (hyp h)))` | binders lower innermost-first: body `(hyp 1)` |
| 6 | `(lam <F> (thy 0))` | `(lam <F> (hyp 3))` (= depth 1 + nPrem 2 + 0; the public API always enters at depth 0, so depth is built by wrapping) |
| 7 | `(prem 2)` | `Left ("2", NamedPremOutOfRange 2 2)` — never a silent theory slide |
| 8 | `(hyp x)` unbound | `Left ("x", NamedBinderUnbound)` |
| 9 | `(lam h <F> (lam h <G> (hyp h)))` | `Left ("h", NamedBinderShadowed)` |
| 10 | `(lam 0 <F> (hyp 0))` (arity-3, numeral binder) | `Left ("0", NamedMalformedBinder)` |
| 11 | `(hyp 007)` | `Left ("007", NamedNonCanonicalIndex)` |
| 12 | `(prem 007)` | `Left ("007", NamedPremSlot SlotNonCanonicalNumeral)` |
| 13 | `(lam (prem a) (hyp 0))` — named marker in a **formula** position | `Left ("a", NamedResidual)` |
| 14 | `(foo (prem a))` — non-grammar node containing a marker | `Left ("a", NamedResidual)` |
| 15 | `(foo bar)` — marker-free junk | unchanged (backend rejects at R13, as today) |
| 16 | `(prem q)` with `ρ q = Left SlotNameUnresolved` | `Left ("q", NamedPremSlot SlotNameUnresolved)` |
| 17 | `(lam h <F> (hyp 0))` | `(lam <F> (hyp 0))` — numeric `hyp` stays raw de Bruijn under a named binder (contrast with 3/18: only `prem`/`thy`/named `hyp` shift) |
| 18 | `(lam h <F> (prem 0))` | `(lam <F> (hyp 1))` — the slot-stable citation vector 17 contrasts with |
| 19 | `(lam é <F> (hyp é))` | `(lam <F> (hyp 0))` — `isIdentStart` is Unicode-aware; a non-ASCII binder/reference is legal (the CertSlotsSpec Unicode-pin precedent) |

- [ ] **Step 2: Run to verify failure** (module doesn't exist → compile failure, then reds).

- [ ] **Step 3: Implement.** Structure (this is the real skeleton; keep haddocks in the
  CertSlots.hs voice, including a pipeline diagram):

```haskell
lowerNamedPayload resolve nPrem payload = do
  lowered <- go [] payload
  case firstResidual lowered of
    Just s -> Left (s, NamedResidual)
    Nothing -> pure lowered
  where
    depthOf env = toInteger (length env)
    hypNode i = SList [SAtom (tagToString THyp), SAtom (show i)]

    go :: [Maybe String] -> SExpr -> Either (String, NamedRefError) SExpr
    go env e = case e of
      SList [SAtom k, SAtom a] | parseTag k == Just THyp ->
        case parseCanonicalNat a of
          Just _ -> pure e                                   -- kernel index, untouched
          Nothing
            | startsIdent a -> case bindingIndex a env of
                Just i -> pure (hypNode i)
                Nothing -> Left (a, NamedBinderUnbound)
            | otherwise -> Left (a, NamedNonCanonicalIndex)
      SList [SAtom k, SAtom a] | k == Cell.tagToString Cell.TPrem ->
        case parseCanonicalNat a of
          Just n | n < toInteger nPrem -> pure (hypNode (depthOf env + n))
                 | otherwise -> Left (a, NamedPremOutOfRange n nPrem)
          Nothing
            | startsIdent a -> case resolve a of
                Right slot -> pure (hypNode (depthOf env + toInteger slot))
                Left err -> Left (a, NamedPremSlot err)
            | otherwise -> Left (a, NamedPremSlot SlotNonCanonicalNumeral)
      SList [SAtom k, SAtom a] | k == namedTagToString NTThy ->
        case parseCanonicalNat a of
          Just n -> pure (hypNode (depthOf env + toInteger nPrem + n))
          Nothing -> Left (a, NamedNonCanonicalIndex)
      SList [SAtom k, phi, body] | parseTag k == Just TLam ->      -- kernel binder: anonymous
        (\b -> SList [SAtom k, phi, b]) <$> go (Nothing : env) body
      SList [SAtom k, SAtom x, phi, body] | parseTag k == Just TLam -> -- named binder
        if not (startsIdent x) then Left (x, NamedMalformedBinder)
        else if Just x `elem` env then Left (x, NamedBinderShadowed)
        else (\b -> SList [SAtom k, phi, b]) <$> go (Just x : env) body
      SList [SAtom k, f, x] | parseTag k == Just TApp ->
        (\f' x' -> SList [SAtom k, f', x']) <$> go env f <*> go env x
      SList [SAtom k, phi, body] | parseTag k == Just TAbort ->
        (\b -> SList [SAtom k, phi, b]) <$> go env body
      _ -> pure e   -- not cert grammar: backend-owned; firstResidual polices markers
```

  `bindingIndex x env` = index of the first `Just x` counting from the head (innermost).
  `firstResidual` = leftmost-outermost scan for any named marker: a `(prem _)` node, a
  `(thy _)` node, a `(hyp a)` with non-numeral `a`, or a 4-element `lam`. `startsIdent` =
  `isIdentStart` on the first char (the CertSlots.hs `startsSourceIdentifier` twin — factor
  it out or duplicate the 3-liner with a cross-comment; do NOT export a new Syntax helper).

- [ ] **Step 4: Run to green**, then **Step 5: Commit**:
  `git commit -m "feat(syntax): nd@1 named-form lowering pass (lara-syntax@0.9, #132)"`

### Task B2: Elaborator dispatch + `CertNd*` error family

**Files:**
- Modify: `src/Lara/Elaborate/Internal.hs` (`lowerArgCert` dispatches nd@1 to the new pass),
  `src/Lara/Elaborate/Error.hs` (six constructors + templates)
- Test: `test/NDNamedSpec.hs` (parse+elaborate half), `test/ElaborateSpec.hs` (one message pin)

**Interfaces:**
- Consumes: Task B1's `lowerNamedPayload`/`NamedRefError`; Part A's `certSlotResolver`.
- Produces: `ElabError` constructors (Task B4's doc appendix and rejection-surface rows quote
  these templates verbatim):

```haskell
  | CertNdBinderUnbound ArgId BackendId Int ArgRef
  | CertNdBinderShadowed ArgId BackendId Int ArgRef
  | CertNdMalformedBinder ArgId BackendId Int ArgRef
  | CertNdNonCanonicalIndex ArgId BackendId Int ArgRef
  | CertNdPremOutOfRange ArgId BackendId Int ArgRef Integer Int
  | CertNdResidualNamed ArgId BackendId Int ArgRef
```

- [ ] **Step 1: Write the failing tests** (parse+elaborate, S1-shaped fixtures on the
  `strict-v1` policy): the named spelling of S1's `(hyp 0)` — `(prem e1)` — elaborates to
  S1's exact Unit bytes; conformance vector 4's program-level twin (named redex vs numeric
  redex, byte-identical Units and verdicts); one end-to-end rejection per new template;
  the R13-boundary invariant, **both sides tested explicitly**: (a) tampering a byte of the
  *lowered* `.core.sexp` payload still rejects at R13 (the S6-pattern test, unchanged), and
  a marker-free malformed authored payload (e.g. `(foo bar)`) still passes elaboration and
  rejects at R13 exactly as today; (b) a payload carrying a named-form marker that cannot be
  lowered (e.g. `(foo (prem e1))`) now rejects at elaboration as `CertNdResidualNamed` —
  the deliberate migration, mirroring `@0.6`'s moved rejection site (E.4); printer
  round-trip of the named spelling at the AST level — `parse (print (parse f)) == parse f`
  with the named atoms surviving as atoms (payload trivia canonicalizes; no byte-level
  claim, per the Global Constraints).

- [ ] **Step 2: Implement the dispatch.** In `lowerArgCert` (post-Part A it holds `rule`):

```haskell
lowerArgCert env rule priors aid prems assurance = case assurance of
  AssuranceCert cert
    | isNdNamed cert ->
        case lowerNamedPayload (certSlotResolver env rule priors prems)
               (length prems) (certPayload cert) of
          Right p -> Right (AssuranceCert cert {certPayload = p})
          Left (name, err) -> Left (ndNamedError aid rule cert name err)
    | otherwise -> {- existing lowerCertPayload path, unchanged -}
  _ -> Right assurance
  where
    isNdNamed c =
      certBackend c == BackendId (Strict.backendName ndBackendId)
        && certVersion c == Strict.backendVersion ndBackendId
```

  (`ndBackendId` imported from `Lara.Strict.ND` — the `nd` spelling keeps its one home.)
  `ndNamedError` maps `NamedPremSlot e` through the existing `certSlotError` (so `(prem s)`
  failures reuse the `CertSlot*` family and messages verbatim) and the six nd-specific
  verdicts to the new constructors. Templates (renderer, `certSlotPrefix` style):

```text
arg 'A': certificate 'B' reference 'N' names no enclosing lam binder
arg 'A': certificate 'B' lam binder 'N' shadows an enclosing binder; rename one
arg 'A': certificate 'B' lam binder 'N' is not a source identifier
arg 'A': certificate 'B' index 'N' is not a canonical index (use unsigned decimal with no leading zeros)
arg 'A': certificate 'B' premise reference 'N' names slot I but this argument has only J premise slot(s)
arg 'A': certificate 'B' named spelling 'N' sits where the nd@1 grammar gives it no meaning
```

- [ ] **Step 3: Run to green** (`cabal test`), then **Step 4: Commit**:
  `git commit -m "feat(syntax): elaborate nd@1 named certificates (#132)"`

### Task B3: Properties — conservativity and translation equivalence

**Files:**
- Test: `test/NDNamedSpec.hs`

**Interfaces:** consumes B1 only.

- [ ] **Step 1: Write a kernel-cert generator** (sized QuickCheck `Gen Cert` over
  `Lara.Strict.ND.Cert`, plus an encoder `certToSExpr` built from the `Tag` table — the
  module haddock explicitly licenses conformance tests to share the table).
- [ ] **Step 2: Property — conservativity**: for every generated kernel cert `c` and any
  resolver, `lowerNamedPayload ρ n (certToSExpr c) === Right (certToSExpr c)`. This is the
  frozen-corpus safety property (every existing artifact lowers to itself).
- [ ] **Step 3: Property — translation equivalence**: a small inductive of *named* terms with
  a reference de Bruijn translation written independently (textbook: carry
  `[Maybe String]`, count all binders for depth), a renderer to `SExpr`, and the property
  that `lowerNamedPayload` on the rendering equals rendering the reference translation —
  for well-scoped terms; ill-scoped generation asserts the matching error. Keep the named
  inductive local to the spec (it is the test's oracle, not product code).
- [ ] **Step 4: Run** (`cabal test`), **Step 5: Commit**:
  `git commit -m "test(syntax): nd@1 named-form conservativity and translation properties (#132)"`

### Task B4: Worked example S8

**Files:**
- Create: `examples/S8/example.lara`, `examples/S8/example.core.sexp`,
  `examples/S8/expected.json` (reuse S1's policy file — copy it in as S8's policy the way S6
  carries its own, or reference S1's if `runExample` requires a local file; follow S1's layout)
- Modify: `examples/README.md`, `test/WorkedExamplesSpec.hs` (`prop_S8`),
  `test/DifferentialSpec.hs` (freshness row)

- [ ] **Step 1: Author** S1's artifact with the named spelling. The argument keeps S1's
  honesty-note framing (a deliberate detour to exercise the binder):

```text
arg a1 : supports(c1) by certified_citation from [e1]
  assurance = cert(nd@1, sha256:strict-v1-theory-0,
    (app (lam h <KEY_E1> (hyp h)) (prem e1)))
```

  where `<KEY_E1>` is `(atom "…")` holding `encodeAtomKey (nf <e1's prop>)` — compute it
  with a `runghc` one-liner against `Lara.Strict.ND.encodeAtomKey` and paste; the header
  comment must show that command (this is the surviving hand-hostile spot; note it as the
  candidate follow-up issue: named formula annotations). The numeric twin is
  `(app (lam <KEY_E1> (hyp 0)) (hyp 0))`; the committed golden carries the twin's bytes.
- [ ] **Step 2: Generate + verify goldens** exactly as Task A3 Step 3 (regenerate from the
  numeric twin, diff, commit the identical bytes). Wire `prop_S8` + DifferentialSpec row;
  header comment narrates the shift-free citation under a binder (`(prem e1)` at depth 1 →
  `(hyp 1)`… here depth 1 + slot 0 → `(hyp 1)` inside the lam vs `(hyp 0)` outside — spell
  the two lowered indices out in the comment; that contrast IS the feature).
- [ ] **Step 3: `cabal test`**, **Step 4: Commit**:
  `git commit -m "feat(examples): S8 named nd@1 worked example (#132)"`

### Task B5: Lean mechanization

**Files:**
- Create: `lean/Lara/NDNamed.lean`
- Modify: `lean/Lara.lean` (import), `lean/AxCheck.lean` (new theorems)

**Interfaces:** consumes `Lara.ND` (Tag/Cert), `Lara.Support.SExpr`, `Lara.Cell`
(`Tag.prem`, `parseCanonNat`) — same spelling discipline as `CertSlots.lean`'s header
documents.

- [ ] **Step 1: Port the pass**: `lowerNamed (startsIdent : String → Bool)
  (ρ : String → Option Nat) (nPrem : Nat) : List (Option String) → SExpr → Option SExpr`,
  mirroring Task B1 line-for-line (`none` models every failure kind uniformly; the
  classifier and resolver stay abstract — CertSlots.lean's exact parameterization
  discipline, for the same ASCII-`isAlpha` reason its header records).
- [ ] **Step 2: Theorem 1 — conservativity.** Define `encodeCert : ND.Cert → SExpr` from the
  ND tag table (add beside `Lara.ND` if absent) and prove
  `lowerNamed_id_of_kernel : ∀ c env, lowerNamed startsIdent ρ nPrem env (encodeCert c) = some (encodeCert c)`
  by structural induction (each kernel node matches the untouched branch; `hyp` payloads are
  canonical numerals by `Nat.repr` canonicity, the `parseCanonNat` round-trip lemma already
  in `Lara.Cell`). This is the frozen-corpus safety theorem.
- [ ] **Step 3: Theorem 2 — translation.** Inductive `NCert` (named certs: `hypN Nat`,
  `hypX String`, `prem (Nat ⊕ String)`, `thy Nat`, `lam (Option String) ND.Formula NCert`,
  `app`, `abort ND.Formula NCert`), rendered via `encodeFormula : ND.Formula → SExpr` (the
  `decodeFormula` inverse, `lean/Lara/ND.lean:60,150` — add `encodeFormula` beside
  `encodeCert` if absent), `render : NCert → SExpr`,
  `toDB : List (Option String) → NCert → Option ND.Cert` (the textbook translation), and
  `lowerNamed_eq_translation : WellFormed t → lowerNamed … env (render t) = (encodeCert ∘ ·) <$> toDB env t`
  where `WellFormed` carries the binder-identifier and no-shadowing side conditions.
  **Why `ND.Formula` and not opaque `SExpr` annotations:** the pass rejects residual named
  markers *anywhere*, including formula positions, so an arbitrary `SExpr` formula holding
  `(prem a)` makes `lowerNamed` fail while `toDB` succeeds — the equivalence would be false.
  A formula rendered from `ND.Formula` contains only `atom`/`false`/`imp` nodes, so the
  residual scan provably cannot fire on a `render`-image; prove that as the key supporting
  lemma (`render_formula_no_marker`).
- [ ] **Step 4: Gate.** Add both theorems to `AxCheck.lean`; `lake build` +
  `scripts/check-axioms.sh` pass `sorry`-free within the axiom trio. `cabal test` still
  green (conformance vectors in NDNamedSpec are the cross-language witnesses; port vectors
  1–7 and 17–19 of Task B1's table into Lean `example` checks to pin the two
  implementations together, the CertSlots.lean conformance-vector precedent).
- [ ] **Step 5: Commit**:
  `git commit -m "feat(lean): mechanize nd@1 named-form lowering (#132)"`

### Task B6: Docs — Appendix H, rejection surface, closeout

**Files:**
- Modify: `docs/lara-surface-grammar.md` (Appendix H; E.7 first-bullet `*Resolved at @0.9:*`
  banner), `docs/rejection-surface.md` (§1.2 rows for the six `CertNd*` templates + the
  reused `CertSlot*` note), `examples/README.md` (if not finished in B4)

- [ ] **Step 1: Write Appendix H** (`lara-syntax@0.9`, named nd@1 proof terms): the named
  grammar (Task B1's table-form, as a grammar block); head-separated namespaces (decision 3)
  and why E.7's collision worry dissolves; the no-shadowing rule (decision 4) with the
  Lean-allows-it rejected alternative; `(thy N)` numeric-only (decision 5) and the
  named-formula-annotation follow-up pointer; the depth arithmetic
  (`prem s → hyp (depth + slot)`, `thy N → hyp (depth + nPrem + N)`) and the out-of-range
  guard (decision 6); the extended dead-wire rule (decision 8) and exactly what still
  passes through to R13; the normative `CertNd*` template list; conservativity +
  translation theorems by name as the mechanization record; S8 as the standing
  byte-identity witness; the trust note (validated-not-verified elaborator pass, Lean
  mirror carries the math — the CertSlots.lean split, restated).
- [ ] **Step 2: Run everything**: `cabal build && cabal test`, `lake build`,
  `scripts/check-axioms.sh`, `scripts/check-presentation-parity.sh`,
  `scripts/walking-skeleton-golden.sh` (if the examples flow through it — check its header).
- [ ] **Step 3: Commit + PR**:
  `git commit -m "docs(syntax): Appendix H — lara-syntax@0.9 named nd@1 proof terms (#132)"`;
  `gh pr create` titled `lara-syntax@0.9: named nd@1 proof terms (#132)`, body citing
  Appendix H, the two theorems, and `Closes #132`. If the formula-annotation follow-up is
  real after S8 (it will be), open its issue (`gh issue create`) and reference it from the
  PR — deferrals live in issues, never only in comments (repo CLAUDE.md).
- [ ] **Step 4: Delete this plan file** in the closing PR (executed plans are deleted, with
  anything durable already moved into `docs/` — Appendices G/H carry all of it). Run
  `/research-manager` at session end: two surface-version features is a qualifying change.

---

## Self-review checklist (run after implementation, before each PR)

- Every changed `CertSlot*` message has: a renderer template, an Appendix G/H entry, a
  rejection-surface row, and at least one test pinning the exact string.
- `git grep -n '"nd"' src/` shows no new literal outside the ND tag/identity tables.
- The S7/S8 goldens were regenerated from the numeric twins and byte-compared, not assumed.
- `plans/popl-research-review.md` and any doc that says "nd@1 is excluded from named slots"
  got the pointer sweep (see the post-@0.7 sweep commit `dc26572` for the checklist shape).
