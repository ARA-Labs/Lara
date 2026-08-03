# Strict-Certificate Worked Example Implementation Plan

> **Status: complete — closed by PR #39.**

> **For agentic workers:** REQUIRED SUB-SKILL: Use `executing-plans` to
> implement this plan task by task. Keep checkbox state current as each focused
> test and gate lands.

**Goal:** One worked example (`examples/S1/`) whose claim is supported by a
**strict** rule carrying an `nd@1` certificate, end-to-end
(`.lara` → elaborate → verdict + `.core.sexp`), closing the suite's
defeasible-only honesty gap (`examples/README.md`; TODOS P3 item
"Strict-certificate worked example (nd@1 frontend cert path)").

**Architecture:** Pure presentation-layer (`lara-syntax@0.1` → additive
`lara-syntax@0.2`) change: the AST already carries `Assurance`/`Cert`
(`src/Lara/AST.hs:315-318, 302-308`), the wire codec already round-trips
certs and theories (`src/Lara/Wire.hs:582-604, 729-733, 808-815`), and the
checker/driver already replays `nd@1` (`src/Lara/Driver.hs:55-63`). What is
missing is (a) surface syntax for support-term assurance and for a
policy-carried theory table, (b) elaborator lowering (today it forces
`AssuranceNone`, `src/Lara/Elaborate.hs:257`), and (c) the CLI threading the
policy's theory table into the elaborator's `TheoryRegistry` (today hardcoded
`emptyRegistry`, `app/Main.hs:113`). No Unit-reachable type changes;
`lara-core@0.1` untouched.

**Tech Stack:** Haskell (megaparsec-style hand-rolled `P` monad in
`Lara.Syntax`), QuickCheck specs, `scripts/gen-worked-examples.hs` golden
regeneration, Lean differential via committed `.core.sexp`.

## Global Constraints

- **No frozen (Unit-reachable) type changes.** `lara-syntax@0.2` must decode to
  the same `lara-core@0.1` abstract syntax (versioning rule,
  `docs/lara-surface-grammar.md` header; A0.5 precedent: presentation-only AST
  additions are legal, `Policy` is not Unit-reachable).
- **`parse ∘ print == id` (spec result 12) must keep holding** for both new
  constructs; the canonical printer owns field order.
- **The theory table is a trusted input.** It lives in the *policy* file
  (co-located, version-pinned, digest-covered by M4b's replay manifest), never
  in the artifact program — "instantiates, never defines" (spec §4/§5).
- **The elaborator stays thin.** It lowers syntax faithfully; mode/assurance
  legality is the checker's job (R7, `src/Lara/SupportTerm.hs:327-332`). Do not
  duplicate checker logic in `Lara.Elaborate`.
- **Only hypothesis-reuse certs certify source-referenced content.**
  `encodeND` maps every source `Prop` to a flat atom
  (`src/Lara/Strict/ND.hs:245-246`), and theory entries are encoded the same
  way, so no surface construct can reference an implication formula. Richer
  `lam`/`app` payload structure is *technically* replayable but only by
  hand-spelling the backend's internal atom keys (`encodeAtomKey (nf p)`) via
  payload-embedded formulas (`decodeFormula`, `src/Lara/Strict/ND.hs:346-351`)
  — opaque, never produced by any surface encoding, and certifying nothing
  about source-level structure; `abort` cannot close a goal from atomic
  premises at all (no `FFalse` hypothesis is derivable). The example mirrors
  the proven fixture `strictCertAccept` (`scripts/gen-corpus.hs:333-355`,
  golden-tested at `test/DifferentialSpec.hs:102-104`): strict rule with
  premise ≡ conclusion, empty theory, payload `(hyp 0)`. The example must
  carry an honesty comment stating this (see Task S4 for the precise wording).
- Digests in surface syntax use the colon form (`ident:body`,
  `docs/lara-surface-grammar.md` §1.3), matching `digestLit`
  (`src/Lara/Syntax.hs:266-274`) and `certRefP` (`src/Lara/Syntax.hs:968-978`).

---

## Task S0: grammar addendum — `lara-syntax@0.2`

**Files:**
- Modify: `docs/lara-surface-grammar.md`

**Interfaces:**
- Produces: the frozen surface contract Tasks S1–S4 implement. Two additions,
  both additive over `@0.1`:
  - `assuranceLine ::= "assurance" "=" ( "none" | "trusted" | "cert" "(" backendRef "," digest "," sexp ")" )`
    — an optional arg-block line, folded with `discharge`/`open` lines in any
    order, at most one per arg. Default (absent) is `none`.
  - `theoryLine ::= "theory" digest "=" "[" [ prop { "," prop } ] "]"`
    — a policy declaration, partitioned like `rule`/`contrary`/`exception`.
- The addendum MUST state: additive version bump (decodes to `lara-core@0.1`);
  `sexp` is the wire S-expression sub-grammar (`src/Lara/Wire.hs:30-65`
  lexical rules); assurance on a bare `leaf(…)` term is rejected by the
  *parser* (fail fast — a silently discarded assurance would mislead the
  author; the checker never sees it), and a second `assurance` line in one
  arg block or a duplicate theory digest in one policy is likewise a parse
  error. Mode/assurance legality on rule applications remains the checker's
  job (R7/R13).

- [x] **Step 1: Write the addendum**

Append a new section to `docs/lara-surface-grammar.md`:

```markdown
---

## Appendix A — `lara-syntax@0.2` (additive, 2026-07-29)

Two additive constructs over `lara-syntax@0.1`, both decoding to the same
`lara-core@0.1` abstract syntax (spec result 12 unaffected; no Unit-reachable
type changes). Motivation: the strict-certificate worked example
(`plans/2026-07-29-strict-cert-worked-example.md`); the Unit-level cert path
(`Lara.Strict.ND`, `Driver.buildCertOk`) predates this surface.

### A.1 Support-term assurance (arg blocks)

assuranceLine ::= "assurance" "=" assuranceValue
assuranceValue ::= "none" | "trusted" | "cert" "(" backendRef "," digest "," sexp ")"

- Optional, at most one per `arg` block; folds with `discharge`/`open` lines
  in any order. Absent means `none` (`AssuranceNone`). A second `assurance`
  line in the same block is a **parse error** (not last-wins).
- Only meaningful on a rule application; `assurance` on a bare `leaf(…)`
  support term is a **parse error** (the checker has no rule to check it
  against, and silently dropping it would mislead the author).
- `sexp` is the wire S-expression sub-grammar (canonical atom/string rules of
  `Lara.Wire`); the payload is opaque — only the named backend decodes it
  (spec §5).
- Legality (strict rule, `allow-trusted`, certifier allowlist, replay) is
  enforced by the checker as R7/R13 (spec §4, §5, §10.1), never by the parser
  or elaborator.

### A.2 Policy theory table (trusted input)

theoryLine ::= "theory" digest "=" "[" [ prop { "," prop } ] "]"

- A policy-level declaration, partitioned like `rule`/`contrary`/`exception`;
  order-insensitive, canonical printer emits it last.
- The theory table is a *trusted* input (spec §5: theory digests are part of
  replay identity, §2.1). It lives in the co-located policy file so replay
  pinning covers it; artifact programs may reference digests (in `cert(…)`)
  but may never define the table.
- `theory h = [p1, …]` declares that digest `h` names the theory whose entries
  are the ground propositions `p1, …` (empty list allowed: the empty theory).
- Declaring the same digest twice in one policy is a **parse error** (the
  replay oracle's `lookup` would otherwise silently use the first entry).
```

- [x] **Step 2: Commit**

```bash
git add docs/lara-surface-grammar.md
git commit -m "docs(grammar): lara-syntax@0.2 — support-term assurance + policy theory table"
```

---

## Task S1: policy theory table — AST field, parser, printer

**Files:**
- Modify: `src/Lara/AST.hs:278-285` (the `Policy` record)
- Modify: `src/Lara/Syntax.hs` (`PolicyAcc` 828, `policyP` 830-842,
  `policyDecls` 844-852, `printPolicy` 1165-1176)
- Modify: `src/Lara/Negatives.hs` (6 `Policy` construction sites, grep
  `policyAdmission =`: lines 292, 353, 401, 442, 480, 518) — add the new field
- Test: `test/SyntaxSpec.hs` — including `genPolicy` (339-344), the 7th
  `Policy` construction site the grep MISSES (applicative `Policy <$> …`,
  positionally breaks when the record gains a field)

**Interfaces:**
- Produces: `Policy.policyTheories :: [(TheoryDigest, [Prop])]` (Task S3
  consumes it at the CLI call site); `theoryLineP :: P (TheoryDigest, [Prop])`.

- [x] **Step 1: Write the failing test**

Add to `test/SyntaxSpec.hs`, matching the module's existing round-trip test
style (result-12 pins):

```haskell
prop_policyTheoriesRoundTrip :: Property
prop_policyTheoriesRoundTrip =
  let src =
        unlines
          [ "policy strict-v1"
          , "rule certified_citation(X, D)"
          , "  mode = strict"
          , "  premises = [ holds(X, D) ]"
          , "  conclusion = holds(X, D)"
          , "  allow-trusted = false"
          , "  certifiers = [ (nd@1, sha256:strict-v1-theory-0) ]"
          , "theory sha256:strict-v1-theory-0 = []"
          ]
   in case parsePolicy src of
        Left e -> counterexample ("parse failed: " ++ show e) False
        Right pol ->
          conjoin
            [ counterexample "round-trip" $
                parsePolicy (printPolicy pol) === Right pol
            , counterexample "theories" $
                policyTheories pol
                  === [(TheoryDigest "sha256:strict-v1-theory-0", [])]
            ]
```

- [x] **Step 2: Run test to verify it fails**

Run: `cabal test` (or the suite's focused filter for SyntaxSpec)
Expected: FAIL — `policyTheories` not in scope / `Policy` missing field.

- [x] **Step 3: Implement**

`src/Lara/AST.hs` — add the field to `Policy` (after `policyAdmission`):

```haskell
data Policy = Policy
  { policyId :: PolicyId
  , policyRules :: [Rule]
  , policyContraries :: [Contrary]
  , policyExceptions :: [Exception]
  , policyAdmission :: [((LeafKind, Provenance), Admission)]
  , policyTheories :: [(TheoryDigest, [Prop])]
    -- ^ Trusted theory table (lara-syntax@0.2, grammar App. A.2); lowered to
    -- 'unitTheories' via the elaborator's 'TheoryRegistry'.
  }
```

`src/Lara/Syntax.hs` — extend the accumulator, dispatch, entry, and printer:

```haskell
data PolicyAcc
  = PolicyAcc [Rule] [Contrary] [Exception]
      [((LeafKind, Provenance), Admission)] [(TheoryDigest, [Prop])]

policyP :: P Policy
policyP = do
  keyword "policy"
  pid <- identifier
  PolicyAcc rs cs es adm ts <- policyDecls (PolicyAcc [] [] [] [] [])
  pure
    Policy
      { policyId = PolicyId pid
      , policyRules = rs
      , policyContraries = cs
      , policyExceptions = es
      , policyAdmission = adm
      , policyTheories = ts
      }

policyDecls :: PolicyAcc -> P PolicyAcc
policyDecls acc@(PolicyAcc rs cs es adm ts) = do
  mw <- peekIdent
  case mw of
    Just "rule" -> do r <- ruleP; policyDecls (PolicyAcc (rs ++ [r]) cs es adm ts)
    Just "contrary" -> do c <- contraryP; policyDecls (PolicyAcc rs (cs ++ [c]) es adm ts)
    Just "exception" -> do e <- exceptionP; policyDecls (PolicyAcc rs cs (es ++ [e]) adm ts)
    Just "admission" -> do a <- admissionP; policyDecls (PolicyAcc rs cs es (adm ++ a) ts)
    Just "theory" -> do
      t@(TheoryDigest d, _) <- theoryLineP
      if any (\(TheoryDigest d', _) -> d' == d) ts
        then failP ("duplicate theory digest: " ++ d)
        else policyDecls (PolicyAcc rs cs es adm (ts ++ [t]))
    _ -> pure acc

-- | @theoryLine ::= "theory" digest "=" "[" [ prop { "," prop } ] "]"@
-- (grammar App. A.2).
theoryLineP :: P (TheoryDigest, [Prop])
theoryLineP = do
  keyword "theory"
  Digest d <- digestLit
  symbol '='
  ps <- brackets propP
  pure (TheoryDigest d, ps)
```

Printer — append to `printPolicy` after the admission block:

```haskell
printTheories :: [(TheoryDigest, [Prop])] -> [String]
printTheories [] = []
printTheories ts =
  "" : [ "theory " ++ d ++ " = [" ++ intercalate ", " (map printProp ps) ++ "]"
       | (TheoryDigest d, ps) <- ts
       ]
```

and in `printPolicy`'s list: `++ printAdmission (policyAdmission p) ++ printTheories (policyTheories p)`.

Fix every other `Policy` construction site: run
`grep -rn "policyAdmission =" --include=*.hs src test scripts` AND
`grep -rn "Policy" --include=*.hs test | grep -v policyAdmission` — the first
finds the 6 record-syntax sites in `src/Lara/Negatives.hs`; the second catches
`genPolicy` (`test/SyntaxSpec.hs:339-344`), which builds
`Policy <$> … <*> …` applicatively and breaks positionally. Convert
`genPolicy` to record syntax (`Policy { policyId = …, …, policyTheories = ts }`)
and extend it to sometimes emit theory lines (small list of
`(TheoryDigest, [Prop])` pairs, mostly empty) so `prop_policyRoundTrip`
(2000 successes) actually exercises `theoryLineP`/`printTheories`.

- [x] **Step 4: Run test to verify it passes**

Run: `cabal test`
Expected: PASS (new round-trip test green; existing suite unaffected — no
shipped policy uses `theory`, and `printTheories [] = []`).

- [x] **Step 4b: Negative parse tests (theory lines)**

Add table-driven negative props to `test/SyntaxSpec.hs` (match existing
style), one case per new `failP` branch: duplicate theory digest in one
policy → parse error; `theory` line missing `=` → parse error; unterminated
`[` → parse error; malformed digest (no colon body) → parse error.

- [x] **Step 5: Commit**

```bash
git add src/Lara/AST.hs src/Lara/Syntax.hs src/Lara/Negatives.hs test/SyntaxSpec.hs
git commit -m "feat(syntax): policy theory table (lara-syntax@0.2 App. A.2)"
```

---

## Task S2: support-term assurance — parser + printer

**Files:**
- Modify: `src/Lara/Syntax.hs` (`argBody` 720-741, new `assuranceP`/`sexpLitP`/
  `backendVersionP`, `certRefP` 968-978 refactored onto `backendVersionP`,
  `printSupportTerm` 1134-1146; add `import Lara.Wire (parseSExpr, printSExpr)`
  and `import Lara.Strict (SExpr)` to the import list)
- Test: `test/SyntaxSpec.hs` (plus `genProgram`'s support-term generator —
  extend to sometimes emit assurance so `prop_programRoundTrip` covers it)

**Interfaces:**
- Consumes: `digestLit`, `natLit`, `identifier`, `symbol`, `peekIdent`,
  `getInput`, `advanceP`, `failP` (all existing in `Lara.Syntax`);
  `Lara.Wire.parseSExpr :: String -> Either ParseError SExpr`,
  `Lara.Wire.printSExpr :: SExpr -> String`.
- Produces: `assuranceP :: P Assurance`; arg blocks accept the `assurance`
  line; `printSupportTerm` emits it. `Lara.Wire` does not import `Lara.Syntax`
  (no cycle).

- [x] **Step 1: Write the failing test**

Add to `test/SyntaxSpec.hs`:

```haskell
prop_argAssuranceRoundTrip :: Property
prop_argAssuranceRoundTrip =
  let src =
        unlines
          [ "artifact paper_42 at sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
          , "policy strict-v1"
          , "use backends [nd@1]"
          , ""
          , "claim c1"
          , "  nl = \"The safety invariant holds for deployment D\""
          , "  formal = holds(safety_invariant, D)"
          , "  binding = { author = alice, rationale = \"r\", audit-status = reviewed }"
          , ""
          , "leaf e1 : holds(safety_invariant, D)"
          , "  kind = attested"
          , "  provenance = user"
          , "  refs = [evidence/safety_audit.txt#section=invariants]"
          , ""
          , "arg a1 : supports(c1) by certified_citation(safety_invariant, D)"
          , "  assurance = cert(nd@1, sha256:strict-v1-theory-0, (hyp 0))"
          , ""
          , "status c1"
          ]
   in case parseProgram src of
        Left e -> counterexample ("parse failed: " ++ show e) False
        Right prog ->
          counterexample "round-trip" $
            parseProgram (printProgram prog) === Right prog
```

- [x] **Step 2: Run test to verify it fails**

Run: `cabal test`
Expected: FAIL — `assurance` line rejected by `argBody` (`peekIdent` falls
through, then the next-declaration parse errors).

- [x] **Step 3: Implement**

In `src/Lara/Syntax.hs`, extend `argBody` with the assurance fold. The
accumulator tracks whether assurance was already set (grammar: at most one
per arg), and rejects assurance on a non-rule base term:

```haskell
argBody :: SupportTerm -> P SupportTerm
argBody base = go base False
  where
    go acc seenAssurance = do
      mw <- peekIdent
      case mw of
        Just "discharge" -> do
          keyword "discharge"
          q <- identifier
          keyword "with"
          ref <- identifier
          go (addDischarge acc (QuestionId q) (SLeaf (LeafId ref))) seenAssurance
        Just "open" -> do
          keyword "open"
          _q <- identifier
          keyword "as"
          o <- identifier
          go (addHole acc (ObligationId o)) seenAssurance
        Just "assurance" -> do
          if seenAssurance
            then failP "duplicate assurance line in arg block"
            else case acc of
              SRule {} -> do
                a <- assuranceP
                go (setAssurance acc a) True
              _ -> failP "assurance requires a rule application, not a bare leaf"
        _ -> pure acc

setAssurance :: SupportTerm -> Assurance -> SupportTerm
setAssurance (SRule r th pr ds hs _) a = SRule r th pr ds hs a
setAssurance t _ = t -- unreachable: argBody rejects non-SRule bases above
```

Factor the shared `backend@version` parser out of `certRefP` (968-978) —
`assuranceP` needs the same `ident@nat` shape (DRY: this is the third parser
of that shape; `backendRefP` at 489 yields a `String` version for
`use backends` and cannot be reused):

```haskell
-- | @backendRef ::= ident "@" nat@ — shared by 'certRefP' and 'assuranceP'.
backendVersionP :: P (BackendId, Int)
backendVersionP = do
  b <- identifier
  symbol '@'
  v <- natLit
  pure (BackendId b, v)

certRefP :: P CertRef
certRefP = do
  symbol '('
  (b, v) <- backendVersionP
  symbol ','
  Digest dig <- digestLit
  symbol ')'
  pure (CertRef b v (TheoryDigest dig))
```
-- | @assuranceLine@ (grammar App. A.1). The cert payload is a raw
-- S-expression captured by 'sexpLitP' and decoded by the wire codec.
assuranceP :: P Assurance
assuranceP = do
  keyword "assurance"
  symbol '='
  mw <- peekIdent
  case mw of
    Just "none" -> AssuranceNone <$ keyword "none"
    Just "trusted" -> AssuranceTrusted <$ keyword "trusted"
    Just "cert" -> do
      keyword "cert"
      symbol '('
      (b, v) <- backendVersionP
      symbol ','
      Digest dig <- digestLit
      symbol ','
      payload <- sexpLitP
      symbol ')'
      pure (AssuranceCert (Cert b v (TheoryDigest dig) payload))
    _ -> failP "expected an assurance (none | trusted | cert(…))"

-- | Consume one character.
char1 :: P Char
char1 = do
  s <- getInput
  case s of
    (c : _) -> c <$ advanceP
    [] -> failP "unexpected end of input"

-- | A raw S-expression literal, captured by a quote-aware balanced-paren scan
-- and decoded by 'Lara.Wire.parseSExpr' (the canonical wire parser). The
-- payload must be a parenthesised form — every nd@1 certificate is a list
-- (`decodeCert`, src/Lara/Strict/ND.hs:353-364).
sexpLitP :: P SExpr
sexpLitP = do
  mc <- peekChar
  case mc of
    Just '(' -> do
      raw <- scan (0 :: Int) False False ""
      case parseSExpr raw of
        Right e -> pure e
        Left _ -> failP "malformed certificate payload S-expression"
    _ -> failP "certificate payload must be a parenthesised S-expression"
  where
    scan depth inStr esc acc = do
      mc <- peekChar
      case mc of
        Nothing -> failP "unterminated certificate payload"
        Just c
          | esc -> consume (\a -> scan depth inStr False a)
          | inStr && c == '\\' -> consume (\a -> scan depth inStr True a)
          | inStr && c == '"' -> consume (\a -> scan depth False False a)
          | inStr -> consume (\a -> scan depth inStr False a)
          | c == '"' -> consume (\a -> scan depth True False a)
          | c == '(' -> consume (\a -> scan (depth + 1) False False a)
          | c == ')' && depth > 1 -> consume (\a -> scan (depth - 1) False False a)
          | c == ')' && depth == 1 -> do
              ch <- char1
              pure (acc ++ [ch])
          | otherwise -> consume (\a -> scan depth False False a)
          where
            consume k = do
              ch <- char1
              k (acc ++ [ch])
```

Extend `printSupportTerm`'s `SRule` case to append the assurance line:

```haskell
printSupportTerm :: SupportTerm -> (String, [String])
printSupportTerm t = case t of
  SLeaf (LeafId l) -> ("leaf(" ++ l ++ ")", [])
  SRule (RuleId r) theta _prems disch _holes assurance ->
    ( r ++ "(" ++ intercalate ", " (map printTerm (map snd theta)) ++ ")"
    , [ "  discharge " ++ q ++ " with " ++ dischargeRef w
      | (QuestionId q, w) <- disch
      ]
        ++ assuranceLine assurance
    )
  where
    dischargeRef (SLeaf (LeafId l)) = l
    dischargeRef (SRule (RuleId r) _ _ _ _ _) = r -- totality fallback only

assuranceLine :: Assurance -> [String]
assuranceLine a = case a of
  AssuranceNone -> []
  AssuranceTrusted -> ["  assurance = trusted"]
  AssuranceCert (Cert (BackendId b) v (TheoryDigest h) payload) ->
    [ "  assurance = cert(" ++ b ++ "@" ++ show v ++ ", " ++ h ++ ", "
        ++ printSExpr payload ++ ")"
    ]
```

- [x] **Step 4: Run test to verify it passes**

Run: `cabal test`
Expected: PASS. NOTE — elaboration still forces `AssuranceNone`
(Task S3); this task only parses/prints.

- [x] **Step 4b: Negative parse tests (assurance lines + payloads)**

Add table-driven negative props to `test/SyntaxSpec.hs`, one case per new
`failP` branch: duplicate `assurance` line in one arg block → parse error;
`assurance = …` on a `leaf(…)` support term → parse error; unknown assurance
keyword (`assurance = maybe`) → parse error; non-parenthesised payload →
parse error; unterminated payload (input ends mid-scan) → parse error;
balanced-but-malformed payload (`parseSExpr` fails, e.g. stray quotes) →
parse error.

- [x] **Step 4c: Extend the program generator**

Extend `genProgram`'s support-term generator in `test/SyntaxSpec.hs` to
sometimes emit `AssuranceTrusted` and `AssuranceCert` (arbitrary small
`SExpr` payloads via `SAtom`/`SList`) so `prop_programRoundTrip` (2000
successes) exercises `assuranceP`/`sexpLitP`/`assuranceLine`. Keep
`AssuranceNone` the common case.

- [x] **Step 5: Commit**

```bash
git add src/Lara/Syntax.hs test/SyntaxSpec.hs
git commit -m "feat(syntax): support-term assurance surface (lara-syntax@0.2 App. A.1)"
```

---

## Task S3: elaborator lowering + CLI theory-registry threading

**Files:**
- Modify: `src/Lara/Elaborate.hs` (module header 30-35, `elabTerm` 234-257,
  new exported `registryOf`)
- Modify: `app/Main.hs:113` (the `elaborate` call site)
- Test: `test/ElaborateSpec.hs`

**Interfaces:**
- Consumes: `Policy.policyTheories` (Task S1); surface `Assurance` on `SRule`
  (Task S2).
- Produces: elaborated `SRule` carries the surface assurance;
  `registryOf :: Policy -> TheoryRegistry` — the single named derivation every
  caller uses. There are **10** `emptyRegistry` call sites repo-wide:
  `app/Main.hs:113`, `scripts/gen-worked-examples.hs:60`,
  `test/WorkedExamplesSpec.hs:108, 211, 233, 288, 297`, and
  `test/ElaborateSpec.hs:81, 100, 136`. Per this review, ALL 10 convert to
  `registryOf pol` (zero behavior change for theory-less policies; one idiom
  everywhere, matching the docstring's own rule). Task S3 converts
  `app/Main.hs` and the three `ElaborateSpec` sites; Task S4 converts the
  generator and the five `WorkedExamplesSpec` sites.

- [x] **Step 1: Write the failing test**

Add to `test/ElaborateSpec.hs` (match existing style): elaborate the S1-shaped
program + policy (same content as the Task S2 test source, plus the policy
from Task S1) and assert:

```haskell
-- after elaborate (TheoryRegistry (policyTheories pol)) prog pol:
-- 1. the elaborated a1's srAssurance is
--      AssuranceCert (Cert (BackendId "nd") 1
--        (TheoryDigest "sha256:strict-v1-theory-0") (SList [SAtom "hyp", SAtom "0"]))
-- 2. unitTheories unit == [(TheoryDigest "sha256:strict-v1-theory-0", [])]
-- 3. runUnit unit == VAccept with status justified for holds(safety_invariant, D)
```

Assertion 3 exercises the full `buildCertOk` replay — the test fails today at
assertion 1 (forced `AssuranceNone` → actually R7 `WrongMode` at check).

Also add the R13-via-presentation reject case (same program, but the policy
omits the `theory` declaration so the cert cites an undeclared digest):
assert `runUnit unit` is `VReject` with R13 class. This pins the failure a
user hits when they typo a digest — today it surfaces only as "unknown
theory digest" inside the ND backend.

- [x] **Step 2: Run test to verify it fails**

Run: `cabal test`
Expected: FAIL — `srAssurance == AssuranceNone`; `runUnit` yields
`VReject (RejectClass R7)`.

- [x] **Step 3: Implement**

`src/Lara/Elaborate.hs` — thread the surface assurance instead of forcing
`AssuranceNone` (in `elabTerm`'s `SRule` case):

```haskell
  SRule r posTheta _shallowPrems shallowDisch holes assurance -> do
    …
    disch <- resolveDischarges env priors aid shallowDisch
    -- lara-syntax@0.2: the surface assurance is lowered verbatim; legality
    -- (strict mode, allow-trusted, certifier allowlist, replay) is the
    -- checker's R7/R13, not the elaborator's.
    pure (SRule r theta prems disch holes assurance)
```

Rewrite the module header's "Defeasible-only" section (lines 30-35) to:

```haskell
-- == Assurance
--
-- Strict /rules/ pass through into 'unitRules' as policy declarations.
-- Support-term assurance (lara-syntax@0.2, grammar App. A.1) is lowered
-- verbatim from the surface; the elaborator performs no mode or certifier
-- check — R7/R13 at @checkUnit@ are the single enforcement point.
```

Add the exported registry derivation to `src/Lara/Elaborate.hs` (export list +
definition, next to `emptyRegistry`):

```haskell
-- | The theory registry a policy declares (lara-syntax@0.2, grammar App. A.2).
-- Every caller that elaborates against a parsed policy should pass
-- @registryOf pol@ instead of 'emptyRegistry' so the policy's theory table
-- reaches 'unitTheories'.
registryOf :: Policy -> TheoryRegistry
registryOf = TheoryRegistry . policyTheories
```

`app/Main.hs` — replace `emptyRegistry` with the policy-derived table:

```haskell
elaborate defeasibleSuiteSigma (registryOf pol) prog pol
```

(swap `emptyRegistry` for `registryOf` in the `Lara.Elaborate` import list at
`app/Main.hs:37-41`.)

`test/ElaborateSpec.hs` — replace `emptyRegistry` with `registryOf pol` at the
three call sites (81, 100, 136; the module imports `Lara.Elaborate`
whole-module at 26-27, so `registryOf` is already in scope).

- [x] **Step 4: Run test to verify it passes**

Run: `cabal test`
Expected: PASS — including the `runUnit` accept assertion (this is the
`strictCertAccept` shape replayed through the presentation path).

- [x] **Step 5: Commit**

```bash
git add src/Lara/Elaborate.hs app/Main.hs test/ElaborateSpec.hs
git commit -m "feat(elaborate): lower support-term assurance; CLI threads policy theories"
```

---

## Task S4: the S1 worked example + suite registration

**Files:**
- Create: `examples/S1/example.lara`, `examples/S1/strict-v1.policy.lara`
- Create (generated): `examples/S1/example.core.sexp`, `examples/S1/expected.json`
- Modify: `scripts/gen-worked-examples.hs:37-46` (examples list)
- Modify: `test/WorkedExamplesSpec.hs` (header 13-22, `examplePolicies` 85-94,
  new `prop_S1`, `workedExamplesSpecProps` 309+)
- Modify: `test/CliSpec.hs` (new accept case after `prop_cliLaraAcceptB` 158)
- Modify: `test/DifferentialSpec.hs:116-145` (`workedExampleGoldens`)

**Interfaces:**
- Consumes: Tasks S1–S3 (parse/elaborate/print/registry all live).
- Produces: the committed S1 artifacts all suites key on.

- [x] **Step 1: Author the example**

`examples/S1/strict-v1.policy.lara`:

```lara
# strict-v1 — strict-certificate policy for worked example S1
#
# Exercises the nd@1 certificate path end-to-end (TODOS P3 strict-cert item).
# The theory table is a trusted input (grammar App. A.2): S1's artifact
# references the digest but may not define the table.

policy strict-v1

# A certified citation: the conclusion is a strict (backend-certified)
# consequence of the premise. HONESTY NOTE: nd@1 encodes every source
# proposition — premises and theory entries alike — as a flat atom
# (src/Lara/Strict/ND.hs encodeND), so hypothesis reuse (`(hyp N)` over a
# premise or theory slot) is the only certificate shape that references
# source-level content. Richer lam/app structure is technically replayable
# but only by hand-spelling the backend's internal atom keys in
# payload-embedded formulas (decodeCert/decodeFormula,
# src/Lara/Strict/ND.hs:346-364) — opaque, produced by no surface encoding,
# and certifying nothing about source-level structure; abort cannot close a
# goal from atomic premises at all. The premise ≡ conclusion shape below is
# therefore the maximal honest shape, not a simplification.
rule certified_citation(X, D)
  mode       = strict
  premises   = [ holds(X, D) ]
  conclusion = holds(X, D)
  allow-trusted = false
  certifiers = [ (nd@1, sha256:strict-v1-theory-0) ]

# The empty theory the certificate cites. The digest is a placeholder like the
# artifact digests (no digest computation exists in the codebase — M4b B0
# investigation, docs/m4b-b0-source-and-replay-bundle.md).
theory sha256:strict-v1-theory-0 = []
```

`examples/S1/example.lara`:

```lara
# S1 — strict-certificate worked example (lara-syntax@0.2)
#
# The first worked example exercising the frontend certificate path:
# assurance = cert(…) parses, elaborates to AssuranceCert, and replays through
# nd@1 (Driver.buildCertOk) to an accept verdict. See the policy file's
# honesty note for why the certificate is hypothesis reuse.

artifact paper_42 at sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
policy strict-v1
use backends [nd@1]

claim c1
  nl      = "The safety invariant holds for deployment D"
  formal  = holds(safety_invariant, D)
  binding = { author = alice, rationale = "Certified citation of the audited safety invariant.", audit-status = reviewed }

leaf e1 : holds(safety_invariant, D)
  kind       = attested
  provenance = user
  refs       = [evidence/safety_audit.txt#section=invariants]

arg a1 : supports(c1) by certified_citation(safety_invariant, D)
  assurance = cert(nd@1, sha256:strict-v1-theory-0, (hyp 0))

status c1
```

- [x] **Step 2: Register and regenerate**

Add `("examples/S1", "strict-v1.policy.lara")` to the `examples` list in
`scripts/gen-worked-examples.hs:37-46`. In the same file, replace
`emptyRegistry` with `registryOf pol` at the `elaborate` call (line 60) and in
the import (line 28). Regenerate:

```bash
cabal exec -- runghc scripts/gen-worked-examples.hs
```

Verify `examples/S1/example.core.sexp` and `examples/S1/expected.json` appear.

- [x] **Step 3: Wire the test suites**

`test/WorkedExamplesSpec.hs`:
- Add `("examples/S1", "strict-v1.policy.lara")` to `examplePolicies`.
- Replace `emptyRegistry` with `registryOf pol` at all five `elaborate` call
  sites (lines 108, 211, 233, 288, 297) and in the import (line 44). Without
  this S1 elaborates to an empty-theories unit and fails R13.
- Add a prop helper next to `improves` (line 57-62):

```haskell
-- | @holds(x, d)@ over two nullary-constant names.
holdsP :: String -> String -> Prop
holdsP x d = Prop (Pred "holds") [con x, con d]
```

- Add, after `prop_E3`:

```haskell
-- | S1: the strict nd@1 certificate replays; the certified arg is @in@ and
-- the claim is justified.
prop_S1 :: Property
prop_S1 = once $ ioProperty $
  runExample "examples/S1" "strict-v1.policy.lara" $ \v ->
    case v of
      VReject r -> counterexample ("S1: unexpected reject " ++ show r) False
      VAccept{} ->
        conjoin
          [ counterexample "S1 labels: a1 → in" $
              verdictLabels v === [(0, LIn)]
          , counterexample "S1 status: c1 → justified" $
              verdictStatuses v === [(holdsP "safety_invariant" "D", Justified)]
          ]
```

- Add `("S1 strict nd@1 cert → accept, arg in, claim justified", quickCheckResult prop_S1)`
  to `workedExamplesSpecProps` and update the module-header
suite description (lines 13-22) and `prop_coverageMatrix`'s suite comment
(258-259: "the six §1 examples E1–E3 / R1–R3 plus the two teaching examples A
and B" → mention S1).

`test/CliSpec.hs` — after `prop_cliLaraAcceptB`:

```haskell
prop_cliLaraAcceptS1 = once $ ioProperty $ do
  (code, out, _) <- runLara ["check", "examples/S1/example.lara"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitSuccess)
      , counterexample "stdout bytes" $
          out
            === "(verdict accept (labels (0 in)) (edges) (statuses (status (atom holds (con safety_invariant) (con D)) justified)))\n"
      ]
```

`test/DifferentialSpec.hs` — add to `workedExampleGoldens`:

```haskell
  , ( "examples/S1/example.core.sexp"
    , "(verdict accept (labels (0 in)) (edges)"
        ++ " (statuses (status (atom holds (con safety_invariant) (con D)) justified)))"
    )
```

- [x] **Step 4: Run the full suite**

Run: `cabal test`
Expected: PASS — all existing suites green plus S1 cases. If the regenerated
`expected.json` verdict differs from the predicted bytes above, trust the
checker output, update the two goldens to match, and note the delta in the
commit message.

- [x] **Step 5: Commit**

```bash
git add examples/S1 scripts/gen-worked-examples.hs test/WorkedExamplesSpec.hs test/CliSpec.hs test/DifferentialSpec.hs
git commit -m "feat(examples): S1 — strict nd@1 certificate worked example end-to-end"
```

---

## Task S5: docs sync + backlog retirement

**Files:**
- Modify: `examples/README.md` (suite layout + the defeasible-only honesty
  note, lines 76-82)
- Modify: `TODOS.md` (retire the strict-cert item to Completed)
- Modify: `docs/m4a-checklist.md:38-39` (the "strict-certificate worked
  example → TODOS" bullet)

**Work:**

- [x] **Step 1: `examples/README.md`** — add S1 to the suite listing; rewrite
  the honesty note: the suite is no longer defeasible-only; the cert path is
  exercised by S1 with the hypothesis-reuse caveat (premise ≡ conclusion is
  the maximal honest shape; richer `lam`/`app` structure replayable only via
  internal atom keys, never source-referencing — mirror the precise wording
  of the S1 policy's HONESTY NOTE).
- [x] **Step 2: `TODOS.md`** — move "Strict-certificate worked example (nd@1
  frontend cert path)" under `## Completed` with a one-line summary (S1 lands
  the frontend cert path; hypothesis-reuse caveat recorded in
  `examples/S1/strict-v1.policy.lara`). Also add two new P3 items under
  `## Mechanization`:
  - **Print hole-lines in support terms.** `printSupportTerm` drops `_holes`;
    `open … as …` would survive parse but break the surface round-trip. Low
    priority until an example needs it. Flagged in the plan's Out of Scope.
  - **Theory-line groundness.** The grammar says theory entries are ground
    propositions, but `propP` accepts variables (harmless in practice:
    `encodeND` flattens everything to atoms). Tighten the parser or update
    the grammar.
- [x] **Step 3: `docs/m4a-checklist.md`** — update the out-of-scope bullet to
  point at the landed S1 instead of TODOS.
- [x] **Step 4: Run `cabal test` one final time (all green), then commit**

```bash
git add examples/README.md TODOS.md docs/m4a-checklist.md
git commit -m "docs: suite no longer defeasible-only; retire strict-cert backlog item"
```

---

## Definition of Done

- `lara check examples/S1/example.lara` exits 0 and prints the justified
  verdict above, through the **unchanged** checker (no `Lara.Check`,
  `Lara.Driver`, `Lara.Strict*`, `Lara.Wire`, or Lean edits).
- `parse ∘ print == id` holds for both new constructs (SyntaxSpec).
- The S1 `.core.sexp` passes the Haskell↔Lean differential golden
  (DifferentialSpec) — proof the Unit-level cert path agrees across drivers.
- The suite's honesty note no longer claims defeasible-only.

## Out of scope

- `use backends […]` validation by `Lara.Elaborate` (M4b B0 finding, TODOS).
- Artifact/theory digest computation (placeholders remain; M4b replay manifest
  introduces hashing at the replay layer).
- Non-hypothesis-reuse certificate shapes (lam/app replayable only via internal
  atom keys, never source-referencing; abort can't close from atomic premises.
  Would require a backend encoding change, i.e. spec §5 evolution). See the
  S1 policy HONESTY NOTE for the precise caveats.
- The latent printer gap for `open … as …` hole lines (`printSupportTerm`
  drops holes; no example exercises `open`). Flagged, not fixed here.

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | `/codex review` | Independent 2nd opinion | 1 | timeout | timed out after 5 min; Claude fallback also failed |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | CLEAR | 10 findings, 0 unresolved, 0 critical gaps |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | — |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | — |

**CODEX:** Codex timed out (5 min); Claude outside-voice subagent failed (exit 1).
Proceeding without independent second opinion.

**VERDICT:** ENG CLEARED — ready to implement. Run `/ship` when done.

NO UNRESOLVED DECISIONS
