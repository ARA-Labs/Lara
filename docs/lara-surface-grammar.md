# LARA surface grammar — frozen (`lara-syntax@0.1`)

_Task **A0.5** of M4a (GitHub #31; tracker `docs/m4a-checklist.md`).
This document **freezes** the concrete `.lara` grammar so that Task A1's parser +
printer (`Lara.Syntax`) and the `Program → Unit` elaborator (`Lara.Elaborate`)
implement a fixed contract instead of inventing language semantics. It is grounded
in what `examples/A/example.lara`, `examples/B/example.lara`,
and `examples/A/empirical-v1.policy.lara` actually write, and in the abstract syntax
of `src/Lara/AST.hs`._

Status of the artifacts this task touches:

- **AST** — `src/Lara/AST.hs` gained two presentation-only types (`ChallengeTarget`,
  `ArgConcl`) and `Arg.argClaim :: PropId` became `Arg.argConcl :: ArgConcl`. No
  frozen (Unit-reachable) type changed. See §7 and §9.1.
- **A / B** — already conform to the grammar below; **no reconciliation edits were
  required** (see §10). The gap that A0.5 existed to close was in the *AST*, not the
  example text: the surface forms `challenges(…)` and `supports(c1_neg)`
  (undeclared) had no representable conclusion until `ArgConcl` landed.

Versioning: the presentation surface is versioned **separately** from the core
(`docs/spec.md` §2.1). This document defines `lara-syntax@0.1`; it decodes to
`lara-core@0.1`. A grammar change that still decodes to the same abstract syntax is
invisible to the checker by spec result 12 (`parse ∘ print == id`, mechanized in
A3).

---

## 0. Two top-levels, one file, disambiguated by the leading keyword

A source file is **either** an artifact program **or** a policy. The authoritative
disambiguator is the **first significant token**:

| Leading keyword | Top-level | Conventional extension | AST target |
| --- | --- | --- | --- |
| `artifact` | artifact program | `.lara` | `Program` |
| `policy`   | policy            | `.policy.lara` | `Policy` |

The extension is a **convention** (and what `lara check`'s co-located policy
resolution keys on, plan A1 / D-Arch-2); the **keyword is normative**. A `.lara`
file that begins `policy …` is a policy, and vice versa. The two grammars share the
lexical layer (§1) and the proposition/term/pattern sub-grammars (§2), and are
otherwise disjoint.

---

## 1. Lexical grammar (tokenizer)

The lexer runs in two modes. **Normal mode** is the default. **Ref-list mode** is
entered between `[` and `]` of a `refs = [ … ]` field and nowhere else (§1.3); it
exists solely to make `#` literal inside a source reference.

### 1.1 Whitespace and layout

Whitespace (spaces, tabs) and newlines separate tokens and are otherwise
insignificant: LARA is **not** layout-sensitive. Indentation in the examples is
cosmetic. A block (`claim`, `leaf`, `arg`, `rule`) is delimited by its header line
and its field keywords, not by indentation. Field lines within a block may appear
in any order unless stated otherwise; the **canonical printer** emits them in the
fixed order shown in §3–§4 so that `parse ∘ print == id` holds.

### 1.2 Comments — the `#` rule (FROZEN)

```
# begins a line comment that runs to end-of-line — EXCEPT inside a refs list.
```

- **Normal mode:** `#` begins a comment. Everything from `#` to (but not including)
  the next newline is discarded. A comment may follow code on the same line
  (`discharge external_validity with e6   # rests on the raw measurement leaf e6`).
- **Ref-list mode** (between the `[` and the matching `]` of a `refs = […]` field):
  `#` is an **ordinary character** of the current source-ref token. No comment is
  recognized. Thus `refs = [paper_17.pdf#sec=4.1]` is one source reference
  `paper_17.pdf#sec=4.1`, not a reference followed by a comment.
- The exception is **scoped to the brackets**. After the closing `]`, normal mode
  resumes and `#` is a comment again (`refs = [a.csv#r=1]  # trailing note` — the
  trailing note is a comment).

Rationale: a source ref is opaque provenance (`SourceRef`, a single `String`); `#`
is a legitimate fragment/anchor character in it. Everywhere else `#` is the only
comment sigil. Making the exception positional (inside `refs = […]`) keeps the
tokenizer's state machine to two modes with a single trigger.

### 1.3 Token classes

```
ident      ::= (letter | "_") { letter | digit | "_" | "-" }
             -- letters, digits, underscore, hyphen; must not start with a digit or "-".
             -- Covers: paper_17, corpus_field_X, external_validity, audit-status,
             --         ai-executed, controlled_experiment, nd, alice.
number     ::= [ "+" | "-" ] digit { digit } [ "." digit { digit } ]
             -- e.g. +0.00251, -2.1, 4  (a Term literal; see nf, spec §3.2).
string     ::= '"' { any-char-except-'"'-or-newline } '"'
             -- single line; used by nl and rationale.
digest     ::= ident ":" digestBody
digestBody ::= { letter | digit | "." | "_" | "-" }      -- maximal, non-empty
             -- e.g. sha256:aaaa...  sha256:bbbb...   (the "..." are ordinary dots)
backendRef ::= ident "@" ( number | ident )              -- e.g. nd@1  →  (BackendId "nd", "1")
sourceRef  ::= { any-char-except "," "]" and surrounding whitespace }   -- ref-list mode only
punct      ::= "(" | ")" | "[" | "]" | "{" | "}" | "," | ":" | "=" | "."
```

Reserved words are the keyword/tag vocabulary of §1.4. An `ident` equal to a
reserved word is that keyword in the positions where a keyword is expected; the
grammar is not otherwise keyword-quarantined (a `pred`/`funsym`/`id` occurrence is
positionally determined). Two idents are reserved from the **question-id**
namespace because they are terminal markers in attack position suffixes (§8):
`rule` and `leaf`.

### 1.4 Keyword & tag vocabulary (single `toString`/`parse` table)

Per CLAUDE.md ("keep the core symbolic"), each fixed-vocabulary word has **one**
surface spelling, and the `Lara.Syntax` codec owns this table — no scattered
string literals. A given spelling may bind to more than one AST constructor when
its meaning is fixed by syntactic position (e.g. `quarantine` / `reject` name an
`Admission` outcome on a leaf and a `GroupConflictMode` on a `duplicate-reports`
policy field); the codec still resolves each occurrence from its position, so the
surface↔AST mapping stays single-valued per position. Structural keywords:

```
artifact  policy  at  use  backends  claim  leaf  arg  status  group
rule  mode  premises  conclusion  question  contrary  exception  admission
duplicate-reports  quarantine
nl  formal  binding  kind  provenance  refs  author  rationale  audit-status
by  supports  challenges  discharge  with  open  as
rebut  undercut  undermine
allow-trusted  certifiers  cert  trusted  none
```

Closed tag enumerations (surface ↔ `Lara.AST` constructor):

| Field | Surface spelling | AST |
| --- | --- | --- |
| `mode` | `strict` / `defeasible` | `Mode` `Strict` / `Defeasible` |
| `kind` | `observed` / `attested` / `assumed` / `certified` | `LeafKind` `Observed` / `Attested` / `Assumed` / `Certified` |
| `provenance` | `user` / `ai-executed` / `checker(name, version)` | `Provenance` `User` / `AiExecuted` / `Checker name version` |
| `audit-status` | `unreviewed` / `reviewed` / `disputed` | `AuditStatus` `Unreviewed` / `Reviewed` / `Disputed` |
| question necessity | `(mandatory)` / `(optional)` | `Necessity` `Mandatory` / `Optional` (default `mandatory`) |
| admission outcome | `admit` / `quarantine` / `reject` | `Admission` `Admit` / `Quarantine` / `Reject` |
| duplicate-reports mode | `quarantine` / `reject` | `GroupConflictMode` `QuarantineOnConflict` / `RejectOnConflict` |
| assurance | `none` / `trusted` / `cert(…)` | `Assurance` `AssuranceNone` / `AssuranceTrusted` / `AssuranceCert` |

---

## 2. Shared sub-grammars: propositions, terms, patterns

Used by both top-levels.

```
prop    ::= pred [ "(" term { "," term } ")" ]        -- an atom; nullary allowed
term    ::= ident                                       -- constant (nullary constructor)
          | ident "(" term { "," term } ")"             -- applied constructor
          | number                                      -- numeric literal (TNum)
pred    ::= ident
funsym  ::= ident
```

Whether an `ident` heads a `pred` (an atom) or a `funsym` (a term) is fixed by
position: the head of `prop`, of a `conclusion`/`premises`/`question` pattern, and
of a `contrary`/`exception` atom is a `pred`; heads inside are `funsym`s. Arities
are checked against `Σ` by the elaborator, not the grammar.

Patterns (policy only) replace ground terms with parameters:

```
pat     ::= param                                       -- an UPPERCASE-or-declared rule parameter
          | ident                                       -- a ground constant literal (PLit/PCon …)
          | ident "(" pat { "," pat } ")"
apat    ::= pred [ "(" pat { "," pat } ")" ]
param   ::= ident                                       -- one of the rule's declared parameters
```

In the reference policy the parameters are written `M, Q, D, Exp` (single/short
capitalized idents) and constants are lowercase, but the grammar does **not**
enforce a case convention: a `pat` head/leaf is a `param` iff it is one of the
enclosing rule's declared parameters, otherwise a ground literal. (This resolution
is elaborator work; the parser records the raw ident.)

---

## 3. Artifact grammar (`.lara` → `Program`)

```
program   ::= "artifact" ident "at" digest
              "policy" ident
              "use" "backends" "[" [ backendRef { "," backendRef } ] "]"
              { decl }

decl      ::= claimDecl | leafDecl | argDecl | attackDecl | statusDecl | groupDecl

claimDecl ::= "claim" ident
              "nl"      "=" string
              "formal"  "=" prop
              "binding" "=" binding

binding   ::= "{" bindingField { "," bindingField } "}"
bindingField ::= "author"       "=" ident
               | "rationale"    "=" string          -- optional
               | "audit-status" "=" auditStatus
             -- author and audit-status required; rationale optional (defaults to "").

leafDecl  ::= "leaf" ident ":" prop
              "kind"       "=" leafKind
              "provenance" "=" provenance
              "refs"       "=" refsList

refsList  ::= "[" [ sourceRef { "," sourceRef } ] "]"   -- lexed in ref-list mode (§1.2)

groupDecl ::= "group" ident "=" "[" [ ident { "," ident } ] "]"   -- duplicate-report group (spec §4.3)
              -- members are declared leaf ids; the named group locates an R9 diagnostic

argDecl   ::= "arg" ident ":" argConcl "by" supportTerm { dischargeLine | openLine }

argConcl  ::= "supports"   "(" ident ")"                 -- SupportsClaim / SupportsDerived (§6)
            | "challenges" "(" challengeTarget ")"       -- Challenges (§6)

challengeTarget ::= ident "(" ident ")"                  -- ChallengesQuestion  q(u)
                  | ident                                -- ChallengesLeaf      l

supportTerm ::= "leaf" "(" ident ")"                     -- SLeaf
              | ident "(" [ term { "," term } ] ")"      -- rule instance: id + ground θ (§5)

dischargeLine ::= "discharge" ident "with" argRef        -- discharge q with <support>
openLine      ::= "open" ident "as" ident                -- open q as o   (explicit hole)
argRef        ::= ident                                  -- a leaf id or a prior arg id

attackDecl ::= "rebut"     ident ident
             | "undercut"  ident posTarget               -- terminal marker ".rule"
             | "undermine" ident posTarget               -- terminal marker ".leaf"

posTarget  ::= ident { "." step } "." marker             -- u . π-steps . (rule|leaf)
step       ::= number                                    -- StepPremise i
             | ident                                     -- StepQuestion q
marker     ::= "rule" | "leaf"

statusDecl ::= "status" ident
```

Notes:

- `use backends [ … ]` may be empty (`[]`); `nd@1` is the only registry entry in
  v0.1 and is **inert** for the defeasible-only worked-examples suite (plan A2
  honesty note).
- Field order inside `claim`/`leaf` is the canonical printer order shown; the
  parser accepts that order for v0.1.
- Every `decl` is order-free at the top level except that a name must be in scope
  by elaboration time (forward references across the file are allowed; scoping is
  the elaborator's job, not the grammar's).

---

## 4. Policy grammar (`.policy.lara` → `Policy`)

```
policyTop  ::= "policy" ident { policyDecl }

policyDecl ::= ruleDecl | contraryDecl | exceptionDecl | admissionDecl | groupModeDecl

ruleDecl   ::= "rule" ident "(" [ param { "," param } ] ")"
               "mode"       "=" mode
               "premises"   "=" "[" [ apat { "," apat } ] "]"
               "conclusion" "=" apat
               [ "allow-trusted" "=" bool ]              -- strict rules only
               [ "certifiers"    "=" "[" [ certRef { "," certRef } ] "]" ]  -- strict only
               { questionLine }

questionLine ::= "question" ident ":" apat [ "(" necessity ")" ]   -- default (mandatory)
certRef      ::= "(" backendRef "," digest ")"           -- (beta@version, theory-digest)
bool         ::= "true" | "false"

contraryDecl  ::= "contrary" apat apat                   -- two atoms, whitespace-separated
exceptionDecl ::= "exception" ident ":" apat             -- exception r : E

admissionDecl ::= "admission" "{" [ admitRow { "," admitRow } ] "}"   -- OPTIONAL block
admitRow      ::= "(" leafKind "," provenance ")" "=" admission

groupModeDecl ::= "duplicate-reports" "=" groupMode   -- OPTIONAL; default "quarantine"
groupMode     ::= "quarantine" | "reject"             -- §4.3 conflict outcome (R9 on "reject")
```

Notes:

- `allow-trusted` / `certifiers` are **absent** on defeasible rules and present
  only on strict rules (spec §4). The reference policy `empirical-v1` is
  defeasible-only, so neither appears there.
- The `admission` block is **optional**. `empirical-v1.policy.lara` omits it; the
  A1 elaborator chooses the default admission map (plan A1 / outside-voice #12 — a
  decision **owned by A1**, not frozen here). The grammar only fixes that the block
  *may* be omitted and, when present, is a total-ish association of
  `(kind, provenance) ↦ outcome` rows.

---

## 5. Support terms: premises IMPLICIT, discharges EXPLICIT (FROZEN)

The `by r(g1, …, gn)` application supplies the **full ground substitution `θ`** over
`r`'s declared parameters, positionally (`r`'s i-th parameter ↦ `gi`). Example A's
`controlled_experiment(M, accuracy, D, exp_3)` binds all four parameters of
`rule controlled_experiment(M, Q, D, Exp)` — `{M↦M, Q↦accuracy, D↦D, Exp↦exp_3}` —
so every premise pattern is fully ground under `θ`.

**Premise sub-terms are NOT written in the surface.** The elaborator reconstructs
each premise `i` by:

1. computing the ground premise proposition `Apᵢ · θ`;
2. resolving it to the **unique** declared leaf or prior `arg` whose conclusion is
   `≡ Apᵢ · θ` (spec §3.2 `nf`-equality).

This is the reading `by r(…)` takes in v0.1: the parenthesized arguments are the
**θ binding**, not sub-argument references. (This diverges from `docs/spec.md` §4.4's
`by r(a1,…,an)` notation, where `a1..an` are premise sub-arguments; the divergence
is deliberate and grounded in what A/B write — every A/B `by`-application lists the
rule's *parameters/terms*, and omits the principal premise leaf `e1`/`e7`. The
checker still receives the fully explicit support term; premise reconstruction is
untrusted elaborator work, spec §4.1 "reconstructing an elided `theta` is elaborator
work.")

**Determinism (plan D3).** Premise resolution is a total function on well-formed
input:

- `nf`/`≡` is decidable and the declared leaf+arg set is finite, so "the set of
  declared conclusions `≡ Apᵢ·θ`" is computable;
- **exactly one** match ⇒ that sub-term (deterministic);
- **zero** matches ⇒ a located elaborate error (unresolved premise);
- **≥ 2** matches ⇒ a located elaborate error (ambiguous premise).

No search, no backtracking, no preference — the elaborator is deterministic and
total-on-well-formed-input as D3 requires.

**Discharges stay EXPLICIT.** Each critical question is discharged by name:
`discharge q with <argRef>` (A/B use bare leaf ids: `discharge randomization with
e2`). Open holes are explicit too: `open q as o`. The `D ⊎ H = questions(r)`
accounting invariant (spec §4.2) is checked by the elaborator against the resolved
discharge/open sets. A/B need no premise edits under this rule.

---

## 6. Argument conclusion forms (`ArgConcl` / `ChallengeTarget`)

An `arg` announces a conclusion role. The checker consumes only the support term's
own `concl(w)` (spec §6.1), so the arm chosen **never changes the compiled AF** — it
records the author's stated role, which the elaborator resolves/validates.

| Surface | `ArgConcl` | Meaning | A/B site |
| --- | --- | --- | --- |
| `supports(c)`, `c` a declared `claim` | `SupportsClaim (PropId c)` | elaborator checks `concl(w) ≡ c.claimFormal` (spec §3.1) | `a1`, `pa`, `pb` |
| `supports(c)`, `c` **not** declared | `SupportsDerived (PropId c)` | `c`'s formal prop is **derived** from `concl(w)`; A0.5 records only the label. No status is computed for `c` unless a separate `status c` names it. | `d3` (`supports(c1_neg)`) |
| `challenges(q(u))` | `Challenges (ChallengesQuestion (QuestionId q) (ArgId u))` | attack-only arg; real edge is the paired `undercut`/`undermine` line. Target = the CQ `q` of arg `u`. | `d1` (`challenges(external_validity(a1))`) |
| `challenges(l)` | `Challenges (ChallengesLeaf (LeafId l))` | attack-only arg; target = frontier leaf `l`; real edge is the paired `undermine` line. | `d2` (`challenges(e6)`) |

The `challenges(…)` target is **presentation intent only**: `d1`'s real conclusion
(for the Unit) is `concl(leaf e4) = distribution_shift(…)`, and its defeat edge is
`undercut d1 a1.rule` — the challenge label and the attack line are independent, and
the elaborator uses the label solely for diagnostics. The two `ChallengeTarget`
forms mirror the two attackable non-root positions (a CQ discharge occurrence, a
frontier leaf), matching the shape of the attack targets in §8.

---

## 7. Attacks and the position-suffix ↔ `[Step]` mapping (FROZEN)

Attacks **reuse the frozen checker types** `Attack` / `Position` / `Step`
(`src/Lara/AST.hs`; Unit-reachable, off-limits) — A0.5 adds **no** presentation
attack type. The surface suffix has **one canonical spelling per (attack-kind,
position)**, so `parse ∘ print == id` holds.

A `Position = [Step]` and `Step = StepPremise Int | StepQuestion QuestionId`. The
surface path is `u`, then `.`-joined steps, then a terminal marker that encodes the
occurrence kind. Because the occurrence kind is already implied by the attack
constructor (`Undercut` ⇒ a rule occurrence ⇒ marker `rule`; `Undermine` ⇒ a leaf
occurrence ⇒ marker `leaf`), the **printer regenerates the marker canonically** and
the parser **requires** it.

| Attack | Surface | AST | π |
| --- | --- | --- | --- |
| rebut (root conclusion) | `rebut w u` | `Rebut (ArgId w) (ArgId u)` | — (root; defeasible only) |
| undercut, root rule | `undercut w u.rule` | `Undercut w u []` | `[]` |
| undercut, premise-`i` rule | `undercut w u.<i>.rule` | `Undercut w u [StepPremise i]` | `[StepPremise i]` |
| undercut, CQ-`q` rule | `undercut w u.<q>.rule` | `Undercut w u [StepQuestion q]` | `[StepQuestion q]` |
| undermine, leaf under CQ-`q` | `undermine w u.<q>.leaf` | `Undermine w u [StepQuestion q]` | `[StepQuestion q]` |
| undermine, leaf at premise-`i` | `undermine w u.<i>.leaf` | `Undermine w u [StepPremise i]` | `[StepPremise i]` |
| (deeper) | `… u.<s1>.<s2>.….marker` | steps left→right | `[s1, s2, …]` |

**Step disambiguation.** A dotted segment that is a decimal integer is a
`StepPremise`; otherwise it is a `StepQuestion` (the question id). The **final**
segment is the terminal marker and must equal `rule` (for `undercut`) or `leaf` (for
`undermine`); a mismatch is a located parse error. To keep this unambiguous, `rule`
and `leaf` are **reserved from the question-id namespace** (a policy must not name a
`question rule` or `question leaf`; §1.3).

**Printer (canonical).** `Undercut w u π` → `undercut w u` + `"." + printStep s` for
each `s ∈ π` + `".rule"`; root `π=[]` → `undercut w u.rule`. `Undermine w u π` →
same with `".leaf"`. `Rebut w u` → `rebut w u`. `printStep (StepPremise i) = show i`;
`printStep (StepQuestion (QuestionId q)) = q`.

Worked from Example A:

- `undercut d1 a1.rule` ⇒ `Undercut (ArgId "d1") (ArgId "a1") []`.
- `undermine d2 a1.external_validity.leaf`
  ⇒ `Undermine (ArgId "d2") (ArgId "a1") [StepQuestion (QuestionId "external_validity")]`.
- `rebut d3 a1` ⇒ `Rebut (ArgId "d3") (ArgId "a1")`.

---

## 8. Decisions & rationale (the five A0.5 items)

1. **Attack-arguments without a declared claim → `ArgConcl` sum (§6).** `Arg`'s
   conclusion went from `argClaim :: PropId` to `argConcl :: ArgConcl` with three
   arms: `SupportsClaim` (declared), `SupportsDerived` (undeclared — `d3`'s
   `supports(c1_neg)`), and `Challenges` carrying a `ChallengeTarget` (the two
   surface forms `challenges(q(u))` and `challenges(l)` — `d1`, `d2`). This is the
   only field change; `ArgConcl`/`ChallengeTarget` are presentation-only and never
   reach `Unit`. **Deviation from the "e.g." in the plan:** the plan floated "an
   attack-argument node, or a claim-inference desugaring" — a single sum on the
   existing `Arg` is smaller (one field, no new `Decl` arm) and keeps every `arg`
   uniform, so I took the orchestrator's recommended `ArgConcl` instead. `d_comp`
   in `Lara.Examples` (concludes `forward_path_rewrite(rmsnorm)`, id
   `c05_compliance` not declared) is likewise `SupportsDerived`.

2. **`challenges(…)` target syntax + position suffixes (§6, §7).** `challenges(q(u))`
   and `challenges(l)` map to `ChallengesQuestion`/`ChallengesLeaf`. Dotted position
   suffixes lower to `[Step]` by the §7 table with a terminal `rule`/`leaf` marker
   whose value is fixed by the attack constructor — one canonical spelling per
   (kind, position) for the round-trip.

3. **Premises implicit, discharges explicit (§5).** `by r(…)` supplies the full
   ground `θ`; premise sub-terms are elaborator-reconstructed by unique `≡`-match
   (deterministic: 0 ⇒ error, 1 ⇒ resolved, ≥2 ⇒ error). Discharges/holes are named
   explicitly. Matches A/B verbatim; no premise edits needed.

4. **`#` lexing (§1.2).** `#` is a to-EOL comment everywhere **except** inside a
   `refs = […]` list, where it is a literal source-ref character. Two lexer modes,
   one trigger (the `refs` bracket).

5. **Two top-levels, one extension, keyword-disambiguated (§0).** `artifact …` ⇒
   `Program` (`.lara`); `policy …` ⇒ `Policy` (`.policy.lara`). The extension is
   convention; the leading keyword is authoritative.

---

## 9. AST delta (what A0.5 landed)

### 9.1 `src/Lara/AST.hs`

```haskell
-- NEW
data ChallengeTarget
  = ChallengesQuestion QuestionId ArgId   -- challenges(q(u))
  | ChallengesLeaf LeafId                 -- challenges(l)
  deriving (Eq, Show)

data ArgConcl
  = SupportsClaim PropId     -- supports(c), c declared
  | SupportsDerived PropId   -- supports(c), c NOT declared; prop derived from concl(w)
  | Challenges ChallengeTarget
  deriving (Eq, Show)

-- CHANGED: argClaim :: PropId  →  argConcl :: ArgConcl
data Arg = Arg
  { argId    :: ArgId
  , argConcl :: ArgConcl
  , argTerm  :: SupportTerm
  }
  deriving (Eq, Show)
```

Exports gained `ChallengeTarget (..)`, `ArgConcl (..)`. No Unit-reachable type
(`Unit`, `SupportTerm`, `Attack`, `Step`, `Position`, `Rule`, `Contrary`,
`Exception`, `Prop`, `Term`, the `*Id` newtypes, …) was touched.

### 9.2 Construction-site updates (kept green, no new warnings)

- `src/Lara/Examples.hs` — 5 sites: `a02`, `a_rec`, `a08`, `a09` → `SupportsClaim`;
  `d_comp` → `SupportsDerived` (its id is undeclared).
- `src/Lara/Negatives.hs` — 8 sites: all declared claims → `SupportsClaim`.

No test constructs the presentation `Arg` (the `Unit`-level `unitArgs` in
`WireSpec`/`CheckSpec` is a different, frozen type), so no test needed editing.

---

## 10. Conformance of the committed examples

Verified construct-by-construct against the grammar above (A1 confirms by parsing to
the committed `.core.sexp`):

- **`examples/A/example.lara`** — conforms. `challenges(external_validity(a1))`,
  `challenges(e6)`, `supports(c1_neg)` (undeclared), the `#`-in-refs tokens, the
  `a1.rule` / `a1.external_validity.leaf` suffixes, and the implicit-premise `by`
  applications are all representable. **No edits.**
- **`examples/B/example.lara`** — conforms. `supports(c_pos)`/`supports(c_neg)`
  over declared claims, multi-line `binding` with `rationale`, mutual `rebut`, and
  implicit premises. **No edits.**
- **`examples/A/empirical-v1.policy.lara`** — conforms to §4. Defeasible `rule`s with
  `question … (mandatory)`, `contrary A B`, `exception r : E`, no `admission` block
  (elaborator default, A1). **No edits.**

The inline `EXPECTED VERDICT (golden oracle)` blocks in A and B are **untouched**;
they remain the A0 goldens frozen in `docs/m4a-checklist.md` §1.

_Frozen 2026-07-27 as Task A0.5. Gates A1 (`Lara.Syntax` + `Lara.Elaborate`)._

---

## Appendix A — `lara-syntax@0.2` (additive, 2026-07-29)

Two additive constructs over `lara-syntax@0.1`, both decoding to the same
`lara-core@0.1` abstract syntax (spec result 12 unaffected; no Unit-reachable
type changes). Motivation: the strict-certificate worked example
(`examples/S1/`; `docs/worked-examples-plan.md`); the Unit-level cert path
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
