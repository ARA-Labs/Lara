# LARA surface grammar — frozen (`lara-syntax@0.6`)

_Task **A0.5** of M4a (GitHub #31; tracker `docs/m4a-checklist.md`).
This document **freezes** the concrete `.lara` grammar so that Task A1's parser +
printer (`Lara.Syntax`) and the `Program → Unit` elaborator (`Lara.Elaborate`)
implement a fixed contract instead of inventing language semantics. It is grounded
in what `examples/A/example.lara`, `examples/B/example.lara`,
and `examples/A/empirical-v1.policy.lara` actually write, and in the abstract syntax
of `src/Lara/AST.hs`._

Historical A0.5 baseline (the status below predates later additive surface
versions):

- **AST** — `src/Lara/AST.hs` gained two presentation-only types
  (`ChallengeTarget`, `ArgConcl`) and `Arg.argClaim :: PropId` became
  `Arg.argConcl :: ArgConcl`. No frozen (Unit-reachable) type changed. See §7
  and §9.1.
- **A / B** — at the original A0.5 baseline, both already conformed to the
  grammar below; **no reconciliation edits were required at that stage** (see
  §10). The later `lara-syntax@0.5` implementation intentionally migrates the
  A and S1 witness spellings to inferred arguments as a separate additive
  surface change; that migration does not revise this historical baseline.
  The gap that A0.5 existed to close was in the *AST*, not the example text:
  the surface forms `challenges(…)` and `supports(c1_neg)` (undeclared) had no
  representable conclusion until `ArgConcl` landed.

The active `@0.6` additions are specified in Appendix E: an `ord@1` or `ra@1`
certificate payload may cite a premise slot by source name (`(prem e4)`
instead of `(prem 0)`), and elaboration lowers the name to the canonical
numeric slot after premise resolution, so the wire `Unit` and `lara-core@0.2`
remain unchanged. The `@0.5` inferred-theta form (`Arg` carrying
`ArgInstantiation` with `ArgRef` references, exercised by the migrated A/S1
witnesses) remains specified in Appendix D.

Versioning: the presentation surface is versioned **separately** from the core
(`docs/spec.md` §2.1). This document defines `lara-syntax@0.6`; it decodes to
`lara-core@0.2`. Signature declarations lower to `unitSigma`; the additive
`@0.3` forms, `@0.4` value bindings, `@0.5` inferred-theta form, and `@0.6`
symbolic certificate premise references remain presentation-layer data until
elaboration. The Haskell `parse ∘ print == id` property covers this current
concrete surface. The structured Lean round-trip in
`lean/Lara/Presentation.lean` covers the complete live `Program`/`Policy` AST
for this surface, including value bindings, inferred argument instantiations,
`policySigma`, and optional measurand polarity — an AST-shape anchor, not a
correctness proof for the Haskell concrete parser. `scripts/check-presentation-parity.sh`
compares the two models' normalized shape inventories so the surface cannot grow
on one side only. Exact compiler witnesses pin record fields, sum payloads,
aliases, and anonymous entry types; named record selectors are compared in order.
Positional constructors have no source selector names: exact signatures pin their
arity and positional type sequence, but semantic labels and swaps among same-typed
positions remain assertions. The guard documents two representation exemptions
(`SortName` erasure; `Cert`'s native payload).

The runtime semantics of the existing `admission` and `duplicate-reports`
constructs are frozen separately in `docs/policy-admission-calculus-decision.md`.
Byte-level `lara-evidence@0.1` syntax and verification remain gated under issue #78.

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

-- lara-syntax@0.2 (Appendix A)
assurance  theory

-- lara-syntax@0.3 (Appendix B)
measurand  comparison  comparison-scheme  recheck  bridge  result  baseline
relation  claims  on  where  cell
higher-is-better  lower-is-better  strictly-better  at-least-as-good

-- lara-syntax@0.4 (Appendix C)
let

-- lara-syntax@0.5 (Appendix D)
from
```
The @0.5 entry `from` is contextual after a rule identifier; it is listed
under the version delta without becoming a lexer-reserved identifier.
`@0.6` adds no keywords and no lexer or parser change at all: the symbolic
`(prem name)` spelling lives inside the opaque `sexp` payload of `cert(…)`,
whose atom grammar already admits identifiers (Appendix E).

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
              "nl"      "=" nlString
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

supportTerm ::= "leaf" "(" ident ")"                           -- explicit leaf support
              | ident "(" [ term { "," term } ] ")"      -- explicit rule θ
              | ident "from" "[" [ argRef { "," argRef } ] "]" -- inferred θ

argRef        ::= ident                                  -- a leaf id or a prior arg id
dischargeLine ::= "discharge" ident "with" argRef        -- discharge q with <support>
openLine      ::= "open" ident "as" ident                -- open q as o   (explicit hole)

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
- Reusing a `LeafId` in two `leafDecl`s is source invalidity. It is rejected before
  policy admission; it is neither R8 admission rejection nor core R1 reference
  rejection.

---

## 4. Policy grammar (`.policy.lara` → `Policy`)

```
policyTop  ::= "policy" ident { policyDecl }

policyDecl ::= sortDecl | conDecl | predDecl
             | ruleDecl | contraryDecl | exceptionDecl | admissionDecl | groupModeDecl

-- The signature blocks (spec §2, §3.4; lara-core@0.2). Unlike everything else
-- in this grammar these are NOT presentation-only: they lower to `unitSigma`
-- and the checker enforces them as rejection class R2.
sortDecl   ::= "sort" ident { "," ident }
conDecl    ::= "con"  ident [ "(" [ sort { "," sort } ] ")" ] ":" sort
predDecl   ::= "pred" ident [ "(" [ sort { "," sort } ] ")" ]
sort       ::= "Num" | "Str" | ident       -- two reserved base sorts, then declared names

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

- The signature blocks are printed immediately after the `policy` header, in the
  canonical order `sort` (one line carrying every declared sort), then one `con`
  line per constructor, then one `pred` line per predicate. Each block is elided
  when empty, so a signature-free policy prints byte-identically to the pre-`@0.2`
  grammar. A nullary symbol is spelled **without** parentheses (`con alice : Sys`,
  `pred blinded`); `()` parses but never prints, the usual permissive-parser /
  canonical-printer split.
- `Num` and `Str` are reserved: they are the sorts of the two term literal forms
  and are not declarable. `sort Num` **parses** — the parser is a decode boundary
  and records what was written — and is rejected by the checker as base-sort
  shadowing (R2), exactly as a duplicate rule id parses and is rejected later.
- `allow-trusted` / `certifiers` are **absent** on defeasible rules and present
  only on strict rules (spec §4). The reference policy `empirical-v1` is
  defeasible-only, so neither appears there.
- The `admission` block is **optional**. `empirical-v1.policy.lara` omits it; the
  runtime interprets the rows as a finite exact-key association from
  `(LeafKind, Provenance)` to outcome. An omitted/empty block or an unmatched key
  defaults to `admit`, making lookup total. Repeating a key is source invalidity,
  not first- or last-row-wins.
- The source outcome precedence is source invalidity, policy R8, replay R13,
  duplicate-group R9, then core rejection. R8 is a valid source judgment, distinct
  from group R9 and core R1: it selects the first leaf in source declaration order
  whose exact key matches a `reject` row, and the CLI uses exit 1, empty stdout, and
  exactly one deterministic stderr line identifying its leaf id, kind, provenance,
  and matched admission row. Source invalidity uses exit 2 and empty stdout;
  replay/group/accepted/core-rejection paths retain core-verdict stdout.
- Group consistency reads all declared leaves before pruning. Policy-quarantine
  and group-quarantine seeds are unioned once; one prune removes seeded leaves,
  every dependent argument (including dependencies nested in premises and
  discharges), and every attack with a removed raw endpoint. Blocked reporting and
  the canonical audit derive from that same prune. Audit rows follow leaf
  declaration order, list `PolicyQuarantine` before each causing
  `GroupQuarantine` (once, in group order), and list removed arguments/attacks in
  declaration order; every removed leaf has exactly one row with nonempty causes.

---

## 5. Support terms: premises implicit, discharges explicit (versioned contract)

For the legacy explicit form, `by r(g1, …, gn)` supplies the **full ground
substitution `θ`** over `r`'s declared parameters, positionally (`r`'s i-th
parameter ↦ `gi`). The parenthesized terms are θ bindings, not premise
sub-argument references. The elaborator reconstructs each implicit premise by
computing `Apᵢ · θ` and resolving the unique declared leaf or prior `arg` whose
conclusion is `≡ Apᵢ · θ` (spec §3.2 `nf`-equality).

This explicit positional reading is the historical v0.1 contract reflected by
the original A/B sources. It explains the older notation's divergence from
`docs/spec.md` §4.4's `by r(a1,…,an)` premise-reference notation. The additive
`lara-syntax@0.5` form may instead write `by r from [ref1,…,refn]`; Appendix D
defines that form. Inferred references select the support terms directly in
policy-premise order, including the principal leaf such as `e1` or `e7`, and
the elaborator derives θ by ordered matching.

Both forms reach the checker as a fully explicit support term. Explicit
premise reconstruction is untrusted elaborator work, as stated in spec §4.1;
inferred reconstruction is deterministic and source-selected, as specified in
Appendix D. Discharges and open holes remain explicit in both forms.

**Explicit-form determinism (plan D3).** For positional θ, premise resolution is
a total function on well-formed input:

- `nf`/`≡` is decidable and the declared leaf+arg set is finite, so the set of
  declared conclusions matching `Apᵢ·θ` is computable;
- **exactly one** match ⇒ that sub-term (deterministic);
- **zero** matches ⇒ a located elaborate error (unresolved premise);
- **≥ 2** matches ⇒ a located elaborate error (ambiguous premise).

No search, no backtracking, no preference — explicit premise reconstruction is
deterministic and total on well-formed input. Inferred matching has its separate
left-to-right scope and precedence contract in Appendix D.

**Discharges stay EXPLICIT.** Each critical question is discharged by name:
`discharge q with <argRef>` (A/B use bare leaf ids: `discharge randomization with
e2`). Open holes are explicit too: `open q as o`. The `D ⊎ H = questions(r)`
accounting invariant (spec §4.2) is checked by the elaborator against the resolved
discharge/open sets. No premise edits are needed for the historical explicit
A/B sources under this positional rule; current inferred sources are specified
in Appendix D.

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

> **AMENDMENT (`lara-syntax@0.3`, 2026-08-08).** §7's claim that A0.5 adds **no**
> presentation attack type no longer holds as of `@0.3`. Appendix B.5 admits a
> dotted segment that names a rule's premise *label* (`a2.binding.leaf`) beside the
> existing integer spelling (`a2.1.leaf`), and the printer cannot choose between
> them: `printProgram :: Program -> String` never receives the `Policy`, and
> `Source` keeps the program and its policy as separate files, so the labels the
> choice would depend on are not in scope where printing happens. If the authored
> spelling is not recorded in the presentation AST, `parse ∘ print = id` fails for
> whichever spelling the printer does not pick — and making a *program* file's
> canonical form depend on a *different* file would be worse than the problem it
> solves.
>
> **Resolution.** The presentation `Program` carries a shallow step,
> `SurfaceStep = StepIndex Int | StepName String`, and `Lara.Elaborate` resolves
> `StepName` against the target rule, where the policy *is* in hand
> (`elaborate sigma registry program policy`). This is the same A1a → A1b contract
> `Lara.Syntax`'s header already describes for support terms: the parser records
> what the surface states and leaves the rest for the elaborator.
>
> **Scope.** The amendment is **strictly additive**. The integer spelling keeps
> working, keeps its meaning, and stays canonical for any premise without a label;
> the §7 table, the terminal-marker rule, and the printer clauses above are
> unchanged for it. **No Unit-reachable type moves** — `Attack`, `Position`, and
> `Step` are untouched. `SurfaceStep` is presentation-only and is resolved away
> before the checker anchor exists, so the compiled AF is byte-identical either
> way.
>
> **Sign-off.** Signed off 2026-08-08; this was the sole open item of the
> `lara-syntax@0.3` design pass (PR #92), now resolved. The surface rules are
> Appendix B.4 and B.5 below.

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

3. **Premises implicit, discharges explicit (§5).** Legacy positional `by r(…)`
   supplies full ground `θ`; premise sub-terms are reconstructed by unique
   `≡`-match (0 ⇒ error, 1 ⇒ resolved, ≥2 ⇒ error). Current `@0.5` sources may
   use `by r from […]`, whose ordered source references and matching contract
   are defined in Appendix D. Discharges and holes remain explicit.

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

-- NEW
newtype ArgRef = ArgRef String
  deriving (Eq, Ord, Show)

type ArgDischarge = [(QuestionId, ArgRef)]

data ArgInstantiation
  = ExplicitTheta SupportTerm
  | InferTheta RuleId [ArgRef] ArgDischarge [ObligationId] Assurance
  deriving (Eq, Show)

-- CHANGED: argClaim :: PropId  →  argConcl :: ArgConcl
data Arg = Arg
  { argId             :: ArgId
  , argConcl          :: ArgConcl
  , argInstantiation  :: ArgInstantiation
  }
  deriving (Eq, Show)
```

Exports gained `ChallengeTarget (..)`, `ArgConcl (..)`, `ArgRef (..)`,
`ArgDischarge`, and `ArgInstantiation (..)`. No Unit-reachable type
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

---

## Appendix B — `lara-syntax@0.3` (one source-level migration, 2026-08-08)

Additive over `lara-syntax@0.2` except for §3's ordinary `claim nl`: every
claim-form `nl` now adopts B.6's brace contract. Existing `@0.2` prose with a
literal `{` or `}` must spell it `{{` or `}}` under `@0.3`; the committed
`corpus-units/lbcs/C05` and `corpus-units/sapg/C06` sources make exactly this
spelling migration. `nl` does not enter `Unit`, so the migration changes no
`.core.sexp` byte.

Every form below is parsed into the **presentation AST** and **expanded in
`Lara.Elaborate` before the checker anchor exists**; every form elaborates to a
byte-identical `Unit`. Nothing here changes `Unit`, the `.core.sexp` door, the
wire codec, `checkUnit`, or the strict backends. Motivation: the comparison
worked examples (`examples/S2`, `S3`, `S4`) make the author write `num_lt`
argument orders, premise slot indices, and two θ vectors by hand — none of
which is the research claim being made. The direction-of-goodness contract
behind the form is written up in `lean/Lara/Comparison.lean`; the surface rules
are Appendix B.1–B.3 below.

Expansion happens in the elaborator and not in `Lara.Syntax` on purpose: spec
result 12 (`parse ∘ print == id`) is stated on the presentation AST, and
macro-expanding at parse time would lose round-tripping for exactly these forms.
A `comparison` round-trips as a `comparison`, never as its expansion.

**`@0.3` is where #88 splits.** `#88a` — `nl` interpolation (B.6) — lands here.
`#88b` — `let` value bindings and named premise-slot references `(prem e1)` —
waits on #89 (the many-sorted Σ) and is **not** part of `@0.3`: a mistyped bare
binding name is indistinguishable from a nullary constant until a declared
signature can reject it, and App. A declares the `cert(…)` payload opaque, so a
surface `(prem e1)` needs its own layering decision (made at `lara-syntax@0.6`;
Appendix E).

Identifier aliases used below are all `ident` (§1.3), spelled distinctly for
readability: `propId` (a `claim` id), `leafId`, `argId`, `ruleId`. `binding` is
§3's `binding` block. `prop`, `apat`, and `param` are §2's.

### B.1 Measurand table with declared polarity

```
measurandLine ::= "measurand" ident ":" sort [ "where" polarity ]
polarity      ::= "higher-is-better" | "lower-is-better"
sort          ::= §4's sort           -- "Num" | "Str" | a declared sort name
```

```
measurand accuracy   : Num  where higher-is-better
measurand perplexity : Num  where lower-is-better
```

- A **policy-level** declaration, partitioned like `rule`/`contrary`/`exception`/
  `theory`; order-insensitive.
- Polarity is **domain knowledge, not usage**: whether a larger accuracy or a
  smaller perplexity is the better result cannot be recovered from how the number
  is used in an artifact. So it is **declared and not inferrable**, which is why
  it is written here rather than derived at a use site.
- The elaborator reads it to select the comparison scheme (B.2) whose rules are
  written in the measurand's direction. **It never enters `Unit`** — nothing
  downstream consumes it. That is what keeps the declaration on the surface track
  and out of the core.
- Declaring the same measurand twice in one policy is a **parse error** (the same
  rule, and the same reason, as A.2's duplicate digest: a silent first-wins lookup
  would pick a polarity the author did not intend).
- **#89 landed here, as designed.** The `: Num` slot was always a **sort
  position**, not decoration, so `lara-core@0.2`'s many-sorted Σ extends *this*
  declaration rather than introducing a parallel one: the slot now admits any
  sort §4 declares, over the same vocabulary the `sort` block names. The two
  tracks never forked the spelling.
- **The `where` clause is optional and `Num`-gated.** A polarity presupposes an
  *ordered* domain and only `Num` is ordered, so a polarity clause on a
  non-`Num` measurand is a parse error. A `Num` measurand with no clause is
  well-formed; it simply cannot key a `comparison-scheme`, and a `comparison`
  block naming it is a located elaboration error
  (`ComparisonMeasurandNoPolarity`) rather than a silent default direction.

### B.2 The `comparison-scheme` policy block

```
schemeBlock ::= "comparison-scheme" relation polarity
                "recheck" "=" ruleId
                "bridge"  "=" ruleId
relation    ::= "strictly-better" | "at-least-as-good"
```

```
comparison-scheme strictly-better higher-is-better
  recheck = beats_recheck
  bridge  = beats_baseline

comparison-scheme at-least-as-good higher-is-better
  recheck = tie_recheck
  bridge  = no_worse
```

- A policy-level declaration, partitioned and order-insensitive like B.1.
- It exists because **rule names are policy-specific**. `examples/S2` uses
  `beats_recheck`/`beats_baseline`; `examples/S3` uses `tie_recheck`/`no_worse`
  under a different policy entirely. A `comparison` form that hardcoded one
  policy's rule names would be unusable in the other.
- Schemes are keyed by the **pair (relation, polarity)**, not by relation alone.
  Relation alone cannot express direction, because the *rules* carry it: which
  argument order the strict rule's premises expect is fixed when the rule is
  written. Binding the scheme to the pair is what makes a disagreement between
  the declared direction and the rules' direction *nameable at all*; the
  direction-of-goodness check in the well-formedness list below is what makes it
  **rejected**. Neither half suffices alone: structural correspondence maps the
  recheck conclusion into the bridge's comparison premise even when the two
  rules use disjoint parameter names. It constrains the rules to each other, not
  either rule to the declared `polarity`, so a policy with both flipped together
  is internally consistent and externally backwards.
- A policy declares only the pairs its rules actually support; there are at most
  **four** entries. A policy with no matching scheme simply has no `comparison`
  form available for that pair — a located error at the use site, never a silent
  fallback. A duplicate (relation, polarity) pair is a **parse error**.
- Well-formedness the elaborator checks at each `comparison` **use site**, after
  selecting the scheme by the authored measurand's polarity. Each failure is a
  located error naming that comparison:
  - `recheck` is a **strict** rule listing an `ord@1` certifier;
  - `bridge` is **defeasible**;
  - `bridge` has **exactly two premise patterns**, in either order: one
    structurally corresponds to `recheck`'s conclusion, and one is the six-role
    binding pattern over system, baseline, measurand, dataset, result value, and
    baseline value;
  - the authored conclusion in the `comparison` line (B.3), **after the
    elaborator forms its 4-ary version** from the 2-ary system pair plus the `on`
    and `@` fields, matches `bridge`'s declared conclusion pattern. The check is
    against the formed 4-ary atom, never against the 2-ary surface spelling;
  - `bridge`'s conclusion pattern is **4-ary over S, B, Q, D with the favored
    system first**. This positional convention is what
    `better(sys_new, sys_base) on accuracy @ imagenet_val` elaborates against.
    Richer bridge conclusions — e.g. one carrying an evaluation-setting
    parameter — are an explicit **non-goal** for `@0.3`.
  - **direction of goodness**: `recheck`'s conclusion, with each operand
    attributed to `result` or `baseline` by *which match introduced it*, is
    written in the order the measurand's `polarity` declares — `rel(base, ours)`
    for `higher-is-better`, `rel(ours, base)` for `lower-is-better`, i.e. exactly
    the lookup table in B.3. Without this check `polarity` would be inert after
    scheme selection, and a policy whose `recheck` and `bridge` rules were
    flipped *together* would certify a worse system as `better` — §1.2's hazard,
    reachable through a mis-written policy rather than a mis-written artifact.
    The error is located at the `comparison` use site, not at the scheme
    declaration or a backend rejection downstream.
- **The form inherits whatever the scheme's rules demand.** If `beats_recheck`'s
  premise patterns share one `Exp` variable, both cells must come from the same
  experiment, so a baseline number quoted from a *prior paper's* experiment is
  unauthorable through that scheme and needs a rule (and a scheme) written with
  two experiment variables. This is a domain fact expressed by the policy, not a
  limitation of the sugar; the θ-consistency error names the conflicting binding
  so it reads that way.

### B.3 The `comparison` declaration

A new program-level `decl` (§3), alongside `claimDecl`/`leafDecl`/`argDecl`/… .

```
comparisonBlock ::= "comparison" ":" prop "on" ident "@" ident
                    "relation" "=" relation
                    "recheck"  "=" argId
                    "bridge"   "=" argId
                    "result"   "=" leafId
                    "baseline" "=" leafId
                    "binding"  "=" leafId
                    claimsBlock
                    [ "supports" propId ]

claimsBlock     ::= "claims" propId
                    "nl"      "=" nlString
                    "binding" "=" binding
```

The `prop` after `:` is the authored conclusion's **system pair** — a 2-ary atom
`pred(S, B)` with the favored system first; the `on <measurand> @ <dataset>`
fields supply Q and D, and the elaborator forms the 4-ary conclusion the scheme's
bridge declares (B.2). `nlString` is B.6's interpolating string; `binding` is §3's
attestation block.

Worked, from `examples/S2`:

```
comparison : better(sys_new, sys_base) on accuracy @ imagenet_val
  relation = strictly-better
  recheck  = a1
  bridge   = a2
  result   = e2
  baseline = e1
  binding  = e3
  claims c2
    nl      = "The reported baseline accuracy 0.71 is strictly below the reported system accuracy 0.74"
    binding = { author = alice, audit-status = reviewed }
  supports c1
```

- The author never writes `num_lt`, never a slot index, never an argument order.
  Switching the measurand to one declared `lower-is-better` generates the flipped
  goal from the same source.
- **The generated-goal lookup contract:**

  | `relation` | `higher-is-better` | `lower-is-better` | research reading |
  |---|---|---|---|
  | `strictly-better` | `num_lt(base, ours)` | `num_lt(ours, base)` | "outperforms" |
  | `at-least-as-good` | `num_le(base, ours)` | `num_le(ours, base)` | non-inferiority, ties |

  This is a **lookup contract, not elaborator magic**: direction lives in the
  policy's rules. Structural correspondence between the recheck conclusion and
  the bridge comparison premise transfers the result/baseline roles across
  independently named rule parameters; the bridge's six-role binding premise
  then ties those roles to its system, baseline, measurand, dataset, and value
  parameters. That correspondence constrains the *rules to each other*; it says
  nothing about whether either rule matches the declared `polarity`. Each cell
  is realized only if the policy declares a scheme for that (relation, polarity)
  pair, written in that direction (B.2) — and B.2's direction-of-goodness check
  is what enforces "written in that direction",
  rejecting a scheme whose rules realize the *other* row of this table than the
  one its `polarity` names. The table is therefore a specification of the
  elaborator, not a parallel description of it: it is the same table
  `Lara.Comparison.goalOf` computes in the Lean development (`lean/`), and the
  Haskell now checks against it rather than merely being expected to agree.
- **`relation` is required and closed**, and both members are needed.
  Non-inferiority — "matches the baseline at a third the cost" — is a distinct and
  common research argument, and `examples/S3` is exactly that case; without
  `relation` this form could not express S3 at all.
- **The sub-claim is declared, not vanished.** The comparison sub-claim carries
  authored prose, an author attestation, and possibly a `status` line — all of
  which reach `Unit` and none of which can be machine-invented. So the block
  *declares* the sub-claim's id and human parts in the `claims` sub-block, and the
  elaborator emits the claim with the **generated goal as its `formal`**. Only the
  arithmetic is generated. Declaring the id also keeps `status c2`, and any future
  attack on the sub-claim, resolvable by name.
- **Both argument ids are author-declared** (`recheck = a1`, `bridge = a2`), and
  this is not cosmetic: `examples/S4` attacks the generated structure by id and
  position (`undermine x1 a2.binding.leaf`). Anonymous or derived ids would break
  every existing attack and put byte-identity out of reach.
- **No value bindings are needed to name the cells.**
  `Lara.Strict.Cell.premiseCell` already extracts the unique numeric literal from
  a premise — it is what `ord@1` itself uses — so `result = e2` suffices and the
  elaborator reads the value out of the named leaf. The leaf's premise-cell
  obligation (exactly one numeric literal anywhere in its argument terms) becomes
  a **precondition of this form**: violating it is a **located source error naming
  the leaf**, never a downstream backend rejection the author has to decode.
- **The binding leaf is never generated.** `comparison_setup` is attested evidence
  carrying an author, a provenance tag, and `refs`. `binding = e3` names an
  *existing* leaf; that line stays a human claim. If the block synthesized it, the
  sugar would manufacture evidence nobody attested, and the thing `examples/S4`
  attacks would be something the compiler invented.
- **Generating certificates adds no trust.** Replay re-checks the certificate
  against the goal and the premises, so a wrongly generated certificate is an R13
  rejection, never a false accept. The elaborator is a convenience whose output is
  independently verified.
- **Located errors** (all raised before the checker anchor exists):
  - no matching `comparison-scheme` for the (relation, polarity) pair;
  - the measurand named by `on` is undeclared;
  - `binding` names something that is not a declared leaf;
  - `result` or `baseline` names a leaf failing the premise-cell obligation;
  - **`result` and `baseline` name the same leaf**;
  - **generated id collisions** — the `recheck`, `bridge`, or `claims` id colliding
    with a declared `decl` or with each other;
  - **duplicate or overlapping `comparison` blocks**;
  - **authored conclusion vs. the supported claim's `formal`** mismatch;
  - measurand/`on`-field inconsistency (the measurand θ-matched out of the named
    leaves disagreeing with the one written after `on`).

### B.4 Labelled rule premises

```
premiseList     ::= "[" [ labelledPremise { "," labelledPremise } ] "]"
labelledPremise ::= [ ident ":" ] apat
```

This supersedes the `"premises" "=" "[" [ apat { "," apat } ] "]"` fragment of §4's
`ruleDecl`; everything else about `ruleDecl` is unchanged.

```
rule beats_baseline(S, B, Q, D, Sv, Bv)
  mode     = defeasible
  premises = [ cmp:     num_lt(Bv, Sv),
               binding: comparison_setup(S, B, Q, D, Sv, Bv) ]
  …
```

- Labels are **optional**, per premise. An unlabelled premise behaves exactly as
  it does today.
- **Policy well-formedness**, checked at declaration time: a rule's premise labels
  must be **disjoint from that rule's question ids**, and `rule` and `leaf` are
  **reserved from the premise-label namespace** (§1.3 already reserves them from
  the question-id namespace) — otherwise `a2.leaf.leaf` parses two ways. Both
  namespaces are policy-declared, so a collision is statically detectable and is
  **rejected at declaration time**, not discovered at an attack site.
- Duplicate labels within one rule are an error, for the same reason.
- Labels **never enter `Unit`**: `cmp` and `0` resolve to the same
  `StepPremise 0`, and the rule's compiled form is unchanged.

### B.5 Attack-path name segments

See the **AMENDMENT** note appended to §7, which this subsection is the surface
half of.

- A dotted segment of a position suffix (§7) that is a **decimal integer** is a
  `StepIndex`; **otherwise** it is a `StepName`, which the elaborator resolves
  against the target rule to **either** a premise label (B.4) **or** a question id
  — at most one of the two, guaranteed by B.4's disjointness requirement.
- Integers keep resolving directly to `StepPremise`, unchanged; question ids keep
  resolving to `StepQuestion`, unchanged. The terminal `rule`/`leaf` marker rule
  of §7 is untouched.
- Both spellings elaborate to the **same `Position`**, and each **round-trips in
  the spelling it was written in** — which is why the presentation AST carries
  `SurfaceStep` rather than reconstructing a spelling at print time.
- All `comparison` blocks expand before any attack path resolves, so an
  `undermine` targeting a generated argument (or a label inside one) resolves
  against the post-expansion argument set.
- **Index basis.** Attack-path integers, `(prem i)` certificate slots, and
  premise-label resolution are all **0-based**. 1-based indices appear only in
  human-facing error text (`resolvePremises` zips `[1..]` today) and are converted
  at the message boundary — never in a generated certificate or a resolved `Step`.

### B.6 `nl` interpolation (#88a)

```
nlString  ::= '"' { nlChar | directive | "{{" | "}}" } '"'
nlChar    ::= any-char-except '"', newline, "{", "}"
directive ::= "{" "cell" leafId "}"
```

This block records the historical `@0.3` spelling. The active `@0.5` surface
retains the historical `@0.4` value-binding grammar introduced in Appendix
C.5: it permits inline spaces or tabs around directive tokens and retains those
authored gaps for round-tripping; the cell lookup and `renderDecimal` semantics
below are unchanged.

```
claim c1
  nl = "sys_new outperforms sys_base on ImageNet-val accuracy ({cell e2} vs {cell e1})"
```

- **The lexical contract for braces.** Every claim-form `nl` uses `nlString`:
  both §3's ordinary `claim` and B.3's nested `claims` block. Inside `nl`, `{{`
  and `}}` denote literal braces — the f-string / `format!` convention this
  surface's Python-literate audience already knows — and **any other `{` must
  open a recognized directive**, which in `@0.3` means `{cell <leafId>}`.
  Anything else is a **located error naming the claim**.
  This is strict rather than lenient on purpose: if `{cel e2}` (a typo) silently
  stayed literal text, a number the author believed was auto-synced would be
  frozen prose — the exact silent prose↔formal staleness this feature exists to
  kill.
- `{cell e2}` resolves via `premiseCell` on leaf `e2` — the same helper `ord@1`
  and the `comparison` form use — and is rendered back through `renderDecimal`.
  **No binding is required, so #88a stands alone** and does not wait on #88b.
- Interpolating a **cell** is the *stronger* form for the prose↔formal binding
  audit: a number quoted in prose is then guaranteed to equal the number the cited
  evidence leaf actually carries, sourced from the leaf itself. Interpolating a
  `let` would only guarantee agreement with a parallel declaration, which could
  itself be wrong. When #88b lands, `{acc_new}` becomes an **additional**
  interpolation source; it does not replace `{cell e2}`.
- **Preconditions and errors:** the named leaf must exist and must satisfy the
  premise-cell obligation (exactly one numeric literal); failure is a **located
  source error naming the leaf**.
- **Round-tripping.** Directives and `{{`/`}}` escapes round-trip **raw** through
  the printer and are never expanded there. Interpolation happens in the
  elaborator, so the resulting `nl` is a plain `String` before anything downstream
  sees it.

### B.7 Keyword vocabulary delta

`@0.3` adds these reserved words to §1.4's vocabulary block, which stays the
single `toString`/`parse` table:

```
measurand  comparison  comparison-scheme  recheck  bridge  result  baseline
relation  claims  on  where  cell
higher-is-better  lower-is-better  strictly-better  at-least-as-good
```

Closed tag enumerations added by `@0.3` (surface ↔ presentation AST):

| Field | Surface spelling | Presentation AST |
| --- | --- | --- |
| measurand polarity | `higher-is-better` / `lower-is-better` | `Polarity` `HigherIsBetter` / `LowerIsBetter` |
| comparison relation | `strictly-better` / `at-least-as-good` | `Relation` `StrictlyBetter` / `AtLeastAsGood` |

Neither reaches `Unit`; both are resolved away during expansion.

Two housekeeping notes:

- **Appendix A's omission is corrected here.** `@0.2` added `assurance` (A.1) and
  `theory` (A.2) without updating §1.4, leaving the vocabulary block stale. Both
  are now listed there under a `lara-syntax@0.2` sub-block.
- `test/SyntaxSpec.hs`'s `reservedWords` list **mirrors §1.4** and must be kept in
  sync with it. If it is not, the round-trip generator will emit identifiers that
  collide with the new keywords and the property will fail for a reason that has
  nothing to do with the grammar.


---

## Appendix C — `lara-syntax@0.4` (value bindings, 2026-08-11)

Additive over `lara-syntax@0.3`. This appendix adds a presentation-only table of
named ground terms and a one-token `nl` interpolation form. It does not change
`lara-core@0.2`, `Unit`, the `.core.sexp` door, the JSON/wire codecs, checker
judgments, strict backends, scientific claims, or verdicts.

### C.1 Grammar position and canonical form (D1)

```text
program      ::= artifactHeader valueBinding* declaration*
valueBinding ::= "let" valueName "=" term
valueName    ::= ident
```

The binding table appears after the complete fixed program header (`artifact`,
`policy`, and `use backends`) and before the first declaration. A `let` after
the first declaration is rejected. `cell` is reserved from `valueName` because
`{cell leafId}` already owns that directive head; every other `valueName` uses
the existing `ident` lexical class. The parser rejects a duplicate at its second
`let`.

The canonical printer preserves source order, prints one binding per line, and
prints one blank line before declarations when the table is non-empty. A legacy
program has an empty table and retains its previous canonical bytes. `@0.4`
adds the single keyword `let` to §1.4.

For example:

```lara
artifact ord_demo at sha256:5252525252525252525252525252525252525252525252525252525252525252
policy ord-v1
use backends [ord@1]

let candidate = sys_new
let baseline = sys_base
let metric = accuracy
let dataset = imagenet_val
let candidate_score = 0.74
let baseline_score = 0.71

claim c1
  nl      = "{candidate} outperforms {baseline} on ImageNet-val accuracy ({candidate_score} vs {baseline_score})"
  formal  = better(candidate, baseline, metric, dataset)
  binding = { author = alice, rationale = "Ordered comparison of two reported accuracy cells.", audit-status = reviewed }
```

In a `comparison`, bindings may occur in the ground terms of its conclusion,
but the typed selector fields remain identifiers:

```lara
comparison : better(candidate, baseline) on accuracy @ imagenet_val
```

Here `candidate` and `baseline` are term occurrences and are substituted.
`accuracy` after `on` is a `MeasurandId`, and `imagenet_val` after `@` is a
`DatasetId`; neither selector is a value-binding site.

### C.2 Typed presentation table and fail-closed names (D2, D4)

The presentation AST carries a distinct namespace and retains authored order:

```haskell
newtype ValueName = ValueName String

data ValueBinding = ValueBinding
  { valueName :: ValueName
  , valueTerm :: Term
  }

programValueBindings :: [ValueBinding]
```

Before substitution, the elaborator validates in this order:

1. reject duplicate names, including hand-built ASTs that bypass the parser;
2. reject the reserved name `cell`, including hand-built ASTs;
3. reject a name colliding with any constructor declared by `Σ`, regardless of
   that constructor's arity;
4. run `sortOf Σ` on every right-hand side and retain the exact `SortFault`.

There is no guessed or permissive fallback. An unbound bare term remains a
nullary constructor occurrence, so the existing strict `Σ` check rejects an
undeclared spelling.

Source-parser errors are located and use these exact messages:

```text
duplicate value binding: <name>
'cell' is reserved and cannot be used as a value binding name
expected a term
value binding declarations must precede all program declarations
```

The elaboration renderer uses these exact templates:

```text
value binding '<name>': duplicate declaration
value binding '<name>': reserved name (the 'cell' interpolation head)
value binding '<name>': collides with declared constructor '<name>'
value binding '<name>': ill-sorted right-hand side: <sort fault>
claim '<claim>': ill-sorted formal after value substitution: <sort fault>
```

`<sort fault>` is rendered by the existing `Σ` vocabulary:

```text
undeclared predicate '<predicate>'
undeclared constructor '<constructor>'
predicate '<predicate>' expects <expected> argument(s) but got <actual>
constructor '<constructor>' expects <expected> argument(s) but got <actual>
expected sort <expected> but got <actual>
```

Every ordinary claim formal is sort-checked after substitution, before an
unsupported or unqueried claim could disappear during lowering. Surviving leaf,
argument, and generated comparison terms still reach the checker-boundary R2
pass.

### C.3 Flat, simultaneous, non-recursive bindings (D3)

The elaborator builds one flat `ValueName → Term` environment. Every right-hand
side is validated exactly as authored and is never rewritten through that
environment. Substitution is therefore simultaneous and order-independent even
though printing and diagnostics preserve declaration order.

```lara
let x = y
let y = 0.74
```

This is not a chain. The `y` in `x`'s right-hand side is an ordinary constructor
occurrence and must itself be declared by `Σ`; the second binding does not turn
`x` into `0.74`.

### C.4 Substitution surface and consuming order (D5)

Only a nullary term `TCon (FunSym name) []` whose `name` is in the environment
is replaced. Traversal recurses into the arguments of applied constructors but
never replaces a constructor head. The pass visits every program-side
term-bearing field:

- `Leaf.leafProp`;
- `Claim.claimFormal`;
- `Arg.argInstantiation`: substitute inside each `ExplicitTheta` payload,
  including each `SRule.srSubst` term and nested premise/discharge support term;
  `InferTheta` keeps its named `ArgRef` values unchanged;
- `Comparison.cmpConclusion`.

The pass is consuming and runs exactly once:

```text
parsed Program
  -> validate binding names and RHS terms against Policy.policySigma
  -> substitute every authored term position
  -> validate every substituted ordinary claim formal
  -> expand claim prose ({name}, {cell leaf}, {{, }})
  -> clear programValueBindings
  -> expand comparison blocks
  -> resolve labels/attacks and lower to Unit
```

Comparison expansion therefore derives generated claims, θ vectors, and
certificates from already-substituted values. The post-expansion semantic
`Program` has an empty binding table and can be compared directly with an
equivalent hand-written unbound program. This is deliberately one-way: a brace
escape has already become semantic prose and must not be interpreted a second
time.

### C.5 Natural-language interpolation (D6)

The live brace grammar is:

```text
igap      ::= { " " | "\t" }
hgap      ::= ( " " | "\t" ) igap
directive ::= "{" igap "cell" hgap leafId igap "}"
            | "{" igap valueName igap "}"
            | "{{"
            | "}}"
```

`{cell e2}` retains Appendix B.6's premise-cell validation and canonical decimal
rendering. `{candidate_score}` looks up that binding and renders its authored
right-hand side with `prettyTerm`. The distinction is intentional: a numeric
binding preserves authored digits (`0.710` remains `0.710`), whereas a cell
renders the evidence-derived rational canonically (`0.710` becomes `0.71`).
A `TStr` binding can occur only in a hand-built presentation AST because the
concrete `.lara` term grammar has no string-literal term; if present, it retains
`prettyTerm`'s quoted and escaped spelling. Inline spaces or tabs around either
directive form are ignored during resolution but retained in the raw
presentation AST for `parse ∘ print = id`.

The same one-pass grammar applies to `Claim.claimNl` and
`ComparisonClaim.ccNlRaw`. Thus the C.1 example expands to the exact previous
prose:

```text
sys_new outperforms sys_base on ImageNet-val accuracy (0.74 vs 0.71)
```

A one-token directive is a value reference, so a missing binding fails closed.
A multi-token unknown head such as `{cel e2}` remains an unknown directive.
The concrete parser uses these exact messages:

```text
unmatched '}' in nl string (write '}}' for a literal brace)
expected a directive after '{' in nl string (write '{{' for a literal brace)
expected a leaf id in a '{cell …}' nl directive
unterminated '{cell …}' nl directive (expected '}')
unknown nl directive '<head>' (expected a one-token value reference or '{cell <leaf>}')
```

A parsed one-token reference is resolved during elaboration. The renderer also
covers hand-built presentation ASTs that bypassed the concrete parser, using
these exact templates:

```text
claim '<claim>': nl references undeclared value '<name>'
claim '<claim>': nl has an unterminated '{' directive
claim '<claim>': nl has an unescaped '}' (write '}}' for a literal brace)
claim '<claim>': nl has an unknown directive '{<body>}' (expected '{<value>}' or '{cell <leaf>}')
claim '<claim>': nl directive '{cell <leaf>}' names '<leaf>', which is not a declared leaf
claim '<claim>': nl directive '{cell <leaf>}' names a leaf that does not carry exactly one numeric literal (the premise-cell obligation)
```

### C.6 Opaque certificate boundary and explicit deferrals

Value substitution operates on `Term` fields in the presentation AST. It never
enters `Cert`: the certificate payload remains the native opaque S-expression
owned and decoded only by its named backend (Appendix A.1). Consequently,
`@0.4` does not add symbolic certificate slots such as `(prem e1)`; authored
certificates keep numeric premise slots. A future named-slot design must define
an explicit layer above the opaque payload rather than making the general value
pass inspect backend syntax. Appendix E (`lara-syntax@0.6`) defines exactly
that layer; value substitution still never enters `Cert`.

Likewise, value bindings do not rename named premise references. The plain-argument
theta-matching form is defined in Appendix D (`lara-syntax@0.5`).

## Appendix D — `lara-syntax@0.5` (plain-argument theta inference, 2026-08-12)

### D.1 Syntax and presentation scope

The inferred form records references instead of positional terms:

```text
supportTerm ::= "leaf" "(" ident ")"                          -- explicit leaf
              | ident "(" [ term { "," term } ] ")"           -- ExplicitTheta
              | ident "from" "[" [ argRefList ] "]"          -- InferTheta
argRef      ::= ident
argRefList  ::= argRef ("," argRef)*
```

`ExplicitTheta` owns the complete surface `SupportTerm` for an explicit leaf or
rule application. `InferTheta` owns the complete inferred payload: the rule id,
named premise references, shallow discharge references, obligation ids, and
assurance.

The `ident` and `term` nonterminals are those defined in §§1.3 and 2. The
`from` alternative is contextual after the rule identifier; it does not change
the lexical identifier class. The lexer still accepts `from` as an identifier
in positions where a rule, predicate, leaf, or argument name is expected.
`InferTheta` carries these fields as one presentation payload; the parser folds
`discharge`, `open`, and `assurance` lines into that payload. For either rule
instantiation — explicit `r(g1,…,gn)` or inferred `r from [...]` — the parser
drops the critical-question token in `open q as obligation` and retains only the
`ObligationId`. The canonical printer re-emits each retained hole as
`open obligation as obligation`. §3 leaves `dischargeLine`/`openLine` order free
and A.1 lets `assurance` fold in anywhere; the canonical printer picks one order
— discharges, then opens, then assurance. For inferred arguments it prints the
rule, named references, discharges, opens, and assurance.

On a bare `leaf(…)` support term there is nothing to retain: the parser accepts
`discharge` and `open` lines there and then drops them entirely, id and all
(issue #135). That is the opposite of A.1's ruling for `assurance`, which is a
parse error in the same position precisely so the author is not misled.

Re-emitting the obligation id in both slots is exact, not a guess at the
discarded token: §6.1 reads a hole's `ObligationId` *as* the question it leaves
open (`holeNames` in `Lara.SupportTerm`, Lean `H : List QuestionId`), so
`obligation` names the question actually in force and the dropped `q` is never
consulted after parsing. Printing therefore normalizes a divergent `q` to the
obligation id. Every committed `open` line already spells the two identically.
An earlier revision of this paragraph said the printer "intentionally omits
`open` lines"; that omission was issue #127 — it broke result 12
(`parse ∘ print = id`) on any term with a non-empty hole set.

At argument `a`, each reference is resolved in this fixed scope. A name that
matches both namespaces is ambiguous; a name that matches neither is unresolved.
Only declared leaves and arguments already elaborated earlier in declaration order
are in scope. A later argument is never a valid prior-argument reference. A prior
argument contributes its complete support term and its derived conclusion.

### D.2 Matching order and derived support

The elaborator first checks the reference count against the rule premise count.
It then resolves references from left to right, matching reference `i` against
premise `i` in policy order. Matching uses the existing one-way `matchAPat`
operation and its normalized term equality. Shape mismatches and repeated
parameter conflicts are reported at the reference and one-based premise
position. After all premises match, every declared rule parameter must be bound;
the resulting substitution is reordered by `ruleParams`. The selected complete
support terms become the semantic premise list in the same authored order.

Inference is therefore deterministic: it performs no global premise search,
backtracking, or preference selection. Explicit positional arguments retain their
existing elaboration path, including unique premise reconstruction. The two paths
meet only at the complete `SRule` consumed by the checker.

### D.3 Diagnostics and precedence

Inference failures are checked in this order: unknown rule; reference-count
mismatch; left-to-right scope resolution (including an underivable prior
conclusion); left-to-right premise matching; unbound parameters in `ruleParams`
order; then inferred discharge and announced-conclusion validation. The complete
`InferTheta` payload makes malformed explicit/inferred pairings unrepresentable
by the AST, so they have no diagnostics. Diagnostics identify the argument and
rule, and reference failures also identify the one-based premise number and exact
source spelling. Shape mismatches include the selected proposition; conflicts
include the parameter and both terms.

The stable diagnostic families are `UnknownRule`,
`ThetaReferenceCountMismatch`, `ThetaReferenceUnresolved`,
`ThetaReferenceAmbiguous`, `ThetaReferenceShapeMismatch`,
`ThetaReferenceConflict`, `ThetaReferenceConclUnderivable`, and
`ThetaParameterUnbound`.

### D.4 Explicit/inferred equality contract

When an explicit argument spells each parameter exactly as the cited premise
terms spell it, explicit and inferred elaboration produce byte-identical
semantic units, core S-expressions, verdict JSON, and exit classifications.
The inferred substitution adopts terms from cited propositions; explicit theta
retains the author's spelling. If spellings differ but are normalized-equal,
such as `0.710` and `0.71`, the semantic units can differ in bytes while their
verdict JSON and exit classifications remain equal. This spelling condition is
part of the contract; byte identity is not unconditional.

## Appendix E — `lara-syntax@0.6` (named certificate premise slots, 2026-08-12)

Additive over `lara-syntax@0.5`. This appendix adds a symbolic spelling for the
premise-slot references inside `ord@1` and `ra@1` certificate payloads, lowered
to the canonical numeric slots at elaboration. It does not change
`lara-core@0.2`, `Unit`, the `.core.sexp` door, the JSON/wire codecs, checker
judgments, strict backends, or replay identity — and, uniquely among the
additive versions, it changes no lexer or parser rule either.

### E.1 Symbolic form, supported backends, and grammar position (D2, D7)

Inside the opaque `sexp` payload of `cert(…)` (Appendix A.1), a premise-slot
node may spell its slot by source name:

```text
slotRef     ::= "(" "prem" slotNumeral ")"   -- canonical numeric slot (unchanged)
              | "(" "prem" ident ")"         -- symbolic: a declared leaf or prior argument
slotNumeral ::= "0" | nonZeroDigit digit*    -- a canonical natural (no leading zeros)
```

A `(prem s)` node is *symbolic* iff `s` is not a canonical natural. If
`s` cannot begin a source identifier, such as `007`, `-1`, `+1`, `1.0`, or
`0x10`, it is a malformed numeral rather than a name. The dedicated
non-canonical-numeral error fires before name resolution.

Only the declared *reference positions* of a schema'd backend payload are
lowered. Each supported backend exports one flat schema — head keyword, arity,
0-based reference positions — and the closed aggregate table lives in
`Lara.Elaborate.CertSlots`; the elaborator learns no other backend grammar:

| backend | head | arity | reference positions | untouched positions |
| --- | --- | --- | --- | --- |
| `ord@1` | `ordcmp` | 2 | 0, 1 | — |
| `ra@1` | `radrop` | 3 | 0, 1 | 2 (the `frac` witness) |

There is zero concrete-syntax change: the wire S-expression sub-grammar already
admits an identifier atom, and the printer prints the stored payload verbatim,
so the surface AST keeps the authored spelling and `parse ∘ print = id` holds
unchanged. Lowering happens only at elaboration, *after* premise resolution, at
both instantiation sites: the explicit rule application and the inferred
`by r from […]` form (Appendix D). Every declared premise-reference position in
the wire `Unit` therefore carries a numeric slot.

Symbolic and numeric authoring of the same argument produce byte-identical
`Cert` payloads and byte-identical encoded `Unit`s; `examples/S6/` authors the
symbolic spelling and its committed `.core.sexp` golden is the standing
byte-identity witness. `lean/Lara/CertSlots.lean` mechanizes the lowering:
`lower_id_of_no_symbolic` (byte preservation on every payload the frozen
corpus can contain) and `lower_eq_numeric_subst` (lowering equals substituting
every resolved name first).

### E.2 Name resolution: namespace and collision policy (D3)

A symbolic name resolves in the `lara-syntax@0.5` reference namespace —
declared leaves ∪ prior arguments, exactly the scope an inferred θ reference
sees (Appendix D.1): "prior" means already elaborated earlier in declaration
order, and a later argument is never a valid reference. A name that matches both namespaces is a **hard error**,
never silently one of them — deliberately aligned with the inferred-reference
resolver, not with the discharge resolver's silent leaf preference (that
inconsistency is tracked separately as issue #129, untouched here).

### E.3 Slot mapping and mixed forms (D4, D5)

The resolved referent — a leaf's `SLeaf` or a prior argument's elaborated term
— is located in the argument's **resolved premise sequence** by term equality.
That sequence is exactly the one replay hands the backend, so a name denotes
"the slot this source occupies in the premises the certificate is checked
against", never a positional convention of the surface text.

- Exactly one occupied slot → that 0-based index.
- Zero slots → error: the referent is real but is not among this argument's
  premises.
- Two or more slots (the same leaf feeding two premises) → error; the author
  must cite numeric slots there.

*Representation rule:* locating matches whatever representation the author's
spelling actually put in the resolved premise sequence. A prior-argument
citation locates both the argument's elaborated term (what `by r from […]`
premise resolution stores) and the bare `SLeaf` spelling of its identifier
(what an authored premise list would store); the explicit/inferred twins
therefore lower identically, with no spurious not-a-premise error on one side.

Mixed symbolic and numeric references are legal: each reference position
lowers independently, so `(radrop (prem e4) (prem 1) (frac 119 500))` is
well-formed if `e4` resolves to slot 0's premise.

### E.4 Pass-through, the dead-wire rule, and the moved rejection site (D6)

Payloads stay backend-owned. Unknown backend/version payloads, non-`(prem …)`
nodes at reference positions, canonical numeric slots, and every
non-reference position are left untouched and reach the backend exactly as
today. This includes symbolic-looking `(prem s)` nodes at a matched schema's
non-reference positions, whether direct or nested: the schema does not declare
them as premise references, so the backend owns their meaning and rejection.
A backend with no declared schema (`nd@1`, E.7) always passes through
byte-identical. A head-keyword or arity mismatch under a *schema'd* backend
also passes through unless the payload contains a symbolic `(prem s)`
anywhere. No declared positions exist under a mismatch, so such a spelling
cannot be lowered; it fails at elaboration as a schema mismatch. Detection is
a generic sub-tree scan, and the elaborator still learns no backend grammar.

Consequences: every existing accepted artifact lowers to itself — frozen
payloads contain no symbolic names, and byte preservation is the E.1 Lean
theorem — and every existing rejection path is preserved. The intended
exception: spelling-level mistakes at a matched schema's reference positions
now die **earlier**, at elaboration instead of at certificate replay (R13):
malformed numerals (`(prem 007)`, `(prem -1)`), name typos (`(prem e44)`), and
symbolic names inside schema-mismatched payloads (`(ordcmp (prem e4))`, one
argument short) fail before the checker (`docs/rejection-surface.md` §1.2 and
the R13 row). Acceptance is unchanged.

### E.5 Stable error messages

The six diagnostic families are `CertSlotUnresolved`, `CertSlotAmbiguous`,
`CertSlotNotAPremise`, `CertSlotMultiSlot`, `CertSlotNonCanonicalNumeral`, and
`CertSlotSchemaMismatch` — located `ElabError`s in the `ThetaReference*` style
(D.3), attributed to the enclosing `arg` block. This list is their normative
home. The renderer uses these exact templates, where `A` is the enclosing
argument, `B` is the backend spelling `name@version` from the `assurance`
line, `N` is the authored reference spelling, and `I`/`J` are 0-based slots:

```text
arg 'A': certificate 'B' premise reference 'N' names neither a declared leaf nor prior argument
arg 'A': certificate 'B' premise reference 'N' is ambiguous between a declared leaf and a prior argument
arg 'A': certificate 'B' premise reference 'N' does not resolve to any of this argument's premise slots
arg 'A': certificate 'B' premise reference 'N' occupies premise slots I and J; cite a numeric slot
arg 'A': certificate 'B' premise reference 'N' is not a canonical slot numeral (use unsigned decimal with no leading zeros); write the canonical numeral or a source name
arg 'A': certificate 'B' payload does not match the backend's premise-reference schema but contains symbolic premise reference 'N'
```

### E.6 Recursion semantics (D8)

Lowering applies at **every** rule-application depth, resolving each declared
reference position against that node's own resolved premise list, with
diagnostics attributed to the enclosing argument's id. A nested certificate
on a premise instance therefore lowers against the nested instance's premises,
not the enclosing argument's. Symbolic-looking nodes outside a matched
schema's declared reference positions remain backend-owned as specified in
E.4.
The `@0.6` surface grammar
cannot yet author a nested assurance — a parsed rule application carries no
authored premise list, and `assurance` attaches only to the `arg` block's own
rule application — so the recursive case is reachable only from a hand-built
AST today, but it is on the path the moment premises become authorable.
`test/CertSlotsSpec.hs` records the reachability note and pins the recursive
behavior at the AST level through the real elaborator entry point.

### E.7 The nd@1 exclusion and future work (D1, D3)

`nd@1` admits no named slots and is deliberately schema-less: its payloads
pass through byte-identical and keep numeric `hyp` indices. `ord@1` and `ra@1`
payloads are single flat head applications with premise references at fixed
argument positions — a name is a stable notion there. `nd@1` payloads are
recursive de Bruijn proof terms: `hyp i` shifts under `lam` binders and
conflates premise slots with theory entries by offset, so "the premise named
`e4`" is not well-defined at a fixed payload position without teaching the
presentation layer the full ND grammar and binder discipline.

Two future-work notes, recorded here so the next design starts from them:

- *A named `nd@1` form* should start from Lean 4's kernel/surface split rather
  than inventing new machinery: the kernel term stays de Bruijn (`hyp i`), the
  presentation writes named binders (`(lam h FORMULA CERT)` with `h` bound in
  `CERT`, and premise/theory slots cited by source name), and the elaborator
  owns the index shifting, exactly as Lean's elaborator lowers
  `fun h => … h …` to bound-variable indices. The locally-nameless literature
  covers the metatheory of that lowering.
- *Rule premise labels as a second symbolic class (considered and deferred).*
  `premiseLabelIndex` already maps a rule's declared premise labels to slot
  indices, and a label names the backend slot directly — it would even cover
  the E.3 multi-slot case, where this design falls back to numerals. Deferred
  at `@0.6` because labels are optional (`rulePremiseLabels ::
  [Maybe PremiseLabel]`), so they cannot be the universal namespace, and a
  second symbolic class would need its own collision policy against leaves and
  priors, growing exactly the resolution surface this feature is supposed to
  keep predictable. Premise-label citation remains a natural future
  `lara-syntax@0.x` extension.