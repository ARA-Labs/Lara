# Lara surface grammar (`lara-syntax@0.11`)

This document defines the concrete `.lara` grammar implemented by the parser
and printer (`Lara.Syntax`) and the `Program → Unit` elaborator
(`Lara.Elaborate`). The abstract checker contract is [the language
specification](spec.md); [the base-language design](theory-core.md) covers the
surface calculus and its preservation results.
The grammar is grounded in the committed examples and the abstract syntax
of `src/Lara/AST.hs`.

**How to read this document (non-normative).** This is the contract for the
concrete `.lara` syntax: what the parser accepts, what the printer emits, and
how each surface form lowers to the abstract syntax the checker consumes. Its
audience is implementers of the parser/printer/elaborator and readers writing
or reviewing `.lara` files by hand. The main body defines the base grammar;
each appendix (A–J) specifies one group of constructs of the current surface.
An appendix's title carries the `lara-syntax` version label that code and tests
use to cite it, and appendix letters and subsection numbers are stable
references. If you are new to Lara,
read the [README](../README.md) and a worked example
([`examples/README.md`](../examples/README.md)) first; this document assumes
you already know what a claim, leaf, argument, and policy are (spec §0 has
the one-paragraph vocabulary).

Every presentation convenience lowers to the exact bytes of the terse spelling
it abbreviates; named certificate forms, for example, lower to the numeric
spelling's exact bytes. This surface gets *more readable*, never *natural*: a
convenience removes transcription, not checking. [The specification](spec.md#natural-language-and-the-trusted-boundary)
states where natural language is admitted and where the trusted boundary lies.

Versioning: the presentation surface is versioned **separately** from the core
(`docs/spec.md` §2.1). This document defines `lara-syntax@0.11`; the current
core is `lara-core@0.3`. Signature declarations lower to `unitSigma`. Every
other presentation form is resolved during elaboration, so the decoded core
object does not depend on the surface version. The Haskell `parse ∘ print == id` property covers this current
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
constructs are frozen separately in `docs/evidence-admission-design.md#policy-admission-at-the-source-boundary`.
Byte-level `lara-evidence@0.1` is implemented through `lara check-ara`; Appendix J defines its source fields and the [evidence-admission design](evidence-admission-design.md#concrete-package-contract) defines the package contract.

---

## 0. Two top-levels, one file, disambiguated by the leading keyword

A source file is **either** an artifact program **or** a policy. The authoritative
disambiguator is the **first significant token**:

| Leading keyword | Top-level | Conventional extension | AST target |
| --- | --- | --- | --- |
| `artifact` | artifact program | `.lara` | `Program` |
| `policy`   | policy            | `.policy.lara` | `Policy` |

The extension is a **convention** (and what `lara check`'s co-located policy
resolution keys on); the **keyword is normative**. A `.lara`
file that begins `policy …` is a policy, and vice versa. The two grammars share the
lexical layer (§1) and the proposition/term/pattern sub-grammars (§2), and are
otherwise disjoint.

---

## 1. Lexical grammar (tokenizer)

**Source text is UTF-8, by definition and not by environment**. A `.lara`
or `.policy.lara` file is a sequence of UTF-8 bytes; the character stream the
rules below run over is that byte sequence decoded as UTF-8, and bytes that are
not valid UTF-8 are not a program. Nothing about what a file means depends on
`LC_ALL`, `LANG`, or any other property of the machine reading it — two readers
that disagreed on the encoding would disagree about which identifiers a file
declares, and a symbol's identity is already its UTF-8 bytes downstream:
`Lara.Strict.ND.encodeAtomKey` frames every predicate and function symbol by
its UTF-8 byte length, which is the key the backend and the Lean adapter share.
The `lara` CLI implements this by setting its own encodings once, before it
reads anything (`textBoundary` in `app/Main.hs`); a file that is not UTF-8 is
refused at the read, with the same exit-2 boundary line an unreadable file gets.

This says nothing about which *characters* an identifier may contain — that is
§1.3's `letter`, which is Unicode-wide — and nothing about normalization:
nothing here applies a Unicode normal form, so two spellings of a name that
differ only by normalization are two different names.

The lexer runs in two modes. **Normal mode** is the default. **Ref-list mode** is
entered between `[` and `]` of a `refs = [ … ]` field and nowhere else (§1.3); it
exists solely to make `#` literal inside a source reference.

### 1.1 Whitespace and layout

Whitespace (spaces, tabs) and newlines separate tokens and are otherwise
insignificant: Lara is **not** layout-sensitive. Indentation in the examples is
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
namespace because they are terminal markers in attack position suffixes (§7):
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
by  supports  challenges  discharge  with  open
rebut  undercut  undermine
allow-trusted  certifiers  cert  trusted  none

-- signature declarations (§4)
sort  con  pred  Num  Str

-- Appendix A
assurance  theory

-- Appendix B
measurand  comparison  comparison-scheme  recheck  bridge  result  baseline
relation  claims  on  where  cell
higher-is-better  lower-is-better  strictly-better  at-least-as-good

-- Appendix C
let

-- Appendix D
from

-- Appendix J
extract  evidence-checkers
```
`as` is an ordinary identifier: a hole is spelled `open q` (Appendix F.3).
`from` is contextual after a rule identifier and is not a lexer-reserved
identifier. The symbolic `(prem name)` spelling of Appendix E adds no keyword:
it lives inside the opaque `sexp` payload of `cert(…)`, whose atom grammar
already admits identifiers.

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
              [ "extract" "=" extractionRequest ]    -- @0.11, Appendix J

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
openLine      ::= "open" ident                           -- open q        (explicit hole; @0.7, App. F.3)

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

- `use backends [ … ]` may be empty (`[]`). The backend registry holds `nd@1`,
  `ra@1`, `ord@1`, and `insp@1`; a backend listed by a defeasible-only artifact
  is **inert**.
- Field order inside `claim`/`leaf` is fixed: the parser accepts only the
  canonical printer order shown.
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
             | "evidence-checkers" "=" evidenceCheckers  -- @0.11, Appendix J

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
  when empty, so a signature-free policy prints no signature lines. A nullary symbol is spelled **without** parentheses (`con alice : Sys`,
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

## 5. Support terms: premises implicit, discharges explicit

The explicit form `by r(g1, …, gn)` supplies the **full ground
substitution `θ`** over `r`'s declared parameters, positionally (`r`'s i-th
parameter ↦ `gi`). The parenthesized terms are θ bindings, not premise
sub-argument references. The elaborator reconstructs each implicit premise by
computing `Apᵢ · θ` and resolving the unique declared leaf or prior `arg` whose
conclusion is `≡ Apᵢ · θ` (spec §3.2 `nf`-equality). This positional reading
differs from `docs/spec.md` §4.4's `by r(a1,…,an)` premise-reference notation.

The inferred form `by r from [ref1,…,refn]` (Appendix D) instead selects the
support terms directly in policy-premise order, including the principal leaf
such as `e1` or `e7`, and the elaborator derives θ by ordered matching.

Both forms reach the checker as a fully explicit support term. Explicit
premise reconstruction is untrusted elaborator work, as stated in spec §4.1;
inferred reconstruction is deterministic and source-selected, as specified in
Appendix D. Discharges and open holes remain explicit in both forms.

**Explicit-form determinism.** For positional θ, premise resolution is
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
`discharge q with <argRef>` (examples A and B use bare leaf ids: `discharge
randomization with e2`). Open holes are explicit too: `open q` (Appendix F.3).
The `D ⊎ H = questions(r)` accounting invariant (spec §4.2) is checked by the
elaborator against the resolved discharge/open sets.

---

## 6. Argument conclusion forms (`ArgConcl` / `ChallengeTarget`)

An `arg` announces a conclusion role. The checker consumes only the support term's
own `concl(w)` (spec §6.1), so the arm chosen **never changes the compiled AF** — it
records the author's stated role, which the elaborator resolves/validates.

| Surface | `ArgConcl` | Meaning | A/B site |
| --- | --- | --- | --- |
| `supports(c)`, `c` a declared `claim` | `SupportsClaim (PropId c)` | elaborator checks `concl(w) ≡ c.claimFormal` (spec §3.1) | `a1`, `pa`, `pb` |
| `supports(c)`, `c` **not** declared | `SupportsDerived (PropId c)` | `c`'s formal prop is **derived** from `concl(w)`; the elaborator records only the label. No status is computed for `c` unless a separate `status c` names it. | `d3` (`supports(c1_neg)`) |
| `challenges(q(u))` | `Challenges (ChallengesQuestion (QuestionId q) (ArgId u))` | attack-only arg; real edge is the paired `undercut`/`undermine` line. Target = the CQ `q` of arg `u`. | `d1` (`challenges(external_validity(a1))`) |
| `challenges(l)` | `Challenges (ChallengesLeaf (LeafId l))` | attack-only arg; target = frontier leaf `l`; real edge is the paired `undermine` line. | `d2` (`challenges(e6)`) |

The `challenges(…)` target is **presentation intent only**: `d1`'s real conclusion
(for the Unit) is `concl(leaf e4) = distribution_shift(…)`, and its defeat edge is
`undercut d1 a1.rule` — the challenge label and the attack line are independent, and
the elaborator uses the label solely for diagnostics. The two `ChallengeTarget`
forms mirror the two attackable non-root positions (a CQ discharge occurrence, a
frontier leaf), matching the shape of the attack targets in §7.

---

## 7. Attacks and the position-suffix ↔ `[Step]` mapping (FROZEN)

Attacks **reuse the frozen checker types** `Attack` / `Position` / `Step`
(`src/Lara/AST.hs`; Unit-reachable). The only presentation-side step type is
the shallow `SurfaceStep` described under named step segments below. The surface suffix has **one canonical spelling per (attack-kind,
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
`StepPremise`; otherwise it is a name, which resolves to a `StepQuestion` (the
question id) or, when it is a premise label, to a `StepPremise` (named step
segments, below). The **final**
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

**Named step segments.** A dotted segment may name a rule's premise *label*
(`a2.binding.leaf`; Appendix B.4 and B.5) beside the integer spelling
(`a2.1.leaf`). The printer cannot choose between the two spellings:
`printProgram :: Program -> String` never receives the `Policy`, and `Source`
keeps the program and its policy as separate files, so the labels the choice
would depend on are not in scope where printing happens, and a program file's
canonical form must not depend on a different file. The presentation `Program` therefore records the authored spelling in a shallow
step, `SurfaceStep = StepIndex Int | StepName String`, and `Lara.Elaborate`
resolves `StepName` against the target rule, where the policy *is* in hand
(`elaborate sigma registry program policy`). This is the contract
`Lara.Syntax`'s header describes for support terms: the parser records what the
surface states and leaves the rest to the elaborator.

The integer spelling keeps its meaning and is canonical for any premise without
a label; the table, the terminal-marker rule, and the printer clauses above
apply to it as written. `SurfaceStep` is presentation-only and is resolved
before the checker anchor exists, so `Attack`, `Position`, and `Step` carry no
trace of it and the compiled AF is byte-identical for either spelling.

---

## 8. Presentation AST types

`src/Lara/AST.hs` defines the presentation-only types for argument conclusions
(§6) and inferred support terms (Appendix D):

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

A single `ArgConcl` sum on `Arg` covers every conclusion role, so an
attack-only argument needs no separate declaration form. None of these types
reaches `Unit`; the Unit-reachable types (`Unit`, `SupportTerm`, `Attack`,
`Step`, `Position`, `Rule`, `Contrary`, `Exception`, `Prop`, `Term`, the `*Id`
newtypes, …) are separate.

---

## 9. Conformance of the committed examples

The committed examples conform to this grammar. `test/WorkedExamplesSpec.hs`'s
freshness property re-derives every `example.core.sexp` anchor from its `.lara`
source and policy, and the inline `EXPECTED VERDICT (golden oracle)` blocks in
examples A and B are the goldens described in
`docs/implementation.md#worked-examples`. The parser, printer and elaborator
share this grammar contract.

---

## Appendix A — Support-term assurance and theory tables (`lara-syntax@0.2`)

Two constructs, both decoding to the core abstract syntax with no new
Unit-reachable type (spec result 12 is unaffected). The strict-certificate
worked example is `examples/S1/` (`docs/implementation.md#worked-examples`);
the Unit-level certificate path is `Lara.Strict.ND` and `Driver.buildCertOk`.

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

## Appendix B — Comparisons, labelled premises and `nl` interpolation (`lara-syntax@0.3`)

Every form below is parsed into the **presentation AST** and **expanded in
`Lara.Elaborate` before the checker anchor exists**; every form elaborates to a
byte-identical `Unit`. None of them affects `Unit`, the `.core.sexp` door, the
wire codec, `checkUnit`, or the strict backends. Without them, the comparison
worked examples (`examples/S2`, `S3`, `S4`) would make the author write
`num_lt` argument orders, premise slot indices, and two θ vectors by hand —
none of which is the research claim being made. The direction-of-goodness contract
behind the form is written up in `lean/Lara/Comparison.lean`; the surface rules
are Appendix B.1–B.3 below.

Expansion happens in the elaborator and not in `Lara.Syntax` on purpose: spec
result 12 (`parse ∘ print == id`) is stated on the presentation AST, and
macro-expanding at parse time would lose round-tripping for exactly these forms.
A `comparison` round-trips as a `comparison`, never as its expansion.

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
- **The `: Num` slot is a sort position**, not decoration. It admits `Num`,
  `Str`, or any sort §4 declares, over the same vocabulary the `sort` block
  names, so the many-sorted Σ and the measurand table share one spelling.
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
    Bridge conclusions are exactly 4-ary; a bridge conclusion carrying a
    further parameter, such as an evaluation setting, is not supported.
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
  Haskell elaborator checks against it.
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

This refines the `"premises" "=" "[" [ apat { "," apat } ] "]"` fragment of §4's
`ruleDecl`; the rest of `ruleDecl` is as §4 states.

```
rule beats_baseline(S, B, Q, D, Sv, Bv)
  mode     = defeasible
  premises = [ cmp:     num_lt(Bv, Sv),
               binding: comparison_setup(S, B, Q, D, Sv, Bv) ]
  …
```

- Labels are **optional**, per premise. An unlabelled premise is cited by index
  only.
- **Policy well-formedness**, checked at declaration time: a rule's premise labels
  must be **disjoint from that rule's question ids**, and `rule` and `leaf` are
  **reserved from the premise-label namespace** (§1.3 already reserves them from
  the question-id namespace) — otherwise `a2.leaf.leaf` parses two ways. Both
  namespaces are policy-declared, so a collision is statically detectable and is
  **rejected at declaration time**, not discovered at an attack site.
- Duplicate labels within one rule are an error, for the same reason.
- Labels **never enter `Unit`**: `cmp` and `0` resolve to the same
  `StepPremise 0`, and the rule's compiled form is the same with or without
  labels.

### B.5 Attack-path name segments

§7 (named step segments) describes the presentation AST this subsection relies
on.

- A dotted segment of a position suffix (§7) that is a **decimal integer** is a
  `StepIndex`; **otherwise** it is a `StepName`, which the elaborator resolves
  against the target rule to **either** a premise label (B.4) **or** a question id
  — at most one of the two, guaranteed by B.4's disjointness requirement.
- Integers resolve directly to `StepPremise` and question ids to `StepQuestion`.
  §7's terminal `rule`/`leaf` marker rule applies to every spelling.
- Both spellings elaborate to the **same `Position`**, and each **round-trips in
  the spelling it was written in** — which is why the presentation AST carries
  `SurfaceStep` rather than reconstructing a spelling at print time.
- All `comparison` blocks expand before any attack path resolves, so an
  `undermine` targeting a generated argument (or a label inside one) resolves
  against the post-expansion argument set.
- **Index basis.** Attack-path integers, `(prem i)` certificate slots, and
  premise-label resolution are all **0-based**. 1-based indices appear only in
  human-facing error text (`resolvePremises` zips `[1..]`) and are converted
  at the message boundary — never in a generated certificate or a resolved `Step`.

### B.6 `nl` interpolation

```
nlString  ::= '"' { nlChar | directive | "{{" | "}}" } '"'
nlChar    ::= any-char-except '"', newline, "{", "}"
directive ::= "{" "cell" leafId "}"
```

This production covers the `{cell …}` directive. Appendix C.5 gives the
complete directive grammar, which adds one-token value references and permits
inline spaces or tabs around directive tokens, retained for round-tripping. The
cell lookup and `renderDecimal` semantics below apply to both.

```
claim c1
  nl = "sys_new outperforms sys_base on ImageNet-val accuracy ({cell e2} vs {cell e1})"
```

- **The lexical contract for braces.** Every claim-form `nl` uses `nlString`:
  both §3's ordinary `claim` and B.3's nested `claims` block. Inside `nl`, `{{`
  and `}}` denote literal braces — the f-string / `format!` convention this
  surface's Python-literate audience already knows — and **any other `{` must
  open a recognized directive**: `{cell <leafId>}` or a one-token value
  reference (C.5).
  Anything else is a **located error naming the claim**.
  This is strict rather than lenient on purpose: if `{cel e2}` (a typo) silently
  stayed literal text, a number the author believed was auto-synced would be
  frozen prose — the exact silent prose↔formal staleness this feature exists to
  kill.
- `{cell e2}` resolves via `premiseCell` on leaf `e2` — the same helper `ord@1`
  and the `comparison` form use — and is rendered back through `renderDecimal`.
  No value binding is required.
- Interpolating a **cell** is the *stronger* form for the prose↔formal binding
  audit: a number quoted in prose is then guaranteed to equal the number the cited
  evidence leaf actually carries, sourced from the leaf itself. Interpolating a
  `let` would only guarantee agreement with a parallel declaration, which could
  itself be wrong. A value reference such as `{acc_new}` (C.5) is an
  **additional** interpolation source; it does not replace `{cell e2}`.
- **Preconditions and errors:** the named leaf must exist and must satisfy the
  premise-cell obligation (exactly one numeric literal); failure is a **located
  source error naming the leaf**.
- **Round-tripping.** Directives and `{{`/`}}` escapes round-trip **raw** through
  the printer and are never expanded there. Interpolation happens in the
  elaborator, so the resulting `nl` is a plain `String` before anything downstream
  sees it.

### B.7 Comparison vocabulary

The comparison forms use these reserved words from §1.4's vocabulary block,
which is the single `toString`/`parse` table:

```
measurand  comparison  comparison-scheme  recheck  bridge  result  baseline
relation  claims  on  where  cell
higher-is-better  lower-is-better  strictly-better  at-least-as-good
```

Closed tag enumerations of the comparison forms (surface ↔ presentation AST):

| Field | Surface spelling | Presentation AST |
| --- | --- | --- |
| measurand polarity | `higher-is-better` / `lower-is-better` | `Polarity` `HigherIsBetter` / `LowerIsBetter` |
| comparison relation | `strictly-better` / `at-least-as-good` | `Relation` `StrictlyBetter` / `AtLeastAsGood` |

Neither reaches `Unit`; both are resolved away during expansion.

`test/SyntaxSpec.hs`'s `reservedWords` list mirrors §1.4 and must be kept in
sync with it. If it is not, the round-trip generator will emit identifiers that
collide with keywords and the property will fail for a reason that has nothing
to do with the grammar.


---

## Appendix C — Value bindings (`lara-syntax@0.4`)

This appendix specifies a presentation-only table of named ground terms and a
one-token `nl` interpolation form. Neither affects the core, `Unit`, the
`.core.sexp` door, the JSON/wire codecs, checker judgments, strict backends,
scientific claims, or verdicts.

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
prints one blank line before declarations when the table is non-empty; a
program with an empty table prints neither. `let` is listed in §1.4.

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
`ComparisonClaim.ccNlRaw`. Thus the C.1 example expands to the prose a
hand-written literal would give:

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

### C.6 Opaque certificate boundary

Value substitution operates on `Term` fields in the presentation AST. It never
enters `Cert`: the certificate payload remains the native opaque S-expression
owned and decoded only by its named backend (Appendix A.1). Symbolic
certificate slots such as `(prem e1)` are a separate layer above the opaque
payload (Appendix E), so the value pass never inspects backend syntax.

Value bindings also do not rename the named premise references of the inferred
form (Appendix D); `InferTheta` keeps its `ArgRef` values (C.4).

## Appendix D — Plain-argument theta inference (`lara-syntax@0.5`)

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
instantiation — explicit `r(g1,…,gn)` or inferred `r from [...]` — a hole is
authored and printed as `open q`, stored as `ObligationId q` (Appendix F.3).
§3 leaves `dischargeLine`/`openLine` order free
and A.1 lets `assurance` fold in anywhere; the canonical printer picks one order
— discharges, then opens, then assurance. For inferred arguments it prints the
rule, named references, discharges, opens, and assurance.

A bare `leaf(…)` support term instantiates no rule, so `discharge`, `open`, and
`assurance` lines are located parse errors there (Appendix F.2).

One identifier per hole suffices because §6.1 reads a hole's `ObligationId`
*as* the question it leaves open (`holeNames` in `Lara.SupportTerm`, Lean
`H : List QuestionId`), so the stored id names the question actually in force.
The printer emits every `open` line; omitting them would break result 12
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

## Appendix E — Named certificate premise slots (`lara-syntax@0.6`)

This appendix specifies a symbolic spelling for the premise-slot references
inside schema'd certificate payloads (E.1), lowered to the canonical numeric
slots at elaboration. It needs no lexer or parser rule and does not affect the
core, `Unit`, the `.core.sexp` door, the JSON/wire codecs, checker judgments,
strict backends, or replay identity.

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
lowered. Each supported backend exports one flat schema per certificate shape
— head keyword, arity, 0-based reference positions; `insp@1` has two, told
apart by head and arity — and the closed aggregate table lives in
`Lara.Elaborate.CertSlots`; the elaborator learns no other backend grammar:

| backend | head | arity | reference positions | untouched positions |
| --- | --- | --- | --- | --- |
| `ord@1` | `ordcmp` | 2 | 0, 1 | — |
| `ra@1` | `radrop` | 3 | 0, 1 | 2 (the `frac` witness) |
| `insp@1` | `inspect` | 1 | 0 | — |
| `insp@1` | `inspectdiff` | 2 | 0, 1 | — |

The concrete syntax needs no new rule: the wire S-expression sub-grammar
admits an identifier atom, and the printer prints the stored payload verbatim,
so the surface AST keeps the authored spelling and `parse ∘ print = id` holds. Lowering happens only at elaboration, *after* premise resolution, at
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

A symbolic name resolves in the Appendix D reference namespace —
declared leaves ∪ prior arguments, exactly the scope an inferred θ reference
sees (Appendix D.1): "prior" means already elaborated earlier in declaration
order, and a later argument is never a valid reference. Appendix G.2 adds the
citing rule's declared premise labels as a third class. A name that matches
both a declared leaf and a prior argument is a **hard error**, never silently
one of them. The inferred-θ resolver (D.3) and the discharge resolver (F.4)
apply the same collision policy, so all three argument-body reference
positions agree.

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
  cites a numeric slot or, when the rule labels the intended slot, that
  premise label (Appendix G.4).

*Representation rule:* locating matches whatever representation the author's
spelling actually put in the resolved premise sequence. A prior-argument
citation locates both the argument's elaborated term (what `by r from […]`
premise resolution stores) and the bare `SLeaf` spelling of its identifier
(what an authored premise list would store); the explicit/inferred twins
therefore lower identically, with no spurious not-a-premise error on one side.

Mixed symbolic and numeric references are legal: each reference position
lowers independently, so `(radrop (prem e4) (prem 1) (frac 119 500))` is
well-formed if `e4` resolves to slot 0's premise.

### E.4 Pass-through, the dead-wire rule, and the rejection site (D6)

Payloads stay backend-owned. Unknown backend/version payloads, non-`(prem …)`
nodes at reference positions, canonical numeric slots, and every
non-reference position are left untouched and reach the backend as
authored. This includes symbolic-looking `(prem s)` nodes at a matched schema's
non-reference positions, whether direct or nested: the schema does not declare
them as premise references, so the backend owns their meaning and rejection.
A backend with no declared schema (`nd@1`, E.7) always passes through
byte-identical. A head-keyword or arity mismatch under a *schema'd* backend
also passes through unless the payload contains a symbolic `(prem s)`
anywhere. No declared positions exist under a mismatch, so such a spelling
cannot be lowered; it fails at elaboration as a schema mismatch. Detection is
a generic sub-tree scan, and the elaborator still learns no backend grammar.

Consequences: a payload with no symbolic names lowers to itself (byte
preservation is the E.1 Lean theorem), and every backend rejection path is
preserved. The one exception is deliberate: spelling-level mistakes at a
matched schema's reference positions fail **earlier**, at elaboration rather
than at certificate replay (R13):
malformed numerals (`(prem 007)`, `(prem -1)`), name typos (`(prem e44)`), and
symbolic names inside schema-mismatched payloads (`(ordcmp (prem e4))`, one
argument short) fail before the checker (`docs/rejection-surface.md` §1.2 and
the R13 row). Acceptance is the same as for the numeric spelling.

### E.5 Stable error messages

The `CertSlot*` diagnostic families and their exact templates are listed in
Appendix G.5, which covers the leaf and prior-argument names of this appendix
together with the premise labels of Appendix G.

### E.6 Recursion semantics (D8)

Lowering applies at **every** rule-application depth, resolving each declared
reference position against that node's own resolved premise list, with
diagnostics attributed to the enclosing argument's id. A nested certificate
on a premise instance therefore lowers against the nested instance's premises,
not the enclosing argument's. Symbolic-looking nodes outside a matched
schema's declared reference positions remain backend-owned as specified in
E.4.
The surface grammar cannot author a nested assurance — a parsed rule
application carries no authored premise list, and `assurance` attaches only to
the `arg` block's own rule application — so the recursive case is reachable
only from a hand-built AST. `test/CertSlotsSpec.hs` pins the recursive
behavior at the AST level through the real elaborator entry point.

### E.7 `nd@1` has no slot schema (D1, D3)

`nd@1` declares no slot schema, so its kernel payloads pass through this pass
byte-identical and keep numeric `hyp` indices. `ord@1`, `ra@1` and `insp@1`
payloads are single flat head applications with premise references at fixed
argument positions, where a name is a stable notion. `nd@1` payloads are
recursive de Bruijn proof terms: `hyp i` shifts under `lam` binders and covers
premise slots and theory entries by offset, so "the premise named `e4`" is not
a fixed payload position. Named `nd@1` authoring is a separate presentation
form with its own binder discipline and lowering arithmetic (Appendix H).

## Appendix F — Surface strictness (`lara-syntax@0.7`)

### F.1 Scope

Three restrictions, all enforcing one invariant: **every
authored surface token must affect the semantic object or trigger an explicit
error.** A token the parser reads and then discards is a lie to the author, who
reasonably concludes the checker saw what they wrote.

- **F.2** — `discharge` and `open` under a bare `leaf(…)` support term
  are parse errors, not silently dropped lines.
- **F.3** — a hole is spelled `open q`. The two-identifier
  `open q as o` form is a located parse error carrying its repair, and `as`
  is not a keyword.
- **F.4** — a `discharge q with x` whose `x` names both a declared leaf
  and a prior argument is a hard elaboration error, not a silent preference for
  the leaf.

This appendix adds **no productions**; every clause narrows what the parser or
elaborator accepts. None of the restrictions reaches the kernel: the AST, the
wire, `.core.sexp`, checker judgments, strict backends and replay are
unaffected. F.4's check sits in the validated-not-verified elaborator
(`ara/logic/solution/constraints.md`), outside the mechanized checker boundary
described in [implementation](implementation.md).

No compatibility alias exists. Each of the three cases has the same shape — the
surface would accept an author's token and then not mean it — and an alias that
kept accepting the rejected spelling would preserve exactly that misreading
while doubling the spellings a reader must know.

### F.2 `discharge`/`open` on a bare leaf are parse errors

Appendix A.1 rules that `assurance` on a bare `leaf(…)` support term is
a parse error, "the checker has no rule to check it against, and silently
dropping it would mislead the author". That reasoning is not specific to
`assurance`. A `discharge` or an `open` line answers or defers a *critical
question of a rule*; a bare leaf instantiates no rule, so it declares no
questions, and there is nothing for either line to attach to. Dropping the
line silently would let an author who writes `discharge q with e2` under
`leaf(e1)` believe `q` was answered.

A.1's ruling therefore covers both siblings, with the same wording shape:

```text
discharge requires a rule application, not a bare leaf
open requires a rule application, not a bare leaf
assurance requires a rule application, not a bare leaf   -- A.1, unchanged
```

Each is a located `ParseError` (spec §10.1 R14) positioned at the offending
keyword, so the diagnostic points at the line the author must delete or move.

**The ruling does not rest on a parser-side convention.** `addArgDischarge`,
`addArgHole` and `setArgAssurance` in `Lara.Syntax` each return
`Either String ArgInstantiation`, with **one equation per `ArgInstantiation`
shape and no catch-all**; `argBody` turns a `Left` into the located error above.
The guarantee therefore lives in the type: a caller that reaches a helper by
another path (a bundle lowerer, a test builder, a reordered `argBody`) still
cannot drop the line, because the impossible case has no equation that can
quietly succeed.

The error is a parse error rather than an elaboration error because the line
sits in a position the grammar gives no meaning, and §1 places surface
well-formedness in `Lara.Syntax`; the presentation AST therefore cannot
represent a state the surface cannot mean.

### F.3 The sole hole spelling is `open q`

```text
openLine ::= "open" ident                 -- open q   (explicit hole)
```

**A hole has one identity.** Spec §6.1 question-accounting reads a hole *as the
question it leaves open*: `holeNames` in `Lara.SupportTerm` maps each stored
`ObligationId` to the `QuestionId` of the same text (Lean `H : List QuestionId`;
the Lean driver decodes `holes` straight to `QuestionId`), and `D ⊎ H =
questions(r)` is then checked against the rule's declared questions. No
reporting path — verdict JSON, `Lara.Reporting`, the located-obligation output
of an E2-style gap — consumes an obligation name independent of that question
name, so a second identifier could only be redundant (when equal) or
misleading (when divergent). The parser stores `ObligationId q` from the single
authored identifier, which is exactly the name §6.1 uses.

`open q as q` and `open q as o` are rejected identically. There is no carve-out
for the equal spelling, because it is still a second way to say one thing:

```text
lara-syntax@0.7 uses 'open q'; remove 'as …'
```

located at the `as` token, on `open q as q` and `open q as o` alike, and the
message carries the repair rather than only the complaint.

**`as` is an ordinary identifier.** It has no syntactic role, so it is not in
§1.4: a leaf, argument, rule, question, or predicate may be named `as`, and
`test/SyntaxSpec.hs` (`unit_asIsAnOrdinaryIdentifier`) pins that. The
reserved-word list the round-trip generator consults (`test/SyntaxSpec.hs`)
mirrors §1.4.

The retained `ObligationId` newtype is **not** collapsed into `QuestionId`. It
is the spec §2 obligation name class, and the symbolic-core discipline keeps
distinct namespaces in distinct types (CLAUDE.md); only the *surface* cannot
name the two independently. The single sanctioned bridge is exactly
`open q → ObligationId q → QuestionId q`, confined to
`holeNames`, and `src/Lara/SupportTerm.hs` documents it there.

### F.4 Discharge collision policy

`discharge q with x` resolves `x` in the Appendix D reference namespace:
declared leaves ∪ prior arguments (Appendix D.1). It applies the same collision
policy as Appendix D's inferred-θ references (`ThetaReferenceAmbiguous`) and
Appendix E.2's certificate premise slots (`CertSlotAmbiguous`), so one argument
body gives one answer whichever line the author is writing. One
`refMatches`-based `resolveDischargeRef` serves **both** discharge payload
forms — the explicit one (where the parser spells the target
`SLeaf (LeafId ref)`) and the inferred one (where it arrives as `ArgRef ref`) —
so the two surfaces cannot drift apart:

| declared leaf named `x` | prior argument named `x` | result |
| --- | --- | --- |
| yes | no | the leaf's `SLeaf` |
| no | yes | that argument's elaborated support term |
| yes | yes | **`AmbiguousDischarge`** |
| no | no | `UnresolvedDischarge` |

"Prior" keeps D.1's meaning: strictly earlier in declaration order, i.e.
whatever `elabOne` has accumulated when this argument is elaborated. A discharge
naming a *later* argument is therefore `UnresolvedDischarge`, not a forward
reference — the same scope rule the θ references and the E.2 premise-slot names
already obey.

Diagnostics (`Lara.Elaborate.Error`, the D.3 `ThetaReference*` style, attributed
to the enclosing `arg`):

```text
arg 'A': discharge of 'q' names 'x', which is neither a declared leaf nor a prior argument
arg 'A': discharge of 'q' names 'x', which is ambiguous between a declared leaf and a prior argument
```

The families are `AmbiguousDischarge ArgId QuestionId ArgRef` and
`UnresolvedDischarge ArgId QuestionId ArgRef`. The source identifier is carried
in the type the namespace is defined over and is unwrapped in exactly one
place, the renderer, as in every other reference diagnostic of this family.

A collision is an error rather than a documented leaf preference because a
program whose meaning turns on a shadowing rule is not readable at the
Python-literate baseline this surface targets; the author renames in one edit.

### F.5 Effect on accepted sources

The three restrictions only reject. They change the meaning of no accepted
source, so no derived `.core.sexp`, `expected.json`, verdict, or measurement
byte depends on them.

## Appendix G — Premise-label certificate citation (`lara-syntax@0.8`)

### G.1 Scope

A certificate premise reference may cite the **premise label** the citing rule
declares for that slot (Appendix B.4), alongside the leaf and prior-argument
names of Appendix E. Like Appendix E, this needs no lexer or parser rule: the
spelling `(prem s)` is the same, and only the set of names `s` may carry is
larger.

Nothing here reaches the kernel: the core, `Lara.AST`, the wire, `.core.sexp`,
checker judgments, strict backends and replay are unaffected. A label citation
and its numeric twin produce byte-identical `Cert` payloads, byte-identical
encoded `Unit`s, and byte-identical verdicts; `examples/S7/` authors the label
spelling and its committed `.core.sexp` golden is the standing byte-identity
witness (G.7).

**Why labels are their own name class.** Appendix E resolves a name by locating
the *referent's term* in the resolved premise sequence, so when one leaf feeds
two premises the leaf name occupies both slots (E.3's third bullet). A label
names the **slot** in the rule that declares it, not the term, so it stays
unambiguous however the instance is filled.

### G.2 The three-class namespace and resolution rule

A symbolic `(prem s)` resolves in **three** classes:

1. the **premise labels declared by the rule of the instance whose certificate
   this is** — the citing rule, never an enclosing or nested one;
2. the **declared leaves**;
3. the **prior arguments** (already elaborated, in declaration order).

Class 1 is answered by `premiseLabelIndex`, which maps a label to its 0-based
slot directly and needs no locating step. Classes 2 and 3 are Appendix E's
namespace (`refMatches`) and keep E.3's locating rule verbatim: the referent's
term is located in the resolved premise sequence by term equality, with the
representation rule of E.3 intact.

Resolution reads as one case split, in this order:

- label hit, and the name is in **neither** other class → that label's slot,
  provided the slot exists in this instance's premise list. It does not exist
  only when an authored premise list is shorter than the rule's premise
  vector, which is a not-a-premise error.
- label hit, and the name is **also** a declared leaf or prior argument →
  hard error (G.3), whatever the other class would have resolved to.
- no label hit → Appendix E's resolution, with all of E.2's and E.3's verdicts.

Labels are optional (`rulePremiseLabels :: [Maybe PremiseLabel]`, `[]` when the
rule labels nothing). For a rule that labels nothing, class 1 is empty and the
resolver behaves exactly as Appendix E's; `test/CertSlotsSpec.hs` carries an
unlabelled control rule pinning both its resolving and its failing path.

The class is **per rule, not per policy**: a label of rule `r` is not a name
that rule `r'` knows, and a nested instance's certificate resolves against its
own rule's labels, never the enclosing instance's (E.6, extended in G.6).

### G.3 Collision policy: cross-class collision is a hard error

A name carried by both class 1 and class 2 or 3 is `CertSlotLabelAmbiguous`,
never silently either class. This is E.2's and F.4's one collision policy
applied to the new class, and it holds **even when the two classes would
resolve to the same slot**.

A carve-out for agreeing referents would make the policy conditional on
something not visible in the citing line: whether `(prem base)` is ambiguous
would depend on which slot a leaf elsewhere in the artifact happens to fill.

### G.4 What labels resolve that names could not

E.3's multi-slot case — the source name occupies two or more slots — has two
exits: a numeric slot or the label of the intended slot. The label is the
better one, because it says which slot was meant in the rule's own vocabulary
rather than by position.

When every slot occupied by the ambiguous source name has its own usable
premise label, the `CertSlotMultiSlot` message names both repairs: cite a
numeric slot or that rule's label for the intended slot. A label is usable only
when its spelling does not collide with a declared leaf or prior argument.
`examples/S7/` argument `a2` is the worked case: one leaf fills both premise
slots of a two-premise rule, and only `(prem left)`/`(prem right)` resolve
there. An unrelated, partially declared, or colliding label does not advertise
a nonexistent repair.

Labels are not a *universal* namespace. They are optional, so a rule that
declares none is cited exactly as in Appendix E, and the multi-slot case then
has only the numeric exit. A policy author opens the label exit by labelling
the rule's premises.

### G.5 Stable error messages

Seven diagnostic families — `CertSlotUnresolved`, `CertSlotAmbiguous`,
`CertSlotLabelAmbiguous`, `CertSlotNotAPremise`, `CertSlotMultiSlot`,
`CertSlotNonCanonicalNumeral`, and `CertSlotSchemaMismatch` — are located
`ElabError`s in the `ThetaReference*` style (D.3), attributed to the enclosing
`arg` block. This is the normative template list for Appendix E and this
appendix. `A` is the enclosing argument, `B` the
backend spelling `name@version`, `N` the authored reference spelling, `R` the
citing rule's id, and `I`/`J` are 0-based slots:

```text
arg 'A': certificate 'B' premise reference 'N' names neither a premise label of rule 'R', a declared leaf, nor a prior argument
arg 'A': certificate 'B' premise reference 'N' is ambiguous between a declared leaf and a prior argument
arg 'A': certificate 'B' premise reference 'N' is ambiguous between rule 'R' premise label and a declared leaf or prior argument
arg 'A': certificate 'B' premise reference 'N' does not resolve to any of this argument's premise slots
arg 'A': certificate 'B' premise reference 'N' occupies premise slots I and J; cite a numeric slot or the rule's premise label for the slot you mean
arg 'A': certificate 'B' premise reference 'N' occupies premise slots I and J; cite a numeric slot
arg 'A': certificate 'B' premise reference 'N' is not a canonical slot numeral (use unsigned decimal with no leading zeros); write the canonical numeral or a source name
arg 'A': certificate 'B' payload does not match the backend's premise-reference schema but contains symbolic premise reference 'N'
```

The first and third templates name the citing rule,
because "a premise label" is only actionable once the author knows whose labels
were consulted — the same reason `ThetaReference*` messages name their rule.
The labelled multi-slot template applies exactly when every slot in the
resolver's complete matching-slot set has a `Just` at the corresponding
position in `rulePremiseLabels` and each label has no declared-leaf or
prior-argument collision. Otherwise the following numeric-only template
applies. Thus the advice is actionable for whichever matching slot the author
intended. `test/CertSlotsSpec.hs` pins all seven families, both multi-slot
branches, the partial-label case, a three-match case, and a shadowed-label case;
the production CLI preserves the rendered diagnostic on stderr.

### G.6 Recursion and mechanization

E.6's recursion semantics hold verbatim, with the citing rule's labels part
of what "that node's own scope" means: a nested certificate resolves against
the nested instance's premise list *and* the nested rule's labels. A label of
the enclosing rule is unresolved inside a nested certificate, and vice versa.
`test/CertSlotsSpec.hs` pins both directions at the AST level, because a leaked
label would be the worst kind of silent success — it names a slot index both
instances have.

`lean/Lara/CertSlots.lean` parameterizes the
mechanized pass over an *abstract* resolver `ρ : String → Option Nat` and an
abstract classifier `startsSourceIdentifier : String → Bool`, and both
theorems — `lower_id_of_no_symbolic` (byte preservation on every payload the
frozen corpus can contain) and `lower_eq_numeric_subst` (a successful lowering
is exactly the declarative substitution) — are universally quantified over `ρ`.
The label-extended resolver is one more instance of `ρ`, so both theorems cover
it.

The resolver itself lives in the validated-not-verified elaborator
(`ara/logic/solution/constraints.md`), outside the mechanized checker boundary
described in [implementation](implementation.md). The Lean mirror carries the
lowering math, and the Haskell property tests carry conformance.

### G.7 Worked example

`examples/S7/` (`example.lara`, `ord-labeled-v1.policy.lara`, and the two
generated files) is the worked label citation. Both of its certificates lower
to `(ordcmp (prem 0) (prem 1))`, the bytes its numeric twin produces;
`test/WorkedExamplesSpec.hs`'s freshness property re-proves that on every run,
and `scripts/differential.sh` confirms both drivers agree on the anchor.

## Appendix H — Named `nd@1` proof terms (`lara-syntax@0.9`)

### H.1 Scope and the two modes

The registered `nd@1` backend keeps its closed, numeric de Bruijn grammar;
this appendix specifies a presentation form that the untrusted elaborator
lowers before replay. The grammars are deliberately
separate:

```text
formula       ::= "false"
                | "(" "atom" KEY ")"
                | "(" "imp" formula formula ")"

kernelCert    ::= "(" "hyp" canonicalNat ")"
                | "(" "lam" formula kernelCert ")"
                | "(" "app" kernelCert kernelCert ")"
                | "(" "abort" formula kernelCert ")"

namedCert     ::= "(" "hyp" sourceName ")"             -- enclosing named binder
                | "(" "prem" premRef ")"               -- premise slot
                | "(" "thy" canonicalNat ")"           -- theory entry
                | "(" "lam" sourceName formula namedCert ")" -- named binder
                | "(" "lam" formula namedCert ")"       -- anonymous kernel binder
                | "(" "app" namedCert namedCert ")"
                | "(" "abort" formula namedCert ")"

premRef       ::= canonicalNat | sourceName
sourceName    ::= S-expression atom whose decoded string is nonempty and
                  whose first character satisfies §1.3 `isIdentStart`
canonicalNat  ::= "0" | nonZeroDigit { digit }
```

`formula` is the frozen backend annotation grammar. In particular an atom is
`(atom KEY)`, never a bare key. Producing `KEY` from a source proposition
is an encoding feature, not reference lowering; Appendix I's `(prop TEXT)`
presentation formula provides it.

`sourceName` deliberately uses the shipped source-name classifier, not the
complete concrete-syntax `ident` production. The first decoded character must
be a Unicode letter or `_`; the entire decoded S-expression atom is then the
name. Consequently punctuation after that first character can survive the
S-expression codec and remains part of binder lookup and comparison. This is
the same first-character boundary used by named certificate-slot lowering.

**D9 — kernel/named mode separation.** A payload is in exactly one mode. If
the D7 marker scan in H.4 finds no marker,
the payload is **kernel mode** and passes through structure-identically for the
backend to decode and replay. If it finds any marker, the whole payload is
**named mode** and is subject to this appendix. A canonical numeric `(hyp N)`
inside named mode is therefore `CertNdKernelIndex`, not a second spelling. Raw
`hyp` indices are excluded from named terms because `(prem N)` shifts under
binders while `(hyp N)` would not, which would give one term two
context-sensitive shift regimes.

Nothing in this appendix affects the core, `Lara.AST`, the wire,
`.core.sexp`, a checker judgment, or replay.

Named mode gives binders, premises, and theory offsets one explicit lowering
discipline, which closes silent index misbinding. Formula annotations are
written either as opaque `(atom KEY)` values or as source propositions
(Appendix I).

### H.2 Namespaces and binder discipline

The three reference namespaces are separated by their heads (D1): `(hyp x)`
consults only enclosing named binders; `(prem s)` consults only premise slots;
and `(thy N)` consults only theory entries. They never compete for one syntactic
position, so recursive proof terms need no global shadowing preference between
them.

A named binder is spelled `(lam x FORMULA CERT)`. Its `x` must be a
`sourceName`: an S-expression atom whose first decoded character satisfies
`isIdentStart`. Numeral and structured binders are rejected, but the remainder
of the atom is not re-lexed as a complete §1.3 `ident`; it stays part of the
name verbatim. The kernel three-field spelling `(lam FORMULA CERT)` remains
legal inside named mode as an anonymous binder and still contributes one level
to de Bruijn depth.

Local binder shadowing is forbidden (D3): a nested named `lam` may not reuse an
enclosing binder's name, so a `(hyp x)` keeps one referent. With shadowing, the
same `(hyp x)` would silently change its referent after crossing the inner
binder. A named binder also may not use a name that the citing instance's
shared resolver successfully resolves to a citable premise (D10). Only a
successful resolution reserves the name: unresolved, ambiguous, and
not-a-premise resolver failures leave it available, so an irrelevant
program-global name does not poison the binder namespace.

**D2 — premise resolver reuse.** A `(prem s)` whose `s` is a `sourceName` uses
Appendix G's three-class resolver—citing-rule premise labels, declared leaves,
and prior arguments—with its hard collision policy and exact `CertSlot*` errors
unchanged. D1 keeps that premise namespace under the `prem` head rather than
letting it compete with binder lookup.

**D5 — theory references stay numeric-only.** `(thy N)` accepts only a
canonical natural because theory entries have no source names. Separately,
**D6 — numeric premises are slot-stable and range-checked.** A canonical
numeric `(prem N)` is a legal premise spelling, and D6 owns its range guard;
D5 does not govern numeric premises.

### H.3 Lowering arithmetic

Let `depth` be the count of all enclosing `lam` binders, named or anonymous;
let `nPrem` be the citing instance's premise count; and let `slot` be the
resolved zero-based premise slot. Lowering is:

```text
(hyp x)     -> (hyp binderIndex(x))
(prem s)    -> (hyp (depth + slot(s)))
(thy N)     -> (hyp (depth + nPrem + N))
(lam x F C) -> (lam F lower(C))
```

Thus the same `(prem e1)` lowers to `(hyp 1)` inside one binder and `(hyp 0)`
outside it. A numeric `(prem N)` is slot-stable and is checked before the theory
offset is applied: `N >= nPrem` is `CertNdPremOutOfRange`, never a silent slide
into theory entry `N - nPrem`. Theory indices have no presentation-side upper
bound; the backend checks them against the selected theory table during replay.

### H.4 Exact D7 boundary and rejection site

The same marker vocabulary drives two leftmost-outermost scans. The first
selects named mode. Before lowering, a traversal-aware scan checks positions
that the lowering grammar treats as opaque. The markers are exactly:

1. a two-field `(prem ATOM)` node;
2. a two-field `(thy ATOM)` node;
3. a four-element `(lam BINDER FORMULA CERT)` node; and
4. a two-field `(hyp a)` whose decoded atom `a` is nonempty and whose first
   character satisfies `isIdentStart`.

Appendix I.2 adds a fifth marker, a two-field `(prop ATOM)` node.

Everything with none of those markers is kernel mode and passes through
unchanged—valid kernel certificates, marker-free junk such as `(foo bar)`, and
even noncanonical `(hyp 007)` alike. The backend continues to own their decode
or replay result, including R13. Once any marker selects named mode, known proof
constructors are recursively lowered. A named marker in an opaque formula
position or an unknown subtree is `CertNdResidualNamed` at the source boundary,
even when lowering a traversed node would fail for another reason. Consequently
only payloads that contain a marker fail as a located elaboration error rather
than at backend R13; marker-free payloads keep their backend behavior. A raw `.sexp` has no presentation lowering and remains backend-owned.

### H.5 Stable source-boundary diagnostics

Eight `CertNd*` templates are normative. `A` is the enclosing argument, `B` is
the backend spelling `name@version`, `N` is the offending authored spelling,
`I` is an authored/resolved slot, and `J` is the number of premise slots. For a
non-atom `lam` binder, `N` is its canonical S-expression rendering:

```text
arg 'A': certificate 'B' reference 'N' names no enclosing lam binder
arg 'A': certificate 'B' lam binder 'N' shadows an enclosing binder; rename one
arg 'A': certificate 'B' lam binder 'N' is also a citable premise name of this instance; rename the binder
arg 'A': certificate 'B' lam binder 'N' is not a source identifier
arg 'A': certificate 'B' index 'N' is not a canonical index (use unsigned decimal with no leading zeros)
arg 'A': certificate 'B' kernel index 'N' appears in a named-form payload; cite a binder by name, a premise with (prem ...), or a theory entry with (thy ...)
arg 'A': certificate 'B' premise reference 'N' names slot I but this argument has only J premise slot(s)
arg 'A': certificate 'B' named spelling 'N' sits where the nd@1 grammar gives it no meaning
```

These are, in order, `CertNdBinderUnbound`, `CertNdBinderShadowed`,
`CertNdBinderShadowsPremise`, `CertNdMalformedBinder`,
`CertNdNonCanonicalIndex`, `CertNdKernelIndex`, `CertNdPremOutOfRange`, and
`CertNdResidualNamed`. A `(prem s)` resolver failure does **not** acquire a
parallel `CertNd` rendering: it reuses the applicable `CertSlot*` family and
the Appendix G.5 template verbatim.

Lowering is one-way. If lowering succeeds but `nd@1` later rejects at R13, its
backend diagnostic describes the lowered de Bruijn term. The `.lara` door maps
two parts of that term back to the authored spelling:

- **The premise list.** An R13 renders the slot → source mapping of the
  refused instance, in the authored spelling (`docs/rejection-surface.md`
  §1.5).
- **The formula annotations.** The same R13 renders the authored spelling of
  every atom the reason names, drawn from the `(prop TEXT)` annotations *and*
  the declared leaf propositions, because a mismatch names one of each
  (`docs/rejection-surface.md` §1.6).

Binder names are not mapped back. A `hyp i` index is relative to the local
binder context at the failure site *inside* the adapter, which reports through
a flat string, so no sound recovery exists from outside it; recovering binder
names would require a structured rejection at the registered-backend seam.
This limit affects only the user-facing message, not replay.

### H.6 Mechanization, witness, and trust boundary

The Lean mirror proves two named results:
`Lara.NDNamed.lowerNamed_id_of_kernel` (every encoded kernel certificate takes
the marker-free identity arm) and
`Lara.NDNamed.lowerNamed_eq_translation` (every well-formed named term lowers
to exactly the independently defined de Bruijn translation). Twelve executable,
axiom-free `#guard` vectors pin the successful and failing boundary shapes to
the Haskell tests. `examples/S8/` is the standing end-to-end byte-identity
witness: the named redex lowers to the numeric redex in its committed
`.core.sexp`, and freshness tests re-prove that equality.

The trust split remains explicit. `Lara.Elaborate.NDNamed` is Haskell
validated-not-verified boundary code: its classifier, resolver, traversal, and
execution are covered by properties and integration tests. The Lean mirror
proves the lowering mathematics over abstract classifier and resolver
parameters; it does **not** prove that the Haskell implementation executed that
function, nor verify the Haskell classifier or resolver. Named mode removes
silent index misbinding from premise and binder authoring; Appendix I covers
source-authored formula annotations.

## Appendix I — Source-authored `nd@1` formula annotations (`lara-syntax@0.10`)

### I.1 Scope

In a named `nd@1` proof term (Appendix H), the formula annotation of a `lam` or
`abort` may be a source proposition instead of an opaque `(atom KEY)` whose
`KEY` comes from out-of-band tooling. The presentation formula grammar for
named mode is:

```text
namedFormula ::= "false"
               | "(" "atom" KEY ")"                       -- opaque, unchanged
               | "(" "imp" namedFormula namedFormula ")"
               | "(" "prop" TEXT ")"                      -- NEW: source authored
```

`TEXT` is one S-expression atom — in practice a quoted string, since surface
propositions contain parentheses — whose decoded string is a **complete §2
`prop` production**, parsed by `Lara.Syntax.parseProp`. Annotation text shares
the proposition grammar and Unicode identifier rules used by `formal`, `leaf`,
and `theory` lines, but accepts whitespace only as trivia: `#` remains literal
and causes a complete-input parse failure instead of starting a line comment.
There is no second proposition grammar; `printProp` output is by construction a
legal annotation text. Because the surface `term` production has no string
literals, the spelling covers exactly the propositions the surface can already
declare.

The untrusted elaborator lowers `(prop TEXT)` through the shared
normalization/encoding path — `encodeAtomKey (nf p)`, precisely the backend's
`encode_ND` — and re-emits the frozen `(atom KEY)` node. The authored and the
hand-computed key spellings are therefore byte-equivalent by construction.
Nothing here affects the core, `Lara.AST`, the wire, `.core.sexp`, a checker
judgment, or replay.

### I.2 Extensions to Appendix H's boundary

- **Marker vocabulary (H.4).** A two-field `(prop ATOM)` node is the fifth
  D7 marker; any payload containing one is named mode, subject to D9's whole-
  payload discipline (in particular, a numeric kernel `(hyp N)` beside a
  `(prop TEXT)` is `CertNdKernelIndex`). Like `prem` and `thy`, only the exact
  two-field atom shape is a marker: a `prop` head of any other arity, or with
  a non-atom payload, is inert junk that the strict backend owns (R13).
- **Formula positions are traversed through `imp`.** The residual scan and the
  lowering both traverse `imp` nodes in formula positions to reach nested
  `prop` spellings, rebuilding byte-identically when none occur; `false`,
  `(atom KEY)`, and non-grammar formula subtrees still pass through unchanged.
  A *different* named marker in a formula position — for example `(prem s)`
  posing as a formula, or any marker inside an opaque formula subtree — stays
  `CertNdResidualNamed`, as does a `(prop _)` node sitting in a certificate
  position.
- **Rejection surface (H.5).** A ninth template, `CertNdFormulaMalformed`,
  fires when the annotation text is not a
  complete surface proposition (including trailing input):

  ```text
  arg 'A': certificate 'B' formula annotation 'N' is not a source proposition
  ```

  `N` is the decoded annotation text. As in H.4, only payloads carrying a
  marker fail at elaboration rather than at backend R13.
- **Σ is not consulted.** A lowered annotation is an opaque atom key to the
  checker, exactly as a hand-authored key is; it matters only up to equality
  with the premise/goal encodings during replay. A source-authored annotation
  therefore carries no signature obligation that the numeric spelling lacks.

### I.3 Mechanization and witness

The Lean mirror (`lean/Lara/NDNamed.lean`) abstracts the proposition encoder
as `encodeProp : String → Option String` — the composition of the surface
proposition parser with `encodeAtomKey ∘ nf` stays validated-not-verified
Haskell boundary code — and proves the named result
`Lara.NDNamed.lowerFormula_eq_translation` (every well-formed named formula
lowers to exactly the kernel wire image of its independent translation)
alongside the two Appendix H theorems, which are stated over the same
parameter. Nineteen executable `#guard` vectors pin the boundary, seven of
them for `prop`. On the Haskell side,
`prop_sourceFormulaMatchesEncoder` checks authored spellings against
`encode_ND` itself, `prop_parsePropRoundTrip` pins `parseProp ∘ printProp`,
and `examples/S8/`, which authors
`(app (lam h (prop "holds(safety_invariant, D)") (prem e1)) (prem e1))`, is the
end-to-end byte-identity witness against its committed numeric `.core.sexp`,
with no out-of-band command in its provenance.

R13 attribution for a lowered term follows H.5: the reason is phrased over the
numeric de Bruijn image with the encoded key, and the `.lara` door prints,
beneath it, the authored spelling of every atom the reason names
(`docs/rejection-surface.md` §1.6). The map is recovered from the retained
source `Program`, not threaded out of the elaborator, so it involves no core,
wire, `.core.sexp`, checker-judgment or replay component. It draws on **two**
sources, because a mismatch names one atom of each: the `(prop TEXT)`
annotations of the proof term, and the propositions of the declared leaves a
`(prem s)` cites. Binder names remain unmapped (H.5).

## Appendix J — Certified-evidence requests (`lara-syntax@0.11`)

### J.1 Which source fields does it define?

A leaf may carry one `extract` field immediately after `refs`. A policy may carry one `evidence-checkers` field among its policy declarations. Both contain embedded S-expressions decoded by `Lara.Evidence.Syntax`; they are presentation data, not fields in the core wire.

```text
leaf evidence : result(7)
  kind = certified
  provenance = checker(csv-row, 1)
  refs = [evidence/results.csv]
  extract = (csv-row 1 results
    (key "id" "run-a")
    (select ("score" decimal))
    (predicate result))

evidence-checkers = (checkers (csv-row 1) (json-pointer 1))
```

The object identifier `results` must resolve to a manifest entry whose path matches a leaf reference before its `#` fragment. The request's checker and version must match the provenance and the policy allowlist. Omission of the policy field means an empty allowlist; omission of a request on a certified leaf rejects at R8.

### J.2 What is the extraction-request grammar?

```text
extractionRequest ::= "(" "csv-row" version objectId
                        "(" "key" atom atom ")"
                        "(" "select" { csvSelector } ")"
                        "(" "predicate" atom ")" ")"
                    | "(" "json-pointer" version objectId
                        "(" "select" { jsonSelector } ")"
                        "(" "predicate" atom ")" ")"
csvSelector       ::= "(" atom ("decimal" | "text") ")"
jsonSelector      ::= "(" atom ("decimal" | "text" | "decimal-line") ")"
evidenceCheckers   ::= "(" "checkers" { "(" checker version ")" } ")"
checker            ::= "csv-row" | "json-pointer"
```

Here `atom` is a bare or quoted S-expression atom, not the source proposition grammar. `version` is a canonical natural number; the implemented registry accepts version `1`. `objectId` is an S-expression atom in the manifest's object namespace. Selector order determines output argument order, and each request accepts at most 256 selectors.

CSV selection requires exactly one row with the exact raw key. `decimal` decodes exact decimal or scientific notation and `text` preserves a string. JSON selectors use RFC 6901 pointers: `""` selects the root, `/` separates tokens, `~0` encodes `~`, and `~1` encodes `/`. Array indices must be canonical nonnegative integers. `decimal` selects a JSON number, `text` selects a JSON string, and `decimal-line` selects a string containing a decimal followed by exactly one LF. CSV does not accept `decimal-line`.

### J.3 Where do malformed or unsupported requests fail?

Duplicate request fields, duplicate allowlist fields or entries, unknown checker names or encodings, malformed selectors or pointers, and noncanonical version spellings are source parse errors (exit 2). A decoded but unsupported version, a noncertified leaf with an extraction request, or a mismatch among provenance, allowlist and manifest reference is an evidence-binding rejection at R8. The exact numeric and byte bounds live in [the evidence-admission design](evidence-admission-design.md#concrete-package-contract).

`lara check-ara ROOT [--policy FILE] [--out DIR]` supplies the captured package context needed to certify a leaf. Ordinary source commands, including `check`, `deps`, map and possible-world source loaders, reject certified declarations without that context. A decoded request alone does not grant assurance. Raw `.sexp` checking remains conditional on declared evidence.

### J.4 Which checks cover this surface extension?

The Haskell printer emits `extract` after `refs` and emits a policy allowlist only when nonempty. `Lara.Presentation` mirrors the request and allowlist types without adding fields to `Lara.Unit`. `make presentation-parity surface-conformance` checks the two representations; `make evidence-cli evidence-differential` exercises the real package command and the finite typed model separately. The model's proofs and its trusted byte-parser boundary are documented in [the evidence theory note](evidence-admission-design.md#what-successful-admission-proves).
