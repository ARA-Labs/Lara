# LARA surface grammar — frozen (`lara-syntax@0.9`)

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

The `@0.6` additions are specified in Appendix E: an `ord@1` or `ra@1`
certificate payload may cite a premise slot by source name (`(prem e4)`
instead of `(prem 0)`), and elaboration lowers the name to the canonical
numeric slot after premise resolution, so the wire `Unit` and `lara-core@0.2`
remain unchanged. The `@0.5` inferred-theta form (`Arg` carrying
`ArgInstantiation` with `ArgRef` references, exercised by the migrated A/S1
witnesses) remains specified in Appendix D. `@0.7`'s three *restrictions* —
`discharge`/`open` on a bare leaf are parse errors, a hole is spelled `open q`,
and a shadowed discharge target is a hard error — are specified in Appendix F;
they remove surface and add none, so the AST, the wire, and `lara-core@0.2` are
again unchanged. `@0.8` lets a certificate premise reference cite the citing
rule's declared premise **label** beside the `@0.6` leaf and prior-argument
names (Appendix G). The current surface is `@0.9`, which gives `nd@1` a named
proof-term presentation over its unchanged de Bruijn kernel (Appendix H).
Neither addition changes a lexer or parser rule, and each successful named
form lowers to the numeric spelling's exact bytes.

Versioning: the presentation surface is versioned **separately** from the core
(`docs/spec.md` §2.1). This document defines `lara-syntax@0.9`; it decodes to
`lara-core@0.2`. Signature declarations lower to `unitSigma`; the additive
`@0.3` forms, `@0.4` value bindings, `@0.5` inferred-theta form, and the `@0.6`
symbolic, `@0.8` premise-label, and `@0.9` named-`nd@1` certificate references
remain presentation-layer data until elaboration, and `@0.7`'s restrictions
(bare-leaf body lines, the sole `open q` hole spelling, and the unified
discharge collision policy) remove
presentation-layer forms without adding any, so the decoded `lara-core@0.2`
object is unchanged. The Haskell `parse ∘ print == id` property covers this current
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
by  supports  challenges  discharge  with  open
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

-- lara-syntax@0.7 (Appendix F)
-- removed: `as`. A hole is spelled `open q`, so the keyword has no remaining
-- syntactic role and `as` is once again an ordinary identifier.
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
e2`). Open holes are explicit too: `open q` (`@0.7`, Appendix F.3). The `D ⊎ H = questions(r)`
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
   `≡`-match (0 ⇒ error, 1 ⇒ resolved, ≥2 ⇒ error). Current sources may use the
   `@0.5` form `by r from […]`, whose ordered source references and matching
   contract are defined in Appendix D. Discharges and holes remain explicit.

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

This block records the historical `@0.3` spelling. The active `@0.7` surface
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
instantiation — explicit `r(g1,…,gn)` or inferred `r from [...]` — a hole is
authored and printed as `open q`, stored as `ObligationId q`. (At `@0.5` and
`@0.6` the production was `open q as o`: the parser read `q`, discarded it, and
retained only the `ObligationId o`, and the canonical printer re-emitted
`open o as o`. `@0.7` retired that two-identifier form — a hole has one identity
— and both legacy shapes are now located parse errors carrying the repair; see
Appendix F.3.) §3 leaves `dischargeLine`/`openLine` order free
and A.1 lets `assurance` fold in anywhere; the canonical printer picks one order
— discharges, then opens, then assurance. For inferred arguments it prints the
rule, named references, discharges, opens, and assurance.

On a bare `leaf(…)` support term there is nothing to retain. At `@0.5` and
`@0.6` the parser accepted `discharge` and `open` lines there and then dropped
them entirely, id and all (issue #135) — the opposite of A.1's ruling for
`assurance`, which is a parse error in the same position precisely so the author
is not misled. `@0.7` extends A.1's ruling to both siblings: all three lines are
located parse errors on a bare leaf (Appendix F.2).

That the discarded token was never consulted is exactly why one name suffices:
§6.1 reads a hole's `ObligationId` *as* the question it leaves open
(`holeNames` in `Lara.SupportTerm`, Lean `H : List QuestionId`), so the stored
id names the question actually in force. Under the retired `@0.5`/`@0.6`
spelling every committed `open` line already spelled the two identically, which
is why `@0.7`'s migration is textual only (Appendix F.5).
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

*Extended at `@0.8`:* Appendix G.2 adds the citing rule's declared premise
labels as a third name class, under the same collision policy (G.3). The
two classes below and their collision rule are unchanged.

A symbolic name resolves in the `lara-syntax@0.5` reference namespace —
declared leaves ∪ prior arguments, exactly the scope an inferred θ reference
sees (Appendix D.1): "prior" means already elaborated earlier in declaration
order, and a later argument is never a valid reference. A name that matches both namespaces is a **hard error**,
never silently one of them — deliberately aligned with the inferred-reference
resolver, not with the discharge resolver's silent leaf preference (that
inconsistency is tracked separately as issue #129, untouched here).
*Resolved at `@0.7`:* Appendix F.4 gives the discharge resolver this same
collision policy, so the carve-out named in this paragraph no longer exists —
all three argument-body reference positions now agree.

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
  must cite numeric slots there. *Superseded at `@0.8`:* a numeric slot is no
  longer the only exit — the rule's premise label for the intended slot is the
  other, and the better one (Appendix G.4).

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

*Superseded by Appendix G.5:* `@0.8` adds a seventh family
(`CertSlotLabelAmbiguous`) and rewords two of the six below, so **G.5 is the
normative template list**. The list here is kept as the `@0.6` record.

The six diagnostic families are `CertSlotUnresolved`, `CertSlotAmbiguous`,
`CertSlotNotAPremise`, `CertSlotMultiSlot`, `CertSlotNonCanonicalNumeral`, and
`CertSlotSchemaMismatch` — located `ElabError`s in the `ThetaReference*` style
(D.3), attributed to the enclosing `arg` block. This *was* their normative
home at `@0.6`; the renderer *used* these exact templates, where `A` is the
enclosing argument, `B` is the backend spelling `name@version` from the
`assurance` line, `N` is the authored reference spelling, and `I`/`J` are
0-based slots:

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

> **Resolved at `lara-syntax@0.9`:** Appendix H lands the first bullet's named
> kernel/surface split (#132). This section remains as the historical record of
> why `nd@1` was excluded at `@0.6`; Appendix H is normative for current
> `nd@1` authoring.

`nd@1` admitted no named slots and was deliberately schema-less: its payloads
passed through byte-identical and kept numeric `hyp` indices. `ord@1` and
`ra@1` payloads were single flat head applications with premise references at
fixed argument positions — a name was a stable notion there. `nd@1` payloads
were recursive de Bruijn proof terms: `hyp i` shifted under `lam` binders and
conflated premise slots with theory entries by offset, so "the premise named
`e4`" was not well-defined at a fixed payload position without teaching the
presentation layer the full ND grammar and binder discipline.

Two future-work notes were recorded here so the next design could start from them:

- *A named `nd@1` form* was expected to start from Lean 4's kernel/surface
  split rather than inventing new machinery. The kernel term would stay de
  Bruijn (`hyp i`). The presentation would write named binders
  (`(lam h FORMULA CERT)` with `h` bound in `CERT`) and cite premise/theory
  slots by source name. The elaborator would own the index shifting, exactly
  as Lean's elaborator lowered
  `fun h => … h …` to bound-variable indices. The locally-nameless literature
  covered the metatheory of that lowering.
  *Resolved at `@0.9`:* Appendix H defines this form, including the exact
  binder discipline, mode boundary, lowering arithmetic, and rejection
  surface. Formula annotation authoring is the one deliberately separate
  follow-up, tracked by [#144](https://github.com/ARA-Labs/lara/issues/144).
- *Rule premise labels as a second symbolic class (considered and deferred).*
  `premiseLabelIndex` already mapped a rule's declared premise labels to slot
  indices, and a label named the backend slot directly — it would even have
  covered the E.3 multi-slot case, where this design fell back to numerals.
  It was deferred at `@0.6` because labels were optional
  (`rulePremiseLabels :: [Maybe PremiseLabel]`) and could not be the universal
  namespace. A second symbolic class would have needed its own collision
  policy against leaves and priors, growing the resolution surface that this
  feature was supposed to keep predictable. Premise-label citation remained a
  natural future `lara-syntax@0.x` extension.
  *Resolved at `@0.8`:* Appendix G lands premise-label citation (#131). The
  collision policy this bullet asks for is G.3 — cross-class collision is a
  hard error, with no carve-out for agreeing referents — and the optionality
  concern is answered by keeping labels a *third* class beside the other two
  rather than a replacement (G.2): a rule that labels nothing is cited exactly
  as at `@0.6`. The multi-slot case this bullet anticipated is G.4, worked in
  `examples/S7/`.

## Appendix F — `lara-syntax@0.7` (surface strictness, 2026-08-20)

### F.1 Scope

Three restrictions over `lara-syntax@0.6`, all enforcing one invariant: **every
authored surface token must affect the semantic object or trigger an explicit
error.** A token the parser reads and then discards is a lie to the author, who
reasonably concludes the checker saw what they wrote.

- **F.2 (#135)** — `discharge` and `open` under a bare `leaf(…)` support term
  are parse errors, not silently dropped lines.
- **F.3 (#133)** — a hole is spelled `open q`. The two-identifier
  `open q as o` form is a located parse error carrying its repair, and `as`
  leaves the §1.4 vocabulary.
- **F.4 (#129)** — a `discharge q with x` whose `x` names both a declared leaf
  and a prior argument is a hard elaboration error, not a silent preference for
  the leaf.

This appendix adds **no productions**. `@0.7` is the first surface version that
only *removes* surface: `@0.2`–`@0.6` were additive (`@0.3` carried one source
migration; `@0.6` changed no lexer or parser rule at all), while every clause
below narrows what the parser or elaborator accepts.

Nothing here reaches the kernel. There is no `lara-core@0.2` change, no
`Lara.AST` change, no wire or `.core.sexp` change, no checker-judgment change,
and no strict-backend or replay change. The surface version never reaches the
wire, so every derived `.core.sexp`, `expected.json`, verdict, mutant fixture,
and frozen measurement byte is unchanged (F.5). Because the AST is unchanged,
`lean/Lara/Presentation.lean`'s structured model still holds at `@0.7` and
`scripts/check-presentation-parity.sh` stayed green throughout; no Lean work was
owed. The `@0.7` elaborator addition (F.4) sits in the validated-not-verified
elaborator (`ara/logic/solution/constraints.md`), which the mechanization plan
does not cover.

**Why removal is the right instrument here, and why no compatibility alias.**
Every one of these three warts has the same shape — the surface accepts an
author's token and then does not mean it — and an alias that keeps accepting the
old spelling would preserve exactly the misreading each fix exists to remove.
The usual argument against a breaking surface change is the installed base;
LARA has none. There is no public release of `lara-syntax`, and every `.lara`
source that exists is in this repository, so the migration cost is bounded,
mechanical, and paid in the same commit as the restriction (F.5: ten spellings
in seven of 109 tracked files). Under those conditions a compatibility alias
buys nothing and permanently doubles the spellings a reader must know. The
window for this trade closes when the surface is published; that is an argument
for making the surface strict *now*, not for deferring.

### F.2 `discharge`/`open` on a bare leaf are parse errors (#135)

Appendix A.1 already rules that `assurance` on a bare `leaf(…)` support term is
a parse error, "the checker has no rule to check it against, and silently
dropping it would mislead the author". That reasoning is not specific to
`assurance`. A `discharge` or an `open` line answers or defers a *critical
question of a rule*; a bare leaf instantiates no rule, so it declares no
questions, and there is nothing for either line to attach to. Before `@0.7` the
parser accepted both there and dropped them entirely, id and all — a strictly
worse outcome than the sibling it sat next to, since the author who writes
`discharge q with e2` under `leaf(e1)` is told nothing and believes `q` was
answered.

`@0.7` extends A.1's ruling to both siblings, with the same wording shape:

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
Previously the bare-leaf case was a silent identity fall-through —
`addArgDischarge inst _ _ = inst`, `addArgHole inst _ = inst`,
`setArgAssurance inst _ = inst` — which meant the rejection lived only in the
parser's decision to check first, and a future caller reaching the helper by another path (a bundle
lowerer, a test builder, a refactor that reorders `argBody`) would silently
resurrect the drop. Making the helpers total-with-error moves the guarantee
into the type: the impossible case has no equation that can quietly succeed.
`setArgAssurance` was brought to the same shape in a follow-up commit for
exactly this reason, even though A.1's diagnostic and its position were already
correct — the consistency is structural, not cosmetic.

*Rejected alternative:* keep accepting the lines and make the elaborator reject
them. That would move an unambiguously syntactic error (a line in a position
the grammar gives no meaning) past the decode boundary, contradicting §1's
placement of surface well-formedness in `Lara.Syntax`, and would leave the
presentation AST able to represent a state the surface cannot mean.

### F.3 The sole hole spelling is `open q` (#133)

```text
openLine ::= "open" ident                 -- open q   (explicit hole)
```

Before `@0.7` the production was `open ident "as" ident`. The parser read the
first identifier, **discarded it**, and stored the second as the hole's
`ObligationId`; the canonical printer then re-emitted `open o as o`, normalizing
away any divergence the author had written. So `open external_validity as o1`
was checked as a hole on the *question* `o1` — a question that in general does
not exist — and printed back as `open o1 as o1`.

**A hole has one identity.** Spec §6.1 question-accounting reads a hole *as the
question it leaves open*: `holeNames` in `Lara.SupportTerm` maps each stored
`ObligationId` to the `QuestionId` of the same text (Lean `H : List QuestionId`;
the Lean driver decodes `holes` straight to `QuestionId`), and `D ⊎ H =
questions(r)` is then checked against the rule's declared questions. No
reporting path — verdict JSON, `Lara.Reporting`, the located-obligation output
of an E2-style gap — ever consumed an obligation name independent of that
question name. The second identifier was therefore never *read* as a separate
thing; it could only be redundant (when equal) or actively misleading (when
divergent). `@0.7` stores `ObligationId q` from the single authored identifier,
which is exactly the name §6.1 goes on to use.

Both legacy shapes are rejected identically — there is no "equal spelling is
harmless" carve-out, because a spelling that is currently harmless is still a
second way to say one thing:

```text
lara-syntax@0.7 uses 'open q'; remove 'as …'
```

located at the `as` token, on `open q as q` and `open q as o` alike, and the
message carries the repair rather than only the complaint.

**`as` leaves the grammar.** It had no other syntactic role, so §1.4 records it
as *removed* at `@0.7` and it is once again an ordinary identifier: a leaf,
argument, rule, question, or predicate may be named `as`, and
`test/SyntaxSpec.hs` (`unit_asIsAnOrdinaryIdentifier`) pins that. This is the
narrow reason the §1.4 table is a single `toString`/`parse` vocabulary — the
keyword's disappearance from the surface is one table edit, and the reserved-word
list the round-trip generator consults (`test/SyntaxSpec.hs`) mirrors it.

The retained `ObligationId` newtype is **not** collapsed into `QuestionId`. It
is the spec §2 obligation name class, and the symbolic-core discipline keeps
distinct namespaces in distinct types (CLAUDE.md); what `@0.7` removes is the
claim that the *surface* can name the two independently. The single sanctioned
bridge is now exactly `open q → ObligationId q → QuestionId q`, confined to
`holeNames`, and `src/Lara/SupportTerm.hs` documents it there.

*Rejected alternative:* keep `open q as o` and make the elaborator check that
`q` is a declared question of the rule (using both names for real). That adds a
second name class to the surface and a new diagnostic family in exchange for an
identifier no downstream consumer reads. Appendix D's inferred-θ payload,
Appendix E's premise-slot names, and F.4's discharge targets all shrink the
number of independently-authorable names in an argument body; this moves the
same way.

### F.4 Discharge collision policy unified with D and E.2 (#129)

`discharge q with x` resolves `x` in the `lara-syntax@0.5` reference namespace:
declared leaves ∪ prior arguments (Appendix D.1). Before `@0.7`, when `x` named
**both**, the resolver silently preferred the declared leaf. The identical
collision was already a hard error in the two neighbouring positions — Appendix
D's inferred-θ references (`ThetaReferenceAmbiguous`) and Appendix E.2's
certificate premise slots (`CertSlotAmbiguous`) — so one argument body carried
two opposite answers to the same question, and which one an author got depended
on which line they were writing.

`@0.7` gives all three positions one policy. One `refMatches`-based
`resolveDischargeRef` serves **both** discharge payload forms — the explicit one
(where the parser spells the target `SLeaf (LeafId ref)`) and the inferred one
(where it arrives as `ArgRef ref`) — so the two surfaces cannot drift apart:

| declared leaf named `x` | prior argument named `x` | result |
| --- | --- | --- |
| yes | no | the leaf's `SLeaf` |
| no | yes | that argument's elaborated support term |
| yes | yes | **`AmbiguousDischarge`** (new at `@0.7`) |
| no | no | `UnresolvedDischarge` |

"Prior" keeps D.1's meaning: strictly earlier in declaration order, i.e.
whatever `elabOne` has accumulated when this argument is elaborated. A discharge
naming a *later* argument is therefore `UnresolvedDischarge`, not a forward
reference — the same scope rule the θ references and the E.2 premise-slot names
already obey. The two non-error rows are unchanged behavior: the previous
implementation tested `elem` against `envLeafIds env = map fst envGamma`, which
is exactly the leaf half of `refMatches`, so the **only** new rejection is the
ambiguity itself.

Diagnostics (`Lara.Elaborate.Error`, the D.3 `ThetaReference*` style, attributed
to the enclosing `arg`):

```text
arg 'A': discharge of 'q' names 'x', which is neither a declared leaf nor a prior argument
arg 'A': discharge of 'q' names 'x', which is ambiguous between a declared leaf and a prior argument
```

`AmbiguousDischarge ArgId QuestionId ArgRef` is the new family.
`UnresolvedDischarge`'s final field is retyped `String → ArgRef` in the same
change, so the source identifier is carried in the type the namespace is defined
over and is unwrapped in exactly one place — the renderer — matching how every
other reference diagnostic in this family already works.

**This closes E.2's carve-out.** Appendix E.2 records the `@0.6` decision to
align the certificate premise-slot resolver "with the inferred-reference
resolver, not with the discharge resolver's silent leaf preference (that
inconsistency is tracked separately as issue #129, untouched here)". At `@0.7`
there is no discharge exception left to name: all three argument-body reference
positions resolve in one namespace under one collision policy, each keeping only
its own error *family* because each names a different surface position.

*Rejected alternative:* make the leaf preference explicit and documented instead
of an error. Shadowing rules are exactly the kind of surface knowledge a reader
must hold in their head to read a program correctly, and a program whose meaning
turns on one is not readable at the Python-literate baseline this surface
targets. The author who hit the collision can rename in one edit; the reader who
does not know the rule silently misreads the argument.

### F.5 Migration

Every `.lara` source in the repository was migrated in the same commit as the
restriction that required it, so the suite never went red.

- **10 spellings across 7 of 109 tracked `.lara` files** — all of them F.3's
  hole spelling, and all of them the *equal* form `open X as X`:
  `corpus-units/bam/C05`, `corpus-units/fre/C01`,
  `corpus-units/rebench-restricted_mlm/C14`,
  `corpus-units/rebench-triton_cumsum/C09` (one line each), and the three
  rebuttal-replay examples `examples/rebuttal-replay/round0`, `round1`,
  `round2` (two lines each).
- **F.2 required no source migration**: no committed source attaches a
  `discharge` or `open` line to a bare `leaf(…)` support term.
- **F.4 required no source migration and cannot fire on the corpus**: no
  tracked `.lara` file has a name that is both a declared leaf id and an
  argument id. Acceptance is unchanged corpus-wide.

**Zero derived semantic artifacts changed.** Verified by explicit pathspec diff
over `corpus-units/**/*.core.sexp`, `corpus-units/**/expected.json`,
`examples/**/*.core.sexp`, `examples/**/expected.json`, `fixtures/mutants` and
`measurements/frozen` — empty. The authored `.lara` sources moved, so their
containing trees re-pin (intentional, and recorded in
`docs/m5-freeze-checklist.md` as provenance):

| tree | `@0.6` | `@0.7` |
| --- | --- | --- |
| `corpus-units/` | `1dc20ea9d79adb2690731a66216dae828a100cf3` | `cadb5fa62b9f7f6ace14129f1435e3c32b2dff7b` |
| `examples/` | `4ab6b5f480d9e3bddd94b17908d1c6a910b7944f` | `9e6291fbf1a53703092123a4550ab2099cbed52c` |

The two frozen trees that hold no `.lara` source are byte-identical and did not
move: `fixtures/mutants/` = `fd7142072d58da4d35642cbad6f144c970627afa`,
`measurements/frozen/` = `a067c921e0142eae69b34ed500ff18c7efea1bed`.

**No measurement re-run is owed.** The measurement harness consumes
`.core.sexp` bytes, every one of which is unchanged, so the headline numbers of
record stand as measured: **564/564** class match, **564/564** `lean_agree`,
**60/60** replay.

## Appendix G — `lara-syntax@0.8` (premise-label certificate citation, 2026-08-21)

### G.1 Scope

Additive over `lara-syntax@0.7`. A certificate premise reference may now cite
the **premise label** the citing rule declares for that slot (Appendix B.4),
alongside the `@0.6` leaf and prior-argument names. Like `@0.6`, this changes
no lexer or parser rule: the spelling `(prem s)` is unchanged, and only the set
of names `s` may carry grows.

Nothing here reaches the kernel. No `lara-core@0.2` change, no `Lara.AST`
change, no wire or `.core.sexp` change, no checker-judgment change, and no
strict-backend or replay change. A label citation and its numeric twin produce
byte-identical `Cert` payloads, byte-identical encoded `Unit`s, and
byte-identical verdicts; `examples/S7/` authors the label spelling and its
committed `.core.sexp` golden is the standing byte-identity witness (G.7).

**Why labels earned their own name class.** `@0.6` resolves a name by locating
the *referent's term* in the resolved premise sequence, which has one case it
structurally cannot express: when one leaf feeds two premises, the leaf name
occupies both slots and the author is pushed back to numerals (E.3's third
bullet). A label does not name the term — it names the **slot**, in the rule
that declares it — so it stays unambiguous however the instance is filled.
That is the gap #131 closes, and it is closed with an existing, tested
mechanism (`premiseLabelIndex`) rather than new machinery.

### G.2 The three-class namespace and resolution rule

A symbolic `(prem s)` resolves in **three** classes:

1. the **premise labels declared by the rule of the instance whose certificate
   this is** — the citing rule, never an enclosing or nested one;
2. the **declared leaves**;
3. the **prior arguments** (already elaborated, in declaration order).

Class 1 is answered by `premiseLabelIndex`, which maps a label to its 0-based
slot directly and needs no locating step. Classes 2 and 3 are `@0.6`'s
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
- no label hit → exactly `@0.6`, with all of E.2's and E.3's verdicts.

Labels are optional (`rulePremiseLabels :: [Maybe PremiseLabel]`, `[]` when the
rule labels nothing), so class 1 is empty for every rule written before `@0.8`
— which is every rule in the frozen corpus. For those rules the resolver is
bitwise the `@0.6` one, and `test/CertSlotsSpec.hs` carries an unlabelled
control rule pinning both its resolving and its failing path.

The class is **per rule, not per policy**: a label of rule `r` is not a name
that rule `r'` knows, and a nested instance's certificate resolves against its
own rule's labels, never the enclosing instance's (E.6, extended in G.6).

### G.3 Collision policy: cross-class collision is a hard error

A name carried by both class 1 and class 2 or 3 is `CertSlotLabelAmbiguous`,
never silently either class. This is E.2's and F.4's one collision policy
applied to the new class, and it holds **even when the two classes would
resolve to the same slot**.

That last clause is the deliberate part. A carve-out for agreeing referents is
tempting — nothing is lost by picking either — but it would be the first
conditional case in a policy that is otherwise a single uniform sentence, and
its condition is not visible in the citing line: whether `base` is ambiguous
would depend on which slot a leaf elsewhere in the artifact happens to fill.
An author reading `(prem base)` could not tell. Predictability beats
convenience here, and relaxing the rule later is additive while tightening it
later would be breaking.

The rejected alternatives, for the record: *label wins* and *leaf wins* both
reintroduce the silent preference #129 removed from the discharge resolver;
*agreeing referents are fine* is the conditional rule above.

### G.4 What labels resolve that names could not

E.3's third bullet — two or more occupied slots — said the author "must cite
numeric slots there". That is no longer the only exit. **Superseded by this
section:** the multi-slot case now has two exits, a numeric slot or the
label of the intended slot, and the label is the better one, because it says
which slot was meant in the rule's own vocabulary rather than by position.

When every slot occupied by the ambiguous source name has its own usable
premise label, the `CertSlotMultiSlot` message names both repairs: cite a
numeric slot or that rule's label for the intended slot. A label is usable only
when its spelling does not collide with a declared leaf or prior argument.
`examples/S7/` argument `a2` is the worked case: one leaf fills both premise
slots of a two-premise rule, and only `(prem left)`/`(prem right)` resolve
there. An unrelated, partially declared, or colliding label does not advertise
a nonexistent repair.

Note that this does not make labels a *universal* namespace. Labels are
optional, so a rule that declares none is cited exactly as at `@0.6`, and the
multi-slot dead end survives for such a rule. What `@0.8` gives is an exit the
policy author can open.

### G.5 Stable error messages

Seven diagnostic families: E.5's six, of which **two are reworded here** and
the multi-slot template is reworded at `@0.9`, plus `CertSlotLabelAmbiguous`.
This list supersedes E.5's as the normative home;
E.5 carries a banner pointing here. `A` is the enclosing argument, `B` the
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

The first and third templates changed at `@0.8`; the labelled multi-slot
template changes at `@0.9`. The first and third name the citing rule,
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

### G.6 Recursion, and why no Lean change is owed

E.6's recursion semantics hold verbatim, with the citing rule's labels now part
of what "that node's own scope" means: a nested certificate resolves against
the nested instance's premise list *and* the nested rule's labels. A label of
the enclosing rule is unresolved inside a nested certificate, and vice versa.
`test/CertSlotsSpec.hs` pins both directions at the AST level, because a leaked
label would be the worst kind of silent success — it names a slot index both
instances have.

**No Lean change is owed.** `lean/Lara/CertSlots.lean` parameterizes the
mechanized pass over an *abstract* resolver `ρ : String → Option Nat` and an
abstract classifier `startsSourceIdentifier : String → Bool`, and both
theorems — `lower_id_of_no_symbolic` (byte preservation on every payload the
frozen corpus can contain) and `lower_eq_numeric_subst` (a successful lowering
is exactly the declarative substitution) — are universally quantified over `ρ`.
The label-extended resolver is one more instance of `ρ`, so both theorems hold
over it without re-proof. This is the F.1 precedent restated: a surface change
that does not alter the modeled shape owes no Lean work, and saying so
explicitly is part of the record. `scripts/check-axioms.sh` and
`scripts/check-presentation-parity.sh` stayed green with no Lean edit.

The resolver itself lives in the validated-not-verified elaborator
(`ara/logic/solution/constraints.md`), which the mechanization plan does not
cover; the Lean mirror carries the lowering math, and the Haskell property
tests carry conformance.

### G.7 Migration and derived artifacts

**No source migration.** `@0.8` adds names to a namespace and removes nothing,
so every `.lara` source in the repository is unchanged and every existing
spelling keeps its meaning. `@0.8` cannot fire on any pre-existing artifact:
no tracked policy labels a premise of a rule whose certificates cite names, so
class 1 is empty throughout the frozen corpus and the resolver's behavior there
is bitwise `@0.6`'s.

**One new worked example, no changed derived artifact.** `examples/S7/`
(`example.lara`, `ord-labeled-v1.policy.lara`, and the two generated files) is
added; no other `example.core.sexp`, `expected.json`, mutant fixture, or frozen
measurement byte changes. S7's own golden was verified byte-equal to the one
its numeric twin produces — both certificates lower to
`(ordcmp (prem 0) (prem 1))` — and `test/WorkedExamplesSpec.hs`'s freshness
property re-proves that on every run, while `scripts/differential.sh` confirms
both drivers agree on the new anchor.

**No measurement re-run is owed**, for F.5's reason: the measurement harness
consumes `.core.sexp` bytes and none of the measured ones moved.

## Appendix H — `lara-syntax@0.9` (named `nd@1` proof terms, 2026-08-22)

### H.1 Scope and the two modes

Additive over `lara-syntax@0.8`. The registered `nd@1` backend keeps its
closed, numeric de Bruijn grammar; `@0.9` adds a presentation form that the
untrusted elaborator lowers before replay. The grammars are deliberately
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
still `(atom KEY)`, never a bare key. Producing `KEY` from a source proposition
is an encoding feature, not reference lowering, and remains tracked only by
[#144](https://github.com/ARA-Labs/lara/issues/144).

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
inside named mode is therefore `CertNdKernelIndex`, not a second spelling. The
rejected gradual-conversion alternative would have retained raw `hyp` indices
inside named terms; it was rejected because `(prem N)` shifts under binders
while `(hyp N)` would not, giving one term two context-sensitive shift regimes.
Relaxing this rule later would be additive; tightening it later would break
authored artifacts.

Nothing in this appendix changes `lara-core@0.2`, `Lara.AST`, the wire,
`.core.sexp`, the frozen corpus, a checker judgment, or replay. No corpus
regeneration or freeze-tag bump is owed.

`@0.9` is the **substrate** for eventual named formula authoring, not a complete
deep-`nd@1` authoring solution. It closes silent index-misbinding by giving
binders, premises, and theory offsets one explicit lowering discipline, while
formula annotations remain opaque `(atom KEY)` values that still require
out-of-band tooling until #144 lands.

### H.2 Namespaces and binder discipline

The three reference namespaces are separated by their heads (D1): `(hyp x)`
consults only enclosing named binders; `(prem s)` consults only premise slots;
and `(thy N)` consults only theory entries. They never compete for one syntactic
position. That head separation is why E.7's general collision concern dissolves
for recursive proof terms instead of requiring a global shadowing preference.

A named binder is spelled `(lam x FORMULA CERT)`. Its `x` must be a
`sourceName`: an S-expression atom whose first decoded character satisfies
`isIdentStart`. Numeral and structured binders are rejected, but the remainder
of the atom is not re-lexed as a complete §1.3 `ident`; it stays part of the
name verbatim. The kernel three-field spelling `(lam FORMULA CERT)` remains
legal inside named mode as an anonymous binder and still contributes one level
to de Bruijn depth.

Local binder shadowing is forbidden (D3): a nested named `lam` may not reuse an
enclosing binder's name. Lean-style shadowing was considered and rejected
because the same `(hyp x)` would silently change its referent after crossing the
inner binder. A named binder also may not use a name that the citing instance's
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

### H.4 Exact D7 boundary and rejection-site migration

The same marker vocabulary drives two leftmost-outermost scans. The first
selects named mode. Before lowering, a traversal-aware scan checks positions
that the lowering grammar treats as opaque. The markers are exactly:

1. a two-field `(prem ATOM)` node;
2. a two-field `(thy ATOM)` node;
3. a four-element `(lam BINDER FORMULA CERT)` node; and
4. a two-field `(hyp a)` whose decoded atom `a` is nonempty and whose first
   character satisfies `isIdentStart`.

Everything with none of those markers is kernel mode and passes through
unchanged—valid kernel certificates, marker-free junk such as `(foo bar)`, and
even noncanonical `(hyp 007)` alike. The backend continues to own their decode
or replay result, including R13. Once any marker selects named mode, known proof
constructors are recursively lowered. A named marker in an opaque formula
position or an unknown subtree is `CertNdResidualNamed` at the source boundary,
even when lowering a traversed node would fail for another reason. Consequently
only payloads that actually contain one of the four markers migrate from
backend R13 to a located elaboration error; marker-free payload behavior is
unchanged. A raw `.sexp` has no presentation lowering and remains backend-owned.

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
backend diagnostic describes the lowered de Bruijn term; there is no source map
back to binder or premise names. The source author may therefore have to map an
index back by hand. This error-attribution limitation does not weaken replay,
but it belongs to the honest user-facing boundary.

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
function, nor verify the Haskell classifier or resolver. `@0.9` removes silent
index-misbinding from named premise/binder authoring, but complete formula
authoring still needs tooling until #144 lands.
