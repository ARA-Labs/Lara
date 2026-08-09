# `lara-syntax@0.3`: the evidence-first authoring surface

**Goal:** Make a `.lara` artifact read like the research argument it encodes, and make it
cheap to author incrementally — by a human working from a table, or by an agent sweeping
evidence out of a paper before it knows what it will claim. Three additive surface forms,
all elaborated away: a measurand table with declared polarity, a `comparison` derived
declaration, and value bindings with `nl` interpolation.

**The invariant that makes this reviewable (2026-08-08):** nothing below the surface
moves. No change to `Unit`, `.core.sexp`, the wire codec, `checkUnit`, the strict
backends, or any existing result in `lean/`. Every form here is parsed into the
presentation AST and expanded in `Lara.Elaborate` before the checker anchor exists, and
every example must elaborate to a **byte-identical `Unit`**. Additive over
`lara-syntax@0.2` exactly as App. A of `docs/lara-surface-grammar.md` was additive over
`0.1`.

**Scope boundary:** the many-sorted signature decided in #89 is *core* work — it puts Σ
into `Unit`, bumps the wire to `lara-core@0.2`, and needs a spec amendment. It is
deliberately **not** in this plan. The one piece of it that belongs here is the measurand
table (§3.1), which never enters `Unit`.

Issues: #91 (tracker), #90 (`comparison` form), #88 (bindings). Related: #89 (sorts, core
track), #87 (binding audit).

---

## 1. Background: what exists today

`ord@1` (`plans/2026-08-06-ord1-comparison-backend.md`, PR #83) certifies the most common
claim shape in ML methodology papers as a closed two-predicate family, `num_lt(A, B)` and
`num_le(A, B)`, over two canonical decimal numerals, in exact rational arithmetic. The
worked examples that exercise it are `examples/S2` (strict inequality), `examples/S3` (the
`num_le` tie), and `examples/S4` (an audit undermining the binding leaf).

The layering those examples establish is the right one, and this plan does not touch it:

- a **strict** rule, certified by `ord@1`, concludes the bare comparison `num_lt(Bv, Sv)`;
- a **defeasible** bridge rule consumes that conclusion together with a `comparison_setup`
  binding leaf — which says *which* systems and measurand those two numbers belong to —
  and concludes the comparative claim `better(S, B, Q, D)`.

The split is load-bearing. The arithmetic is unarguable; the inference from "0.71 < 0.74"
to "sys_new is better" is defeasible, because it depends on the binding being right and on
the comparison being the relevant one. `examples/S4` is the demonstration: an audit
undermines the binding leaf, the bridge is defeated, and the certified comparison stays
justified.

### 1.1 What is wrong with it

Not the calculus — the surface. Three specific costs.

**The author writes both legs by hand.** In `examples/S2/example.lara`, delivering one
comparative claim takes a `claim c2` whose `formal` is `num_lt(0.71, 0.74)`, an `arg a1`
carrying `(ordcmp (prem 0) (prem 1))`, and an `arg a2` repeating the same seven-term θ.
So the arithmetic is the most conspicuous thing in a file whose subject is a comparative
claim. **The artifact reads like arithmetic because the author had to type arithmetic**,
not because the calculus thinks in arithmetic. That matters for the stated audience: the
surface targets researchers who read Python, not PL experts.

**Everything is transcribed at every use site.** `0.74` appears at five substitutable
sites in S2 (`claim c2` formal, leaf `e2`, leaf `e3`, arg `a1`'s θ, arg `a2`'s θ) and once
more inside `claim c1`'s `nl` prose. `sys_new`, `accuracy`, and `imagenet_val` repeat
similarly. Change one measurement and every site must move together; miss one and the
elaborator's `≡`-match premise resolution fails with `UnresolvedPremise`, an error naming
the resolution failure rather than the typo that caused it.

**The certificate's slot indices are derived from a different file.** `(ordcmp (prem 0)
(prem 1))` names positions in the **policy rule's** `premises` list, not positions in the
source. To write them the author opens `ord-v1.policy.lara`, reads that `beats_recheck`
lists the baseline cell first, and hand-derives `prem 0` = `e1`. Swap them and you get an
R13 replay rejection whose message is about a cell mismatch, not about the swap.

### 1.2 The direction-of-goodness problem

Underneath the readability complaint is a real correctness hazard. **Direction of goodness
is a property of the measurand, not of the comparison.** Higher accuracy is better; lower
perplexity, latency, error rate, and FLOPs are better. So "we beat the baseline" is
`num_lt(base, ours)` for accuracy but `num_lt(ours, base)` for perplexity — and today the
author performs that conversion unaided, every time, with no check that they got it right.
A swap produces a well-formed artifact that certifies the opposite of what was meant.

---

## 2. Motivation

**Human authoring.** The costs in §1.1 are the ordinary friction of keeping five copies of
a number consistent, plus one genuinely error-prone index. They are annoying at three
claims and untenable at thirty.

**Machine authoring.** This is the sharper case. An agent sweeping tables out of a paper
writes evidence *incrementally*, before it knows what claims it will make: it drops leaves
as it reads, then assembles claims and arguments over them. Positional slot indices into a
policy file, across an artifact it is still writing, are exactly the wrong interface — and
the polarity conversion in §1.2 is precisely the kind of silent, systematic error a
generator makes at scale.

**Readability as a research artifact.** An ARA is meant to be read by a reviewer, not only
checked by a tool. If the formal object's most visible content is `num_lt(0.71, 0.74)`,
the artifact reads as arithmetic bookkeeping rather than as an argument, and the layering
that makes it defensible — strict arithmetic under a defeasible bridge — is invisible
under the syntax that implements it.

**Why not just θ-matching on plain `arg`?** (eng review 2026-08-08.) The expansion's core
mechanism — derive θ by matching named leaves against the rule's premise patterns (§5) —
would, applied to ordinary `arg` declarations, remove transcribed θ vectors for *every*
rule with no new declaration form, no scheme registry, and no version bump. That baseline
is real and is captured in `TODOS.md` as a candidate #88b rider. It is not sufficient for
this plan's goals: it cannot *generate* the comparison goal (the author would still write
`num_lt` in the sub-claim's `formal`), so the §1.2 polarity hazard survives untouched; and
it cannot collapse the claim + two-arg pattern into one readable block. The `comparison`
form is justified by exactly the two things the baseline cannot do — goal generation under
declared polarity, and the one-block reading — not by θ relief alone.

---

## 3. The design

### 3.1 Measurand table with declared polarity

```
measurand accuracy   : Num  where higher-is-better
measurand perplexity : Num  where lower-is-better
```

Declared in the policy. Polarity is domain knowledge, not usage, so it is **not
inferrable** — which is why it is declared rather than derived, and why it is the one
piece of #89 that belongs on this track.

The elaborator reads it to select the comparison scheme (§3.3) whose rules are written in
the measurand's direction. **It never enters `Unit`**; nothing downstream consumes it.
That is what keeps it on the surface track and out of the `lara-core@0.2` work.

**Forward-compatibility with #89 (eng review 2026-08-08).** The `: Num` slot in this
declaration is deliberately a *sort position*: when #89 puts Σ into the core, its
many-sorted signature should extend this same declaration (the surface #89 elaborates
into), not introduce a parallel one. App. B must say so, and #89's tracker gets a
cross-reference, so the two tracks cannot fork the spelling.

### 3.2 The `comparison` declaration

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

The author never writes `num_lt`, never writes a slot index, never picks an argument
order. Switch the measurand to `perplexity` and the same source, under a policy whose
scheme covers `lower-is-better`, generates the flipped goal.

**The sub-claim is declared, not vanished** (eng review 2026-08-08, T2-A). The comparison
sub-claim (`c2` today) carries authored prose, an author attestation (`binding`), and — in
S4 — a `status` line; all of that reaches `Unit`, and prose cannot be machine-invented. So
the block *declares* the sub-claim's id and human parts in a `claims` sub-block, and the
elaborator emits the claim with the **generated goal as its `formal`**. Only the
arithmetic is generated; the prose and attestation stay human — the same philosophy as the
binding leaf in §5. Declaring the id also keeps `status c2` and any future attack on the
sub-claim resolvable, the same lesson as §3.4's argument ids.

**`relation` is required and closed**, with two members — the family has two members and
both are needed:

| `relation` | `higher-is-better` | `lower-is-better` | research reading |
|---|---|---|---|
| `strictly-better` | `num_lt(base, ours)` | `num_lt(ours, base)` | "outperforms" |
| `at-least-as-good` | `num_le(base, ours)` | `num_le(ours, base)` | non-inferiority, ties |

This table is a **lookup contract, not elaborator magic** (eng review 2026-08-08, T1-A):
direction lives in the policy's rules, welded to the bridge's conclusion through shared
variables, so the elaborator cannot flip an argument order without flipping who is claimed
to be better. Each cell of this table is realized only if the policy declares a scheme for
that (relation, polarity) pair, written in that direction (§3.3).

Non-inferiority is a distinct and common research argument ("matches the baseline at a
third the cost"), and `examples/S3` is exactly that case. Without `relation` this form
could not express S3 at all.

**No value bindings are needed to name the cells.** `Lara.Strict.Cell.premiseCell`
already extracts the unique numeric literal from a premise — it is what `ord@1` itself
uses — so `result = e2` suffices and the elaborator reads the value out of the named leaf.
The leaf's premise-cell obligation (exactly one numeric literal) becomes a precondition of
this form, and violating it is a located source error naming the leaf, not a downstream
backend rejection.

### 3.3 The `comparison-scheme` policy block

The generated arguments instantiate policy rules, and **rule names are policy-specific**.
S2 uses `beats_recheck`/`beats_baseline`; S3 uses `tie_recheck`/`no_worse` under a
different policy entirely. A `comparison` form that hardcoded S2's names would be unusable
elsewhere.

So the policy registers which of its rules play the two roles, **per (relation,
polarity)** (eng review 2026-08-08, T1-A — relation alone cannot express direction,
because the rules carry it):

```
comparison-scheme strictly-better higher-is-better
  recheck = beats_recheck
  bridge  = beats_baseline

comparison-scheme at-least-as-good higher-is-better
  recheck = tie_recheck
  bridge  = no_worse
```

A policy declares only the pairs its rules actually support; up to four entries. The
elaborator's lookup composes the block's `relation` with the measurand's declared
polarity; a missing pair is the same located-error class as a missing scheme. Binding the
scheme to the pair (rather than declaring one scheme and letting `relation` or direction
vary inside it) removes a whole error class: the generated goal's family member, its
argument order, and the rules that consume it cannot disagree.

Well-formedness the elaborator checks when a scheme is declared:

- `recheck` is a **strict** rule listing an `ord@1` certifier;
- `bridge` is **defeasible**;
- `bridge`'s premise patterns admit the comparison atom and the binding atom;
- the authored conclusion in the `comparison` line matches `bridge`'s declared conclusion
  pattern;
- `bridge`'s conclusion pattern is **4-ary over S, B, Q, D with the favored system
  first** (eng review 2026-08-08, F4). This positional convention is what `better(sys_new,
  sys_base) on accuracy @ imagenet_val` elaborates against; richer bridge conclusions
  (e.g. a settings parameter) are a §9 non-goal for this version of the form.

A policy with no matching `comparison-scheme` simply has no `comparison` form available —
a located error at the use site, never a silent fallback.

**The form inherits whatever the scheme's rules demand** (eng review 2026-08-08, F6). In
particular, `beats_recheck`'s premise patterns share one `Exp`, so both cells must come
from the same experiment; a baseline number quoted from a *prior paper's* experiment is
unauthorable through this scheme and needs a rule (and scheme) written with two experiment
variables. The θ-consistency error (§5) must name the conflicting binding so this reads as
a domain fact, not a mystery.

### 3.4 Explicit argument ids — required, and why

The block declares `recheck = a1` and `bridge = a2`: **the ids of the two arguments it
generates.** This is not cosmetic. `examples/S4` attacks the generated structure:

```
arg x1 : challenges(e3) by setting_audit(…)
undermine x1 a2.1.leaf
```

`a2.1.leaf` is a position path into the bridge argument's premise 1. If the `comparison`
block generated anonymous or derived ids, every existing attack in S4 would break, and the
byte-identical-`Unit` property would be unreachable. Declaring both ids keeps the attack
syntax working verbatim.

Declaring the ids leaves one positional index — `a2.1` — still counted into a generated
argument. §3.5 closes that.

### 3.5 Labelled premises and symbolic attack positions

`a2.1.leaf` counts premises positionally into a *generated* argument: the same fragility
this plan removes everywhere else, reappearing on the attack surface. Rule premises gain
optional labels, and an attack path may use one:

```
rule beats_baseline(S, B, Q, D, Sv, Bv)
  mode     = defeasible
  premises = [ cmp:     num_lt(Bv, Sv),
               binding: comparison_setup(S, B, Q, D, Sv, Bv) ]
  …

undermine x1 a2.binding.leaf
```

**The disambiguation problem.** Grammar §7 (FROZEN) reads any non-integer dotted segment
as a `StepQuestion`, so a bare premise label is indistinguishable from a question id.
Resolved by **policy well-formedness**: a rule's premise labels must be **disjoint from
that rule's question ids**, and — like question ids under §7 — **`rule` and `leaf` are
reserved from the premise-label namespace** (eng review 2026-08-08, F5; otherwise
`a2.leaf.leaf` parses two ways). Both are policy-declared, so a collision is statically
detectable and rejected at declaration time, and a segment then resolves to at most one
thing. Integers keep resolving directly to `StepPremise`, unchanged.

**Consequence: the presentation AST needs its own attack step.** Grammar §7 states that
attacks reuse the frozen `Attack`/`Position`/`Step` types and that A0.5 "adds **no**
presentation attack type". That cannot hold here, because `printProgram :: Program ->
String` never receives the `Policy` (and `Source` keeps the two as separate files), so the
printer cannot choose between `a2.1.leaf` and `a2.binding.leaf` from policy labels. If the
spelling is not recorded, `parse ∘ print = id` fails for whichever form the printer does
not pick — and making a *program* file's canonical form depend on a *different* file would
be worse than the problem it solves.

So the presentation `Program` carries a shallow step, `SurfaceStep = StepIndex Int |
StepName String`, and `Lara.Elaborate` resolves `StepName` against the target rule — where
the policy *is* in hand (`elaborate sigma registry program policy`). This is exactly the
A1a → A1b contract `Lara.Syntax`'s header already describes for support terms: "premises
are implicit, θ is positional with the parameter *names* living in the policy… the parser
records what the surface states and leaves the rest for the elaborator."

**This amends a FROZEN section** and needs its own sign-off, like #89's R2 amendment
though much smaller. It is strictly additive: the integer spelling keeps working, keeps
its meaning, and stays canonical for any premise without a label. Nothing in
`Attack`/`Position`/`Step` — the Unit-reachable types — moves.

**Sequencing (eng review 2026-08-08, scope decision).** §3.5 is implemented **last**, as a
detachable tail after D1–D6's comparison + interpolation core: it is the only piece
touching a FROZEN section and the only piece gated on the §6.2 sign-off. Until it lands,
S4 uses `a2.1.leaf`; if the sign-off stalls, §3.5 detaches into its own PR at zero cost to
the rest of the track.

### 3.6 Value bindings and `nl` interpolation

```
let acc_new  = 0.74
let acc_base = 0.71

leaf e2 : reports(exp1, score_cell(sys_new, accuracy, imagenet_val, acc_new))

claim c1
  nl = "sys_new outperforms sys_base on ImageNet-val accuracy ({acc_new} vs {acc_base})"
```

A binding maps a name to a **ground `Term`** and nothing else — never a rule parameter,
never an open term, never an atom with a hole. Expansion is closed-term substitution, so
every `Prop` reaching `Unit` is exactly as ground as it is today and `Lara.Prop`'s
no-binders invariant is untouched. Flat table: a `let` may not refer to another `let`, so
there is no ordering question, no cycle check, and no elaboration fixpoint.

**Bare names, no sigil** (decided). The hazard — a mistyped binding name silently becoming
a nullary `TCon k []` constant, yielding a different well-formed artifact — is what strict
Σ (#89) closes: under a declared signature a mistyped identifier is neither a declared
constant nor a binding, so it is undeclared and rejected. **That protection does not exist
until #89 lands.**

**So #88 splits along the hazard line** (decided). The hazard is confined to *value
bindings in term position*; the other two sub-features cannot be confused with a constant
at all:

| sub-feature | ambiguous with a nullary constant? |
|---|---|
| `nl` interpolation — `"… ({acc_new} vs {acc_base})"` | **No** — inside a string literal; `{name}` is a distinct syntactic position with no term reading |
| value bindings — `score_cell(…, acc_new)` | **Yes** — the entire hazard |

- **#88a — now, on this track:** `nl` interpolation.
- **#88b — after #89 lands:** `let` value bindings, and named premise-slot references
  `(prem e1)`.

> **Named slot refs moved to #88b** (eng review 2026-08-08, 5B). They are safe from the
> constant-confusion hazard, but App. A declares the `cert(…)` payload opaque ("only the
> named backend decodes it"), and a surface `(prem e1)` would be the grammar's first
> statement about payload internals — a layering precedent that deserves its own decision.
> The `comparison` form generates certificates for every current use (S2–S4), so nothing
> on this track needs them; hand-authored certs keep numeric slots until #88b.

This gets the `nl` interpolation that #87 needs without waiting on a core-track effort
that has a spec amendment on its own critical path, and defers only what is genuinely
unsafe. Cost is two PRs and a grammar appendix landing in two pieces.

#### 3.6.1 Interpolating cells, not only bindings

The split has a latent dependency the walkthrough exposed: `{acc_new}` interpolates a
**binding**, and bindings are #88b. Shipped alone, #88a would have nothing to interpolate.

The fix is that interpolation's primary source should be the **evidence leaf**, not a
parallel `let`:

```
claim c1
  nl = "sys_new outperforms sys_base on ImageNet-val accuracy ({cell e2} vs {cell e1})"
```

`{cell e2}` resolves via `premiseCell` on leaf `e2` — the same helper `ord@1` and the
`comparison` form use — rendered back through `renderDecimal`. No binding required, so
**#88a stands alone**.

It is also the *stronger* form for #87's purpose. A number quoted in prose is then
guaranteed to equal the number the cited evidence leaf actually carries, sourced from the
leaf itself. Interpolating a `let` only guarantees agreement with a parallel declaration,
which could itself be wrong. When #88b lands, `{acc_new}` becomes an additional
interpolation source; it does not replace `{cell e2}`.

Preconditions and errors are the same as elsewhere: the named leaf must exist and must
satisfy the premise-cell obligation (exactly one numeric literal), and failure is a
located source error naming the leaf.

**The lexical contract for braces** (eng review 2026-08-08, 4A). `nl` strings currently
have no escapes (`Lara.Syntax`'s `stringLit`, grammar §1.3), so App. B must state one:
inside `nl`, `{{` and `}}` denote literal braces (the f-string/`format!` convention the
Python-literate audience already knows), and **any other `{` must open a recognized
directive** — `{cell <leafid>}` now, `{<binding>}` under #88b — else it is a located error
naming the claim. Strict, not lenient, deliberately: if `{cel e2}` (typo) silently stayed
literal text, a number the author thought was auto-synced would be frozen prose — the
exact silent prose↔formal staleness this feature exists to kill.

**`nl` interpolation is the highest-value part of §3.6.** Without it, bindings harden the
formal side of a claim while the prose silently goes stale — and stale prose *is* a
prose↔formal binding defect, the untrusted author-signed link that #87 audits across 38
load-bearing leaves and that the paper concedes is unchecked by construction. Interpolated
`nl` makes numbers quoted in prose guaranteed to match the formal side, so the feature
**supports** the audit instead of widening what it has to cover. Interpolation is string
substitution in the presentation layer; the resulting `nl` is a plain `String` before
anything downstream sees it.

---

## 4. Paper walkthrough (the validation, run before any code)

#91 §4 makes this the first deliverable, on the argument that prose-level design holes are
cheap to find by hand and expensive to find in code. It worked: **three holes surfaced
here**, each now folded into §3.

### 4.1 `examples/S2` — strict inequality

```
let acc_new  = 0.74
let acc_base = 0.71

claim c1
  nl      = "sys_new outperforms sys_base on ImageNet-val accuracy ({acc_new} vs {acc_base})"
  formal  = better(sys_new, sys_base, accuracy, imagenet_val)
  binding = { author = alice, rationale = "…", audit-status = reviewed }

leaf e1 : reports(exp1, score_cell(sys_base, accuracy, imagenet_val, acc_base))
  kind = observed   provenance = ai-executed   refs = [evidence/tables/accuracy.md#row=sys_base]
leaf e2 : reports(exp1, score_cell(sys_new, accuracy, imagenet_val, acc_new))
  kind = observed   provenance = ai-executed   refs = [evidence/tables/accuracy.md#row=sys_new]
leaf e3 : comparison_setup(sys_new, sys_base, accuracy, imagenet_val, acc_new, acc_base)
  kind = attested   provenance = user          refs = [evidence/tables/accuracy.md#caption]

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

status c1
```

The `claim c2` **declaration** disappears; the claim itself does not (eng review
2026-08-08, T2-A — its authored prose, attestation, and S4's `status c2` all reach `Unit`
and cannot be machine-invented). Its human parts move into the block's `claims` sub-block
and its `formal` is generated. Every `num_lt`, every slot index, and both θ vectors are
gone from the surface.

> **Staging note.** This shows the end state. The `let` block is **#88b**, after #89. Until
> then S2's leaves carry the literals directly and the prose interpolates **cells, not
> bindings** — see §3.6.1, which is what makes #88a independently useful.

### 4.2 `examples/S3` — the `num_le` tie

Identical shape, three lines different: `relation = at-least-as-good`, the conclusion is
`at_least_as_good(sys_new, sys_base)`, and both cells are `0.71`. Under the policy's
`at-least-as-good` scheme this selects `tie_recheck`/`no_worse` and generates
`num_le(0.71, 0.71)`.

> **Hole 1 found here.** The first draft of the `comparison` form had no `relation` field
> and could only generate `num_lt`. S3 was listed as an example to rewrite, which it could
> not have been. → §3.2.

> **Hole 2 found here.** S3 uses different rule names *and a different policy* from S2, so
> a form that generated `beats_recheck`/`beats_baseline` was silently bound to one
> example. → §3.3.

### 4.3 `examples/S4` — the audit that defeats the bridge

S2's body plus the audit leaf and:

```
arg x1 : challenges(e3) by setting_audit(sys_new, sys_base, accuracy, imagenet_val, acc_new, acc_base, aud1)
undermine x1 a2.binding.leaf
```

> **Hole 3 found here.** The first draft gave the `comparison` block a single id, but it
> generates *two* arguments — and S4's attack addresses the bridge by id and position. Both
> ids must be author-declared or every existing attack breaks. → §3.4.

> **Hole 4 found here.** Resolving `a2.binding.leaf` needs the policy's premise labels, but
> `printProgram :: Program -> String` never receives the `Policy`. Without a presentation
> step type the printer cannot round-trip whichever spelling it does not choose. → §3.5,
> which is why grammar §7's "no presentation attack type" has to give.

### 4.4 What the walkthrough confirms

The three examples still differ in exactly one thing each — strictness (S3), and
defeasibility of the binding (S4) — which is what made them readable as a set in the first
place. The new surface preserves that: S2→S3 is one field, S2→S4 is two added
declarations.

---

## 5. Elaboration semantics

All three forms live in the **presentation AST** and expand in `Lara.Elaborate`. They are
*not* macro-expanded in `Lara.Syntax`: `parse ∘ print = id` on the presentation AST is
spec result 12, and expanding at parse time would lose round-tripping for the forms —
repeating the known wart where `open` lines are documented as not losslessly
representable.

```
comparison : better(S,B) on Q @ D            policy
  relation, recheck=a1, bridge=a2,             │
  result=e2, baseline=e1, binding=e3,          ▼
  claims c2 {nl, binding}      ┌─ comparison-scheme[relation × polarity(Q)] → rules
        │                      ├─ measurand[Q] → polarity
        ▼                      │
  ┌─ elaborate ────────────────┤
  │  θ ← match(e1,e2 props     └─ strict rule's premise patterns
  │        vs premise patterns,     │
  │        consistency-checked)     ▼
  ▼
  claim c2   (authored nl/binding, generated formal = goal atom)
  arg a1     (strict: cert(ord@1, <digest>, (ordcmp (prem i) (prem j))))
  arg a2     (defeasible: [goal, e3] ⊢ authored conclusion) ──→ supports c1
```

Expansion of a `comparison`, in order (eng review 2026-08-08: steps amended per 1A, T1-A,
T2-A):

1. look up the measurand's polarity; error if undeclared;
2. resolve the `comparison-scheme` for **(`relation`, polarity)**; error if the policy
   declares no such pair;
3. derive θ by **one-way matching** of the named `result`/`baseline` leaf props against
   the scheme's strict-rule premise patterns, and of the authored conclusion against the
   bridge's conclusion pattern — binding *every* rule parameter, including ones like `Exp`
   that appear in no comparison field. A variable bound twice must agree; disagreement is
   a located error naming the leaves and the conflicting binding. The premise-cell
   obligation (exactly one numeric literal, via `premiseCell` — extraction only, never its
   backend-worded error string) is checked on `result` and `baseline` here;
4. emit the sub-claim declared by `claims`: authored `nl` and `binding`, **generated
   `formal`** — the goal atom, the scheme's strict-rule conclusion pattern under θ;
5. emit the `recheck` argument: an instance of the scheme's strict rule under θ, and
   `assurance = cert(ord@1, <digest>, (ordcmp (prem i) (prem j)))` with `i`/`j` the
   **0-based** slots the named leaves occupy in that rule's premise list;
6. emit the `bridge` argument: an instance of the scheme's defeasible rule over the
   generated comparison and the named binding leaf, concluding the authored atom.

**Ordering across blocks** (eng review 2026-08-08, F5): all `comparison` blocks expand
before any attack path resolves, so an `undermine` targeting a generated argument (or a
label inside one) resolves against the post-expansion argument set.

**Index basis** (eng review 2026-08-08, 6A): attack-path integers, `(prem i)` slots, and
premise-label resolution are all **0-based**. 1-based indices appear only in human-facing
error text (`resolvePremises` zips `[1..]` today), converted at the message boundary —
never in a generated certificate or a resolved `Step`.

**Generating certificates adds no trust.** Replay re-checks the certificate against the
goal and the premises, so a wrongly generated certificate is an R13 rejection, never a
false accept. The elaborator is a convenience whose output is independently verified —
the same argument shape as the golden equality in §7.

**The binding leaf is never generated.** `comparison_setup` is attested evidence carrying
an author, a provenance tag, and `refs`. If the block synthesized it, the sugar would
manufacture evidence nobody attested, and the thing S4 attacks would become something the
compiler invented. `binding = e3` names an existing leaf; that one line stays a human
claim.

---

## 6. Decisions

### 6.1 Taken (2026-08-08)

| # | Decision | Chosen |
|---|---|---|
| 1 | Where sort checking lives | Checker stage, real R2 — **#89, core track, not this plan** |
| 2 | Vocabulary discipline | Strict |
| 3 | Binding syntax | **Bare names**, no sigil, plus `nl` interpolation |
| 4 | Timing vs. PLDI (#60) | **Design note now, code after** — this document is the deliverable |
| 5 | `lara-core@0.2` migration | Hard cutover (#89 concern; no impact here) |
| 6 | #88 sequencing | **Split along the hazard line** — #88a (`nl` interpolation) now; #88b (`let` bindings, named slot refs) after #89. §3.6 *(amended 2026-08-08: slot refs moved to #88b, 5B)* |
| 7 | Symbolic attack positions | **In scope, sequenced last** as a detachable tail. Labelled premises, bare names, disjointness + `rule`/`leaf` reservation enforced as policy WF. §3.5 |

### 6.1.1 Eng review decisions (2026-08-08)

| id | Decision |
|---|---|
| 1A | θ for generated arguments derived by one-way matching of named leaves against premise patterns, consistency-checked (§5) |
| 2A | D5 is an **additive** surface-context line above the unchanged, byte-pinned kernel rejection; `.lara` door only |
| 3C | New deliverable **D8**: after D6 freezes the forms, port them (plus the stale 0.2/`groupMode` backlog) to `lean/Lara/Presentation.lean`, extend result 12, fix its scope header |
| 4A | `nl` braces: strict directives, `{{`/`}}` escapes (§3.6.1) |
| 5B | Named slot refs `(prem e1)` deferred to #88b (§3.6) |
| 6A | Index basis documented 0-based with a regression test (§5, §8) |
| 7A | Surface cell-obligation failures are dedicated `ElabError`s; `premiseCell` reused for extraction only |
| 8A | Five error cases added to §8 (id collision, duplicate blocks, conclusion↔claim mismatch, result=baseline, measurand consistency) |
| 9A | Generators extended with cover assertions; raw-directive printing golden; diagnostics golden (§8) |
| T1-A | Schemes keyed by (relation × polarity); D6 gains a `lower-is-better` example (§3.3) |
| T2-A | The block declares the sub-claim (`claims` sub-block); only its `formal` is generated (§3.2) |
| T3-B | θ-matching-on-plain-`arg` baseline documented in §2 and captured in TODOS.md |
| F4 | Bridge conclusion convention (4-ary, favored system first) is scheme WF; richer shapes are a §9 non-goal |
| F5 | `rule`/`leaf` reserved from premise labels; comparison expansion precedes attack resolution |
| F6 | Same-`Exp` constraint documented as inherited from the scheme's rules (§3.3) |
| F7 | `measurand`'s `: Num` slot is a sort position; #89 extends this declaration (§3.1) |

### 6.2 Resolved (2026-08-08)

- **Grammar §7 amendment sign-off** (§3.5). ~~Open.~~ **Signed off 2026-08-08.** A
  presentation-level attack step is required — the printer cannot see the policy — which
  contradicts §7's "adds **no** presentation attack type". Strictly additive and it moves
  no Unit-reachable type, but §7 is marked FROZEN, so it needed the same sign-off
  discipline as #89's R2 amendment. The amendment text is now appended to §7 of
  `docs/lara-surface-grammar.md`, and §3.5 shipped rather than detaching: `SurfaceStep` is
  in the presentation AST, `undermine x1 a2.binding.leaf` is what `examples/S4` now writes,
  and `a2.binding.leaf == a2.1.leaf` is a test.

### 6.3 Not decided here

The R2 spec amendment (#89 §7) is on the critical path for the *core* track and needs its
own sign-off. It does not gate anything in this plan.

---

## 7. Deliverables

Grouped by ship unit. **#90 + #88a land together on this track; #88b waits on #89.**

**D1 — grammar.** `docs/lara-surface-grammar.md` App. B for `lara-syntax@0.3`:
`measurand`, `comparison-scheme`, `comparison`, labelled rule premises, the attack-path
name segment, and `nl` interpolation. Plus the §7 amendment text (§6.2) for sign-off.

**D2 — presentation AST.** `src/Lara/AST.hs`: measurand table, (relation × polarity)
schemes, and premise labels on `Policy`; `comparison` decl (with its `claims` sub-block)
on `Program`; `SurfaceStep = StepIndex Int | StepName String` and the presentation attack
carrying it (§3.5). Note the construction-site churn: `Examples.hs`, `Negatives.hs`,
`ClaimSupport.hs`, `MechReview.hs` and their specs all match on `Decl`, and a new arm
forces `-Wall` fixes (the A0.5 precedent touched 13 sites).

**D3 — parser/printer.** `src/Lara/Syntax.hs`. A `comparison` **round-trips as a
`comparison`**, never as its expansion; an attack round-trips in the spelling it was
written in; `nl` directives and `{{` escapes round-trip **raw**, never expanded.

**D4 — elaboration.** `src/Lara/Elaborate/Internal.hs`: the expansion in §5 (θ-matching,
sub-claim emission), (relation × polarity) scheme resolution, polarity lookup, `{cell l}`
interpolation, attack-step name resolution, the premise-label WF checks (question-id
disjointness, `rule`/`leaf` reservation), and the located errors in §8 — all as dedicated
`ElabError` constructors (7A), never surfaced kernel strings.

**D5 — diagnostics.** *(Amended 2026-08-08, 2A — not `Reporting.hs`, which never sees
backend rejections; the kernel string lives in `Strict/Ord.hs` and is byte-pinned by
`CliSpec` and `docs/rejection-surface.md`.)* A new author-facing layer above
`sourceResultDiagnostics`/the driver's located-rejection path: on the `.lara` door only,
prepend a surface-context line naming the authored `comparison`, its result, baseline, and
measurand — **above the unchanged kernel line**. Requires a provenance breadcrumb from
elaboration mapping generated arguments back to their block. The `.sexp` door is
byte-unchanged; all existing pins hold.

**D6 — examples.** `examples/S2`, `S3`, `S4` rewritten per §4; their policies gain
schemes (keyed by relation × polarity), measurands, and premise labels. Plus a small
**`lower-is-better` example** (e.g. perplexity) so §8's polarity test executes (T1-A), and
the worked-example list deduplicated between `scripts/gen-worked-examples.hs` and
`test/WorkedExamplesSpec.hs` (one shared source — eng review, D16.1).

**D7 — #88b, after #89.** `let` bindings, bare names, `{acc_new}` as a second
interpolation source, and named premise-slot refs `(prem e1)` (5B).

**D8 — Lean presentation port.** *(Added 2026-08-08, 3C.)* After D6's byte-identity
acceptance passes — the forms are then frozen — port the new constructs **plus the stale
backlog** (`theories`, `groupMode`, `DeclGroup`) to `lean/Lara/Presentation.lean`, extend
result 12 (`parse_printProgram`/`parse_printPolicy`) over them, and fix the `:38-40` scope
header, which today claims field-for-field parity it does not have. `AxCheck` stays clean.

Order: D1 → D2/D3 → D4 → D6 → D5 → §3.5 tail → D8, then D7 later. D6 is the acceptance
test for D1–D4.

---

## 8. Verification

**The expansion invariant is the whole review surface.** For S2, S3, and S4, the new
source must elaborate to a `Unit` **byte-identical** to the one today's hand-written
source produces. Not equivalent — identical. One golden test per example.

Also:

- `parse ∘ print = id` extended over programs carrying all three new forms — which
  requires **extending the QuickCheck generators** (`genPolicy`, `genRule`, `genProgram`,
  `genAttack`, `genDecl` in `test/SyntaxSpec.hs`) with arms for every new form, plus a
  QuickCheck `cover`/`label` assertion that generated programs actually include each one
  (9A — without it the extended property passes vacuously);
- a committed **raw-directive golden**: a program carrying `{cell …}` directives and
  `{{`/`}}` escapes round-trips **raw** through the printer, and its elaborated `Unit`
  carries the **expanded** `nl` (9A);
- **polarity test:** the same source under a `lower-is-better` measurand (the new D6
  example's policy) emits the flipped goal via that policy's `lower-is-better` scheme, and
  the flipped goal is what `ord@1` accepts;
- **relation test:** `at-least-as-good` reproduces S3's `num_le` unit exactly;
- **S4 still defeats the bridge** while the comparison stays justified — the generated
  structure is attackable at exactly the same point;
- **attack-path equivalence:** `undermine x1 a2.binding.leaf` and `undermine x1 a2.1.leaf`
  elaborate to the same `Undermine … [StepPremise 1]`, and each round-trips in its own
  spelling — this doubles as the **0-based index regression test** (6A), cross-checked
  against the generated cert's `(prem i)` slots;
- **θ-consistency negatives** (1A): a leaf that fails to match its premise pattern, and a
  pair of leaves binding a shared variable (e.g. `Exp`) inconsistently — each a located
  error naming the leaves;
- **diagnostics golden** (9A/2A): a CliSpec-style golden asserting the surface-context
  line appears above the unchanged kernel line on the `.lara` door, and that `.sexp`-door
  output is byte-unchanged;
- located source errors for: no matching `comparison-scheme` for the (relation, polarity)
  pair; ill-formed scheme (recheck not strict, no `ord@1` certifier, bridge not
  defeasible, conclusion pattern mismatch, bridge conclusion not 4-ary favored-first);
  undeclared measurand; `binding` naming a non-leaf; `result`/`baseline` leaf failing the
  premise-cell obligation; **`result` and `baseline` naming the same leaf** (8A);
  **generated id collisions** — `recheck`/`bridge`/`claims` id colliding with a declared
  decl or with each other (8A/T2-A); **duplicate or overlapping `comparison` blocks**
  (8A); **authored conclusion vs. supported claim's `formal` mismatch** (8A — verify
  whether existing arg/claim checks already fire on generated args, else add);
  **measurand/`on`-field consistency** (8A — falls out of θ-matching, named so the test
  exists); an attack-path name matching no premise label or question id; a premise label
  colliding with a question id of the same rule or spelling `rule`/`leaf` (policy WF, F5);
  an unknown `{…}` directive or unterminated brace in `nl` (4A); a `{cell l}`
  interpolation naming a non-leaf or a leaf failing the premise-cell obligation; and — with
  D7 — unbound or duplicate `let`, and a binding name colliding with a declared id;
- full `cabal test all` green; existing differential pins unchanged.

`corpus-units/` is untouched, so `m5-freeze-checklist.md` row 2 does not move,
`measurements/frozen/` stays valid, and there is no new freeze tag.

---

## 9. Non-goals

- **Changing the `ord@1` family.** Two predicates over two numerals; `lean/Lara/Ord.lean`
  untouched. A backend must certify something decidable over ground literals, and
  `outperforms` is not — it depends on the binding and the polarity, which are evidence
  and policy. Making the comparative claim the strict goal would certify the interpretive
  step, which is exactly what must stay attackable, and would lose the intra-family
  exclusivity theorem that lets the family declare no contraries.
- **Sorts, in any form.** #89, core track.
- **Measurand-indexed numeric sorts** (`Num[accuracy @ imagenet_val]`). Would make
  comparing an accuracy against a BLEU score a sort error — attractive, but it is a
  units-of-measure design that starts eating `comparison_setup`'s job and moves something
  currently *attackable* into something *statically rejected*. Likely adjacent to the
  possible-worlds direction.
- **Richer bridge conclusion shapes** (eng review 2026-08-08, F4). The `comparison` form
  targets bridges concluding a 4-ary `pred(S, B, Q, D)` with the favored system first —
  checked as scheme WF. A bridge with an extra parameter (e.g. an evaluation-setting slot,
  the possible-worlds direction) is inexpressible through this form for now; that
  generalization rides with the possible-worlds work, not this track.
- **Corpus work of any kind.**
- **Evaluating whether agents author better artifacts with this surface.** That is axis
  (b)/(d) work for the ACL/EMNLP follow-up, not this plan and not the current draft.

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | `/codex review` | Independent 2nd opinion | 0 | — | — |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | ISSUES FOLDED (PLAN) | 16 issues, 0 critical gaps — all 16 resolved and folded into this document (2026-08-08) |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | — |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | — |

- **CROSS-MODEL:** Outside voice (Claude subagent; Codex timed out) found 3 substantive
  misses beyond the primary review — polarity unimplementable via relation-only schemes
  (→ T1-A), the sub-claim cannot vanish under byte-identity (→ T2-A), and the missing
  justification against the θ-matching-on-plain-args baseline (→ T3-B) — plus 4 accepted
  documentation-level findings (F4–F7). All folded; decisions recorded in §6.1.1.
- **VERDICT:** ENG REVIEW COMPLETE — all 16 findings resolved; D1–D6 + D8 are ready to
  implement now. The §3.5 tail alone waits on the grammar §7 amendment sign-off (§6.2).

**UNRESOLVED DECISIONS:** none. The one open item — the grammar §7 amendment sign-off
(§6.2) — was signed off 2026-08-08 and §3.5 shipped with the rest of the track rather than
detaching.

## IMPLEMENTATION STATUS (2026-08-08)

Implemented on `lara-syntax-03-design`. D1–D6, D8, and the §3.5 tail all landed; **D7
(#88b — `let` bindings, named slot refs `(prem e1)`) remains deferred behind #89**, as
designed.

| Deliverable | Commit |
|---|---|
| D1 — grammar App. B + §7 amendment | `637d769` |
| D8+ — Lean direction-of-goodness contract | `ca78131` |
| D2/D3 — presentation AST + parser/printer | `30773d1` |
| D4 — elaboration (expansion, interpolation, name resolution) | `d103987` |
| D8 — Lean presentation port + result 12 | `3cb391f` |
| D6 — examples rewritten + §3.5 tail | `2045ef9` |
| D5 — author-facing surface diagnostics | `424a3a6` |

**§8's acceptance criterion holds.** `examples/S{2,3,4}/example.core.sexp` and
`expected.json` are byte-identical to `main` while all three `.lara` sources were rewritten
onto the `comparison` form (+137/−62). Three tests assert identity, not equivalence.

Two findings the plan did not anticipate, both recorded in the commits:

1. **§3.5's premise labels collided with a frozen type.** `rulePremises :: [AtomPat]` is on
   `Rule`, which is copied verbatim into `unitRules`, so labels could not change its type.
   They landed as a parallel `rulePremiseLabels :: [Maybe PremiseLabel]`; `Wire.encodeRule`
   enumerates its eight encoded fields explicitly, so the new field is structurally unable
   to move a wire byte.
2. **Result 12 had been proved over a smaller language than the parser accepts.**
   `Presentation.lean`'s scope header claimed field-for-field parity from M4a onward while
   `policyTheories`, `policyGroupMode`, `GroupConflictMode`, `GroupId`/`DupGroup`, and the
   `DeclGroup` arm were never ported. D8 closed that backlog alongside the `@0.3` work;
   `Policy` went 5→9 fields and `Decl` 5→7 arms.

On D8+: the literal "expansion is deterministic given (scheme, polarity, θ)" invariant is
**not reachable** — `Lara.Presentation` is a closed island, nothing maps
`Presentation.Program → Unit`, and Lean's entry point is the wire decoder on an
already-elaborated `.sexp`. What is mechanized instead is §1.2's direction-of-goodness
contract over the frozen `Cell`/`Ord` layer. The elaborator itself stays
validated-not-verified, exactly as the `.lara` parser already was.

---

## Post-review amendment (2026-08-09) — the direction-of-goodness check

Code review on PR #92 found that §3.2's and §3.3's welding argument, as written above,
covers only half the space. The claim "the generated goal's argument order and the rules
that consume it cannot disagree" is true of the *rules relative to each other* — shared
variables do weld the recheck conclusion to the bridge's `cmp` premise — but neither rule
was welded to the declared `polarity`. `polarity` was read once, to select a scheme
(`Elaborate/Comparison.hs`), and never used again.

The consequence was a working repro: flipping the recheck conclusion **and** the bridge's
`cmp` premise together, leaving `measurand accuracy : Num where higher-is-better` and
`comparison-scheme strictly-better higher-is-better` untouched, produced an internally
consistent and externally backwards policy. A system scoring 0.71 against a 0.74 baseline
certified `better(sys_new, sys_base)` as `justified`, exit 0 — verbatim §1.2's hazard,
reachable through a mis-written policy rather than a mis-written artifact.

**Resolution: the check was added, not the claims weakened.** A fifth scheme
well-formedness obligation now sits in `expandComparison` between slot attribution and
certificate formation: the goal's two operands, attributed to `result`/`baseline` by the
provenance rule §5 already uses, must be in the order the declared polarity means —
`rel(base, ours)` for `higher-is-better`, `rel(ours, base)` for `lower-is-better`, i.e.
exactly §3.2's table. The new `ComparisonSchemeDirectionMismatch` locates the rejection at
the scheme. All four shipped policies (S2, S3, S4, S5) pass unchanged, and the acceptance
criterion is untouched: the six `examples/S{2,3,4}` goldens stay byte-identical to `main`.

The effect on the mechanization is the part worth recording. `Lara.Comparison.goalOf`
*computes* this table from the polarity; the Haskell previously did not, so
`goalOf_iff_better` and `goalOf_polarity_mismatch_excl` were true of a model the shipped
elaborator was not held to. They are now true of a table the elaborator checks itself
against. That is still a check in Haskell, not a proof about Haskell — the elaborator
remains validated-not-verified — but the two sides can no longer disagree silently.

Two documentation consequences, both applied: the three places that asserted the
unenforced property (grammar App. B.2 and B.3, `examples/S2/ord-v1.policy.lara`) now
distinguish what the welding gives from what the check gives, and B.2's enumerated
well-formedness list carries the new obligation as a fifth bullet rather than leaving it
implied by surrounding prose.

---

## Post-review amendment (2026-08-09) — `claim nl` brace migration

Round-two review on PR #92 found that this plan's original additivity premise no longer
held after B.6's brace contract was widened from a `comparison` block's nested claim to
every claim-form `nl`. `lara-syntax@0.2` allowed a bare `{` or `}` in an ordinary claim;
`@0.3` reserves those characters for directives and requires literal braces to be written
as `{{` and `}}`. The surface grammar therefore has one source-compatibility migration,
even though the presentation expansion, `Unit`, wire codec, checker, and backends remain
additive.

**Resolution: record the migration rather than narrow B.6 again.** The strict contract
prevents `{cell ...}` typos from behaving differently between ordinary and comparison
claims. `corpus-units/lbcs/C05` and `corpus-units/sapg/C06` were migrated by doubling
their literal braces. Their rendered mechanical-review output remains byte-identical,
`nl` still never enters `Unit`, and the six `examples/S{2,3,4}` core/verdict goldens
remain byte-identical to `main`. Appendix B's heading and preamble now state the
exception and the exact `{` → `{{` / `}` → `}}` migration.
