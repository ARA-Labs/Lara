# The claim-support calculus

_The frozen core of LARA v0.1 (source of truth: `docs/spec.md` §1–§8, settled by
`docs/claim-support-calculus-decision.md`). One support-term language; strict/defeasible is a rule
mode; strict certificates are opaque backend payloads; attacks are positional._

## 1. Scope and guarantee

A program declares artifact-scoped propositions and evidence leaves, instances of strict or defeasible
inference schemes, obligations those instances generate, typed rebut/undercut/undermine relations, and
claim roots whose status is requested. The checker validates a submitted certificate; it does not
establish empirical truth and does not search for every possible argument. Acceptance means: references
and types are well-formed; strict certificates check through fixed/versioned backends and scheme
instances check against fixed/versioned schemas; every dependency and open obligation is explicit;
every attack has a checked source and type-correct target; and the reported status is the grounded
result for the compiled graph. "Complete" is policy-relative.

A program is checked against a fixed proposition signature `Σ`, a versioned policy `Π`, a fixed
strict-backend registry `R`, and an artifact snapshot `A`. JSON is the producer/checker wire encoding;
a presentation syntax is the paper/debugging language; both decode to one abstract syntax.

## 2. Propositions and the identity relation

Propositions are ground first-order atoms over a fixed vocabulary in `Σ` (`atom ::= pred(g₁,…,gₙ)`;
the nullary case is the Phase-0 opaque identifier). Support-level propositions are atomic — conflict
comes from the declared `contrary` relation, not negation-to-falsum, and an implication `E → C` is
reified as a named rule, not asserted as a proposition.

The normal form `nf` is literal canonicalization (`canon`) plus structural recursion; `p ≡ q iff
nf(p) = nf(q)`. `canon` normalizes numeric literals, string escaping, and (as a documented extension)
Unicode NFC, and does NOT reorder arguments — no predicate is AC or symmetric in v0.1. `≡` is
decidable, total, an equivalence, and linear in term size. **Implemented and property-tested** in
`Lara.Prop` (see `src/execution/Prop.hs`, C01).

### The `supports` relation

A claim is a triple `{nl, formal, binding}`. `w supports c iff concl(w) ≡ c.formal` — support is
positional identity, no entailment, no solver in the trusted base. `c.binding` (the NL↔formal
correspondence) is never a checker obligation; it is a versioned, human-signed audit field.

## 3. Policies, schemes, obligations

A policy `Π` defines named inference schemes with a `mode` (strict|defeasible), premise/conclusion
patterns, and — for defeasible schemes — critical questions (mandatory by default). It also declares
the `contrary` relation (the only source of propositional conflict, closed under ground instantiation)
and `exception` conditions (undercutting licenses). Policies are versioned trusted inputs; artifact
programs instantiate but never define or modify rules.

Instances are always ground: the abstract syntax and JSON carry the substitution `θ` explicitly, so
instance checking is substitution application plus syntactic identity (no unification in the trusted
checker). Each declared critical question is either discharged by a support term or declared an
explicit open hole; an open mandatory hole excludes the incomplete argument from the framework and
yields a `gap`.
The reviewed source contract applies leaf admission before core evaluation as a total policy map over
`(kind × provenance)`, defaulting unmatched rows to `admit`. `reject` produces source rejection R8
without a checked unit. `quarantine` removes the leaf, every argument whose transitive support uses it,
and every attack with a removed endpoint. Duplicate-report groups are still evaluated against declared
leaves; their quarantine seed is then unioned with the policy seed to construct the final checked
context. Admission creates neither attacks nor a fifth core status; conservative source reporting may
publish `evidence-blocked` for affected roots while retaining any conditional core diagnostic. The
runtime contract and compatibility boundary are fixed in
`docs/policy-admission-calculus-decision.md`.

## 4. Support terms and dependencies

One category: `w ::= leaf l | r⟨θ ; w₁,…,wₙ ; {q ↦ w_q} ; {o*} ; assurance⟩`, `assurance ∈ {none,
trusted, cert(β, theory-digest, κ)}`. The source judgment `Σ; Π; Γ; R ⊢ w : supports(p) ▷ O` records
open obligations `O` only. The dependency set is derived: `leaves(w)` (the leaf constants in `w`, each
declared in `Γ`), with strict-certificate dependencies reported separately as `certDeps(w)`. The
former accountability theorem is thus an inversion lemma (C08). Multiple independent supports for one
claim are separate `arg` declarations — never merged — so defeat can eliminate one while another
survives.

## 5. Typed positional attacks

A position `π ::= ε | π.i | π.q` is a path of premise indices and question names; `w@π` is the subterm
at `π`. The three attack kinds are the three position kinds (C02):
- `rebut w u` — targets `u`'s defeasible root conclusion; `(concl(w), concl(u))` is a declared
  contrary pair.
- `undercut w u@π` — targets a defeasible rule occurrence; `w` concludes `E θ` for a declared
  `exception r : E`.
- `undermine w u@π` — targets a leaf occurrence; `w` concludes a declared contrary of the leaf's
  proposition.

Strict rules cannot be undercut or rebutted (ASPIC+: strict inferences are unattackable). Attack
checking is subterm-occurrence checking + a contrary-relation lookup: decidable, local, and the
position doubles as the diagnostic source location. A dead end creates an attack only if it constructs
one of these typed forms.

## 6. Compilation and grounded four-state status

A well-formed program compiles to a finite Dung framework `AF = (Args, Attack)`. `Args` are complete
checked support terms; `Attack` is exactly the compiled typed attacks, closed under subarguments (an
attack on `u@π` compiles to edges onto every argument containing the attacked occurrence). The grounded
labelling (least fixed point of Dung's monotone characteristic function from ∅, stabilizing in ≤ |Args|
steps) maps each argument to in/out/undec. Claim status:

```
gap       if support(P,p) is empty, or a mandatory root obligation is open with no complete alternative
justified if some support argument is labelled in
contested if none is in and some is undec
defeated  if supports exist and every one is out
```

**Two definitional points remain open** (must close before M1 freeze; see
`docs/mechanization-plan.md` §5): the hole-vs-complete-alternative case (spec §8, self-flagged), and
`contested`-SCC provenance reporting. LARA is non-monotonic at the consequence level across framework
extensions (C06), while the internal transfer operator is monotone over a finite-height lattice (C07).

## 7. Consistency (§8.1, Path B)

v0.1 imposes a compile-time well-formedness check: no strict-rule consequent, and no proposition
reachable on a strict chain, may participate in a declared `contrary` pair. Under this restriction
every conflict is rebuttable at a defeasible step, so direct = indirect consistency hold by
construction and two contrary claims are never jointly `justified` (C09). Flip criterion: Path A (a
total involutive contradictory map + transposition closure) if the corpus shows strict rules genuinely
feeding contested claims.
