# Concepts

## Claim-support term
- **Notation**: `w ::= leaf l | r⟨θ ; w₁,…,wₙ ; {q ↦ w_q} ; {o*} ; assurance⟩`
- **Definition**: The single syntactic category of arguments. A term is either an evidence leaf or an
  instance of a policy rule `r` carrying its ground substitution `θ`, its premise terms, a discharge
  map from critical questions to discharging terms, its explicitly open obligations, and an assurance
  marker. Strict vs defeasible is a *mode* of the rule looked up in the policy, not separate syntax; a
  strict instance is the degenerate case (empty critical-question map, no holes).
- **Boundary conditions**: The main source judgment `Σ; Π; Γ; R ⊢ w : supports(p) ▷ O` records open
  obligations `O` only; the dependency set is derived as `leaves(w)`, not tracked.
- **Related concepts**: Support judgment, Leaf, Inference scheme, Assurance

## Proposition normal form (`nf`) and identity (`≡`)
- **Notation**: `p ≡ q  iff  nf(p) = nf(q)`
- **Definition**: `nf` is literal canonicalization (`canon`) plus structural recursion over ground
  first-order atoms; `≡` is syntactic equality of normal forms. `canon` normalizes numeric literals,
  string escaping, and (as a documented extension) Unicode NFC — but does NOT reorder arguments, so no
  predicate/constructor is associative, commutative, or symmetric in v0.1.
- **Boundary conditions**: Decidable, total, reflexive, symmetric, transitive, linear in term size.
  The trusted-base equality for the `supports` check and `contrary` matching. Flip criterion: add
  argument sorting (AC symbols) / de Bruijn indexing (binders) if the corpus needs them.
- **Related concepts**: Claim-support term, `supports` relation, Trusted base

## `supports` relation (positional identity)
- **Notation**: `w supports c  iff  concl(w) ≡ c.formal`
- **Definition**: An argument supports a claim exactly when its normalized conclusion is identical to
  the claim's formal target. There is no entailment step and no solver in the trusted base — support
  is positional identity, as in AIF inference nodes and the theorem-is-the-object convention of proof
  assistants.
- **Boundary conditions**: The NL↔formal `binding` of the claim is never a checker obligation; it is a
  versioned, human-signed audit field evaluated on the semantic-faithfulness axis, never proven.
- **Related concepts**: Claim, Proposition normal form, Semantic faithfulness

## Claim (nl / formal / binding triple)
- **Notation**: `claim c { nl = "…"; formal = atom; binding = {author, rationale, audit-status} }`
- **Definition**: A claim is a natural-language string, a formal target proposition, and an *untrusted*
  binding between them. `nl` is the human-facing text; `formal` is the checkable target; `binding` is
  the audited, human-signed correspondence.
- **Boundary conditions**: `binding` is the single most load-bearing unchecked step; it is evaluated,
  never proven.
- **Related concepts**: `supports` relation, Semantic faithfulness

## Leaf and leaf admission
- **Notation**: `leaf l : prop` with `kind ∈ {observed, attested, assumed, certified}`, `provenance ∈
  {user, ai-executed, checker(name,version)}`
- **Definition**: An evidence leaf is an untrusted hypothesis bound to source references. Admission is
  a total policy map over (kind × provenance) → {admit, quarantine, reject}, applied *before* argument
  evaluation. A quarantined leaf stays out of the context and produces a `gap`; admission never
  creates an attack.
- **Boundary conditions**: A `certified` leaf additionally needs a checker witness listed in the
  policy and a replayable reference; provenance is not an attack.
- **Related concepts**: Claim-support term, Provenance, Trusted base

## Inference scheme (strict / defeasible rule)
- **Notation**: `rule r(X₁,…,Xₘ) { mode = strict|defeasible; premises = […]; conclusion = …;
  question q : Apat (mandatory|optional) }`
- **Definition**: A named, versioned, policy-defined inference pattern. Strict schemes are deductive;
  defeasible schemes give presumptive support and list critical questions that must be discharged or
  explicitly left open. Artifact programs instantiate schemes but may not define or modify them.
- **Boundary conditions**: A strict rule is well-formed only if `allow-trusted = true` or it lists at
  least one backend certifier; defeasible rules always use `assurance = none`.
- **Related concepts**: Critical-question obligation, Contrary relation, Assurance, Policy

## Critical-question obligation and hole
- **Notation**: `discharge q with w_q` | `open q as o`
- **Definition**: Each scheme question is discharged by a support term (checked against the question's
  answer pattern) or declared an explicit open hole. An open *mandatory* question contributes a located
  obligation that excludes the incomplete argument from the framework and yields a `gap`; an open
  *optional* question is a diagnostic only. Every declared question must be accounted for.
- **Boundary conditions**: "Complete" means policy-relative: all premises and critical questions of an
  instantiated scheme are discharged or reported as holes. Not mechanical completeness of a scientific
  argument.
- **Related concepts**: Inference scheme, `gap` status, Exception

## Backend-parametric strict-certificate interface
- **Notation**: `check_β : Theory_β → List Form_β → Form_β → Cert_β → accept | reject(error)`
- **Definition**: The one seam for strict deductive steps. A registered backend supplies `encode`,
  `check`, `uses`, and a semantics `models`, and must discharge six obligations (decidable replay,
  normalization fidelity, certificate soundness, dependency accountability, closed registration,
  structural consequence laws). The source calculus knows none of a backend's formulas, proof terms,
  axioms, or model theory.
- **Boundary conditions**: The backend receives only normalized proposition encodings and returns only
  accept/reject + dependencies + diagnostics (the factivity firewall). A non-monotonic reasoner is not
  a strict backend.
- **Related concepts**: Natural-deduction reference adapter, Backend replacement, Assurance, Non-factivity

## Natural-deduction reference adapter
- **Notation**: `φ ::= a | false | φ → φ`; `e ::= hyp i | lam φ e | app e e | abort φ e`
- **Definition**: The required v0.1 reference backend: intuitionistic natural deduction for implication
  and falsum, certificates using de Bruijn indices. Sound (by induction on the typing derivation) but
  intentionally not complete; encodes a source proposition as `atom(canonicalSerialize(nf(p)))`.
- **Boundary conditions**: Certifies only the propositional consequences visible in its encoding and
  declared theory; a non-logical domain law stays a reported theory dependency or trusted policy rule.
- **Related concepts**: Backend-parametric strict interface, Dependency accountability

## Typed positional attack (rebut / undercut / undermine)
- **Notation**: `k ::= rebut w u | undercut w u@π | undermine w u@π`; `π ::= ε | π.i | π.q`
- **Definition**: An attack addresses a position in a support term. Rebut targets a defeasible root
  conclusion (a declared contrary of it); undercut targets a defeasible rule occurrence (a declared
  exception of it); undermine targets a leaf occurrence (a contrary of the leaf's proposition). The
  three attack kinds are exactly the three position kinds.
- **Boundary conditions**: Strict rules cannot be undercut or rebutted. A dead end creates an attack
  only if it constructs one of these typed forms; provenance/confidence alone is not an attack.
- **Related concepts**: Contrary relation, Exception, Claim-support term, Compilation

## Grounded four-state claim status
- **Notation**: `justified | gap | defeated | contested`
- **Definition**: After compiling to a finite Dung framework and computing the grounded labelling
  (in/out/undec) as a least fixed point, a claim is `gap` if it has no complete support or an
  unresolved obligation, `justified` if some support is `in`, `contested` if none is `in` and some is
  `undec`, `defeated` if all its supports are `out`.
- **Boundary conditions**: `contested` = grounded `undec`, broader than mutual defeat; the report must
  name the responsible SCC. Deterministic and terminating because `Args` is finite.
- **Related concepts**: Compilation, Non-monotonic acceptance, Typed positional attack

## Backend replacement
- **Notation**: `compile(P_β) ≅ compile(P_γ)` ⟹ equal claim statuses
- **Definition**: The theorem that source-identical programs whose backends accept exactly the same
  strict instances compile (after certificate erasure) to isomorphic argumentation frameworks and
  yield equal four-state statuses — so claim-status semantics is independent of certificate internals.
- **Boundary conditions**: Backend identity, theory, dependencies, and certificate size remain visible
  in audit reports; only *status* is invariant. The formal reason no single logic is foundational.
- **Related concepts**: Backend-parametric strict interface, Grounded four-state status
