# Strict-certificate backend decision

_Status: settled for language v0.1. Recorded 2026-07-21. This decision supersedes the
LP-specific strict-witness interface in `spec.md` Section 5, `term-calculus-decision.md`, and
`gap-resolution.md`. LP remains an optional adapter; it is no longer a foundation of the source
calculus._

## 1. Decision

The source language has one warrant-term calculus and one small seam for strict certificates. A
strict rule instance may carry an opaque certificate checked by a registered backend. The warrant
calculus knows neither the backend's proof-term grammar nor its axioms.

This replaces

```text
Sigma_LP ; { x_i : P_i theta } |- d => t : C theta
```

with

```text
strictCheck(beta, T, [P_1 theta, ..., P_n theta], C theta, kappa) = accept
```

where `beta` is a fixed backend identifier and version, `T` is a digest-addressed backend theory,
and `kappa` is an opaque certificate. Programs may select registered backends and theories but may
not define either at runtime.

The source-level meaning is deliberately narrow:

- a successful check discharges the *deductive validity* of this strict step, conditional on its
  premise conclusions and the declared theory;
- it does not establish that the premise warrants are true;
- it does not expose a backend formula or proof term to the warrant language; and
- it does not change attack or status semantics.

An unwitnessed strict rule remains permitted as an explicitly trusted policy rule. Reports must
distinguish `certified(beta, theory-digest)` from `trusted-policy`; only the first receives the
backend-soundness guarantee.

## 2. Abstract strict-certificate system

A registered backend `B_beta` consists of:

```text
Form_beta                         backend formulas
Cert_beta                         serialized certificates
Theory_beta                       finite, versioned background theories

encode_beta : prop -> Form_beta
check_beta  : Theory_beta
              -> List Form_beta   -- premise conclusions
              -> Form_beta        -- goal
              -> Cert_beta
              -> accept | reject(error)

uses_beta   : Cert_beta -> Set Dependency
models_beta : Theory_beta -> List Form_beta -> Form_beta -> Prop
```

`models_beta(T, Delta, phi)` is written `T ; Delta |=_beta phi`. It is a mathematical semantics used
to state soundness; it need not be executable. `Dependency` names free premise slots and entries in
`T`. Locally introduced and discharged assumptions are not dependencies.

Every registered backend must establish these obligations:

1. **Decidable replay.** `check_beta` is total, deterministic, and terminating on finite input.
2. **Normalization fidelity.**

   ```text
   p equiv q    iff    encode_beta(p) = encode_beta(q)
   ```

   The forward direction preserves source identity; the reverse direction prevents an encoder from
   silently collapsing distinct propositions. Stronger semantic equivalences must be proved through
   an explicit backend theory/certificate.
3. **Certificate soundness.**

   ```text
   check_beta(T, Delta, phi, kappa) = accept
   ------------------------------------------------
                    T ; Delta |=_beta phi
   ```

4. **Dependency accountability.** On acceptance, every free premise or theory entry consulted by
   `kappa` is returned by `uses_beta(kappa)`, and every returned dependency names a declared premise
   slot or an entry in the digest-addressed `T`. Adapters should prove exactness where their
   certificate syntax permits it.
5. **Closed registration.** The backend implementation, decoder, source encoding, and admissible
   theory format are fixed by `(beta, version)`. An artifact cannot upload code, axioms, or a new
   encoding.
6. **Structural consequence laws.** `models_beta` has:
   - reflexivity: every member of `Delta` follows from `T ; Delta`;
   - cut/transitivity: consequences established for intermediate premises may be substituted into a
     consequence using those premises; and
   - weakening: extending `T` or `Delta` with assumptions preserves a consequence.

   A non-monotonic reasoner is not a strict backend; it belongs in the warrant/attack layer.

The trusted implementation for a run is the source checker plus the selected backend adapters. A
backend theorem is evidence about its mathematical checker; conformance of an executable adapter is
still a separate obligation.

## 3. Source rule

For a strict policy rule

```text
r : P_1, ..., P_n => C
```

at ground substitution `theta`, let

```text
Delta = [encode_beta(P_1 theta), ..., encode_beta(P_n theta)]
phi   = encode_beta(C theta)
```

The certified strict-instance rule is:

```text
Sigma; Pi; Gamma; R |- w_i : P_i theta ▷ O_i       for every i
Pi(r).mode = strict
(beta@version, h) in Pi(r).certifiers
R(beta, version) = B_beta
theoryDigest(T) = h
check_beta(T, Delta, phi, kappa) = accept
------------------------------------------------------------------- (Strict-Cert)
Sigma; Pi; Gamma; R |- r<theta; w_1,...,w_n; cert(beta,h,kappa)>
                         : C theta ▷ union_i O_i
```

`R` is the fixed backend registry. Strict rules have no critical-question map or local holes.
Open obligations in premise terms still propagate.

The trusted-policy form has the same source conclusion but no semantic entailment premise:

```text
Sigma; Pi; Gamma; R |- w_i : P_i theta ▷ O_i       for every i
Pi(r).mode = strict
Pi(r).allow-trusted = true
------------------------------------------------------------------- (Strict-Trusted)
Sigma; Pi; Gamma; R |- r<theta; w_1,...,w_n; trusted>
                         : C theta ▷ union_i O_i
```

`Strict-Trusted` is structural validation against `Pi`, not a logical proof. It is intentionally
excluded from the certified strict-soundness theorem.

Every strict policy rule declares `allow-trusted : Bool` and a finite allowlist of
`(backend-version, theory-digest)` certifiers and is well formed only if at least one path is
available. This prevents an artifact from downgrading a certificate-required rule to trusted,
selecting an adapter the policy did not approve, or changing the adapter's background theory.

The backend receives only normalized proposition encodings. It never receives warrant terms,
argument identifiers, attack declarations, provenance, or statuses. Conversely, its returned object
is only `accept/reject`, dependencies, and diagnostics; no backend proof term can be reinserted as a
source proposition. This is the factivity firewall.

## 4. Reference adapters

### 4.1 Minimal natural-deduction adapter

The required v0.1 reference adapter is intuitionistic natural deduction for implication and falsum:

```text
phi ::= a | false | phi -> phi
e   ::= hyp i | lam phi e | app e e | abort phi e
```

Its typing rules are:

```text
Gamma(i) = phi
----------------------- (Hyp)
Gamma |- hyp i : phi

Gamma, phi |- e : psi
----------------------- (Imp-I)
Gamma |- lam phi e : phi -> psi

Gamma |- f : phi -> psi      Gamma |- x : phi
----------------------------------------------- (Imp-E)
Gamma |- app f x : psi

Gamma |- e : false
----------------------- (False-E)
Gamma |- abort phi e : phi
```

The source premises and selected theory entries form the free context. Certificates use de Bruijn
indices, making binding and dependency checking syntactic. This adapter is intentionally modest: it
certifies only propositional consequences visible in its encoding. Domain laws remain explicit
theory dependencies or trusted policy rules rather than hidden logical axioms.

Its source encoding is

```text
encode_ND(p) = atom(canonicalSerialize(nf(p))).
```

Canonical serialization is fixed, structural, and injective on normalized source ASTs. Hence
`p equiv q` iff `encode_ND(p) = encode_ND(q)`, discharging normalization fidelity.

For the required soundness result,
`T ; Delta |=_ND phi` means every Boolean valuation satisfying `T` and `Delta` satisfies `phi`.
This relation has reflexivity, cut, and weakening by its definition. Intuitionistic natural
deduction is sound but not complete for this Boolean semantics; completeness is not required because
LARA checks submitted certificates rather than searching for every valid proof.

Classical reasoning, arithmetic, temporal logic, or code behavior belongs in a different adapter
with its own semantics and soundness theorem. The core does not gain a classical axiom merely because
one adapter needs it.

### 4.2 Optional LP adapter

An LP adapter may retain the existing formula and proof-polynomial language:

```text
t ::= x | c | t.t | t+t | !t
F ::= p | false | F -> F | t:F
```

Its registered theory fixes the admissible constant specification and standard LP axiom schemas.
The adapter must prove its `check_LP` sound for the chosen LP semantics. LP reflection, sum,
positive introspection, and realization remain internal to this adapter. They are not source-language
constructs and do not constrain other backends.

The current Haskell `ConstantSpec` is not a conforming adapter because callers can register arbitrary
`(constant, formula)` pairs. It becomes eligible only after fixed schema recognition and a
conformance argument.

Keeping both natural-deduction and LP adapters makes the seam real rather than hypothetical. Corpus
evidence decides whether LP ships in the evaluated configuration.

## 5. Results and proofs

### Theorem 1: certified strict-step soundness

If a `Strict-Cert` instance with premises `p_1,...,p_n`, conclusion `c`, theory `T`, and backend
`beta` checks, then

```text
T ; [encode_beta(p_1), ..., encode_beta(p_n)] |=_beta encode_beta(c).
```

**Proof.** `Strict-Cert` has
`check_beta(T, [encode_beta(p_i)], encode_beta(c), kappa) = accept` as a premise. Apply backend
obligation 3. No claim about the truth of any `p_i` follows. QED.

### Corollary 1: soundness of a homogeneous strict-only certified tree

Suppose every internal node of a warrant tree is `Strict-Cert` under the same backend `beta`, and the
leaves conclude `l_1,...,l_m`. Then the encoded root is a semantic consequence under `models_beta`
of the encoded leaves and the union of the declared theory entries.

**Proof sketch.** Induct on the warrant tree. A leaf is an assumption. At an internal node, the
induction hypotheses establish the premise conclusions; Theorem 1 establishes the node conclusion
conditional on those premises. Compose semantic consequence. Normalization coherence ensures that
the conclusion exported by a child is the formula imported for the corresponding parent premise.
Backend obligation 6 supplies cut for composing child consequences and weakening for interpreting
every local consequence under the union of the tree's declared theories. QED.

The corollary does not apply through a defeasible or `Strict-Trusted` node. Above either kind of node,
the guarantee returns to policy-relative warrant validity.

For a tree mixing backends, Theorem 1 applies separately at each node, and the source checker proves
that child and parent propositions agree under source normalization. A global semantic-consequence
theorem would additionally require a proved interpretation between the backends' model classes.
LARA does not assume such an interpretation merely because both adapters are registered.

### Theorem 2: backend replacement preserves warrant status

Let `P_beta` and `P_gamma` be source-identical programs after erasing strict certificate payloads.
Assume corresponding payloads under backends `beta` and `gamma` accept exactly the same strict
instances. Let `eraseCert` replace each accepted certificate annotation by `certified` while
preserving argument names, rule instances, conclusions, obligations, and positions. Then

```text
compile(P_beta) ~= compile(P_gamma)
```

under the node bijection induced by equal `eraseCert` argument names/skeletons, and every claim has
the same `justified`, `defeated`, `contested`, or `gap` status.

**Proof.**

1. By structural induction on warrant terms, the same leaves and rule instances check in both
   programs. The only differing case is `Strict-Cert`, equalized by the acceptance hypothesis.
2. Certificate payloads do not occur in conclusions, positions, obligation sets, or attack typing.
   Therefore `eraseCert` gives a bijection between complete argument nodes and typed attacks.
3. Compilation preserves that bijection, so it is a graph isomorphism between the target Dung
   frameworks.
4. Dung's characteristic function commutes with graph isomorphism. Iteration from the empty set
   therefore yields corresponding unique grounded labels.
5. Claim aggregation is a deterministic function of corresponding support sets, equal holes, and
   corresponding labels. Statuses are equal. QED.

This theorem is the formal reason not to make LP syntax foundational to **claim-status semantics**:
status cannot distinguish LP from another adapter with the same strict acceptance profile. Replay,
certificate-size, backend-theory, and dependency reports may differ and remain visible for audit.

### Theorem 3: source non-factivity

No source derivation can use backend acceptance to derive a truth judgment for a warranted
proposition.

**Proof.** The source calculus has judgments only of the form
`Sigma; Pi; Gamma; R |- w : p ▷ O`, attack judgments, and status judgments. It has no judgment
`|- p true` and no rule eliminating a warrant into such a judgment. `Strict-Cert` returns another
warrant judgment and exports no backend formula constructor. By inversion on the final source rule,
backend acceptance can therefore produce only a warrant. QED.

This is a syntactic confinement result. It does not claim that a selected backend is non-factive
internally; an LP or theorem-prover adapter may be fully factive.

### Theorem 4: soundness of the natural-deduction adapter

If `Gamma |- e : phi`, then every Boolean valuation satisfying all formulas in `Gamma` satisfies
`phi`.

**Proof.** By induction on the typing derivation.

- `Hyp`: `phi` is in `Gamma`, so it is satisfied by assumption.
- `Imp-I`: assume the valuation satisfies the antecedent. It then satisfies the extended context;
  the induction hypothesis gives the consequent, hence it satisfies the implication.
- `Imp-E`: the induction hypotheses give both `phi -> psi` and `phi`; Boolean implication yields
  `psi`.
- `False-E`: no valuation satisfies `false`, so the conclusion follows vacuously.

Thus accepted natural-deduction certificates satisfy backend obligation 3. QED.

### Lemma 5: natural-deduction dependency exactness

For a well-typed certificate `e`, the free de Bruijn indices in `e` are exactly the premise/theory
slots on which its derivation depends.

**Proof sketch.** Structural induction on `e`. `hyp i` contributes `{i}`; `app` takes union; `abort`
preserves the child's set; `lam` removes the newly bound index and shifts the remaining free
indices. The checker rejects every out-of-range free index. QED.

## 6. Why modal, evidence, or justification logic is not the source semantics

### Proposition 6: ordinary modal logic cannot determine dependency reports

Let two evidence-labelled structures have the same Kripke frame and propositional valuation but
different leaf identities, provenance, or source positions. Every formula of ordinary propositional
modal logic has the same truth value in both structures, while LARA's required dependency or attack
report can differ.

**Proof.** Induct on modal formulas. Atomic truth uses only the shared valuation; Boolean cases use
the induction hypotheses; `box` and `diamond` use only the shared accessibility relation and the
induction hypotheses at related worlds. Evidence labels and source positions are never inspected.
Therefore modal truth is invariant under changing only those labels. LARA's `leaves(w)` and
positional targets inspect exactly those labels, so they are not determined by the ordinary modal
reduct. QED.

This does not show that modal logic cannot be extended with names or proof terms. It shows that
ordinary S4 alone omits information the checker is required to preserve. S4 remains appropriate
inside an adapter whose certificate restores that information.

### Proposition 7: factive LP cannot interpret source warrant

Assume source warrant `w : p` is interpreted as LP assertion `t:p`, and the intended source models
permit a policy-valid warrant for a proposition that is false in the world. Then LP reflection
`t:p -> p` is invalid for that interpretation.

**Proof.** Choose an intended source model with `w : p` accepted and `p` false; such models are
required because LARA validates structure relative to leaves and policy rather than empirical truth.
The proposed interpretation makes `t:p` true and `p` false, falsifying `t:p -> p`. QED.

Thus factive LP may certify a strict conditional step but cannot supply the meaning of source
warrant. J/J4 avoids this particular contradiction by omitting reflection.

### Proposition 8: monotonic consequence cannot represent defeat-driven retraction

No monotonic consequence relation can, by itself, represent LARA claim acceptance under framework
extension.

**Proof.** Let input `X` contain a complete unattacked support for `p`, so `p` is `justified`. Extend
it to `Y` by adding a checked, undefeated attacker, so `X` is a subset of `Y` but `p` is no longer
`justified`. If acceptance were represented by a monotonic consequence relation, `X |- p` and
`X subseteq Y` would imply `Y |- p`, a contradiction. QED.

Ordinary S4, LP, J, and J4 are monotonic and therefore cannot be the whole status semantics. Their
strict consequences can still be used behind the backend interface.

### What these propositions do not exclude

- **Evidence logic.** Neighborhood and dynamic evidence logics can model evidence-sensitive belief
  and, in some variants, update. No theorem above excludes using one. The current design does not
  make it the source calculus because it still needs certificate syntax, policy obligations,
  provenance, and positional attack diagnostics. Use it as policy/admission semantics when a corpus
  requirement for evidence aggregation appears; only a monotonic evidence-entailment fragment may
  satisfy the strict-backend contract.
- **Default justification logic.** Pandzic-style systems already combine justification terms and
  defeasibility. They are a genuine alternative, not ruled out by Proposition 8. LARA chooses the
  ASPIC+/Dung route because it directly supplies the required rebut/undercut/undermine structure,
  skeptical grounded status, and a small executable compilation target. The paper must defend this
  choice through the certificate-language delta and corpus fit, not by claiming default JL is
  incapable.

## 7. What proof cannot decide

Four design questions require evidence rather than theorem proving:

1. **Whether LP earns its implementation and explanation cost.** Backend replacement proves that LP
   is not foundational; it cannot prove that LP is useless. Measure the fraction of corpus steps
   requiring `t:F`, `!`, `+`, or realization, and compare certificate size and checking cost.
2. **Whether a warrant policy is epistemically adequate.** A sound checker can establish correct
   instantiation only relative to `Pi`. Policy quality requires expert sourcing, corpus coverage,
   sensitivity analysis, and adjudication.
3. **Whether natural language was faithfully formalized.** The `nl`/`formal` binding remains an
   audited empirical translation. No backend soundness theorem closes that gap.
4. **Whether a backend encoding and theory match the intended domain.** Soundness is relative to
   `encode_beta`, `T`, and `models_beta`. A theorem can show the executable checker implements those
   definitions; it cannot show that they faithfully represent an experiment, program, or scientific
   concept. Audit and evaluate backend encoding/theory selection separately.

These are evaluation obligations. Presenting them as missing proofs would confuse mathematical
validity with empirical adequacy.

## 8. Consequences

- The paper's foundation is the warrant calculus plus compilation to grounded argumentation, not
  LP or S4.
- `spec.md` defines one backend-parametric strict rule and one reference natural-deduction adapter.
- LP realization moves to optional-adapter metatheory and related work.
- The trusted-base report lists the selected adapters and theory digests for each run.
- The evaluation reports certified versus trusted strict steps per backend. The previous single
  "LP witness fraction" becomes a backend-neutral strict-certification rate.
- Existing LP code is retained as an experimental adapter seed, not called the trusted core of
  LARA.
