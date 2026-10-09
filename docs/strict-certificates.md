# Strict certificate backends

Lara arguments carry two strengths of step. A *defeasible* step holds by default and can be attacked. A *strict* step has its conclusion re-verified mechanically. This document is the reference for how strict steps are verified: one small seam where an opaque certificate is handed to a registered, versioned external checker (a *backend*); the obligations every backend must meet; the adapters that ship; the theorems about mixing several backends in one program; and the two optional domain adapters, ordered comparison and static code inspection, that arrived after the seam was fixed.

Nothing here makes the source language a proof system. The one claim-support calculus knows neither a backend's proof-term grammar nor its axioms, and a successful check buys deductive validity relative to the cited premises and the declared theory, not the truth of any premise and not the empirical truth of any measurement.

## 1. One seam for opaque strict certificates

The source language has one claim-support calculus and one small seam for strict certificates. A strict rule instance may carry an opaque certificate checked by a registered backend. The claim-support calculus knows neither the backend's proof-term grammar nor its axioms.

This replaces

```text
Sigma_LP ; { x_i : P_i theta } |- d => t : C theta
```

with

```text
strictCheck(beta, T, [P_1 theta, ..., P_n theta], C theta, kappa) = accept
```

where `beta` is a fixed backend identifier and version, `T` is a digest-addressed backend theory, and `kappa` is an opaque certificate. Programs may select registered backends and theories but may not define either at runtime.

The source-level meaning is deliberately narrow:

- a successful check discharges the *deductive validity* of this strict step, conditional on its premise conclusions and the declared theory;
- it does not establish that the premise support terms' conclusions are true;
- it does not expose a backend formula or proof term to the support language; and
- it does not change attack or status semantics.

An unwitnessed strict rule remains permitted as an explicitly trusted policy rule. Reports must distinguish `certified(beta, theory-digest)` from `trusted-policy`; only the first receives the backend-soundness guarantee.

## 2. The abstract strict-certificate system

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

`models_beta(T, Delta, phi)` is written `T ; Delta |=_beta phi`. It is a mathematical semantics used to state soundness; it need not be executable. `Dependency` names free premise slots and entries in `T`. Locally introduced and discharged assumptions are not dependencies.

Every registered backend must establish these obligations:

1. **Decidable replay.** `check_beta` is total, deterministic, and terminating on finite input.
2. **Normalization fidelity.**

   ```text
   p equiv q    iff    encode_beta(p) = encode_beta(q)
   ```

   The forward direction preserves source identity; the reverse direction prevents an encoder from silently collapsing distinct propositions. Stronger semantic equivalences must be proved through an explicit backend theory or certificate.
3. **Certificate soundness.**

   ```text
   check_beta(T, Delta, phi, kappa) = accept
   ------------------------------------------------
                    T ; Delta |=_beta phi
   ```
4. **Dependency accountability.** On acceptance, every free premise or theory entry consulted by `kappa` is returned by `uses_beta(kappa)`, and every returned dependency names a declared premise slot or an entry in the digest-addressed `T`. Adapters should prove exactness where their certificate syntax permits it.
5. **Closed registration.** The backend implementation, decoder, source encoding, and admissible theory format are fixed by `(beta, version)`. An artifact cannot upload code, axioms, or a new encoding.

Whole-tree semantic consequence needs additional laws: reflexivity, cut/transitivity and weakening over premises and theory entries. These were previously listed as a sixth registration obligation, but the mechanized `Strict.Backend` record does not require them. Its guaranteed results are occurrence-local soundness and dependency accounting. Shipped domain relations restrict which goals they interpret: `ordModels`, for example, rejects an arbitrary non-comparison atom even when it appears as a premise, so it is not reflexive over all encoded source atoms. The homogeneous-tree corollary below explicitly assumes the extra laws; the Boolean ND interpretation is the reference example that satisfies them.

The trusted implementation for a run is the source checker plus the selected backend adapters. A backend theorem is evidence about its mathematical checker; conformance of an executable adapter is still a separate obligation.

## 3. Source rules for certified and trusted strict steps

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

`R` is the fixed backend registry. Strict rules have no critical-question map or local holes. Open obligations in premise terms still propagate.

The trusted-policy form has the same source conclusion but no semantic entailment premise:

```text
Sigma; Pi; Gamma; R |- w_i : P_i theta ▷ O_i       for every i
Pi(r).mode = strict
Pi(r).allow-trusted = true
------------------------------------------------------------------- (Strict-Trusted)
Sigma; Pi; Gamma; R |- r<theta; w_1,...,w_n; trusted>
                         : C theta ▷ union_i O_i
```

`Strict-Trusted` is structural validation against `Pi`, not a logical proof. It is deliberately excluded from the certified strict-soundness theorem.

Every strict policy rule declares `allow-trusted : Bool` and a finite allowlist of `(backend-version, theory-digest)` certifiers, and is well formed only if at least one path is available. This prevents an artifact from downgrading a certificate-required rule to trusted, selecting an adapter the policy did not approve, or changing the adapter's background theory.

The backend receives only normalized proposition encodings. It never receives support terms, argument identifiers, attack declarations, provenance, or statuses. Conversely, its returned object is only `accept/reject`, dependencies, and diagnostics; no backend proof term can be reinserted as a source proposition. This is the factivity firewall.

## 4. Reference adapters

### 4.1 Required: intuitionistic natural deduction

The v0.1 reference adapter is intuitionistic natural deduction for implication and falsum:

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

The source premises and selected theory entries form the free context. Certificates use de Bruijn indices, making binding and dependency checking syntactic. This adapter is intentionally modest: it certifies only propositional consequences visible in its encoding. Domain laws remain explicit theory dependencies or trusted policy rules rather than hidden logical axioms.

Its source encoding is

```text
encode_ND(p) = atom(canonicalSerialize(nf(p))).
```

Canonical serialization is fixed, structural, and injective on normalized source ASTs. Hence `p equiv q` iff `encode_ND(p) = encode_ND(q)`, discharging normalization fidelity.

For the required soundness result, `T ; Delta |=_ND phi` means every Boolean valuation satisfying `T` and `Delta` satisfies `phi`. This relation has reflexivity, cut, and weakening by its definition. Intuitionistic natural deduction is sound but not complete for this Boolean semantics; completeness is not required because Lara checks submitted certificates rather than searching for every valid proof.

Classical reasoning, arithmetic, temporal logic, or code behavior belongs in a different adapter with its own semantics and soundness theorem. The core does not gain a classical axiom merely because one adapter needs it. The adapter lives in `Lara.Strict.ND` and `lean/Lara/ND.lean`; its soundness and dependency results are Theorem 4 and Lemma 5 below.

### 4.2 Optional: LP

An LP adapter may retain the existing formula and proof-polynomial language:

```text
t ::= x | c | t.t | t+t | !t
F ::= p | false | F -> F | t:F
```

Its registered theory fixes the admissible constant specification and standard LP axiom schemas. The adapter must prove its `check_LP` sound for the chosen LP semantics. LP reflection, sum, positive introspection, and realization remain internal to this adapter. They are not source-language constructs and do not constrain other backends.

The Haskell `ConstantSpec` is not a conforming adapter because callers can register arbitrary `(constant, formula)` pairs. It becomes eligible only after fixed schema recognition and a conformance argument.

LP is an experimental adapter seed, not a shipped conforming backend. Theorem 2 makes the interface independent of LP syntax; shipping an LP adapter would still require the fixed-schema and conformance obligations above.

### 4.3 Ordered comparison: `ord@1`

`ord@1` re-checks ordered numeric comparisons, such as `0.71 < 0.74`, from a certificate. Its closed predicate family contains `num_lt` and `num_le`. It lives in `Lara.Strict.Ord` and `lean/Lara/Ord.lean`; section 9 distinguishes its worked examples from measured corpus coverage.

#### What an accepted step certifies

An accepted certificate discharges the comparison relative to the premise conclusions, never the truth of any cell. The measurement leaves stay defeasible: attackable, quarantinable, admission-governed. You cannot argue with the arithmetic; you argue with the measurements.

Stated exactly: both numerals appear in the goal, so the relation is decidable from the goal alone. What the premises add is provenance anchoring. An accepted step certifies that each cited premise's unique numeric literal equals the corresponding goal numeral, and that the goal's relation holds of those numerals. Neither the plan nor the paper should let "certifies the comparison" suggest more.

The dependency set is a metatheory-level obligation: the runtime seam (`buildCertOk`) collapses acceptance to a `Bool`, so `deps` feeds the soundness statement and audit reports, not the checked graph.

#### Premise-only slots and intra-family exclusivity

Two consequences are mechanized rather than asserted, in `lean/Lara/Ord.lean`: the premise-only slot guard, so a certificate cannot cite a self-supplied theory entry as measured evidence, and intra-family exclusivity (`ordModels_excl_of_lt`), which is why `num_lt` and `num_le` head no declared contrary pair and so never trip R12.

### 4.4 Static code inspection: `insp@1`

The adapter portfolio ships `insp@1` beside `ra@1` and `ord@1`, in `Lara.Strict.Insp` and `lean/Lara/Insp.lean`. It closes the code-inspection shape an artifact asserts when its argument depends on something not being in the code, for example "the shipped implementation never uses the test set". It certifies structural facts about referenced source, as a closed four-predicate family over declared exhaustive inventories:

| goal | inventories cited | what it says |
| --- | --- | --- |
| `code_absent(Src, Feat)` | 1 | `Feat` occurs nowhere in `Src` |
| `code_present(Src, Feat)` | 1 | `Feat` occurs in `Src` |
| `code_unique(Src, Feat)` | 1 | `Src`'s inspection found something, and everything it found is `Feat` |
| `code_planned_not_shipped(Plan, Src, Feat)` | 2 | `Feat` is in `Plan`'s inspection and absent from `Src`'s |

The last member is the corpus's own scheme name. The M0 C13/C14 study counted `code_inspection` (merging `plan_vs_shipped_diff`) as 3 of 60 sampled claims, small but real, and the only measured strict shape the portfolio had left unshipped. Certificates are

```text
cert ::= (inspect (prem N))                 -- the one-inventory members
       | (inspectdiff (prem N) (prem M))    -- the plan-vs-shipped diff
```

There is no witness value. The relation is read off the goal predicate, as in `ord@1`; what the certificate fixes beyond the slots is the arity of the step, which is why the two family shapes get two wire keywords and two flat `SlotSchema`s. An `(inspect ...)` payload under a `code_planned_not_shipped` goal is a rejection, not a re-interpretation.

#### The closed-world step

This is the question the whole adapter turns on, because "static code inspection" sounds like a measurement, and a measurement is not a strict step.

A negative existential over code, "the shipped module has no repair call site anywhere", is not an observation. It is an inference from an exhaustive enumeration: given that the inspection covered the whole unit and enumerated everything it found, absence follows deductively. That inference is what `insp@1` replays, and it is the only thing it replays.

The enumeration arrives as an ordinary premise:

```text
inv(Src, finding(f1, finding(f2, no_findings)))
```

read as "an exhaustive inspection of `Src` found exactly `f1` and `f2`." The empty inventory `inv(Src, no_findings)`, inspected and found nothing, is the pure negative-existential case; `Lara.Insp.relHolds_absent_of_nil` is that one-line theorem, and `fixtures/corpus/insp-empty-inventory-accept.sexp` is its standing wire anchor.

`Σ` fixes each constructor's arity (spec §2), so `inv(U, f1, …, fn)` is not declarable at all: a unit's signature would have to name one `inv` per length, and the R2 sort checker could not check it. The convention is therefore three fixed-arity reserved symbols, `inv`/2, `finding`/2, and `no_findings`/0, and the enumeration is an ordinary source-level list. This is the same one-table discipline the wire keywords follow: the concrete spellings live in `Lara.Strict.Insp`'s `Con` table (Lean: `Lara.Insp.Con`) and nowhere else.

A consulted premise must contain exactly one `inv(…)` node anywhere in its argument terms. This is `Lara.Strict.Cell.premiseCell`'s "exactly one numeric literal" discipline, for the same reason: a premise carrying two inventories does not say which one the certificate meant, and guessing is how a checker becomes unsound quietly. The scan does not stop at the first match, so a nested `inv` inside a finding is a second node and rejects too.

An accepted certificate does not assert that an inventory faithfully describes source bytes, covers the whole module, or names the version relevant to the claim. Those are evidence-admission and human-review obligations, outside this strict adapter. An inventory remains a defeasible evidence leaf: attackable, quarantinable and admission-governed.

The corpus makes this concrete rather than hypothetical. `corpus-units/rebench-rust_codecontests/C09` is exactly a `plan_vs_shipped_diff` where the coverage half is met and the version half is not: `notes.md`, the sole documentary basis for the "planned" half, ships nowhere in the artifact tree. Its honest verdict is a `gap`, and no certificate changes that. The worked example `examples/S9` supplies the version attestation C09 could not, so the same shape reaches `justified`; the two read together are the demonstration that the certificate settles the inference and not the evidence. What the adapter does remove from the trusted base is narrower and real: the step from an enumeration to a structural conclusion no longer rests on a trusted policy rule.

#### Premise-only slots

`insp@1` rejects any certificate slot `>= nPrem`, the seam-wide rule `ra@1` and `ord@1` already follow. Here the guard protects the closed-world premise itself. On the raw `.sexp` door the backend theory table is built from the unit's own wire `theories` section and replay preflight never validates its content, so without the guard an artifact could supply a theory entry asserting "I inspected everything and found nothing" and certify against it, with no leaf, no provenance, no admission check, and nothing for an attack to land on.

`fixtures/corpus/insp-premise-only-{accept,reject}.sexp` isolate it: both units declare the same one-entry theory carrying an inventory that would have satisfied the goal, and differ only in whether the certificate cites the premise or the theory entry.

The Lean side reaches the same acceptance set from the other direction, exactly as the two arithmetic backends do: `Lara.Driver.buildRegistry` resolves any known `insp@1` digest to `[]`, so `Γ = Δ ++ [] = Δ` and "names a premise" coincides with "is in range of `Γ`". An unknown digest still fails to resolve, which is a rejection.

#### Contraries

`num_lt` and `num_le` head no declared contrary pair, and that is a theorem: comparison goals are decided against a shared ground truth, the numerals in the goal itself, so a sound backend can never accept two conflicting members (`Lara.Ord.ordModels_excl_of_lt`).

Inspection goals are not like that. They are decided against a declared inventory, and two units may declare different inventories for the same source. `code_absent(S, F)` and `code_present(S, F)` are therefore genuinely co-acceptable. Both halves are mechanized:

- `Lara.Insp.inspModels_excl_of_same_entry`, two arguments reading the same inspection leaf cannot both be backed for opposite polarities;
- `Lara.Insp.inspModels_absent_present_sat`, two arguments reading different leaves can.

`InspSpec.prop_inspContraryCoAcceptable` is the executable mirror of the second.

This has a direct consequence for policy authors, and it is a Path B consequence, not an `insp@1` one. Spec §8.1 forbids a strict-reachable conclusion pattern from overlapping either side of a `contrary` declaration (R12). So a policy may not both make `code_absent` and `code_present` strict conclusions and declare them contrary; that is an R12 rejection at compile time. The conflict therefore belongs on the defeasible bridge's conclusions, one layer up, which is exactly the layering `examples/S9/insp-v1.policy.lara` uses and the same shape `ord@1`'s S2 uses for a different reason. Under that restriction every conflict is rebuttable at a defeasible step, which is what Path B buys.

#### Rejected designs

One premise per finding plus a separate exhaustiveness premise was rejected: a negative existential would cite the exhaustiveness premise together with all occurrence premises, so the certificate's slot count would vary with the size of the enumeration. That is not a flat `SlotSchema`, so the symbolic-slot elaboration pass (`Lara.Elaborate.CertSlots`) could not lower `(prem name)` references for it, and the wire grammar would stop being a fixed-arity keyword application. The enumeration belongs in one premise because it is one observation.

The separately implemented `lara-evidence@0.1` layer checks bindings to source bytes ([design](evidence-admission-design.md)). Building those observations into a strict backend would instead make a defeasible measurement a trusted premise of the adapter. Byte-level admission strengthens the evidence leaf without changing this adapter's inference.

A `code_diff` spelling for the diff member was rejected on the §4.5 naming taste already settled for the scheme vocabulary: the target reader is a Python-literate domain researcher reading the formalization of their own artifact, so long-and-obvious wins over short-and-precise-to-insiders.

Making `code_present` a separate backend, or dropping it, was rejected. It carries no closed-world content on its own, being plain membership, but it stays because it is the positive half that makes the contrary question above statable and testable, and because the diff member decomposes into it (`Lara.Insp.inspModels_diff_halves`).

#### What the adapter does not settle

Whether an inventory is a good formalization of an inspection is an audit question, not a proof question, and it is the fourth item of section 8 below. A theorem shows the executable adapter implements `inspModels`; it cannot show that `inspModels` faithfully represents what a reader means by "the module has no repair path". That gap closes with evidence admission and human audit, not with a stronger backend.

## 5. Results and proofs

### Theorem 1: certified strict-step soundness

If a `Strict-Cert` instance with premises `p_1,...,p_n`, conclusion `c`, theory `T`, and backend `beta` checks, then

```text
T ; [encode_beta(p_1), ..., encode_beta(p_n)] |=_beta encode_beta(c).
```

**Proof.** `Strict-Cert` has `check_beta(T, [encode_beta(p_i)], encode_beta(c), kappa) = accept` as a premise. Apply backend obligation 3. No claim about the truth of any `p_i` follows. QED.

### Corollary 1: soundness of a homogeneous strict-only certified tree

Suppose every internal node of a support tree is `Strict-Cert` under the same backend `beta`, the leaves conclude `l_1,...,l_m`, and `models_beta` satisfies reflexivity, cut/transitivity and weakening over the premises and the union of declared theory entries. Under these additional semantic hypotheses, the encoded root is a consequence of the encoded leaves and that theory union. Registration alone does not supply these hypotheses.

**Proof sketch.** Induct on the support tree. Reflexivity covers a leaf. At an internal node, the induction hypotheses establish the premise conclusions and Theorem 1 establishes the node conclusion conditional on those premises. The assumed cut law composes those consequences. Normalization coherence identifies a child's exported formula with the parent's imported premise, and the assumed weakening laws place each consequence under the union of the declared theories. This is a conditional mathematical argument, not a generic theorem provided by `Strict.Backend`.

The corollary does not apply through a defeasible or `Strict-Trusted` node. Above either kind of node, the guarantee returns to policy-relative claim-support validity.

For a tree mixing backends, Theorem 1 applies separately at each node, and the source checker proves that child and parent propositions agree under source normalization. A global semantic-consequence theorem would additionally require a proved interpretation between the backends' model classes. Lara does not assume such an interpretation merely because both adapters are registered.

### Theorem 2: backend replacement preserves claim status

Let an accepted program be related to another by one uniform injective relabeling of assurances that preserves strict-certificate acceptance. The mechanized backend-replacement theorem preserves the compiled argumentation framework and every claim's `justified`, `defeated`, `contested` or `gap` status.

`Erase.backend_replacement` in `lean/Lara/Erase.lean` proves status equality for the relabeled programs. `EraseTransport.backend_replacement_transport` constructs the relabeled well-checked program. Uniformity keeps a shared subterm's assurance identical at every occurrence; injectivity keeps distinct assurances and subterms distinct.

The proof transports support typing and positional attacks, preserves subterm occurrence and closure edges, and obtains the same compiled framework. Grounded labeling and claim aggregation then agree.

Replacing every certificate by a single `certified` marker is not a valid substitute for the injective relabeling. It can collapse distinct subterms, merge occurrences and add subargument-closure edges. Equal backend acceptance profiles alone do not justify that erasure.

This theorem is the formal reason not to make LP syntax foundational to claim-status semantics: status cannot distinguish LP from another adapter with the same strict acceptance profile. Replay, certificate-size, backend-theory, and dependency reports may differ and remain visible for audit.

### Theorem 3: source non-factivity

No source derivation can use backend acceptance to derive a truth judgment for a supported proposition.

**Proof.** The source calculus has judgments only of the form `Sigma; Pi; Gamma; R |- w : p ▷ O`, attack judgments, and status judgments. It has no judgment `|- p true` and no rule eliminating support into such a judgment. `Strict-Cert` returns another support judgment and exports no backend formula constructor. By inversion on the final source rule, backend acceptance can therefore produce only support. QED.

This is a syntactic confinement result. It does not claim that a selected backend is non-factive internally; an LP or theorem-prover adapter may be fully factive.

### Theorem 4: soundness of the natural-deduction adapter

If `Gamma |- e : phi`, then every Boolean valuation satisfying all formulas in `Gamma` satisfies `phi`.

**Proof.** By induction on the typing derivation.

- `Hyp`: `phi` is in `Gamma`, so it is satisfied by assumption.
- `Imp-I`: assume the valuation satisfies the antecedent. It then satisfies the extended context; the induction hypothesis gives the consequent, hence it satisfies the implication.
- `Imp-E`: the induction hypotheses give both `phi -> psi` and `phi`; Boolean implication yields `psi`.
- `False-E`: no valuation satisfies `false`, so the conclusion follows vacuously.

Thus accepted natural-deduction certificates satisfy backend obligation 3. QED.

### Lemma 5: natural-deduction dependency exactness

For a well-typed certificate `e`, the free de Bruijn indices in `e` are exactly the premise and theory slots on which its derivation depends.

**Proof sketch.** Structural induction on `e`. `hyp i` contributes `{i}`; `app` takes union; `abort` preserves the child's set; `lam` removes the newly bound index and shifts the remaining free indices. The checker rejects every out-of-range free index. QED.

## 6. Heterogeneous composition: the firewall and the accounting laws

A program may mix certificates from several registered backends. What the theory has to guarantee is that no backend's acceptance can leak influence into another's mathematics. The composition results are mechanized in `lean/Lara/BackendComposition.lean` (abstract) and `lean/Lara/Examples/BackendComposition.lean` (worked witness), with a cross-language half in `src/Lara/Strict/Deps.hs` and `test/StrictSpec.hs`. Every theorem named in this section is covered by `lean/AxCheck.lean`, sorry-free, on the standard axiom trio `propext`, `Classical.choice`, and `Quot.sound`.

Several of these properties were already true and unstated. `certOkOf` (`Lara/Support.lean`) resolves each `BackendId` to its own `RegisteredBackend`, each carrying its own `core : Strict.Backend canon` with its own private `core.Form`, so heterogeneity was already structural; nothing forced two occurrences to share a formula type. `cert_node_accounted` and `cert_steps_accounted` already lifted per-instance strict soundness through `HasSupport` with the backend record bound in a per-node existential, and `mem_certDeps_step` and `cert_step_deps_subset` were already the two directions of the dependency union. What was missing is that no theorem *stated* heterogeneity: every existing result quantified one occurrence at a time. An unstated property is one a later refactor can silently break, so the work here is consolidation, one genuinely new theorem (the firewall), and the repair of a live gap on the Haskell side.

### Frozen definitions

| Object | Declaration | What it fixes |
|---|---|---|
| Certified occurrence | `CertOccurrence`, `.node`, `OccursIn` | The eight-binder node pattern of `CertStepIn`, bundled as a statement surface |
| Named identities | `usedBackends`, `usedBackendsList`, `usedBackendsDis` | Which backends a term *names*, source-visibly |
| Occurrence-local consequence | `OccurrenceConsequence` | What one occurrence's backend establishes, with its formula type bound inside |

`CertOccurrence` derives rather than stores. The paper plan's field list included the instantiated premise conclusions and the source conclusion, and the mechanization does not store them. They are not part of the node's syntax; they are recovered from the rule and the substitution (`instAPats θ r.premises`, `instAPat θ r.concl`) and exist only relative to a typing derivation. Storing them would let a caller forge an occurrence whose recorded premises disagree with the ones its rule actually instantiates. The derived-fields phrasing is the authoritative one.

### How an occurrence is stated

```lean
def OccurrenceConsequence {canon : String → String} (reg : BackendRegistry canon)
    (β : BackendId) (hd : Digest) (κ : CertRef) (As : List Atom) (C : Atom) : Prop :=
  ∃ registered T, reg β = some registered ∧ registered.resolveTheory hd = some T ∧
    registered.core.modelsFull
      (Strict.selectSlots (As.map registered.core.enc ++ T) (registered.core.uses κ))
      (registered.core.enc C)
```

`registered.core.Form` is bound by the `∃`. The formula type, the theory data, and the consequence relation are all projections of a witness this proposition introduces and discharges; each existential closes before the next opens. So conjoining two occurrences' consequences introduces **no binder requiring them to share a formula type, a theory, or a consequence relation**.

That is a claim about the absence of a relating binder, not an assertion that the two are disjoint. A registry is an arbitrary function `BackendId → Option (RegisteredBackend canon)`; nothing stops it mapping two identities to the same core, in which case the two formula types *are* equal. Type disjointness is neither provable nor intended. Heterogeneity here means the composition is unconstrained, not that the parts are distinct.

Two binders *are* shared across the conjuncts, and saying so keeps the sentence above from compressing into the false "nothing is shared": the registry `reg` and the source canonicalizer `canon` that every `Backend canon` is indexed by. Both are source-side. Neither relates the backends' internal mathematics, so the three enumerated items remain unshared. Sharing `canon` is in fact what the composition needs; it is what makes two backends' conclusions comparable as claims about the same source. A display that reads "different backends have different formula types" would be false.

### The firewall

The one new theorem, in two halves:

- `prem_subterm_swap`, replacing a premise subterm with any term of the same conclusion and obligations preserves the parent's typing.
- `dis_subterm_swap`, the same at a discharge slot, with the question key carried across by `map_fst_set_of_getElem?`.

Neither statement mentions a backend, and that is the content: the replacement may be certified by a different registered identity over a different private formula type under a different theory, and no side condition of the parent can express the difference. Naming the two backends is a corollary (`mixed_swap`, `mixed_dis_swap`), not the theorem.

The theorem is cheap, and how it is cheap is verified mechanically. `InstSide` reaches `ws` only through three length fields, `lenAs`, `lenCs`, and `lenOs`, and `List.set` preserves length. The check is not a reading of the structure: the premise half's proof is `refine .inst { hside with lenAs := …, lenCs := …, lenOs := … }`, and *that elaborating* is Lean confirming those three fields are the only place `InstSide` mentions `ws`. The discharge half touches more, lengths, `ans`, and the four fields reading `D.map Prod.fst`, so its surviving side conditions are written out one by one rather than inherited, because which fields survive is the point of the theorem.

Backend leakage is inexpressible in Lean. A parent cannot attempt to inspect a child's formula: `Assurance` carries only `(β, hd, κ)`, and there is no syntax anywhere in the AST naming another backend's `Form`. The attempt is not ill-typed; it is inexpressible, so there is no Lean term to reject. The honest Lean deliverable is the positive opacity theorem above plus this non-expressibility note. At the Haskell wire level the attempt is expressible, because the wire form is untyped: an `nd@1` certificate whose payload embeds an `ord@1` sub-payload is a real `SExpr` that `nd@1`'s decoder rejects. That vector (`prop_crossBackendPayloadRejected`) runs through `buildCertOk`, not `strictCheck`, because a firewall vector that never runs on the shipped path checks the wrong checker. An `Assurance`-extension alternative was rejected: it would put a non-source construct in the frozen core to serve a test.

### The accounting laws

- `certDeps_eq_union`, certificate dependencies are exactly the union of the occurrence-local backend reports. Each `stepDeps o.node` is computed by `o.β`'s own core, so this is a union over heterogeneous reporters, not a report from a shared one. The collection law survives heterogeneity because it never had to look inside a backend to hold.
- `hetero_occurrences_accounted`, the headline result. Every certified occurrence of a typed term is accounted by *its own* registered core. It carries the acceptance conjunct the paper's target theorem states ("its local checker accepts its certificate") as a conjunct separate from the consequence: acceptance is the checkable fact a verifier re-runs, consequence is the semantic fact it buys.
- `usedBackends_accounted`, the syntactic identity list is exactly the set of logics the term's correctness rests on. Read as an audit: for each `β` a reviewer scans out of a term, it names the occurrence to inspect, the certificate to re-check, and the digest fixing which axioms that check may consult.

All three are derivations from the pre-existing `Lara/Support.lean` results (repackage, do not re-prove; design decision D4). No new induction was needed anywhere, which was the intended signal that the repackaging was the right shape.

### Dependency accounting in the shipped checker

The shipped checker retains and surfaces certificate dependencies. `CertOutcome.CertAccepted` carries the `Set Dependency` the adapter already returns; the acceptance projection `certAccepted` stays a `Bool`, which is the invariant that makes the widening safe, since no checked-graph decision, and therefore no soundness statement, can start depending on dependency data. `Lara.Strict.Deps.certDeps` collects the term-level report, tagging each step with its own backend as it walks; identity is tagged with `St.BackendId` (name and version), not the AST's name-only id, so two same-name different-version backends cannot collide into one indistinguishable report.

The reports are surfaced to shipped consumers on the current path. `Lara.Driver.runCheckDeps` produces rejection diagnostics, certificate dependencies, claim reports, and AF-node names from one pass; `unitCertDeps` reads `certDeps` per argument; and the `lara deps` subcommand renders them. Arguments with no certificate dependencies are still listed, with a header and no lines under it, because a strict-mode argument that consulted nothing and an argument that is not in the report at all are different facts and a reader auditing what evidence a verdict rests on needs to tell them apart. On checked terms the Haskell collector agrees with Lean's `certDeps`; the two differ only in totality, since Lean's `stepDeps` reports a resolvable certificate's uses even when acceptance fails while the Haskell collector sees a report only through `CertAccepted`, and on typed terms acceptance holds at every certificate node anyway.

**Labeled history.** Before the accounting was wired through, `strictCheck`, the only constructor of the sealed `StrictJudgment` and the only thing retaining `sjDependencies`, was called from `test/` and from nowhere in `src/`, and the production checker reached backends through `buildCertOk`, which called `runBackend` and **discarded the dependency report**. Lean proved `certDeps` accounted for every certified occurrence while the shipped checker accounted for none of them, which is why `CertOutcome.CertAccepted` was widened to carry the report.

### The worked witnesses

The typed firewall results use a fixture core. `mixed_swap` and `mixed_dis_swap` need a genuinely typed child, and typing a certificate node requires its acceptance to hold in-kernel. The child is `fixCore`, a minimal `Strict.Backend` whose every field is genuinely proved and whose `uses` reports a real slot rather than nothing; an empty report would discharge `uses_covers`, `uses_valid`, and `uses_account` vacuously, and the fixture would prove nothing about the accounting laws it exists to exercise. What sits above that child differs between the two halves, and only the premise half witnesses a swap under a shipped parent:

- For `mixed_swap` the parent is the real `nd@1`, via the already-worked `registry_success_bridge`, and the swapped term names both identities (`usedBackends mixedSwapTerm = [ndId, fixId]`).
- For `mixed_dis_swap` the parent is an unassured defeasible `ruleMix` node, not `nd@1`: `strictNoQ` forces `D = []` on strict nodes, so a certified node in a discharge position needs a defeasible ancestor. `nd@1` is the replaced child here, so `usedBackends disParent = [ndId]` and `usedBackends disSwapTerm = [fixId]`: the swap crosses a backend boundary, but the post-swap term is homogeneous. The discharge-side firewall is therefore witnessed against a shipped backend only as the term being swapped out, not as the parent that survives the swap.

`mixed_registrations_distinct` is proved through a non-dependent projection, the resolved theory's *length*, because the theory data itself has type `List r.core.Form` and cannot be compared across records.

The shipped `nd@1` and `ord@1` carry the syntactic and resolution facts. `mixed_usedBackends` and `mixed_registrations_distinct` need no acceptance: which identities a term names is readable from the term alone, and registration is a registry lookup. The required per-literal string lemmas that would have let a real `ord@1` numeric certificate be accepted inside the Lean kernel are infeasible: `ord@1` acceptance routes through `Cell.parseDecimal` → `parseUnsigned` → `String.splitOn`, and through `parseCanonInt` → `String.startsWith`. Under the current Slice-based `String` API those functions are kernel-opaque, so `rfl`, `decide`, `simp`, `exact?`, and `grind` all fail on literal goals and unfolding the recursion diverges. `native_decide` would close the gap and is forbidden: the axiom gate admits only the standard trio, and `native_decide` would add `Lean.ofReduceBool`. What does reduce per-literal is `String.toNat?` (via `String.toNat?_eq_some_ofDigitChars`), string-literal equality, `String.toList`, and `String.length`; `Lara.NDNamed.parseCanonNat_repr` proves `parseCanonNat (Nat.repr n) = some n` generically and is the place to start if this is revisited. A later reader should not "fix" the split back without first checking whether the core `String` API has gained the reduction lemmas.

Cross-language conformance for the mixed case uses a golden file only. Lean emits the mixed term's `certDeps`, a committed golden pins it, and a Haskell test asserts the same list. The cross-language golden uses shipped backends on both sides; `certDeps` needs only resolution and `Backend.uses`, and `ord@1`'s `ordUses` routes through `decodeCert` → `decodeSlot` → `parseCanonNat` → `String.toNat?`, which is per-literal provable. So the one artifact where both languages compute the same thing over the same two shipped backends, `nd@1` and `ord@1`, is unaffected by the in-kernel acceptance limit. The worked mixed `nd@1`/`ord@1` acceptance vector lives in Haskell (`test/StrictSpec.hs`), running on the shipped `inferSupport` and `buildCertOk` path. Lean's `ord@1` and `ra@1` results have stopped at the resolution layer for exactly this reason since before this work.

### The claims boundary

The following may be claimed: one checked support term may carry certified strict instances from different registered backends, each accounted in its own logic, with no shared backend logic introduced (`hetero_occurrences_accounted`); certificate dependencies are exactly the union of the occurrence-local backend reports (`certDeps_eq_union`); a premise or discharge subterm may be replaced by any term of the same conclusion and obligations without disturbing the parent's typing, and the replacement may be certified by a different identity (`prem_subterm_swap`, `dis_subterm_swap`, instantiated at `mixed_swap` and `mixed_dis_swap`); the set of backend identities a term names is source-visible, and every name in it is registered and discharges an occurrence (`usedBackends_accounted`); and backend identity is quantified independently at each occurrence, since the existential in `OccurrenceConsequence` binds `core.Form`.

The following must not be claimed. Lean does not reject a backend-leakage program; it cannot be written, so there is nothing to reject, and the Lean content is the positive firewall theorem plus the non-expressibility note while the rejection artifact is the Haskell wire vector. Different registered identities do not have different formula types; that is not provable, not stated, and not true in general, since a registry may map two identities to one core, and what is claimed is the absence of a binder relating them. This is not parametricity: it quantifies over registered identities, not relationally over related backends, the same distinction the theory-pw spine draws. The Lean mixed witness does not use two shipped backends in its typed results: `mixed_swap` and `mixed_dis_swap` use `nd@1` plus the fixture core, and only the syntactic, resolution, and `certDeps` results use `nd@1` plus `ord@1`. And a backend certificate never establishes the empirical truth of a measurement or a claim: acceptance is a fact a verifier re-runs, and the leaves it depends on stay defeasible.

## 7. Why modal, evidence, or justification logic is not the source semantics

### Proposition 6: ordinary modal logic cannot determine dependency reports

Let two evidence-labelled structures have the same Kripke frame and propositional valuation but different leaf identities, provenance, or source positions. Every formula of ordinary propositional modal logic has the same truth value in both structures, while Lara's required dependency or attack report can differ.

**Proof.** Induct on modal formulas. Atomic truth uses only the shared valuation; Boolean cases use the induction hypotheses; `box` and `diamond` use only the shared accessibility relation and the induction hypotheses at related worlds. Evidence labels and source positions are never inspected. Therefore modal truth is invariant under changing only those labels. Lara's `leaves(w)` and positional targets inspect exactly those labels, so they are not determined by the ordinary modal reduct. QED.

This does not show that modal logic cannot be extended with names or proof terms. It shows that ordinary S4 alone omits information the checker is required to preserve. S4 remains appropriate inside an adapter whose certificate restores that information.

### Proposition 7: factive LP cannot interpret source support

Assume source support `w : p` is interpreted as LP assertion `t:p`, and the intended source models permit policy-valid support for a proposition that is false in the world. Then LP reflection `t:p -> p` is invalid for that interpretation.

**Proof.** Choose an intended source model with `w : p` accepted and `p` false; such models are required because Lara validates structure relative to leaves and policy rather than empirical truth. The proposed interpretation makes `t:p` true and `p` false, falsifying `t:p -> p`. QED.

Thus factive LP may certify a strict conditional step but cannot supply the meaning of source support. J/J4 avoids this particular contradiction by omitting reflection.

### Proposition 8: monotonic consequence cannot represent defeat-driven retraction

No monotonic consequence relation can, by itself, represent Lara claim acceptance under framework extension.

**Proof.** Let input `X` contain a complete unattacked support for `p`, so `p` is `justified`. Extend it to `Y` by adding a checked, undefeated attacker, so `X` is a subset of `Y` but `p` is no longer `justified`. If acceptance were represented by a monotonic consequence relation, `X |- p` and `X subseteq Y` would imply `Y |- p`, a contradiction. QED.

Ordinary S4, LP, J, and J4 are monotonic and therefore cannot be the whole status semantics. Their strict consequences can still be used behind the backend interface.

### What these propositions do not exclude

Evidence logic is not excluded. Neighborhood and dynamic evidence logics can model evidence-sensitive belief and, in some variants, update, and no theorem above rules one out. The current design does not make one the source calculus because it still needs certificate syntax, policy obligations, provenance, and positional attack diagnostics. Use it as policy or admission semantics when a corpus requirement for evidence aggregation appears; only a monotonic evidence-entailment fragment may satisfy the strict-backend contract.

Default justification logic is not excluded either. Pandzic-style systems already combine justification terms and defeasibility, and they are a genuine alternative that Proposition 8 does not rule out. Lara chooses the ASPIC+/Dung route because it directly supplies the required rebut, undercut, and undermine structure, skeptical grounded status, and a small executable compilation target. The paper must defend this choice through the certificate-language delta and corpus fit, not by claiming default justification logic is incapable.

## 8. What proof cannot decide

Four design questions require evidence rather than theorem proving:

1. Whether LP earns its implementation and explanation cost. Backend replacement proves that LP is not foundational; it cannot prove that LP is useless. Measure the fraction of corpus steps requiring `t:F`, `!`, `+`, or realization, and compare certificate size and checking cost.
2. Whether a claim-support policy is epistemically adequate. A sound checker can establish correct instantiation only relative to `Pi`. Policy quality requires expert sourcing, corpus coverage, sensitivity analysis, and adjudication.
3. Whether natural language was faithfully formalized. The `nl`/`formal` binding remains an audited empirical translation. No backend soundness theorem closes that gap.
4. Whether a backend encoding and theory match the intended domain. Soundness is relative to `encode_beta`, `T`, and `models_beta`. A theorem can show the executable checker implements those definitions; it cannot show that they faithfully represent an experiment, program, or scientific concept. Audit and evaluate backend encoding and theory selection separately.

These are evaluation obligations. Presenting them as missing proofs would confuse mathematical validity with empirical adequacy.

## 9. Corpus and conformance evidence for the optional backends

The frozen `corpus-v1` reports one claim-support strict row, `1/1` (`adaptive-pruning/C04`, `ra@1`). No corpus unit exercises `ord@1` or `insp@1`; extending the corpus with units for them is deferred to a `corpus-v2` cycle. So the evidence for the two optional backends is of a different kind from corpus coverage, and the paper must say so.

For `ord@1`, the motivation is that the comparison shape is pervasive in the literature, and that is currently a design argument rather than a measurement: no real paper's beats-claim has gone through the backend. The demonstration lands in `examples/` instead. `examples/S3` is the `num_le` tie, sitting exactly on the boundary where the two family members separate. `examples/S4` has an audit undermining the binding leaf, so the bridge is defeated while the certified comparison stays justified. Together with `examples/S2` these are three artifacts sharing one shape and varying one thing each, which is what makes them readable as a set.

For `insp@1`, the corpus evidence is the M0 C13/C14 count of 3 of 60 sampled claims for the `code_inspection` shape. The worked example `examples/S9` carries the demonstration against C09's shape.

Conformance and mutation evidence covers both shipped backends. `test/StrictSpec.hs` and `test/InspSpec.hs` (23 property groups) exercise the adapters against the seam obligations as conformance evidence, not soundness proofs. Golden anchors are byte-compared across both drivers by `scripts/differential.sh`: the four hand-authored wire anchors under `fixtures/corpus/insp-*.sexp` plus `examples/S9`. The mutation refresh added `S9` (`insp@1`) and `S2` (`ord@1`) together, 27 verified mutants each, growing the seeded suite from 541 to 595 and the measured input set from 601 to 655; all previous mutant bytes were unchanged. `S9`'s `cert-payload-tamper` replaces an `inspect` payload with `mut_corrupt` (R13), and `cert-theory-swap` changes an `inspectdiff` theory digest (R7 allowlist rejection, before backend replay), covering decoder and allowlist rejection rather than every semantic recheck branch. `MutationSpec.prop_backendCertificateCoverage` pins both backends' measured certificate cases. These counts are historical measurements, recorded with their sources; the clean measurement snapshot and publication procedure are in `evaluation.md#frozen-provenance-current-evaluation-freeze-v8`.

Because `corpus-units/` is a frozen input row, adding a corpus unit for a new backend regenerates the seeded mutant suite, invalidates `measurements/frozen/`, and forces a fresh freeze tag. That is a `corpus-v2` scale task, and it is worth doing properly rather than by appending a single unit to an otherwise frozen sample: a corpus unit would answer "do real beats-claims fit this shape without distortion?", which is an empirical question about the modeling and wants the same sampling protocol the original 60 used.

### What a corpus unit would need

Recorded so the deferral does not lose the design. `examples/S2` is the template; a corpus unit instantiates it with a real paper's numbers.

- Two reported cells as observed leaves, each carrying exactly one numeric literal (the premise-cell convention) and its own `refs` into the artifact's evidence.
- A binding leaf, `S2`'s `comparison_setup`, naming which systems and measurand the two numbers belong to. This is the piece a real paper usually leaves implicit in a table caption, and eliciting it is the part of the lowering that will take judgment.
- A strict re-check rule with `certifiers = [(ord@1, <digest>)]` and an empty theory, plus a defeasible bridge rule consuming the comparison and the binding. Both already exist verbatim in `examples/S2/ord-v1.policy.lara`; a corpus policy would adopt them rather than reinvent them.
- A decision about `corpus-v1`'s rule vocabulary. The existing corpus policy has no comparison family, and adding one is a policy change affecting every unit's `unit.core.sexp` through the shared policy, which is why this is a `corpus-v2` question and not a unit-level edit.

## 10. Scope and claims boundary

A strict certificate establishes deductive validity relative to its premise conclusions and declared theory. It does not establish empirical truth: not the truth of a premise, not the faithfulness of a measurement, and not the adequacy of a formalization. The evidence leaves stay defeasible and admission-governed, and the four questions in section 8 stay evaluation obligations rather than proofs.

Consequences for how the system is described:

- The foundation is the claim-support calculus plus compilation to grounded argumentation, not LP or S4.
- `spec.md` defines one backend-parametric strict rule and one reference natural-deduction adapter.
- LP realization belongs to optional-adapter metatheory and related work.
- The trusted-base report lists the selected adapters and theory digests for each run.
- The evaluation reports certified versus trusted strict steps per backend. The previous single "LP witness fraction" is a backend-neutral strict-certification rate.
- Existing LP code is retained as an experimental adapter seed, not the trusted core of Lara.

## 11. Sources and audit mapping

The seam and its obligations are implemented in `src/Lara/Strict.hs` (interface and registry), with adapters in `src/Lara/Strict/ND.hs`, `src/Lara/Strict/Ord.hs`, `src/Lara/Strict/RA.hs`, and `src/Lara/Strict/Insp.hs`, and term-level dependency accounting in `src/Lara/Strict/Deps.hs`. The driver reaches backends and surfaces reports through `src/Lara/Driver/Internal.hs` (`runCheckDeps`, `unitCertDeps`, the `lara deps` subcommand).

The theorems and their Lean sources: Theorems 1, 3, and 4, Lemma 5, and the strict-step soundness obligations are mechanized under `lean/Lara/` with the natural-deduction adapter in `lean/Lara/ND.lean`; Theorem 2 is `Erase.backend_replacement` and `EraseTransport.backend_replacement_transport` in `lean/Lara/Erase.lean`; the composition results are in `lean/Lara/BackendComposition.lean` and `lean/Lara/Examples/BackendComposition.lean`; the `ord@1` results are in `lean/Lara/Ord.lean`; the `insp@1` results, including `enc_iff` via `equiv_iff_nf_eq`, `inspReplay_iff`, `inspSound`, the obligation-4 laws `inspUses_covers`, `inspUses_valid`, and `inspUses_account`, the domain theory (`relHolds_absent_of_nil`, `relHolds_present_of_unique`, `relHolds_polarity_excl`, `relHolds_unique_absent_excl`, `inspModels_diff_halves`, `inspModels_one_witness`), and the contrary-pair theorems are in `lean/Lara/Insp.lean`. Every result named here is pinned in `lean/AxCheck.lean`, and the audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

The conformance and golden surfaces are `test/StrictSpec.hs`, `test/InspSpec.hs`, the wire anchors under `fixtures/corpus/`, the worked examples `examples/S2` through `examples/S7` and `examples/S9`, and the cross-language harnesses `scripts/differential.sh` and `scripts/admission-differential.sh`.

## Supporting declaration index

The subject contracts above use the following supporting declarations. Their source files retain the proof details; `lean/AxCheck.lean` records the public theorem audit. This index does not strengthen any theorem assumption or turn a witness into a general result.

| Lean source | Supporting declarations |
| --- | --- |
| [`lean/Lara/Complexity/Numeral.lean`](../lean/Lara/Complexity/Numeral.lean) | `Lara.ND.decodeNat_repr` |
| [`lean/Lara/ND.lean`](../lean/Lara/ND.lean) | `Lara.ND.decodeNat_leading_zero_01`, `Lara.ND.decodeNat_repr` |
| [`lean/Lara/Support.lean`](../lean/Lara/Support.lean) | `certStep_deps_subset` |
