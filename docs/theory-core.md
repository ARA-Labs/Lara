# Lara base language: support, compilation and observation

Lara's base language turns declared claim support into an argumentation framework and a claim verdict. This document is the subject reference for that layer. It covers the support-term calculus and its obligations, the compilation carrier and the framework image it induces, semantics-parametric observation, restricted-class complexity, one-step source updates, contextual equivalence and backend replacement, generic semantics and relational parametricity, the verified surface calculus, and located and term-level holes.

`docs/spec.md` is the normative contract for the language. This document records the design, the exact theorem contracts, and the limits, and it cites declarations in `lean/` rather than restating the metatheory. Claims that were once backed by a milestone status line are stated here as current contracts; where a result was superseded, the current statement is given and the superseded reading is noted only where it still bounds what may be claimed.

## Support calculus and obligations

Lara has one syntactic category for arguments. Every argument, whether a strict certificate-checked step or a defeasible overridable one, is a **support term**:

```text
w ::= l | r⟨w₁,…,wₙ ; {q ↦ w_q} ; {o}⟩
```

Strict and defeasible are a *mode* of the policy rule `r`, not separate syntax. A strict instance is the degenerate case with an empty critical-question map and no holes, and it carries either an explicit trust marker or an opaque certificate for a registered backend.

The central judgment is `Σ; Π; Γ; R ⊢ w : F ▷ O`, read "`w` supports `F` with open obligations `O`". The leaf dependency set `leaves(w)` is the frontier of the term, derived rather than tracked, and backend-certificate dependencies are reported separately. Proof-term traditions supply the term discipline, not Lara's axioms: the LP axioms A0 to A4 and realization, when used at all, belong only to an optional LP adapter and are not axioms of the source calculus.

The support judgment is **non-factive**. There is no support-level justification operator (`justified(term, prop)` is absent from the language). A strict backend receives only encoded premise conclusions and returns acceptance, dependencies, and diagnostics. Its formulas and proof terms cannot enter source syntax, so even a factive backend cannot eliminate support into truth.

Attacks are **positional**. `rebut w u` targets the root conclusion of `u`, `undercut w u@π` targets the rule occurrence at position `π`, and `undermine w u@π` targets the leaf occurrence at `π`. Rebut and undermine type-check against a policy-declared contrary relation, not full classical negation. The three attack types are the three kinds of positions in a term: root to rebut, internal rule occurrence to undercut, frontier leaf to undermine. Attack well-formedness therefore becomes subterm-occurrence checking plus the contrary relation, which is decidable and local, and source-located diagnostics come for free because a position *is* a location.

Four things are deliberately absent from the support level: backend-specific sum, proof variables, modalities, and internalized justification operators. Multiple independent supports for a claim are multiple support terms, that is, separate argumentation-framework nodes, and never one backend-combined term.

The evidence for this shape is threefold. Factivity is wrong for empirical support: LP's axiom A1 (`t:F → F`) says justified implies true, which is correct for mathematical proof and exactly what Lara's honesty story denies for empirical support, so Lara avoids the support-level modality entirely and confines every strict logic behind the backend interface; adapter opacity is the stronger firewall because it also covers classical provers, model checkers, and future backends. Backend combination can destroy defeat granularity: LP's `s + t` merges alternative supports into one term, while the defeat semantics needs them as separate framework nodes so that an undercut kills one support while the other survives. Accountability holds by construction: the former judgment component `L` and the intended leaf-accountability theorem collapse into a structural fact, that the leaf dependency set of a checked term is exactly the set of leaf constants occurring in it, while backend theory dependencies stay explicit through each certificate's `uses_beta` and are not misclassified as leaves.

### Claims and the supports relation

A claim is a triple and `supports` is normalized identity:

```text
claim c
  nl      = "Method M improves accuracy on distribution D"   -- primary, human-facing
  formal  = atom                                             -- the checkable target
  binding = { author, rationale, audit-status }              -- untrusted, audited
```

The relation `w supports c` holds exactly when `concl(w) ≡ c.formal`, where `≡` is structural identity up to the fixed total normalization of `spec.md` §3.2: literal canonicalization plus structural recursion over ground atoms, with no argument reordering and no binders. No entailment, no solver, and nothing extra is added to the trusted base. The NL-to-formal link in `c.binding` is not a checker obligation. It is the single most load-bearing unchecked step, it is a first-class, versioned, human-signed audit field, and it is evaluated on the semantic-faithfulness axis and never proven.

Policy-declared entailment is strictly more expressive but is not part of v0.1, because it would put an entailment procedure in the trusted base. The forward path is to add it as sugar: an explicit `entails` support step whose own conclusion is discharged against `c.formal` by identity, so the trusted core never grows.

At the support level, `prop ::= atom`. Implication, falsum, modalities, and domain-specific formula formers belong to backend encodings only. Conflict comes from the declared contrary relation and not negation-to-falsum, and implication is reified as a named rule and not a proposition. Undermine attacks a leaf's proposition only, not its admissibility: admissibility is entirely a §4.3 pre-evaluation policy decision (admit, quarantine, or reject) and never creates an attack.

### Strict certificates and the backend interface

A strict rule `r : P₁,…,Pₙ ⇒ C` instantiated at `theta` may carry a backend certificate `kappa`:

```text
check_beta(T,
  [encode_beta(P₁theta), ..., encode_beta(Pₙtheta)],
  encode_beta(Ctheta),
  kappa) = accept
```

Every registered backend proves that acceptance implies

```text
T ; [encode_beta(P₁theta), ..., encode_beta(Pₙtheta)] |=_beta encode_beta(Ctheta).
```

This is a conditional deductive skeleton that does not privilege LP. The backend theorem establishes local consequence, and premise truth is neither exported nor assumed by the source checker. Support-layer defeat propagates through subargument closure regardless of certificate internals. Backend adapters and their acceptance contracts are specified in `docs/strict-certificates.md`; heterogeneous backend composition, the firewall theorem, and the accounting laws are recorded there in "Heterogeneous composition: the firewall and the accounting laws".

A rule can be strict in two ways, and the trust-reduction measure distinguishes them. A **strict, trusted-policy** rule is an indefeasible trusted policy schema or domain law; it stays in the policy trusted base and receives no semantic-consequence theorem. A **strict, certified** rule is discharged by a registered backend relative to its declared, digest-addressed theory. The trust-reduction measure is the fraction of load-bearing strict steps that carry an accepted certificate, broken down by backend and theory. Whether LP earns a place is empirical: measure the strict steps that need LP-specific `t:F`, `!`, `+`, or realization. Backend replacement proves that the choice does not alter claim-support status when adapters accept the same instances; it cannot prove which adapter is useful on the corpus.

Factivity is exactly one axiom, present in JT/LP and absent in J/J4. Rather than choose one justification logic for every strict domain, Lara removes the support-level modality and confines every strict logic behind the backend interface, which also covers non-justification-logic backends such as arithmetic checkers and model checkers. The source non-factivity theorem is syntactic: by inversion on the source rules, no rule concludes a truth judgment because no such judgment exists. This is stronger and more general than recognizing A1 only for an LP constant specification. Pandžić's default justification logic is factive and confines defeasibility by keeping the inference license out of the evidence base and retracting at the extension layer; his `t:F` is therefore factive-within-an-accepted-extension, never globally non-factive, and Lara departs from him on exactly this axis.

### Defeat conditions and the strict-conclusion well-formedness guard

The ASPIC+ guardrails fix the attack discipline. Strict rules cannot be undercut or rebutted: `undercut` targets defeasible rule occurrences only, and `rebut` targets arguments whose top rule is defeasible. A conflict "behind" a strict rule must be reachable through a defeasible step, or it is silently dropped, which is the single most common way these systems violate consistency.

Under grounded semantics with an arbitrary contrary relation and no transposition, only sub-argument closure is free. Direct and indirect consistency and closure under strict rules fail in general, because a conflict that surfaces only after a strict rule is invisible to the attack relation. Two repairs exist. Path A gives the contrary relation enough structure to define transposition, a total involutive contradictory map with `−−φ = φ`, and closes strict rules under transposition, which buys all four rationality postulates under grounded semantics; negation then lives in the contrary relation rather than the proposition language, so "no classical negation in propositions" survives. Path B, which v0.1 adopts, forbids strict rules from producing contested conclusions, via a compile-time well-formedness check that no strict-rule consequent, nor any proposition on a strict chain, can overlap either side of a declared contrary pair at the ground-instance level. Then every conflict is rebuttable at a defeasible step, strict closure introduces no new conflict, and direct and indirect consistency hold by construction. This keeps the contrary relation arbitrary and adds no negation, at the cost of a real expressiveness limit: strict chains may only target uncontested claims. Path A is the reopening criterion if the corpus shows strict rules genuinely feeding contested claims. The policy law is mechanized: `Policy.WellFormed` (`lean/Lara/Policy.lean`) forbids any declared contrary either of whose sides overlaps a strict-reachable conclusion pattern, and `StrictReachable` is exactly "conclusion of a declared strict rule".

One caveat carries from Pandžić: LP sum and accrual `t:F → (t+u):F` is not adopted at the support level, because monotonicity fails once a defeater co-occurs. Sum may exist inside an optional LP certificate, where it cannot merge source argument nodes.

### Relation to default justification logic

Pandžić's default justification logic represents defeasible arguments as object-level terms `t : F` and covers rebutting, undercutting, and undermining attacks (Argument & Computation 2022, doi:10.3233/AAC-200536; Ann. Math. Artif. Intell. 90(2-3):297-337, 2022, doi:10.1007/s10472-021-09765-z). Terms-as-defeasible-arguments is therefore viable prior art, and Lara must not claim it as the novelty.

The delta Lara contributes over that logic is what it adds as a language and system:

| Pandžić's logic | Lara's language and system |
|---|---|
| Operator-theoretic default justification logic | A checkable certificate language with versioned policies |
| Default rules, no completeness obligations | Scheme instances with critical-question obligations and explicit holes |
| Undermining via belief-revision contraction | Undermining via a typed, policy-declared contrary relation (smaller trusted base, decidable) |
| No provenance, artifacts, or admission | Provenance-gated leaf admission, artifact digests, replay identity |
| Semantics given logically | Checked compilation to Dung frameworks with mechanized soundness, accountability, and status-preservation theorems |
| No implementation or evaluation | Haskell checker, untrusted-LLM producer (proof-carrying-code architecture), corpus evaluation |

The paper should cite Pandžić in the must-read tier and claim the calculus-as-language: policy obligations, positional attacks, the compilation theorem, mechanization, and four-state aggregation. It should not claim terms-as-arguments as the novelty.

The question "does LP earn its keep?" no longer determines the core calculus. Backend replacement proves that claim-support semantics is independent of certificate internals when acceptance profiles match, so the corpus decides only whether the optional LP adapter ships. The pitch is: a claim-support calculus with a small strict-certificate interface, where terms give syntactic accountability and positional defeat, argumentation gives the non-monotonic semantics, and registered backends reduce trust in strict steps without defining claim-support semantics.

### Reopening triggers

Three conditions would justify changing the frozen support-calculus decisions. Reintroduce an internalized justification operator if meta-level claims ("the paper argues that", claims about other arguments) turn out to be a material fraction of the corpus. Promote the optional LP adapter, with a dedicated payload codec and realization results in the paper body, if strict modal-deductive chaining is common rather than rare. Revisit belief-revision-style undermining if the typed contrary relation proves too weak to express the undermining attacks annotators actually find.

## Compilation carrier and image

A *conclusion-labelled argumentation framework* is the compiler's output: a finite directed graph of arguments and attack edges in which each node also carries the proposition it concludes, so claim statuses can be read off the graph.

### The carrier and the erasure

The carrier is a conclusion-labelled finite argumentation framework with a total Boolean attack relation:

```lean
structure StructuredAF where
  nodes  : List Atom          -- node i's conclusion, in declaration order
  attack : Nat → Nat → Bool   -- the compiled closure-edge relation
```

`Lara.Invariants.StructuredAF` (`lean/Lara/Invariants.lean:67`). Node identity is the declaration-order position, matching `Compile.toAF`, where `Grounded.Arg = Nat` already indexes `CheckedProgram.args`.

The erasure is `eraseAF` (`lean/Lara/Invariants.lean:84`), which drops the conclusion labelling and keeps positions and edges. It is not a new construction: `Invariants.erase_compileUnit` proves that erasing a compiled accepted unit returns exactly `Compile.checkedAF`, the framework the existing pipeline already evaluates.

The invariant record is `CompilerInvariant` (`lean/Lara/Invariants.lean:121`), with two fields, `ranged` and `conflictComplete`. The choices were forced rather than convenient. Three carriers were considered: a naked framework (`Grounded.AF`) is uninformative, because the constraint that makes the image interesting, that edges are forced by the fixed contrary policy, is invisible without node labels; a term-labelled framework is vacuous, because "realizable" would degenerate to "already built out of checked support terms"; the conclusion-labelled framework is chosen, with enough structure to state the forcing constraint and little enough that realizability is a real question in both directions. The choice is also adequate: `Invariants.status_compileUnit` (`:257`) proves that the four-state status of any claim, computed entirely inside the carrier, equals the status the existing pipeline reports over `Compile.checkedAF`. Nothing an accepted unit says about a claim survives outside `StructuredAF`, which is what licenses quantifying over carriers instead of over programs.

There is no `attackable` node label. `Compile.AttackComplete` (`lean/Lara/Compile.lean:646`) is guarded by `Compile.ConflictAttackable` (`:512`), a property of a support term (a leaf, or an instance whose root rule is defeasible), so the obvious reading would need a per-node Boolean label. It is redundant: `Consistency.wellFormed_contrary_target_attackable` (`lean/Lara/Consistency.lean:42`) proves that in a well-formed accepted policy a contrary target can never be a strict-rule root, so conflict attackability follows from the contrary match itself. `CompilerInvariant.conflictComplete` is correspondingly unguarded, a strictly stronger invariant than the guarded version would have been.

### The invariant record

The table classifies every invariant named in the compiler scope by its layer, its Lean home, and its rejecting counterexample. *carrier* means visible in `StructuredAF` as a field of `CompilerInvariant`; *source* means an invariant of the source judgment, quantifying over term structure that erasure discards, so it constrains which carriers arise but cannot be restated as a carrier predicate; *adequacy* means not an invariant with a violating instance but a theorem that the carrier retains an observation.

| # | Invariant | Layer | Lean declaration | Rejecting counterexample |
| --- | --- | --- | --- | --- |
| 1 | Endpoint-safe pruning | carrier | `Invariants.CompilerInvariant.ranged`; holds by `Invariants.compileUnit_ranged` (`:162`), from `Compile.edgeB_faithful` (`Compile.lean:821`) | `Examples.CompilerInvariants.unrangedEx` (`:30`), rejected by `unrangedEx_not_realizable` (`:41`) |
| 2 | Conflict completeness (forced edges) | carrier | `Invariants.CompilerInvariant.conflictComplete`; holds by `Invariants.compileUnit_conflictComplete` (`:175`), from `Unit.CheckedUnit.attack_complete` (`Lara/Unit.lean:200`) via `Compile.complete_conflict_edge` | `Examples.CompilerInvariants.unforcedConflictEx` (`:58`), rejected by `unforcedConflictEx_not_realizable` (`:71`); non-vacuous off the diagonal by `unforcedDistinctConflict_not_invariant` (`:118`) via `sharedContrary` (`:114`), which forces an edge between the distinct conclusions `pTa`/`qTa` under `Examples.dpShared`. Without it the field would be witnessed only where row 3 already bites |
| 3 | Self-attack condition | carrier (derived) | `Invariants.compileUnit_selfConflict` (`:217`), the `i = j` diagonal of #2, not an independent field | `unforcedSelfConflict_not_invariant` (`:97`), non-vacuous by `selfContrary` (`:89`); source-level witness `Examples.GroundedConsistency.missing_self_edge_rejected` (`:128`) |
| 4 | Conclusion and claim ownership | adequacy | `Invariants.support_compileUnit` (`:246`), carrier support agrees with `Consistency.claimSupportFor` (`Consistency.lean:63`); lifted to status by `Invariants.status_compileUnit` (`:257`) | none: a violation is not a framework but a disagreement between two projections, which the theorem excludes |
| 5 | Subargument closure | source | `Compile.Covered` (`Compile.lean:542`), decided by `Compile.coveredB_iff` (`:553`) over the per-attack closure test `Compile.attackClosureB_iff` (`:459`); `Compile.closure_includes_direct` (`:707`) shows closure extends, never replaces, the direct attack | `Examples.CompilerInvariants.closure_rejects_noncontaining_target` (`:133`): in the running fixture node `0` is in range and is the attack's own source, yet receives no edge because it does not contain the attacked occurrence. Closure adds edges onto containing arguments only |
| 6 | Positional attack coherence | source | `Compile.AttackOcc` (`Compile.lean:76`), `attackOcc_unique` (`:82`), `target_contains_occ` (`:97`) | the inversion theorems are the rejections: `Attack.undercut_target_rule` (`Lara/Attack.lean:622`) and `Attack.undermine_target_leaf` (`:632`) exclude the mismatched position kinds; `rebut_top_defeasible` (`:590`) and `undercut_pos_defeasible` (`:603`) exclude strict occurrences |
| 7 | Strict-chain well-formedness | source | `Support.cert_steps_accounted` (`Lara/Support.lean:1361`) over `Support.CertStepIn` (`:1162`) | closed by the heterogeneous-backend firewall; see the paragraph below and `docs/strict-certificates.md` |
| 8 | Declared-identity preservation | source | `Compile.CheckedProgram.nodup` (`Compile.lean:588`); `Unit.CheckedUnit.nodes_terms` (`Lara/Unit.lean:205`) aligns the cache with the argument list | none at the carrier level, deliberately: two nodes may share a conclusion. Term-level identity is a source invariant and is not observable after labelling |

Row 7's invariant holds, and it is closed by the heterogeneous-backend firewall: a parent cannot inspect a child's formula type, so cross-backend leakage is *inexpressible* rather than merely rejected. The firewall itself is `prem_subterm_swap` and `dis_subterm_swap`, with named corollaries `mixed_swap` and `mixed_dis_swap`, and the accounting laws are `certDeps_eq_union`, `hetero_occurrences_accounted`, and `usedBackends_accounted`, all in `lean/Lara/BackendComposition.lean` (see `docs/strict-certificates.md`, "Heterogeneous composition: the firewall and the accounting laws"). The Haskell wire vector `prop_crossBackendPayloadRejected` (`test/StrictSpec.hs`) is the rejection artifact, running through `buildCertOk`; there is no Lean rejection term, because the leakage it would reject cannot be written. `cert_steps_accounted` is the pre-existing `Support.lean` result that the accounting law repackages rather than re-proves. The recorded signature well-sortedness obligation is closed at the executable realization boundary by `Realizability.Realization.node_conclusion_wellSorted`, under successful checking and used-leaf ground coverage; it does not add a field to the invariant record. `Unit.CheckedUnit.args_well_sorted` (`Lara/Unit.lean:222`) covers argument terms, not node conclusions, which is why the closure is stated at the realization boundary.

### The compilation image

Fix a canonicalizer `canon`, signature `sigma`, policy `policy`, and backend registry `reg`. The target is an `Invariants.StructuredAF`. `Realizability.StructuredAFIso F G` is equality up to node renaming: its `nodeEquiv : Realizability.Equiv Nat Nat` renames the total position space, `labels` preserves exact optional node labels, and `attacks` preserves the total attack relation. `Realizability.StructuredAFIso.refl`, `.symm`, and `.trans` prove this is an equivalence relation.

`Realizability.Realization canon sigma policy reg F` exhibits all data needed to place `F` in the executable compilation image: a leaf context `Gamma`, finite `ground` input, and raw `Lara.Unit`; an accepted `Unit.CheckedUnit` with an equation showing that `Check.Unit.checkUnit Gamma reg ground raw` returns that accepted unit; equations fixing the accepted signature and policy to `sigma` and `policy`; `GroundCoversUsedLeaves Gamma ground raw.args`; and a `StructuredAFIso` from `Invariants.compileUnit accepted` to `F`. `Realizability.Realizable canon sigma policy reg F` is the proposition that such a `Realization` exists. The definition requires an executable witness; it does not identify realizability with a carrier-only predicate.

Necessity holds for every fixed context. `Realizability.compilerInvariant_iso` transports the frozen record across the isomorphism:

```lean
theorem compilerInvariant_iso
    (hiso : StructuredAFIso F G)
    (hF : Invariants.CompilerInvariant canon dp F) :
    Invariants.CompilerInvariant canon dp G
```

and `Realizability.realizable_invariant` is the only-if direction:

```lean
theorem realizable_invariant
    (h : Realizable canon sigma policy reg F) :
    Invariants.CompilerInvariant canon policy.defeat F
```

The proof applies `Invariants.compileUnit_invariant` to the exhibited accepted unit and transports the result through `Realization.compiled_iso`.

Sufficiency fails, and the failure is fixed-context. For any atom `p`, `Examples.Realizability.oneSelfEdge p` has one node and a self-edge. `Examples.Realizability.oneSelfEdge_invariant` proves it satisfies `Invariants.CompilerInvariant canon emptyDefeat` (its endpoints are in range, and conflict completeness is vacuous because the policy declares no contraries), while `Examples.Realizability.oneSelfEdge_not_realizable` takes any `sigma`, `policy`, and `reg` with `policy.defeat = emptyDefeat` and proves it is not `Realizable canon sigma policy reg`. Under `emptyDefeat` every compiled edge is false, so the record accepts the self-edge while no typed source attack exists. `Examples.Realizability.emptyUnitCheck_ok` supplies a successful executable unit in the same empty-policy context, so the negative result does not depend on an inconsistent checker context.

The counterexample identifies the information erasure discarded. `conflictComplete` constrains which edges must be present, but it does not show that every present edge has a typed source attack. Optional edge support, including support terms, attacked positions, and declared attack provenance, does not survive in `StructuredAF`. There is therefore no `realize` operation under the original quantifiers and no sufficiency theorem. Necessity holds for every fixed context; the empty-defeat theorems refute a converse quantified over all fixed contexts, and they do not establish non-sufficiency for every policy.

`Realizability.Realization.node_conclusion_wellSorted` closes the recorded conclusion-sortedness obligation at the realization boundary:

```lean
theorem node_conclusion_wellSorted
    (R : Realization canon sigma policy reg F)
    {node : Compile.CheckedNode canon R.accepted.policy.ruleLookup
      R.Gamma (Support.certOkOf reg)}
    (hnode : node ∈ R.accepted.nodes) :
    Sigma.WellSorted sigma node.conclusion
```

Its conclusion applies under used-leaf ground coverage; it is not an unconditional theorem about every standalone `Unit.CheckedUnit` value. `Examples.Realizability.nonempty_swapped_realizable` assembles the accepted two-argument `Examples.rawUnitEx`, its nonempty ground input, explicit used-leaf coverage, and a two-node swap that fixes every position from two onward, and `Examples.Realizability.nonempty_swapped_node_wellSorted` applies the theorem to an actual retained node. `lean/AxCheck.lean` audits both declarations.

After the empty-defeat counterexample, candidate extensions to the carrier were evaluated. Checked support terms, declared attack data, source blueprints, and search certificates would store the source witness that `Realizable` already requires, so they would make the converse circular. Endpoint-label edge licensing is not necessary because undercut, undermine, and closure edges depend on erased target occurrences or containment. Empty-policy edge soundness and canonical leaf-only restrictions describe strict subclasses, not the fixed-context compilation image. None of these candidates supplied both an independent compiler-necessity proof and a constructive checker-success proof, so the carrier is retained. This is a decision about the evaluated candidates, not an impossibility theorem for every future carrier extension.

An erased-framework image characterization is omitted. Once conclusion labels and source terms are removed, the surviving endpoint-range condition is generic finite-framework well-formedness rather than a Lara-specific image characterization.

### Paper claims and prohibitions

The paper may claim that executable realizability implies the frozen compiler invariant in every fixed context. It may also claim that a converse universal over fixed contexts is false, citing the accepted empty-policy anchor and the one-self-edge counterexample.

The paper must not state the original unconditional iff, cite a constructive `realize` theorem, or imply that every invariant-satisfying framework has a checked source program. The mechanization contains no such declaration. A generated-policy theorem or a realization-kit theorem, which could use different quantifiers and retain source witnesses that the frozen carrier erases, is proposed follow-up work and not a result.

## Semantics-parametric observation

Argumentation theory has several settle-who-wins rules, called semantics. The observation interface makes the semantics a parameter, so theorems are stated once for an arbitrary semantics rather than welded to grounded. The parameter is not decorative: the pre-parameter development could state every status theorem only for `Grounded.grounded`, so a paper sentence about the compiler being semantics-agnostic would have sat next to mechanized sentences without being one, and the grounded-only reading is now recovered as a theorem rather than an assumption.

### The interface and the observation layer

`Semantics.ExtensionSemantics` has exactly three fields:

```lean
structure ExtensionSemantics where
  spec : AF → List Arg → Prop
  enumerate : AF → List (List Arg)
  sound : ∀ F, F.args.Nodup → ∀ S, S ∈ enumerate F ↔ (S.Sublist F.args ∧ spec F S)
```

Five instances are declared: `groundedSem`, `completeSem`, `preferredSem`, `stableSem`, `semiStableSem`. `groundedSem.spec` is `LeastComplete`, not `S = Grounded.grounded F`; picking the grounded case out by a first-order condition in the same shape as the other four is what makes a theorem quantified over `ExtensionSemantics` say something about it. The five instances are registered in `Lara.Semantics.Registry`, whose total label and object maps and `allSemantics_complete` ensure every registered constructor appears.

An extension is an order-preserving subsequence of `F.args`. `Semantics.subseqs` and its characterization (`mem_subseqs`, `sublist_ext`, `subseqs_ext`, `subseqs_nodup`, `nodup_flatMap_pair`) live in `Lara/Semantics/Sublists.lean`, because core Lean at `leanprover/lean4:v4.32.0` has no `List.sublists`; the module imports core Lean only and implements the subsequence enumeration locally. `candidates` stays in `Lara/Semantics.lean` because it takes an `AF`.

The carrier bound lives inside the predicates (`Bounded` is a conjunct of `Admissible` and `Stable`), not in the quantifiers. `Grounded.defendedB` scans attackers only inside `F.args`, so under an unbounded reading `[0, 5]` is admissible in `{args := [0], attack := fun _ _ => false}` and the maximality clause of `Preferred` collapses.

The observation layer has two levels, deliberately not defined through each other. `AcceptanceProfile` carries four `Bool` fields (`inAll`, `inSome`, `outAll`, `outSome`), computed by `profile`. Four rather than two because rejection is not the complement of acceptance: `profile_groundedSem_twoCycle` exhibits an argument with all four bits `false`. `ClaimObservation` is `noExtension | observed (s : Status)`, computed by `observe`. `noExtension` is a constructor rather than a side condition because `List.all [] p = true`: on an empty enumeration the acceptance and defeat guards would both fire.

`observe` uses `attackedByB`, not `Semantics.attacked`. `mem_attacked_iff` makes the difference a theorem: `attacked` intersects with the carrier, while `Grounded.labelC` bounds the attacker and leaves the target unbounded. Reusing `attacked` would make `observe_grounded` false.

### Adequacy, representative uniqueness, and exclusivity

`ExtensionSemantics.sound` binds `F.args.Nodup` and no instance consumes it. `Examples.Semantics.sound_holds_without_nodup` re-proves all five adequacy statements with the hypothesis absent from the statement entirely. What `Nodup` buys is that no two entries of an enumeration denote the same set: `candidates_ext`, `candidates_nodup`, and `enumerate_ext`, the last derived for any instance from `sound` alone. It genuinely fails without the hypothesis: `not_candidates_ext_without_nodup` and `not_enumerate_ext_without_nodup` refute both over `dupCarrier`, with `[0]` and `[0, 0]` as witnesses.

The field stays in the record, because an instance whose enumeration depends on unique representatives, such as one deduplicating, counting, or indexing extensions, could not add the hypothesis after the fact.

The grounded instance is pinned exactly. `Semantics.groundedSem_enumerate` proves that `groundedSem.enumerate F` is a one-element list, not merely that some entry exists; `mem_canonize_grounded` pins that entry's members to `Grounded.grounded F` with no hypothesis, and `groundedSem_singleton` fuses both halves so the sublist-representation artifact `canonize` stays out of downstream statements. The regression theorem is:

```lean
theorem observe_grounded {F : AF} (h : F.args.Nodup) (c : Grounded.Claim) :
    observe groundedSem F c = ClaimObservation.observed (Grounded.statusC F c)
```

The `noExtension` arm is excluded rather than assumed, because the singleton makes `isEmpty` provably `false`; `Nodup` is consumed at exactly one place, obtaining the singleton, and the `gap` branch closes before that. `profile_grounded` is the corresponding collapse at the argument level: skeptical and credulous bits coincide under `groundedSem`, which is the precise sense in which the pre-observation development could not tell the two readings apart.

Exclusivity is not free. `justified_defeated_exclusive` needs a non-empty enumeration and conflict-freedom of every extension. `ExtensionSemantics` supplies neither, because its `spec` is an arbitrary `AF → List Arg → Prop`, so conflict-freedom enters as an explicit hypothesis, `SpecConflictFree`, discharged once per instance (`groundedSem_specConflictFree`, `completeSem_specConflictFree`, `preferredSem_specConflictFree`, `stableSem_specConflictFree`, `semiStableSem_specConflictFree`). `observe_justified_not_all_defeated` is the consumer-facing form: when `observe` reports `justified`, the `defeated` guard it never reached is genuinely false. `SpecConflictFree` is phrased over `spec` rather than `enumerate`, which is the only reason `F.args.Nodup` appears in those compatibility theorems: crossing from enumeration membership to `spec` goes through `sound`.

An enumeration-based follow-up adds `EnumerateConflictFree sem F`, requiring conflict-freedom of exactly the extensions returned by `sem.enumerate F`. `justified_defeated_exclusive_of_enumerate` and `observe_justified_not_all_defeated_of_enumerate` prove the same conclusions without `Nodup`, and each of the five instances has an unconditional `*_enumerateConflictFree` discharge proved from its actual enumerator. The old theorems retain their signatures and delegate through `specConflictFree_enumerateConflictFree`; only that bridge needs `Nodup`.

The non-emptiness half is discharged for preferred semantics: `preferredSem_enumerate_ne_nil` holds for every framework, so together with `preferredSem_enumerateConflictFree` exclusivity at preferred semantics is unconditional in the carrier. Dung's existence result for preferred extensions (`Semantics.preferred_exists`, `Semantics.preferred_exists_candidate`) may therefore be cited with no `Nodup` side condition. The proof does not compare two extensions by `⊆`: it takes a longest admissible candidate `S` and meets a competitor `T` at `canonize F T`, where `List.Sublist.filter` places `S` inside the competitor as a sublist rather than as a subset, and `List.Sublist.eq_of_length` closes it. `stableSem` has no non-emptiness counterpart; `stableSem_enumerate_threeCycle` refutes it.

### Source-to-framework transport

`Observation.AttackExtensional` is carrier-locality of a specification: two frameworks with equal `args` that agree pointwise on `attack` at carrier members satisfy the same specification. It is proved for all five specs, plus `attackExtensional_bounded` and `attackExtensional_admissible`.

`Observation.observe_congr` lifts that to observations, and `srcObservation_iff_checked` states the source-level form:

```lean
theorem srcObservation_iff_checked (sem : ExtensionSemantics)
    (hext : AttackExtensional sem.spec)
    (P : Compile.CheckedProgram canon Pi Gamma CertOk dp) (c : Grounded.Claim)
    (hsupp : ∀ i ∈ c.support, i < P.args.length) (o : ClaimObservation) :
    SrcObservation sem P c o ↔ o = observe sem (Compile.checkedAF P) c
```

`SrcObservation` quantifies over every `Edge`-deciding oracle satisfying `AgreesOnArgs`. `srcObservation_checked` is existence and `srcObservation_unique` is functionality, the latter with no hypotheses at all.

Every claim-level transport result carries the support-boundedness hypothesis, including `observe_congr`, `srcObservation_iff_checked`, `srcObservation_checked`, and `srcStatus_iff_srcObservation`. The results that read one framework do not, and `srcObservation_unique` does not either. The hypothesis is necessary where it appears, not an artifact: `attackedByB` bounds the attacker and deliberately leaves the target unbounded (without which `observe_grounded` is false), so `observe` reads `attack` at support arguments outside the carrier, exactly where `AgreesOnArgs` says nothing. `not_observe_congr_of_unbounded_support` is the concrete separation and `observe_congr_needs_support_bound` is the refutation of the hypothesis-free statement.

`Compile.srcStatus_iff_checked` has no support side condition and is unchanged and independently proved; `Lara/Compile.lean` was not modified by the observation work. It is not an instance or a special case of `srcObservation_iff_checked`, whose hypothesis is stronger and whose subject differs. The honest bridge is `Observation.srcStatus_iff_srcObservation`: under the support bound, `Compile.SrcStatus P c s` holds exactly when the `groundedSem` source observation is `observed s`.

### Separations and non-collapse

Every theorem stated generically over `sem` or at one instance would still be compatible with `ExtensionSemantics` being an abstraction over a one-element set, so the example module supplies the separations.

- Nonexistence. `stableSem_enumerate_threeCycle` proves stable has no extension on the bare three-cycle, `observe_stableSem_threeCycle` proves the `noExtension` constructor is reached for an arbitrary supported claim, and `observe_stableSem_threeCycle_ne_justified` and `observe_stableSem_threeCycle_ne_defeated` name the two answers vacuous `all`-guards would otherwise have produced. `threeCycle_enumerate_nonStable` shows the other four are non-empty there, so nonexistence is stable's property and not the framework being hard. The general claim that a framework containing an odd attack cycle has no stable extension is false: adding a fourth argument that attacks all of the cycle leaves the cycle present and gives stable extensions `[[3]]`, and `stableSem_enumerate_threeCycleAttacked` states the edges and that extension in one theorem.
- Ten pairwise separations. `five_semantics_pairwise_distinct` states all ten unordered pairs in a single theorem, so the count is checked by the elaborator rather than by a reader counting theorems.
- Structural contrasts. `preferred_exists_where_stable_does_not`, `semiStable_exists_where_stable_does_not`, `semiStable_proper_refinement_of_preferred`.
- No four-state function realizes both credulous readings. `credulous_not_functional` quantifies over every candidate `AF → Arg → Status` function and refutes the simultaneous requirements `justified ↔ inSome` and `defeated ↔ outSome` under preferred semantics. Argument `0` of the two-cycle makes both bits true, and `profile_preferredSem_twoCycle_symm` shows that argument `1` has the same profile, so a framework-internal tie-break cannot distinguish them.
- `observe` does not factor through `profile`. `observe_not_determined_by_profile` shows `completeSem` and `preferredSem` giving the identical `AcceptanceProfile` for every carrier argument of the two-cycle and different `ClaimObservation`s for the same claim; the mechanism is a checked conjunct, since the two enumerations differ by exactly the entry `[]` and `claimAcceptedB [] claimBoth = false`.
- `AgreesOnArgs` is strictly weaker than `Compile.Faithful`. `agreesOnArgs_strictly_weaker_than_faithful`, from `eJunk_agreesOnArgs` and `not_faithful_eJunk`.

### The observation table and the conformance mirror

`Examples.Semantics.observationTable` is the paper figure: 120 rows, one per (semantics, framework, claim) over five semantics, six frameworks, and four claims, printed by `#eval` from the definitions rather than written by hand, so the figure cannot drift from what it depicts. The row labels come from closed sum types declared in the module (`SemanticsName`, `FrameworkName`, `ClaimName`), each with exactly one spelling table and exactly one map to the object it names, so no row can name one instance and evaluate another.

The `|E|` column is load-bearing rather than decoration. `grounded` and `complete` occupy 48 of the 120 rows, two per (framework, claim) input; on all 24 of those inputs their observations are identical, while their extension counts differ on 12 of the 24, so without `|E|` the table would read as though the two semantics were the same. `reinstatementChain` contributes 20 rows in which all five semantics enumerate the two-element extension `[0, 2]`, so these rows exercise reinstatement rather than only unattacked singleton extensions. The only `noExtension` cells are `stable`/`threeCycle` on the three supported claims, and that same pair reports `gap` on `claimNoSupport` with `|E| = 0`, because the `gap` guard is tested first.

`scripts/check-semantics-registry.py` adds the missing declaration check: it discovers Lean modules from the repository tree and inspects their elaborated environments, including modules outside the library root's imports, and every named, closed declaration of type `ExtensionSemantics` must be referenced by the central registry's object map. A value alias is a separate declaration and must be registered too. This is a repository build guarantee, not enumeration of all inhabitants of an open structure: parameterized semantics families, local values, and external modules outside the audited repository remain outside the finite table, and the semantics interface and its universally quantified theorems remain open.

`src/Lara/Semantics.hs` mirrors the executable layer of `Lara.Semantics`: the powerset scan, the `Bool` deciders, and the five `enumerate` functions, with `test/SemanticsSpec.hs` checking them against golden values Lean computed. The `Prop` layer and the adequacy theorems have no Haskell counterpart, and the `ExtensionSemantics` record is not mirrored, because its content is the bundled `sound` field, without which the record would be a five-element enum of functions dressed up as the Lean interface. Per the repository's mechanization discipline, Haskell property tests are conformance evidence, not soundness; the Lean proofs carry soundness. The goldens agreeing is evidence about outputs on six frameworks under five semantics, not a proof that the two sets of definitions correspond. `prop_goldensCoverProduct` catches a dropped or duplicated row, and `make semantics-goldens` regenerates the Lean block and diffs it against the checked-in Haskell transcript. Neither the enumerations nor `candidates` is a proposed runtime: `candidates` is an exponential powerset scan and the preferred, semi-stable, and least-complete deciders scan that list once per candidate, while the runtime evaluator stays grounded.

### Gate coupling: anything printed during the Lean build

`scripts/check-axioms.sh` extracts every `[...]` in its input and treats the comma-separated contents as axiom names, reading the whole stream rather than only lines matching a declaration report. A Haskell list literal is nothing but brackets, so a `#eval` printing `[[0],[0,2]]` during `lake build` contributes bracket-runs that reduce to the tokens `0`, `0`, `2`, and the gate exits 1 with a spurious "non-standard axiom" error. Two consequences are in force: `renderObservation` prints one word per cell rather than delegating to the derived `Repr`, and the observation table carries no extension lists; the golden emitter, which must print list literals, is guarded on `LARA_EMIT_GOLDENS`, which no build or gate command sets. The hazard is latent rather than active, because the gate loads the example module from its `.olean` and never re-runs the `#eval`. The constraint is recorded because it is invisible from either side on its own: anything that prints during the Lean build shares a channel with the axiom audit, and the coupling is between two files that never mention each other.

### Paper claims

The paper may claim that compilation is semantics-agnostic in a precise sense: the observation interface is parametric in `ExtensionSemantics`, and the pipeline (`Compile.toAF`, `Compile.checkedAF`) never inspects a semantics. The support for this is structural, since `Lara.Compile` does not import `Lara.Semantics` and no observation-layer commit modified it, together with `Observation.srcObservation_iff_checked`, which holds for every `sem` whose specification is `AttackExtensional`. That theorem must not be displayed without its support hypothesis `∀ i ∈ c.support, i < P.args.length`.

The paper may also claim that the four-state status the pipeline already prints is the grounded instance of the general definition, citing `Semantics.observe_grounded`, with `Observation.srcStatus_iff_srcObservation` as the source-level bridge and its support hypothesis named; that all ten pairwise separations among the five semantics are witnessed, citing `Examples.Semantics.five_semantics_pairwise_distinct`; that stable extensions can fail to exist and that `observe` then reports `noExtension` rather than fabricating a `Status`, citing `stableSem_enumerate_threeCycle` and `observe_stableSem_threeCycle` with its two negative halves; and that `gap` is the one semantics-independent status, citing `Semantics.observe_gap` and `observe_gap_iff`, with `observe_twoCycle_grounded_ne_preferred` and `observe_twoCycleSink_grounded_ne_preferred` as witnesses that the other three vary.

The paper must not print the credulous reading as a four-state verdict, since `Examples.Semantics.credulous_not_functional` refutes every `AF → Arg → Status` function that would make `justified ↔ inSome` and `defeated ↔ outSome` under preferred semantics; the credulous reading is exposed only through `profile`'s `inSome` and `outSome` bits. It must not say that `observe` factors through per-argument acceptance data, since `observe_not_determined_by_profile` refutes it; must not assert the general non-emptiness of stable extensions or read `preferred_exists` as licensing one; must not say that `Compile.srcStatus_iff_checked` is an instance or special case of `srcObservation_iff_checked`, or rewrite the existing preservation citation to route through it; and must not state any transport over `Compile.Faithful` on both sides, or claim `AttackExtensional ConflictFree`. The paper must not print the credulous reading as a four-state verdict, since `Examples.Semantics.credulous_not_functional` refutes every `AF → Arg → Status` function that would make `justified ↔ inSome` and `defeated ↔ outSome` under preferred semantics; the credulous reading is exposed only through `profile`'s `inSome` and `outSome` bits. It must not say that `observe` factors through per-argument acceptance data, since `observe_not_determined_by_profile` refutes it; must not assert the general non-emptiness of stable extensions or read `preferred_exists` as licensing one; must not say that `Compile.srcStatus_iff_checked` is an instance or special case of `srcObservation_iff_checked`, or rewrite the existing preservation citation to route through it; and must not state any transport over `Compile.Faithful` on both sides, or claim `AttackExtensional ConflictFree`. `Observation.faithful_unique` proves that any two `Compile.Faithful` oracles for the same program are literally equal, so a transport stated over `Faithful` on both sides would be a `funext` away and the extensionality hypothesis would never be invoked; `not_attackExtensional_conflictFree` refutes `AttackExtensional ConflictFree` on the carrier `[0]` and the junk set `[0, 5]`, with `admissible_transports_on_junk` as the positive contrast on the same framework pair.

## Restricted-class complexity

This section covers the mechanized groundwork for a hardness claim about the restricted program class. It provides a family-wide realization theorem, so every formula's reduction target is a genuinely checked unit, with polynomially bounded cost accounting. The complexity-class claim itself, such as NP-completeness, is deliberately not proved in Lean; the exact mechanized and paper-level split is part of the boundary below.

The module inventory, all `sorry`-free, within the standard axiom trio, and registered in `lean/AxCheck.lean`:

- `lean/Lara/Complexity/Numeral.lean`, verified decimal round-trip and `natRepr_inj` (D7).
- `lean/Lara/Complexity/Gadget.lean`, the formula-indexed 3SAT gadget behind a closed leaf vocabulary (D8), the family-wide `checkUnit_complete` premises, and the assembled checker equation `checkUnit_formula_ok`.
- `lean/Lara/Complexity/Reduction.lean`, the compile image (`reduceCode`, `reduceIso`, `coveredB_gadget`), the frozen promise and size obligations (`reduce_realizable`, `reduce_nodes`, `reduce_byteSize`), reduction correctness (`reduce_correct` and its quoting corollaries), executable fixtures, and the class-membership negative control (`selfEdgeCode_not_realizable`).
- `lean/Lara/Complexity.lean`, the cost-instrumented grounded kernel and the shared carrier-status evaluator.
- `lean/Lara/Examples/Complexity.lean`, the fixed-context realizable quartic witness and the carrier-status transfer.

The formula-independent fixed context (`Lara/Complexity/Context.lean`) and the finite encodings (`Lara/Complexity/Encoding.lean`) predate this closure and were frozen and untouched throughout.

### Frozen decisions

The inherited constraints D1 to D6 came from the motivation and executive review, the spike record, and the crystallized boundaries in `ara/logic/claims.md` (`#C44`, `#C45`) and `ara/logic/solution/constraints.md`. Reintroducing any rejected form requires a new review.

- D1, the fixed context is frozen. Every theorem uses exactly `canon := id`, `m2bSigma`, `m2bPolicy`, `m2bRegistry`. No formula-specific policy, signature, registry, axiom, `sorry`, or placeholder. A construction that needs a per-instance policy changes the class being studied and is out of scope.
- D2, the INCONCLUSIVE record is not evidence. Nothing may reinterpret the earlier spike as support for hardness or tractability; only closed proofs move the class claims.
- D3, a restricted-class witness carries class membership. Tightness and hardness claims require the executable checker equation and a `StructuredAFIso` under the fixed context; `CompilerInvariant` alone is never substituted for realizability.
- D4, the proved universal lower bound is quadratic. The two-node regression refutes only the rejected exact pointwise `n³` inequality at `n = 2`. Quartic statements are existential worst-case results on a realizable family, and documentation must never merge the two quantifiers.
- D5, oracle cost and classical input size use separate frozen representations. `CarrierCode.byteSize` is a carrier accounting measure (framing unit plus atom-key text plus matrix cells plus query-index text), not a serialized wire length; `Formula3.byteSize` is the UTF-8 length of the canonical S-expression.
- D6, the stop rule binds. The realization gate has three outcomes; on INCONCLUSIVE, record the exact obstruction, stop before the hardness phase, keep the issue open, and claim nothing.

The new frozen decisions D7 to D9 are current constraints.

- D7, numeral injectivity comes from a verified decoder round-trip. `natRepr_inj : Nat.repr m = Nat.repr n → m = n` is proved by applying a decoder with a proven round-trip, never by induction over string representations. The decoder is a local copy of the two-line `decodeNat` pattern from `Lara.ND` (round-trip by `simp [decodeNat]` with `Std.Data.String.ToNat` imported), and it lives in `lean/Lara/Complexity/Numeral.lean` rather than importing `Lara.ND`, so the complexity spine does not depend on the natural-deduction backend module.
- D8, the gadget lives in the library behind a closed-sum leaf vocabulary. `rawUnitOfFormula`, `gammaOfFormula`, `groundOfFormula`, and their helpers live in the public `Lara.Complexity.Gadget`, because `reduceCode` and `Reduction.lean` must reference them and library code must not import `Examples`. The move is definitional-identity: every leaf-id spelling stays exactly as the merged shape fixture pins it, and `rawUnitOfFormula_shape` is the regression that proves it. The leaf namespace is a closed sum type `GadgetLeaf` (`negLit`, `posLit`, `occurrence`, `query`) with the single injective encode table `GadgetLeaf.encode`; the string builders are `GadgetLeaf.encode ∘ constructor`, so exactly one spelling table exists.
- D9, the renewed gate. The gate was re-decided from proof artifacts alone, recording exactly one of HARDNESS, TRACTABILITY CANDIDATE, or INCONCLUSIVE; only HARDNESS unlocked the hardness phase. TRACTABILITY CANDIDATE would still have required an independently proved structure theorem, and a failed lemma is not one.

The gate reached HARDNESS: every mandatory theorem named by the superseded INCONCLUSIVE record's obstruction section exists `sorry`-free under the frozen context, and the reduction target family is realizable with polynomially bounded carrier accounting. HARDNESS names the gate outcome only; no NP-hardness claim is made by it. The earlier INCONCLUSIVE record is retained only as the reason for D2 and as the source of the obstruction list that the closure discharges; it is not evidence about hardness or tractability.

### Realization closure: the compositional architecture

The closure proves each premise of the sanctioned completeness surface `Check.Unit.checkUnit_complete` (`lean/Lara/Check/Unit.lean`) as its own parameterized lemma family over `rawUnitOfFormula φ`, then assembles once. The alternatives, manual `CheckedUnit` construction (same obligations, weaker artifact, no executable checker equation) and a replacement gadget (same family-wide obligations, discards the shape fixture, needs a new motivation review), were rejected in review.

The premise-by-premise closure, in dependency order:

1. Numeral foundation (`Numeral.lean`): `decodeNat_repr`, `natRepr_inj`, `repr_no_dash` (a decimal repr contains no `'-'`, which pins the separator in the `occurrence` leaf spelling).
2. Leaf vocabulary and table lookup (`Gadget.lean`): `GadgetLeaf.encode_inj`, `formulaLeafEntries_keys_nodup`, `lookupLeaf_eq_some_of_nodup`, the four `gammaOfFormula_*` lookup corollaries, and ground coverage `groundOfFormula_covers` (`groundOfFormula` is the `Prod.snd` projection of the same table `gammaOfFormula` reads).
3. Structural premises: `formulaArguments_nodup` (per-block Nodup plus pairwise block disjointness), `groundOfFormula_wellSorted`, `formulaArguments_wellSorted`, `signatureStage_formula_none`.
4. Recursive support: `hasSupport_gadgetLeaf`, `hasSupport_clauseArgument` (the fixed clause rule instantiated at `clauseSubst j c`, with the premise-conclusion matches packaged as reusable `simp` lemmas), assembled into `formulaArguments_supported`.
5. Typed attacks and endpoints: `hasAttack_formula` over the three generators (mutual literal-root undermines, positional undermines of occurrences, clause-root undermines of `query`), plus `formulaAttacks_source_mem` and `formulaAttacks_target_mem`.
6. Exact attack completeness (`formulaAttacks_complete`, the highest-risk step): invert `HasSupport` to pin every root conclusion (`formulaArgument_conclusion`), characterize `ContraryMatch` over root conclusions (`contraryMatch_rootConclusion_iff`), then exhibit each firing pair's declared attack. Where numeral injectivity actually fires is not in the `ContraryMatch` characterization itself, because the two `lit ↔ lit` schema rows bind the payload variable once per row, so the positive direction is pattern computation; it fires in the assembly, where `litAtom_inj` (which is two applications of `natRepr_inj` to the `lit` atom's decimal payloads) forces equal variable indices when two root conclusions collide. Without it, two distinct variables with equal reprs would demand an undeclared attack.
7. Assembly: `checkUnit_formula_accepts` (one application of `checkUnit_complete` with the nine family lemmas plus the closed policy facts), the named accepted unit `acceptedUnitOfFormula`, and the headline equation `checkUnit_formula_ok`.

The compile image is `reduceCode φ : CarrierCode`, which lists the gadget conclusions in declaration order with the intended adjacency matrix, and `reduceIso φ`, a `StructuredAFIso` from `Invariants.compileUnit (acceptedUnitOfFormula φ)` to `(reduceCode φ).decode` at the identity position reindexing. The edge half is `coveredB_gadget`: the checker's own closure-edge scan over the generated family equals `gadgetEdgeB`, namely mutual literal pairs, satisfying-literal-to-clause edges (positional undermines compile to edges on the clause argument node), clause-to-query edges, and no closure-generated extras, proved rather than stipulated.

### Cost results and the quantifier boundary

`Lara.Complexity` mirrors `Grounded.defendedB`/`step`/`iter`/`grounded` with an attack-query counter (`groundedC` and friends), with first-projection agreement theorems (`*_fst`) tying every bound to the existing evaluator.

- Short-circuit cost model (frozen). The counter increments exactly once per `F.attack` evaluation, and the mirrors reproduce the left-to-right short-circuit evaluation the Boolean connectives actually perform: a defense scan stops at its first undefeated attacker, and the inner attacker scan runs only after `F.attack b a` answered `true`. This is not a free choice: the frozen regression `groundedC_twoNodeAllAttacks_cost : (groundedC twoNodeAllAttacks).2 = 4`, the two-node all-attacks run costing exactly `4 = 2²`, holds only under short-circuit counting, and it is the negative regression that refutes the rejected exact pointwise cubic inequality at `n = 2`.
- Universal bounds. `groundedC_cost_le : cost ≤ n³(1 + n)` and `groundedC_cost_ge : n² ≤ cost` for every framework, `n = F.args.length`. The pre-existing prose claim that the grounded fixpoint queries the oracle `O(n³)` times was corrected in `src/Lara/Runtime.hs` to these proved facts; the production Haskell runtime itself is not instrumented.
- Worst-case quartic tightness (existential). The three-block family `quarticAF k` (`k−1` neutral `g` nodes then the defender `d`, then `k` attacked `b` nodes, then `k` target `a` nodes; edges exactly `d → b(i)` and `b(i) → a(j)`) is realizable in the fixed context (`quartic_realizable`, with `quartic_size : size = 3k`), and for `2 ≤ k` pays at least `k⁴` attack queries (`quartic_cost_ge`), with closed evaluations at `k = 2, 3, 4`. Together with `groundedC_cost_le` this is worst-case Θ(n⁴) *over the fixed-context realizable class*, never a universal per-instance floor (D4).
- Shared carrier status. `statusSharedC` computes the grounded extension once, only after the empty-support guard, preserving `Grounded.statusC`'s observable guard order, and `carrierStatusC` is the exposed carrier query over `Invariants.eraseAF` and `Invariants.claim`. Agreement is `carrierStatusC_fst = Invariants.status`. Citation discipline: `carrierStatusC_cost_le : cost ≤ n³(1 + n) + 2n²` (with `claim_support_length_le`) is the paper-citable upper theorem, while the generic claim bound `statusSharedC_cost_le` is internal accounting and must not be cited as the restricted-class headline. The quartic floor transfers to this surface: `carrierStatus_quartic_cost_ge` (the `d` claim has nonempty complete support, so the grounded branch runs and is fully counted).
- `Grounded.deficit_bound` bounds rounds, not queries, and must not be quoted as a query-cost result.

### Mechanized and paper-level boundary

Mechanized, and only quotable together, since the `reduce_correct_*` corollaries package them:

- `reduce_correct : Formula3.Satisfiable φ ↔ FixedCredComplete (reduceCode φ)`, two-sided reduction correctness, with soundness extracting a satisfying assignment from a complete extension containing `query` and completeness building the model extension directly, with no unproved admissible-to-complete lemma;
- `reduce_realizable : M2bPromise (reduceCode φ)`, class membership with the executable checker equation and `StructuredAFIso`;
- `reduce_nodes` and `reduce_byteSize` give polynomial output size under the frozen D5 measures, with `reduce_nodes : (reduceCode φ).nodes.length = 2 * variableCount φ + φ.length + 1` and `reduce_byteSize : (reduceCode φ).byteSize ≤ 64 * (Formula3.byteSize φ + 1) ^ 2` and the engineering-cleared constant `64` intact.

Paper-level only: NP-completeness bookkeeping (encodings, machine model, membership in NP). It is deliberately not a Lean statement; the paper cites the mechanized obligations above.

There is no general-framework transfer. No hardness theorem about unrestricted argumentation frameworks was transferred into a restricted-class claim without a fixed-context realization proof. Every reduction output and every lower-bound witness carries its own `Realization` under the frozen context (D1, D3), and `selfEdgeCode_not_realizable`, the one-node `g(0)` self-edge carrier that is not `M2bPromise`-realizable because no `m2bPolicy` contrary row licenses `g(0) → g(0)`, is the negative control that keeps the correctness theorem a statement about the realizable class and not about all frameworks.

Proof-side refactoring deferrals (shared id-canon and pattern helpers, the `checkUnit` ok-assembly boilerplate, and a possible correctness-half split of `Reduction.lean`) have no corpus or freeze-tag impact and are tracked as follow-ups.

## Source updates and status dynamics

This section fixes a one-step source update model, states the hypotheses proved for each constructor, and records the theorem-backed transition matrices. The question it answers: if you edit one declaration of a checked source program, whether by adding a leaf, retracting an argument, or changing an attack, what can happen to each claim's status, and which transitions are provably impossible?

### The source boundary

`Lara.Update.SourceState` in `lean/Lara/Update.lean` contains exactly the raw inputs from which admission and whole-unit checking are derived:

```text
sigma, policy, table, metas, leaves, argsRaw, rawAtts, groups, ground
```

It contains no `CheckedUnit`. `Lara.Update.Accepted reg state` means that an aligned raw-attack resolution exists, `Admission.evaluateAdmission` accepts the raw carriers, and `Check.Unit.checkUnit` accepts the exact pruned unit and checker context produced by that admission result. `Lara.Update.AcceptedRun` retains one proof-relevant successful run: its aligned attacks, admission result, checked unit, admission equality, and checker equality. `AcceptedRun.accepted` forgets those witnesses into `Accepted`.

`Lara.Update.SourceUpdate` is the closed update vocabulary. The first fragment has four constructors; the two completion constructors were added later (D13 and D14, recorded under holes below):

```text
addLeaf id atom metadata
tighten (leaf-kind, provenance)
addAttack raw-attack
addInstance raw-name support-term
dischargeOpen raw-name position question support-term
atomic [atomic-edit]
```

An `AtomicEdit` is one of `addLeaf`, `addInstance`, `addAttack`, or `dischargeOpen`. It is a separate type, so a batch cannot contain a batch.

The `String` in `addInstance` and `dischargeOpen` is deliberate. It names a pre-parse `argsRaw` row; it is not a second parsed argument identifier. Raw attack endpoints use the same pre-parse names. The Haskell mirror in `src/Lara/Update.hs` preserves this exception and otherwise reuses the project's symbolic ADTs.

`Lara.Update.UpdateRejection` is a closed diagnostic type. Its constructor-side cases are `leafNotFresh`, `keyNotAdmitted`, `endpointNotDeclared`, `instanceNotFresh`, and `notDischargeable`; a batch reports its first failing edit as `batchEdit index reason`. Revalidation can also report duplicate raw argument names, attack-resolution failure, source invalidity, source rejection, or whole-unit rejection. No free-form rejection string crosses this boundary.

`Lara.Update.applyUpdate` checks the constructor side condition, edits only the corresponding raw carrier, and calls the real admission and whole-unit checker on the edited state. It returns the edited `SourceState` only after both stages accept. The first four edits append a leaf and its metadata, replace or append one admission row with `quarantine`, append one raw attack, or append one raw argument row. `dischargeOpen` rewrites one raw argument row in place: at the rule occurrence at the position it removes the question from the open set and appends the discharge (`Lara.Update.Discharge.dischargeAt`), and the row keeps its name and declaration index. `atomic` applies its raw edits in order, checking each edit's side condition against the state the earlier edits produced (`applyBatch`), and then admits and checks the final raw state once. There is no admit-to-reject constructor, because `Admission.source_reject_no_checked_unit` proves that a rejected source has no checked-unit target.

The Haskell mirror intentionally stops before `applyUpdate`. It provides constructor and decider conformance, the discharge rewrite, and the raw stage of a batch only. No driver, parser, `.lara` section, wire command, corpus case, or runtime update feature is part of this model.

### Side conditions and preservation hypotheses

The named executable deciders and Lean adequacy theorems:

| Update | Side condition | Decider and adequacy |
|---|---|---|
| `addLeaf` | The id is absent from semantic leaf rows, metadata rows, and every duplicate-group member list. | `AddLeafFresh`, `addLeafFreshB`, `addLeafFreshB_iff` |
| `tighten` | `Admission.decisionFor` returns `admit` at the key; omitted keys default to `admit`. | `AdmittedAt`, `admittedAtB`, `admittedAtB_iff` |
| `addAttack` | Both raw endpoints name rows in `argsRaw`. | `EndpointDeclared`, `endpointDeclaredB`, `endpointDeclaredB_iff` |
| `addInstance` | Both the raw name and the semantic support term are fresh in `argsRaw`. | `InstanceFresh`, `instanceFreshB`, `instanceFreshB_iff` |
| `dischargeOpen` | The raw name resolves (first match, as endpoints do) to a term whose occurrence at the position is a rule instance with the question in its open set. | `DischargeOpen`, `dischargeOpenB`, `dischargeOpenB_iff` (term level: `Discharge.OpenAt`, `openAtB`, `openAtB_iff`) |
| `atomic` | Each edit's own side condition, above, against the state the earlier edits produced. | `applyBatch`; the first failure is `batchEdit index reason` |

The two completion constructors are characterized exactly rather than by sufficient conditions: `applyUpdate_dischargeOpen_ok_iff` (site precondition and acceptance of the rewritten source) and `applyUpdate_atomic_ok_iff` (raw batch success and acceptance of its final state). Their metatheory lives in `lean/Lara/Update/Discharge.lean` and `lean/Lara/Update/Completion.lean`.

The preservation theorems in `lean/Lara/Update.lean` are sufficient-condition results, not unconditional admissibility claims:

- `applyUpdate_addLeaf_ok` assumes an accepted source, three-carrier freshness, and admission of the new metadata key.
- `applyUpdate_tighten_ok` assumes an accepted source, an admitted old key, a tightened table at least as restrictive as the old table, a valid and rejection-free tightened table, agreement of the old and new checker contexts on retained leaves, and survival of old coverage witnesses between retained endpoints.
- `applyUpdate_addAttack_ok` assumes an accepted source, successful resolution of the new raw attack to one typed attack, typing of that attack, and retention of both endpoint terms under the existing prune.
- `applyUpdate_addInstance_ok` assumes an accepted source, name-and-term freshness, well-sortedness of the new term, a complete support derivation for it, and `Compile.AttackComplete` for the old retained arguments extended by that term.

Each conclusion produces a state for which the actual `applyUpdate` call returns `ok` and `Accepted` holds. None says that its constructor always succeeds.

### Core and public observations

`Lara.Update.coreObs` applies an arbitrary `Semantics.ExtensionSemantics` to the checked framework and the complete claim projection for an atom. `CoreTransition` pairs the source and target observations. The transition matrices below instantiate it with `Semantics.groundedSem`. They therefore classify grounded four-state transitions; they are not a matrix for every extension semantics.

Three theorems give the full semantics-parametric update-transition boundary. Each quantifies over an arbitrary `Semantics.ExtensionSemantics` and assumes explicit alignment, admission, and checking for the source and target, plus a successful update. Their classification hypotheses are constructor-specific. `Update.AdditiveUpdate.addLeaf` carries `AddLeafFresh source id` and `Admission.decisionFor source.table m.kind m.provenance = .admit` for the new metadata row; its `.addAttack` and `.addInstance` constructors carry no extra classification premise beyond the theorem's exact source and target runs and successful `applyUpdate`. `Update.NonInstanceUpdate.addLeaf` carries the same freshness and admit conditions, while its `.addAttack` constructor carries no extra classification premise; its `.tighten` constructor carries the exact `Admission.AtLeastAsRestrictive` and retained-Gamma premises, and the successful `applyUpdate` and target admission and checking hypotheses supply the admitted-key and tightened-table validity checks.

`Update.addAttack_gap_fixed` covers only `addAttack` and maps a source `gap` observation to target `gap`. `Update.additive_no_gap_entry` covers the three `Update.AdditiveUpdate` constructors and maps source non-`gap` to target non-`gap`; `tighten` is outside its scope. `Update.nonInstance_gap_fixed` covers the three `Update.NonInstanceUpdate` constructors and maps source `gap` to target `gap`; `addInstance` is deliberately outside its scope. `addInstance` is the only constructor that may move from a source `gap` to a non-`gap` target. For the first fragment these are the only non-grounded update-transition claims. The matrix claims instantiate `Semantics.groundedSem`.

`Lara.Update.PublicReport` has five constructors: `gap`, `justified`, `contested`, `defeated`, and `evidenceBlocked`, with publication labels `gap`, `justified`, `both`, `refuted`, and `evidence-blocked`. `publicReport` uses the exact production blocked-query computation first: if the query is blocked it returns `evidenceBlocked`, otherwise it embeds the grounded core status. `PublicTransition` recomputes the complete claim for the same atom on both accepted runs. It does not transport checked support indices or holes across an update.

`Lara.Update.CleanBase run` means exactly `run.admission.prune.removedSeed = []` for the source accepted run. Under this hypothesis, `publicReport_eq_core_of_clean` identifies the source public report with its grounded core report. For a successful `AdditiveUpdate` (`addLeaf`, `addAttack`, or `addInstance`), `additive_clean_target` derives a clean target and `additive_public_eq_core` identifies the target public and core reports, and `additive_public_ne_evidenceBlocked` then excludes the blocked target column. This boundary does not apply to `tighten`, which may prune arguments.

`Update.quarantine_nonpromotion_corollary` quantifies over exact source and target `AcceptedRun`s, a key, and `applyUpdate reg source (.tighten key) = .ok target`. It assumes `CleanBase sourceRun`, the `.tighten` case of `NonInstanceUpdate` (which carries the exact restrictiveness and retained-Gamma hypotheses), an atom `p`, and `publicReport targetRun p = .justified`. The proof first applies `tighten_public_justified_source_justified` to derive justification for the source checked complete claim. `tighten_public_row_justified_nonpromotion` then lifts that claim along the source's checked carrier into the source declared framework over the specification carrier (every declaration except the typed holes), exactly the conclusion shape of `Admission.source_justified_nonpromotion`. With holes the compact framework only embeds into the declared one, so the lift is not the identity. This is the matrix-to-legacy direction, and the proof does not call the older admission theorem.

`CleanBase` cannot be dropped from the universal additive theorem. `Examples.Update.addAttack_blocked_growth` gives a real accepted, non-clean source whose removed incoming edge already blocks one retained argument. A successful `addAttack` extends that blocked closure and changes the public report from `justified` to `evidenceBlocked`, while the target conditional core status is `defeated`. This witness refutes an unconditional additive/core equality theorem; it does not make `CleanBase` necessary for every individual run.

### Generated matrices

`lean/UpdateMatrices.lean` prints `Examples.Update.groundedCoreMatrixReport` and `Examples.Update.fiveValuedPublicMatrixReport`. `R` marks a reachable cell with a successful accepted source and target witness. `U` marks a cell excluded by the named theorem under the constructor-local hypotheses encoded by the matrix domain. The committed byte-for-byte output is `test/update-matrices.golden`:

<!-- BEGIN GENERATED UPDATE MATRICES -->
```text
addLeaf grounded core matrix
reachable=4/16
source \ target | justified                        | refuted                      | both                   | gap                  
justified       | R addLeaf_justified_to_justified | U* addLeaf_core_fixed        | U* addLeaf_core_fixed  | U* addLeaf_core_fixed
refuted         | U* addLeaf_core_fixed            | R addLeaf_refuted_to_refuted | U* addLeaf_core_fixed  | U* addLeaf_core_fixed
both            | U* addLeaf_core_fixed            | U* addLeaf_core_fixed        | R addLeaf_both_to_both | U* addLeaf_core_fixed
gap             | U* addLeaf_core_fixed            | U* addLeaf_core_fixed        | U* addLeaf_core_fixed  | R addLeaf_gap_to_gap 
U* requires AddLeafFresh and admission of the new metadata key.

tighten grounded core matrix
reachable=13/16
source \ target | justified                        | refuted                        | both                        | gap                       
justified       | R tighten_justified_to_justified | R tighten_justified_to_refuted | R tighten_justified_to_both | R tighten_justified_to_gap
refuted         | R tighten_refuted_to_justified   | R tighten_refuted_to_refuted   | R tighten_refuted_to_both   | R tighten_refuted_to_gap  
both            | R tighten_both_to_justified      | R tighten_both_to_refuted      | R tighten_both_to_both      | R tighten_both_to_gap     
gap             | U* nonInstance_gap_fixed         | U* nonInstance_gap_fixed       | U* nonInstance_gap_fixed    | R tighten_gap_to_gap      
U* requires NonInstanceUpdate restrictiveness and retained-Gamma premises.

addAttack grounded core matrix
reachable=10/16
source \ target | justified                          | refuted                          | both                          | gap                    
justified       | R addAttack_justified_to_justified | R addAttack_justified_to_refuted | R addAttack_justified_to_both | U additive_no_gap_entry
refuted         | R addAttack_refuted_to_justified   | R addAttack_refuted_to_refuted   | R addAttack_refuted_to_both   | U additive_no_gap_entry
both            | R addAttack_both_to_justified      | R addAttack_both_to_refuted      | R addAttack_both_to_both      | U additive_no_gap_entry
gap             | U addAttack_gap_fixed              | U addAttack_gap_fixed            | U addAttack_gap_fixed         | R addAttack_gap_to_gap 

addInstance grounded core matrix
reachable=10/16
source \ target | justified                            | refuted                             | both                                | gap                     
justified       | R addInstance_justified_to_justified | U* addInstance_sink_status_monotone | U* addInstance_sink_status_monotone | U additive_no_gap_entry 
refuted         | R addInstance_refuted_to_justified   | R addInstance_refuted_to_refuted    | R addInstance_refuted_to_both       | U additive_no_gap_entry 
both            | R addInstance_both_to_justified      | U* addInstance_sink_status_monotone | R addInstance_both_to_both          | U additive_no_gap_entry 
gap             | R addInstance_gap_to_justified       | R addInstance_gap_to_refuted        | R addInstance_gap_to_both           | R addInstance_gap_to_gap
U* requires InstanceSinkPremises freshness and complete support.

additive public rows under CleanBase (via additive_public_eq_core)
addLeaf reachable=4/20 (conditional exclusions); evidenceBlocked=0; addAttack reachable=10/20; evidenceBlocked=0; addInstance reachable=10/20; evidenceBlocked=0
addLeaf conditional exclusions require AddLeafFresh and admission of the new metadata key.

tighten five-valued public matrix under CleanBase
reachable=13/20; evidenceBlocked=3
source \ target | justified                                   | refuted                                | both                                    | gap                               | evidence-blocked                             
justified       | R tighten_public_justified_to_justified     | R tighten_public_justified_to_defeated | R tighten_public_justified_to_contested | R tighten_public_justified_to_gap | R tighten_public_justified_to_evidenceBlocked
refuted         | U tighten_public_justified_source_justified | R tighten_public_defeated_to_defeated  | U tighten_public_defeated_not_contested | R tighten_public_defeated_to_gap  | R tighten_public_defeated_to_evidenceBlocked 
both            | U tighten_public_justified_source_justified | R tighten_public_contested_to_defeated | R tighten_public_contested_to_contested | R tighten_public_contested_to_gap | R tighten_public_contested_to_evidenceBlocked
gap             | U tighten_public_gap_fixed                  | U tighten_public_gap_fixed             | U tighten_public_gap_fixed              | R tighten_public_gap_to_gap       | U tighten_public_gap_fixed                   

completion witnesses (atomic batches and in-place discharge)
addInstance b alone | rejected missing-conflict | sequential_completion_fails
addAttack b->a alone | rejected endpoint-not-declared | sequential_completion_fails
atomic [addInstance b, addAttack b->a] | accepted | sequential_completion_fails
atomic [addInstance b] | rejected missing-conflict; source kept | partial_batch_rejected
atomic [addAttack b->a, addInstance b] | rejected at edit 0: endpoint-not-declared | batch_edits_checked_in_order
atomic beside hole h | accepted; holes 1 -> 1, h kept | atomic_keeps_old_hole
dischargeOpen h eps q1 | accepted; holes 1 -> 0; p gap -> justified | discharge_hole_becomes_node
dischargeOpen h 0 q1 alone | rejected missing-conflict | discharge_needs_attack
atomic [dischargeOpen h 0 q1, addAttack h->a] | accepted; holes 1 -> 0; q gap -> justified | discharge_needs_attack
atomic [addInstance b] beside lone hole h | accepted; holes 1 -> 1; p gap -> justified | atomic_completion_public_justified
dischargeOpen h eps q2 by hole tUse | accepted; holes 0 -> 1; p justified -> gap | discharge_optional_enters_gap
dischargeOpen h 0 q1 after addAttack h->a | accepted; holes 1 -> 0; p justified -> refuted | discharge_outgoing_defeats
atomic [addLeaf l3 quarantined, addInstance c] beside hole h | accepted; args 1 -> 1; holes 1 -> 1, c pruned | atomic_quarantined_leaf_pruned
```
<!-- END GENERATED UPDATE MATRICES -->

<!-- BEGIN GENERATED UPDATE SUMMARY -->
The four core products contain 64 cells and 37 reachable cells: `addLeaf` 4,
`tighten` 13, `addAttack` 10, and `addInstance` 10. Cells marked `U*` are
unreachable only under the premise printed below their matrix. Under `CleanBase`,
the public additive products contain 20 cells each and retain the core reachable
counts, with zero reachable `evidenceBlocked` targets. The `addLeaf` count also
uses the admitted-new-key blocker premise. Under `CleanBase`, the public
`tighten` product has 13 reachable cells, including 3 `evidenceBlocked`
targets.

The mechanization refuted the predicted `addInstance` count of 13. The actual
count is 10. A fresh instance is a sink in the old framework: freshness prevents
old raw attacks from naming it, while old-to-old edges and labels are preserved.
`Grounded.SinkExtension`, `SinkExtension.label_old`,
`SinkExtension.justified_preserved`, and
`SinkExtension.contested_not_defeated` support
`addInstance_sink_status_monotone`. This excludes justified-to-refuted,
justified-to-both, and both-to-refuted, in addition to the additive no-gap
column. The matrix and `addInstance_reachable_count` record 10.
<!-- END GENERATED UPDATE SUMMARY -->

### Holes and the AGM probe

`Semantics.observe_holes_independent` proves, for every extension semantics, that changing only `Grounded.Claim.holes` leaves observation unchanged. It also states that the observation is `gap` exactly when complete support is empty. `Consistency.completeClaimFor` therefore sets `holes := []` without changing the status subject. This result does not erase diagnostics: `Grounded.incompleteAlternative` separately reports whether the full reporting claim has holes, and the Haskell reporting path computes located incomplete alternatives in `src/Lara/Reporting.hs`. Holes are neither a fifth grounded status nor a sixth public report.

Since `lara-core@0.3` an accepted source can contain holes: declared arguments that type-check with a nonempty mandatory obligation set. The checked framework holds only the complete arguments, so `completeClaimFor` and every matrix above still read complete support only. `Accepted` no longer implies that every raw argument is complete: what an accepted run yields as checked arguments and attacks is the complete arguments and the attacks whose source is complete. `applyUpdate_addInstance_ok` keeps its complete-support premise; it is the completion case. `applyUpdate_addInstance_hole_ok` is the hole case; it needs no conflict premise, since attack completeness constrains complete arguments only.

Adding a hole is inert only conditionally. A fresh `addInstance` whose term is a hole, with the attacks unchanged, leaves the complete arguments, their typing context, and the closure coverage between them fixed, so every core status is unchanged and the only new output is the hole's diagnostic (`addInstance_hole_core_fixed`, witnessed by `Examples.Update.addInstance_hole_inert`). The unconditional claim is false: an attack from a complete source onto an occurrence inside a hole produces closure edges onto complete arguments containing that occurrence, so `addAttack` onto a hole can change a core status, and removing a hole can remove such an attack at the raw endpoint boundary. Graph and status invariance is therefore stated under unchanged complete-to-complete coverage, or for the fresh hole-only `addInstance` above. No update other than `addInstance` changes which declared terms are holes: a typed term keeps its obligations wherever the leaf context agrees on its leaves (`typed_obligations_preserved`), so `addLeaf` and `addAttack` leave the reported holes unchanged and `tighten` preserves the obligations of every surviving term (`addLeaf_obligations_preserved`, `addAttack_obligations_preserved`, `tighten_obligations_preserved`). Tightening can still quarantine a hole, so its reported hole list only shrinks.

Completion has three routes (D11 and the two completion decisions recorded under holes below).

*Additive.* An author adds each fresh admitted leaf with `addLeaf`, then a distinct complete term under a fresh raw name with `addInstance`. The old hole and every raw attack stay declared, and the old hole stays reported (`addInstance_holes_persist`). This sequence is not accepted step by step in general: the complete term goes through ordinary attack-completeness checking, so if it licenses an outgoing conflict that no declared attack covers, `addInstance` rejects, and the `addAttack` that would cover it rejects first because its source is not declared yet (`Examples.UpdateCompletion.sequential_completion_fails`).

*Atomic.* `atomic` performs the whole completion as one batch and checks the completed program once. It is accepted exactly when its raw edits apply and the final state is accepted (`applyUpdate_atomic_ok_iff`); a rejected batch leaves the source unchanged (`atomic_partial_rejected`, with `applyOrKeep`). Completion is complete: whenever the program obtained by adding fresh leaves, fresh instances, or an in-place discharge, and the needed attacks is accepted, the batch yields exactly that program (`atomic_completion_complete`, `atomic_discharge_completion_complete`). Every batch keeps raw attacks and argument names at their indices, and a batch without discharge keeps every argument row (`applyBatchFrom_prefix`). Whether or not its new leaves are admitted, it keeps the old complete arguments and the old reported holes as prefixes of the new ones (`atomic_additive_checked_prefix`, exact form `atomic_additive_checked_split`, witnessed by `Examples.UpdateCompletion.atomic_keeps_old_hole`). A quarantined new leaf prunes only new rows: the removed seed grows by exactly the quarantined new leaves, so every old kept row stays kept under the same checker context (`atomic_additive_kept`), and a pruned row is neither a framework argument nor a reported hole (`AcceptedRun.pruned_not_reported`, witnessed by `atomic_quarantined_leaf_pruned`). An admitted batch keeps a clean source run clean (`atomic_additive_clean_target`).

The per-constructor transition results compose over an additive batch as far as follows (`lean/Lara/Update/Transitions.lean`). No claim enters `gap`, under every extension semantics (`atomic_additive_no_gap_entry`). A batch with no `addInstance` keeps every `gap` claim in `gap` (`atomic_instanceFree_gap_fixed`). A batch with no `addAttack` adds only fresh sinks, so a grounded `justified` claim stays `justified` and a `contested` one is not `defeated` (`atomic_attackFree_sink_status_monotone`). Nothing else composes: one `addAttack` already reaches every transition among the three non-`gap` statuses. After an admitted batch from a clean source run, a complete target row that no compiled attack reaches justifies every claim equivalent to its conclusion, in the core and in the public report (`atomic_completion_justified`, run-level form `AcceptedRun.justified_of_unattacked_row`, witnessed by `atomic_completion_public_justified`).

*In place.* `dischargeOpen` answers an open question of a declared argument under its own name. The term-level results in `lean/Lara/Update/Discharge.lean` show that every old position stays defined at the same occurrence kind (`subterm_dischargeAt_old`), that the conclusion is unchanged (`dischargeAt_conclusion`) and typing preserved when the discharge answers the question (`dischargeAt_hasSupport`), and that the new obligations are exactly the old ones away from the site, the ones still open at the site, and the discharge's own (`dischargeAt_obligations_iff`). Through the pipeline, raw endpoint alignment is preserved index by index (`dischargeOpen_resolved`), every other hole and complete argument persists (`dischargeOpen_others_persist`), and a retained hole discharged to completion becomes a framework node whose claim leaves `gap` under every extension semantics (`dischargeOpen_hole_becomes_node`, witnessed by `Examples.UpdateCompletion.discharge_hole_becomes_node`). Because the discharged argument keeps its declared name, its covering attack can also be added first, one update at a time (`discharge_needs_attack`).

`dischargeOpen` has no unrestricted transition theorem. Discharging an optional question of a complete argument with a hole turns a framework node into a hole, and its claim moves from `justified` to `gap` (`Examples.UpdateCompletion.discharge_optional_enters_gap`). Completing a hole that a declared raw attack already names as its source makes that attack fire, and the attacked claim moves from `justified` to `refuted` (`discharge_outgoing_defeats`). The transition results are therefore stated for a discharge that completes a retained hole, which inserts one framework node into the old framework. No claim enters `gap` (`dischargeOpen_completion_no_gap_entry`), and only a claim equivalent to the completed conclusion leaves it (`dischargeOpen_completion_gap_fixed`), under every extension semantics. When, in addition, no raw attack names the discharged argument, which is what freshness gives `addInstance`, the compiled attacks are unchanged and the new node is a sink, so `addInstance_sink_status_monotone` carries over (`dischargeOpen_completion_sink_status_monotone`). A completed argument that no compiled attack of the target reaches justifies every claim equivalent to its conclusion, in the core and in the public report unless the claim is blocked (`dischargeOpen_completion_justified`), which a clean source run rules out (`dischargeOpen_completion_public_justified`). The grounded results rest on `Grounded.SinkEmbedding`, which inserts sinks anywhere in the declaration order. No transition matrix is computed for `dischargeOpen` or `atomic`.

`Lara.Update.beliefSet sem unit p` means `coreObs sem unit p = observed justified`. The AGM comparison fixes `sem = Semantics.groundedSem` and tests exactly two probes. `Examples.Update.agm_success_fails` gives an accepted `addInstance` whose new, sole support for the target claim is defeated on arrival, so the inserted claim is absent from the target belief set. `Examples.Update.agm_inclusion_fails` gives an accepted `addAttack` that removes a previously justified claim, so the source belief set is not a subset of the target belief set. Both probes fail. The comparison stops there; no remaining AGM postulate was tested and the projection was not adjusted to recover one.

### Paper claim boundary

The paper may claim a checked, one-step source-update calculus with four first-fragment constructors and named, executable constructor side conditions; sufficient-condition acceptance preservation under the exact hypotheses of `applyUpdate_addLeaf_ok`, `applyUpdate_tighten_ok`, `applyUpdate_addAttack_ok`, and `applyUpdate_addInstance_ok`; complete grounded core 4 by 4 matrices for the four constructors, with mechanized reachable and unreachable evidence and counts 4, 13, 10, and 10; clean-base public additive summaries and the complete clean-base public `tighten` 4 by 5 matrix, using publication labels `refuted`, `both`, and `evidence-blocked`; the full semantics-parametric gap boundary, where `addAttack` preserves `gap`, additive updates cannot enter `gap`, and every non-instance update preserves a source `gap`, and for the first fragment these are the only non-grounded update-transition claims; from a justified target public report, under `CleanBase` on the exact source run, an exact successful `tighten`, and its `NonInstanceUpdate` hypotheses, the matrix-to-legacy `Update.quarantine_nonpromotion_corollary` for the source declared framework; the count refutation for `addInstance`, the counterexample to dropping `CleanBase` from the universal additive theorem, holes independence, and the two failed grounded AGM probes; and two completion constructors with exact acceptance characterizations, where in-place discharge preserves position, conclusion, typing, and obligations and atomic batches are all-or-nothing and complete for completion, with the concrete sequential-failure counterexample. Restricted transitions are claimable for both: a discharge that completes a retained hole never enters `gap` and exits it only for the completed conclusion, keeps the `addInstance` sink guarantees when no raw attack names the argument, and justifies an unattacked completion; an additive batch never enters `gap`, keeps `gap` without `addInstance`, and keeps the sink guarantees without `addAttack`, with the two discharge counterexamples bounding these restrictions.

The paper must not claim an unindexed four-valued general-semantics matrix; that public additive behavior equals core behavior without `CleanBase`; unconditional `addInstance` admissibility; a transition matrix for `dischargeOpen` or `atomic`, or a transition result for either without the stated restrictions; a theory of update composition beyond one atomic batch, removal, or un-tightening; a CLI or runtime update feature; full AGM compliance; or that the holes diagnostic is a sixth report.

## Contexts, contextual adequacy and backend replacement

A *fragment* is a piece of a checked program, a *context* is a surrounding program with a hole the fragment fills, and *observation* is what the completed program's verdict reveals. The central result is contextual representation independence: relabeling a fragment's backend certificates, without changing what the backend accepts, is invisible to every admissible context. It extends the whole-program backend-replacement result along the context quantifier, and the two statements are incomparable: the whole-program result ranges over arbitrary checked whole programs and carries no admissibility hypothesis, while the congruence ranges over admissible fragment contexts.

### Fragments, contexts and linking

`Lara.Context.Fragment` carries `sigma`, `policy`, `gammaFrag`, `ground`, `args`, `atts`, `imports`, `exports`. Every field is forced by something in the frozen core:

| Field | Forced by |
|---|---|
| `sigma`, `policy` | Both are `Lara.Unit` fields, and the signature and policy mismatch rejection class must retain the two disagreeing values, so they are compared structurally at the guard. |
| `gammaFrag` | `Lara.Unit` has no Γ field; Γ indexes `Unit.CheckedUnit`, and it is what the two sides contribute, so `link` returns `Lara.Unit × (LeafId → Option Atom)` and builds Γ with `Admission.buildGamma`. |
| `ground` | `Check.Unit.checkUnit` takes a `ground : List Atom` and sorts it (`Lara.groundWellSorted`); a fragment that contributed arguments but no ground atoms could not be checked. |
| `args`, `atts` | The declared material `Compile.CheckedProgram` is built from. |
| `imports` | Leaf-name openness. |
| `exports` | Observable conclusions, not pinned claims. |

`Lara.Context.Context` wraps one `Fragment` as the material surrounding the hole. Contexts are fragment-shaped on purpose: it is what makes `compose` definable, and congruence is unstateable without composition.

Fixed across linking are `canon`, Σ, the policy (including `defeat`), and the backend registry. Σ and the policy are fragment fields and their agreement is enforced by the guard. `canon` and the registry are parameters of `link`, `crossAtts`, `fragmentAF`, and `obs`, because a context is data rather than a checker invocation, so it cannot supply a different registry and "registry mismatch" is unrepresentable rather than rejected. Γ is not fixed: it is exactly what the two sides contribute, and the Γ-extension transport in `Lara/Update.lean` carries derivations into the linked Γ.

Rejection is decidable and total. `linkOk` is the `isNone` projection of named fault functions returning `Option LinkFault`; each one-sided fault retains its side and leaf, and each signature or policy fault retains both disagreeing values. `native_decide` is banned by the axiom discipline.

| Class | Component | Behavior |
|---|---|---|
| R-L1 duplicate or shared identifier | `idHygieneFault` via `firstDup?` / `firstShared?` | reject with side and identifier |
| R-L2 unsatisfied import | `firstMissing?` | reject with importing side and identifier |
| R-L3 signature or policy mismatch | `sigmaPolicyFault` | reject with both values |
| duplicate support term across the boundary | `dedupList` | merge |

The last row is not a rejection, and the reason is that rejecting it would refute the theorem being proved. `SupportTerm` equality is structural, so a context argument built only from imported leaf identifiers can be structurally identical to a fragment argument, and hygiene on identifiers does not prevent term collision. If term collision rejected the link, then for a fragment `F₁` containing a term `t ∉ F₂.args`, the context that declares `t` would link with `F₂` and be rejected against `F₁`, so `F₁` and `F₂` would be distinguishable by a context that reads nothing about them; contextual equivalence would collapse to term-set equality and no congruence coarser than syntax could hold. Merging is semantically inert, because identical terms have identical edge sets, and `link_merge_status_eq` proves it status-preserving rather than asserting it.

Saturation is forced, not chosen. `Compile.AttackComplete` is an all-pairs condition over the declared arguments and is a premise of `Check.Unit.checkUnit_complete`. A `link` that merely concatenated `C.atts ++ F.atts` would leave every cross-boundary contrary conflict uncovered, `hattackComplete` would be unsatisfiable on exactly the interesting links, and the calculus would only ever accept programs whose two halves cannot interact. So `link` emits `crossAtts`, which enumerates the cross pairs whose cached conclusions satisfy `Attack.contraryMatchB` onto a `Compile.conflictAttackableB` target, in both directions, and emits one attack per pair in the shape the target admits: a `.leaf` target is undermined at the root position (`HasAttack.undermine` reads `Gamma l`, which the linked Γ supplies), and an `.inst` target is rebutted (`HasAttack.rebut` reads the root rule's instantiated conclusion, which `Support.InstSide.concl` supplies, and requires `r.mode = .defeasible`, which is exactly what `conflictAttackableB` returns true on for an instance). Both shapes place the attacked occurrence at the target itself, so `Compile.Covered` holds through `Compile.contains_refl`. A consequence worth stating plainly, because the full-abstraction constructions depend on it: a context cannot withhold a cross-boundary attack. If a context argument's conclusion contrary-matches an attackable fragment occurrence, the link emits the edge whether or not the context wants it.

`link` runs before checking, so it cannot read conclusions off `Unit.CheckedUnit.nodes`, which exists only once the linked program has been accepted. `Lara.Context.conclusionCache` therefore infers conclusions with the checker's own `Check.inferSupport`, whose `inferSupport_sound` and `inferSupport_complete` pair makes the cache exactly the graph of `HasSupport … w C []` on the terms that have one. `Lara.Context.conclusionCache` and `Lara.Check.conflictCache` compute the same idea at two different times, before checking under the hypothetical linked Γ and after acceptance off `CheckedUnit.nodes`. Their agreement is proved: on any accepted unit the inferred cache over the program's arguments is the `(term, conclusion)` projection of the conflict cache (`Context.conclusionCache_eq_conflictCache`, via `Check.conflictCache_conclusions`), and on an accepted link each side's saturation cache is the restriction of the checker's cache to that side's arguments (`Context.link_cache_bridge`). The saturation `link` performs is the one the checker would have computed.

### Contextual representation independence

`obs` returns a closed `Observation`: `.incompatible fault` for a guard failure, `.rejected error` for a compatible linked unit rejected by the checker, and `.observed statuses` for an accepted link. `CtxEquiv` compares this detailed outcome in every context, so incompatibility cannot be masked by checker rejection.

```lean
theorem backend_replacement_congruence
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F) (hfix : FixesContext f C) :
    obs reg₁ C F = obs reg₂ C (mapAssurFrag f F)
```

`Lara.Context.backend_replacement_congruence`, `lean/Lara/Context/Equivalence.lean`. The relabel-free generalization `registry_swap_congruence` drops the relabel and the injectivity entirely: if every assurance the first registry accepts the second accepts too, the same fragment reads the same way in every admissible context. One precision the plan's phrasing did not carry: the hypothesis is global, not restricted to the fragment's certificate occurrences, since `hasSupport_mapAssur`, which transports the derivations, quantifies over every rule and assurance. `Examples.Linking.cert_registry_swap_witness` exhibits a genuinely different pair of registries at a fragment that actually carries a certificate, so the acceptance hypothesis is discharged on something rather than vacuously. `certSwap` wraps every `nd` certificate payload and `registryWrapped` reads the same registry through a backend core that unwraps before replaying, so the relabel is injective and acceptance-preserving by construction; `cert_relabel_moves` proves it is not the identity on the fragment, and `cert_congruence_witness` is the congruence applied to it.

The assurance-free fixtures (`congruence_witness`, `registry_swap_witness`) are retained as shape witnesses only: a fragment of bare leaves has no certificate, so `mapAssurFrag f` is the identity on it for every `f`, and they exercise the plumbing, not the theorem.

Contexts are closed under `compose` where its guard holds (`Lara.Context.Compose`), so the congruence's quantifier already ranges over every composite, and `admissible_composed` assembles a composite's side of the hypothesis from its two halves. One boundary is stated rather than hidden: `compose` does not saturate. `link` covers the conflicts between the whole context and the fragment, and nothing ever emits the conflicts between the two halves, so `sideOk_composed` takes the two cross-boundary quadrants as explicit hypotheses, and a composite of two contexts that attack each other across their own boundary is not admissible, which places it outside the theorem's quantifier rather than making it a counterexample. Composition is closed for hygiene (`linkOk_composed`, `composed_ownIds`) but not for linkability, and that boundary is a theorem: `Examples.Linking` builds two contexts each admissible for one fragment (`hostile_left_admissible`, `hostile_right_admissible`), composes them (`hostile_compose_ok`), shows the composite passes the guard (`hostile_composite_links`), and proves it is not admissible (`hostile_composite_not_admissible`).

The admissibility hypothesis is content, not scaffolding. `Admissible reg C F` says the guard passes, both sides' declared material is well-formed relative to the linked environment (`SideOkHoles`), the linked program passes stage 2, and the shared policy is well-formed. Nothing in it mentions the conclusion, and `Examples.Linking.admissible_split` discharges it on a concrete pair, so it is inhabited rather than decorative. It cannot simply be dropped: `obs` distinguishes a checker rejection from an observed status list, and a forward-only acceptance hypothesis lets `reg₂` accept certificates `reg₁` rejects, so an unconditional "for every context" statement would be false unless acceptance is two-way, a strictly stronger notion of backend replacement than the whole-program result's model. The theorem is as strong as the acceptance relation it is given, and no stronger.

Since issue #13 a side may carry located holes: `SideOkHoles` asks each declared argument only to type, and a hole-free side enters through `SideOk.toHoles`. So the congruence, the registry-swap generalization, and the relational parametricity theorems all cover fragments and contexts with holes. A relabel or a related backend keeps each declaration's obligation set, so holes stay holes. `Examples.LinkHoles.admissible_hole` discharges the hypothesis for a fragment with a hole. `obsGen_hole_blind` says what holes can change: two fragments with the same interface, the same complete arguments, and the same live attacks are observed alike in every context admissible for both. The live-attack premise cannot be dropped, because `Examples.LinkHoles.hole_erasure_observable` deletes a hole together with an attack aimed inside it, and the link is then rejected.

### The surface corollary

Contexts live at the core `Lara.Unit` level and the surface layer is a corollary target rather than the primary quantifier. `lean/Lara/Context/Surface.lean` delivers it: `surface_directAF_relabel`, for two accepted surface programs whose elaborated units are related by an injective relabel present the same framework, via `Lara.Surface.direct_compiled_agree`, and `surface_directAF_link` for the instance where the two units are the two sides of a link. Everything the surface layer reports off that framework agrees, for every carrier-local extension semantics (`Lara.Surface.observe_coherent`).

The worked pair is `Lara.Examples.SurfaceTransport.surfaceTransport_directAF_eq`: two accepted surface programs, differing only in one `nd@1` certificate related by `Examples.Linking.certSwap`, present the same framework, and the statement is unconditional because the two accepted units are produced by `CoreObligations.checkUnit_complete` rather than assumed. Two guards keep it from being a tautology, since `f = id` would otherwise satisfy every hypothesis: `surfaceTransport_relabel_moves` (`output₂.unit.args ≠ output₁.unit.args`) and `surfaceTransport_inputs_differ`. The attack-bearing pair is `Lara.Examples.SurfaceTransportAttack.surfaceTransportAttack_directAF_eq`, which declares three arguments and one rebut, so `coveredB_relabel` runs on a one-element list and the four attack-side `CoreObligations` fields are real obligations rather than vacuous ones. Three further guards keep it honest: `surfaceTransportAttack_atts_nonempty`, `surfaceTransportAttack_relabel_moves_atts`, and `surfaceTransportAttack_directAF_edge`. The attack could not be sourced at the certified argument, and the reason is a policy law rather than a proof-engineering limit: `Policy.WellFormed` forbids any declared contrary either of whose sides overlaps a strict-reachable conclusion pattern, and the certified rule is strict with conclusion `q`, so a certified argument can be neither endpoint of a rebut in a well-formed policy. The fixture therefore makes the certificate a premise of both endpoints: two plain defeasible rules `q ⊢ s` and `q ⊢ t` over the certified argument, with `contrary s t`. `mapAssurAtt certSwap` consequently moves the declared attack and not just the argument list.

Getting there required not using the obvious route. Every accepted surface fixture in `lean/Lara/Examples/Surface.lean` is proved by `native_decide`, which the axiom discipline bans: a witness built on one would import `Lean.ofReduceBool` into the audit and fail `scripts/check-axioms.sh`. The obstruction is narrow rather than "the surface checker's evaluation does not fit kernel `decide`": the surface predicates decide fine on the full fixture, and `reconstructExplicitTerm` and its mutual partners compile to `brecOn` structural recursion, not well-founded recursion. Exactly one function on the path is kernel-opaque: `Lara.NDNamed.lowerFormula` and its caller `lowerNamedExpr` are `termination_by sizeOf`, so Lean compiles them to `WellFounded.Nat.fix` and marks them irreducible, and an accepted fixture carrying a certificate cannot be obtained by evaluation. That dictates the fixture's shape: the certificate is authored in kernel form (`NDNamed.encodeCert`, so `lowerNamed` returns the payload unchanged, with `NDNamed.lowerNamed_id_of_kernel` stating exactly this), `Checks.program` is hand-built through relational inductives whose constructors never mention `reconstructArgument`, `CoreObligations` is hand-built with a `HasSupport` derivation following `Examples.Linking.certArg_checked` field for field, and registry acceptance is inherited rather than replayed because the lowered payload is definitionally `Examples.slot1Cert`.

The link corollary `surface_directAF_link` is witnessed by `Lara.Examples.SurfaceTransport.surfaceTransport_link_directAF_eq` on the same fixture. It derives the argument and attack correspondence from `link_relabel_commutes` rather than taking them as hypotheses, and the split it exhibits is forced rather than chosen: the elaborated unit declares exactly one core argument, `linkedUnit`'s argument field is `dedupList (C.frame.args ++ F.args)`, so the fragment owns that argument and the context owns none, while the context owns the evidence leaf `l-p` that the fragment imports, so the link is real at the interface. Two degeneracies are each closed by their own fixture: the attack-bearing fixture closes the edge-free gap for `surface_directAF_relabel`, and `Lara.Examples.SurfaceTransportContext.surfaceTransportContext_link_directAF_eq` closes the empty-context gap with a non-empty `C.frame.args`, where the same `certSwap` is the identity on the context's own argument and is not the identity on the fragment's (`surfaceTransportContext_fixes_is_substantive`, `surfaceTransportContext_ctx_args_nonempty`). The replacement for `linkedUnit_of_empty_ctx` reads the saturation's emission guard instead of its caches (`crossAtts_of_no_contraries`), because with a context argument present the caches would call `Check.inferSupport` through `certOkOf` on the non-reducing `nd` core.

### Leaf-name openness and the term-hole remainder

The fragment calculus supplies leaf-name openness by extending Γ. That cannot discharge a critical question, because the answer is a support term inside an instance's discharge map: an unresolved mandatory question cannot cross `Compile.CheckedProgram.complete` (`Compile.lean:590`), and its discharge lives inside the term rather than in a name environment. Merely extending Γ therefore cannot provide it, and `Grounded.Claim.holes` is likewise never read by the observation.

The additive `Lara.Context.Holes` calculus supplies the term-level remainder: named holes occur in critical-question answer positions, recursively within premise and answer templates; a context supplies independently typed core terms; typed substitution produces a complete argument before the unchanged checker and compiler boundary; arguments and attack endpoints are instantiated together. The extension proves source-erasure typing, typed substitution, conservative embedding of the old calculus, guarded composition, and functional and relational observation transport. `Examples.TermHoles` has repeated local question names at nested nodes with distinct hole identifiers, nonempty source obligations, typed closure and checked acceptance, missing, duplicate, and wrong-answer rejection, and a real attack whose endpoint includes a substituted discharge. The exact scope and theorem map are recorded in the holes section below.

This closes the term-hole remainder, not the separately gated full-abstraction work. `Grounded.Claim.holes` and the frozen observation are unchanged, and unresolved named holes are rejected before the old observation runs.

### Paper claim boundary

The paper may claim that backend replacement is a congruence: an injective, acceptance-preserving relabel of a fragment's certificates is unobservable in every admissible well-formed context whose own assurances satisfy `FixesContext` (`backend_replacement_congruence`). It may claim the relabel-free form, that two registries where the second accepts everything the first accepts are contextually indistinguishable on the same fragment (`registry_swap_congruence`, with a global rather than occurrence-restricted hypothesis, witnessed on two genuinely different registries at a fragment that actually carries a certificate). It may claim that a composite's linkability is assembled from its halves (`sideOk_composed`, `admissible_composed`) under explicit cross-coverage hypotheses, because `compose` does not saturate. It may claim that the calculus is mechanized rather than sketched: fragments, interfaces, contexts, a witnessed link guard with three rejection classes, saturating linking, structural merge, context composition and its closure, and acceptance of a well-linked composition (`link_checked`). It may claim that linking's design choices are theorems rather than conventions: saturation makes `AttackComplete` hold on a link (`link_attackComplete`) and the merge is semantically inert (`link_merge_status_eq`), with `crossAtts_nonempty` witnessing a link where saturation adds a real cross-boundary attack. It may claim that the grounded observation is invariant under any node-merging morphism of argumentation frameworks (`Lara.Invariants.CarrierMerge.status_eq`), a statement about frameworks independent of this calculus. It may claim that the result transports to the surface (`surface_directAF_relabel`), that the contextual-adequacy obligation is discharged for leaf-name openness, and that the congruence and its companions hold under every extension semantics in the observation interface with the same hypotheses and no additional one (`backend_replacement_congruence_sem`, `registry_swap_congruence_sem`, `backend_replacement_congruence_composed_sem`, `whole_program_replacement_sem`). The generalization is non-trivial: `Examples.ContextSemantics.obsSem_cycle_stable_ne_grounded` reaches an observation arm the grounded reading cannot reach, and `obsSem_sink_preferred_ne_grounded` has two semantics answer and disagree.

The paper must not call the congruence parametricity, because it quantifies over a function `f : Assurance → Assurance`, not a relation; the relational form is a separate theorem with its own name and its own simpler hypotheses, and the relational form is itself bounded to partial-bijective certificate relations. It must not claim full abstraction, since no logical relation is defined in the contextual-adequacy development. It must not state the result as unconditional in the context quantifier, because it is about admissible contexts, and a paper display must carry that hypothesis. It must not claim it holds under contexts changed by the relabel, since `FixesContext f C` requires the relabel to fix every assurance in the context's own arguments and attacks. It must not present it as a new proof of the whole-program backend-replacement result, which is cited and not re-derived. It must not claim any unrestricted implication between the equivalence relations: a separation result refutes grounded `CtxEquiv` implying `CtxEquivSem sem` for every semantics allowed by the interface (`Examples.ContextualSeparation.counterexample`), which combines an all-context grounded proof with a selector-semantics distinction; this does not separate the standard non-grounded instances, and the grounded instance still coincides by `ctxEquivSem_grounded_iff`. It must not claim that contexts are closed under composition for linkability, and it must not claim that a context may redefine the policy or the registry. It is not a Haskell-side result: the calculus adds no checker, CLI, wire, or corpus surface.

### Full abstraction: descoped

Full abstraction, a logical relation with soundness and completeness, was not entered and is descoped by maintainer decision rather than deferred. Two obstructions are recorded, unchanged by the contextual-adequacy work.

1. The semantic interface is wider than the declared imports. `AttackComplete` is all-pairs and `Compile.Covered` closes under subarguments, so a context can attack any fragment argument whose conclusion contrary-matches, and grounded labelling is a fixpoint over the linked framework, so a non-exported boundary argument feeds back into an export. A relation over declared imports is refuted; a relation over the full contrary-visible occurrence profile risks collapsing into a generalized `Erase.mapAssur`.
2. Completeness is policy-conditional. Under `emptyDefeat` no attack types, so `logrel_complete` is false without a hypothesis; and since `ConflictAttackable` is unconditionally true on leaves while rebut requires `.defeasible`, a symmetric contrary table forces only `{in, undec}`.

The contextual-adequacy result is deliberately immune to both, because a uniform relabel preserves the whole occurrence profile, so "what is the interface" never has to be answered.

The descope rationale is that no consumer needs the result: what the system's story needs, backend interchangeability under every admissible context, is the congruence; full abstraction would add a context-free proof method for arbitrary fragment equivalences, and no obligation in the development or the paper uses one. The tautology risk is structural rather than incidental, since full abstraction is informative only when the logical relation is coarser than syntax, while Lara's contexts are close to maximally discriminating, which pushes contextual equivalence toward syntactic identity up to contrary-invisible decoration. It was also the theory spine's named drop, the highest-effort item with an explicit drop policy. The paper claims the congruence under its honest name, contextual representation independence, and states full abstraction as not attempted, with the empty-defeat and symmetric-contrary boundary facts as content.

For a future reopening, the retained design: phase G0 is an unlanded soundness spike answering the interface question, whether a sound relation is more than a generalized `Erase.mapAssur`; G1 freezes `LogRel` over the contrary-visible occurrence profile with emitted and observed sides separated, a dated freeze record, and an amendment procedure; G2 proves soundness by grounded-fixpoint induction over the linked framework; G3 proves completeness by contrapositive via `checkUnit_complete` plus a ground-coverage obligation, not via `Realizability.Realizable`, whose `compiled_iso` targets a given whole-unit `StructuredAF`, precisely the unknown; G4 closes out. The stop rule is that if completeness stalls beyond the expressiveness hypothesis, keep G2 as adequacy of the logical relation and do not rename it full abstraction. The completeness hypothesis belongs on the policy, not on the context quantifier: the policy must supply, for the atoms a forcing gadget uses, either an asymmetric contrary pair or a strict-rooted attacker, relative to atoms unused by both fragments. Intended positive witness is `m2bPolicy`'s asymmetry; intended negative witness is `emptyDefeat`, seeded by `oneSelfEdge_not_realizable`.

The interface gate was later run again. Its written exit is re-descoped: an occurrence-profile candidate loses cross-boundary term identity, and a same-context copying check distinguishes two accepted certificate variants. The candidate `R_occ` compared declared arguments and subterm occurrences, emitted attacks, received attacks, internal influence, and observed conclusions by a bijection; it failed a same-context test where one fragment contains `wrapped a` and the other `wrapped b`, both accepted by the same backend, with identical declaration envelopes and matching isolated profiles, and a common context that declares `wrapped a` plus an undercut of its own copy: the first merges with the attacked copy and export `p` is defeated, while the second remains distinct and `p` is justified. Retaining exact identities avoids that failure, but the spike does not establish a useful independent logical relation or a characterization of contextual equivalence, so the soundness and completeness phases remain unentered and no theorem is added. Universal contextual equivalence equal to decorated identity is not established by the copying case, which shows only that admissible decorations depend on the context; the empty-defeat case shows why occurrence distinctions need not produce status distinctions. A future reopening must state the consuming equivalence problem, its policy and context domain, and a candidate that survives the copying case, and any equivalence that keeps exact fault observations must cover or explicitly exclude them under a separately named relation.

Relational parametricity and the generic observation amortize transport and finite realization, but neither needs a complete, context-free decision method for arbitrary fragment equivalence, so neither removes the absence of a consumer. This is a completed negative gate result, not a postponed implementation plan.

## Generic semantics and relational parametricity

The observation interface made the argumentation semantics an object, but the contextual theorems were still stated only at the grounded instance, while quantifying over the parameter only at the framework level. That asymmetry was an artefact of the order the layers landed in, not a fact about the theory, and this section closes it. The contextual representation-independence result and its companions now hold under every extension semantics in the interface, with the same hypotheses and no additional one.

### Generalizing the projection

What is parameterized is the projection, not a duplicated copy of the observation. The obvious implementation duplicates `Observation` and `obs` into a semantics-aware copy and re-runs the congruence proofs on the copy; that first draft was rejected, and what is parameterized instead is:

```lean
def obsGen {α : Type} (g : Invariants.StructuredAF → Atom → α) {canon : String → String}
    (reg : BackendRegistry canon) (C : Context) (F : Fragment) : ObservationOf α
```

`obs` is `obsGen` at `g := Invariants.status canon`, and `obsSem sem` is defined as `obsGen (Invariants.observeSem sem canon)`. The congruence is proved once, in `obsGen_congr`, and each of the four semantics-parametric congruences is a one-line instantiation. This is not only economy: proving the congruence for an arbitrary `g` states, as a theorem rather than a remark, that the congruence was never a fact about the grounded labelling, whereas a development that copied the proof four times would have the same theorems and would leave that fact as a comment.

The projection layer sits beside the theorems it generalizes rather than beside the semantics that instantiate it, and the payload-generic `ObservationOf α` replaced the three-armed `Observation` inductive rather than being introduced next to it. Two things follow. First, `obs` is `obsGen` at the grounded projection, as a theorem, by `rfl`: with two distinct result types, the design premise could only be asserted in prose, whereas with one type it is `Context.obs_eq_obsGen` and it closes by `rfl`. Second, the grounded theorems are corollaries rather than copies: `obs_eq_of_ok` is `obsGen_eq_of_ok _ hlink h` and `backend_replacement_congruence` is `obsGen_congr _ hf hpres hadm hfix`, each a single line, so a change to the argument cannot silently hold in only one place. The cost is that `Fragment.lean` and `Equivalence.lean` are edited, though no existing statement moves: every grounded theorem keeps its name, its type, and its implicit-argument order, and `Examples/Linking.lean`'s `congruence_witness` and `registry_swap_witness` compile unchanged, which is the load-bearing check that it did.

`liftObservation` still exists, because the two payloads still differ: `obsSem groundedSem reg C F` lives in `ObservationOf ClaimObservation` while `obs reg C F` lives in `ObservationOf Grounded.Status`, so the statement "the grounded instance is the old observation" is still not an equation between them as they stand. `liftObservation` is the injection that makes them comparable and `liftObservation_inj` is what the forward direction of the equivalence needs. It is bookkeeping forced by `Grounded.Status` against `ClaimObservation`, not by the container, and it carries no mathematical content beyond the injectivity of `List.map` over a constructor.

The generalization lattice runs from `Semantics.observe sem` at the framework level, through `Invariants.observeSem sem canon` (read off an erased carrier) and `Lara.Context.obsSem sem` (read off the linked carrier of a context plus fragment), to `Lara.Context.CtxEquivSem sem` (quantified over all contexts). Each arrow is witnessed by a theorem, `observeSem_grounded`, `obsSem_grounded`, `ctxEquivSem_grounded_iff`, and each arrow goes one way only.

### Why the congruence needed no new hypotheses

This is the finding most worth recording, because the cost estimate expected otherwise. Every congruence funnels through one carrier-equality lemma, `compileUnit_link_relabel`, whose conclusion is an equation between carriers, not a pointwise agreement between them. Once the two sides meet at a single `G : StructuredAF`, the projection hanging off it is applied to the same argument on both branches, so it cannot distinguish them, whatever the projection is. So `obsGen_congr` is `backend_replacement_congruence`'s proof with `Invariants.status canon` replaced by `g`, and with no new hypothesis. In particular there is no `AttackExtensional sem.spec`.

That absence is load-bearing, not incidental. `Lara.Observation.observe_congr` does assume `AttackExtensional`, but it moves an observation between two distinct frameworks that merely agree pointwise on the carrier, and extensionality is what licenses concluding the extensions agree. Here the frameworks are equal, so no such licence is needed, and a generic result that assumed `AttackExtensional` anyway would be strictly weaker than its grounded ancestor and would not deserve to be called its generalization.

The `Nodup` obligation discharges unconditionally. `ExtensionSemantics.sound` and `Semantics.observe_grounded` carry `F.args.Nodup`, but in `observeSem_grounded` the framework is `Invariants.eraseAF F`, whose carrier is `List.range F.size` by definition, so `List.nodup_range` closes the obligation outright and it never reaches the statement. It is a property of the frozen erasure, not a convenience: every carrier this development observes is positional, so duplicate arguments are not representable.

### The grounded regression is an iff, not an implication

```lean
theorem ctxEquivSem_grounded_iff (reg) (F₁ F₂) :
    CtxEquivSem groundedSem reg F₁ F₂ ↔ CtxEquiv reg F₁ F₂
```

It is an `iff` in both directions, so grounded generic equivalence and `CtxEquiv` are the same relation, and nothing stated about `CtxEquiv` is weakened, strengthened, or otherwise disturbed. The scope is narrow: this settles the grounded instance and nothing else, and it must not be cited as saying that `CtxEquiv reg F₁ F₂` implies `CtxEquivSem sem reg F₁ F₂` at any other semantics.

The separations proved at this level are between observation functions at a concrete context and fragment. `obsSem_cycle_stable_ne_grounded` shows that on a linked three-cycle `stableSem` observes `ClaimObservation.noExtension` while `groundedSem` observes `contested`, and `obsSem_sink_preferred_ne_grounded` shows that on a linked sink `groundedSem` observes `contested` and `preferredSem` observes `defeated`. Those witnesses do not separate the observation relations, because a relation counterexample requires two fragments grounded-equivalent in every context, not just one grounded-indistinguishable fixture. A follow-up supplies the missing universal argument in `Lara.Examples.ContextualSeparation`: two fragments share every field except the single exported atom, both own leaf support, the fixed policy permits no attacks, their link guards and checker inputs are identical, and for any accepted context both exported atoms have unattacked checked support and are grounded-justified, which proves `grounded_ctxEquiv` over all contexts including failing ones. The adequate semantics family `singletonSem a` retains exactly the carrier sublists equal to `[a]`, and at a concrete accepted empty context selecting one supporting position distinguishes the exported atoms; `singleton_not_ctxEquivSem` uses that context, and `counterexample` and `grounded_does_not_imply_semantic` refute the implication quantified over arbitrary `ExtensionSemantics`. The scope is explicit: the interface requires an adequate enumerator, not that its extensions are complete, maximal, or invariant under argument renaming, and the selector is a valid instance of that interface. So the result refutes the unrestricted implication but does not prove separation at complete, preferred, stable, or semi-stable semantics, nor an implication restricted to identical export lists, and the current `CtxEquiv` definition imposes no identical-exports premise. The grounded instance still coincides by `ctxEquivSem_grounded_iff`.

Beyond its definition, `ctxEquivSem_negative` exhibits a pair `CtxEquivSem` is false of at `stableSem`, a non-grounded instance, so it is not merely `Linking.ctxEquiv_negative` transported through the `iff`. `ctxEquivSem_semantic_negative` strengthens that: an empty context distinguishes `fullCycleFrag` from `singletonCycleFrag` under the same cyclic policy, with identical exports `[pA]`, and both links pass the guard and whole-unit checker; `obsSem_semantic_negative` pins both outer constructors to `.observed`, with payloads `noExtension` and `observed justified`, and proves their disequality, while `obsSem_semantic_negative_grounded` also pins the cycle's grounded payload to `observed contested`, so the semantics choice matters at this witness.

### Non-triviality and the fixtures

There was no context-level fixture on which two semantics disagree, so the fixtures were built. Both reuse the `Examples.Linking` vocabulary and change only the `defeat` field. The split is forced by `SideOk.attack_complete`: a side must declare an attack for every contrary pair among its own arguments, while cross-boundary conflicts are saturated automatically by `crossAtts`, so the pair needing a declared edge goes inside the fragment and the link supplies the rest.

The three-cycle (`p ⊣ q`, `q ⊣ s`, `s ⊣ p`, with the context declaring `q`, the fragment declaring `p` and `s` and the `s ⊣ p` edge, and exporting `p`) is the sharper of the two. `noExtension` is a constructor the grounded reading provably cannot reach, because `observeSem_grounded` always returns `ClaimObservation.observed _` and `liftObservation` only produces that constructor, so this shows `obsSem` inhabiting an arm of `ObservationOf ClaimObservation` that `liftObservation ∘ obs` cannot inhabit. The widening of the observed payload from `Grounded.Status` to `ClaimObservation` is therefore forced by a fixture of this development, not only by `Semantics.observe`'s signature. The sink (`p ⊣ q`, `q ⊣ p`, both attacking `s`, with the fragment exporting `s`) answers the sceptic who grants the `noExtension` arm and argues that whenever both semantics do answer they answer the same: neither side reports `noExtension`, both answer, and they disagree. Reusing `symPolicy` would not have worked, because there the observed claim is supported by a node inside the two-cycle, so the skeptical reading is `contested` under every semantics; the sink observes a node outside the cycle that every preferred extension attacks, and that asymmetry is what the separation needs. Each separation carries a disequality conjunct, so a future collapse of a fixture is a build failure rather than a silent regression of two values pinned separately, and both carriers are pinned first, so a fixture that stops linking is distinguishable from a separation that collapsed. Three acceptance criteria that would otherwise be enforced by a reader are enforced by the build: `ctxEquivSem_grounded_iff` must stay an `iff`, since `ctxEquivSem_grounded_negative` consumes `.mp` and `ctxEquivSem_grounded_of_ctxEquiv` consumes `.mpr`; the separations must actually separate; and `obsSem_grounded` must be exercised, not merely stated.

Three results are stated over an arbitrary `sem` rather than checked at instances, because the theorems they instantiate are: `obsSem_gap_uniform` (since `Semantics.observe_gap` is universally quantified with no hypothesis, a five-instance check would be strictly weaker and would say nothing about semantics nobody has written down), and `obsSem_incompatible_id_clash` and `obsSem_rejected_signature` (the link guard and the whole-unit checker both fire before any projection is consulted, which is the content of `obsGen_incompatible` and `obsGen_rejected`).

`congruence_witness_sem` instantiates the generic congruence on `cycleCtx` and `cycleFrag`, the same carrier where `obsSem_cycle_stable_ne_grounded` separates the observations, so the congruence holds uniformly in `sem` at a carrier where the choice of semantics changes the observed value. `registry_swap_witness_sem` still uses the two-node chain where all five semantics agree, and its semantics quantifier remains inert. The assurance-free caveat applies to both: `cycleFrag` and `fragEx` carry no certificates, so `mapAssurFrag f` is the identity on them for every `f`. `cert_congruence_witness_sem` and `cert_registry_swap_witness_sem` close the certificate-bearing witness gap, instantiating the semantics-parametric congruences on the certified fragment with `certSwap` and `registryWrapped`; they quantify over arbitrary `sem` and are pinned in `AxCheck.lean`, but they do not establish that the semantics quantifier is non-inert at this certified carrier, which the three-cycle supplies separately.

### Relational parametricity

The congruence quantifies over a function `f : Assurance → Assurance` and relates `F` to `mapAssurFrag f F`. The relational form replaces the function by a relation while keeping the theorem's shape:

```lean
theorem obsGen_parametricity {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
    {R : Assurance → Assurance → Prop} {C : Context} {F₁ F₂ : Fragment}
    (hR : RelInj R)
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F₁) (hF : RelFrag R F₁ F₂)
    (hfix : RelFixesContext R C) :
    obsGen g reg₁ C F₁ = obsGen g reg₂ C F₂
```

The four hypotheses are in `lean/Lara/Context/Parametricity.lean`:

| Hypothesis | What it says | Functional counterpart |
|---|---|---|
| `RelInj R` | `R` reflects and preserves equality on what it relates, so it is the graph of a partial injection | `Function.Injective f` |
| `RelPreserving R CertOk₁ CertOk₂` | acceptance transports, guarded by `R α β` | `AssurPreserving f`, unguarded |
| `RelFrag R F₁ F₂` | the two fragments agree on Σ, policy, declared leaves, ground atoms, imports, and exports, and their args and attacks are pointwise `R`-related | `F₂ = mapAssurFrag f F` |
| `RelFixesContext R C` | `R` relates the context's own material to itself | `FixesContext f C` |

It is proved once over an arbitrary projection `g`, exactly as `obsGen_congr` is, so the semantics-parametric form is an instantiation and not a second proof.

| Declaration | Conclusion |
|---|---|
| `Context.obsGen_parametricity` | `obsGen g reg₁ C F₁ = obsGen g reg₂ C F₂`, any projection `g` |
| `Context.backend_replacement_parametricity_sem` | `obsSem sem reg₁ C F₁ = obsSem sem reg₂ C F₂`, any `ExtensionSemantics` |
| `Context.backend_replacement_parametricity` | `obs reg₁ C F₁ = obs reg₂ C F₂`, the grounded reading |
| `Context.backend_replacement_parametricity_local` | the same, under an acceptance hypothesis ranging only over `occurrences F` |
| `Context.backend_replacement_parametricity_local_sem` | the occurrence-local form at any `ExtensionSemantics` |
| `Context.backend_replacement_congruence_of_parametricity` | `backend_replacement_congruence`, re-derived as the `graphOf f` instance |
| `Context.congruence_correspondence` | that re-derivation restates the original exactly (`rfl`) |

The development's own relation vocabulary mirrors the functional lemmas one for one. A representative sample of the `_rel` lemmas and the functional lemma each mirrors: `hasSupport_rel` mirrors `hasSupport_mapAssur`; `hasAttack_rel` mirrors `hasAttack_mapAssur`; `conclusionCache_rel` and `crossAtts_rel` mirror `conclusionCache_map` and `crossAtts_relabel`; `dedupList_rel` mirrors `dedupList_map_of_injective`; `link_rel_commutes` mirrors `link_relabel_commutes`; `covered_rel` mirrors `covered_mapAssur`; `attackComplete_rel` mirrors `attackComplete_map`; `checkUnit_rel` mirrors `checkUnit_map`; `coveredB_rel`, `attackClosureB_rel`, and `containsB_rel` mirror their `mapAssur` counterparts; `nodes_conclusion_rel` mirrors `nodes_conclusion_map`; `compileUnit_rel` mirrors `compileUnit_map`; `exists_accepted_rel` mirrors `exists_accepted_relabel`; `compileUnit_link_rel` mirrors `compileUnit_link_relabel`; and `obsGen_parametricity` mirrors `obsGen_congr`. `Lara.Forall₂` (`lean/Lara/ListRel.lean`) is the pointwise list relation the development consumes; core Lean has no `List.Forall₂`, so the family and its lemmas are authored locally. `RelTerms` and `RelDis` are not `Forall₂` instances, because they must be declared in the same `mutual` block as `RelTerm`, which recurses through the support term's nested list fields; `relTerms_iff_forall₂` bridges the two spellings at their construction sites.

### Why RelInj is necessary

`RelInj R` says `R` reflects and preserves equality on the assurances it relates. Three consumers force it, and they are not proof-engineering conveniences, because each one is a place where the calculus itself compares terms. First, `dedupList`, the structural merge, decides `x ∈ rest`, so a relation collapsing two distinct arguments changes the merged argument list, and with it the node count of the compiled framework. Second, `coveredB` decides `k.source = source`, so a collapsing relation adds edges; the header of `Lara/Erase.lean` already records this for the non-injective erase-to-certified map, that collapsing distinct subterms can merge occurrences and add subargument-closure edges. Third, `checkUnit_complete`'s `Nodup` premise on the merged argument list is discharged here by `nodup_rel`.

This is witnessed, not asserted. `Context.relInj_necessary` is `coveredB_rel` with `hR` deleted and the conclusion negated: it exhibits a relation, two attack lists, and two source and target pairs satisfying every remaining hypothesis, on which the two coverage verdicts differ. `RelInj` is also characterized rather than described: `relInj_functional` proves `R` is single-valued and `relInj_injective` proves it is injective. The honest name for what is proved is parametricity over partial-bijective certificate relations.

The relational form costs a hypothesis the functional one did not in one place: `attackOcc_rel` and `contains_rel` carry `RelInj R` where their functional originals carry nothing. The reason is structural: the functional lemmas may compute the image occurrence as `mapAssur f t`, so its uniqueness is free, while a relation supplies no such image, so the occurrence has to be produced (`attackOcc_rel_exists`) and then pinned to the one the caller already holds, which is exactly `relTerm_inj`, that is `RelInj`. Every call site already carries `RelInj`, so nothing downstream weakens.

The necessity of `RelInj` is also witnessed at the observation level. `lean/Lara/Examples/CertificateCollapse.lean` uses a context that declares the premise and attacker leaves but contributes no arguments. The fragment has two syntactically distinct defeasible wrappers with the same conclusion `p`, each containing a strict certificate for `q`, and a leaf concluding `s`; one explicit undercut targets the first wrapper at its root, and the contrary table is empty, because `SideOk.attack_complete` covers all contrary pairs but does not require all possible exception attacks to be declared. The certificates share backend identity and digest and differ in payload; a fixture-only natural-deduction adapter interprets every payload as the same free-slot proof, bypassing opaque decimal parsing during kernel reduction without adding an axiom, and it neither changes the production decoder nor asserts that production natural deduction accepts the rejected certificate. `collapse` keeps backend identity and digest fixed and replaces each certificate payload with the accepted slot certificate, so acceptance preservation holds for arbitrary rules; the relation is `graphOf collapse`, with `related`, `fixes_context`, and `not_relInj` discharging its structural premises and exhibiting its failure of equality reflection. Before collapse, the second wrapper is unattacked and justifies `p`; after collapse, structural deduplication merges it with the attacked first wrapper, and `p` is defeated. `linked_shape` pins the argument lists, `accepted` pins both checker successes, and `observations` proves both values and their inequality by `decide`. The bundled `relInj_observationally_necessary` states exactly the other premises plus the negated observation equality. The witness concerns the interaction of structural merging and attack coverage; it does not isolate coverage as the sole mechanism, nor establish a minimal replacement hypothesis.

### What the relational form buys, and localization

The structural step is mechanized in `lean/Lara/Context/FiniteExtension.lean`:

```lean
theorem relFrag_exists_injective_fixesContext
    (hR : RelInj R) (hF : RelFrag R F₁ F₂) (hC : RelFixesContext R C) :
    ∃ f : Assurance → Assurance, Function.Injective f ∧
      F₂ = mapAssurFrag f F₁ ∧ FixesContext f C
```

`relFrag_exists_injective` gives the fragment-only version, and `exists_total_injective_extension_on` proves the underlying construction: for any finite list `xs`, some total injection agrees with every pair of `R` whose source lies in `xs`. Induction starts at the identity and composes with an output swap for each new constraint, and partial functionality and injectivity ensure that the swap preserves previously required pairs; instantiating `xs` with `occurrences F₁ ++ occurrences C.frame` realizes both finite structures. No enumeration of `Assurance`, decidability of `R`, or Mathlib is needed, since classical choice handles the existential case split.

Extending all of an arbitrary `R` is false, even on this countably infinite type: the proposed statement confused finite realization with an unrestricted extension. `not_every_relInj_has_total_extension` mechanizes the counterexample, where `shiftAssurance` increments every certificate's backend version, fixing `none` and `trusted`; it is injective and misses certificates with version zero, and its inverse graph satisfies `RelInj` while already mapping onto the entire type, so an injective total extension would have no unused image for a version-zero certificate. The finite theorem discharges the structural obligations of functional congruence, including the context requirement, but it supplies no proof of global acceptance preservation; if a realizing map also has that property, the original congruence applies after rewriting by the realization equation. The remaining distinction is therefore acceptance scope, not a structural obstruction to realizing finite related material.

`RelPreserving R` is conditioned on `R α β`: it obliges only the pairs `R` actually relates, where `AssurPreserving f` obliges every rule and every assurance in the type. The localized obligation has a concrete theorem instance: `occRel F` is the identity relation restricted to `occurrences F`, the assurances the fragment actually carries, with `relInj_occRel` and `relFrag_occRel` discharging the two side conditions, and

```lean
theorem backend_replacement_parametricity_local
    (hlocal : ∀ r As Cc α, α ∈ occurrences F →
      AssuranceOk (certOkOf reg₁) r As Cc α → AssuranceOk (certOkOf reg₂) r As Cc α)
    (hadm : Admissible reg₁ C F)
    (hC : ∀ α ∈ occursList C.frame.args, α ∈ occurrences F)
    (hA : ∀ α ∈ (C.frame.atts.map occursAtt).flatten, α ∈ occurrences F) :
    obs reg₁ C F = obs reg₂ C F
```

is representation independence under an acceptance hypothesis that ranges over `F`'s own certificate occurrences and nothing else. `backend_replacement_parametricity_local_sem` is the same at an arbitrary `ExtensionSemantics`. There is no separate `registry_swap_parametricity`: its statement would be character-for-character `backend_replacement_parametricity_local`, since `registry_swap_congruence` differs from `backend_replacement_congruence` only by moving no material, and the occurrence-local form already moves no material, so two names for one theorem would be worse than one.

How local "local" actually is: `RelFixesContext R C` requires `R` to relate the context's own material to itself, and combined with `RelInj` that makes `R` the identity on the context's occurrences, so an assurance appearing in both the context and the fragment cannot move. This is inherited from `FixesContext` and is correct, because a backend swap inside a fragment is not licensed to rename the context's certificates, and a statement that let it would be comparing two different contexts. But it is a real bound on the localization claim, and it is why `backend_replacement_parametricity_local` carries the two side hypotheses `hC` and `hA`: the localization is to `F`'s occurrences plus whatever the context also carries, not to `F`'s occurrences alone.

The grounded fixpoint needed nothing. `compileUnit_rel` concludes an equation between `StructuredAF`s, not a pointwise agreement, and `Grounded.statusC` and `Semantics.observe` are then applied to one and the same framework on both branches, so the relation is erased before any semantics runs. No grounded-labelling lemma, no `AttackExtensional` hypothesis, and no new fixpoint machinery appears anywhere in this development. The dependency chain runs from the two side conditions, through the judgment transport (`hasSupport_rel`, then `hasAttack_rel`, which calls it in all three of its cases), the saturation (`conclusionCache_rel`, then `crossAtts_rel`), the merge and deciders (where `RelInj` is consumed by `dedupList_rel` and `coveredB_rel`), the linked unit and acceptance (where it is consumed by `checkUnit_complete`'s `Nodup` premise), and the carrier (`compileUnit_link_rel`), at which point the relation is erased and only instantiations remain.

### Composed and whole-program companions

All four semantics-parametric congruences have relational companions:

| Functional | Relational |
|---|---|
| `backend_replacement_congruence_sem` | `backend_replacement_parametricity_sem` |
| `registry_swap_congruence_sem` | `backend_replacement_parametricity_local_sem` |
| `backend_replacement_congruence_composed_sem` | `backend_replacement_parametricity_composed_sem` |
| `whole_program_replacement_sem` | `whole_program_parametricity_sem` |

`relFixesContext_composed` combines the two relational fixed-context premises, using `dedupList_rel` on the appended argument lists and `Forall₂.append` on attacks; `obsGen_parametricity_composed` then instantiates the single contextual root with grounded and arbitrary-semantics wrappers, and `admissible_composed` applies unchanged. The whole-program companion takes a different contract: `whole_program_replacement_sem` takes two already checked programs and observes `checkedAF`, with no context or admissibility, so its relational companion follows `coveredB_rel → edgeB_rel → checkedAF_rel` and rewrites the framework. It requires `RelInj` and pointwise related argument and attack lists, but no `RelPreserving`, because both programs already carry validity evidence; routing it through contextual acceptance would add premises absent from the original. Neither route needs `AttackExtensional`, because each establishes carrier equality.

For the closed-link reading, `closedOccurrences C F` is the concatenation of `occurrences C.frame` and `occurrences F`, representing union by membership; `mem_closedOccurrences` proves that union statement and `occurrences_composed` proves that context composition also takes union by membership, despite argument deduplication. These are declared occurrences, including assurances nested in attack terms, and no claim of list equality or duplicate elimination is made. `closedOccRel C F` restricts identity to that union, and its injectivity, related fragment, and fixed context are proved without the fragment-only theorem's containment assumptions. `obsGen_parametricity_closed_local` factors through `obsGen_parametricity`, and `whole_program_parametricity_local_sem` and its grounded twin instantiate it. This local form moves no material and still requires admissibility of the original link; it localizes acceptance to the whole closed link, whereas the older local form localizes to the fragment at the cost of context containment, and neither claim should be silently substituted for the other. All added theorems are pinned in `AxCheck.lean`. Both new modules carry `set_option autoImplicit false`, which is load-bearing rather than style: with auto-implicit on tree-wide, a bare or mistyped predicate in a hypothesis position would auto-bind as an implicit of unknown type and elaborate into a vacuous theorem that builds clean and passes both gates, and this option is the only thing that can catch that.

### Paper claim boundary

The paper may claim that representation independence over related backends is proved with a relational quantifier (`R : Assurance → Assurance → Prop`), lifted structurally through support terms, attacks, and fragments (`obsGen_parametricity`); that it holds at every extension semantics in the interface with no additional hypothesis (`backend_replacement_parametricity_sem`), because the whole chain factors through the single choke point `obsGen`; and that the acceptance hypothesis can be localized to the fragment's own certificate occurrences (`backend_replacement_parametricity_local`, `_local_sem`), which is the localization the docstrings of `registry_swap_congruence` and `registry_swap_congruence_sem` name as the hypothesis they do not themselves carry. State the trade rather than a pure upgrade: the localized theorem is not strictly stronger than `registry_swap_congruence`, because it weakens the acceptance hypothesis to `α ∈ occurrences F` but adds `hC` and `hA`, and neither theorem implies the other. The honest sentence is "localizes the acceptance hypothesis at the cost of two context-containment side conditions", never "strictly stronger". The paper may also claim that the existing functional theorem is re-derived rather than paralleled (`backend_replacement_congruence_of_parametricity` is the `graphOf f` instance, and `congruence_correspondence` checks by `rfl` that it restates `backend_replacement_congruence` exactly), and that `RelInj` cannot be dropped from the observational theorem, since `relInj_necessary` witnesses coverage failure and `Examples.CertificateCollapse.relInj_observationally_necessary` supplies every other premise and negates the conclusion.

The paper must not call this parametricity over arbitrary relations; `RelInj` is required, and the honest phrase is parametricity over partial-bijective certificate relations. It must not claim full abstraction: `RelTerm` is a structural lifting of a relation on certificates, not the logical relation over the contrary-visible occurrence profile, and nothing here reopens the full-abstraction work. It must not state the result as unconditional in the context quantifier, since `Admissible reg₁ C F₁` is inherited for the reason the congruence records. It must not claim the result is local to `F` alone, per the fixed-context discussion above, and must not claim that every non-injective relation separates observations, since the fixture refutes deleting `RelInj` wholesale with the graph of a non-injective function that violates equality reflection but not single-valuedness; it does not establish necessity of each half of `RelInj` separately or prove that no weaker, carrier-specific hypothesis could suffice. It must not extend all pairs of an arbitrary relation: the finite-extension follow-up proves finite realization, including context fixing, and refutes the unrestricted extension statement, while global acceptance preservation remains an independent hypothesis with no strict-separation witness. It is not a Haskell-side result.

## Surface calculus and verified elaboration

The surface calculus closes the trusted-boundary gap between the structured presentation codec and the core checker. The codec round trip and the core metatheory were each proved, but the lowering between those two boundaries was justified only by executable tests, so a parsed value-binding, comparison, inferred argument, named certificate, or surface attack could in principle be lowered differently from the object assumed by the core proof. The verified model's input is already a `Lara.Presentation.Program` paired with a `Lara.Presentation.Policy`.

### Trusted boundary and the supported fragment

`Lara.Surface.Input` contains two complete live `lara-syntax@0.10` AST values unchanged, and the environment is quantified:

```lean
structure Lara.Surface.Env (canon : String → String) where
  registry : Support.BackendRegistry canon
  startsIdent : String → Bool
  startsIdent_nat_false : ∀ n, startsIdent (Nat.repr n) = false
  encodeProp : String → Option String
```

The theorem begins after concrete parsing. It covers the full structured AST and the pure elaboration model, not source bytes, lexer tokens, comments, whitespace, source locations, or concrete parser diagnostics. The backend registry and identifier classifier remain parameters with explicit soundness premises where they are transported; the proposition encoder is also a parameter, but global renaming reuses it unchanged on formula source text that `RenamingSound` requires to remain fixed, so there is no separate encoder-renaming premise.

`Lara.Surface.Elaborated canon` retains the core gamma, ground atoms, and `Lara.Unit`, as well as surface-visible claims, authored argument IDs and obligations, open questions, resolved attacks, and the expanded semantic program. These extra fields are the alignment witnesses needed to state preservation without pretending that the core unit retains authored names.

The supported fragment is not a smaller AST. `Supported` records the complete live AST's structural lowering restrictions:

```lean
structure Lara.Surface.Supported (input : Input) : Prop where
  policy_matches : input.program.policy = input.policy.id
  declaration_ids_nodup : DeclarationIdsNodup input.program
  rule_namespaces_wf : RuleNamespacesWellFormed input.policy
  value_bindings_wf : ValueBindingsWellFormed input
  comparisons_wf : ComparisonsWellFormed input.program input.policy
  inferred_args_wf : InferredArgsWellFormed input.program input.policy
  named_certs_wf : NamedCertificatesWellFormed input.program input.policy
  attack_names_wf : SurfaceAttacksWellFormed input.program input.policy
  canonical_labels : CanonicalPremiseLabels input.policy
```

The fields mean, exactly: the program names the supplied policy; leaf, argument, claim, and value-binding identifiers are duplicate-free; rule IDs are duplicate-free, each rule's premise-label and question namespaces are duplicate-free and disjoint, and reserved labels are absent; value bindings, structured value substitution, prose interpolation, and `{cell ...}` references satisfy the frozen sort and name restrictions; every comparison has one matching relation and polarity scheme and its generated declarations, roles, substitutions, and conclusions have the required shape; inferred arguments refer only to uniquely resolved earlier declarations, cover their rule parameters, and have shape-correct named discharges; named certificates have an allowed schema, unambiguous premise slots, well-formed named binders, and valid formula annotations; rebut, undercut, and undermine endpoints and paths resolve in their typed namespaces; and premise labels are either absent or have rule-premise length with at least one named slot.

`supportedB` is the executable conjunction of the named field deciders, and `supportedB_iff` proves `Lara.Surface.supportedB input = true ↔ Lara.Surface.Supported input`. The component correspondences (`declarationIdsNodupB_iff`, `ruleNamespacesWellFormedB_iff`, `valueBindingsWellFormedB_iff`, `comparisonsWellFormedB_iff`, `inferredArgsWellFormedB_iff`, `namedCertificatesWellFormedB_iff`, `surfaceAttacksWellFormedB_iff`, `canonicalPremiseLabelsB_iff`) expose the projections used by reflection.

Role, status, and group checks run after value and comparison expansion and are carried separately by the syntax-directed judgment, matching production order. `ChecksAuthoredConclusion` validates a reconstructed argument's announced role: a declared `supports(c)` must have a conclusion equivalent to `claimFormal(c)`, an undeclared support ID is the explicit derived-support arm, and a challenge must name a declared target argument or leaf. `StatusesWellFormed` and `statusesWellFormedB_iff` require every requested status ID to name a declared claim, including comparison-generated ones. `GroupsWellFormed` and `groupsWellFormedB_iff` require unique group IDs, distinct members, at least two members, and only declared leaves. `AttackEndpointsDeclared` and `validateAttackEndpoints` are the adjacent raw namespace guard before groups, and group diagnostics use production's seen-prefix rule, reporting the value at the first repeated occurrence, so `[a,b,b,a]` reports `b`. These are independent predicates and deciders, not consequences of core acceptance, and keeping them separate makes their post-expansion error precedence explicit rather than folding them into the early structural guard.

### Binding is not global renaming

Alpha-equivalence is reserved for genuine lexical binders. `Surface.Binding.RuleAlpha` abstracts rule parameters by declaration slot, with `ruleAlpha_refl`, `ruleAlpha_symm`, and `ruleAlpha_trans` making it an equivalence, and `substParam` is capture-avoiding and partial, with `substParam_fresh_identity`, `substParam_preserves_wellSorted`, and `substParam_compose_of_fresh` stating its identity, preservation, and fresh-composition laws. `NDNamed.Alpha` similarly abstracts only named `nd@1` lambda binders and their bound `.hypX` occurrences; numeric and symbolic premise references, theory indices, formula text, and anonymous binders remain fixed. `NDNamed.toDB_eq_of_alpha` and `NDNamed.lowerNamed_eq_of_alpha` prove that alpha-equivalent well-formed named certificates have identical de Bruijn and kernel lowerings, and `Surface.alpha_elaboration_invariant` exposes the paper-facing lowering equality under both well-formedness premises and `startsIdent_nat_false`.

Top-level declaration IDs, argument references, premise labels, value names, source references, and related global namespaces are not binders. They use the typed `Surface.Binding.GlobalRenaming`, and backend IDs, versions, theory and artifact digests, policy IDs, and other replay-significant identities are not fields of this renamer and stay fixed. Global equivariance has two explicit hypotheses: `RenamingSound ρg program policy` supplies the structural and fixed-spelling conditions, and `EnvRenamingSound env ρg` supplies preservation of `env.startsIdent` under `renameText` and registry replay under the renamed certificate, premise, and conclusion data. Under those hypotheses, `Binding.supported_rename_iff` preserves and reflects `Supported`; `Renaming.global_renaming_stage_transports` packages transport of supportedness, value and comparison expansion, reconstruction and certificate lowering, attack resolution, admission and pruning, and core-check acceptance; and `Renaming.global_renaming_equivariant` says that a successful audited source elaboration has a related successful audited renamed elaboration, both pure elaborations return their audit outputs, core-check success agrees, and every accepted source checked unit has a related accepted renamed unit. Two ground relations appear in that last theorem, for different purposes. `ElaboratedRelated.ground` uses `GroundRelated`, which renames the executable retained-leaf and requested-status prefix but keeps the policy theory table as a literal replay-significant suffix, so the theorem's equality of `exceptIsOk` results compares the actual source and target elaboration outputs. The final `CheckedUnitRelated` witness instead checks `source.output.ground.map (renameResidualAtom ρg)` together with `renameCoreUnit ρg source.output.unit`; it is the fully mapped-ground core transport witness supplied by `checkUnit_ok_rename`, and it is not a claim that this ground equals `target.output.ground` when fixed theory atoms are present. This is typed equivariance, not alpha-equivalence and not permission to rename replay identities.

### Production-ordered passes

`Surface.elaborateWithAudit` performs one canonical sequence:

```text
program/policy ID match
  → canonical premise-label validation
  → duplicate admission-key and leaf-ID validation
  → value substitution, prose interpolation, and {cell ...} expansion
  → comparison expansion in declaration order
  → authored argument/claim and rule-namespace checks
  → raw surface-attack endpoint declaration checks
  → duplicate-group validation
  → left-to-right argument reconstruction
      (reference resolution, theta inference, named discharges,
       certificate-name/formula lowering, authored-role validation)
  → surface attack resolution, then raw attack alignment
  → requested-status resolution
  → declared Unit assembly
  → one admission evaluation and policy/group prune
  → retained Elaborated output
```

`{cell ...}` belongs to value expansion, not comparison expansion. Certificate-name and source-authored formula lowering occur inside the left-to-right argument fold, where earlier declarations form the reference environment. All declared surface attacks resolve before admission pruning. The declared unit is assembled before the one admission evaluation, and the retained unit is constructed from that evaluation's prune. The finite core-check ground is retained leaf conclusions, resolved requested status formals, and the policy theory table; unrequested declared claims do not silently enter `surfaceGround`.

`Surface.elaborate` projects the audited output. It intentionally does not call `Check.Unit.checkUnit`, `Surface.check`, or a concrete parser. In particular, it does not itself establish core signature and ground sorting, recursive support typing, typed conflict completeness, or backend certificate acceptance.

### Independent judgment and executable correspondence

Value interpolation and comparison expansion each have an independent relation:

```lean
expandValues policy program = .ok out → ExpandsValues program out
ValueBindingsWellFormed ⟨program, policy⟩ →
  ExpandsValues program out → expandValues policy program = .ok out

expandComparisons policy program = .ok (target, generated) →
  ExpandsComparisons policy program target generated
GeneratedIdsFresh program = true →
  ComparisonsWellFormed program policy →
  ExpandsComparisons policy program target generated →
  expandComparisons policy program = .ok (target, generated)
```

These are `expandValues_sound` and `expandValues_complete` and `expandComparisons_sound` and `expandComparisons_complete`. The prose walker has the corresponding `expandNl_sound` and `expandNl_complete` pair against `ExpandsNl`.

`Surface.Checks env input output` is syntax-directed. Its constructors and fields carry supportedness, admission, generated-ID freshness, per-rule, role, status, and group well-formedness, the two independent expansion derivations, the left-to-right argument and attack derivations, exact output component equalities, and `CoreObligations env output`. `CoreObligations` contains declarative signature and policy sorting, scope and rule-ID conditions, argument uniqueness, `HasSupport` derivations (including certificate and backend acceptance) at whatever root obligation set each declaration has, typed attacks, endpoint membership, and `AttackComplete`. A declaration with open mandatory questions types and becomes a located hole, so the support field asks only for typing; examples that need every declaration complete prove that stronger fact separately. It does not contain `checkUnit` success, `exceptIsOk`, or an equivalent wrapper.

`CoreObligations.checkUnit_complete` feeds those fields to `Check.Unit.checkUnit_complete_holes` and derives a concrete accepted carrier, and `CoreObligations.of_checkUnit_ok` is the converse extraction used by the executable checker. Thus `Checks` is not defined as successful `elaborate` or successful core execution, and no derivation constructor calls `elaborate`. For all `env`, `input`, and `output`:

```lean
check env input = .ok output → Checks env input output       -- check_sound
Checks env input output → check env input = .ok output       -- check_complete
Checks env input out₁ → Checks env input out₂ → out₁ = out₂  -- checks_deterministic
Checks env input output → Supported input                    -- checks_supported
```

`check` is the executable decider for the independent judgment. It executes the core checker after declarative surface assembly; soundness extracts `CoreObligations`, while completeness derives the execution from those obligations.

### Elaboration theorems

Pure elaboration completeness is one-way and unconditional once a derivation exists:

```lean
theorem elaborate_complete
    (env) (input) (output)
    (h : Checks env input output) :
    elaborate env input = .ok output
```

There is deliberately no unconditional `elaborate_sound : elaborate env input = .ok output → Checks env input output`, because pure elaboration omits the core check and the full supported-fragment validation, so that statement is false. The preservation theorem quantifies over `env`, `input`, `output`, and a surface derivation:

```lean
theorem elaborate_preserves
    (env) (input) (output) (h : Checks env input output) :
  ∃ checked,
    elaborate env input = .ok output ∧
    Check.Unit.checkUnit output.gamma env.registry output.ground output.unit =
      .ok checked ∧
    output.openQuestions.map Prod.fst = output.argIds ∧
    output.openQuestions.map Prod.snd = coreOpenQuestions output.unit ∧
    output.unit.atts = output.resolvedAttacks
```

Thus a derivable surface input lowers successfully to the same output, the actual core checker accepts that output, authored argument order aligns with the core-visible question sequence, and retained attacks are exact. Reflection quantifies over an explicit checked-unit witness and has both load-bearing hypotheses:

```lean
theorem elaborate_reflects
    (env) (input) (output) (checked)
    (hsupported : Supported input)
    (helab : elaborate env input = .ok output)
    (hcore :
      Check.Unit.checkUnit output.gamma env.registry output.ground output.unit =
        .ok checked) :
    Checks env input output
```

Its direction is from this already-parsed, supported input's successful canonical lowering plus successful core checking back to the independent surface judgment, and it does not quantify over arbitrary core units. The separately quotable projections are exact: `obligations_preserved` (`output.authoredObligations = authoredObligationsOf input.program`); `attacks_preserved` (`output.unit.atts = output.resolvedAttacks`); `conclusions_preserved` (a successful `reconstructArgument` followed by successful `lowerToSupportTerm` has `conclOfTerm ... built.term = some built.conclusion`); and `argument_order_preserved` (authored IDs equal the first projection of `openQuestions`, while `coreOpenQuestions output.unit` equals its second projection).

### Direct and compiled observation

`directAF hsurface` is indexed by a surface derivation. Its carrier is the index range of `directArgs`, the retained declarations whose core support typing has an empty obligation set, in retained order; both attack endpoints index that list, and attacks are computed from `output.resolvedAttacks`. A located hole is never a node, so a leading hole cannot become node zero. It does not call `elaborate`, `Compile.edgeB`, or `Compile.checkedAF`.

`Elaborated` is built before core checking, so it carries only the claim alternative ledger `output.claimAlternatives` (`claimAlternativesOf`): for each declared claim, the retained declaration positions of the arguments whose authored conclusion supports it. `claimsOf nodeDecls holeDecls` classifies a ledger by a declaration partition: an alternative at the declaration of framework node `n` contributes `n` to `support`, and one at a located hole contributes its retained declaration position to `holes`. The authored root open set decides nothing; it stays in `openQuestions` and `authoredObligations` as diagnostic data.

The two claim APIs are independently defined and optional. `directClaims` re-runs source reconstruction over the semantic program and classifies its ledger by the direct partition (`directNodeDecls`, `directHoleDecls`); it reads neither `output.claimAlternatives` nor a checked cache. `coreClaim? output checked claimId` classifies `output.claimAlternatives` by the accepted unit's cached node declarations and hole positions. `directDecls_eq_checked`, `directClaims_eq_coreClaims`, and `directClaim_eq_coreClaim?` prove their agreement for an accepted surface derivation. A missing ID remains `none` on both sides and is never manufactured into an empty-support gap claim.

`claimAlternatives_coherent` states the surface and core hole correspondence: each claim's holes are the cached holes sitting at its alternatives, in declaration order, each the retained declaration at its position with an `ArgId` and exactly the core's obligation set, and its support is the framework index of every alternative that is a node. The global hole list `checked.holes` also holds holes whose conclusion no claim names. As with `support`, a claim's holes are selected by authored claim id, not by conclusion equivalence: `claimAlternatives_holes_sound` shows every selected hole concludes the claim's formal (excluding the derived-support role, which is never compared with a formal), and `claimAlternatives_holes_complete` shows conclusion equivalence selects nothing more when every argument supports a formal-bearing claim and claim formals are pairwise inequivalent, while with shared formals the id selection can miss alternatives the core's conclusion-equivalence selection includes. `coreHoleReport` renders that global list as `(ArgId, obligations)` rows, and `coreHoleReport_obligations` shows it drops none. The kernel-checked `Lara.Examples.SurfaceHoles` fixture exercises a root, a premise, and a discharge hole (each with exactly one deduplicated mandatory obligation), an optional-only alternative that stays complete support, a claim with both complete and incomplete alternatives, and a claim with only a hole (`gap`).

For a surface derivation `hsurface : Checks env input output` and a concrete successful core check `hchecked`, `directClaim_support_bound hsurface claimId hclaim` proves every support index of the selected claim is in the direct carrier, and `direct_compiled_agree hsurface hchecked` proves exact framework equality: `directAF hsurface = Compile.checkedAF checked.program`. The public observation theorem is parametric over attack-extensional extension semantics:

```lean
theorem observe_coherent
    (sem : Semantics.ExtensionSemantics)
    (hext : Observation.AttackExtensional sem.spec)
    (hsurface : Checks env input output)
    (hchecked :
      Check.Unit.checkUnit output.gamma env.registry output.ground output.unit =
        .ok checked)
    (claimId : Presentation.PropId) :
  Surface.observe sem hsurface claimId =
    (coreClaim? output checked claimId).map
      (Semantics.observe sem (Compile.checkedAF checked.program))
```

The named corollaries instantiate grounded, complete, preferred, stable, and semi-stable semantics and discharge the corresponding `AttackExtensional` premise internally; callers supply only the surface and core acceptance data and the claim ID. The stable corollary preserves `noExtension`; it does not collapse nonexistence into a local claim status. Grounded coherence uses `Observation.attackExtensional_leastComplete`, because grounded semantics is represented by the least complete extension specification. All six coherence results preserve lookup absence as `none` as well as comparing present claims.

### Load-bearing counterexamples

The following checked witnesses target distinct hypotheses rather than merely showing generic rejection:

| Dropped hypothesis | Mechanized witness | Observed consequence |
| --- | --- | --- |
| Generated comparison IDs are fresh | `Examples.Surface.necessity_generated_ids_fresh` | The later colliding comparison returns `invalidComparison`. |
| Premise resolution is unambiguous and earlier-only | Executable example beside `inferredArgsWellFormedB_iff` | Two prior rows with one authored reference make `inferredArgsWellFormedB = false`. |
| Named binders are capture-free | Executable captured-binder and naive-core-bypass examples | The surface checker rejects the captured binder even though a naive lowered core bypass is accepted. |
| Comparison polarity matches the scheme | Executable example beside `comparisonsWellFormedB_iff` | A higher-is-better scheme with a lower-is-better measurand returns `invalidComparison`. |
| Argument IDs are unique before attack indexing | Executable duplicate-ID example | Duplicating the attacked source argument returns `duplicateArgId`. |
| A declared support role matches its claim | Executable conclusion-mismatch example beside `checkAuthoredConclusion_sound` | A `supports(c)` argument with a non-equivalent conclusion returns `conclusionMismatch`. |
| Challenge targets are declared | Executable undeclared-challenge example | A challenge naming an absent argument returns `challengeTargetUndeclared`. |
| Requested statuses name declared claims | Executable unknown-status example beside `resolveStatuses_sound` | An unknown status ID returns `unknownStatusClaim` before core assembly. |
| Group declarations match production invariants | Executable duplicate-ID, duplicate-member, singleton, and undeclared-member examples beside `validateGroups_sound` | Duplicate IDs and members, cardinality below two, and undeclared leaf members return their distinct group errors. |
| Production precedence is compositional | Executable first-repeat and certificate-precedence examples plus the strengthened conclusion and group conformance fixtures | Endpoints precede groups; groups precede the argument fold; certificate lowering precedes the same argument's role; roles precede attack paths; group payloads use first-repeat order. |
| The lowered unit passes the core checker | Executable invalid-core-support examples beside `CoreObligations.checkUnit_complete` | `supportedB` remains true and pure elaboration succeeds, while `check` rejects the unsupported core unit. |
| Direct claim support is carrier-local | `Surface.not_observe_coherent_of_unbounded_support` | Two frameworks that agree on their retained carrier can yield different observations for junk support outside it. |
| Missing claims remain absent | Executable example beside `directClaim_eq_coreClaim?` | Independent direct and core lookup and optional direct observation all return `none`. |

The supported-fragment decider also has isolated boundary fixtures: `duplicateArgument_unsupported`, `premiseQuestionCollision_unsupported`, `unknownValueInterpolation_unsupported`, `missingComparisonScheme_unsupported`, `laterArgumentReference_unsupported`, `ambiguousNamedCertificate_unsupported`, and `unresolvedAttackPath_unsupported`, each proving a distinct malformed input has `supportedB = false`.

### Cross-language conformance provenance

`fixtures/surface/MANIFEST.tsv` is the ordered provenance source. It contains 25 cases: the all-forms acceptor, rule- and natural-deduction-alpha pairs, focused comparison, cell interpolation, named premise and formula cases, eleven named structural rejections, an admission-pruned open-obligation case, and accepted fixtures that force `gap`, `defeated`, `contested`, and stable `noExtension`. Its closed feature vocabulary covers labelled premises, named discharges, comparisons, both interpolation forms, named certificates and formulas, both binder classes, all surface attacks, capture, ambiguity, comparison and attack-path rejection, role and challenge rejection, status rejection, all four group guards, admission pruning, and an open obligation. The manifest is complete with respect to that closed required-feature vocabulary, not with respect to the parser or AST input space, and the 25 fixtures are representative finite exercised production behavior, not a parser-correctness proof or exhaustive coverage.

The two emitters are independent. Haskell parses the concrete files through the production parser and runs the production `prepareSource` and `runSourceCheck` path; Lean constructs matching `Presentation.Program` and `Policy` values directly and runs the verified surface checker, elaborator, and observation functions. Each emits the same eight-column canonical table (`case_id`, `ast_fingerprint`, `outcome`, `core_fingerprint`, `authored_open`, `located_holes`, `attacks`, `observations`). The `authored_open` column has retained, post-admission semantics: it walks every authored open question of retained `output.unit.args` recursively, in retained argument order and term order, mandatory and optional alike, and renders `arg-id:question-id`; it is deliberately not the pre-prune `output.authoredObligations` ledger used by `obligations_preserved`, and the real `admission-prune-accept` row proves the distinction, since the quarantined argument is removed while the retained open argument emits exactly `arg-open:cq`. The `located_holes` column is the accepted unit's located holes in retained declaration order, one `arg-id:question-id` atom per exact mandatory obligation in the core's deduplicated order; in `admission-prune-accept` the open `cq` is optional, so `authored_open` is `arg-open:cq` while `located_holes` is empty. The AST fingerprint prevents output agreement over different inputs. The gate `scripts/check-surface-conformance.sh` rejects an empty or malformed manifest, unknown or uncovered features, empty outputs, missing, extra, or reordered case IDs, disagreement between either emitter and `test/surface-conformance.golden`, or disagreement between the emitters during an update, and `scripts/check-presentation-parity.sh` separately checks the full AST shape inventory.

### Exclusions and the evaluation contract

The surface calculus does not prove concrete parser correctness, since no theorem starts from `.lara` bytes or relates the Haskell parser to `Presentation.Program` and `Policy`. It does not prove surjectivity onto the core, since there is no theorem saying every accepted `Lara.Unit` or checked core program has a surface preimage. It does not prove injectivity or unique recovery, since value expansion, generated comparisons, binder alpha-equivalence, admission pruning, and erased authored names can map distinct surface inputs to the same core result, and no unique source recovery theorem is stated. It does not prove unconditional elaboration soundness, since a successful pure `elaborate` call alone does not imply `Checks`; reflection also requires `Supported` and a successful `checkUnit`. It does not derive Haskell correctness from Lean alone, since Lean proves the model and the shared table and Haskell tests provide finite conformance evidence. It does not prove diagnostic or byte preservation beyond the stated gates, since error-message text, parser locations, comments, and whitespace are outside the theorem.

The paper may claim verified full-structured-AST elaboration for the exact supported fragment; an independent syntax-directed surface judgment with a sound, complete, and deterministic executable checker; preservation from a surface derivation to pure lowering and actual core acceptance; supported-fragment reflection from canonical lowering plus actual core acceptance back to the independent surface judgment; exact preservation of authored obligations, retained attacks, reconstructed conclusions, and authored and core argument-question order in the forms stated above; production-ordered validation of authored roles, requested status IDs, and group IDs and members, with requested statuses rather than all declared claims feeding the finite core-check ground; genuine-binder alpha-lowering invariance and typed global-renaming equivariance under their explicit soundness hypotheses; and optional, independently defined direct and core claim lookup and direct and compiled observation coherence for extension semantics satisfying `Observation.AttackExtensional sem.spec`, with named grounded, complete, preferred, stable, and semi-stable corollaries that discharge that premise and preserve missing claims as `none`.

The paper must not claim verified correctness of the concrete `.lara` parser; that every accepted core program has a source preimage; that a source preimage is unique or recoverable; that `elaborate ok` alone implies surface validity; that replay-significant identities are alpha-renamable; or that Haskell correctness follows from the Lean proof alone.

The layer succeeds only when all three evidence layers pass, and no layer substitutes for another. Formal evidence requires the theorem-bearing modules to build and the axiom audit to report the public theorem families without proof holes or dependencies beyond `propext`, `Classical.choice`, and `Quot.sound`, which establishes the surface model's formal contracts and not properties of the shipped Haskell implementation. Cross-language conformance evidence requires the independent Haskell production-path emitter and the Lean verified-model emitter to produce the same nonempty, ordered canonical rows for the finite manifest, including AST fingerprints, outcomes, core images, authored open questions, located holes, attacks, and observations, which connects the model to exercised shipped behavior and remains finite conformance evidence rather than parser or Haskell correctness. Regression evidence requires the pre-existing core bytes, verdicts, differential anchors, semantics and backend goldens, and generated core artifacts to remain unchanged, with the surface fixtures and their own eight-column golden intentionally advancing together and the adapted before-and-after patch comparison proving their generators introduce no further drift. Lean proof without cross-language evidence does not validate the shipped path; matching emitters without the independent surface theorems remain testing; and both are insufficient if the established core bytes, verdicts, or artifacts drift.

## Holes: located gaps and term-level critical questions

An *argument* is a declared support term for a claim. A defeasible step must answer each of its rule's *critical questions*, either by discharging it with evidence or by leaving it explicitly *open*. An open mandatory question is an unresolved obligation. Up to `lara-core@0.2` a unit containing an argument with an unresolved obligation was rejected whole; an author who could not answer a question had to delete the argument, and the verdict then said only that the claim had no support. The `lara-core@0.3` contract makes the checker accept such a unit and report the incomplete argument, with the questions it leaves open, as a *located gap*. `docs/spec.md` §4.3, §4.4, §8, §10, and §10.1 state the normative rules; this section keeps the reasons and the rejected alternatives.

### The judgment and the declaration partition

A **hole** is a declared argument that type-checks under spec §6.1 with a nonempty root obligation set:

```text
Sigma; Pi; Gamma; R |- a : supports(p_a) ▷ O      O ≠ ∅
```

`O` is the mandatory, transitive set: it contains every mandatory question left open in `a` itself or in any premise or discharge subterm, because spec §6.1 unions obligations upward (`collectObligations` in `lean/Lara/Support.lean`). An open optional question contributes no obligation and never makes a hole. A term whose support inference fails is not a hole; it is a rejection.

Two older uses of "hole" are different notions. The open set `H` of a rule instance (spec §6.1, spelled `open q`) lists the questions that instance leaves open, optional ones included; a located hole is a whole declared argument, and it may contain no `open` of its own when its obligation comes from a subterm. The template holes of `Lara.Context.Holes` are answer positions that a context fills, and they never reach this judgment.

An accepted unit's checked declarations split once into two disjoint lists:

```text
Args(P)  = { a declared | |- a : supports(p_a) ▷ ∅ }         -- complete: framework nodes
Holes(P) = { a declared | |- a : supports(p_a) ▷ O, O ≠ ∅ }  -- located gaps
```

The two lists cover every checked declaration, keep declaration order, and keep the conclusion and obligation set the support stage cached. Compilation and reporting read that cache; neither re-runs support inference.

Everything that rejected a unit before program checking is unchanged: codec and replay errors, source and admission rejections, `duplicate-rule`, R2, and R12. Within program checking, in the fixed stage order of spec §8.2, a unit is accepted if and only if no two declared arguments are equal; every declared argument type-checks under spec §6.1, complete or hole, with every R-class of that judgment, R5 question accounting included, still rejecting; every declared attack type-checks under spec §7.1, whatever its source and target are; and every conflict that the policy's contraries license between two complete arguments is covered by an attack whose source is complete (`missing-conflict` otherwise). The only change is that a nonempty root obligation set no longer fails the second step.

Only complete arguments become framework nodes. An attack produces closure edges only when its source is complete, and then onto every complete argument that contains the attacked occurrence (spec §8). Claim status is unchanged in form: a claim with empty complete support is `gap`, and a claim with complete support takes its status from the labels, with any holes concluding the same proposition reported beside it as incomplete alternatives.

### Core contract decisions

These are the `lara-core@0.3` contract decisions, kept as the record of the reasons and the alternatives. Their numbers are stable identifiers cited from other documents.

- D1, `lara-core@0.3`, hard cutover. The replay identity's core component becomes `lara-core@0.3`, the decoder accepts exactly that version and refuses `lara-core@0.2` inputs as an R14 codec error, as `@0.2` refused `@0.1`. A unit none of whose declared arguments is a hole, retained or quarantined, gets the same labels, edges, and statuses under `@0.3`, and only the core version component of its verdict changes. A unit accepted under `@0.2` has no retained hole but may have quarantined one; `@0.2` counted such a hole as a node of the conservative-reporting reference framework, and `@0.3` does not (D7), so its outgoing attacks no longer cause `evidence-blocked`, while labels and edges are unchanged. The version moves in the same change as the driver and wire work, before the committed fixtures are regenerated.
- D2, an optional `holes` section, not a status. An accepted verdict gains an optional, nonempty `(holes ...)` section after `conditional`. A hole is neither a fifth core status, nor a public status, nor a framework label. `gap` keeps the meaning it always had: no complete support.
- D3, retire `incomplete-argument`. The named rejection kind, its error constructors in both runtimes, its wire tag, its renderers, and its mutation expectations are removed. R5 question accounting is unchanged: a declared question in neither the discharge map nor the open set `H`, or a discharge or an `open` naming an undeclared question, still rejects.
- D4, attacks sourced at a hole are checked, then inert. A declared attack whose source is a hole must still type under spec §7.1; an ill-typed one rejects the unit with its R-class, as before. A well-typed one contributes no framework edge, and the hole's report lists it by its original attack declaration index.
- D5, three index spaces with explicit maps. Holes are reported by original declaration index, `ArgId`, and exact mandatory root obligations. Labels, edges, and complete support use compact framework indices.
- D6, attacks targeting a hole are kept. An attack from a complete source onto an occurrence inside a hole is not discarded. If the attacked occurrence is a complete subterm that also occurs in a complete argument, the closure edge onto that complete argument is produced. A rebut of the hole's root adds no edge onto a complete wrapper of it, because a wrapper inherits the hole's mandatory obligations and is therefore itself a hole.
- D7, conservative reporting compares against complete declared arguments. The reference framework of spec §4.3 excludes typed holes. It keeps quarantined declarations whose support inference fails under the full declared Γ as conservative nodes. The checked framework holds only the retained complete nodes. Raw declared attacks and their endpoint alignment are kept.
- D8, the surface classifies by the core obligation set. A `.lara` argument is a hole exactly when its core obligation set is nonempty, mandatory, and transitive. Questions authored at an argument's root, optional ones included, remain separate diagnostic data and do not decide hole-hood. A surface claim selects its alternatives, holes as well as complete support, by authored claim id; outside the derived-support role a selected hole always concludes the claim's formal, but where claims share an equivalent formal the id selection can miss alternatives that the core's conclusion-equivalence selection includes.
- D9, composition results cover holes. Linking, composition, and contextual-equivalence results are stated over `SideOkHoles` (`lean/Lara/Context/Link.lean`, issue #13): each declared argument of a side must type, as a complete argument or as a hole. The hole-free `SideOk` theorems (`link_checked`, `link_accepted_raw`, `batch_checked`, `linkedUnitOf_checked`) are now corollaries. `link_checked_holes` accepts the link, and `link_accepted_holes` (`lean/Lara/Context/LinkHoles.lean`) says what the accepted link is: its framework arguments are the sides' merged complete arguments, its holes are the sides' merged holes, and its compiled attacks are each side's live attacks followed by the saturation. `link_classify`, `link_hole_report`, and `link_side_hole_reported` show that a declaration keeps its side's classification, conclusion, and obligation set. `link_hole_source_inert` (D4) and `link_shared_occurrence_edge` (D6) carry the attack rules through the link, and `crossAtts_endpoints_complete` says the saturation never touches a hole. `Admissible` now takes `SideOkHoles` sides, so every congruence stated over it covers fragments and contexts with holes, including backend replacement, registry swap, relational parametricity, and `surface_directAF_link`. `obsGen_hole_blind` bounds what holes can change, and its live-attack premise is needed, because deleting a hole together with an attack aimed inside it can remove the only cover of a conflict, so the link is rejected (`Lara.Examples.LinkHoles.hole_erasure_observable`). The map layer has matching statements (`batch_checked_holes`, `batch_hole_report`, `linkedUnitOf_hole_report`). General acceptance and arbitrary-obligation transport are preserved. Possible-world status results remain about complete support and do not claim a correspondence between hole reports. The hole term ledger is part of the duplicate-world identity in both runtimes, so two worlds that differ only in their holes are not merged.
- D10, no separate surface rejection or warning for holes. After admission the surface and the core report the same incomplete alternatives, and the surface's existing diagnostics for authored questions are unchanged and stay distinct.
- D11, completion is additive, in place, or atomic. An author completes a gap by adding fresh admitted leaves and a distinct complete term under a fresh id, by discharging the hole's open question under its own id (`dischargeOpen`, D13), or by applying leaves, instances, or discharges and the attacks they need as one batch admitted and checked once (`atomic`, D14). The individually rechecked additive sequence is not universally accepted: the new complete term goes through ordinary attack-completeness checking, so if it licenses an outgoing conflict with no covering attack, `addInstance` can reject before a later `addAttack` could supply the cover, and the atomic batch closes that gap. Updates are source-level and not on the verdict wire, so none of this changes the core contract.
- D12, each obligation is located at its rule occurrences (issue #16). A hole row reports every root obligation together with its *sites*: the positions, inside the hole's own support term, of the rule instances that leave the question open with the question mandatory for their rule. These are exactly the occurrences that contribute the question to the root obligation set, so an obligation inherited through a premise or a discharge points at the step that needs the answer instead of at the wrapper argument. The row becomes `(obligation ID POS+)` inside `obligations`; `POS` is the attack position encoding of spec §7, relative to the hole's root term. There is no version bump, because `lara-core@0.3` had not shipped, so the `@0.3` hole row is amended in place rather than moved to a new core version or given an additive optional field; a consumer that read the bare-id `@0.3` rows from a development build fails to decode the new rows rather than misreading them. The obligation list keeps exactly the content and order it had, the core's deduplicated union order, and a row's sites follow the traversal `collectObligations` uses (premise subterms in index order, then discharge subterms in discharge-map order, then the instance itself, post-order) and are distinct. Sites are read off the checked hole's term and the rule lookup (`Lara.Check.openSites`, Haskell `Lara.SupportTerm.openSites`), and no driver re-runs support inference for them. `lean/Lara/Check/HoleSites.lean` proves soundness (`openSites_sound`: every site is a rule occurrence leaving the question open, mandatory for its rule), completeness (`openSites_complete`, with no typing premise), that the questions with a site are exactly the root obligations (`mem_obligations_iff_sites`), and that no site repeats under typing (`openSites_nodup`, `sitesFor_nodup`); `obligationSites_adequate` packages these per row and `Lara.Driver.holeRows_obligations` ties every emitted row to them. The map layer is unchanged: `map-verdict@2` hole rows stay `(hole ALIAS ARG-ID (obligations ID+))`, and sites are reported by the core verdict only, so a map consumer that needs them runs the member's unit through the core driver. On the `.lara` path a site is a core position relative to the lowered term, the same convention as attack positions, and the surface's own diagnostics and conformance contract are unchanged.

The two completion decisions are source-update decisions and are not on the verdict wire, so neither changes `lara-core@0.3`, the replay identity, any committed verdict, or the evaluation freeze.

- D13, discharge a located hole in place (`dischargeOpen`, issue #14). `dischargeOpen name π q v` answers the open question `q` of the rule occurrence at position `π` (spec §7, `π ::= ε | π.i | π.q`) inside the declared argument `name`, with the discharge term `v`. Its precondition (`DischargeOpen`, decided by `dischargeOpenB`) is syntactic: the name resolves, through the first-match lookup raw attack endpoints use, to a term whose occurrence at `π` is a rule instance with `q` in its open set `H`; whether `v` answers `q`'s pattern, and whether the result is typed, are left to the checker, as for every other update. Its effect is that at that occurrence `q` leaves `H` and `(q, v)` is appended to the discharge map (`Discharge.dischargeAt`); the row keeps its name and declaration index, the raw attacks are untouched, and admission and `checkUnit` then rerun on the edited source. Appending is forced because `lookupDis` reads the first matching entry, so appending leaves every discharge lookup that succeeded before unchanged, every position that was defined in the old term stays defined and addresses an occurrence of the same kind (the same leaf, or the same rule and substitution), and off the root-to-`π` path it is the identical subterm (`subterm_dischargeAt_old`); on a typed term `q` had no discharge (`D ⊎ H` is a partition), so `π.q` is a new position and addresses `v` (`subterm_dischargeAt_new`), and raw attack identities and endpoint alignment are preserved (`resolveAttacks_dischargeRows`, `dischargeOpen_resolved`). The metatheory: the conclusion is unchanged (`dischargeAt_conclusion`); the rewritten term types whenever the old one did and `v` answers the question (`dischargeAt_hasSupport`); its obligations are exactly the old open mandatory questions away from `π`, those still open at `π`, and `v`'s obligations (`dischargeAt_obligations_iff`, built on `mem_obligations_iff`); discharging the only open mandatory question at its only open occurrence with a complete term yields a complete term (`dischargeAt_complete`); every hole and complete argument other than the discharged one persists in both directions (`dischargeOpen_others_persist`); and a retained hole discharged to completion by a term that uses no quarantined leaf becomes a framework node, leaves the hole report under both its old and its new term, and moves every claim equivalent to its conclusion out of `gap` under every extension semantics (`dischargeOpen_hole_becomes_node`). The restricted transitions and their counterexamples are recorded in the source-updates section: no status matrix and no unrestricted transition theorem, an optional-question discharge can move a node into `gap` (`Examples.UpdateCompletion.discharge_optional_enters_gap`), a raw attack declared while its source was a hole fires once the discharge completes it (`discharge_outgoing_defeats`), and even a hole-to-hole discharge can change an edge when an attack from a complete source targets a position on the root-to-`π` path, a case the no-attack premise excludes with no separate witness pinned.
- D14, atomic multi-edit completion (`atomic`, issue #11). `atomic edits` applies a list of raw edits (`addLeaf`, `addInstance`, `addAttack`, and `dischargeOpen`; `AtomicEdit` is a separate type so a batch cannot nest) in order, then runs admission and `checkUnit` exactly once on the final raw state. Per-edit checks: each edit's syntactic side condition is checked against the state the earlier edits produced, so an attack may name an instance added earlier in the same batch but not a later one, and the first failing edit rejects the batch with `batchEdit index reason`. All or nothing: the batch is accepted exactly when its raw edits apply and the final raw state is `Accepted`, and it then returns that state (`applyUpdate_atomic_ok_iff`); a rejected batch returns no state and the caller keeps the source (`applyOrKeep`, `atomic_partial_rejected`). Completeness of completion: if the program obtained by adding fresh leaves, fresh instances (or an in-place discharge) and the attacks they need is accepted, the corresponding batch is accepted and yields exactly that program (`atomic_completion_complete`, `atomic_discharge_completion_complete`), and no intermediate state is checked, which is what the sequential route lacks. Identities: every successful batch keeps every raw attack and every argument name at its declaration index; a batch without discharge keeps every argument row (`applyBatchFrom_prefix`), and whether or not its new leaves are admitted, keeps the source's complete arguments and reported holes as prefixes of the target's (`atomic_additive_checked_prefix`, `atomic_additive_checked_split`); a quarantined new leaf prunes only new rows (`atomic_additive_kept`), and a pruned row is never a framework argument or a reported hole (`AcceptedRun.pruned_not_reported`). Transitions: over a batch without discharge the per-constructor results compose as recorded in the source-updates section, and `tighten` is excluded because tightening never completes a gap, which keeps every batch without discharge inside the additive metatheory.

The Haskell mirror (`src/Lara/Update.hs`) carries both constructors, the site decider, the rewrite, and the raw stage of a batch, and `make update-differential` diffs them exhaustively against Lean. Batch acceptance is Lean-only, like `applyUpdate`.

### Index convention

Three index spaces appear in verdicts and their reports:

| Space | Ranges over | Used by |
| --- | --- | --- |
| original declaration index | the supplied unit's argument (or attack) declarations, before admission | hole rows, hole attack lists |
| checked (local) declaration index | the post-admission unit `checkUnit` checks | rejection constituents, as today |
| framework index | the complete nodes of the checked unit, in declaration order | `labels`, `edges`, complete support |

Positions computed by the core are local to the exact post-admission unit it checked. The maps between the spaces are admission's retained-argument map (checked declaration to original declaration) and retained-attack map (checked attack to original attack), reused unchanged, plus one new map, complete node to checked declaration, produced by the declaration partition. The driver composes these to report each hole at its original position. With no quarantine the first two maps are identities; with no holes the third is. Rejection constituents keep their existing local declaration ids, and framework label ids are a separate numbering never used to address a declaration.

On the raw `.sexp` path, "original" means the order of the `args` and `attacks` sections of the supplied unit. On the `.lara` path it means the expanded and lowered declaration ledger before admission. Arguments the elaborator generates carry authored-or-generated provenance and are never presented as authored `.lara` declaration positions. A quarantined declaration stays in the admission audit and is absent from the accepted hole report, whether or not it would have been a hole.

### Wire: the holes section

The accepted verdict grammar becomes:

```text
VERDICT ::= (verdict REPLAY-ID accept
              (labels (NAT LABEL)*)
              (edges (NAT NAT)*)
              (statuses (status ATOM STATUS)*)
              CONDITIONAL-SEC? HOLES-SEC?)
HOLES-SEC ::= (holes HOLE+)
HOLE ::= (arg NAT ID (obligations OBL+) (attacks NAT*))
OBL  ::= (obligation ID POS+)
POS  ::= (pos ((prem NAT) | (ques ID))*)
```

The hole's `NAT` is its original argument declaration index and `ID` is its `ArgId`. `obligations` lists the hole's exact mandatory root obligations, in the core's deterministic deduplicated union order, which is the order `collectObligations` builds: premise obligations, then discharge obligations, then the instance's own open mandatory questions, each question kept at its last occurrence. Each `OBL` names one obligation and its sites (D12): every position, relative to the hole's root term and in the attack position encoding of spec §7, of a rule instance that leaves the question open with the question mandatory for its rule; `(pos)` is the hole's root, and sites follow the `collectObligations` traversal and are distinct. `attacks` lists the original declaration indices of the surviving, successfully typed raw attacks whose source is this hole; it uses raw endpoint alignment and is taken before live-source filtering, and an empty `(attacks)` is canonical. Holes appear in original argument order, every surviving hole is emitted even when no query names its conclusion, and identifiers use the existing atom printer including quoting and Unicode. The section is omitted when there are no holes, so a verdict for a unit with no hole among its declarations is byte-identical to its `@0.2` form apart from the core version. A claim report selects its incomplete alternatives by conclusion equivalence, and that selection does not change the global hole list.

A standalone verdict decoder checks row shape, canonical naturals, nonempty obligation lists, unique obligation ids within a row, a nonempty site list per obligation, no repeated site within an obligation, unique hole indices, unique hole ids, and the fixed section order. It does not bound hole indices by the number of framework labels, because a hole index is a declaration position, not a node. Agreement between a hole's index and its id, and validity of its attack references, depend on the supplied input and its admission maps, so only a decoder that holds the input can check them.

The map layer (`map-verdict@2`) is unchanged in shape. A multi-artifact map (spec §12) links its members into one unit and runs the ordinary checker on it, so a member's hole is a hole of the linked unit and the map accepts it. `nodes`, `labels`, and `edges` share the framework index space, and a node's index is reached through the checked unit's framework-to-declaration map, never the linked declaration position. An optional, nonempty trailing `(holes (hole ALIAS ARG-ID (obligations ID+))+)` section reports every handle whose linked argument is a hole, by member alias and member-local argument id, with the exact obligations in core order, in the same member-then-declaration order as `nodes`; it carries no index, no attack list, and no obligation sites (D12). The cross-member saturation generates no attack sourced at or aimed at a hole (D4, D6), as `Lara.Map.crossPairs_endpoints_complete` states, and `batch_generated_live` ties it to the accepted linked unit. The map driver's acceptance of linked units with holes is covered by the hole-aware linking results of D9.

### Conservative reporting with holes

Spec §4.3 publishes `evidence-blocked` for a queried claim whose complete support could have been changed by quarantine. With holes the two frameworks of that rule are fixed as follows, all in original declaration index space.

The reference carrier `D` is the original declarations classified, under the full declared Γ, as either complete or *unclassified*. A declaration is unclassified when its support inference fails, as happens to a quarantined declaration with a missing leaf or rule or an invalid assurance. Typed holes are excluded. Retained declarations reuse the checked cache, because the checked Γ agrees with the declared one on every leaf a retained term uses, so their classification is already known, and each quarantined declaration is inferred at most once for this classification. No Γ-independent structural classifier is introduced. The checked carrier `K` is the retained complete declarations, so `K ⊆ D`. Framework `G` has carrier `D` and the closure edges of the raw declared attacks between members of `D`; framework `F` has carrier `K` and the closure edges of the retained attacks between members of `K`. The seed and blocked set are:

```text
seed = (D \ K) ∪ { j ∈ K | ∃ i ∈ K. G.attack i j ∧ ¬ F.attack i j }
B    = forward closure of seed along G's edges, over D only
```

A queried claim with a complete retained support argument in `B` reports `evidence-blocked`, and its four-state label moves to `conditional` as before.

Three consequences are stated as acceptance cases. Holes and the attacks they source can neither seed nor propagate blocking, because holes are not in `D` and their attacks have no edge in `G`. An attack from a retained complete source onto an occurrence inside a hole, dropped because quarantine removed the hole, can still seed a retained complete argument that contains the same occurrence, because `G` has that closure edge and `F` lost it. Quarantining a hole alone, when no such dropped closure edge exists, blocks nothing. An unclassified quarantined term stays a node even when it has a raw outgoing attack onto complete support, which keeps the conservative block, and the term is never reported as a typed hole. The stronger statement that `D` is exactly the complete declared arguments holds only under a full-declared support-typing premise, and is proved only under it. The nonpromotion theorem keeps its shape: a publicly `justified` claim is `justified` in `G`, and the fast path where nothing is quarantined still blocks nothing, so a clean unit with holes never reports `evidence-blocked`.

### Term-level critical-question holes

The fragment calculus resolves imported leaf names by extending Γ. That alone cannot discharge a critical question, because its answer is a support term inside an instance's discharge map. The additive `Lara.Context.Holes` calculus represents those answer positions explicitly, substitutes context-supplied terms, and then uses the existing checked linker and observations.

A template is either an embedded core `SupportTerm` or a rule instance with recursive premise and answer templates. An answer is a template or a named `HoleId`. Hole identifiers and local `QuestionId`s are different types: two nested instances can ask the same question while requiring different answers from their context, sharing a hole identifier is intentional sharing, and typing requires its demanded answers to agree through the declared hole signature. A filling table is a finite list of hole identifiers and core support terms; holes may occur arbitrarily deeply in the template, and filling values do not contain new named template holes, so substitution does not recursively chase environment bindings or require a cycle policy. This is a finite critical-question-substitution calculus, not a recursive module system or arbitrary missing-premise calculus.

Existing core terms embed unchanged, including their ordinary optional questions. A named template hole is an explicit obligation of this interface, and an old `H` entry is not automatically promoted to one. The frozen `SupportTerm`, checker, four-state observation, and `Grounded.Claim.holes` behavior are unchanged.

`eraseOpen` removes unanswered named-hole entries from the discharge map and adds their question keys to `H`, so it yields a real source support term and not just a diagnostic list; the source-erasure typing theorem derives its `HasSupport` judgment, and mandatory questions can make its obligation list nonempty. Template typing is independent of any actual filling: it checks the original rule lookup, instantiation, premise types, question partition, assurance, and answer pattern obligations, `InstMeta` factors the original `InstSide` premises through argument counts and discharge keys, conversion to the existing judgment is proved, and a named hole receives its demanded answer through the hole signature. Typed fillings supply independently derived complete support, with conclusions equivalent to the demanded answer atoms; typed substitution derives support of the resulting term with the same root conclusion and residual obligations, and the conclusion is not an assumption hidden in a template-validity predicate. When the template's residual obligations are empty, the substituted term is complete and can cross the existing compilation boundary. Partial substitution preserves unresolved holes, final instantiation rejects a duplicate filling identifier or a missing hole, instantiation is structural, and the old checker supplies the detailed rejection for a supplied term that fails to answer the question or otherwise fails typing.

Hole fragments carry template arguments and template attacks, and instantiation substitutes both source and target endpoints, including nested question-answer subterms, before calling the existing linker. Hole contexts carry an old context frame plus their filling table, and observations retain hole-instantiation failures separately from the old incompatible, rejected, and observed outcomes. Substitution can identify distinct templates, so no theorem assumes it is injective to transport `Nodup`; the existing linker deduplicates the instantiated argument lists. Filling can also introduce new subarguments and attack targets, so open-term attack coverage is not claimed to imply closed-term coverage, and link acceptance and attack completeness keep the explicit post-substitution attack conditions of the old `SideOk` boundary, with their support premises derived from typed substitution.

Disjoint filling tables compose by concatenation, with duplicate identifiers rejected; partial substitution agrees with sequential substitution under the stated domain condition; and context frame composition retains the original calculus's compatibility and coverage hypotheses, so adding holes does not make arbitrary contexts composable. Closed embeddings recover the existing observations, and contextual equivalence quantifies over hole contexts, with its closed-fragment specialization recovering the old relation, including shared instantiation failures. Backend replacement passes through instantiation before invoking the existing contextual congruence, and fixing a hole context requires fixing certificates in its fillings as well as its frame, because those terms become part of the substituted fragment. Relational transport likewise requires self-related context fillings and retains `RelInj`, and semantics-parametric observation transport uses the same compiled-carrier argument as the context calculus; this extension does not assert full abstraction.

The theorem map, all names under `Lara.Context.Holes` unless stated otherwise:

| Obligation | Declarations |
|---|---|
| Independent rule metadata | `InstMeta.toInstSide`, `InstMeta.ofInstSide`, `InstMeta.answers_equiv` |
| Supported source and filled term | `eraseOpen_hasSupport`, `instantiate_hasSupport` |
| Structural composition and guard | `subst_append`, `fillingNodup_append`, `instantiateFragment_subst` |
| Old calculus recovered | `obs_closed`, `obsSem_closed`, `ctxEquiv_closed_iff`, `ctxEquivSem_closed_iff` |
| Checked instantiated link | `instantiated_support`, `sideOk_of_typed`, `link_attackComplete`, `link_checked` |
| Context composition | `compose_assoc_defined`, `composed_frame_material_assoc`, `composed_filling_assoc` |
| Backend transport | `instantiate_map`, `instantiateAux_rel`, `backend_replacement_congruence_sem`, `backend_replacement_parametricity_sem` |

Context association has the original calculus's scope: both guarded bracketings are defined under pairwise compatibility and disjointness, frame material agrees extensionally, and filling concatenation agrees exactly, while raw context-record equality additionally requires equality of the old composed frame records.

`Lara.Examples.TermHoles` supplies the nested repeated-question-name example, source obligations, typed closure, checked acceptance, rejection cases, composition, and substituted attack endpoint, and every public theorem is covered by `AxCheck`. The positive `functional_transport_sem` and `relational_transport_sem` fixtures apply the actual new wrappers to the nested template and its attack, at arbitrary semantics and across the wrapped registry; their material has only leaf and `none` assurances, so no certificate moves in that positive instance. Separately, `certificate_context_not_fixed` uses an independently typed certified filling: the old frame is fixed by the relabel, but the filling is not, which makes the extra context-fixing condition substantive. This closes the term-level critical-question-hole obligation retained from the update work. It changes no Haskell code, corpus vector, or freeze tag, and the original contextual theorems remain available, with the new layer proving the substitution bridges that make them applicable to instantiated fragments.

### Rejected alternatives

**Keep rejecting, the `@0.2` contract.** Rejection was a v0.1 scope decision, not a soundness requirement (see `docs/evidence-admission-design.md`, "Alternatives considered"). It forced an honest author to delete the argument, so the verdict could say a claim had no support but not which question was missing, and it also let the earliest incomplete argument mask any later support or attack defect in the same unit. The status function of spec §8 was already stated over holes, and `statusC` already yields `gap` exactly on empty complete support (`statusC_gap_iff` in `lean/Lara/Grounded.lean`), so accepting holes needs no new status.

**Drop attacks that target a hole.** This would discard a typed attack on a complete subterm merely because the subterm also occurs inside a hole, and lose the closure edge onto complete arguments that share it. Spec §8 closes attacks under subarguments for exactly this case.

**Make holes nodes of the nonpromotion reference framework.** Counterexample: let claim `c` have one complete support `a`, and let an unattacked hole `h` carry a typed attack onto `a`. In the checked framework the attack is inert (D4), so `a` is `in` and `c` is `justified`; in a reference framework with `h` as a node, `h` is `in`, `a` is `out`, and `c` is `defeated`. Nonpromotion would then fail on a unit with nothing quarantined, or would require blocking `c` and so make a clean unit report `evidence-blocked`. Holes are not nodes of any accepted framework, so they are not nodes of the reference framework.

**Treat inference failure as incompleteness.** The prototype classified any term whose inference failed as a hole. On the retained core path such a term is a rejection, and reporting it as a hole would accept ill-typed arguments. Only on the quarantined side, where no rejection is possible, are such terms kept, and there they are conservative nodes, never holes.

**Re-infer completeness while compiling.** Recomputing completeness with support inference duplicated the checker's work and made kernel-evaluated examples time out, so the partition is taken once from the checked cache.

**Report a hole as a status or a label.** A fifth status would change the four-state vocabulary, and a label would put a non-node into the framework. The located report is diagnostic data beside the unchanged status.

**Nest `SourceUpdate` inside `atomic`.** A nested inductive allows batches of batches and complicates every induction for no expressive gain.

**Check every intermediate state of a batch.** That is the sequential route again, and it fails on the same counterexample.

**Delete the hole and re-add the completed term under the same id.** There is no removal update, and a delete-then-add sequence passes through a state in which the attacks naming the id do not resolve. Rewriting the row in place keeps the id, the index, and every raw attack.

**Prepend the discharge, or keep the discharge map sorted.** On an ill-formed raw term either can shadow an earlier entry with the same key and move an existing position. Appending provably preserves every old position.

### Non-goals and cost

The follow-ups this contract first deferred have landed with it. Hole rows locate each open obligation at its rule occurrences (D12, issue #16), though the map layer still reports obligations without sites. Linking and composition cover units with holes (D9, issue #13). In-place discharge (issue #14) and atomic multi-edit completion (issue #11) are source updates. The frozen `corpus-units` declare their incomplete arguments as located holes (`corpus-units/LOWERING.md`, issue #15).

The version bump changes every committed verdict and check-input byte that carries the replay identity. The cutover therefore regenerates the mutation suite, corpus fixtures, worked examples, and freeze bundles, and cuts a new evaluation freeze with a full axis-(c) re-run. The update golden prints the completion witnesses and counterexamples (`Examples.UpdateCompletion.completionWitnessReport`); no transition matrix is computed for `dischargeOpen` or `atomic`, whose transition results are the restricted theorems recorded in the source-updates section.

## Supporting declaration index

The subject contracts above use the following supporting declarations. Their source files retain the proof details; `lean/AxCheck.lean` records the public theorem audit. This index does not strengthen any theorem assumption or turn a witness into a general result.

| Lean source | Supporting declarations |
| --- | --- |
| [`lean/Lara/Attack.lean`](../lean/Lara/Attack.lean) | `contraryMatchB_iff` |
| [`lean/Lara/Compile.lean`](../lean/Lara/Compile.lean) | `conflictAttackableB_iff` |
| [`lean/Lara/Complexity/Context.lean`](../lean/Lara/Complexity/Context.lean) | `b_does_not_attack_d`, `d_attacks_b`, `m2bRegistry_empty` |
| [`lean/Lara/Complexity/Encoding.lean`](../lean/Lara/Complexity/Encoding.lean) | `fixedCredCompleteB_iff`, `matrixByteSize_eq_square` |
| [`lean/Lara/Consistency.lean`](../lean/Lara/Consistency.lean) | `Consistency.contrary_args_not_both_grounded` |
| [`lean/Lara/Context/Equivalence.lean`](../lean/Lara/Context/Equivalence.lean) | `argsWellSorted_map`, `attackFor_mapAssur`, `attackOcc_mapAssurAtt`, `conflictAttackableB_mapAssur`, `contains_mapAssur`, `crossAttsFrom_map`, `linkFault_mapAssurFrag`, `signatureStage_map`, `termWellSorted_mapAssur` |
| [`lean/Lara/Context/Link.lean`](../lean/Lara/Context/Link.lean) | `conclusionCache_sound`, `mem_conclusionCache` |
| [`lean/Lara/Context/Parametricity.lean`](../lean/Lara/Context/Parametricity.lean) | `argsWellSorted_rel`, `attackFor_rel`, `conflictAttackableB_rel`, `containsBDis_rel`, `containsBList_rel`, `crossAttsFrom_rel`, `linkFault_rel`, `linkGamma_rel`, `linkGround_rel`, `linkOk_rel`, `relTerm_subterm`, `signatureStage_rel`, `termWellSorted_rel` |
| [`lean/Lara/Context/Surface.lean`](../lean/Lara/Context/Surface.lean) | `checkedAF_map` |
| [`lean/Lara/Erase.lean`](../lean/Lara/Erase.lean) | `Erase.mapAssur_subterm`, `attackClosureB_mapAssur`, `containsB_mapAssur` |
| [`lean/Lara/Examples.lean`](../lean/Lara/Examples.lean) | `registry_exact_digest_accepts` |
| [`lean/Lara/Examples/CertificateCollapse.lean`](../lean/Lara/Examples/CertificateCollapse.lean) | `replaySlot_eq`, `source_sideOk` |
| [`lean/Lara/Examples/Complexity/Realization.lean`](../lean/Lara/Examples/Complexity/Realization.lean) | `checkUnit_cycle_ok`, `checkUnit_path_ok`, `checkUnit_reversedPath_rejected`, `rawUnitOfFormula_fixedFields` |
| [`lean/Lara/Examples/ContextSemantics.lean`](../lean/Lara/Examples/ContextSemantics.lean) | `cycle_accepted`, `cycle_admissible`, `cycle_link_ok`, `cycle_linked_shape`, `obsSem_linking_agrees`, `obsSem_linking_grounded`, `obsSem_sym_agrees`, `semantic_negative_accepted`, `semantic_negative_link_ok` |
| [`lean/Lara/Examples/Linking.lean`](../lean/Lara/Examples/Linking.lean) | `Linking.obs_defeated`, `certSwap_injective`, `certSwap_preserving` |
| [`lean/Lara/Examples/Realizability.lean`](../lean/Lara/Examples/Realizability.lean) | `Examples.Realizability.noAttack_of_emptyDefeat`, `compiled_no_edges_of_emptyDefeat` |
| [`lean/Lara/Examples/Semantics.lean`](../lean/Lara/Examples/Semantics.lean) | `dupCarrier_candidates`, `dupCarrier_enumerate`, `observe_claimNoSupport_uniform`, `twoCycle_defeated_unreachable`, `twoCycle_extensions` |
| [`lean/Lara/Examples/SurfaceTransport.lean`](../lean/Lara/Examples/SurfaceTransport.lean) | `crossAtts_of_ctx_args_nil`, `surfaceTransport_link_imports_nonempty`, `surfaceTransport_link_relabel_moves`, `surfaceTransport_link_relabel_moves_args`, `transport_coreObligations_kernel`, `transport_unit_is_link`, `transport_unit_wrapped_is_link` |
| [`lean/Lara/Examples/SurfaceTransportContext.lean`](../lean/Lara/Examples/SurfaceTransportContext.lean) | `contextLink_fixesContext` |
| [`lean/Lara/Examples/UpdateCompletion.lean`](../lean/Lara/Examples/UpdateCompletion.lean) | `discharge_completion_public_justified` |
| [`lean/Lara/Invariants/Observation.lean`](../lean/Lara/Invariants/Observation.lean) | `Invariants.observeSem_gap`, `Invariants.observeSem_of_status_gap`, `observeSem_of_status_gap` |
| [`lean/Lara/Observation.lean`](../lean/Lara/Observation.lean) | `agreesOnArgs_of_faithful`, `attackExtensional_complete`, `attackExtensional_preferred`, `attackExtensional_semiStable`, `attackExtensional_stable`, `conflictFree_congr_af` |
| [`lean/Lara/Realizability.lean`](../lean/Lara/Realizability.lean) | `R.ground_covers`, `ground_covers` |
| [`lean/Lara/Semantics.lean`](../lean/Lara/Semantics.lean) | `Semantics.admissible_nil`, `claimAcceptedB_of_nil`, `claimDefeatedB_of_nil`, `enumerate_ne_nil_of_observed_ne_gap`, `no_verdict_on_empty`, `observe_noExtension_iff` |
| [`lean/Lara/Semantics/Sublists.lean`](../lean/Lara/Semantics/Sublists.lean) | `Semantics.exists_max_length` |
