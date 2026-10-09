# The possible-world outer model

The outer model treats each checking context (its vocabulary, policy, and setting) as a world, so that support and status established in one world can be transported to another only along an explicitly declared, checked bridge. It lets a program compare what one checking context establishes with what another does, and it answers a comparison that crosses vocabularies without silently changing the claim it compares. Nothing in the outer layer redefines the local checker: the wrapper is a comparison layer over unchanged local Lara judgments, and every result below either imports the local layer or states an explicit hypothesis about it.

This document is the design, theorem, and runtime reference for that layer. It covers the outer frame and its semantics, the bridges that carry support and status (exact support transport, conditional status preservation, and path composition), the sorted surface and wire contract authors write against, and the Haskell runtime that executes a declared frame. It then states the limits of each part, the distinction from Belief Hoare Logic's epistemic equivalence, and the audit that keeps the claims honest.

The results are recorded against the Lean modules that hold them. A reader citing a contract should cite the declaration rather than re-derive it.

| Result | Lean modules | Section |
|---|---|---|
| Outer model, executable comparison boundary, T0 to T5, T7 counterexample | `Lara/PW/{Outer,Instance,Uniform,Compare}.lean`, `Lara/Examples/PW.lean` | The outer frame and satisfaction |
| Exact checked-support transport | `Lara/PW/{Structural,Translation}.lean`, `Lara/Examples/PWStructural.lean` | Structural bridges and exact support transport |
| Conditional status preservation | `Lara/PW/{Status,AFBisim,StatusCheck,AttackTransport}.lean`, `Lara/Examples/{PWStatus,PWStatusCheck,PWAttack}.lean` | Conditional status preservation |
| Exact structural-path composition | `Lara/PW/Compose.lean`, `Lara/Examples/PWCompose.lean` | Path composition |
| Sorted queries and the outer surface | `Lara/PW/{Sorted,Surface}.lean`, `Lara/Examples/{PWSorted,PWSurface}.lean` | Sorted queries and the outer surface |
| Declared bridges, wire contract, finite execution | `Lara/PW/{Declared,Finite}.lean`, `Lara/Examples/{PWFileHost,PWDeclared}.lean` | Declared bridges and the wire contract; Finite execution |
| Haskell runtime and differential conformance | `src/Lara/PW/*.hs`, `Lara/PW/Run.lean` | The Haskell runtime and conformance |

## The outer frame and satisfaction

The frame is a frame plus a valuation, not one monolithic model. `PW.Frame` (`lean/Lara/PW/Outer.lean`) carries contexts `K`, bridges `B` with `src`/`tgt`, per-context `World` and `Query`, the candidate relation `R`, the applicability judgment `accept`, and the claim translation `translate`. The valuation is not a frame field: it is a parameter of `PW.Sat`. The design instantiates one parameterized model twice, `M[V := V^src]` and `M[V := V^cmp]`; making the valuation a parameter states that parameterization once instead of duplicating the model. The accepted-edge relation is `A_b = R_b ∩ accept_b` (`PW.Frame.A`), fixed per bridge and independent of the formula being evaluated, which is the condition that supports normal modal logic.

Satisfaction is formula-first. The Lean is `Sat F V φ w`, where the paper writes `M, w ⊨ φ`. The order is forced: a world does not name its context, so with the world first no earlier argument determines the context index `κ`, and the `box`/`dia` arms do not elaborate. Taking the formula first lets the match refine `κ` from the constructor. `PW.KSat` follows the same order so both sides of T3 read alike.

Queries are all of `Atom`. Both status observations are total on `Atom` (a query with no matching retained node has empty complete support, hence `gap`), so the outer model takes the total query set. Well-sortedness is enforced by the sorted-query layer, which refines `Query_κ` to well-sorted claims over `Σ_κ` (see [Sorted queries and the outer surface](#sorted-queries-and-the-outer-surface)). Translations are bridge-global and partial: `translate : (b : B) → Query (src b) → Option (Query (tgt b))`. Edge-dependent translation is not mechanized. The primitive modalities do not translate their operands; translation appears only in derived formulas, which is what keeps each accepted relation formula-independent and hence the logic normal (T2).

`crossCompare`'s guard order is translation, then candidates, then acceptance (`lean/Lara/PW/Compare.lean`). It is generic over world and query types and takes the finite candidate list, the decidable acceptance, and the target status function as explicit inputs. The frame's `R`/`accept` are `Prop`-valued and carry no enumeration, and the design is explicit that no executability claim applies to an implicit set of admissible states without an effective finite representation.

`Presents` is the obligation that makes `crossCompare` an implementation rather than a lookalike. Nothing in `crossCompare`'s type says the candidate list enumerates `R_b(w, ·)` or that `acceptB` decides `accept_b(w, ·)`; it takes them on trust. `PW.Presents` states that obligation, and `PW.mem_compare_iff_sat_dia` then proves the executable interface computes the model's `⟨b⟩`. Without it, `crossCompare` and `Sat` are two unconnected islands and `Frame.translate` is a field no definition reads.

A `Prop`-valued valuation does not by itself say a claim has one status. `PW.Valuation.Functional` and `.Total` name that side condition. A model satisfying every T2 law can otherwise make `Justified(c) ∧ Defeated(c)` true; such a model is not a Lara model.

Stronger modal laws (T, 4, B, D, 5) are not posited; they belong only to bridges whose accepted relations satisfy the corresponding relational laws, and all five are refuted on outer-model-legal frames by `sat_T_fails`, `sat_D_fails`, `sat_B_fails`, `sat_5_fails` (two-world frame) and `sat_4_fails` (three-world chain). The outer model defines no sensitivity predicates.

## The outer model's checked results

Every row is `lean/AxCheck.lean`-gated: sorry-free, within the standard trio `propext` / `Classical.choice` / `Quot.sound`, no `native_decide` (which would add `ofReduceBool`). Every public theorem the five modules declare is gated.

| # | Content | Lean declaration | File |
|---|---|---|---|
| T0 | Current-Lara conservativity, compiled side | `PW.Instance.t0_cmp` | `Lara/PW/Instance.lean` |
| T0 | Current-Lara conservativity, source side | `PW.Instance.t0_src` | `Lara/PW/Instance.lean` |
| T1 | World-local source/compiled preservation | `PW.Instance.srcStatus_iff_cmpStatus` | `Lara/PW/Instance.lean` |
| T2 | Derived implication semantics | `PW.sat_imp` | `Lara/PW/Outer.lean` |
| T2 | Typed K | `PW.sat_K` | `Lara/PW/Outer.lean` |
| T2 | Typed necessitation | `PW.sat_nec` | `Lara/PW/Outer.lean` |
| T2 | Duality `⟨b⟩φ ↔ ¬[b]¬φ` | `PW.sat_dia_iff_not_box_neg` | `Lara/PW/Outer.lean` |
| T2 | Top preservation | `PW.sat_box_top` | `Lara/PW/Outer.lean` |
| T2 | Finite-meet preservation | `PW.sat_box_conj` | `Lara/PW/Outer.lean` |
| T2⁻ | **Every stronger frame axiom fails** (normal, and no more): T, D, B, 5 on one frame, 4 on a chain | `Examples.PW.sat_T_fails`, `sat_D_fails`, `sat_B_fails`, `sat_5_fails`, `sat_4_fails` | `Lara/Examples/PW.lean` |
| T3 | Uniform-language reduction to multimodal Kripke | `PW.sat_lift` | `Lara/PW/Uniform.lean` |
| T4 | Valuation congruence (generic core) | `PW.sat_congr` | `Lara/PW/Outer.lean` |
| T4 | Modal source/compiled coherence | `PW.Instance.sat_src_iff_cmp` | `Lara/PW/Instance.lean` |
| T4 | Worked instances of the congruence, both readings | `Examples.PW.t7_dia_defeated_src`, `t7_box_defeated_src` | `Lara/Examples/PW.lean` |
| T5 | Undefined translation | `PW.compare_none`, `PW.compare_translationUndefined_iff` | `Lara/PW/Compare.lean` |
| T5 | No candidate world | `PW.compare_no_candidate` | `Lara/PW/Compare.lean` |
| T5 | All candidates rejected | `PW.compare_all_rejected` | `Lara/PW/Compare.lean` |
| T5 | Comparable profile | `PW.compare_comparable`, `PW.mem_compare_profile_iff` | `Lara/PW/Compare.lean` |
| T5 | Constructor disjointness (gate 3, structural) | `PW.incomparable_ne_comparable` | `Lara/PW/Compare.lean` |
| T5 | Adequacy: the profile *is* `⟨b⟩` | `PW.mem_compare_iff_sat_dia` | `Lara/PW/Compare.lean` |
| T5 | Gate 3, semantically: incomparable ⇒ no accepted witness | `PW.not_sat_dia_of_incomparable` | `Lara/PW/Compare.lean` |
| T5 | The presentation obligation, discharged at a real bridge | `Examples.PW.presentsT7` | `Lara/Examples/PW.lean` |
| T5 | Adequacy round trip: `crossCompare` ⇒ `⟨b⟩`, on that bridge | `Examples.PW.t7_dia_via_adequacy` | `Lara/Examples/PW.lean` |
| T5 | Gate 3's semantic arm, discharged at a rejected bridge | `Examples.PW.presentsOverlapRejected`, `overlap_rejected_no_dia` | `Lara/Examples/PW.lean` |
| n/a | Valuation coherence, compiled | `PW.Instance.cmpVal_functional`, `cmpVal_total` | `Lara/PW/Instance.lean` |
| n/a | Valuation coherence, source (**only through T1**) | `PW.Instance.srcVal_functional`, `srcVal_total` | `Lara/PW/Instance.lean` |
| n/a | No world reports two statuses | `PW.not_sat_two_status` | `Lara/PW/Outer.lean` |
| n/a | …instantiated at a Lara bridge | `Examples.PW.t7_no_two_status` | `Lara/Examples/PW.lean` |
| T7 | Status non-preservation witness | `Examples.PW.t7_witness` | `Lara/Examples/PW.lean` |
| T7 | The `⟨b⟩` reading | `Examples.PW.t7_dia_defeated` | `Lara/Examples/PW.lean` |
| T7 | The `[b]` reading | `Examples.PW.t7_box_defeated` | `Lara/Examples/PW.lean` |
| T7 | The transport is the identity on the source support | `Examples.PW.t7_support_transported` | `Lara/Examples/PW.lean` |
| n/a | The local `gap` gate 3 declines to report | `Examples.PW.overlap_local_gap` | `Lara/Examples/PW.lean` |

T1 is the substantive theorem, and its two sides are independently defined. `PW.Instance.srcStatus` is the relational, oracle-free `Compile.SrcStatus`, read off `SrcIn`/`SrcOut` with no compiled framework, no grounded labelling, and no enumeration. `PW.Instance.cmpStatus` is the executable `Grounded.statusC` over `Compile.checkedAF`. Neither is defined through the other. Their agreement is `Compile.srcStatus_iff_checked`, Lara's existing source-to-compilation preservation chain, instantiated at the world.

T4 is an integration theorem, not an independent Lara result. `sat_congr` is a routine structural induction whose content is that satisfaction is extensional in the atomic valuation; the substantive result underneath it is T1. It is stated over the *same* frame, so the accepted relations are literally shared and the modal cases move across for free. That is what makes it a genuine lifting theorem rather than definitional duplication. `t7_dia_defeated_src` is its worked instance, a congruence theorem with no instance can be true and useless.

T7's content. One context (`ctxT7`, whose defeat table declares `q` contrary to `p`), two accepted worlds. The source world admits only the `p` argument and justifies `p`. The target world admits the same `p` argument plus one unattacked `q` attacker with the required typed undermine edge, and defeats `p`. The transported support term `SupportTerm.leaf l1` remains a checked argument of the target program (`t7_transport_wellFormed`), and the transport really is the identity on the source claim's support rather than mere coincidental membership: source and target complete supports for `p` are the same nonempty index set `[0]`, and that shared index resolves through both retained node caches (the structure support indices actually index) to the same term `leaf l1` (`t7_support_transported`). So transporting well-formed support does not transport grounded status: status preservation needs strictly more than support transport, which fixes the boundary between T6 (exact support transport) and T8.

The witness exists at all only because the missing-conflict search is directional: `firstMissingConflict?` (`Lara/Check/Program.lean:610-633`) tests `contraryMatchB canon dp source.conclusion target.conclusion` in one direction, so the contrary pair demands the edge `q → p` and no reverse edge. A forced symmetric edge would leave `p` *contested* rather than defeated.

## The outer model's limitations

These are design commitments, not oversights.

**`accept` is a frame parameter, and the checker's tie to it is a separate layer.** In `PW.Frame` itself, `accept` is an arbitrary `Prop`: nothing in the frame ties it to a checker, to a certificate, to a soundness condition, or even to `R`. The checker-tied discipline is supplied on top: `PW.Admits` states that the target world's accepted program carries the transport of every argument of the source world's accepted program, and `admits_transport` turns an admitted edge into checked mathematics.

**`gap` conflates four conditions:** out of vocabulary, ill-sorted, not posed, and posed but unsupported, because queries are all of `Atom`. Modal instability at a `gap` may therefore reflect a vocabulary mismatch rather than a scientific disagreement, and a reader must not read `⟨b⟩Gap(c)` as "the target field considered this and found it unsupported". The executable layer separates only the bridge-domain case, and reports it as `translationUndefined` rather than as any status, which is exactly what `overlap_translationUndefined` fixes for the source-only claim `s`.

The sorted-query refinement removes the two signature-level conditions: out-of-vocabulary and ill-sorted atoms are not queries, and `PW.Sorted.pose` reports the distinction before consulting a world. `PW.Sorted.notPosable_world_independent` proves that this refusal depends on no world. Translation refusal separately distinguishes an absent bridge-map entry from a target query that cannot be stated. For a well-sorted query, `PW.Sorted.cmpStatus_gap_iff_not_addresses` says `gap` means no complete support. It does not distinguish an absent argument from an incomplete-only attempt: accepted worlds may retain located holes, which this status projection does not expose.

**A `Context` fixes the checking environment, not a scientific state.** A `Context` is (Σ, Policy, Registry) plus the checker parameters; two worlds of one context may differ in program, admitted evidence, declared supports, and attacks. That is intended, because it is what makes `⟨b⟩` and `[b]` non-trivial *within* a context, and the T7 witness is exactly such a pair. But "world of this context" must not be read as "this artifact". Nothing pins the program.

## Structural bridges and exact support transport

The translation is a partial symbol map, lifted structurally. `PW.SymMap` carries independent partial maps on the predicate and constructor namespaces (`Lara/PW/Translation.lean`); everything else (variables, numeric and string literals, rule identifiers, question keys, hole sets, assurances including the frozen certificate triple) is carried across verbatim, and evidence leaves are renamed by a separate *total* `LeafId` map. Partiality is the translation-domain evidence: every lift is `Option`-valued, `none` exactly at an out-of-vocabulary symbol, and the transport theorem consumes the `some` hypotheses rather than assuming totality. The dependent partial support map `T_{b}` of the design is `PW.trSupport`.

The contract is three clauses over a shared `canon` (`PW.StructuralBridge`, `Lara/PW/Structural.lean`), one clause per environment parameter the typing judgment `HasSupport canon Pi Gamma CertOk` reads:

- `leaf_ok`: a leaf typed at `p` in the source is typed at the translated `p` in the target under the leaf map ("admitted evidence and artifact identity");
- `rule_ok`: the target policy carries, at the *same* rule identifier, exactly the translated rule, with premises, conclusion, and answers translated, and mode, parameters, premise order, question keys, the trusted flag, and the certifier allowlist preserved on the nose ("sorts, substitutions, constructors, identifiers, premise order");
- `cert_ok`: certificate acceptance survives translation of the encoded step ("backend registry entries and per-occurrence certificates").

The shared `canon` is a commitment, not an omission: the source canonicalizer is the one thing two bridged environments must agree on for their conclusions to be comparable as claims, the same shared binder B0 records for registries (`docs/strict-certificates.md#6-heterogeneous-composition-the-firewall-and-the-accounting-laws`, "two binders ARE shared").

Every contract field is read by a named arm of the transport induction; the contract carries no field the proof does not consume.

| Result | Declaration |
|---|---|
| T6 exact checked-support transport | `PW.support_transport` |
| T6 completeness clause | `PW.support_transport_complete` |
| Claim-level transport | `PW.supports_transport` |
| Conclusion law (pattern level) | `PW.instAPat_tr`, `instAPats_tr` |
| `≡` survives translation | `PW.equiv_tr` (via `trAtom_nf`, `trTerm_nf`) |
| Target-side occurrence replay | `PW.transport_occurrences_accounted` |
| Checker-tied applicability | `PW.Admits`, `PW.admits_transport` |
| Identity endobridge | `PW.StructuralBridge.refl`, `Examples.PW.admitsIdT7`, `t7_t6_transport` |
| T6/T8 boundary at a live instance | `Examples.PW.t7_t6_boundary` |
| Renaming instance | `Examples.PW.bridgeRen`, `hasSupport_ren`, `ren_transport` |
| Strict-certificate renaming instance | `Examples.PW.bridgeCert`, `hasSupport_cert`, `cert_transport` |
| Contract clauses exercised off the identity | `Examples.PW.ren_leaf_translated`, `ren_support_renamed`, `cert_accept_translated`, `cert_reject_untranslated`, `cert_support_renamed` |
| Strict-fixture drift guards | `Examples.PW.cert_reject_mismatched_certifier`, `cert_target_rule`, `cert_only_assurance` |
| Translation-domain negative | `Examples.PW.ren_out_of_vocabulary`, `ren_translationUndefined` |

The renaming instance discharges `rule_ok` and `leaf_ok` under a translation that actually renames: the target policy carries the translated rule, and the renamed leaf is admitted at the translated atom. The strict-certificate instance discharges the third clause: a strict rule with a live certifier allowlist and `allowTrusted` off, a `CertOk` pair holding exactly at the fixture's encoded step on each side, `cert_accept_translated` pinning that source acceptance at `([e], p)` survives translation to target acceptance at `([e_r], p_r)`, and `cert_reject_untranslated` pinning that neither side accepts the other's encoded step. `cert_transport` runs the transported derivation through the `AssuranceOk.cert` arm off the identity, the frozen `(β, hd, κ)` triple carried verbatim. Soundness is carried by `support_transport`, not by these examples; they are the conformance evidence that all three contract clauses are inhabitable off the identity.

Because `cert_transport` exercises the strict fixture at exactly one certifier triple and one encoded step, two mutations of the fixture would leave it green while making the accepted reading false. The drift guards close both. Dropping `(β, hd, κ)` from either acceptance judgment, so that acceptance is a predicate on the encoded step alone, is rejected by `cert_reject_mismatched_certifier`, which pins that mismatching exactly one of the three components, with the side's own encoded step held fixed, is refused on both sides. Flipping `ruleCert.allowTrusted` on is rejected by `cert_only_assurance`, which pins the flag off and proves that neither `.trusted` (which needs the flag) nor `.none` (which needs a defeasible rule) can satisfy `AssuranceOk` at the fixture's encoded step, in the source *and* in the target environment, so the certificate arm is the only reachable assurance, which is what makes `cert_ok` load-bearing. `cert_target_rule` ties the target half down: the target rule is written out independently of `ruleCert` and the equation `piCertTgt rnCert = some ruleCertTgt` holds by `rfl`, so any drift in `ruleCert`'s mode, allowlist, or trusted flag breaks it.

`support_transport` states: under the contract, if `HasSupport canon Pi Gamma CertOk w C O` and `trSupport sym leafMap w = some w'`, then there is a `C'` with `trAtom sym C = some C'` and `HasSupport canon Pi' Gamma' CertOk' w' C' O`. The conclusion's translation definedness is *derived*; the obligation list is the *same* `O`.

Completeness needs no condition on obligations: the obligation list transports *unchanged*, because obligations are lists of question *names*, question names are rule-local vocabulary the translation never touches (`trRule_questionNames`, `trRule_mandatoryNames`), and discharge keys and hole sets are carried verbatim (`trSupportDis_fst`). `collectObligations` then computes identically on both sides. Completeness (`O = []`) is the special case, not an extra hypothesis.

The same two commuting facts carry the whole induction. Instantiation commutes with translation (`instAPat_tr`): translating a substitution and a pattern and then instantiating equals instantiating and then translating, because variables are untouched and the instantiated constructor name is the pattern's own. And `≡` survives translation (`equiv_tr`): `nf` canonicalizes numeric literals only, the translation renames predicate/constructor names only, so the two commute and `nf`-equality is preserved. That is what lets premise identity (`premEq`) and discharge answers (`ans`) transport.

Target-side occurrences replay against the target registry. Instantiating both certificate judgments from registries (`CertOk := certOkOf reg`, `CertOk' := certOkOf reg'`), `transport_occurrences_accounted` applies B0's headline (`hetero_occurrences_accounted`) to the *transported* derivation: every strict occurrence of the transported term is accounted by its own backend as registered in the target registry, the target policy carries its rule, the certificate is accepted by the target instantiation, and the occurrence-local consequence holds. It is a corollary rather than a new induction.

At structural bridges, `PW.Admits` ties `accept` to the checker (the first limitation of the outer model): the target world's accepted program carries the transport of every argument of the source world's accepted program. `admits_transport` then turns an admitted edge into checked mathematics: every source argument transports to a member of the target's own accepted program carrying a complete checked support for the translated conclusion, checked in the target context's environment.

The T6/T8 boundary is packaged at the live T7 fixtures. `Examples.PW.t7_t6_boundary` states: the identity endobridge's transport succeeds (`Admits` holds between `wT7src` and `wT7tgt`) *and* `cmpStatus` flips from `justified` to `defeated`, so the T6 machinery itself exhibits that support transport does not give status preservation. T8 must therefore quantify over the target's attackers; nothing in T6's theorem set can be strengthened into T8 without new hypotheses.

The limits of the transport contract:

1. **The translation is bridge-global and functional.** One `SymMap` answers for every world pair of the bridge, so the alias case cannot be expressed: a source atom names an entity by an obsolete alias, one target world under the bridge carries the ontology version that resolves it and another target world under the *same* bridge does not, and a single global `translate b` must answer once for both. An edge-indexed translation would be a relation `Translate : (b : B) → World (src b) → World (tgt b) → Query (src b) → Query (tgt b) → Prop`, which also admits *ambiguity* (several target queries for one source query) that `Option` forbids by construction. Moving to it is a genuine contract change, not a refinement: `mem_compare_iff_sat_dia` and `compare_translationUndefined_iff` are both stated against the `Option` form, and the executable `crossCompare` takes a single `Option Q` as its first guard.
2. **The leaf map is total.** A source leaf with no target counterpart cannot be expressed; partial evidence translation would push `Option` into the leaf arm of `trSupport` and into `leaf_ok`.
3. **Attacks sit outside the transport contract, by design.** Basic support checking does not read attacks, so `support_transport` preserves nothing about attack structure. Attack correspondence is a separate layer with its own hypotheses: `PW.StatusBridge` (`forth`/`back`/`matched`) at the compiled level, and `PW.AttackBridge` over declared `atts` via `trAttack`.
4. **Path composition is a separate layer.** `trSupport` composes as a function, but the bridge-level coherence laws for a path of structural bridges are T9's (see [Path composition](#path-composition)), not stated in T6's contract.
5. **Question keys are frozen across the bridge.** A bridge that renames its critical-question vocabulary is not expressible; obligations transport verbatim *because* of this. Relaxing it would make "mapped obligations" a genuine map and completeness conditional on that map.

## Conditional status preservation

The primitive is a total attack bisimulation, not an isomorphism. `PW.AttackBisim F G Z` relates two finite frameworks through a relation `Z` on argument ids with five clauses: `dom` (`Z` relates carrier members only), `left_total` (every source argument is related to a target argument), `right_total` (every target argument is related to a source argument), `forth` (a source attacker of a related argument is matched by a related target attacker), and `back` (a target attacker of a related argument is matched by a related source attacker). Grounded labels and the four-state status are invariant under such a relation (`labelC_of_bisim`, `statusC_of_bisim`).

The design's AF isomorphism is `PW.AFIso F G f`, the graph of a bijection that preserves and reflects attack (fields `maps`, `inj`, `surj`, `attack_iff`), and `AFIso.toBisim` shows its graph is a bisimulation, so the isomorphism route (`statusC_of_iso`) is a corollary. The `inj` field is consumed by no proof. Both right-totality and the `back` clause of the induced bisimulation are discharged by `surj` alone: a target attacker must be exhibited as an `f`-image before `attack_iff` can reflect it, and nothing ever needs two source arguments with the same image to be equal. The design's isomorphism is therefore strictly stronger than what status preservation requires; a surjective bounded morphism already suffices. `AFIso` keeps `inj` because it is what "isomorphism" means; the primitive status preservation rests on is the bisimulation.

At a structural bridge the relation is index-level. Compiled arguments are list positions (`Compile.toAF`), so the relation the bisimulation lives on is `PW.Corr m lm w v i j`: the `i`-th argument of the source world's accepted program transports under `trSupport m lm` to the `j`-th argument of the target world's. The T8 hypotheses are the four fields of `PW.StatusBridge m lm w v`:

- `admits`: T6's `Admits`, every source argument transports into the target program (left-totality of `Corr`), also named `PW.Matched` for the converse scan;
- `matched`: every target argument *is* a transport of some source argument (right-totality), the clause that excludes unmatched target supports and attackers, and the one the T7 target violates;
- `forth` and `back`: the attack conditions, stated on the compiled edge decider `Compile.edgeB`, a source attacker of a `Corr`-related argument is matched by a target attacker of its counterpart, and conversely.

```text
source: checkedAF w.unit.program        target: checkedAF v.unit.program

     k --edgeB--> i  ---- Corr i j ----  j <--edgeB-- k'

forth: from a source edge k → i and Corr i j, find k' with Corr k k'
       and a target edge k' → j
back:  from a target edge k' → j and Corr i j, find k with Corr k k'
       and a source edge k → i
```

`StatusBridge.bisim` shows these four clauses are exactly an `AttackBisim` of the two `checkedAF`s under `Corr`. Nothing in the `StructuralBridge` contract implies any of them; that is the point.

The support-set correspondence is derived, not assumed. For every translatable query `c` with `trAtom B.sym c = some c'`, `PW.claimSupport_corr` proves `SupportCorr (Corr …) (claimAt w c) (claimAt v c')` from the contract and the hypotheses. Its forward half runs T6 transport and `equiv_tr` through `corr_conclusion` (the target node's conclusion at a related index *is* the translated source conclusion, by `hasSupport_unique`); its backward half runs `matched` and `equiv_tr_reflect`, and it is the backward half that needs `PW.SymMap.Injective`. `PW.status_transport` is the headline for injective bridges; `PW.status_transport_of_corr` is the theorem for bridges whose translation is not injective but whose support correspondence is supplied by other means.

`StatusBridge.forth`/`back` drop `AttackBisim`'s `b ∈ F.args` premise on the attacker, and `StatusBridge.bisim` discards it, so an instance discharging these fields must recover in-rangeness of the attacker index itself, via `(Compile.edgeB_faithful P).ranged`; every executable witness in `Lara/Examples/PWStatus.lean` does exactly this.

Every public theorem declared by the five modules appears below. Definition rows are included to identify the objects those theorems constrain; they are audited transitively through the gated theorems that mention them.

Generic layer, `Lara/PW/AFBisim.lean`:

| Result | Declaration | File |
|---|---|---|
| Total attack bisimulation and its converse | `PW.AttackBisim` (fields `dom`, `left_total`, `right_total`, `forth`, `back`); `PW.AttackBisim.symm` | `Lara/PW/AFBisim.lean` |
| The declarative grounded judgments transfer along a bisimulation | `PW.directIn_bisim`, `PW.directOut_bisim`; iff forms `PW.directIn_iff_of_bisim`, `PW.directOut_iff_of_bisim` | `Lara/PW/AFBisim.lean` |
| Grounded labels are bisimulation-invariant | `PW.labelC_of_bisim` | `Lara/PW/AFBisim.lean` |
| Complete-support correspondence and the status congruence it feeds | `PW.SupportCorr`; `PW.statusC_congr` | `Lara/PW/AFBisim.lean` |
| Four-state status is bisimulation-invariant on corresponding claims | `PW.statusC_of_bisim` | `Lara/PW/AFBisim.lean` |
| The design's AF isomorphism and its graph | `PW.AFIso` (fields `maps`, `inj`, `surj`, `attack_iff`); `PW.AFIso.graph` | `Lara/PW/AFBisim.lean` |
| An isomorphism is a bisimulation (`inj` unused) | `PW.AFIso.toBisim` | `Lara/PW/AFBisim.lean` |
| Labels and status along an isomorphism | `PW.labelC_of_iso`, `PW.statusC_of_iso` | `Lara/PW/AFBisim.lean` |
| The design's "onto the complete support set" yields the correspondence | `PW.supportCorr_of_image` | `Lara/PW/AFBisim.lean` |

Instantiation at structural bridges, `Lara/PW/Status.lean`:

| Result | Declaration | File |
|---|---|---|
| Injectivity-where-defined of a partial translation, and the identity | `PW.SymMap.Injective`; `PW.SymMap.id_injective` | `Lara/PW/Status.lean` |
| An injective translation is injective on terms, term lists, and atoms | `PW.trTerm_inj`, `PW.trTerms_inj`, `PW.trAtom_inj` | `Lara/PW/Status.lean` |
| `≡` reflects along an injective translation (converse of T6's `equiv_tr`) | `PW.equiv_tr_reflect` | `Lara/PW/Status.lean` |
| The index relation a translation induces, and its range bound | `PW.Corr`; `PW.corr_lt` | `Lara/PW/Status.lean` |
| The T8 hypotheses | `PW.StatusBridge` (fields `admits`, `matched`, `forth`, `back`) | `Lara/PW/Status.lean` |
| The hypotheses are a bisimulation of the compiled frameworks | `PW.StatusBridge.bisim` | `Lara/PW/Status.lean` |
| Target conclusion at a related index is the translated source conclusion | `PW.corr_conclusion` | `Lara/PW/Status.lean` |
| Derived support-set correspondence for every translatable query | `PW.claimSupport_corr` | `Lara/PW/Status.lean` |
| Status preservation from a supplied correspondence | `PW.status_transport_of_corr` | `Lara/PW/Status.lean` |
| **T8: conditional status preservation** | `PW.status_transport` | `Lara/PW/Status.lean` |
| T8 at the source observation (T1 on both sides) | `PW.srcStatus_transport` | `Lara/PW/Status.lean` |
| The modal reading: `[b]` and `⟨b⟩` collapse to the local atom | `PW.sat_status_iff_box`, `PW.sat_status_iff_dia`, `PW.sat_status_iff_box_src` | `Lara/PW/Status.lean` |
| Injectivity is closed under Kleisli composition | `PW.SymMap.Injective.comp` | `Lara/PW/Status.lean` |
| `Corr` along the composite factors through the intermediate world | `PW.corr_comp_iff` | `Lara/PW/Status.lean` |
| Status bridges compose along the T9 composite | `PW.StatusBridge.comp` | `Lara/PW/Status.lean` |
| Declared-attack translation and its list lift | `PW.trAttack`, `PW.trAttackList`; `PW.trAttackList_cons` | `Lara/PW/AttackTransport.lean` |
| Translation injectivity on support terms, and equality reflection | `PW.trSubst_inj`, `PW.trSupport_inj`, `PW.trSupportList_inj`, `PW.trSupportDis_inj`, `PW.trSupport_eq_iff` | `Lara/PW/AttackTransport.lean` |
| Positional navigation commutes with translation | `PW.lookupDis_trSupportDis`, `PW.trSupport_subterm`, `PW.trSupport_subterm_some` (helpers `PW.trSupport_leaf`, `PW.trSupport_inst_inv`, `PW.lookupDis_mem`, `PW.trSupportList_some_of_mem`, `PW.trSupportDis_some_of_mem`) | `Lara/PW/AttackTransport.lean` |
| Containment, attack closure, and declared-edge coverage are translation-invariant under injectivity | `PW.containsB_trSupport`, `PW.containsBList_trSupport`, `PW.containsBDis_trSupport`, `PW.trAttack_source`, `PW.attackClosureB_trAttack`, `PW.coveredB_trAttack` | `Lara/PW/AttackTransport.lean` |
| The `Contains`/`AttackOcc` Prop faces | `PW.Contains_trSupport`, `PW.AttackOcc_trSupport` | `Lara/PW/AttackTransport.lean` |
| T8's attack hypotheses on the source language, and the index-level clauses derived | `PW.AttackBridge`; `PW.AttackBridge.toStatusBridge` | `Lara/PW/AttackTransport.lean` |

Executable decider, `Lara/PW/StatusCheck.lean`:

| Result | Declaration | File |
|---|---|---|
| `Corr`, `Admits`, and the matched conjunct as `Bool` scans over the shared transport test, with their Prop reflections | `PW.corrB`, `PW.admitsB`, `PW.matchedB`; `PW.transportsB`; `PW.corrB_iff`, `PW.admitsB_iff`, `PW.matchedB_iff`, `PW.transportsB_iff` | `Lara/PW/StatusCheck.lean` |
| `forth`/`back` as one directed bisimulation scan at the two orientations, with the range bound of a `true` `corrB` cell | `PW.bisimScanB`; `PW.forthB`, `PW.backB`; `PW.corrB_lt` | `Lara/PW/StatusCheck.lean` |
| The scan is sound and complete, once generically and once per orientation | `PW.bisimScanB_sound`, `PW.bisimScanB_complete`; `PW.forthB_sound`, `PW.forthB_complete`, `PW.backB_sound`, `PW.backB_complete` | `Lara/PW/StatusCheck.lean` |
| The `StatusBridge` decider (a four-way `&&` of the scans) | `PW.statusBridgeB` | `Lara/PW/StatusCheck.lean` |
| The decider decides `StatusBridge` exactly | `PW.statusBridgeB_sound`, `PW.statusBridgeB_complete`, `PW.statusBridgeB_iff` | `Lara/PW/StatusCheck.lean` |

`StatusBridge` quantifies unboundedly over `Nat`, so it is not decidable as stated and has no `Decidable` instance; the decider is a `Bool` checker with a sound/complete pair, matching `edgeB`/`edgeB_faithful`. `StatusBridge.back` is `StatusBridge.forth` with the two sides swapped, so the directed scan, its soundness, and its completeness are written once over abstract `Nat → Nat → Bool` relations (`bisimScanB`) and instantiated at the two orientations.

`status_transport` states: for contexts `κ`, `λ` with `λ.canon = κ.canon` (`hcanon`, T6's shared-canonicalizer commitment), a structural bridge `B` between them, worlds `w : World κ` and `v : World λ` with `StatusBridge B.sym B.leafMap w v` and `B.sym.Injective`, and any `c`, `c'` with `trAtom B.sym c = some c'`: `cmpStatus v c' = cmpStatus w c`.

Executable witnesses, `Lara/Examples/PWStatus.lean` (namespace `Lara.Examples.PW.Status`):

| Witness | Declaration | File |
|---|---|---|
| The T7 identity edge satisfies `forth` (vacuously: no source attacks) | `Examples.PW.Status.t7_forth` | `Lara/Examples/PWStatus.lean` |
| The T7 target's attacker is unmatched: `matched` fails at `leaf l2` | `Examples.PW.Status.t7_l2_mem`, `t7_unmatched`, `t7_not_statusBridge` | `Lara/Examples/PWStatus.lean` |
| The same, by T8's contrapositive from the status flip alone | `Examples.PW.Status.t7_not_statusBridge_of_flip` | `Lara/Examples/PWStatus.lean` |
| A forward attack homomorphism is insufficient | `Examples.PW.Status.t7_forward_hom_insufficient` | `Lara/Examples/PWStatus.lean` |
| Source context over the empty registry and its two accepted worlds | `Examples.PW.Status.regEmpty`, `ctxS`, `wS1`, `wS2`; `unitS1_accepted`, `unitS2_accepted` | `Lara/Examples/PWStatus.lean` |
| Renamed context, vocabulary, policy, and its two accepted worlds | `Examples.PW.Status.pR`, `qR`, `sR`, `ΓR`, `sigmaR`, `polR`, `ctxR`, `wR1`, `wR2`; `unitR1_accepted`, `unitR2_accepted` | `Lara/Examples/PWStatus.lean` |
| The renaming translation, leaf map, and structural bridge off the identity | `Examples.PW.Status.symR`, `leafMapR`, `bridgeR`; `symR_injective` | `Lara/Examples/PWStatus.lean` |
| Status bridges between the one-argument and the attacked two-argument worlds | `Examples.PW.Status.s1_r1_statusBridge`, `s2_r2_statusBridge` | `Lara/Examples/PWStatus.lean` |
| `justified` transports, with both cells evaluated | `Examples.PW.Status.t8_justified_preserved`, `t8_justified_cells` | `Lara/Examples/PWStatus.lean` |
| `defeated` transports through a real matched attacker, with both cells | `Examples.PW.Status.t8_defeated_preserved`, `t8_defeated_cells` | `Lara/Examples/PWStatus.lean` |
| `gap` transports on the unsupported claim, with both cells | `Examples.PW.Status.t8_gap_preserved`, `t8_gap_cells` | `Lara/Examples/PWStatus.lean` |
| `contested` transports, with both cells evaluated (symmetric contraries, two matched attacks each way) | `Examples.PW.Status.polS3`, `ctxS3`, `wS3`, `polR3`, `ctxR3`, `wR3`, `bridgeR3`; `unitS3_accepted`, `unitR3_accepted`, `s3_corr_diag`, `s3_r3_statusBridge`; `t8_contested_preserved`, `t8_contested_cells` | `Lara/Examples/PWStatus.lean` |
| The transported claim is genuinely renamed | `Examples.PW.Status.t8_renamed` | `Lara/Examples/PWStatus.lean` |
| Two-context bridge data, its accepted edge, and every successor bridged | `Examples.PW.Status.bridgeDataR`; `r_edge_accepted`, `r_all_bridged` | `Lara/Examples/PWStatus.lean` |
| The `[b]` cell at `defeated`, and its inhabitation | `Examples.PW.Status.t8_box_defeated_r`, `t8_box_defeated_r_holds` | `Lara/Examples/PWStatus.lean` |

Decider conformance cells, `Lara/Examples/PWStatusCheck.lean` (namespace `Lara.Examples.PW.StatusCheck`):

| Witness | Declaration | File |
|---|---|---|
| The three positive bridges re-established by one `decide` each | `Examples.PW.StatusCheck.s1_r1_decider`, `s2_r2_decider`, `s3_r3_decider` | `Lara/Examples/PWStatusCheck.lean` |
| Soundness turns a decider cell back into the Prop-level bridge | `Examples.PW.StatusCheck.s2_r2_statusBridge_via_decider` | `Lara/Examples/PWStatusCheck.lean` |
| The T7 negative through the decider: a `false` scan, refuted via completeness | `Examples.PW.StatusCheck.t7_decider_rejects`, `t7_not_statusBridge_via_decider` | `Lara/Examples/PWStatusCheck.lean` |
| T7 clause by clause: `matched` and `back` fail, `admits` and `forth` hold | `Examples.PW.StatusCheck.t7_matchedB_false`, `t7_backB_false`, `t7_admits_forth_hold` | `Lara/Examples/PWStatusCheck.lean` |
| Isolating negatives pinning `admitsB` and `matchedB` independently | `Examples.PW.StatusCheck.s2_r1_admits_fails`, `s2_r1_matched_holds`, `s1_r2_matched_fails`, `s1_r2_admits_holds` | `Lara/Examples/PWStatusCheck.lean` |
| Isolating negatives pinning `forthB` and `backB` independently | `Examples.PW.StatusCheck.forthB_discriminates`, `backB_discriminates` | `Lara/Examples/PWStatusCheck.lean` |

The positive witnesses are off the identity: `symR` renames all three predicates, `leafMapR` renames every leaf, and `bridgeR` discharges `leaf_ok` at each of the three source leaves under that renaming. `s2_r2_statusBridge` exercises `forth` and `back` on a real compiled edge (`1 → 0` on each side), index by index, which is what makes `t8_defeated_preserved` a transport through a matched attacker rather than a vacuous one.

Why status needs the target's attackers. A claim's status at a world is `Grounded.statusC (Compile.checkedAF w.unit.program) (claimAt w c)`, with `claimAt w c = Consistency.completeClaimFor w.unit c` (`PW.cmpStatus`, `Lara/PW/Instance.lean`). That is a global grounded fixed point over the whole compiled framework, every argument and every attack, read at the claim's complete-support index set. It is not a property of any one support term. T6's contract is term-local by design: `support_transport` carries one checked derivation across, and attacks do not transport.

The boundary has two ends, both at the live T7 fixtures. `Examples.PW.t7_t6_boundary` (T6, unchanged) shows the identity endobridge's `Admits` holds between `wT7src` and `wT7tgt` and `cmpStatus` flips from `justified` to `defeated`, so support transport alone cannot give status. `Examples.PW.Status.t7_forward_hom_insufficient` (T8) shows that on the same edge, left-totality (`Admits`) *and* `forth` hold (the edge is a forward attack homomorphism) and the status still flips, so a forward homomorphism alone cannot give status either. The field the T7 edge fails is `matched`, at `leaf l2`: the target's attacker is in the target program (`t7_l2_mem`) and is the transport of no source argument (`t7_unmatched`), so `t7_not_statusBridge` refutes `StatusBridge` directly at that field. The hand refutation needs no other clause, but the executable checker records a second failure: `back` also fails (`t7_backB_false`), because the target's `1 → 0` attack has no counterpart across the identity correlation, the source program having no attacks at all. `t7_not_statusBridge_of_flip` recovers the same refutation from the flip alone, by running `status_transport` at the identity bridge and contradicting the two evaluated cells: T8's contrapositive reads a status flip as proof that some hypothesis fails, without naming which.

Where injectivity enters and what breaks without it. `claimSupport_corr`'s backward half must show that every target support argument for `τ(c)` is the transport of a source support argument for `c`. `matched` supplies a source argument whose transport it is; what remains is that its conclusion is `≡ c`. T6's `equiv_tr` runs the wrong way for this, since it takes `≡` forward. `equiv_tr_reflect` runs it backward, and it is exactly here that `SymMap.Injective` is consumed: `nf` commutes with translation (`trAtom_nf`), so equal target normal forms are translations of the two source normal forms, and injectivity identifies them.

Without injectivity the derivation stops: a merging translation, two source predicates sent to one target predicate, is exactly what `equiv_tr_reflect` cannot invert, so the backward half of `claimSupport_corr` is unavailable. No Lean cell witnesses a concrete flip under a merging translation; the claim is only that the derivation needs injectivity. `status_transport` is therefore stated with `hinj : B.sym.Injective`. `status_transport_of_corr` is the escape hatch for bridges whose translation merges: it takes the support correspondence as an explicit hypothesis and proves the same equation from `StatusBridge.bisim`.

`PW.SymMap.Injective` is injectivity-*where-defined*, in the three-variable form `∀ x y z, m.predMap x = some z → m.predMap y = some z → x = y` (and the same on `conMap`), deliberately not `Function.Injective` on the partial `String → Option String` fields. Total injectivity would identify any two symbols mapped to `none`, forbidding a translation from leaving more than one symbol out of vocabulary; the reflection argument only ever compares two `some` images. `SymMap.id_injective` and `SymMap.Injective.comp` (closure under T9's Kleisli composition) are the two instances the examples and the composition section use.

The modal reading. The design defines `RobustlyJustified_b(w,c) := Comparable_b(w,c) ∧ w ⊨ [b]Justified(τ_b c)` and `PossiblyJustified_b(w,c) := Translatable_b(c) ∧ w ⊨ ⟨b⟩Justified(τ_b c)`. `sat_status_iff_box` and `sat_status_iff_dia` state: when every accepted `b`-successor of `w` is T8-related to `w` (`hall`) and there is at least one such successor (`hreach`), the local status atom at `w` is equivalent to its boxed and to its diamonded translation at the successors, for every status `s`, not only `justified`. In the design's vocabulary, the translatability hypothesis `trAtom B.sym c = some c'` is `Translatable` and `hreach` is `Reachable`; `Comparable` is discharged by the same hypotheses. `sat_status_iff_box_src` is the same equivalence under the source valuation, through T4 (`sat_src_iff_cmp`) on both sides.

The executable cell is `Examples.PW.Status.t8_box_defeated_r`, at the two-context `bridgeDataR` whose single accepted edge is `wS2 → wR2`: `wS2 ⊨ Defeated(p) ↔ wS2 ⊨ [b] Defeated(p_r)`, the `RobustlyJustified` shape at `defeated` with the guard discharged. `t8_box_defeated_r_holds` then shows the left side is true, so the box is inhabited rather than vacuous.

Composition. Statuses are values. Preservation along a path of status bridges is `Eq.trans` of the per-edge `status_transport` instances, together with the per-edge canonicalizer equalities (`hcanon`); no path-indexed status theorem is needed and none is declared. What needs proving is that the *hypotheses* compose, and `PW.StatusBridge.comp` proves it: the T9 composite bridge of two status bridges is a status bridge, through a chosen intermediate world. T9's intermediate-world dependence is kept, not erased: the intermediate world is an explicit argument, and `corr_comp_iff` (`Corr` along the composite factors through it) needs only the first leg's `Admits`, so that the intermediate term is an intermediate *argument*. `SymMap.Injective.comp` carries injectivity along.

The two layers' composition operators take their legs in opposite orders: `StatusBridge.comp h₁ h₂` and `SymMap.Injective.comp h₁ h₂` take their legs in *path* order, first leg first, while T9's `StructuralBridge.comp B₂ B₁` and `SymMap.comp m₂ m₁` take them in *function-composition* order. The composite `StatusBridge.comp h₁ h₂` is stated over `m₂.comp m₁` and `lm₂ ∘ lm₁`, so the two conventions meet at the type.

T8's four guarantees and their declarations. Lean proves status preservation from explicit structural correspondence: `PW.status_transport` (T8), with `PW.statusC_of_bisim` and `PW.statusC_of_iso` as the generic core over an explicit relation, live at `Examples.PW.Status.t8_justified_preserved`, `t8_defeated_preserved`, `t8_gap_preserved`, and the modal cell `t8_box_defeated_r`. The hypotheses exclude unmatched target attackers and supports: `StatusBridge.matched` (no target argument is unmatched) and `StatusBridge.back` (no target attacker is unmatched); the T7 target fails `matched` at `leaf l2` (`t7_unmatched`, `t7_not_statusBridge`), and `t7_forward_hom_insufficient` retains the forward-homomorphism counterexample. The result preserves all four aggregated statuses without treating them as argument labels: `status_transport` is an equation between `cmpStatus` values (`Grounded.statusC` over `Claim.support`) proved through `statusC_congr`, which reads a claim only through emptiness of its support and, per label, existence of a support argument with that label; no status is ever a label of an argument, and `srcStatus_transport` restates the equation at the source observation. And the theorem does not strengthen T6 implicitly: every theorem takes `StatusBridge` (or an explicit `SupportCorr`) as an additional hypothesis, and `Examples.PW.t7_t6_boundary` still shows `Admits` alone flips status.

The limits of the status contract:

1. **The frozen attack clauses are index-level, with a declared-attack route above them.** `StatusBridge.forth`/`back` are the frozen hypotheses, stated on the compiled edge decider `Compile.edgeB`, over argument indices, which is the AF-level correspondence the design states, so a reader should not mistake them for structural conditions on the source language. A declared-attack derivation exists as a stricter layer, and it takes more machinery than the frozen clause: deriving it needs `trSupport` to commute with `Attack.subterm`, `Compile.Contains`, `Compile.AttackOcc`, and `coveredB`, an `Erase.lean`-scale lemma set over a partial map.

   `AttackBridge` (`Lara/PW/AttackTransport.lean`) states the attack hypotheses on declared `atts` via `trAttack`, and `AttackBridge.toStatusBridge` derives the index-level `forth`/`back` clauses from them; the commutation ladder mirrors `Erase.lean` over the partial map. The route additionally assumes `Function.Injective lm`, which the frozen `StatusBridge` contract does not, because injectivity is load-bearing when `containsB` compares subterms by `decide (v = t)` (`Lara/Compile.lean:120-123`), so a collapsing leaf map makes two distinct source subterms translate equal. The general, injectivity-free index-level statement therefore still stands; `AttackBridge` supplies a bridge-contract-level sufficient condition for it, witnessed at `Examples.PW.Attack.*`.
2. **`status_transport` needs an injective translation.** A merging translation breaks the reflection half of `claimSupport_corr`. Non-injective bridges use `status_transport_of_corr` and supply the support correspondence themselves.
3. **The executable `StatusBridge` checker is fixture-scale.** `statusBridgeB` and its sound/complete pair (`Lara/PW/StatusCheck.lean`) put each conformance cell at one `decide`, and the T7 negative is refuted through completeness. But `bisimScanB` nests three `List.range.all` scans plus an inner `List.range.any` witness scan, so the decider is `O(n²m²)` kernel steps, and each step recomputes a full `trSupport` traversal inside `corrB` and a `coveredB` scan over `atts` inside `edgeB`. It runs in the kernel, `decide` only, `native_decide` banned repo-wide. That is free on the T8 conformance fixtures and it is the only scale this decider is for. Pointing it at a program with a realistic argument count will not reduce in practical time. Hoisting `trSupport` out of `corrB` would remove that cost but changes `corrB`'s shape, so `corrB_iff` and both halves of `statusBridgeB_sound`/`_complete` would have to be re-proved.
4. **T6 limitations 1, 2, and 5 are inherited.** Symbol translation remains bridge-global and functional, the leaf map remains total, and question keys remain frozen across the bridge.
5. **All four statuses have an executable transport cell, `contested` included.** `t8_contested_preserved` and `t8_contested_cells` are evaluated cells because `checkUnit` admits symmetric contraries here: `Policy.WellFormed` constrains only strict-reachable rule conclusions, and the `polS3`/`polR3` policies have no rules. No status is left merely covered by the theorem.

## Path composition

Composition is first-leg-first Kleisli composition. For partial symbol maps, `SymMap.comp m₂ m₁` denotes τ₂ ∘ τ₁: apply `m₁`, then apply `m₂` to the result. The lifted `trX_comp` laws are theorem-level bind equations, not reduction rules or definitions of the lifts. `StructuralBridge.comp B₂ B₁` uses the same order, composes the total leaf maps as `B₂.leafMap ∘ B₁.leafMap`, and chains each bridge-contract clause through the chosen middle checking environment.

The following diagram fixes both the typed endpoints and the flow direction. `Eᵢ` abbreviates one checking environment over the shared canonicalizer.

```text
E₀  -- B₁ : (m₁, lm₁) -->  E₁  -- B₂ : (m₂, lm₂) -->  E₂
 |                              |                              |
 t -- trSupport m₁ lm₁ --> some t' -- trSupport m₂ lm₂ --> some t''

composite E₀ -> E₂:  B₂.comp B₁
symbol map:            m₂.comp m₁       (τ₂ ∘ τ₁)
leaf map:              lm₂ ∘ lm₁
```

Paths are first-class indexed data. `BridgePath` is indexed by its source and target policy, evidence, and certificate environments and lives in `Type 1`, because `.cons` quantifies over an intermediate environment. A path therefore retains its chosen intermediates rather than existentially erasing them. `BridgePath.compose` folds the path into a named structural bridge from `StructuralBridge.refl` at `.nil`.

This fold equation explains why the first edge remains the first translation even though the recursive composite appears on the left of `.comp`.

```text
compose(nil) = refl

compose(cons b rest)
  = compose(rest).comp b
  = first run b, then run every edge in rest
```

`BridgePath.trans` is the corresponding stepwise Kleisli chain of partial support maps. `BridgePath.trans_eq_compose` proves that this stepwise chain is the support map induced by the folded bridge.

Every public theorem declared by `Lara/PW/Compose.lean` appears in the first table. Definition rows are included to identify the objects those theorems constrain.

| Result | Declaration |
|---|---|
| First-leg-first partial symbol composition and its two unit laws | `PW.SymMap.comp`; `PW.SymMap.id_comp`, `PW.SymMap.comp_id` |
| Term and term-list bind laws | `PW.trTerm_comp`, `PW.trTerms_comp` |
| Atom and atom-list bind laws | `PW.trAtom_comp`, `PW.trAtoms_comp` |
| First-edge and intermediate-edge atom gaps remain composite gaps | `PW.trAtom_comp_none_left`, `PW.trAtom_comp_none_mid` |
| Pattern and pattern-list bind laws | `PW.trPat_comp`, `PW.trPats_comp` |
| Atomic-pattern and atomic-pattern-list bind laws | `PW.trAPat_comp`, `PW.trAPats_comp` |
| Substitution bind law | `PW.trSubst_comp` |
| Support, support-list, and discharge-list bind laws | `PW.trSupport_comp`, `PW.trSupportList_comp`, `PW.trSupportDis_comp` |
| Question and question-list bind laws | `PW.trQuestion_comp`, `PW.trQuestions_comp` |
| Rule bind law | `PW.trRule_comp` |
| Binary structural-bridge composition | `PW.StructuralBridge.comp` |
| Explicit two-stage applicability predicate and exact factorization | `PW.AdmitsSteps`; `PW.admits_comp`, `PW.admits_steps_of_intermediate` |
| Binary transport with intermediate and final judgments exposed | `PW.support_transport_comp` |
| Indexed paths, their fold, and their stepwise partial support map | `PW.BridgePath`, `PW.BridgePath.compose`, `PW.BridgePath.trans` |
| Equality of stepwise and folded transport | `PW.BridgePath.trans_eq_compose` |
| Direct/path commuting contract and exact map-equality characterization | `PW.Commutes` (fields `atom_eq`, `support_eq`); `PW.Commutes.of_maps_eq` |
| Map equalities extracted from a commuting direct/path pair | `PW.Commutes.leafMap_eq`, `PW.Commutes.predMap_eq`, `PW.Commutes.conMap_eq`, `PW.Commutes.sym_eq` |
| Direct and path transport agree on a checked source support | `PW.direct_transport_agrees` |
| Rule and admitted-leaf translations pinned by common target typing | `PW.commutes_on_rules`, `PW.commutes_on_leaves` |
| Direct/path checker-tied applicability equivalence | `PW.admits_iff_of_commutes` |
| Full accepted edge as caller relation conjoined with checker applicability | `PW.Accepted`; `PW.accepted_iff_of_commutes` |
| T9 path theorem for an arbitrary chosen exact path | `PW.path_support_transport` |

The following facts in `Lara/Examples/PWCompose.lean` are the substantive conformance witnesses, all `AxCheck.lean`-gated.

| Witness | Declaration |
|---|---|
| Live second rename and concrete two-edge path | `Examples.PW.Compose.ren2Sym`, `bridgeRen2`, `pathRen`, `bridgeRenDirect`, `wRenTgt2`; `ren2_conclusion`, `ren_path_trans`, `ren_path_transport` |
| Positive direct/two-edge commuting triangle and checked transport agreement | `Examples.PW.Compose.ren_path_commutes`, `ren_direct_transport_agrees` |
| A real three-edge path with a positive triangle and transport agreement | `Examples.PW.Compose.pathRen3`; `ren_path3_commutes`, `ren_path3_transport_agrees` |
| Binary theorem path with the intermediate and final checked judgments visible | `Examples.PW.Compose.ren_support_transport_comp` |
| Common-target consequences and map equalities on the live rename | `Examples.PW.Compose.ren_commutes_on_rule`, `ren_commutes_on_leaf`, `ren_commutes_on_symbol_maps` |
| Inhabited identity applicability and a chosen intermediate world | `Examples.PW.Compose.bridgeIdT7`, `pathIdT7`; `admitsSelfT7`, `t7_admits_steps_of_intermediate` |
| Both directions of composite applicability and an inhabited result | `Examples.PW.Compose.t7_admits_comp_iff`, `t7_admits_composite` |
| Positive identity direct/path triangle and applicability equivalence | `Examples.PW.Compose.t7_identity_path_commutes`, `t7_admits_iff_of_commutes` |
| Candidate-relation premise, accepted-edge equivalence, inhabitation, and negative separation | `Examples.PW.Compose.candidateDirectT7`, `candidatePathT7`, `candidatePathFalseT7`; `t7_candidate_relations_agree`, `t7_accepted_iff_of_commutes`, `t7_accepted_inhabited`, `t7_accepted_needs_candidate_coherence` |
| Negative triangle caused by a different leaf renaming | `Examples.PW.Compose.bridgeSwap`, `twinIdentityPath`; `direct_ne_composed_support` |
| Negative triangle caused only by different predicate translation | `Examples.PW.Compose.claimOnlySym`, `claimOnlyBridge`, `claimIdentityPath`; `direct_ne_composed_claim` |
| Non-vacuous certificate acceptance through two live bridge legs | `Examples.PW.Compose.certCertTgt2`, `bridgeCert2`, `certCompBridge`; `certComp_two_live_legs` |
| Real atom, support-transport, and context-tied applicability vocabulary gaps | `Examples.PW.Compose.gapSym`, `gapBridgeRen`, `gapBridgeRen2`, `gapBridgeDrop`, `gapPath`, `gapSupportPath`; `mid_path_out_of_vocabulary`, `mid_path_translationUndefined`, `mid_path_support_undefined`; `gapConFirstBridge`, `gapConDropBridge`, `gapAppContext`, `gapAppWorld`, `gap_admits_comp_fails` |
| Nonempty lifted-map computations and their concrete inputs and outputs | `Examples.PW.Compose.substRenSrc`, `substRenTgt`, `substRenTgt2`, `patRenSrc`, `patRenTgt`, `patRenTgt2`, `questionRenSrc`, `questionRenTgt`, `questionRenTgt2`, `supportDisRenSrc`, `supportDisRenTgt`, `supportDisRenTgt2`; `trSubst_nonempty_computes`, `trPat_nonempty_computes`, `trQuestions_nonempty_computes`, `trSupportDis_nonempty_computes` |
| First-leg atom gap witnessed both computed and via the law | `Examples.PW.Compose.first_leg_gap_computes`, `first_leg_gap_law` |
| Unit laws pinned at a non-identity partial map | `Examples.PW.Compose.id_comp_ren2`, `comp_id_ren2` |

The three-edge witness is genuinely a `BridgePath` with three `.cons` constructors: the two live rename edges are followed by a reflexive edge in the final environment. Its positive triangle and transport theorem establish that the path-level statements are not merely a binary encoding.

Pinned consequences, not commuting premises. `Commutes B P` has exactly two fields. The diagram shows one named direct bridge against an arbitrary chosen path with the same endpoints and labels those two induced-map equalities.

```text
                         B
                    +----------+
                    |          v
source environment  |     target environment
                    |          ^
                    +-- b₁ ... bₙ --+
                         path P

Commutes.atom_eq:    trAtom B.sym a
                   = trAtom P.compose.sym a

Commutes.support_eq: trSupport B.sym B.leafMap w
                   = P.trans w
```

`commutes_on_rules` is a consequence of the two bridges' `rule_ok` clauses: when a source rule is present at a shared rule id, both routes must put its translation at that same id in the common target policy, so the translations cannot disagree there. `commutes_on_leaves` is a consequence once the direct and composite leaf maps agree at an admitted source leaf: their `leaf_ok` clauses and the common target evidence environment then pin the translated atom. Neither theorem is an input to `Commutes`, and neither discharges one of its fields.

The negative witnesses identify the two fields' independent content. In `direct_ne_composed_support`, a valid bridge swaps equally typed leaves while the competing path leaves them fixed. In `direct_ne_composed_claim`, the direct bridge and path have equal leaf and constructor maps and agree on a constructor-bearing support translation, but their predicate translations differ. The latter fixture uses empty policy and evidence environments so no typing clause can introduce a second disagreement.

`Commutes.leafMap_eq` extracts pointwise equality of the direct and folded leaf maps from `support_eq`; `Commutes.predMap_eq` extracts predicate-map equality from `atom_eq`. Support terms also expose constructor translation directly: an `.inst` substitution containing `.con k ...` lets `Commutes.conMap_eq` extract constructor-map equality from `support_eq`. `Commutes.sym_eq` combines the predicate and constructor results. Consequently `Commutes.of_maps_eq` is an iff: this `Commutes` contract is exactly full symbol-map and leaf-map equality, not a weaker observational triangle.

Applicability and acceptance. `Admits m lm w u` remains T6's checker-tied `accept` discipline: every program argument in `w` has a defined translated support term that belongs to `u`'s program. It is not, by itself, the outer model's full accepted-edge relation.

For a binary bridge composite, `AdmitsSteps B₂ B₁ w u` exposes a chosen intermediate support term for every source program term and requires the two translations and final membership. `admits_comp` is the exact iff between `Admits (B₂.comp B₁)` and that two-stage translation/membership condition. `admits_steps_of_intermediate` supplies the step predicate from two admitted legs through an explicitly chosen middle world; the converse of `admits_comp` does not reconstruct such a world.

`gap_admits_comp_fails` exercises the failure direction on a checked world. Both bridge types use that world's actual policy lookup, evidence environment, and certificate relation at their endpoints. The first bridge renames a constructor inside an instance substitution, the second bridge omits that image, and both `AdmitsSteps` and composite `Admits` are false.

`admits_iff_of_commutes` says a commuting direct bridge and path have the same checker-tied applicability because their support maps agree. The full relation is instead `Accepted R m lm w u = R w u ∧ Admits m lm w u`: a caller-owned candidate relation conjoined with checker-tied applicability. Accordingly, `accepted_iff_of_commutes` requires both `Commutes` and a separately supplied pointwise equivalence between the direct and path candidate relations. The T7 examples prove the candidate premise, applicability, and inhabitation separately before combining them; `t7_accepted_needs_candidate_coherence` keeps the bridges commuting and applicability true while a false path candidate relation makes the path edge unaccepted.

Intermediate-world dependence. All path theorems are per chosen `BridgePath`; equal endpoints do not identify different paths. `support_transport_comp` returns both the intermediate and final checked `HasSupport` judgments, so the middle environment remains in the evidence. `admits_steps_of_intermediate` takes the intermediate world as an explicit argument. At path level, `BridgePath.trans_eq_compose` states that the final partial support map is the map obtained through that chosen path's fold. It does not assert that every path between the same endpoints induces the same map.

The mid-path failure case makes that dependence observable. Here the first edge succeeds on `a`, but the second edge has no translation for the running image `a'`; partiality propagates through the fold and comparison reports an incomparability reason, never a local status.

```text
a -- trAtom m₁ --> some a' -- trAtom m₂ --> none
\________________ trAtom (m₂.comp m₁) ________________/ = none

none -- crossCompare --> incomparable(translationUndefined)
                         (not justified/defeated/both/neither)
```

`Examples.PW.Compose.mid_path_out_of_vocabulary` realizes this with `e` translating to `e_r` on the first edge and `e_r` missing on the second. `mid_path_translationUndefined` then derives `.incomparable .translationUndefined` through the comparison API.

Every result here concerns exact `StructuralBridge` paths. Nothing generalizes these theorems to approximation bridges. Approximate composition needs its own domains, observables or comparison spaces, and error and convergence laws; none is smuggled into `Commutes`, `Admits`, or path transport.

The limits of the path contract:

1. **There are no bridge-level associativity or unit equalities.** `SymMap` has `id_comp` and `comp_id`, but T9 does not identify differently nested `StructuralBridge.comp` values. Semantic path flattening is expressed by `BridgePath.trans_eq_compose`, per chosen path.
2. **Paths retain T6 limitations 1, 2, and 5.** Symbol translation remains bridge-global and functional, the leaf map remains total, and question keys remain fixed.
3. **Endpoint equality is not path independence.** Different chosen paths may induce different translations; `Commutes` is the explicit agreement needed to compare a named direct bridge with one path.
4. **Status along a path is a composition of layers, not a T9 theorem.** Checked-support preservation along paths is T6 composed by T9. Status preservation along such paths is T8's `status_transport` composed along the T9 composite: `PW.StatusBridge.comp` composes the attack-correspondence hypotheses through a chosen intermediate world, so status along a path is `Eq.trans` of the per-edge instances together with the per-edge canonicalizer equalities. T9 states no status theorem itself, by design.
5. **Approximation remains out of scope.** The exact boundary above is a separate theory problem, not an omitted case of structural composition.

## Sorted queries and the outer surface

The sorted layer has two halves: `Query_κ` well-sortedness, where per-context queries are well-sorted claims over `Σ_κ` and the executable layer has a posing stage that runs before any world is consulted; and surface syntax for the outer language, authoring forms for declaring a bridge and posing a modal query.

The sorted layer redefines nothing local and nothing in the outer model. `PW.Frame`, `PW.Sat`, `PW.crossCompare`, `PW.CrossResult` and `PW.IncomparabilityReason` are shared unchanged. The refinement is a second frame *builder* plus a strictly earlier guard, and `PW.Sorted.sat_erase` proves the two models agree.

A query is a claim its context's signature can state. `PW.Sorted.Query sg` is the subtype `{c : Atom // Sigma.WellSorted sg c}`, the *existing* `Sigma` judgment (result 13), not a second one. An ill-sorted query is therefore *unrepresentable*, since `Subtype.mk` demands a `WellSorted` proof, which is a stronger guarantee than a hidden constructor. `PW.Sorted.pose` is the sanctioned *decision procedure* over that type: it either returns a query or names which of exactly two conditions stopped it.

The two query faults are the two arms of `Sigma.wsAtom`, and no more. `undeclaredPredicate` is *out of vocabulary* (the head is not in `Σ_κ`); `illSortedArguments` is *ill-sorted* (the head is declared, the argument list fails its declared sort vector, arity included, arity being the length of that vector). `not_wellSorted_iff_exists_fault` proves they exhaust ill-formedness, and `queryFault_pred` proves a fault is *located*: it names the atom's own head predicate. That is the discipline `Sigma.sigmaFault` already follows.

For a well-sorted query `gap` has exactly one meaning, and it is a theorem. `cmpStatus_gap_iff_not_addresses` reads the compiled observation's `gap` off one condition: the world declares no complete argument concluding the claim. The proof is `Grounded.statusC_gap_iff` instantiated at the world, with no new definition, and `srcStatus_gap_iff_not_addresses` says the same for the relational source observation, through T1.

The refined report is a partition, not a new answer. `PW.Sorted.report` has four constructors (`outOfVocabulary`, `illSorted`, `unaddressed`, `observed`), each pinned to exactly its condition. `report_ne_observed_iff_gap` proves that at a `SortedWorld` the three non-`observed` reports are exactly the atoms the outer model answered `gap` for, so the refinement splits one report and moves no other.

`SortedWorld` is a real hypothesis, not a formality. `Gamma` is a checker *parameter*, so an admitted evidence leaf can carry an atom outside `Σ_κ`; at such a world an ill-sorted atom could be `justified`, and the refinement would be changing an answer rather than splitting one. The condition is stated where it is used. `sortedWorld_of_nodes` discharges it from a finite check on the retained nodes whenever `canon = id`.

Every fault is located, including the bridge's. `queryFault` names the offending head predicate, and `PW.Sorted.vocabFault`, `trAtom`'s own traversal, names the first symbol a bridge's map cannot carry, in whichever of the two namespaces it falls (`OutOfVocabulary.pred` / `.con`). `vocabFault_eq_none_iff` proves the scan is exactly `trAtom`'s domain condition, so carrying the symbol costs nothing in the definedness theorems. That matters because a surface-declared bridge always has a finite vocabulary (`Surface.predMapOf_eq_none`), which makes this the fault most likely to reach an author.

Posing is world-independent, and that is the point. `notPosable_world_independent` proves the three bridge-level posing faults give the same verdict for *any* candidate list, acceptance predicate and status function, including at a target context with no worlds at all. This is what stops a vocabulary or sorting mismatch from being read as "the target field considered this and found it unsupported".

The bridge translation is derived from a symbol map, not a free field. `PW.Sorted.SortedBridgeData` carries `sym : B → SymMap` (T6's), and `PW.Sorted.trQuery` derives the typed partial translation: translate the symbols, then demand the result be a query of the *target* signature. So a translated claim the target field cannot state is a reported fault rather than a `gap` at a target world.

`translationUndefined` is split. The outer model's single reason conflates *outside the bridge's symbol map* with *the target field cannot state this*. `PosingFault.bridgeVocabulary` and `PosingFault.targetQuery` separate them, and the second names the offending predicate.

The surface is untyped and elaboration is a typing pass. `Surface.SForm` carries raw `Atom`s and names bridges by identifier; `PW.Form` is intrinsically typed by its context index. `Surface.elabForm` resolves and types, and its status-atom case *is* `Sorted.pose`, which is where the two halves meet.

One of T6's three clauses is decidable; two are not. A `Policy` carries its rules as a finite `List RuleDecl`, so `Surface.ruleOkB` decides `StructuralBridge.rule_ok` and `ruleOkB_iff` proves the decider is the clause. `leaf_ok` quantifies over `Gamma`, a function, and `cert_ok` is an arbitrary `Prop` over backends; both stay declared premises in `Surface.BridgeObligations`. The canonicalizer agreement is likewise undecidable and is a *field* of `Surface.BridgeEnv` rather than a check the elaborator pretends to perform.

Every *theorem* row below is `lean/AxCheck.lean`-gated: sorry-free, within the standard trio (`propext`, `Classical.choice`, `Quot.sound`), no `native_decide`. Rows that also name a *definition* (`structuralBridgeOf` in U4, `unelab` in U9, `SortedWorld` in S9) name it for orientation; a definition carries no `#print axioms` line of its own and is audited transitively through the gated theorems that mention it.

| # | Result | Lean |
|---|---|---|
| S1 | No fault is exactly well-sortedness | `PW.Sorted.queryFault_eq_none_iff` |
| S2 | Each fault pinned to exactly its condition | `PW.Sorted.queryFault_undeclaredPredicate_iff`, `queryFault_illSortedArguments_iff` |
| S3 | A fault is located at the atom's own head | `PW.Sorted.queryFault_pred` (the total classifier behind it is `private`: it fabricates a fault for a well-sorted atom, so only the gated report is public) |
| S4 | The two faults exhaust ill-formedness | `PW.Sorted.not_wellSorted_iff_exists_fault` |
| S5 | Posing is sound, complete, and does not rewrite the claim | `PW.Sorted.pose_ok_iff`, `pose_error_iff`, `pose_ok_val`, `pose_val_self` |
| S6 | **`gap` means exactly "the world declares no complete argument for this"** | `PW.Sorted.cmpStatus_gap_iff_not_addresses`, `srcStatus_gap_iff_not_addresses` |
| S7 | An addressed claim never gaps; it gets a substantive status | `PW.Sorted.not_gap_of_addresses`, `status_of_addresses` |
| S8 | The refined report's four constructors, each pinned | `PW.Sorted.report_observed_iff`, `report_unaddressed_iff`, `report_outOfVocabulary_iff`, `report_illSorted_iff` |
| S9 | **The split moves no outer-model answer** | `PW.Sorted.report_ne_observed_iff_gap` (hypothesis `SortedWorld`, discharged by `sortedWorld_of_nodes`) |
| S10 | The three bridge posing faults, each pinned | `PW.Sorted.crossComparePosed_sourceQuery_iff`, `_bridgeVocabulary_iff`, `_targetQuery_iff` |
| S10a | The vocabulary fault names its symbol, and the scan is exactly `trAtom`'s domain | `PW.Sorted.vocabFault_eq_none_iff`, `vocabFault_isSome_of_trAtom_none`, `vocabFaultTerm_eq_none_iff`, `vocabFaultTerms_eq_none_iff` |
| S10b | The outer model's `translationUndefined` is unreachable past the posing guard, so the split has no live rival | `PW.Sorted.crossComparePosed_ne_translationUndefined`, `crossCompare_some_ne_translationUndefined` |
| S11 | **A posing fault consults no world** | `PW.Sorted.notPosable_world_independent` |
| S12 | A fault carries no `Status`, structurally | `PW.Sorted.notPosable_ne_compared` |
| S13 | Where the outer model answered, the refined interface returns its answer | `PW.Sorted.crossComparePosed_compared` |
| S14 | T4 and valuation coherence at the sorted frame | `PW.Sorted.sat_src_iff_cmp`, `cmpVal_functional`, `cmpVal_total`, `srcVal_functional`, `srcVal_total` |
| S15 | **Conservativity: the sorted and outer models satisfy the same formulas** | `PW.Sorted.sat_erase`, `sat_erase_src` |
| U1 | The declared symbol map is undefined outside its declaration | `PW.Surface.predMapOf_eq_none` |
| U2 | **`ruleOkB` decides `StructuralBridge.rule_ok`** | `PW.Surface.ruleOkB_iff` |
| U2a | The clause-completeness check quantifies over the `Clause` *type*, not over a maintained list | `PW.Surface.Clause.mem_all`, `find?_missing_none_iff` |
| U3 | Bridge declarations: sound, complete, deterministic, with the judgment stating T6's `rule_ok` verbatim, so the trio is not bookkeeping over the decider | `PW.Surface.elabBridge_sound`, `elabBridge_complete`, `elaboratesBridge_deterministic` |
| U4 | **Preservation: a derivable declaration is T6's contract** | `PW.Surface.elabBridge_preserves`; the contract is carried by the *type* of `structuralBridgeOf`, exercised at a fixture by `Examples.PWSurface.bridgeDeclOK` with `obligations_declOK` discharged |
| U5 | **T6 at a surface-authored bridge**, concluding in the target's own judgment | `PW.Surface.elabBridge_support_transport`, instantiated at `Examples.PWSurface.support_transport_declOK` |
| U6 | Reflection | `PW.Surface.elabBridge_reflects` |
| U7 | Names identify frame indices, and resolution round-trips in both directions so an error report echoes the spelling the author wrote | `PW.Surface.Naming.ctxName_inj`, `bridgeName_inj` (premises `ctxName_of_ctxOf`, `bridgeName_of_bridgeOf`) |
| U8 | Modal queries: sound, complete, deterministic, with the judgment stating that the typed query carries the authored claim, not that `pose` succeeded | `PW.Surface.elabForm_sound`, `elabForm_complete`, `elaborates_deterministic` |
| U9 | **Preservation: the typing pass renames nothing** | `PW.Surface.elaborates_preserves` (round trip `unelab ∘ elab = id`) |
| U10 | Reflection, and the other round trip | `PW.Surface.elaborates_reflects`, `elabForm_unelab` |
| U11 | Posing resolves the context name | `PW.Surface.elabPosed_ok_iff` |

Mechanized results about a refinement are worth little without a case where the refinement fires, so the headline fixture is one world at which the outer model reports `gap` three times for three different reasons (`lean/Lara/Examples/PWSorted.lean`). It reuses the overlapping-fields pair unchanged, `sigmaEx` declares `p`, `q`, `s` and `sigmaOverlap` declares `p`, `q`, `r` and not `s`, because that pair exists precisely to make "neither vocabulary contains the other" concrete, and `overlap_local_gap` already pins the outer-model answer being refined.

At `wOverlap`, whose single admitted argument concludes `q`:

| authored claim | outer model (`cmpStatus`) | refined (`report`) |
|---|---|---|
| `p()` | `gap` | `unaddressed` |
| `s()` | `gap` | `outOfVocabulary "s"` |
| `q(z)` | `gap` | `illSorted "q"` |
| `q()` | `justified` | `observed justified` (unchanged) |

`reports_distinct` proves the three are pairwise distinct and `split_not_change` proves all three are still outer-model `gap`s, so the split is real *and* is a split.

At the bridge, `sorted_s_targetQuery` is the sharpened form of `overlap_translationUndefined`, and `bridge_and_target_faults_distinct` pins that the two conditions the outer model does not tell apart differ, as an inequality between two `crossComparePosed` applications rather than between two constructors. `sorted_t_targetIllSorted` closes the target fault's other branch (a predicate declared at *both* ends with different arities, which a vocabulary-membership test would pass), and `sorted_t_bridgeVocabulary_con` closes the vocabulary fault's constructor namespace.

For the surface (`lean/Lara/Examples/PWSurface.lean`), the bridge fixture declares a policy with a *rule*, so `ruleOkB` is not vacuous: `rule_clause_holds` is the positive cell, and there is one negative cell per way the clause can fail (the target carries nothing at the identifier, `rule_clause_fails`; the target carries a *different* rule there, `rule_clause_fails_mistranslated`; and the declared map cannot translate the source rule at all, `rule_clause_fails_untranslatable`).

The fixture's two contexts carry a `Gamma` pair **inside the declared vocabulary**, so `obligations_declOK` *discharges* `BridgeObligations` instead of assuming it: `bridgeDeclOK` is a real `PW.StructuralBridge` at a concrete declaration, and `support_transport_declOK` carries a checked support across it into the target field's own judgment, with U4 and U5 exercised, not merely stated. `elabBridge_nameMismatch` / `_sourceMismatch` / `_targetMismatch` show the declaration's own names are read.

`elab_illSorted` is the fixture that joins the two halves: an ill-sorted authored claim is a typing error at authoring time, named and located, where the outer model sends it to a world and reports the `gap` that comes back. `elab_sourceMismatch` exercises the typing of the modality itself, rejecting `⟨b⟩` read from the wrong field, and `elabPosed_unknownContext` the one step `elabPosed` adds over `elabForm`.

For a well-sorted query, `Addresses w c` means that the world has nonempty complete support for `c`; it does not mean merely that an author declared or attempted the claim. Every retained AF node is complete, but an accepted `Unit.CheckedUnit` can also retain located holes outside the AF. `PW.Sorted.not_gap_of_addresses` therefore excludes `gap` only when complete support exists. With incomplete-only support, the claim still reports `gap`; with complete support, grounded labeling selects `justified`, `defeated` or `contested`.

The current PW status projection cannot distinguish an incomplete-only attempt from an absent argument. `Consistency.completeClaimFor` builds the claim from complete support and leaves its legacy `holes` field empty; the checked unit's separate located-hole report is not part of this observation. Exposing that report would extend the outer observation contract. The sorted layer separates vocabulary and sorting faults, but it does not close this remaining information gap.

What the sorted layer deliberately does not contain: an edit to `PW.Frame`, `PW.Sat`, `crossCompare`, or `CrossResult` (the outer model's contract; the refinement is a second builder and an earlier guard, and `sat_erase` relates them); `holes(P, p)` at the instance layer; edge-dependent (configuration) translation, which stays bridge-global exactly as `Frame.translate` is; `StructuralBridge.refl` as a surface declaration, since `SymMap.id` is total and no finite entry list is (`predMapOf_eq_none`), a boundary of the authoring form rather than of the model; and a decided `leaf_ok`, `cert_ok`, or canonicalizer agreement, all undecidable since `Gamma` and `canon` are functions and `CertOk` is an arbitrary `Prop`, so they are declared premises named where used.

## Declared bridges and the wire contract

A checked registry derives both the frame's bridges and query-name resolution from the declarations, and a file-driven Lean example evaluates modal queries and runs source-claim comparisons through those same bridges. `Lara/PW/Declared.lean` adds `Surface.Declared.Host`, `Resolved`, and `Registry`. The host supplies context identities, their checking environments, and explicit canonicalizer agreement. `resolve` resolves both endpoints and runs the existing `elabBridge`. A `Resolved` value retains the original declaration and its `ElaboratesBridge` proof. `load` processes declarations in order and rejects a repeated bridge ID, an unknown endpoint, a missing clause, or a failed rule check.

Frame bridge indices are names whose registry lookup succeeds. Both the frame symbol map and `Naming.bridgeOf` come from that lookup. They cannot independently choose different meanings for a name. `Registry.coherent` also ties the declared source, target, and evidence-leaf map to the resolved bridge.

`load_declarations` proves that a successful load retains exactly the input list, in order. `elabPosed_declared` then proves that **every modal occurrence** in a successfully elaborated posed query, including nested occurrences, resolves to an original declaration from that list with precisely the frame's symbol map. `elabForm_declared` gives the same result before the outer context is resolved.

The low-level `Naming` and `BridgeEnv` APIs remain useful for hand-authored models. The stronger guarantee applies when callers use the checked registry.

The wire contract `pw-surface` version 1 is one S-expression:

```text
(pw-surface 1
  (bridges
    (bridge BRIDGE_ID SOURCE_CONTEXT TARGET_CONTEXT
      (symbols (pred SOURCE TARGET)* (con SOURCE TARGET)*)
      (leaves (leaf SOURCE TARGET)*)
      (clauses CLAUSE*)))
  (queries (pose CONTEXT FORM)*))
```

The stars describe repetition, not literal input. There may be any number of bridge declarations. Predicate and constructor entries may be interleaved; the decoder preserves their original order. All sections occur exactly once, in the displayed order. Empty bridge/query lists are valid.

```text
FORM   ::= (status STATUS ATOM) | (top) | (not FORM) | (and FORM FORM)
         | (box BRIDGE_ID FORM) | (dia BRIDGE_ID FORM)
STATUS ::= gap | justified | contested | defeated
CLAUSE ::= leaf-ok | rule-ok | cert-ok
ATOM   ::= (atom PREDICATE TERM*)
TERM   ::= (num TEXT) | (str TEXT) | (con CONSTRUCTOR TERM*)
```

Identifiers and literal payloads are S-expression atoms. The existing `Lara.Driver` reader/printer supplies quoting and escapes. Bare atoms use printable ASCII excluding parentheses, semicolon, quote, and backslash; empty or other text is quoted. Quoted text accepts `\"`, `\\`, and `\n`; other escape sequences are rejected. Unicode is preserved. Whitespace and semicolon comments are accepted; a second top-level expression is rejected. The canonical printer puts one space between list elements and adds no line breaks. Inside quoted atoms it escapes only `"`, `\`, and newline, so a tab, carriage return, or NUL in a name is printed raw.

Numeric term payloads retain their authored text, as the existing `Atom` AST requires. No numeric normalization happens in this codec. Version `1` is exact; `01` and other versions are rejected. The decoder reads the version before the section layout, so a later version reports `unsupported-version` even when its sections differ from version 1's. Fixed tokens use closed types with one spelling table. `num`, `str`, `con`, and `atom` encode the same `Term`/`Atom` shape as the inner checker wire, so `Wire.Tag` takes those four spellings from `Lara.Driver.tagToString`; renaming one there renames it here. Domain names become the existing distinct identifier types.

`Wire.Document` contains lists of `BridgeDecl` and `Posed`. The structured codec preserves every list, including duplicates. First-match symbol and leaf map semantics therefore remain unchanged. Duplicate *bridge IDs* are rejected by the loader, not erased or normalized by the codec. Repeated clause entries are retained; the existing elaborator checks that all required clauses occur.

`decodeDocument_encode` proves `decodeDocument (encodeDocument d) = .ok d`, with corresponding proofs for each nested AST type. `encodeDocument_injective` proves that distinct documents cannot share an encoding. These theorems cover structured S-expression trees. The existing byte reader/printer is a **tested boundary**, not a newly verified textual parser. Executable round trips cover all constructors, escaping, Unicode, and malformed input.

Wire failures have stable categories `syntax`, `malformed`, and `unsupported-version`. Syntax diagnostics preserve reader line/column detail. Other detail text explains the failed constructor; consumers should branch on the category, not parse the detail string. Loading and query elaboration have separate typed errors, preserving the offending names and query faults.

From the repository root:

```sh
(cd lean && lake build pw-example)
lean/.lake/build/bin/pw-example fixtures/pw/declared.sexp
python3 scripts/check-pw-example.py
```

The host in `Examples/PWFileHost.lean` supplies `src` and `tgt` contexts, reusing the checked `wT7src` and `wOverlap` worlds. Each context has one selected world. Every bridge's candidate relation selects the target context's world, and the host's acceptance predicate is true. The file supplies all bridge declarations and posed formulas; those are not hardcoded into the executable.

The bundled file returns:

```text
(pw-example-result 1 (queries true true true) (comparisons (comparison b (atom q) (comparable justified))))
```

Query answers occur in input order. Separately, the example compares the explicit source probe `q()` through each declared bridge, also in input order. The probe is printed beside the result. Changing the file's `q → q` map to `q → p` changes that comparison from `justified` to `gap`, while its modal query about target `q()` stays true. Removing the map reports `not-posable (bridge-vocabulary ...)`, not `gap`.

This separation is semantic: primitive `box` and `dia` evaluate their operands as written in the target context. They never implicitly translate them. `compareProbe` is the separate `crossComparePosed` operation that translates a source claim using the frame's exact declared symbol map.

Exit 0 means the document executed. A false modal answer or tagged incomparability is a result, not a process error. Exit 1 means wire decoding (`syntax`, `malformed`, or `unsupported-version`), loading, elaboration, file access, or command usage failed. Both paths print a single S-expression; error envelopes begin `pw-example-error 1`. The example result protocol is separate from `pw-surface` input and the local checker wire format.

## Finite execution

`Lara/PW/Finite.lean` adds a finite presentation of accepted successors and a Boolean evaluator for the existing grammar. Its `mem_successors` premise states that list membership is exactly the frame's accepted relation. `evalFinite_iff` proves agreement with unchanged `PW.Sat` under the host's Boolean observation. The example discharges this premise and `PWFileHost.evaluates_iff` connects its observation to `Sorted.cmpVal` over real checked worlds.

This does not assert that every abstract frame has an executable enumeration. Empty lists give vacuously true boxes and false diamonds. Duplicates do not change Boolean answers. The fixture suite exercises both cases and nesting.

The loader checks T6's rule clause, exactly as `elabBridge` does. `Examples.PWDeclared.rule_rejected` shows a load failing that check. In the file example it is vacuous: both host policies (`polT7`, `polOverlap`) have no rules, so every file map passes. Listing `leaf-ok` and `cert-ok` does not prove them: evidence-leaf and certificate transport, and the host's canonicalizer agreement, remain supplied premises (see [Trusted boundaries and unproved obligations](#trusted-boundaries-and-unproved-obligations)). The example's chosen acceptance relation does not assert T6 applicability.

Finite execution leaves `PW.Frame`, `PW.Sat`, `crossCompare`, the T6 contract, and the local compiler unchanged.

## The Haskell runtime and conformance

`pw-run 1` is the Haskell runtime of the possible-world outer language. An author writes one file that declares worlds, candidate edges, bridges and queries. `lara pw` evaluates that file, and a Lean reference executable must print the same bytes. Proofs connect the Lean reference to `PW.Sat`.

```sh
cabal run -v0 exe:lara -- pw fixtures/pw/run/fields.sexp   # the Haskell runtime
(cd lean && lake build pw-run)
lean/.lake/build/bin/pw-run fixtures/pw/run/fields.sexp    # the Lean reference
cabal run -v0 exe:lara -- pw-input fixtures/pw/source/lara.sexp   # the derivation door
make pw-conformance                                         # the differential gate
```

A run file contains exactly one S-expression:

```text
(pw-run 1
  (worlds (world WORLD_ID CONTEXT_ID SOURCE)*)
  (edges (edge BRIDGE_ID SOURCE_WORLD TARGET_WORLD ACCEPTANCE)*)
  (comparisons (compare BRIDGE_ID SOURCE_WORLD ATOM)*)
  DOCUMENT)
SOURCE     ::= (inline CHECK_INPUT) | (file PATH) | (lara PATH)
ACCEPTANCE ::= accepted | rejected
DOCUMENT   ::= (pw-surface 1 ...)    ; the wire contract, unchanged
```

Stars mark repetition. The four sections occur once each, in this order, and each may be empty. `ATOM` is the `pw-surface` atom production. Version `1` is exact, and the version is read before the layout, as for `pw-surface`. Sections decode in order, and each section finishes before the next header is read. The reader, quoting and error categories (`syntax`, `malformed`, `unsupported-version`) are those of `pw-surface 1`. The embedded document goes through the wire-contract decoder unchanged, so its bridge declarations and posed queries keep their contract exactly.

A world's `CHECK_INPUT` uses the current local checker envelope (`check-input`, `lara-core@0.3`), the same bytes `lara check` reads. A `file` path is resolved relative to the run file's directory and holds those bytes. The run codec carries an envelope as an untyped tree. The envelope is decoded when its world loads, so a malformed envelope is a world failure, not a run-codec failure.

A `lara` path, also relative to the run file's directory, names a `.lara` presentation program with its co-located policy. `lara pw` elaborates it through the steps `lara check` takes on that file alone (`Lara.Source.Load`, `Lara.Elaborate.prepareSource`) and uses the envelope that elaboration binds, so a `lara` world is exactly the envelope `lara check` would have checked. The Lean reference has no surface parser: `pw-run` reports a `lara` world as `world-input` and never guesses at its meaning. The two are compared through a derivation door, `lara pw-input <run.sexp>`, which prints the same `pw-run 1` document with every world source replaced by the envelope tree it yielded, inline. The gate runs `lara pw` on the original and both drivers on the derived document, and requires one output.

The `lara` form is an additive `SOURCE` production within version `1`: a document without it means the same to every reader, `pw-result 1` and `pw-error 1` do not depend on it, and a reader without the production refuses a `lara` source as `malformed world-source`, which says precisely what it cannot read. The version changes only for a change that alters the meaning of a document an old reader accepts.

Stages run in this order, and the first refusal is the run's error:

1. **Worlds**, in declaration order. A repeated world ID is refused. Otherwise the source is read to an envelope tree and decoded. For a `lara` source, reading is elaboration, and whatever stops the program before an envelope exists (an unreadable or unparsable program or policy, a source the elaborator refuses, a policy admission stop, or a policy quarantine, whose pruned unit the frozen envelope cannot express) is `world-input`, so the fault set does not grow. An envelope with a duplicate-report group whose members disagree is refused as `world-groups W G`, naming the first such group in declaration order; groups that agree are inert. Replay preflight comes next (R13), then the unchanged checker (`checkUnit` in Lean, `checkUnitWith fullConfig` in Haskell). The checker sees the envelope's leaves, theories and queries as its ground atoms, exactly as the local drivers do. A context is created by its first world, and that world fixes the context's environment: Σ, the policy, the leaf table and the theory table. Every later world of the context must declare the same environment. Two worlds of one context may not have the same checked program: the same AF arguments, compiled attacks and located holes. The holes are part of a world's identity, so two worlds that differ only in their incomplete alternatives are both loaded. Statuses still come from complete support alone.
2. **Bridges**: `Declared.load` over the loaded contexts. It refuses a duplicate ID, an unknown endpoint, a missing clause, and a failed `rule-ok`.
3. **Edges**, in order. The bridge must exist, both worlds must exist, each world must lie in the bridge's corresponding context, and the triple (bridge, source, target) may occur at most once.
4. **Queries**: `elabPosed` against the checked registry's naming, so `elabPosed_declared` applies. Each query is answered at **every world of its context**, in declaration order.
5. **Comparisons**: the bridge must exist, and the world must exist in the bridge's source context. Then `crossComparePosed` runs over that world's declared candidates, in edge order. Accepted and rejected edges are both candidates.

A completed run prints:

```text
(pw-result 1
  (queries (query (at WORLD BOOL)*)*)
  (comparisons (comparison BRIDGE WORLD ATOM RESULT)*))
RESULT ::= (comparable STATUS+) | (incomparable REASON) | (not-posable FAULT)
```

A refused run prints `(pw-error 1 STAGE FAULT)`. `STAGE` is one of `wire`, `world`, `bridge`, `edge`, `query`, `comparison`, or `io`. The fault constructors are listed in `Lara.PW.Run.encodeError` and in its Haskell mirror. Only three faults carry runtime-specific text as their last atom: a reader's `syntax` message, `world-input` (a world that could not be read or decoded), and `io` (the run file could not be read). Consumers branch on the constructors.

Exit `0` means the run completed. A false modal answer and an incomparable comparison are results, not errors. Exit `2` means the run file could not be read or decoded. Exit `1` means a decoded run was refused. Both drivers print exactly one UTF-8 line on stdout and nothing on stderr, and both read the run-file argument and every file path as UTF-8, whatever the locale. A wrong argument count is outside the contract: `lara pw` falls through to `lara`'s usage message on stderr (exit 2), and `pw-run` prints `(pw-error 1 usage …)` (exit 2). `lara pw` therefore departs from the other `lara` doors, which report failures on stderr. The output protocol here is structured, and the Lean reference must be able to print the same bytes.

The text boundary is UTF-8, and program text strictly so. `textBoundary` switches five boundaries before anything is read: stdout, stderr, the command line, the file-system encoding, and the locale encoding, which is the one `Lara.Source.Load` reads `.lara` text through. The first four use `UTF-8//ROUNDTRIP`, because bytes that are not UTF-8 must survive a round trip through `String`: a path has to be handed back to `open` as the bytes it came in as, and an echoed path must not stop the encoder mid-message. Program text is the opposite case and uses **strict** UTF-8: a permissive decoder would turn a stray byte into a surrogate escape and elaborate a world from a file `lara check` refuses to read at all, which is precisely what the run contract forbids. Because both PW doors share the boundary, they would agree with each other while both disagreeing with the solo door, so only a direct gate case, not the cross-driver comparison, can see this; the gate has one.

The boundary is the whole CLI's, not these two doors'. `textBoundary` runs once in `main`, so `check`, `deps`, `map-input` and both PW doors read one file as one program under every `LC_ALL`. Because a program is readable under `LC_ALL=C`, the diagnostics that echo author-chosen names must be printable too, so stderr is retargeted beside stdout. The solo door's locale coverage lives in `test/CliSpec.hs` (accept, rejection diagnostics, `deps`, non-UTF-8 program text, and a non-UTF-8 path argument, each rerun under the POSIX locale); the ISO-8859-1 cases live in the PW conformance gate, which builds that locale with `localedef` and exercises the same shared function.

Primitive `box` and `dia` evaluate their operands as written, in the target context; they never translate them. A comparison is the separate source-claim operation: it translates the claim through the bridge's declared symbol map. The gate checks both halves directly: remapping `p` to `q` in a bridge changes the comparison profile, and the run's `queries` section stays equal to the unmapped golden's.

The finite model boundary. The runtime evaluates one specific frame, the frame the file declares. A context's worlds are exactly its declared worlds, and each world is an accepted local unit under the context's environment, so its status atoms are `statusC` over its compiled framework (`Instance.cmpStatus`). A bridge's candidate relation is its declared edge list, and acceptance is each edge's declared flag. Nothing here claims that the flag reflects T6 applicability: acceptance is host data, as in `PWFileHost`. Context environments are compared as decoded, in declaration order, on both sides, so two worlds whose signatures list the same predicates in a different order get `context-environment`. This is deliberate: the environment is the envelope's declared data, not a normalized set. A world is identified by its checked program, which is why a context may not hold two worlds with the same program; otherwise one world value would name two declarations, and the frame could not tell their edges apart. A duplicate-report group whose members disagree refuses its world, because policy quarantine would make a public status conditional (`evidence-blocked`) and a Boolean status atom cannot say "conditionally justified", while under the `reject` conflict mode the local checker would refuse the unit outright (R9). Either way the world is not an unconditionally checked unit, so `world-groups` names the group whatever the mode. A group whose members agree quarantines nothing: `Groups.quarantined_eq_nil` gives an empty quarantine set, and `quarantineLeaves_nil` / `quarantineArgs_nil` make both quarantine operations the identity, so the loader checks exactly the unit the local driver checks (`addWorld_checks_declared`). Consistent groups are per-world data like arguments: they do not enter the context environment, and a context may mix worlds that declare them with worlds that do not. The conditional label is not a fifth outer observation, because one would change `Sorted.cmpVal` and every theorem over it.

`Sat` over an arbitrary frame is proposition-valued, and nothing here claims it is executable. The finite frame above is what makes evaluation decidable.

What is proved in Lean (`lean/Lara/PW/Run.lean`, all in `AxCheck.lean`, standard axioms only):

| Result | Statement |
|---|---|
| `decodeRun_encode`, `encodeRun_injective` | Structured round trip of the run document, including the embedded surface document. |
| `Model.evaluates_iff` | Each printed query answer is `evalFinite` over the declared `Finite` presentation, hence `PW.Sat` of the elaborated formula under `Sorted.cmpVal`. |
| `Model.presents`, `Model.compare_mem_iff_sat` | Comparison inputs `Presents` the frame by construction. So when a claim poses and translates, a status occurs in the printed profile exactly when `⟨b⟩Status_s(τ_b(c))` holds at that world. |
| `indexIn_declared`, `Model.index_declared`, `Model.candidates_declared`, `Model.accepts_declared` | At declared worlds, the frame's candidates and acceptance are exactly the resolved edges, read at world positions, in order. This uses the loader's distinct-program invariant (`LoadedCtx.distinct`). |
| `positionIn_some`, `resolveEdge_declared`, `resolveEdges_declared` | Resolution keeps the file's edges one for one: each resolved edge lies along the bridge its declared name finds, carries its declared acceptance, and sits at the positions of the worlds its declared names identify. |
| `loadWorlds_nodup` (via `IdsOk`, `addWorld_ids`, `loadWorlds_ids`) | No context of a loaded run holds two worlds with one identifier: the loader refuses a repeated name before it checks anything. |
| `Model.candidates_named`, `Model.accepts_named`, `loadModel_spec`, `load_candidates_named`, `load_accepts_named` | For a loaded run, the frame's candidates at a declared world are the worlds named as targets by exactly the file's edges along that bridge from that world's identifier, in declaration order. Acceptance between two declared worlds is the declared flag of such an edge. |
| `distinct_append`, `Hosted.find_isSome`, `Hosted.entry_mem` | The loader's invariant and host naming lemmas. The host's context bijection holds by construction: context indices are declared names. |
| `ResultTag.parse_text`, `ResultTag.text_injective` | Every keyword of the result protocol has exactly one spelling. |
| `addWorld_decoded`, `addWorld_quarantine_empty`, `addWorld_checks_declared` (with `Groups.quarantined_eq_nil`, `Groups.quarantineLeaves_nil`, `Groups.quarantineArgs_nil`) | A world the loader accepts has no conflicting group, hence an empty quarantine set, hence the leaf table and argument list it hands `checkUnit` are the declared ones, the unit the local driver checks. |

The existing results then apply unchanged to a loaded run: `elabPosed_declared` (every modal occurrence resolves to a declaration from the file, with that declaration's symbol map), `evalFinite_iff`, `mem_compare_iff_sat_dia`, and the posing theorems of `Lara.PW.Sorted`.

Tested, not proved. The Haskell runtime (`src/Lara/PW/*.hs`) transcribes the Lean definitions. `scripts/check-pw-conformance.py` requires both drivers to print identical bytes and exit codes, in three families.

The seven committed fixtures `fixtures/pw/run/*.sexp`, each with a committed `*.expected` golden, cover nested modalities that complete and a world with no candidates; translation-domain and sort failures (all five posing faults); canonical numerals; the rule clause under a renaming symbol map, through a constructor sub-pattern and a critical question (`renamed.sexp`); and duplicate-report groups that agree, under both conflict modes, with the supporting argument resting on a grouped report (`groups.sexp`), whose answers are `inline.sexp`'s. Each fixture is also derived with `lara pw-input`, and the derived document must run to the same golden on both drivers.

The generated cases mutate those fixtures. They cover every error stage and fault, and declaration/name mismatches; stage order, and fault order within each stage; every field of a context's environment; each position the rule clause translates, broken in turn; a conflicting group under both modes, the first conflicting group named among consistent ones, consistent groups answering as without them, and a group with an undeclared member refused at decoding; map and acceptance dependence, including all-rejected bridges; and quoted Unicode names, non-ASCII world paths, run-file paths and run directories, including missing ones, and files that are not UTF-8. The Unicode-name and non-ASCII path cases run again under `LC_ALL=C` and under an ISO-8859-1 locale, which the gate builds with glibc's `localedef` (no root needed). An unreadable run file is one more run.

The third family is the `.lara` sources (`fixtures/pw/source/lara.sexp`, whose two worlds are the T7 witness as presentation programs beside it). `lara pw` must print the committed golden, `pw-run` must refuse the same file as `world-input`, and both drivers must print the golden on the document `lara pw-input` derives. Its generated cases cover every way a `.lara` world stops before an envelope exists (unreadable, not UTF-8, unparsable, no policy, source invalid, policy admission stop, policy quarantine), each pinned to the text of the step that stopped rather than to the shared fault constructor; a world that elaborates and is then refused by the checker (R1, `missing-conflict`) or by a group conflict, under both modes, through the derived envelope; consistent groups under `reject`; a `.lara` world sharing a context with an inline envelope; non-ASCII program paths and program text under the same three locales; and a run file that does not decode. When `lara pw` refuses a world's source, `lara pw-input` must print the same envelope.

Every comparison is byte equality, except for the three detail-bearing faults. For those, the gate checks the fault's arity, masks only the final atom, and compares the rest atom for atom. `test/PWSpec.hs` holds the Haskell side to the goldens in-process (for both fixture directories, and for the derived document of each) and to the mirrored laws of the Lean development, including the group rule on the inline fixture. The byte reader and printer are a tested boundary, as in the wire contract, and so is the world pipeline's use of `decodeCheckInput`. Edge resolution's step from names to positions is proved (`resolveEdges_declared`, `load_candidates_named`). Both readers enforce the shared `maxDepth = 10000` nesting bound; the conformance gate checks the bound and exact depth-refusal diagnostics. The elaboration of a `lara` world is Haskell-only by construction: it is the `.lara` door's own pipeline, tested where that door is tested, and the differential covers its output rather than its steps.

The runtime's unproved obligations (canonicalizer agreement, `leaf-ok`, `cert-ok`) are those listed under [Trusted boundaries and unproved obligations](#trusted-boundaries-and-unproved-obligations); `rule-ok` is decided by the loader (`ruleOkB_iff`).

The runtime leaves the local checker wire and its drivers, `pw-surface 1`, `PW.Frame`, `PW.Sat`, `crossCompare`, and the T6 contract unchanged. The `pw-example` executable remains the fixed-host example.

Out of scope for the runtime: approximation bridges, epistemic, dynamic and hybrid operators, global scenarios, and T10. A `lara` world source is elaborated by the Haskell runtime only; the Lean reference reads envelopes, and `lara pw-input` is the door that turns a run with `.lara` worlds into one the reference reads. A `.lara` world whose policy quarantines source material has no envelope and is refused as `world-input`, exactly as a map refuses such a member: the frozen envelope cannot express the pruned unit.

## Distinction from BHL epistemic equivalence

The possible-world outer model is not Belief Hoare Logic's epistemic semantics, and the two must not be conflated when a paper cites either. BHL's observation-equivalence relation is an equivalence relation over complete observation traces, and it is what supports BHL's knowledge laws: the BHL development proves reference knowledge is S5 and that reference accessibility satisfies reflexivity, symmetry, and transitivity (`Model.accessible_refl`, `accessible_symm`, `accessible_trans`, `accessible_equivalence`, and the view-accessibility laws).

Lara's accepted-context bridge relation is a different object. It is the caller-supplied candidate relation `R_b` conjoined with the applicability judgment `accept_b`, and the outer model posits no frame laws for it. Every stronger frame axiom fails on legal frames, by checked refutation: T, D, B, and 5 fail on a single two-world frame and 4 fails on a three-world chain (`sat_T_fails`, `sat_D_fails`, `sat_B_fails`, `sat_5_fails`, `sat_4_fails`). So a bridge is normal (T2's K and necessitation laws hold) and no more.

There is no modality coercion between the two. BHL's reflexivity and introspection laws cannot be imported into a bridge for free; any future translation between them must state and prove its own frame/relation and interpretation-preservation hypotheses.

## Nonempirical worlds and the checked bridge boundary

A world may withhold an assumed axiom that another world uses. This section states what the runtime and the Lean development say about such a pair.

A policy can withdraw assumed leaves with an admission row such as `admission { (assumed, ai-executed) = quarantine }`. The key is exactly `(kind, provenance)`, not a leaf name or proposition, so the row withdraws every matching assumed leaf; it singles out one postulate only when that leaf is the only one with the matching key. An omitted row defaults to `admit`, and a `reject` row stops source admission with R8 instead of yielding a target world. See the [admission contract](evidence-admission-design.md#policy-admission-at-the-source-boundary). Under quarantine the leaf and its dependent arguments are removed; losing all support is a `gap`, not `evidence-blocked` (`Lara.Blocked.blockedQueries`). `WorkedExamplesSpec.prop_axiomAdmissionBoundary` exercises this on a source with an `assumed` parallel-postulate atom and an `nd@1` hypothesis-reuse certificate: `Justified` with admission, `Gap` under quarantine.

`lara pw` refuses a policy-pruned world before bridge loading. `sourceResultCheckInput` does not export a policy-pruned source as a frozen `CheckInput`, so the [world loader](#the-haskell-runtime-and-conformance) reports the target as `world-input` with a policy-quarantine diagnostic. The runtime therefore exhibits no bridge failure for a withdrawn axiom. A target file that simply omits the premise would not exhibit one either: `Lara.PW.Run.loadBridges` decides `rule-ok` but only requires `leaf-ok` and `cert-ok` to be listed, and an edge's `accepted` or `rejected` flag is author-supplied input, not detection.

The obstruction lives in the Lean structural contract. `leaf_ok` requires every source leaf to exist at its translated proposition in the target environment, so a source leaf with no target counterpart cannot satisfy it. `lean/Lara/Examples/AxiomWithdrawal.lean`, described in [D5](demos/d5-axiom-withdrawal.md), witnesses this: the retained context transports the certificate-bearing support through the identity bridge (T6), its Boolean leaf-preservation check is proved equivalent to the identity map's `leaf_ok` clause for this source, and `no_withdrawn_bridge` rules out every symbol and leaf map to the empty target environment. That is a bounded Lean result, not a `lara pw` capability.

Neither the runtime nor D5 checks a geometric consequence of the withdrawn axiom. The `nd@1` source encoder encodes each proposition as a flat atom, so a hypothesis for `parallel_postulate()` cannot, by hypothesis reuse, prove a different atom such as `triangle_sum_180()`; adding that atom to the trusted theory would make it available independently of the premise. The [S1 policy](../examples/S1/strict-v1.policy.lara) documents the same limit, and a geometric consequence would also need the remaining geometric axioms. The [P1 philosophy demo](demos/d4-philmath.md) supplies checked local statuses only.

## Trusted boundaries and unproved obligations

Several conditions hold because of how the artifacts are built, not because a theorem checks them, and a reader should not mistake them for verified facts. The source canonicalizer is shared between two bridged environments as a commitment (`hcanon`); it holds because every context uses the production `dcanon`, not because it is checked. `leaf-ok` and `cert-ok` are premises a run file lists, and listing them proves nothing: they remain `BridgeObligations` premises, and a run file's symbol and leaf maps are not claimed to satisfy them. `rule-ok` is the decidable one, decided by `Surface.ruleOkB` and by the loader. A bridge's acceptance flag is host data: nothing claims it reflects T6 applicability. Over an arbitrary frame `Sat` is proposition-valued and not claimed executable; only a declared finite frame is decidable. The byte reader/printer is a tested boundary rather than a verified textual parser, though the structured codec round trips are proved. Both readers enforce the shared nesting bound; exact refusal behavior is checked by the conformance gate. Elaboration of a `.lara` world is Haskell-only by construction; the differential covers its output rather than its steps.

## Verification and audit

`lean/AxCheck.lean` is the declaration-level axiom audit: every public theorem in the possible-world modules and every substantive theorem witness in the example modules has a corresponding `#print axioms` entry. `scripts/check-axcheck-coverage.py` is the targeted coverage guard that compares public theorem declarations in named source files with those entries. `scripts/check-axioms.sh` checks the emitted audit and permits only the standard axiom trio: `propext`, `Classical.choice`, and `Quot.sound`. No declaration here can reach a `sorryAx`, `ofReduceBool`, or `nativeDecide` obligation, and `native_decide` is banned repo-wide.

The outer layer imports local checking, compilation and grounded semantics rather than defining a second local checker. A change to those shared contracts must be checked against the transport hypotheses and the Haskell/Lean conformance gates.

The audit mechanisms above, not an example's reducibility or a property test, carry the audit contract.

## Supporting declaration index

The subject contracts above use the following supporting declarations. Their source files retain the proof details; `lean/AxCheck.lean` records the public theorem audit. This index does not strengthen any theorem assumption or turn a witness into a general result.

| Lean source | Supporting declarations |
| --- | --- |
| [`lean/Lara/Grounded.lean`](../lean/Lara/Grounded.lean) | `Grounded.labelC_spec` |
