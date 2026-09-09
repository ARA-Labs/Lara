-- LARA mechanized reference semantics — library root.
-- Currently mechanized:
--   * the frozen nf/≡ carve-out (spec §9 result 11 / claim C01)  — Lara.Prop
--   * the presentation-AST codec round-trip (spec §9 result 12): the complete
--     live presentation Program/Policy shape at lara-syntax@0.10 — every field
--     of both top-levels, value bindings, inferred argument instantiations, and
--     policySigma included; @0.9/@0.10 lower named nd@1 payload atoms without
--     changing the presentation AST — serializes to a structured
--     S-expression and parses back exactly (parse ∘ print = id) — a metatheory
--     anchor for the AST shape, NOT a proof of the concrete-syntax Haskell
--     parser — Lara.Presentation
--   * the standalone presentation-parity guard: exact record and sum-payload
--     constructor signatures, explicit alias/entry anchors, exhaustive
--     eliminators, the 73-row normalized shape inventory both runtimes emit,
--     the Lean half of the CI cross-language parity gate
--     (scripts/check-presentation-parity.sh) — Lara.PresentationParity. This
--     meta module is intentionally not imported by the proof-library root.
--   * the ND reference adapter: soundness + dependency exactness (results 10, 8) — Lara.ND
--   * the abstract strict-backend seam: Theorem 1 + ND instantiation (result 8) — Lara.Strict
--   * the whole-status layer: direct vs compiled grounded semantics agreement
--     (result 6) + grounded termination/determinism (result 5 core) — Lara.Grounded
--   * the semantics parameter, made explicit (theory M2a, issue #185): the
--     generic ExtensionSemantics interface (declarative spec + proof-oriented
--     reference enumerator + bundled adequacy), the carrier-bounded admissible /
--     complete / stable / preferred / semi-stable predicates with their Bool
--     deciders, and representative-uniqueness under a nodup carrier. Dung's
--     existence result for preferred extensions is proved here too
--     (preferred_exists, issue #196): every framework has one, with no nodup
--     hypothesis, so preferredSem's enumeration is never empty. The
--     pre-existing grounded status layer is shown to AGREE with the groundedSem
--     instance (observe_grounded, groundedSem_enumerate) rather than being
--     re-derived from it, and no theorem here is a strict generalization of one
--     downstream; the runtime evaluator stays grounded — Lara.Semantics. The
--     list-level powerset scan it is built on — subseqs, its characterization
--     against the core List.Sublist relation, and one-representative-per-subset
--     under Nodup, plus the maximal-element principle preferred_exists runs on
--     — mentions no framework and is proved separately in core Lean 4, no
--     Mathlib — Lara.Semantics.Sublists. The disagreements that make
--     the interface more than an abstraction over a one-element set — stable
--     nonexistence and the noExtension arm it forces, credulous acceptance
--     failing to be a function, observe not factoring through profile, gap's
--     semantics-independence, semi-stable strictly between stable and
--     preferred, and reinstatement in a multi-element extension — are six table
--     frameworks and forty checked theorems in Lara.Examples.Semantics
--   * support-term typing (spec §6.1, v0.1-frozen): dependency accountability
--     (result 3, both halves — leaves_declared and the certDeps layer over
--     Backend.uses), uniqueness/determinism, the D⊎H accounting invariants,
--     and the cert-assurance ∘ Theorem-1 seam — Lara.Support
--   * typed positional attacks (spec §7.1, v0.1-frozen): checked source,
--     strict-unattackability, position-kind partition, local/global conclusion
--     coherence — Lara.Attack
--   * executable support, positional-attack, and whole-program checking with
--     exact relational adequacy (result 1 checker portion); legacy
--     checkProgram/CheckedProgram remains the generic attack-soundness
--     boundary, while detailed acceptance adds completeness — Lara.Check
--   * compilation with subargument closure (spec §8, v0.1-frozen): result 4
--     both halves, closure ⊇ direct, and the N16 bridge from source-level
--     declarative status to the abstract grounded layer — with result 6's
--     source-vs-compiled half complete: the Faithful oracle is now
--     constructively discharged by Compile.edgeB_faithful, exposed through the
--     oracle-free wrappers checkedAF / srcStatus_checked / srcStatus_iff_checked
--     — Lara.Compile
--   * source-to-framework observation transport (theory M2a, issue #185): the
--     carrier-locality property AttackExtensional, proved for all five
--     specifications and refuted for bare ConflictFree; the generic transport
--     of a carrier-local specification between two frameworks that decide
--     Compile.Edge at declared argument positions, with one corollary per
--     semantics; and the claim-level SrcObservation with
--     srcObservation_iff_checked, whose groundedSem case is proved equivalent
--     to Compile.srcStatus_iff_checked under a support-boundedness hypothesis
--     — Lara.Observation
--   * the many-sorted proposition signature and well-sortedness (result 13,
--     lara-core@0.2 / issue #89): the object, sortOf, Sigma-WF, derived rule
--     parameter sorts, decidability without classical input, and the
--     substitution lemma that carries pattern well-sortedness through
--     instantiation — Lara.Sigma
--   * the §8.1 Path-B policy validator: strict-reachable patterns, executable
--     wf(Pi), and located R12 violations, now with spec §4.1 rule scope as the
--     class's second arm — Lara.Policy
--   * the public checkUnit boundary, in fixed order: duplicate rule IDs → R2
--     signature → R12 → duplicate arguments → support → typed attacks →
--     missing conflict.
--     CheckedUnit carries detailed attack completeness and exact retained
--     checker nodes; support is not re-inferred — Lara.Unit / Lara.Check.Unit
--   * downstream-only accepted-unit consistency (result 7 / C09): Path-B
--     attackability, generic grounded conflict-freedom, self-conflict, exact
--     completeClaimFor projection from retained nodes, and the computed-claim
--     headline theorem — Lara.Consistency
--   * backend replacement (result 9): uniform injective assurance relabel,
--     with constructive well-checkedness transport making it non-vacuous —
--     Lara.Erase / Lara.EraseTransport
--   * conservative reporting for quarantine-affected claims (spec §4.3, issue
--     #76): the locality lemma for the declarative grounded judgment, and the
--     non-promotion result plus same-support status preservation — Lara.Blocked;
--     a declared-index framework pair and the drivers' seed discharge the three
--     abstract Blocking obligations — Lara.BlockedProgram. The reindexing and
--     support bridge to the compact production AF closes issue #80.
--   * the `comparison` surface form's direction-of-goodness contract
--     (lara-syntax@0.3 §1.2 / grammar Appendix B.3): the generated `ord@1` goal
--     holds exactly when "ours is better than base" under the measurand's
--     declared polarity, and a polarity swap transposes the operands of the
--     same relation, so it certifies the opposite claim rather than a weaker
--     one. This is the surface-level lookup table, NOT a theorem about the
--     Haskell elaborator, which stays validated-not-verified — Lara.Comparison
--   * named certificate premise slots (lara-syntax@0.6, #105): the
--     presentation-layer payload lowering over an abstract name resolver —
--     byte-identity on payloads with no symbolic reference in scope
--     (dead-wire arm included) and agreement with the declarative positional
--     substitution SymNumericSubst; the Haskell elaborator's name resolution
--     and error taxonomy stay validated-not-verified — Lara.CertSlots
--   * named nd@1 proof terms (lara-syntax@0.9, #132; source-authored formula
--     annotations lara-syntax@0.10, #144): marker-selected lowering of named
--     binders, premise references, theory references, and (prop TEXT) formula
--     annotations to the frozen de Bruijn kernel image; conservativity for
--     kernel certificates and structural agreement with an independent
--     named-term translation over an abstract proposition encoder —
--     Lara.NDNamed
--   * the M2b realization closure (issue #209): the verified decimal
--     round-trip and numeral injectivity for the complexity spine —
--     Lara.Complexity.Numeral; the formula-indexed 3SAT gadget behind the
--     closed injective leaf vocabulary `GadgetLeaf`, with the closed leaf
--     table (Nodup + lookup spec), family-wide ground coverage for the
--     realization record, and every family-wide `checkUnit_complete` premise
--     (argument Nodup, the R2 sorts stage, recursive support, typed attacks
--     with endpoint membership, exact attack completeness) assembled into the
--     family-wide checker equation `checkUnit_formula_ok` under the frozen
--     M2b context of Lara.Complexity.Context — Lara.Complexity.Gadget
--   * the M2b compile image (issue #209, Task 8): the reduction output
--     `reduceCode` with its intended adjacency matrix, the exact-edge
--     characterization of the compiled closure over the generated family
--     (`coveredB_gadget` — no closure-generated extras), the
--     `StructuredAFIso` to the decoded carrier, and the frozen promise and
--     size obligations `reduce_realizable` / `reduce_nodes` /
--     `reduce_byteSize`; extended by the reduction correctness (Task 12):
--     satisfiability over the explicit three-literal syntax
--     (`Formula3.Satisfiable`), the complete-extension soundness and direct
--     completeness arguments over the gadget edges, the frozen
--     `reduce_correct` quoted beside the class-membership and size
--     obligations, executable fixture verdicts through
--     `fixedCredCompleteB`, and the `g(0)` self-edge negative control
--     `selfEdgeCode_not_realizable` keeping the result a theorem about the
--     realizable class, not unrestricted AFs — Lara.Complexity.Reduction
--   * the M2b cost-instrumented grounded kernel (issue #209, Task 9): the
--     attack-query-counting mirrors `anyAttackerC` / `defendedC` / `stepC` /
--     `iterC` / `groundedC` of the proof-oriented grounded evaluator, their
--     first-projection agreement with `Lara.Grounded`, and the two-sided
--     query bounds with distinct quantifiers — the universal quadratic lower
--     bound `groundedC_cost_ge`, the `n³(1+n)` ceiling `groundedC_cost_le`,
--     and the two-node all-attacks regression (cost `4 = 2²`) refuting the
--     rejected exact pointwise cubic inequality at `n = 2` — Lara.Complexity
--   * the M2b realizable quartic witness (issue #209, Task 10): the
--     three-block carrier `quarticAF` (for positive k: k-1 neutral `g` nodes,
--     the defender `d` declared last in its block, k `b` nodes, and k `a`
--     nodes; edges exactly `d → b(i)` and `b(i) → a(j)`), realized under
--     a leaf-only raw unit through the executable checker with a
--     `StructuredAFIso` at the identity reindexing (`quartic_realizable`,
--     `quartic_size`); the grounded iterate shape (round one exactly the
--     defender block, every later round defender + target blocks); and the
--     quartic bound `quartic_cost_ge` (`k⁴ ≤` instrumented grounded cost,
--     `2 ≤ k`) with closed evaluations at `k = 2, 3, 4` — a *worst-case*
--     `Θ(n⁴)` result on this fixed-context realizable family, NOT a universal
--     per-instance floor (the proved universal lower bound remains `n²`) —
--     Lara.Examples.Complexity
--   * the M2b shared carrier-status evaluator (issue #209, Task 11): the
--     status query factored over one grounded run — `labelFromGroundedC`
--     reading labels off a shared grounded result, `statusSharedC`
--     preserving `Grounded.statusC`'s observable guard order while computing
--     `groundedC` at most once, and the exposed carrier query
--     `carrierStatusC` over the erased carrier with agreement
--     `carrierStatusC_fst = Invariants.status`; `carrierStatusC_cost_le`
--     (`n³(1+n) + 2n²`) is the paper-citable GroundedStatus upper theorem
--     (the generic `statusSharedC_cost_le` is internal accounting), and the
--     quartic floor transfers to this surface via
--     `carrierStatus_quartic_cost_ge` — Lara.Complexity and
--     Lara.Examples.Complexity
--   * the PW0 possible-world outer-model gate (issue #192, tracker #189): the
--     typed outer frame — scientific contexts, per-context worlds and queries,
--     bridges carrying a candidate relation, a checked applicability judgment,
--     and a bridge-global partial claim translation — the many-sorted outer
--     modal language and its satisfaction (formula-first, `Sat F V φ w`, for
--     the elaboration reason recorded in that definition's doc comment), and
--     the T2 typed normality laws (K, necessitation, duality, `[b]⊤`, finite
--     meets) together with the refutation of every stronger frame axiom
--     (T, 4, B, D, 5) in Lara.Examples.PW, so "normal, and no more" is a
--     theorem and not a comment — Lara.PW.Outer. The T3 uniform-language reduction embeds an
--     independently defined ordinary multimodal Kripke semantics into the
--     one-context frame and matches satisfaction clause by clause —
--     Lara.PW.Uniform. The executable comparison layer keeps incomparability
--     in its own constructor (neither CrossResult nor IncomparabilityReason
--     contains a Status, so no collapse into a local status is constructible),
--     pins each reason to exactly its defining condition, and is tied to the
--     model by the `Presents` obligation and the adequacy theorems
--     `mem_compare_iff_sat_dia` / `not_sat_dia_of_incomparable` — so `crossCompare`
--     implements the model's ⟨b⟩ rather than resembling it — Lara.PW.Compare.
--     The Lara instantiation reads two INDEPENDENTLY DEFINED world-local
--     observations — the relational oracle-free Compile.SrcStatus and the
--     executable Grounded.statusC over Compile.checkedAF — whose agreement
--     (T1) is the existing srcStatus_iff_checked preservation chain applied at
--     a world; T4 is valuation congruence instantiated at T1, the
--     Functional/Total valuation coherence side conditions are discharged for
--     both valuations (for the source one only THROUGH T1), and T0 embeds a
--     current Lara run into a bridge-free singleton context where atomic
--     satisfaction is definitionally the unchanged local status judgment —
--     Lara.PW.Instance. The T7 witness exhibits an accepted bridge edge whose
--     source world justifies a claim and whose target world defeats its
--     identity-translated form while the transported support term remains a
--     checked argument of the target program — in both the ⟨b⟩ and [b]
--     readings, each under both valuations — beside one executable fixture
--     per incomparability reason (every decidable fixture closed by decide;
--     the modal-layer facts are term or tactic proofs) and a
--     Presents-discharged instantiation of not_sat_dia_of_incomparable —
--     Lara.Examples.PW. The
--     wrapper redefines nothing local: the PW modules only import, and no
--     existing semantics module changed. Deliberately absent: structural
--     bridges/T6, T8-T10, approximation, epistemic/dynamic/hybrid operators,
--     global scenarios, surface syntax — see docs/theory-pw0-outer-model.md
--   * the PW-T6 exact checked-support transport (issue #191, tracker #189):
--     the bridge-global partial symbol translation lifted structurally over
--     terms, atoms, patterns, substitutions, rules, and support terms, with
--     the two commuting facts that carry the milestone — instantiation
--     commutes with translation (instAPat_tr), and ≡ survives translation
--     (equiv_tr) because nf touches only numeric literals while the
--     translation touches only predicate/constructor names —
--     Lara.PW.Translation. The StructuralBridge contract is three clauses,
--     one per environment parameter HasSupport reads (leaf_ok, rule_ok,
--     cert_ok over a SHARED canon), and support_transport carries a checked
--     source support to a checked target support with the translated
--     conclusion and the VERBATIM obligation list (question keys are
--     rule-local names the translation preserves), so completeness
--     transports for free; target-side strict occurrences replay against
--     the target registry by B0's headline applied to the transported
--     derivation, and PW0's arbitrary `accept` gains its promised checker
--     tie at structural bridges via Admits/admits_transport —
--     Lara.PW.Structural. The identity endobridge at the T7 pair packages
--     the T6/T8 boundary at a live instance (transport succeeds, status
--     still flips), and a genuine predicate-renaming bridge exercises the
--     vocabulary machinery off the identity, with the out-of-vocabulary
--     claim reported as exactly translationUndefined —
--     Lara.Examples.PWStructural. The theorem neither assumes nor concludes
--     grounded status preservation (that boundary is T8, #193); the modules
--     only import — see docs/theory-pw-t6-structural-transport.md
--   * PW-T9 structural-path composition (issue #190, tracker #189):
--     arbitrary typed `BridgePath`s retain the chosen sequence of structural
--     bridges and fold it to a named first-leg-first composite. Exact checked
--     support transports stepwise along any such path and agrees with transport
--     by its fold. A named direct bridge agrees with a chosen path only under
--     an explicit path-level `Commutes` witness; common endpoints alone do not
--     force a triangle. Checker-tied `Admits` composes, while the full
--     `Accepted R = R ∧ Admits` relation keeps caller-supplied candidates
--     separate and requires their own coherence. Missing translations remain
--     comparison-level incomparability, never a local status; grounded-status
--     preservation is the T8 boundary (#193), while approximation bridges
--     remain tracker #189 — Lara.PW.Compose and Lara.Examples.PWCompose.
--   * PW-T8 conditional status preservation (issue #193, tracker #189):
--     grounded labelling and four-state claim status over an abstract AF are
--     invariant under a total attack bisimulation, with the design's AF
--     isomorphism as a corollary whose injectivity half no proof consumes —
--     Lara.PW.AFBisim. At a structural bridge the bisimulation is the
--     bridge-induced index relation between compiled arguments; the T8
--     hypotheses `StatusBridge` are T6's `Admits`, its converse `matched`,
--     and attack forth/back on the compiled edge decider; complete-support
--     sets correspond for every translatable query through T6 transport and
--     `≡`-reflection along an injective translation; `status_transport`
--     then preserves `gap`/`justified`/`contested`/`defeated` at once, and
--     the modal reading collapses `RobustlyJustified`/`PossiblyJustified`
--     to the local status. Status bridges compose along the T9 composite —
--     Lara.PW.Status. The T7 identity edge is a forward attack homomorphism
--     that fails `matched`; one renaming translation transports `justified`,
--     `defeated`, `gap`, and `contested` off the identity, and one `[b]`
--     cell instantiates the modal reading — Lara.Examples.PWStatus.
--     `statusBridgeB` decides the hypotheses over the finite compiled index
--     ranges (sound and complete), so a conformance cell is one `decide` —
--     Lara.PW.StatusCheck, Lara.Examples.PWStatusCheck.
--     Neither T6 nor T9 is strengthened: every bridge-level result takes
--     `StatusBridge` (or an explicit `SupportCorr`) as an extra hypothesis.
--   * the fragment/linking context calculus and contextual representation
--     independence (theory M4 part A, issue #187): fragments with import/export
--     interfaces, a witnessed link guard, linking that saturates cross-boundary
--     conflicts and merges structurally identical arguments, context
--     composition, and the headline — an injective, acceptance-preserving
--     relabel of a fragment's certificates is unobservable in every admissible
--     context, with the acceptance-profile generalization over two registries.
--     Not parametricity, not full abstraction — Lara.Context.*
--   * the same contextual observation at an arbitrary M2a extension semantics
--     (issue #216): `obsGen` parameterizes the *projection* read off the linked
--     carrier, so `obsGen_congr` proves the congruence once for every reading
--     at once and `obsSem` / `CtxEquivSem` are instantiations of it rather than
--     a second development. The generic congruences carry *no* additional
--     hypothesis — in particular no `AttackExtensional` — because they
--     transport along the carrier equality `compileUnit_link_relabel` supplies
--     rather than along pointwise attack agreement. The projection layer sits
--     in Lara.Context.Fragment / Lara.Context.Equivalence rather than beside
--     the semantics: `Observation` is an abbreviation of a payload-generic
--     `ObservationOf α`, `obsGen` lives next to the theorems it generalizes,
--     `obs_eq_obsGen` holds by `rfl`, and the grounded `obs_eq_of_ok` /
--     `backend_replacement_congruence` are one-line corollaries rather than a
--     second copy of the same proof. `obs`, `CtxEquiv` and every grounded
--     statement are unchanged. The grounded case at a *semantics* is likewise
--     recovered as a theorem (`obsSem_grounded`, and `ctxEquivSem_grounded_iff`
--     as an `iff`, so no M4 statement moves). Context-level separations witness
--     that the semantics parameter is not an abstraction over one instance: a
--     linked three-cycle where `stableSem` reports `noExtension` and a sink
--     where `preferredSem` and `groundedSem` disagree —
--     Lara.Invariants.Observation, Lara.Context.Observation,
--     Lara.Examples.ContextSemantics.
-- See docs/mechanization-plan.md for the result-by-result map.
import Lara.Prop
import Lara.Presentation
import Lara.ND
import Lara.NDNamed
import Lara.Certificate
import Lara.Strict
import Lara.Cell
import Lara.RA
import Lara.Ord
import Lara.Insp
import Lara.Comparison
import Lara.CertSlots
import Lara.Grounded
import Lara.Semantics
import Lara.Semantics.Sublists
import Lara.Support
import Lara.BackendComposition
import Lara.Groups
import Lara.Blocked
import Lara.BlockedProgram
import Lara.RawAttack
import Lara.Admission
import Lara.Update
import Lara.Attack
import Lara.Compile
import Lara.Observation
import Lara.Erase
import Lara.EraseTransport
import Lara.Policy
import Lara.Unit
import Lara.Check
import Lara.Check.Unit
import Lara.Consistency
import Lara.Invariants
import Lara.Realizability
import Lara.Complexity.Context
import Lara.Complexity.Encoding
import Lara.Complexity.Numeral
import Lara.Complexity.Gadget
import Lara.Complexity.Reduction
import Lara.Complexity
import Lara.Examples
import Lara.Examples.AttackCompleteness
import Lara.Examples.PolicyAcceptance
import Lara.Examples.GroundedConsistency
import Lara.Examples.CompilerInvariants
import Lara.Examples.Complexity
-- The Task-2 restricted-class realization spike. Imported here because
-- nothing else did: the module was outside the build entirely, so its
-- theorems were never elaborated and could not be axiom-audited (#242).
import Lara.Examples.Complexity.Realization
import Lara.Examples.Realizability
import Lara.Examples.BackendComposition
import Lara.Examples.Semantics
import Lara.Examples.Update
import Lara.ListRel
import Lara.Context.Fragment
import Lara.Context.Link
import Lara.Context.Merge
import Lara.Context.Compose
import Lara.Invariants.Merge
import Lara.Invariants.Observation
import Lara.Context.Equivalence
import Lara.Context.Observation
import Lara.Context.Parametricity
import Lara.Context.FiniteExtension
import Lara.Context.Surface
import Lara.Examples.Linking
import Lara.Examples.ContextSemantics
import Lara.Examples.CertificateCollapse
-- The #227 surface-transport witness. Imported here for the same reason as
-- Lara.Examples.Complexity.Realization above: AxCheck.lean is not a lake
-- target, so a module reachable only from it is outside `lake build` and its
-- theorems would never be elaborated on a clean checkout.
import Lara.Examples.SurfaceTransport
-- The #258 attack-bearing surface-transport witness, for the same reason.
import Lara.Examples.SurfaceTransportAttack
-- The #264 context-bearing surface-link witness, for the same reason.
import Lara.Examples.SurfaceTransportContext
import Lara.PW.Outer
import Lara.PW.Uniform
import Lara.PW.Compare
import Lara.PW.Instance
import Lara.PW.Translation
import Lara.PW.Structural
import Lara.Examples.PW
import Lara.Examples.PWStructural
import Lara.PW.Compose
import Lara.Examples.PWCompose
import Lara.PW.AFBisim
import Lara.PW.Status
import Lara.Examples.PWStatus
import Lara.PW.StatusCheck
import Lara.Examples.PWStatusCheck
import Lara.PW.AttackTransport
import Lara.Examples.PWAttack
