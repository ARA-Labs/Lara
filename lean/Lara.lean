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
--     deciders, and representative-uniqueness under a nodup carrier. The
--     pre-existing grounded status layer is shown to AGREE with the groundedSem
--     instance (observe_grounded, groundedSem_enumerate) rather than being
--     re-derived from it, and no theorem here is a strict generalization of one
--     downstream; the runtime evaluator stays grounded — Lara.Semantics. The
--     list-level powerset scan it is built on — subseqs, its characterization
--     against the core List.Sublist relation, and one-representative-per-subset
--     under Nodup — mentions no framework and is proved separately in core
--     Lean 4, no Mathlib — Lara.Semantics.Sublists. The disagreements that make
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
import Lara.Examples.Realizability
import Lara.Examples.BackendComposition
import Lara.Examples.Semantics
import Lara.Examples.Update
