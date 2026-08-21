-- LARA mechanized reference semantics — library root.
-- Currently mechanized:
--   * the frozen nf/≡ carve-out (spec §9 result 11 / claim C01)  — Lara.Prop
--   * the presentation-AST codec round-trip (spec §9 result 12): the complete
--     live presentation Program/Policy shape at lara-syntax@0.8 — every field of
--     both top-levels, value bindings, inferred argument instantiations, and
--     policySigma included — serializes to a structured
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
-- See docs/mechanization-plan.md for the result-by-result map.
import Lara.Prop
import Lara.Presentation
import Lara.ND
import Lara.Certificate
import Lara.Strict
import Lara.Cell
import Lara.RA
import Lara.Ord
import Lara.Comparison
import Lara.CertSlots
import Lara.Grounded
import Lara.Support
import Lara.Groups
import Lara.Blocked
import Lara.BlockedProgram
import Lara.RawAttack
import Lara.Admission
import Lara.Attack
import Lara.Compile
import Lara.Erase
import Lara.EraseTransport
import Lara.Policy
import Lara.Unit
import Lara.Check
import Lara.Check.Unit
import Lara.Consistency
import Lara.Examples
import Lara.Examples.AttackCompleteness
import Lara.Examples.PolicyAcceptance
import Lara.Examples.GroundedConsistency
