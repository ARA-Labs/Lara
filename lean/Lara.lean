-- LARA mechanized reference semantics — library root.
-- Currently mechanized:
--   * the frozen nf/≡ carve-out (spec §9 result 11 / claim C01)  — Lara.Prop
--   * the ND reference adapter: soundness + dependency exactness (results 10, 8) — Lara.ND
--   * the abstract strict-backend seam: Theorem 1 + ND instantiation (result 8) — Lara.Strict
--   * the whole-status layer: direct vs compiled grounded semantics agreement
--     (result 6) + grounded termination/determinism (result 5 core) — Lara.Grounded
--   * support-term typing (spec §6.1, v0.1-frozen): leaf-dependency
--     accountability (result 3 leaf half), uniqueness/determinism, the D⊎H
--     accounting invariants, and the cert-assurance ∘ Theorem-1 seam — Lara.Support
--   * typed positional attacks (spec §7.1, v0.1-frozen): checked source,
--     strict-unattackability, position-kind partition, local/global conclusion
--     coherence — Lara.Attack
--   * executable support, positional-attack, and whole-program checking with
--     exact relational adequacy (result 1 checker portion) — Lara.Check
--   * compilation with subargument closure (spec §8, v0.1-frozen): result 4
--     both halves, closure ⊇ direct, and the N16 bridge from source-level
--     declarative status to the abstract grounded layer (oracle-parametric)
--     — Lara.Compile
--   * the §8.1 Path-B policy validator: strict-reachable patterns, executable
--     wf(Pi), and located R12 violations — Lara.Policy
-- To come: the general checker-built Compile.Faithful edge decider (issue
-- #17, closing result 6), certDeps accountability (result 3 certificate
-- half, needs Backend.uses), the result-7 consistency theorem (issue #18,
-- needs attack completeness), and backend replacement (result 9, needs
-- certificate-erased argument identity). See docs/mechanization-plan.md.
import Lara.Prop
import Lara.ND
import Lara.Certificate
import Lara.Strict
import Lara.Grounded
import Lara.Support
import Lara.Attack
import Lara.Compile
import Lara.Policy
import Lara.Check
import Lara.Examples
