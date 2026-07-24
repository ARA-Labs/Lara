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
--   * compilation with subargument closure (spec §8, v0.1-frozen): result 4
--     both halves, closure ⊇ direct, and the N16 bridge from source-level
--     declarative status to the abstract grounded layer (oracle-parametric)
--     — Lara.Compile
-- To come: the executable support/attack/edge checkers (result 1 other half;
-- they also constructively supply Compile.Faithful, closing result 6's
-- source-vs-compiled half), certDeps accountability (needs Backend.uses),
-- backend replacement (result 9). See docs/mechanization-plan.md.
import Lara.Prop
import Lara.ND
import Lara.Certificate
import Lara.Strict
import Lara.Grounded
import Lara.Support
import Lara.Attack
import Lara.Compile
import Lara.Examples
