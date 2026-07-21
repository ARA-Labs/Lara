-- LARA mechanized reference semantics — library root.
-- Currently mechanized:
--   * the frozen nf/≡ carve-out (spec §9 result 11 / claim C01)  — Lara.Prop
--   * the ND reference adapter: soundness + dependency exactness (results 10, 8) — Lara.ND
--   * the abstract strict-backend seam: Theorem 1 + ND instantiation (result 8) — Lara.Strict
-- To come (post-M1 freeze): support terms + dependency accountability (result 3),
-- compilation + grounded least-fixpoint (results 4,5), backend replacement
-- (result 9). See docs/mechanization-plan.md.
import Lara.Prop
import Lara.ND
import Lara.Strict
