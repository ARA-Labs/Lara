/-
Axiom audit for the LARA mechanization. Not part of the `Lara` library target;
run standalone in CI as the "the proofs are real" gate:

    lake env lean AxCheck.lean

`#print axioms t` reports the full axiom dependency set of `t`, transitively. If
any theorem were closed with `sorry`/`admit` (even indirectly), its report would
include `sorryAx`; a rogue `axiom` declaration would show up by name. The CI
script greps this output and fails on `sorryAx` or any axiom outside the standard
Lean trio (`propext`, `Classical.choice`, `Quot.sound`). See `lean/README.md`.
-/
import Lara.Prop
import Lara.ND
import Lara.Strict

open Lara

-- Result 11 / C01: nf/≡ carve-out.
#print axioms equiv_iff_nf_eq
#print axioms equiv_refl
#print axioms equiv_symm
#print axioms equiv_trans
#print axioms nfTerm_idem
#print axioms nfTerms_idem
#print axioms nf_idem
#print axioms equiv_nf
#print axioms no_reorder

-- Result 10 / C05: ND reference-adapter soundness + dependency exactness.
#print axioms Lara.ND.nd_relevance
#print axioms Lara.ND.nd_sound
#print axioms Lara.ND.fv_in_range
#print axioms Lara.ND.hyp_out_of_range_untypable
#print axioms Lara.ND.mem_shiftDown

-- Layer C: the algorithm `infer` (port of Haskell `inferType`) decides the
-- relation `HasType` and returns exactly `fv` — ties the running checker to the
-- metatheory proved about the relation.
#print axioms Lara.ND.infer_sound
#print axioms Lara.ND.infer_complete
#print axioms Lara.ND.infer_deps_eq_fv
#print axioms Lara.ND.infer_iff
#print axioms Lara.ND.hasType_unique

-- Result 8 / C03: abstract strict-step soundness (Theorem 1) + ND instantiation.
#print axioms Lara.Strict.strict_step_sound
#print axioms Lara.Strict.ndBackend
#print axioms Lara.Strict.nd_strict_step_sound
