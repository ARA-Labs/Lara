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

open Lara

#print axioms equiv_iff_nf_eq
#print axioms equiv_refl
#print axioms equiv_symm
#print axioms equiv_trans
#print axioms nfTerm_idem
#print axioms nfTerms_idem
#print axioms nf_idem
#print axioms equiv_nf
#print axioms no_reorder
