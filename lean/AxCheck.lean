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
import Lara.Grounded
import Lara.Support
import Lara.Attack
import Lara.Compile
import Lara.Examples

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

-- Result 2 / C03: source non-factivity (Theorem 3, the factivity firewall).
#print axioms Lara.Strict.nd_nonfactive_witness
#print axioms Lara.Strict.no_truth_projection
#print axioms Lara.Strict.nd_relative_not_absolute

-- Result 3 (leaf half) + result 1 (uniqueness half) / spec §6.1 freeze:
-- support-term typing — dependency accountability, determinism, the D⊎H
-- accounting invariants (incl. the extensional partition), and the
-- cert-assurance ∘ Theorem-1 composition. Every theorem in the file is
-- audited, helper lemmas included (CLAUDE.md: AxCheck covers every new
-- theorem).
#print axioms Lara.Support.memB_iff
#print axioms Lara.Support.mem_dedupQuestions
#print axioms Lara.Support.dedupQuestions_nodup
#print axioms Lara.Support.unionAll
#print axioms Lara.Support.unionAll_nodup
#print axioms Lara.Support.collectObligations
#print axioms Lara.Support.collectObligations_nodup
#print axioms Lara.Support.append_eq_nil'
#print axioms Lara.Support.getElem?_some_of_lt
#print axioms Lara.Support.lt_of_getElem?_some
#print axioms Lara.Support.getElem?_none_of_ge
#print axioms Lara.Support.ext_getElem?
#print axioms Lara.Support.mem_leavesList
#print axioms Lara.Support.mem_leavesDis
#print axioms Lara.Support.mem_mandatoryNames
#print axioms Lara.Support.mem_questionNames
#print axioms Lara.Support.leaves_declared
#print axioms Lara.Support.hasSupport_unique
#print axioms Lara.Support.supports_resp_equiv
#print axioms Lara.Support.strict_no_questions
#print axioms Lara.Support.complete_mandatory_discharged
#print axioms Lara.Support.dh_partition
#print axioms Lara.Support.certOkOf_strict_step

-- Spec §7.1 freeze: typed positional attacks — checked source (§1 guarantee 4),
-- strict-unattackability, position-kind partition, and the coherence of local
-- attack checking with global support typing.
#print axioms Lara.Attack.attack_source_checked
#print axioms Lara.Attack.rebut_top_defeasible
#print axioms Lara.Attack.undercut_pos_defeasible
#print axioms Lara.Attack.undercut_target_rule
#print axioms Lara.Attack.undermine_target_leaf
#print axioms Lara.Attack.rebut_concl_coherent

-- Spec §8 compile freeze: result 4 both halves (no untyped node or attack),
-- subargument closure extends the direct attack, and the N16 bridge at both
-- levels — argument (srcIn_iff_grounded) and exact four-state claim status
-- (srcStatus_iff) — oracle-parametric via Compile.Faithful.
#print axioms Lara.Compile.contains_refl
#print axioms Lara.Compile.attackOcc_unique
#print axioms Lara.Compile.target_contains_occ
#print axioms Lara.Compile.compile_nodes_checked
#print axioms Lara.Compile.edge_iff
#print axioms Lara.Compile.closure_includes_direct
#print axioms Lara.Compile.srcIn_direct
#print axioms Lara.Compile.srcOut_direct
#print axioms Lara.Compile.direct_srcIn
#print axioms Lara.Compile.direct_srcOut
#print axioms Lara.Compile.srcIn_iff_directIn
#print axioms Lara.Compile.srcOut_iff_directOut
#print axioms Lara.Compile.srcIn_iff_grounded
#print axioms Lara.Compile.srcStatus_correct
#print axioms Lara.Compile.srcStatus_unique
#print axioms Lara.Compile.srcStatus_iff

-- Concrete conformance examples: obligation accounting (mixed/nested/missing),
-- subterm traversal boundaries, and subargument-closure superset behavior with
-- a concrete edge decider and grounded verdict.
#print axioms Lara.Examples.no_prems
#print axioms Lara.Examples.no_dis
#print axioms Lara.Examples.subterm_boundaries
#print axioms Lara.Examples.sideMix
#print axioms Lara.Examples.mixed_holes_obligations
#print axioms Lara.Examples.sideUse
#print axioms Lara.Examples.nested_obligation_propagates
#print axioms Lara.Examples.sideDisUse
#print axioms Lara.Examples.discharge_obligation_propagates
#print axioms Lara.Examples.sidePair
#print axioms Lara.Examples.repeated_obligation_deduplicated
#print axioms Lara.Examples.missing_question_rejected
#print axioms Lara.Examples.overlapping_question_rejected
#print axioms Lara.Examples.defeasible_rebut_typed
#print axioms Lara.Examples.strict_root_rebut_rejected
#print axioms Lara.Examples.nested_undercut_typed
#print axioms Lara.Examples.mixed_path_undermine_typed
#print axioms Lara.Examples.sideWrap
#print axioms Lara.Examples.vWrap_typed
#print axioms Lara.Examples.kAtk_typed
#print axioms Lara.Examples.closure_edge_direct
#print axioms Lara.Examples.closure_edge_wrapper
#print axioms Lara.Examples.closure_no_edge_unrelated
#print axioms Lara.Examples.edge_fixture_iff
#print axioms Lara.Examples.edgeBEx_faithful
#print axioms Lara.Examples.closure_grounded_verdict

-- Result 5 / C07: grounded termination + determinism (finite stabilization).
#print axioms Lara.Grounded.grounded_stable
#print axioms Lara.Grounded.grounded_fixpoint

-- Result 6 / C08 (abstract AF layer): declarative grounded ≡ executable grounded
-- labelling over any AF (spec §9 result 6 abstract core; N16 partially resolved).
-- The source-vs-compiled preservation exercising `compile`/subargument closure is
-- M1 work; `compile_attack_iff` characterizes (not: exercises) the closure edges.
-- `statusC_gap_iff` mechanizes the N17-(1) "gap only on empty complete support" half.
#print axioms Lara.Grounded.directIn_iff
#print axioms Lara.Grounded.labelC_inn_iff
#print axioms Lara.Grounded.labelC_out_iff
#print axioms Lara.Grounded.labelC_undec_iff
#print axioms Lara.Grounded.status_preservation
#print axioms Lara.Grounded.compile_attack_iff
#print axioms Lara.Grounded.statusC_gap_iff
