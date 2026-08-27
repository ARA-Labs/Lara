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
import Lara.Presentation
import Lara.ND
import Lara.NDNamed
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
import Lara.Sigma
import Lara.Check
import Lara.Driver
import Lara.Examples
import Lara.Examples.AttackCompleteness
import Lara.Invariants
import Lara.Examples.CompilerInvariants
import Lara.Examples.PolicyAcceptance
import Lara.Examples.GroundedConsistency

open Lara

-- The closed wire keyword vocabulary is injective, as required by the Haskell
-- Map-backed reverse lookup.
#print axioms Lara.Driver.tagToString_injective

-- Result 13 (the many-sorted signature, `lara-core@0.2` / issue #89).
-- (a) decidability without classical input: the executable check IS the
--     relation, so the instance below reports the empty axiom set.
#print axioms Lara.Sigma.wellSorted_decidable
#print axioms Lara.Sigma.sigmaWellFormed_decidable
#print axioms Lara.Sigma.wellSorted_iff
#print axioms Lara.Sigma.sigmaFault
#print axioms Lara.Sigma.sortOf
#print axioms Lara.Sigma.ruleParamSorts
-- (b) the substitution lemma, at every level the checker uses it. This is the
--     load-bearing metatheory: stage 2 checks patterns once and each θ range
--     separately, and NOTHING checks the instantiated atoms directly.
#print axioms Lara.Sigma.lookupParam_append_of_none
#print axioms Lara.Sigma.lookupParam_append_mono
#print axioms Lara.Sigma.checkPat_mono
#print axioms Lara.Sigma.checkPats_mono
#print axioms Lara.Sigma.checkAPat_mono
#print axioms Lara.Sigma.checkAPats_mono
#print axioms Lara.Sigma.instPat_sortOf
#print axioms Lara.Sigma.instPats_expectTerms
#print axioms Lara.Sigma.wellSorted_subst
#print axioms Lara.Sigma.wellSorted_subst_list
#print axioms Lara.Sigma.wellSorted_subst_mem
#print axioms Lara.Sigma.wellSorted_rule
-- (c) the statement the paper cites: accepted support instances and the unit's
--     ground environment are well-sorted under that unit's own Σ.
#print axioms Lara.Check.Unit.signatureStage
#print axioms Lara.Check.Unit.signatureStage_sigma_wf
#print axioms Lara.Check.Unit.signatureStage_policy
#print axioms Lara.Check.Unit.signatureStage_ground
#print axioms Lara.Check.Unit.signatureStage_args
#print axioms Lara.Check.Unit.thetaWellSorted_sortRespecting
#print axioms Lara.Check.Unit.thetaWellSorted_ruleSortRespecting
#print axioms Lara.Check.Unit.checkUnit_wellSorted

-- Symbolic certificate wire equality (nested `List SExpr`, decided manually).
#print axioms Lara.Support.SExpr.decEq
#print axioms Lara.Support.SExpr.decEqList

-- Shared raw attack identity and endpoint alignment (policy admission
-- boundary, metatheory plan Task 1). The vocabulary moved out of Lara.Driver;
-- `resolve_filter_commute` proves filtering by raw endpoint id commutes with
-- resolution.
#print axioms Lara.RawAttack.selectAligned
#print axioms Lara.RawAttack.resolveAttacks
#print axioms Lara.RawAttack.resolve_filter_commute
#print axioms Lara.RawAttack.resolveAttacks_endpoints_mem
#print axioms Lara.RawAttack.selectAligned_mono
#print axioms Lara.RawAttack.lookupArg_of_mem_nodup

-- R14 argument-id uniqueness as a carried invariant: the wire decoder proves
-- it (`firstDup_none_nodup`) and `AlignedAttacks.ids_nodup` transports it into
-- the admission model, where `retained_attack_source_retained` needs it.
#print axioms Lara.Driver.firstDup_none_nodup

-- Policy admission at the trusted source boundary (metatheory plan Task 2):
-- the declarative judgment, its correspondence with the evaluator, the two
-- context layers, the endpoint-safe prune, the canonical audit, the
-- all-admit identity, restrictiveness, rejection, and source non-promotion.
#print axioms Lara.Admission.evaluateAdmission_iff_judgment
#print axioms Lara.Admission.admission_deterministic
#print axioms Lara.Admission.policy_admitted_iff
#print axioms Lara.Admission.checked_admitted_iff
#print axioms Lara.Admission.checked_admitted_ids_eq_prune
#print axioms Lara.Admission.nodup_ids_eq_of_mem
#print axioms Lara.Admission.policy_quarantined_absent
#print axioms Lara.Admission.policy_quarantined_arg_excluded
#print axioms Lara.Admission.retained_attack_endpoints
#print axioms Lara.Admission.retained_attack_source_retained
#print axioms Lara.Admission.retained_attacks_selectAligned
#print axioms Lara.Admission.admission_audit_exact
#print axioms Lara.Admission.audit_leaves_nonempty
#print axioms Lara.Admission.policy_all_admit_group_identity
#print axioms Lara.Admission.mem_policyQuarantineSeed_iff
#print axioms Lara.Admission.policy_all_admit_checkUnit_identity
#print axioms Lara.Admission.policyQuarantineSeed_subset_of_restrictive
#print axioms Lara.Admission.removedSeed_subset_of_restrictive
#print axioms Lara.Admission.accepted_prune_eq
#print axioms Lara.Admission.accepted_metadata_aligned
#print axioms Lara.Admission.accepted_checked_context_exact
#print axioms Lara.Admission.accepted_resolved_aligned
#print axioms Lara.Admission.more_restrictive_cannot_add_structure
#print axioms Lara.Admission.source_reject_no_checked_unit
#print axioms Lara.Admission.source_justified_nonpromotion

-- `usesLeaf` monotonicity (mutual `def`s in `Prop`, used as theorems).
#print axioms Lara.Groups.usesLeaf_mono
#print axioms Lara.Groups.usesLeafList_mono
#print axioms Lara.Groups.usesLeafDisch_mono

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

-- Result 12: presentation-AST codec round-trip (`parse ∘ print = id`). The two
-- top-level theorems plus every helper round-trip lemma the module proves
-- (CLAUDE.md: AxCheck covers every new theorem).
#print axioms Lara.Presentation.parse_printProgram
#print axioms Lara.Presentation.parse_printPolicy
-- Generic list/pair combinators.
#print axioms Lara.Presentation.listOfSx_sxOfList
#print axioms Lara.Presentation.unSxList_sxList
#print axioms Lara.Presentation.unSxPair_sxPair
#print axioms Lara.Presentation.unOpt_sxOpt
-- Primitive leaves.
#print axioms Lara.Presentation.unStr_sxStr
#print axioms Lara.Presentation.un_sxList_String
#print axioms Lara.Presentation.unInt_sxInt
#print axioms Lara.Presentation.unBool_sxBool
-- Identifier newtypes.
#print axioms Lara.Presentation.un_PropId
#print axioms Lara.Presentation.un_QuestionId
#print axioms Lara.Presentation.un_LeafId
#print axioms Lara.Presentation.un_RuleId
#print axioms Lara.Presentation.un_ArgId
#print axioms Lara.Presentation.un_ArgRef
#print axioms Lara.Presentation.un_sxList_ArgRef
#print axioms Lara.Presentation.un_sxArgDischarge
#print axioms Lara.Presentation.un_ObligationId
#print axioms Lara.Presentation.un_BackendId
#print axioms Lara.Presentation.un_PolicyId
#print axioms Lara.Presentation.un_Param
#print axioms Lara.Presentation.un_SourceRef
#print axioms Lara.Presentation.un_TheoryDigest
#print axioms Lara.Presentation.un_Digest
#print axioms Lara.Presentation.un_GroupId
#print axioms Lara.Presentation.un_MeasurandId
#print axioms Lara.Presentation.un_DatasetId
#print axioms Lara.Presentation.un_PremiseLabel
#print axioms Lara.Presentation.un_ValueName
#print axioms Lara.Presentation.un_sxList_LeafId
#print axioms Lara.Presentation.un_sxOpt_PremiseLabel
#print axioms Lara.Presentation.un_sxList_optPremiseLabel
#print axioms Lara.Presentation.un_sxOpt_PropId
-- Closed enum vocabularies.
#print axioms Lara.Presentation.un_LeafKind
#print axioms Lara.Presentation.un_Provenance
#print axioms Lara.Presentation.un_AuditStatus
#print axioms Lara.Presentation.un_Mode
#print axioms Lara.Presentation.un_Necessity
#print axioms Lara.Presentation.un_Admission
#print axioms Lara.Presentation.un_sxStep
#print axioms Lara.Presentation.un_GroupConflictMode
#print axioms Lara.Presentation.un_Polarity
#print axioms Lara.Presentation.un_sxOpt_Polarity
#print axioms Lara.Presentation.un_Relation
-- The declared signature Σ, reused from `Lara.Sigma` (spec §2, §3.4).
#print axioms Lara.Presentation.un_TermSort
#print axioms Lara.Presentation.un_sxList_TermSort
#print axioms Lara.Presentation.un_sxConSig
#print axioms Lara.Presentation.un_sxList_ConSig
#print axioms Lara.Presentation.un_sxPredSig
#print axioms Lara.Presentation.un_sxList_PredSig
#print axioms Lara.Presentation.un_sxSigma
-- Propositions (reused semantic core).
#print axioms Lara.Presentation.un_sxTerm
#print axioms Lara.Presentation.un_sxTerms
#print axioms Lara.Presentation.un_sxAtom
#print axioms Lara.Presentation.un_sxList_Atom
#print axioms Lara.Presentation.un_sxTheoryEntry
#print axioms Lara.Presentation.un_sxList_TheoryEntry
-- Patterns.
#print axioms Lara.Presentation.un_sxPat
#print axioms Lara.Presentation.un_sxPats
#print axioms Lara.Presentation.un_sxAtomPat
-- Certificates, assurance, and the recursive support-term algebra.
#print axioms Lara.Presentation.un_sxCert
#print axioms Lara.Presentation.un_sxAssurance
#print axioms Lara.Presentation.un_sxSubst
#print axioms Lara.Presentation.un_sxHoles
#print axioms Lara.Presentation.un_sxST
#print axioms Lara.Presentation.un_sxSTs
#print axioms Lara.Presentation.un_sxDis
-- Record layer + list-field round-trips.
#print axioms Lara.Presentation.un_sxList_SourceRef
#print axioms Lara.Presentation.un_sxList_Param
#print axioms Lara.Presentation.un_sxList_AtomPat
#print axioms Lara.Presentation.un_sxLeaf
#print axioms Lara.Presentation.un_sxBinding
#print axioms Lara.Presentation.un_sxClaim
#print axioms Lara.Presentation.un_sxQuestion
#print axioms Lara.Presentation.un_sxList_Question
#print axioms Lara.Presentation.un_sxCertRef
#print axioms Lara.Presentation.un_sxList_CertRef
#print axioms Lara.Presentation.un_sxRule
#print axioms Lara.Presentation.un_sxList_Rule
#print axioms Lara.Presentation.un_sxContrary
#print axioms Lara.Presentation.un_sxList_Contrary
#print axioms Lara.Presentation.un_sxException
#print axioms Lara.Presentation.un_sxList_Exception
#print axioms Lara.Presentation.un_sxAdmEntry
#print axioms Lara.Presentation.un_sxList_AdmEntry
-- Duplicate-report groups (spec §4.3) and the @0.3 policy-level comparison surface.
#print axioms Lara.Presentation.un_sxDupGroup
#print axioms Lara.Presentation.un_sxMeasurand
#print axioms Lara.Presentation.un_sxList_Measurand
#print axioms Lara.Presentation.un_sxComparisonScheme
#print axioms Lara.Presentation.un_sxList_ComparisonScheme
#print axioms Lara.Presentation.un_sxList_Step
#print axioms Lara.Presentation.un_sxAttack
-- Presentation-only attack positions (@0.3, grammar §7 AMENDMENT / App. B.5).
#print axioms Lara.Presentation.un_sxSurfaceStep
#print axioms Lara.Presentation.un_sxList_SurfaceStep
#print axioms Lara.Presentation.un_sxSurfaceAttack
#print axioms Lara.Presentation.un_sxChallengeTarget
#print axioms Lara.Presentation.un_sxArgConcl
#print axioms Lara.Presentation.un_sxArgInstantiation
#print axioms Lara.Presentation.un_sxArg
-- Comparison blocks (@0.3, grammar App. B.3).
#print axioms Lara.Presentation.un_sxComparisonClaim
#print axioms Lara.Presentation.un_sxComparison
#print axioms Lara.Presentation.un_sxDecl
#print axioms Lara.Presentation.un_sxList_Decl
#print axioms Lara.Presentation.un_sxBackend
#print axioms Lara.Presentation.un_sxList_Backend
#print axioms Lara.Presentation.un_sxValueBinding
#print axioms Lara.Presentation.un_sxList_ValueBinding

-- Result 10 / C05: ND reference-adapter soundness + dependency exactness.
#print axioms Lara.ND.nd_relevance
#print axioms Lara.ND.nd_sound
#print axioms Lara.ND.fv_in_range
#print axioms Lara.ND.hyp_out_of_range_untypable
#print axioms Lara.ND.mem_shiftDown

-- Named nd@1 proof-term lowering (`lara-syntax@0.9`, #132; source-authored
-- formula annotations `lara-syntax@0.10`, #144): closed-tag and encoder
-- support, kernel conservativity, formula-annotation agreement with the
-- abstract proposition encoder, and structural agreement with the
-- independent named-term-to-de-Bruijn translation.  This mechanizes the pure
-- pass semantics; the Haskell classifier/resolver/proposition-encoder remain
-- validated-not-verified.
#print axioms Lara.NDNamed.NamedTag.parse_toString
#print axioms Lara.NDNamed.decodeFormula_encodeFormula
#print axioms Lara.NDNamed.decodeCert_encodeCert
#print axioms Lara.NDNamed.encodeFormula_markerFree
#print axioms Lara.NDNamed.encodeCert_markerFree
#print axioms Lara.NDNamed.lowerNamed_id_of_kernel
#print axioms Lara.NDNamed.lowerFormula_eq_translation
#print axioms Lara.NDNamed.lowerNamed_eq_translation

-- Layer C: the algorithm `infer` (port of Haskell `inferType`) decides the
-- relation `HasType` and returns exactly `fv` — ties the running checker to the
-- metatheory proved about the relation.
#print axioms Lara.ND.infer_sound
#print axioms Lara.ND.infer_complete
#print axioms Lara.ND.infer_deps_eq_fv
#print axioms Lara.ND.infer_iff
#print axioms Lara.ND.hasType_unique
#print axioms Lara.ND.Tag.parse_toString
#print axioms Lara.ND.decodeNat_repr
#print axioms Lara.ND.decodeNat_leading_zero_01
#print axioms Lara.ND.decodeNat_some_canonical
#print axioms Lara.ND.decodeFormula_list_bad_arity
#print axioms Lara.ND.decodeCert_list_bad_arity
#print axioms Lara.ND.decodeFormula_unknown_atom
#print axioms Lara.ND.decodeFormula_unknown_list
#print axioms Lara.ND.decodeCert_unknown_list
#print axioms Lara.ND.lookup_eq_getElem?
#print axioms Lara.ND.infer_agree

-- Result 8 / C03: abstract strict-step soundness (Theorem 1) + ND instantiation.
#print axioms Lara.Strict.StrictJudgment.ofReplay
#print axioms Lara.Strict.strict_step_sound
#print axioms Lara.Strict.ndReplay_iff
#print axioms Lara.Strict.ndBackend
#print axioms Lara.Strict.FrameTag.parse_toString
#print axioms Lara.Strict.charByteSize_toList
#print axioms Lara.Strict.splitColon_append
#print axioms Lara.Strict.takeUtf8_append
#print axioms Lara.Strict.parseFrame_frame
#print axioms Lara.Strict.decodeFramesAux_render
#print axioms Lara.Strict.decodeFrames_render
#print axioms Lara.Strict.frame_length_pos
#print axioms Lara.Strict.sourceTermsOfList_toList
#print axioms Lara.Strict.encodeTermKeys_eq_map
#print axioms Lara.Strict.decodeTermKeyAux_encode
#print axioms Lara.Strict.decodeTermKeys_encode
#print axioms Lara.Strict.payloadChars_le_renderFrames
#print axioms Lara.Strict.payloadChars_append
#print axioms Lara.Strict.atomTermDepth_le_key_length
#print axioms Lara.Strict.atomTermsDepth_le_keys_length
#print axioms Lara.Strict.decodeAtomKey_encodeAtomKey
#print axioms Lara.Strict.encodeAtomKey_injective
#print axioms Lara.Strict.ndEnc_iff
#print axioms Lara.Strict.nd_strict_step_sound

-- Issue #57: the rational-arithmetic domain-checker backend `ra@1` — the
-- full `Backend` instantiation (replay adequacy, certificate soundness via
-- witness cancellation, and the three obligation-4 laws), plus its
-- supporting integer-cancellation and extraction lemmas.
#print axioms Lara.RA.raBackend
#print axioms Lara.RA.raReplay_iff
#print axioms Lara.RA.raSound
#print axioms Lara.RA.raUses_covers
#print axioms Lara.RA.raUses_valid
#print axioms Lara.RA.raUses_account
#print axioms Lara.RA.mul_right_cancel
#print axioms Lara.RA.dropEq_of_witness
#print axioms Lara.RA.checkB_extract
#print axioms Lara.RA.decodeCert_witness_den_pos

-- The cell machinery shared by the rational-arithmetic backends
-- (`Lara.Strict.Cell` mirror): the cross-multiplied comparison mirrors and
-- the order facts the `ord@1` family rests on.
#print axioms Lara.Cell.ratEqB_iff
#print axioms Lara.Cell.ratGeB_iff
#print axioms Lara.Cell.ratLtB_iff
#print axioms Lara.Cell.ratLeB_iff
#print axioms Lara.Cell.ratLe_iff_lt_or_eq
#print axioms Lara.Cell.ratLt_irrefl
#print axioms Lara.Cell.ratLe_refl
#print axioms Lara.Cell.lt_of_getElem?_eq_some

-- The ordered-comparison domain-checker backend `ord@1` — the full `Backend`
-- instantiation (replay adequacy, certificate soundness, and the three
-- obligation-4 laws), plus the intra-family exclusivity lemmas that make
-- "num_lt/num_le declare no contrary pair" a theorem rather than a
-- workaround (design §3.2).
#print axioms Lara.Ord.ordBackend
#print axioms Lara.Ord.ordReplay_iff
#print axioms Lara.Ord.ordSound
#print axioms Lara.Ord.ordUses_covers
#print axioms Lara.Ord.ordUses_valid
#print axioms Lara.Ord.ordUses_account
#print axioms Lara.Ord.checkB_extract
#print axioms Lara.Ord.relHoldsB_iff
#print axioms Lara.Ord.lt_excl_lt
#print axioms Lara.Ord.lt_excl_le
#print axioms Lara.Ord.le_le_iff_eq
#print axioms Lara.Ord.ordModels_relHolds
#print axioms Lara.Ord.ordModels_excl_of_lt

-- Named certificate premise slots (lara-syntax@0.6, #105): the presentation
-- pass's payload-rewrite math over an abstract resolver.  The identity
-- theorem (no symbolic reference in scope → byte-identical pass-through,
-- dead-wire arm included) and the substitution theorem (a successful
-- lowering IS the declarative positional substitution SymNumericSubst),
-- plus the shape and position-wise engine lemmas they rest on.  Elaborator
-- name resolution and the error taxonomy stay validated-not-verified
-- (test/CertSlotsSpec.hs); these carry the rewrite metatheory.
#print axioms Lara.CertSlots.lower_id_of_no_symbolic
#print axioms Lara.CertSlots.lower_eq_numeric_subst
#print axioms Lara.CertSlots.matchSchema_shape
#print axioms Lara.CertSlots.lowerArgs_pointwise

-- The `comparison` surface form's direction-of-goodness contract
-- (lara-syntax@0.3 §1.2 / grammar Appendix B.3): the 2x2 lookup table
-- generating the `ord@1` goal agrees with the intended research meaning on
-- every cell, and the two polarities generate the same relation on transposed
-- operands — so a mis-declared polarity certifies the opposite claim, not a
-- weaker one.  Surface-level only: the Haskell elaborator stays
-- validated-not-verified (Lara.Admission).
#print axioms Lara.Comparison.goalOf_iff_better
#print axioms Lara.Comparison.goalOf_polarity_swap
#print axioms Lara.Comparison.better_polarity_swap
#print axioms Lara.Comparison.goalOf_polarity_mismatch_excl
#print axioms Lara.Comparison.better_excl
#print axioms Lara.Comparison.better_atLeastAsGood_antisymm
#print axioms Lara.Comparison.better_strict_imp_atLeastAsGood
#print axioms Lara.Comparison.betterB_iff

-- Result 3 (certificate half) / result 10 (dependency exactness), backend
-- layer: the fixed-core `uses` report interface (coverage, validity,
-- accounting over the full consulted context `Δ ++ T`), the derived closed
-- forms over data-only resolved theory (incl. the theory-coverage
-- specializations of `uses_covers`), and the ND adapter's discharging
-- proofs.
#print axioms Lara.Strict.selectSlots
#print axioms Lara.Strict.mem_selectSlots
#print axioms Lara.Strict.selectSlots_map
#print axioms Lara.Strict.Backend.models
#print axioms Lara.Strict.Backend.accepts
#print axioms Lara.Strict.Backend.replay
#print axioms Lara.Strict.Backend.replay_iff
#print axioms Lara.Strict.Backend.sound
#print axioms Lara.Strict.Backend.uses_valid_closed
#print axioms Lara.Strict.Backend.replay_theory_covers
#print axioms Lara.Strict.Backend.replay_theory_agnostic
#print axioms Lara.Strict.ndUses
#print axioms Lara.Strict.ndUses_account
#print axioms Lara.Strict.ndReplay_agree
#print axioms Lara.Strict.ndUses_valid
#print axioms Lara.Strict.ndUses_eq_infer_deps

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
#print axioms Lara.Support.certOkBOf_iff
#print axioms Lara.Support.certOkBOf_theory_covers
#print axioms Lara.Support.certOkOf_strict_step
#print axioms Lara.Support.SupportTerm.decEq
#print axioms Lara.Support.SupportTerm.decEqList
#print axioms Lara.Support.SupportTerm.decEqDischarges

-- Result 3 (certificate half) / spec §6 `certDeps`: strict-dependency
-- accountability at the support level — the per-node accounting through the
-- registry, the `certDeps` collection identity (both directions), and the
-- two resolution results: premise dependencies resolve to the exact premise
-- occurrence of their reporting node (`certDeps_resolved`), and theory
-- dependencies name a valid entry of the digest-resolved theory
-- (`certDeps_theory_valid`).
#print axioms Lara.Support.resolveSlot
#print axioms Lara.Support.stepDeps
#print axioms Lara.Support.certDeps
#print axioms Lara.Support.certDepsList
#print axioms Lara.Support.certDepsDis
#print axioms Lara.Support.mem_certDepsList
#print axioms Lara.Support.mem_certDepsDis
#print axioms Lara.Support.certDeps_mem_list
#print axioms Lara.Support.certDeps_mem_dis
#print axioms Lara.Support.certStepIn_typed
#print axioms Lara.Support.certOkOf_uses_account
#print axioms Lara.Support.cert_node_accounted
#print axioms Lara.Support.cert_steps_accounted
#print axioms Lara.Support.mem_certDeps_step
#print axioms Lara.Support.certStep_deps_subset
#print axioms Lara.Support.certDeps_resolved
#print axioms Lara.Support.certDeps_theory_valid

-- Result 1 executable half: Boolean side conditions and the support checker's
-- exact soundness/completeness bridge to `HasSupport`.
#print axioms Lara.Check.substDomainB_iff
#print axioms Lara.Check.atomsEquivB_iff
#print axioms Lara.Check.AtomsEquiv.length
#print axioms Lara.Check.AtomsEquiv.get
#print axioms Lara.Check.AtomsEquiv.of_get
#print axioms Lara.Check.strictNoQuestionB_iff
#print axioms Lara.Check.assuranceOkB_iff
#print axioms Lara.Check.answerOkB_iff
#print axioms Lara.Check.answersOkB_iff
#print axioms Lara.Check.knownAnswersOkB_eq_answersOkB
#print axioms Lara.Check.AnswersOk.length
#print axioms Lara.Check.AnswersOk.get
#print axioms Lara.Check.AnswersOk.of_get
#print axioms Lara.Check.inferSupport_sound
#print axioms Lara.Check.inferSupport_complete

-- Spec §7.1 freeze: typed positional attacks — checked source (§1 guarantee 4),
-- strict-unattackability, position-kind partition, and the coherence of local
-- attack checking with global support typing.
#print axioms Lara.Attack.attack_source_checked
#print axioms Lara.Attack.rebut_top_defeasible
#print axioms Lara.Attack.undercut_pos_defeasible
#print axioms Lara.Attack.undercut_target_rule
#print axioms Lara.Attack.undermine_target_leaf
#print axioms Lara.Attack.rebut_concl_coherent
#print axioms Lara.Attack.SubstExtends.refl
#print axioms Lara.Attack.SubstExtends.trans
#print axioms Lara.Attack.instPat_of_extends
#print axioms Lara.Attack.instPats_of_extends
#print axioms Lara.Attack.instAPat_of_extends
#print axioms Lara.Attack.matchPat_sound
#print axioms Lara.Attack.matchPats_sound
#print axioms Lara.Attack.matchAPat_sound
#print axioms Lara.Attack.matchPat_complete
#print axioms Lara.Attack.matchPats_complete
#print axioms Lara.Attack.matchAPat_complete
#print axioms Lara.Attack.emptySubstCanonAgrees
#print axioms Lara.Attack.contraryMatchDecl_iff
#print axioms Lara.Attack.contraryMatchB_iff

-- Exact executable positional attack checking, including finite exception
-- selection and cached-source/public adequacy.
#print axioms Lara.Check.exceptionMatchB_iff
#print axioms Lara.Check.checkAttackTarget_iff
#print axioms Lara.Check.checkAttackWithSource_sound
#print axioms Lara.Check.checkAttackWithSource_complete
#print axioms Lara.Check.checkAttack_sound
#print axioms Lara.Check.checkAttack_complete

-- Proof-bearing whole-program construction: deterministic duplicate boundary,
-- aligned checked-source cache, strengthened R1 endpoint boundary, and exact
-- relational soundness/completeness.
#print axioms Lara.Check.incompleteArgument_no_rejectClass
#print axioms Lara.Check.firstDuplicate_none_iff
#print axioms Lara.Check.CheckedArguments.cache_nodup
#print axioms Lara.Check.lookupChecked_term
#print axioms Lara.Check.lookupChecked_complete
#print axioms Lara.Check.checkProgram_sound
#print axioms Lara.Check.checkProgram_complete
#print axioms Lara.Check.checkProgram_accepted_source_declared
#print axioms Lara.Check.checkProgram_accepted_target_declared
#print axioms Lara.Check.checkProgram_nodes_complete

-- Spec §8 compile freeze: result 4 both halves (no untyped node or attack),
-- subargument closure extends the direct attack, and the N16 bridge at both
-- levels — argument (srcIn_iff_grounded) and exact four-state claim status
-- (srcStatus_iff). Result 6's source-vs-compiled half is no longer merely
-- oracle-parametric: the constructive checker-built edge decider
-- (`containsB`/`attackClosureB`/`edgeB`) discharges `Compile.Faithful` via
-- `edgeB_faithful`, so the specialized wrappers (`srcIn_iff_checkedGrounded`,
-- `srcStatus_checked`, `srcStatus_iff_checked`) hold with no oracle hypothesis.
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
#print axioms Lara.Compile.hasSupport_disNodup
#print axioms Lara.Compile.lookupDis_some_mem
#print axioms Lara.Compile.containsB_iff
#print axioms Lara.Compile.attackClosureB_iff
#print axioms Lara.Compile.edgeB_iff
#print axioms Lara.Compile.edgeB_faithful
#print axioms Lara.Compile.srcIn_iff_checkedGrounded
#print axioms Lara.Compile.srcStatus_checked
#print axioms Lara.Compile.srcStatus_iff_checked

-- Spec §8.1 Path-B policy validator: the finite strict-reachable set denotes
-- the relational least set, and executable wf(Pi) is exact.
#print axioms Lara.Policy.strictReachable_closed
#print axioms Lara.Policy.strictReachable_iff_mem
#print axioms Lara.Policy.aPatMayOverlap_of_instances
#print axioms Lara.Policy.wfB_iff
#print axioms Lara.Policy.wellFormed_no_strict_contrary_left
#print axioms Lara.Policy.wellFormed_no_strict_contrary_right
#print axioms Lara.Policy.Regression.overlap_is_not_pattern_equality
#print axioms Lara.Policy.Regression.strict_conclusion_instance
#print axioms Lara.Policy.Regression.declared_instance_is_contrary
#print axioms Lara.Policy.Regression.instantiated_strict_contrary_rejected

-- Concrete conformance examples: obligation accounting (mixed/nested/missing),
-- subterm traversal boundaries, and subargument-closure superset behavior with
-- a concrete edge decider and grounded verdict.
#print axioms Lara.Examples.slotTheory
#print axioms Lara.Examples.registry_exact_digest_accepts
#print axioms Lara.Examples.registry_exact_digest_rejects
#print axioms Lara.Examples.registry_backend_absent
#print axioms Lara.Examples.registry_version_mismatch
#print axioms Lara.Examples.registry_digest_unknown
#print axioms Lara.Examples.registry_success_bridge

-- The `ord@1` entry in the example registry: the empty-theory resolution
-- discipline `Lara.Driver.buildRegistry` uses, and the invariant the
-- premise-only slot guard rests on (the consulted context is the premises).
#print axioms Lara.Examples.registry_ord_registered
#print axioms Lara.Examples.ord_resolveTheory_known
#print axioms Lara.Examples.ord_resolveTheory_unknown
#print axioms Lara.Examples.ord_replay_context_is_premises
#print axioms Lara.Examples.ord_models_context_is_premises

-- The `ra@1` entry, on the same terms: the seam-wide premise-only parity
-- decision means both rational-arithmetic backends resolve a known digest to
-- the empty theory, so an accepted step is accountable to the premises alone.
#print axioms Lara.Examples.registry_ra_registered
#print axioms Lara.Examples.ra_resolveTheory_known
#print axioms Lara.Examples.ra_resolveTheory_unknown
#print axioms Lara.Examples.ra_replay_context_is_premises
#print axioms Lara.Examples.ra_models_context_is_premises
#print axioms Lara.Examples.registry_missing_bridge
#print axioms Lara.Examples.registry_premises_before_theory
#print axioms Lara.Examples.registry_fixed_theory_order
-- The six executable ND conformance matrices are enforced with `#guard` in
-- `Lara.Examples`; unlike theorems, commands do not have an axiom set to print.
#print axioms Lara.Examples.ndEnc_distinct_atoms
#print axioms Lara.Examples.ndEnc_numeric_canonical_equal
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
#print axioms Lara.Examples.check_declared_leaf
#print axioms Lara.Examples.check_mixed_holes
#print axioms Lara.Examples.check_nested_obligations
#print axioms Lara.Examples.check_discharge_propagation
#print axioms Lara.Examples.check_obligation_deduplication
#print axioms Lara.Examples.check_missing_question
#print axioms Lara.Examples.check_question_overlap
#print axioms Lara.Examples.check_premise_mismatch
#print axioms Lara.Examples.check_discharge_mismatch
#print axioms Lara.Examples.check_discharge_precedes_question_accounting
#print axioms Lara.Examples.check_missing_leaf
#print axioms Lara.Examples.check_missing_rule_precedence
#print axioms Lara.Examples.check_duplicate_substitution_precedence
#print axioms Lara.Examples.check_substitution_domain
#print axioms Lara.Examples.check_substitution_extra_binding
#print axioms Lara.Examples.check_premise_instantiation
#print axioms Lara.Examples.check_conclusion_instantiation
#print axioms Lara.Examples.check_too_few_premises
#print axioms Lara.Examples.check_too_many_premises
#print axioms Lara.Examples.check_child_error_precedes_parent_shape
#print axioms Lara.Examples.check_duplicate_declarations
#print axioms Lara.Examples.check_duplicate_discharges
#print axioms Lara.Examples.check_duplicate_holes
#print axioms Lara.Examples.check_undeclared_discharge
#print axioms Lara.Examples.check_undeclared_hole
#print axioms Lara.Examples.check_answer_instantiation
#print axioms Lara.Examples.check_strict_questions
#print axioms Lara.Examples.check_strict_trusted_success
#print axioms Lara.Examples.check_strict_cert_success
#print axioms Lara.Examples.certDeps_theory_entry_reported
#print axioms Lara.Examples.certDeps_premise_reported
#print axioms Lara.Examples.check_assurance_wrong_mode
#print axioms Lara.Examples.check_assurance_trusted_disallowed
#print axioms Lara.Examples.check_assurance_unallowlisted
#print axioms Lara.Examples.check_assurance_backend_missing
#print axioms Lara.Examples.check_assurance_digest_missing
#print axioms Lara.Examples.check_assurance_replay_rejected
#print axioms Lara.Examples.defeasible_rebut_typed
#print axioms Lara.Examples.strict_root_rebut_rejected
#print axioms Lara.Examples.nested_undercut_typed
#print axioms Lara.Examples.mixed_path_undermine_typed
#print axioms Lara.Examples.contrary_shared_substitution
#print axioms Lara.Examples.contrary_shared_substitution_rejects
#print axioms Lara.Examples.contrary_repeated_variable
#print axioms Lara.Examples.contrary_repeated_variable_rejects
#print axioms Lara.Examples.contrary_canonical_numeric
#print axioms Lara.Examples.contrary_nonidempotent_repeated_rejects
#print axioms Lara.Examples.contrary_constructor_arity_rejects
#print axioms Lara.Examples.check_rebut_success
#print axioms Lara.Examples.check_nested_undercut_success
#print axioms Lara.Examples.check_mixed_undermine_success
#print axioms Lara.Examples.check_rebut_strict_root
#print axioms Lara.Examples.check_undercut_strict_occurrence
#print axioms Lara.Examples.check_undercut_undefined_position
#print axioms Lara.Examples.check_undermine_undefined_position
#print axioms Lara.Examples.check_undercut_wrong_occurrence
#print axioms Lara.Examples.check_undermine_wrong_occurrence
#print axioms Lara.Examples.check_rebut_wrong_occurrence
#print axioms Lara.Examples.check_rebut_missing_contrary
#print axioms Lara.Examples.check_undermine_missing_contrary
#print axioms Lara.Examples.check_rebut_missing_target_rule
#print axioms Lara.Examples.check_undercut_missing_target_rule
#print axioms Lara.Examples.check_rebut_target_conclusion_instantiation
#print axioms Lara.Examples.check_undercut_exception_instantiation
#print axioms Lara.Examples.check_undercut_missing_exception
#print axioms Lara.Examples.check_undercut_exception_mismatch
#print axioms Lara.Examples.check_undermine_undeclared_leaf
#print axioms Lara.Examples.check_attack_source_failure_rebut
#print axioms Lara.Examples.check_attack_source_failure_undercut
#print axioms Lara.Examples.check_attack_source_failure_undermine
#print axioms Lara.Examples.sideWrap
#print axioms Lara.Examples.vWrap_typed
#print axioms Lara.Examples.kAtk_typed
#print axioms Lara.Examples.PExCheck_success
#print axioms Lara.Examples.PExCheck_ok
#print axioms Lara.Examples.PEx_args
#print axioms Lara.Examples.PEx_atts
#print axioms Lara.Examples.supportTerm_nested_structural_equality
#print axioms Lara.Examples.supportTerm_certificate_payload_distinct
#print axioms Lara.Examples.registry_wrapped_certificate_accepts
#print axioms Lara.Examples.check_wrapped_certificate_success
#print axioms Lara.Examples.check_program_empty
#print axioms Lara.Examples.check_program_one_complete
#print axioms Lara.Examples.check_program_full_PEx
#print axioms Lara.Examples.check_program_certificate_payload_distinct
#print axioms Lara.Examples.check_program_duplicate_first_pair
#print axioms Lara.Examples.check_program_duplicate_crossing_first_pair
#print axioms Lara.Examples.check_program_incomplete_exact
#print axioms Lara.Examples.check_program_incomplete_not_rejection_class
#print axioms Lara.Examples.check_program_support_error_wrapped
#print axioms Lara.Examples.check_program_first_argument_failure
#print axioms Lara.Examples.check_program_undeclared_source
#print axioms Lara.Examples.check_program_undeclared_target
#print axioms Lara.Examples.check_program_endpoint_reject_classes
#print axioms Lara.Examples.check_program_rebut_error_wrapped
#print axioms Lara.Examples.check_program_undercut_error_wrapped
#print axioms Lara.Examples.check_program_undermine_error_wrapped
#print axioms Lara.Examples.check_program_first_attack_failure
#print axioms Lara.Examples.check_program_many_attacks_one_source
#print axioms Lara.Examples.closure_edge_direct
#print axioms Lara.Examples.closure_edge_wrapper
#print axioms Lara.Examples.closure_no_edge_unrelated
#print axioms Lara.Examples.edge_fixture_iff
#print axioms Lara.Examples.edgeBEx_faithful
#print axioms Lara.Examples.closure_grounded_verdict
#print axioms Lara.Examples.checked_edge_fixture
#print axioms Lara.Examples.checked_edge_fixture_faithful
#print axioms Lara.Examples.edgeB_PEx_eq_edgeBEx
#print axioms Lara.Examples.checked_closure_status
#print axioms Lara.Examples.checked_src_status_exists
#print axioms Lara.Examples.containsB_wrapper_leaf
#print axioms Lara.Examples.containsB_leaf_unrelated
#print axioms Lara.Examples.attackClosureB_direct
#print axioms Lara.Examples.attackClosureB_wrapper
#print axioms Lara.Examples.containsB_inst_self
#print axioms Lara.Examples.containsB_discharge_hit
#print axioms Lara.Examples.containsB_dupkey_true
#print axioms Lara.Examples.containsB_dupkey_not_contains
#print axioms Lara.Examples.vDup_not_disNodup
#print axioms Lara.Examples.attackClosureB_rebut
#print axioms Lara.Examples.attackClosureB_positional
#print axioms Lara.Examples.attackClosureB_badpos

-- Result 5 / C07: grounded termination + determinism (finite stabilization).
#print axioms Lara.Grounded.grounded_stable
#print axioms Lara.Grounded.grounded_fixpoint

-- Result 6 / C08 (abstract AF layer): declarative grounded ≡ executable grounded
-- labelling over any AF. Lara.Compile above now exercises the source compile
-- relation oracle-parametrically; `compile_attack_iff` remains the older abstract
-- characterization at this layer.
-- `statusC_gap_iff` mechanizes the N17-(1) "gap only on empty complete support" half.
#print axioms Lara.Grounded.directIn_iff
#print axioms Lara.Grounded.labelC_inn_iff
#print axioms Lara.Grounded.labelC_out_iff
#print axioms Lara.Grounded.labelC_undec_iff
#print axioms Lara.Grounded.status_preservation
#print axioms Lara.Grounded.compile_attack_iff
#print axioms Lara.Grounded.statusC_gap_iff

-- Issue 18 / result 7: attack-complete checked units. This section audits the
-- exact executable/declarative bridges, accepted-unit projections, generic
-- grounded conflict-freedom, and every focused matrix fixture added with the
-- feature.
#print axioms Lara.Attack.contraryMatch_congr
#print axioms Lara.Compile.conflictAttackableB_iff
#print axioms Lara.Compile.coveredB_iff
#print axioms Lara.Compile.complete_conflict_edge
#print axioms Lara.Check.missingConflict_no_rejectClass
#print axioms Lara.Check.CheckedArguments.nodes_terms
#print axioms Lara.Check.sourceAttackBucket_mem_iff
#print axioms Lara.Check.conflictCache_terms
#print axioms Lara.Check.sourceAttackBucket_coveredB_iff
#print axioms Lara.Check.firstMissingConflict_none_iff
#print axioms Lara.Check.checkProgramDetailed_sound
#print axioms Lara.Check.checkProgramDetailed_complete
#print axioms Lara.Policy.firstDuplicateRuleId?_none_iff
#print axioms Lara.Policy.lookupRuleDecl_some_mem
#print axioms Lara.Policy.lookupRuleDecl_of_mem_nodup
#print axioms Lara.Policy.firstViolation_none_iff
#print axioms Lara.Policy.firstViolation_some_sound
#print axioms Lara.Check.Unit.checkUnit_sound
#print axioms Lara.Check.Unit.checkUnit_complete
#print axioms Lara.Unit.CheckedUnit.nodes_terms
#print axioms Lara.Unit.CheckedUnit.attack_complete
#print axioms Lara.Grounded.iter_conflictFree
#print axioms Lara.Grounded.grounded_conflictFree
#print axioms Lara.Grounded.labelC_inn_no_attack
#print axioms Lara.Grounded.statusC_justified_iff
#print axioms Lara.Grounded.statusC_empty_support_not_justified
#print axioms Lara.Grounded.statusC_all_out_not_justified
#print axioms Lara.Consistency.wellFormed_contrary_target_attackable
#print axioms Lara.Consistency.mem_claimSupportFor_iff
#print axioms Lara.Consistency.contrary_args_not_both_grounded
#print axioms Lara.Consistency.contrary_claims_not_both_justified

#print axioms Lara.Examples.check_unit_valid
#print axioms Lara.Examples.rawUnitCheck_ok
#print axioms Lara.Examples.check_unit_duplicate_rule_location
#print axioms Lara.Examples.check_unit_r12_location
#print axioms Lara.Examples.check_unit_policy_before_duplicate_argument
#print axioms Lara.Examples.check_unit_duplicate_rule_before_policy_and_program
#print axioms Lara.Examples.unit_error_reject_classes
#print axioms Lara.Examples.check_unit_duplicate_argument_wrapped
#print axioms Lara.Examples.check_unit_support_error_wrapped
#print axioms Lara.Examples.check_unit_typed_attack_error_wrapped
#print axioms Lara.Examples.check_unit_missing_conflict_wrapped
#print axioms Lara.Examples.checked_unit_retained_alignment
#print axioms Lara.Examples.checked_unit_final_status

#print axioms Lara.Examples.AttackCompleteness.leaf_conflict_attackable
#print axioms Lara.Examples.AttackCompleteness.defeasible_root_conflict_attackable
#print axioms Lara.Examples.AttackCompleteness.strict_root_not_conflict_attackable
#print axioms Lara.Examples.AttackCompleteness.unknown_rule_not_conflict_attackable
#print axioms Lara.Examples.AttackCompleteness.direct_attack_covered
#print axioms Lara.Examples.AttackCompleteness.wrapper_closure_covered
#print axioms Lara.Examples.AttackCompleteness.wrong_target_not_covered
#print axioms Lara.Examples.AttackCompleteness.no_attacks_not_covered
#print axioms Lara.Examples.AttackCompleteness.same_edge_rebut_typed
#print axioms Lara.Examples.AttackCompleteness.same_edge_different_reason_covered
#print axioms Lara.Examples.AttackCompleteness.missing_conflict_no_reject_class
#print axioms Lara.Examples.AttackCompleteness.first_missing_pair
#print axioms Lara.Examples.AttackCompleteness.crossing_pair_source_major
#print axioms Lara.Examples.AttackCompleteness.closure_covered_wrapper_accepted
#print axioms Lara.Examples.AttackCompleteness.nonmatching_attack_decoy
#print axioms Lara.Examples.AttackCompleteness.self_conflict_missing_at_origin
#print axioms Lara.Examples.AttackCompleteness.support_error_precedes_missing_conflict
#print axioms Lara.Examples.AttackCompleteness.attack_error_precedes_missing_conflict
#print axioms Lara.Examples.AttackCompleteness.detailed_empty_accepted
#print axioms Lara.Examples.AttackCompleteness.detailed_no_contrary_accepted
#print axioms Lara.Examples.AttackCompleteness.detailed_strict_root_contrary_not_required
#print axioms Lara.Examples.AttackCompleteness.legacy_acceptance_unchanged
#print axioms Lara.Examples.AttackCompleteness.legacy_support_error_unchanged
#print axioms Lara.Examples.AttackCompleteness.legacy_attack_error_unchanged
#print axioms Lara.Examples.AttackCompleteness.detailed_default_heartbeat_stress
#print axioms Lara.Examples.AttackCompleteness.stressDetailed_ok
#print axioms Lara.Examples.AttackCompleteness.retained_node_alignment
#print axioms Lara.Examples.AttackCompleteness.nonempty_source_buckets_exact
#print axioms Lara.Examples.AttackCompleteness.stress_source_bucket_adequacy
#print axioms Lara.Examples.AttackCompleteness.detailed_sound_fixture
#print axioms Lara.Examples.AttackCompleteness.detailed_complete_fixture

#print axioms Lara.Examples.PolicyAcceptance.empty_policy_accepted
#print axioms Lara.Examples.PolicyAcceptance.defeasible_only_accepted
#print axioms Lara.Examples.PolicyAcceptance.first_strict_violation_located
#print axioms Lara.Examples.PolicyAcceptance.multiple_violations_report_first_rule
#print axioms Lara.Examples.PolicyAcceptance.multiple_violations_report_first_contrary_pair
#print axioms Lara.Examples.PolicyAcceptance.duplicate_rule_identifier_has_first_two_indices
#print axioms Lara.Examples.PolicyAcceptance.valid_unique_policy_accepted
#print axioms Lara.Examples.PolicyAcceptance.known_rule_lookup
#print axioms Lara.Examples.PolicyAcceptance.duplicate_rule_lookup_returns_first_declaration
#print axioms Lara.Examples.PolicyAcceptance.unknown_rule_lookup_none

#print axioms Lara.Examples.GroundedConsistency.one_way_grounded
#print axioms Lara.Examples.GroundedConsistency.one_way_grounded_conflict_free
#print axioms Lara.Examples.GroundedConsistency.cycle_grounded_empty
#print axioms Lara.Examples.GroundedConsistency.cycle_allowed_and_conflict_free
#print axioms Lara.Examples.GroundedConsistency.empty_support_not_justified
#print axioms Lara.Examples.GroundedConsistency.all_out_support_not_justified
#print axioms Lara.Examples.GroundedConsistency.grounded_default_heartbeat_regression
#print axioms Lara.Examples.GroundedConsistency.numeric_unit_accepted
#print axioms Lara.Examples.GroundedConsistency.claim_support_zero
#print axioms Lara.Examples.GroundedConsistency.claim_support_one_with_decoy
#print axioms Lara.Examples.GroundedConsistency.claim_support_multiple_canonical_equivalent
#print axioms Lara.Examples.GroundedConsistency.claim_support_noisy_equivalent_same_order
#print axioms Lara.Examples.GroundedConsistency.complete_claim_projection_holes_empty
#print axioms Lara.Examples.GroundedConsistency.missing_self_edge_rejected
#print axioms Lara.Examples.GroundedConsistency.typed_self_edge_accepted
#print axioms Lara.Examples.GroundedConsistency.covered_self_edge_check_ok
#print axioms Lara.Examples.GroundedConsistency.self_attacking_node_not_grounded
#print axioms Lara.Examples.GroundedConsistency.self_claim_support_includes_node
#print axioms Lara.Examples.GroundedConsistency.computed_self_claim_not_justified
#print axioms Lara.Examples.GroundedConsistency.computed_self_claim_result7

-- Result 9 (backend replacement / Theorem 2, Model A): uniform injective
-- certificate relabel preserves the compiled AF and every claim status.
#print axioms Lara.Erase.mapAssur_injective
#print axioms Lara.Erase.mapAssur_eq_iff
#print axioms Lara.Erase.mapAssurAtt_source
#print axioms Lara.Erase.lookupDis_mapAssurDis
#print axioms Lara.Erase.mapAssur_subterm
#print axioms Lara.Erase.containsB_mapAssur
#print axioms Lara.Erase.attackClosureB_mapAssur
#print axioms Lara.Erase.coveredB_relabel
#print axioms Lara.Erase.edgeB_relabel
#print axioms Lara.Erase.checkedAF_relabel
#print axioms Lara.Erase.backend_replacement
#print axioms Lara.Erase.labelC_relabel

-- Result 9 (transport): a uniform injective relabel preserves well-checkedness,
-- so backend replacement is non-vacuous by construction.
#print axioms Lara.Erase.mapAssurDis_eq
#print axioms Lara.Erase.mapAssurAtt_target
#print axioms Lara.Erase.hasSupport_mapAssur
#print axioms Lara.Erase.hasAttack_mapAssur
#print axioms Lara.Erase.mapCertProg_args
#print axioms Lara.Erase.mapCertProg_atts
#print axioms Lara.Erase.backend_replacement_transport

-- Duplicate-report groups (spec §4.3, issue #38): the frozen consistency and
-- quarantine/escalation definitions and their metatheory.
#print axioms Lara.Groups.all_equiv_head_iff
#print axioms Lara.Groups.consistentB_iff
#print axioms Lara.Groups.mem_quarantined_iff
#print axioms Lara.Groups.quarantined_arg_excluded
#print axioms Lara.Groups.quarantined_leaf_absent
#print axioms Lara.Groups.conflictReject_iff

-- Conservative public reporting for quarantine-affected claims (spec §4.3,
-- issue #76): the locality lemma and the non-promotion / preservation results
-- (preservation requires equal complete-support sets), plus the declared-index
-- seed obligations and the compact production-AF bridge (issue #80).
#print axioms Lara.Blocked.directIn_transfer
#print axioms Lara.Blocked.directOut_transfer
#print axioms Lara.Blocked.directIn_reflect
#print axioms Lara.Blocked.directOut_reflect
#print axioms Lara.Blocked.directIn_iff_of_unblocked
#print axioms Lara.Blocked.directOut_iff_of_unblocked
#print axioms Lara.Blocked.labelC_agree
#print axioms Lara.Blocked.justified_nonpromotion
#print axioms Lara.Blocked.statusC_agree
#print axioms Lara.Blocked.closure_stable
#print axioms Lara.Blocked.seed_subset_blocked
#print axioms Lara.Blocked.blocked_closed
#print axioms Lara.Blocked.blocking_of_seed
#print axioms Lara.BlockedProgram.coveredB_mono
#print axioms Lara.BlockedProgram.edgeIn_eq
#print axioms Lara.BlockedProgram.edgeIn_mono
#print axioms Lara.BlockedProgram.selectAligned_subset
#print axioms Lara.BlockedProgram.retainedIndices_subset
#print axioms Lara.BlockedProgram.retained_lengths_eq
#print axioms Lara.BlockedProgram.retainedArguments_eq_filter
#print axioms Lara.BlockedProgram.retained_lookup
#print axioms Lara.BlockedProgram.retained_lookup_of_mem
#print axioms Lara.BlockedProgram.directIn_embed
#print axioms Lara.BlockedProgram.directOut_embed
#print axioms Lara.BlockedProgram.labelC_inn_embed
#print axioms Lara.BlockedProgram.statusC_justified_embed
#print axioms Lara.BlockedProgram.compile_checkedAF_embedding
#print axioms Lara.BlockedProgram.blockedSeed_hmissing
#print axioms Lara.BlockedProgram.blockedSeed_hedge
#print axioms Lara.BlockedProgram.blocking_of_blockedSeed
#print axioms Lara.BlockedProgram.mem_liftSupport_iff
#print axioms Lara.BlockedProgram.supportBlocked_false_unblocked
#print axioms Lara.BlockedProgram.supportBlocked_false_of_not_mem
#print axioms Lara.BlockedProgram.supportBlocked_false_of_not_mem_blockedQueries
#print axioms Lara.BlockedProgram.claimSupportFor_mem_checkedAF
#print axioms Lara.BlockedProgram.production_justified_nonpromotion
#print axioms Lara.BlockedProgram.production_justified_nonpromotion_of_not_blocked
#print axioms Lara.BlockedProgram.checked_production_justified_nonpromotion_of_not_blocked

/-! ### M0 — the frozen compilation carrier and invariant record (issue #183) -/

#print axioms Lara.Invariants.compileUnit_size
#print axioms Lara.Invariants.erase_compileUnit
#print axioms Lara.Invariants.compileUnit_ranged
#print axioms Lara.Invariants.compileUnit_conflictComplete
#print axioms Lara.Invariants.compileUnit_invariant
#print axioms Lara.Invariants.compileUnit_selfConflict
#print axioms Lara.Invariants.support_compileUnit
#print axioms Lara.Invariants.status_compileUnit

/-! ### M0 rejecting counterexamples -/

#print axioms Lara.Examples.CompilerInvariants.unrangedEx_not_invariant
#print axioms Lara.Examples.CompilerInvariants.unrangedEx_not_realizable
#print axioms Lara.Examples.CompilerInvariants.unforcedConflictEx_not_invariant
#print axioms Lara.Examples.CompilerInvariants.unforcedConflictEx_not_realizable
#print axioms Lara.Examples.CompilerInvariants.selfContrary
#print axioms Lara.Examples.CompilerInvariants.unforcedSelfConflict_not_invariant
#print axioms Lara.Examples.CompilerInvariants.sharedContrary
#print axioms Lara.Examples.CompilerInvariants.unforcedDistinctConflict_not_invariant
#print axioms Lara.Examples.CompilerInvariants.closure_rejects_noncontaining_target
#print axioms Lara.Examples.CompilerInvariants.selfEdgeUnit_nodes
#print axioms Lara.Examples.CompilerInvariants.selfEdgeUnit_selfEdge
