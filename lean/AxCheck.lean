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
import Lara.Evidence.Composition
import Lara.BHL.Types
import Lara.BHL.Numeric
import Lara.BHL.ReferenceAudit
import Lara.BHL.Value
import Lara.BHL.History
import Lara.BHL.State
import Lara.BHL.Trace
import Lara.BHL.TraceLaws
import Lara.BHL.Model
import Lara.BHL.ModelLaws
import Lara.Examples.BHLModel
import Lara.BHL.Ghost
import Lara.BHL.NumericalEvent
import Lara.BHL.Syntax
import Lara.BHL.Interpretation
import Lara.BHL.Assertion
import Lara.BHL.AssertionLaws
import Lara.BHL.Belief
import Lara.BHL.GhostTransforms
import Lara.BHL.GhostSubstitution
import Lara.BHL.Substitution
import Lara.BHL.BeliefEventLaws
import Lara.BHL.BeliefLaws
import Lara.BHL.Dependencies
import Lara.Examples.BHLBelief
import Lara.BHL.Program
import Lara.BHL.Execution
import Lara.BHL.ProgramLaws
import Lara.BHL.ExecutionLaws
import Lara.BHL.ControlGraph
import Lara.BHL.Parallel
import Lara.Examples.BHLExecution
import Lara.BHL.Derivation
import Lara.BHL.Soundness
import Lara.BHL.StatisticalFrame
import Lara.BHL.StatisticalRules
import Lara.Examples.BHLSoundnessDataset
import Lara.Examples.BHLSoundnessScience
import Lara.Examples.BHLSoundness
import Lara.BHL.ControlCoding
import Lara.BHL.ControlMetadata
import Lara.BHL.WeakestLiberal
import Lara.BHL.WlpRepresentation
import Lara.BHL.ControlLogData
import Lara.BHL.ControlLogLaws
import Lara.BHL.ControlLogSyntax
import Lara.BHL.ControlLogTerms
import Lara.BHL.CompletenessCore
import Lara.BHL.ControlLogEdges
import Lara.BHL.ControlLogBinders
import Lara.BHL.Completeness
import Lara.Examples.BHLCompleteness
import Lara.BHL.FiniteProbability
import Lara.BHL.Tests.Binary
import Lara.Examples.BHLBinaryModel
import Lara.Examples.BHLBinaryScience
import Lara.Examples.BHLBinaryRuns
import Lara.Examples.BHLStatistical
import Lara.Examples.BHLFiniteBelief
import Lara.BHL.RuleCode
import Lara.BHL.Check
import Lara.BHL.FiniteModel
import Lara.BHL.FiniteExecution
import Lara.BHL.CheckedMethods
import Lara.ND
import Lara.NDNamed
import Lara.Strict
import Lara.Cell
import Lara.RA
import Lara.Ord
import Lara.Insp
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
import Lara.Map.Qualify
import Lara.Map.Batch
import Lara.Map.Link
import Lara.Policy
import Lara.Sigma
import Lara.Check
import Lara.Driver
import Lara.Map.Driver
import Lara.Examples
import Lara.Examples.AttackCompleteness
import Lara.Examples.EvidenceBlocked
import Lara.Invariants
import Lara.Realizability
import Lara.Complexity.Numeral
import Lara.Complexity.Gadget
import Lara.Complexity.Reduction
import Lara.Complexity
import Lara.Examples.Complexity
import Lara.Examples.Complexity.Realization
import Lara.Examples.CompilerInvariants
import Lara.Examples.PolicyAcceptance
import Lara.Examples.GroundedConsistency
import Lara.Examples.Realizability
import Lara.Semantics
import Lara.Observation
import Lara.Semantics.Sublists
import Lara.Examples.Semantics
import Lara.Examples.SurfaceTransport
import Lara.Examples.SurfaceTransportAttack
import Lara.Examples.SurfaceTransportContext
import Lara.Examples.SurfaceHoles
import Lara.Update
import Lara.Update.Discharge
import Lara.Update.Completion
import Lara.Examples.Update
import Lara.Examples.UpdateCompletion
import Lara.Invariants.Merge
import Lara.Context.Fragment
import Lara.Context.Link
import Lara.Context.LinkHoles
import Lara.Context.Merge
import Lara.Context.Compose
import Lara.Context.Equivalence
import Lara.Invariants.Observation
import Lara.Context.Observation
import Lara.ListRel
import Lara.Context.Parametricity
import Lara.Context.FiniteExtension
import Lara.Examples.ContextSemantics
import Lara.Examples.ContextualSeparation
import Lara.Context.Holes.Transport
import Lara.Examples.TermHoles
import Lara.Context.Surface
import Lara.Examples.Linking
import Lara.Examples.LinkHoles
import Lara.Examples.CertificateCollapse
import Lara.Examples.BackendComposition
import Lara.Surface.Syntax
import Lara.Surface.Binding
import Lara.Surface.ValueBinding
import Lara.Surface.Comparison
import Lara.Surface.Check
import Lara.Surface.Elaborate
import Lara.Surface.Correctness
import Lara.Surface.Observation
import Lara.Examples.Surface
import Lara.PresentationParity
import Lara.PW.Outer
import Lara.PW.Uniform
import Lara.PW.Compare
import Lara.PW.Instance
import Lara.PW.Translation
import Lara.PW.Structural
import Lara.Examples.PW
import Lara.Examples.AxiomWithdrawal
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
import Lara.PW.Sorted
import Lara.Examples.PWSorted
import Lara.PW.Surface
import Lara.Examples.PWSurface
import Lara.PW.Declared
import Lara.PW.Wire
import Lara.PW.Finite
import Lara.Examples.PWDeclared
import Lara.Examples.PWWire
import Lara.Examples.PWFinite
import Lara.Examples.PWFileHost
import Lara.PW.Run
import Lara.Examples.PWRun

open Lara

-- The closed wire keyword vocabulary is injective, as required by the Haskell
-- Map-backed reverse lookup.
#print axioms Lara.Driver.tagToString_injective

-- The same, for the multi-artifact map's own keyword table. Both
-- Haskell map tables derive their reverse lookup by enumerating their tag type,
-- so a spelling collision would break the inverse silently rather than failing
-- to compile.
#print axioms Lara.Map.Driver.mtagToString_injective

-- Result 13 (the many-sorted signature, `lara-core@0.2`).
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

-- The wire reader's nesting bound, proved rather than only differentialled
-- The reader used to be a `partial def` mutual block, about which
-- nothing is provable; it is now total (well-founded on the remaining input,
-- with `Parsed` carrying the consumption proof `parseList`'s element loop
-- needs), which is what makes these statements reachable at all.
--   * the bound fires before dispatch, on depth alone;
--   * a failed element read is reported at the post-`skipSpace` position, which
--     is why the Haskell and Lean columns agree;
--   * any input nesting deeper than `maxDepth` is refused with the depth
--     message at line 1, column `maxDepth + 2`.
#print axioms Lara.Driver.parseForm_of_maxDepth_lt
#print axioms Lara.Driver.parseList_error_of_parseForm_error
#print axioms Lara.Driver.parseList_of_maxDepth_lt
#print axioms Lara.Driver.parseForm_nested_error
#print axioms Lara.Driver.parseWire_nested_error
-- The consumption and position lemmas the totality argument and the located
-- column rest on.
#print axioms Lara.Driver.step_input
#print axioms Lara.Driver.step_length_lt
#print axioms Lara.Driver.step_length_le
#print axioms Lara.Driver.step_of_cons
#print axioms Lara.Driver.skipComment_length_le
#print axioms Lara.Driver.skipSpace_length_le
#print axioms Lara.Driver.skipSpace_eq_self
#print axioms Lara.Driver.skipSpace_eq_self_startsForm
#print axioms Lara.Driver.spanBare_length
#print axioms Lara.Driver.spanBare_fst_ne_nil
#print axioms Lara.Driver.spanBare_snd_length_lt
#print axioms Lara.Driver.isBareChar_props
#print axioms Lara.Driver.startsForm_of_isBareChar
#print axioms Lara.Driver.startsForm_opens
#print axioms Lara.Driver.opens_add

-- Policy admission at the trusted source boundary (metatheory plan Task 2):
-- the declarative judgment, its correspondence with the evaluator, the two
-- context layers, the endpoint-safe prune, the canonical audit, the
-- all-admit identity, restrictiveness, rejection, and source non-promotion.
#print axioms Lara.Admission.buildGamma_append_of_some
#print axioms Lara.Admission.buildGamma_append_ne
#print axioms Lara.Admission.buildGamma_append_fresh
#print axioms Lara.Admission.buildGamma_some_mem
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
#print axioms Lara.equiv_iff_nf_eq
#print axioms Lara.equiv_refl
#print axioms Lara.equiv_symm
#print axioms Lara.equiv_trans
#print axioms Lara.nfTerm_idem
#print axioms Lara.nfTerms_idem
#print axioms Lara.nf_idem
#print axioms Lara.equiv_nf
#print axioms Lara.no_reorder

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

-- Named nd@1 proof-term lowering (`lara-syntax@0.9`; source-authored
-- formula annotations `lara-syntax@0.10`): closed-tag and encoder
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

-- The rational-arithmetic domain-checker backend `ra@1` — the
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

-- The static code-inspection domain-checker backend `insp@1` —
-- the full `Backend` instantiation (replay adequacy, certificate soundness,
-- and the three obligation-4 laws), plus the domain theory: the closed-world
-- step itself, the diff decomposition, and the two halves of the
-- contrary-pair argument (exclusive at a shared inspection leaf, jointly
-- satisfiable across two).
#print axioms Lara.Insp.inspBackend
#print axioms Lara.Insp.inspReplay_iff
#print axioms Lara.Insp.inspSound
#print axioms Lara.Insp.inspUses_covers
#print axioms Lara.Insp.inspUses_valid
#print axioms Lara.Insp.inspUses_account
#print axioms Lara.Insp.checkB_one_extract
#print axioms Lara.Insp.checkB_diff_extract
#print axioms Lara.Insp.relHoldsB_iff
#print axioms Lara.Insp.relHolds_absent_of_nil
#print axioms Lara.Insp.relHolds_present_of_unique
#print axioms Lara.Insp.relHolds_polarity_excl
#print axioms Lara.Insp.relHolds_unique_absent_excl
#print axioms Lara.Insp.inspModels_diff_halves
#print axioms Lara.Insp.inspModels_one_witness
#print axioms Lara.Insp.inspModels_excl_of_same_entry
#print axioms Lara.Insp.inspModels_absent_present_sat

-- Named certificate premise slots (lara-syntax@0.6): the presentation
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
#print axioms Lara.Support.hasSupport_obligations_indep
#print axioms Lara.Support.hasSupport_inst_root
#print axioms Lara.Support.hasSupport_leaf_gamma
#print axioms Lara.Support.hasSupport_mono_gamma
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
#print axioms Lara.Attack.hasAttack_mono_gamma
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
-- The derived `DecidableEq Attack` enters the kernel computation of every
-- `by decide` over an attack-mentioning statement, so it is pinned here too.
#print axioms Lara.Attack.instDecidableEqAttack

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
#print axioms Lara.Check.firstDuplicate_none_iff
#print axioms Lara.Check.CheckedArguments.cache_nodup
#print axioms Lara.Check.lookupChecked_term
#print axioms Lara.Check.lookupChecked_complete
#print axioms Lara.Check.checkProgram_sound
#print axioms Lara.Check.checkProgram_complete
#print axioms Lara.Check.checkProgram_accepted_source_declared
#print axioms Lara.Check.checkProgram_accepted_target_declared

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
#print axioms Lara.Examples.PEx_holes
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
#print axioms Lara.Examples.check_program_incomplete_is_hole
#print axioms Lara.Examples.check_program_incomplete_hole_report
#print axioms Lara.Examples.check_program_incomplete_no_complete_support
#print axioms Lara.Examples.check_program_hole_attack_closes_onto_complete
#print axioms Lara.Examples.check_program_hole_rebut_no_edge
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
#print axioms Lara.Check.conflictCache_conclusions
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
#print axioms Lara.Consistency.completeClaimFor_gap_of_only_holes
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

-- lara-core@0.3 located gaps (spec §4.4, §8; docs/located-gap-decision.md).
-- Accepted units may carry typed arguments with open mandatory obligations as
-- located holes. The checker partitions its retained cache once into complete
-- nodes and holes and proves agreement with the inference-based specification
-- views; attacks sourced at holes are typed then inert (D4); attacks on a
-- complete occurrence shared with a hole keep their closure edges (D6); a
-- claim with no complete support is `gap`; and status depends only on the
-- complete arguments and their complete-to-complete closure coverage.
#print axioms Lara.Unit.CheckedUnit.holes_terms
#print axioms Lara.Compile.lookupDis_some_getElem?
#print axioms Lara.Compile.hasSupport_subterm
#print axioms Lara.Compile.complete_contains_complete
#print axioms Lara.Compile.complete_not_contains_hole
#print axioms Lara.Compile.CheckedProgram.target_declared_of_holes_nil
#print axioms Lara.Compile.no_edge_of_not_arg
#print axioms Lara.Compile.closure_reaches_shared_occurrence
#print axioms Lara.Compile.hole_occurrence_reaches_no_arg
#print axioms Lara.Compile.checkedAF_eq_of_coverage
#print axioms Lara.Compile.status_independent_of_holes
#print axioms Lara.Compile.checkedAF_independent_of_holes
#print axioms Lara.Check.argComplete_iff
#print axioms Lara.Check.argHole_iff
#print axioms Lara.Check.argComplete_of_hasSupport
#print axioms Lara.Check.argHole_of_hasSupport
#print axioms Lara.Check.mem_completeArgs_iff
#print axioms Lara.Check.mem_holeArgs_iff
#print axioms Lara.Check.completeArgs_holeArgs_disjoint
#print axioms Lara.Check.mem_completeArgs_or_holeArgs
#print axioms Lara.Check.completeArgs_append
#print axioms Lara.Check.holeArgs_append
#print axioms Lara.Check.completeArgs_congr
#print axioms Lara.Check.completeArgs_subset
#print axioms Lara.Check.completeArgs_sublist
#print axioms Lara.Check.completeArgs_length_le
#print axioms Lara.Check.completeArgs_eq_self
#print axioms Lara.Check.holeArgs_eq_nil
#print axioms Lara.Support.hasSupport_congr_gamma_on
#print axioms Lara.Check.argComplete_congr_gamma_on
#print axioms Lara.Check.argHole_congr_gamma_on
#print axioms Lara.Check.mem_liveAttacks_iff
#print axioms Lara.Check.liveAttacks_eq_self
#print axioms Lara.Check.liveAttacks_congr
#print axioms Lara.Check.liveAttacks_append
#print axioms Lara.Check.liveAttacks_snoc_unused_source
#print axioms Lara.Check.covered_liveAttacks_iff
#print axioms Lara.Check.attackComplete_iff_complete_live
#print axioms Lara.Check.attackComplete_completeArgs_iff
#print axioms Lara.Check.coveredB_liveAttacks
#print axioms Lara.Check.mem_declPositions_iff
#print axioms Lara.Check.declPositions_map
#print axioms Lara.Check.declPositions_congr
#print axioms Lara.Check.declPositions_sorted
#print axioms Lara.Check.declPositions_cons
#print axioms Lara.Check.declPositions_length
#print axioms Lara.Check.eq_of_pairwise_lt_of_mem_iff
#print axioms Lara.Check.DeclPartition.mem_nodeDecls_iff
#print axioms Lara.Check.DeclPartition.mem_holeIndices_iff
#print axioms Lara.Check.DeclPartition.nodeDecls_eq
#print axioms Lara.Check.DeclPartition.holeIndices_eq
-- Located obligation sites (Lara.Check.HoleSites, located-gap decision D12)
#print axioms Lara.Check.mem_prefixSites
#print axioms Lara.Check.mem_ownSites
#print axioms Lara.Check.mem_openSitesList
#print axioms Lara.Check.mem_openSitesDis
#print axioms Lara.Check.mem_openSites_inst
#print axioms Lara.Check.mem_sitesFor
#print axioms Lara.Check.lookupDis_mem
#print axioms Lara.Check.lookupDis_of_nodup
#print axioms Lara.Check.openSites_sound
#print axioms Lara.Check.openSites_complete
#print axioms Lara.Check.mem_openSites_iff
#print axioms Lara.Check.mem_obligations_iff_sites
#print axioms Lara.Check.sitesFor_ne_nil
#print axioms Lara.Check.openSites_nodup
#print axioms Lara.Check.sitesFor_nodup
#print axioms Lara.Check.obligationSites_questions
#print axioms Lara.Check.obligationSites_adequate
#print axioms Lara.Check.holeObligationSites_adequate
#print axioms Lara.Driver.holeRows_obligations
#print axioms Lara.Check.CheckedArguments.holes_terms
#print axioms Lara.Check.CheckedArguments.partition
#print axioms Lara.Check.CheckedArguments.typed
#print axioms Lara.Check.checkProgram_complete_holes
#print axioms Lara.Check.checkProgramDetailed_complete_holes
#print axioms Lara.Check.Unit.termsWellSorted_filter
#print axioms Lara.Check.Unit.checkUnit_complete_holes
#print axioms Lara.Check.Unit.CheckUnitSound.raw_attack_complete
#print axioms Lara.Check.Unit.CheckUnitSound.args_eq_of_complete
#print axioms Lara.Check.Unit.CheckUnitSound.atts_eq_of_complete
#print axioms Lara.Check.Unit.CheckUnitSound.holes_eq_nil_of_complete
#print axioms Lara.Check.Unit.CheckUnitSound.holes_iff
#print axioms Lara.Check.Unit.CheckUnitSound.hole_reports_exact
#print axioms Lara.Check.Unit.CheckUnitSound.nodeDecls_eq
#print axioms Lara.Check.Unit.CheckUnitSound.holeIndices_eq
#print axioms Lara.Check.Unit.CheckUnitSound.hole_inert_source
#print axioms Lara.Check.Unit.gap_of_only_holes

-- Conservative reporting with located holes (spec §4.3; decision §5, D7):
-- the reference carrier `D` excludes typed holes and keeps unclassified
-- quarantined terms, the checked carrier `K` holds the retained complete
-- nodes, and the seed is `(D \ K)` plus retained complete nodes that lost an
-- incoming edge. `K ⊆ D` is obligation transport on supported retained terms;
-- nothing quarantined means nothing blocked, holes or not.
#print axioms Lara.BlockedProgram.mem_retainedIndices_iff
#print axioms Lara.BlockedProgram.checkedCarrier_eq
#print axioms Lara.BlockedProgram.referenceCarrier_eq
#print axioms Lara.BlockedProgram.retainedIndices_mono
#print axioms Lara.BlockedProgram.retainedIndices_congr
#print axioms Lara.BlockedProgram.retainedArguments_keepComplete
#print axioms Lara.BlockedProgram.keepComplete_terms
#print axioms Lara.BlockedProgram.coveredB_liveAttacks
#print axioms Lara.BlockedProgram.referenceLive_of_keepComplete
#print axioms Lara.BlockedProgram.complete_subset_reference
#print axioms Lara.BlockedProgram.blockedQueries_eq_nil_of_keep_all
#print axioms Lara.BlockedProgram.referenceLive_indices_of_keep_all
#print axioms Lara.BlockedProgram.blockedSeed_eq_nil_of_keep_all
#print axioms Lara.BlockedProgram.blockedSet_nil
#print axioms Lara.BlockedProgram.supportBlocked_nil
#print axioms Lara.BlockedProgram.production_justified_nonpromotion_of_keep_all
#print axioms Lara.BlockedProgram.checked_args_keepComplete
#print axioms Lara.BlockedProgram.checked_atts_live
#print axioms Lara.BlockedProgram.referenceLive_eq_notHole
#print axioms Lara.BlockedProgram.checked_complete_subset_notHole
#print axioms Lara.BlockedProgram.referenceLive_indices_eq_notHole
#print axioms Lara.BlockedProgram.notHole_indices_eq_complete_of_typed
#print axioms Lara.BlockedProgram.checked_production_justified_nonpromotion_notHole
#print axioms Lara.Groups.usesLeaf_eq_true_iff
#print axioms Lara.Groups.keepArg_leaves
#print axioms Lara.Admission.buildGamma_quarantineLeaves
#print axioms Lara.Admission.prune_gamma_agree
#print axioms Lara.Examples.EvidenceBlocked.tMixDone_complete
#print axioms Lara.Examples.EvidenceBlocked.tHolePair_hole
#print axioms Lara.Examples.EvidenceBlocked.tHoleL2_hole
#print axioms Lara.Examples.EvidenceBlocked.hole_alone_reference_eq_complete
#print axioms Lara.Examples.EvidenceBlocked.hole_alone_quarantine_not_blocked
#print axioms Lara.Examples.EvidenceBlocked.hole_alone_quarantine_blocked_under_all_declared
#print axioms Lara.Examples.EvidenceBlocked.dropped_attack_seed
#print axioms Lara.Examples.EvidenceBlocked.dropped_attack_onto_hole_blocks_support
#print axioms Lara.Examples.EvidenceBlocked.unclassified_not_hole
#print axioms Lara.Examples.EvidenceBlocked.unclassified_quarantine_blocks_support
#print axioms Lara.Examples.EvidenceBlocked.clean_unit_with_hole_not_blocked

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
#print axioms Lara.Erase.mapCertProg_holes
#print axioms Lara.Erase.mapCertProg_atts
#print axioms Lara.Erase.backend_replacement_transport

-- Duplicate-report groups (spec §4.3): the frozen consistency and
-- quarantine/escalation definitions and their metatheory.
#print axioms Lara.Groups.all_equiv_head_iff
#print axioms Lara.Groups.consistentB_iff
#print axioms Lara.Groups.mem_quarantined_iff
#print axioms Lara.Groups.quarantined_arg_excluded
#print axioms Lara.Groups.quarantined_leaf_absent
#print axioms Lara.Groups.conflictReject_iff

-- Conservative public reporting for quarantine-affected claims (spec §4.3):
-- the locality lemma and the non-promotion / preservation results
-- (preservation requires equal complete-support sets), plus the declared-index
-- seed obligations and the compact production-AF bridge.
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

/-! ### M0 — the frozen compilation carrier and invariant record -/

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

#print axioms Lara.Realizability.StructuredAFIso.refl
#print axioms Lara.Realizability.StructuredAFIso.symm
#print axioms Lara.Realizability.StructuredAFIso.trans

#print axioms Lara.Realizability.compilerInvariant_iso
#print axioms Lara.Realizability.realizable_invariant
#print axioms Lara.Realizability.HasSupport.conclusion_wellSorted
#print axioms Lara.Realizability.Realization.node_conclusion_wellSorted

/-! ### M1 — frozen-invariant non-sufficiency under a fixed policy -/

#print axioms Lara.Examples.Realizability.noAttack_of_emptyDefeat
#print axioms Lara.Examples.Realizability.compiled_no_edges_of_emptyDefeat
#print axioms Lara.Examples.Realizability.emptyUnitCheck_ok
#print axioms Lara.Examples.Realizability.nonempty_swapped_realizable
#print axioms Lara.Examples.Realizability.nonempty_swapped_node_wellSorted
#print axioms Lara.Examples.Realizability.oneSelfEdge_invariant
#print axioms Lara.Examples.Realizability.oneSelfEdge_not_realizable

/-! ### M2a — semantics-parametric observation

The generic `ExtensionSemantics` interface and its five instances. Each
instance bundles its own adequacy proof (`sound`), so printing axioms for the
instance covers that proof too — an instance cannot be added without one. -/

#print axioms Lara.Semantics.not_eq_true_iff
#print axioms Lara.Semantics.not_and_eq_true

#print axioms Lara.Semantics.mem_subseqs
#print axioms Lara.Semantics.sublist_ext
#print axioms Lara.Semantics.subseqs_ext
#print axioms Lara.Semantics.nodup_flatMap_pair
#print axioms Lara.Semantics.subseqs_nodup
#print axioms Lara.Semantics.exists_max_length
#print axioms Lara.Semantics.mem_candidates
#print axioms Lara.Semantics.candidates_ext
#print axioms Lara.Semantics.candidates_nodup

#print axioms Lara.Semantics.subB_iff
#print axioms Lara.Semantics.boundedB_iff
#print axioms Lara.Semantics.conflictFreeB_iff
#print axioms Lara.Semantics.admissibleB_iff
#print axioms Lara.Semantics.completeB_iff
#print axioms Lara.Semantics.stableB_iff

#print axioms Lara.Semantics.defendedB_mono
#print axioms Lara.Semantics.defendedB_congr
#print axioms Lara.Semantics.bounded_congr
#print axioms Lara.Semantics.conflictFree_congr
#print axioms Lara.Semantics.admissible_congr
#print axioms Lara.Semantics.complete_congr
#print axioms Lara.Semantics.stable_congr

#print axioms Lara.Semantics.mem_canonize
#print axioms Lara.Semantics.canonize_mem_candidates
#print axioms Lara.Semantics.exists_candidate_ext
#print axioms Lara.Semantics.enumerate_ext
#print axioms Lara.Semantics.mem_filter_candidates

#print axioms Lara.Semantics.iter_subset_complete
#print axioms Lara.Semantics.grounded_complete
#print axioms Lara.Semantics.grounded_least
#print axioms Lara.Semantics.grounded_leastComplete
#print axioms Lara.Semantics.leastCompleteB_iff

#print axioms Lara.Semantics.maximalB_iff
#print axioms Lara.Semantics.preferredB_iff
#print axioms Lara.Semantics.admissible_nil
#print axioms Lara.Semantics.preferred_exists_candidate
#print axioms Lara.Semantics.preferred_exists
#print axioms Lara.Semantics.preferredSem_enumerate_ne_nil
#print axioms Lara.Semantics.admissible_cons
#print axioms Lara.Semantics.preferred_complete

#print axioms Lara.Semantics.mem_attacked
#print axioms Lara.Semantics.mem_reach
#print axioms Lara.Semantics.reach_congr
#print axioms Lara.Semantics.semiStableB_iff

#print axioms Lara.Semantics.groundedSem
#print axioms Lara.Semantics.completeSem
#print axioms Lara.Semantics.preferredSem
#print axioms Lara.Semantics.stableSem
#print axioms Lara.Semantics.semiStableSem

/-! ### M2a — grounded is the singleton instance -/

#print axioms Lara.Semantics.leastComplete_unique
#print axioms Lara.Semantics.leastComplete_congr
#print axioms Lara.Semantics.mem_canonize_grounded
#print axioms Lara.Semantics.eq_singleton_of_nodup_of_unique
#print axioms Lara.Semantics.groundedSem_enumerate
#print axioms Lara.Semantics.groundedSem_singleton

/-! ### M2a — semantics-parametric claim observation

The per-argument acceptance profile, the claim-level observation, its collapse to
`Grounded.statusC` on the grounded instance, and the justified/defeated
exclusivity result with its five per-instance hypothesis discharges. -/

#print axioms Lara.Semantics.mem_attacked_iff
#print axioms Lara.Semantics.attackedByB_congr
#print axioms Lara.Semantics.attackedByB_congr_eq
#print axioms Lara.Semantics.profile_grounded

#print axioms Lara.Semantics.observe_gap
#print axioms Lara.Semantics.observe_gap_iff
#print axioms Lara.Semantics.observe_noExtension_iff
#print axioms Lara.Semantics.enumerate_ne_nil_of_observed_ne_gap
#print axioms Lara.Semantics.no_verdict_on_empty
#print axioms Lara.Semantics.claimDefeatedB_of_nil
#print axioms Lara.Semantics.claimAcceptedB_of_nil

#print axioms Lara.Semantics.labelC_inn_iff_mem
#print axioms Lara.Semantics.attackedByB_grounded_iff
#print axioms Lara.Semantics.labelC_undec_iff_unattacked
#print axioms Lara.Semantics.observe_grounded

#print axioms Lara.Semantics.justified_defeated_exclusive
#print axioms Lara.Semantics.observe_justified_not_all_defeated
#print axioms Lara.Semantics.specConflictFree_enumerateConflictFree
#print axioms Lara.Semantics.justified_defeated_exclusive_of_enumerate
#print axioms Lara.Semantics.observe_justified_not_all_defeated_of_enumerate
#print axioms Lara.Semantics.completeSem_specConflictFree
#print axioms Lara.Semantics.stableSem_specConflictFree
#print axioms Lara.Semantics.preferredSem_specConflictFree
#print axioms Lara.Semantics.semiStableSem_specConflictFree
#print axioms Lara.Semantics.groundedSem_specConflictFree
#print axioms Lara.Semantics.completeSem_enumerateConflictFree
#print axioms Lara.Semantics.stableSem_enumerateConflictFree
#print axioms Lara.Semantics.preferredSem_enumerateConflictFree
#print axioms Lara.Semantics.semiStableSem_enumerateConflictFree
#print axioms Lara.Semantics.groundedSem_enumerateConflictFree

/-! ### M2a — concrete witnesses (`Lara.Examples.Semantics`)

The six table frameworks cover stable nonexistence and the `noExtension` arm it
forces, credulous non-functionality, the failure of `observe` to factor through
`profile`, `gap`'s semantics-independence at all five instances, the
semi-stable / preferred / stable strictness chain, and reinstatement through a
defended argument in a multi-element extension. -/

#print axioms Lara.Examples.Semantics.stableSem_enumerate_threeCycle
#print axioms Lara.Examples.Semantics.observe_stableSem_threeCycle
#print axioms Lara.Examples.Semantics.observe_stableSem_threeCycle_ne_justified
#print axioms Lara.Examples.Semantics.observe_stableSem_threeCycle_ne_defeated
#print axioms Lara.Examples.Semantics.stableSem_enumerate_threeCycleAttacked
#print axioms Lara.Examples.Semantics.threeCycle_enumerate_nonStable
#print axioms Lara.Examples.Semantics.preferred_exists_where_stable_does_not

#print axioms Lara.Examples.Semantics.preferredSem_enumerate_twoCycle
#print axioms Lara.Examples.Semantics.groundedSem_enumerate_twoCycle
#print axioms Lara.Examples.Semantics.credulous_not_functional
#print axioms Lara.Examples.Semantics.profile_preferredSem_twoCycle_symm
#print axioms Lara.Examples.Semantics.profile_preferredSem_twoCycle
#print axioms Lara.Examples.Semantics.profile_groundedSem_twoCycle
#print axioms Lara.Examples.Semantics.observe_twoCycle_grounded_ne_preferred
#print axioms Lara.Examples.Semantics.observe_twoCycleSink_grounded_ne_preferred

#print axioms Lara.Examples.Semantics.completeSem_enumerate_twoCycle
#print axioms Lara.Examples.Semantics.observe_not_determined_by_profile

#print axioms Lara.Examples.Semantics.observe_claimNoSupport_uniform

#print axioms Lara.Examples.Semantics.semiStable_proper_refinement_of_preferred
#print axioms Lara.Examples.Semantics.semiStable_exists_where_stable_does_not

/-! ### M2a — the enumerations behind the ten pairwise separations, and the
last two evaluation-only claims of that module, promoted to theorems. -/

#print axioms Lara.Examples.Semantics.semiStableSem_enumerate_twoCycle
#print axioms Lara.Examples.Semantics.completeSem_enumerate_rangeSplit
#print axioms Lara.Examples.Semantics.five_semantics_pairwise_distinct
#print axioms Lara.Examples.Semantics.threeCycle_conflictFree
#print axioms Lara.Examples.Semantics.twoCycle_extensions

/-! ### M2a — `defeated` is unreachable on the bare two-cycle

The entailment `twoCycleSink`'s docstring used to draw in prose from an
upper-bound extension list, proved instead: one non-defeating extension closes
`observe`'s defeat guard, and every one of the five enumerations on `twoCycle`
contains such an extension for any claim with non-empty support. -/

#print axioms Lara.Examples.Semantics.observe_ne_defeated_of_mem_enumerate
#print axioms Lara.Examples.Semantics.claimDefeatedB_nil_eq_false
#print axioms Lara.Examples.Semantics.twoCycle_defeat_split
#print axioms Lara.Examples.Semantics.twoCycle_defeated_unreachable

/-! ### M2a — what `ExtensionSemantics.sound`'s `Nodup` hypothesis is for

Adequacy holds without it at all five instances; representative uniqueness
(`candidates_ext`, `enumerate_ext`) is false without it. -/

#print axioms Lara.Examples.Semantics.dupCarrier_candidates
#print axioms Lara.Examples.Semantics.not_candidates_ext_without_nodup
#print axioms Lara.Examples.Semantics.not_enumerate_ext_without_nodup
#print axioms Lara.Examples.Semantics.dupCarrier_enumerate
#print axioms Lara.Examples.Semantics.sound_holds_without_nodup

/-! ### M2a — `Observation.AgreesOnArgs` is strictly weaker than `Compile.Faithful`

The oracle `eJunk` agrees with `Compile.Edge` at every declared argument of
`Lara.Examples.PEx` and carries one junk edge at an undeclared index pair, so it
satisfies `AgreesOnArgs` and fails `Faithful.ranged`. -/

#print axioms Lara.Examples.Semantics.eJunk_agreesOnArgs
#print axioms Lara.Examples.Semantics.not_faithful_eJunk
#print axioms Lara.Examples.Semantics.agreesOnArgs_strictly_weaker_than_faithful

/-! ### M2a — the observation table's row axes are exhaustive

`semanticsLabel` / `semanticsInstance` and their two counterparts are total
matches, so a new constructor breaks them. The three order lists are hand-written
literals and are not checked that way; these theorems are that check, and without
them a new constructor would silently drop a table row. -/

#print axioms Lara.Semantics.Registry.allSemantics_complete
#print axioms Lara.Examples.Semantics.allSemantics_complete
#print axioms Lara.Examples.Semantics.allFrameworks_complete
#print axioms Lara.Examples.Semantics.allClaims_complete

/-! ### M2a — source-to-framework observation transport

Carrier-locality of the five specifications, the generic transport onto the
compiled framework with its per-semantics corollaries, and the claim-level
source observation. The three refutations (`not_attackExtensional_conflictFree`,
`not_observe_congr_of_unbounded_support`, `observe_congr_needs_support_bound`)
are audited alongside the positive results: they are what makes the two carrier
bounds checked rather than asserted. -/

#print axioms Lara.Observation.agree_symm
#print axioms Lara.Observation.attackExtensional_of_imp
#print axioms Lara.Observation.bounded_congr_af
#print axioms Lara.Observation.conflictFree_congr_af
#print axioms Lara.Observation.defendedB_congr_af
#print axioms Lara.Observation.mem_reach_congr_af

#print axioms Lara.Observation.attackExtensional_bounded
#print axioms Lara.Observation.attackExtensional_admissible
#print axioms Lara.Observation.attackExtensional_complete
#print axioms Lara.Observation.attackExtensional_stable
#print axioms Lara.Observation.attackExtensional_preferred
#print axioms Lara.Observation.attackExtensional_leastComplete
#print axioms Lara.Observation.attackExtensional_semiStable

#print axioms Lara.Observation.oneJunk_agree
#print axioms Lara.Observation.not_attackExtensional_conflictFree
#print axioms Lara.Observation.admissible_transports_on_junk

#print axioms Lara.Observation.all_congr_of_mem
#print axioms Lara.Observation.isEmpty_congr_of_mem
#print axioms Lara.Observation.bounded_of_mem_enumerate
#print axioms Lara.Observation.enumerate_mem_congr
#print axioms Lara.Observation.attackedByB_congr_af
#print axioms Lara.Observation.claimDefeatedB_congr_af
#print axioms Lara.Observation.observe_congr

#print axioms Lara.Observation.oneAttacksJunk_agree
#print axioms Lara.Observation.not_observe_congr_of_unbounded_support
#print axioms Lara.Observation.observe_congr_needs_support_bound

#print axioms Lara.Observation.agreesOnArgs_of_faithful
#print axioms Lara.Observation.agreesOnArgs_edgeB
#print axioms Lara.Observation.faithful_unique
#print axioms Lara.Observation.mem_toAF_args
#print axioms Lara.Observation.toAF_attack_agree
#print axioms Lara.Observation.spec_congr_of_agreesOnArgs
#print axioms Lara.Observation.spec_toAF_iff_checkedAF

#print axioms Lara.Observation.admissible_toAF_iff_checkedAF
#print axioms Lara.Observation.complete_toAF_iff_checkedAF
#print axioms Lara.Observation.stable_toAF_iff_checkedAF
#print axioms Lara.Observation.preferred_toAF_iff_checkedAF
#print axioms Lara.Observation.semiStable_toAF_iff_checkedAF
#print axioms Lara.Observation.leastComplete_toAF_iff_checkedAF

#print axioms Lara.Observation.srcObservation_iff_checked
#print axioms Lara.Observation.srcObservation_checked
#print axioms Lara.Observation.srcObservation_unique
#print axioms Lara.Observation.srcStatus_iff_srcObservation

/-! ## Theory M3 — source updates and status dynamics

The M3 audit covers the complete public source-update surface, every supporting
lemma promoted for the preservation and transition proofs, all reachable and
unreachable matrix witnesses, and the typed evidence used by the report
emitters.  Private proof helpers and private fixture builders are intentionally
outside the public audit surface. -/

/-! ### M3 — source, acceptance, and update vocabulary -/

#print axioms Lara.Update.SourceState
#print axioms Lara.Update.Accepted
#print axioms Lara.Update.AcceptedRun
#print axioms Lara.Update.AcceptedRun.accepted
#print axioms Lara.Update.UpdateRejection
#print axioms Lara.Update.SourceUpdate

#print axioms Lara.Update.AddLeafFresh
#print axioms Lara.Update.addLeafFreshB
#print axioms Lara.Update.addLeafFreshB_iff
#print axioms Lara.Update.AdmittedAt
#print axioms Lara.Update.admittedAtB
#print axioms Lara.Update.admittedAtB_iff
#print axioms Lara.Update.EndpointDeclared
#print axioms Lara.Update.endpointDeclaredB
#print axioms Lara.Update.endpointDeclaredB_iff
#print axioms Lara.Update.InstanceFresh
#print axioms Lara.Update.instanceFreshB
#print axioms Lara.Update.instanceFreshB_iff

#print axioms Lara.Update.applyUpdate
#print axioms Lara.Update.applyUpdate_addLeaf_notFresh
#print axioms Lara.Update.applyUpdate_tighten_notAdmitted
#print axioms Lara.Update.applyUpdate_addAttack_endpointNotDeclared
#print axioms Lara.Update.applyUpdate_addInstance_notFresh
#print axioms Lara.Update.applyUpdate_addLeaf_ok
#print axioms Lara.Update.applyUpdate_tighten_ok
#print axioms Lara.Update.applyUpdate_addAttack_ok
#print axioms Lara.Update.applyUpdate_addInstance_ok
#print axioms Lara.Update.applyUpdate_addInstance_hole_ok

/-! ### M3 — preservation support -/

#print axioms Lara.Admission.firstDuplicateLeafId_none_iff_nodup
#print axioms Lara.Admission.evaluateAdmission_accepted_conditions
#print axioms Lara.Admission.retained_semantic_attack_endpoints
#print axioms Lara.Admission.retained_identity_of_length_eq
#print axioms Lara.Admission.liftSupport_range_eq_of_mem
#print axioms Lara.Admission.checkedAF_eq_declaredAF

#print axioms Lara.RawAttack.mem_of_mem_selectAligned
#print axioms Lara.RawAttack.resolveAttacks_append
#print axioms Lara.RawAttack.resolveAttacks_attack_lookup
#print axioms Lara.RawAttack.resolveAttacks_mono_lookup
#print axioms Lara.RawAttack.lookupArg_append_of_some
#print axioms Lara.RawAttack.lookupArg_some_row
#print axioms Lara.RawAttack.selectAligned_append_of_length_eq
#print axioms Lara.RawAttack.resolveAttacks_length
#print axioms Lara.RawAttack.selectAligned_congr_on

#print axioms Lara.BlockedProgram.directIn_reflect_embedding
#print axioms Lara.BlockedProgram.directOut_reflect_embedding
#print axioms Lara.BlockedProgram.labelC_eq_of_embedding
#print axioms Lara.BlockedProgram.production_unblocked_label_agree

#print axioms Lara.Grounded.statusC_defeated_all_out
#print axioms Lara.Grounded.SinkExtension
#print axioms Lara.Grounded.SinkExtension.directIn_forward
#print axioms Lara.Grounded.SinkExtension.directOut_forward
#print axioms Lara.Grounded.SinkExtension.directIn_backward
#print axioms Lara.Grounded.SinkExtension.directOut_backward
#print axioms Lara.Grounded.SinkExtension.label_old
#print axioms Lara.Grounded.statusC_contested_has_undec
#print axioms Lara.Grounded.statusC_ne_defeated_of_undec
#print axioms Lara.Grounded.SinkExtension.justified_preserved
#print axioms Lara.Grounded.SinkExtension.contested_not_defeated
#print axioms Lara.Grounded.SinkEmbedding
#print axioms Lara.Grounded.SinkEmbedding.directIn_forward
#print axioms Lara.Grounded.SinkEmbedding.directOut_forward
#print axioms Lara.Grounded.SinkEmbedding.directIn_backward
#print axioms Lara.Grounded.SinkEmbedding.directOut_backward
#print axioms Lara.Grounded.SinkEmbedding.label_old
#print axioms Lara.Grounded.SinkEmbedding.justified_preserved
#print axioms Lara.Grounded.SinkEmbedding.contested_not_defeated
#print axioms Lara.Grounded.labelC_inn_of_unattacked

#print axioms Lara.Consistency.claimSupportFor
#print axioms Lara.Consistency.completeClaimFor
#print axioms Lara.Grounded.incompleteAlternative
#print axioms Lara.Semantics.observe_holes_independent

/-! ### M3 — core transition API and matrix boundaries -/

#print axioms Lara.Update.coreObs
#print axioms Lara.Update.beliefSet
#print axioms Lara.Update.CoreTransition

#print axioms Lara.Update.addAttack_gap_fixed
#print axioms Lara.Update.additive_no_gap_entry
#print axioms Lara.Update.addLeaf_core_fixed
#print axioms Lara.Update.nonInstance_gap_fixed
#print axioms Lara.Update.addInstance_sink_status_monotone

-- Obligations and holes across updates (docs/located-gap-decision.md §6).
#print axioms Lara.Update.typed_obligations_preserved
#print axioms Lara.Update.addLeaf_obligations_preserved
#print axioms Lara.Update.addAttack_obligations_preserved
#print axioms Lara.Update.tighten_obligations_preserved
#print axioms Lara.Update.addInstance_holes_persist
#print axioms Lara.Update.addInstance_hole_core_fixed

/-! ### Completion updates — in-place discharge (D13) and atomic batches (D14) -/

#print axioms Lara.Update.AtomicEdit
#print axioms Lara.Update.DischargeOpen
#print axioms Lara.Update.dischargeOpenB
#print axioms Lara.Update.dischargeOpenB_iff
#print axioms Lara.Update.dischargeRows
#print axioms Lara.Update.AtomicEdit.applyRaw
#print axioms Lara.Update.applyBatchFrom
#print axioms Lara.Update.applyBatch
#print axioms Lara.Update.applyUpdate_dischargeOpen_notDischargeable
#print axioms Lara.Update.applyUpdate_atomic_batchRejected
#print axioms Lara.Update.applyUpdate_dischargeOpen_ok_iff
#print axioms Lara.Update.applyUpdate_dischargeOpen_target
#print axioms Lara.Update.applyUpdate_atomic_ok_iff
#print axioms Lara.Update.applyUpdate_atomic_target
#print axioms Lara.Update.usesLeaf_true_iff

-- Term-level discharge (lean/Lara/Update/Discharge.lean).
#print axioms Lara.Update.Discharge.replaceDis
#print axioms Lara.Update.Discharge.closeOpen
#print axioms Lara.Update.Discharge.dischargeAt
#print axioms Lara.Update.Discharge.OpenAt
#print axioms Lara.Update.Discharge.openAtB
#print axioms Lara.Update.Discharge.openAtB_iff
#print axioms Lara.Update.Discharge.lookupDis_append_of_some
#print axioms Lara.Update.Discharge.lookupDis_append_of_none
#print axioms Lara.Update.Discharge.lookupDis_append_cases
#print axioms Lara.Update.Discharge.lookupDis_replaceDis
#print axioms Lara.Update.Discharge.replaceDis_map_fst
#print axioms Lara.Update.Discharge.replaceDis_eq_set
#print axioms Lara.Update.Discharge.lookupDis_none_of_not_mem
#print axioms Lara.Update.Discharge.lookupDis_of_getElem?_nodup
#print axioms Lara.Update.Discharge.OccKind
#print axioms Lara.Update.Discharge.occKind
#print axioms Lara.Update.Discharge.openSet
#print axioms Lara.Update.Discharge.dischargeAt_nil
#print axioms Lara.Update.Discharge.dischargeAt_isSome_iff
#print axioms Lara.Update.Discharge.subterm_dischargeAt_old
#print axioms Lara.Update.Discharge.subterm_dischargeAt_site
#print axioms Lara.Update.Discharge.subterm_dischargeAt_new
#print axioms Lara.Update.Discharge.subterm_dischargeAt_cases
#print axioms Lara.Update.Discharge.OpenMandatoryAt
#print axioms Lara.Update.Discharge.OpenMandatoryAway
#print axioms Lara.Update.Discharge.mem_collectObligations_iff
#print axioms Lara.Update.Discharge.mem_obligations_iff
#print axioms Lara.Update.Discharge.hasSupport_concl_of_occKind
#print axioms Lara.Update.Discharge.occKind_dischargeAt
#print axioms Lara.Update.Discharge.dischargeAt_conclusion
#print axioms Lara.Update.Discharge.lookupDis_site_none
#print axioms Lara.Update.Discharge.mem_site_of_dischargeAt
#print axioms Lara.Update.Discharge.dischargeAt_obligations_iff
#print axioms Lara.Update.Discharge.dischargeAt_obligations_subset
#print axioms Lara.Update.Discharge.dischargeAt_obligations_retained
#print axioms Lara.Update.Discharge.dischargeAt_closes
#print axioms Lara.Update.Discharge.dischargeAt_complete
#print axioms Lara.Update.Discharge.dischargeAt_hasSupport
#print axioms Lara.Update.Discharge.mem_leavesList_iff
#print axioms Lara.Update.Discharge.mem_leavesDis_iff
#print axioms Lara.Update.Discharge.leaves_dischargeAt
#print axioms Lara.Update.Discharge.dischargeAt_ne

-- Batch and pipeline-level discharge metatheory (lean/Lara/Update/Completion.lean).
#print axioms Lara.Update.applyOrKeep
#print axioms Lara.Update.applyOrKeep_of_error
#print axioms Lara.Update.applyOrKeep_of_ok
#print axioms Lara.Update.atomic_rejected_iff
#print axioms Lara.Update.atomic_partial_rejected
#print axioms Lara.Update.applyBatchFrom_append
#print axioms Lara.Update.leafEdits
#print axioms Lara.Update.instanceEdits
#print axioms Lara.Update.attackEdits
#print axioms Lara.Update.withLeaves
#print axioms Lara.Update.applyBatchFrom_leafEdits
#print axioms Lara.Update.applyBatchFrom_instanceEdits
#print axioms Lara.Update.applyBatchFrom_attackEdits
#print axioms Lara.Update.completionEdits
#print axioms Lara.Update.completionState
#print axioms Lara.Update.atomic_completion_complete
#print axioms Lara.Update.dischargeRows_map_fst
#print axioms Lara.Update.dischargeCompletionEdits
#print axioms Lara.Update.dischargeCompletionState
#print axioms Lara.Update.atomic_discharge_completion_complete
#print axioms Lara.Update.AtomicEdit.Additive
#print axioms Lara.Update.AtomicEdit.applyRaw_prefix
#print axioms Lara.Update.applyBatchFrom_prefix
#print axioms Lara.Update.applyUpdate_atomic_raw_prefix
#print axioms Lara.Update.AtomicEdit.AdmittedAdditive
#print axioms Lara.Update.atomic_additive_kept
#print axioms Lara.Update.atomic_additive_checked_split
#print axioms Lara.Update.atomic_additive_checked_prefix
#print axioms Lara.Update.AcceptedRun.pruned_not_reported
#print axioms Lara.Update.atomic_additive_clean_target
#print axioms Lara.Update.dischargeTerm
#print axioms Lara.Update.lookupArg_dischargeRows
#print axioms Lara.Update.retarget
#print axioms Lara.Update.resolveAttacks_dischargeRows
#print axioms Lara.Update.dischargeOpen_raw_identities
#print axioms Lara.Update.dischargeOpen_resolved
#print axioms Lara.Update.dischargeOpen_runs
#print axioms Lara.Update.dischargeOpen_others_persist
#print axioms Lara.Update.dischargeOpen_row_kept
#print axioms Lara.Update.claimSupportFor_ne_nil_of_arg
#print axioms Lara.Update.dischargeOpen_hole_becomes_node

-- Status transitions of the completion updates (lean/Lara/Update/Transitions.lean).
#print axioms Lara.Update.insertShift
#print axioms Lara.Update.claimSupportFor_insertShift
#print axioms Lara.Update.sinkEmbedding_insertShift
#print axioms Lara.Update.coreObs_not_gap_of_insert
#print axioms Lara.Update.coreObs_gap_of_insert
#print axioms Lara.Update.grounded_sink_monotone_of_insert
#print axioms Lara.Update.Unattacked
#print axioms Lara.Update.statusC_justified_of_unattacked
#print axioms Lara.Update.coreObs_justified_of_unattacked
#print axioms Lara.Update.publicReport_justified_of_unattacked
#print axioms Lara.Update.dischargeOpen_completion_no_gap_entry
#print axioms Lara.Update.dischargeOpen_completion_gap_fixed
#print axioms Lara.Update.dischargeOpen_completion_sink_status_monotone
#print axioms Lara.Update.dischargeOpen_completion_justified
#print axioms Lara.Update.dischargeOpen_completion_public_justified
#print axioms Lara.Update.AtomicEdit.AddsNoInstance
#print axioms Lara.Update.AtomicEdit.AddsNoAttack
#print axioms Lara.Update.atomic_additive_no_gap_entry
#print axioms Lara.Update.atomic_instanceFree_gap_fixed
#print axioms Lara.Update.atomic_attackFree_sink_status_monotone
#print axioms Lara.Update.AcceptedRun.justified_of_unattacked_row
#print axioms Lara.Update.atomic_completion_justified

-- Completion fixtures (lean/Lara/Examples/UpdateCompletion.lean).
#print axioms Lara.Examples.UpdateCompletion.stateWith
#print axioms Lara.Examples.UpdateCompletion.coverAttack
#print axioms Lara.Examples.UpdateCompletion.baseState
#print axioms Lara.Examples.UpdateCompletion.completedState
#print axioms Lara.Examples.UpdateCompletion.sequential_completion_fails
#print axioms Lara.Examples.UpdateCompletion.completion_theorem_applies
#print axioms Lara.Examples.UpdateCompletion.partial_batch_rejected
#print axioms Lara.Examples.UpdateCompletion.batch_edits_checked_in_order
#print axioms Lara.Examples.UpdateCompletion.holeState
#print axioms Lara.Examples.UpdateCompletion.holeCompletedState
#print axioms Lara.Examples.UpdateCompletion.atomic_keeps_old_hole
#print axioms Lara.Examples.UpdateCompletion.gapState
#print axioms Lara.Examples.UpdateCompletion.tMixDischarged
#print axioms Lara.Examples.UpdateCompletion.gapDischargedState
#print axioms Lara.Examples.UpdateCompletion.discharge_hole_becomes_node
#print axioms Lara.Examples.UpdateCompletion.useState
#print axioms Lara.Examples.UpdateCompletion.useCover
#print axioms Lara.Examples.UpdateCompletion.tUseDischarged
#print axioms Lara.Examples.UpdateCompletion.useDischargedState
#print axioms Lara.Examples.UpdateCompletion.discharge_needs_attack
#print axioms Lara.Examples.UpdateCompletion.discharge_completion_public_justified
#print axioms Lara.Examples.UpdateCompletion.gapBatchState
#print axioms Lara.Examples.UpdateCompletion.atomic_completion_public_justified
#print axioms Lara.Examples.UpdateCompletion.tMixBoth
#print axioms Lara.Examples.UpdateCompletion.optionalDischargedState
#print axioms Lara.Examples.UpdateCompletion.discharge_optional_enters_gap
#print axioms Lara.Examples.UpdateCompletion.useAttackedState
#print axioms Lara.Examples.UpdateCompletion.discharge_outgoing_defeats
#print axioms Lara.Examples.UpdateCompletion.quarantineRow
#print axioms Lara.Examples.UpdateCompletion.quarantineHoleState
#print axioms Lara.Examples.UpdateCompletion.quarantinedMeta
#print axioms Lara.Examples.UpdateCompletion.quarantineBatch
#print axioms Lara.Examples.UpdateCompletion.quarantineBatchState
#print axioms Lara.Examples.UpdateCompletion.atomic_quarantined_leaf_pruned
#print axioms Lara.Examples.UpdateCompletion.completionWitnessReport

/-! ### M3 — public transition API and matrix boundaries -/

#print axioms Lara.Update.PublicReport
#print axioms Lara.Update.PublicReport.ofStatus
#print axioms Lara.Update.PublicReport.ofStatus_injective
#print axioms Lara.Update.PublicReport.render
#print axioms Lara.Update.PublicReport.publicationLabel

#print axioms Lara.Update.checkedCarrierForRun
#print axioms Lara.Update.referenceCarrierForRun
#print axioms Lara.Update.declaredCarrier
#print axioms Lara.Update.blockedQueriesForRun
#print axioms Lara.Update.blockedSeedForRun
#print axioms Lara.Update.blockedSetForRun
#print axioms Lara.Update.publicReport
#print axioms Lara.Update.publicReport_gap_of_empty_support
#print axioms Lara.Update.PublicTransition

#print axioms Lara.Update.CleanBase
#print axioms Lara.Update.AcceptedRun.prune_eq
#print axioms Lara.Update.blockedQueriesForRun_eq_nil_of_clean
#print axioms Lara.Update.publicReport_eq_core_of_clean
#print axioms Lara.Update.keptArgs_eq_raw_of_clean
#print axioms Lara.Update.retainedIndices_eq_range_of_clean
#print axioms Lara.Update.keptAttacks_eq_resolved_of_clean
#print axioms Lara.Update.checkedArgs_eq_raw_of_clean
#print axioms Lara.Update.checkedAF_embedding_of_clean
#print axioms Lara.Update.blockedSeedForRun_eq_nil_of_clean
#print axioms Lara.Update.blockedSetForRun_eq_nil_of_clean

#print axioms Lara.Update.blockedSet_eq_nil_of_seed_nil
#print axioms Lara.Update.blockedQueriesForRun_eq_nil_of_empty_closure
#print axioms Lara.Update.publicReport_eq_core_of_empty_closure
#print axioms Lara.Update.checkedAF_embedding_of_no_arg_prune

#print axioms Lara.Update.AdditiveUpdate
#print axioms Lara.Update.additive_clean_target
#print axioms Lara.Update.additive_target_blockedSeed_eq_nil
#print axioms Lara.Update.additive_target_blockedSet_eq_nil
#print axioms Lara.Update.additive_public_eq_core
#print axioms Lara.Update.additive_public_ne_evidenceBlocked

#print axioms Lara.Update.NonInstanceUpdate
#print axioms Lara.Update.tighten_lifted_support_subset
#print axioms Lara.Update.tighten_public_defeated_not_contested
#print axioms Lara.Update.tighten_public_justified_source_justified
#print axioms Lara.Update.tighten_public_gap_fixed
#print axioms Lara.Update.tighten_public_row_justified_nonpromotion
#print axioms Lara.Update.quarantine_nonpromotion_corollary

/-! ### M3 — exported examples and reachable witnesses -/

#print axioms Lara.Examples.Update.AcceptedRun
#print axioms Lara.Examples.Update.resolvedOrEmpty
#print axioms Lara.Examples.Update.declaredOf
#print axioms Lara.Examples.Update.admissionOf
#print axioms Lara.Examples.Update.checkedResultOf
#print axioms Lara.Examples.Update.checkedOf
#print axioms Lara.Examples.Update.fixtureOf
#print axioms Lara.Examples.Update.SuccessfulCoreCell
#print axioms Lara.Examples.Update.SuccessfulPublicCell
#print axioms Lara.Examples.Update.SuccessfulCoreCell.transition

#print axioms Lara.Examples.Update.addInstance_uncovered_rejected
#print axioms Lara.Examples.Update.addInstance_hole_inert
#print axioms Lara.Examples.Update.addInstance_complete_alternative
#print axioms Lara.Examples.Update.addAttack_blocked_growth

-- The 37 reachable grounded core cells.
#print axioms Lara.Examples.Update.addLeaf_justified_to_justified
#print axioms Lara.Examples.Update.addLeaf_refuted_to_refuted
#print axioms Lara.Examples.Update.addLeaf_both_to_both
#print axioms Lara.Examples.Update.addLeaf_gap_to_gap

#print axioms Lara.Examples.Update.tighten_justified_to_justified
#print axioms Lara.Examples.Update.tighten_justified_to_refuted
#print axioms Lara.Examples.Update.tighten_justified_to_both
#print axioms Lara.Examples.Update.tighten_justified_to_gap
#print axioms Lara.Examples.Update.tighten_refuted_to_justified
#print axioms Lara.Examples.Update.tighten_refuted_to_refuted
#print axioms Lara.Examples.Update.tighten_refuted_to_both
#print axioms Lara.Examples.Update.tighten_refuted_to_gap
#print axioms Lara.Examples.Update.tighten_both_to_justified
#print axioms Lara.Examples.Update.tighten_both_to_refuted
#print axioms Lara.Examples.Update.tighten_both_to_both
#print axioms Lara.Examples.Update.tighten_both_to_gap
#print axioms Lara.Examples.Update.tighten_gap_to_gap

#print axioms Lara.Examples.Update.addAttack_justified_to_justified
#print axioms Lara.Examples.Update.addAttack_justified_to_refuted
#print axioms Lara.Examples.Update.addAttack_justified_to_both
#print axioms Lara.Examples.Update.addAttack_refuted_to_justified
#print axioms Lara.Examples.Update.addAttack_refuted_to_refuted
#print axioms Lara.Examples.Update.addAttack_refuted_to_both
#print axioms Lara.Examples.Update.addAttack_both_to_justified
#print axioms Lara.Examples.Update.addAttack_both_to_refuted
#print axioms Lara.Examples.Update.addAttack_both_to_both
#print axioms Lara.Examples.Update.addAttack_gap_to_gap

#print axioms Lara.Examples.Update.addInstance_justified_to_justified
#print axioms Lara.Examples.Update.addInstance_refuted_to_justified
#print axioms Lara.Examples.Update.addInstance_refuted_to_refuted
#print axioms Lara.Examples.Update.addInstance_refuted_to_both
#print axioms Lara.Examples.Update.addInstance_both_to_justified
#print axioms Lara.Examples.Update.addInstance_both_to_both
#print axioms Lara.Examples.Update.addInstance_gap_to_justified
#print axioms Lara.Examples.Update.addInstance_gap_to_refuted
#print axioms Lara.Examples.Update.addInstance_gap_to_both
#print axioms Lara.Examples.Update.addInstance_gap_to_gap

-- The 13 reachable five-valued public tightening cells.
#print axioms Lara.Examples.Update.tighten_public_justified_to_justified
#print axioms Lara.Examples.Update.tighten_public_justified_to_defeated
#print axioms Lara.Examples.Update.tighten_public_justified_to_contested
#print axioms Lara.Examples.Update.tighten_public_justified_to_gap
#print axioms Lara.Examples.Update.tighten_public_justified_to_evidenceBlocked
#print axioms Lara.Examples.Update.tighten_public_defeated_to_defeated
#print axioms Lara.Examples.Update.tighten_public_defeated_to_gap
#print axioms Lara.Examples.Update.tighten_public_defeated_to_evidenceBlocked
#print axioms Lara.Examples.Update.tighten_public_contested_to_defeated
#print axioms Lara.Examples.Update.tighten_public_contested_to_contested
#print axioms Lara.Examples.Update.tighten_public_contested_to_gap
#print axioms Lara.Examples.Update.tighten_public_contested_to_evidenceBlocked
#print axioms Lara.Examples.Update.tighten_public_gap_to_gap

#print axioms Lara.Examples.Update.agm_success_fails
#print axioms Lara.Examples.Update.agm_inclusion_fails

/-! ### M3 — typed matrix evidence and report emitters -/

#print axioms Lara.Examples.Update.UpdateKind
#print axioms Lara.Examples.Update.PublicationStatus
#print axioms Lara.Examples.Update.PublicationStatus.grounded
#print axioms Lara.Examples.Update.publicationStatuses
#print axioms Lara.Examples.Update.MatrixCoordinate
#print axioms Lara.Examples.Update.canonicalCoordinates
#print axioms Lara.Examples.Update.canonicalCoordinates_nodup
#print axioms Lara.Examples.Update.canonicalCoordinates_length
#print axioms Lara.Examples.Update.UpdateOfKind

#print axioms Lara.Examples.Update.ReachableClaim
#print axioms Lara.Examples.Update.ReachableTag
#print axioms Lara.Examples.Update.ReachableTag.sound
#print axioms Lara.Examples.Update.UnreachableTag
#print axioms Lara.Examples.Update.MatrixRun
#print axioms Lara.Examples.Update.InstanceSinkPremises
#print axioms Lara.Examples.Update.UnreachablePremises
#print axioms Lara.Examples.Update.UnreachableClaim
#print axioms Lara.Examples.Update.UnreachableTag.sound

#print axioms Lara.Examples.Update.CellEvidence
#print axioms Lara.Examples.Update.CellEvidence.Claim
#print axioms Lara.Examples.Update.CellEvidence.sound
#print axioms Lara.Examples.Update.evidenceFor
#print axioms Lara.Examples.Update.MatrixCellEntry

#print axioms Lara.Examples.Update.addLeafMatrix
#print axioms Lara.Examples.Update.tightenMatrix
#print axioms Lara.Examples.Update.addAttackMatrix
#print axioms Lara.Examples.Update.addInstanceMatrix
#print axioms Lara.Examples.Update.addLeaf_coordinates
#print axioms Lara.Examples.Update.tighten_coordinates
#print axioms Lara.Examples.Update.addAttack_coordinates
#print axioms Lara.Examples.Update.addInstance_coordinates
#print axioms Lara.Examples.Update.addLeaf_reachable_count
#print axioms Lara.Examples.Update.tighten_reachable_count
#print axioms Lara.Examples.Update.addAttack_reachable_count
#print axioms Lara.Examples.Update.addInstance_reachable_count
#print axioms Lara.Examples.Update.grounded_matrix_cell_count
#print axioms Lara.Examples.Update.grounded_reachable_count
#print axioms Lara.Examples.Update.groundedCoreMatrixReport

#print axioms Lara.Examples.Update.publicReports
#print axioms Lara.Examples.Update.PublicMatrixCoordinate
#print axioms Lara.Examples.Update.canonicalPublicCoordinates
#print axioms Lara.Examples.Update.canonicalPublicCoordinates_nodup
#print axioms Lara.Examples.Update.canonicalPublicCoordinates_length
#print axioms Lara.Examples.Update.canonicalPublicCoordinates_order

#print axioms Lara.Examples.Update.TightenPublicRun
#print axioms Lara.Examples.Update.TightenPublicReachableTag
#print axioms Lara.Examples.Update.TightenPublicReachableClaim
#print axioms Lara.Examples.Update.TightenPublicReachableTag.sound
#print axioms Lara.Examples.Update.TightenPublicUnreachableTag
#print axioms Lara.Examples.Update.TightenPublicUnreachableClaim
#print axioms Lara.Examples.Update.TightenPublicUnreachableTag.sound
#print axioms Lara.Examples.Update.TightenPublicCellEvidence
#print axioms Lara.Examples.Update.TightenPublicCellEvidence.Claim
#print axioms Lara.Examples.Update.TightenPublicCellEvidence.sound
#print axioms Lara.Examples.Update.tightenPublicEvidenceFor
#print axioms Lara.Examples.Update.TightenPublicCellEntry
#print axioms Lara.Examples.Update.tightenPublicMatrix
#print axioms Lara.Examples.Update.tightenPublicMatrix_coordinates
#print axioms Lara.Examples.Update.tighten_public_reachable_count
#print axioms Lara.Examples.Update.tighten_public_blocked_reachable_count

#print axioms Lara.Examples.Update.AdditiveKind
#print axioms Lara.Examples.Update.AdditiveKind.updateKind
#print axioms Lara.Examples.Update.AdditiveKind.label
#print axioms Lara.Examples.Update.AdditivePublicRun
#print axioms Lara.Examples.Update.AdditivePublicRun.toCore
#print axioms Lara.Examples.Update.AdditivePublicRun.publicTransition
#print axioms Lara.Examples.Update.AdditivePublicReachableClaim
#print axioms Lara.Examples.Update.ReachableTag.additivePublicSound
#print axioms Lara.Examples.Update.AdditiveBlockedRun
#print axioms Lara.Examples.Update.AdditiveBlockedRun.emptyClosure
#print axioms Lara.Examples.Update.AdditiveBlockedRun.false
#print axioms Lara.Examples.Update.AdditivePublicCellEvidence
#print axioms Lara.Examples.Update.AdditivePublicCellEvidence.Claim
#print axioms Lara.Examples.Update.AdditivePublicCellEvidence.sound
#print axioms Lara.Examples.Update.additivePublicEvidenceFor
#print axioms Lara.Examples.Update.AdditivePublicCellEntry

#print axioms Lara.Examples.Update.addLeafPublicMatrix
#print axioms Lara.Examples.Update.addAttackPublicMatrix
#print axioms Lara.Examples.Update.addInstancePublicMatrix
#print axioms Lara.Examples.Update.addLeafPublicMatrix_coordinates
#print axioms Lara.Examples.Update.addAttackPublicMatrix_coordinates
#print axioms Lara.Examples.Update.addInstancePublicMatrix_coordinates
#print axioms Lara.Examples.Update.addLeafPublicMatrix_length
#print axioms Lara.Examples.Update.addAttackPublicMatrix_length
#print axioms Lara.Examples.Update.addInstancePublicMatrix_length
#print axioms Lara.Examples.Update.addLeaf_public_reachable_count
#print axioms Lara.Examples.Update.addAttack_public_reachable_count
#print axioms Lara.Examples.Update.addInstance_public_reachable_count
#print axioms Lara.Examples.Update.addLeaf_public_blocked_reachable_count
#print axioms Lara.Examples.Update.addAttack_public_blocked_reachable_count
#print axioms Lara.Examples.Update.addInstance_public_blocked_reachable_count
#print axioms Lara.Examples.Update.fiveValuedPublicMatrixReport

-- Milestone B0: heterogeneous backend compositionality
-- (`Lara.BackendComposition`).  The occurrence vocabulary and the syntactic
-- identity scan, the two halves of the backend firewall, and the accounting
-- laws restated per occurrence — including the B0 headline
-- (`hetero_occurrences_accounted`) and its `usedBackends` corollary.
#print axioms Lara.BackendComposition.CertOccurrence.node
#print axioms Lara.BackendComposition.OccursIn
#print axioms Lara.BackendComposition.usedBackends
#print axioms Lara.BackendComposition.usedBackendsList
#print axioms Lara.BackendComposition.usedBackendsDis
#print axioms Lara.BackendComposition.OccurrenceConsequence
#print axioms Lara.BackendComposition.usedBackends_mem_list
#print axioms Lara.BackendComposition.usedBackends_mem_dis
#print axioms Lara.BackendComposition.certStep_usedBackends_subset
#print axioms Lara.BackendComposition.usedBackends_node
#print axioms Lara.BackendComposition.mem_usedBackends_occ
#print axioms Lara.BackendComposition.mem_usedBackendsListOcc
#print axioms Lara.BackendComposition.mem_usedBackendsDisOcc
#print axioms Lara.BackendComposition.mem_usedBackends_iff
#print axioms Lara.BackendComposition.map_fst_set_of_getElem?
#print axioms Lara.BackendComposition.prem_subterm_swap
#print axioms Lara.BackendComposition.dis_subterm_swap
#print axioms Lara.BackendComposition.stepDeps_cert_shape
#print axioms Lara.BackendComposition.certDeps_eq_union
#print axioms Lara.BackendComposition.hetero_occurrences_accounted
#print axioms Lara.BackendComposition.usedBackends_accounted

-- The worked mixed-backend witness (`Lara.Examples.BackendComposition`).
-- The fixture child core and every one of its `Strict.Backend` obligations,
-- proved rather than assumed; the registry extension and its transport
-- lemma; the two shipped-identity facts (`mixed_usedBackends`,
-- `mixed_registrations_distinct`); and the two firewall instantiations
-- (`mixed_swap`, `mixed_dis_swap`) with the typing derivations they rest on.
#print axioms Lara.Examples.BackendComposition.fixReplay_iff
#print axioms Lara.Examples.BackendComposition.fixSound
#print axioms Lara.Examples.BackendComposition.fixUses_covers
#print axioms Lara.Examples.BackendComposition.fixUses_valid
#print axioms Lara.Examples.BackendComposition.fixUses_account
#print axioms Lara.Examples.BackendComposition.fixCore
#print axioms Lara.Examples.BackendComposition.registryMix_nd
#print axioms Lara.Examples.BackendComposition.registryMix_ord
#print axioms Lara.Examples.BackendComposition.registryMix_fix
#print axioms Lara.Examples.BackendComposition.certOkOf_registry_congr
#print axioms Lara.Examples.BackendComposition.nd_accepts_mix
#print axioms Lara.Examples.BackendComposition.fix_certOkB_pA
#print axioms Lara.Examples.BackendComposition.fix_accepts_pA
#print axioms Lara.Examples.BackendComposition.fix_certOkB_pB
#print axioms Lara.Examples.BackendComposition.fix_accepts_pB
#print axioms Lara.Examples.BackendComposition.mixed_usedBackends
#print axioms Lara.Examples.BackendComposition.ndRegistered_theory_length
#print axioms Lara.Examples.BackendComposition.ordRegistered_theory_length
#print axioms Lara.Examples.BackendComposition.mixed_registrations_distinct
#print axioms Lara.Examples.BackendComposition.sideNdParent
#print axioms Lara.Examples.BackendComposition.ndParent_prems
#print axioms Lara.Examples.BackendComposition.ndParent_typed
#print axioms Lara.Examples.BackendComposition.sideFixA
#print axioms Lara.Examples.BackendComposition.fixChildA_typed
#print axioms Lara.Examples.BackendComposition.mixed_swap
#print axioms Lara.Examples.BackendComposition.mixed_swap_usedBackends
#print axioms Lara.Examples.BackendComposition.mixed_swap_accounted
#print axioms Lara.Examples.BackendComposition.sideFixB
#print axioms Lara.Examples.BackendComposition.fixChildB_typed
#print axioms Lara.Examples.BackendComposition.sideDisMix
#print axioms Lara.Examples.BackendComposition.disParent_dis
#print axioms Lara.Examples.BackendComposition.disParent_typed
#print axioms Lara.Examples.BackendComposition.mixed_dis_swap
#print axioms Lara.Examples.BackendComposition.mixed_dis_swap_usedBackends

-- The cross-language `certDeps` golden over the SHIPPED nd@1/ord@1 pair
-- (`scripts/check-backend-deps-golden.sh`). No fixture core appears here: a
-- dependency report never calls acceptance, so the `ord@1` kernel-opacity that
-- forces the typed witnesses above onto `fixCore` does not reach these.
#print axioms Lara.Examples.BackendComposition.depsParseCanonNat0
#print axioms Lara.Examples.BackendComposition.depsParseCanonNat1
#print axioms Lara.Examples.BackendComposition.depsOrdUses
#print axioms Lara.Examples.BackendComposition.depsNdUses
#print axioms Lara.Examples.BackendComposition.depsMixedTerm_stepDeps
#print axioms Lara.Examples.BackendComposition.depsOrdNode_stepDeps
#print axioms Lara.Examples.BackendComposition.depsMixedTerm_both_halves_nonempty
#print axioms Lara.Examples.BackendComposition.depsMixedTerm_certDeps
#print axioms Lara.Examples.BackendComposition.depsMixedTerm_usedBackends

-- The second golden vector (`depsDupTerm`): escapes, nested `con`, and the
-- repeated-slot certificate that pins the List-vs-Set multiplicity
-- reconciliation. Same shipped cores, same no-fixture discipline.
#print axioms Lara.Examples.BackendComposition.depsDupOrdUses
#print axioms Lara.Examples.BackendComposition.depsDupNdUses
#print axioms Lara.Examples.BackendComposition.depsDupTerm_stepDeps
#print axioms Lara.Examples.BackendComposition.depsDupOrdNode_stepDeps
#print axioms Lara.Examples.BackendComposition.depsDupTerm_certDeps
#print axioms Lara.Examples.BackendComposition.depsDupTerm_usedBackends

/-! ### M5 — verified surface calculus and full-AST elaboration -/

-- Supported-fragment Boolean/Prop correspondence, including the named
-- projections consumed by reflection.
#print axioms Lara.Surface.declarationIdsNodupB_iff
#print axioms Lara.Surface.ruleNamespacesWellFormedB_iff
#print axioms Lara.Surface.valueBindingsWellFormedB_iff
#print axioms Lara.Surface.comparisonsWellFormedB_iff
#print axioms Lara.Surface.inferredArgsWellFormedB_iff
#print axioms Lara.Surface.namedCertificatesWellFormedB_iff
#print axioms Lara.Surface.surfaceAttacksWellFormedB_iff
#print axioms Lara.Surface.canonicalPremiseLabelsB_iff
#print axioms Lara.Surface.statusesWellFormedB_iff
#print axioms Lara.Surface.groupsWellFormedB_iff
#print axioms Lara.Surface.supportedB_iff

-- Genuine binders: capture-avoiding parameter substitution, rule alpha,
-- named-ND alpha, and invariance of de Bruijn/kernel lowering.
#print axioms Lara.Surface.Binding.substParam_fresh_identity
#print axioms Lara.Surface.Binding.substParam_preserves_wellSorted
#print axioms Lara.Surface.Binding.substParam_compose_of_fresh
#print axioms Lara.Surface.Binding.ruleAlpha_refl
#print axioms Lara.Surface.Binding.ruleAlpha_symm
#print axioms Lara.Surface.Binding.ruleAlpha_trans
#print axioms Lara.NDNamed.alpha_refl
#print axioms Lara.NDNamed.alpha_symm
#print axioms Lara.NDNamed.alpha_trans
#print axioms Lara.NDNamed.toDB_eq_of_alpha
#print axioms Lara.NDNamed.lowerNamed_eq_of_alpha
#print axioms Lara.Surface.lowerCertificate_alpha_invariant
#print axioms Lara.Surface.alpha_elaboration_invariant

-- Independent value/interpolation and comparison expansion relations.
#print axioms Lara.Surface.expandNl_sound
#print axioms Lara.Surface.expandNl_complete
#print axioms Lara.Surface.expandValues_sound
#print axioms Lara.Surface.expandValues_complete
#print axioms Lara.Surface.expandComparisons_sound
#print axioms Lara.Surface.expandComparisons_complete

-- The syntax-directed assembly/derivation is independent of the elaborator:
-- `Checks` reconstructs the source rather than assuming `elaborate` success.
-- `Checks.core` carries declarative signature/policy/support/certificate/attack
-- obligations; concrete `checkUnit` success is derived through completeness.
#print axioms Lara.Surface.checkAuthoredConclusion_sound
#print axioms Lara.Surface.checkAuthoredConclusion_complete
#print axioms Lara.Surface.attackEndpointsDeclaredB_iff
#print axioms Lara.Surface.validateAttackEndpoints_sound
#print axioms Lara.Surface.validateAttackEndpoints_complete
#print axioms Lara.Surface.validateGroups_sound
#print axioms Lara.Surface.validateGroups_complete
#print axioms Lara.Surface.resolveStatuses_sound
#print axioms Lara.Surface.resolveStatuses_complete
#print axioms Lara.Surface.CoreObligations.of_checkUnit_ok
#print axioms Lara.Surface.CoreObligations.checkUnit_complete
#print axioms Lara.Surface.check_sound
#print axioms Lara.Surface.check_complete
#print axioms Lara.Surface.checks_deterministic
#print axioms Lara.Surface.checks_supported

-- Pure elaboration alignment/completeness and production-pass boundaries.
#print axioms Lara.Surface.elaborateWithAudit_alignment
#print axioms Lara.Surface.elaborateWithAudit_reconstruction_boundary
#print axioms Lara.Surface.elaborateWithAudit_attack_boundary
#print axioms Lara.Surface.elaborateWithAudit_unit_boundary
#print axioms Lara.Surface.elaborateWithAudit_admission_boundary
#print axioms Lara.Surface.elaborateWithAudit_output_boundary
#print axioms Lara.Surface.reconstructArgument_preserves_conclusion
#print axioms Lara.Surface.reconstructArgument_preserves_obligations
#print axioms Lara.Surface.lowerCertificate_sound
#print axioms Lara.Surface.lowerCertificate_kernel_identity
#print axioms Lara.Surface.lowerCertificate_alpha_invariant
#print axioms Lara.Surface.resolveSurfaceAttacks_order_alignment
#print axioms Lara.Surface.resolveSurfaceAttacks_endpoint_membership
#print axioms Lara.Surface.outputFromAdmission_alignment
#print axioms Lara.Surface.elaborationPrologue_complete
#print axioms Lara.Surface.value_pass_complete
#print axioms Lara.Surface.comparison_pass_complete
#print axioms Lara.Surface.elaborate_complete

-- Headline preservation/reflection and the separately quotable projections.
#print axioms Lara.Surface.elaborate_preserves
#print axioms Lara.Surface.elaborate_reflects
#print axioms Lara.Surface.obligations_preserved
#print axioms Lara.Surface.attacks_preserved
#print axioms Lara.Surface.conclusions_preserved
#print axioms Lara.Surface.argument_order_preserved

-- Typed global renaming is distinct from alpha-equivalence. The transport
-- package covers supportedness, every elaboration pass, admission, and the
-- core checker; the headline theorem transports the audited elaboration.
#print axioms Lara.Surface.Binding.supported_rename_iff
#print axioms Lara.Surface.Renaming.checkUnit_ok_rename
#print axioms Lara.Surface.Renaming.checkUnit_isOk_rename
#print axioms Lara.Surface.Renaming.global_renaming_stage_transports
#print axioms Lara.Surface.Renaming.global_renaming_equivariant

-- Direct surface carrier/claim alignment and coherence parametric over
-- extension semantics satisfying `Observation.AttackExtensional sem.spec`.
#print axioms Lara.Surface.directAF_args
#print axioms Lara.Surface.directAF_attack_iff
#print axioms Lara.Surface.claimsOf_support_lt
#print axioms Lara.Surface.claimAlternativesOf_sorted
#print axioms Lara.Surface.directDecls_eq_checked
#print axioms Lara.Surface.directClaims_eq_coreClaims
#print axioms Lara.Surface.directClaim_eq_coreClaim?
#print axioms Lara.Surface.directClaim_support_bound
#print axioms Lara.Surface.direct_compiled_agree
-- Surface/core located-hole coherence (D8, D10).
#print axioms Lara.Surface.claimAlternatives_coherent
#print axioms Lara.Surface.claimAlternatives_holes_sound
#print axioms Lara.Surface.claimAlternatives_holes_complete
#print axioms Lara.Surface.coreHoleReport_obligations
#print axioms Lara.Surface.observe_coherent
#print axioms Lara.Surface.observe_grounded_coherent
#print axioms Lara.Surface.observe_complete_coherent
#print axioms Lara.Surface.observe_preferred_coherent
#print axioms Lara.Surface.observe_stable_coherent
#print axioms Lara.Surface.observe_semiStable_coherent
#print axioms Lara.Surface.unboundedDirectClaim_support_unaligned
#print axioms Lara.Surface.not_observe_coherent_of_unbounded_support

-- Exported surface examples and boundary witnesses.
#print axioms Lara.Examples.Surface.allForms_supported
#print axioms Lara.Examples.Surface.ambiguousInferenceReference_unsupported
#print axioms Lara.Examples.Surface.ambiguousNamedCertificate_isolated
#print axioms Lara.Examples.Surface.ambiguousNamedCertificate_unsupported
#print axioms Lara.Examples.Surface.asciiIdentifierTailParity
#print axioms Lara.Examples.Surface.asciiNumericStartParity
#print axioms Lara.Examples.Surface.authoredCellSpellings_normalize
#print axioms Lara.Examples.Surface.comparison_expansion_exact
#print axioms Lara.Examples.Surface.comparison_expansion_relation
#print axioms Lara.Examples.Surface.comparison_explicit_same_decls
#print axioms Lara.Examples.Surface.comparison_explicit_same_printed_ast
#print axioms Lara.Examples.Surface.declaredNonCellInterpolation_unsupported
#print axioms Lara.Examples.Surface.duplicateArgument_isolated
#print axioms Lara.Examples.Surface.duplicateArgument_unsupported
#print axioms Lara.Examples.Surface.equalCellReversedVariable_unsupported
#print axioms Lara.Examples.Surface.equalCellVariableProvenance_supported
#print axioms Lara.Examples.Surface.inferenceShapeMismatch_unsupported
#print axioms Lara.Examples.Surface.laterArgumentReference_isolated
#print axioms Lara.Examples.Surface.laterArgumentReference_unsupported
#print axioms Lara.Examples.Surface.literalGoalFallback_supported
#print axioms Lara.Examples.Surface.missingComparisonScheme_isolated
#print axioms Lara.Examples.Surface.missingComparisonScheme_unsupported
#print axioms Lara.Examples.Surface.named_value_explicit_same_term
#print axioms Lara.Examples.Surface.necessity_generated_ids_fresh
#print axioms Lara.Examples.Surface.noBindings_skips_claim_sort_validation
#print axioms Lara.Examples.Surface.normalizedCellCanonicalLiteral_supported
#print axioms Lara.Examples.Surface.normalizedComparisonRoles_supported
#print axioms Lara.Examples.Surface.premiseQuestionCollision_isolated
#print axioms Lara.Examples.Surface.premiseQuestionCollision_unsupported
#print axioms Lara.Examples.Surface.rawMatchingNoncanonicalLiteral_unsupported
#print axioms Lara.Examples.Surface.renamedComparisonParameters_supported
#print axioms Lara.Examples.Surface.sourceIdentifierClassifier_boundaries
#print axioms Lara.Examples.Surface.unboundInferenceParameter_unsupported
#print axioms Lara.Examples.Surface.unknownValueInterpolation_isolated
#print axioms Lara.Examples.Surface.unknownValueInterpolation_unsupported
#print axioms Lara.Examples.Surface.unresolvedAttackPath_isolated
#print axioms Lara.Examples.Surface.unresolvedAttackPath_unsupported
/-! ### M2b follow-up — realization closure

The plan's headline rows: the numeral-injectivity foundation, the closed leaf
vocabulary, the family-wide `checkUnit_complete` premises, and the assembled
checker equation (`Lara.Complexity.Numeral` / `Lara.Complexity.Gadget`). -/

#print axioms Lara.Complexity.Numeral.natRepr_inj
#print axioms Lara.Complexity.GadgetLeaf.encode_inj
#print axioms Lara.Complexity.formulaLeafEntries_keys_nodup
#print axioms Lara.Complexity.groundOfFormula_covers
#print axioms Lara.Complexity.formulaArguments_nodup
#print axioms Lara.Complexity.signatureStage_formula_none
#print axioms Lara.Complexity.formulaArguments_supported
#print axioms Lara.Complexity.hasAttack_formula
#print axioms Lara.Complexity.formulaAttacks_complete
#print axioms Lara.Complexity.checkUnit_formula_ok

-- The supporting public surface the headline rows rest on (CLAUDE.md: AxCheck
-- covers every new theorem).
#print axioms Lara.Complexity.Numeral.decodeNat_repr
#print axioms Lara.Complexity.Numeral.repr_no_dash
#print axioms Lara.Complexity.Numeral.natRepr_toList_inj
#print axioms Lara.Complexity.GadgetLeaf.encode_eq_iff
#print axioms Lara.Complexity.m2bPolicy_ruleLookup_clause
#print axioms Lara.Complexity.clauseSubst_keys
#print axioms Lara.Complexity.instAPats_clauseSubst_premises
#print axioms Lara.Complexity.instAPat_clauseSubst_concl
#print axioms Lara.Complexity.occurrenceLeafId_inj
#print axioms Lara.Complexity.lookupLeaf_eq_some_of_nodup
#print axioms Lara.Complexity.lookupLeaf_mem_snd
#print axioms Lara.Complexity.gammaOfFormula_negLit
#print axioms Lara.Complexity.gammaOfFormula_posLit
#print axioms Lara.Complexity.gammaOfFormula_occurrence
#print axioms Lara.Complexity.gammaOfFormula_query
#print axioms Lara.Complexity.gammaOfFormula_literalLeaf
#print axioms Lara.Complexity.groundOfFormula_wellSorted
#print axioms Lara.Complexity.formulaArguments_wellSorted
#print axioms Lara.Complexity.formulaAttacks_source_mem
#print axioms Lara.Complexity.formulaAttacks_target_mem
#print axioms Lara.Complexity.formulaArgument_conclusion
#print axioms Lara.Complexity.contraryMatch_rootConclusion_iff
#print axioms Lara.Complexity.contraryMatch_negLit_posLit
#print axioms Lara.Complexity.contraryMatch_posLit_negLit
#print axioms Lara.Complexity.contraryMatch_lit_occ
#print axioms Lara.Complexity.contraryMatch_clause_query
#print axioms Lara.Complexity.hasSupport_gadgetLeaf
#print axioms Lara.Complexity.hasSupport_clauseArgument
#print axioms Lara.Complexity.hasAttack_negLit_posLit
#print axioms Lara.Complexity.hasAttack_posLit_negLit
#print axioms Lara.Complexity.hasAttack_literal_occurrence
#print axioms Lara.Complexity.hasAttack_clause_query
#print axioms Lara.Complexity.Formula3.occurringVariables_nodup
#print axioms Lara.Complexity.Formula3.mem_occurringVariables
#print axioms Lara.Complexity.checkUnit_formula_accepts

-- Task 8: the compile image, the frozen promise/size obligations, and the
-- exact-edge characterization ("no closure-generated extras") of
-- Lara.Complexity.Reduction, with the reduction-facing surface of the gadget
-- and encoding modules it reads.
#print axioms Lara.Complexity.reduce_realizable
#print axioms Lara.Complexity.reduce_nodes
#print axioms Lara.Complexity.reduce_byteSize
#print axioms Lara.Complexity.reduceIso
#print axioms Lara.Complexity.coveredB_gadget
#print axioms Lara.Complexity.clauseArgument_index_inj
#print axioms Lara.Complexity.variable_mem_occurringVariables
#print axioms Lara.Complexity.subterm_clauseArgument_prem
#print axioms Lara.Complexity.clauseArgument_conclusion_eq
#print axioms Lara.Complexity.mem_formulaAttacks
#print axioms Lara.Complexity.undermine_negLit_mem
#print axioms Lara.Complexity.undermine_posLit_mem
#print axioms Lara.Complexity.undermine_clause_query_mem
#print axioms Lara.Complexity.undermine_literal_occurrence_mem
#print axioms Lara.Complexity.Formula3.exists_literal_of_mem_occurringVariables
#print axioms Lara.Complexity.Formula3.occurringVariables_length_le
#print axioms Lara.Complexity.Formula3.literals_length

-- Spike-era fixed-context surface: the pre-existing public
-- theorems of Lara.Complexity.Context and Lara.Complexity.Encoding that the
-- the M2b closure reads (registered here per a Task-7 review follow-up; the
-- occurringVariables Nodup row is above).
#print axioms Lara.Complexity.m2bSigma_wellFormed
#print axioms Lara.Complexity.m2bPolicy_wellSorted
#print axioms Lara.Complexity.m2bPolicy_ruleIds_unique
#print axioms Lara.Complexity.m2bPolicy_scopesWellFormed
#print axioms Lara.Complexity.m2bPolicy_noViolation
#print axioms Lara.Complexity.d_attacks_b
#print axioms Lara.Complexity.b_attacks_a
#print axioms Lara.Complexity.negative_lit_attacks_positive_lit
#print axioms Lara.Complexity.positive_lit_attacks_negative_lit
#print axioms Lara.Complexity.lit_attacks_occ
#print axioms Lara.Complexity.clause_attacks_query
#print axioms Lara.Complexity.b_does_not_attack_d
#print axioms Lara.Complexity.a_does_not_attack_b
#print axioms Lara.Complexity.lit_different_variable_does_not_attack
#print axioms Lara.Complexity.occ_does_not_attack_lit
#print axioms Lara.Complexity.m2bRegistry_empty
#print axioms Lara.Complexity.decode_size
#print axioms Lara.Complexity.decode_attack
#print axioms Lara.Complexity.erase_decode_args_nodup
#print axioms Lara.Complexity.fixedCredCompleteB_iff
#print axioms Lara.Complexity.matrixByteSize_eq_square
#print axioms Lara.Complexity.byteSize_accounting
#print axioms Lara.Complexity.byteSize_pos
#print axioms Lara.Complexity.nodeKeyByteSize_le
#print axioms Lara.Complexity.queryByteSize_le

-- Task 9 (Lara.Complexity): the cost-instrumented grounded kernel.
-- Evaluator agreement — every mirror's first projection is its
-- Lara.Grounded original.
#print axioms Lara.Complexity.anyAttackerC_fst
#print axioms Lara.Complexity.defendedAuxC_fst
#print axioms Lara.Complexity.defendedC_fst
#print axioms Lara.Complexity.stepAuxC_fst
#print axioms Lara.Complexity.stepC_fst
#print axioms Lara.Complexity.iterC_fst
#print axioms Lara.Complexity.groundedC_fst
-- Upper bounds: the full grounded run costs at most n³(1 + n).
#print axioms Lara.Complexity.anyAttackerC_cost_le
#print axioms Lara.Complexity.defendedAuxC_cost_le
#print axioms Lara.Complexity.defendedC_cost_le
#print axioms Lara.Complexity.stepAuxC_cost_cons
#print axioms Lara.Complexity.stepAuxC_cost_le
#print axioms Lara.Complexity.stepC_cost_le
#print axioms Lara.Complexity.iter_length_le
#print axioms Lara.Complexity.iterC_cost_le
#print axioms Lara.Complexity.groundedC_cost_le
-- Short-circuit scan composition (the public per-round accounting layer).
#print axioms Lara.Complexity.anyAttackerC_cons_hit
#print axioms Lara.Complexity.anyAttackerC_cons_miss
#print axioms Lara.Complexity.anyAttackerC_prefix
#print axioms Lara.Complexity.defendedAuxC_cons_miss
#print axioms Lara.Complexity.defendedAuxC_cons_defended
#print axioms Lara.Complexity.defendedAuxC_no_attack
#print axioms Lara.Complexity.defendedAuxC_append_true
#print axioms Lara.Complexity.defendedAuxC_uniform
#print axioms Lara.Complexity.stepAuxC_cost_append
#print axioms Lara.Complexity.stepAuxC_cost_uniform
-- Corrected lower bounds: the proved universal lower bound is quadratic; the
-- two-node evaluation refutes the rejected exact cubic inequality at `n = 2`.
#print axioms Lara.Complexity.defendedAuxC_cost_ge_one
#print axioms Lara.Complexity.defendedC_cost_ge_one
#print axioms Lara.Complexity.stepAuxC_cost_ge
#print axioms Lara.Complexity.stepC_cost_ge
#print axioms Lara.Complexity.iterC_cost_ge
#print axioms Lara.Complexity.groundedC_cost_ge
#print axioms Lara.Complexity.groundedC_twoNodeAllAttacks_cost

-- Task 10 (Lara.Examples.Complexity): the fixed-context realizable quartic
-- witness — closed leaf vocabulary, class membership through the executable
-- checker, iterate shape, and the existential quartic worst case.
#print axioms Lara.Examples.Complexity.quarticLeaves_length
#print axioms Lara.Examples.Complexity.quarticAttack_eq_true_iff
#print axioms Lara.Examples.Complexity.quartic_size
#print axioms Lara.Examples.Complexity.QuarticLeaf.encode_inj
#print axioms Lara.Examples.Complexity.quarticGamma_encode
#print axioms Lara.Examples.Complexity.quarticGround_covers
#print axioms Lara.Examples.Complexity.contraryMatch_d_b
#print axioms Lara.Examples.Complexity.contraryMatch_b_a
#print axioms Lara.Examples.Complexity.quartic_checkUnit_accepts
#print axioms Lara.Examples.Complexity.quartic_checkUnit_ok
#print axioms Lara.Examples.Complexity.quarticEmpty_accepts
#print axioms Lara.Examples.Complexity.quarticEmpty_checkUnit_ok
#print axioms Lara.Examples.Complexity.quartic_realizable
#print axioms Lara.Examples.Complexity.quartic_iter_one
#print axioms Lara.Examples.Complexity.quartic_iter_fix
#print axioms Lara.Examples.Complexity.quartic_cost_ge
#print axioms Lara.Examples.Complexity.quartic_cost_eval_two
#print axioms Lara.Examples.Complexity.quartic_cost_eval_three
#print axioms Lara.Examples.Complexity.quartic_cost_eval_four

-- Task 11 (Lara.Complexity + the Examples transfer): the shared
-- carrier-status evaluator. carrierStatusC_cost_le is the paper-citable
-- GroundedStatus headline; statusSharedC_cost_le is internal accounting.
#print axioms Lara.Complexity.outScanC_fst
#print axioms Lara.Complexity.outScanC_cost_le
#print axioms Lara.Complexity.labelFromGroundedC_fst
#print axioms Lara.Complexity.labelFromGroundedC_cost_le
#print axioms Lara.Complexity.supportScanC_fst
#print axioms Lara.Complexity.supportScanC_cost_le
#print axioms Lara.Complexity.statusSharedC_fst
#print axioms Lara.Complexity.statusSharedC_cost_le
#print axioms Lara.Complexity.statusSharedC_cost_ge_grounded
#print axioms Lara.Complexity.claim_support_length_le
#print axioms Lara.Complexity.carrierStatusC_fst
#print axioms Lara.Complexity.carrierStatusC_cost_le
#print axioms Lara.Examples.Complexity.carrierStatus_quartic_cost_ge

-- Task 12 (Lara.Complexity.Reduction): 3SAT reduction correctness inside
-- the fixed realizable class, the adjacency corollaries that keep class
-- membership and size quotable with it, the executable fixtures, and the
-- class-membership negative control.
#print axioms Lara.Complexity.reduce_correct
#print axioms Lara.Complexity.reduce_correct_realizable
#print axioms Lara.Complexity.reduce_correct_nodes
#print axioms Lara.Complexity.reduce_correct_byteSize
#print axioms Lara.Complexity.positiveFixture_satisfiable
#print axioms Lara.Complexity.positiveFixture_accepted
#print axioms Lara.Complexity.negativeFixture_rejected
#print axioms Lara.Complexity.negativeFixture_unsatisfiable
#print axioms Lara.Complexity.selfEdgeCode_not_realizable

/-! ### M2b follow-up — shared lemma extraction

The drift-tripwire lemmas formerly held as verbatim private copies by the
gadget and witness modules, now public at their owning modules, plus the
shared ok-assembly helper behind the named accepted checker outputs. -/

#print axioms Lara.nfTerm_id
#print axioms Lara.nfTerms_id
#print axioms Lara.nf_id
#print axioms Lara.equiv_id_eq
#print axioms Lara.Complexity.Numeral.toDigits_inj
#print axioms Lara.Complexity.m2bDefeat_contraries
#print axioms Lara.Support.instAPat_head
#print axioms Lara.Support.nodup_map_of_injective
#print axioms Lara.Check.Unit.exists_ok_of_isOk
#print axioms Lara.Check.Unit.okValue_eq

/-! ### PW0 — possible-world outer-model gate -/
-- Task 1 (Lara.PW.Outer): typed normality, valuation coherence, and the
-- valuation-congruence core that makes T4 a one-line instantiation.
#print axioms Lara.PW.sat_imp
#print axioms Lara.PW.sat_K
#print axioms Lara.PW.sat_nec
#print axioms Lara.PW.sat_dia_iff_not_box_neg
#print axioms Lara.PW.sat_box_top
#print axioms Lara.PW.sat_box_conj
#print axioms Lara.PW.sat_congr
#print axioms Lara.PW.not_sat_two_status
#print axioms Lara.PW.exists_status_of_total

-- Task 2 (Lara.PW.Uniform): T3 reduction to ordinary multimodal Kripke
-- semantics, with KForm/KSat defined independently.
#print axioms Lara.PW.sat_lift

-- Task 3 (Lara.PW.Compare): T5 tagged comparison, the profile
-- characterization, and the adequacy tying `crossCompare` to the model's ⟨b⟩.
#print axioms Lara.PW.compare_none
#print axioms Lara.PW.compare_no_candidate
#print axioms Lara.PW.compare_all_rejected
#print axioms Lara.PW.compare_comparable
#print axioms Lara.PW.mem_compare_profile_iff
#print axioms Lara.PW.incomparable_ne_comparable
#print axioms Lara.PW.mem_compare_iff_sat_dia
#print axioms Lara.PW.not_sat_dia_of_incomparable
#print axioms Lara.PW.compare_translationUndefined_iff

-- Task 4 (Lara.PW.Instance): T1 world-local preservation, T4 coherence, the
-- valuation coherence discharges, and T0 conservativity.
#print axioms Lara.PW.Instance.srcStatus_iff_cmpStatus
#print axioms Lara.PW.Instance.sat_src_iff_cmp
#print axioms Lara.PW.Instance.cmpVal_functional
#print axioms Lara.PW.Instance.cmpVal_total
#print axioms Lara.PW.Instance.srcVal_functional
#print axioms Lara.PW.Instance.srcVal_total
#print axioms Lara.PW.Instance.t0_cmp
#print axioms Lara.PW.Instance.t0_src

-- Task 5 (Lara.Examples.PW): the T7 witness in both modal readings, each
-- under both valuations, the T2 negative controls (all five stronger frame
-- axioms refuted), one fixture per incomparability reason, and the
-- Presents-discharged instantiation of the gate-3 semantic theorem.
#print axioms Lara.Examples.PW.unitT7src_accepted
#print axioms Lara.Examples.PW.unitT7tgt_accepted
#print axioms Lara.Examples.PW.t7_src_justified
#print axioms Lara.Examples.PW.t7_tgt_defeated
#print axioms Lara.Examples.PW.t7_transport_wellFormed
#print axioms Lara.Examples.PW.t7_support_transported
#print axioms Lara.Examples.PW.t7_witness
#print axioms Lara.Examples.PW.t7_dia_defeated
#print axioms Lara.Examples.PW.t7_box_defeated
#print axioms Lara.Examples.PW.t7_dia_defeated_src
#print axioms Lara.Examples.PW.t7_box_defeated_src
#print axioms Lara.Examples.PW.presentsT7
#print axioms Lara.Examples.PW.t7_dia_via_adequacy
#print axioms Lara.Examples.PW.t7_no_two_status
#print axioms Lara.Examples.PW.sat_T_fails
#print axioms Lara.Examples.PW.sat_D_fails
#print axioms Lara.Examples.PW.sat_B_fails
#print axioms Lara.Examples.PW.sat_5_fails
#print axioms Lara.Examples.PW.sat_4_fails
#print axioms Lara.Examples.PW.unitOverlap_accepted
#print axioms Lara.Examples.PW.overlap_comparable
#print axioms Lara.Examples.PW.overlap_translationUndefined
#print axioms Lara.Examples.PW.overlap_local_gap
#print axioms Lara.Examples.PW.overlap_noCandidate
#print axioms Lara.Examples.PW.overlap_allRejected
#print axioms Lara.Examples.PW.presentsOverlapRejected
#print axioms Lara.Examples.PW.overlap_rejected_no_dia

/-! ### PW-T6 — exact checked-support transport -/
-- Task 1 (Lara.PW.Translation): the partial symbol translation and its
-- structural lifts, the list/substitution/rule bookkeeping, the two
-- commuting facts (instantiation, ≡), and the inert identity translation.
#print axioms Lara.PW.SymMap.id
#print axioms Lara.PW.trTerm
#print axioms Lara.PW.trTerms
#print axioms Lara.PW.trAtom
#print axioms Lara.PW.trAtoms
#print axioms Lara.PW.trPat
#print axioms Lara.PW.trPats
#print axioms Lara.PW.trAPat
#print axioms Lara.PW.trAPats
#print axioms Lara.PW.trSubst
#print axioms Lara.PW.trQuestion
#print axioms Lara.PW.trQuestions
#print axioms Lara.PW.trRule
#print axioms Lara.PW.trSupport
#print axioms Lara.PW.trSupportList
#print axioms Lara.PW.trSupportDis
#print axioms Lara.PW.trAtoms_getElem?
#print axioms Lara.PW.trAtoms_length
#print axioms Lara.PW.trAtoms_defined
#print axioms Lara.PW.trSubst_fst
#print axioms Lara.PW.lookupSubst_tr
#print axioms Lara.PW.instPat_tr
#print axioms Lara.PW.instPats_tr
#print axioms Lara.PW.instAPat_tr
#print axioms Lara.PW.instAPats_tr
#print axioms Lara.PW.trTerm_nf
#print axioms Lara.PW.trTerms_nf
#print axioms Lara.PW.trAtom_nf
#print axioms Lara.PW.equiv_tr
#print axioms Lara.PW.trQuestion_inv
#print axioms Lara.PW.trQuestions_mem
#print axioms Lara.PW.trQuestions_mem_rev
#print axioms Lara.PW.trQuestions_names
#print axioms Lara.PW.trQuestions_mand_names
#print axioms Lara.PW.trRule_inv
#print axioms Lara.PW.trRule_mode
#print axioms Lara.PW.trRule_params
#print axioms Lara.PW.trRule_allowTrusted
#print axioms Lara.PW.trRule_certifiers
#print axioms Lara.PW.trRule_questionNames
#print axioms Lara.PW.trRule_mandatoryNames
#print axioms Lara.PW.trSupportList_getElem?
#print axioms Lara.PW.trSupportList_length
#print axioms Lara.PW.trSupportDis_fst
#print axioms Lara.PW.trSupportDis_getElem?
#print axioms Lara.PW.trTerm_id
#print axioms Lara.PW.trTerms_id
#print axioms Lara.PW.trAtom_id
#print axioms Lara.PW.trAtoms_id
#print axioms Lara.PW.trPat_id
#print axioms Lara.PW.trPats_id
#print axioms Lara.PW.trAPat_id
#print axioms Lara.PW.trAPats_id
#print axioms Lara.PW.trSubst_id
#print axioms Lara.PW.trQuestion_id
#print axioms Lara.PW.trQuestions_id
#print axioms Lara.PW.trRule_id
#print axioms Lara.PW.trSupport_id
#print axioms Lara.PW.trSupportList_id
#print axioms Lara.PW.trSupportDis_id

-- Task 2 (Lara.PW.Structural): the StructuralBridge contract, the T6
-- transport theorem and its completeness/claim-level corollaries, the
-- target-registry occurrence replay, and the induced checker-tied
-- applicability judgment.
#print axioms Lara.PW.StructuralBridge.refl
#print axioms Lara.PW.support_transport
#print axioms Lara.PW.support_transport_complete
#print axioms Lara.PW.supports_transport
#print axioms Lara.PW.transport_occurrences_accounted
#print axioms Lara.PW.Admits
#print axioms Lara.PW.admits_transport

-- Task 3 (Lara.Examples.PWStructural): the identity endobridge at the T7
-- pair with the packaged T6/T8 boundary, the genuine renaming bridge with
-- its transported derivation, and the translation-domain negative.
#print axioms Lara.Examples.PW.admitsIdT7
#print axioms Lara.Examples.PW.t7_t6_transport
#print axioms Lara.Examples.PW.t7_t6_boundary
#print axioms Lara.Examples.PW.bridgeRen
#print axioms Lara.Examples.PW.ren_support_renamed
#print axioms Lara.Examples.PW.ren_leaf_translated
#print axioms Lara.Examples.PW.hasSupport_ren
#print axioms Lara.Examples.PW.ren_conclusion
#print axioms Lara.Examples.PW.ren_transport
#print axioms Lara.Examples.PW.ren_out_of_vocabulary
#print axioms Lara.Examples.PW.ren_translationUndefined
-- The strict-certificate renaming bridge — cert_ok discharged
-- non-vacuously off the identity, and the transported strict derivation.
#print axioms Lara.Examples.PW.bridgeCert
#print axioms Lara.Examples.PW.cert_accept_translated
#print axioms Lara.Examples.PW.cert_reject_untranslated
#print axioms Lara.Examples.PW.cert_support_renamed
#print axioms Lara.Examples.PW.hasSupport_cert
#print axioms Lara.Examples.PW.cert_transport
-- The fixture's drift guards — the acceptance judgments read the
-- certifier triple on both sides, and the certificate arm is the only
-- reachable assurance (`allowTrusted` pinned off, source and target).
#print axioms Lara.Examples.PW.cert_reject_mismatched_certifier
#print axioms Lara.Examples.PW.cert_target_rule
#print axioms Lara.Examples.PW.cert_only_assurance

/-! ### PW-T9 — structural-path composition -/
-- The definitions `StructuralBridge.comp`, `AdmitsSteps`, `BridgePath`,
-- `BridgePath.compose`, `BridgePath.trans`, `Commutes`, and `Accepted` have no
-- standalone axiom rows; the theorem rows below audit them transitively. Every
-- theorem declaration in both PW-T9 modules is gated directly.

-- Translation laws and exact binary structural-bridge composition.
#print axioms Lara.PW.SymMap.id_comp
#print axioms Lara.PW.SymMap.comp_id
#print axioms Lara.PW.trTerm_comp
#print axioms Lara.PW.trTerms_comp
#print axioms Lara.PW.trAtom_comp
#print axioms Lara.PW.trAtoms_comp
#print axioms Lara.PW.trAtom_comp_none_left
#print axioms Lara.PW.trAtom_comp_none_mid
#print axioms Lara.PW.trPat_comp
#print axioms Lara.PW.trPats_comp
#print axioms Lara.PW.trAPat_comp
#print axioms Lara.PW.trAPats_comp
#print axioms Lara.PW.trSubst_comp
#print axioms Lara.PW.trSupport_comp
#print axioms Lara.PW.trSupportList_comp
#print axioms Lara.PW.trSupportDis_comp
#print axioms Lara.PW.trQuestion_comp
#print axioms Lara.PW.trQuestions_comp

-- The shared traversal seam behind the composition family.
#print axioms Lara.PW.zipOpt_bind
#print axioms Lara.PW.trAtoms_cons
#print axioms Lara.PW.trTerms_cons
#print axioms Lara.PW.trTerm_con
#print axioms Lara.PW.trPats_cons
#print axioms Lara.PW.trAPats_cons
#print axioms Lara.PW.trSubst_cons
#print axioms Lara.PW.trQuestions_cons
#print axioms Lara.PW.trSupportList_cons
#print axioms Lara.PW.trSupportDis_cons
#print axioms Lara.PW.trRule_comp
#print axioms Lara.PW.admits_comp
#print axioms Lara.PW.admits_steps_of_intermediate
#print axioms Lara.PW.support_transport_comp

-- Arbitrary typed paths, their folded composite, and exact path transport.
#print axioms Lara.PW.BridgePath.trans_eq_compose
#print axioms Lara.PW.path_support_transport

-- Explicit direct-versus-path commutation and its structural consequences.
#print axioms Lara.PW.Commutes.of_maps_eq
#print axioms Lara.PW.Commutes.leafMap_eq
#print axioms Lara.PW.Commutes.predMap_eq
#print axioms Lara.PW.Commutes.conMap_eq
#print axioms Lara.PW.Commutes.sym_eq
#print axioms Lara.PW.direct_transport_agrees
#print axioms Lara.PW.commutes_on_rules
#print axioms Lara.PW.commutes_on_leaves

-- Checker-tied applicability and full accepted-edge separation.
#print axioms Lara.PW.admits_iff_of_commutes
#print axioms Lara.PW.accepted_iff_of_commutes

-- The named bridges, paths, candidate relations, and checked worlds in the
-- example module are definitions audited transitively by these direct theorem
-- gates.

-- Live two-leg path and its commuting direct bridge.
#print axioms Lara.Examples.PW.Compose.ren2_conclusion
#print axioms Lara.Examples.PW.Compose.ren_path_trans
#print axioms Lara.Examples.PW.Compose.ren_path_transport
#print axioms Lara.Examples.PW.Compose.ren_path_commutes
#print axioms Lara.Examples.PW.Compose.ren_direct_transport_agrees

-- Three-edge path and theorem-level composition/path witnesses.
#print axioms Lara.Examples.PW.Compose.ren_path3_commutes
#print axioms Lara.Examples.PW.Compose.ren_path3_transport_agrees
#print axioms Lara.Examples.PW.Compose.ren_support_transport_comp
#print axioms Lara.Examples.PW.Compose.ren_commutes_on_rule
#print axioms Lara.Examples.PW.Compose.ren_commutes_on_leaf
#print axioms Lara.Examples.PW.Compose.ren_commutes_on_symbol_maps

-- Identity-world applicability and accepted-edge separation.
#print axioms Lara.Examples.PW.Compose.admitsSelfT7
#print axioms Lara.Examples.PW.Compose.t7_admits_steps_of_intermediate
#print axioms Lara.Examples.PW.Compose.t7_admits_comp_iff
#print axioms Lara.Examples.PW.Compose.t7_admits_composite
#print axioms Lara.Examples.PW.Compose.t7_identity_path_commutes
#print axioms Lara.Examples.PW.Compose.t7_admits_iff_of_commutes
#print axioms Lara.Examples.PW.Compose.t7_candidate_relations_agree
#print axioms Lara.Examples.PW.Compose.t7_accepted_iff_of_commutes
#print axioms Lara.Examples.PW.Compose.t7_accepted_inhabited
#print axioms Lara.Examples.PW.Compose.t7_accepted_needs_candidate_coherence

-- Successful but noncommuting direct/path triangles.
#print axioms Lara.Examples.PW.Compose.direct_ne_composed_support
#print axioms Lara.Examples.PW.Compose.direct_ne_composed_claim

-- Certificate composition, a mid-path gap, and nonempty translation witnesses.
#print axioms Lara.Examples.PW.Compose.certComp_two_live_legs
#print axioms Lara.Examples.PW.Compose.mid_path_out_of_vocabulary
#print axioms Lara.Examples.PW.Compose.mid_path_translationUndefined
#print axioms Lara.Examples.PW.Compose.gapAppUnit_accepted
#print axioms Lara.Examples.PW.Compose.gap_admits_comp_fails
#print axioms Lara.Examples.PW.Compose.trSubst_nonempty_computes
#print axioms Lara.Examples.PW.Compose.trPat_nonempty_computes
#print axioms Lara.Examples.PW.Compose.mid_path_support_undefined
#print axioms Lara.Examples.PW.Compose.trQuestions_nonempty_computes
#print axioms Lara.Examples.PW.Compose.trSupportDis_nonempty_computes

-- Focused witnesses for the remaining composition laws.
#print axioms Lara.Examples.PW.Compose.first_leg_gap_computes
#print axioms Lara.Examples.PW.Compose.first_leg_gap_law
#print axioms Lara.Examples.PW.Compose.id_comp_ren2
#print axioms Lara.Examples.PW.Compose.comp_id_ren2
#print axioms Lara.Examples.PW.Compose.zipOpt_computes

/-! ### PW-T8 — conditional status preservation -/
-- The definitions `AttackBisim`, `SupportCorr`, `AFIso`, `AFIso.graph`,
-- `SymMap.Injective`, `Corr`, `StatusBridge` have no standalone rows; the
-- theorem rows below audit them transitively. Every theorem declaration in
-- the three PW-T8 modules is gated directly.

-- Generic layer (Lara.PW.AFBisim).
#print axioms Lara.PW.AttackBisim.symm
#print axioms Lara.PW.directIn_bisim
#print axioms Lara.PW.directOut_bisim
#print axioms Lara.PW.directIn_iff_of_bisim
#print axioms Lara.PW.directOut_iff_of_bisim
#print axioms Lara.PW.labelC_of_bisim
#print axioms Lara.PW.statusC_congr
#print axioms Lara.PW.statusC_of_bisim
#print axioms Lara.PW.AFIso.toBisim
#print axioms Lara.PW.labelC_of_iso
#print axioms Lara.PW.statusC_of_iso
#print axioms Lara.PW.supportCorr_of_image

-- Lara instantiation (Lara.PW.Status).
#print axioms Lara.PW.SymMap.id_injective
#print axioms Lara.PW.trTerm_inj
#print axioms Lara.PW.trTerms_inj
#print axioms Lara.PW.trAtom_inj
#print axioms Lara.PW.equiv_tr_reflect
#print axioms Lara.PW.corr_lt
#print axioms Lara.PW.StatusBridge.bisim
#print axioms Lara.PW.corr_conclusion
#print axioms Lara.PW.claimSupport_corr
#print axioms Lara.PW.status_transport_of_corr
#print axioms Lara.PW.status_transport
#print axioms Lara.PW.srcStatus_transport
#print axioms Lara.PW.sat_status_iff_box
#print axioms Lara.PW.sat_status_iff_dia
#print axioms Lara.PW.sat_status_iff_box_src
#print axioms Lara.PW.SymMap.Injective.comp
#print axioms Lara.PW.corr_comp_iff
#print axioms Lara.PW.StatusBridge.comp

-- PW-T8 examples (Lara.Examples.PWStatus).
#print axioms Lara.Examples.PW.Status.t7_forth
#print axioms Lara.Examples.PW.Status.t7_l2_mem
#print axioms Lara.Examples.PW.Status.t7_unmatched
#print axioms Lara.Examples.PW.Status.t7_not_statusBridge
#print axioms Lara.Examples.PW.Status.t7_not_statusBridge_of_flip
#print axioms Lara.Examples.PW.Status.t7_forward_hom_insufficient
#print axioms Lara.Examples.PW.Status.unitS1_accepted
#print axioms Lara.Examples.PW.Status.unitS2_accepted
#print axioms Lara.Examples.PW.Status.unitR1_accepted
#print axioms Lara.Examples.PW.Status.unitR2_accepted
#print axioms Lara.Examples.PW.Status.symR_injective
#print axioms Lara.Examples.PW.Status.s1_r1_statusBridge
#print axioms Lara.Examples.PW.Status.s2_r2_statusBridge
#print axioms Lara.Examples.PW.Status.t8_justified_preserved
#print axioms Lara.Examples.PW.Status.t8_justified_cells
#print axioms Lara.Examples.PW.Status.t8_defeated_preserved
#print axioms Lara.Examples.PW.Status.t8_defeated_cells
#print axioms Lara.Examples.PW.Status.t8_gap_preserved
#print axioms Lara.Examples.PW.Status.t8_gap_cells
#print axioms Lara.Examples.PW.Status.t8_renamed
#print axioms Lara.Examples.PW.Status.unitS3_accepted
#print axioms Lara.Examples.PW.Status.unitR3_accepted
#print axioms Lara.Examples.PW.Status.s3_corr_diag
#print axioms Lara.Examples.PW.Status.s3_r3_statusBridge
#print axioms Lara.Examples.PW.Status.t8_contested_preserved
#print axioms Lara.Examples.PW.Status.t8_contested_cells
#print axioms Lara.Examples.PW.Status.r_edge_accepted
#print axioms Lara.Examples.PW.Status.r_all_bridged
#print axioms Lara.Examples.PW.Status.t8_box_defeated_r
#print axioms Lara.Examples.PW.Status.t8_box_defeated_r_holds

/-! ### Theory M4 — the fragment/linking context calculus

Phase F0 is definitions only (`Lara.Context.Fragment`), so it has nothing to
audit. F1 mechanizes the calculus — the guard's rejection classes, the
saturation, Γ transport, acceptance, the merge's semantic inertness and
context composition — F2 proves contextual representation independence, and
F3 adds the surface corollary. -/

-- Invariants.Merge: node-merging morphisms of argumentation frameworks
#print axioms Lara.Grounded.iter_add
#print axioms Lara.Grounded.stable_iter_add
#print axioms Lara.Grounded.mem_grounded_iff_iter
#print axioms Lara.Invariants.AFMerge.iter_iff
#print axioms Lara.Invariants.AFMerge.grounded_iff
#print axioms Lara.Invariants.AFMerge.attackedByIn_eq
#print axioms Lara.Invariants.AFMerge.labelC_eq
#print axioms Lara.Invariants.AFMerge.statusC_eq
#print axioms Lara.Invariants.mem_support_iff
#print axioms Lara.Invariants.CarrierMerge.toAFMerge
#print axioms Lara.Invariants.CarrierMerge.status_eq

-- Context.Link: the linking calculus (F1)
#print axioms Lara.Context.mem_dedupList
#print axioms Lara.Context.dedupList_nodup
#print axioms Lara.Context.dedupList_eq_self
#print axioms Lara.Context.conclusionOf_eq_some_iff
#print axioms Lara.Context.mem_conclusionCache
#print axioms Lara.Context.conclusionCache_sound
#print axioms Lara.Context.conclusionCache_terms
#print axioms Lara.Context.conclusionCache_of_nodes
#print axioms Lara.Context.conclusionCache_eq_conflictCache
#print axioms Lara.Context.link_some_inv
#print axioms Lara.Context.mem_conclusionCache_of_sub
#print axioms Lara.Context.link_cache_bridge
#print axioms Lara.Context.firstDup?_none_iff
#print axioms Lara.Context.firstMissing?_none_iff
#print axioms Lara.Context.firstShared?_none_iff
#print axioms Lara.Context.idHygieneFault_none_iff
#print axioms Lara.Context.sigmaPolicyFault_none_iff
#print axioms Lara.Context.linkOk_eq_true_iff
#print axioms Lara.Context.link_eq_some
#print axioms Lara.Context.link_eq_none
#print axioms Lara.Context.exists_fault_of_not_linkOk
#print axioms Lara.Context.mem_crossAttsFrom
#print axioms Lara.Context.attackFor_source
#print axioms Lara.Context.attackFor_target
#print axioms Lara.Context.attackOcc_attackFor
#print axioms Lara.Context.covered_of_mem_attackFor
#print axioms Lara.Context.covered_mono
#print axioms Lara.Context.hasAttack_attackFor
#print axioms Lara.Context.crossAttsFrom_spec
#print axioms Lara.Context.cache_spec_left
#print axioms Lara.Context.cache_spec_right
#print axioms Lara.Context.crossAtts_spec
#print axioms Lara.Context.crossAtts_covers
#print axioms Lara.Context.crossAtts_covers'
#print axioms Lara.Context.linkGamma_extends_left
#print axioms Lara.Context.linkGamma_extends_right
#print axioms Lara.Context.groundWellSorted_append
#print axioms Lara.Context.termsWellSorted_iff_mem
#print axioms Lara.Context.argsWellSorted_link
#print axioms Lara.Context.signatureStage_link
#print axioms Lara.Context.SideOk.mono_gamma
#print axioms Lara.Context.SideOk.toHoles
#print axioms Lara.Context.SideOkHoles.toSideOk
#print axioms Lara.Context.SideOkHoles.mono_gamma
#print axioms Lara.Context.fragmentAF_eq
#print axioms Lara.Context.link_attackComplete
#print axioms Lara.Context.link_checked
#print axioms Lara.Context.linkedUnit_args_complete
#print axioms Lara.Context.link_accepted_raw
#print axioms Lara.Context.link_attackComplete_holes
#print axioms Lara.Context.linkedUnit_args_typed
#print axioms Lara.Context.link_checked_holes

-- Context.LinkHoles: linking units with located holes (issue #13)
#print axioms Lara.Context.filter_dedupList
#print axioms Lara.Context.conclusionOf_eq_none_of_not_complete
#print axioms Lara.Context.conclusionCache_completeArgs
#print axioms Lara.Context.crossAtts_endpoints_complete
#print axioms Lara.Context.crossAtts_completeArgs
#print axioms Lara.Context.link_accepted_holes
#print axioms Lara.Context.crossAtts_avoid_holes
#print axioms Lara.Context.link_classify
#print axioms Lara.Context.link_hole_report
#print axioms Lara.Context.link_side_hole_reported
#print axioms Lara.Context.link_node_report
#print axioms Lara.Context.link_hole_source_inert
#print axioms Lara.Context.link_shared_occurrence_edge
#print axioms Lara.Context.link_edge_iff

-- Context.Merge: the structural merge is semantically inert (F1)
#print axioms Lara.Context.posOf_lt
#print axioms Lara.Context.getElem?_posOf
#print axioms Lara.Context.posOf_getElem
#print axioms Lara.Context.termCarrier_attack_eq_edgeB
#print axioms Lara.Context.dedup_carrierMerge
#print axioms Lara.Context.dedup_status_eq
#print axioms Lara.Context.compileUnit_eq_termCarrier
#print axioms Lara.Context.link_merge_status_eq
#print axioms Lara.Context.linkedUnit_args_linkedPos_frag
#print axioms Lara.Context.linkedUnit_args_linkedPos_ctx
#print axioms Lara.Context.linkedPos_of_index

-- Context.Compose: composition of contexts (F1)
#print axioms Lara.Context.composeOk_eq_true_iff
#print axioms Lara.Context.compose_eq_some
#print axioms Lara.Context.compose_eq_none
#print axioms Lara.Context.exists_fault_of_not_composeOk
#print axioms Lara.Context.eq_composedContext
#print axioms Lara.Context.mem_residualImports
#print axioms Lara.Context.composed_declared
#print axioms Lara.Context.composed_args
#print axioms Lara.Context.composed_atts
#print axioms Lara.Context.composed_imports
#print axioms Lara.Context.composed_ownIds
#print axioms Lara.Context.linkOk_composed
#print axioms Lara.Context.residualImports_assoc
#print axioms Lara.Context.composeOk_assoc_left
#print axioms Lara.Context.composeOk_assoc_right
#print axioms Lara.Context.compose_assoc_fields
#print axioms Lara.Context.compose_assoc_mem
#print axioms Lara.Context.sideOkHoles_composed
#print axioms Lara.Context.sideOk_composed

-- Context.Equivalence: contextual representation independence (F2)
#print axioms Lara.Context.mapAssurFrag_declared
#print axioms Lara.Context.mapAssurFrag_imports
#print axioms Lara.Context.mapAssurFrag_sigma
#print axioms Lara.Context.mapAssurFrag_policy
#print axioms Lara.Context.mapAssurFrag_exports
#print axioms Lara.Context.mapAssurFrag_args
#print axioms Lara.Context.mapAssurFrag_atts
#print axioms Lara.Context.linkFault_mapAssurFrag
#print axioms Lara.Context.linkOk_mapAssurFrag
#print axioms Lara.Context.linkGamma_mapAssurFrag
#print axioms Lara.Context.linkGround_mapAssurFrag
#print axioms Lara.Context.dedupList_map_of_injective
#print axioms Lara.Context.eq_of_map_eq_self
#print axioms Lara.Context.conflictAttackableB_mapAssur
#print axioms Lara.Context.attackFor_mapAssur
#print axioms Lara.Context.crossAttsFrom_map
#print axioms Lara.Context.conclusionCache_map
#print axioms Lara.Context.termWellSorted_mapAssur
#print axioms Lara.Context.termsWellSorted_mapAssur
#print axioms Lara.Context.dischargesWellSorted_mapAssur
#print axioms Lara.Context.argsWellSorted_map
#print axioms Lara.Context.signatureStage_map
#print axioms Lara.Context.attackOcc_mapAssurAtt
#print axioms Lara.Context.contains_mapAssur
#print axioms Lara.Context.covered_mapAssur
#print axioms Lara.Context.conflictAttackable_mapAssur
#print axioms Lara.Context.crossAtts_relabel
#print axioms Lara.Context.link_relabel_commutes
#print axioms Lara.Context.attackComplete_map
#print axioms Lara.Context.signatureStage_of_ok
#print axioms Lara.Context.checkUnit_map
#print axioms Lara.Context.checkUnit_map_program
#print axioms Lara.Context.nodes_conclusion_map
#print axioms Lara.Context.compileUnit_map
-- The projection layer: `obsGen` is `obs` with the per-export reading
-- left open, so `obs_eq_of_ok` and `backend_replacement_congruence` below are
-- one-line corollaries of it. Rationale in docs/theory-m4-generic-observation.md §2.
#print axioms Lara.Context.obsGen_incompatible
#print axioms Lara.Context.obsGen_rejected
#print axioms Lara.Context.obsGen_eq_of_ok
#print axioms Lara.Context.obs_eq_obsGen
#print axioms Lara.Context.obs_eq_of_ok
#print axioms Lara.Context.exists_accepted_of_admissible
#print axioms Lara.Context.exists_accepted_relabel
#print axioms Lara.Context.link_relabel_program
#print axioms Lara.Context.compileUnit_link_relabel
#print axioms Lara.Context.obsGen_congr
#print axioms Lara.Context.backend_replacement_congruence
#print axioms Lara.Context.mapAssur_id
#print axioms Lara.Context.mapAssurList_id
#print axioms Lara.Context.mapAssurDis_id
#print axioms Lara.Context.mapAssurAtt_id
#print axioms Lara.Context.mapAssur_id_eq
#print axioms Lara.Context.mapAssurAtt_id_eq
#print axioms Lara.Context.mapAssurFrag_id
#print axioms Lara.Context.fixesContext_id
#print axioms Lara.Context.registry_swap_congruence
#print axioms Lara.Context.map_eq_self_of_mem
#print axioms Lara.Context.fixesContext_composed
#print axioms Lara.Context.admissible_composed
#print axioms Lara.Context.backend_replacement_congruence_composed
#print axioms Lara.Context.whole_program_replacement
#print axioms Lara.Context.compileUnit_eq_of_program
#print axioms Lara.Context.obsGen_hole_blind
#print axioms Lara.Context.obs_hole_blind

-- Invariants.Observation: the semantics-parametric carrier projection.
-- `Invariants.status` reads the grounded labelling off a `StructuredAF`; these
-- read an arbitrary `ExtensionSemantics` off the same carrier, and recover the
-- old function at `groundedSem` with no hypothesis.
#print axioms Lara.Invariants.observeSem_grounded
#print axioms Lara.Invariants.observeSem_gap
#print axioms Lara.Invariants.observeSem_of_status_gap

-- Context.Observation: the semantics layer — the observation at an
-- arbitrary `ExtensionSemantics`, its equivalence relation, the grounded
-- regression, and the four congruences. Each congruence is `obsGen_congr`
-- (pinned above, in the Context.Equivalence block) instantiated at one
-- projection; none needs an `AttackExtensional` hypothesis, because they
-- transport along the carrier equality `compileUnit_link_relabel` supplies.
#print axioms Lara.Context.obsSem_eq_of_ok
#print axioms Lara.Context.obsSem_incompatible
#print axioms Lara.Context.obsSem_rejected
#print axioms Lara.Context.liftObservation_inj
#print axioms Lara.Context.obsSem_grounded
#print axioms Lara.Context.ctxEquivSem_grounded_iff
#print axioms Lara.Context.backend_replacement_congruence_sem
#print axioms Lara.Context.registry_swap_congruence_sem
#print axioms Lara.Context.backend_replacement_congruence_composed_sem
#print axioms Lara.Context.whole_program_replacement_sem

-- ListRel: pointwise list relations. Core Lean 4.32.0 has no `List.Forall₂`;
-- this is the local replacement the relational development consumes.
#print axioms Lara.Forall₂.length_eq
#print axioms Lara.Forall₂.of_same
#print axioms Lara.Forall₂.of_map_right
#print axioms Lara.Forall₂.append
#print axioms Lara.Forall₂.getElem?_right
#print axioms Lara.Forall₂.getElem?_left
#print axioms Lara.Forall₂.getElem?_none
#print axioms Lara.Forall₂.mem_right
#print axioms Lara.Forall₂.mem_left
#print axioms Lara.Forall₂.filter

-- Context.Parametricity: the relational form of the M4 congruence.
-- `R` replaces the function `f`; `RelInj` is what the structural merge and the
-- coverage decider force on it, and `relInj_necessary` witnesses that.
#print axioms Lara.Context.relInj_necessary
#print axioms Lara.Context.relTerms_iff_forall₂
#print axioms Lara.Context.relTerms_length

-- Finite realization and unrestricted-extension counterexample.
#print axioms Lara.Context.swapAssurance_involutive
#print axioms Lara.Context.swapAssurance_injective
#print axioms Lara.Context.exists_total_injective_extension_on
#print axioms Lara.Context.relTerm_eq_mapAssur
#print axioms Lara.Context.relTerms_eq_mapAssurList
#print axioms Lara.Context.relDis_eq_mapAssurDis
#print axioms Lara.Context.relAtt_eq_mapAssurAtt
#print axioms Lara.Context.relAtts_eq_map
#print axioms Lara.Context.relFrag_eq_mapAssurFrag
#print axioms Lara.Context.relFrag_exists_injective
#print axioms Lara.Context.relFrag_exists_injective_fixesContext
#print axioms Lara.Context.shiftAssurance_injective
#print axioms Lara.Context.shiftAssurance_ne_zero
#print axioms Lara.Context.not_every_relInj_has_total_extension

#print axioms Lara.Context.relInj_functional
#print axioms Lara.Context.relInj_injective
#print axioms Lara.Context.relTerm_graphOf
#print axioms Lara.Context.relTerms_graphOf
#print axioms Lara.Context.relDis_graphOf
#print axioms Lara.Context.relAtt_graphOf
#print axioms Lara.Context.relFrag_graphOf
#print axioms Lara.Context.relInj_graphOf
#print axioms Lara.Context.relPreserving_graphOf
#print axioms Lara.Context.relFixesContext_graphOf
#print axioms Lara.Context.relTerm_inj
#print axioms Lara.Context.relTerms_inj
#print axioms Lara.Context.relDis_inj
#print axioms Lara.Context.relAtt_source_inj
#print axioms Lara.Context.relDis_length
#print axioms Lara.Context.relDis_keys
#print axioms Lara.Context.relTerms_getElem?_right
#print axioms Lara.Context.relTerms_getElem?_left
#print axioms Lara.Context.relDis_getElem?_right
#print axioms Lara.Context.relDis_lookup
#print axioms Lara.Context.relTerm_subterm
#print axioms Lara.Context.hasSupport_rel
#print axioms Lara.Context.hasAttack_rel
#print axioms Lara.Context.conflictAttackableB_rel
#print axioms Lara.Context.attackFor_rel
#print axioms Lara.Context.crossAttsFrom_inner_rel
#print axioms Lara.Context.crossAttsFrom_rel
#print axioms Lara.Context.conclusionCache_rel
#print axioms Lara.Context.crossAtts_rel
#print axioms Lara.Context.dedupList_rel
#print axioms Lara.Context.linkFault_rel
#print axioms Lara.Context.linkOk_rel
#print axioms Lara.Context.linkGamma_rel
#print axioms Lara.Context.linkGround_rel
#print axioms Lara.Context.link_rel_commutes
#print axioms Lara.Context.termWellSorted_rel
#print axioms Lara.Context.termsWellSorted_rel
#print axioms Lara.Context.dischargesWellSorted_rel
#print axioms Lara.Context.argsWellSorted_rel
#print axioms Lara.Context.signatureStage_rel
#print axioms Lara.Context.relAtt_source
#print axioms Lara.Context.relAtt_target
#print axioms Lara.Context.attackOcc_rel_exists
#print axioms Lara.Context.attackOcc_rel
#print axioms Lara.Context.contains_rel
#print axioms Lara.Context.covered_rel
#print axioms Lara.Context.conflictAttackable_rel
#print axioms Lara.Context.attackComplete_rel
#print axioms Lara.Context.nodup_rel
#print axioms Lara.Context.checkUnit_rel
#print axioms Lara.Context.checkUnit_rel_program
#print axioms Lara.Context.relTerms_getElem?_none
#print axioms Lara.Context.relDis_lookup_none
#print axioms Lara.Context.relTerm_subterm_none
#print axioms Lara.Context.containsB_rel
#print axioms Lara.Context.containsBList_rel
#print axioms Lara.Context.containsBDis_rel
#print axioms Lara.Context.attackClosureB_rel
#print axioms Lara.Context.coveredB_rel
#print axioms Lara.Context.nodes_conclusion_rel
#print axioms Lara.Context.compileUnit_rel
#print axioms Lara.Context.exists_accepted_rel
#print axioms Lara.Context.compileUnit_link_rel
#print axioms Lara.Context.obsGen_parametricity
#print axioms Lara.Context.backend_replacement_parametricity_sem
#print axioms Lara.Context.backend_replacement_parametricity
#print axioms Lara.Context.backend_replacement_congruence_of_parametricity
#print axioms Lara.Context.congruence_correspondence
#print axioms Lara.Context.occurs
#print axioms Lara.Context.occursList
#print axioms Lara.Context.occursDis
#print axioms Lara.Context.occursAtt
#print axioms Lara.Context.occurrences
#print axioms Lara.Context.mem_occursList
#print axioms Lara.Context.mem_occursAtts
#print axioms Lara.Context.relTerm_self
#print axioms Lara.Context.relTerms_self
#print axioms Lara.Context.relDis_self
#print axioms Lara.Context.relAtt_self
#print axioms Lara.Context.relInj_occRel
#print axioms Lara.Context.relFrag_occRel
#print axioms Lara.Context.relFixesContext_occRel
#print axioms Lara.Context.backend_replacement_parametricity_local
#print axioms Lara.Context.backend_replacement_parametricity_local_sem

-- A collapsing relation changes an accepted grounded observation.
#print axioms Lara.Examples.CertificateCollapse.replaySlot_eq
#print axioms Lara.Examples.CertificateCollapse.observations
#print axioms Lara.Examples.CertificateCollapse.preserving
#print axioms Lara.Examples.CertificateCollapse.not_relInj
#print axioms Lara.Examples.CertificateCollapse.related
#print axioms Lara.Examples.CertificateCollapse.fixes_context
#print axioms Lara.Examples.CertificateCollapse.source_support
#print axioms Lara.Examples.CertificateCollapse.source_sideOk
#print axioms Lara.Examples.CertificateCollapse.admissible
#print axioms Lara.Examples.CertificateCollapse.accepted
#print axioms Lara.Examples.CertificateCollapse.linked_shape
#print axioms Lara.Examples.CertificateCollapse.relInj_observationally_necessary

-- Examples.ContextSemantics: the semantics parameter is not an abstraction
-- over one instance at the context level either.
#print axioms Lara.Examples.ContextSemantics.cycle_sideOk_ctx
#print axioms Lara.Examples.ContextSemantics.cycle_sideOk_frag
#print axioms Lara.Examples.ContextSemantics.cycle_admissible
#print axioms Lara.Examples.ContextSemantics.cycle_link_ok
#print axioms Lara.Examples.ContextSemantics.cycle_accepted
#print axioms Lara.Examples.ContextSemantics.cycle_linked_shape
#print axioms Lara.Examples.ContextSemantics.obsSem_cycle_stable_ne_grounded
#print axioms Lara.Examples.ContextSemantics.sink_link_ok
#print axioms Lara.Examples.ContextSemantics.sink_accepted
#print axioms Lara.Examples.ContextSemantics.sink_linked_shape
#print axioms Lara.Examples.ContextSemantics.obsSem_sink_preferred_ne_grounded
#print axioms Lara.Examples.ContextSemantics.congruence_witness_sem
#print axioms Lara.Examples.ContextSemantics.registry_swap_witness_sem
#print axioms Lara.Examples.ContextSemantics.cert_congruence_witness_sem
#print axioms Lara.Examples.ContextSemantics.cert_registry_swap_witness_sem
#print axioms Lara.Examples.ContextSemantics.ctxEquivSem_negative
#print axioms Lara.Examples.ContextSemantics.ctxEquivSem_grounded_negative
#print axioms Lara.Examples.ContextSemantics.ctxEquivSem_grounded_of_ctxEquiv
#print axioms Lara.Examples.ContextSemantics.obsSem_linking_grounded
#print axioms Lara.Examples.ContextSemantics.obsSem_linking_agrees
#print axioms Lara.Examples.ContextSemantics.obsSem_sym_agrees
#print axioms Lara.Examples.ContextSemantics.obsSem_gap_uniform
#print axioms Lara.Examples.ContextSemantics.obsSem_incompatible_id_clash
#print axioms Lara.Examples.ContextSemantics.obsSem_rejected_signature

-- Context.Surface: the surface-transport corollary (F3)
#print axioms Lara.Context.checkedAF_map
#print axioms Lara.Context.surface_directAF_relabel
#print axioms Lara.Context.surface_directAF_link

-- Examples.Linking: executable witnesses (F1, F2)
#print axioms Lara.Examples.Linking.link_guard_ok
#print axioms Lara.Examples.Linking.link_guard_ok_quiet
#print axioms Lara.Examples.Linking.reject_duplicate_own_id
#print axioms Lara.Examples.Linking.reject_id_clash
#print axioms Lara.Examples.Linking.reject_unsatisfied_import
#print axioms Lara.Examples.Linking.reject_unsatisfied_context_import
#print axioms Lara.Examples.Linking.reject_sigma_mismatch
#print axioms Lara.Examples.Linking.reject_policy_mismatch
#print axioms Lara.Examples.Linking.link_rejected_of_fault
#print axioms Lara.Examples.Linking.obs_incompatible_id_clash
#print axioms Lara.Examples.Linking.malformed_link_guard_ok
#print axioms Lara.Examples.Linking.obs_rejected_signature
#print axioms Lara.Examples.Linking.crossAtts_nonempty
#print axioms Lara.Examples.Linking.linked_atts
#print axioms Lara.Examples.Linking.linked_args
#print axioms Lara.Examples.Linking.linked_accepted
#print axioms Lara.Examples.Linking.obs_defeated
#print axioms Lara.Examples.Linking.obs_justified
#print axioms Lara.Examples.Linking.obs_gap
#print axioms Lara.Examples.Linking.obs_gap_flipped
#print axioms Lara.Examples.Linking.merge_link_ok
#print axioms Lara.Examples.Linking.merge_fires
#print axioms Lara.Examples.Linking.merge_accepted
#print axioms Lara.Examples.Linking.merge_obs_unchanged
#print axioms Lara.Examples.Linking.compose_ok
#print axioms Lara.Examples.Linking.reject_compose_id_clash
#print axioms Lara.Examples.Linking.compose_rejected
#print axioms Lara.Examples.Linking.compose_declares_both
#print axioms Lara.Examples.Linking.compose_residual
#print axioms Lara.Examples.Linking.compose_links
#print axioms Lara.Examples.Linking.compose_obs
#print axioms Lara.Examples.Linking.strict_target_contrary_matches
#print axioms Lara.Examples.Linking.strict_target_not_attackable
#print axioms Lara.Examples.Linking.crossAttsFrom_skips_strict_target
#print axioms Lara.Examples.Linking.linkGamma_l2
#print axioms Lara.Examples.Linking.linkGamma_l1
#print axioms Lara.Examples.Linking.leaf2_checked
#print axioms Lara.Examples.Linking.leaf1_checked
#print axioms Lara.Examples.Linking.sideOk_ctx
#print axioms Lara.Examples.Linking.sideOk_frag
#print axioms Lara.Examples.Linking.admissible_split
#print axioms Lara.Examples.Linking.admissible_composite
#print axioms Lara.Examples.Linking.link_checked_split

-- Examples.LinkHoles: linking with located holes, and hole erasure observable (issue #13)
#print axioms Lara.Examples.LinkHoles.tMix_hole
#print axioms Lara.Examples.LinkHoles.holeFrag_sideOkHoles
#print axioms Lara.Examples.LinkHoles.holeFrag_not_sideOk
#print axioms Lara.Examples.LinkHoles.admissible_hole
#print axioms Lara.Examples.LinkHoles.link_checked_hole
#print axioms Lara.Examples.LinkHoles.link_hole_accepted
#print axioms Lara.Examples.LinkHoles.obs_holeFrag_eq
#print axioms Lara.Examples.LinkHoles.obs_holeFrag
#print axioms Lara.Examples.LinkHoles.erasure_keeps_complete_args
#print axioms Lara.Examples.LinkHoles.erasure_changes_live_attacks
#print axioms Lara.Examples.LinkHoles.hole_erasure_observable
#print axioms Lara.Examples.Linking.compose_triple_ok
#print axioms Lara.Examples.Linking.compose_triple_ok'
#print axioms Lara.Examples.Linking.compose_assoc_witness
#print axioms Lara.Examples.Linking.hostile_compose_ok
#print axioms Lara.Examples.Linking.hostile_composite_links
#print axioms Lara.Examples.Linking.hostile_left_admissible
#print axioms Lara.Examples.Linking.hostile_right_admissible
#print axioms Lara.Examples.Linking.hostile_composite_not_sideOk
#print axioms Lara.Examples.Linking.hostile_composite_not_admissible
#print axioms Lara.Examples.Linking.obs_contested
#print axioms Lara.Examples.Linking.obs_four_states
#print axioms Lara.Examples.Linking.ctxEquiv_negative
#print axioms Lara.Examples.Linking.obs_no_exports
#print axioms Lara.Examples.Linking.registryOnlyNd_ord
#print axioms Lara.Examples.Linking.registryOnlyNd_ne_registryEx
#print axioms Lara.Examples.Linking.certOk_onlyNd_le
#print axioms Lara.Examples.Linking.assurPreserving_onlyNd
#print axioms Lara.Examples.Linking.registry_swap_witness
#print axioms Lara.Examples.Linking.congruence_witness
#print axioms Lara.Examples.Linking.registryPlus_alias
#print axioms Lara.Examples.Linking.registryEx_alias
#print axioms Lara.Examples.Linking.registryPlus_ne_registryEx
#print axioms Lara.Examples.Linking.certOk_plus_le
#print axioms Lara.Examples.Linking.certOk_alias_of_nd
#print axioms Lara.Examples.Linking.certLinkOk
#print axioms Lara.Examples.Linking.certRuleLookup
#print axioms Lara.Examples.Linking.certLinkGamma_l1
#print axioms Lara.Examples.Linking.certArg_checked
#print axioms Lara.Examples.Linking.certArg_nd
#print axioms Lara.Examples.Linking.certLeaf_checked
#print axioms Lara.Examples.Linking.certSideOk_ctx
#print axioms Lara.Examples.Linking.certSideOk_frag
#print axioms Lara.Examples.Linking.certAdmissible
#print axioms Lara.Examples.Linking.cert_registry_swap_witness
#print axioms Lara.Examples.Linking.unwrap_wrap
#print axioms Lara.Examples.Linking.wrapCert_injective
#print axioms Lara.Examples.Linking.certUnswap_certSwap
#print axioms Lara.Examples.Linking.certSwap_injective
#print axioms Lara.Examples.Linking.certSwap_preserving
#print axioms Lara.Examples.Linking.cert_congruence_witness
#print axioms Lara.Examples.Linking.cert_relabel_moves_args
#print axioms Lara.Examples.Linking.cert_relabel_moves

-- ---------------------------------------------------------------------------
-- Ledger completion.
--
-- The sections above are organized by *result*: each groups the theorems one
-- spec result or plan task delivered. That organization left the modules
-- below with public theorems no section claimed, because no single result
-- owned them. `CLAUDE.md`'s rule is "every new theorem", not "every
-- headline theorem", so they are pinned here, grouped by module, and the CI
-- gate now runs `check-axcheck-coverage.py` over the whole `Lara/` tree
-- rather than a named file list — the gap was invisible precisely because
-- the gate's scope and the rule's scope had drifted apart.
--
-- 344 entries. Internal helpers that happen to be public
-- (`memberOf_iff`, `map_pair_eq_zip_map`, `findDuplicate_none_nodup`) are
-- pinned like everything else: making them `private` instead would be a
-- semantic change to the module interface, and would create a third,
-- undocumented visibility category. Absence from this ledger is meaningful
-- only for public declarations — `#print axioms` cannot reach a `private`
-- one from another module (`docs/examples-corpus-decision.md`).
-- ---------------------------------------------------------------------------

-- Lara/ND.lean (9).
-- Result 10, remainder: the ND reference adapter's grammar, typing, and
-- Boolean semantics beyond the headline soundness/exactness pair.
#print axioms Lara.ND.lookup_mem
#print axioms Lara.ND.lookup_lt
#print axioms Lara.ND.lookup_append_lt
#print axioms Lara.ND.lookup_append_ge
#print axioms Lara.ND.lookup_of_lt
#print axioms Lara.ND.lookup_none_of_ge
#print axioms Lara.ND.depProj_zero
#print axioms Lara.ND.depProj_append
#print axioms Lara.ND.depProj_succ_shiftDown

-- Lara/RA.lean (2).
-- `ra@1` rational arithmetic: the cross-multiplied comparison core the
-- relative-drop certificate is decided by.
#print axioms Lara.RA.decodeFrac_den_pos
#print axioms Lara.RA.dropEqWB_iff

-- Lara/Grounded.lean (22).
-- Results 5-7, remainder: the generic finite-AF grounded core — executable
-- evaluator, least-fixed-point judgment, four-state aggregation, and
-- conflict-freedom, all quantified over an arbitrary finite `AF`.
#print axioms Lara.Grounded.memB_iff
#print axioms Lara.Grounded.defendedB_iff
#print axioms Lara.Grounded.mem_step
#print axioms Lara.Grounded.step_subset_args
#print axioms Lara.Grounded.step_mono
#print axioms Lara.Grounded.iter_subset_args
#print axioms Lara.Grounded.iter_mono
#print axioms Lara.Grounded.directOut_iff
#print axioms Lara.Grounded.directIn_mem_args
#print axioms Lara.Grounded.iter_directIn
#print axioms Lara.Grounded.filter_length_le
#print axioms Lara.Grounded.filter_length_lt
#print axioms Lara.Grounded.stable_succ
#print axioms Lara.Grounded.stable_add
#print axioms Lara.Grounded.deficit_lt
#print axioms Lara.Grounded.deficit_iter_zero
#print axioms Lara.Grounded.deficit_bound
#print axioms Lara.Grounded.directIn_sound
#print axioms Lara.Grounded.directOut_sound
#print axioms Lara.Grounded.directOut_iff_bex
#print axioms Lara.Grounded.attackedByIn_iff
#print axioms Lara.Grounded.labelC_spec

-- Lara/Blocked.lean (7).
-- Spec 4.3 conservative reporting: the quarantine deficit bounds
-- that keep missing evidence from making a claim look stronger.
#print axioms Lara.Blocked.any_congr
#print axioms Lara.Blocked.closureIter_subset_args
#print axioms Lara.Blocked.closureIter_mono
#print axioms Lara.Blocked.cstable_succ
#print axioms Lara.Blocked.cstable_add
#print axioms Lara.Blocked.cdeficit_lt
#print axioms Lara.Blocked.cdeficit_bound

-- Lara/RawAttack.lean (3).
-- Raw attack identity, remainder: endpoint-safe filtering must go through the
-- declared argument ids, never the resolved support terms.
#print axioms Lara.RawAttack.resolveAttacks_rebut
#print axioms Lara.RawAttack.resolveAttacks_undercut
#print axioms Lara.RawAttack.resolveAttacks_undermine

-- Lara/Policy.lean (2).
-- Executable policy well-formedness: the 8.1-frozen Path-B restriction.
#print axioms Lara.Policy.patMayOverlap_of_instances
#print axioms Lara.Policy.patsMayOverlap_of_instances

-- Lara/Erase.lean (6).
-- Result 9 (Theorem 2, Model A), remainder: the uniform injective certificate
-- relabel and the identity node bijection it induces on the compiled AF.
#print axioms Lara.Erase.mapAssurList_eq
#print axioms Lara.Erase.mapAssur_inj
#print axioms Lara.Erase.mapAssurList_inj
#print axioms Lara.Erase.mapAssurDis_inj
#print axioms Lara.Erase.containsBList_mapAssur
#print axioms Lara.Erase.containsBDis_mapAssur

-- Lara/EraseTransport.lean (5).
-- Result 9, well-checkedness transport: `mapCertProg` exhibits the second
-- `CheckedProgram`, so `backend_replacement` is non-vacuous by construction.
#print axioms Lara.Erase.mapAssurList_length
#print axioms Lara.Erase.mapAssurDis_length
#print axioms Lara.Erase.mapAssurDis_keys
#print axioms Lara.Erase.mapAssurList_getElem?_some
#print axioms Lara.Erase.mapAssurDis_getElem?_some

-- Lara/Surface/Syntax.lean (69).
-- M5 surface calculus: the presentation AST's own laws.
#print axioms Lara.Surface.cellObligationB_iff
#print axioms Lara.Surface.comparisonExpansion?_sound
#print axioms Lara.Surface.comparisonExpansion?_complete
#print axioms Lara.Surface.propTextWellFormedB_iff
#print axioms Lara.Surface.policyMatchesB_iff
#print axioms Lara.Surface.RenamingSound.toComparison
#print axioms Lara.Surface.Renaming.programValues_renameProgram
#print axioms Lara.Surface.Renaming.valueNames_renameProgram
#print axioms Lara.Surface.Renaming.leafIds_renameProgram
#print axioms Lara.Surface.Renaming.argIds_renameProgram
#print axioms Lara.Surface.Renaming.claimIds_renameProgram
#print axioms Lara.Surface.Renaming.statusIds_renameProgram
#print axioms Lara.Surface.Renaming.groupDecls_renameProgram
#print axioms Lara.Surface.Renaming.ruleIds_renamePolicy
#print axioms Lara.Surface.Renaming.premiseLabels_renameRule
#print axioms Lara.Surface.Renaming.questionIds_renameRule
#print axioms Lara.Surface.Renaming.comparisonDecls_renameProgram
#print axioms Lara.Surface.Renaming.declaredLeaves_renameProgram
#print axioms Lara.Surface.Renaming.atomFixed_of_decl
#print axioms Lara.Surface.Renaming.lookupSurfaceSubst_rename
#print axioms Lara.Surface.Renaming.substituteValueTerm_rename
#print axioms Lara.Surface.Renaming.substituteValueTerms_rename
#print axioms Lara.Surface.Renaming.substituteValueAtom_rename
#print axioms Lara.Surface.Renaming.parseNl_renameNl
#print axioms Lara.Surface.Renaming.nodup_map_iff_of_injective
#print axioms Lara.Surface.Renaming.valueBindingsWellFormedB_rename
#print axioms Lara.Surface.Renaming.ruleById_rename
#print axioms Lara.Surface.Renaming.comparisonExpansion?_rename
#print axioms Lara.Surface.Renaming.comparisonsWellFormedB_rename
#print axioms Lara.Surface.Renaming.priorPayloadsFromProgram_nil
#print axioms Lara.Surface.Renaming.priorPayloadsFromProgram_append_one
#print axioms Lara.Surface.Renaming.renameResidualTerm_eq_iff
#print axioms Lara.Surface.Renaming.renameResidualTerms_eq_iff
#print axioms Lara.Surface.Renaming.instantiateSurfaceAtom_renameResidual
#print axioms Lara.Surface.Renaming.renameResidualAtom_eq_renameValueAtom
#print axioms Lara.Surface.Renaming.renameResidualSupportTerm_eq_renameSupportTerm
#print axioms Lara.Surface.Renaming.supportTermFixed_of_explicitArg
#print axioms Lara.Surface.Renaming.declaredLeaves_renameResidual
#print axioms Lara.Surface.Renaming.premisePatternFixed
#print axioms Lara.Surface.Renaming.conclusionPatternFixed
#print axioms Lara.Surface.Renaming.conclOfTerm_rename
#print axioms Lara.Surface.Renaming.resolveReference_rename
#print axioms Lara.Surface.Renaming.buildArgument_rename
#print axioms Lara.Surface.Renaming.comparisonExpansionData_fixed
#print axioms Lara.Surface.Renaming.argumentPayloadsFromProgram
#print axioms Lara.Surface.Renaming.resolveReference_preserves_priorPayloads
#print axioms Lara.Surface.Renaming.buildArgument_preserves_priorPayloads
#print axioms Lara.Surface.Renaming.buildProgramArguments_rename
#print axioms Lara.Surface.Renaming.inferredArgsWellFormedB_rename
#print axioms Lara.Surface.Renaming.supportTermsToList_rename
#print axioms Lara.Surface.Renaming.renameResidualSupportTerm_eq_iff
#print axioms Lara.Surface.Renaming.labelIndex?_rename
#print axioms Lara.Surface.Renaming.certificateResolver_rename
#print axioms Lara.Surface.Renaming.hasSymbolicRef_renameCertPayload
#print axioms Lara.Surface.Renaming.lowerPayload_sx_resolver_fixed
#print axioms Lara.Surface.Renaming.opaqueDefault_node_children_contained
#print axioms Lara.Surface.Renaming.lowerPayload_isSome_renameCertPayload
#print axioms Lara.Surface.Renaming.namedCertificatesWellFormedB_rename
#print axioms Lara.Surface.Renaming.collectProgramArguments_rename
#print axioms Lara.Surface.Renaming.questionByName?_rename
#print axioms Lara.Surface.Renaming.surfaceAttacksWellFormedB_rename
#print axioms Lara.Surface.Renaming.policyMatchesB_rename
#print axioms Lara.Surface.Renaming.declarationIdsNodupB_rename
#print axioms Lara.Surface.Renaming.ruleNamespacesWellFormedB_rename
#print axioms Lara.Surface.Renaming.canonicalPremiseLabelsB_rename
#print axioms Lara.Surface.Renaming.statusesWellFormedB_rename
#print axioms Lara.Surface.Renaming.groupsWellFormedB_rename
#print axioms Lara.Surface.Renaming.supportedB_rename
#print axioms Lara.Surface.Binding.supported_sourceOnly_rename_iff

-- Lara/Surface/Binding.lean (103).
-- M5 surface calculus: binding and typed-renaming laws. The largest single
-- block — `GlobalRenaming` proves one transport lemma per syntactic category,
-- and each is a theorem the ledger owes an entry.
#print axioms Lara.Surface.Binding.substPat_compose_of_fresh
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_prop
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_question
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_leaf
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_rule
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_arg
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_argRef
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_obligation
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_source
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_group
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_measurand
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_dataset
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_premiseLabel
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_valueName
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_valueName_fun
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_prop_fun
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_question_fun
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_leaf_fun
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_rule_fun
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_arg_fun
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_argRef_fun
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_obligation_fun
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_group_fun
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_measurand_fun
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_dataset_fun
#print axioms Lara.Surface.Binding.GlobalRenaming.sourceOnly_premiseLabel_fun
#print axioms Lara.Surface.Binding.GlobalRenaming.injective
#print axioms Lara.Surface.Binding.id_prop
#print axioms Lara.Surface.Binding.id_question
#print axioms Lara.Surface.Binding.id_leaf
#print axioms Lara.Surface.Binding.id_rule
#print axioms Lara.Surface.Binding.id_arg
#print axioms Lara.Surface.Binding.id_argRef
#print axioms Lara.Surface.Binding.id_obligation
#print axioms Lara.Surface.Binding.id_source
#print axioms Lara.Surface.Binding.id_group
#print axioms Lara.Surface.Binding.id_measurand
#print axioms Lara.Surface.Binding.id_dataset
#print axioms Lara.Surface.Binding.id_premiseLabel
#print axioms Lara.Surface.Binding.id_valueName
#print axioms Lara.Surface.Binding.comp_prop
#print axioms Lara.Surface.Binding.comp_question
#print axioms Lara.Surface.Binding.comp_leaf
#print axioms Lara.Surface.Binding.comp_rule
#print axioms Lara.Surface.Binding.comp_arg
#print axioms Lara.Surface.Binding.comp_argRef
#print axioms Lara.Surface.Binding.comp_obligation
#print axioms Lara.Surface.Binding.comp_source
#print axioms Lara.Surface.Binding.comp_group
#print axioms Lara.Surface.Binding.comp_measurand
#print axioms Lara.Surface.Binding.comp_dataset
#print axioms Lara.Surface.Binding.comp_premiseLabel
#print axioms Lara.Surface.Binding.comp_valueName
#print axioms Lara.Surface.Binding.id_prop_fun
#print axioms Lara.Surface.Binding.id_question_fun
#print axioms Lara.Surface.Binding.id_leaf_fun
#print axioms Lara.Surface.Binding.id_rule_fun
#print axioms Lara.Surface.Binding.id_arg_fun
#print axioms Lara.Surface.Binding.id_argRef_fun
#print axioms Lara.Surface.Binding.id_obligation_fun
#print axioms Lara.Surface.Binding.id_source_fun
#print axioms Lara.Surface.Binding.id_group_fun
#print axioms Lara.Surface.Binding.id_measurand_fun
#print axioms Lara.Surface.Binding.id_dataset_fun
#print axioms Lara.Surface.Binding.id_premiseLabel_fun
#print axioms Lara.Surface.Binding.id_valueName_fun
#print axioms Lara.Surface.Binding.comp_prop_fun
#print axioms Lara.Surface.Binding.comp_question_fun
#print axioms Lara.Surface.Binding.comp_leaf_fun
#print axioms Lara.Surface.Binding.comp_rule_fun
#print axioms Lara.Surface.Binding.comp_arg_fun
#print axioms Lara.Surface.Binding.comp_argRef_fun
#print axioms Lara.Surface.Binding.comp_obligation_fun
#print axioms Lara.Surface.Binding.comp_source_fun
#print axioms Lara.Surface.Binding.comp_group_fun
#print axioms Lara.Surface.Binding.comp_measurand_fun
#print axioms Lara.Surface.Binding.comp_dataset_fun
#print axioms Lara.Surface.Binding.comp_premiseLabel_fun
#print axioms Lara.Surface.Binding.comp_valueName_fun
#print axioms Lara.Surface.Binding.renameText_id
#print axioms Lara.Surface.Binding.renameText_comp
#print axioms Lara.Surface.Binding.renameText_injective
#print axioms Lara.Surface.Binding.rename_question_val
#print axioms Lara.Surface.Binding.rename_leaf_val
#print axioms Lara.Surface.Binding.rename_rule_val
#print axioms Lara.Surface.Binding.rename_arg_val
#print axioms Lara.Surface.Binding.rename_argRef_val
#print axioms Lara.Surface.Binding.rename_obligation_val
#print axioms Lara.Surface.Binding.rename_group_val
#print axioms Lara.Surface.Binding.rename_measurand_val
#print axioms Lara.Surface.Binding.rename_dataset_val
#print axioms Lara.Surface.Binding.rename_premiseLabel_val
#print axioms Lara.Surface.Binding.rename_valueName_val
#print axioms Lara.Surface.Binding.renameSourceRefsProgram_eq_of_fixed
#print axioms Lara.Surface.Binding.renameSupportTerm_id
#print axioms Lara.Surface.Binding.renameSupportTerms_id
#print axioms Lara.Surface.Binding.renameDischarges_id
#print axioms Lara.Surface.Binding.renameProgram_id
#print axioms Lara.Surface.Binding.renameProgram_comp
#print axioms Lara.Surface.Binding.renamePolicy_id
#print axioms Lara.Surface.Binding.renamePolicy_comp
#print axioms Lara.Surface.Binding.renameProgram_sourceOnly
#print axioms Lara.Surface.Binding.renamePolicy_sourceOnly

-- Lara/Surface/ValueBinding.lean (11).
-- M5 surface calculus: value expansion — soundness, completeness over the
-- reviewed well-formed fragment, idempotence, and declaration-id stability.
#print axioms Lara.Surface.Renaming.duplicateName?_rename
#print axioms Lara.Surface.Renaming.valueBindingErrors_rename
#print axioms Lara.Surface.Renaming.valueBindingErrors_some_cases
#print axioms Lara.Surface.Renaming.expandNl_rename_related
#print axioms Lara.Surface.Renaming.substitutedDecls_rename
#print axioms Lara.Surface.bind_ok_reduce
#print axioms Lara.Surface.expandValues_eq_of_none_checks
#print axioms Lara.Surface.expandValues_preserves_decl_ids
#print axioms Lara.Surface.expandValues_fixed_point
#print axioms Lara.Surface.Renaming.termNullaryCons_of_sortOf_some
#print axioms Lara.Surface.expandValues_idempotent

-- Lara/Surface/Comparison.lean (11).
-- M5 surface calculus: comparison-block expansion into the generated
-- sub-claim, strict recheck argument, and defeasible bridge.
#print axioms Lara.Surface.generatedIdsFresh_of_ids_nodup
#print axioms Lara.Surface.duplicateComparisonClaim?_eq_none_iff
#print axioms Lara.Surface.expandComparisons_preserves_order
#print axioms Lara.Surface.expandComparisons_generated_ids
#print axioms Lara.Surface.expandComparisons_eliminates
#print axioms Lara.Surface.Renaming.generatedIdCollisionClaim?_rename
#print axioms Lara.Surface.Renaming.duplicateComparisonClaim?_rename
#print axioms Lara.Surface.Renaming.generatedDecls_eraseNl
#print axioms Lara.Surface.Renaming.generatedDecls_rename
#print axioms Lara.Surface.Renaming.generatedDecls_reconstruction_safe
#print axioms Lara.Surface.Renaming.generatedArgs_rename

-- Lara/Surface/Check.lean (71).
-- M5 Task 4: the independent syntax-directed surface judgment, and the
-- sound/complete pairs relating it to the executable checker.
#print axioms Lara.Surface.exceptIsOk_iff
#print axioms Lara.Surface.findDuplicate_none_nodup
#print axioms Lara.Surface.findDuplicate_none_of_nodup
#print axioms Lara.Surface.memberOf_iff
#print axioms Lara.Surface.map_pair_eq_zip_map
#print axioms Lara.Surface.findsRule_sound
#print axioms Lara.Surface.findsRule_complete
#print axioms Lara.Surface.ruleById_sound
#print axioms Lara.Surface.ruleById_complete
#print axioms Lara.Surface.resolveReference_sound
#print axioms Lara.Surface.resolveReference_complete
#print axioms Lara.Surface.resolveReferences_sound
#print axioms Lara.Surface.resolveReferences_complete
#print axioms Lara.Surface.matchResolvedPremises_sound
#print axioms Lara.Surface.matchResolvedPremises_complete
#print axioms Lara.Surface.paramsCoveredB_iff
#print axioms Lara.Surface.resolveNamedDischarges_sound
#print axioms Lara.Surface.resolveNamedDischarges_complete
#print axioms Lara.Surface.resolveImplicitPremises_sound
#print axioms Lara.Surface.resolveImplicitPremises_complete
#print axioms Lara.Surface.reconstructExplicitTerm_sound
#print axioms Lara.Surface.reconstructExplicitTerms_sound
#print axioms Lara.Surface.reconstructExplicitDischarges_sound
#print axioms Lara.Surface.reconstructExplicitTerm_complete
#print axioms Lara.Surface.reconstructExplicitTerms_complete
#print axioms Lara.Surface.reconstructExplicitDischarges_complete
#print axioms Lara.Surface.conclOfTerm_sound
#print axioms Lara.Surface.conclOfTerm_complete
#print axioms Lara.Surface.checksAssurance_complete
#print axioms Lara.Surface.lowerToSupportTerm_sound
#print axioms Lara.Surface.lowerToSupportTerms_sound
#print axioms Lara.Surface.lowerToSupportDischarges_sound
#print axioms Lara.Surface.lowerToSupportTerm_complete
#print axioms Lara.Surface.lowerToSupportTerms_complete
#print axioms Lara.Surface.lowerToSupportDischarges_complete
#print axioms Lara.Surface.reconstructArgument_conclusion_sound
#print axioms Lara.Surface.reconstructArgument_sound
#print axioms Lara.Surface.reconstructArgument_complete
#print axioms Lara.Surface.reconstructArgs_sound
#print axioms Lara.Surface.reconstructArgs_complete
#print axioms Lara.Surface.resolvePathCore_sound
#print axioms Lara.Surface.resolvePathCore_complete
#print axioms Lara.Surface.resolveSurfaceAttack_sound
#print axioms Lara.Surface.resolveSurfaceAttack_complete
#print axioms Lara.Surface.resolveSurfaceAttacks_sound
#print axioms Lara.Surface.resolveSurfaceAttacks_complete
#print axioms Lara.Surface.expandDecls_complete_independent
#print axioms Lara.Surface.expandComparisons_complete_independent
#print axioms Lara.Surface.expandComparisons_guards
#print axioms Lara.Surface.AttackEndpointsDeclared.of_surfaceAttacksWellFormed
#print axioms Lara.Surface.assembleGuards_ok
#print axioms Lara.Surface.firstRejectedLeaf_none_of_admission
#print axioms Lara.Surface.assembleGuards_complete
#print axioms Lara.Surface.CoreObligations.signatureStage_none
#print axioms Lara.Surface.semanticIdentifierChecks_complete
#print axioms Lara.Surface.assemble_sound
#print axioms Lara.Surface.assemble_complete
#print axioms Lara.Surface.check_eq_of_assemble
#print axioms Lara.Surface.Renaming.sxToSExpr_renameCertPayload
#print axioms Lara.Surface.Renaming.lowerAssuranceCertificate_rename
#print axioms Lara.Surface.Renaming.lowerToSupportTerm_rename
#print axioms Lara.Surface.Renaming.lowerToSupportTerms_rename
#print axioms Lara.Surface.Renaming.lowerToSupportDischarges_rename
#print axioms Lara.Surface.Renaming.premiseMatches_rename
#print axioms Lara.Surface.Renaming.reconstructExplicitTerm_rename
#print axioms Lara.Surface.Renaming.reconstructExplicitTerms_rename
#print axioms Lara.Surface.Renaming.reconstructExplicitDischarges_rename
#print axioms Lara.Surface.Renaming.reconstructArgument_rename
#print axioms Lara.Surface.Renaming.reconstructArgs_rename
#print axioms Lara.Surface.Renaming.resolvePathCore_rename
#print axioms Lara.Surface.Renaming.resolveSurfaceAttacks_rename

-- Lara/Surface/Elaborate.lean (5).
-- M5 Task 5: production-ordered pure presentation elaboration.
#print axioms Lara.Surface.checksAttacks_raw_alignment
#print axioms Lara.Surface.checksAttacks_raw_selection_alignment
#print axioms Lara.Surface.Renaming.rawResolveAttacks_rename
#print axioms Lara.Surface.Renaming.resolveAligned_rename
#print axioms Lara.Surface.Renaming.validateAttackEndpoints_rename

-- Lara/Surface/Correctness.lean (9).
-- M5 surface calculus: the core-visible correctness statements over the
-- elaborated unit.
#print axioms Lara.Surface.Renaming.expandValues_rename_related
#print axioms Lara.Surface.Renaming.expandComparisons_semantic_related
#print axioms Lara.Surface.Renaming.expandValuesThenComparisons_rename_related
#print axioms Lara.Surface.Renaming.evaluateAdmission_rename
#print axioms Lara.Surface.Renaming.RenamingSound.coreSigma
#print axioms Lara.Surface.Renaming.hasSupport_rename_iff
#print axioms Lara.Surface.Renaming.hasAttack_rename_iff
#print axioms Lara.Surface.Renaming.attackComplete_rename_iff
#print axioms Lara.Surface.Renaming.reconstructExpandedArgs_rename

-- Lara/Examples/Realizability.lean (4).
-- M1 counterexample corpus: the frozen two-field compiler invariant is
-- necessary but not sufficient for realizability. A separation result, so it
-- has no cross-language differential counterpart
-- (`docs/examples-corpus-decision.md`).
#print axioms Lara.Examples.Realizability.swapFirstTwo_involutive
#print axioms Lara.Examples.Realizability.nonempty_ground_covers
#print axioms Lara.Examples.Realizability.nonempty_accepted_nodes
#print axioms Lara.Examples.Realizability.nonemptyRetainedNode_mem

-- Lara/Examples/Complexity/Realization.lean (5).
-- M2b Task-2 restricted-class realization spike. Until ledger completion this module
-- was an orphan: nothing imported it, so `lake build` never elaborated it and
-- its theorems were unchecked. `Lara.lean` now imports it, which is what puts
-- it in the build and in reach of `#print axioms`.
#print axioms Lara.Examples.Complexity.Realization.checkUnit_path_ok
#print axioms Lara.Examples.Complexity.Realization.checkUnit_cycle_ok
#print axioms Lara.Examples.Complexity.Realization.checkUnit_reversedPath_rejected
#print axioms Lara.Examples.Complexity.Realization.rawUnitOfFormula_shape
#print axioms Lara.Examples.Complexity.Realization.rawUnitOfFormula_fixedFields

/-! ### PW-T8 — executable StatusBridge checker -/

-- Deciders are definitions (audited transitively through their theorems).
#print axioms Lara.PW.corrB_iff
#print axioms Lara.PW.transportsB_iff
#print axioms Lara.PW.admitsB_iff
#print axioms Lara.PW.matchedB_iff
#print axioms Lara.PW.corrB_lt
#print axioms Lara.PW.bisimScanB_sound
#print axioms Lara.PW.bisimScanB_complete
#print axioms Lara.PW.forthB_sound
#print axioms Lara.PW.forthB_complete
#print axioms Lara.PW.backB_sound
#print axioms Lara.PW.backB_complete
#print axioms Lara.PW.statusBridgeB_sound
#print axioms Lara.PW.statusBridgeB_complete
#print axioms Lara.PW.statusBridgeB_iff

-- Conformance cells.
#print axioms Lara.Examples.PW.StatusCheck.s1_r1_decider
#print axioms Lara.Examples.PW.StatusCheck.s2_r2_decider
#print axioms Lara.Examples.PW.StatusCheck.s3_r3_decider
#print axioms Lara.Examples.PW.StatusCheck.s2_r2_statusBridge_via_decider
#print axioms Lara.Examples.PW.StatusCheck.t7_decider_rejects
#print axioms Lara.Examples.PW.StatusCheck.t7_not_statusBridge_via_decider

-- T7, clause by clause.
#print axioms Lara.Examples.PW.StatusCheck.t7_matchedB_false
#print axioms Lara.Examples.PW.StatusCheck.t7_admits_forth_hold
#print axioms Lara.Examples.PW.StatusCheck.t7_backB_false

-- Isolating negatives for the admits/matched conjuncts (eng review, 6A).
#print axioms Lara.Examples.PW.StatusCheck.s2_r1_admits_fails
#print axioms Lara.Examples.PW.StatusCheck.s2_r1_matched_holds
#print axioms Lara.Examples.PW.StatusCheck.s1_r2_matched_fails
#print axioms Lara.Examples.PW.StatusCheck.s1_r2_admits_holds

-- Isolating negatives for the directed scans.
#print axioms Lara.Examples.PW.StatusCheck.forthB_discriminates
#print axioms Lara.Examples.PW.StatusCheck.backB_discriminates

/-! ### PW-T8 — declared-attack transport -/

-- Definitions `trAttack`, `trAttackList`, and the `AttackBridge` structure
-- are audited transitively through the theorems below.
#print axioms Lara.PW.trAttackList_cons
#print axioms Lara.PW.trSupport_leaf
#print axioms Lara.PW.trSupport_inst_inv
#print axioms Lara.PW.trSubst_inj
#print axioms Lara.PW.trSupport_inj
#print axioms Lara.PW.trSupportList_inj
#print axioms Lara.PW.trSupportDis_inj
#print axioms Lara.PW.trSupport_eq_iff
#print axioms Lara.PW.lookupDis_mem
#print axioms Lara.PW.lookupDis_trSupportDis
#print axioms Lara.PW.trSupportList_some_of_mem
#print axioms Lara.PW.trSupportDis_some_of_mem
#print axioms Lara.PW.trSupport_subterm
#print axioms Lara.PW.trSupport_subterm_some
#print axioms Lara.PW.containsB_trSupport
#print axioms Lara.PW.containsBList_trSupport
#print axioms Lara.PW.containsBDis_trSupport
#print axioms Lara.PW.trAttack_source
#print axioms Lara.PW.attackClosureB_trAttack
#print axioms Lara.PW.coveredB_trAttack
#print axioms Lara.PW.Contains_trSupport
#print axioms Lara.PW.AttackOcc_trSupport
#print axioms Lara.PW.AttackBridge.toStatusBridge

-- Conformance cells: the S2/R2 AttackBridge, both negatives (eng review 2A),
-- and the ques-position witness (eng review 7A).
#print axioms Lara.Examples.PW.Attack.leafMapR_injective
#print axioms Lara.Examples.PW.Attack.s2_r2_atts_transported
#print axioms Lara.Examples.PW.Attack.s2_r2_attackBridge
#print axioms Lara.Examples.PW.Attack.s2_r2_statusBridge_via_attacks
#print axioms Lara.Examples.PW.Attack.gap_attack_undefined
#print axioms Lara.Examples.PW.Attack.collapsed_containsB_breaks
#print axioms Lara.Examples.PW.Attack.ques_position_computes
#print axioms Lara.Examples.PW.Attack.ques_position_law

/-! ### The surface transport fixture

The certificate-lowering foundation for a `native_decide`-free instance of
`Lara.Context.surface_directAF_relabel`. These are the only obligations that sit
on the kernel-opaque `NDNamed.lowerNamed` path, so they are the ones whose axiom
footprint matters: if any of them silently acquired `Lean.ofReduceBool`, the
fixture would be worthless. -/
#print axioms Lara.Examples.SurfaceTransport.kernelRef_eq_slot1
#print axioms Lara.Examples.SurfaceTransport.sxToSExpr_kernelPayload
#print axioms Lara.Examples.SurfaceTransport.transport_lower_kernel
#print axioms Lara.Examples.SurfaceTransport.firstNamedMarker_wrappedPayload
#print axioms Lara.Examples.SurfaceTransport.transport_lower_wrapped
#print axioms Lara.Examples.SurfaceTransport.transport_relabel_moves_cert
#print axioms Lara.Examples.SurfaceTransport.transport_payloads_differ
#print axioms Lara.Examples.SurfaceTransport.transport_certSwap_image
#print axioms Lara.Examples.SurfaceTransport.theoryDigestA_lowers
#print axioms Lara.Examples.SurfaceTransport.transport_cert_accepted
#print axioms Lara.Examples.SurfaceTransport.transport_cert_accepted_wrapped
#print axioms Lara.Examples.SurfaceTransport.transport_supported
#print axioms Lara.Examples.SurfaceTransport.transport_supported_wrapped
#print axioms Lara.Examples.SurfaceTransport.transport_freshness
#print axioms Lara.Examples.SurfaceTransport.transport_freshness_wrapped
#print axioms Lara.Examples.SurfaceTransport.transport_checksArgument
#print axioms Lara.Examples.SurfaceTransport.transport_checksProgram_kernel
#print axioms Lara.Examples.SurfaceTransport.transport_checksProgram_wrapped
#print axioms Lara.Examples.SurfaceTransport.transport_expansions
#print axioms Lara.Examples.SurfaceTransport.transport_gamma_leafP
#print axioms Lara.Examples.SurfaceTransport.transport_ruleLookup
#print axioms Lara.Examples.SurfaceTransport.transport_hasSupport
#print axioms Lara.Examples.SurfaceTransport.transport_cert_accepted_wrapped_raw
#print axioms Lara.Examples.SurfaceTransport.transport_args_kernel
#print axioms Lara.Examples.SurfaceTransport.transport_args_wrapped
#print axioms Lara.Examples.SurfaceTransport.transport_complete_kernel
#print axioms Lara.Examples.SurfaceTransport.transport_complete_wrapped
#print axioms Lara.Examples.SurfaceTransport.transport_coreObligations_kernel
#print axioms Lara.Examples.SurfaceTransport.transport_coreObligations_wrapped
#print axioms Lara.Examples.SurfaceTransport.transport_checks_kernel
#print axioms Lara.Examples.SurfaceTransport.transport_checks_wrapped
#print axioms Lara.Examples.SurfaceTransport.transport_checkUnit_kernel
#print axioms Lara.Examples.SurfaceTransport.transport_checkUnit_wrapped
#print axioms Lara.Examples.SurfaceTransport.surfaceTransport_directAF_eq
#print axioms Lara.Examples.SurfaceTransport.surfaceTransport_relabel_moves
#print axioms Lara.Examples.SurfaceTransport.surfaceTransport_inputs_differ
#print axioms Lara.Examples.SurfaceTransport.transportCorePolicy_ruleLookup
#print axioms Lara.Examples.SurfaceTransport.transport_hasSupport_of_gamma
#print axioms Lara.Examples.SurfaceTransport.crossAtts_of_ctx_args_nil
#print axioms Lara.Examples.SurfaceTransport.linkedUnit_of_empty_ctx
#print axioms Lara.Examples.SurfaceTransport.linkFrag_relabel
#print axioms Lara.Examples.SurfaceTransport.linkGamma_leafP
#print axioms Lara.Examples.SurfaceTransport.transport_unit_is_link
#print axioms Lara.Examples.SurfaceTransport.transport_unit_wrapped_is_link
#print axioms Lara.Examples.SurfaceTransport.linkSideOk_ctx
#print axioms Lara.Examples.SurfaceTransport.linkSideOk_frag
#print axioms Lara.Examples.SurfaceTransport.transportLink_admissible
#print axioms Lara.Examples.SurfaceTransport.surfaceTransport_link_directAF_eq
#print axioms Lara.Examples.SurfaceTransport.surfaceTransport_link_relabel_moves_args
#print axioms Lara.Examples.SurfaceTransport.surfaceTransport_link_relabel_moves
#print axioms Lara.Examples.SurfaceTransport.surfaceTransport_link_imports_nonempty

/-! ### The attack-bearing surface transport witness -/

#print axioms Lara.Examples.SurfaceTransportAttack.attack_supported
#print axioms Lara.Examples.SurfaceTransportAttack.attack_supported_wrapped
#print axioms Lara.Examples.SurfaceTransportAttack.attack_freshness
#print axioms Lara.Examples.SurfaceTransportAttack.attack_freshness_wrapped
#print axioms Lara.Examples.SurfaceTransportAttack.attack_checksArgument_cert
#print axioms Lara.Examples.SurfaceTransportAttack.attack_checksCertificate_cert
#print axioms Lara.Examples.SurfaceTransportAttack.attack_checksArgument_s
#print axioms Lara.Examples.SurfaceTransportAttack.attack_checksArgument_t
#print axioms Lara.Examples.SurfaceTransportAttack.attack_checksProgram_kernel
#print axioms Lara.Examples.SurfaceTransportAttack.attack_checksProgram_wrapped
#print axioms Lara.Examples.SurfaceTransportAttack.attack_checksAttacks
#print axioms Lara.Examples.SurfaceTransportAttack.attack_expansions
#print axioms Lara.Examples.SurfaceTransportAttack.attack_gamma_leafP
#print axioms Lara.Examples.SurfaceTransportAttack.attack_ruleLookup_cert
#print axioms Lara.Examples.SurfaceTransportAttack.attack_ruleLookup_s
#print axioms Lara.Examples.SurfaceTransportAttack.attack_ruleLookup_t
#print axioms Lara.Examples.SurfaceTransportAttack.attack_hasSupport_cert
#print axioms Lara.Examples.SurfaceTransportAttack.attack_hasSupport_plain
#print axioms Lara.Examples.SurfaceTransportAttack.attack_concl_of_inst
#print axioms Lara.Examples.SurfaceTransportAttack.attack_args
#print axioms Lara.Examples.SurfaceTransportAttack.attack_atts
#print axioms Lara.Examples.SurfaceTransportAttack.attack_contraries
#print axioms Lara.Examples.SurfaceTransportAttack.attack_strictConclusions
#print axioms Lara.Examples.SurfaceTransportAttack.attack_contraryMatch
#print axioms Lara.Examples.SurfaceTransportAttack.attack_s_ne_t
#print axioms Lara.Examples.SurfaceTransportAttack.attack_s_ne_q
#print axioms Lara.Examples.SurfaceTransportAttack.attack_concl_cert
#print axioms Lara.Examples.SurfaceTransportAttack.attack_concl_s
#print axioms Lara.Examples.SurfaceTransportAttack.attack_concl_t
#print axioms Lara.Examples.SurfaceTransportAttack.attack_cert_not_attackable
#print axioms Lara.Examples.SurfaceTransportAttack.attack_hasAttack
#print axioms Lara.Examples.SurfaceTransportAttack.attack_attackComplete
#print axioms Lara.Examples.SurfaceTransportAttack.attack_complete_kernel
#print axioms Lara.Examples.SurfaceTransportAttack.attack_complete_wrapped
#print axioms Lara.Examples.SurfaceTransportAttack.attack_coreObligations_kernel
#print axioms Lara.Examples.SurfaceTransportAttack.attack_coreObligations_wrapped
#print axioms Lara.Examples.SurfaceTransportAttack.attack_checks_kernel
#print axioms Lara.Examples.SurfaceTransportAttack.attack_checks_wrapped
#print axioms Lara.Examples.SurfaceTransportAttack.attack_checkUnit_kernel
#print axioms Lara.Examples.SurfaceTransportAttack.attack_checkUnit_wrapped
#print axioms Lara.Examples.SurfaceTransportAttack.surfaceTransportAttack_directAF_eq
#print axioms Lara.Examples.SurfaceTransportAttack.surfaceTransportAttack_atts_nonempty
#print axioms Lara.Examples.SurfaceTransportAttack.surfaceTransportAttack_relabel_moves_atts
#print axioms Lara.Examples.SurfaceTransportAttack.surfaceTransportAttack_directAF_edge
#print axioms Lara.Examples.SurfaceTransportAttack.surfaceTransportAttack_relabel_moves
#print axioms Lara.Examples.SurfaceTransportAttack.surfaceTransportAttack_inputs_differ

-- Kernel-checked located-hole claim map (root, premise and discharge holes;
-- optional-only completeness; complete-plus-hole status; only-hole gap).
#print axioms Lara.Examples.SurfaceHoles.holesCheck_ok
#print axioms Lara.Examples.SurfaceHoles.holes_partition
#print axioms Lara.Examples.SurfaceHoles.holes_claims
#print axioms Lara.Examples.SurfaceHoles.holes_complete_alternative_status
#print axioms Lara.Examples.SurfaceHoles.holes_only_incomplete_gap
#print axioms Lara.Examples.SurfaceHoles.holes_optional_only

/-! ### The context-bearing surface link fixture

`SurfaceTransport.surfaceTransport_link_directAF_eq` discharges `FixesContext`
on an empty context argument list, so the one hypothesis distinguishing a
link-respecting relabel from an arbitrary one was witnessed only degenerately.
This fixture splits a two-argument unit across the boundary — the context owns
a plain defeasible argument, the fragment the certified one — so the relabel
has material it must fix and material it does move. The saturation lemmas at
the head of the block are what replace `linkedUnit_of_empty_ctx`, which the
context's own arguments make unavailable. -/
#print axioms Lara.Examples.SurfaceTransportContext.contraryMatchB_of_no_contraries
#print axioms Lara.Examples.SurfaceTransportContext.crossAttsFrom_of_no_contraries
#print axioms Lara.Examples.SurfaceTransportContext.crossAtts_of_no_contraries
#print axioms Lara.Examples.SurfaceTransportContext.linkedUnit_of_no_contraries
#print axioms Lara.Examples.SurfaceTransportContext.contextPolicy_no_contraries
#print axioms Lara.Examples.SurfaceTransportContext.context_supported
#print axioms Lara.Examples.SurfaceTransportContext.context_supported_wrapped
#print axioms Lara.Examples.SurfaceTransportContext.context_freshness
#print axioms Lara.Examples.SurfaceTransportContext.context_freshness_wrapped
#print axioms Lara.Examples.SurfaceTransportContext.context_checksArgument_ctx
#print axioms Lara.Examples.SurfaceTransportContext.context_checksArgument_cert
#print axioms Lara.Examples.SurfaceTransportContext.context_checksProgram_kernel
#print axioms Lara.Examples.SurfaceTransportContext.context_checksProgram_wrapped
#print axioms Lara.Examples.SurfaceTransportContext.context_expansions
#print axioms Lara.Examples.SurfaceTransportContext.contextCorePolicy_ruleLookup_cert
#print axioms Lara.Examples.SurfaceTransportContext.contextCorePolicy_ruleLookup_ctx
#print axioms Lara.Examples.SurfaceTransportContext.context_gamma_leafP
#print axioms Lara.Examples.SurfaceTransportContext.context_hasSupport_ctx
#print axioms Lara.Examples.SurfaceTransportContext.context_hasSupport_cert
#print axioms Lara.Examples.SurfaceTransportContext.context_args_kernel
#print axioms Lara.Examples.SurfaceTransportContext.context_args_wrapped
#print axioms Lara.Examples.SurfaceTransportContext.context_complete_kernel
#print axioms Lara.Examples.SurfaceTransportContext.context_complete_wrapped
#print axioms Lara.Examples.SurfaceTransportContext.context_coreObligations_kernel
#print axioms Lara.Examples.SurfaceTransportContext.context_coreObligations_wrapped
#print axioms Lara.Examples.SurfaceTransportContext.context_checks_kernel
#print axioms Lara.Examples.SurfaceTransportContext.context_checks_wrapped
#print axioms Lara.Examples.SurfaceTransportContext.context_checkUnit_kernel
#print axioms Lara.Examples.SurfaceTransportContext.context_checkUnit_wrapped
#print axioms Lara.Examples.SurfaceTransportContext.linkFrag_relabel
#print axioms Lara.Examples.SurfaceTransportContext.linkGamma_leafP
#print axioms Lara.Examples.SurfaceTransportContext.context_unit_is_link
#print axioms Lara.Examples.SurfaceTransportContext.context_unit_wrapped_is_link
#print axioms Lara.Examples.SurfaceTransportContext.linkSideOk_ctx
#print axioms Lara.Examples.SurfaceTransportContext.linkSideOk_frag
#print axioms Lara.Examples.SurfaceTransportContext.contextLink_admissible
#print axioms Lara.Examples.SurfaceTransportContext.contextLink_fixesContext
#print axioms Lara.Examples.SurfaceTransportContext.surfaceTransportContext_link_directAF_eq
#print axioms Lara.Examples.SurfaceTransportContext.surfaceTransportContext_ctx_args_nonempty
#print axioms Lara.Examples.SurfaceTransportContext.surfaceTransportContext_fixes_is_substantive
#print axioms Lara.Examples.SurfaceTransportContext.surfaceTransportContext_relabel_moves_args
#print axioms Lara.Examples.SurfaceTransportContext.surfaceTransportContext_relabel_moves
#print axioms Lara.Examples.SurfaceTransportContext.surfaceTransportContext_link_imports_nonempty
#print axioms Lara.Examples.SurfaceTransportContext.surfaceTransportContext_inputs_differ

-- Accepted fragments separated by their semantic payloads.
#print axioms Lara.Examples.ContextSemantics.semantic_negative_exports
#print axioms Lara.Examples.ContextSemantics.semantic_negative_link_ok
#print axioms Lara.Examples.ContextSemantics.semantic_negative_accepted
#print axioms Lara.Examples.ContextSemantics.semantic_negative_cycle_shape
#print axioms Lara.Examples.ContextSemantics.obsSem_semantic_negative
#print axioms Lara.Examples.ContextSemantics.obsSem_semantic_negative_grounded
#print axioms Lara.Examples.ContextSemantics.ctxEquivSem_semantic_negative

-- Composed and whole-program relational companions.
#print axioms Lara.Context.relFixesContext_composed
#print axioms Lara.Context.obsGen_parametricity_composed
#print axioms Lara.Context.backend_replacement_parametricity_composed_sem
#print axioms Lara.Context.backend_replacement_parametricity_composed
#print axioms Lara.Context.edgeB_rel
#print axioms Lara.Context.checkedAF_rel
#print axioms Lara.Context.whole_program_parametricity_sem
#print axioms Lara.Context.whole_program_parametricity
#print axioms Lara.Context.mem_closedOccurrences
#print axioms Lara.Context.relInj_closedOccRel
#print axioms Lara.Context.relFrag_closedOccRel
#print axioms Lara.Context.relFixesContext_closedOccRel
#print axioms Lara.Context.obsGen_parametricity_closed_local
#print axioms Lara.Context.whole_program_parametricity_local_sem
#print axioms Lara.Context.whole_program_parametricity_local
#print axioms Lara.Context.mem_occursList_iff
#print axioms Lara.Context.mem_occurrences_iff
#print axioms Lara.Context.occurrences_composed

-- An all-context grounded equivalence separated by an adequate selector.
#print axioms Lara.Examples.ContextualSeparation.grounded_ctxEquiv
#print axioms Lara.Examples.ContextualSeparation.separating_link_ok
#print axioms Lara.Examples.ContextualSeparation.separating_accepted
#print axioms Lara.Examples.ContextualSeparation.separating_observations
#print axioms Lara.Examples.ContextualSeparation.singleton_not_ctxEquivSem
#print axioms Lara.Examples.ContextualSeparation.counterexample
#print axioms Lara.Examples.ContextualSeparation.grounded_does_not_imply_semantic

-- Typed CQ substitution, contextual integration and transport.

-- lean/Lara/Context/Holes/Assurance.lean
#print axioms Lara.Context.Holes.lookupFilling_map
#print axioms Lara.Context.Holes.mapFilling_keys
#print axioms Lara.Context.Holes.firstDuplicate_map
#print axioms Lara.Context.Holes.instantiateAux_map
#print axioms Lara.Context.Holes.instantiateAnswer_map
#print axioms Lara.Context.Holes.instantiateList_map
#print axioms Lara.Context.Holes.instantiateDis_map
#print axioms Lara.Context.Holes.instantiate_map
#print axioms Lara.Context.Holes.relTemplates_iff_forall₂
#print axioms Lara.Context.Holes.lookupFilling_rel
#print axioms Lara.Context.Holes.instantiateAux_rel
#print axioms Lara.Context.Holes.instantiateAnswer_rel
#print axioms Lara.Context.Holes.instantiateList_rel
#print axioms Lara.Context.Holes.instantiateDis_rel

-- lean/Lara/Context/Holes/Link.lean
#print axioms Lara.Context.Holes.instantiateList_core
#print axioms Lara.Context.Holes.instantiateAttack_closed
#print axioms Lara.Context.Holes.instantiateAttacks_closed
#print axioms Lara.Context.Holes.instantiateFragment_closed
#print axioms Lara.Context.Holes.obsGen_closed
#print axioms Lara.Context.Holes.obs_closed
#print axioms Lara.Context.Holes.obsSem_closed
#print axioms Lara.Context.Holes.instantiateFragment_inv
#print axioms Lara.Context.Holes.obsGen_of_instantiate
#print axioms Lara.Context.Holes.ctxEquiv_closed_iff
#print axioms Lara.Context.Holes.ctxEquivSem_closed_iff
#print axioms Lara.Context.Holes.mem_instantiateList
#print axioms Lara.Context.Holes.substAttack_append
#print axioms Lara.Context.Holes.substFragment_append
#print axioms Lara.Context.Holes.instantiateAux_subst
#print axioms Lara.Context.Holes.instantiateAnswer_subst
#print axioms Lara.Context.Holes.instantiateList_subst
#print axioms Lara.Context.Holes.instantiateDis_subst
#print axioms Lara.Context.Holes.instantiateAttack_subst
#print axioms Lara.Context.Holes.instantiateAttacks_subst
#print axioms Lara.Context.Holes.instantiateFragment_subst
#print axioms Lara.Context.Holes.compose_eq_some
#print axioms Lara.Context.Holes.composed_filling_assoc
#print axioms Lara.Context.Holes.composed_subst_assoc
#print axioms Lara.Context.Holes.compose_assoc_defined
#print axioms Lara.Context.Holes.composed_frame_material_assoc
#print axioms Lara.Context.Holes.composed_context_assoc

-- lean/Lara/Context/Holes/Syntax.lean
#print axioms Lara.Context.Holes.firstDuplicate_none_iff
#print axioms Lara.Context.Holes.instantiate_eq_aux
#print axioms Lara.Context.Holes.instantiate_core
#print axioms Lara.Context.Holes.eraseOpen_core
#print axioms Lara.Context.Holes.lookupFilling_append
#print axioms Lara.Context.Holes.subst_append
#print axioms Lara.Context.Holes.substAnswer_append
#print axioms Lara.Context.Holes.substList_append
#print axioms Lara.Context.Holes.substDis_append
#print axioms Lara.Context.Holes.fillingNodup_append

-- lean/Lara/Context/Holes/Template.lean
#print axioms Lara.Context.Holes.InstMeta.toInstSide
#print axioms Lara.Context.Holes.InstMeta.ofInstSide
#print axioms Lara.Context.Holes.InstMeta.answers_equiv
#print axioms Lara.Context.Holes.instantiateList_supported
#print axioms Lara.Context.Holes.instantiateDis_supported
#print axioms Lara.Context.Holes.instantiateAux_hasSupport
#print axioms Lara.Context.Holes.instantiateAnswer_hasSupport
#print axioms Lara.Context.Holes.instantiate_hasSupport
#print axioms Lara.Context.Holes.eraseList_length
#print axioms Lara.Context.Holes.eraseDis_keys_perm
#print axioms Lara.Context.Holes.eraseDis_keys_mem
#print axioms Lara.Context.Holes.eraseList_supported
#print axioms Lara.Context.Holes.eraseDis_supported
#print axioms Lara.Context.Holes.InstMeta.eraseOpen
#print axioms Lara.Context.Holes.eraseOpen_hasSupport

-- lean/Lara/Context/Holes/Transport.lean
#print axioms Lara.Context.Holes.instantiateAttack_map
#print axioms Lara.Context.Holes.instantiateAttacks_map
#print axioms Lara.Context.Holes.instantiateFragment_map
#print axioms Lara.Context.Holes.obsGen_congr
#print axioms Lara.Context.Holes.backend_replacement_congruence_sem
#print axioms Lara.Context.Holes.backend_replacement_congruence
#print axioms Lara.Context.Holes.instantiateAttack_rel
#print axioms Lara.Context.Holes.instantiateAttacks_rel
#print axioms Lara.Context.Holes.instantiateFragment_rel
#print axioms Lara.Context.Holes.obsGen_parametricity
#print axioms Lara.Context.Holes.backend_replacement_parametricity_sem
#print axioms Lara.Context.Holes.backend_replacement_parametricity

-- lean/Lara/Context/Holes.lean
#print axioms Lara.Context.Holes.instantiated_support
#print axioms Lara.Context.Holes.sideOk_of_typed
#print axioms Lara.Context.Holes.link_attackComplete
#print axioms Lara.Context.Holes.link_checked
#print axioms Lara.Context.Holes.obsGen_eq_of_ok

-- lean/Lara/Examples/TermHoles.lean
#print axioms Lara.Examples.TermHoles.source_support
#print axioms Lara.Examples.TermHoles.source_obligations_nonempty
#print axioms Lara.Examples.TermHoles.erase_nested
#print axioms Lara.Examples.TermHoles.instantiate_nested
#print axioms Lara.Examples.TermHoles.fillings_nodup
#print axioms Lara.Examples.TermHoles.fillings_disjoint
#print axioms Lara.Examples.TermHoles.sequential_substitution
#print axioms Lara.Examples.TermHoles.sequential_instantiation
#print axioms Lara.Examples.TermHoles.missing_binding
#print axioms Lara.Examples.TermHoles.duplicate_binding
#print axioms Lara.Examples.TermHoles.template_typed
#print axioms Lara.Examples.TermHoles.fillings_typed
#print axioms Lara.Examples.TermHoles.erased_source_typed
#print axioms Lara.Examples.TermHoles.filled_support
#print axioms Lara.Examples.TermHoles.filled_attack_typed
#print axioms Lara.Examples.TermHoles.linked_gamma
#print axioms Lara.Examples.TermHoles.closed_link_accepted
#print axioms Lara.Examples.TermHoles.attack_endpoint_discharge
#print axioms Lara.Examples.TermHoles.wrong_answer_instantiates
#print axioms Lara.Examples.TermHoles.wrong_answer_rejected
#print axioms Lara.Examples.TermHoles.fragment_instantiated
#print axioms Lara.Examples.TermHoles.attack_instantiated
#print axioms Lara.Examples.TermHoles.hole_observation
#print axioms Lara.Examples.TermHoles.hole_missing
#print axioms Lara.Examples.TermHoles.hole_duplicate
#print axioms Lara.Examples.TermHoles.hole_wrong_answer
#print axioms Lara.Examples.TermHoles.fragment_sequential
#print axioms Lara.Examples.TermHoles.contexts_compose
#print axioms Lara.Examples.TermHoles.composed_observation
#print axioms Lara.Examples.TermHoles.certificate_filling_typed
#print axioms Lara.Examples.TermHoles.certificate_frame_fixed
#print axioms Lara.Examples.TermHoles.typed_link_checked
#print axioms Lara.Examples.TermHoles.certificate_filling_moves
#print axioms Lara.Examples.TermHoles.certificate_context_not_fixed
#print axioms Lara.Examples.TermHoles.functional_transport_sem
#print axioms Lara.Examples.TermHoles.relational_transport_sem

-- Multi-artifact maps: member-alias qualification and the
-- N-member linking fold.
#print axioms Lara.Map.qualifiedKey_inj
#print axioms Lara.Map.qualifyLeaf_injective
#print axioms Lara.Map.qualifyLeaf_ne_of_alias_ne
#print axioms Lara.Map.mapLeafList_eq
#print axioms Lara.Map.mapLeafDis_eq
#print axioms Lara.Map.mapLeafAtt_source
#print axioms Lara.Map.mapLeafAtt_target
#print axioms Lara.Map.mapLeaf_inj
#print axioms Lara.Map.mapLeafList_inj
#print axioms Lara.Map.mapLeafDis_inj
#print axioms Lara.Map.mapLeaf_injective
#print axioms Lara.Map.mapLeaf_eq_iff
#print axioms Lara.Map.lookupDis_mapLeafDis
#print axioms Lara.Map.mapLeaf_subterm
#print axioms Lara.Map.containsB_mapLeaf
#print axioms Lara.Map.containsBList_mapLeaf
#print axioms Lara.Map.containsBDis_mapLeaf
#print axioms Lara.Map.attackClosureB_mapLeaf
#print axioms Lara.Map.coveredB_mapLeaf
#print axioms Lara.Map.mapLeafList_length
#print axioms Lara.Map.mapLeafDis_length
#print axioms Lara.Map.mapLeafDis_keys
#print axioms Lara.Map.mapLeafList_getElem?_some
#print axioms Lara.Map.mapLeafDis_getElem?_some
#print axioms Lara.Map.hasSupport_mapLeaf
#print axioms Lara.Map.hasAttack_mapLeaf
#print axioms Lara.Map.mapLeafProg_args
#print axioms Lara.Map.mapLeafProg_holes
#print axioms Lara.Map.mapLeafProg_atts
#print axioms Lara.Map.edgeB_mapLeaf
#print axioms Lara.Map.checkedAF_mapLeaf
#print axioms Lara.Map.labelC_mapLeaf
#print axioms Lara.Map.statusC_mapLeaf
#print axioms Lara.Map.statusC_mapLeafProg
#print axioms Lara.Map.buildGamma_qualifyGamma
#print axioms Lara.Map.qualifyGamma_disjoint
#print axioms Lara.Map.sideGamma_linkStep
#print axioms Lara.Map.linkStep_sideOk
#print axioms Lara.Map.linkStep_sideOkHoles
#print axioms Lara.Map.linkMembers_sideOk
#print axioms Lara.Map.linkMembers_sideOkHoles
#print axioms Lara.Map.firstShared?_nil
#print axioms Lara.Map.linkOk_closedTail
#print axioms Lara.Map.sideOk_closedTail
#print axioms Lara.Map.linkMembers_checked
#print axioms Lara.Map.linkMembers_checked_holes
#print axioms Lara.Map.linkStep_declared
#print axioms Lara.Map.linkMembers_declared
#print axioms Lara.Map.qualifyFragment_declared
#print axioms Lara.Map.qualifiedBy_qualifyFragment
#print axioms Lara.Map.foldHygiene_of_distinct_aliases
#print axioms Lara.Map.foldHygiene_emptyMap
#print axioms Lara.Map.linkStep_declared_nodup
#print axioms Lara.Map.linkMembers_declared_nodup
#print axioms Lara.Map.qualifyFragment_declared_nodup
#print axioms Lara.Map.foldHygiene_two_aliases_of_one_member
-- The premises of `linkMembers_checked` exhibited holding together at a
-- concrete map, which is what makes that theorem non-vacuous rather than merely
-- true.
#print axioms Lara.Map.memberP_foldHygiene
#print axioms Lara.Map.memberP_sideOk
#print axioms Lara.Map.unitPolicyEx_wellFormed
#print axioms Lara.Map.soloMap_linkMembers_checked
#print axioms Lara.Map.contestedMap_extends
#print axioms Lara.Map.contestedMap_atts
#print axioms Lara.Map.soloMap_accepted
#print axioms Lara.Map.contestedMap_accepted
#print axioms Lara.Map.soloMap_status
#print axioms Lara.Map.contestedMap_status
#print axioms Lara.Map.linkMembers_status_not_preserved
-- The batch link the drivers run, and its agreement with the fold.
#print axioms Lara.Map.mem_crossPairs
#print axioms Lara.Map.crossPairs_spec
#print axioms Lara.Map.crossPairs_endpoints_complete
#print axioms Lara.Map.crossPairs_emits
#print axioms Lara.Map.batchGamma_extends
#print axioms Lara.Map.ownedApart_iff
#print axioms Lara.Map.batch_checked
#print axioms Lara.Map.batch_checked_holes
#print axioms Lara.Map.batch_classify
#print axioms Lara.Map.batch_hole_report
#print axioms Lara.Map.batch_member_hole_reported
#print axioms Lara.Map.batch_generated_live
#print axioms Lara.Map.batch_hole_source_inert
#print axioms Lara.Map.mem_batchArgs
#print axioms Lara.Map.mem_batchAtts
#print axioms Lara.Map.batchUnit_checked
#print axioms Lara.Map.Emits.mono
#print axioms Lara.Map.mem_crossPairs_iff_emits
#print axioms Lara.Map.declared_nodup_of_qualified
#print axioms Lara.Map.linkMembers_emits
#print axioms Lara.Map.batch_atts_mem_iff_fold
#print axioms Lara.Map.batch_args_mem_iff_fold
#print axioms Lara.Map.memberQ_sideOk
#print axioms Lara.Map.contestedPairs_batchAtts
#print axioms Lara.Map.contestedPairs_batchUnit_checked
-- The Lean driver's linked unit is an instance of `batch_checked`.
#print axioms Lara.Map.Driver.mem_firstOccurrences
#print axioms Lara.Map.Driver.firstOccurrences_nodup
#print axioms Lara.Map.Driver.mem_dedupAttacks
#print axioms Lara.Map.Driver.mem_dedupStrings
#print axioms Lara.Map.Driver.mem_declaredArgs
#print axioms Lara.Map.Driver.mem_ownersOf
#print axioms Lara.Map.Driver.crossMember_ownersOf_iff
#print axioms Lara.Map.Driver.linkedGammaOf_eq
#print axioms Lara.Map.Driver.mem_linkedTermsOf
#print axioms Lara.Map.Driver.linkedUnitOf_checked
#print axioms Lara.Map.Driver.linkedUnitOf_checked_holes
#print axioms Lara.Map.Driver.linkedUnitOf_hole_report
#print axioms Lara.Map.Driver.generatedAttacksOf_endpoints_complete
#print axioms Lara.Map.Driver.generatedAttacksOf_live
/-! ### PW — the `Query_κ` well-sortedness refinement -/

-- 1. Query formation. `queryFault` is the existing `Sigma` judgment, located:
--    no fault IS well-sortedness, each of the two faults is pinned to exactly
--    its condition, a fault names the atom's own head predicate
--    (`queryFault_pred`; the total classifier behind it is private, since it
--    is only meaningful under the gate), and the two exhaust ill-formedness.
--    `pose` is the sanctioned decision procedure and does not rewrite the
--    authored claim.
#print axioms Lara.PW.Sorted.queryFault_eq_none_iff
#print axioms Lara.PW.Sorted.queryFault_pred
#print axioms Lara.PW.Sorted.not_wellSorted_of_lookupPred_none
#print axioms Lara.PW.Sorted.queryFault_undeclaredPredicate_iff
#print axioms Lara.PW.Sorted.queryFault_illSortedArguments_iff
#print axioms Lara.PW.Sorted.not_wellSorted_iff_exists_fault
#print axioms Lara.PW.Sorted.pose_ok_iff
#print axioms Lara.PW.Sorted.pose_error_iff
#print axioms Lara.PW.Sorted.pose_ok_val
#print axioms Lara.PW.Sorted.pose_val_self
#print axioms Lara.PW.Sorted.query_no_fault

-- 2. What a `gap` still means. `Grounded.statusC_gap_iff` at the world: the
--    compiled observation gaps exactly when the world declares no complete
--    argument concluding the claim, so "posed but unsupported" is not a fourth
--    gap cause but a theorem-level collapse into the third. The refined
--    `report` splits the remaining conditions, each constructor pinned, and
--    `report_ne_observed_iff_gap` proves the split moves no PW0 answer.
#print axioms Lara.PW.Sorted.addresses_iff
#print axioms Lara.PW.Sorted.cmpStatus_gap_iff_not_addresses
#print axioms Lara.PW.Sorted.srcStatus_gap_iff_not_addresses
#print axioms Lara.PW.Sorted.not_gap_of_addresses
#print axioms Lara.PW.Sorted.status_of_addresses
#print axioms Lara.PW.Sorted.report_observed_iff
#print axioms Lara.PW.Sorted.report_unaddressed_iff
#print axioms Lara.PW.Sorted.report_outOfVocabulary_iff
#print axioms Lara.PW.Sorted.report_illSorted_iff
#print axioms Lara.PW.Sorted.sortedWorld_of_nodes
#print axioms Lara.PW.Sorted.report_ne_observed_iff_gap

-- 3. Posing across a bridge. The refined executable comparison adds one guard
--    before PW0's three; each fault is pinned and *located* — `vocabFault` is
--    `trAtom`'s own traversal reporting the first symbol the bridge cannot
--    carry, and `vocabFault_eq_none_iff` proves the scan is exactly `trAtom`'s
--    domain condition. No fault carries a `Status`, PW0's
--    `translationUndefined` is unreachable past the new guard
--    (`crossComparePosed_ne_translationUndefined`), and
--    `notPosable_world_independent` is the load-bearing one: a posing fault is
--    a statement about the two signatures and the bridge, never about a world.
#print axioms Lara.PW.Sorted.vocabFaultTerm_eq_none_iff
#print axioms Lara.PW.Sorted.vocabFaultTerms_eq_none_iff
#print axioms Lara.PW.Sorted.vocabFault_eq_none_iff
#print axioms Lara.PW.Sorted.vocabFault_isSome_of_trAtom_none
#print axioms Lara.PW.Sorted.trQueryFault_ne_sourceQuery
#print axioms Lara.PW.Sorted.trQueryFault_eq_none_iff
#print axioms Lara.PW.Sorted.notPosable_ne_compared
#print axioms Lara.PW.Sorted.crossComparePosed_sourceQuery_iff
#print axioms Lara.PW.Sorted.crossComparePosed_bridgeVocabulary_iff
#print axioms Lara.PW.Sorted.crossComparePosed_targetQuery_iff
#print axioms Lara.PW.Sorted.crossComparePosed_compared
#print axioms Lara.PW.Sorted.crossCompare_some_ne_translationUndefined
#print axioms Lara.PW.Sorted.crossComparePosed_ne_translationUndefined
#print axioms Lara.PW.Sorted.notPosable_world_independent

-- 4. The sorted frame: T4 and the valuation coherence again at the refined
--    query set, and `sat_erase` — the conservativity theorem proving the
--    refinement changes no answer PW0 could already give.
#print axioms Lara.PW.Sorted.sat_src_iff_cmp
#print axioms Lara.PW.Sorted.cmpVal_functional
#print axioms Lara.PW.Sorted.cmpVal_total
#print axioms Lara.PW.Sorted.srcVal_functional
#print axioms Lara.PW.Sorted.srcVal_total
#print axioms Lara.PW.Sorted.sat_erase
#print axioms Lara.PW.Sorted.sat_erase_src

-- 5. The witnesses: one world at which PW0 reports `gap` three times for three
--    different reasons, and the three reports that replace it; the three
--    posing faults at a bridge, including the sharpened form of
--    `overlap_translationUndefined`; and the erasure instantiated.
#print axioms Lara.Examples.PWSorted.pw0_gap_p
#print axioms Lara.Examples.PWSorted.pw0_gap_s
#print axioms Lara.Examples.PWSorted.pw0_gap_illSorted
#print axioms Lara.Examples.PWSorted.pw0_justified_q
#print axioms Lara.Examples.PWSorted.report_p
#print axioms Lara.Examples.PWSorted.report_s
#print axioms Lara.Examples.PWSorted.report_illSorted
#print axioms Lara.Examples.PWSorted.report_q
#print axioms Lara.Examples.PWSorted.reports_distinct
#print axioms Lara.Examples.PWSorted.split_not_change
#print axioms Lara.Examples.PWSorted.sortedWorld_wOverlap
#print axioms Lara.Examples.PWSorted.sorted_r_sourceQuery
#print axioms Lara.Examples.PWSorted.sorted_qz_sourceQuery
#print axioms Lara.Examples.PWSorted.sorted_q_bridgeVocabulary
#print axioms Lara.Examples.PWSorted.sorted_s_targetQuery
#print axioms Lara.Examples.PWSorted.sorted_t_targetIllSorted
#print axioms Lara.Examples.PWSorted.sorted_t_bridgeVocabulary_con
#print axioms Lara.Examples.PWSorted.bridge_and_target_faults_distinct
#print axioms Lara.Examples.PWSorted.sorted_q_compared
#print axioms Lara.Examples.PWSorted.trQuery_q
#print axioms Lara.Examples.PWSorted.sorted_dia_q
#print axioms Lara.Examples.PWSorted.sorted_dia_q_erased
#print axioms Lara.Examples.PWSorted.sorted_dia_q_src

/-! ### PW — surface syntax for the outer language -/

-- 6. The declared maps, and the one clause the elaborator decides. `ruleOkB`
--    is a genuine decider for `StructuralBridge.rule_ok` because a policy
--    carries its rules as a finite list; `leaf_ok` and `cert_ok` cannot be
--    decided and stay declared premises. `Clause.mem_all` is what makes the
--    completeness check quantify over the clause *type* rather than over a
--    hand-maintained list.
#print axioms Lara.PW.Surface.Clause.mem_all
#print axioms Lara.PW.Surface.leafMapOf_nil
#print axioms Lara.PW.Surface.leafMapOf_cons_self
#print axioms Lara.PW.Surface.leafMapOf_cons_other
#print axioms Lara.PW.Surface.predMapOf_eq_none
#print axioms Lara.PW.Surface.ruleOkB_iff
#print axioms Lara.PW.Surface.bridgeError?_eq_none_iff
#print axioms Lara.PW.Surface.find?_missing_none_iff

-- 7. Bridge declarations, in the M5 shape: independent judgment, executable
--    decider, sound/complete/deterministic, then preservation (a derivable
--    declaration *is* T6's contract) and reflection.
--    `elabBridge_support_transport` is where `BridgeEnv.canon_shared` becomes
--    load-bearing: the transported support is a judgment of the target
--    context's own environment.
#print axioms Lara.PW.Surface.elabBridge_sound
#print axioms Lara.PW.Surface.elabBridge_complete
#print axioms Lara.PW.Surface.elaboratesBridge_deterministic
#print axioms Lara.PW.Surface.elabBridge_preserves
#print axioms Lara.PW.Surface.elabBridge_support_transport
#print axioms Lara.PW.Surface.elabBridge_reflects
#print axioms Lara.PW.Surface.elabBridge_of_no_rules

-- 8. Posed modal queries. The surface form is untyped and `PW.Form` is
--    intrinsically typed, so elaboration is a typing pass: names identify
--    frame indices (`ctxName_inj`), status atoms are posed by `Sorted.pose`,
--    and the round trip proves the pass renames nothing.
#print axioms Lara.PW.Surface.Naming.ctxName_inj
#print axioms Lara.PW.Surface.Naming.bridgeName_inj
#print axioms Lara.PW.Surface.formError?_eq_none_iff
#print axioms Lara.PW.Surface.elabForm_sound
#print axioms Lara.PW.Surface.elabForm_complete
#print axioms Lara.PW.Surface.elaborates_deterministic
#print axioms Lara.PW.Surface.elaborates_preserves
#print axioms Lara.PW.Surface.elaborates_reflects
#print axioms Lara.PW.Surface.elabForm_unelab
#print axioms Lara.PW.Surface.elabPosed_ok_iff

-- 9. The surface witnesses: a bridge declaration whose rule clause is
--    non-vacuous (one positive cell and one per failure mode of `ruleOkB`),
--    whose `BridgeObligations` are *discharged* rather than assumed, and
--    across which `elabBridge_support_transport` actually carries a checked
--    support; and a posed query whose ill-sorted variant is a *typing error at
--    authoring time* — the fixture that joins the two halves.
#print axioms Lara.Examples.PWSurface.rule_clause_holds
#print axioms Lara.Examples.PWSurface.rule_clause_fails
#print axioms Lara.Examples.PWSurface.rule_clause_fails_mistranslated
#print axioms Lara.Examples.PWSurface.rule_clause_fails_untranslatable
#print axioms Lara.Examples.PWSurface.leafMap_declared
#print axioms Lara.Examples.PWSurface.leafMap_undeclared
#print axioms Lara.Examples.PWSurface.predMap_declared_after_con
#print axioms Lara.Examples.PWSurface.conMap_declared
#print axioms Lara.Examples.PWSurface.conMap_undeclared
#print axioms Lara.Examples.PWSurface.trAtom_renames_con
#print axioms Lara.Examples.PWSurface.elaborates_declOK
#print axioms Lara.Examples.PWSurface.elabBridge_declOK
#print axioms Lara.Examples.PWSurface.elabBridge_missingClause
#print axioms Lara.Examples.PWSurface.elabBridge_ruleClauseFails
#print axioms Lara.Examples.PWSurface.elabBridge_ruleClauseFails_mistranslated
#print axioms Lara.Examples.PWSurface.elabBridge_nameMismatch
#print axioms Lara.Examples.PWSurface.elabBridge_sourceMismatch
#print axioms Lara.Examples.PWSurface.elabBridge_targetMismatch
#print axioms Lara.Examples.PWSurface.obligations_declOK
#print axioms Lara.Examples.PWSurface.structuralBridge_declOK
#print axioms Lara.Examples.PWSurface.trSupport_wDecl
#print axioms Lara.Examples.PWSurface.hasSupport_wDecl
#print axioms Lara.Examples.PWSurface.support_transport_declOK
#print axioms Lara.Examples.PWSurface.elaborates_surfaceQuery
#print axioms Lara.Examples.PWSurface.elabForm_surfaceQuery
#print axioms Lara.Examples.PWSurface.unelab_surfaceQuery
#print axioms Lara.Examples.PWSurface.elab_illSorted
#print axioms Lara.Examples.PWSurface.elab_outOfVocabulary
#print axioms Lara.Examples.PWSurface.elab_unknownBridge
#print axioms Lara.Examples.PWSurface.elab_sourceMismatch
#print axioms Lara.Examples.PWSurface.elabPosed_surfaceQuery
#print axioms Lara.Examples.PWSurface.elabPosed_unknownContext
#print axioms Lara.Examples.PWSurface.surfaceQuery_holds

/-! ### Declared outer bridges, wire round trips, and finite evaluation -/
#print axioms Lara.PW.Surface.Declared.Registry.lookup_name
#print axioms Lara.PW.Surface.Declared.Registry.lookup_mem
#print axioms Lara.PW.Surface.Declared.Registry.lookup_get
#print axioms Lara.PW.Surface.Declared.Registry.lookup_isSome_of_mem
#print axioms Lara.PW.Surface.Declared.Registry.bridges_names
#print axioms Lara.PW.Surface.Declared.Registry.coherent
#print axioms Lara.PW.Surface.Declared.Registry.resolved_decl
#print axioms Lara.PW.Surface.Declared.resolve_decl
#print axioms Lara.PW.Surface.Declared.loadInto_declarations
#print axioms Lara.PW.Surface.Declared.load_declarations
#print axioms Lara.PW.Surface.Declared.elaborates_resolves
#print axioms Lara.PW.Surface.Declared.elabForm_declared
#print axioms Lara.PW.Surface.Declared.elabPosed_declared
#print axioms Lara.PW.Wire.Tag.parse_text
#print axioms Lara.PW.Wire.Tag.text_injective
#print axioms Lara.PW.Wire.head_tagged
#print axioms Lara.PW.Wire.bind_ok
#print axioms Lara.PW.Wire.map_ok
#print axioms Lara.PW.Wire.decodeList_map
#print axioms Lara.PW.Wire.decodeTerm_encode
#print axioms Lara.PW.Wire.decodeTerms_encode
#print axioms Lara.PW.Wire.decodeAtom_encode
#print axioms Lara.PW.Wire.decodeStatus_encode
#print axioms Lara.PW.Wire.decodeClause_encode
#print axioms Lara.PW.Wire.decodeSymEntry_encode
#print axioms Lara.PW.Wire.decodeLeafEntry_encode
#print axioms Lara.PW.Wire.sectionItems_tagged
#print axioms Lara.PW.Wire.decodeBridgeDecl_encode
#print axioms Lara.PW.Wire.decodeForm_encode
#print axioms Lara.PW.Wire.decodePosed_encode
#print axioms Lara.PW.Wire.decodeDocument_encode
#print axioms Lara.PW.Wire.encodeDocument_injective
#print axioms Lara.PW.evalFinite_iff
#print axioms Lara.Examples.PWDeclared.loaded
#print axioms Lara.Examples.PWDeclared.duplicate_rejected
#print axioms Lara.Examples.PWDeclared.unknown_source_rejected
#print axioms Lara.Examples.PWDeclared.unknown_target_rejected
#print axioms Lara.Examples.PWDeclared.clause_rejected
#print axioms Lara.Examples.PWDeclared.rule_rejected
#print axioms Lara.Examples.PWDeclared.name_resolves
#print axioms Lara.Examples.PWDeclared.declared_translation
#print axioms Lara.Examples.PWDeclared.undeclared_rejected
#print axioms Lara.Examples.PWDeclared.context_mismatch_rejected
#print axioms Lara.Examples.PWDeclared.nested_elaborates
#print axioms Lara.Examples.PWDeclared.source_spelling_rejected
#print axioms Lara.Examples.PWFinite.empty_box
#print axioms Lara.Examples.PWFinite.empty_dia
#print axioms Lara.Examples.PWFinite.local_and_neg
#print axioms Lara.Examples.PWFinite.nested_modal
#print axioms Lara.Examples.PWFinite.nested_modal_false
#print axioms Lara.Examples.PWFileHost.evaluates_iff
#print axioms Lara.PW.Run.Tag.parse_text
#print axioms Lara.PW.Run.Tag.text_injective
#print axioms Lara.PW.Run.head_tagged
#print axioms Lara.PW.Run.sectionItems_tagged
#print axioms Lara.PW.Run.decodeAcceptance_encode
#print axioms Lara.PW.Run.decodeSource_encode
#print axioms Lara.PW.Run.decodeWorld_encode
#print axioms Lara.PW.Run.decodeEdge_encode
#print axioms Lara.PW.Run.decodeCompare_encode
#print axioms Lara.PW.Run.decodeRun_encode
#print axioms Lara.PW.Run.encodeRun_injective
#print axioms Lara.PW.Run.distinct_append
#print axioms Lara.PW.Run.Hosted.find_isSome
#print axioms Lara.PW.Run.indexIn_declared
#print axioms Lara.PW.Run.Model.evaluates_iff
#print axioms Lara.PW.Run.Model.presents
#print axioms Lara.PW.Run.Model.compare_mem_iff_sat
#print axioms Lara.PW.Run.Model.index_declared
#print axioms Lara.PW.Run.Model.candidates_declared
#print axioms Lara.PW.Run.Model.accepts_declared
#print axioms Lara.PW.Run.ResultTag.parse_text
#print axioms Lara.PW.Run.ResultTag.text_injective
#print axioms Lara.PW.Run.IdsOk.mono
#print axioms Lara.PW.Run.extendCtx_ids
#print axioms Lara.PW.Run.placeWorld_ids
#print axioms Lara.PW.Run.addWorld_ids
#print axioms Lara.PW.Run.loadWorlds_ids
#print axioms Lara.PW.Run.loadWorlds_nodup
#print axioms Lara.PW.Run.Hosted.entry_mem
#print axioms Lara.PW.Run.positionIn_some
#print axioms Lara.PW.Run.resolveEdge_declared
#print axioms Lara.PW.Run.resolveEdges_declared
#print axioms Lara.PW.Run.index_of_id
#print axioms Lara.PW.Run.find?_id
#print axioms Lara.PW.Run.Model.candidates_named
#print axioms Lara.PW.Run.Model.accepts_named
#print axioms Lara.PW.Run.loadModel_spec
#print axioms Lara.PW.Run.load_candidates_named
#print axioms Lara.PW.Run.load_accepts_named

-- PW outer runtime: consistent duplicate-report groups are inert. The
-- §4.3 identities (`Lara.Groups`) and the loader theorem that rests on them:
-- a world `addWorld` accepts has an empty quarantine set, so the leaf table
-- and argument list it checks are the declared ones.
#print axioms Lara.Groups.quarantined_eq_nil
#print axioms Lara.Groups.anyConflict_eq_false_iff
#print axioms Lara.Groups.quarantineLeaves_nil
#print axioms Lara.Groups.usesLeaf_nil
#print axioms Lara.Groups.usesLeafList_nil
#print axioms Lara.Groups.usesLeafDisch_nil
#print axioms Lara.Groups.keepArg_nil
#print axioms Lara.Groups.quarantineArgs_nil
#print axioms Lara.PW.Run.addWorld_decoded
#print axioms Lara.PW.Run.addWorld_quarantine_empty
#print axioms Lara.PW.Run.addWorld_checks_declared

-- PW outer runtime: duplicate-world identity carries the located holes. Two
-- worlds whose checked programs agree on AF arguments and compiled attacks but
-- not on holes are both loaded; a repeated program, holes included, is refused.
#print axioms Lara.Examples.PWRun.holes_world_kept
#print axioms Lara.Examples.PWRun.holes_world_states
#print axioms Lara.Examples.PWRun.holes_world_complete_parts_agree
#print axioms Lara.Examples.PWRun.holes_world_duplicate

-- Admission, local statuses, and structural failure are separate facts.
#print axioms Lara.Examples.AxiomWithdrawal.withdrawal_prunes
#print axioms Lara.Examples.AxiomWithdrawal.rejection_stops
#print axioms Lara.Examples.AxiomWithdrawal.certificate_depends_on_premise
#print axioms Lara.Examples.AxiomWithdrawal.units_accepted
#print axioms Lara.Examples.AxiomWithdrawal.local_statuses
#print axioms Lara.Examples.AxiomWithdrawal.source_support
#print axioms Lara.Examples.AxiomWithdrawal.retained_transport
#print axioms Lara.Examples.AxiomWithdrawal.leafCheck_iff
#print axioms Lara.Examples.AxiomWithdrawal.leaf_controls
#print axioms Lara.Examples.AxiomWithdrawal.no_withdrawn_bridge

#print axioms Lara.Evidence.except_bind_error
#print axioms Lara.Evidence.except_bind_ok
#print axioms Lara.Evidence.checkerName_injective
#print axioms Lara.Evidence.encodingName_injective
#print axioms Lara.Evidence.requestObjects_singleton
#print axioms Lara.Presentation.un_sxLeafChecker
#print axioms Lara.Presentation.un_sxCheckerVersion
#print axioms Lara.Presentation.un_sxEvidenceChecker
#print axioms Lara.Presentation.un_sxList_EvidenceChecker
#print axioms Lara.Presentation.un_sxEncoding
#print axioms Lara.Presentation.un_sxJsonToken
#print axioms Lara.Presentation.un_sxJsonPath
#print axioms Lara.Presentation.un_sxCsvSelector
#print axioms Lara.Presentation.un_sxCsvSelectors
#print axioms Lara.Presentation.un_sxJsonSelector
#print axioms Lara.Presentation.un_sxJsonSelectors
#print axioms Lara.Presentation.un_sxExtractionRequest
#print axioms Lara.Presentation.un_sxOpt_ExtractionRequest
#print axioms Lara.Presentation.sxExtractionRequest_injective
#print axioms Lara.Evidence.decodeScalar_iff
#print axioms Lara.Evidence.column_iff
#print axioms Lara.Evidence.csvColumns_iff
#print axioms Lara.Evidence.pointer_iff
#print axioms Lara.Evidence.pointer_unique
#print axioms Lara.Evidence.jsonColumns_iff
#print axioms Lara.Evidence.jsonMeasure_empty_object
#print axioms Lara.Evidence.jsonMeasure_empty_array
#print axioms Lara.Evidence.jsonMeasure_object_cons
#print axioms Lara.Evidence.jsonMeasure_array_cons
#print axioms Lara.Evidence.jsonMeasure_object_singleton
#print axioms Lara.Evidence.jsonMeasure_array_singleton
#print axioms Lara.Evidence.jsonMeasure_nodes_positive
#print axioms Lara.Evidence.jsonMeasure_every_depth
#print axioms Lara.Evidence.jsonWithinBounds_iff
#print axioms Lara.Evidence.jsonWithinBounds_array_singleton_iff
#print axioms Lara.Evidence.jsonWithinBounds_reject_depth
#print axioms Lara.Evidence.jsonWithinBounds_depth_boundary
#print axioms Lara.Evidence.csv_unique_row
#print axioms Lara.Evidence.csvWellFormed_iff
#print axioms Lara.Evidence.csvSelect_iff
#print axioms Lara.Evidence.extract_csv_exact
#print axioms Lara.Evidence.extract_json_exact
#print axioms Lara.Evidence.extracted_normal_form
#print axioms Lara.Evidence.lookup_id
#print axioms Lara.Evidence.run_dependencies
#print axioms Lara.Evidence.supply_membership
#print axioms Lara.Evidence.run_snapshot_membership
#print axioms Lara.Evidence.supply_locality
#print axioms Lara.Evidence.run_locality
#print axioms Lara.Evidence.missing_dependency
#print axioms Lara.Evidence.run_registry_replacement
#print axioms Lara.Evidence.supply_exact_ids
#print axioms Lara.Evidence.run_exact_declared_dependencies
#print axioms Lara.Evidence.run_deterministic
#print axioms Lara.Evidence.firstInvalid_none_iff
#print axioms Lara.Evidence.firstInvalid_prefix
#print axioms Lara.Evidence.replayLeaf_iff
#print axioms Lara.Evidence.replayLeaves_iff
#print axioms Lara.Evidence.admit_iff
#print axioms Lara.Evidence.all_declared_supported
#print axioms Lara.Evidence.declared_replay_witness
#print axioms Lara.Evidence.retained_supported
#print axioms Lara.Evidence.admission_deterministic
#print axioms Lara.Evidence.binding_precedes_capture
#print axioms Lara.Evidence.capture_precedes_extraction
#print axioms Lara.Evidence.firstInvalid_mem
#print axioms Lara.Evidence.firstInvalid_congr
#print axioms Lara.Evidence.replayLeaf_registry_congr
#print axioms Lara.Evidence.replayLeaves_registry_congr
#print axioms Lara.Evidence.admission_registry_replacement
#print axioms Lara.Evidence.request_local_of_source_local
#print axioms Lara.Evidence.replayLeaves_locality
#print axioms Lara.Evidence.admission_locality
#print axioms Lara.Evidence.all_declared_certified_witness
#print axioms Lara.Evidence.retained_certified_witness
#print axioms Lara.Evidence.replayLeaves_first_error
#print axioms Lara.Evidence.admission_first_extraction_error
#print axioms Lara.Evidence.checked_partition_exact
#print axioms Lara.Surface.sourceWithoutEvidence_core
#print axioms Lara.Surface.sourceWithoutEvidence_sound
#print axioms Lara.Surface.sourceWithEvidence_sound
#print axioms Lara.Evidence.successful_gate_conservativity
#print axioms Lara.Evidence.package_checked_context_exact
#print axioms Lara.Evidence.package_retained_gamma_agree
#print axioms Lara.Evidence.package_source_preserves
#print axioms Lara.Evidence.package_holes_iff
#print axioms Lara.Evidence.package_hole_reports_exact
#print axioms Lara.Evidence.package_source_justified_nonpromotion
#print axioms Lara.Surface.sourceWithEvidence_semantic
#print axioms Lara.Evidence.package_same_source_witness
#print axioms Lara.Evidence.concrete_admission_refinement
#print axioms Lara.Evidence.replay_checked_partition
#print axioms Lara.Surface.finishAssembled_eq_check
#print axioms Lara.Surface.elaborateSourceWithoutEvidence_assembled
#print axioms Lara.Surface.sourceWithEvidence_core_and_semantic
#print axioms Lara.Evidence.binding_stage_first_error
#print axioms Lara.Evidence.capture_stage_first_error
#print axioms Lara.Surface.sourceWithoutEvidence_conservative

#print axioms Lara.BHL.varId_index_injective
#print axioms Lara.BHL.testId_index_injective
#print axioms Lara.BHL.datasetId_index_injective
#print axioms Lara.BHL.hypothesisId_index_injective
#print axioms Lara.BHL.ghostId_index_injective
#print axioms Lara.BHL.variable_id_injective
#print axioms Lara.BHL.ReferenceAudit.equal_memory_equal_valuation
#print axioms Lara.BHL.ReferenceAudit.assignment_substitution_counterexample
#print axioms Lara.BHL.ReferenceAudit.alias_history_consistent
#print axioms Lara.BHL.ReferenceAudit.history_assertion_counterexample
#print axioms Lara.BHL.ReferenceAudit.named_history_update_inconsistent
#print axioms Lara.BHL.ReferenceAudit.modal_memory_encoding_counterexample
#print axioms Lara.BHL.ReferenceAudit.equality_threshold_not_monotone
#print axioms Lara.BHL.eventProbability_nonneg
#print axioms Lara.BHL.eventProbability_le_one
#print axioms Lara.BHL.eventProbability_empty
#print axioms Lara.BHL.eventProbability_univ
#print axioms Lara.BHL.eventProbability_mono
#print axioms Lara.BHL.eventProbability_union_le
#print axioms Lara.BHL.eventProbability_inter_le_min
#print axioms Lara.BHL.eventProbability_map
#print axioms Lara.BHL.NumericTest.measurable_tailEvent
#print axioms Lara.BHL.NumericTest.tailProbability_nonneg
#print axioms Lara.BHL.NumericTest.tailProbability_le_one
#print axioms Lara.BHL.NumericTest.tailProbability_mono
#print axioms Lara.BHL.ProbabilityCoupling.left_event
#print axioms Lara.BHL.ProbabilityCoupling.right_event
#print axioms Lara.BHL.ProbabilityCoupling.union_le
#print axioms Lara.BHL.ProbabilityCoupling.inter_le_min
#print axioms Lara.BHL.NumericTest.coupled_tail_union_le
#print axioms Lara.BHL.NumericTest.coupled_tail_inter_le_min
#print axioms Lara.BHL.eventProbability_dirac_of_mem
#print axioms Lara.BHL.eventProbability_dirac_of_notMem
#print axioms Lara.BHL.realDiracTest_inhabits
#print axioms Lara.BHL.realDiracTest_tailProbability_zero
#print axioms Lara.BHL.realDiracTest_tailProbability_one

#print axioms Lara.BHL.History.empty_count
#print axioms Lara.BHL.History.empty_eq_zero
#print axioms Lara.BHL.History.eq_iff_counts
#print axioms Lara.BHL.History.recordRepeated_count_other
#print axioms Lara.BHL.History.recordRepeated_count_self
#print axioms Lara.BHL.History.recordRepeated_succ
#print axioms Lara.BHL.History.recordRepeated_zero
#print axioms Lara.BHL.History.record_card
#print axioms Lara.BHL.History.record_comm
#print axioms Lara.BHL.History.record_count_other
#print axioms Lara.BHL.History.record_count_self
#print axioms Lara.BHL.History.record_ne_self
#print axioms Lara.BHL.History.record_preserves_entries
#print axioms Lara.BHL.History.record_strict
#print axioms Lara.BHL.Memory.assemble_projections
#print axioms Lara.BHL.Memory.ext
#print axioms Lara.BHL.Memory.hidden_assemble
#print axioms Lara.BHL.Memory.memory_update_typed
#print axioms Lara.BHL.Memory.observable_assemble
#print axioms Lara.BHL.Memory.read_empty
#print axioms Lara.BHL.Memory.read_rename
#print axioms Lara.BHL.Memory.read_update_invisible
#print axioms Lara.BHL.Memory.read_update_other
#print axioms Lara.BHL.Memory.read_update_self
#print axioms Lara.BHL.Memory.rename_binding_preserves
#print axioms Lara.BHL.Memory.rename_comp
#print axioms Lara.BHL.Memory.rename_empty
#print axioms Lara.BHL.Memory.rename_id
#print axioms Lara.BHL.Memory.rename_symm
#print axioms Lara.BHL.Memory.rename_update
#print axioms Lara.BHL.Memory.update_overwrite
#print axioms Lara.BHL.Model.accessible_equivalence
#print axioms Lara.BHL.Model.accessible_refl
#print axioms Lara.BHL.Model.accessible_symm
#print axioms Lara.BHL.Model.accessible_trans
#print axioms Lara.BHL.Model.validView_nonempty
#print axioms Lara.BHL.Model.validWorld_nonempty
#print axioms Lara.BHL.Model.viewOf_back
#print axioms Lara.BHL.Model.viewOf_forth
#print axioms Lara.BHL.Model.viewOf_surjective
#print axioms Lara.BHL.Model.view_accessible_back
#print axioms Lara.BHL.Model.view_accessible_forth
#print axioms Lara.BHL.ModelExamples.alias_count_one
#print axioms Lara.BHL.ModelExamples.alias_names_distinct
#print axioms Lara.BHL.ModelExamples.aliases_have_equal_values
#print axioms Lara.BHL.ModelExamples.different_histories
#print axioms Lara.BHL.ModelExamples.hidden_alternatives_accessible
#print axioms Lara.BHL.ModelExamples.hidden_alternatives_different
#print axioms Lara.BHL.ModelExamples.histories_initially_empty
#print axioms Lara.BHL.ModelExamples.initial_admitted
#print axioms Lara.BHL.ModelExamples.initial_has_defined_result
#print axioms Lara.BHL.ModelExamples.lawful_prefix
#print axioms Lara.BHL.ModelExamples.mathematical_carriers_defined
#print axioms Lara.BHL.ModelExamples.model_inhabited
#print axioms Lara.BHL.ModelExamples.reassignment_changes_lookup_not_ledger
#print axioms Lara.BHL.ModelExamples.recordSnapshot_admitted
#print axioms Lara.BHL.ModelExamples.repeated_admitted
#print axioms Lara.BHL.ModelExamples.repeated_combination_keeps_multiplicity
#print axioms Lara.BHL.ModelExamples.repeated_count_two
#print axioms Lara.BHL.ModelExamples.same_final_memory
#print axioms Lara.BHL.ModelExamples.same_memory_different_observations
#print axioms Lara.BHL.ModelExamples.single_admitted
#print axioms Lara.BHL.State.withHidden_hidden
#print axioms Lara.BHL.State.withHidden_history
#print axioms Lara.BHL.State.withHidden_visible
#print axioms Lara.BHL.Variable.rename_comp
#print axioms Lara.BHL.Variable.rename_id
#print axioms Lara.BHL.Variable.rename_symm
#print axioms Lara.BHL.World.extend_current
#print axioms Lara.BHL.World.extend_prefix
#print axioms Lara.BHL.World.extend_trace
#print axioms Lara.BHL.World.initial_history
#print axioms Lara.BHL.World.rebuildHidden_current
#print axioms Lara.BHL.World.rebuildHidden_current_hidden
#print axioms Lara.BHL.World.rebuildHidden_initial_hidden
#print axioms Lara.BHL.World.rebuildHidden_samplingProvenance
#print axioms Lara.BHL.World.rebuildHidden_trace
#print axioms Lara.BHL.World.samplingProvenance_extend_command
#print axioms Lara.BHL.World.samplingProvenance_extend_sample
#print axioms Lara.BHL.World.start_current
#print axioms Lara.BHL.World.trace_nonempty
#print axioms Lara.BHL.accessible_current_observation
#print axioms Lara.BHL.accessible_current_visible
#print axioms Lara.BHL.accessible_dataset_eq
#print axioms Lara.BHL.accessible_history_eq
#print axioms Lara.BHL.accessible_refl
#print axioms Lara.BHL.accessible_sampling_provenance
#print axioms Lara.BHL.accessible_symm
#print axioms Lara.BHL.accessible_trans
#print axioms Lara.BHL.accessible_visible_eq
#print axioms Lara.BHL.admitted_current_hidden
#print axioms Lara.BHL.admitted_current_hidden_binding
#print axioms Lara.BHL.admitted_extend
#print axioms Lara.BHL.admitted_hidden
#print axioms Lara.BHL.admitted_hidden_mem_compatible
#print axioms Lara.BHL.admitted_initial
#print axioms Lara.BHL.admitted_initial_hidden_mem_compatible
#print axioms Lara.BHL.admitted_prefix
#print axioms Lara.BHL.admitted_rebuildHidden_iff
#print axioms Lara.BHL.admitted_sample_transition
#print axioms Lara.BHL.admitted_start
#print axioms Lara.BHL.compatibleHidden_eq_of_accessible
#print axioms Lara.BHL.compatibleHidden_rebuildHidden
#print axioms Lara.BHL.constantHidden_binding
#print axioms Lara.BHL.constantHidden_current
#print axioms Lara.BHL.constantHidden_extend
#print axioms Lara.BHL.constantHidden_prefix
#print axioms Lara.BHL.constantHidden_rebuildHidden
#print axioms Lara.BHL.decompose_conj
#print axioms Lara.BHL.decompose_conj_assoc
#print axioms Lara.BHL.decompose_conj_comm
#print axioms Lara.BHL.decompose_count_conj
#print axioms Lara.BHL.decompose_count_disj
#print axioms Lara.BHL.decompose_count_leaf_self
#print axioms Lara.BHL.decompose_disj
#print axioms Lara.BHL.decompose_disj_assoc
#print axioms Lara.BHL.decompose_disj_comm
#print axioms Lara.BHL.decompose_leaf
#print axioms Lara.BHL.decompose_repeated_pair_conj
#print axioms Lara.BHL.decompose_repeated_pair_disj
#print axioms Lara.BHL.extend_accessible_iff
#print axioms Lara.BHL.history_count_alias
#print axioms Lara.BHL.history_count_lookup
#print axioms Lara.BHL.history_count_reassignment
#print axioms Lara.BHL.history_count_update_other
#print axioms Lara.BHL.history_count_update_self
#print axioms Lara.BHL.model_has_world
#print axioms Lara.BHL.observeState_withHidden
#print axioms Lara.BHL.observe_current
#print axioms Lara.BHL.observe_extend
#print axioms Lara.BHL.observe_rebuildHidden
#print axioms Lara.BHL.populationId_index_injective
#print axioms Lara.BHL.rebuildHidden_accessible
#print axioms Lara.BHL.semanticView_rebuildHidden
#print axioms Lara.BHL.traceEdges_append
#print axioms Lara.BHL.traceEdges_prefix
#print axioms Lara.BHL.traceEdges_sample
#print axioms Lara.BHL.traceEdges_take
#print axioms Lara.BHL.traceEdges_take_drop
#print axioms Lara.BHL.view_accessible_back
#print axioms Lara.BHL.view_accessible_equivalence
#print axioms Lara.BHL.view_accessible_forth
#print axioms Lara.BHL.view_accessible_refl
#print axioms Lara.BHL.view_accessible_symm
#print axioms Lara.BHL.view_accessible_trans
#print axioms Lara.BHL.measurable_list_coordinate
#print axioms Lara.BHL.value_population_carrier
#print axioms Lara.BHL.value_measurable_product
#print axioms Lara.BHL.value_population_mass
#print axioms Lara.BHL.value_nonempty
#print axioms Lara.BHL.ModelExamples.joint_list_boolean_laws_inhabit_memory
#print axioms Lara.BHL.ModelExamples.joint_law_normalized
#print axioms Lara.BHL.traceAllowed_extend
#print axioms Lara.BHL.compatibleHidden_extend_command

#print axioms Lara.BHL.GhostRenaming.id_apply
#print axioms Lara.BHL.GhostRenaming.comp_apply
#print axioms Lara.BHL.GhostRenaming.weaken_apply
#print axioms Lara.BHL.GhostRenaming.lift_here
#print axioms Lara.BHL.GhostRenaming.lift_there
#print axioms Lara.BHL.GhostRenaming.id_comp
#print axioms Lara.BHL.GhostRenaming.comp_id
#print axioms Lara.BHL.GhostRenaming.comp_assoc
#print axioms Lara.BHL.GhostRenaming.lift_id
#print axioms Lara.BHL.GhostRenaming.lift_comp
#print axioms Lara.BHL.GhostRenaming.weaken_comp_lift
#print axioms Lara.BHL.GhostEnv.lookup_push_here
#print axioms Lara.BHL.GhostEnv.lookup_push_there
#print axioms Lara.BHL.GhostEnv.ext
#print axioms Lara.BHL.GhostEnv.empty_unique
#print axioms Lara.BHL.GhostEnv.lookup_reindex
#print axioms Lara.BHL.GhostEnv.reindex_id
#print axioms Lara.BHL.GhostEnv.reindex_comp
#print axioms Lara.BHL.GhostEnv.reindex_weaken_push
#print axioms Lara.BHL.GhostEnv.reindex_lift_push
#print axioms Lara.BHL.GhostEnv.push_lookup_reindex
#print axioms Lara.BHL.GhostEnv.push_eq_push_iff
#print axioms Lara.BHL.NumericalEvent.probability_nonneg
#print axioms Lara.BHL.NumericalEvent.probability_le_one
#print axioms Lara.BHL.NumericalEvent.probability_mem_Icc
#print axioms Lara.BHL.NumericalEvent.tail_law
#print axioms Lara.BHL.NumericalEvent.tail_event
#print axioms Lara.BHL.NumericalEvent.mem_tail_event
#print axioms Lara.BHL.NumericalEvent.tail_measurableEvent
#print axioms Lara.BHL.NumericalEvent.tail_probability
#print axioms Lara.BHL.NumericalEvent.union_law
#print axioms Lara.BHL.NumericalEvent.intersection_law
#print axioms Lara.BHL.NumericalEvent.union_event
#print axioms Lara.BHL.NumericalEvent.intersection_event
#print axioms Lara.BHL.NumericalEvent.mem_union_event
#print axioms Lara.BHL.NumericalEvent.mem_intersection_event
#print axioms Lara.BHL.NumericalEvent.union_measurableEvent
#print axioms Lara.BHL.NumericalEvent.intersection_measurableEvent
#print axioms Lara.BHL.NumericalEvent.left_lift_probability
#print axioms Lara.BHL.NumericalEvent.right_lift_probability
#print axioms Lara.BHL.NumericalEvent.union_probability_le
#print axioms Lara.BHL.NumericalEvent.intersection_probability_le_min
#print axioms Lara.BHL.semanticView_mem_views
#print axioms Lara.BHL.reference_view_modal_correspondence
#print axioms Lara.BHL.reference_view_assertion_correspondence
#print axioms Lara.BHL.satisfies_view_iff
#print axioms Lara.BHL.satisfies_congr
#print axioms Lara.BHL.know_truth
#print axioms Lara.BHL.know_distribution
#print axioms Lara.BHL.knows_mono
#print axioms Lara.BHL.knows_congr
#print axioms Lara.BHL.knows_invariant
#print axioms Lara.BHL.know_positive_introspection
#print axioms Lara.BHL.know_negative_introspection
#print axioms Lara.BHL.possible_iff_exists
#print axioms Lara.BHL.possible_mono
#print axioms Lara.BHL.possible_congr
#print axioms Lara.BHL.possible_invariant
#print axioms Lara.BHL.possible_known
#print axioms Lara.BHL.know_possible_iff
#print axioms Lara.BHL.possible_know_iff
#print axioms Lara.BHL.referenceModalSatisfaction_disj
#print axioms Lara.BHL.referenceModalSatisfaction_implies
#print axioms Lara.BHL.referenceModalSatisfaction_possible
#print axioms Lara.BHL.viewModalSatisfaction_disj
#print axioms Lara.BHL.viewModalSatisfaction_implies
#print axioms Lara.BHL.referenceAssertionSatisfaction_disj
#print axioms Lara.BHL.referenceAssertionSatisfaction_implies
#print axioms Lara.BHL.referenceAssertionSatisfaction_exists
#print axioms Lara.BHL.viewAssertionSatisfaction_disj
#print axioms Lara.BHL.viewAssertionSatisfaction_implies
#print axioms Lara.BHL.viewAssertionSatisfaction_exists
#print axioms Lara.BHL.GhostTerm.renameGhosts_id
#print axioms Lara.BHL.GhostTerm.renameGhosts_comp
#print axioms Lara.BHL.GhostSubstitution.lift_here
#print axioms Lara.BHL.GhostSubstitution.lift_there
#print axioms Lara.BHL.GhostSubstitution.lift_id
#print axioms Lara.BHL.GhostSubstitution.lift_ofRenaming
#print axioms Lara.BHL.GhostTerm.substituteGhosts_id
#print axioms Lara.BHL.GhostTerm.substituteGhosts_comp
#print axioms Lara.BHL.GhostTerm.renameGhosts_eq_substituteGhosts
#print axioms Lara.BHL.GhostTerm.weaken_substitute_lift
#print axioms Lara.BHL.GhostSubstitution.id_comp
#print axioms Lara.BHL.GhostSubstitution.comp_id
#print axioms Lara.BHL.GhostSubstitution.comp_assoc
#print axioms Lara.BHL.GhostSubstitution.lift_comp
#print axioms Lara.BHL.AssertionTerm.renameGhosts_id
#print axioms Lara.BHL.ValueArguments.renameGhosts_id
#print axioms Lara.BHL.TestExpression.renameGhosts_id
#print axioms Lara.BHL.AssertionAtom.renameGhosts_id
#print axioms Lara.BHL.ModalFormula.renameGhosts_id
#print axioms Lara.BHL.Assertion.renameGhosts_id
#print axioms Lara.BHL.AssertionTerm.renameGhosts_comp
#print axioms Lara.BHL.ValueArguments.renameGhosts_comp
#print axioms Lara.BHL.TestExpression.renameGhosts_comp
#print axioms Lara.BHL.AssertionAtom.renameGhosts_comp
#print axioms Lara.BHL.ModalFormula.renameGhosts_comp
#print axioms Lara.BHL.Assertion.renameGhosts_comp
#print axioms Lara.BHL.AssertionTerm.substituteGhosts_id
#print axioms Lara.BHL.ValueArguments.substituteGhosts_id
#print axioms Lara.BHL.TestExpression.substituteGhosts_id
#print axioms Lara.BHL.AssertionAtom.substituteGhosts_id
#print axioms Lara.BHL.ModalFormula.substituteGhosts_id
#print axioms Lara.BHL.Assertion.substituteGhosts_id
#print axioms Lara.BHL.AssertionTerm.substituteGhosts_comp
#print axioms Lara.BHL.ValueArguments.substituteGhosts_comp
#print axioms Lara.BHL.TestExpression.substituteGhosts_comp
#print axioms Lara.BHL.AssertionAtom.substituteGhosts_comp
#print axioms Lara.BHL.ModalFormula.substituteGhosts_comp
#print axioms Lara.BHL.Assertion.substituteGhosts_comp
#print axioms Lara.BHL.AssertionTerm.renameGhosts_eq_substituteGhosts
#print axioms Lara.BHL.ValueArguments.renameGhosts_eq_substituteGhosts
#print axioms Lara.BHL.TestExpression.renameGhosts_eq_substituteGhosts
#print axioms Lara.BHL.AssertionAtom.renameGhosts_eq_substituteGhosts
#print axioms Lara.BHL.ModalFormula.renameGhosts_eq_substituteGhosts
#print axioms Lara.BHL.Assertion.renameGhosts_eq_substituteGhosts
#print axioms Lara.BHL.mem_dischargeGhosts_of_there
#print axioms Lara.BHL.GhostSubstitution.Fixes.append_left
#print axioms Lara.BHL.GhostSubstitution.Fixes.append_right
#print axioms Lara.BHL.GhostSubstitution.Fixes.lift
#print axioms Lara.BHL.GhostTerm.substituteGhosts_of_fixes
#print axioms Lara.BHL.AssertionTerm.substituteGhosts_of_fixes
#print axioms Lara.BHL.ValueArguments.substituteGhosts_of_fixes
#print axioms Lara.BHL.TestExpression.substituteGhosts_of_fixes
#print axioms Lara.BHL.AssertionAtom.substituteGhosts_of_fixes
#print axioms Lara.BHL.ModalFormula.substituteGhosts_of_fixes
#print axioms Lara.BHL.Assertion.substituteGhosts_of_fixes
#print axioms Lara.BHL.GhostTerm.eval_renameGhosts
#print axioms Lara.BHL.GhostTerm.eval_substituteGhosts
#print axioms Lara.BHL.substitutionEnv_id
#print axioms Lara.BHL.substitutionEnv_ofRenaming
#print axioms Lara.BHL.substitutionEnv_comp
#print axioms Lara.BHL.substitutionEnv_lift_push
#print axioms Lara.BHL.substitutionEnv_lift
#print axioms Lara.BHL.evalTerm_substituteGhosts
#print axioms Lara.BHL.evalArguments_substituteGhosts
#print axioms Lara.BHL.evalNumericalEvent_substituteGhosts
#print axioms Lara.BHL.evalTestEntries_substituteGhosts
#print axioms Lara.BHL.evalTestHistory_substituteGhosts
#print axioms Lara.BHL.modelRequirements_substituteGhosts
#print axioms Lara.BHL.atomMeaning_substituteGhosts
#print axioms Lara.BHL.viewModalSatisfaction_substituteGhosts
#print axioms Lara.BHL.viewAssertionSatisfaction_substituteGhosts
#print axioms Lara.BHL.referenceModalSatisfaction_substituteGhosts
#print axioms Lara.BHL.referenceAssertionSatisfaction_substituteGhosts
#print axioms Lara.BHL.satisfies_substituteGhosts
#print axioms Lara.BHL.satisfiesView_substituteGhosts
#print axioms Lara.BHL.evalTerm_renameGhosts
#print axioms Lara.BHL.evalArguments_renameGhosts
#print axioms Lara.BHL.evalNumericalEvent_renameGhosts
#print axioms Lara.BHL.atomMeaning_renameGhosts
#print axioms Lara.BHL.viewModalSatisfaction_renameGhosts
#print axioms Lara.BHL.referenceModalSatisfaction_renameGhosts
#print axioms Lara.BHL.viewAssertionSatisfaction_renameGhosts
#print axioms Lara.BHL.referenceAssertionSatisfaction_renameGhosts
#print axioms Lara.BHL.satisfies_renameGhosts
#print axioms Lara.BHL.satisfiesView_renameGhosts
#print axioms Lara.BHL.view_liberalPreimage_iff
#print axioms Lara.BHL.reference_liberalPreimage_iff
#print axioms Lara.BHL.liberalPreimage_undefined
#print axioms Lara.BHL.liberalPreimage_successor_iff
#print axioms Lara.BHL.eval_assignmentView
#print axioms Lara.BHL.eval_datasetAssignmentView
#print axioms Lara.BHL.eval_simultaneous_fold
#print axioms Lara.BHL.eval_simultaneousAssignmentView
#print axioms Lara.BHL.simultaneous_writes_preserve_information
#print axioms Lara.BHL.eval_testAssignmentView
#print axioms Lara.BHL.command_successor_admitted
#print axioms Lara.BHL.command_successor_view
#print axioms Lara.BHL.hidden_observable_write
#print axioms Lara.BHL.assignmentState_hidden
#print axioms Lara.BHL.testState_hidden
#print axioms Lara.BHL.assignment_successor_view
#print axioms Lara.BHL.test_successor_view
#print axioms Lara.BHL.assignment_preimage_iff
#print axioms Lara.BHL.test_preimage_iff
#print axioms Lara.BHL.commandState_visible
#print axioms Lara.BHL.commandState_hidden
#print axioms Lara.BHL.simultaneous_assignment_preimage_iff
#print axioms Lara.BHL.observationInvariant_ghost
#print axioms Lara.BHL.observationInvariant_datasetRead
#print axioms Lara.BHL.fixedRealTerm_ghost
#print axioms Lara.BHL.fixedRealTerm_rational
#print axioms Lara.BHL.observableTest_entries_invariant
#print axioms Lara.BHL.observableTest_history_invariant
#print axioms Lara.BHL.observableTest_event_invariant
#print axioms Lara.BHL.observationInvariant_pvalue
#print axioms Lara.BHL.evalTestHistory_leaf
#print axioms Lara.BHL.evalTestHistory_disj
#print axioms Lara.BHL.evalTestHistory_conj
#print axioms Lara.BHL.eval_testHistoryTerm
#print axioms Lara.BHL.exactHistory_iff_ledger
#print axioms Lara.BHL.exactHistory_disj_iff
#print axioms Lara.BHL.exactHistory_conj_iff
#print axioms Lara.BHL.evalNumericalEvent_disj_of_coupling
#print axioms Lara.BHL.evalNumericalEvent_conj_of_coupling
#print axioms Lara.BHL.exactHistory_iff_entries
#print axioms Lara.BHL.evalTestHistory_repeated_disj
#print axioms Lara.BHL.evalTestHistory_repeated_conj
#print axioms Lara.BHL.exactHistory_repeated_leaf_card
#print axioms Lara.BHL.prior_total_alternative_or_null
#print axioms Lara.BHL.prior_exclude_lower_iff_upper_or_null
#print axioms Lara.BHL.prior_exclude_upper_iff_lower_or_null
#print axioms Lara.BHL.statisticalBelief_unfold
#print axioms Lara.BHL.belief_invariant
#print axioms Lara.BHL.belief_positive_introspection
#print axioms Lara.BHL.belief_negative_introspection
#print axioms Lara.BHL.belief_possibility_known
#print axioms Lara.BHL.belief_possibility_negative_introspection
#print axioms Lara.BHL.knowledge_implies_statistical_belief
#print axioms Lara.BHL.pvalue_atom_fixed_iff
#print axioms Lara.BHL.pvalue_atom_undefined
#print axioms Lara.BHL.pvalue_atom_threshold_undefined
#print axioms Lara.BHL.belief_of_pvalue_implication
#print axioms Lara.BHL.belief_le_mono
#print axioms Lara.BHL.belief_lt_mono
#print axioms Lara.BHL.belief_eq_to_le
#print axioms Lara.BHL.belief_le_possibility_antitone
#print axioms Lara.BHL.belief_lt_possibility_antitone
#print axioms Lara.BHL.belief_eq_possibility_of_le
#print axioms Lara.BHL.exactHistory_invariant
#print axioms Lara.BHL.exactHistory_known
#print axioms Lara.BHL.exactHistory_known_iff
#print axioms Lara.BHL.exactHistory_possible_iff
#print axioms Lara.BHL.pvalue_atom_self
#print axioms Lara.BHL.belief_from_exact_test_history
#print axioms Lara.BHL.belief_from_exact_history_fixed_bound
#print axioms Lara.BHL.belief_from_observable_exception
#print axioms Lara.BHL.belief_combined_disj
#print axioms Lara.BHL.belief_combined_conj
#print axioms Lara.BHL.belief_combined_disj_fixed
#print axioms Lara.BHL.belief_combined_conj_fixed
#print axioms Lara.BHL.belief_from_exact_leaf_history
#print axioms Lara.BHL.modelRequirements_leaf_undefined
#print axioms Lara.BHL.modelRequirements_leaf_defined_iff
#print axioms Lara.BHL.undefined_numerical_binding_not_belief
#print axioms Lara.BHL.SupportAgreement.append_iff
#print axioms Lara.BHL.SupportAgreement.append_left
#print axioms Lara.BHL.SupportAgreement.append_right
#print axioms Lara.BHL.SupportAgreement.visible_eq
#print axioms Lara.BHL.SupportAgreement.view_eq
#print axioms Lara.BHL.readSupport_valueRead_ambient
#print axioms Lara.BHL.readSupport_datasetRead_ambient
#print axioms Lara.BHL.readSupport_visibleOf_ambient
#print axioms Lara.BHL.readSupport_hiddenOf_ambient
#print axioms Lara.BHL.readSupport_historyOf_ambient
#print axioms Lara.BHL.readSupport_provenanceOf_ambient
#print axioms Lara.BHL.readSupport_compatibleOf_ambient
#print axioms Lara.BHL.readSupport_visibleOf_covers_variable
#print axioms Lara.BHL.readSupport_visibleOf_covers_dataset
#print axioms Lara.BHL.readSupport_hiddenOf_covers_variable
#print axioms Lara.BHL.wholeVisibleRegression_readSupport
#print axioms Lara.BHL.wholeVisibleRegression_covers_variable
#print axioms Lara.BHL.wholeVisibleRegression_covers_dataset
#print axioms Lara.BHL.wholeHiddenRegression_readSupport
#print axioms Lara.BHL.wholeHiddenRegression_covers_variable
#print axioms Lara.BHL.readSupport_writeValue
#print axioms Lara.BHL.readSupport_writeDataset
#print axioms Lara.BHL.readSupport_addHistory
#print axioms Lara.BHL.readSupport_currentView_ghost
#print axioms Lara.BHL.readSupport_worldTrace_ghost
#print axioms Lara.BHL.writeViewValue_visible_ne
#print axioms Lara.BHL.wholeVisibleRegression_zero_to_one
#print axioms Lara.BHL.evalTerm_structural_frame
#print axioms Lara.BHL.evalTerm_currentView_ghost_fixed
#print axioms Lara.BHL.evalTerm_worldTrace_ghost_fixed
#print axioms Lara.Examples.BHLBelief.hiddenMemory_parameter
#print axioms Lara.Examples.BHLBelief.hiddenMemory_false_ne_true
#print axioms Lara.Examples.BHLBelief.constantTest_pvalue_zero
#print axioms Lara.Examples.BHLBelief.constantTest_pvalue_one
#print axioms Lara.Examples.BHLBelief.testFor_pvalue
#print axioms Lara.Examples.BHLBelief.population_statistic_law
#print axioms Lara.Examples.BHLBelief.dirac_zero_ne_one
#print axioms Lara.Examples.BHLBelief.lawBinding_iff
#print axioms Lara.Examples.BHLBelief.chosenId_wrong
#print axioms Lara.Examples.BHLBelief.startWorld_admitted
#print axioms Lara.Examples.BHLBelief.sampledWorld_admitted
#print axioms Lara.Examples.BHLBelief.testState_admitted
#print axioms Lara.Examples.BHLBelief.testedWorld_admitted
#print axioms Lara.Examples.BHLBelief.fixtureWorld_admitted
#print axioms Lara.Examples.BHLBelief.fixtureWorld_hidden
#print axioms Lara.Examples.BHLBelief.fixtureWorld_data
#print axioms Lara.Examples.BHLBelief.fixtureWorld_history
#print axioms Lara.Examples.BHLBelief.fixtureWorld_provenance
#print axioms Lara.Examples.BHLBelief.fixtureWorld_report
#print axioms Lara.Examples.BHLBelief.fixtureWorld_accessible
#print axioms Lara.Examples.BHLBelief.fixtureWorld_compatible
#print axioms Lara.Examples.BHLBelief.fixture_rebuild_closure
#print axioms Lara.Examples.BHLBelief.fixtureView_mem
#print axioms Lara.Examples.BHLBelief.fixtureView_accessible
#print axioms Lara.Examples.BHLBelief.fixtureView_false_ne_true
#print axioms Lara.Examples.BHLBelief.fixtureView_enumeration
#print axioms Lara.Examples.BHLBelief.datasetTerm_evaluation
#print axioms Lara.Examples.BHLBelief.pvalue_evaluation
#print axioms Lara.Examples.BHLBelief.report_evaluation
#print axioms Lara.Examples.BHLBelief.alternative_meaning
#print axioms Lara.Examples.BHLBelief.requirements_meaning
#print axioms Lara.Examples.BHLBelief.fixtureLedger_exact
#print axioms Lara.Examples.BHLBelief.exactHistory_meaning
#print axioms Lara.Examples.BHLBelief.pvalue_meaning
#print axioms Lara.Examples.BHLBelief.view_conj_iff
#print axioms Lara.Examples.BHLBelief.view_neg_iff
#print axioms Lara.Examples.BHLBelief.exception_meaning
#print axioms Lara.Examples.BHLBelief.fixture_knows
#print axioms Lara.Examples.BHLBelief.belief_meaning
#print axioms Lara.Examples.BHLBelief.exceptional_belief_false_alternative
#print axioms Lara.Examples.BHLBelief.model_failure_only_at_zero
#print axioms Lara.Examples.BHLBelief.exception_requirements_hold
#print axioms Lara.Examples.BHLBelief.exception_only_branch
#print axioms Lara.Examples.BHLBelief.equality_nonmonotone
#print axioms Lara.Examples.BHLBelief.unchanged_report_extra_ledger
#print axioms Lara.Examples.BHLBelief.hidden_alternative_nonidentifiable
#print axioms Lara.Examples.BHLBelief.quote_witnessBelief
#print axioms Lara.Examples.BHLBelief.finitePvalue_one
#print axioms Lara.Examples.BHLBelief.compareRational_correspondence
#print axioms Lara.Examples.BHLBelief.evaluateAtom_correspondence
#print axioms Lara.Examples.BHLBelief.evaluate_correspondence
#print axioms Lara.Examples.BHLBelief.evaluate_satisfies_correspondence
#print axioms Lara.Examples.BHLBelief.executable_exception_certificate
#print axioms Lara.Examples.BHLBelief.executable_failure_certificate
#print axioms Lara.Examples.BHLBelief.nested_knowledge_view_reevaluation
#print axioms Lara.Examples.BHLBelief.captureSubstitution_environment
#print axioms Lara.Examples.BHLBelief.scopedCaptureExample_correct
#print axioms Lara.Examples.BHLBelief.scopedCapture_distinct_bindings

/-! ### BHL observable program execution and finite control -/

#print axioms Lara.BHL.Step.source_some
#print axioms Lara.BHL.Step.terminal_impossible
#print axioms Lara.BHL.Steps.zero_iff
#print axioms Lara.BHL.Steps.terminal_iff
#print axioms Lara.BHL.Run.refl
#print axioms Lara.BHL.Run.terminal_iff
#print axioms Lara.BHL.ProgramCell.Agrees.refl
#print axioms Lara.BHL.ProgramCell.Agrees.symm
#print axioms Lara.BHL.ProgramCell.Agrees.trans
#print axioms Lara.BHL.ProgramAgreement.refl
#print axioms Lara.BHL.ProgramAgreement.symm
#print axioms Lara.BHL.ProgramAgreement.trans
#print axioms Lara.BHL.ProgramAgreement.nil
#print axioms Lara.BHL.ProgramAgreement.append_iff
#print axioms Lara.BHL.ProgramAgreement.append_left
#print axioms Lara.BHL.ProgramAgreement.append_right
#print axioms Lara.BHL.ProgramAgreement.mono
#print axioms Lara.BHL.ProgramAgreement.visible_eq
#print axioms Lara.BHL.ProgramFrame.refl
#print axioms Lara.BHL.ProgramFrame.symm
#print axioms Lara.BHL.ProgramFrame.trans
#print axioms Lara.BHL.ProgramFrame.agreement
#print axioms Lara.BHL.evalProgramExpr_congr
#print axioms Lara.BHL.evalProgramArgs_congr
#print axioms Lara.BHL.evalDatasetExpr_congr
#print axioms Lara.BHL.evalTerm_toProgramExpr
#print axioms Lara.BHL.evalArguments_toProgramArgs
#print axioms Lara.BHL.evalTerm_toDatasetExpr
#print axioms Lara.BHL.observable_update_assemble_independent
#print axioms Lara.BHL.VisibleWrite.apply_value_visible
#print axioms Lara.BHL.VisibleWrite.apply_value_self
#print axioms Lara.BHL.VisibleWrite.apply_value_datasets
#print axioms Lara.BHL.VisibleWrite.apply_dataset_memory
#print axioms Lara.BHL.VisibleWrite.apply_dataset_self
#print axioms Lara.BHL.VisibleWrite.apply_frame
#print axioms Lara.BHL.VisibleWrite.apply_agrees
#print axioms Lara.BHL.VisibleWrite.apply_agreement
#print axioms Lara.BHL.evalPrimitive_viewTerm
#print axioms Lara.BHL.evalPrimitive_congr
#print axioms Lara.BHL.evalPrimitive_cells
#print axioms Lara.BHL.primitiveEffect_frame
#print axioms Lara.BHL.evalPrimitive_skip
#print axioms Lara.BHL.evalPrimitive_assign
#print axioms Lara.BHL.evalPrimitive_assignDataset
#print axioms Lara.BHL.evalPrimitive_test
#print axioms Lara.BHL.evalPrimitive_assign_enabled
#print axioms Lara.BHL.evalPrimitive_assignDataset_enabled
#print axioms Lara.BHL.evalPrimitive_test_enabled
#print axioms Lara.BHL.evalPrimitive_assign_pvalue
#print axioms Lara.BHL.evalPrimitive_assign_none_iff
#print axioms Lara.BHL.evalPrimitive_assignDataset_none_iff
#print axioms Lara.BHL.evalPrimitive_test_none_iff
#print axioms Lara.BHL.primitiveEffect_skip
#print axioms Lara.BHL.primitiveEffect_assign
#print axioms Lara.BHL.primitiveEffect_assignDataset
#print axioms Lara.BHL.primitiveEffect_test
#print axioms Lara.BHL.primitiveEffect_none_iff
#print axioms Lara.BHL.primitiveEffect_agreement
#print axioms Lara.BHL.evalPrimitive_viewTerm_enabled
#print axioms Lara.BHL.primitive_viewTerm_preserves_information
#print axioms Lara.BHL.ProgramContext.ofRelations_interpretation
#print axioms Lara.BHL.ProgramContext.ofRelations_initial
#print axioms Lara.BHL.ProgramContext.ofRelations_sampling
#print axioms Lara.BHL.ProgramContext.ofRelations_command
#print axioms Lara.BHL.ProgramContext.ofRelations_binding
#print axioms Lara.BHL.ProgramContext.ofRelations_has_world
#print axioms Lara.BHL.ProgramContext.ofRelations_validWorld_nonempty
#print axioms Lara.BHL.noninterferingCheck_iff
#print axioms Lara.BHL.Program.wellFormedCheck_iff
#print axioms Lara.BHL.Noninterfering.symm
#print axioms Lara.BHL.Noninterfering.mono_left
#print axioms Lara.BHL.Noninterfering.mono_right
#print axioms Lara.BHL.Noninterfering.mono
#print axioms Lara.BHL.Noninterfering.writes_not_reads
#print axioms Lara.BHL.Noninterfering.writes_not_writes
#print axioms Lara.BHL.Noninterfering.seq_left
#print axioms Lara.BHL.Noninterfering.seq_right
#print axioms Lara.BHL.Noninterfering.par_left
#print axioms Lara.BHL.Noninterfering.par_right
#print axioms Lara.BHL.Noninterfering.ite_left
#print axioms Lara.BHL.Noninterfering.ite_right
#print axioms Lara.BHL.Noninterfering.loop_body
#print axioms Lara.BHL.Step.command_iff
#print axioms Lara.BHL.Step.seq_iff
#print axioms Lara.BHL.Step.ite_iff
#print axioms Lara.BHL.Step.loop_iff
#print axioms Lara.BHL.Step.par_iff
#print axioms Lara.BHL.Step.seq_lift
#print axioms Lara.BHL.Step.par_left_lift
#print axioms Lara.BHL.Step.par_right_lift
#print axioms Lara.BHL.Steps.trans
#print axioms Lara.BHL.Steps.one_iff
#print axioms Lara.BHL.Steps.succ_iff
#print axioms Lara.BHL.Steps.seq_lift
#print axioms Lara.BHL.Steps.par_left_lift
#print axioms Lara.BHL.Steps.par_right_lift
#print axioms Lara.BHL.Steps.command_iff
#print axioms Lara.BHL.Steps.seq_iff
#print axioms Lara.BHL.Steps.seq_to_parallel
#print axioms Lara.BHL.Run.single
#print axioms Lara.BHL.Run.trans
#print axioms Lara.BHL.Run.first_iff
#print axioms Lara.BHL.Run.seq_lift
#print axioms Lara.BHL.Run.par_left_lift
#print axioms Lara.BHL.Run.par_right_lift
#print axioms Lara.BHL.step_command_iff
#print axioms Lara.BHL.run_command_iff
#print axioms Lara.BHL.steps_skip_iff
#print axioms Lara.BHL.run_skip_iff
#print axioms Lara.BHL.exec_skip_iff
#print axioms Lara.BHL.run_seq_iff
#print axioms Lara.BHL.run_ite_iff
#print axioms Lara.BHL.run_ite_undefined
#print axioms Lara.BHL.run_loop_unfold_iff
#print axioms Lara.BHL.Steps.loop_finite_iterations
#print axioms Lara.BHL.FiniteLoopIterations.run
#print axioms Lara.BHL.run_loop_finite_iterations_iff
#print axioms Lara.BHL.exec_loop_finite_iterations
#print axioms Lara.BHL.primitiveEffect_delta_shape
#print axioms Lara.BHL.primitiveEffect_pure_delta
#print axioms Lara.BHL.Step.actual_effect
#print axioms Lara.BHL.Step.admitted
#print axioms Lara.BHL.Step.information
#print axioms Lara.BHL.Step.hidden
#print axioms Lara.BHL.Step.compatible_hidden
#print axioms Lara.BHL.Step.sampling_provenance
#print axioms Lara.BHL.Step.trace_prefix
#print axioms Lara.BHL.Step.ledger_delta
#print axioms Lara.BHL.Steps.admitted
#print axioms Lara.BHL.Steps.information
#print axioms Lara.BHL.Steps.ledger_delta
#print axioms Lara.BHL.Run.admitted
#print axioms Lara.BHL.Run.information
#print axioms Lara.BHL.Run.hidden
#print axioms Lara.BHL.Run.compatible_hidden
#print axioms Lara.BHL.Run.sampling_provenance
#print axioms Lara.BHL.Run.trace_prefix
#print axioms Lara.BHL.Run.ledger_delta
#print axioms Lara.BHL.exec_admitted
#print axioms Lara.BHL.exec_seq_iff
#print axioms Lara.BHL.exec_ite_iff
#print axioms Lara.BHL.run_seq_to_parallel
#print axioms Lara.BHL.exec_seq_to_parallel
#print axioms Lara.BHL.primitiveEffect_test_iff
#print axioms Lara.BHL.test_step_effect
#print axioms Lara.BHL.test_step_report
#print axioms Lara.BHL.test_step_multiplicity
#print axioms Lara.BHL.run_skip_not_identity
#print axioms Lara.BHL.visibleWrite_value_typed
#print axioms Lara.BHL.admitted_eq_of_accessible_hidden
#print axioms Lara.BHL.command_accessible_forth
#print axioms Lara.BHL.command_accessible_back
#print axioms Lara.BHL.Steps.terminating_pos
#print axioms Lara.BHL.Steps.ite_iff
#print axioms Lara.BHL.Steps.loop_unfold_iff
#print axioms Lara.BHL.exec_loop_unfold_iff
#print axioms Lara.BHL.Program.mem_residuals
#print axioms Lara.BHL.Program.residuals_closed
#print axioms Lara.BHL.Program.source_mem_controlNodes
#print axioms Lara.BHL.Program.terminal_mem_controlNodes
#print axioms Lara.BHL.Step.control_edge
#print axioms Lara.BHL.Program.control_edge_step
#print axioms Lara.BHL.Step.control_edge_iff
#print axioms Lara.BHL.Program.some_mem_controlNodes
#print axioms Lara.BHL.Program.control_edge_target
#print axioms Lara.BHL.Step.controlNodes_closed
#print axioms Lara.BHL.Steps.controlNodes_closed

/-! ### BHL exact interleaving replay and actual execution witnesses -/

#print axioms Lara.BHL.ResidualBound.initial
#print axioms Lara.BHL.ResidualBound.terminal
#print axioms Lara.BHL.Step.support_mono
#print axioms Lara.BHL.Step.residual_bound
#print axioms Lara.BHL.Steps.support_mono
#print axioms Lara.BHL.Noninterfering.left_read
#print axioms Lara.BHL.Noninterfering.right_read
#print axioms Lara.BHL.Noninterfering.left_write
#print axioms Lara.BHL.Noninterfering.residual_mono
#print axioms Lara.BHL.Step.wellFormed
#print axioms Lara.BHL.Steps.wellFormed
#print axioms Lara.BHL.SourceEffect.apply_visible
#print axioms Lara.BHL.SourceEffect.apply_history
#print axioms Lara.BHL.SourceEffect.apply_agrees
#print axioms Lara.BHL.SourceEffect.apply_frame
#print axioms Lara.BHL.SourceEffect.accessible
#print axioms Lara.BHL.EffectOrigin.reads_mono
#print axioms Lara.BHL.EffectOrigin.valid_congr
#print axioms Lara.BHL.EffectOrigin.reference
#print axioms Lara.BHL.EffectOrigin.writes_mono
#print axioms Lara.BHL.Step.recorded_effect
#print axioms Lara.BHL.Step.effect_origin_iff
#print axioms Lara.BHL.VisibleWrite.apply_commute
#print axioms Lara.BHL.primitive_read_enabledness
#print axioms Lara.BHL.primitive_actual_payload_commute
#print axioms Lara.BHL.step_effect_replay_origin
#print axioms Lara.BHL.step_effect_replay
#print axioms Lara.BHL.Step.frame
#print axioms Lara.BHL.Step.target_enabled_iff
#print axioms Lara.BHL.Steps.frame
#print axioms Lara.BHL.MatchedSteps.left
#print axioms Lara.BHL.MatchedSteps.right
#print axioms Lara.BHL.MatchedSteps.agreement
#print axioms Lara.BHL.MatchedSteps.ledger
#print axioms Lara.BHL.MatchedSteps.accessible
#print axioms Lara.BHL.Steps.replay
#print axioms Lara.BHL.Steps.accessible_forth
#print axioms Lara.BHL.Steps.accessible_back
#print axioms Lara.BHL.PairedStep.reference
#print axioms Lara.BHL.PairedStep.of_reference
#print axioms Lara.BHL.PairedStep.reference_iff
#print axioms Lara.BHL.PairedSteps.reference
#print axioms Lara.BHL.PairedSteps.terminal_iff
#print axioms Lara.BHL.Steps.paired
#print axioms Lara.BHL.Steps.parallel_paired_iff
#print axioms Lara.BHL.Steps.paired_iff
#print axioms Lara.BHL.ProjectedSchedule.paired
#print axioms Lara.BHL.ProjectedSchedule.left_steps
#print axioms Lara.BHL.ProjectedSchedule.right_steps
#print axioms Lara.BHL.ParallelMerge.refl
#print axioms Lara.BHL.ParallelMerge.left_apply
#print axioms Lara.BHL.ParallelMerge.right_apply
#print axioms Lara.BHL.PairedSteps.project
#print axioms Lara.BHL.parallel_project
#print axioms Lara.BHL.parallel_sequential_representative
#print axioms Lara.BHL.sequential_parallel_recombine
#print axioms Lara.BHL.parallel_recombine
#print axioms Lara.BHL.parallel_terminates_iff
#print axioms Lara.BHL.semanticView_endpoint_fields
#print axioms Lara.BHL.exec_parallel_correspondence
#print axioms Lara.BHL.exec_parallel_project
#print axioms Lara.BHL.exec_parallel_terminates_iff
#print axioms Lara.BHL.parallel_assertion_correspondence
#print axioms Lara.BHL.parallel_satisfying_execution_iff
#print axioms Lara.BHL.endpoint_hidden_replay
#print axioms Lara.BHL.correspondence_epistemic_forth
#print axioms Lara.BHL.correspondence_epistemic_back
#print axioms Lara.BHL.parallel_endpoint_epistemic_forth
#print axioms Lara.BHL.parallel_endpoint_epistemic_back
#print axioms Lara.Examples.BHLExecution.good_ni
#print axioms Lara.Examples.BHLExecution.bad_ni
#print axioms Lara.Examples.BHLExecution.good_ni_computes
#print axioms Lara.Examples.BHLExecution.bad_ni_computes
#print axioms Lara.Examples.BHLExecution.exact_dirac_pvalue
#print axioms Lara.Examples.BHLExecution.start_admitted
#print axioms Lara.Examples.BHLExecution.start_reifies
#print axioms Lara.Examples.BHLExecution.integer_correspondence
#print axioms Lara.Examples.BHLExecution.guard_correspondence
#print axioms Lara.Examples.BHLExecution.command_correspondence
#print axioms Lara.Examples.BHLExecution.next_correspondence
#print axioms Lara.Examples.BHLExecution.scheduled_correspondence
#print axioms Lara.Examples.BHLExecution.sampled_admitted
#print axioms Lara.Examples.BHLExecution.sampled_reifies
#print axioms Lara.Examples.BHLExecution.sampled_hidden_distinct
#print axioms Lara.Examples.BHLExecution.sampled_accessible
#print axioms Lara.Examples.BHLExecution.loop_computes
#print axioms Lara.Examples.BHLExecution.loop_seven_steps
#print axioms Lara.Examples.BHLExecution.loop_executes
#print axioms Lara.Examples.BHLExecution.loop_final_x
#print axioms Lara.Examples.BHLExecution.loop_three_command_states
#print axioms Lara.Examples.BHLExecution.left_computes
#print axioms Lara.Examples.BHLExecution.right_computes
#print axioms Lara.Examples.BHLExecution.left_steps
#print axioms Lara.Examples.BHLExecution.right_steps
#print axioms Lara.Examples.BHLExecution.left_executes
#print axioms Lara.Examples.BHLExecution.right_executes
#print axioms Lara.Examples.BHLExecution.parallel_visible
#print axioms Lara.Examples.BHLExecution.parallel_semantic_view
#print axioms Lara.Examples.BHLExecution.parallel_order_differs
#print axioms Lara.Examples.BHLExecution.parallel_complete_traces_differ
#print axioms Lara.Examples.BHLExecution.repeated_computes
#print axioms Lara.Examples.BHLExecution.repeated_executes
#print axioms Lara.Examples.BHLExecution.alias_multiplicity
#print axioms Lara.Examples.BHLExecution.reporting_computes
#print axioms Lara.Examples.BHLExecution.report_adds_no_history
#print axioms Lara.Examples.BHLExecution.report_is_not_a_test
#print axioms Lara.Examples.BHLExecution.protected_old_result
#print axioms Lara.Examples.BHLExecution.undefined_guard_computes
#print axioms Lara.Examples.BHLExecution.undefined_guard_no_run
#print axioms Lara.Examples.BHLExecution.source_skip_step
#print axioms Lara.Examples.BHLExecution.false_loop_step
#print axioms Lara.Examples.BHLExecution.branch_true_step
#print axioms Lara.Examples.BHLExecution.branch_false_step
#print axioms Lara.Examples.BHLExecution.nonzero_ledger_computes
#print axioms Lara.Examples.BHLExecution.nonzero_ledger_executes
#print axioms Lara.Examples.BHLExecution.preserves_nonzero_ledger
#print axioms Lara.Examples.BHLExecution.same_memory_different_histories
#print axioms Lara.Examples.BHLExecution.parallel_all_assertions
#print axioms Lara.Examples.BHLExecution.parallel_nested_knowledge
#print axioms Lara.Examples.BHLExecution.sampled_both_hidden_compatible
#print axioms Lara.Examples.BHLExecution.independently_correct_test
#print axioms Lara.Examples.BHLExecution.false_loop_no_command_state
#print axioms Lara.Examples.BHLExecution.source_skip_one_command_state
#print axioms Lara.Examples.BHLExecution.aliases_share_multiplicity
#print axioms Lara.Examples.BHLExecution.bad_writes_are_disjoint
#print axioms Lara.Examples.BHLExecution.true_branch_computes
#print axioms Lara.Examples.BHLExecution.false_branch_computes
#print axioms Lara.Examples.BHLExecution.true_branch_executes
#print axioms Lara.Examples.BHLExecution.false_branch_executes
#print axioms Lara.Examples.BHLExecution.loop_checks_compute
#print axioms Lara.Examples.BHLExecution.parallel_checks_compute
#print axioms Lara.Examples.BHLExecution.history_checks_compute
#print axioms Lara.Examples.BHLExecution.undefined_check_computes


-- PR05: independent eight-rule soundness, statistical frames and inhabited witnesses.
#print axioms Lara.BHL.Primitive.assign_isPureAssignment
#print axioms Lara.BHL.Primitive.assignDataset_isPureAssignment
#print axioms Lara.BHL.Primitive.skip_not_isPureAssignment
#print axioms Lara.BHL.Primitive.test_not_isPureAssignment
#print axioms Lara.BHL.AssertionEntails.refl
#print axioms Lara.BHL.AssertionEntails.trans
#print axioms Lara.BHL.AssertionEntails.conj_left
#print axioms Lara.BHL.AssertionEntails.conj_right
#print axioms Lara.BHL.AssertionEntails.conj
#print axioms Lara.BHL.Derivation.wellFormed
#print axioms Lara.BHL.primitive_viewTerm_realized
#print axioms Lara.BHL.primitive_viewTerm_successor
#print axioms Lara.BHL.primitive_preimage_successor_iff
#print axioms Lara.BHL.primitive_preimage_valid
#print axioms Lara.BHL.reference_guardAssertion_iff
#print axioms Lara.BHL.satisfies_guardAssertion_iff
#print axioms Lara.BHL.guard_false_defined_negation
#print axioms Lara.BHL.guardAssertion_undefined
#print axioms Lara.BHL.satisfies_conj
#print axioms Lara.BHL.rule_skip_sound
#print axioms Lara.BHL.rule_assign_sound
#print axioms Lara.BHL.rule_test_sound
#print axioms Lara.BHL.rule_seq_sound
#print axioms Lara.BHL.rule_if_sound
#print axioms Lara.BHL.rule_loop_sound
#print axioms Lara.BHL.rule_consequence_sound
#print axioms Lara.BHL.rule_parallel_sound
#print axioms Lara.BHL.derivation_sound
#print axioms Lara.BHL.evalTerm_support_congr
#print axioms Lara.BHL.evalArguments_support_congr
#print axioms Lara.BHL.evalNumericalEvent_support_congr
#print axioms Lara.BHL.evalTestEntries_support_congr
#print axioms Lara.BHL.evalTestHistory_support_congr
#print axioms Lara.BHL.modelRequirements_support_congr
#print axioms Lara.BHL.atomMeaning_support_congr
#print axioms Lara.BHL.ModalTestFrame.disj
#print axioms Lara.BHL.ModalTestFrame.implies
#print axioms Lara.BHL.ModalTestFrame.possible
#print axioms Lara.BHL.AssertionTestFrame.disj
#print axioms Lara.BHL.AssertionTestFrame.implies
#print axioms Lara.BHL.AssertionTestFrame.exists
#print axioms Lara.BHL.test_step_datasets
#print axioms Lara.BHL.test_step_program_frame
#print axioms Lara.BHL.test_step_program_agreement
#print axioms Lara.BHL.evalProgramExpr_test_frame
#print axioms Lara.BHL.evalDatasetExpr_test_frame
#print axioms Lara.BHL.test_step_read_other
#print axioms Lara.BHL.test_step_fresh_support
#print axioms Lara.BHL.evalTerm_test_frame
#print axioms Lara.BHL.atom_test_frame
#print axioms Lara.BHL.modal_test_frame
#print axioms Lara.BHL.assertion_test_frame
#print axioms Lara.BHL.satisfies_test_frame
#print axioms Lara.BHL.measurable_jointStatistic
#print axioms Lara.BHL.evalTerm_report
#print axioms Lara.BHL.evalTerm_rational
#print axioms Lara.BHL.evalNumericalEvent_leaf
#print axioms Lara.BHL.evalNumericalEvent_leaf_some
#print axioms Lara.BHL.evalTerm_pvalue_leaf_some
#print axioms Lara.BHL.pvalue_leaf_some_iff
#print axioms Lara.BHL.stored_iff
#print axioms Lara.BHL.observationInvariant_report
#print axioms Lara.BHL.observationInvariant_toDatasetExpr
#print axioms Lara.BHL.observableTest_leaf
#print axioms Lara.BHL.stored_at_accessible
#print axioms Lara.BHL.reportRange_of_eval
#print axioms Lara.BHL.test_step_frame
#print axioms Lara.BHL.test_step_read_ne
#print axioms Lara.BHL.test_step_dataset_value
#print axioms Lara.BHL.evalTestHistory_combined
#print axioms Lara.BHL.single_pre_entails_book_preimage
#print axioms Lara.BHL.single_book_entails_post
#print axioms Lara.BHL.twoHT_derivable
#print axioms Lara.BHL.lowHT_derivable
#print axioms Lara.BHL.upHT_derivable
#print axioms Lara.BHL.twoHT_sound
#print axioms Lara.BHL.lowHT_sound
#print axioms Lara.BHL.upHT_sound
#print axioms Lara.BHL.twoHT_post_meaningful
#print axioms Lara.BHL.lowHT_post_meaningful
#print axioms Lara.BHL.upHT_post_meaningful
#print axioms Lara.BHL.multi_pre_entails_book_preimage
#print axioms Lara.BHL.multiDisj_book_entails_post
#print axioms Lara.BHL.multiConj_book_entails_post
#print axioms Lara.BHL.multDisj_derivable
#print axioms Lara.BHL.multConj_derivable
#print axioms Lara.BHL.multDisj_sound
#print axioms Lara.BHL.multConj_sound
#print axioms Lara.BHL.multDisj_post_meaningful
#print axioms Lara.BHL.multDisj_pair_meaningful
#print axioms Lara.BHL.multConj_post_meaningful
#print axioms Lara.BHL.multConj_pair_meaningful
#print axioms Lara.Examples.BHLSoundnessDataset.alias_quote
#print axioms Lara.Examples.BHLSoundnessDataset.start_admitted
#print axioms Lara.Examples.BHLSoundnessDataset.test_effect_start
#print axioms Lara.Examples.BHLSoundnessDataset.test_effect_once
#print axioms Lara.Examples.BHLSoundnessDataset.alias_effect
#print axioms Lara.Examples.BHLSoundnessDataset.once_admitted
#print axioms Lara.Examples.BHLSoundnessDataset.before_admitted
#print axioms Lara.Examples.BHLSoundnessDataset.after_admitted
#print axioms Lara.Examples.BHLSoundnessDataset.first_test
#print axioms Lara.Examples.BHLSoundnessDataset.second_test
#print axioms Lara.Examples.BHLSoundnessDataset.assignment_step
#print axioms Lara.Examples.BHLSoundnessDataset.derivation
#print axioms Lara.Examples.BHLSoundnessDataset.complete_history
#print axioms Lara.Examples.BHLSoundnessDataset.protected_output
#print axioms Lara.Examples.BHLSoundnessDataset.probability_changes
#print axioms Lara.Examples.BHLSoundnessDataset.count_changes
#print axioms Lara.Examples.BHLSoundnessDataset.final_satisfaction
#print axioms Lara.Examples.BHLSoundnessDataset.initial_satisfaction
#print axioms Lara.Examples.BHLSoundnessDataset.initial_alias_ghost
#print axioms Lara.Examples.BHLSoundnessDataset.assignment_evaluates
#print axioms Lara.Examples.BHLSoundnessDataset.smoke_flags
#print axioms Lara.Examples.BHLSoundnessDataset.pre_correspondence
#print axioms Lara.Examples.BHLSoundnessDataset.post_correspondence
#print axioms Lara.Examples.BHLSoundnessDataset.pre_evaluator_correspondence
#print axioms Lara.Examples.BHLSoundnessDataset.post_evaluator_correspondence
#print axioms Lara.Examples.BHLSoundnessDataset.assignment_evaluator_correspondence
#print axioms Lara.Examples.BHLSoundnessScience.theta_hiddenMemory
#print axioms Lara.Examples.BHLSoundnessScience.testFor_statistic
#print axioms Lara.Examples.BHLSoundnessScience.testFor_nullLaw
#print axioms Lara.Examples.BHLSoundnessScience.testFor_pvalue
#print axioms Lara.Examples.BHLSoundnessScience.statistic_law
#print axioms Lara.Examples.BHLSoundnessScience.measurable_pairStatistic
#print axioms Lara.Examples.BHLSoundnessScience.joint_statistic_law
#print axioms Lara.Examples.BHLSoundnessScience.couplingFor_selected
#print axioms Lara.Examples.BHLSoundnessScience.start_admitted
#print axioms Lara.Examples.BHLSoundnessScience.sampled_admitted
#print axioms Lara.Examples.BHLSoundnessScience.admitted_parameter
#print axioms Lara.Examples.BHLSoundnessScience.sampled_accessible
#print axioms Lara.Examples.BHLSoundnessScience.lower_iff
#print axioms Lara.Examples.BHLSoundnessScience.upper_iff
#print axioms Lara.Examples.BHLSoundnessScience.sampled_lower_possible
#print axioms Lara.Examples.BHLSoundnessScience.sampled_upper_possible
#print axioms Lara.Examples.BHLSoundnessScience.low_upper_impossible
#print axioms Lara.Examples.BHLSoundnessScience.up_lower_impossible
#print axioms Lara.Examples.BHLSoundnessScience.lower_frame
#print axioms Lara.Examples.BHLSoundnessScience.upper_frame
#print axioms Lara.Examples.BHLSoundnessScience.alternative_frame
#print axioms Lara.Examples.BHLSoundnessScience.sample_frame
#print axioms Lara.Examples.BHLSoundnessScience.ψ_frame
#print axioms Lara.Examples.BHLSoundnessScience.requirements_of_sample
#print axioms Lara.Examples.BHLSoundnessScience.alternatives_exclusive
#print axioms Lara.Examples.BHLSoundnessScience.joint_population_marginals
#print axioms Lara.Examples.BHLSoundnessScience.twoDerivation
#print axioms Lara.Examples.BHLSoundnessScience.lowDerivation
#print axioms Lara.Examples.BHLSoundnessScience.upDerivation
#print axioms Lara.Examples.BHLSoundnessScience.pair_requirements
#print axioms Lara.Examples.BHLSoundnessScience.multDisjDerivation
#print axioms Lara.Examples.BHLSoundnessScience.multConjDerivation
#print axioms Lara.Examples.BHLSoundnessScience.single_computes
#print axioms Lara.Examples.BHLSoundnessScience.pair_computes
#print axioms Lara.Examples.BHLSoundnessScience.sampled_reifies
#print axioms Lara.Examples.BHLSoundnessScience.test_effect_eq
#print axioms Lara.Examples.BHLSoundnessScience.test_step
#print axioms Lara.Examples.BHLSoundnessScience.single_steps
#print axioms Lara.Examples.BHLSoundnessScience.single_reifies
#print axioms Lara.Examples.BHLSoundnessScience.single_executes
#print axioms Lara.Examples.BHLSoundnessScience.second_step
#print axioms Lara.Examples.BHLSoundnessScience.second_executes
#print axioms Lara.Examples.BHLSoundnessScience.pair_steps
#print axioms Lara.Examples.BHLSoundnessScience.pair_executes
#print axioms Lara.Examples.BHLSoundnessScience.initial_pre
#print axioms Lara.Examples.BHLSoundnessScience.two_final
#print axioms Lara.Examples.BHLSoundnessScience.low_final
#print axioms Lara.Examples.BHLSoundnessScience.up_final
#print axioms Lara.Examples.BHLSoundnessScience.single_report
#print axioms Lara.Examples.BHLSoundnessScience.single_data
#print axioms Lara.Examples.BHLSoundnessScience.single_stored
#print axioms Lara.Examples.BHLSoundnessScience.single_range
#print axioms Lara.Examples.BHLSoundnessScience.multi_pre
#print axioms Lara.Examples.BHLSoundnessScience.multDisj_final
#print axioms Lara.Examples.BHLSoundnessScience.multConj_final
#print axioms Lara.Examples.BHLSoundnessScience.pair_ledger
#print axioms Lara.Examples.BHLSoundnessScience.pair_reports
#print axioms Lara.Examples.BHLSoundnessScience.pair_stored
#print axioms Lara.Examples.BHLSoundnessScience.union_probability
#print axioms Lara.Examples.BHLSoundnessScience.intersection_probability
#print axioms Lara.Examples.BHLSoundnessScience.composite_bounds
#print axioms Lara.Examples.BHLSoundnessScience.finite_union_mass
#print axioms Lara.Examples.BHLSoundnessScience.finite_intersection_mass
#print axioms Lara.Examples.BHLSoundnessScience.pre_checks
#print axioms Lara.Examples.BHLSoundnessScience.single_post_checks
#print axioms Lara.Examples.BHLSoundnessScience.pair_post_checks
#print axioms Lara.Examples.BHLSoundnessScience.smoke_observations
#print axioms Lara.Examples.BHLSoundnessScience.finite_union_correspondence
#print axioms Lara.Examples.BHLSoundnessScience.finite_intersection_correspondence
#print axioms Lara.Examples.BHLSoundnessScience.two_smoke_correspondence
#print axioms Lara.Examples.BHLSoundnessScience.low_smoke_correspondence
#print axioms Lara.Examples.BHLSoundnessScience.up_smoke_correspondence
#print axioms Lara.Examples.BHLSoundnessScience.multDisj_smoke_correspondence
#print axioms Lara.Examples.BHLSoundnessScience.multConj_smoke_correspondence
#print axioms Lara.Examples.BHLSoundnessScience.pre_smoke_correspondence
#print axioms Lara.Examples.BHLSoundnessScience.genuine_null
#print axioms Lara.Examples.BHLSoundnessScience.three_parameters
#print axioms Lara.Examples.BHLSoundnessScience.hiddenMemory_injective
#print axioms Lara.Examples.BHLSoundnessScience.pair_counts
#print axioms Lara.Examples.BHLSoundnessScience.first_report_protected
#print axioms Lara.Examples.BHLSoundnessScience.dataset_frame
#print axioms Lara.Examples.BHLSoundnessScience.pair_event_disj
#print axioms Lara.Examples.BHLSoundnessScience.pair_event_conj
#print axioms Lara.Examples.BHLSoundnessScience.pair_pvalues
#print axioms Lara.Examples.BHLSoundnessScience.stored_thresholds
#print axioms Lara.Examples.BHLSoundness.stateAssertion_iff
#print axioms Lara.Examples.BHLSoundness.preimage_step_iff
#print axioms Lara.Examples.BHLSoundness.derivation_preimage_mono
#print axioms Lara.Examples.BHLSoundness.preimage_exec_iff
#print axioms Lara.Examples.BHLSoundness.sampled_state
#print axioms Lara.Examples.BHLSoundness.incrementX_entails
#print axioms Lara.Examples.BHLSoundness.incrementY_entails
#print axioms Lara.Examples.BHLSoundness.incrementX_derivation
#print axioms Lara.Examples.BHLSoundness.incrementY_derivation
#print axioms Lara.Examples.BHLSoundness.skip_derivation
#print axioms Lara.Examples.BHLSoundness.skip_computes
#print axioms Lara.Examples.BHLSoundness.skip_executes
#print axioms Lara.Examples.BHLSoundness.increment_computes
#print axioms Lara.Examples.BHLSoundness.increment_executes
#print axioms Lara.Examples.BHLSoundness.increment_inhabited
#print axioms Lara.Examples.BHLSoundness.entails_disj_left
#print axioms Lara.Examples.BHLSoundness.entails_disj_right
#print axioms Lara.Examples.BHLSoundness.eval_intLess_read
#print axioms Lara.Examples.BHLSoundness.guard_less_iff
#print axioms Lara.Examples.BHLSoundness.branch_yes_entails
#print axioms Lara.Examples.BHLSoundness.branch_no_entails
#print axioms Lara.Examples.BHLSoundness.branch_derivation
#print axioms Lara.Examples.BHLSoundness.variable_true_computes
#print axioms Lara.Examples.BHLSoundness.variable_false_computes
#print axioms Lara.Examples.BHLSoundness.variable_true_executes
#print axioms Lara.Examples.BHLSoundness.variable_false_executes
#print axioms Lara.Examples.BHLSoundness.both_branch_premises_inhabited
#print axioms Lara.Examples.BHLSoundness.state_entails_loop
#print axioms Lara.Examples.BHLSoundness.loop_body_entails
#print axioms Lara.Examples.BHLSoundness.loop_derivation
#print axioms Lara.Examples.BHLSoundness.loop_inhabited
#print axioms Lara.Examples.BHLSoundness.semanticView_eq_of_reifies
#print axioms Lara.Examples.BHLSoundness.report_only_derivation
#print axioms Lara.Examples.BHLSoundness.report_only_executes
#print axioms Lara.Examples.BHLSoundness.report_only_post
#print axioms Lara.Examples.BHLSoundness.report_only_pre_inhabited
#print axioms Lara.Examples.BHLSoundness.first_computes
#print axioms Lara.Examples.BHLSoundness.second_computes
#print axioms Lara.Examples.BHLSoundness.first_executes
#print axioms Lara.Examples.BHLSoundness.second_executes
#print axioms Lara.Examples.BHLSoundness.two_tests_derivation
#print axioms Lara.Examples.BHLSoundness.two_tests_executes
#print axioms Lara.Examples.BHLSoundness.two_tests_post
#print axioms Lara.Examples.BHLSoundness.two_tests_pre_inhabited
#print axioms Lara.Examples.BHLSoundness.parallel_derivation
#print axioms Lara.Examples.BHLSoundness.parallel_post_left
#print axioms Lara.Examples.BHLSoundness.parallel_post_right
#print axioms Lara.Examples.BHLSoundness.parallel_seq_computes
#print axioms Lara.Examples.BHLSoundness.parallel_pre_inhabited
#print axioms Lara.Examples.BHLSoundness.parallel_inhabited
#print axioms Lara.Examples.BHLSoundness.parallel_sound
#print axioms Lara.Examples.BHLSoundness.extra_computes
#print axioms Lara.Examples.BHLSoundness.first_ledger
#print axioms Lara.Examples.BHLSoundness.afterExtra_ledger
#print axioms Lara.Examples.BHLSoundness.extra_executes
#print axioms Lara.Examples.BHLSoundness.observeWorld_sampled
#print axioms Lara.Examples.BHLSoundness.observeEvent_irrel
#print axioms Lara.Examples.BHLSoundness.eventWorld_observe
#print axioms Lara.Examples.BHLSoundness.eventWorld_observe_congr
#print axioms Lara.Examples.BHLSoundness.observeWorld_eventsWorld_irrel
#print axioms Lara.Examples.BHLSoundness.hidden_sampled
#print axioms Lara.Examples.BHLSoundness.hidden_eventsWorld
#print axioms Lara.Examples.BHLSoundness.provenance_eventsWorld
#print axioms Lara.Examples.BHLSoundness.sampled_provenance
#print axioms Lara.Examples.BHLSoundness.first_provenance
#print axioms Lara.Examples.BHLSoundness.first_accessible
#print axioms Lara.Examples.BHLSoundness.afterExtra_accessible
#print axioms Lara.Examples.BHLSoundness.first_dataset
#print axioms Lara.Examples.BHLSoundness.first_visible_dataset
#print axioms Lara.Examples.BHLSoundness.first_datasetEval
#print axioms Lara.Examples.BHLSoundness.afterExtra_datasetEval
#print axioms Lara.Examples.BHLSoundness.first_report
#print axioms Lara.Examples.BHLSoundness.first_pvalue
#print axioms Lara.Examples.BHLSoundness.first_exact_history
#print axioms Lara.Examples.BHLSoundness.first_old
#print axioms Lara.Examples.BHLSoundness.first_report_pvalue
#print axioms Lara.Examples.BHLSoundness.first_requirements
#print axioms Lara.Examples.BHLSoundness.first_possible
#print axioms Lara.Examples.BHLSoundness.first_belief
#print axioms Lara.Examples.BHLSoundness.legal_pre
#print axioms Lara.Examples.BHLSoundness.afterExtra_exact_history_false
#print axioms Lara.Examples.BHLSoundness.not_post
#print axioms Lara.Examples.BHLSoundness.not_valid_freshness
#print axioms Lara.Examples.BHLSoundness.visible_report_preserved
#print axioms Lara.Examples.BHLSoundness.extra_not_derivable
#print axioms Lara.Examples.BHLSoundness.skipRow_computes
#print axioms Lara.Examples.BHLSoundness.incrementRow_computes
#print axioms Lara.Examples.BHLSoundness.reportRow_computes
#print axioms Lara.Examples.BHLSoundness.twoTestRow_computes
#print axioms Lara.Examples.BHLSoundness.branchTrueRow_computes
#print axioms Lara.Examples.BHLSoundness.branchFalseRow_computes
#print axioms Lara.Examples.BHLSoundness.loopRow_computes
#print axioms Lara.Examples.BHLSoundness.parallelLeftRow_computes
#print axioms Lara.Examples.BHLSoundness.parallelRightRow_computes
#print axioms Lara.Examples.BHLSoundness.firstRow_computes
#print axioms Lara.Examples.BHLSoundness.extraRow_computes
#print axioms Lara.Examples.BHLSoundness.firstLedgerCounts
#print axioms Lara.Examples.BHLSoundness.extraLedgerCounts
#print axioms Lara.Examples.BHLSoundness.freshnessSummary_computes
#print axioms Lara.Examples.BHLSoundness.rows_compute
#print axioms Lara.Examples.BHLSoundness.otherChecks_compute
#print axioms Lara.Examples.BHLSoundness.rows_all_true

-- BHL PR06: actual finite assertion expressiveness and relative completeness.
#print axioms Lara.BHL.Program.controlCode_none
#print axioms Lara.BHL.Program.controlCode_nonneg
#print axioms Lara.BHL.Program.controlCode_le_length
#print axioms Lara.BHL.Program.controlCode_lt_length
#print axioms Lara.BHL.Program.controlCode_lt_length_iff
#print axioms Lara.BHL.Program.controlCode_eq_length_of_not_mem
#print axioms Lara.BHL.Program.controlNode_natCast
#print axioms Lara.BHL.Program.controlNode_of_nonneg
#print axioms Lara.BHL.Program.controlNode_of_neg
#print axioms Lara.BHL.Program.controlNode_eq_none_iff
#print axioms Lara.BHL.Program.controlNode_of_ge_length
#print axioms Lara.BHL.Program.controlNode_eq_some_iff
#print axioms Lara.BHL.Program.controlNode_mem
#print axioms Lara.BHL.Program.controlNode_bounds
#print axioms Lara.BHL.Program.controlNode_getElem
#print axioms Lara.BHL.Program.controlNode_zero
#print axioms Lara.BHL.Program.controlNode_controlCode
#print axioms Lara.BHL.Program.controlNode_controlCode_iff
#print axioms Lara.BHL.Program.controlCode_injective
#print axioms Lara.BHL.Program.controlCode_eq_iff
#print axioms Lara.BHL.Program.controlCode_some_pos
#print axioms Lara.BHL.Program.controlCode_some_ne_zero
#print axioms Lara.BHL.Program.controlCode_eq_zero_iff
#print axioms Lara.BHL.Program.controlCode_source_pos
#print axioms Lara.BHL.Program.controlCode_source_wellFormed
#print axioms Lara.BHL.Program.controlCode_terminal_wellFormed
#print axioms Lara.BHL.Program.control_edge_target_mem_controlNodes
#print axioms Lara.BHL.Program.controlCode_edge_target_wellFormed
#print axioms Lara.BHL.World.appendStates_initial
#print axioms Lara.BHL.World.appendStates_rest
#print axioms Lara.BHL.World.appendStates_nil
#print axioms Lara.BHL.World.appendStates_singleton
#print axioms Lara.BHL.World.appendStates_assoc
#print axioms Lara.BHL.World.appendStates_trace
#print axioms Lara.BHL.World.appendStates_trace_length
#print axioms Lara.BHL.World.appendStates_trace_prefix
#print axioms Lara.BHL.World.appendStates_take_trace_prefix
#print axioms Lara.BHL.World.appendStates_current
#print axioms Lara.BHL.World.appendStates_take_zero
#print axioms Lara.BHL.World.appendStates_take_succ
#print axioms Lara.BHL.World.appendStates_take_succ_current
#print axioms Lara.BHL.World.appendStates_start_prefix
#print axioms Lara.BHL.LogCell.control_variable_id
#print axioms Lara.BHL.LogCell.commands_variable_id
#print axioms Lara.BHL.LogCell.distinct_ids
#print axioms Lara.BHL.LogCell.variable_id_injective
#print axioms Lara.BHL.LogCell.variable_injective
#print axioms Lara.BHL.LogCell.distinct_variables
#print axioms Lara.BHL.ControlMetadata.memory_read_control
#print axioms Lara.BHL.ControlMetadata.memory_read_commands
#print axioms Lara.BHL.ControlMetadata.memory_read_other_integer
#print axioms Lara.BHL.ControlMetadata.memory_read_other_sort
#print axioms Lara.BHL.ControlMetadata.memory_hidden
#print axioms Lara.BHL.ControlMetadata.memory_read_invisible
#print axioms Lara.BHL.ControlMetadata.memory_eq_of_hidden_eq
#print axioms Lara.BHL.ControlMetadata.memory_memory
#print axioms Lara.BHL.ControlMetadata.state_memory
#print axioms Lara.BHL.ControlMetadata.state_datasets
#print axioms Lara.BHL.ControlMetadata.state_history
#print axioms Lara.BHL.ControlMetadata.state_action
#print axioms Lara.BHL.ControlMetadata.state_hidden
#print axioms Lara.BHL.ControlMetadata.state_read_control
#print axioms Lara.BHL.ControlMetadata.state_read_commands
#print axioms Lara.BHL.ControlMetadata.state_read_invisible
#print axioms Lara.BHL.ControlMetadata.state_state
#print axioms Lara.BHL.ControlMetadata.seed_initial
#print axioms Lara.BHL.ControlMetadata.seed_rest
#print axioms Lara.BHL.ControlMetadata.seed_current
#print axioms Lara.BHL.ControlMetadata.seed_read_control
#print axioms Lara.BHL.ControlMetadata.seed_read_commands
#print axioms Lara.BHL.ControlMetadata.trace_nil
#print axioms Lara.BHL.ControlMetadata.trace_cons
#print axioms Lara.BHL.ControlMetadata.trace_singleton
#print axioms Lara.BHL.ControlMetadata.trace_length
#print axioms Lara.BHL.ControlMetadata.trace_append
#print axioms Lara.BHL.ControlMetadata.trace_take
#print axioms Lara.BHL.ControlMetadata.trace_getElem
#print axioms Lara.BHL.ControlMetadata.world_initial
#print axioms Lara.BHL.ControlMetadata.world_rest
#print axioms Lara.BHL.ControlMetadata.world_trace
#print axioms Lara.BHL.ControlMetadata.world_nil
#print axioms Lara.BHL.ControlMetadata.world_append
#print axioms Lara.BHL.ControlMetadata.world_append_singleton
#print axioms Lara.BHL.ControlMetadata.world_current_getLast
#print axioms Lara.BHL.ControlMetadata.world_prefix
#print axioms Lara.BHL.ControlMetadata.prefix_trace
#print axioms Lara.BHL.ControlMetadata.prefix_eq_world_take
#print axioms Lara.BHL.ControlMetadata.prefix_zero
#print axioms Lara.BHL.ControlMetadata.prefix_zero_current
#print axioms Lara.BHL.ControlMetadata.prefix_succ
#print axioms Lara.BHL.ControlMetadata.prefix_succ_current
#print axioms Lara.BHL.ControlMetadata.prefix_of_length_le
#print axioms Lara.BHL.ControlMetadata.prefix_trace_prefix
#print axioms Lara.BHL.ControlMetadata.prefix_zero_read_control
#print axioms Lara.BHL.ControlMetadata.prefix_zero_read_commands
#print axioms Lara.BHL.ControlMetadata.prefix_succ_read_control
#print axioms Lara.BHL.ControlMetadata.prefix_succ_read_commands
#print axioms Lara.BHL.ControlMetadata.prefix_current_cases
#print axioms Lara.BHL.ControlMetadata.prefix_current_invariants
#print axioms Lara.BHL.ControlMetadata.prefix_current_read_invisible
#print axioms Lara.BHL.ControlMetadata.world_constantHidden
#print axioms Lara.BHL.ControlMetadata.evalTerm_valueRead_currentView
#print axioms Lara.BHL.ControlMetadata.evalTerm_appendWorld
#print axioms Lara.BHL.ControlMetadata.evalTerm_traceTake_ofNat
#print axioms Lara.BHL.ControlMetadata.evalTerm_appendWorld_traceTake
#print axioms Lara.BHL.ControlMetadata.evalTerm_prefix_zero_control
#print axioms Lara.BHL.ControlMetadata.evalTerm_prefix_zero_commands
#print axioms Lara.BHL.ControlMetadata.evalTerm_prefix_succ_control
#print axioms Lara.BHL.ControlMetadata.evalTerm_prefix_succ_commands
#print axioms Lara.BHL.valid_iff_entails_wlp
#print axioms Lara.BHL.wlp_mono
#print axioms Lara.BHL.wlp_command_iff
#print axioms Lara.BHL.wlp_skip_iff
#print axioms Lara.BHL.wlp_seq_iff
#print axioms Lara.BHL.wlp_ite_iff
#print axioms Lara.BHL.wlp_ite_undefined
#print axioms Lara.BHL.wlp_loop_body
#print axioms Lara.BHL.wlp_loop_exit
#print axioms Lara.BHL.wlp_loop_undefined
#print axioms Lara.BHL.wlp_parallel_iff
#print axioms Lara.BHL.wlp_true_loop
#print axioms Lara.BHL.ControlLabel.viewEffect_replay
#print axioms Lara.BHL.ControlLabel.effect_viewEffect
#print axioms Lara.BHL.ControlLog.append_source
#print axioms Lara.BHL.ControlLog.append_program_length
#print axioms Lara.BHL.ControlLog.append_control_length
#print axioms Lara.BHL.ControlLog.append_programPrefix
#print axioms Lara.BHL.ControlLog.append_readCell
#print axioms Lara.BHL.ControlLog.append_readCell_end_control
#print axioms Lara.BHL.ControlLog.append_readCell_end_commands
#print axioms Lara.BHL.ControlLog.append_terminal
#print axioms Lara.BHL.ControlLog.programPrefix_length
#print axioms Lara.BHL.ControlLog.programPrefix_zero
#print axioms Lara.BHL.ControlLog.append_edge_previous
#print axioms Lara.BHL.ControlLog.append_ready
#print axioms Lara.BHL.ControlLog.ready_valid
#print axioms Lara.BHL.ControlLog.terminal_admitted
#print axioms Lara.BHL.ControlLog.decode_suffix
#print axioms Lara.BHL.ControlLog.decode
#print axioms Lara.BHL.Steps.controlLog_encode
#print axioms Lara.BHL.ControlLog.encode
#print axioms Lara.BHL.ControlLogSyntax.Terms.denotes_bound
#print axioms Lara.BHL.ControlLogSyntax.Terms.denotes_rename
#print axioms Lara.BHL.ControlLogSyntax.Terms.eval_traceTake
#print axioms Lara.BHL.ControlLogSyntax.Terms.eval_metadataWorld
#print axioms Lara.BHL.ControlLogSyntax.Terms.eval_cell
#print axioms Lara.BHL.ControlLogSyntax.Terms.eval_count
#print axioms Lara.BHL.ControlLogSyntax.Terms.eval_programWorld
#print axioms Lara.BHL.ControlLogSyntax.Terms.eval_programView
#print axioms Lara.BHL.ControlLogSyntax.Terms.eval_terminal
#print axioms Lara.BHL.ControlLogSyntax.Terms.eval_programLength
#print axioms Lara.BHL.ControlLogSyntax.Terms.eval_controlLength
#print axioms Lara.BHL.ControlLogSyntax.reindex_original
#print axioms Lara.BHL.ControlLogSyntax.eval_nextIndex
#print axioms Lara.BHL.canonical_derivation
#print axioms Lara.BHL.relative_completeness_of_family
#print axioms Lara.BHL.derivation_iff_valid_of_family
#print axioms Lara.BHL.ControlLogSyntax.conjunction_satisfaction
#print axioms Lara.BHL.ControlLogSyntax.disjunction_satisfaction
#print axioms Lara.BHL.ControlLogSyntax.edge_satisfaction
#print axioms Lara.BHL.ControlLogSyntax.edges_satisfaction
#print axioms Lara.BHL.ControlLogSyntax.header_satisfaction
#print axioms Lara.BHL.ControlLogSyntax.validLocalLog_satisfaction
#print axioms Lara.BHL.ControlLogSyntax.representative_reference_iff
#print axioms Lara.BHL.control_log_represents_wlp
#print axioms Lara.BHL.weakest_liberal_assertion_represents
#print axioms Lara.BHL.weakest_liberal_assertion_derivation
#print axioms Lara.BHL.relative_completeness
#print axioms Lara.BHL.derivation_iff_valid
#print axioms Lara.BHL.malformed_program_not_derivable
#print axioms Lara.BHL.malformed_program_vacuously_valid
#print axioms Lara.Examples.BHLCompleteness.loop_body_semantically_preserves
#print axioms Lara.Examples.BHLCompleteness.loop_exit_entails_three
#print axioms Lara.Examples.BHLCompleteness.loop_semantically_valid
#print axioms Lara.Examples.BHLCompleteness.loop_reconstructed
#print axioms Lara.Examples.BHLCompleteness.canonical_loop_inhabited
#print axioms Lara.Examples.BHLCompleteness.canonical_loop_preserves
#print axioms Lara.Examples.BHLCompleteness.canonical_loop_exit
#print axioms Lara.Examples.BHLCompleteness.parallel_semantically_valid
#print axioms Lara.Examples.BHLCompleteness.parallel_reconstructed
#print axioms Lara.Examples.BHLCompleteness.divergent_loop_precondition
#print axioms Lara.Examples.BHLCompleteness.divergent_loop_reconstructed
#print axioms Lara.Examples.BHLCompleteness.incompatible_parallel_vacuously_valid
#print axioms Lara.Examples.BHLCompleteness.incompatible_parallel_not_reconstructed
#print axioms Lara.Examples.BHLCompleteness.loop_counts
#print axioms Lara.Examples.BHLCompleteness.left_counts
#print axioms Lara.Examples.BHLCompleteness.right_counts

-- Exact finite statistical instance and reference-corresponding endpoint checks.
#print axioms Lara.BHL.FiniteProbability.eventMass_nonnegative
#print axioms Lara.BHL.FiniteProbability.eventMass_false
#print axioms Lara.BHL.FiniteProbability.eventMass_true
#print axioms Lara.BHL.FiniteProbability.eventMass_le_one
#print axioms Lara.BHL.FiniteProbability.eventMass_mono
#print axioms Lara.BHL.FiniteProbability.product_mass
#print axioms Lara.BHL.FiniteProbability.eventMass_product_fst
#print axioms Lara.BHL.FiniteProbability.eventMass_product_snd
#print axioms Lara.BHL.FiniteProbability.measure_apply
#print axioms Lara.BHL.FiniteProbability.measure_univ
#print axioms Lara.BHL.FiniteProbability.probability_toMeasure
#print axioms Lara.BHL.FiniteProbability.eventProbability_probability_set
#print axioms Lara.BHL.FiniteProbability.eventProbability_probability
#print axioms Lara.BHL.FiniteProbability.eventProbability_map_probability
#print axioms Lara.BHL.FiniteProbability.probability_product_fst
#print axioms Lara.BHL.FiniteProbability.probability_product_snd
#print axioms Lara.BHL.Tests.Binary.null_mass_true
#print axioms Lara.BHL.Tests.Binary.null_mass_false
#print axioms Lara.BHL.Tests.Binary.alternative_mass_true
#print axioms Lara.BHL.Tests.Binary.alternative_mass_false
#print axioms Lara.BHL.Tests.Binary.null_ne_alternative
#print axioms Lara.BHL.Tests.Binary.null_mass_positive
#print axioms Lara.BHL.Tests.Binary.alternative_mass_positive
#print axioms Lara.BHL.Tests.Binary.null_probability_true
#print axioms Lara.BHL.Tests.Binary.null_probability_false
#print axioms Lara.BHL.Tests.Binary.alternative_probability_true
#print axioms Lara.BHL.Tests.Binary.alternative_probability_false
#print axioms Lara.BHL.Tests.Binary.null_probability_true_pos
#print axioms Lara.BHL.Tests.Binary.null_probability_false_pos
#print axioms Lara.BHL.Tests.Binary.alternative_probability_true_pos
#print axioms Lara.BHL.Tests.Binary.alternative_probability_false_pos
#print axioms Lara.BHL.Tests.Binary.statistic_false
#print axioms Lara.BHL.Tests.Binary.statistic_low_true
#print axioms Lara.BHL.Tests.Binary.statistic_two_true
#print axioms Lara.BHL.Tests.Binary.statistic_up_true
#print axioms Lara.BHL.Tests.Binary.pvalue_true
#print axioms Lara.BHL.Tests.Binary.pvalue_false
#print axioms Lara.BHL.Tests.Binary.rationalTail_probability
#print axioms Lara.BHL.Tests.Binary.measurable_statistic
#print axioms Lara.BHL.Tests.Binary.measurable_realTail
#print axioms Lara.BHL.Tests.Binary.test_statistic_eq
#print axioms Lara.BHL.Tests.Binary.test_tail_eq
#print axioms Lara.BHL.Tests.Binary.test_nullLaw_eq
#print axioms Lara.BHL.Tests.Binary.tail_on_samples
#print axioms Lara.BHL.Tests.Binary.tail_event_preimage
#print axioms Lara.BHL.Tests.Binary.pvalue_correct
#print axioms Lara.BHL.Tests.Binary.tailProbability_true
#print axioms Lara.BHL.Tests.Binary.tailProbability_false
#print axioms Lara.BHL.Tests.Binary.calibration_mass_real
#print axioms Lara.BHL.Tests.Binary.superuniform
#print axioms Lara.BHL.Tests.Binary.calibration_mass_rational
#print axioms Lara.BHL.Tests.Binary.superuniform_rational
#print axioms Lara.BHL.Tests.Binary.calibration_rational_le
#print axioms Lara.BHL.Tests.Binary.null_rejection_at_quarter
#print axioms Lara.BHL.Tests.Binary.alternative_rejection_at_quarter
#print axioms Lara.BHL.Tests.Binary.measurable_strictRealTail
#print axioms Lara.BHL.Tests.Binary.strictTest_statistic_eq
#print axioms Lara.BHL.Tests.Binary.strictTest_tail_eq
#print axioms Lara.BHL.Tests.Binary.strictTest_nullLaw_eq
#print axioms Lara.BHL.Tests.Binary.strictTail_on_samples
#print axioms Lara.BHL.Tests.Binary.strict_tail_event_preimage
#print axioms Lara.BHL.Tests.Binary.strict_tailProbability_true
#print axioms Lara.BHL.Tests.Binary.strict_tailProbability_false
#print axioms Lara.BHL.Tests.Binary.strict_zero_mass
#print axioms Lara.BHL.Tests.Binary.strict_zero_not_superuniform
#print axioms Lara.BHL.Tests.Binary.measurable_pairStatistic
#print axioms Lara.BHL.Tests.Binary.null_population_left_marginal
#print axioms Lara.BHL.Tests.Binary.null_population_right_marginal
#print axioms Lara.BHL.Tests.Binary.alternative_population_left_marginal
#print axioms Lara.BHL.Tests.Binary.alternative_population_right_marginal
#print axioms Lara.BHL.Tests.Binary.null_joint_fst_event
#print axioms Lara.BHL.Tests.Binary.null_joint_snd_event
#print axioms Lara.BHL.Tests.Binary.null_population_independent
#print axioms Lara.BHL.Tests.Binary.nullCoupling_joint
#print axioms Lara.BHL.Tests.Binary.null_statistic_left_marginal
#print axioms Lara.BHL.Tests.Binary.null_statistic_right_marginal
#print axioms Lara.BHL.Tests.Binary.null_statistic_independent
#print axioms Lara.BHL.Tests.Binary.measurable_unionEvent
#print axioms Lara.BHL.Tests.Binary.measurable_interEvent
#print axioms Lara.BHL.Tests.Binary.unionEvent_preimage
#print axioms Lara.BHL.Tests.Binary.interEvent_preimage
#print axioms Lara.BHL.Tests.Binary.union_probability
#print axioms Lara.BHL.Tests.Binary.inter_probability
#print axioms Lara.BHL.Tests.Binary.union_true_true
#print axioms Lara.BHL.Tests.Binary.inter_true_true
#print axioms Lara.BHL.Tests.Binary.union_true_true_le_half
#print axioms Lara.BHL.Tests.Binary.inter_true_true_le_quarter
#print axioms Lara.Examples.BHLBinaryModel.testFor_pvalue
#print axioms Lara.Examples.BHLBinaryModel.population_support
#print axioms Lara.Examples.BHLBinaryModel.null_statistic_law
#print axioms Lara.Examples.BHLBinaryModel.joint_population_marginals
#print axioms Lara.Examples.BHLBinaryModel.couplingFor_selected
#print axioms Lara.Examples.BHLBinaryModel.start_admitted
#print axioms Lara.Examples.BHLBinaryModel.first_sample_admitted
#print axioms Lara.Examples.BHLBinaryModel.sampled_admitted
#print axioms Lara.Examples.BHLBinaryModel.admitted_parameter
#print axioms Lara.Examples.BHLBinaryModel.sampled_accessible
#print axioms Lara.Examples.BHLBinaryModel.lower_iff
#print axioms Lara.Examples.BHLBinaryModel.upper_iff
#print axioms Lara.Examples.BHLBinaryScience.sampled_lower_possible
#print axioms Lara.Examples.BHLBinaryScience.sampled_upper_possible
#print axioms Lara.Examples.BHLBinaryScience.low_upper_impossible
#print axioms Lara.Examples.BHLBinaryScience.up_lower_impossible
#print axioms Lara.Examples.BHLBinaryScience.requirements_of_sample
#print axioms Lara.Examples.BHLBinaryScience.alternatives_exclusive
#print axioms Lara.Examples.BHLBinaryScience.joint_population_support
#print axioms Lara.Examples.BHLBinaryScience.joint_null_statistic_law
#print axioms Lara.Examples.BHLBinaryScience.twoDerivation
#print axioms Lara.Examples.BHLBinaryScience.lowDerivation
#print axioms Lara.Examples.BHLBinaryScience.upDerivation
#print axioms Lara.Examples.BHLBinaryScience.pair_requirements
#print axioms Lara.Examples.BHLBinaryScience.multDisjDerivation
#print axioms Lara.Examples.BHLBinaryScience.multConjDerivation
#print axioms Lara.Examples.BHLBinaryRuns.test_effect
#print axioms Lara.Examples.BHLBinaryRuns.pvalue_effect
#print axioms Lara.Examples.BHLBinaryRuns.test_step
#print axioms Lara.Examples.BHLBinaryRuns.sampled_reifies
#print axioms Lara.Examples.BHLBinaryRuns.single_steps
#print axioms Lara.Examples.BHLBinaryRuns.single_reifies
#print axioms Lara.Examples.BHLBinaryRuns.single_executes
#print axioms Lara.Examples.BHLBinaryRuns.second_step
#print axioms Lara.Examples.BHLBinaryRuns.second_executes
#print axioms Lara.Examples.BHLBinaryRuns.pair_steps
#print axioms Lara.Examples.BHLBinaryRuns.pair_executes
#print axioms Lara.Examples.BHLBinaryRuns.hidden_steps
#print axioms Lara.Examples.BHLBinaryRuns.hidden_executes
#print axioms Lara.Examples.BHLBinaryRuns.single_report
#print axioms Lara.Examples.BHLBinaryRuns.single_data
#print axioms Lara.Examples.BHLBinaryRuns.pair_ledger
#print axioms Lara.Examples.BHLBinaryRuns.hidden_ledger
#print axioms Lara.Examples.BHLBinaryRuns.pair_reports
#print axioms Lara.Examples.BHLBinaryRuns.hidden_report_unchanged
#print axioms Lara.Examples.BHLStatistical.initial_pre
#print axioms Lara.Examples.BHLStatistical.two_final
#print axioms Lara.Examples.BHLStatistical.low_final
#print axioms Lara.Examples.BHLStatistical.up_final
#print axioms Lara.Examples.BHLStatistical.single_stored
#print axioms Lara.Examples.BHLStatistical.single_range
#print axioms Lara.Examples.BHLStatistical.multi_pre
#print axioms Lara.Examples.BHLStatistical.multDisj_final
#print axioms Lara.Examples.BHLStatistical.multConj_final
#print axioms Lara.Examples.BHLStatistical.single_alternative_false
#print axioms Lara.Examples.BHLStatistical.exceptional_belief_false_alternative
#print axioms Lara.Examples.BHLStatistical.exceptional_requirements_hold
#print axioms Lara.Examples.BHLStatistical.exceptional_only_branch
#print axioms Lara.Examples.BHLStatistical.alternative_not_known
#print axioms Lara.Examples.BHLStatistical.hidden_exact_history_false
#print axioms Lara.Examples.BHLStatistical.hidden_single_post_false
#print axioms Lara.Examples.BHLStatistical.hidden_alternative_false
#print axioms Lara.Examples.BHLStatistical.hidden_requirements_hold
#print axioms Lara.Examples.BHLStatistical.hidden_single_belief_false
#print axioms Lara.Examples.BHLStatistical.hidden_procedure_invalid
#print axioms Lara.Examples.BHLFiniteBelief.eventMass_disj
#print axioms Lara.Examples.BHLFiniteBelief.eventMass_conj
#print axioms Lara.Examples.BHLFiniteBelief.eventMass_disj_correct
#print axioms Lara.Examples.BHLFiniteBelief.eventMass_conj_correct
#print axioms Lara.Examples.BHLFiniteBelief.eventMass_single_correct
#print axioms Lara.Examples.BHLFiniteBelief.eventMass_true_true
#print axioms Lara.Examples.BHLFiniteBelief.compareRational_correct
#print axioms Lara.Examples.BHLFiniteBelief.endpoint_admitted
#print axioms Lara.Examples.BHLFiniteBelief.endpoint_accessible
#print axioms Lara.Examples.BHLFiniteBelief.endpoint_data
#print axioms Lara.Examples.BHLFiniteBelief.endpoint_ledger
#print axioms Lara.Examples.BHLFiniteBelief.endpoint_sample
#print axioms Lara.Examples.BHLFiniteBelief.bundle_observable
#print axioms Lara.Examples.BHLFiniteBelief.bundle_history_eval
#print axioms Lara.Examples.BHLFiniteBelief.bundle_pvalue_eval
#print axioms Lara.Examples.BHLFiniteBelief.bundle_requirements_of_samples
#print axioms Lara.Examples.BHLFiniteBelief.endpoint_requirements
#print axioms Lara.Examples.BHLFiniteBelief.accessible_endpoint_requirements
#print axioms Lara.Examples.BHLFiniteBelief.null_alternative_false
#print axioms Lara.Examples.BHLFiniteBelief.exception_iff_check
#print axioms Lara.Examples.BHLFiniteBelief.checkBelief_correct
#print axioms Lara.Examples.BHLFiniteBelief.checkBelief_satisfies
#print axioms Lara.Examples.BHLFiniteBelief.checkSingle_correct
#print axioms Lara.Examples.BHLFiniteBelief.checkDisjunction_correct
#print axioms Lara.Examples.BHLFiniteBelief.checkConjunction_correct
#print axioms Lara.Examples.BHLFiniteBelief.checkHiddenSingle_correct
#print axioms Lara.Examples.BHLFiniteBelief.checkAccountedDisjunction_correct
#print axioms Lara.Examples.BHLFiniteBelief.checkAccountedConjunction_correct
#print axioms Lara.Examples.BHLFiniteBelief.checkHiddenSingle_false
#print axioms Lara.Examples.BHLFiniteBelief.exceptional_single_checked
#print axioms Lara.Examples.BHLFiniteBelief.accounted_pair_checked
#print axioms Lara.Examples.BHLFiniteBelief.exceptional_checked_false_alternative
#print axioms Lara.Examples.BHLFiniteBelief.hidden_checked_report_unchanged

-- PR08: executable rule decoding, declared finite semantics, exhaustive runs, and exact applications.
-- Lara.BHL.RuleCode: 4 public theorems.
#print axioms Lara.BHL.Primitive.pureAssignmentCheck_iff
#print axioms Lara.BHL.EntailmentBinding.entails
#print axioms Lara.BHL.DerivationCodeBinding.derivation
#print axioms Lara.BHL.DerivationSlotBinding.derivation
-- Lara.BHL.Check: 20 public theorems.
#print axioms Lara.BHL.EntailmentEvidence.bound
#print axioms Lara.BHL.checkDerivation_derivation
#print axioms Lara.BHL.checkDerivation_sound
#print axioms Lara.BHL.checkDerivation_application
#print axioms Lara.BHL.checkDerivation_wellFormed
#print axioms Lara.BHL.DerivationCheckExamples.reflexiveConsequence_accepted
#print axioms Lara.BHL.DerivationCheckExamples.assignment_accepted
#print axioms Lara.BHL.DerivationCheckExamples.testRule_accepted
#print axioms Lara.BHL.DerivationCheckExamples.skipSequence_accepted
#print axioms Lara.BHL.DerivationCheckExamples.skipConditional_accepted
#print axioms Lara.BHL.DerivationCheckExamples.skipLoop_accepted
#print axioms Lara.BHL.DerivationCheckExamples.skipParallel_accepted
#print axioms Lara.BHL.DerivationCheckExamples.missingImplication_rejected
#print axioms Lara.BHL.DerivationCheckExamples.missingFinalImplication_rejected
#print axioms Lara.BHL.DerivationCheckExamples.invalidImplication_rejected
#print axioms Lara.BHL.DerivationCheckExamples.missingPremise_rejected
#print axioms Lara.BHL.DerivationCheckExamples.invalidAssignment_rejected
#print axioms Lara.BHL.DerivationCheckExamples.testViaAssign_rejected
#print axioms Lara.BHL.DerivationCheckExamples.invalidRecursivePremise_rejected
#print axioms Lara.BHL.DerivationCheckExamples.noninterferingFailure_rejected
-- Lara.BHL.FiniteModel: 20 public theorems.
#print axioms Lara.BHL.FiniteModel.hiddenCarrier_complete
#print axioms Lara.BHL.FiniteModel.admitted_hidden_canonical
#print axioms Lara.BHL.FiniteModel.endpoint_hidden
#print axioms Lara.BHL.FiniteModel.endpoint_datasets
#print axioms Lara.BHL.FiniteModel.accessible_endpoint_coverage
#print axioms Lara.BHL.FiniteModel.accessible_view_coverage
#print axioms Lara.BHL.FiniteModel.carrier_endpoint_admitted
#print axioms Lara.BHL.FiniteModel.accessible_views_exact
#print axioms Lara.BHL.FiniteModel.evalBoolean_correct
#print axioms Lara.BHL.FiniteModel.evalDataset_correct
#print axioms Lara.BHL.FiniteModel.evalModal_correct
#print axioms Lara.BHL.FiniteModel.evalFinite_reference_correct
#print axioms Lara.BHL.FiniteModel.evalFinite_correct
#print axioms Lara.BHL.FiniteModel.checkFiniteEntailment_correct
#print axioms Lara.BHL.FiniteModel.checkSatisfaction_correct
#print axioms Lara.BHL.FiniteModel.checkSatisfaction_pre_false
#print axioms Lara.BHL.FiniteModel.checkSatisfaction_post_false
#print axioms Lara.BHL.FiniteModel.Examples.quantified_examples
#print axioms Lara.BHL.FiniteModel.Examples.epistemic_examples
#print axioms Lara.BHL.FiniteModel.Examples.belief_ledger_examples
-- Lara.BHL.FiniteExecution: 28 public theorems.
#print axioms Lara.BHL.FiniteExecution.integer_correspondence
#print axioms Lara.BHL.FiniteExecution.guard_correspondence
#print axioms Lara.BHL.FiniteExecution.command_effect
#print axioms Lara.BHL.FiniteExecution.command_ledger
#print axioms Lara.BHL.FiniteExecution.nextAll_correspondence
#print axioms Lara.BHL.FiniteExecution.nextAll_complete
#print axioms Lara.BHL.FiniteExecution.nextAll_empty_iff
#print axioms Lara.BHL.FiniteExecution.explore_correspondence
#print axioms Lara.BHL.FiniteExecution.explore_coverage
#print axioms Lara.BHL.FiniteExecution.exhaustiveRun_correspondence
#print axioms Lara.BHL.FiniteExecution.exhaustiveRun_coverage
#print axioms Lara.BHL.FiniteExecution.exhaustiveRun_executes
#print axioms Lara.BHL.FiniteExecution.replay_correspondence
#print axioms Lara.BHL.FiniteExecution.scheduledRun_correspondence
#print axioms Lara.BHL.FiniteExecution.scheduledRun_executes
#print axioms Lara.BHL.FiniteExecution.Smoke.nested_successor_codes
#print axioms Lara.BHL.FiniteExecution.Smoke.terminal_zero
#print axioms Lara.BHL.FiniteExecution.Smoke.nonterminal_zero
#print axioms Lara.BHL.FiniteExecution.Smoke.completed_cases
#print axioms Lara.BHL.FiniteExecution.Smoke.mixed_command_order
#print axioms Lara.BHL.FiniteExecution.Smoke.all_nested_orders
#print axioms Lara.BHL.FiniteExecution.Smoke.undefined_guard
#print axioms Lara.BHL.FiniteExecution.Smoke.malformed_parallel
#print axioms Lara.BHL.FiniteExecution.Smoke.fuel_exhaustion
#print axioms Lara.BHL.FiniteExecution.Smoke.repeated_full_ledger
#print axioms Lara.BHL.FiniteExecution.Smoke.pvalue_no_ledger
#print axioms Lara.BHL.FiniteExecution.Smoke.protected_old_report
#print axioms Lara.BHL.FiniteExecution.Smoke.calibrated_report
-- Lara.BHL.CheckedMethods: 10 public theorems.
#print axioms Lara.BHL.CheckedMethods.method_checked
#print axioms Lara.BHL.CheckedMethods.method_derivation
#print axioms Lara.BHL.CheckedMethods.method_valid
#print axioms Lara.BHL.CheckedMethods.method_run_completed
#print axioms Lara.BHL.CheckedMethods.point_reifies
#print axioms Lara.BHL.CheckedMethods.method_run_endpoint
#print axioms Lara.BHL.CheckedMethods.method_initial
#print axioms Lara.BHL.CheckedMethods.method_execution
#print axioms Lara.BHL.CheckedMethods.conditional_false_not_applicable
#print axioms Lara.BHL.CheckedMethods.application_post
