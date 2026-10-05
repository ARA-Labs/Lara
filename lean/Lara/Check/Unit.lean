/-
Executable orchestration of the public unit-acceptance boundary.

`checkUnit` is the canonical executable constructor of `Unit.CheckedUnit`.
Its public seven-stage order is: duplicate rule identifiers, R2 signature
well-formedness and well-sortedness, policy R12, duplicate arguments, support,
typed attacks, then missing conflict. The first three stages run before program
checking; the remaining four are the detailed program checker's fixed order.

Σ conformance sits at position 2 because it is a precondition for reading the
policy as patterns at all: both the R12 Path-B validator and support inference
instantiate patterns, and both should be entitled to assume well-sortedness
rather than re-derive it. Running it after duplicate-rule detection means the
stage never has to reason about which of two same-named rules it is checking.

The finite ground atoms of the environment — Γ's leaf conclusions, the backend
theory table, and the queried claim atoms — are passed in as `ground` rather
than read off the unit, because `Unit` deliberately carries Γ as a *function*.
They are checked inside this stage, in the same position the Haskell mirror
checks them, so the two drivers cannot disagree about which stage rejects
first. Successful construction carries that checker's
exact retained-node cache, so it neither rechecks support terms nor asks
callers to provide alignment proofs. Manual proof-level construction of
`CheckedUnit` still requires every invariant.

Since `lara-core@0.3` a unit whose arguments all type is accepted even when
some leave a mandatory question open (spec §4.4). Those arguments are located
holes: they are carried by `CheckedUnit.holes` with their checked declaration
indices, stay out of the AF, and cannot change any claim's status. The raw
facts the checker establishes about every declaration are exposed by
`CheckUnitSound` directly, and the hole-free specializations
(`args_eq_of_complete`, `atts_eq_of_complete`) recover the earlier exact
correspondence under the stronger all-complete premise.
-/

import Lara.Unit
import Lara.Check.Program

namespace Lara.Check.Unit

open Lara Lara.Support Lara.Attack

/-- Which clause of stage 2 failed. Every arm is rejection class R2; the payload
is the located diagnostic, which never reaches the wire (the wire carries the
class atom only). -/
inductive SignatureFault where
  | malformedSigma
  | policyIllSorted
  | groundIllSorted
  | argsIllSorted
deriving DecidableEq

/-- Closed diagnostics for whole-unit acceptance. -/
inductive UnitError where
  | duplicateRule : Policy.DuplicateRule → UnitError
  | signature : SignatureFault → UnitError
  | scopeViolation : Policy.ScopeViolation → UnitError
  | policyViolation : Policy.Violation → UnitError
  | program : ProgramError → UnitError
deriving DecidableEq

/-- Only the signature stage, policy R12, and wrapped frozen checker failures
have rejection classes.  Structural duplicate-rule errors preserve their typed
payload without inventing a frozen rejection class. -/
def UnitError.rejectClass : UnitError → Option RejectClass
  | .duplicateRule _ => none
  | .signature _ => some .R2
  | .scopeViolation _ => some .R12
  | .policyViolation _ => some .R12
  | .program error => error.rejectClass

/-- Stage 2, in the Haskell mirror's order: Σ itself, then the policy's
patterns, then the environment's ground atoms, then θ. -/
def signatureStage (ground : List Atom) (unit : Lara.Unit) : Option SignatureFault :=
  if Sigma.sigmaWellFormed unit.sigma = false then some .malformedSigma
  else if Lara.policyWellSorted unit.sigma unit.policy = false then some .policyIllSorted
  else if Lara.groundWellSorted unit.sigma ground = false then some .groundIllSorted
  else if Lara.argsWellSorted unit.sigma unit.policy unit.args = false then
    some .argsIllSorted
  else none

/-- Well-sortedness of an argument list survives filtering. -/
theorem termsWellSorted_filter (sg : Sigma.Sigma) (P : Policy.Policy)
    (p : Support.SupportTerm → Bool) :
    ∀ (l : List Support.SupportTerm),
      Lara.termsWellSorted sg P l = true →
      Lara.termsWellSorted sg P (l.filter p) = true
  | [], _ => rfl
  | w :: ws, h => by
      simp only [Lara.termsWellSorted, Bool.and_eq_true] at h
      have ih := termsWellSorted_filter sg P p ws h.2
      by_cases hp : p w = true
      · simp [hp, Lara.termsWellSorted, h.1, ih]
      · simp [hp, ih]

/-! ### The three facts stage 2 establishes

Each is read straight off the deterministic scan: `signatureStage` returning
`none` means every guard fell through, so each guarded condition is `false`,
i.e. the corresponding check is `true`. -/

theorem signatureStage_sigma_wf {ground : List Atom} {unit : Lara.Unit}
    (h : signatureStage ground unit = none) :
    Sigma.sigmaWellFormed unit.sigma = true := by
  unfold signatureStage at h
  by_cases h1 : Sigma.sigmaWellFormed unit.sigma = false
  · rw [if_pos h1] at h; exact absurd h (by simp)
  · exact Bool.not_eq_false _ |>.mp h1

theorem signatureStage_policy {ground : List Atom} {unit : Lara.Unit}
    (h : signatureStage ground unit = none) :
    Lara.policyWellSorted unit.sigma unit.policy = true := by
  unfold signatureStage at h
  by_cases h1 : Sigma.sigmaWellFormed unit.sigma = false
  · rw [if_pos h1] at h; exact absurd h (by simp)
  · rw [if_neg h1] at h
    by_cases h2 : Lara.policyWellSorted unit.sigma unit.policy = false
    · rw [if_pos h2] at h; exact absurd h (by simp)
    · exact Bool.not_eq_false _ |>.mp h2

theorem signatureStage_ground {ground : List Atom} {unit : Lara.Unit}
    (h : signatureStage ground unit = none) :
    Lara.groundWellSorted unit.sigma ground = true := by
  unfold signatureStage at h
  by_cases h1 : Sigma.sigmaWellFormed unit.sigma = false
  · rw [if_pos h1] at h; exact absurd h (by simp)
  · rw [if_neg h1] at h
    by_cases h2 : Lara.policyWellSorted unit.sigma unit.policy = false
    · rw [if_pos h2] at h; exact absurd h (by simp)
    · rw [if_neg h2] at h
      by_cases h3 : Lara.groundWellSorted unit.sigma ground = false
      · rw [if_pos h3] at h; exact absurd h (by simp)
      · exact Bool.not_eq_false _ |>.mp h3

theorem signatureStage_args {ground : List Atom} {unit : Lara.Unit}
    (h : signatureStage ground unit = none) :
    Lara.argsWellSorted unit.sigma unit.policy unit.args = true := by
  unfold signatureStage at h
  by_cases h1 : Sigma.sigmaWellFormed unit.sigma = false
  · rw [if_pos h1] at h; exact absurd h (by simp)
  · rw [if_neg h1] at h
    by_cases h2 : Lara.policyWellSorted unit.sigma unit.policy = false
    · rw [if_pos h2] at h; exact absurd h (by simp)
    · rw [if_neg h2] at h
      by_cases h3 : Lara.groundWellSorted unit.sigma ground = false
      · rw [if_pos h3] at h; exact absurd h (by simp)
      · rw [if_neg h3] at h
        by_cases h4 : Lara.argsWellSorted unit.sigma unit.policy unit.args = false
        · rw [if_pos h4] at h; exact absurd h (by simp)
        · exact Bool.not_eq_false _ |>.mp h4

/-- The canonical executable constructor for proof-bearing accepted units. -/
def checkUnit {canon : String → String}
    (Gamma : LeafId → Option Atom) (reg : BackendRegistry canon)
    (ground : List Atom) (unit : Lara.Unit) :
    Except UnitError (Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)) :=
  match hduplicate : Policy.firstDuplicateRuleId? unit.policy.rules with
  | some duplicate => .error (.duplicateRule duplicate)
  | none =>
      match hsignature : signatureStage ground unit with
      | some fault => .error (.signature fault)
      | none =>
          match hscope : Policy.firstOutOfScope? unit.policy with
          | some scope => .error (.scopeViolation scope)
          | none =>
          match hviolation : Policy.firstViolation? canon unit.policy with
          | some violation => .error (.policyViolation violation)
          | none =>
              match checkProgramDetailed unit.policy.ruleLookup Gamma reg
                  unit.policy.defeat unit.args unit.atts with
              | .error error => .error (.program error)
              | .ok accepted =>
                  .ok
                    { sigma := unit.sigma
                    , policy := unit.policy
                    , ruleIds_nodup :=
                        (Policy.firstDuplicateRuleId?_none_iff
                          unit.policy.rules).mp hduplicate
                    , sigma_wf := signatureStage_sigma_wf hsignature
                    , policy_well_sorted := signatureStage_policy hsignature
                    , scopes_wf := hscope
                    , policy_wf :=
                        (Policy.firstViolation_none_iff).mp hviolation
                    , program := accepted.program
                    , attack_complete := accepted.attack_complete
                    , nodes := accepted.nodes
                    , nodes_terms := accepted.nodes_terms
                    , nodeDecls := accepted.nodeDecls
                    , holes := accepted.holes
                    , holes_terms := accepted.holes_terms
                    , args_well_sorted := by
                        rw [accepted.arguments_eq]
                        exact termsWellSorted_filter _ _ _ _
                          (signatureStage_args hsignature) }

/-- The facts supplied by successful unit checking. Named projections keep
clients independent of the order in which these obligations are recorded. The
`raw_*` fields and `signature_ok` are what the checker established about the
supplied declarations, holes included; `args_eq`, `holes_eq` and `atts_eq`
relate the compiled program to the specification views of `Check.Program`;
`partition` locates every checked declaration as an AF node or a hole. -/
structure CheckUnitSound (canon : String → String)
    (Gamma : LeafId → Option Atom) (reg : BackendRegistry canon)
    (ground : List Atom) (unit : Lara.Unit)
    (accepted : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)) : Prop where
  sigma_eq : accepted.sigma = unit.sigma
  sigma_wf : Sigma.sigmaWellFormed accepted.sigma = true
  policy_sorted : Lara.policyWellSorted accepted.sigma accepted.policy = true
  ground_sorted : Lara.groundWellSorted accepted.sigma ground = true
  args_sorted : Lara.argsWellSorted accepted.sigma accepted.policy accepted.program.args = true
  policy_eq : accepted.policy = unit.policy
  ruleIds_nodup : (accepted.policy.rules.map (·.id)).Nodup
  policy_wf : Policy.WellFormed canon accepted.policy
  signature_ok : signatureStage ground unit = none
  raw_sorted : Lara.argsWellSorted unit.sigma unit.policy unit.args = true
  raw_nodup : unit.args.Nodup
  raw_support : ∀ w ∈ unit.args, ∃ C O,
    HasSupport canon unit.policy.ruleLookup Gamma (certOkOf reg) w C O
  raw_typed : ∀ k ∈ unit.atts,
    HasAttack canon unit.policy.ruleLookup Gamma (certOkOf reg)
      unit.policy.defeat k
  raw_source : ∀ k ∈ unit.atts, k.source ∈ unit.args
  raw_target : ∀ k ∈ unit.atts, k.target ∈ unit.args
  args_eq : accepted.program.args =
    completeArgs unit.policy.ruleLookup Gamma reg unit.args
  holes_eq : accepted.program.holes =
    holeArgs unit.policy.ruleLookup Gamma reg unit.args
  atts_eq : accepted.program.atts = liveAttacks accepted.program.args unit.atts
  attack_complete : Compile.AttackComplete canon accepted.policy.ruleLookup Gamma
    (certOkOf reg) accepted.policy.defeat accepted.program.args accepted.program.atts
  nodes_terms : accepted.nodes.map (·.term) = accepted.program.args
  partition : DeclPartition unit.args accepted.nodes accepted.nodeDecls
    accepted.holes

/-- Successful executable acceptance exposes every field of `CheckedUnit` by
its public name, together with the raw facts about the declaration lists
supplied to the checker and their exact partition into nodes and holes. -/
theorem checkUnit_sound {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {ground : List Atom} {unit : Lara.Unit}
    {accepted : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (h : checkUnit Gamma reg ground unit = .ok accepted) :
    CheckUnitSound canon Gamma reg ground unit accepted := by
  unfold checkUnit at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · split at h
          · contradiction
          · rename_i _ hsignature _ _ _ programAcceptance hprogram
            have hacc := Except.ok.inj h
            subst hacc
            exact {
              sigma_eq := rfl
              sigma_wf := signatureStage_sigma_wf hsignature
              policy_sorted := signatureStage_policy hsignature
              ground_sorted := signatureStage_ground hsignature
              args_sorted := by
                rw [programAcceptance.arguments_eq]
                exact termsWellSorted_filter _ _ _ _
                  (signatureStage_args hsignature)
              policy_eq := rfl
              ruleIds_nodup :=
                (Policy.firstDuplicateRuleId?_none_iff unit.policy.rules).mp (by assumption)
              policy_wf := (Policy.firstViolation_none_iff).mp (by assumption)
              signature_ok := hsignature
              raw_sorted := signatureStage_args hsignature
              raw_nodup := programAcceptance.raw_nodup
              raw_support := programAcceptance.raw_support
              raw_typed := programAcceptance.raw_typed
              raw_source := programAcceptance.raw_source
              raw_target := programAcceptance.raw_target
              args_eq := programAcceptance.arguments_eq
              holes_eq := programAcceptance.holes_eq
              atts_eq := programAcceptance.attacks_eq
              attack_complete := programAcceptance.attack_complete
              nodes_terms := programAcceptance.nodes_terms
              partition := programAcceptance.partition }

/-- **Exact completeness with located holes.** The premises are the raw policy
and detailed-program obligations checked in the public fixed order, with every
declared argument required only to type, complete or not. Attack completeness
constrains complete arguments alone, which is all `AttackComplete` asks. -/
theorem checkUnit_complete_holes {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {ground : List Atom} {unit : Lara.Unit}
    (hsignature : signatureStage ground unit = none)
    (hscope : Policy.firstOutOfScope? unit.policy = none)
    (hruleIds : (unit.policy.rules.map (·.id)).Nodup)
    (hpolicy : Policy.WellFormed canon unit.policy)
    (hargs : unit.args.Nodup)
    (hsupport : ∀ w ∈ unit.args, ∃ C O,
      HasSupport canon unit.policy.ruleLookup Gamma (certOkOf reg) w C O)
    (htyped : ∀ k ∈ unit.atts,
      HasAttack canon unit.policy.ruleLookup Gamma (certOkOf reg)
        unit.policy.defeat k)
    (hsource : ∀ k ∈ unit.atts, k.source ∈ unit.args)
    (htarget : ∀ k ∈ unit.atts, k.target ∈ unit.args)
    (hattackComplete :
      Compile.AttackComplete canon unit.policy.ruleLookup Gamma
        (certOkOf reg) unit.policy.defeat unit.args unit.atts) :
    ∃ accepted, checkUnit Gamma reg ground unit = .ok accepted := by
  have hduplicate :
      Policy.firstDuplicateRuleId? unit.policy.rules = none :=
    (Policy.firstDuplicateRuleId?_none_iff unit.policy.rules).mpr hruleIds
  have hviolation : Policy.firstViolation? canon unit.policy = none :=
    (Policy.firstViolation_none_iff).mpr hpolicy
  obtain ⟨programAcceptance, hprogram⟩ :=
    checkProgramDetailed_complete_holes hargs hsupport htyped hsource htarget
      hattackComplete
  unfold checkUnit
  split
  · rename_i duplicate hfound
    rw [hduplicate] at hfound
    contradiction
  · split
    · rename_i fault hfound
      rw [hsignature] at hfound
      contradiction
    · split
      · rename_i scope hfound
        rw [hscope] at hfound
        contradiction
      · split
        · rename_i violation hfound
          rw [hviolation] at hfound
          contradiction
        · split
          · rename_i error hfound
            rw [hprogram] at hfound
            contradiction
          · rename_i found hfound
            have hfound_eq : found = programAcceptance :=
              Except.ok.inj (hfound.symm.trans hprogram)
            subst found
            exact ⟨_, rfl⟩

/-- Exact completeness of the unit checker for hole-free units: the
all-complete corollary of `checkUnit_complete_holes`. -/
theorem checkUnit_complete {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {ground : List Atom} {unit : Lara.Unit}
    (hsignature : signatureStage ground unit = none)
    (hscope : Policy.firstOutOfScope? unit.policy = none)
    (hruleIds : (unit.policy.rules.map (·.id)).Nodup)
    (hpolicy : Policy.WellFormed canon unit.policy)
    (hargs : unit.args.Nodup)
    (hsupport : ∀ w ∈ unit.args, ∃ C,
      HasSupport canon unit.policy.ruleLookup Gamma (certOkOf reg) w C [])
    (htyped : ∀ k ∈ unit.atts,
      HasAttack canon unit.policy.ruleLookup Gamma (certOkOf reg)
        unit.policy.defeat k)
    (hsource : ∀ k ∈ unit.atts, k.source ∈ unit.args)
    (htarget : ∀ k ∈ unit.atts, k.target ∈ unit.args)
    (hattackComplete :
      Compile.AttackComplete canon unit.policy.ruleLookup Gamma
        (certOkOf reg) unit.policy.defeat unit.args unit.atts) :
    ∃ accepted, checkUnit Gamma reg ground unit = .ok accepted :=
  checkUnit_complete_holes hsignature hscope hruleIds hpolicy hargs
    (fun w hw => let ⟨C, hC⟩ := hsupport w hw; ⟨C, [], hC⟩)
    htyped hsource htarget hattackComplete

/-! ### Hole-free specializations

Each states the stronger all-complete premise explicitly and recovers the exact
correspondence between the compiled program and the raw declarations that held
for every accepted unit up to `lara-core@0.2`. -/

section Specializations

variable {canon : String → String} {Gamma : LeafId → Option Atom}
  {reg : BackendRegistry canon} {ground : List Atom} {unit : Lara.Unit}
  {accepted : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}

/-- With every declared argument complete, the AF arguments are exactly the
declarations. -/
theorem CheckUnitSound.args_eq_of_complete
    (hs : CheckUnitSound canon Gamma reg ground unit accepted)
    (h : ∀ w ∈ unit.args, ∃ C,
      HasSupport canon unit.policy.ruleLookup Gamma (certOkOf reg) w C []) :
    accepted.program.args = unit.args :=
  hs.args_eq.trans (completeArgs_eq_self h)

/-- With every declared argument complete, the compiled attacks are exactly
the declared attacks. -/
theorem CheckUnitSound.atts_eq_of_complete
    (hs : CheckUnitSound canon Gamma reg ground unit accepted)
    (h : ∀ w ∈ unit.args, ∃ C,
      HasSupport canon unit.policy.ruleLookup Gamma (certOkOf reg) w C []) :
    accepted.program.atts = unit.atts := by
  rw [hs.atts_eq, hs.args_eq_of_complete h]
  exact liveAttacks_eq_self hs.raw_source

/-- With every declared argument complete, there is no hole. -/
theorem CheckUnitSound.holes_eq_nil_of_complete
    (hs : CheckUnitSound canon Gamma reg ground unit accepted)
    (h : ∀ w ∈ unit.args, ∃ C,
      HasSupport canon unit.policy.ruleLookup Gamma (certOkOf reg) w C []) :
    accepted.program.holes = [] ∧ accepted.holes = [] := by
  have hprogram : accepted.program.holes = [] :=
    hs.holes_eq.trans (holeArgs_eq_nil h)
  refine ⟨hprogram, ?_⟩
  have hterms := accepted.holes_terms
  rw [hprogram] at hterms
  exact List.map_eq_nil_iff.mp hterms

end Specializations

/-! ### The located-gap guarantee (spec §4.4, §8) -/

section LocatedGap

variable {canon : String → String} {Gamma : LeafId → Option Atom}
  {reg : BackendRegistry canon} {ground : List Atom} {unit : Lara.Unit}
  {accepted : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}

/-- **Holes are exactly the open declarations.** Under the support typing every
accepted declaration has, checked declaration `i` is reported as a hole iff its
root obligation set is nonempty, and the report carries exactly that term,
conclusion and obligation set. -/
theorem CheckUnitSound.holes_iff
    (hs : CheckUnitSound canon Gamma reg ground unit accepted)
    {i : Nat} {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (hi : unit.args[i]? = some w)
    (hw : HasSupport canon unit.policy.ruleLookup Gamma (certOkOf reg) w C O) :
    (∃ h ∈ accepted.holes, h.index = i) ↔ O ≠ [] := by
  rw [← hs.policy_eq] at hw
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hat := hs.partition.hole_decls h hh
    rw [hi, Option.some.injEq] at hat
    subst hat
    exact (hasSupport_unique h.valid hw).2 ▸ h.nonempty
  · intro hO
    have hlt : i < unit.args.length := lt_of_getElem?_some hi
    rcases (hs.partition.cover i).mp hlt with hnode | hhole
    · exfalso
      obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hnode
      have hmap := congrArg (·[n]?) hs.partition.node_decls
      simp only [List.getElem?_map, hn, Option.map_some, hi] at hmap
      cases hnodeAt : accepted.nodes[n]? with
      | none => rw [hnodeAt] at hmap; cases hmap
      | some node =>
        rw [hnodeAt] at hmap
        simp only [Option.map_some, Option.some.injEq] at hmap
        rw [hmap] at hw
        exact hO (hasSupport_unique node.valid hw).2.symm
    · exact hhole

/-- The reported record of a hole is exactly its cached judgment: its term is
the declaration at its index, and its conclusion and obligations are the ones
the declaration types with. -/
theorem CheckUnitSound.hole_reports_exact
    (hs : CheckUnitSound canon Gamma reg ground unit accepted)
    {h : Compile.CheckedHole canon accepted.policy.ruleLookup Gamma
      (certOkOf reg)} (hh : h ∈ accepted.holes)
    {C : Atom} {O : List QuestionId}
    (hw : HasSupport canon unit.policy.ruleLookup Gamma (certOkOf reg)
      h.term C O) :
    unit.args[h.index]? = some h.term ∧ h.conclusion = C ∧ h.obligations = O := by
  rw [← hs.policy_eq] at hw
  exact ⟨hs.partition.hole_decls h hh, hasSupport_unique h.valid hw⟩

/-- **Attacks sourced at a hole are inert (D4).** Such a raw attack is not
compiled, and no edge leaves its source. -/
theorem CheckUnitSound.hole_inert_source
    (hs : CheckUnitSound canon Gamma reg ground unit accepted)
    {k : Attack} (hsource : k.source ∈ accepted.program.holes) :
    k ∉ accepted.program.atts ∧
      ∀ b, ¬ Compile.Edge accepted.program k.source b := by
  have hnotArg : k.source ∉ accepted.program.args := by
    rw [hs.holes_eq] at hsource
    rw [hs.args_eq]
    intro hc
    exact completeArgs_holeArgs_disjoint hc hsource
  refine ⟨fun hk => ?_, Compile.no_edge_of_not_arg accepted.program hnotArg⟩
  rw [hs.atts_eq] at hk
  exact hnotArg (mem_liveAttacks_iff.mp hk).2

end LocatedGap

/-- **A claim with no complete support is `gap` (spec §8).** If no retained
complete node concludes `p`, then any claim whose support indices name nodes
concluding `p` has status `gap`. This holds whatever the claim lists as holes:
holes concluding `p` never count as support. -/
theorem gap_of_only_holes {canon : String → String}
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (unit : Lara.Unit.CheckedUnit canon Gamma CertOk) {p : Atom}
    {c : Grounded.Claim}
    (hsupport : ∀ i ∈ c.support, ∃ node, unit.nodes[i]? = some node ∧
      equiv canon node.conclusion p)
    (hnone : ∀ node ∈ unit.nodes, ¬ equiv canon node.conclusion p) :
    Grounded.statusC (Compile.checkedAF unit.program) c = .gap := by
  apply (Grounded.statusC_gap_iff _ c).mpr
  cases hc : c.support with
  | nil => rfl
  | cons i is =>
    obtain ⟨node, hnode, hequiv⟩ := hsupport i (by simp [hc])
    exact absurd hequiv (hnone node (List.mem_of_getElem? hnode))

/-! ### Naming a successful check's accepted output

The generated families and closed fixtures all follow one assembly: prove a
checker call succeeds, name the accepted payload, and export the `.ok`
equation for that name. `okValue`/`okValue_eq` package the assembly once —
`checkUnit_complete` supplies the existential directly, and
`exists_ok_of_isOk` admits the closed fixtures' decidable `isOk` form. -/

/-- A decidably successful `Except` is an `.ok`. -/
theorem exists_ok_of_isOk {ε α : Type _} {e : Except ε α}
    (h : e.isOk = true) : ∃ a, e = .ok a := by
  cases e with
  | error _ => simp [Except.isOk, Except.toBool] at h
  | ok a => exact ⟨a, rfl⟩

/-- The accepted payload of a checker call known to succeed. -/
def okValue {ε α : Type _} {e : Except ε α} (h : ∃ a, e = .ok a) : α :=
  e.toOption.get (by obtain ⟨a, rfl⟩ := h; rfl)

/-- The `.ok` equation for the named payload. -/
theorem okValue_eq {ε α : Type _} {e : Except ε α} (h : ∃ a, e = .ok a) :
    e = .ok (okValue h) := by
  cases e with
  | error _ => exact h.elim fun a ha => nomatch ha
  | ok a => rfl

private theorem lookupSubst_mem {θ : Subst} {x : VarId} {t : Term}
    (h : lookupSubst θ x = some t) : (x, t) ∈ θ := by
  induction θ with
  | nil => simp [lookupSubst] at h
  | cons b rest ih =>
      rcases b with ⟨y, u⟩
      simp only [lookupSubst] at h
      split at h
      · rename_i heq
        subst y
        simp only [Option.some.injEq] at h
        subst u
        simp
      · exact List.mem_cons_of_mem _ (ih h)

theorem thetaWellSorted_sortRespecting
    {sg : Sigma.Sigma} {r : Rule} {env : Sigma.ParamSorts} {θ : Subst}
    (hθ : Lara.thetaWellSorted sg r env θ = true)
    (hdom : ∀ x : VarId, x ∈ θ.map Prod.fst ↔ x ∈ r.params) :
    Sigma.SortRespecting sg env θ := by
  intro x s henv t ht
  have hpair : (x, t) ∈ θ := lookupSubst_mem ht
  have hxθ : x ∈ θ.map Prod.fst := List.mem_map.mpr ⟨(x, t), hpair, rfl⟩
  have hxparams : x ∈ r.params := (hdom x).mp hxθ
  have hchecked := List.all_eq_true.mp hθ (x, t) hpair
  have hcontains : r.params.contains x = true := by
    simpa using hxparams
  simp only [hcontains, if_true] at hchecked
  cases hsort : Sigma.sortOf sg t with
  | none => simp [hsort] at hchecked
  | some actual =>
      simp only [hsort, henv] at hchecked
      have heq : actual = s := of_decide_eq_true hchecked
      subst actual
      rfl

theorem thetaWellSorted_ruleSortRespecting
    {sg : Sigma.Sigma} {r : Rule} {env : Sigma.ParamSorts} {θ : Subst}
    (henv : Sigma.ruleParamSorts sg r = some env)
    (hθ : Lara.thetaWellSorted sg r env θ = true)
    (hdom : ∀ x : VarId, x ∈ θ.map Prod.fst ↔ x ∈ r.params) :
    Sigma.RuleSortRespecting sg r θ := by
  intro env' henv'
  have henvEq : env' = env := Option.some.inj (henv'.symm.trans henv)
  subst env'
  exact thetaWellSorted_sortRespecting hθ hdom

private theorem termsWellSorted_mem {sg : Sigma.Sigma} {P : Policy.Policy}
    {ws : List SupportTerm} (h : Lara.termsWellSorted sg P ws = true)
    {w : SupportTerm} (hw : w ∈ ws) :
    Lara.termWellSorted sg P w = true := by
  induction ws with
  | nil => simp at hw
  | cons u us ih =>
      simp only [Lara.termsWellSorted, Bool.and_eq_true] at h
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact h.1
      · exact ih h.2 hw

private theorem dischargesWellSorted_mem
    {sg : Sigma.Sigma} {P : Policy.Policy}
    {D : List (QuestionId × SupportTerm)}
    (h : Lara.dischargesWellSorted sg P D = true)
    {d : QuestionId × SupportTerm} (hd : d ∈ D) :
    Lara.termWellSorted sg P d.2 = true := by
  induction D with
  | nil => simp at hd
  | cons e es ih =>
      simp only [Lara.dischargesWellSorted, Bool.and_eq_true] at h
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact h.1
      · exact ih h.2 hd

private theorem allInstancesWellSortedList_iff
    {sg : Sigma.Sigma} {Pi : RuleId → Option Rule}
    {ws : List SupportTerm} :
    Lara.AllInstancesWellSortedList sg Pi ws ↔
      ∀ w ∈ ws, Lara.AllInstancesWellSorted sg Pi w := by
  induction ws with
  | nil => simp [Lara.AllInstancesWellSortedList]
  | cons w ws ih =>
      simp [Lara.AllInstancesWellSortedList, ih]

private theorem allInstancesWellSortedDischarges_iff
    {sg : Sigma.Sigma} {Pi : RuleId → Option Rule}
    {D : List (QuestionId × SupportTerm)} :
    Lara.AllInstancesWellSortedDischarges sg Pi D ↔
      ∀ d ∈ D, Lara.AllInstancesWellSorted sg Pi d.2 := by
  induction D with
  | nil => simp [Lara.AllInstancesWellSortedDischarges]
  | cons d D ih =>
      simp [Lara.AllInstancesWellSortedDischarges, ih]

private theorem hasSupport_allInstancesWellSorted
    {canon : String → String} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {sg : Sigma.Sigma} {P : Policy.Policy}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (hs : HasSupport canon P.ruleLookup Gamma CertOk w C O)
    (hws : Lara.termWellSorted sg P w = true) :
    Lara.AllInstancesWellSorted sg P.ruleLookup w := by
  induction hs with
  | leaf =>
      trivial
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis ihprems ihdis =>
      simp only [Lara.termWellSorted, hside.rule] at hws
      cases henv : Sigma.ruleParamSorts sg r with
      | none => simp [henv] at hws
      | some env =>
          simp only [henv, Bool.and_eq_true] at hws
          refine ⟨?_, ?_, ?_⟩
          · intro r' hr'
            have hr : r' = r := Option.some.inj (hr'.symm.trans hside.rule)
            subst r'
            have hrespect :=
              thetaWellSorted_ruleSortRespecting henv hws.1.1 hside.θDom
            exact Sigma.wellSorted_rule henv (hrespect env henv)
          · rw [allInstancesWellSortedList_iff]
            intro w hw
            obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
            have hiLt := lt_of_getElem?_some hi
            obtain ⟨A, hA⟩ := getElem?_some_of_lt Cs i
              (by have := hside.lenCs; omega)
            obtain ⟨O', hO⟩ := getElem?_some_of_lt Os i
              (by have := hside.lenOs; omega)
            exact ihprems i w A O' hi hA hO
              (termsWellSorted_mem hws.1.2 hw)
          · rw [allInstancesWellSortedDischarges_iff]
            intro d hd
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hd
            have hjLt := lt_of_getElem?_some hj
            rcases d with ⟨q, w⟩
            obtain ⟨A, hA⟩ := getElem?_some_of_lt DCs j
              (by have := hside.lenDCs; omega)
            obtain ⟨O', hO⟩ := getElem?_some_of_lt DOs j
              (by have := hside.lenDOs; omega)
            exact ihdis j q w A O' hj hA hO
              (dischargesWellSorted_mem hws.2 hd)

/-! ### Result 13(c): accepted support instances and their ground environment

The statement the paper cites, and the justification for the per-instance half
of stage 2 being as thin as it is. It derives the following acceptance facts
from the executable checks:

* Σ itself is well-formed, so `sortOf` is total on declared data;
* every ground atom the environment contributed — Γ's leaf conclusions, the
  backend theory table, and the queried claim atoms — is well-sorted;
* every premise, conclusion, and critical-question answer instantiated by an
  actual rule instance recursively reachable through an accepted support term
  is well-sorted.

The bridge uses both executable halves that constrain an actual θ: stage 2
checks its range terms, while accepted support supplies R3's exact-domain
invariant. Nothing checks the instantiated atoms directly; they are reached
through `Sigma.wellSorted_rule`, the substitution lemma. -/
theorem checkUnit_wellSorted {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {ground : List Atom} {unit : Lara.Unit}
    {accepted : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (h : checkUnit Gamma reg ground unit = .ok accepted) :
    Sigma.sigmaWellFormed accepted.sigma = true ∧
    (∀ a ∈ ground, Sigma.WellSorted accepted.sigma a) ∧
    (∀ w ∈ accepted.program.args,
      Lara.AllInstancesWellSorted accepted.sigma accepted.policy.ruleLookup w) := by
  have hs := checkUnit_sound h
  have hwf := hs.sigma_wf
  have hground := hs.ground_sorted
  have hargs := hs.args_sorted
  refine ⟨hwf, ?_, ?_⟩
  · intro a ha
    unfold Lara.groundWellSorted at hground
    exact List.all_eq_true.mp hground a ha
  · intro w hw
    obtain ⟨C, hsupport⟩ := accepted.program.complete w hw
    exact hasSupport_allInstancesWellSorted hsupport
      (termsWellSorted_mem hargs hw)

end Lara.Check.Unit
