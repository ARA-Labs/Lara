/-
Executable axiom-withdrawal witness (#350). This is a separate Lean
structural-contract example, not an extension of `lara pw` or CheckInput.
The source certifies the assumed postulate itself using the production ND
backend and an empty theory. Admission computes both checking environments.
-/
import Lara.Admission
import Lara.Driver
import Lara.PW.Structural

namespace Lara.Examples.AxiomWithdrawal

open Lara.Support Lara.Admission Lara.Check.Unit
open Lara.PW Lara.PW.Instance
open Lara.Presentation (Admission)

def postulate : Atom := .atom "parallel_postulate" .nil
def premise : LeafId := ⟨"pp"⟩
def citation : RuleId := ⟨"citation"⟩
def digest : Digest := ⟨"sha256:empty"⟩
def certificate : CertRef := ⟨.list [.atom "hyp", .atom "0"]⟩
def reg : BackendRegistry Driver.dcanon := Driver.buildRegistry [(digest, [])]
def rule : Rule :=
  { mode := .strict, params := [], premises := [⟨⟨"parallel_postulate"⟩, .nil⟩]
  , concl := ⟨⟨"parallel_postulate"⟩, .nil⟩, questions := [], allowTrusted := false
  , certifiers := [(Driver.ndBackendId, digest)] }
def policy : Policy.Policy := { rules := [⟨citation, rule⟩], defeat := ⟨[], []⟩ }
def sigma : Sigma.Sigma := { sorts := [], cons := [], preds := [⟨⟨"parallel_postulate"⟩, []⟩] }
def support : SupportTerm :=
  .inst citation [] [.leaf premise] [] [] (.cert Driver.ndBackendId digest certificate)
def args : List (String × SupportTerm) := [("a", support)]
def aligned : AlignedAttacks args [] := ⟨[], rfl, by decide⟩
def table (action : Admission) : List AdmissionRow :=
  [⟨(.assumed, .aiExecuted), action⟩]
def admission (action : Admission) : SourceAdmission :=
  evaluateAdmission Driver.dcanon (table action) [⟨premise, .assumed, .aiExecuted⟩]
    [(premise, postulate)] args [] [] aligned
def result? (action : Admission) : Option AdmissionResult :=
  match admission action with
  | .accepted result => some result
  | _ => none
def retained : AdmissionResult := (result? .admit).get (by decide)
def withdrawn : AdmissionResult := (result? .quarantine).get (by decide)
def gamma (result : AdmissionResult) := Admission.buildGamma result.prune.checkedLeaves

/-- Quarantine succeeds as admission, removing the premise and its dependent
argument. It does not create a rejected source or a defeated argument. -/
theorem withdrawal_prunes :
    withdrawn.prune.checkedLeaves = [] ∧ withdrawn.prune.keptArgs = [] ∧
    withdrawn.audit.leaves = [(premise, [.policy])] ∧ withdrawn.audit.args = ["a"] := by cbv

/-- Reject stops admission and cannot supply a target checking environment. -/
theorem rejection_stops :
    admission .reject = .rejected ⟨premise, .assumed, .aiExecuted,
      ⟨(.assumed, .aiExecuted), .reject⟩⟩ ∧ result? .reject = none := by
  constructor <;> rfl

/-- Real ND replay accepts hypothesis reuse, but cannot replay it without the
premise. Both calls use the same empty theory and certificate. -/
theorem certificate_depends_on_premise :
    certOkBOf reg Driver.ndBackendId digest certificate [postulate] postulate = true ∧
    certOkBOf reg Driver.ndBackendId digest certificate [] postulate = false := by cbv


def rawUnit (result : AdmissionResult) : Lara.Unit :=
  { sigma := sigma, policy := policy, args := result.prune.keptArgs.map (·.2)
  , atts := result.prune.keptAttacks }
def checked (result : AdmissionResult) :=
  checkUnit (gamma result) reg [postulate] (rawUnit result)

theorem source_support :
    HasSupport Driver.dcanon policy.ruleLookup (gamma retained) (certOkOf reg)
      support postulate [] := by
  apply Lara.Check.inferSupport_sound (result := ⟨postulate, []⟩) (loc := .root)
  cbv

def ctx (result : AdmissionResult) : Context :=
  { canon := Driver.dcanon, Gamma := gamma result, CertOk := certOkOf reg
  , sigma := sigma, policy := policy }

/-- Assemble a proof-bearing world from the admitted program's checked nodes.
This avoids reducing the checker's dependent proof record during each status
calculation. `units_accepted` separately proves the production checker accepts
these exact admitted programs. -/
def world (result : AdmissionResult)
    (nodes : List (Compile.CheckedNode Driver.dcanon policy.ruleLookup
      (gamma result) (certOkOf reg)))
    (hnodes : nodes.map (·.term) = (rawUnit result).args)
    (hnodup : (rawUnit result).args.Nodup)
    (hatts : (rawUnit result).atts = [])
    (hsig : signatureStage [postulate] (rawUnit result) = none) : World (ctx result) where
  unit :=
    { sigma := sigma, policy := policy
    , ruleIds_nodup := by decide
    , sigma_wf := signatureStage_sigma_wf hsig
    , policy_well_sorted := signatureStage_policy hsig
    , scopes_wf := by decide
    , policy_wf := (Policy.firstViolation_none_iff).mp (by
        change Policy.firstViolation? Driver.dcanon policy = none
        decide)
    , program :=
        { args := (rawUnit result).args, nodup := hnodup
        , complete := by
            intro w hw
            rw [← hnodes] at hw
            obtain ⟨node, _, rfl⟩ := List.mem_map.mp hw
            exact ⟨node.conclusion, node.valid⟩
        , atts := (rawUnit result).atts
        , typed := by simp [hatts]
        , source_declared := by simp [hatts]
        , target_declared := by simp [hatts] }
    , attack_complete := by
        intro _ _ _ _ _ _ _ _ hcontrary
        simp [Attack.ContraryMatch, policy] at hcontrary
    , nodes := nodes, nodes_terms := hnodes
    , args_well_sorted := signatureStage_args hsig }
  sigma_eq := rfl
  policy_eq := rfl

def source : World (ctx retained) :=
  world retained [⟨support, postulate, source_support⟩] rfl (by decide) rfl (by decide)
def target : World (ctx withdrawn) :=
  world withdrawn [] rfl (by decide) rfl (by decide)

/-- Both admitted programs satisfy every premise of the production unit
checker's exact completeness theorem, including support and attack coverage. -/
theorem units_accepted : (checked retained).isOk = true ∧
    (checked withdrawn).isOk = true := by
  constructor
  · obtain ⟨accepted, h⟩ := checkUnit_complete
      (Gamma := gamma retained) (reg := reg)
      (ground := [postulate]) (unit := rawUnit retained)
      (by decide) source.unit.scopes_wf source.unit.ruleIds_nodup
      source.unit.policy_wf source.unit.program.nodup source.unit.program.complete
      source.unit.program.typed source.unit.program.source_declared
      source.unit.program.target_declared source.unit.attack_complete
    change (checked retained).isOk = true
    rw [checked, h]
    rfl
  · obtain ⟨accepted, h⟩ := checkUnit_complete
      (Gamma := gamma withdrawn) (reg := reg)
      (ground := [postulate]) (unit := rawUnit withdrawn)
      (by decide) target.unit.scopes_wf target.unit.ruleIds_nodup
      target.unit.policy_wf target.unit.program.nodup target.unit.program.complete
      target.unit.program.typed target.unit.program.source_declared
      target.unit.program.target_declared target.unit.attack_complete
    change (checked withdrawn).isOk = true
    rw [checked, h]
    rfl

/-- The status change is a local observation, independent of any bridge edge. -/
theorem local_statuses : cmpStatus source postulate = .justified ∧
    cmpStatus target postulate = .gap := by decide

/-- Positive control: the retained assumption supplies a structural bridge.
The leaf and certificate clauses have live instances in `support`. -/
def retainedBridge : StructuralBridge Driver.dcanon policy.ruleLookup policy.ruleLookup
    (gamma retained) (gamma retained) (certOkOf reg) (certOkOf reg) :=
  .refl _ _ _ _

/-- T6 transports the checked certificate-bearing support in the positive
control. Neither the bridge nor this theorem asserts grounded preservation. -/
theorem retained_transport :
    ∃ C', trAtom retainedBridge.sym postulate = some C' ∧
      HasSupport Driver.dcanon policy.ruleLookup (gamma retained) (certOkOf reg)
        support C' [] :=
  support_transport_complete retainedBridge source_support (trSupport_id support)

/-- The finite identity-map leaf obligation, evaluated on the actual admitted
source table. This is an example check, not a new production bridge loader. -/
def leafCheck (targetGamma : LeafId → Option Atom) : Bool :=
  retained.prune.checkedLeaves.all (fun row => targetGamma row.1 == some row.2)

/-- The executable check decides precisely the identity bridge's leaf clause
for this source, not an author-supplied accepted/rejected edge flag. -/
theorem leafCheck_iff (targetGamma : LeafId → Option Atom) :
    leafCheck targetGamma = true ↔
      ∀ l p, gamma retained l = some p →
        ∃ p', trAtom SymMap.id p = some p' ∧ targetGamma l = some p' := by
  have hs : retained.prune.checkedLeaves = [(premise, postulate)] := by cbv
  simp only [leafCheck, hs, List.all_cons, List.all_nil, Bool.and_true, beq_iff_eq]
  constructor
  · intro h l p hp
    change (([(premise, postulate)].find? (fun e => decide (e.1 = l))).map (·.2)) = some p at hp
    by_cases hl : premise = l
    · subst l
      have he : postulate = p := by simpa using hp
      subst p
      exact ⟨postulate, trAtom_id postulate, h⟩
    · simp [hl] at hp
  · intro h
    obtain ⟨p', ht, hg⟩ := h premise postulate rfl
    rw [trAtom_id] at ht
    cases ht
    exact hg

theorem leaf_controls : leafCheck (gamma retained) = true ∧
    leafCheck (gamma withdrawn) = false := by cbv

/-- A missing target premise refutes the actual structural contract, even
if a caller tries a different symbol or leaf map. No bridge is constructed
and then marked rejected by declaration. -/
theorem no_withdrawn_bridge :
    ¬ Nonempty (StructuralBridge Driver.dcanon policy.ruleLookup policy.ruleLookup
      (gamma retained) (gamma withdrawn) (certOkOf reg) (certOkOf reg)) := by
  rintro ⟨B⟩
  obtain ⟨p', _, hp⟩ := B.leaf_ok premise postulate rfl
  change (none : Option Atom) = some p' at hp
  contradiction

end Lara.Examples.AxiomWithdrawal
