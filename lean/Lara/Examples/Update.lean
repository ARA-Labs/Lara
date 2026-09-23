/-
A closed source-update fixture exposing the add-instance coverage obligation.
-/

import Lara.Update
import Lara.Examples

namespace Lara.Examples.Update

open Lara Lara.Support Lara.Attack Lara.Compile Lara.Check

private def baseMetas : List Admission.LeafMeta :=
  [ { id := l1, kind := .observed, provenance := .user }
  , { id := l2, kind := .observed, provenance := .user } ]

private def baseArgs : List (String × SupportTerm) :=
  [("a", .leaf l1)]

private def baseDeclared : Admission.AlignedAttacks baseArgs [] :=
  { resolved := []
  , resolve_eq := rfl
  , ids_nodup := by decide }

private def baseAdmission : Admission.AdmissionResult :=
  { prune := Admission.buildPrune id [] baseMetas [(l1, pA), (l2, pB)]
      baseArgs [] [] baseDeclared.resolved
  , declaredResolved := baseDeclared.resolved
  , audit := Admission.buildAdmissionAudit id [] baseMetas [(l1, pA), (l2, pB)]
      baseArgs [] [] baseDeclared.resolved }

private def baseState : Lara.Update.SourceState :=
  { sigma := sigmaEx
  , policy := unitPolicyEx
  , table := []
  , metas := baseMetas
  , leaves := [(l1, pA), (l2, pB)]
  , argsRaw := baseArgs
  , rawAtts := []
  , groups := []
  , ground := groundEx }

private def baseGamma : LeafId → Option Atom :=
  Admission.buildGamma [(l1, pA), (l2, pB)]

private def baseUnit : Lara.Unit :=
  { sigma := sigmaEx
  , policy := unitPolicyEx
  , args := [.leaf l1]
  , atts := [] }

private def baseCheck :=
  Check.Unit.checkUnit baseGamma registryEx groundEx baseUnit

private theorem baseCheck_isOk : baseCheck.isOk = true := by decide

private def baseChecked :
    Lara.Unit.CheckedUnit id baseGamma (certOkOf registryEx) :=
  baseCheck.toOption.get (by decide)

private theorem baseCheck_ok : baseCheck = .ok baseChecked := by
  cases h : baseCheck with
  | error error =>
      have hs := baseCheck_isOk
      rw [h] at hs
      contradiction
  | ok checked =>
      have hoption : baseCheck.toOption = some checked :=
        congrArg Except.toOption h
      have haccepted : baseChecked = checked := by
        unfold baseChecked
        apply Option.get_of_eq_some
        exact hoption
      rw [haccepted]

/-- Adding the fresh, completely supported `l2` argument to a genuinely
accepted one-argument source is rejected for exactly the new uncovered
`pB`-against-`pA` conflict.  Thus freshness and complete support do not replace
the extended-list `AttackComplete` premise of `applyUpdate_addInstance_ok`. -/
theorem addInstance_uncovered_rejected :
    Lara.Update.Accepted registryEx baseState ∧
    Lara.Update.InstanceFresh baseState "b" (.leaf l2) ∧
    (∃ C, HasSupport id unitPolicyEx.ruleLookup
      (Admission.buildGamma [(l1, pA), (l2, pB)])
      (certOkOf registryEx) (.leaf l2) C []) ∧
    ¬ AttackComplete id unitPolicyEx.ruleLookup
      (Admission.buildGamma [(l1, pA), (l2, pB)])
      (certOkOf registryEx) unitPolicyEx.defeat
      [.leaf l1, .leaf l2] [] ∧
    Lara.Update.applyUpdate registryEx baseState
      (.addInstance "b" (.leaf l2)) =
      .error (.unitRejected (.program
        (.missingConflict ⟨1, 0, pB, pA⟩))) := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · refine ⟨baseDeclared, baseAdmission, baseChecked, rfl, ?_⟩
    change baseCheck = .ok baseChecked
    exact baseCheck_ok
  · simpa [Lara.Update.InstanceFresh, baseState, baseArgs] using
      (show l1 ≠ l2 by decide)
  · exact ⟨pB, .leaf (by decide)⟩
  · intro hcomplete
    have hcovered := hcomplete (.leaf l2) (by simp) (.leaf l1) (by simp)
      pB pA (.leaf (by decide)) (.leaf (by decide))
      (by
        exact ⟨(apB, apA), by simp [unitPolicyEx, dpEx], [], pB, pA,
          by decide, by decide, equiv_refl id pB, equiv_refl id pA⟩)
      (by simp [ConflictAttackable])
    simp [Covered] at hcovered

/-! ### Reusable grounded-transition fixture family -/

/-- Hidden atoms used by the graph-realization fixtures. -/

private def h0 : Atom := .atom "h0" .nil
private def h1 : Atom := .atom "h1" .nil
private def h2 : Atom := .atom "h2" .nil
private def h3 : Atom := .atom "h3" .nil
private def h4 : Atom := .atom "h4" .nil

private def ah0 : APat := ⟨⟨"h0"⟩, .nil⟩
private def ah1 : APat := ⟨⟨"h1"⟩, .nil⟩
private def ah2 : APat := ⟨⟨"h2"⟩, .nil⟩
private def ah3 : APat := ⟨⟨"h3"⟩, .nil⟩

private def lh0 : LeafId := ⟨"matrix-h0"⟩
private def lh1 : LeafId := ⟨"matrix-h1"⟩
private def lh2 : LeafId := ⟨"matrix-h2"⟩
private def lh3 : LeafId := ⟨"matrix-h3"⟩
private def lh4 : LeafId := ⟨"matrix-h4"⟩

private def rp0 : RuleId := ⟨"matrix-p0"⟩
private def rp1 : RuleId := ⟨"matrix-p1"⟩
private def rp2 : RuleId := ⟨"matrix-p2"⟩
private def rq0 : RuleId := ⟨"matrix-q0"⟩
private def rq1 : RuleId := ⟨"matrix-q1"⟩
private def rq2 : RuleId := ⟨"matrix-q2"⟩
private def rnew0 : RuleId := ⟨"matrix-new0"⟩
private def rnew1 : RuleId := ⟨"matrix-new1"⟩
private def rnew2 : RuleId := ⟨"matrix-new2"⟩
private def rnewQ : RuleId := ⟨"matrix-new-q"⟩

private def graphRule (premise conclusion : APat) : Rule :=
  { mode := .defeasible
  , params := []
  , premises := [premise]
  , concl := conclusion
  , questions := []
  , allowTrusted := false
  , certifiers := [] }

private def matrixSigma : Sigma.Sigma :=
  { sigmaEx with
    preds := sigmaEx.preds ++
      [⟨⟨"h0"⟩, []⟩, ⟨⟨"h1"⟩, []⟩, ⟨⟨"h2"⟩, []⟩,
       ⟨⟨"h3"⟩, []⟩, ⟨⟨"h4"⟩, []⟩] }

private def matrixRules : List Policy.RuleDecl :=
  [ ⟨rp0, graphRule ah0 apA⟩, ⟨rp1, graphRule ah1 apA⟩,
    ⟨rp2, graphRule ah2 apA⟩, ⟨rq0, graphRule ah0 apB⟩,
    ⟨rq1, graphRule ah1 apB⟩, ⟨rq2, graphRule ah2 apB⟩,
    ⟨rnew0, graphRule ah0 apA⟩, ⟨rnew1, graphRule ah1 apA⟩,
    ⟨rnew2, graphRule ah2 apA⟩, ⟨rnewQ, graphRule ah0 apB⟩ ]

private def hiddenLeaf : Nat → LeafId
  | 0 => lh0
  | 1 => lh1
  | 2 => lh2
  | _ => lh3

private def hiddenAtom : Nat → Atom
  | 0 => h0
  | 1 => h1
  | 2 => h2
  | _ => h3

private def hiddenPat : Nat → APat
  | 0 => ah0
  | 1 => ah1
  | 2 => ah2
  | _ => ah3

private def nodeRuleId (supportsClaim : Bool) : Nat → RuleId
  | 0 => if supportsClaim then rp0 else rq0
  | 1 => if supportsClaim then rp1 else rq1
  | _ => if supportsClaim then rp2 else rq2

private def nodePat (supportsClaim : Bool) : APat :=
  if supportsClaim then apA else apB

private def nodeTerm (supportsClaim : Bool) (i : Nat) : SupportTerm :=
  .inst (nodeRuleId supportsClaim i) [] [.leaf (hiddenLeaf i)] [] [] .none

private def nodeName (i : Nat) : String := s!"n{i}"

private def newNodeTerm (carrier : Nat) : SupportTerm :=
  let rid := if carrier = 0 then rnew0 else if carrier = 1 then rnew1 else rnew2
  .inst rid [] [.leaf (hiddenLeaf carrier)] [] [] .none

private def newAuxTerm : SupportTerm :=
  .inst rnewQ [] [.leaf lh0] [] [] .none

/-- A small graph encoded through real supported arguments.  Every declared
edge attacks the target argument's private premise, so root-conflict
completeness remains vacuous while compilation realizes exactly the requested
graph. -/
private structure GraphSpec where
  supports : List Bool
  edges : List (Nat × Nat)
  licensed : List (Nat × Nat) := edges
  removed : List Nat := []

private def graphLeaves : List (LeafId × Atom) :=
  [(lh0, h0), (lh1, h1), (lh2, h2), (lh3, h3)]

private def graphMetas (removed : List Nat) : List Admission.LeafMeta :=
  [ { id := lh0, kind := if 0 ∈ removed then .attested else .observed,
      provenance := .user },
    { id := lh1, kind := if 1 ∈ removed then .attested else .observed,
      provenance := .user },
    { id := lh2, kind := if 2 ∈ removed then .attested else .observed,
      provenance := .user },
    { id := lh3, kind := .observed, provenance := .user } ]

private def graphArgs (spec : GraphSpec) : List (String × SupportTerm) :=
  (List.range spec.supports.length).map fun i =>
    (nodeName i, nodeTerm (spec.supports.getD i false) i)

private def graphRawAttack (edge : Nat × Nat) : RawAttack.RawAttack :=
  .undermine (nodeName edge.1) (nodeName edge.2) [.prem 0]

private def graphPolicy (spec : GraphSpec) : Policy.Policy :=
  { rules := matrixRules
  , defeat :=
      { contraries := spec.licensed.map fun edge =>
          (nodePat (spec.supports.getD edge.1 false), hiddenPat edge.2)
      , exceptions := [] } }

private def graphState (spec : GraphSpec) : Lara.Update.SourceState :=
  { sigma := matrixSigma
  , policy := graphPolicy spec
  , table := []
  , metas := graphMetas spec.removed
  , leaves := graphLeaves
  , argsRaw := graphArgs spec
  , rawAtts := spec.edges.map graphRawAttack
  , groups := []
  , ground := groundEx ++ [h0, h1, h2, h3, h4] }

private def resolvedOrEmpty (state : Lara.Update.SourceState) : List Attack.Attack :=
  match RawAttack.resolveAttacks state.argsRaw state.rawAtts with
  | .ok attacks => attacks
  | .error _ => []

private def declaredOf (state : Lara.Update.SourceState)
    (hresolve :
      RawAttack.resolveAttacks state.argsRaw state.rawAtts =
        .ok (resolvedOrEmpty state))
    (hids : (state.argsRaw.map (·.1)).Nodup) :
    Admission.AlignedAttacks state.argsRaw state.rawAtts :=
  { resolved := resolvedOrEmpty state
  , resolve_eq := hresolve
  , ids_nodup := hids }

private def admissionOf (state : Lara.Update.SourceState)
    (declared : Admission.AlignedAttacks state.argsRaw state.rawAtts) :
    Admission.AdmissionResult :=
  { prune := Admission.buildPrune id state.table state.metas state.leaves
      state.argsRaw state.rawAtts state.groups declared.resolved
  , declaredResolved := declared.resolved
  , audit := Admission.buildAdmissionAudit id state.table state.metas state.leaves
      state.argsRaw state.rawAtts state.groups declared.resolved }

private def checkedResultOf (state : Lara.Update.SourceState)
    (admission : Admission.AdmissionResult) :=
  Check.Unit.checkUnit (Admission.buildGamma admission.prune.checkedLeaves)
    registryEx state.ground
    { sigma := state.sigma
    , policy := state.policy
    , args := admission.prune.keptArgs.map (·.2)
    , atts := admission.prune.keptAttacks }

private def checkedOf (state : Lara.Update.SourceState)
    (admission : Admission.AdmissionResult)
    (hok : (checkedResultOf state admission).isOk = true) :
    Lara.Unit.CheckedUnit id
      (Admission.buildGamma admission.prune.checkedLeaves)
      (certOkOf registryEx) :=
  (checkedResultOf state admission).toOption.get (by
    cases h : checkedResultOf state admission with
    | error error =>
        rw [h] at hok
        contradiction
    | ok checked =>
        exact rfl)

/-- One exact successful admission/checker run specialized to the example
registry. -/
abbrev AcceptedRun (state : Lara.Update.SourceState) :=
  Lara.Update.AcceptedRun registryEx state


private def fixtureOf (state : Lara.Update.SourceState)
    (hresolve :
      RawAttack.resolveAttacks state.argsRaw state.rawAtts =
        .ok (resolvedOrEmpty state))
    (hids : (state.argsRaw.map (·.1)).Nodup)
    (hadmission :
      Admission.evaluateAdmission id state.table state.metas state.leaves
        state.argsRaw state.rawAtts state.groups
          (declaredOf state hresolve hids) =
        .accepted (admissionOf state (declaredOf state hresolve hids)))
    (hcheck :
      (checkedResultOf state
        (admissionOf state (declaredOf state hresolve hids))).isOk = true) :
    AcceptedRun state := by
  let declared := declaredOf state hresolve hids
  let admission := admissionOf state declared
  let checked := checkedOf state admission hcheck
  refine
    { declared := declared
    , admission := admission
    , checked := checked
    , admission_ok := ?_
    , check_ok := ?_ }
  · exact hadmission
  cases h : checkedResultOf state admission with
  | error error =>
      rw [h] at hcheck
      contradiction
  | ok result =>
      have hoption :
          (checkedResultOf state admission).toOption = some result :=
        congrArg Except.toOption h
      have hchecked : checked = result := by
        unfold checked checkedOf
        apply Option.get_of_eq_some
        exact hoption
      rw [hchecked]
      simpa [checkedResultOf] using h

private def quarantineKey :
    Presentation.LeafKind × Presentation.Provenance :=
  (.attested, .user)

private def quarantineRow : Admission.AdmissionRow :=
  { key := quarantineKey, decision := .quarantine }

private def tightenTarget (spec : GraphSpec) : Lara.Update.SourceState :=
  { graphState spec with table := [quarantineRow] }

private def addLeafMeta : Admission.LeafMeta :=
  { id := lh4, kind := .observed, provenance := .user }

private def addLeafTarget (spec : GraphSpec) : Lara.Update.SourceState :=
  { graphState spec with
    metas := (graphState spec).metas ++ [addLeafMeta]
    leaves := (graphState spec).leaves ++ [(lh4, h4)] }

private def addAttackTarget (spec : GraphSpec) (edge : Nat × Nat) :
    Lara.Update.SourceState :=
  { graphState spec with
    rawAtts := (graphState spec).rawAtts ++ [graphRawAttack edge] }

private def addInstanceTarget (spec : GraphSpec) (carrier : Nat)
    (supportsClaim : Bool := true) : Lara.Update.SourceState :=
  { graphState spec with
    argsRaw := (graphState spec).argsRaw ++
      [("new", if supportsClaim then newNodeTerm carrier else newAuxTerm)] }

private def fixtureJ : GraphSpec :=
  { supports := [true], edges := [] }

private def fixtureD : GraphSpec :=
  { supports := [false, true], edges := [(0, 1)] }

private def fixtureC : GraphSpec :=
  { supports := [true], edges := [(0, 0)] }

private def fixtureG : GraphSpec :=
  { supports := [false], edges := [] }

private def acceptedGraphJ : AcceptedRun (graphState fixtureJ) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

private def acceptedGraphD : AcceptedRun (graphState fixtureD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

private def acceptedGraphC : AcceptedRun (graphState fixtureC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

private def acceptedGraphG : AcceptedRun (graphState fixtureG) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

/-- A matrix cell packages the exact source and target admission/checker runs
used by the semantic transition, together with the successful source edit. -/
def SuccessfulCoreCell
    (sem : Semantics.ExtensionSemantics)
    (source target : Lara.Update.SourceState)
    (update : Lara.Update.SourceUpdate)
    (p : Atom) (before after : Grounded.Status) : Prop :=
  ∃ (sourceRun : AcceptedRun source) (targetRun : AcceptedRun target),
    Lara.Update.applyUpdate registryEx source update = .ok target ∧
    Lara.Update.CoreTransition sem sourceRun.checked targetRun.checked p =
      (.observed before, .observed after)

/-- A public matrix cell carries exact source/target pipeline runs, successful
application, and the clean-base premise required by every public theorem. -/
def SuccessfulPublicCell
    (source target : Lara.Update.SourceState)
    (update : Lara.Update.SourceUpdate) (p : Atom)
    (before : Grounded.Status) (after : Lara.Update.PublicReport) : Prop :=
  ∃ (sourceRun : AcceptedRun source) (targetRun : AcceptedRun target),
    Lara.Update.applyUpdate registryEx source update = .ok target ∧
    Lara.Update.CleanBase sourceRun ∧
    Lara.Update.PublicTransition sourceRun targetRun p =
      (Lara.Update.PublicReport.ofStatus before, after)

private theorem successfulPublicCellOf
    (sourceRun : AcceptedRun source) (targetRun : AcceptedRun target)
    (update : Lara.Update.SourceUpdate) (p : Atom)
    (before : Grounded.Status) (after : Lara.Update.PublicReport)
    (happly : Lara.Update.applyUpdate registryEx source update = .ok target)
    (hclean : Lara.Update.CleanBase sourceRun)
    (htransition :
      Lara.Update.PublicTransition sourceRun targetRun p =
        (Lara.Update.PublicReport.ofStatus before, after)) :
    SuccessfulPublicCell source target update p before after :=
  ⟨sourceRun, targetRun, happly, hclean, htransition⟩

/-- Recover the exact pipeline-linked checked observations from a successful
matrix cell. -/
theorem SuccessfulCoreCell.transition
    (cell : SuccessfulCoreCell sem source target update p before after) :
    ∃ (sourceRun : AcceptedRun source) (targetRun : AcceptedRun target),
      Lara.Update.CoreTransition sem sourceRun.checked targetRun.checked p =
        (.observed before, .observed after) := by
  obtain ⟨sourceRun, targetRun, _, hcore⟩ := cell
  exact ⟨sourceRun, targetRun, hcore⟩

private theorem successfulCoreCellOf
    (sourceFixture : AcceptedRun source)
    (targetFixture : AcceptedRun target)
    (update : Lara.Update.SourceUpdate)
    (before after : Grounded.Status)
    (happly : Lara.Update.applyUpdate registryEx source update = .ok target)
    (hcore : Lara.Update.CoreTransition sem sourceFixture.checked
      targetFixture.checked pA = (.observed before, .observed after)) :
    SuccessfulCoreCell sem source target update pA before after :=
  ⟨sourceFixture, targetFixture, happly, hcore⟩

private def addLeafTargetJ : AcceptedRun (addLeafTarget fixtureJ) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

/-- A real admitted `addLeaf` update preserves a grounded justified claim. -/
theorem addLeaf_justified_to_justified :
    SuccessfulCoreCell Semantics.groundedSem (graphState fixtureJ)
      (addLeafTarget fixtureJ) (.addLeaf lh4 h4 addLeafMeta)
      pA .justified .justified :=
  successfulCoreCellOf acceptedGraphJ addLeafTargetJ _ _ _
    (by rfl) (by decide)

private def addLeafTargetD : AcceptedRun (addLeafTarget fixtureD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

private def addLeafTargetC : AcceptedRun (addLeafTarget fixtureC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

private def addLeafTargetG : AcceptedRun (addLeafTarget fixtureG) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

/-- A real admitted `addLeaf` update preserves a grounded refuted claim. -/
theorem addLeaf_refuted_to_refuted :
    SuccessfulCoreCell Semantics.groundedSem (graphState fixtureD)
      (addLeafTarget fixtureD) (.addLeaf lh4 h4 addLeafMeta)
      pA .defeated .defeated :=
  successfulCoreCellOf acceptedGraphD addLeafTargetD _ _ _
    (by rfl) (by decide)

/-- A real admitted `addLeaf` update preserves a grounded both claim. -/
theorem addLeaf_both_to_both :
    SuccessfulCoreCell Semantics.groundedSem (graphState fixtureC)
      (addLeafTarget fixtureC) (.addLeaf lh4 h4 addLeafMeta)
      pA .contested .contested :=
  successfulCoreCellOf acceptedGraphC addLeafTargetC _ _ _
    (by rfl) (by decide)

/-- A real admitted `addLeaf` update preserves a grounded gap claim. -/
theorem addLeaf_gap_to_gap :
    SuccessfulCoreCell Semantics.groundedSem (graphState fixtureG)
      (addLeafTarget fixtureG) (.addLeaf lh4 h4 addLeafMeta)
      pA .gap .gap :=
  successfulCoreCellOf acceptedGraphG addLeafTargetG _ _ _
    (by rfl) (by decide)

/-! ### Tighten matrix: all thirteen reachable cells -/

private def tightJJ : GraphSpec :=
  { supports := [true, false, false], edges := [], removed := [1] }
private def tightJD : GraphSpec :=
  { supports := [true, false, false], edges := [(1, 2), (2, 0)],
    removed := [1] }
private def tightJC : GraphSpec :=
  { supports := [true, false, false],
    edges := [(0, 2), (1, 2), (2, 0)], removed := [1] }
private def tightJG : GraphSpec :=
  { supports := [true, false, false], edges := [], removed := [0] }
private def tightDJ : GraphSpec :=
  { supports := [true, false, false], edges := [(1, 0)], removed := [1] }
private def tightDD : GraphSpec :=
  { supports := [true, false, false], edges := [(1, 0)], removed := [2] }
private def tightDC : GraphSpec :=
  { supports := [true, false, false],
    edges := [(0, 1), (1, 0), (2, 0)], removed := [2] }
private def tightDG : GraphSpec :=
  { supports := [true, false, false], edges := [(1, 0)], removed := [0] }
private def tightCJ : GraphSpec :=
  { supports := [true, false, false], edges := [(0, 1), (1, 0)],
    removed := [1] }
private def tightCD : GraphSpec :=
  { supports := [true, false, false],
    edges := [(0, 1), (1, 2), (2, 0)], removed := [1] }
private def tightCC : GraphSpec :=
  { supports := [true, false, false], edges := [(0, 1), (1, 0)],
    removed := [2] }
private def tightCG : GraphSpec :=
  { supports := [true, false, false], edges := [(0, 1), (1, 0)],
    removed := [0] }
private def tightGG : GraphSpec :=
  { supports := [false, false], edges := [], removed := [1] }

private def tightPublicJD : GraphSpec :=
  { supports := [true, true, false], edges := [(2, 1)], removed := [0] }
private def tightPublicJC : GraphSpec :=
  { supports := [true, true], edges := [(1, 1)], removed := [0] }
private def tightPublicCD : GraphSpec :=
  { supports := [true, true, false], edges := [(0, 0), (2, 1)],
    removed := [0] }

private def tightSourceJJ : AcceptedRun (graphState tightJJ) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightTargetJJ : AcceptedRun (tightenTarget tightJJ) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightSourceJD : AcceptedRun (graphState tightJD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightTargetJD : AcceptedRun (tightenTarget tightJD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightSourceJC : AcceptedRun (graphState tightJC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightTargetJC : AcceptedRun (tightenTarget tightJC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightSourceJG : AcceptedRun (graphState tightJG) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightTargetJG : AcceptedRun (tightenTarget tightJG) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightSourceDJ : AcceptedRun (graphState tightDJ) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightTargetDJ : AcceptedRun (tightenTarget tightDJ) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightSourceDD : AcceptedRun (graphState tightDD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightTargetDD : AcceptedRun (tightenTarget tightDD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightSourceDC : AcceptedRun (graphState tightDC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightTargetDC : AcceptedRun (tightenTarget tightDC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightSourceDG : AcceptedRun (graphState tightDG) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightTargetDG : AcceptedRun (tightenTarget tightDG) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightSourceCJ : AcceptedRun (graphState tightCJ) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightTargetCJ : AcceptedRun (tightenTarget tightCJ) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightSourceCD : AcceptedRun (graphState tightCD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightTargetCD : AcceptedRun (tightenTarget tightCD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightSourceCC : AcceptedRun (graphState tightCC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightTargetCC : AcceptedRun (tightenTarget tightCC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightSourceCG : AcceptedRun (graphState tightCG) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightTargetCG : AcceptedRun (tightenTarget tightCG) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightSourceGG : AcceptedRun (graphState tightGG) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightTargetGG : AcceptedRun (tightenTarget tightGG) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

private def tightPublicSourceJD : AcceptedRun (graphState tightPublicJD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightPublicTargetJD : AcceptedRun (tightenTarget tightPublicJD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightPublicSourceJC : AcceptedRun (graphState tightPublicJC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightPublicTargetJC : AcceptedRun (tightenTarget tightPublicJC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightPublicSourceCD : AcceptedRun (graphState tightPublicCD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def tightPublicTargetCD : AcceptedRun (tightenTarget tightPublicCD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

/-! ### Necessity of the clean-base premise -/

private def blockedGrowthSpec : GraphSpec :=
  { supports := [false, false, true]
  , edges := [(0, 1)]
  , licensed := [(0, 1), (1, 2)]
  , removed := [0] }

private def blockedGrowthSource : Lara.Update.SourceState :=
  { graphState blockedGrowthSpec with table := [quarantineRow] }

private def blockedGrowthTarget : Lara.Update.SourceState :=
  { blockedGrowthSource with
    rawAtts := blockedGrowthSource.rawAtts ++ [graphRawAttack (1, 2)] }

private def blockedGrowthSourceRun : AcceptedRun blockedGrowthSource :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

private def blockedGrowthTargetRun : AcceptedRun blockedGrowthTarget :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

/-- **CleanBase is necessary.**  The accepted source already quarantines
argument `0`; its removed incoming edge makes retained argument `1` blocked.
The real successful `addAttack` from `1` to claim-supporting argument `2`
extends the blocked closure, changing the exact public report for `pA` from
`justified` to `evidenceBlocked` (with conditional target core status
`defeated`). -/
theorem addAttack_blocked_growth :
    ∃ (sourceRun : AcceptedRun blockedGrowthSource)
        (targetRun : AcceptedRun blockedGrowthTarget),
      Lara.Update.applyUpdate registryEx blockedGrowthSource
          (.addAttack (graphRawAttack (1, 2))) =
        .ok blockedGrowthTarget ∧
      ¬ Lara.Update.CleanBase sourceRun ∧
      1 ∈ Lara.Update.blockedSetForRun sourceRun ∧
      Lara.Update.PublicTransition sourceRun
          targetRun pA =
        (.justified, .evidenceBlocked) ∧
      Grounded.statusC (Compile.checkedAF targetRun.checked.program)
          (Consistency.completeClaimFor targetRun.checked pA) =
        .defeated := by
  refine ⟨blockedGrowthSourceRun, blockedGrowthTargetRun, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro hclean
    have hmem :
        lh0 ∈ blockedGrowthSourceRun.admission.prune.removedSeed := by decide
    change blockedGrowthSourceRun.admission.prune.removedSeed = [] at hclean
    rw [hclean] at hmem
    simp at hmem
  · decide
  · decide
  · decide

/-! ### Tighten reachable witnesses -/

/-- Tightening witnesses grounded justified to justified. -/
theorem tighten_justified_to_justified :
    SuccessfulCoreCell Semantics.groundedSem (graphState tightJJ)
      (tightenTarget tightJJ) (.tighten quarantineKey)
      pA .justified .justified :=
  successfulCoreCellOf tightSourceJJ tightTargetJJ _ _ _ (by rfl) (by decide)

/-- Tightening witnesses grounded justified to refuted. -/
theorem tighten_justified_to_refuted :
    SuccessfulCoreCell Semantics.groundedSem (graphState tightJD)
      (tightenTarget tightJD) (.tighten quarantineKey)
      pA .justified .defeated :=
  successfulCoreCellOf tightSourceJD tightTargetJD _ _ _ (by rfl) (by decide)

/-- Tightening witnesses grounded justified to both. -/
theorem tighten_justified_to_both :
    SuccessfulCoreCell Semantics.groundedSem (graphState tightJC)
      (tightenTarget tightJC) (.tighten quarantineKey)
      pA .justified .contested :=
  successfulCoreCellOf tightSourceJC tightTargetJC _ _ _ (by rfl) (by decide)

/-- Tightening witnesses grounded justified to gap. -/
theorem tighten_justified_to_gap :
    SuccessfulCoreCell Semantics.groundedSem (graphState tightJG)
      (tightenTarget tightJG) (.tighten quarantineKey)
      pA .justified .gap :=
  successfulCoreCellOf tightSourceJG tightTargetJG _ _ _ (by rfl) (by decide)

/-- Tightening witnesses grounded refuted to justified. -/
theorem tighten_refuted_to_justified :
    SuccessfulCoreCell Semantics.groundedSem (graphState tightDJ)
      (tightenTarget tightDJ) (.tighten quarantineKey)
      pA .defeated .justified :=
  successfulCoreCellOf tightSourceDJ tightTargetDJ _ _ _ (by rfl) (by decide)

/-- Tightening witnesses grounded refuted to refuted. -/
theorem tighten_refuted_to_refuted :
    SuccessfulCoreCell Semantics.groundedSem (graphState tightDD)
      (tightenTarget tightDD) (.tighten quarantineKey)
      pA .defeated .defeated :=
  successfulCoreCellOf tightSourceDD tightTargetDD _ _ _ (by rfl) (by decide)

/-- Tightening witnesses grounded refuted to both. -/
theorem tighten_refuted_to_both :
    SuccessfulCoreCell Semantics.groundedSem (graphState tightDC)
      (tightenTarget tightDC) (.tighten quarantineKey)
      pA .defeated .contested :=
  successfulCoreCellOf tightSourceDC tightTargetDC _ _ _ (by rfl) (by decide)

/-- Tightening witnesses grounded refuted to gap. -/
theorem tighten_refuted_to_gap :
    SuccessfulCoreCell Semantics.groundedSem (graphState tightDG)
      (tightenTarget tightDG) (.tighten quarantineKey)
      pA .defeated .gap :=
  successfulCoreCellOf tightSourceDG tightTargetDG _ _ _ (by rfl) (by decide)

/-- Tightening witnesses grounded both to justified. -/
theorem tighten_both_to_justified :
    SuccessfulCoreCell Semantics.groundedSem (graphState tightCJ)
      (tightenTarget tightCJ) (.tighten quarantineKey)
      pA .contested .justified :=
  successfulCoreCellOf tightSourceCJ tightTargetCJ _ _ _ (by rfl) (by decide)

/-- Tightening witnesses grounded both to refuted. -/
theorem tighten_both_to_refuted :
    SuccessfulCoreCell Semantics.groundedSem (graphState tightCD)
      (tightenTarget tightCD) (.tighten quarantineKey)
      pA .contested .defeated :=
  successfulCoreCellOf tightSourceCD tightTargetCD _ _ _ (by rfl) (by decide)

/-- Tightening witnesses grounded both to both. -/
theorem tighten_both_to_both :
    SuccessfulCoreCell Semantics.groundedSem (graphState tightCC)
      (tightenTarget tightCC) (.tighten quarantineKey)
      pA .contested .contested :=
  successfulCoreCellOf tightSourceCC tightTargetCC _ _ _ (by rfl) (by decide)

/-- Tightening witnesses grounded both to gap. -/
theorem tighten_both_to_gap :
    SuccessfulCoreCell Semantics.groundedSem (graphState tightCG)
      (tightenTarget tightCG) (.tighten quarantineKey)
      pA .contested .gap :=
  successfulCoreCellOf tightSourceCG tightTargetCG _ _ _ (by rfl) (by decide)

/-- Tightening witnesses the only reachable grounded gap-row cell. -/
theorem tighten_gap_to_gap :
    SuccessfulCoreCell Semantics.groundedSem (graphState tightGG)
      (tightenTarget tightGG) (.tighten quarantineKey)
      pA .gap .gap :=
  successfulCoreCellOf tightSourceGG tightTargetGG _ _ _ (by rfl) (by decide)


/-! ### Tighten public-row witnesses under `CleanBase` -/

/-- Clean-base tightening publicly witnesses justified to justified. -/
theorem tighten_public_justified_to_justified :
    SuccessfulPublicCell (graphState tightJJ) (tightenTarget tightJJ)
      (.tighten quarantineKey) pA .justified .justified :=
  successfulPublicCellOf tightSourceJJ tightTargetJJ _ _ _ _
    (by rfl) (by rfl) (by decide)

/-- Clean-base tightening can lose a justified alternative and publicly report
defeated without blocking the retained support. -/
theorem tighten_public_justified_to_defeated :
    SuccessfulPublicCell (graphState tightPublicJD)
      (tightenTarget tightPublicJD) (.tighten quarantineKey)
      pA .justified .defeated :=
  successfulPublicCellOf tightPublicSourceJD tightPublicTargetJD _ _ _ _
    (by rfl) (by rfl) (by decide)

/-- Clean-base tightening can lose a justified alternative and publicly report
contested without blocking the retained support. -/
theorem tighten_public_justified_to_contested :
    SuccessfulPublicCell (graphState tightPublicJC)
      (tightenTarget tightPublicJC) (.tighten quarantineKey)
      pA .justified .contested :=
  successfulPublicCellOf tightPublicSourceJC tightPublicTargetJC _ _ _ _
    (by rfl) (by rfl) (by decide)

/-- Clean-base tightening publicly witnesses justified to gap. -/
theorem tighten_public_justified_to_gap :
    SuccessfulPublicCell (graphState tightJG) (tightenTarget tightJG)
      (.tighten quarantineKey) pA .justified .gap :=
  successfulPublicCellOf tightSourceJG tightTargetJG _ _ _ _
    (by rfl) (by rfl) (by decide)

/-- Clean-base tightening publicly blocks a claim whose conditional target
status depends on quarantined material. -/
theorem tighten_public_justified_to_evidenceBlocked :
    SuccessfulPublicCell (graphState tightJD) (tightenTarget tightJD)
      (.tighten quarantineKey) pA .justified .evidenceBlocked :=
  successfulPublicCellOf tightSourceJD tightTargetJD _ _ _ _
    (by rfl) (by rfl) (by decide)

/-- Clean-base tightening publicly witnesses defeated to defeated. -/
theorem tighten_public_defeated_to_defeated :
    SuccessfulPublicCell (graphState tightDD) (tightenTarget tightDD)
      (.tighten quarantineKey) pA .defeated .defeated :=
  successfulPublicCellOf tightSourceDD tightTargetDD _ _ _ _
    (by rfl) (by rfl) (by decide)

/-- Clean-base tightening publicly witnesses defeated to gap. -/
theorem tighten_public_defeated_to_gap :
    SuccessfulPublicCell (graphState tightDG) (tightenTarget tightDG)
      (.tighten quarantineKey) pA .defeated .gap :=
  successfulPublicCellOf tightSourceDG tightTargetDG _ _ _ _
    (by rfl) (by rfl) (by decide)

/-- Clean-base tightening reports evidence blocked rather than publishing a
promotion from defeated material. -/
theorem tighten_public_defeated_to_evidenceBlocked :
    SuccessfulPublicCell (graphState tightDJ) (tightenTarget tightDJ)
      (.tighten quarantineKey) pA .defeated .evidenceBlocked :=
  successfulPublicCellOf tightSourceDJ tightTargetDJ _ _ _ _
    (by rfl) (by rfl) (by decide)

/-- Clean-base tightening can remove an undecided alternative and publicly
report defeated on the unaffected retained support. -/
theorem tighten_public_contested_to_defeated :
    SuccessfulPublicCell (graphState tightPublicCD)
      (tightenTarget tightPublicCD) (.tighten quarantineKey)
      pA .contested .defeated :=
  successfulPublicCellOf tightPublicSourceCD tightPublicTargetCD _ _ _ _
    (by rfl) (by rfl) (by decide)

/-- Clean-base tightening publicly witnesses contested to contested. -/
theorem tighten_public_contested_to_contested :
    SuccessfulPublicCell (graphState tightCC) (tightenTarget tightCC)
      (.tighten quarantineKey) pA .contested .contested :=
  successfulPublicCellOf tightSourceCC tightTargetCC _ _ _ _
    (by rfl) (by rfl) (by decide)

/-- Clean-base tightening publicly witnesses contested to gap. -/
theorem tighten_public_contested_to_gap :
    SuccessfulPublicCell (graphState tightCG) (tightenTarget tightCG)
      (.tighten quarantineKey) pA .contested .gap :=
  successfulPublicCellOf tightSourceCG tightTargetCG _ _ _ _
    (by rfl) (by rfl) (by decide)

/-- Clean-base tightening reports evidence blocked rather than publishing a
promotion from contested material. -/
theorem tighten_public_contested_to_evidenceBlocked :
    SuccessfulPublicCell (graphState tightCJ) (tightenTarget tightCJ)
      (.tighten quarantineKey) pA .contested .evidenceBlocked :=
  successfulPublicCellOf tightSourceCJ tightTargetCJ _ _ _ _
    (by rfl) (by rfl) (by decide)

/-- Clean-base tightening leaves an unsupported query at public gap. -/
theorem tighten_public_gap_to_gap :
    SuccessfulPublicCell (graphState tightGG) (tightenTarget tightGG)
      (.tighten quarantineKey) pA .gap .gap :=
  successfulPublicCellOf tightSourceGG tightTargetGG _ _ _ _
    (by rfl) (by rfl) (by decide)

/-! ### Add-attack matrix: the complete non-gap block plus fixed gap -/

private def attackJJ : GraphSpec :=
  { supports := [true, false], edges := [], licensed := [(0, 1)] }
private def attackJD : GraphSpec :=
  { supports := [true, false], edges := [], licensed := [(1, 0)] }
private def attackJC : GraphSpec :=
  { supports := [true], edges := [], licensed := [(0, 0)] }
private def attackDJ : GraphSpec :=
  { supports := [false, true, false], edges := [(0, 1)],
    licensed := [(0, 1), (2, 0)] }
private def attackDD : GraphSpec :=
  { supports := [false, true], edges := [(0, 1)],
    licensed := [(0, 1), (1, 1)] }
private def attackDC : GraphSpec :=
  { supports := [false, true], edges := [(0, 1)],
    licensed := [(0, 1), (0, 0)] }
private def attackCJ : GraphSpec :=
  { supports := [false, true, false], edges := [(0, 1), (0, 0)],
    licensed := [(0, 1), (0, 0), (2, 0)] }
private def attackCD : GraphSpec :=
  { supports := [true, false], edges := [(0, 0)],
    licensed := [(0, 0), (1, 0)] }
private def attackCC : GraphSpec :=
  { supports := [true, false], edges := [(0, 0)],
    licensed := [(0, 0), (0, 1)] }
private def attackGG : GraphSpec :=
  { supports := [false, false], edges := [], licensed := [(0, 1)] }

private def attackSourceJJ : AcceptedRun (graphState attackJJ) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackTargetJJ : AcceptedRun (addAttackTarget attackJJ (0, 1)) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackSourceJD : AcceptedRun (graphState attackJD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackTargetJD : AcceptedRun (addAttackTarget attackJD (1, 0)) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackSourceJC : AcceptedRun (graphState attackJC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackTargetJC : AcceptedRun (addAttackTarget attackJC (0, 0)) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackSourceDJ : AcceptedRun (graphState attackDJ) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackTargetDJ : AcceptedRun (addAttackTarget attackDJ (2, 0)) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackSourceDD : AcceptedRun (graphState attackDD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackTargetDD : AcceptedRun (addAttackTarget attackDD (1, 1)) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackSourceDC : AcceptedRun (graphState attackDC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackTargetDC : AcceptedRun (addAttackTarget attackDC (0, 0)) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackSourceCJ : AcceptedRun (graphState attackCJ) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackTargetCJ : AcceptedRun (addAttackTarget attackCJ (2, 0)) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackSourceCD : AcceptedRun (graphState attackCD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackTargetCD : AcceptedRun (addAttackTarget attackCD (1, 0)) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackSourceCC : AcceptedRun (graphState attackCC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackTargetCC : AcceptedRun (addAttackTarget attackCC (0, 1)) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackSourceGG : AcceptedRun (graphState attackGG) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def attackTargetGG : AcceptedRun (addAttackTarget attackGG (0, 1)) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

/-- Adding an attack witnesses grounded justified to justified. -/
theorem addAttack_justified_to_justified :
    SuccessfulCoreCell Semantics.groundedSem (graphState attackJJ)
      (addAttackTarget attackJJ (0, 1)) (.addAttack (graphRawAttack (0, 1)))
      pA .justified .justified :=
  successfulCoreCellOf attackSourceJJ attackTargetJJ _ _ _ (by rfl) (by decide)

/-- Adding an attack witnesses grounded justified to refuted. -/
theorem addAttack_justified_to_refuted :
    SuccessfulCoreCell Semantics.groundedSem (graphState attackJD)
      (addAttackTarget attackJD (1, 0)) (.addAttack (graphRawAttack (1, 0)))
      pA .justified .defeated :=
  successfulCoreCellOf attackSourceJD attackTargetJD _ _ _ (by rfl) (by decide)

/-- Adding an attack witnesses grounded justified to both. -/
theorem addAttack_justified_to_both :
    SuccessfulCoreCell Semantics.groundedSem (graphState attackJC)
      (addAttackTarget attackJC (0, 0)) (.addAttack (graphRawAttack (0, 0)))
      pA .justified .contested :=
  successfulCoreCellOf attackSourceJC attackTargetJC _ _ _ (by rfl) (by decide)

/-- Adding an attack witnesses grounded refuted to justified. -/
theorem addAttack_refuted_to_justified :
    SuccessfulCoreCell Semantics.groundedSem (graphState attackDJ)
      (addAttackTarget attackDJ (2, 0)) (.addAttack (graphRawAttack (2, 0)))
      pA .defeated .justified :=
  successfulCoreCellOf attackSourceDJ attackTargetDJ _ _ _ (by rfl) (by decide)

/-- Adding an attack witnesses grounded refuted to refuted. -/
theorem addAttack_refuted_to_refuted :
    SuccessfulCoreCell Semantics.groundedSem (graphState attackDD)
      (addAttackTarget attackDD (1, 1)) (.addAttack (graphRawAttack (1, 1)))
      pA .defeated .defeated :=
  successfulCoreCellOf attackSourceDD attackTargetDD _ _ _ (by rfl) (by decide)

/-- Adding an attack witnesses grounded refuted to both. -/
theorem addAttack_refuted_to_both :
    SuccessfulCoreCell Semantics.groundedSem (graphState attackDC)
      (addAttackTarget attackDC (0, 0)) (.addAttack (graphRawAttack (0, 0)))
      pA .defeated .contested :=
  successfulCoreCellOf attackSourceDC attackTargetDC _ _ _ (by rfl) (by decide)

/-- Adding an attack witnesses grounded both to justified. -/
theorem addAttack_both_to_justified :
    SuccessfulCoreCell Semantics.groundedSem (graphState attackCJ)
      (addAttackTarget attackCJ (2, 0)) (.addAttack (graphRawAttack (2, 0)))
      pA .contested .justified :=
  successfulCoreCellOf attackSourceCJ attackTargetCJ _ _ _ (by rfl) (by decide)

/-- Adding an attack witnesses grounded both to refuted. -/
theorem addAttack_both_to_refuted :
    SuccessfulCoreCell Semantics.groundedSem (graphState attackCD)
      (addAttackTarget attackCD (1, 0)) (.addAttack (graphRawAttack (1, 0)))
      pA .contested .defeated :=
  successfulCoreCellOf attackSourceCD attackTargetCD _ _ _ (by rfl) (by decide)

/-- Adding an attack witnesses grounded both to both. -/
theorem addAttack_both_to_both :
    SuccessfulCoreCell Semantics.groundedSem (graphState attackCC)
      (addAttackTarget attackCC (0, 1)) (.addAttack (graphRawAttack (0, 1)))
      pA .contested .contested :=
  successfulCoreCellOf attackSourceCC attackTargetCC _ _ _ (by rfl) (by decide)

/-- Adding an attack witnesses the fixed grounded gap-row cell. -/
theorem addAttack_gap_to_gap :
    SuccessfulCoreCell Semantics.groundedSem (graphState attackGG)
      (addAttackTarget attackGG (0, 1)) (.addAttack (graphRawAttack (0, 1)))
      pA .gap .gap :=
  successfulCoreCellOf attackSourceGG attackTargetGG _ _ _ (by rfl) (by decide)

/-! ### Add-instance matrix: exact ten reachable cells -/

private def instanceJJ : GraphSpec :=
  { supports := [true], edges := [] }
private def instanceDJ : GraphSpec :=
  { supports := [false, true], edges := [(0, 1)] }
private def instanceDD : GraphSpec :=
  { supports := [false, true], edges := [(0, 1)] }
private def instanceDC : GraphSpec :=
  { supports := [false, false, true], edges := [(1, 1), (0, 2)] }
private def instanceCJ : GraphSpec :=
  { supports := [true, false], edges := [(0, 0)] }
private def instanceCC : GraphSpec :=
  { supports := [true], edges := [(0, 0)] }
private def instanceGJ : GraphSpec :=
  { supports := [false], edges := [] }
private def instanceGD : GraphSpec :=
  { supports := [false, false], edges := [(0, 1)] }
private def instanceGC : GraphSpec :=
  { supports := [false], edges := [(0, 0)] }
private def instanceGG : GraphSpec :=
  { supports := [false], edges := [] }

private def instanceSourceJJ : AcceptedRun (graphState instanceJJ) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceTargetJJ : AcceptedRun (addInstanceTarget instanceJJ 0) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceSourceDJ : AcceptedRun (graphState instanceDJ) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceTargetDJ : AcceptedRun (addInstanceTarget instanceDJ 0) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceSourceDD : AcceptedRun (graphState instanceDD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceTargetDD : AcceptedRun (addInstanceTarget instanceDD 1) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceSourceDC : AcceptedRun (graphState instanceDC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceTargetDC : AcceptedRun (addInstanceTarget instanceDC 1) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceSourceCJ : AcceptedRun (graphState instanceCJ) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceTargetCJ : AcceptedRun (addInstanceTarget instanceCJ 1) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceSourceCC : AcceptedRun (graphState instanceCC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceTargetCC : AcceptedRun (addInstanceTarget instanceCC 0) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceSourceGJ : AcceptedRun (graphState instanceGJ) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceTargetGJ : AcceptedRun (addInstanceTarget instanceGJ 0) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceSourceGD : AcceptedRun (graphState instanceGD) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceTargetGD : AcceptedRun (addInstanceTarget instanceGD 1) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceSourceGC : AcceptedRun (graphState instanceGC) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceTargetGC : AcceptedRun (addInstanceTarget instanceGC 0) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceSourceGG : AcceptedRun (graphState instanceGG) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)
private def instanceTargetGG :
    AcceptedRun (addInstanceTarget instanceGG 0 false) :=
  fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

/-- Adding an instance witnesses grounded justified to justified. -/
theorem addInstance_justified_to_justified :
    SuccessfulCoreCell Semantics.groundedSem (graphState instanceJJ)
      (addInstanceTarget instanceJJ 0) (.addInstance "new" (newNodeTerm 0))
      pA .justified .justified :=
  successfulCoreCellOf instanceSourceJJ instanceTargetJJ _ _ _
    (by rfl) (by decide)

/-- Adding an instance witnesses grounded refuted to justified. -/
theorem addInstance_refuted_to_justified :
    SuccessfulCoreCell Semantics.groundedSem (graphState instanceDJ)
      (addInstanceTarget instanceDJ 0) (.addInstance "new" (newNodeTerm 0))
      pA .defeated .justified :=
  successfulCoreCellOf instanceSourceDJ instanceTargetDJ _ _ _
    (by rfl) (by decide)

/-- Adding an instance witnesses grounded refuted to refuted. -/
theorem addInstance_refuted_to_refuted :
    SuccessfulCoreCell Semantics.groundedSem (graphState instanceDD)
      (addInstanceTarget instanceDD 1) (.addInstance "new" (newNodeTerm 1))
      pA .defeated .defeated :=
  successfulCoreCellOf instanceSourceDD instanceTargetDD _ _ _
    (by rfl) (by decide)

/-- Adding an instance witnesses grounded refuted to both. -/
theorem addInstance_refuted_to_both :
    SuccessfulCoreCell Semantics.groundedSem (graphState instanceDC)
      (addInstanceTarget instanceDC 1) (.addInstance "new" (newNodeTerm 1))
      pA .defeated .contested :=
  successfulCoreCellOf instanceSourceDC instanceTargetDC _ _ _
    (by rfl) (by decide)

/-- Adding an instance witnesses grounded both to justified. -/
theorem addInstance_both_to_justified :
    SuccessfulCoreCell Semantics.groundedSem (graphState instanceCJ)
      (addInstanceTarget instanceCJ 1) (.addInstance "new" (newNodeTerm 1))
      pA .contested .justified :=
  successfulCoreCellOf instanceSourceCJ instanceTargetCJ _ _ _
    (by rfl) (by decide)

/-- Adding an instance witnesses grounded both to both. -/
theorem addInstance_both_to_both :
    SuccessfulCoreCell Semantics.groundedSem (graphState instanceCC)
      (addInstanceTarget instanceCC 0) (.addInstance "new" (newNodeTerm 0))
      pA .contested .contested :=
  successfulCoreCellOf instanceSourceCC instanceTargetCC _ _ _
    (by rfl) (by decide)

/-- Adding an instance witnesses grounded gap to justified. -/
theorem addInstance_gap_to_justified :
    SuccessfulCoreCell Semantics.groundedSem (graphState instanceGJ)
      (addInstanceTarget instanceGJ 0) (.addInstance "new" (newNodeTerm 0))
      pA .gap .justified :=
  successfulCoreCellOf instanceSourceGJ instanceTargetGJ _ _ _
    (by rfl) (by decide)

/-- Adding an instance witnesses grounded gap to refuted. -/
theorem addInstance_gap_to_refuted :
    SuccessfulCoreCell Semantics.groundedSem (graphState instanceGD)
      (addInstanceTarget instanceGD 1) (.addInstance "new" (newNodeTerm 1))
      pA .gap .defeated :=
  successfulCoreCellOf instanceSourceGD instanceTargetGD _ _ _
    (by rfl) (by decide)

/-- Adding an instance witnesses grounded gap to both. -/
theorem addInstance_gap_to_both :
    SuccessfulCoreCell Semantics.groundedSem (graphState instanceGC)
      (addInstanceTarget instanceGC 0) (.addInstance "new" (newNodeTerm 0))
      pA .gap .contested :=
  successfulCoreCellOf instanceSourceGC instanceTargetGC _ _ _
    (by rfl) (by decide)

/-- Adding an unrelated instance witnesses grounded gap to gap. -/
theorem addInstance_gap_to_gap :
    SuccessfulCoreCell Semantics.groundedSem (graphState instanceGG)
      (addInstanceTarget instanceGG 0 false) (.addInstance "new" newAuxTerm)
      pA .gap .gap :=
  successfulCoreCellOf instanceSourceGG instanceTargetGG _ _ _
    (by rfl) (by decide)

/-! ### Grounded AGM probe

Exactly success and additive inclusion are tested.  Both fail for the fixed
grounded belief-set projection, so the AGM comparison stops here; no remaining
postulates are claimed, and the projection is not adjusted to make them hold. -/

/-- AGM-style success fails on a real accepted `addInstance`: the fresh row at
index `2` is the target's sole support for `pA`, but that support is defeated
on arrival and `pA` is not in the resulting grounded belief set. -/
theorem agm_success_fails :
    ∃ (sourceRun : AcceptedRun (graphState instanceGD))
        (targetRun : AcceptedRun (addInstanceTarget instanceGD 1)),
      Lara.Update.applyUpdate registryEx (graphState instanceGD)
          (.addInstance "new" (newNodeTerm 1)) =
        .ok (addInstanceTarget instanceGD 1) ∧
      Lara.Update.coreObs Semantics.groundedSem sourceRun.checked pA =
        .observed .gap ∧
      Lara.Update.InstanceFresh (graphState instanceGD) "new" (newNodeTerm 1) ∧
      targetRun.checked.program.args[2]? = some (newNodeTerm 1) ∧
      targetRun.checked.nodes[2]?.map (fun node =>
        (node.term, node.conclusion)) = some (newNodeTerm 1, pA) ∧
      Consistency.claimSupportFor targetRun.checked pA = [2] ∧
      Lara.Update.coreObs Semantics.groundedSem targetRun.checked pA =
        .observed .defeated ∧
      ¬ Lara.Update.beliefSet Semantics.groundedSem targetRun.checked pA := by
  refine ⟨instanceSourceGD, instanceTargetGD, by rfl, by decide, ?_, by decide,
    by decide, by decide, by decide, ?_⟩
  · apply (Lara.Update.instanceFreshB_iff _ _ _).mp
    decide
  · change Lara.Update.coreObs Semantics.groundedSem
      instanceTargetGD.checked pA ≠ .observed .justified
    decide

/-- Additive inclusion fails on a real accepted `addAttack`: `pA` belongs to
the source grounded belief set, is absent from the target belief set, and hence
the source belief set is not a subset of the target belief set. -/
theorem agm_inclusion_fails :
    ∃ (sourceRun : AcceptedRun (graphState attackJD))
        (targetRun : AcceptedRun (addAttackTarget attackJD (1, 0))),
      Lara.Update.applyUpdate registryEx (graphState attackJD)
          (.addAttack (graphRawAttack (1, 0))) =
        .ok (addAttackTarget attackJD (1, 0)) ∧
      Lara.Update.beliefSet Semantics.groundedSem sourceRun.checked pA ∧
      ¬ Lara.Update.beliefSet Semantics.groundedSem targetRun.checked pA ∧
      ¬ ∀ q,
        Lara.Update.beliefSet Semantics.groundedSem sourceRun.checked q →
        Lara.Update.beliefSet Semantics.groundedSem targetRun.checked q := by
  have hsource :
      Lara.Update.beliefSet Semantics.groundedSem attackSourceJD.checked pA := by
    change Lara.Update.coreObs Semantics.groundedSem
      attackSourceJD.checked pA = .observed .justified
    decide
  have htarget :
      ¬ Lara.Update.beliefSet Semantics.groundedSem attackTargetJD.checked pA := by
    change Lara.Update.coreObs Semantics.groundedSem
      attackTargetJD.checked pA ≠ .observed .justified
    decide
  refine ⟨attackSourceJD, attackTargetJD, by rfl, hsource, htarget, ?_⟩
  intro hsubset
  exact htarget (hsubset pA hsource)

/-! ### Typed, theorem-anchored matrix inventory and deterministic emitter -/

/-- The four source edits represented by the publication matrices. -/
inductive UpdateKind where
  | addLeaf
  | tighten
  | addAttack
  | addInstance
deriving DecidableEq, Repr

/-- Closed publication vocabulary for grounded statuses. -/
inductive PublicationStatus where
  | justified
  | refuted
  | both
  | gap
deriving DecidableEq, Repr

def PublicationStatus.grounded : PublicationStatus → Grounded.Status
  | .justified => .justified
  | .refuted => .defeated
  | .both => .contested
  | .gap => .gap

private def PublicationStatus.label : PublicationStatus → String
  | .justified => "justified"
  | .refuted => "refuted"
  | .both => "both"
  | .gap => "gap"

private def UpdateKind.label : UpdateKind → String
  | .addLeaf => "addLeaf"
  | .tighten => "tighten"
  | .addAttack => "addAttack"
  | .addInstance => "addInstance"

/-- Canonical publication order for rows and columns. -/
def publicationStatuses : List PublicationStatus :=
  [.justified, .refuted, .both, .gap]

/-- One typed source-to-target coordinate. -/
structure MatrixCoordinate where
  source : PublicationStatus
  target : PublicationStatus
deriving DecidableEq, Repr

/-- The canonical row-major four-by-four Cartesian product. -/
def canonicalCoordinates : List MatrixCoordinate :=
  publicationStatuses.flatMap fun source =>
    publicationStatuses.map fun target => ⟨source, target⟩

/-- The canonical Cartesian-product coordinates are unique. -/
theorem canonicalCoordinates_nodup : canonicalCoordinates.Nodup := by decide

/-- The canonical Cartesian product contains exactly sixteen coordinates. -/
theorem canonicalCoordinates_length : canonicalCoordinates.length = 16 := by decide

/-- A source update belongs to exactly the constructor family named by its
matrix. -/
inductive UpdateOfKind : UpdateKind → Lara.Update.SourceUpdate → Prop where
  | addLeaf {id : LeafId} {a : Atom} {m : Admission.LeafMeta} :
      UpdateOfKind .addLeaf (.addLeaf id a m)
  | tighten {key : Presentation.LeafKind × Presentation.Provenance} :
      UpdateOfKind .tighten (.tighten key)
  | addAttack {raw : RawAttack.RawAttack} :
      UpdateOfKind .addAttack (.addAttack raw)
  | addInstance {name : String} {w : SupportTerm} :
      UpdateOfKind .addInstance (.addInstance name w)

/-- A reachable tag is sound when it projects to a real exported cell witness
of the indexed update kind and coordinate. -/
def ReachableClaim
    (kind : UpdateKind) (source target : PublicationStatus) : Prop :=
  ∃ (beforeState afterState : Lara.Update.SourceState)
      (update : Lara.Update.SourceUpdate) (p : Atom),
    UpdateOfKind kind update ∧
    SuccessfulCoreCell Semantics.groundedSem beforeState afterState update p
      source.grounded target.grounded

/-- Closed reachable-cell tags.  No constructor exists at an unreachable
coordinate. -/
inductive ReachableTag : UpdateKind → PublicationStatus → PublicationStatus → Type
  | addLeafJJ : ReachableTag .addLeaf .justified .justified
  | addLeafDD : ReachableTag .addLeaf .refuted .refuted
  | addLeafCC : ReachableTag .addLeaf .both .both
  | addLeafGG : ReachableTag .addLeaf .gap .gap
  | tightenJJ : ReachableTag .tighten .justified .justified
  | tightenJD : ReachableTag .tighten .justified .refuted
  | tightenJC : ReachableTag .tighten .justified .both
  | tightenJG : ReachableTag .tighten .justified .gap
  | tightenDJ : ReachableTag .tighten .refuted .justified
  | tightenDD : ReachableTag .tighten .refuted .refuted
  | tightenDC : ReachableTag .tighten .refuted .both
  | tightenDG : ReachableTag .tighten .refuted .gap
  | tightenCJ : ReachableTag .tighten .both .justified
  | tightenCD : ReachableTag .tighten .both .refuted
  | tightenCC : ReachableTag .tighten .both .both
  | tightenCG : ReachableTag .tighten .both .gap
  | tightenGG : ReachableTag .tighten .gap .gap
  | addAttackJJ : ReachableTag .addAttack .justified .justified
  | addAttackJD : ReachableTag .addAttack .justified .refuted
  | addAttackJC : ReachableTag .addAttack .justified .both
  | addAttackDJ : ReachableTag .addAttack .refuted .justified
  | addAttackDD : ReachableTag .addAttack .refuted .refuted
  | addAttackDC : ReachableTag .addAttack .refuted .both
  | addAttackCJ : ReachableTag .addAttack .both .justified
  | addAttackCD : ReachableTag .addAttack .both .refuted
  | addAttackCC : ReachableTag .addAttack .both .both
  | addAttackGG : ReachableTag .addAttack .gap .gap
  | addInstanceJJ : ReachableTag .addInstance .justified .justified
  | addInstanceDJ : ReachableTag .addInstance .refuted .justified
  | addInstanceDD : ReachableTag .addInstance .refuted .refuted
  | addInstanceDC : ReachableTag .addInstance .refuted .both
  | addInstanceCJ : ReachableTag .addInstance .both .justified
  | addInstanceCC : ReachableTag .addInstance .both .both
  | addInstanceGJ : ReachableTag .addInstance .gap .justified
  | addInstanceGD : ReachableTag .addInstance .gap .refuted
  | addInstanceGC : ReachableTag .addInstance .gap .both
  | addInstanceGG : ReachableTag .addInstance .gap .gap

/-- Every reachable tag is projected to its actual exported witness theorem. -/
theorem ReachableTag.sound :
    ReachableTag kind source target → ReachableClaim kind source target
  | .addLeafJJ =>
      ⟨graphState fixtureJ, addLeafTarget fixtureJ,
        .addLeaf lh4 h4 addLeafMeta, pA, .addLeaf,
        addLeaf_justified_to_justified⟩
  | .addLeafDD =>
      ⟨graphState fixtureD, addLeafTarget fixtureD,
        .addLeaf lh4 h4 addLeafMeta, pA, .addLeaf,
        addLeaf_refuted_to_refuted⟩
  | .addLeafCC =>
      ⟨graphState fixtureC, addLeafTarget fixtureC,
        .addLeaf lh4 h4 addLeafMeta, pA, .addLeaf,
        addLeaf_both_to_both⟩
  | .addLeafGG =>
      ⟨graphState fixtureG, addLeafTarget fixtureG,
        .addLeaf lh4 h4 addLeafMeta, pA, .addLeaf,
        addLeaf_gap_to_gap⟩
  | .tightenJJ =>
      ⟨graphState tightJJ, tightenTarget tightJJ, .tighten quarantineKey,
        pA, .tighten, tighten_justified_to_justified⟩
  | .tightenJD =>
      ⟨graphState tightJD, tightenTarget tightJD, .tighten quarantineKey,
        pA, .tighten, tighten_justified_to_refuted⟩
  | .tightenJC =>
      ⟨graphState tightJC, tightenTarget tightJC, .tighten quarantineKey,
        pA, .tighten, tighten_justified_to_both⟩
  | .tightenJG =>
      ⟨graphState tightJG, tightenTarget tightJG, .tighten quarantineKey,
        pA, .tighten, tighten_justified_to_gap⟩
  | .tightenDJ =>
      ⟨graphState tightDJ, tightenTarget tightDJ, .tighten quarantineKey,
        pA, .tighten, tighten_refuted_to_justified⟩
  | .tightenDD =>
      ⟨graphState tightDD, tightenTarget tightDD, .tighten quarantineKey,
        pA, .tighten, tighten_refuted_to_refuted⟩
  | .tightenDC =>
      ⟨graphState tightDC, tightenTarget tightDC, .tighten quarantineKey,
        pA, .tighten, tighten_refuted_to_both⟩
  | .tightenDG =>
      ⟨graphState tightDG, tightenTarget tightDG, .tighten quarantineKey,
        pA, .tighten, tighten_refuted_to_gap⟩
  | .tightenCJ =>
      ⟨graphState tightCJ, tightenTarget tightCJ, .tighten quarantineKey,
        pA, .tighten, tighten_both_to_justified⟩
  | .tightenCD =>
      ⟨graphState tightCD, tightenTarget tightCD, .tighten quarantineKey,
        pA, .tighten, tighten_both_to_refuted⟩
  | .tightenCC =>
      ⟨graphState tightCC, tightenTarget tightCC, .tighten quarantineKey,
        pA, .tighten, tighten_both_to_both⟩
  | .tightenCG =>
      ⟨graphState tightCG, tightenTarget tightCG, .tighten quarantineKey,
        pA, .tighten, tighten_both_to_gap⟩
  | .tightenGG =>
      ⟨graphState tightGG, tightenTarget tightGG, .tighten quarantineKey,
        pA, .tighten, tighten_gap_to_gap⟩
  | .addAttackJJ =>
      ⟨graphState attackJJ, addAttackTarget attackJJ (0, 1),
        .addAttack (graphRawAttack (0, 1)), pA, .addAttack,
        addAttack_justified_to_justified⟩
  | .addAttackJD =>
      ⟨graphState attackJD, addAttackTarget attackJD (1, 0),
        .addAttack (graphRawAttack (1, 0)), pA, .addAttack,
        addAttack_justified_to_refuted⟩
  | .addAttackJC =>
      ⟨graphState attackJC, addAttackTarget attackJC (0, 0),
        .addAttack (graphRawAttack (0, 0)), pA, .addAttack,
        addAttack_justified_to_both⟩
  | .addAttackDJ =>
      ⟨graphState attackDJ, addAttackTarget attackDJ (2, 0),
        .addAttack (graphRawAttack (2, 0)), pA, .addAttack,
        addAttack_refuted_to_justified⟩
  | .addAttackDD =>
      ⟨graphState attackDD, addAttackTarget attackDD (1, 1),
        .addAttack (graphRawAttack (1, 1)), pA, .addAttack,
        addAttack_refuted_to_refuted⟩
  | .addAttackDC =>
      ⟨graphState attackDC, addAttackTarget attackDC (0, 0),
        .addAttack (graphRawAttack (0, 0)), pA, .addAttack,
        addAttack_refuted_to_both⟩
  | .addAttackCJ =>
      ⟨graphState attackCJ, addAttackTarget attackCJ (2, 0),
        .addAttack (graphRawAttack (2, 0)), pA, .addAttack,
        addAttack_both_to_justified⟩
  | .addAttackCD =>
      ⟨graphState attackCD, addAttackTarget attackCD (1, 0),
        .addAttack (graphRawAttack (1, 0)), pA, .addAttack,
        addAttack_both_to_refuted⟩
  | .addAttackCC =>
      ⟨graphState attackCC, addAttackTarget attackCC (0, 1),
        .addAttack (graphRawAttack (0, 1)), pA, .addAttack,
        addAttack_both_to_both⟩
  | .addAttackGG =>
      ⟨graphState attackGG, addAttackTarget attackGG (0, 1),
        .addAttack (graphRawAttack (0, 1)), pA, .addAttack,
        addAttack_gap_to_gap⟩
  | .addInstanceJJ =>
      ⟨graphState instanceJJ, addInstanceTarget instanceJJ 0,
        .addInstance "new" (newNodeTerm 0), pA, .addInstance,
        addInstance_justified_to_justified⟩
  | .addInstanceDJ =>
      ⟨graphState instanceDJ, addInstanceTarget instanceDJ 0,
        .addInstance "new" (newNodeTerm 0), pA, .addInstance,
        addInstance_refuted_to_justified⟩
  | .addInstanceDD =>
      ⟨graphState instanceDD, addInstanceTarget instanceDD 1,
        .addInstance "new" (newNodeTerm 1), pA, .addInstance,
        addInstance_refuted_to_refuted⟩
  | .addInstanceDC =>
      ⟨graphState instanceDC, addInstanceTarget instanceDC 1,
        .addInstance "new" (newNodeTerm 1), pA, .addInstance,
        addInstance_refuted_to_both⟩
  | .addInstanceCJ =>
      ⟨graphState instanceCJ, addInstanceTarget instanceCJ 1,
        .addInstance "new" (newNodeTerm 1), pA, .addInstance,
        addInstance_both_to_justified⟩
  | .addInstanceCC =>
      ⟨graphState instanceCC, addInstanceTarget instanceCC 0,
        .addInstance "new" (newNodeTerm 0), pA, .addInstance,
        addInstance_both_to_both⟩
  | .addInstanceGJ =>
      ⟨graphState instanceGJ, addInstanceTarget instanceGJ 0,
        .addInstance "new" (newNodeTerm 0), pA, .addInstance,
        addInstance_gap_to_justified⟩
  | .addInstanceGD =>
      ⟨graphState instanceGD, addInstanceTarget instanceGD 1,
        .addInstance "new" (newNodeTerm 1), pA, .addInstance,
        addInstance_gap_to_refuted⟩
  | .addInstanceGC =>
      ⟨graphState instanceGC, addInstanceTarget instanceGC 0,
        .addInstance "new" (newNodeTerm 0), pA, .addInstance,
        addInstance_gap_to_both⟩
  | .addInstanceGG =>
      ⟨graphState instanceGG, addInstanceTarget instanceGG 0 false,
        .addInstance "new" newAuxTerm, pA, .addInstance,
        addInstance_gap_to_gap⟩

/-- Closed unreachable-cell tags.  Constructor indices and disequalities
encode exactly the coordinates ruled out by each named theorem family. -/
inductive UnreachableTag :
    UpdateKind → PublicationStatus → PublicationStatus → Type
  | addLeafFixed {source target} (different : source ≠ target) :
      UnreachableTag .addLeaf source target
  | tightenGapEscape {target} (different : target ≠ .gap) :
      UnreachableTag .tighten .gap target
  | addAttackNoGap {source} (nonGap : source ≠ .gap) :
      UnreachableTag .addAttack source .gap
  | addAttackGapFixed {target} (nonGap : target ≠ .gap) :
      UnreachableTag .addAttack .gap target
  | addInstanceNoGap {source} (nonGap : source ≠ .gap) :
      UnreachableTag .addInstance source .gap
  | addInstanceJustifiedRefuted :
      UnreachableTag .addInstance .justified .refuted
  | addInstanceJustifiedBoth :
      UnreachableTag .addInstance .justified .both
  | addInstanceBothRefuted :
      UnreachableTag .addInstance .both .refuted

/-- The exact accepted source/target runs and observed transition represented by
an indexed matrix coordinate. -/
inductive MatrixRun :
    UpdateKind → PublicationStatus → PublicationStatus → Type
  | addLeaf (sourceState targetState : Lara.Update.SourceState) (p : Atom)
      (leafId : LeafId) (a : Atom) (m : Admission.LeafMeta)
      (sourceRun : AcceptedRun sourceState)
      (targetRun : AcceptedRun targetState)
      (apply_ok : Lara.Update.applyUpdate registryEx sourceState
        (.addLeaf leafId a m) = .ok targetState)
      (transition : Lara.Update.CoreTransition Semantics.groundedSem
        sourceRun.checked targetRun.checked p =
          (.observed source.grounded, .observed target.grounded)) :
      MatrixRun .addLeaf source target
  | tighten (sourceState targetState : Lara.Update.SourceState) (p : Atom)
      (key : Presentation.LeafKind × Presentation.Provenance)
      (sourceRun : AcceptedRun sourceState)
      (targetRun : AcceptedRun targetState)
      (apply_ok : Lara.Update.applyUpdate registryEx sourceState
        (.tighten key) = .ok targetState)
      (transition : Lara.Update.CoreTransition Semantics.groundedSem
        sourceRun.checked targetRun.checked p =
          (.observed source.grounded, .observed target.grounded)) :
      MatrixRun .tighten source target
  | addAttack (sourceState targetState : Lara.Update.SourceState) (p : Atom)
      (raw : RawAttack.RawAttack)
      (sourceRun : AcceptedRun sourceState)
      (targetRun : AcceptedRun targetState)
      (apply_ok : Lara.Update.applyUpdate registryEx sourceState
        (.addAttack raw) = .ok targetState)
      (transition : Lara.Update.CoreTransition Semantics.groundedSem
        sourceRun.checked targetRun.checked p =
          (.observed source.grounded, .observed target.grounded)) :
      MatrixRun .addAttack source target
  | addInstance (sourceState targetState : Lara.Update.SourceState) (p : Atom)
      (name : String) (w : SupportTerm)
      (sourceRun : AcceptedRun sourceState)
      (targetRun : AcceptedRun targetState)
      (apply_ok : Lara.Update.applyUpdate registryEx sourceState
        (.addInstance name w) = .ok targetState)
      (transition : Lara.Update.CoreTransition Semantics.groundedSem
        sourceRun.checked targetRun.checked p =
          (.observed source.grounded, .observed target.grounded)) :
      MatrixRun .addInstance source target

/-- Freshness and new-argument completeness required by the sink-status
blocker. -/
def InstanceSinkPremises
    (sourceState : Lara.Update.SourceState) (name : String)
    (w : SupportTerm) : Prop :=
  Lara.Update.InstanceFresh sourceState name w ∧
    ∃ C, HasSupport id sourceState.policy.ruleLookup
      (Admission.buildGamma
        (Admission.buildPrune id sourceState.table sourceState.metas
          sourceState.leaves sourceState.argsRaw sourceState.rawAtts
          sourceState.groups []).checkedLeaves)
      (certOkOf registryEx) w C []

/-- Constructor-local hypotheses required by the blocker theorem assigned to an
unreachable tag. -/
def UnreachablePremises :
    (tag : UnreachableTag kind source target) →
    MatrixRun kind source target → Prop
  | .addLeafFixed _, .addLeaf sourceState _ _ leafId _ m _ _ _ _ =>
      Lara.Update.AddLeafFresh sourceState leafId ∧
        Admission.decisionFor sourceState.table m.kind m.provenance = .admit
  | .tightenGapEscape _, .tighten sourceState _ _ key _ _ _ _ =>
      Lara.Update.NonInstanceUpdate id sourceState (.tighten key)
  | .addAttackNoGap _, .addAttack sourceState _ _ raw _ _ _ _ =>
      Lara.Update.AdditiveUpdate sourceState (.addAttack raw)
  | .addAttackGapFixed _, .addAttack _ _ _ _ _ _ _ _ => True
  | .addInstanceNoGap _, .addInstance sourceState _ _ name w _ _ _ _ =>
      Lara.Update.AdditiveUpdate sourceState (.addInstance name w)
  | .addInstanceJustifiedRefuted,
      .addInstance sourceState _ _ name w _ _ _ _ =>
      InstanceSinkPremises sourceState name w
  | .addInstanceJustifiedBoth,
      .addInstance sourceState _ _ name w _ _ _ _ =>
      InstanceSinkPremises sourceState name w
  | .addInstanceBothRefuted,
      .addInstance sourceState _ _ name w _ _ _ _ =>
      InstanceSinkPremises sourceState name w

/-- An unreachable tag rules out every exact accepted run at its indexed
coordinate under the constructor-local premises of its blocker theorem. -/
def UnreachableClaim (tag : UnreachableTag kind source target) : Prop :=
  ∀ run : MatrixRun kind source target, UnreachablePremises tag run → False

private theorem PublicationStatus.grounded_injective :
    Function.Injective PublicationStatus.grounded := by
  intro left right equal
  cases left <;> cases right <;>
    simp_all [PublicationStatus.grounded]

/-- Every unreachable tag applies its assigned blocker theorem to the exact
accepted runs and status pair carried by the indexed matrix domain. -/
theorem UnreachableTag.sound :
    (tag : UnreachableTag kind source target) → UnreachableClaim tag
  | .addLeafFixed different => by
      intro run premises
      cases run with
      | addLeaf sourceState targetState p leafId a m sourceRun targetRun
          apply_ok transition =>
          have fixed := Lara.Update.addLeaf_core_fixed (canon := id) registryEx
            sourceState targetState p leafId a m sourceRun.declared
            sourceRun.admission sourceRun.checked targetRun.declared
            targetRun.admission targetRun.checked sourceRun.admission_ok
            sourceRun.check_ok apply_ok targetRun.admission_ok
            targetRun.check_ok premises.1 premises.2
          have sourceObserved :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).1 =
                .observed source.grounded := by
            simpa using congrArg Prod.fst transition
          have targetObserved :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).2 =
                .observed target.grounded := by
            simpa using congrArg Prod.snd transition
          have observationsEqual :
              Semantics.ClaimObservation.observed source.grounded =
                .observed target.grounded :=
            sourceObserved.symm.trans (fixed.trans targetObserved)
          have statusesEqual : source.grounded = target.grounded := by
            injection observationsEqual
          exact different
            (PublicationStatus.grounded_injective statusesEqual)
  | .tightenGapEscape different => by
      intro run nonInstance
      cases run with
      | tighten sourceState targetState p key sourceRun targetRun apply_ok
          transition =>
          have sourceGap :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).1 =
                .observed Grounded.Status.gap := by
            simpa [PublicationStatus.grounded] using congrArg Prod.fst transition
          have targetGap := Lara.Update.nonInstance_gap_fixed (canon := id)
            Semantics.groundedSem registryEx sourceState targetState p
            (.tighten key) sourceRun.declared sourceRun.admission
            sourceRun.checked targetRun.declared targetRun.admission
            targetRun.checked sourceRun.admission_ok sourceRun.check_ok apply_ok
            targetRun.admission_ok targetRun.check_ok nonInstance sourceGap
          have targetObserved :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).2 =
                .observed target.grounded := by
            simpa using congrArg Prod.snd transition
          have groundedEqual : target.grounded = PublicationStatus.gap.grounded := by
            injection targetObserved.symm.trans targetGap
          exact different
            (PublicationStatus.grounded_injective groundedEqual)
  | .addAttackNoGap nonGap => by
      intro run additive
      cases run with
      | addAttack sourceState targetState p raw sourceRun targetRun apply_ok
          transition =>
          have sourceObserved :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).1 =
                .observed source.grounded := by
            simpa using congrArg Prod.fst transition
          have sourceNotGap :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).1 ≠
                .observed Grounded.Status.gap := by
            intro sourceGap
            have groundedEqual :
                source.grounded = PublicationStatus.gap.grounded := by
              injection sourceObserved.symm.trans sourceGap
            exact nonGap
              (PublicationStatus.grounded_injective groundedEqual)
          have targetNotGap := Lara.Update.additive_no_gap_entry (canon := id)
            Semantics.groundedSem registryEx sourceState targetState p
            (.addAttack raw) sourceRun.declared sourceRun.admission
            sourceRun.checked targetRun.declared targetRun.admission
            targetRun.checked sourceRun.admission_ok sourceRun.check_ok apply_ok
            targetRun.admission_ok targetRun.check_ok additive sourceNotGap
          have targetGap :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).2 =
                .observed Grounded.Status.gap := by
            rw [transition]
            rfl
          exact targetNotGap targetGap
  | .addAttackGapFixed nonGap => by
      intro run _
      cases run with
      | addAttack sourceState targetState p raw sourceRun targetRun apply_ok
          transition =>
          have sourceGap :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).1 =
                .observed Grounded.Status.gap := by
            simpa [PublicationStatus.grounded] using congrArg Prod.fst transition
          have targetGap := Lara.Update.addAttack_gap_fixed (canon := id)
            Semantics.groundedSem registryEx sourceState targetState p raw
            sourceRun.declared sourceRun.admission sourceRun.checked
            targetRun.declared targetRun.admission targetRun.checked
            sourceRun.admission_ok sourceRun.check_ok apply_ok
            targetRun.admission_ok targetRun.check_ok sourceGap
          have targetObserved :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).2 =
                .observed target.grounded := by
            simpa using congrArg Prod.snd transition
          have groundedEqual : target.grounded = PublicationStatus.gap.grounded := by
            injection targetObserved.symm.trans targetGap
          exact nonGap
            (PublicationStatus.grounded_injective groundedEqual)
  | .addInstanceNoGap nonGap => by
      intro run additive
      cases run with
      | addInstance sourceState targetState p name w sourceRun targetRun apply_ok
          transition =>
          have sourceObserved :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).1 =
                .observed source.grounded := by
            simpa using congrArg Prod.fst transition
          have sourceNotGap :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).1 ≠
                .observed Grounded.Status.gap := by
            intro sourceGap
            have groundedEqual :
                source.grounded = PublicationStatus.gap.grounded := by
              injection sourceObserved.symm.trans sourceGap
            exact nonGap
              (PublicationStatus.grounded_injective groundedEqual)
          have targetNotGap := Lara.Update.additive_no_gap_entry (canon := id)
            Semantics.groundedSem registryEx sourceState targetState p
            (.addInstance name w) sourceRun.declared sourceRun.admission
            sourceRun.checked targetRun.declared targetRun.admission
            targetRun.checked sourceRun.admission_ok sourceRun.check_ok apply_ok
            targetRun.admission_ok targetRun.check_ok additive sourceNotGap
          have targetGap :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).2 =
                .observed Grounded.Status.gap := by
            rw [transition]
            rfl
          exact targetNotGap targetGap
  | .addInstanceJustifiedRefuted => by
      intro run premises
      cases run with
      | addInstance sourceState targetState p name w sourceRun targetRun apply_ok
          transition =>
          have monotone := Lara.Update.addInstance_sink_status_monotone
            (canon := id) registryEx sourceState targetState p name w
            sourceRun.declared sourceRun.admission sourceRun.checked
            targetRun.declared targetRun.admission targetRun.checked
            sourceRun.admission_ok sourceRun.check_ok apply_ok
            targetRun.admission_ok targetRun.check_ok premises.1 premises.2
          have sourceJustified :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).1 =
                .observed Grounded.Status.justified := by
            simpa [PublicationStatus.grounded] using congrArg Prod.fst transition
          have targetRefuted :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).2 =
                .observed Grounded.Status.defeated := by
            simpa [PublicationStatus.grounded] using congrArg Prod.snd transition
          have := (monotone.1 sourceJustified).symm.trans targetRefuted
          simp at this
  | .addInstanceJustifiedBoth => by
      intro run premises
      cases run with
      | addInstance sourceState targetState p name w sourceRun targetRun apply_ok
          transition =>
          have monotone := Lara.Update.addInstance_sink_status_monotone
            (canon := id) registryEx sourceState targetState p name w
            sourceRun.declared sourceRun.admission sourceRun.checked
            targetRun.declared targetRun.admission targetRun.checked
            sourceRun.admission_ok sourceRun.check_ok apply_ok
            targetRun.admission_ok targetRun.check_ok premises.1 premises.2
          have sourceJustified :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).1 =
                .observed Grounded.Status.justified := by
            simpa [PublicationStatus.grounded] using congrArg Prod.fst transition
          have targetBoth :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).2 =
                .observed Grounded.Status.contested := by
            simpa [PublicationStatus.grounded] using congrArg Prod.snd transition
          have := (monotone.1 sourceJustified).symm.trans targetBoth
          simp at this
  | .addInstanceBothRefuted => by
      intro run premises
      cases run with
      | addInstance sourceState targetState p name w sourceRun targetRun apply_ok
          transition =>
          have monotone := Lara.Update.addInstance_sink_status_monotone
            (canon := id) registryEx sourceState targetState p name w
            sourceRun.declared sourceRun.admission sourceRun.checked
            targetRun.declared targetRun.admission targetRun.checked
            sourceRun.admission_ok sourceRun.check_ok apply_ok
            targetRun.admission_ok targetRun.check_ok premises.1 premises.2
          have sourceBoth :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).1 =
                .observed Grounded.Status.contested := by
            simpa [PublicationStatus.grounded] using congrArg Prod.fst transition
          have targetRefuted :
              (Lara.Update.CoreTransition Semantics.groundedSem
                sourceRun.checked targetRun.checked p).2 =
                .observed Grounded.Status.defeated := by
            rw [transition]
            rfl
          exact monotone.2 sourceBoth targetRefuted

/-- The rendered blocker annotations are selected by a plain closed tag match. -/
private def UnreachableTag.theoremName :
    UnreachableTag kind source target → String
  | .addLeafFixed _ => "addLeaf_core_fixed"
  | .tightenGapEscape _ => "nonInstance_gap_fixed"
  | .addAttackNoGap _ => "additive_no_gap_entry"
  | .addAttackGapFixed _ => "addAttack_gap_fixed"
  | .addInstanceNoGap _ => "additive_no_gap_entry"
  | .addInstanceJustifiedRefuted => "addInstance_sink_status_monotone"
  | .addInstanceJustifiedBoth => "addInstance_sink_status_monotone"
  | .addInstanceBothRefuted => "addInstance_sink_status_monotone"

/-- Whether the blocker carries nontrivial constructor-local hypotheses that
cannot be recovered by matching the update constructor alone. -/
private def UnreachableTag.conditionalB :
    UnreachableTag kind source target → Bool
  | .addLeafFixed _ => true
  | .tightenGapEscape _ => true
  | .addAttackNoGap _ => false
  | .addAttackGapFixed _ => false
  | .addInstanceNoGap _ => false
  | .addInstanceJustifiedRefuted => true
  | .addInstanceJustifiedBoth => true
  | .addInstanceBothRefuted => true

private def ReachableTag.theoremName :
    ReachableTag kind source target → String
  | .addLeafJJ => "addLeaf_justified_to_justified"
  | .addLeafDD => "addLeaf_refuted_to_refuted"
  | .addLeafCC => "addLeaf_both_to_both"
  | .addLeafGG => "addLeaf_gap_to_gap"
  | .tightenJJ => "tighten_justified_to_justified"
  | .tightenJD => "tighten_justified_to_refuted"
  | .tightenJC => "tighten_justified_to_both"
  | .tightenJG => "tighten_justified_to_gap"
  | .tightenDJ => "tighten_refuted_to_justified"
  | .tightenDD => "tighten_refuted_to_refuted"
  | .tightenDC => "tighten_refuted_to_both"
  | .tightenDG => "tighten_refuted_to_gap"
  | .tightenCJ => "tighten_both_to_justified"
  | .tightenCD => "tighten_both_to_refuted"
  | .tightenCC => "tighten_both_to_both"
  | .tightenCG => "tighten_both_to_gap"
  | .tightenGG => "tighten_gap_to_gap"
  | .addAttackJJ => "addAttack_justified_to_justified"
  | .addAttackJD => "addAttack_justified_to_refuted"
  | .addAttackJC => "addAttack_justified_to_both"
  | .addAttackDJ => "addAttack_refuted_to_justified"
  | .addAttackDD => "addAttack_refuted_to_refuted"
  | .addAttackDC => "addAttack_refuted_to_both"
  | .addAttackCJ => "addAttack_both_to_justified"
  | .addAttackCD => "addAttack_both_to_refuted"
  | .addAttackCC => "addAttack_both_to_both"
  | .addAttackGG => "addAttack_gap_to_gap"
  | .addInstanceJJ => "addInstance_justified_to_justified"
  | .addInstanceDJ => "addInstance_refuted_to_justified"
  | .addInstanceDD => "addInstance_refuted_to_refuted"
  | .addInstanceDC => "addInstance_refuted_to_both"
  | .addInstanceCJ => "addInstance_both_to_justified"
  | .addInstanceCC => "addInstance_both_to_both"
  | .addInstanceGJ => "addInstance_gap_to_justified"
  | .addInstanceGD => "addInstance_gap_to_refuted"
  | .addInstanceGC => "addInstance_gap_to_both"
  | .addInstanceGG => "addInstance_gap_to_gap"

/-- Closed evidence for one indexed cell. -/
inductive CellEvidence :
    UpdateKind → PublicationStatus → PublicationStatus → Type
  | reachable (tag : ReachableTag kind source target) :
      CellEvidence kind source target
  | unreachable (tag : UnreachableTag kind source target) :
      CellEvidence kind source target

/-- The semantic proposition projected by a closed cell-evidence tag. -/
def CellEvidence.Claim :
    CellEvidence kind source target → Prop
  | .reachable _ => ReachableClaim kind source target
  | .unreachable tag => UnreachableClaim tag

/-- Every closed cell-evidence tag projects to its indexed semantic proof. -/
theorem CellEvidence.sound (evidence : CellEvidence kind source target) :
    evidence.Claim := by
  cases evidence with
  | reachable tag => exact tag.sound
  | unreachable tag => exact tag.sound

private def CellEvidence.reachableB :
    CellEvidence kind source target → Bool
  | .reachable _ => true
  | .unreachable _ => false


/-- Total classification of every kind/source/target triple. -/
def evidenceFor (kind : UpdateKind) (source target : PublicationStatus) :
    CellEvidence kind source target :=
  match kind, source, target with
  | .addLeaf, .justified, .justified => .reachable .addLeafJJ
  | .addLeaf, .justified, .refuted => .unreachable (.addLeafFixed (by decide))
  | .addLeaf, .justified, .both => .unreachable (.addLeafFixed (by decide))
  | .addLeaf, .justified, .gap => .unreachable (.addLeafFixed (by decide))
  | .addLeaf, .refuted, .justified => .unreachable (.addLeafFixed (by decide))
  | .addLeaf, .refuted, .refuted => .reachable .addLeafDD
  | .addLeaf, .refuted, .both => .unreachable (.addLeafFixed (by decide))
  | .addLeaf, .refuted, .gap => .unreachable (.addLeafFixed (by decide))
  | .addLeaf, .both, .justified => .unreachable (.addLeafFixed (by decide))
  | .addLeaf, .both, .refuted => .unreachable (.addLeafFixed (by decide))
  | .addLeaf, .both, .both => .reachable .addLeafCC
  | .addLeaf, .both, .gap => .unreachable (.addLeafFixed (by decide))
  | .addLeaf, .gap, .justified => .unreachable (.addLeafFixed (by decide))
  | .addLeaf, .gap, .refuted => .unreachable (.addLeafFixed (by decide))
  | .addLeaf, .gap, .both => .unreachable (.addLeafFixed (by decide))
  | .addLeaf, .gap, .gap => .reachable .addLeafGG
  | .tighten, .justified, .justified => .reachable .tightenJJ
  | .tighten, .justified, .refuted => .reachable .tightenJD
  | .tighten, .justified, .both => .reachable .tightenJC
  | .tighten, .justified, .gap => .reachable .tightenJG
  | .tighten, .refuted, .justified => .reachable .tightenDJ
  | .tighten, .refuted, .refuted => .reachable .tightenDD
  | .tighten, .refuted, .both => .reachable .tightenDC
  | .tighten, .refuted, .gap => .reachable .tightenDG
  | .tighten, .both, .justified => .reachable .tightenCJ
  | .tighten, .both, .refuted => .reachable .tightenCD
  | .tighten, .both, .both => .reachable .tightenCC
  | .tighten, .both, .gap => .reachable .tightenCG
  | .tighten, .gap, .justified =>
      .unreachable (.tightenGapEscape (by decide))
  | .tighten, .gap, .refuted =>
      .unreachable (.tightenGapEscape (by decide))
  | .tighten, .gap, .both =>
      .unreachable (.tightenGapEscape (by decide))
  | .tighten, .gap, .gap => .reachable .tightenGG
  | .addAttack, .justified, .justified => .reachable .addAttackJJ
  | .addAttack, .justified, .refuted => .reachable .addAttackJD
  | .addAttack, .justified, .both => .reachable .addAttackJC
  | .addAttack, .justified, .gap =>
      .unreachable (.addAttackNoGap (by decide))
  | .addAttack, .refuted, .justified => .reachable .addAttackDJ
  | .addAttack, .refuted, .refuted => .reachable .addAttackDD
  | .addAttack, .refuted, .both => .reachable .addAttackDC
  | .addAttack, .refuted, .gap =>
      .unreachable (.addAttackNoGap (by decide))
  | .addAttack, .both, .justified => .reachable .addAttackCJ
  | .addAttack, .both, .refuted => .reachable .addAttackCD
  | .addAttack, .both, .both => .reachable .addAttackCC
  | .addAttack, .both, .gap =>
      .unreachable (.addAttackNoGap (by decide))
  | .addAttack, .gap, .justified =>
      .unreachable (.addAttackGapFixed (by decide))
  | .addAttack, .gap, .refuted =>
      .unreachable (.addAttackGapFixed (by decide))
  | .addAttack, .gap, .both =>
      .unreachable (.addAttackGapFixed (by decide))
  | .addAttack, .gap, .gap => .reachable .addAttackGG
  | .addInstance, .justified, .justified => .reachable .addInstanceJJ
  | .addInstance, .justified, .refuted =>
      .unreachable .addInstanceJustifiedRefuted
  | .addInstance, .justified, .both =>
      .unreachable .addInstanceJustifiedBoth
  | .addInstance, .justified, .gap =>
      .unreachable (.addInstanceNoGap (by decide))
  | .addInstance, .refuted, .justified => .reachable .addInstanceDJ
  | .addInstance, .refuted, .refuted => .reachable .addInstanceDD
  | .addInstance, .refuted, .both => .reachable .addInstanceDC
  | .addInstance, .refuted, .gap =>
      .unreachable (.addInstanceNoGap (by decide))
  | .addInstance, .both, .justified => .reachable .addInstanceCJ
  | .addInstance, .both, .refuted =>
      .unreachable .addInstanceBothRefuted
  | .addInstance, .both, .both => .reachable .addInstanceCC
  | .addInstance, .both, .gap =>
      .unreachable (.addInstanceNoGap (by decide))
  | .addInstance, .gap, .justified => .reachable .addInstanceGJ
  | .addInstance, .gap, .refuted => .reachable .addInstanceGD
  | .addInstance, .gap, .both => .reachable .addInstanceGC
  | .addInstance, .gap, .gap => .reachable .addInstanceGG

/-- One typed, indexed cell in a grounded update matrix. -/
structure MatrixCellEntry (kind : UpdateKind) where
  coordinate : MatrixCoordinate
  evidence : CellEvidence kind coordinate.source coordinate.target

private def matrixFor (kind : UpdateKind) : List (MatrixCellEntry kind) :=
  canonicalCoordinates.map fun coordinate =>
    { coordinate
    , evidence := evidenceFor kind coordinate.source coordinate.target }

/-- Complete `addLeaf` grounded matrix, in canonical row-major order. -/
def addLeafMatrix : List (MatrixCellEntry .addLeaf) := matrixFor .addLeaf

/-- Complete `tighten` grounded matrix, in canonical row-major order. -/
def tightenMatrix : List (MatrixCellEntry .tighten) := matrixFor .tighten

/-- Complete `addAttack` grounded matrix, in canonical row-major order. -/
def addAttackMatrix : List (MatrixCellEntry .addAttack) := matrixFor .addAttack

/-- Complete `addInstance` grounded matrix, in canonical row-major order. -/
def addInstanceMatrix : List (MatrixCellEntry .addInstance) :=
  matrixFor .addInstance

private theorem matrixFor_coordinates (kind : UpdateKind) :
    (matrixFor kind).map (·.coordinate) = canonicalCoordinates := by
  change (canonicalCoordinates.map fun coordinate => coordinate) =
    canonicalCoordinates
  simp

/-- `addLeaf` has every canonical coordinate exactly once and in order. -/
theorem addLeaf_coordinates :
    addLeafMatrix.map (·.coordinate) = canonicalCoordinates :=
  matrixFor_coordinates .addLeaf

/-- `tighten` has every canonical coordinate exactly once and in order. -/
theorem tighten_coordinates :
    tightenMatrix.map (·.coordinate) = canonicalCoordinates :=
  matrixFor_coordinates .tighten

/-- `addAttack` has every canonical coordinate exactly once and in order. -/
theorem addAttack_coordinates :
    addAttackMatrix.map (·.coordinate) = canonicalCoordinates :=
  matrixFor_coordinates .addAttack

/-- `addInstance` has every canonical coordinate exactly once and in order. -/
theorem addInstance_coordinates :
    addInstanceMatrix.map (·.coordinate) = canonicalCoordinates :=
  matrixFor_coordinates .addInstance

private def reachableCount (entries : List (MatrixCellEntry kind)) : Nat :=
  (entries.filter fun entry => entry.evidence.reachableB).length

/-- Mechanized reachable-cell count for `addLeaf`. -/
theorem addLeaf_reachable_count : reachableCount addLeafMatrix = 4 := by decide

/-- Mechanized reachable-cell count for `tighten`. -/
theorem tighten_reachable_count : reachableCount tightenMatrix = 13 := by decide

/-- Mechanized reachable-cell count for `addAttack`. -/
theorem addAttack_reachable_count : reachableCount addAttackMatrix = 10 := by decide

/-- Mechanized reachable-cell count for `addInstance`. -/
theorem addInstance_reachable_count : reachableCount addInstanceMatrix = 10 := by decide

/-- The four exact Cartesian products contain sixty-four cells. -/
theorem grounded_matrix_cell_count :
    addLeafMatrix.length + tightenMatrix.length + addAttackMatrix.length +
      addInstanceMatrix.length = 64 := by decide

/-- The four matrices contain exactly thirty-seven reachable cells. -/
theorem grounded_reachable_count :
    reachableCount addLeafMatrix + reachableCount tightenMatrix +
      reachableCount addAttackMatrix + reachableCount addInstanceMatrix = 37 := by decide

private def padRight (width : Nat) (text : String) : String :=
  text ++ String.ofList (List.replicate (width - text.length) ' ')

private def entryText :
    CellEvidence kind source target → String
  | .reachable tag => "R " ++ tag.theoremName
  | .unreachable tag =>
      (if tag.conditionalB then "U* " else "U ") ++ tag.theoremName

private def tableRows (kind : UpdateKind) : List (List String) :=
  ("source \\ target" :: publicationStatuses.map PublicationStatus.label) ::
    publicationStatuses.map fun source =>
      source.label :: publicationStatuses.map fun target =>
        entryText (evidenceFor kind source target)

private def columnWidth (rows : List (List String)) (column : Nat) : Nat :=
  (rows.map fun row => (row.getD column "").length).foldl Nat.max 0

private def renderRows (rows : List (List String)) : String :=
  let widths := (List.range 5).map (columnWidth rows)
  String.intercalate "\n" <| rows.map fun row =>
    String.intercalate " | " <|
      (List.range 5).map fun column =>
        padRight (widths.getD column 0) (row.getD column "")

private def UpdateKind.conditionalNote : UpdateKind → String
  | .addLeaf =>
      "\nU* requires AddLeafFresh and admission of the new metadata key."
  | .tighten =>
      "\nU* requires NonInstanceUpdate restrictiveness and retained-Gamma premises."
  | .addAttack => ""
  | .addInstance =>
      "\nU* requires InstanceSinkPremises freshness and complete support."

private def renderMatrix (kind : UpdateKind)
    (entries : List (MatrixCellEntry kind)) : String :=
  s!"{kind.label} grounded core matrix\nreachable={reachableCount entries}/16\n" ++
    renderRows (tableRows kind) ++ kind.conditionalNote

/-- Deterministic publication and supplement source for all four matrices. -/
def groundedCoreMatrixReport : String :=
  String.intercalate "\n\n"
    [ renderMatrix .addLeaf addLeafMatrix,
      renderMatrix .tighten tightenMatrix,
      renderMatrix .addAttack addAttackMatrix,
      renderMatrix .addInstance addInstanceMatrix ]

/-! ### Typed five-valued tighten public matrix -/

/-- Canonical public target order: four grounded reports, then blocking. -/
def publicReports : List Lara.Update.PublicReport :=
  [.justified, .defeated, .contested, .gap, .evidenceBlocked]

/-- One exact clean-base tighten run at an indexed public coordinate. -/
structure TightenPublicRun
    (source : PublicationStatus) (target : Lara.Update.PublicReport) where
  sourceState : Lara.Update.SourceState
  targetState : Lara.Update.SourceState
  p : Atom
  key : Presentation.LeafKind × Presentation.Provenance
  sourceRun : AcceptedRun sourceState
  targetRun : AcceptedRun targetState
  apply_ok : Lara.Update.applyUpdate registryEx sourceState (.tighten key) =
    .ok targetState
  clean : Lara.Update.CleanBase sourceRun
  transition : Lara.Update.PublicTransition sourceRun
    targetRun p =
      (Lara.Update.PublicReport.ofStatus source.grounded, target)


private theorem TightenPublicRun.sourceCore
    (run : TightenPublicRun source target) :
    Grounded.statusC
      (Compile.checkedAF run.sourceRun.checked.program)
      (Consistency.completeClaimFor run.sourceRun.checked run.p) =
        source.grounded := by
  have hsource :
      Lara.Update.publicReport run.sourceRun run.p =
        Lara.Update.PublicReport.ofStatus source.grounded := by
    simpa [Lara.Update.PublicTransition] using congrArg Prod.fst run.transition
  have hclean := Lara.Update.publicReport_eq_core_of_clean
    run.sourceRun run.clean run.p
  rw [hclean] at hsource
  exact Lara.Update.PublicReport.ofStatus_injective hsource

/-- Closed reachable public tighten cells. -/
inductive TightenPublicReachableTag :
    PublicationStatus → Lara.Update.PublicReport → Type
  | justifiedJustified :
      TightenPublicReachableTag .justified .justified
  | justifiedDefeated :
      TightenPublicReachableTag .justified .defeated
  | justifiedContested :
      TightenPublicReachableTag .justified .contested
  | justifiedGap : TightenPublicReachableTag .justified .gap
  | justifiedBlocked :
      TightenPublicReachableTag .justified .evidenceBlocked
  | defeatedDefeated : TightenPublicReachableTag .refuted .defeated
  | defeatedGap : TightenPublicReachableTag .refuted .gap
  | defeatedBlocked :
      TightenPublicReachableTag .refuted .evidenceBlocked
  | contestedDefeated : TightenPublicReachableTag .both .defeated
  | contestedContested : TightenPublicReachableTag .both .contested
  | contestedGap : TightenPublicReachableTag .both .gap
  | contestedBlocked :
      TightenPublicReachableTag .both .evidenceBlocked
  | gapGap : TightenPublicReachableTag .gap .gap

/-- Semantic reachability means a real exact clean-base public cell exists. -/
def TightenPublicReachableClaim
    (source : PublicationStatus) (target : Lara.Update.PublicReport) : Prop :=
  ∃ (sourceState targetState : Lara.Update.SourceState)
      (key : Presentation.LeafKind × Presentation.Provenance) (p : Atom),
    SuccessfulPublicCell sourceState targetState (.tighten key) p
      source.grounded target

/-- Every reachable tag projects to a real exact pipeline witness. -/
theorem TightenPublicReachableTag.sound :
    TightenPublicReachableTag source target →
      TightenPublicReachableClaim source target
  | .justifiedJustified =>
      ⟨graphState tightJJ, tightenTarget tightJJ, quarantineKey, pA,
        tighten_public_justified_to_justified⟩
  | .justifiedDefeated =>
      ⟨graphState tightPublicJD, tightenTarget tightPublicJD, quarantineKey, pA,
        tighten_public_justified_to_defeated⟩
  | .justifiedContested =>
      ⟨graphState tightPublicJC, tightenTarget tightPublicJC, quarantineKey, pA,
        tighten_public_justified_to_contested⟩
  | .justifiedGap =>
      ⟨graphState tightJG, tightenTarget tightJG, quarantineKey, pA,
        tighten_public_justified_to_gap⟩
  | .justifiedBlocked =>
      ⟨graphState tightJD, tightenTarget tightJD, quarantineKey, pA,
        tighten_public_justified_to_evidenceBlocked⟩
  | .defeatedDefeated =>
      ⟨graphState tightDD, tightenTarget tightDD, quarantineKey, pA,
        tighten_public_defeated_to_defeated⟩
  | .defeatedGap =>
      ⟨graphState tightDG, tightenTarget tightDG, quarantineKey, pA,
        tighten_public_defeated_to_gap⟩
  | .defeatedBlocked =>
      ⟨graphState tightDJ, tightenTarget tightDJ, quarantineKey, pA,
        tighten_public_defeated_to_evidenceBlocked⟩
  | .contestedDefeated =>
      ⟨graphState tightPublicCD, tightenTarget tightPublicCD, quarantineKey, pA,
        tighten_public_contested_to_defeated⟩
  | .contestedContested =>
      ⟨graphState tightCC, tightenTarget tightCC, quarantineKey, pA,
        tighten_public_contested_to_contested⟩
  | .contestedGap =>
      ⟨graphState tightCG, tightenTarget tightCG, quarantineKey, pA,
        tighten_public_contested_to_gap⟩
  | .contestedBlocked =>
      ⟨graphState tightCJ, tightenTarget tightCJ, quarantineKey, pA,
        tighten_public_contested_to_evidenceBlocked⟩
  | .gapGap =>
      ⟨graphState tightGG, tightenTarget tightGG, quarantineKey, pA,
        tighten_public_gap_to_gap⟩

/-- Closed impossible public tighten cells. -/
inductive TightenPublicUnreachableTag :
    PublicationStatus → Lara.Update.PublicReport → Type
  | defeatedJustified :
      TightenPublicUnreachableTag .refuted .justified
  | defeatedContested :
      TightenPublicUnreachableTag .refuted .contested
  | contestedJustified :
      TightenPublicUnreachableTag .both .justified
  | gapEscape {target} (different : target ≠ .gap) :
      TightenPublicUnreachableTag .gap target

/-- Constructor-local metatheory premises for an impossible public cell. -/
def TightenPublicUnreachableClaim
    (_tag : TightenPublicUnreachableTag source target) : Prop :=
  ∀ run : TightenPublicRun source target,
    Lara.Update.NonInstanceUpdate id run.sourceState (.tighten run.key) → False

/-- Every public impossible tag is ruled out on the exact accepted runs carried
by the matrix domain. -/
theorem TightenPublicUnreachableTag.sound :
    (tag : TightenPublicUnreachableTag source target) →
      TightenPublicUnreachableClaim tag
  | .defeatedJustified => by
      intro run hnon
      have htarget :
          Lara.Update.publicReport run.targetRun run.p =
            .justified := by
        have h := congrArg Prod.snd run.transition
        change Lara.Update.publicReport run.targetRun run.p =
          .justified at h
        exact h
      have hsource :=
        Lara.Update.tighten_public_justified_source_justified
          run.sourceRun run.targetRun run.apply_ok
          hnon run.clean run.p htarget
      rw [run.sourceCore] at hsource
      contradiction
  | .defeatedContested => by
      intro run hnon
      exact Lara.Update.tighten_public_defeated_not_contested
        run.sourceRun run.targetRun run.apply_ok
        hnon run.clean run.p (by
          simpa [PublicationStatus.grounded,
            Lara.Update.PublicReport.ofStatus] using run.transition)
  | .contestedJustified => by
      intro run hnon
      have htarget :
          Lara.Update.publicReport run.targetRun run.p =
            .justified := by
        have h := congrArg Prod.snd run.transition
        change Lara.Update.publicReport run.targetRun run.p =
          .justified at h
        exact h
      have hsource :=
        Lara.Update.tighten_public_justified_source_justified
          run.sourceRun run.targetRun run.apply_ok
          hnon run.clean run.p htarget
      rw [run.sourceCore] at hsource
      contradiction
  | .gapEscape different => by
      intro run hnon
      have hsource :
          Lara.Update.publicReport run.sourceRun run.p = .gap := by
        have h := congrArg Prod.fst run.transition
        change Lara.Update.publicReport run.sourceRun run.p =
          .gap at h
        exact h
      have hgap := Lara.Update.tighten_public_gap_fixed
        run.sourceRun run.targetRun run.apply_ok
        hnon run.clean run.p hsource
      have htarget :
          Lara.Update.publicReport run.targetRun run.p = target := by
        have h := congrArg Prod.snd run.transition
        change Lara.Update.publicReport run.targetRun run.p =
          target at h
        exact h
      exact different (htarget.symm.trans hgap)

/-- One canonical source-to-five-valued-target public matrix coordinate. -/
structure PublicMatrixCoordinate where
  source : PublicationStatus
  target : Lara.Update.PublicReport
deriving DecidableEq, Repr

/-- Canonical row-major four-by-five public coordinates, shared by tighten and
all three additive inventories. -/
def canonicalPublicCoordinates : List PublicMatrixCoordinate :=
  publicationStatuses.flatMap fun source =>
    publicReports.map fun target => ⟨source, target⟩

theorem canonicalPublicCoordinates_nodup :
    canonicalPublicCoordinates.Nodup := by decide

theorem canonicalPublicCoordinates_length :
    canonicalPublicCoordinates.length = 20 := by decide

theorem canonicalPublicCoordinates_order :
    canonicalPublicCoordinates =
      [ ⟨.justified, .justified⟩, ⟨.justified, .defeated⟩,
        ⟨.justified, .contested⟩, ⟨.justified, .gap⟩,
        ⟨.justified, .evidenceBlocked⟩,
        ⟨.refuted, .justified⟩, ⟨.refuted, .defeated⟩,
        ⟨.refuted, .contested⟩, ⟨.refuted, .gap⟩,
        ⟨.refuted, .evidenceBlocked⟩,
        ⟨.both, .justified⟩, ⟨.both, .defeated⟩,
        ⟨.both, .contested⟩, ⟨.both, .gap⟩,
        ⟨.both, .evidenceBlocked⟩,
        ⟨.gap, .justified⟩, ⟨.gap, .defeated⟩,
        ⟨.gap, .contested⟩, ⟨.gap, .gap⟩,
        ⟨.gap, .evidenceBlocked⟩ ] := by decide

/-- Closed theorem evidence for one public tighten cell. -/
inductive TightenPublicCellEvidence :
    PublicationStatus → Lara.Update.PublicReport → Type
  | reachable (tag : TightenPublicReachableTag source target) :
      TightenPublicCellEvidence source target
  | unreachable (tag : TightenPublicUnreachableTag source target) :
      TightenPublicCellEvidence source target

def TightenPublicCellEvidence.Claim :
    TightenPublicCellEvidence source target → Prop
  | .reachable _ => TightenPublicReachableClaim source target
  | .unreachable tag => TightenPublicUnreachableClaim tag

theorem TightenPublicCellEvidence.sound
    (evidence : TightenPublicCellEvidence source target) :
    evidence.Claim := by
  cases evidence with
  | reachable tag => exact tag.sound
  | unreachable tag => exact tag.sound

private def TightenPublicReachableTag.theoremName :
    TightenPublicReachableTag source target → String
  | .justifiedJustified => "tighten_public_justified_to_justified"
  | .justifiedDefeated => "tighten_public_justified_to_defeated"
  | .justifiedContested => "tighten_public_justified_to_contested"
  | .justifiedGap => "tighten_public_justified_to_gap"
  | .justifiedBlocked => "tighten_public_justified_to_evidenceBlocked"
  | .defeatedDefeated => "tighten_public_defeated_to_defeated"
  | .defeatedGap => "tighten_public_defeated_to_gap"
  | .defeatedBlocked => "tighten_public_defeated_to_evidenceBlocked"
  | .contestedDefeated => "tighten_public_contested_to_defeated"
  | .contestedContested => "tighten_public_contested_to_contested"
  | .contestedGap => "tighten_public_contested_to_gap"
  | .contestedBlocked => "tighten_public_contested_to_evidenceBlocked"
  | .gapGap => "tighten_public_gap_to_gap"

private def TightenPublicUnreachableTag.theoremName :
    TightenPublicUnreachableTag source target → String
  | .defeatedJustified => "tighten_public_justified_source_justified"
  | .defeatedContested => "tighten_public_defeated_not_contested"
  | .contestedJustified => "tighten_public_justified_source_justified"
  | .gapEscape _ => "tighten_public_gap_fixed"

private def TightenPublicCellEvidence.reachableB :
    TightenPublicCellEvidence source target → Bool
  | .reachable _ => true
  | .unreachable _ => false

private def TightenPublicCellEvidence.theoremName :
    TightenPublicCellEvidence source target → String
  | .reachable tag => tag.theoremName
  | .unreachable tag => tag.theoremName

/-- Total typed classification of every public tighten coordinate. -/
def tightenPublicEvidenceFor
    (source : PublicationStatus) (target : Lara.Update.PublicReport) :
    TightenPublicCellEvidence source target :=
  match source, target with
  | .justified, .justified => .reachable .justifiedJustified
  | .justified, .defeated => .reachable .justifiedDefeated
  | .justified, .contested => .reachable .justifiedContested
  | .justified, .gap => .reachable .justifiedGap
  | .justified, .evidenceBlocked => .reachable .justifiedBlocked
  | .refuted, .justified => .unreachable .defeatedJustified
  | .refuted, .defeated => .reachable .defeatedDefeated
  | .refuted, .contested => .unreachable .defeatedContested
  | .refuted, .gap => .reachable .defeatedGap
  | .refuted, .evidenceBlocked => .reachable .defeatedBlocked
  | .both, .justified => .unreachable .contestedJustified
  | .both, .defeated => .reachable .contestedDefeated
  | .both, .contested => .reachable .contestedContested
  | .both, .gap => .reachable .contestedGap
  | .both, .evidenceBlocked => .reachable .contestedBlocked
  | .gap, .justified => .unreachable (.gapEscape (by decide))
  | .gap, .defeated => .unreachable (.gapEscape (by decide))
  | .gap, .contested => .unreachable (.gapEscape (by decide))
  | .gap, .gap => .reachable .gapGap
  | .gap, .evidenceBlocked => .unreachable (.gapEscape (by decide))

/-- One typed entry in the complete public tighten matrix. -/
structure TightenPublicCellEntry where
  coordinate : PublicMatrixCoordinate
  evidence : TightenPublicCellEvidence coordinate.source coordinate.target

/-- Complete public tighten matrix in canonical row-major order. -/
def tightenPublicMatrix : List TightenPublicCellEntry :=
  canonicalPublicCoordinates.map fun coordinate =>
    { coordinate
    , evidence := tightenPublicEvidenceFor coordinate.source coordinate.target }

theorem tightenPublicMatrix_coordinates :
    tightenPublicMatrix.map (·.coordinate) =
      canonicalPublicCoordinates := by
  change (canonicalPublicCoordinates.map fun coordinate => coordinate) =
    canonicalPublicCoordinates
  simp

private def tightenPublicReachableCount : Nat :=
  (tightenPublicMatrix.filter fun entry => entry.evidence.reachableB).length

/-- The public tighten matrix has thirteen reachable cells out of twenty. -/
theorem tighten_public_reachable_count :
    tightenPublicReachableCount = 13 := by decide
private def tightenPublicBlockedReachableCount : Nat :=
  (tightenPublicMatrix.filter fun entry =>
    entry.evidence.reachableB &&
      decide (entry.coordinate.target = .evidenceBlocked)).length


theorem tighten_public_blocked_reachable_count :
    tightenPublicBlockedReachableCount = 3 := by decide

/-! ### Typed five-valued additive public matrices -/

/-- The three constructors covered by clean-base additive equality. -/
inductive AdditiveKind where
  | addLeaf
  | addAttack
  | addInstance
deriving DecidableEq, Repr

def AdditiveKind.updateKind : AdditiveKind → UpdateKind
  | .addLeaf => .addLeaf
  | .addAttack => .addAttack
  | .addInstance => .addInstance

def AdditiveKind.label : AdditiveKind → String
  | .addLeaf => "addLeaf"
  | .addAttack => "addAttack"
  | .addInstance => "addInstance"

/-- Exact accepted/core data for one non-blocked additive public coordinate. -/
inductive AdditivePublicRun :
    AdditiveKind → PublicationStatus → PublicationStatus → Type
  | addLeaf (sourceState targetState : Lara.Update.SourceState) (p : Atom)
      (leafId : LeafId) (a : Atom) (m : Admission.LeafMeta)
      (sourceRun : AcceptedRun sourceState)
      (targetRun : AcceptedRun targetState)
      (apply_ok : Lara.Update.applyUpdate registryEx sourceState
        (.addLeaf leafId a m) = .ok targetState)
      (additive : Lara.Update.AdditiveUpdate sourceState
        (.addLeaf leafId a m))
      (clean : Lara.Update.CleanBase sourceRun)
      (coreTransition : Lara.Update.CoreTransition Semantics.groundedSem
        sourceRun.checked targetRun.checked p =
          (.observed source.grounded, .observed target.grounded)) :
      AdditivePublicRun .addLeaf source target
  | addAttack (sourceState targetState : Lara.Update.SourceState) (p : Atom)
      (raw : RawAttack.RawAttack)
      (sourceRun : AcceptedRun sourceState)
      (targetRun : AcceptedRun targetState)
      (apply_ok : Lara.Update.applyUpdate registryEx sourceState
        (.addAttack raw) = .ok targetState)
      (additive : Lara.Update.AdditiveUpdate sourceState (.addAttack raw))
      (clean : Lara.Update.CleanBase sourceRun)
      (coreTransition : Lara.Update.CoreTransition Semantics.groundedSem
        sourceRun.checked targetRun.checked p =
          (.observed source.grounded, .observed target.grounded)) :
      AdditivePublicRun .addAttack source target
  | addInstance (sourceState targetState : Lara.Update.SourceState) (p : Atom)
      (name : String) (w : SupportTerm)
      (sourceRun : AcceptedRun sourceState)
      (targetRun : AcceptedRun targetState)
      (apply_ok : Lara.Update.applyUpdate registryEx sourceState
        (.addInstance name w) = .ok targetState)
      (additive : Lara.Update.AdditiveUpdate sourceState (.addInstance name w))
      (clean : Lara.Update.CleanBase sourceRun)
      (coreTransition : Lara.Update.CoreTransition Semantics.groundedSem
        sourceRun.checked targetRun.checked p =
          (.observed source.grounded, .observed target.grounded)) :
      AdditivePublicRun .addInstance source target

def AdditivePublicRun.toCore :
    AdditivePublicRun kind source target →
      MatrixRun kind.updateKind source target
  | .addLeaf sourceState targetState p leafId a m sourceRun targetRun apply_ok
      _ _ coreTransition =>
      .addLeaf sourceState targetState p leafId a m sourceRun targetRun apply_ok
        coreTransition
  | .addAttack sourceState targetState p raw sourceRun targetRun apply_ok _ _
      coreTransition =>
      .addAttack sourceState targetState p raw sourceRun targetRun apply_ok
        coreTransition
  | .addInstance sourceState targetState p name w sourceRun targetRun apply_ok
      _ _ coreTransition =>
      .addInstance sourceState targetState p name w sourceRun targetRun apply_ok
        coreTransition

private theorem additivePublicTransitionOfCore
    {sourceState targetState : Lara.Update.SourceState}
    {update : Lara.Update.SourceUpdate} {p : Atom}
    {source target : PublicationStatus}
    (sourceRun : AcceptedRun sourceState) (targetRun : AcceptedRun targetState)
    (happly : Lara.Update.applyUpdate registryEx sourceState update =
      .ok targetState)
    (hadditive : Lara.Update.AdditiveUpdate sourceState update)
    (hclean : Lara.Update.CleanBase sourceRun)
    (hcore : Lara.Update.CoreTransition Semantics.groundedSem
      sourceRun.checked targetRun.checked p =
        (.observed source.grounded, .observed target.grounded)) :
    Lara.Update.PublicTransition sourceRun targetRun p =
      (Lara.Update.PublicReport.ofStatus source.grounded,
        Lara.Update.PublicReport.ofStatus target.grounded) := by
  have hsourceNodup :
      (Compile.checkedAF sourceRun.checked.program).args.Nodup := by
    change (List.range sourceRun.checked.program.args.length).Nodup
    exact List.nodup_range
  have htargetNodup :
      (Compile.checkedAF targetRun.checked.program).args.Nodup := by
    change (List.range targetRun.checked.program.args.length).Nodup
    exact List.nodup_range
  have hsourceCore :
      Grounded.statusC (Compile.checkedAF sourceRun.checked.program)
          (Consistency.completeClaimFor sourceRun.checked p) =
        source.grounded := by
    have h := congrArg Prod.fst hcore
    change Semantics.observe Semantics.groundedSem
      (Compile.checkedAF sourceRun.checked.program)
      (Consistency.completeClaimFor sourceRun.checked p) =
        .observed source.grounded at h
    rw [Semantics.observe_grounded hsourceNodup] at h
    exact Semantics.ClaimObservation.observed.inj h
  have htargetCore :
      Grounded.statusC (Compile.checkedAF targetRun.checked.program)
          (Consistency.completeClaimFor targetRun.checked p) =
        target.grounded := by
    have h := congrArg Prod.snd hcore
    change Semantics.observe Semantics.groundedSem
      (Compile.checkedAF targetRun.checked.program)
      (Consistency.completeClaimFor targetRun.checked p) =
        .observed target.grounded at h
    rw [Semantics.observe_grounded htargetNodup] at h
    exact Semantics.ClaimObservation.observed.inj h
  have hsourceCore' :
      Grounded.statusC (Compile.checkedAF sourceRun.checked.program)
          (Consistency.completeClaimFor sourceRun.checked p) =
        source.grounded := by
    simpa [AcceptedRun] using hsourceCore
  have htargetCore' :
      Grounded.statusC (Compile.checkedAF targetRun.checked.program)
          (Consistency.completeClaimFor targetRun.checked p) =
        target.grounded := by
    simpa [AcceptedRun] using htargetCore
  apply Prod.ext
  · change Lara.Update.publicReport sourceRun p =
      Lara.Update.PublicReport.ofStatus source.grounded
    rw [Lara.Update.publicReport_eq_core_of_clean sourceRun hclean p,
      hsourceCore']
  · change Lara.Update.publicReport targetRun p =
      Lara.Update.PublicReport.ofStatus target.grounded
    rw [Lara.Update.additive_public_eq_core sourceRun
      targetRun happly hadditive hclean p, htargetCore']

/-- Every non-blocked additive run publishes exactly its typed grounded core
coordinate; this is the matrix bridge to `additive_public_eq_core`. -/
theorem AdditivePublicRun.publicTransition
    (run : AdditivePublicRun kind source target) :
    ∃ (sourceState targetState : Lara.Update.SourceState)
        (sourceRun : AcceptedRun sourceState)
        (targetRun : AcceptedRun targetState) (p : Atom),
      Lara.Update.PublicTransition sourceRun targetRun p =
        (Lara.Update.PublicReport.ofStatus source.grounded,
          Lara.Update.PublicReport.ofStatus target.grounded) := by
  cases run with
  | addLeaf sourceState targetState p leafId a m sourceRun targetRun apply_ok
      additive clean coreTransition =>
      exact ⟨sourceState, targetState, sourceRun, targetRun, p,
        additivePublicTransitionOfCore sourceRun targetRun apply_ok additive clean
          coreTransition⟩
  | addAttack sourceState targetState p raw sourceRun targetRun apply_ok
      additive clean coreTransition =>
      exact ⟨sourceState, targetState, sourceRun, targetRun, p,
        additivePublicTransitionOfCore sourceRun targetRun apply_ok additive clean
          coreTransition⟩
  | addInstance sourceState targetState p name w sourceRun targetRun apply_ok
      additive clean coreTransition =>
      exact ⟨sourceState, targetState, sourceRun, targetRun, p,
        additivePublicTransitionOfCore sourceRun targetRun apply_ok additive clean
          coreTransition⟩

private theorem graphState_clean_of_no_removed
    (spec : GraphSpec) (hremoved : spec.removed = [])
    (run : AcceptedRun (graphState spec)) :
    Lara.Update.CleanBase run := by
  unfold Lara.Update.CleanBase
  change run.admission.prune.removedSeed = []
  rw [run.prune_eq]
  simp [graphState, Admission.buildPrune, hremoved, graphMetas,
    Admission.policyQuarantineSeed, Admission.decisionFor,
    Groups.quarantined]

def AdditivePublicReachableClaim
    (kind : AdditiveKind) (source target : PublicationStatus) : Prop :=
  Nonempty (AdditivePublicRun kind source target)

private theorem additivePublicRunOfCoreCell
    {kind : AdditiveKind} {source target : PublicationStatus}
    {spec : GraphSpec} {targetState : Lara.Update.SourceState}
    {update : Lara.Update.SourceUpdate} {p : Atom}
    (hkind : UpdateOfKind kind.updateKind update)
    (cell : SuccessfulCoreCell Semantics.groundedSem (graphState spec)
      targetState update p source.grounded target.grounded)
    (hremoved : spec.removed = [])
    (hadditive : Lara.Update.AdditiveUpdate (graphState spec) update) :
    AdditivePublicReachableClaim kind source target := by
  obtain ⟨sourceRun, targetRun, happly, hcore⟩ := cell
  have hclean := graphState_clean_of_no_removed spec hremoved sourceRun
  cases kind with
  | addLeaf =>
      cases hkind with
      | addLeaf =>
          exact ⟨.addLeaf _ _ p _ _ _ sourceRun targetRun happly hadditive
            hclean hcore⟩
  | addAttack =>
      cases hkind with
      | addAttack =>
          exact ⟨.addAttack _ _ p _ sourceRun targetRun happly hadditive
            hclean hcore⟩
  | addInstance =>
      cases hkind with
      | addInstance =>
          exact ⟨.addInstance _ _ p _ _ sourceRun targetRun happly hadditive
            hclean hcore⟩

/-- Every additive reachable core tag lifts to a real clean-base public run. -/
theorem ReachableTag.additivePublicSound
    (tag : ReachableTag kind.updateKind source target) :
    AdditivePublicReachableClaim kind source target := by
  cases kind with
  | addLeaf =>
      cases tag with
      | addLeafJJ =>
          exact additivePublicRunOfCoreCell .addLeaf
            addLeaf_justified_to_justified (by rfl)
            (.addLeaf lh4 h4 addLeafMeta (by
              simp [Lara.Update.AddLeafFresh, graphState, graphLeaves,
                graphMetas] <;> decide) (by rfl))
      | addLeafDD =>
          exact additivePublicRunOfCoreCell .addLeaf
            addLeaf_refuted_to_refuted (by rfl)
            (.addLeaf lh4 h4 addLeafMeta (by
              simp [Lara.Update.AddLeafFresh, graphState, graphLeaves,
                graphMetas] <;> decide) (by rfl))
      | addLeafCC =>
          exact additivePublicRunOfCoreCell .addLeaf
            addLeaf_both_to_both (by rfl)
            (.addLeaf lh4 h4 addLeafMeta (by
              simp [Lara.Update.AddLeafFresh, graphState, graphLeaves,
                graphMetas] <;> decide) (by rfl))
      | addLeafGG =>
          exact additivePublicRunOfCoreCell .addLeaf
            addLeaf_gap_to_gap (by rfl)
            (.addLeaf lh4 h4 addLeafMeta (by
              simp [Lara.Update.AddLeafFresh, graphState, graphLeaves,
                graphMetas] <;> decide) (by rfl))
  | addAttack =>
      cases tag with
      | addAttackJJ =>
          exact additivePublicRunOfCoreCell .addAttack
            addAttack_justified_to_justified (by rfl) (.addAttack _)
      | addAttackJD =>
          exact additivePublicRunOfCoreCell .addAttack
            addAttack_justified_to_refuted (by rfl) (.addAttack _)
      | addAttackJC =>
          exact additivePublicRunOfCoreCell .addAttack
            addAttack_justified_to_both (by rfl) (.addAttack _)
      | addAttackDJ =>
          exact additivePublicRunOfCoreCell .addAttack
            addAttack_refuted_to_justified (by rfl) (.addAttack _)
      | addAttackDD =>
          exact additivePublicRunOfCoreCell .addAttack
            addAttack_refuted_to_refuted (by rfl) (.addAttack _)
      | addAttackDC =>
          exact additivePublicRunOfCoreCell .addAttack
            addAttack_refuted_to_both (by rfl) (.addAttack _)
      | addAttackCJ =>
          exact additivePublicRunOfCoreCell .addAttack
            addAttack_both_to_justified (by rfl) (.addAttack _)
      | addAttackCD =>
          exact additivePublicRunOfCoreCell .addAttack
            addAttack_both_to_refuted (by rfl) (.addAttack _)
      | addAttackCC =>
          exact additivePublicRunOfCoreCell .addAttack
            addAttack_both_to_both (by rfl) (.addAttack _)
      | addAttackGG =>
          exact additivePublicRunOfCoreCell .addAttack
            addAttack_gap_to_gap (by rfl) (.addAttack _)
  | addInstance =>
      cases tag with
      | addInstanceJJ =>
          exact additivePublicRunOfCoreCell .addInstance
            addInstance_justified_to_justified (by rfl) (.addInstance _ _)
      | addInstanceDJ =>
          exact additivePublicRunOfCoreCell .addInstance
            addInstance_refuted_to_justified (by rfl) (.addInstance _ _)
      | addInstanceDD =>
          exact additivePublicRunOfCoreCell .addInstance
            addInstance_refuted_to_refuted (by rfl) (.addInstance _ _)
      | addInstanceDC =>
          exact additivePublicRunOfCoreCell .addInstance
            addInstance_refuted_to_both (by rfl) (.addInstance _ _)
      | addInstanceCJ =>
          exact additivePublicRunOfCoreCell .addInstance
            addInstance_both_to_justified (by rfl) (.addInstance _ _)
      | addInstanceCC =>
          exact additivePublicRunOfCoreCell .addInstance
            addInstance_both_to_both (by rfl) (.addInstance _ _)
      | addInstanceGJ =>
          exact additivePublicRunOfCoreCell .addInstance
            addInstance_gap_to_justified (by rfl) (.addInstance _ _)
      | addInstanceGD =>
          exact additivePublicRunOfCoreCell .addInstance
            addInstance_gap_to_refuted (by rfl) (.addInstance _ _)
      | addInstanceGC =>

          exact additivePublicRunOfCoreCell .addInstance
            addInstance_gap_to_both (by rfl) (.addInstance _ _)
      | addInstanceGG =>
          exact additivePublicRunOfCoreCell .addInstance
            addInstance_gap_to_gap (by rfl) (.addInstance _ _)

/-- Exact clean additive data for a purported blocked public target. -/
structure AdditiveBlockedRun (kind : AdditiveKind)
    (source : PublicationStatus) where
  sourceState : Lara.Update.SourceState
  targetState : Lara.Update.SourceState
  update : Lara.Update.SourceUpdate
  p : Atom
  sourceRun : AcceptedRun sourceState
  targetRun : AcceptedRun targetState
  updateKind : UpdateOfKind kind.updateKind update
  apply_ok : Lara.Update.applyUpdate registryEx sourceState update =
    .ok targetState
  additive : Lara.Update.AdditiveUpdate sourceState update
  clean : Lara.Update.CleanBase sourceRun
  sourceCore :
    Grounded.statusC (Compile.checkedAF sourceRun.checked.program)
      (Consistency.completeClaimFor sourceRun.checked p) = source.grounded
  targetBlocked :
    Lara.Update.publicReport targetRun p = .evidenceBlocked

theorem AdditiveBlockedRun.emptyClosure
    (run : AdditiveBlockedRun kind source) :
    Lara.Update.blockedSetForRun run.targetRun = [] :=
  Lara.Update.additive_target_blockedSet_eq_nil run.sourceRun
    run.targetRun run.apply_ok run.additive run.clean

/-- The blocked public column is impossible for every exact clean additive run. -/
theorem AdditiveBlockedRun.false
    (run : AdditiveBlockedRun kind source) : False := by
  exact (Lara.Update.additive_public_ne_evidenceBlocked
    run.sourceRun run.targetRun run.apply_ok
    run.additive run.clean run.p) run.targetBlocked

/-- Typed evidence for every additive four-by-five public coordinate. -/
inductive AdditivePublicCellEvidence
    (kind : AdditiveKind) :
    PublicationStatus → Lara.Update.PublicReport → Type
  | reachable (coreTarget : PublicationStatus)
      (tag : ReachableTag kind.updateKind source coreTarget) :
      AdditivePublicCellEvidence kind source
        (Lara.Update.PublicReport.ofStatus coreTarget.grounded)
  | coreImpossible (coreTarget : PublicationStatus)
      (tag : UnreachableTag kind.updateKind source coreTarget) :
      AdditivePublicCellEvidence kind source
        (Lara.Update.PublicReport.ofStatus coreTarget.grounded)
  | blockedImpossible :
      AdditivePublicCellEvidence kind source .evidenceBlocked

def AdditivePublicCellEvidence.Claim :
    AdditivePublicCellEvidence kind source target → Prop
  | .reachable coreTarget _ =>
      AdditivePublicReachableClaim kind source coreTarget
  | .coreImpossible coreTarget tag =>
      ∀ run : AdditivePublicRun kind source coreTarget,
        UnreachablePremises tag run.toCore → False
  | .blockedImpossible =>
      ∀ _run : AdditiveBlockedRun kind source, False

theorem AdditivePublicCellEvidence.sound
    (evidence : AdditivePublicCellEvidence kind source target) :
    evidence.Claim := by
  cases evidence with
  | reachable _ tag => exact tag.additivePublicSound
  | coreImpossible _ tag =>
      intro run premises
      exact tag.sound run.toCore premises
  | blockedImpossible =>
      intro run
      exact run.false

private def liftCorePublicEvidence
    (kind : AdditiveKind) (source target : PublicationStatus) :
    CellEvidence kind.updateKind source target →
      AdditivePublicCellEvidence kind source
        (Lara.Update.PublicReport.ofStatus target.grounded)
  | .reachable tag => .reachable target tag
  | .unreachable tag => .coreImpossible target tag

/-- Total theorem evidence for one additive public coordinate. -/
def additivePublicEvidenceFor
    (kind : AdditiveKind) (source : PublicationStatus)
    (target : Lara.Update.PublicReport) :
    AdditivePublicCellEvidence kind source target :=
  match target with
  | .justified =>
      liftCorePublicEvidence kind source .justified
        (evidenceFor kind.updateKind source .justified)
  | .defeated =>
      liftCorePublicEvidence kind source .refuted
        (evidenceFor kind.updateKind source .refuted)
  | .contested =>
      liftCorePublicEvidence kind source .both
        (evidenceFor kind.updateKind source .both)
  | .gap =>
      liftCorePublicEvidence kind source .gap
        (evidenceFor kind.updateKind source .gap)
  | .evidenceBlocked => .blockedImpossible

/-- One typed entry in a complete additive public matrix. -/
structure AdditivePublicCellEntry (kind : AdditiveKind) where
  coordinate : PublicMatrixCoordinate
  evidence :
    AdditivePublicCellEvidence kind coordinate.source coordinate.target

private def additivePublicMatrixFor
    (kind : AdditiveKind) : List (AdditivePublicCellEntry kind) :=
  canonicalPublicCoordinates.map fun coordinate =>
    { coordinate
    , evidence :=
        additivePublicEvidenceFor kind coordinate.source coordinate.target }

def addLeafPublicMatrix : List (AdditivePublicCellEntry .addLeaf) :=
  additivePublicMatrixFor .addLeaf

def addAttackPublicMatrix : List (AdditivePublicCellEntry .addAttack) :=
  additivePublicMatrixFor .addAttack

def addInstancePublicMatrix : List (AdditivePublicCellEntry .addInstance) :=
  additivePublicMatrixFor .addInstance

private theorem additivePublicMatrixFor_coordinates (kind : AdditiveKind) :
    (additivePublicMatrixFor kind).map (·.coordinate) =
      canonicalPublicCoordinates := by
  change (canonicalPublicCoordinates.map fun coordinate => coordinate) =
    canonicalPublicCoordinates
  simp

theorem addLeafPublicMatrix_coordinates :
    addLeafPublicMatrix.map (·.coordinate) = canonicalPublicCoordinates :=
  additivePublicMatrixFor_coordinates .addLeaf

theorem addAttackPublicMatrix_coordinates :
    addAttackPublicMatrix.map (·.coordinate) = canonicalPublicCoordinates :=
  additivePublicMatrixFor_coordinates .addAttack

theorem addInstancePublicMatrix_coordinates :
    addInstancePublicMatrix.map (·.coordinate) = canonicalPublicCoordinates :=
  additivePublicMatrixFor_coordinates .addInstance

theorem addLeafPublicMatrix_length : addLeafPublicMatrix.length = 20 := by
  rw [← canonicalPublicCoordinates_length,
    ← List.length_map, addLeafPublicMatrix_coordinates]

theorem addAttackPublicMatrix_length : addAttackPublicMatrix.length = 20 := by
  rw [← canonicalPublicCoordinates_length,
    ← List.length_map, addAttackPublicMatrix_coordinates]

theorem addInstancePublicMatrix_length :
    addInstancePublicMatrix.length = 20 := by
  rw [← canonicalPublicCoordinates_length,
    ← List.length_map, addInstancePublicMatrix_coordinates]


private def AdditivePublicCellEvidence.reachableB :
    AdditivePublicCellEvidence kind source target → Bool
  | .reachable _ _ => true
  | .coreImpossible _ _ => false
  | .blockedImpossible => false

private def additivePublicReachableCount
    (entries : List (AdditivePublicCellEntry kind)) : Nat :=
  (entries.filter fun entry => entry.evidence.reachableB).length

private def additivePublicBlockedReachableCount
    (entries : List (AdditivePublicCellEntry kind)) : Nat :=
  (entries.filter fun entry =>
    entry.evidence.reachableB &&
      decide (entry.coordinate.target = .evidenceBlocked)).length

theorem addLeaf_public_reachable_count :
    additivePublicReachableCount addLeafPublicMatrix = 4 := by decide

theorem addAttack_public_reachable_count :
    additivePublicReachableCount addAttackPublicMatrix = 10 := by decide

theorem addInstance_public_reachable_count :
    additivePublicReachableCount addInstancePublicMatrix = 10 := by decide

theorem addLeaf_public_blocked_reachable_count :
    additivePublicBlockedReachableCount addLeafPublicMatrix = 0 := by decide

theorem addAttack_public_blocked_reachable_count :
    additivePublicBlockedReachableCount addAttackPublicMatrix = 0 := by decide

theorem addInstance_public_blocked_reachable_count :
    additivePublicBlockedReachableCount addInstancePublicMatrix = 0 := by decide



private def publicEvidenceText
    (evidence : TightenPublicCellEvidence source target) : String :=
  (if evidence.reachableB then "R " else "U ") ++ evidence.theoremName

private def publicTableRows : List (List String) :=
  ("source \\ target" ::
      publicReports.map Lara.Update.PublicReport.publicationLabel) ::
    publicationStatuses.map fun source =>
      source.label :: publicReports.map fun target =>
        publicEvidenceText (tightenPublicEvidenceFor source target)

private def renderPublicRows (rows : List (List String)) : String :=
  let widths := (List.range 6).map (columnWidth rows)
  String.intercalate "\n" <| rows.map fun row =>
    String.intercalate " | " <|
      (List.range 6).map fun column =>
        padRight (widths.getD column 0) (row.getD column "")

private def AdditiveKind.countQualifier : AdditiveKind → String
  | .addLeaf => " (conditional exclusions)"
  | .addAttack => ""
  | .addInstance => ""

private def renderAdditivePublicSummary (kind : AdditiveKind)
    (entries : List (AdditivePublicCellEntry kind)) : String :=
  s!"{kind.label} reachable={additivePublicReachableCount entries}/{entries.length}{kind.countQualifier}; " ++
    s!"evidenceBlocked={additivePublicBlockedReachableCount entries}"

/-- Deterministic theorem-backed five-valued public matrix report.  Additive
rows have the grounded counts because `additive_public_eq_core` rules out their
blocked column under `CleanBase`; tighten is the only row with blocked cells. -/
def fiveValuedPublicMatrixReport : String :=
  "additive public rows under CleanBase (via additive_public_eq_core)\n" ++
  String.intercalate "; "
    [ renderAdditivePublicSummary .addLeaf addLeafPublicMatrix,
      renderAdditivePublicSummary .addAttack addAttackPublicMatrix,
      renderAdditivePublicSummary .addInstance addInstancePublicMatrix ] ++
  "\naddLeaf conditional exclusions require AddLeafFresh and admission of the new metadata key.\n\n" ++
  s!"tighten five-valued public matrix under CleanBase\nreachable={tightenPublicReachableCount}/{tightenPublicMatrix.length}; " ++
  s!"evidenceBlocked={tightenPublicBlockedReachableCount}\n" ++
  renderPublicRows publicTableRows

