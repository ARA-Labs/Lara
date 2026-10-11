import Lara.Process.SourceProvenance

set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

namespace Lara.Examples.ProcessSourceProvenance

open Lara.Process Lara.Process.Source

def leafId : Presentation.LeafId := ⟨"l-cell"⟩
def cellPattern : Presentation.AtomPat := ⟨"cell", .nil⟩
def leaf : Presentation.Leaf :=
  ⟨leafId, .atom "cell" .nil, .observed, .user, [], none⟩

def middle : Presentation.AtomPat := ⟨"middle", .nil⟩
def last : Presentation.AtomPat := ⟨"last", .nil⟩

def rule (name : String) (premise conclusion : Presentation.AtomPat) : Presentation.Rule :=
  { id := ⟨name⟩, params := [], mode := .strict, premises := [premise]
    premiseLabels := [], conclusion, allowTrusted := true, certifiers := [], questions := [] }

def baseRule := rule "base-rule" cellPattern cellPattern
def introducedRule := rule "introduced-rule" cellPattern middle
def nextRule := rule "next-rule" middle last
def transitiveRule := rule "transitive-rule" last last
def implicitRule := rule "implicit-rule" middle last
def nestedRule := rule "nested-rule" last last

def dischargeRule : Presentation.Rule :=
  { rule "discharge-rule" cellPattern last with
    mode := .defeasible
    allowTrusted := false
    questions := [⟨⟨"required"⟩, last, .mandatory⟩] }

def namedDischargeRule : Presentation.Rule :=
  { dischargeRule with id := ⟨"named-discharge-rule"⟩ }

def direct (r : Presentation.RuleId) : Presentation.SupportTerm :=
  .rule r [] (.cons (.leaf leafId) .nil) .nil [] .trusted

def argument (name : String) (instantiation : Presentation.ArgInstantiation) : Presentation.Decl :=
  .arg ⟨⟨name⟩, .supportsDerived ⟨name ++ "-claim"⟩, instantiation⟩

def surface : Surface.Input :=
  { policy :=
      { id := ⟨"provenance-policy"⟩
        sigma := ⟨[], [], [⟨⟨"cell"⟩, []⟩, ⟨⟨"middle"⟩, []⟩, ⟨⟨"last"⟩, []⟩]⟩
        rules := [baseRule, introducedRule, nextRule, transitiveRule, dischargeRule,
          namedDischargeRule, implicitRule, nestedRule]
        contraries := [], exceptions := [], admission := [((.observed, .user), .admit)]
        theories := [], groupMode := .quarantineOnConflict, measurands := [], comparisonSchemes := [] }
    program :=
      { artifact := "source-provenance", digest := ⟨"sha256:source-provenance"⟩
        policy := ⟨"provenance-policy"⟩, backends := [], valueBindings := []
        decls := [.leaf leaf,
          argument "independent" (.explicitTheta (direct baseRule.id)),
          argument "introduced" (.explicitTheta (direct introducedRule.id)),
          argument "dependent" (.inferTheta nextRule.id [⟨"introduced"⟩] [] [] .trusted),
          argument "transitive" (.inferTheta transitiveRule.id [⟨"dependent"⟩] [] [] .trusted),
          argument "discharged" (.explicitTheta (.rule dischargeRule.id []
            (.cons (.leaf leafId) .nil)
            (.cons ⟨"required"⟩ (.leaf ⟨"transitive"⟩) .nil) [] .none)),
          argument "named-discharge" (.inferTheta namedDischargeRule.id [⟨leafId.val⟩]
            [(⟨"required"⟩, ⟨"transitive"⟩)] [] .none),
          argument "implicit" (.explicitTheta (.rule implicitRule.id [] .nil .nil [] .trusted)),
          argument "nested-implicit" (.explicitTheta (.rule nestedRule.id []
            (.cons (.rule nextRule.id [] .nil .nil [] .trusted) .nil) .nil [] .trusted))] } }

def input : SourceInput :=
  { surface
    replay :=
      { core := ⟨Driver.coreVersionText⟩
        policy := surface.policy.id
        backends := []
        theories := []
        artifact := surface.program.digest }
    capture := none }

/-- One production observation supplies every probe; the expected result is
checked once rather than normalizing the dependent source checker per probe. -/
def report : Option (List EvidenceKind) := do
  let observed ← (checkSource input).toOption
  let table ← (Provenance.ofObservation observed).toOption
  [("independent", EvidenceKind.hypothetical), ("dependent", .hypothetical),
    ("transitive", .hypothetical), ("discharged", .hypothetical),
    ("named-discharge", .hypothetical), ("implicit", .hypothetical),
    ("nested-implicit", .hypothetical), ("transitive", .conditional),
    ("independent", .conditional)].mapM fun probe => do
      let used ← (Provenance.lookup table ⟨probe.1⟩).toOption
      return (Provenance.scalar (fun key =>
        (if key = .argument ⟨"introduced"⟩ then probe.2 else .observed, true)) used).1

theorem report_results :
    report = some [.observed, .hypothetical, .hypothetical, .hypothetical,
      .hypothetical, .hypothetical, .hypothetical, .conditional, .observed] := by decide +kernel

theorem source_accepted : (checkSource input).isOk = true := by
  have result := report_results
  cases h : checkSource input with
  | error error => simp [report, h, Except.toOption] at result
  | ok observed => rfl

def checkedNames : Option (List Presentation.ArgId) :=
  (checkSource input).toOption.map (fun observed => Coordinates.names observed.run)

theorem all_arguments_retained :
    checkedNames = some (["independent", "introduced", "dependent", "transitive",
      "discharged", "named-discharge", "implicit", "nested-implicit"].map
        (fun name => Presentation.ArgId.mk name)) := by decide +kernel

def checkedDependent : Option EvidenceKind := do
  let observed ← (checkSource input).toOption
  let table ← (Provenance.ofObservation observed).toOption
  let used ← (Provenance.checkedKeys observed table 2).toOption
  return (Provenance.scalar (fun key =>
    (if key = .argument ⟨"introduced"⟩ then .hypothetical else .observed, true)) used).1

theorem checked_node_dependency_capped : checkedDependent = some .hypothetical := by decide +kernel

def capped (index : Nat) : Option EvidenceKind := report.bind (fun rows => rows[index]?)

theorem direct_reference_capped : capped 1 = some .hypothetical := by
  simp [capped, report_results]

theorem independent_rule_unaffected : capped 0 = some .observed := by
  simp [capped, report_results]

theorem transitive_reference_capped : capped 2 = some .hypothetical := by
  simp [capped, report_results]

theorem explicit_discharge_capped : capped 3 = some .hypothetical := by
  simp [capped, report_results]

theorem inferred_discharge_capped : capped 4 = some .hypothetical := by
  simp [capped, report_results]

theorem implicit_prior_capped : capped 5 = some .hypothetical := by
  simp [capped, report_results]

theorem nested_implicit_prior_capped : capped 6 = some .hypothetical := by
  simp [capped, report_results]

theorem conditional_method_propagated : capped 7 = some .conditional := by
  simp [capped, report_results]

theorem conditional_method_unrelated : capped 8 = some .observed := by
  simp [capped, report_results]

theorem missing_provenance_fails :
    Provenance.lookup [] ⟨"missing"⟩ = .error (.missingArgument ⟨"missing"⟩) := rfl

/-- The earlier introduced argument is exactly the leaf used directly by the
later independent rule. Even prior-only core subterm scans misidentify this dependency. -/
def collisionInput : SourceInput :=
  { input with surface := { surface with program := { surface.program with
      decls := [.leaf leaf,
        argument "collision-introduced" (.explicitTheta (.leaf leafId)),
        argument "collision-independent" (.explicitTheta (direct baseRule.id)),
        argument "collision-dependent"
          (.inferTheta introducedRule.id [⟨"collision-introduced"⟩] [] [] .trusted)] } } }

def collisionCores : Option (Support.SupportTerm × Support.SupportTerm) := do
  let observed ← (checkSource collisionInput).toOption
  let independent ← observed.accepted.audit.declared.pairs[1]?
  let introduced ← observed.accepted.audit.declared.pairs[0]?
  return (independent.core, introduced.core)

theorem collision_exact_shared_subterm :
    collisionCores = some
      (.inst (Surface.toSupportRuleId baseRule.id) []
        [.leaf (Surface.toSupportLeafId leafId)] [] [] .trusted,
       .leaf (Surface.toSupportLeafId leafId)) := by decide +kernel

def collisionCheckedReport : Option (List Presentation.ArgId × List EvidenceKind) := do
  let observed ← (checkSource collisionInput).toOption
  let table ← (Provenance.ofObservation observed).toOption
  let kinds ← [0, 1, 2].mapM fun node => do
    let used ← (Provenance.checkedKeys observed table node).toOption
    return (Provenance.scalar (fun key =>
      (if key = .argument ⟨"collision-introduced"⟩ then .hypothetical else .observed,
        true)) used).1
  return (Coordinates.names observed.run, kinds)

theorem collision_checked_reference_identity :
    collisionCheckedReport = some
      ([⟨"collision-introduced"⟩, ⟨"collision-independent"⟩, ⟨"collision-dependent"⟩],
        [.hypothetical, .observed, .hypothetical]) := by decide +kernel

theorem collision_source_accepted : (checkSource collisionInput).isOk = true := by
  have result := collision_checked_reference_identity
  cases h : checkSource collisionInput with
  | error error => simp [collisionCheckedReport, h, Except.toOption] at result
  | ok observed => rfl

/-- A second named root with the identical core is rejected before it can
become a retained argument; it is not a usable accepted collision fixture. -/
def duplicateRootInput : SourceInput :=
  { collisionInput with surface := { collisionInput.surface with
      program := { collisionInput.surface.program with
        decls := collisionInput.surface.program.decls ++
          [argument "duplicate-root" (.explicitTheta (.leaf leafId))] } } }

def duplicateRootRejection : Option SourceRejection :=
  match checkSource duplicateRootInput with
  | .error error => some error
  | .ok _ => none

theorem identical_roots_rejected :
    duplicateRootRejection =
      some (.source (.core (.program (.duplicateArgument 0 3)))) := by decide +kernel

end Lara.Examples.ProcessSourceProvenance
