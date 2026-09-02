/-
Task-2 restricted-class realization spike.

The closed fixtures below exercise the exact fixed context.  The general raw
constructor records the intended formula gadget with a fixed signature and
policy.  Identity canonicalization and the empty backend registry remain
inputs to checker calls; a raw `Lara.Unit` stores neither.  The mandatory gate
was left inconclusive because the family-wide checker/compile/size proof
described at the end of the spike was not closed; no theorem in this file
claims that it was.
-/

import Lara.Complexity.Gadget

namespace Lara.Examples.Complexity.Realization

open Lara Lara.Support Lara.Attack
open Lara.Complexity

/-! ## Closed checker and compilation fixtures -/

private def pathDLeaf : LeafId := ⟨"path-d"⟩
private def pathBLeaf : LeafId := ⟨"path-b"⟩
private def pathALeaf : LeafId := ⟨"path-a"⟩

private def pathDArg : SupportTerm := .leaf pathDLeaf
private def pathBArg : SupportTerm := .leaf pathBLeaf
private def pathAArg : SupportTerm := .leaf pathALeaf

private def pathEntries : List (LeafId × Lara.Atom) :=
  [(pathDLeaf, dAtom), (pathBLeaf, bAtom 0), (pathALeaf, aAtom 0)]

def pathGamma : LeafId → Option Lara.Atom := lookupLeaf pathEntries

def pathGround : List Lara.Atom := pathEntries.map Prod.snd

/-- The closed raw declaration for the directed path `d -> b(0) -> a(0)`. -/
def pathRawUnit : Lara.Unit :=
  { sigma := m2bSigma
    policy := m2bPolicy
    args := [pathDArg, pathBArg, pathAArg]
    atts :=
      [ .undermine pathDArg pathBArg []
      , .undermine pathBArg pathAArg [] ] }

private def pathCheck :=
  Check.Unit.checkUnit pathGamma m2bRegistry pathGround pathRawUnit

private theorem pathCheck_isOk : pathCheck.isOk = true := by decide

/-- Named accepted checker output for the three-node path fixture. -/
def acceptedPathUnit :
    Lara.Unit.CheckedUnit id pathGamma (certOkOf m2bRegistry) :=
  pathCheck.toOption.get (by decide)

/-- The concrete path fixture succeeds through the public unit checker. -/
theorem checkUnit_path_ok :
    Check.Unit.checkUnit pathGamma m2bRegistry pathGround pathRawUnit =
      .ok acceptedPathUnit := by
  cases h : pathCheck with
  | error error =>
      have hs := pathCheck_isOk
      rw [h] at hs
      contradiction
  | ok accepted =>
      have hoption : pathCheck.toOption = some accepted :=
        congrArg Except.toOption h
      have haccepted : acceptedPathUnit = accepted := by
        unfold acceptedPathUnit
        apply Option.get_of_eq_some
        exact hoption
      simpa [pathCheck] using h.trans (congrArg Except.ok haccepted.symm)

private theorem acceptedPath_args :
    acceptedPathUnit.program.args = pathRawUnit.args :=
  (Check.Unit.checkUnit_sound checkUnit_path_ok).2.2.2.2.2.2.2.2.1

private theorem acceptedPath_atts :
    acceptedPathUnit.program.atts = pathRawUnit.atts :=
  (Check.Unit.checkUnit_sound checkUnit_path_ok).2.2.2.2.2.2.2.2.2.1

/-- The hand-written structured carrier for `0 -> 1 -> 2`. -/
def directedPathCarrier : Lara.Invariants.StructuredAF :=
  { nodes := [dAtom, bAtom 0, aAtom 0]
    attack := fun i j => decide ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)) }

private theorem acceptedPath_nodes :
    (Lara.Invariants.compileUnit acceptedPathUnit).nodes =
      directedPathCarrier.nodes := by decide

private theorem acceptedPath_edges (i j : Nat) :
    (Lara.Invariants.compileUnit acceptedPathUnit).attack i j =
      directedPathCarrier.attack i j := by
  change Lara.Compile.edgeB acceptedPathUnit.program i j = _
  unfold Lara.Compile.edgeB
  rw [acceptedPath_args, acceptedPath_atts]
  rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
    simp [pathRawUnit, pathDArg, pathBArg, pathAArg,
      pathDLeaf, pathBLeaf, pathALeaf, directedPathCarrier,
      Lara.Attack.Attack.source, Lara.Compile.coveredB,
      Lara.Compile.attackClosureB, Lara.Compile.containsB,
      Lara.Attack.subterm]

/-- Compilation of the accepted path fixture is exactly the hand-written
three-node path, with the identity all-`Nat` reindexing. -/
def directedPathIso :
    Lara.Realizability.StructuredAFIso
      (Lara.Invariants.compileUnit acceptedPathUnit) directedPathCarrier where
  nodeEquiv := Lara.Realizability.Equiv.refl Nat
  labels := by
    intro i
    rw [acceptedPath_nodes]
    simp [Lara.Realizability.Equiv.refl]
  attacks := by
    intro i j
    simpa [Lara.Realizability.Equiv.refl] using acceptedPath_edges i j

private def cycleNegLeaf : LeafId := ⟨"cycle-neg"⟩
private def cyclePosLeaf : LeafId := ⟨"cycle-pos"⟩
private def cycleNegArg : SupportTerm := .leaf cycleNegLeaf
private def cyclePosArg : SupportTerm := .leaf cyclePosLeaf

private def cycleEntries : List (LeafId × Lara.Atom) :=
  [(cycleNegLeaf, litAtom 0 0), (cyclePosLeaf, litAtom 1 0)]

def cycleGamma : LeafId → Option Lara.Atom := lookupLeaf cycleEntries

def cycleGround : List Lara.Atom := cycleEntries.map Prod.snd

/-- The closed raw declaration for `lit(0,0) <-> lit(1,0)`. -/
def cycleRawUnit : Lara.Unit :=
  { sigma := m2bSigma
    policy := m2bPolicy
    args := [cycleNegArg, cyclePosArg]
    atts :=
      [ .undermine cycleNegArg cyclePosArg []
      , .undermine cyclePosArg cycleNegArg [] ] }

private def cycleCheck :=
  Check.Unit.checkUnit cycleGamma m2bRegistry cycleGround cycleRawUnit

private theorem cycleCheck_isOk : cycleCheck.isOk = true := by decide

/-- Named accepted checker output for the two-cycle fixture. -/
def acceptedCycleUnit :
    Lara.Unit.CheckedUnit id cycleGamma (certOkOf m2bRegistry) :=
  cycleCheck.toOption.get (by decide)

/-- The concrete two-cycle succeeds through the public unit checker. -/
theorem checkUnit_cycle_ok :
    Check.Unit.checkUnit cycleGamma m2bRegistry cycleGround cycleRawUnit =
      .ok acceptedCycleUnit := by
  cases h : cycleCheck with
  | error error =>
      have hs := cycleCheck_isOk
      rw [h] at hs
      contradiction
  | ok accepted =>
      have hoption : cycleCheck.toOption = some accepted :=
        congrArg Except.toOption h
      have haccepted : acceptedCycleUnit = accepted := by
        unfold acceptedCycleUnit
        apply Option.get_of_eq_some
        exact hoption
      simpa [cycleCheck] using h.trans (congrArg Except.ok haccepted.symm)

private theorem acceptedCycle_args :
    acceptedCycleUnit.program.args = cycleRawUnit.args :=
  (Check.Unit.checkUnit_sound checkUnit_cycle_ok).2.2.2.2.2.2.2.2.1

private theorem acceptedCycle_atts :
    acceptedCycleUnit.program.atts = cycleRawUnit.atts :=
  (Check.Unit.checkUnit_sound checkUnit_cycle_ok).2.2.2.2.2.2.2.2.2.1

/-- The hand-written two-cycle carrier. -/
def twoCycleCarrier : Lara.Invariants.StructuredAF :=
  { nodes := [litAtom 0 0, litAtom 1 0]
    attack := fun i j => decide ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) }

private theorem acceptedCycle_nodes :
    (Lara.Invariants.compileUnit acceptedCycleUnit).nodes =
      twoCycleCarrier.nodes := by decide

private theorem acceptedCycle_edges (i j : Nat) :
    (Lara.Invariants.compileUnit acceptedCycleUnit).attack i j =
      twoCycleCarrier.attack i j := by
  change Lara.Compile.edgeB acceptedCycleUnit.program i j = _
  unfold Lara.Compile.edgeB
  rw [acceptedCycle_args, acceptedCycle_atts]
  rcases i with _ | _ | i <;> rcases j with _ | _ | j <;>
    simp [cycleRawUnit, cycleNegArg, cyclePosArg,
      cycleNegLeaf, cyclePosLeaf, twoCycleCarrier,
      Lara.Attack.Attack.source, Lara.Compile.coveredB,
      Lara.Compile.attackClosureB, Lara.Compile.containsB,
      Lara.Attack.subterm]

/-- Compilation of the accepted two-cycle is exactly the hand-written carrier. -/
def twoCycleIso :
    Lara.Realizability.StructuredAFIso
      (Lara.Invariants.compileUnit acceptedCycleUnit) twoCycleCarrier where
  nodeEquiv := Lara.Realizability.Equiv.refl Nat
  labels := by
    intro i
    rw [acceptedCycle_nodes]
    simp [Lara.Realizability.Equiv.refl]
  attacks := by
    intro i j
    simpa [Lara.Realizability.Equiv.refl] using acceptedCycle_edges i j

/-- A source/target reversal of the path's first declaration is rejected by the
fixed checker; `b(0)` is not contrary to `d`. -/
def reversedPathRawUnit : Lara.Unit :=
  { sigma := m2bSigma
    policy := m2bPolicy
    args := [pathDArg, pathBArg, pathAArg]
    atts :=
      [ .undermine pathBArg pathDArg []
      , .undermine pathBArg pathAArg [] ] }

theorem checkUnit_reversedPath_rejected :
    (Check.Unit.checkUnit pathGamma m2bRegistry pathGround
      reversedPathRawUnit).isOk = false := by decide

/-! ## Formula-indexed raw gadget (defined in `Lara.Complexity.Gadget`) -/

private def rawShapeClause : Clause3 :=
  { first := ⟨true, 0⟩
    second := ⟨false, 1⟩
    third := ⟨true, 0⟩ }

/-- Fixture-owned clause term.  It deliberately does not reuse
`clauseSubst` or `clauseArgument`. -/
private def rawShapeExpectedClauseArgument : SupportTerm :=
  .inst m2bClauseRuleId
    [ (⟨"S1"⟩, .num "1")
    , (⟨"X1"⟩, .num "0")
    , (⟨"S2"⟩, .num "0")
    , (⟨"X2"⟩, .num "1")
    , (⟨"S3"⟩, .num "1")
    , (⟨"X3"⟩, .num "0")
    , (⟨"J"⟩, .num "0") ]
    [ .leaf (occurrenceLeafId 0 0)
    , .leaf (occurrenceLeafId 0 1)
    , .leaf (occurrenceLeafId 0 2) ]
    [] [] .none

/-- Executable shape fixture for the formula-indexed constructor data.  The
repeated variable pins duplicate elimination and occurrence order; the exact
checks independently pin every leaf lookup, ground atom, substitution binding,
root, and positional attack. -/
theorem rawUnitOfFormula_shape :
    (gammaOfFormula [rawShapeClause]) (negativeLiteralLeafId 1) =
      some (litAtom 0 1) ∧
    (gammaOfFormula [rawShapeClause]) (positiveLiteralLeafId 1) =
      some (litAtom 1 1) ∧
    (gammaOfFormula [rawShapeClause]) (negativeLiteralLeafId 0) =
      some (litAtom 0 0) ∧
    (gammaOfFormula [rawShapeClause]) (positiveLiteralLeafId 0) =
      some (litAtom 1 0) ∧
    (gammaOfFormula [rawShapeClause]) (occurrenceLeafId 0 0) =
      some (occAtom 1 0) ∧
    (gammaOfFormula [rawShapeClause]) (occurrenceLeafId 0 1) =
      some (occAtom 0 1) ∧
    (gammaOfFormula [rawShapeClause]) (occurrenceLeafId 0 2) =
      some (occAtom 1 0) ∧
    (gammaOfFormula [rawShapeClause]) queryLeafId = some queryAtom ∧
    groundOfFormula [rawShapeClause] =
      [ litAtom 0 1
      , litAtom 1 1
      , litAtom 0 0
      , litAtom 1 0
      , occAtom 1 0
      , occAtom 0 1
      , occAtom 1 0
      , queryAtom ] ∧
    (groundOfFormula [rawShapeClause]).length = 8 ∧
    clauseSubst 0 rawShapeClause =
      [ (⟨"S1"⟩, .num "1")
      , (⟨"X1"⟩, .num "0")
      , (⟨"S2"⟩, .num "0")
      , (⟨"X2"⟩, .num "1")
      , (⟨"S3"⟩, .num "1")
      , (⟨"X3"⟩, .num "0")
      , (⟨"J"⟩, .num "0") ] ∧
    (rawUnitOfFormula [rawShapeClause]).args =
      [ negativeLiteralArg 1
      , positiveLiteralArg 1
      , negativeLiteralArg 0
      , positiveLiteralArg 0
      , rawShapeExpectedClauseArgument
      , queryArg ] ∧
    (rawUnitOfFormula [rawShapeClause]).atts =
      [ .undermine (negativeLiteralArg 1) (positiveLiteralArg 1) []
      , .undermine (positiveLiteralArg 1) (negativeLiteralArg 1) []
      , .undermine (negativeLiteralArg 0) (positiveLiteralArg 0) []
      , .undermine (positiveLiteralArg 0) (negativeLiteralArg 0) []
      , .undermine (positiveLiteralArg 0)
          rawShapeExpectedClauseArgument [.prem 0]
      , .undermine (negativeLiteralArg 1)
          rawShapeExpectedClauseArgument [.prem 1]
      , .undermine (positiveLiteralArg 0)
          rawShapeExpectedClauseArgument [.prem 2]
      , .undermine rawShapeExpectedClauseArgument queryArg [] ] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/- The spike did not close the family-wide proof needed to define
`acceptedUnitOfFormula` without a proof gap.  This is the documentary gate
outcome, not a formal impossibility theorem. -/

/-- Every formula-indexed raw unit reuses the fixed signature and policy stored
on `Lara.Unit`. -/
theorem rawUnitOfFormula_fixedFields (formula : Formula3) :
    (rawUnitOfFormula formula).sigma = m2bSigma ∧
      (rawUnitOfFormula formula).policy = m2bPolicy := by
  constructor <;> rfl

end Lara.Examples.Complexity.Realization
