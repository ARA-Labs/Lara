import Lara.Unit

namespace Lara.Complexity

open Lara.Support

/-- The fixed many-sorted signature. All data positions are numeric; `d` and
`query` are nullary. -/
def m2bSigma : Lara.Sigma.Sigma :=
  { sorts := []
    cons := []
    preds :=
      [ ⟨⟨"g"⟩, [.num]⟩
      , ⟨⟨"d"⟩, []⟩
      , ⟨⟨"b"⟩, [.num]⟩
      , ⟨⟨"a"⟩, [.num]⟩
      , ⟨⟨"lit"⟩, [.num, .num]⟩
      , ⟨⟨"occ"⟩, [.num, .num]⟩
      , ⟨⟨"clause"⟩, [.num]⟩
      , ⟨⟨"query"⟩, []⟩ ] }

private def unaryPat (pred : String) (arg : Pat) : APat :=
  ⟨⟨pred⟩, .cons arg .nil⟩

private def binaryPat (pred : String) (first second : Pat) : APat :=
  ⟨⟨pred⟩, .cons first (.cons second .nil)⟩

private def nullaryPat (pred : String) : APat :=
  ⟨⟨pred⟩, .nil⟩

private def clauseS1 : VarId := ⟨"S1"⟩
private def clauseX1 : VarId := ⟨"X1"⟩
private def clauseS2 : VarId := ⟨"S2"⟩
private def clauseX2 : VarId := ⟨"X2"⟩
private def clauseS3 : VarId := ⟨"S3"⟩
private def clauseX3 : VarId := ⟨"X3"⟩
private def clauseJ : VarId := ⟨"J"⟩

/-- Stable identifier of the sole ordinary defeasible rule in the fixed
policy. -/
def m2bClauseRuleId : RuleId := ⟨"m2b-clause"⟩

/-- `occ(s₁,x₁), occ(s₂,x₂), occ(s₃,x₃) ⇒ clause(j)`. -/
def m2bClauseRule : Rule :=
  { mode := .defeasible
    params :=
      [clauseS1, clauseX1, clauseS2, clauseX2, clauseS3, clauseX3,
        clauseJ]
    premises :=
      [ binaryPat "occ" (.var clauseS1) (.var clauseX1)
      , binaryPat "occ" (.var clauseS2) (.var clauseX2)
      , binaryPat "occ" (.var clauseS3) (.var clauseX3) ]
    concl := unaryPat "clause" (.var clauseJ)
    questions := []
    allowTrusted := false
    certifiers := [] }

private def contraryX : VarId := ⟨"X"⟩
private def contraryY : VarId := ⟨"Y"⟩
private def contraryS : VarId := ⟨"S"⟩
private def contraryJ : VarId := ⟨"J"⟩

/-- The fixed policy: six directional contrary schemas and one ordinary
(defeasible, uncertified) clause rule. -/
def m2bPolicy : Lara.Policy.Policy :=
  { rules := [⟨m2bClauseRuleId, m2bClauseRule⟩]
    defeat :=
      { contraries :=
          [ (nullaryPat "d", unaryPat "b" (.var contraryX))
          , (unaryPat "b" (.var contraryX),
              unaryPat "a" (.var contraryY))
          , (binaryPat "lit" (.num "0") (.var contraryX),
              binaryPat "lit" (.num "1") (.var contraryX))
          , (binaryPat "lit" (.num "1") (.var contraryX),
              binaryPat "lit" (.num "0") (.var contraryX))
          , (binaryPat "lit" (.var contraryS) (.var contraryX),
              binaryPat "occ" (.var contraryS) (.var contraryX))
          , (unaryPat "clause" (.var contraryJ), nullaryPat "query") ]
        exceptions := [] } }

/-- The six contrary rows of the fixed policy, re-spelled literally rather
than through the private pattern builders above — the drift tripwire consumed
by the gadget and witness attack characterizations (issue #211): any drift in
the fixed defeat table breaks this `rfl` at compile time. -/
theorem m2bDefeat_contraries :
    m2bPolicy.defeat.contraries =
      [ (⟨⟨"d"⟩, .nil⟩, ⟨⟨"b"⟩, .cons (.var ⟨"X"⟩) .nil⟩)
      , (⟨⟨"b"⟩, .cons (.var ⟨"X"⟩) .nil⟩, ⟨⟨"a"⟩, .cons (.var ⟨"Y"⟩) .nil⟩)
      , (⟨⟨"lit"⟩, .cons (.num "0") (.cons (.var ⟨"X"⟩) .nil)⟩,
          ⟨⟨"lit"⟩, .cons (.num "1") (.cons (.var ⟨"X"⟩) .nil)⟩)
      , (⟨⟨"lit"⟩, .cons (.num "1") (.cons (.var ⟨"X"⟩) .nil)⟩,
          ⟨⟨"lit"⟩, .cons (.num "0") (.cons (.var ⟨"X"⟩) .nil)⟩)
      , (⟨⟨"lit"⟩, .cons (.var ⟨"S"⟩) (.cons (.var ⟨"X"⟩) .nil)⟩,
          ⟨⟨"occ"⟩, .cons (.var ⟨"S"⟩) (.cons (.var ⟨"X"⟩) .nil)⟩)
      , (⟨⟨"clause"⟩, .cons (.var ⟨"J"⟩) .nil⟩, ⟨⟨"query"⟩, .nil⟩) ] := rfl

/-- The restricted construction uses no strict backend. All non-rule support is
provided by leaves. -/
def m2bRegistry : BackendRegistry id := fun _ => none

@[simp] theorem m2bRegistry_empty (backend : BackendId) :
    m2bRegistry backend = none := rfl

private def numTerm (n : Nat) : Lara.Term := .num (Nat.repr n)

/-- Ground atoms of the fixed signature, shared by later reductions. -/
def gAtom (i : Nat) : Lara.Atom :=
  .atom "g" (.cons (numTerm i) .nil)

def dAtom : Lara.Atom := .atom "d" .nil

def bAtom (x : Nat) : Lara.Atom :=
  .atom "b" (.cons (numTerm x) .nil)

def aAtom (x : Nat) : Lara.Atom :=
  .atom "a" (.cons (numTerm x) .nil)

def litAtom (sign varIdx : Nat) : Lara.Atom :=
  .atom "lit" (.cons (numTerm sign) (.cons (numTerm varIdx) .nil))

def occAtom (sign varIdx : Nat) : Lara.Atom :=
  .atom "occ" (.cons (numTerm sign) (.cons (numTerm varIdx) .nil))

def clauseAtom (j : Nat) : Lara.Atom :=
  .atom "clause" (.cons (numTerm j) .nil)

def queryAtom : Lara.Atom := .atom "query" .nil

/- The fixed signature and policy pass every context-only executable guard that
precedes argument checking in `Check.Unit.checkUnit`. -/
theorem m2bSigma_wellFormed :
    Lara.Sigma.sigmaWellFormed m2bSigma = true := by decide

theorem m2bPolicy_wellSorted :
    Lara.policyWellSorted m2bSigma m2bPolicy = true := by decide

theorem m2bPolicy_ruleIds_unique :
    Lara.Policy.firstDuplicateRuleId? m2bPolicy.rules = none := by decide

theorem m2bPolicy_scopesWellFormed :
    Lara.Policy.firstOutOfScope? m2bPolicy = none := by decide

theorem m2bPolicy_noViolation :
    Lara.Policy.firstViolation? id m2bPolicy = none := by decide

/- Closed evaluations pin every positive directional schema. Distinct values in
`b(0) → a(1)` witness that its two variable positions are independent. -/
theorem d_attacks_b :
    Lara.Attack.contraryMatchB id m2bPolicy.defeat dAtom (bAtom 0) = true := by
  decide

theorem b_attacks_a :
    Lara.Attack.contraryMatchB id m2bPolicy.defeat (bAtom 0) (aAtom 1) = true := by
  decide

theorem negative_lit_attacks_positive_lit :
    Lara.Attack.contraryMatchB id m2bPolicy.defeat
      (litAtom 0 0) (litAtom 1 0) = true := by
  decide

theorem positive_lit_attacks_negative_lit :
    Lara.Attack.contraryMatchB id m2bPolicy.defeat
      (litAtom 1 0) (litAtom 0 0) = true := by
  decide

theorem lit_attacks_occ :
    Lara.Attack.contraryMatchB id m2bPolicy.defeat
      (litAtom 0 0) (occAtom 0 0) = true := by
  decide

theorem clause_attacks_query :
    Lara.Attack.contraryMatchB id m2bPolicy.defeat
      (clauseAtom 0) queryAtom = true := by
  decide

/- Closed negative controls pin directionality and repeated-variable matching. -/
theorem b_does_not_attack_d :
    Lara.Attack.contraryMatchB id m2bPolicy.defeat (bAtom 0) dAtom = false := by
  decide

theorem a_does_not_attack_b :
    Lara.Attack.contraryMatchB id m2bPolicy.defeat (aAtom 0) (bAtom 0) = false := by
  decide

theorem lit_different_variable_does_not_attack :
    Lara.Attack.contraryMatchB id m2bPolicy.defeat
      (litAtom 0 0) (litAtom 1 1) = false := by
  decide

theorem occ_does_not_attack_lit :
    Lara.Attack.contraryMatchB id m2bPolicy.defeat
      (occAtom 0 0) (litAtom 0 0) = false := by
  decide

end Lara.Complexity
