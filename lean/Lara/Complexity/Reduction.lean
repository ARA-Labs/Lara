/-
The compile image of the formula gadget (issue #209, Task 8).

`reduceCode φ` is the finite carrier the M2b reduction emits: the gadget's
root conclusions in declaration order and the *intended* adjacency matrix —
mutual literal pairs, satisfying-literal-to-clause edges (positional
undermines compile to edges on the clause argument node), and
clause-to-query edges.  `reduceIso` proves the compiled accepted unit is
exactly this carrier: `coveredB_gadget` characterizes the checker's own
closure-edge scan over the generated family as `gadgetEdgeB`, so "no
closure-generated extras" is a theorem, not a stipulation.  `reduce_realizable`
packages the family-wide checker equation, ground coverage, and the iso into
the frozen `M2bPromise`; `reduce_nodes` and `reduce_byteSize` are the frozen
size obligations (§1 constraint 5: `CarrierCode.byteSize` is the carrier
accounting measure, `Formula3.byteSize` the UTF-8 length of the canonical
S-expression).

This module owns the compile-image seam (see `docs/theory-m2b-complexity.md`
and issue #209): the gadget module proves what the checker accepts, this one
proves what compilation makes of it and how large the result is.

Task 12 adds the reduction's *correctness*.  `Formula3.Satisfiable` defines
satisfiability over the explicit three-literal syntax; the soundness and
completeness arguments are AF combinatorics over `gadgetEdgeB`'s closed case
analysis on the decoded carrier; and the frozen end-to-end theorem
`reduce_correct : Satisfiable φ ↔ FixedCredComplete (reduceCode φ)` is
stated in one labelled section with the Task 8 class-membership and size
obligations, so correctness cannot be quoted without them.  Executable
fixtures decide both verdicts through `fixedCredCompleteB`, and
`selfEdgeCode` is the class-membership negative control: the one-node
`g(0)` self-edge carrier is not `M2bPromise`-realizable because no
`m2bPolicy` contrary row licenses `g(0) → g(0)`.  NP-completeness itself is
deliberately not a Lean statement; the paper cites these mechanized
obligations.
-/

import Lara.Complexity.Gadget

namespace Lara.Complexity

open Lara Lara.Support Lara.Attack

/-! ## The reduction node vocabulary

One symbolic constructor per gadget node, carrying the generator data the
image proofs need (the clause node carries its clause, so the intended edge
relation is a closed function of two nodes). -/

/-- Symbolic gadget node: the declaration-order carrier positions. -/
inductive GadgetNode where
  | negLit (varIdx : Nat)
  | posLit (varIdx : Nat)
  | clause (clauseIndex : Nat) (clause : Clause3)
  | query
deriving DecidableEq

/-- The declared argument of a gadget node. -/
def GadgetNode.arg : GadgetNode → SupportTerm
  | .negLit v => negativeLiteralArg v
  | .posLit v => positiveLiteralArg v
  | .clause j c => clauseArgument j c
  | .query => queryArg

/-- The root conclusion of a gadget node. -/
def GadgetNode.conclusion : GadgetNode → Lara.Atom
  | .negLit v => litAtom 0 v
  | .posLit v => litAtom 1 v
  | .clause j _ => clauseAtom j
  | .query => queryAtom

/-- The gadget nodes in declaration order: for each occurring variable the
negative then the positive literal root, then the clause instances by clause
index, then the query. -/
def gadgetNodes (φ : Formula3) : List GadgetNode :=
  φ.occurringVariables.flatMap (fun v => [.negLit v, .posLit v]) ++
    φ.zipIdx.map (fun entry => .clause entry.2 entry.1) ++ [.query]

/-- The signed literal `lit(sign, varIdx)` occurs in the clause — i.e.
asserting it satisfies the clause. -/
def signedLiteralOccursB (c : Clause3) (sign varIdx : Nat) : Bool :=
  c.literals.any fun l =>
    literalSign l == sign && l.«variable» == varIdx

/-- **The intended gadget edge relation.**  Mutual literal pairs,
satisfying-literal-to-clause edges, clause-to-query edges — and nothing
else. -/
def gadgetEdgeB : GadgetNode → GadgetNode → Bool
  | .negLit v, .posLit w => v == w
  | .posLit v, .negLit w => v == w
  | .negLit v, .clause _ c => signedLiteralOccursB c 0 v
  | .posLit v, .clause _ c => signedLiteralOccursB c 1 v
  | .clause _ _, .query => true
  | _, _ => false

/-! ## The reduction output -/

/-- **The compile image of the formula gadget.**  Node conclusions in
declaration order, the intended adjacency matrix row by row, and the query
index (the last node). -/
def reduceCode (φ : Formula3) : CarrierCode :=
  { nodes := (gadgetNodes φ).map GadgetNode.conclusion
    matrix := (gadgetNodes φ).map fun a =>
      (gadgetNodes φ).map fun b => gadgetEdgeB a b
    query := (gadgetNodes φ).length - 1
    square := by
      refine ⟨by simp, ?_⟩
      intro row hrow
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hrow
      simp
    query_lt := by
      have h0 : 0 < (gadgetNodes φ).length := by
        simp only [gadgetNodes, List.length_append, List.length_cons,
          List.length_nil]
        omega
      simp only [List.length_map]
      omega }

private theorem length_flatMap_pair {α β : Type _} (f g : α → β) :
    ∀ l : List α, (l.flatMap fun v => [f v, g v]).length = 2 * l.length
  | [] => rfl
  | v :: vs => by
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil, length_flatMap_pair f g vs]
      omega

private theorem gadgetNodes_length (φ : Formula3) :
    (gadgetNodes φ).length = 2 * Formula3.variableCount φ + φ.length + 1 := by
  unfold gadgetNodes
  rw [List.length_append, List.length_append, length_flatMap_pair]
  simp only [List.length_map, List.length_zipIdx, List.length_cons,
    List.length_nil]
  rfl

open Formula3 in
/-- **The frozen node count.**  Two literal roots per occurring variable, one
clause instance per clause, one query. -/
theorem reduce_nodes (φ : Formula3) :
    (reduceCode φ).nodes.length = 2 * variableCount φ + φ.length + 1 := by
  show ((gadgetNodes φ).map GadgetNode.conclusion).length = _
  rw [List.length_map, gadgetNodes_length]

/-! ## Generator inversion for the node list -/

private theorem mem_gadgetNodes {φ : Formula3} {g : GadgetNode}
    (hg : g ∈ gadgetNodes φ) :
    (∃ v ∈ φ.occurringVariables, g = .negLit v ∨ g = .posLit v) ∨
      (∃ c j, (c, j) ∈ φ.zipIdx ∧ g = .clause j c) ∨ g = .query := by
  unfold gadgetNodes at hg
  rcases List.mem_append.mp hg with hlit_clause | hquery
  · rcases List.mem_append.mp hlit_clause with hlit | hclause
    · obtain ⟨v, hv, hgv⟩ := List.mem_flatMap.mp hlit
      exact Or.inl ⟨v, hv, by simpa using hgv⟩
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hclause
      exact Or.inr (Or.inl ⟨e.1, e.2, he, rfl⟩)
  · exact Or.inr (Or.inr (by simpa using hquery))

private theorem mem_occurring_of_negLit {φ : Formula3} {v : Nat}
    (h : GadgetNode.negLit v ∈ gadgetNodes φ) : v ∈ φ.occurringVariables := by
  rcases mem_gadgetNodes h with ⟨w, hw, hvw | hvw⟩ | ⟨c, j, -, hvw⟩ | hvw
  · cases hvw; exact hw
  · exact absurd hvw (by simp)
  · exact absurd hvw (by simp)
  · exact absurd hvw (by simp)

private theorem mem_occurring_of_posLit {φ : Formula3} {v : Nat}
    (h : GadgetNode.posLit v ∈ gadgetNodes φ) : v ∈ φ.occurringVariables := by
  rcases mem_gadgetNodes h with ⟨w, hw, hvw | hvw⟩ | ⟨c, j, -, hvw⟩ | hvw
  · exact absurd hvw (by simp)
  · cases hvw; exact hw
  · exact absurd hvw (by simp)
  · exact absurd hvw (by simp)

private theorem mem_zipIdx_of_clause {φ : Formula3} {j : Nat} {c : Clause3}
    (h : GadgetNode.clause j c ∈ gadgetNodes φ) : (c, j) ∈ φ.zipIdx := by
  rcases mem_gadgetNodes h with ⟨w, -, hvw | hvw⟩ | ⟨c', j', hcj, hvw⟩ | hvw
  · exact absurd hvw (by simp)
  · exact absurd hvw (by simp)
  · injection hvw with h1 h2
    subst h1; subst h2
    exact hcj
  · exact absurd hvw (by simp)

/-! ## The argument list is the node list's projection -/

private theorem formulaArguments_eq_gadget (φ : Formula3) :
    formulaArguments φ = (gadgetNodes φ).map GadgetNode.arg := by
  simp [formulaArguments, literalArguments, clauseArguments, gadgetNodes,
    List.map_flatMap, List.map_map, Function.comp_def, GadgetNode.arg]

/-! ## Structural containment over the gadget terms

`Compile.Contains` quantifies over the infinite position type; over the
gadget's two term shapes it computes away: a leaf contains only itself, and a
clause instance contains itself and its three occurrence leaves. -/

private theorem contains_leaf_iff {l : LeafId} {t : SupportTerm} :
    Compile.Contains (.leaf l) t ↔ t = .leaf l := by
  constructor
  · rintro ⟨π, hπ⟩
    cases π with
    | nil => exact (Option.some.inj hπ).symm
    | cons e rest => simp [Attack.subterm] at hπ
  · rintro rfl
    exact Compile.contains_refl _

/-- The clause instance's premise list, reduced. -/
private theorem clauseArgument_eq (j : Nat) (c : Clause3) :
    clauseArgument j c =
      .inst m2bClauseRuleId (clauseSubst j c)
        [ .leaf (occurrenceLeafId j 0)
        , .leaf (occurrenceLeafId j 1)
        , .leaf (occurrenceLeafId j 2) ] [] [] .none := rfl

private theorem contains_clauseArgument_iff {j : Nat} {c : Clause3}
    {t : SupportTerm} :
    Compile.Contains (clauseArgument j c) t ↔
      t = clauseArgument j c ∨
        t = .leaf (occurrenceLeafId j 0) ∨
        t = .leaf (occurrenceLeafId j 1) ∨
        t = .leaf (occurrenceLeafId j 2) := by
  constructor
  · rintro ⟨π, hπ⟩
    rw [clauseArgument_eq] at hπ
    cases π with
    | nil =>
        rw [← clauseArgument_eq] at hπ
        exact Or.inl (Option.some.inj hπ).symm
    | cons e rest =>
        cases e with
        | prem i =>
            rcases i with _ | _ | _ | i <;>
              simp only [Attack.subterm, List.getElem?_cons_zero,
                List.getElem?_cons_succ, List.getElem?_nil] at hπ
            · exact Or.inr (Or.inl ((contains_leaf_iff.mp ⟨rest, hπ⟩)))
            · exact Or.inr (Or.inr (Or.inl (contains_leaf_iff.mp ⟨rest, hπ⟩)))
            · exact Or.inr (Or.inr (Or.inr (contains_leaf_iff.mp ⟨rest, hπ⟩)))
            · nomatch hπ
        | ques q =>
            simp [Attack.subterm, Attack.lookupDis] at hπ
  · rintro (rfl | rfl | rfl | rfl)
    · exact Compile.contains_refl _
    · exact ⟨[.prem 0], rfl⟩
    · exact ⟨[.prem 1], rfl⟩
    · exact ⟨[.prem 2], rfl⟩

/-! ## Identifying a gadget node from its argument -/

private theorem arg_eq_negLit {a : GadgetNode} {v : Nat}
    (h : a.arg = negativeLiteralArg v) : a = .negLit v := by
  cases a <;>
    simp_all [GadgetNode.arg, negativeLiteralArg, positiveLiteralArg,
      queryArg, clauseArgument, negativeLiteralLeafId, positiveLiteralLeafId,
      queryLeafId, GadgetLeaf.encode_eq_iff]

private theorem arg_eq_posLit {a : GadgetNode} {v : Nat}
    (h : a.arg = positiveLiteralArg v) : a = .posLit v := by
  cases a <;>
    simp_all [GadgetNode.arg, negativeLiteralArg, positiveLiteralArg,
      queryArg, clauseArgument, negativeLiteralLeafId, positiveLiteralLeafId,
      queryLeafId, GadgetLeaf.encode_eq_iff]

private theorem arg_eq_clause {a : GadgetNode} {j : Nat} {c : Clause3}
    (h : a.arg = clauseArgument j c) : ∃ c', a = .clause j c' := by
  cases a with
  | clause j' c' =>
      have hj : j' = j := clauseArgument_index_inj h
      exact ⟨c', by rw [hj]⟩
  | negLit v =>
      simp [GadgetNode.arg, negativeLiteralArg, clauseArgument] at h
  | posLit v =>
      simp [GadgetNode.arg, positiveLiteralArg, clauseArgument] at h
  | query =>
      simp [GadgetNode.arg, queryArg, clauseArgument] at h

/-! ## Identifying a gadget node from a contained occurrence -/

private theorem contains_posLit_eq {b : GadgetNode} {v : Nat}
    (h : Compile.Contains b.arg (positiveLiteralArg v)) : b = .posLit v := by
  cases b with
  | negLit w =>
      rw [show (GadgetNode.negLit w).arg =
        .leaf (negativeLiteralLeafId w) from rfl, contains_leaf_iff] at h
      simp_all [positiveLiteralArg, negativeLiteralLeafId,
        positiveLiteralLeafId, GadgetLeaf.encode_eq_iff]
  | posLit w =>
      rw [show (GadgetNode.posLit w).arg =
        .leaf (positiveLiteralLeafId w) from rfl, contains_leaf_iff] at h
      simp_all [positiveLiteralArg, positiveLiteralLeafId,
        GadgetLeaf.encode_eq_iff]
  | clause j' c' =>
      rw [show (GadgetNode.clause j' c').arg = clauseArgument j' c' from rfl,
        contains_clauseArgument_iff] at h
      rcases h with h | h | h | h <;>
        simp_all [positiveLiteralArg, clauseArgument, positiveLiteralLeafId,
          occurrenceLeafId, GadgetLeaf.encode_eq_iff]
  | query =>
      rw [show GadgetNode.query.arg = .leaf queryLeafId from rfl,
        contains_leaf_iff] at h
      simp_all [positiveLiteralArg, positiveLiteralLeafId, queryLeafId,
        GadgetLeaf.encode_eq_iff]

private theorem contains_negLit_eq {b : GadgetNode} {v : Nat}
    (h : Compile.Contains b.arg (negativeLiteralArg v)) : b = .negLit v := by
  cases b with
  | negLit w =>
      rw [show (GadgetNode.negLit w).arg =
        .leaf (negativeLiteralLeafId w) from rfl, contains_leaf_iff] at h
      simp_all [negativeLiteralArg, negativeLiteralLeafId,
        GadgetLeaf.encode_eq_iff]
  | posLit w =>
      rw [show (GadgetNode.posLit w).arg =
        .leaf (positiveLiteralLeafId w) from rfl, contains_leaf_iff] at h
      simp_all [negativeLiteralArg, negativeLiteralLeafId,
        positiveLiteralLeafId, GadgetLeaf.encode_eq_iff]
  | clause j' c' =>
      rw [show (GadgetNode.clause j' c').arg = clauseArgument j' c' from rfl,
        contains_clauseArgument_iff] at h
      rcases h with h | h | h | h <;>
        simp_all [negativeLiteralArg, clauseArgument, negativeLiteralLeafId,
          occurrenceLeafId, GadgetLeaf.encode_eq_iff]
  | query =>
      rw [show GadgetNode.query.arg = .leaf queryLeafId from rfl,
        contains_leaf_iff] at h
      simp_all [negativeLiteralArg, negativeLiteralLeafId, queryLeafId,
        GadgetLeaf.encode_eq_iff]

private theorem contains_query_eq {b : GadgetNode}
    (h : Compile.Contains b.arg queryArg) : b = .query := by
  cases b with
  | negLit w =>
      rw [show (GadgetNode.negLit w).arg =
        .leaf (negativeLiteralLeafId w) from rfl, contains_leaf_iff] at h
      simp_all [queryArg, negativeLiteralLeafId, queryLeafId,
        GadgetLeaf.encode_eq_iff]
  | posLit w =>
      rw [show (GadgetNode.posLit w).arg =
        .leaf (positiveLiteralLeafId w) from rfl, contains_leaf_iff] at h
      simp_all [queryArg, positiveLiteralLeafId, queryLeafId,
        GadgetLeaf.encode_eq_iff]
  | clause j' c' =>
      rw [show (GadgetNode.clause j' c').arg = clauseArgument j' c' from rfl,
        contains_clauseArgument_iff] at h
      rcases h with h | h | h | h <;>
        simp_all [queryArg, clauseArgument, queryLeafId, occurrenceLeafId,
          GadgetLeaf.encode_eq_iff]
  | query => rfl

private theorem contains_occurrence_clause {φ : Formula3} {b : GadgetNode}
    {c : Clause3} {j p : Nat} (hb : b ∈ gadgetNodes φ)
    (hc : (c, j) ∈ φ.zipIdx)
    (h : Compile.Contains b.arg (.leaf (occurrenceLeafId j p))) :
    b = .clause j c := by
  cases b with
  | negLit w =>
      rw [show (GadgetNode.negLit w).arg =
        .leaf (negativeLiteralLeafId w) from rfl, contains_leaf_iff] at h
      simp_all [negativeLiteralLeafId, occurrenceLeafId,
        GadgetLeaf.encode_eq_iff]
  | posLit w =>
      rw [show (GadgetNode.posLit w).arg =
        .leaf (positiveLiteralLeafId w) from rfl, contains_leaf_iff] at h
      simp_all [positiveLiteralLeafId, occurrenceLeafId,
        GadgetLeaf.encode_eq_iff]
  | clause j' c' =>
      have hj : j' = j := by
        rw [show (GadgetNode.clause j' c').arg = clauseArgument j' c' from rfl,
          contains_clauseArgument_iff] at h
        rcases h with h | h | h | h
        · exact absurd h (by simp [clauseArgument])
        all_goals
          injection h with h'
          exact ((occurrenceLeafId_inj h').1).symm
      subst hj
      have hcj' : (c', j') ∈ φ.zipIdx := mem_zipIdx_of_clause hb
      have h1 := List.mk_mem_zipIdx_iff_getElem?.mp hcj'
      have h2 := List.mk_mem_zipIdx_iff_getElem?.mp hc
      rw [h1] at h2
      rw [Option.some.inj h2]
  | query =>
      rw [show GadgetNode.query.arg = .leaf queryLeafId from rfl,
        contains_leaf_iff] at h
      simp_all [queryLeafId, occurrenceLeafId, GadgetLeaf.encode_eq_iff]

/-! ## Duplicate-key well-formedness of the gadget targets -/

private theorem disNodup_gadgetArg {φ : Formula3} {g : GadgetNode}
    (hg : g ∈ gadgetNodes φ) : Compile.DisNodup g.arg := by
  have hmem : g.arg ∈ (rawUnitOfFormula φ).args := by
    show g.arg ∈ formulaArguments φ
    rw [formulaArguments_eq_gadget]
    exact List.mem_map_of_mem hg
  obtain ⟨C, hC⟩ := formulaArguments_supported φ g.arg hmem
  exact Compile.hasSupport_disNodup hC

/-! ## The exact-edge characterization

`Compile.coveredB` is the checker's own closure-edge scan: some declared
attack sources the tail and its attacked occurrence occurs in the head.  Over
the generated family it computes to `gadgetEdgeB` — the forward direction is
the "no closure-generated extras" obligation (every declared attack's
occurrence lands only where the intended edge already is), and the reverse
exhibits each intended edge's declared undermine. -/

theorem coveredB_gadget (φ : Formula3) {a b : GadgetNode}
    (ha : a ∈ gadgetNodes φ) (hb : b ∈ gadgetNodes φ) :
    Compile.coveredB (formulaAttacks φ) a.arg b.arg = gadgetEdgeB a b := by
  rw [Bool.eq_iff_iff, Compile.coveredB_iff (disNodup_gadgetArg hb)]
  constructor
  · rintro ⟨k, hk, hsrc, t, hocc, hcont⟩
    rcases mem_formulaAttacks hk with
      ⟨v, hv, rfl | rfl⟩ | ⟨c, j, hc, ⟨l, p, hlp, rfl⟩ | rfl⟩
    · -- mutual pair, negative source
      have hsrc' : a.arg = negativeLiteralArg v := hsrc.symm
      obtain rfl := arg_eq_negLit hsrc'
      have ht : t = positiveLiteralArg v := (Option.some.inj hocc).symm
      subst ht
      obtain rfl := contains_posLit_eq hcont
      simp [gadgetEdgeB]
    · -- mutual pair, positive source
      have hsrc' : a.arg = positiveLiteralArg v := hsrc.symm
      obtain rfl := arg_eq_posLit hsrc'
      have ht : t = negativeLiteralArg v := (Option.some.inj hocc).symm
      subst ht
      obtain rfl := contains_negLit_eq hcont
      simp [gadgetEdgeB]
    · -- positional undermine of a clause instance
      have ht : t = .leaf (occurrenceLeafId j p) :=
        (Option.some.inj
          ((subterm_clauseArgument_prem hlp).symm.trans hocc)).symm
      subst ht
      obtain rfl := contains_occurrence_clause hb hc hcont
      have hlmem : l ∈ c.literals :=
        List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hlp)
      cases hpos : l.positive with
      | true =>
          have hsrc' : a.arg = positiveLiteralArg l.«variable» := by
            rw [← hsrc]
            simp [literalArg, literalLeafId, hpos, positiveLiteralArg,
              Attack.Attack.source]
          obtain rfl := arg_eq_posLit hsrc'
          show signedLiteralOccursB c 1 l.«variable» = true
          rw [signedLiteralOccursB, List.any_eq_true]
          exact ⟨l, hlmem, by simp [literalSign, hpos]⟩
      | false =>
          have hsrc' : a.arg = negativeLiteralArg l.«variable» := by
            rw [← hsrc]
            simp [literalArg, literalLeafId, hpos, negativeLiteralArg,
              Attack.Attack.source]
          obtain rfl := arg_eq_negLit hsrc'
          show signedLiteralOccursB c 0 l.«variable» = true
          rw [signedLiteralOccursB, List.any_eq_true]
          exact ⟨l, hlmem, by simp [literalSign, hpos]⟩
    · -- clause-root undermine of the query
      have hsrc' : a.arg = clauseArgument j c := hsrc.symm
      obtain ⟨c', rfl⟩ := arg_eq_clause hsrc'
      have ht : t = queryArg := (Option.some.inj hocc).symm
      subst ht
      obtain rfl := contains_query_eq hcont
      simp [gadgetEdgeB]
  · intro hedge
    cases a with
    | negLit v =>
        cases b with
        | negLit w => exact absurd hedge (by simp [gadgetEdgeB])
        | posLit w =>
            have hvw : (v == w) = true := hedge
            obtain rfl : v = w := beq_iff_eq.mp hvw
            exact ⟨.undermine (negativeLiteralArg v) (positiveLiteralArg v) [],
              undermine_negLit_mem (mem_occurring_of_negLit ha), rfl,
              positiveLiteralArg v, rfl, Compile.contains_refl _⟩
        | clause j c =>
            have hedge' : signedLiteralOccursB c 0 v = true := hedge
            rw [signedLiteralOccursB, List.any_eq_true] at hedge'
            obtain ⟨l, hl, hsv⟩ := hedge'
            rw [Bool.and_eq_true] at hsv
            have hsign : literalSign l = 0 := beq_iff_eq.mp hsv.1
            obtain rfl : l.«variable» = v := beq_iff_eq.mp hsv.2
            have hneg : l.positive = false := by
              cases hpos : l.positive
              · rfl
              · rw [literalSign, if_pos hpos] at hsign
                exact absurd hsign (by omega)
            obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hl
            have hlp : (l, p) ∈ c.literals.zipIdx :=
              List.mk_mem_zipIdx_iff_getElem?.mpr hp
            have hc : (c, j) ∈ φ.zipIdx := mem_zipIdx_of_clause hb
            refine ⟨.undermine (literalArg l) (clauseArgument j c) [.prem p],
              undermine_literal_occurrence_mem hc hlp, ?_,
              .leaf (occurrenceLeafId j p), subterm_clauseArgument_prem hlp,
              ⟨[.prem p], subterm_clauseArgument_prem hlp⟩⟩
            show literalArg l = negativeLiteralArg l.«variable»
            simp [literalArg, literalLeafId, hneg, negativeLiteralArg]
        | query => exact absurd hedge (by simp [gadgetEdgeB])
    | posLit v =>
        cases b with
        | negLit w =>
            have hvw : (v == w) = true := hedge
            obtain rfl : v = w := beq_iff_eq.mp hvw
            exact ⟨.undermine (positiveLiteralArg v) (negativeLiteralArg v) [],
              undermine_posLit_mem (mem_occurring_of_posLit ha), rfl,
              negativeLiteralArg v, rfl, Compile.contains_refl _⟩
        | posLit w => exact absurd hedge (by simp [gadgetEdgeB])
        | clause j c =>
            have hedge' : signedLiteralOccursB c 1 v = true := hedge
            rw [signedLiteralOccursB, List.any_eq_true] at hedge'
            obtain ⟨l, hl, hsv⟩ := hedge'
            rw [Bool.and_eq_true] at hsv
            have hsign : literalSign l = 1 := beq_iff_eq.mp hsv.1
            obtain rfl : l.«variable» = v := beq_iff_eq.mp hsv.2
            have hposl : l.positive = true := by
              cases hpos : l.positive
              · rw [literalSign, if_neg (by simp [hpos])] at hsign
                exact absurd hsign (by omega)
              · rfl
            obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hl
            have hlp : (l, p) ∈ c.literals.zipIdx :=
              List.mk_mem_zipIdx_iff_getElem?.mpr hp
            have hc : (c, j) ∈ φ.zipIdx := mem_zipIdx_of_clause hb
            refine ⟨.undermine (literalArg l) (clauseArgument j c) [.prem p],
              undermine_literal_occurrence_mem hc hlp, ?_,
              .leaf (occurrenceLeafId j p), subterm_clauseArgument_prem hlp,
              ⟨[.prem p], subterm_clauseArgument_prem hlp⟩⟩
            show literalArg l = positiveLiteralArg l.«variable»
            simp [literalArg, literalLeafId, hposl, positiveLiteralArg]
        | query => exact absurd hedge (by simp [gadgetEdgeB])
    | clause j c =>
        cases b with
        | negLit w => exact absurd hedge (by simp [gadgetEdgeB])
        | posLit w => exact absurd hedge (by simp [gadgetEdgeB])
        | clause j' c' => exact absurd hedge (by simp [gadgetEdgeB])
        | query =>
            exact ⟨.undermine (clauseArgument j c) queryArg [],
              undermine_clause_query_mem (mem_zipIdx_of_clause ha), rfl,
              queryArg, rfl, Compile.contains_refl _⟩
    | query =>
        cases b <;> exact absurd hedge (by simp [gadgetEdgeB])

/-! ## The compilation image -/

/-- Root-conclusion determination, node by node: a supported gadget argument
concludes exactly its node's conclusion. -/
private theorem gadgetNode_conclusion_unique {φ : Formula3} {g : GadgetNode}
    (hg : g ∈ gadgetNodes φ) {C : Lara.Atom}
    (hs : Support.HasSupport id m2bPolicy.ruleLookup (gammaOfFormula φ)
      (Support.certOkOf m2bRegistry) g.arg C []) : C = g.conclusion := by
  cases g with
  | negLit v =>
      have hv : v ∈ φ.occurringVariables := mem_occurring_of_negLit hg
      have hs' : Support.HasSupport id m2bPolicy.ruleLookup (gammaOfFormula φ)
          (Support.certOkOf m2bRegistry)
          (.leaf (negativeLiteralLeafId v)) C [] := hs
      cases hs' with
      | leaf hΓ =>
          exact (Option.some.inj
            ((gammaOfFormula_negLit φ hv).symm.trans hΓ)).symm
  | posLit v =>
      have hv : v ∈ φ.occurringVariables := mem_occurring_of_posLit hg
      have hs' : Support.HasSupport id m2bPolicy.ruleLookup (gammaOfFormula φ)
          (Support.certOkOf m2bRegistry)
          (.leaf (positiveLiteralLeafId v)) C [] := hs
      cases hs' with
      | leaf hΓ =>
          exact (Option.some.inj
            ((gammaOfFormula_posLit φ hv).symm.trans hΓ)).symm
  | clause j c =>
      exact clauseArgument_conclusion_eq (φ := φ) hs
  | query =>
      have hs' : Support.HasSupport id m2bPolicy.ruleLookup (gammaOfFormula φ)
          (Support.certOkOf m2bRegistry) (.leaf queryLeafId) C [] := hs
      cases hs' with
      | leaf hΓ =>
          exact (Option.some.inj
            ((gammaOfFormula_query φ).symm.trans hΓ)).symm

/-- The compiled node labels are the gadget conclusions, in declaration
order. -/
private theorem compile_reduce_nodes (φ : Formula3) :
    (Lara.Invariants.compileUnit (acceptedUnitOfFormula φ)).nodes =
      (reduceCode φ).nodes := by
  have hsound := Check.Unit.checkUnit_sound (checkUnit_formula_ok φ)
  have hpol : (acceptedUnitOfFormula φ).policy = m2bPolicy :=
    hsound.2.2.2.2.2.1
  have hterms : (acceptedUnitOfFormula φ).nodes.map (·.term) =
      (gadgetNodes φ).map GadgetNode.arg := by
    rw [(acceptedUnitOfFormula φ).nodes_terms, hsound.2.2.2.2.2.2.2.2.1]
    exact formulaArguments_eq_gadget φ
  show (acceptedUnitOfFormula φ).nodes.map (·.conclusion) =
    (gadgetNodes φ).map GadgetNode.conclusion
  have hlen : (acceptedUnitOfFormula φ).nodes.length =
      (gadgetNodes φ).length := by
    have h := congrArg List.length hterms
    simpa using h
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, List.getElem?_map]
  cases hnode : (acceptedUnitOfFormula φ).nodes[i]? with
  | none =>
      have hi : (gadgetNodes φ).length ≤ i := by
        rw [← hlen]
        exact List.getElem?_eq_none_iff.mp hnode
      rw [List.getElem?_eq_none hi]
      rfl
  | some node =>
      have hi : i < (gadgetNodes φ).length := by
        rw [← hlen]
        exact Support.lt_of_getElem?_some hnode
      obtain ⟨g, hg⟩ := Support.getElem?_some_of_lt (gadgetNodes φ) i hi
      rw [hg]
      have hterm : node.term = g.arg := by
        have h := congrArg (fun l => l[i]?) hterms
        simp only [List.getElem?_map, hnode, hg, Option.map_some] at h
        exact Option.some.inj h
      have hvalid : Support.HasSupport id m2bPolicy.ruleLookup
          (gammaOfFormula φ) (Support.certOkOf m2bRegistry)
          node.term node.conclusion [] := by
        simpa only [hpol] using node.valid
      rw [hterm] at hvalid
      have hcon :=
        gadgetNode_conclusion_unique (List.mem_of_getElem? hg) hvalid
      simp [hcon]

private theorem reduceCode_matrix (φ : Formula3) :
    (reduceCode φ).matrix = (gadgetNodes φ).map fun a =>
      (gadgetNodes φ).map fun b => gadgetEdgeB a b := rfl

/-- The compiled closure-edge decider agrees with the decoded intended
matrix, at every total position pair — the exact-edge half of the image
(out-of-range positions are edge-free on both sides). -/
private theorem compile_reduce_attack (φ : Formula3) (i j : Nat) :
    (Lara.Invariants.compileUnit (acceptedUnitOfFormula φ)).attack i j =
      (reduceCode φ).decode.attack i j := by
  have hsound := Check.Unit.checkUnit_sound (checkUnit_formula_ok φ)
  have hargs : (acceptedUnitOfFormula φ).program.args =
      (gadgetNodes φ).map GadgetNode.arg :=
    (hsound.2.2.2.2.2.2.2.2.1 :
        (acceptedUnitOfFormula φ).program.args = formulaArguments φ).trans
      (formulaArguments_eq_gadget φ)
  have hatts : (acceptedUnitOfFormula φ).program.atts = formulaAttacks φ :=
    hsound.2.2.2.2.2.2.2.2.2.1
  show Lara.Compile.edgeB (acceptedUnitOfFormula φ).program i j = _
  rw [decode_attack]
  unfold Lara.Compile.edgeB
  rw [hargs, hatts, reduceCode_matrix]
  cases hgi : (gadgetNodes φ)[i]? with
  | none => simp [List.getElem?_map, hgi]
  | some a =>
      cases hgj : (gadgetNodes φ)[j]? with
      | none => simp [List.getElem?_map, hgi, hgj]
      | some b =>
          simp only [List.getElem?_map, hgi, hgj, Option.map_some,
            Option.bind_some, Option.getD_some]
          exact coveredB_gadget φ (List.mem_of_getElem? hgi)
            (List.mem_of_getElem? hgj)

/-- **The compilation image (Task 8, Step 1).**  The structured compilation
of the family-wide accepted unit is the decoded intended carrier, at the
identity position reindexing: same conclusion labels, and exactly the gadget
edges — no closure-generated extras. -/
def reduceIso (φ : Formula3) :
    Lara.Realizability.StructuredAFIso
      (Lara.Invariants.compileUnit (acceptedUnitOfFormula φ))
      (reduceCode φ).decode where
  nodeEquiv := Lara.Realizability.Equiv.refl Nat
  labels := by
    intro i
    rw [show (reduceCode φ).decode.nodes = (reduceCode φ).nodes from rfl,
      compile_reduce_nodes φ]
    simp [Lara.Realizability.Equiv.refl]
  attacks := by
    intro i j
    simpa [Lara.Realizability.Equiv.refl] using compile_reduce_attack φ i j

/-- **The frozen realization promise (Task 8, Step 2).**  Every reduction
output is realizable in the fixed M2b context: the family-wide checker
equation, the fixed signature and policy, ground coverage, and the
compilation image assemble into the executable `Realization` record. -/
theorem reduce_realizable (φ : Formula3) : M2bPromise (reduceCode φ) :=
  ⟨{ Gamma := gammaOfFormula φ
     ground := groundOfFormula φ
     raw := rawUnitOfFormula φ
     accepted := acceptedUnitOfFormula φ
     checked := checkUnit_formula_ok φ
     sigma_eq := (Check.Unit.checkUnit_sound (checkUnit_formula_ok φ)).1
     policy_eq :=
       (Check.Unit.checkUnit_sound (checkUnit_formula_ok φ)).2.2.2.2.2.1
     ground_covers := groundOfFormula_covers φ
     compiled_iso := reduceIso φ }⟩

/-! ## The size obligation

`CarrierCode.byteSize` is the frozen carrier accounting measure (framing
unit + framed atom-key text + one unit per matrix cell + decimal query
index); `Formula3.byteSize` is the exact UTF-8 length of the canonical
S-expression.  The bound routes through three facts: the node count is at
most `Formula3.byteSize φ` (each clause costs at least 15 encoded bytes and
contributes at most 7 nodes), every node key is linear in one decimal
numeral that is either visible in the encoded formula (a variable index) or
bounded by the clause count (a clause index), and the matrix contributes
exactly the square of the node count. -/

private theorem digit_utf8Size {c : Char} (h : c.isDigit) : c.utf8Size = 1 := by
  rw [Char.utf8Size_eq_one_iff, UInt32.le_iff_toNat_le]
  rw [Char.isDigit_iff_toNat] at h
  have hd : '9'.toNat = 57 := by decide
  have h127 : (127 : UInt32).toNat = 127 := by decide
  have hcv : c.toNat = c.val.toNat := rfl
  omega

private theorem charByteSize_digits : ∀ {cs : List Char},
    (∀ c ∈ cs, c.isDigit) → Lara.Strict.charByteSize cs = cs.length := by
  intro cs h
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp [Lara.Strict.charByteSize,
        digit_utf8Size (h c List.mem_cons_self), Nat.add_comm,
        ih (fun d hd => h d (List.mem_cons_of_mem _ hd))]

private theorem repr_utf8_eq_length (n : Nat) :
    (Nat.repr n).utf8ByteSize = (Nat.repr n).length := by
  rw [← Lara.Strict.charByteSize_toList, ← String.length_toList]
  exact charByteSize_digits (fun c hc => by
    rw [Nat.toList_repr] at hc
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)

/-- A canonical decimal numeral never takes more bytes than its value plus
one. -/
private theorem repr_utf8_le (n : Nat) :
    (Nat.repr n).utf8ByteSize ≤ n + 1 := by
  rw [repr_utf8_eq_length, Nat.length_repr_le_iff (by omega)]
  calc n < 10 ^ n := Nat.lt_pow_self (by omega)
  _ ≤ 10 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)

private theorem repr_utf8_pos (n : Nat) : 1 ≤ (Nat.repr n).utf8ByteSize := by
  rw [repr_utf8_eq_length]
  exact Nat.length_repr_pos

private theorem frame_utf8 (s : String) :
    (Lara.Strict.frame s).utf8ByteSize =
      (Nat.repr s.utf8ByteSize).utf8ByteSize + 1 + s.utf8ByteSize := by
  simp [Lara.Strict.frame, String.utf8ByteSize_append,
    (by decide : (":" : String).utf8ByteSize = 1)]

private theorem renderFrames_utf8 : ∀ xs : List String,
    (Lara.Strict.renderFrames xs).utf8ByteSize =
      (xs.map fun x =>
        (Nat.repr x.utf8ByteSize).utf8ByteSize + 1 + x.utf8ByteSize).sum
  | [] => by simp [Lara.Strict.renderFrames]
  | x :: xs => by
      show (Lara.Strict.frame x ++ Lara.Strict.renderFrames xs).utf8ByteSize = _
      rw [String.utf8ByteSize_append, frame_utf8, renderFrames_utf8 xs]
      simp

/-- The framed numeral term key is linear in the numeral's byte length. -/
private theorem numFrames_le (m : Nat) :
    (Lara.Strict.renderFrames ["N", Nat.repr m]).utf8ByteSize ≤
      2 * (Nat.repr m).utf8ByteSize + 6 := by
  rw [renderFrames_utf8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [(by decide : ("N" : String).utf8ByteSize = 1)]
  have h1 := repr_utf8_le 1
  have h2 := repr_utf8_le ((Nat.repr m).utf8ByteSize)
  omega

private theorem key_litAtom_le (s v : Nat) (hs : s ≤ 1) :
    (Lara.Strict.encodeAtomKey (litAtom s v)).utf8ByteSize ≤
      4 * (Nat.repr v).utf8ByteSize + 60 := by
  rw [show Lara.Strict.encodeAtomKey (litAtom s v) =
      Lara.Strict.renderFrames
        ["A", "lit", "L", Nat.repr 2,
          Lara.Strict.renderFrames ["N", Nat.repr s],
          Lara.Strict.renderFrames ["N", Nat.repr v]] from rfl,
    renderFrames_utf8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [(by decide : ("A" : String).utf8ByteSize = 1),
    (by decide : ("lit" : String).utf8ByteSize = 3),
    (by decide : ("L" : String).utf8ByteSize = 1)]
  have h1 := repr_utf8_le 1
  have h3 := repr_utf8_le 3
  have hR2 := repr_utf8_le 2
  have hR2' := repr_utf8_le ((Nat.repr 2).utf8ByteSize)
  have htks := numFrames_le s
  have htks' := repr_utf8_le
    ((Lara.Strict.renderFrames ["N", Nat.repr s]).utf8ByteSize)
  have hLs := repr_utf8_le s
  have htkv := numFrames_le v
  have htkv' := repr_utf8_le
    ((Lara.Strict.renderFrames ["N", Nat.repr v]).utf8ByteSize)
  omega

private theorem key_clauseAtom_le (j : Nat) :
    (Lara.Strict.encodeAtomKey (clauseAtom j)).utf8ByteSize ≤
      4 * (Nat.repr j).utf8ByteSize + 60 := by
  rw [show Lara.Strict.encodeAtomKey (clauseAtom j) =
      Lara.Strict.renderFrames
        ["A", "clause", "L", Nat.repr 1,
          Lara.Strict.renderFrames ["N", Nat.repr j]] from rfl,
    renderFrames_utf8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [(by decide : ("A" : String).utf8ByteSize = 1),
    (by decide : ("clause" : String).utf8ByteSize = 6),
    (by decide : ("L" : String).utf8ByteSize = 1)]
  have h1 := repr_utf8_le 1
  have h6 := repr_utf8_le 6
  have hR1 := repr_utf8_le 1
  have hR1' := repr_utf8_le ((Nat.repr 1).utf8ByteSize)
  have htkj := numFrames_le j
  have htkj' := repr_utf8_le
    ((Lara.Strict.renderFrames ["N", Nat.repr j]).utf8ByteSize)
  omega

private theorem key_queryAtom_le :
    (Lara.Strict.encodeAtomKey queryAtom).utf8ByteSize ≤ 60 := by
  rw [show Lara.Strict.encodeAtomKey queryAtom =
      Lara.Strict.renderFrames ["A", "query", "L", Nat.repr 0] from rfl,
    renderFrames_utf8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [(by decide : ("A" : String).utf8ByteSize = 1),
    (by decide : ("query" : String).utf8ByteSize = 5),
    (by decide : ("L" : String).utf8ByteSize = 1)]
  have h1 := repr_utf8_le 1
  have h5 := repr_utf8_le 5
  have hR0 := repr_utf8_le 0
  have hR0' := repr_utf8_le ((Nat.repr 0).utf8ByteSize)
  omega

/-! ### Bounding the gadget numerals by the encoded formula -/

private theorem le_sum_of_mem {n : Nat} :
    ∀ {ns : List Nat}, n ∈ ns → n ≤ ns.sum := by
  intro ns h
  induction ns with
  | nil => simp at h
  | cons first rest ih =>
      rcases List.mem_cons.mp h with rfl | h
      · simp only [List.sum_cons]
        exact Nat.le_add_right _ _
      · simp only [List.sum_cons]
        exact Nat.le_trans (ih h) (Nat.le_add_left _ _)

private theorem sum_le_intercalate (sep : String) :
    ∀ l : List String,
      (l.map String.utf8ByteSize).sum ≤
        (String.intercalate sep l).utf8ByteSize
  | [] => by simp [String.intercalate_nil]
  | [t] => by simp [String.intercalate_singleton]
  | t :: u :: rest => by
      rw [String.intercalate_cons_cons, String.utf8ByteSize_append,
        String.utf8ByteSize_append]
      have ih := sum_le_intercalate sep (u :: rest)
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      omega

private theorem mem_le_intercalate {sep x : String} {l : List String}
    (hx : x ∈ l) :
    x.utf8ByteSize ≤ (String.intercalate sep l).utf8ByteSize :=
  Nat.le_trans
    (le_sum_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩))
    (sum_le_intercalate sep l)

private theorem signAtom_utf8 (l : Literal) :
    (Literal.signAtom l).utf8ByteSize = 1 := by
  cases hpos : l.positive <;> simp [Literal.signAtom, hpos] <;> decide

private theorem literal_encode_utf8 (l : Literal) :
    (Literal.encode l).utf8ByteSize =
      4 + (Nat.repr l.«variable»).utf8ByteSize := by
  simp only [Literal.encode, String.utf8ByteSize_append, signAtom_utf8,
    (by decide : ("(" : String).utf8ByteSize = 1),
    (by decide : (")" : String).utf8ByteSize = 1),
    (by decide : (" " : String).utf8ByteSize = 1)]
  omega

private theorem clause_encode_ge (c : Clause3) :
    15 ≤ (Clause3.encode c).utf8ByteSize := by
  have hsum := sum_le_intercalate " " (c.literals.map Literal.encode)
  have hsum15 :
      15 ≤ ((c.literals.map Literal.encode).map String.utf8ByteSize).sum := by
    simp only [Clause3.literals, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, literal_encode_utf8]
    have h1 := repr_utf8_pos c.first.«variable»
    have h2 := repr_utf8_pos c.second.«variable»
    have h3 := repr_utf8_pos c.third.«variable»
    omega
  simp only [Clause3.encode, String.utf8ByteSize_append]
  omega

private theorem literal_le_clause {c : Clause3} {l : Literal}
    (hl : l ∈ c.literals) :
    (Literal.encode l).utf8ByteSize ≤ (Clause3.encode c).utf8ByteSize := by
  have h := mem_le_intercalate (sep := " ")
    (List.mem_map_of_mem (f := Literal.encode) hl)
  simp only [Clause3.encode, String.utf8ByteSize_append]
  omega

private theorem clause_le_formula {φ : Formula3} {c : Clause3} (hc : c ∈ φ) :
    (Clause3.encode c).utf8ByteSize ≤ Formula3.byteSize φ := by
  have h := mem_le_intercalate (sep := " ")
    (List.mem_map_of_mem (f := Clause3.encode) hc)
  show _ ≤ (Formula3.encode φ).utf8ByteSize
  simp only [Formula3.encode, String.utf8ByteSize_append]
  omega

/-- Every occurring variable's numeral is visible in the encoded formula. -/
private theorem occurring_repr_le {φ : Formula3} {v : Nat}
    (hv : v ∈ φ.occurringVariables) :
    (Nat.repr v).utf8ByteSize ≤ Formula3.byteSize φ := by
  obtain ⟨l, hl, rfl⟩ := Formula3.exists_literal_of_mem_occurringVariables hv
  have hl' : l ∈ φ.flatMap Clause3.literals := hl
  obtain ⟨c, hcφ, hlc⟩ := List.mem_flatMap.mp hl'
  have h1 : (Nat.repr l.«variable»).utf8ByteSize ≤
      (Literal.encode l).utf8ByteSize := by
    rw [literal_encode_utf8]
    omega
  exact Nat.le_trans h1
    (Nat.le_trans (literal_le_clause hlc) (clause_le_formula hcφ))

private theorem sum_ge_mul {α : Type _} {f : α → Nat} {m : Nat} :
    ∀ {l : List α}, (∀ x ∈ l, m ≤ f x) → m * l.length ≤ (l.map f).sum := by
  intro l h
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hx := h x List.mem_cons_self
      have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      have hmul : m * (xs.length + 1) = m * xs.length + m :=
        Nat.mul_succ m xs.length
      omega

/-- Each clause costs at least 15 encoded bytes, plus the outer framing. -/
private theorem formula_size_ge (φ : Formula3) :
    15 * φ.length + 2 ≤ Formula3.byteSize φ := by
  have hsum := sum_ge_mul (l := φ.map Clause3.encode)
    (f := String.utf8ByteSize) (m := 15)
    (fun x hx => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
      exact clause_encode_ge c)
  have hinter := sum_le_intercalate " " (φ.map Clause3.encode)
  rw [List.length_map] at hsum
  show _ ≤ (Formula3.encode φ).utf8ByteSize
  simp only [Formula3.encode, String.utf8ByteSize_append,
    (by decide : ("(" : String).utf8ByteSize = 1),
    (by decide : (")" : String).utf8ByteSize = 1)]
  omega

/-! ### Assembling the three carrier contributions -/

private theorem sum_map_le {α : Type _} {f : α → Nat} {M : Nat} :
    ∀ {l : List α}, (∀ x ∈ l, f x ≤ M) → (l.map f).sum ≤ l.length * M := by
  intro l h
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hx := h x List.mem_cons_self
      have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      have hmul : (xs.length + 1) * M = xs.length * M + M :=
        Nat.succ_mul xs.length M
      omega

private theorem node_count_le (φ : Formula3) :
    (reduceCode φ).nodes.length ≤ Formula3.byteSize φ := by
  rw [reduce_nodes]
  have hV : Formula3.variableCount φ ≤ 3 * φ.length := by
    calc Formula3.variableCount φ
        ≤ φ.literals.length := Formula3.occurringVariables_length_le φ
      _ = 3 * φ.length := Formula3.literals_length φ
  have hB := formula_size_ge φ
  omega

private theorem node_key_le (φ : Formula3) {a : Lara.Atom}
    (ha : a ∈ (reduceCode φ).nodes) :
    (Lara.Strict.encodeAtomKey a).utf8ByteSize ≤
      4 * Formula3.byteSize φ + 60 := by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
  cases g with
  | negLit v =>
      have hv := occurring_repr_le (mem_occurring_of_negLit hg)
      have h := key_litAtom_le 0 v (by omega)
      show (Lara.Strict.encodeAtomKey (litAtom 0 v)).utf8ByteSize ≤ _
      omega
  | posLit v =>
      have hv := occurring_repr_le (mem_occurring_of_posLit hg)
      have h := key_litAtom_le 1 v (by omega)
      show (Lara.Strict.encodeAtomKey (litAtom 1 v)).utf8ByteSize ≤ _
      omega
  | clause j c =>
      have hj : j < φ.length :=
        Support.lt_of_getElem?_some
          (List.mk_mem_zipIdx_iff_getElem?.mp (mem_zipIdx_of_clause hg))
      have hLj := repr_utf8_le j
      have hB := formula_size_ge φ
      have h := key_clauseAtom_le j
      show (Lara.Strict.encodeAtomKey (clauseAtom j)).utf8ByteSize ≤ _
      omega
  | query =>
      have h := key_queryAtom_le
      show (Lara.Strict.encodeAtomKey queryAtom).utf8ByteSize ≤ _
      omega

private theorem nodeByteSize_le (φ : Formula3) :
    (reduceCode φ).nodeByteSize ≤
      (reduceCode φ).nodes.length * (4 * Formula3.byteSize φ + 60) := by
  unfold CarrierCode.nodeByteSize
  calc ((reduceCode φ).nodes.map fun node =>
        (Lara.Strict.encodeAtomKey node).utf8ByteSize).sum
      ≤ (reduceCode φ).nodes.length * (4 * Formula3.byteSize φ + 60) :=
        sum_map_le (fun a ha => node_key_le φ ha)

private theorem reduce_queryByteSize_le (φ : Formula3) :
    (reduceCode φ).queryByteSize ≤ Formula3.byteSize φ := by
  have hlen : (reduceCode φ).nodes.length = (gadgetNodes φ).length :=
    List.length_map ..
  have h0 : 0 < (gadgetNodes φ).length := by
    simp only [gadgetNodes, List.length_append, List.length_cons,
      List.length_nil]
    omega
  have hle := repr_utf8_le ((gadgetNodes φ).length - 1)
  have hn := node_count_le φ
  show (Nat.repr ((gadgetNodes φ).length - 1)).utf8ByteSize ≤ _
  omega

open Formula3 in
/-- **The frozen size bound.**  The carrier accounting measure of the
reduction output is quadratic in the encoded formula's byte length, with the
engineering-cleared constant `64`. -/
theorem reduce_byteSize (φ : Formula3) :
    (reduceCode φ).byteSize ≤ 64 * (Formula3.byteSize φ + 1) ^ 2 := by
  rw [byteSize_accounting]
  have hn := node_count_le φ
  have hnode := nodeByteSize_le φ
  have hquery := reduce_queryByteSize_le φ
  have hnode' : (reduceCode φ).nodeByteSize ≤
      Formula3.byteSize φ * (4 * Formula3.byteSize φ + 60) :=
    Nat.le_trans hnode (Nat.mul_le_mul_right _ hn)
  have hsq : (reduceCode φ).nodes.length ^ 2 ≤ Formula3.byteSize φ ^ 2 :=
    Nat.pow_le_pow_left hn 2
  have e1 : Formula3.byteSize φ * (4 * Formula3.byteSize φ + 60) =
      4 * (Formula3.byteSize φ * Formula3.byteSize φ) +
        60 * Formula3.byteSize φ := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm _ 60]
  have e2 : Formula3.byteSize φ ^ 2 =
      Formula3.byteSize φ * Formula3.byteSize φ := by
    rw [Nat.pow_succ, Nat.pow_one]
  have e3 : (Formula3.byteSize φ + 1) ^ 2 =
      Formula3.byteSize φ * Formula3.byteSize φ +
        2 * Formula3.byteSize φ + 1 := by
    rw [Nat.pow_succ, Nat.pow_one, Nat.add_mul, Nat.mul_add, Nat.mul_add]
    omega
  omega

/-! ## Satisfiability over the explicit syntax (Task 12, Step 1)

A Boolean assignment maps variable indices to truth values; a literal is true
when the assigned value matches its sign, a clause when some literal position
is true, a formula when every clause is.  `Formula3.Satisfiable` is the
existential the reduction-correctness theorem quantifies. -/

/-- Literal truth under an assignment: the assigned value matches the sign. -/
def Literal.eval (σ : Nat → Bool) (l : Literal) : Bool :=
  σ l.«variable» == l.positive

/-- Clause truth: some literal position is true. -/
def Clause3.eval (σ : Nat → Bool) (c : Clause3) : Bool :=
  c.literals.any (Literal.eval σ)

/-- Formula truth: every clause is true. -/
def Formula3.eval (σ : Nat → Bool) (φ : Formula3) : Bool :=
  φ.all (Clause3.eval σ)

/-- **Satisfiability of the explicit three-literal syntax.** -/
def Formula3.Satisfiable (φ : Formula3) : Prop :=
  ∃ σ : Nat → Bool, Formula3.eval σ φ = true

/-- `(x₀ ∨ ¬x₁ ∨ x₀)`: both signs and a repeated variable in one clause. -/
def positiveFixture : Formula3 :=
  [⟨⟨true, 0⟩, ⟨false, 1⟩, ⟨true, 0⟩⟩]

/-- `(x₀ ∨ x₀ ∨ x₀) ∧ (¬x₀ ∨ ¬x₀ ∨ ¬x₀)`: a complementary constant pair,
unsatisfiable because `x₀` would need both values. -/
def negativeFixture : Formula3 :=
  [⟨⟨true, 0⟩, ⟨true, 0⟩, ⟨true, 0⟩⟩,
   ⟨⟨false, 0⟩, ⟨false, 0⟩, ⟨false, 0⟩⟩]

/-- The positive fixture is satisfied by the all-true assignment. -/
theorem positiveFixture_satisfiable : Formula3.Satisfiable positiveFixture :=
  ⟨fun _ => true, rfl⟩

/-- Sign inversion: a sign-`0` literal is negative. -/
private theorem sign_zero_positive {l : Literal} (h : literalSign l = 0) :
    l.positive = false := by
  cases hpos : l.positive
  · rfl
  · simp [literalSign, hpos] at h

/-- Sign inversion: a sign-`1` literal is positive. -/
private theorem sign_one_positive {l : Literal} (h : literalSign l = 1) :
    l.positive = true := by
  cases hpos : l.positive
  · simp [literalSign, hpos] at h
  · rfl

private theorem signedLiteralOccursB_inv {c : Clause3} {s v : Nat}
    (h : signedLiteralOccursB c s v = true) :
    ∃ l ∈ c.literals, literalSign l = s ∧ l.«variable» = v := by
  rw [signedLiteralOccursB, List.any_eq_true] at h
  obtain ⟨l, hl, hb⟩ := h
  rw [Bool.and_eq_true] at hb
  exact ⟨l, hl, beq_iff_eq.mp hb.1, beq_iff_eq.mp hb.2⟩

/-! ## The decoded carrier (Task 12, bridge)

`FixedCredComplete (reduceCode φ)` speaks about complete extensions of
`eraseAF (reduceCode φ).decode`: node positions `0 .. |gadgetNodes φ| - 1`
with the intended matrix as the attack relation.  The bridge lemmas below
translate that framework's carrier and edges back into `gadgetNodes` /
`gadgetEdgeB`, so Steps 2–4 are pure AF combinatorics over the closed edge
case analysis — no checker or compiler reasoning. -/

private abbrev gadgetAF (φ : Formula3) : Lara.Grounded.AF :=
  Lara.Invariants.eraseAF (reduceCode φ).decode

private theorem gadgetAF_args (φ : Formula3) :
    (gadgetAF φ).args = List.range (gadgetNodes φ).length := by
  show List.range (reduceCode φ).decode.size = _
  rw [decode_size]
  show List.range ((gadgetNodes φ).map GadgetNode.conclusion).length = _
  rw [List.length_map]

private theorem mem_gadgetAF_args {φ : Formula3} {i : Nat} :
    i ∈ (gadgetAF φ).args ↔ i < (gadgetNodes φ).length := by
  rw [gadgetAF_args]
  exact List.mem_range

private theorem gadgetAF_attack_eq {φ : Formula3} {i j : Nat}
    {a b : GadgetNode} (ha : (gadgetNodes φ)[i]? = some a)
    (hb : (gadgetNodes φ)[j]? = some b) :
    (gadgetAF φ).attack i j = gadgetEdgeB a b := by
  show (reduceCode φ).decode.attack i j = _
  rw [decode_attack, reduceCode_matrix]
  simp only [List.getElem?_map, ha, hb, Option.map_some, Option.bind_some,
    Option.getD_some]

private theorem gadgetAF_attack_ranged {φ : Formula3} {i j : Nat}
    (h : (gadgetAF φ).attack i j = true) :
    ∃ a b, (gadgetNodes φ)[i]? = some a ∧ (gadgetNodes φ)[j]? = some b ∧
      gadgetEdgeB a b = true := by
  cases hi : (gadgetNodes φ)[i]? with
  | none =>
      exfalso
      have h' : (gadgetAF φ).attack i j = false := by
        show (reduceCode φ).decode.attack i j = false
        rw [decode_attack, reduceCode_matrix]
        simp [List.getElem?_map, hi]
      rw [h'] at h
      simp at h
  | some a =>
      cases hj : (gadgetNodes φ)[j]? with
      | none =>
          exfalso
          have h' : (gadgetAF φ).attack i j = false := by
            show (reduceCode φ).decode.attack i j = false
            rw [decode_attack, reduceCode_matrix]
            simp [List.getElem?_map, hi, hj]
          rw [h'] at h
          simp at h
      | some b =>
          refine ⟨a, b, rfl, rfl, ?_⟩
          rw [← gadgetAF_attack_eq hi hj]
          exact h

private theorem getElem?_concat_length {α : Type _} (xs : List α) (x : α) :
    (xs ++ [x])[(xs ++ [x]).length - 1]? = some x := by
  have h : (xs ++ [x]).length - 1 = xs.length := by
    rw [List.length_append]
    simp
  rw [h, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- The query is the last declared node. -/
private theorem gadgetNodes_last (φ : Formula3) :
    (gadgetNodes φ)[(gadgetNodes φ).length - 1]? = some GadgetNode.query := by
  unfold gadgetNodes
  exact getElem?_concat_length _ _

private theorem negLit_mem_gadgetNodes {φ : Formula3} {v : Nat}
    (hv : v ∈ φ.occurringVariables) : GadgetNode.negLit v ∈ gadgetNodes φ := by
  unfold gadgetNodes
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
    (List.mem_flatMap.mpr ⟨v, hv, by simp⟩))))

private theorem posLit_mem_gadgetNodes {φ : Formula3} {v : Nat}
    (hv : v ∈ φ.occurringVariables) : GadgetNode.posLit v ∈ gadgetNodes φ := by
  unfold gadgetNodes
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
    (List.mem_flatMap.mpr ⟨v, hv, by simp⟩))))

private theorem clause_mem_gadgetNodes {φ : Formula3} {c : Clause3} {j : Nat}
    (hcj : (c, j) ∈ φ.zipIdx) : GadgetNode.clause j c ∈ gadgetNodes φ := by
  unfold gadgetNodes
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
    (List.mem_map.mpr ⟨(c, j), hcj, rfl⟩))))

/-! ## Gadget-edge inversions (Task 12, Step 2)

`gadgetEdgeB` is a closed case analysis; these are the three inversions the
semantic arguments read edges through: only the complementary literal root
attacks a literal root, and only clause instances attack the query. -/

private theorem edge_into_negLit {a : GadgetNode} {v : Nat}
    (h : gadgetEdgeB a (.negLit v) = true) : a = .posLit v := by
  cases a with
  | posLit w =>
      have hw : w = v := beq_iff_eq.mp h
      rw [hw]
  | negLit w => exact absurd h (by simp [gadgetEdgeB])
  | clause j c => exact absurd h (by simp [gadgetEdgeB])
  | query => exact absurd h (by simp [gadgetEdgeB])

private theorem edge_into_posLit {a : GadgetNode} {v : Nat}
    (h : gadgetEdgeB a (.posLit v) = true) : a = .negLit v := by
  cases a with
  | negLit w =>
      have hw : w = v := beq_iff_eq.mp h
      rw [hw]
  | posLit w => exact absurd h (by simp [gadgetEdgeB])
  | clause j c => exact absurd h (by simp [gadgetEdgeB])
  | query => exact absurd h (by simp [gadgetEdgeB])

private theorem edge_into_query {a : GadgetNode}
    (h : gadgetEdgeB a .query = true) : ∃ j c, a = .clause j c := by
  cases a with
  | clause j c => exact ⟨j, c, rfl⟩
  | negLit v => exact absurd h (by simp [gadgetEdgeB])
  | posLit v => exact absurd h (by simp [gadgetEdgeB])
  | query => exact absurd h (by simp [gadgetEdgeB])

/-! ## Soundness (Task 12, Steps 2–3)

From a complete extension containing the query, read an assignment off the
chosen positive literal roots.  Conflict-freedom forbids a complementary pair
inside the extension (the mutual literal edges), and the query's defence
against every clause instance produces a chosen occurring literal per clause
— the satisfying literal. -/

/-- The assignment read off an extension: `v` is true exactly when the
extension contains a position holding the positive literal root of `v`.
(The `decide` is `GadgetNode`'s derived decidable equality at `Option`.) -/
private def extractAssignment (φ : Formula3) (E : List Nat) : Nat → Bool :=
  fun v => E.any fun i => decide ((gadgetNodes φ)[i]? = some (.posLit v))

private theorem extractAssignment_true {φ : Formula3} {E : List Nat} {v : Nat} :
    extractAssignment φ E v = true ↔
      ∃ i ∈ E, (gadgetNodes φ)[i]? = some (.posLit v) := by
  simp [extractAssignment, List.any_eq_true]

/-- Step 3: the extracted assignment satisfies the formula.  For each clause,
defence of the query against that clause's instance yields a chosen literal
root that occurs in the clause with its sign; a chosen negative root forces
the extracted value to `false` because a chosen positive twin would be a
conflict inside the extension. -/
private theorem eval_extract_of_complete {φ : Formula3} {E : List Nat}
    (hE : Lara.Semantics.Complete (gadgetAF φ) E)
    (hq : (reduceCode φ).query ∈ E) :
    Formula3.eval (extractAssignment φ E) φ = true := by
  obtain ⟨⟨-, hcf, hdef⟩, -⟩ := hE
  simp only [Formula3.eval, List.all_eq_true]
  intro c hcφ
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hcφ
  have hcj : (c, j) ∈ φ.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr hj
  obtain ⟨cj, hcjIdx⟩ := List.mem_iff_getElem?.mp (clause_mem_gadgetNodes hcj)
  have hq' : (gadgetNodes φ).length - 1 ∈ E := hq
  have hcjArg : cj ∈ (gadgetAF φ).args :=
    mem_gadgetAF_args.mpr (Support.lt_of_getElem?_some hcjIdx)
  have hattq :
      (gadgetAF φ).attack cj ((gadgetNodes φ).length - 1) = true := by
    rw [gadgetAF_attack_eq hcjIdx (gadgetNodes_last φ)]
    rfl
  obtain ⟨k, hkE, hkatt⟩ :=
    Grounded.defendedB_iff.mp (hdef _ hq') cj hcjArg hattq
  obtain ⟨gk, gcl, hgk, hgcl, hedge⟩ := gadgetAF_attack_ranged hkatt
  rw [hcjIdx] at hgcl
  have hgcl' := Option.some.inj hgcl
  subst hgcl'
  simp only [Clause3.eval, List.any_eq_true]
  cases gk with
  | negLit v =>
      obtain ⟨l, hl, hsign, hvar⟩ := signedLiteralOccursB_inv hedge
      have hneg := sign_zero_positive hsign
      have hval : extractAssignment φ E v = false := by
        cases hval : extractAssignment φ E v
        · rfl
        · exfalso
          obtain ⟨m, hmE, hm⟩ := extractAssignment_true.mp hval
          refine hcf m hmE k hkE ?_
          rw [gadgetAF_attack_eq hm hgk]
          simp [gadgetEdgeB]
      exact ⟨l, hl, by simp [Literal.eval, hvar, hval, hneg]⟩
  | posLit v =>
      obtain ⟨l, hl, hsign, hvar⟩ := signedLiteralOccursB_inv hedge
      have hpos := sign_one_positive hsign
      have hval : extractAssignment φ E v = true :=
        extractAssignment_true.mpr ⟨k, hkE, hgk⟩
      exact ⟨l, hl, by simp [Literal.eval, hvar, hval, hpos]⟩
  | clause j' c' => exact absurd hedge (by simp [gadgetEdgeB])
  | query => exact absurd hedge (by simp [gadgetEdgeB])

/-! ## Completeness (Task 12, Step 4)

From a satisfying assignment, the extension holding the query together with
exactly the asserted literal root per occurring variable is proved complete
*directly*: no chosen pair is joined by a gadget edge; chosen literal roots
defend themselves through the mutual pair; the query is defended because the
satisfying literal of each clause is chosen and occurs in it; and nothing
unchosen is defended, because every unchosen node has a *chosen* attacker
whose only counter-attacker is unchosen. -/

/-- The node the assignment asserts: the literal root matching the assigned
value, and the query.  Clause instances are never chosen. -/
private def chosenB (σ : Nat → Bool) : GadgetNode → Bool
  | .negLit v => !(σ v)
  | .posLit v => σ v
  | .clause _ _ => false
  | .query => true

/-- The model extension: every position whose node the assignment chooses. -/
private def modelExt (φ : Formula3) (σ : Nat → Bool) : List Nat :=
  (List.range (gadgetNodes φ).length).filter fun i =>
    ((gadgetNodes φ)[i]?.map (chosenB σ)).getD false

private theorem mem_modelExt {φ : Formula3} {σ : Nat → Bool} {i : Nat} :
    i ∈ modelExt φ σ ↔
      ∃ g, (gadgetNodes φ)[i]? = some g ∧ chosenB σ g = true := by
  constructor
  · intro hi
    rw [modelExt, List.mem_filter] at hi
    obtain ⟨-, hp⟩ := hi
    cases hg : (gadgetNodes φ)[i]? with
    | none => rw [hg] at hp; simp at hp
    | some g =>
        rw [hg] at hp
        exact ⟨g, rfl, by simpa using hp⟩
  · rintro ⟨g, hg, hc⟩
    rw [modelExt, List.mem_filter]
    exact ⟨List.mem_range.mpr (Support.lt_of_getElem?_some hg),
      by simp [hg, hc]⟩

private theorem query_mem_modelExt (φ : Formula3) (σ : Nat → Bool) :
    (reduceCode φ).query ∈ modelExt φ σ :=
  mem_modelExt.mpr ⟨.query, gadgetNodes_last φ, rfl⟩

/-- No gadget edge joins two chosen nodes: the only edges among choosable
nodes are the mutual literal pairs, and the assignment never chooses both
signs of one variable. -/
private theorem no_edge_between_chosen {σ : Nat → Bool} {a b : GadgetNode}
    (ha : chosenB σ a = true) (hb : chosenB σ b = true) :
    gadgetEdgeB a b = false := by
  cases a with
  | negLit v =>
      cases b with
      | negLit w => rfl
      | posLit w =>
          by_cases hvw : v = w
          · subst hvw
            simp only [chosenB] at ha hb
            rw [hb] at ha
            simp at ha
          · exact beq_eq_false_iff_ne.mpr hvw
      | clause j c => simp [chosenB] at hb
      | query => rfl
  | posLit v =>
      cases b with
      | negLit w =>
          by_cases hvw : v = w
          · subst hvw
            simp only [chosenB] at ha hb
            rw [ha] at hb
            simp at hb
          · exact beq_eq_false_iff_ne.mpr hvw
      | posLit w => rfl
      | clause j c => simp [chosenB] at hb
      | query => rfl
  | clause j c => simp [chosenB] at ha
  | query => cases b <;> rfl

/-- The satisfying literal of a true clause yields a chosen literal root
attacking the clause instance — where satisfiability enters the completeness
argument. -/
private theorem clause_chosen_attacker {φ : Formula3} {σ : Nat → Bool}
    {c : Clause3} {j : Nat} (hcj : (c, j) ∈ φ.zipIdx)
    (hc : Clause3.eval σ c = true) :
    ∃ (m : Nat) (g : GadgetNode), (gadgetNodes φ)[m]? = some g ∧
      chosenB σ g = true ∧ gadgetEdgeB g (.clause j c) = true := by
  simp only [Clause3.eval, List.any_eq_true] at hc
  obtain ⟨l, hl, hlv⟩ := hc
  have hcφ : c ∈ φ :=
    List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hcj)
  have hv : l.«variable» ∈ φ.occurringVariables :=
    Formula3.mem_occurringVariables (List.mem_flatMap_of_mem hcφ hl)
  cases hpos : l.positive with
  | true =>
      have hσv : σ l.«variable» = true := by
        simpa [Literal.eval, hpos] using hlv
      obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp (posLit_mem_gadgetNodes hv)
      refine ⟨m, .posLit l.«variable», hm, by simp [chosenB, hσv], ?_⟩
      show signedLiteralOccursB c 1 l.«variable» = true
      rw [signedLiteralOccursB, List.any_eq_true]
      exact ⟨l, hl, by simp [literalSign, hpos]⟩
  | false =>
      have hσv : σ l.«variable» = false := by
        simpa [Literal.eval, hpos] using hlv
      obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp (negLit_mem_gadgetNodes hv)
      refine ⟨m, .negLit l.«variable», hm, by simp [chosenB, hσv], ?_⟩
      show signedLiteralOccursB c 0 l.«variable» = true
      rw [signedLiteralOccursB, List.any_eq_true]
      exact ⟨l, hl, by simp [literalSign, hpos]⟩

/-- Every unchosen node has a chosen attacker: the asserted twin for an
unchosen literal root, the satisfying literal for a clause instance.  (The
query is always chosen.) -/
private theorem unchosen_has_chosen_attacker {φ : Formula3} {σ : Nat → Bool}
    (hσ : Formula3.eval σ φ = true) {b : Nat} {g : GadgetNode}
    (hgb : (gadgetNodes φ)[b]? = some g) (hun : chosenB σ g = false) :
    ∃ (m : Nat) (g' : GadgetNode), (gadgetNodes φ)[m]? = some g' ∧
      chosenB σ g' = true ∧ gadgetEdgeB g' g = true := by
  have hmem : g ∈ gadgetNodes φ := List.mem_of_getElem? hgb
  cases g with
  | negLit v =>
      have hv : σ v = true := by simpa [chosenB] using hun
      obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp
        (posLit_mem_gadgetNodes (mem_occurring_of_negLit hmem))
      exact ⟨m, .posLit v, hm, by simp [chosenB, hv], by simp [gadgetEdgeB]⟩
  | posLit v =>
      have hv : σ v = false := by simpa [chosenB] using hun
      obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp
        (negLit_mem_gadgetNodes (mem_occurring_of_posLit hmem))
      exact ⟨m, .negLit v, hm, by simp [chosenB, hv], by simp [gadgetEdgeB]⟩
  | clause j c =>
      have hcj := mem_zipIdx_of_clause hmem
      have hcφ : c ∈ φ :=
        List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hcj)
      have hceval : Clause3.eval σ c = true := by
        simp only [Formula3.eval, List.all_eq_true] at hσ
        exact hσ c hcφ
      exact clause_chosen_attacker hcj hceval
  | query => simp [chosenB] at hun

private theorem modelExt_conflictFree (φ : Formula3) (σ : Nat → Bool) :
    Grounded.ConflictFree (gadgetAF φ) (modelExt φ σ) := by
  intro i hi k hk hatt
  obtain ⟨gi, hgi, hci⟩ := mem_modelExt.mp hi
  obtain ⟨gk, hgk, hck⟩ := mem_modelExt.mp hk
  obtain ⟨gi', gk', hgi', hgk', hedge⟩ := gadgetAF_attack_ranged hatt
  rw [hgi] at hgi'
  rw [hgk] at hgk'
  obtain rfl := Option.some.inj hgi'
  obtain rfl := Option.some.inj hgk'
  rw [no_edge_between_chosen hci hck] at hedge
  simp at hedge

/-- Each chosen node is defended: literal roots counter their sole attacker
(the complementary root) themselves, and the query's clause attackers are
each countered by the clause's chosen satisfying literal. -/
private theorem modelExt_defended {φ : Formula3} {σ : Nat → Bool}
    (hσ : Formula3.eval σ φ = true) :
    ∀ i ∈ modelExt φ σ,
      Grounded.defendedB (gadgetAF φ) (modelExt φ σ) i = true := by
  intro i hi
  obtain ⟨g, hgi, hchosen⟩ := mem_modelExt.mp hi
  rw [Grounded.defendedB_iff]
  intro b hb hab
  obtain ⟨gb, g', hgb, hg', hedge⟩ := gadgetAF_attack_ranged hab
  rw [hgi] at hg'
  obtain rfl := Option.some.inj hg'
  cases g with
  | negLit v =>
      obtain rfl := edge_into_negLit hedge
      refine ⟨i, hi, ?_⟩
      rw [gadgetAF_attack_eq hgi hgb]
      simp [gadgetEdgeB]
  | posLit v =>
      obtain rfl := edge_into_posLit hedge
      refine ⟨i, hi, ?_⟩
      rw [gadgetAF_attack_eq hgi hgb]
      simp [gadgetEdgeB]
  | clause j c => simp [chosenB] at hchosen
  | query =>
      obtain ⟨j, c, rfl⟩ := edge_into_query hedge
      have hcj : (c, j) ∈ φ.zipIdx :=
        mem_zipIdx_of_clause (List.mem_of_getElem? hgb)
      have hcφ : c ∈ φ :=
        List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hcj)
      have hceval : Clause3.eval σ c = true := by
        simp only [Formula3.eval, List.all_eq_true] at hσ
        exact hσ c hcφ
      obtain ⟨m, g', hm, hchosen', hatt⟩ := clause_chosen_attacker hcj hceval
      refine ⟨m, mem_modelExt.mpr ⟨g', hm, hchosen'⟩, ?_⟩
      rw [gadgetAF_attack_eq hm hgb]
      exact hatt

/-- Defence closure: a defended carrier node is chosen.  Contrapositively, an
unchosen node has a chosen attacker, and any counter-attack on a chosen node
from inside the extension would join two chosen nodes by an edge. -/
private theorem modelExt_closed {φ : Formula3} {σ : Nat → Bool}
    (hσ : Formula3.eval σ φ = true) :
    ∀ b ∈ (gadgetAF φ).args,
      Grounded.defendedB (gadgetAF φ) (modelExt φ σ) b = true →
        b ∈ modelExt φ σ := by
  intro b hb hdefb
  obtain ⟨g, hgb⟩ := Support.getElem?_some_of_lt (gadgetNodes φ) b
    (mem_gadgetAF_args.mp hb)
  cases hch : chosenB σ g with
  | true => exact mem_modelExt.mpr ⟨g, hgb, hch⟩
  | false =>
      exfalso
      obtain ⟨m, g', hm, hch', hatt⟩ :=
        unchosen_has_chosen_attacker hσ hgb hch
      have hmarg : m ∈ (gadgetAF φ).args :=
        mem_gadgetAF_args.mpr (Support.lt_of_getElem?_some hm)
      have hmatt : (gadgetAF φ).attack m b = true := by
        rw [gadgetAF_attack_eq hm hgb]
        exact hatt
      obtain ⟨k, hkE, hkatt⟩ :=
        Grounded.defendedB_iff.mp hdefb m hmarg hmatt
      obtain ⟨gk, hgk, hchk⟩ := mem_modelExt.mp hkE
      obtain ⟨gk', g'', hgk', hg'', hkedge⟩ := gadgetAF_attack_ranged hkatt
      rw [hgk] at hgk'
      rw [hm] at hg''
      obtain rfl := Option.some.inj hgk'
      obtain rfl := Option.some.inj hg''
      rw [no_edge_between_chosen hchk hch'] at hkedge
      simp at hkedge

/-- Step 4 assembled: the model extension is a complete extension, proved
against the full definition with no admissible-to-complete detour. -/
private theorem modelExt_complete {φ : Formula3} {σ : Nat → Bool}
    (hσ : Formula3.eval σ φ = true) :
    Lara.Semantics.Complete (gadgetAF φ) (modelExt φ σ) := by
  refine ⟨⟨?_, modelExt_conflictFree φ σ, modelExt_defended hσ⟩,
    modelExt_closed hσ⟩
  intro i hi
  obtain ⟨g, hg, -⟩ := mem_modelExt.mp hi
  exact mem_gadgetAF_args.mpr (Support.lt_of_getElem?_some hg)

/-! ## The reduction package (Task 12, Step 5)

The frozen end-to-end theorem, stated with the class-membership and size
obligations *adjacent by design*: correctness of the reduction may not be
quoted without the realization promise and the quadratic size bound, so the
paper-level complexity bookkeeping cites all three from one place.
NP-completeness itself is not stated inside Lean; only these mechanized
obligations are. -/

/-- **Fixed-policy 3SAT reduction correctness.**  The explicit formula is
satisfiable exactly when the reduction output credulously accepts its query
under complete semantics. -/
theorem reduce_correct (φ : Formula3) :
    Formula3.Satisfiable φ ↔ FixedCredComplete (reduceCode φ) := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨modelExt φ σ, modelExt_complete hσ, query_mem_modelExt φ σ⟩
  · rintro ⟨E, hE, hq⟩
    exact ⟨extractAssignment φ E, eval_extract_of_complete hE hq⟩

/-- Class membership, quoted adjacent to correctness: every reduction output
is realizable in the fixed M2b context (`reduce_realizable`). -/
theorem reduce_correct_realizable (φ : Formula3) :
    M2bPromise (reduceCode φ) :=
  reduce_realizable φ

open Formula3 in
/-- The node count, quoted adjacent to correctness (`reduce_nodes`). -/
theorem reduce_correct_nodes (φ : Formula3) :
    (reduceCode φ).nodes.length = 2 * variableCount φ + φ.length + 1 :=
  reduce_nodes φ

open Formula3 in
/-- The size bound, quoted adjacent to correctness (`reduce_byteSize`). -/
theorem reduce_correct_byteSize (φ : Formula3) :
    (reduceCode φ).byteSize ≤ 64 * (Formula3.byteSize φ + 1) ^ 2 :=
  reduce_byteSize φ

/-! ## Executable fixtures through the whole chain (Task 12, Step 1 cont.)

Both fixtures are decided by the executable acceptance decider on their
compiled carriers, and the unsatisfiability of the negative fixture is
*derived* from that executable verdict through `fixedCredCompleteB_iff` and
`reduce_correct` — the decision, the enumeration adequacy, and the reduction
correctness are exercised in one chain.

Kernel-`decide` cost caution: `decide` on `fixedCredCompleteB` makes the
kernel enumerate every subset of the carrier (`2^n` complete-semantics
candidates for an `n`-node carrier), so keep fixtures at roughly seven nodes
or fewer. -/

/-- The positive fixture's carrier accepts its query, executably. -/
theorem positiveFixture_accepted :
    fixedCredCompleteB (reduceCode positiveFixture) = true := by decide

/-- The negative fixture's carrier rejects its query, executably. -/
theorem negativeFixture_rejected :
    fixedCredCompleteB (reduceCode negativeFixture) = false := by decide

/-- Unsatisfiability of the negative fixture, pulled back from the executable
carrier verdict through the mechanized chain. -/
theorem negativeFixture_unsatisfiable :
    ¬ Formula3.Satisfiable negativeFixture := by
  intro h
  have hB : fixedCredCompleteB (reduceCode negativeFixture) = true :=
    (fixedCredCompleteB_iff (reduceCode negativeFixture)).mpr
      ((reduce_correct negativeFixture).mp h)
  rw [negativeFixture_rejected] at hB
  simp at hB

/-! ## Class-membership negative control (Task 12, Step 6)

The correctness theorem is about the *realizable* class, not unrestricted
AFs.  Witness: the one-node self-edge carrier labelled `g(0)` is not
`M2bPromise`-realizable.  A realization would transport the self-edge through
the structured isomorphism onto the compiled unit, where `Compile.edge_iff`
demands a typed declared attack; the fixed policy's sole rule concludes a
`clause` atom, so a node concluding `g(0)` is a leaf, forcing the attack to
be an undermine whose contrary instance relates `g(0)` to `g(0)` — and no
`m2bPolicy` contrary row's head matches the `g` predicate.  (Undercuts are
impossible outright: the policy declares no exceptions.) -/

/-- No contrary row licenses `g(0) → g(0)`: the six rows' heads are `d`,
`b`, `lit` (three rows — the two mutual literal orientations and the
occurrence row), and `clause` — none unifies with `g`. -/
private theorem g_not_contrary_g :
    Lara.Attack.contraryMatchB id m2bPolicy.defeat (gAtom 0) (gAtom 0) =
      false := by decide

/-- The fixed policy's rule table holds exactly the clause rule. -/
private theorem m2bRuleLookup_inv {rn : RuleId} {r : Rule}
    (h : m2bPolicy.ruleLookup rn = some r) : r = m2bClauseRule := by
  have h' : (if m2bClauseRuleId = rn then some m2bClauseRule else none) =
      some r := h
  split at h'
  · exact (Option.some.inj h').symm
  · exact absurd h' (by simp)

/-- Under the fixed policy only a leaf concludes `g(0)`: the sole rule's
conclusion instantiates to a `clause` atom. -/
private theorem hasSupport_gAtom_leaf
    {Gamma : LeafId → Option Lara.Atom}
    {CertOk : BackendId → Digest → CertRef → List Lara.Atom → Lara.Atom →
      Prop}
    {w : SupportTerm} {O : List QuestionId}
    (h : Support.HasSupport id m2bPolicy.ruleLookup Gamma CertOk w
      (gAtom 0) O) :
    ∃ l, w = .leaf l ∧ Gamma l = some (gAtom 0) := by
  cases h with
  | leaf hΓ => exact ⟨_, rfl, hΓ⟩
  | inst hside hprems hdis =>
      exfalso
      have hc := hside.concl
      rw [m2bRuleLookup_inv hside.rule] at hc
      unfold Support.instAPat at hc
      cases hts : Support.instPats _ m2bClauseRule.concl.args with
      | none => rw [hts] at hc; exact absurd hc (by simp)
      | some ts =>
          rw [hts] at hc
          simp only [Option.map_some] at hc
          have hatom := Option.some.inj hc
          rw [show m2bClauseRule.concl.pred.name = "clause" from rfl]
            at hatom
          exact absurd hatom (by simp [gAtom])

/-- A one-node self-attacking carrier labelled `g(0)`. -/
def selfEdgeCode : CarrierCode :=
  { nodes := [gAtom 0]
    matrix := [[true]]
    query := 0
    square := ⟨rfl, fun row hrow => by
      rw [List.mem_singleton] at hrow
      rw [hrow]
      rfl⟩
    query_lt := Nat.one_pos }

/-- **The negative control.**  The unrestricted self-edge carrier lies
outside the fixed realizable class, so `reduce_correct` is a theorem about
that class and not about arbitrary AFs. -/
theorem selfEdgeCode_not_realizable : ¬ M2bPromise selfEdgeCode := by
  rintro ⟨R⟩
  -- Transport the self-edge and the label through the isomorphism.
  have hattack : (Lara.Invariants.compileUnit R.accepted).attack
      (R.compiled_iso.nodeEquiv.invFun 0)
      (R.compiled_iso.nodeEquiv.invFun 0) = true := by
    rw [R.compiled_iso.attacks, R.compiled_iso.nodeEquiv.right_inv]
    rfl
  have hlabel : (Lara.Invariants.compileUnit R.accepted).nodes[
      R.compiled_iso.nodeEquiv.invFun 0]? = some (gAtom 0) := by
    rw [R.compiled_iso.labels, R.compiled_iso.nodeEquiv.right_inv]
    rfl
  -- Identify the compiled node behind that position.
  rw [show (Lara.Invariants.compileUnit R.accepted).nodes =
    R.accepted.nodes.map (·.conclusion) from rfl, List.getElem?_map]
    at hlabel
  cases hnd : R.accepted.nodes[R.compiled_iso.nodeEquiv.invFun 0]? with
  | none => rw [hnd] at hlabel; exact absurd hlabel (by simp)
  | some nd =>
      rw [hnd, Option.map_some] at hlabel
      have hconc : nd.conclusion = gAtom 0 := Option.some.inj hlabel
      have harg : R.accepted.program.args[
          R.compiled_iso.nodeEquiv.invFun 0]? = some nd.term := by
        rw [← R.accepted.nodes_terms, List.getElem?_map, hnd,
          Option.map_some]
      -- The transported edge is a compiled closure edge.
      change Compile.edgeB R.accepted.program _ _ = true at hattack
      obtain ⟨-, -, k, hk, htyped, hsrc, t, hocc, hcont⟩ :=
        (Compile.edge_iff R.accepted.program nd.term nd.term).mp
          ((Compile.edgeB_iff harg harg).mp hattack)
      -- The node's support pins its term to a `g(0)` leaf.
      have hvalid : Support.HasSupport id m2bPolicy.ruleLookup R.Gamma
          (Support.certOkOf m2bRegistry) nd.term (gAtom 0) [] := by
        have h := nd.valid
        rw [hconc] at h
        simpa only [R.policy_eq] using h
      obtain ⟨l, hleaf, hΓl⟩ := hasSupport_gAtom_leaf hvalid
      rw [hleaf] at hcont
      have ht := contains_leaf_iff.mp hcont
      subst ht
      rw [R.policy_eq] at htyped
      rw [hleaf] at hsrc
      cases k with
      | rebut w u =>
          simp only [Compile.AttackOcc] at hocc
          subst hocc
          cases htyped
      | undercut w u π =>
          cases htyped with
          | undercut _ _ _ _ hexc _ _ =>
              exact absurd hexc (by simp [m2bPolicy])
      | undermine w u π =>
          cases htyped with
          | undermine hw hocc2 hΓ2 hcon =>
              rename_i l2 pl Cw Ow
              simp only [Compile.AttackOcc] at hocc
              have hl2 : l2 = l := by
                have h := Option.some.inj (hocc2.symm.trans hocc)
                injection h
              rw [hl2, hΓl] at hΓ2
              have hpl : pl = gAtom 0 := (Option.some.inj hΓ2).symm
              have hwl : w = SupportTerm.leaf l := hsrc
              rw [hwl] at hw
              cases hw with
              | leaf hΓw =>
                  have hCw : Cw = gAtom 0 :=
                    Option.some.inj (hΓw.symm.trans hΓl)
                  rw [hCw, hpl] at hcon
                  have hB := (Lara.Attack.contraryMatchB_iff id
                    m2bPolicy.defeat (gAtom 0) (gAtom 0)).mpr hcon
                  rw [g_not_contrary_g] at hB
                  simp at hB

end Lara.Complexity
