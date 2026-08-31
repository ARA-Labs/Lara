import Lara.Complexity.Context
import Lara.Realizability
import Lara.Semantics

namespace Lara.Complexity

/-- A signed propositional variable. -/
structure Literal where
  positive : Bool
  «variable» : Nat
deriving DecidableEq

/-- A clause with exactly three literal positions. -/
structure Clause3 where
  first : Literal
  second : Literal
  third : Literal
deriving DecidableEq

abbrev Formula3 := List Clause3

namespace Literal

/-- The canonical sign atom: positive is `1`, negative is `0`. -/
def signAtom (literal : Literal) : String :=
  if literal.positive then "1" else "0"

/-- The canonical S-expression for one literal, represented textually as
`(SIGN VARIABLE)`. Both atoms are canonical decimal strings. -/
def encode (literal : Literal) : String :=
  "(" ++ literal.signAtom ++ " " ++ Nat.repr literal.«variable» ++ ")"

end Literal

namespace Clause3

/-- The three literals in positional order. -/
def literals (clause : Clause3) : List Literal :=
  [clause.first, clause.second, clause.third]

/-- The canonical S-expression for one clause. -/
def encode (clause : Clause3) : String :=
  "(" ++ String.intercalate " " (clause.literals.map Literal.encode) ++ ")"

end Clause3

private def dedupNats : List Nat → List Nat
  | [] => []
  | n :: ns =>
      let rest := dedupNats ns
      if Lara.Support.memB n rest then rest else n :: rest

private theorem dedupNats_nodup :
    ∀ ns, (dedupNats ns).Nodup := by
  intro ns
  induction ns with
  | nil => simp [dedupNats]
  | cons n ns ih =>
      simp only [dedupNats]
      split
      · exact ih
      · apply List.nodup_cons.mpr
        rename_i hnot
        exact ⟨fun hmem => hnot (Lara.Support.memB_iff.mpr hmem), ih⟩

namespace Formula3

/-- All literal occurrences in clause order and then field order. -/
def literals (formula : Formula3) : List Literal :=
  formula.flatMap Clause3.literals

/-- The duplicate-free list of variables occurring in the formula, in a
deterministic occurrence-derived order. -/
def occurringVariables (formula : Formula3) : List Nat :=
  dedupNats (formula.literals.map (·.«variable»))

/-- The number of distinct variables occurring in the formula. -/
def variableCount (formula : Formula3) : Nat :=
  formula.occurringVariables.length

/-- The canonical S-expression for the formula: an outer list of its encoded
three-literal clauses. -/
def encode (formula : Formula3) : String :=
  "(" ++ String.intercalate " " (formula.map Clause3.encode) ++ ")"

/-- Exact UTF-8 byte length of the canonical S-expression. It counts sign and
decimal-index atoms, spaces, clause delimiters, and the outer framing. -/
def byteSize (formula : Formula3) : Nat :=
  formula.encode.utf8ByteSize

theorem occurringVariables_nodup (formula : Formula3) :
    formula.occurringVariables.Nodup :=
  dedupNats_nodup _

end Formula3

/-- Finite encoding of a labelled argumentation framework. `square` makes the
matrix dimensions explicit, and `query_lt` makes the queried node a carrier
member. -/
structure CarrierCode where
  nodes    : List Lara.Atom
  matrix   : List (List Bool)
  query    : Nat
  square   : matrix.length = nodes.length ∧
    ∀ row ∈ matrix, row.length = nodes.length
  query_lt : query < nodes.length

namespace CarrierCode

/-- Decode by retaining node order and looking up both matrix coordinates
totally. Any out-of-range coordinate denotes no attack. -/
def decode (code : CarrierCode) : Lara.Invariants.StructuredAF :=
  { nodes := code.nodes
    attack := fun i j =>
      ((code.matrix[i]?.bind fun row => row[j]?).getD false) }

/-- Stipulated contribution of the framed atom keys to the accounting
measure. -/
def nodeByteSize (code : CarrierCode) : Nat :=
  (code.nodes.map fun node =>
    (Lara.Strict.encodeAtomKey node).utf8ByteSize).sum

/-- Stipulated contribution of the Boolean matrix: one unit per entry. -/
def matrixByteSize (code : CarrierCode) : Nat :=
  (code.matrix.map List.length).sum

/-- Stipulated contribution of the canonical decimal query index. -/
def queryByteSize (code : CarrierCode) : Nat :=
  (Nat.repr code.query).utf8ByteSize

/-- Frozen accounting measure for the finite carrier representation: one
framing unit, the UTF-8 sizes of the atom keys and query index, and one unit per
Boolean matrix entry.  No `CarrierCode` serializer is defined, so this is not a
claim about the byte length of a serialized wire format. -/
def byteSize (code : CarrierCode) : Nat :=
  1 + code.nodeByteSize + code.matrixByteSize + code.queryByteSize

end CarrierCode

/-- The fixed restricted-class promise. -/
def M2bPromise (x : CarrierCode) : Prop :=
  Lara.Realizability.Realizable id m2bSigma m2bPolicy m2bRegistry x.decode

/-- Credulous acceptance of the encoded query under complete semantics. -/
def FixedCredComplete (x : CarrierCode) : Prop :=
  ∃ E, Lara.Semantics.Complete (Lara.Invariants.eraseAF x.decode) E ∧
    x.query ∈ E

/-- The executable complete-semantics decision uses the bundled reference
enumerator and its existing acceptance profile. -/
def fixedCredCompleteB (x : CarrierCode) : Bool :=
  (Lara.Semantics.profile Lara.Semantics.completeSem
    (Lara.Invariants.eraseAF x.decode) x.query).inSome

@[simp] theorem decode_size (x : CarrierCode) :
    x.decode.size = x.nodes.length := rfl

@[simp] theorem decode_attack (x : CarrierCode) (i j : Nat) :
    x.decode.attack i j =
      ((x.matrix[i]?.bind fun row => row[j]?).getD false) := rfl

theorem erase_decode_args_nodup (x : CarrierCode) :
    (Lara.Invariants.eraseAF x.decode).args.Nodup := by
  change (List.range x.nodes.length).Nodup
  exact List.nodup_range

/-- The bundled complete enumerator decides exactly the existential complete
extension formulation. No second implementation of complete semantics is
introduced. -/
theorem fixedCredCompleteB_iff (x : CarrierCode) :
    fixedCredCompleteB x = true ↔ FixedCredComplete x := by
  unfold fixedCredCompleteB FixedCredComplete Lara.Semantics.profile
  constructor
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨E, hE, hquery⟩ := h
    refine ⟨E, ?_, Lara.Grounded.memB_iff.mp hquery⟩
    exact ((Lara.Semantics.completeSem.sound
      (Lara.Invariants.eraseAF x.decode) (erase_decode_args_nodup x) E).mp hE).2
  · rintro ⟨E, hcomplete, hquery⟩
    obtain ⟨E', hcandidate, hmembers⟩ :=
      Lara.Semantics.exists_candidate_ext hcomplete.1.1
    have hcomplete' :
        Lara.Semantics.Complete (Lara.Invariants.eraseAF x.decode) E' :=
      Lara.Semantics.complete_congr (fun a => (hmembers a).symm) hcomplete
    have hE' : E' ∈ Lara.Semantics.completeSem.enumerate
        (Lara.Invariants.eraseAF x.decode) :=
      (Lara.Semantics.completeSem.sound
        (Lara.Invariants.eraseAF x.decode) (erase_decode_args_nodup x) E').mpr
        ⟨Lara.Semantics.mem_candidates.mp hcandidate, hcomplete'⟩
    rw [List.any_eq_true]
    exact ⟨E', hE', Lara.Grounded.memB_iff.mpr ((hmembers x.query).mpr hquery)⟩

private theorem rowLengthSum_eq_mul (rows : List (List Bool)) (n : Nat)
    (hrows : ∀ row ∈ rows, row.length = n) :
    (rows.map List.length).sum = rows.length * n := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      have hrow : row.length = n := hrows row (by simp)
      have hrest : ∀ tail ∈ rows, tail.length = n := by
        intro tail htail
        exact hrows tail (by simp [htail])
      simp [hrow, ih hrest, Nat.succ_mul, Nat.add_comm]

/-- `square` makes the matrix contribution exactly the square of the carrier
length. -/
theorem matrixByteSize_eq_square (x : CarrierCode) :
    x.matrixByteSize = x.nodes.length ^ 2 := by
  calc
    x.matrixByteSize = x.matrix.length * x.nodes.length :=
      rowLengthSum_eq_mul x.matrix x.nodes.length x.square.2
    _ = x.nodes.length * x.nodes.length := by rw [x.square.1]
    _ = x.nodes.length ^ 2 := by simp [Nat.pow_succ]

/-- The accounting identity after eliminating the matrix dimensions via
`square`. -/
theorem byteSize_accounting (x : CarrierCode) :
    x.byteSize =
      1 + x.nodeByteSize + x.nodes.length ^ 2 + x.queryByteSize := by
  unfold CarrierCode.byteSize
  rw [matrixByteSize_eq_square]

/-- Every carrier-code accounting measure includes its framing unit. -/
theorem byteSize_pos (x : CarrierCode) : 0 < x.byteSize := by
  unfold CarrierCode.byteSize
  omega

private theorem nat_le_sum_of_mem {n : Nat} :
    ∀ {ns : List Nat}, n ∈ ns → n ≤ ns.sum := by
  intro ns h
  induction ns with
  | nil => simp at h
  | cons first rest ih =>
      simp only [List.mem_cons] at h
      simp only [List.sum_cons]
      rcases h with h | h
      · subst first
        exact Nat.le_add_right _ _
      · exact Nat.le_trans (ih h) (Nat.le_add_left _ _)

/-- The accounting includes the complete UTF-8 key of every declared node. -/
theorem nodeKeyByteSize_le (x : CarrierCode) {node : Lara.Atom}
    (hnode : node ∈ x.nodes) :
    (Lara.Strict.encodeAtomKey node).utf8ByteSize ≤ x.byteSize := by
  have hmem : (Lara.Strict.encodeAtomKey node).utf8ByteSize ∈
      (x.nodes.map fun item =>
        (Lara.Strict.encodeAtomKey item).utf8ByteSize) :=
    List.mem_map.mpr ⟨node, hnode, rfl⟩
  have hsum := nat_le_sum_of_mem hmem
  unfold CarrierCode.byteSize CarrierCode.nodeByteSize
  omega

/-- The accounting includes the complete canonical decimal query index. -/
theorem queryByteSize_le (x : CarrierCode) :
    (Nat.repr x.query).utf8ByteSize ≤ x.byteSize := by
  unfold CarrierCode.byteSize CarrierCode.queryByteSize
  omega

end Lara.Complexity
