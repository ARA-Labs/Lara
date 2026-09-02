/-
The formula-indexed M2b gadget behind a closed leaf vocabulary (issue #209,
decision D8).

`rawUnitOfFormula` and its generators moved here unchanged in value from
`Lara.Examples.Complexity.Realization`, because the post-gate `reduceCode` and
`Reduction.lean` are library code and library code must not import `Examples`.
The leaf namespace is the closed sum `GadgetLeaf` with the single injective
spelling table `GadgetLeaf.encode`; the string builders
(`negativeLiteralLeafId` and friends) are definitionally
`GadgetLeaf.encode ∘ constructor`, so exactly one spelling table exists.  The
closed spelling fixtures below pin every constructor family directly against
literal `LeafId` strings, independently of the merged structural fixture.
-/

import Lara.Complexity.Encoding
import Lara.Complexity.Numeral

namespace Lara.Complexity

open Lara Lara.Support Lara.Attack

/-! ## The closed leaf vocabulary (D8) -/

/-- Closed leaf vocabulary of the formula gadget.  Every leaf identifier the
gadget emits is `GadgetLeaf.encode` of exactly one constructor. -/
inductive GadgetLeaf where
  | negLit (varIdx : Nat)
  | posLit (varIdx : Nat)
  | occurrence (clauseIndex position : Nat)
  | query
deriving DecidableEq

/-- The single spelling table for gadget leaf identifiers. -/
def GadgetLeaf.encode : GadgetLeaf → LeafId
  | .negLit v => ⟨"literal-negative-" ++ Nat.repr v⟩
  | .posLit v => ⟨"literal-positive-" ++ Nat.repr v⟩
  | .occurrence j p => ⟨"occurrence-" ++ Nat.repr j ++ "-" ++ Nat.repr p⟩
  | .query => ⟨"formula-query"⟩

/-! ## The moved gadget generators (values unchanged) -/

/-- Canonical decimal numeral term. -/
def numTerm (n : Nat) : Lara.Term := .num (Nat.repr n)

/-- Sign of a literal: positive is `1`, negative is `0`. -/
def literalSign (literal : Literal) : Nat :=
  if literal.positive then 1 else 0

/-- First-match association lookup over a finite leaf table. -/
def lookupLeaf : List (LeafId × Lara.Atom) → LeafId → Option Lara.Atom
  | [], _ => none
  | (candidate, atom) :: rest, leaf =>
      if candidate = leaf then some atom else lookupLeaf rest leaf

def negativeLiteralLeafId (varIdx : Nat) : LeafId :=
  (GadgetLeaf.negLit varIdx).encode

def positiveLiteralLeafId (varIdx : Nat) : LeafId :=
  (GadgetLeaf.posLit varIdx).encode

def literalLeafId (literal : Literal) : LeafId :=
  if literal.positive then positiveLiteralLeafId literal.«variable»
  else negativeLiteralLeafId literal.«variable»

def occurrenceLeafId (clauseIndex position : Nat) : LeafId :=
  (GadgetLeaf.occurrence clauseIndex position).encode

def queryLeafId : LeafId := GadgetLeaf.query.encode

/-- Closed fixtures for the public leaf-ID spelling contract.  The occurrence
case uses two multi-digit indices to pin both separators. -/
example : negativeLiteralLeafId 12 = ⟨"literal-negative-12"⟩ := by rfl
example : positiveLiteralLeafId 34 = ⟨"literal-positive-34"⟩ := by rfl
example : occurrenceLeafId 12 34 = ⟨"occurrence-12-34"⟩ := by rfl
example : queryLeafId = ⟨"formula-query"⟩ := by rfl

def negativeLiteralArg (varIdx : Nat) : SupportTerm :=
  .leaf (negativeLiteralLeafId varIdx)

def positiveLiteralArg (varIdx : Nat) : SupportTerm :=
  .leaf (positiveLiteralLeafId varIdx)

def literalArg (literal : Literal) : SupportTerm :=
  .leaf (literalLeafId literal)

def queryArg : SupportTerm := .leaf queryLeafId

def literalLeafEntries (varIdx : Nat) : List (LeafId × Lara.Atom) :=
  [ (negativeLiteralLeafId varIdx, litAtom 0 varIdx)
  , (positiveLiteralLeafId varIdx, litAtom 1 varIdx) ]

def occurrenceEntries (clauseIndex : Nat) (clause : Clause3) :
    List (LeafId × Lara.Atom) :=
  clause.literals.zipIdx.map fun entry =>
    (occurrenceLeafId clauseIndex entry.2,
      occAtom (literalSign entry.1) entry.1.«variable»)

def formulaLeafEntries (formula : Formula3) :
    List (LeafId × Lara.Atom) :=
  formula.occurringVariables.flatMap literalLeafEntries ++
    formula.zipIdx.flatMap (fun entry => occurrenceEntries entry.2 entry.1) ++
    [(queryLeafId, queryAtom)]

/-- Formula-dependent leaf lookup; the fixed policy and registry do not depend
on the formula. -/
def gammaOfFormula (formula : Formula3) : LeafId → Option Lara.Atom :=
  lookupLeaf (formulaLeafEntries formula)

/-- Explicit finite ground list covering every formula-gadget leaf entry. -/
def groundOfFormula (formula : Formula3) : List Lara.Atom :=
  (formulaLeafEntries formula).map Prod.snd

def clauseSubst (clauseIndex : Nat) (clause : Clause3) : Subst :=
  [ (⟨"S1"⟩, numTerm (literalSign clause.first))
  , (⟨"X1"⟩, numTerm clause.first.«variable»)
  , (⟨"S2"⟩, numTerm (literalSign clause.second))
  , (⟨"X2"⟩, numTerm clause.second.«variable»)
  , (⟨"S3"⟩, numTerm (literalSign clause.third))
  , (⟨"X3"⟩, numTerm clause.third.«variable»)
  , (⟨"J"⟩, numTerm clauseIndex) ]

def clauseArgument (clauseIndex : Nat) (clause : Clause3) : SupportTerm :=
  .inst m2bClauseRuleId (clauseSubst clauseIndex clause)
    (clause.literals.zipIdx.map fun entry =>
      .leaf (occurrenceLeafId clauseIndex entry.2))
    [] [] .none

def literalArguments (formula : Formula3) : List SupportTerm :=
  formula.occurringVariables.flatMap fun varIdx =>
    [negativeLiteralArg varIdx, positiveLiteralArg varIdx]

def clauseArguments (formula : Formula3) : List SupportTerm :=
  formula.zipIdx.map fun entry => clauseArgument entry.2 entry.1

def formulaArguments (formula : Formula3) : List SupportTerm :=
  literalArguments formula ++ clauseArguments formula ++ [queryArg]

def literalRootAttacks (formula : Formula3) : List Attack :=
  formula.occurringVariables.flatMap fun varIdx =>
    [ .undermine (negativeLiteralArg varIdx) (positiveLiteralArg varIdx) []
    , .undermine (positiveLiteralArg varIdx) (negativeLiteralArg varIdx) [] ]

def occurrenceAttacks (clauseIndex : Nat) (clause : Clause3) : List Attack :=
  clause.literals.zipIdx.map fun entry =>
    .undermine (literalArg entry.1) (clauseArgument clauseIndex clause)
      [.prem entry.2]

def clauseAttacks (formula : Formula3) : List Attack :=
  formula.zipIdx.flatMap fun entry =>
    occurrenceAttacks entry.2 entry.1 ++
      [.undermine (clauseArgument entry.2 entry.1) queryArg []]

def formulaAttacks (formula : Formula3) : List Attack :=
  literalRootAttacks formula ++ clauseAttacks formula

/-- The exact formula-indexed raw unit attempted by the spike.  Only Γ, ground
atoms, identifiers, support terms, and attacks vary with the formula. -/
def rawUnitOfFormula (formula : Formula3) : Lara.Unit :=
  { sigma := m2bSigma
    policy := m2bPolicy
    args := formulaArguments formula
    atts := formulaAttacks formula }

/-! ## Injectivity of the spelling table -/

private theorem toDigits_no_dash (n : Nat) : '-' ∉ Nat.toDigits 10 n := by
  have h := Numeral.repr_no_dash n
  rwa [Nat.toList_repr] at h

/-- Splitting at a separator character that neither prefix contains is
unambiguous. -/
private theorem dashFree_append_inj {l₁ l₂ r₁ r₂ : List Char}
    (h₁ : '-' ∉ l₁) (h₂ : '-' ∉ l₂)
    (h : l₁ ++ '-' :: r₁ = l₂ ++ '-' :: r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => simpa using h
      | cons c cs =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          exact absurd (by rw [← h.1]; exact List.mem_cons_self) h₂
  | cons c cs ih =>
      cases l₂ with
      | nil =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          exact absurd (by rw [h.1]; exact List.mem_cons_self) h₁
      | cons d ds =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨hcd, htail⟩ := h
          have h₁' : '-' ∉ cs := fun hm => h₁ (List.mem_cons_of_mem _ hm)
          have h₂' : '-' ∉ ds := fun hm => h₂ (List.mem_cons_of_mem _ hm)
          obtain ⟨hpre, hpost⟩ := ih h₁' h₂' htail
          exact ⟨by rw [hcd, hpre], hpost⟩

/-- The single spelling table never collides: `GadgetLeaf.encode` is
injective. -/
theorem GadgetLeaf.encode_inj : Function.Injective GadgetLeaf.encode := by
  intro a b h
  have hlist : (GadgetLeaf.encode a).name.toList =
      (GadgetLeaf.encode b).name.toList := by rw [h]
  cases a with
  | negLit v =>
      cases b with
      | negLit w =>
          simp [GadgetLeaf.encode, String.toList_append] at hlist
          rw [Numeral.toDigits_inj hlist]
      | posLit w =>
          simp [GadgetLeaf.encode, String.toList_append] at hlist
      | occurrence j p =>
          simp [GadgetLeaf.encode, String.toList_append] at hlist
      | query =>
          simp [GadgetLeaf.encode, String.toList_append] at hlist
  | posLit v =>
      cases b with
      | negLit w =>
          simp [GadgetLeaf.encode, String.toList_append] at hlist
      | posLit w =>
          simp [GadgetLeaf.encode, String.toList_append] at hlist
          rw [Numeral.toDigits_inj hlist]
      | occurrence j p =>
          simp [GadgetLeaf.encode, String.toList_append] at hlist
      | query =>
          simp [GadgetLeaf.encode, String.toList_append] at hlist
  | occurrence j p =>
      cases b with
      | negLit w =>
          simp [GadgetLeaf.encode, String.toList_append] at hlist
      | posLit w =>
          simp [GadgetLeaf.encode, String.toList_append] at hlist
      | occurrence j' p' =>
          simp [GadgetLeaf.encode, String.toList_append] at hlist
          obtain ⟨hj, hp⟩ := dashFree_append_inj
            (toDigits_no_dash j) (toDigits_no_dash j') hlist
          rw [Numeral.toDigits_inj hj, Numeral.toDigits_inj hp]
      | query =>
          simp [GadgetLeaf.encode, String.toList_append] at hlist
  | query =>
      cases b with
      | negLit w =>
          simp [GadgetLeaf.encode, String.toList_append] at hlist
      | posLit w =>
          simp [GadgetLeaf.encode, String.toList_append] at hlist
      | occurrence j' p' =>
          simp [GadgetLeaf.encode, String.toList_append] at hlist
      | query => rfl

/-- Leaf-identifier equality decides gadget-leaf equality. -/
theorem GadgetLeaf.encode_eq_iff {x y : GadgetLeaf} :
    x.encode = y.encode ↔ x = y :=
  ⟨fun h => GadgetLeaf.encode_inj h, fun h => h ▸ rfl⟩

/-- Positional occurrence leaves determine both indices. -/
theorem occurrenceLeafId_inj {j p j' p' : Nat}
    (h : occurrenceLeafId j p = occurrenceLeafId j' p') : j = j' ∧ p = p' := by
  have hleaf : GadgetLeaf.occurrence j p = GadgetLeaf.occurrence j' p' :=
    GadgetLeaf.encode_inj h
  injection hleaf with h1 h2
  exact ⟨h1, h2⟩

/-! ## The leaf-table lookup spec -/

theorem lookupLeaf_eq_some_of_nodup
    {entries : List (LeafId × Lara.Atom)} {l : LeafId} {a : Lara.Atom}
    (hkeys : (entries.map Prod.fst).Nodup) (hmem : (l, a) ∈ entries) :
    lookupLeaf entries l = some a := by
  induction entries with
  | nil => simp at hmem
  | cons e rest ih =>
      obtain ⟨k, v⟩ := e
      simp only [List.map_cons, List.nodup_cons] at hkeys
      rcases List.mem_cons.mp hmem with heq | hrest
      · cases heq
        simp [lookupLeaf]
      · have hne : k ≠ l := fun hk =>
          hkeys.1 (hk ▸ List.mem_map.mpr ⟨(l, a), hrest, rfl⟩)
        simp only [lookupLeaf, if_neg hne]
        exact ih hkeys.2 hrest

/-- A successful table lookup only ever returns a stored atom. -/
theorem lookupLeaf_mem_snd {entries : List (LeafId × Lara.Atom)}
    {l : LeafId} {a : Lara.Atom} (h : lookupLeaf entries l = some a) :
    a ∈ entries.map Prod.snd := by
  induction entries with
  | nil => simp [lookupLeaf] at h
  | cons e rest ih =>
      obtain ⟨k, v⟩ := e
      simp only [lookupLeaf] at h
      split at h
      · obtain rfl : v = a := Option.some.inj h
        simp
      · simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ih h)

/-! ## Duplicate-freedom of the leaf-table keys -/

private theorem nodup_of_map_nodup {α β : Type _} {f : α → β} {l : List α}
    (h : (l.map f).Nodup) : l.Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at h
  exact h.imp fun hne heq => hne (congrArg _ heq)

private theorem nodup_flatMap {α β : Type _} {l : List α} {f : α → List β}
    (hl : l.Nodup) (hone : ∀ a ∈ l, (f a).Nodup)
    (hdisj : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x ∈ f a, x ∉ f b) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
      obtain ⟨hnotmem, hl'⟩ := List.nodup_cons.mp hl
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨hone a List.mem_cons_self, ?_, ?_⟩
      · exact ih hl' (fun b hb => hone b (List.mem_cons_of_mem _ hb))
          (fun b hb c hc => hdisj b (List.mem_cons_of_mem _ hb)
            c (List.mem_cons_of_mem _ hc))
      · intro x hx y hy heq
        subst heq
        obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hy
        have hab : a ≠ b := fun habeq => hnotmem (habeq ▸ hb)
        exact hdisj a List.mem_cons_self b (List.mem_cons_of_mem _ hb)
          hab x hx hxb

private theorem zipIdx_nodup {α : Type _} (l : List α) : l.zipIdx.Nodup :=
  nodup_of_map_nodup (f := Prod.snd) (by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range')

/-- The literal-leaf block of the key list. -/
private def literalKeys (formula : Formula3) : List LeafId :=
  formula.occurringVariables.flatMap fun varIdx =>
    [negativeLiteralLeafId varIdx, positiveLiteralLeafId varIdx]

/-- The occurrence-leaf block of the key list. -/
private def occurrenceKeys (formula : Formula3) : List LeafId :=
  formula.zipIdx.flatMap fun entry =>
    entry.1.literals.zipIdx.map fun le => occurrenceLeafId entry.2 le.2

private theorem formulaLeafEntries_keys (φ : Formula3) :
    (formulaLeafEntries φ).map Prod.fst =
      literalKeys φ ++ occurrenceKeys φ ++ [queryLeafId] := by
  simp [formulaLeafEntries, literalKeys, occurrenceKeys, literalLeafEntries,
    occurrenceEntries, List.map_flatMap, List.map_map, Function.comp_def]

private theorem mem_literalKeys {φ : Formula3} {x : LeafId}
    (hx : x ∈ literalKeys φ) :
    ∃ v, v ∈ φ.occurringVariables ∧
      (x = negativeLiteralLeafId v ∨ x = positiveLiteralLeafId v) := by
  obtain ⟨v, hv, hxv⟩ := List.mem_flatMap.mp hx
  exact ⟨v, hv, by simpa using hxv⟩

private theorem mem_occurrenceKeys {φ : Formula3} {x : LeafId}
    (hx : x ∈ occurrenceKeys φ) :
    ∃ j p, x = occurrenceLeafId j p := by
  obtain ⟨e, _, hxe⟩ := List.mem_flatMap.mp hx
  obtain ⟨le, _, rfl⟩ := List.mem_map.mp hxe
  exact ⟨e.2, le.2, rfl⟩

private theorem literalKeys_nodup (φ : Formula3) : (literalKeys φ).Nodup := by
  refine nodup_flatMap (Formula3.occurringVariables_nodup φ)
    (fun v _ => ?_) ?_
  · simp [negativeLiteralLeafId, positiveLiteralLeafId,
      GadgetLeaf.encode_eq_iff]
  · intro v _ w _ hvw x hx hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with h | h <;>
      simp_all [negativeLiteralLeafId, positiveLiteralLeafId,
        GadgetLeaf.encode_eq_iff]

private theorem occurrenceKeys_nodup (φ : Formula3) :
    (occurrenceKeys φ).Nodup := by
  refine nodup_flatMap (zipIdx_nodup φ) (fun e _ => ?_) ?_
  · obtain ⟨c, j⟩ := e
    simp [Clause3.literals, occurrenceLeafId, GadgetLeaf.encode_eq_iff]
  · intro e he e' he' hne x hx hx'
    obtain ⟨c, j⟩ := e
    obtain ⟨c', j'⟩ := e'
    obtain ⟨le, hle, rfl⟩ := List.mem_map.mp hx
    obtain ⟨le', hle', heq⟩ := List.mem_map.mp hx'
    obtain ⟨hj, -⟩ := occurrenceLeafId_inj heq
    subst hj
    have h1 := List.mk_mem_zipIdx_iff_getElem?.mp he
    have h2 := List.mk_mem_zipIdx_iff_getElem?.mp he'
    rw [h1] at h2
    exact hne (by rw [Option.some.inj h2])

theorem formulaLeafEntries_keys_nodup (φ : Formula3) :
    ((formulaLeafEntries φ).map Prod.fst).Nodup := by
  rw [formulaLeafEntries_keys φ, List.nodup_append, List.nodup_append]
  refine ⟨⟨literalKeys_nodup φ, occurrenceKeys_nodup φ, ?_⟩, by simp, ?_⟩
  · intro x hx y hy
    obtain ⟨v, -, hxv⟩ := mem_literalKeys hx
    obtain ⟨j, p, rfl⟩ := mem_occurrenceKeys hy
    rcases hxv with rfl | rfl <;>
      simp [negativeLiteralLeafId, positiveLiteralLeafId, occurrenceLeafId,
        GadgetLeaf.encode_eq_iff]
  · intro x hx y hy
    have hyq : y = queryLeafId := by simpa using hy
    subst hyq
    rcases List.mem_append.mp hx with hxA | hxB
    · obtain ⟨v, -, hxv⟩ := mem_literalKeys hxA
      rcases hxv with rfl | rfl <;>
        simp [negativeLiteralLeafId, positiveLiteralLeafId, queryLeafId,
          GadgetLeaf.encode_eq_iff]
    · obtain ⟨j, p, rfl⟩ := mem_occurrenceKeys hxB
      simp [occurrenceLeafId, queryLeafId, GadgetLeaf.encode_eq_iff]

/-! ## The lookup corollaries the family lemmas consume -/

theorem gammaOfFormula_negLit (φ : Formula3) {v : Nat}
    (hv : v ∈ φ.occurringVariables) :
    gammaOfFormula φ (negativeLiteralLeafId v) = some (litAtom 0 v) := by
  apply lookupLeaf_eq_some_of_nodup (formulaLeafEntries_keys_nodup φ)
  rw [formulaLeafEntries]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap_of_mem hv (by simp [literalLeafEntries])))

theorem gammaOfFormula_posLit (φ : Formula3) {v : Nat}
    (hv : v ∈ φ.occurringVariables) :
    gammaOfFormula φ (positiveLiteralLeafId v) = some (litAtom 1 v) := by
  apply lookupLeaf_eq_some_of_nodup (formulaLeafEntries_keys_nodup φ)
  rw [formulaLeafEntries]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap_of_mem hv (by simp [literalLeafEntries])))

theorem gammaOfFormula_occurrence (φ : Formula3) {c : Clause3} {j : Nat}
    {l : Literal} {p : Nat}
    (hc : (c, j) ∈ φ.zipIdx) (hl : (l, p) ∈ c.literals.zipIdx) :
    gammaOfFormula φ (occurrenceLeafId j p) =
      some (occAtom (literalSign l) l.«variable») := by
  apply lookupLeaf_eq_some_of_nodup (formulaLeafEntries_keys_nodup φ)
  rw [formulaLeafEntries]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap_of_mem hc (List.mem_map.mpr ⟨(l, p), hl, rfl⟩)))

theorem gammaOfFormula_query (φ : Formula3) :
    gammaOfFormula φ queryLeafId = some queryAtom := by
  apply lookupLeaf_eq_some_of_nodup (formulaLeafEntries_keys_nodup φ)
  rw [formulaLeafEntries]
  exact List.mem_append_right _ List.mem_cons_self

/-! ## Ground coverage -/

/-- `groundOfFormula` is the `Prod.snd` projection of the same table
`gammaOfFormula` reads, so every successful lookup's atom is a ground
member. -/
theorem groundOfFormula_covers (φ : Formula3) :
    Realizability.GroundCoversUsedLeaves (gammaOfFormula φ)
      (groundOfFormula φ) (rawUnitOfFormula φ).args := by
  intro w _ l _ p hlookup
  exact lookupLeaf_mem_snd hlookup

/-! ## Duplicate-freedom of the generated arguments -/

private theorem leaf_injective : Function.Injective SupportTerm.leaf := by
  intro a b h
  injection h

private theorem literalArguments_eq_map (φ : Formula3) :
    literalArguments φ = (literalKeys φ).map SupportTerm.leaf := by
  simp [literalArguments, literalKeys, List.map_flatMap, negativeLiteralArg,
    positiveLiteralArg]

private theorem literalArguments_nodup (φ : Formula3) :
    (literalArguments φ).Nodup := by
  rw [literalArguments_eq_map]
  exact nodup_map_of_injective leaf_injective (literalKeys_nodup φ)

/-- The clause index is recoverable from a clause instance: its θ binds `J` to
the index's decimal numeral, and decimal numerals are injective.  (Public for
the compile-image proofs in `Lara.Complexity.Reduction`.) -/
theorem clauseArgument_index_inj {j j' : Nat} {c c' : Clause3}
    (h : clauseArgument j c = clauseArgument j' c') : j = j' := by
  simp only [clauseArgument] at h
  injection h with _ hsub _ _ _ _
  simp only [clauseSubst, numTerm, List.cons.injEq, Prod.mk.injEq,
    Lara.Term.num.injEq, true_and, and_true] at hsub
  obtain ⟨-, -, -, -, -, -, hJ⟩ := hsub
  exact Numeral.natRepr_inj hJ

private theorem clauseArguments_nodup (φ : Formula3) :
    (clauseArguments φ).Nodup := by
  rw [clauseArguments]
  simp only [List.nodup_iff_pairwise_ne, List.pairwise_map]
  have hidx : (φ.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  simp only [List.nodup_iff_pairwise_ne, List.pairwise_map] at hidx
  exact hidx.imp fun hne heq => hne (clauseArgument_index_inj heq)

/-- The literal-root block emits only literal leaves. -/
private theorem mem_literalArguments {φ : Formula3} {w : SupportTerm}
    (hw : w ∈ literalArguments φ) :
    ∃ v, v ∈ φ.occurringVariables ∧
      (w = negativeLiteralArg v ∨ w = positiveLiteralArg v) := by
  obtain ⟨v, hv, hwv⟩ := List.mem_flatMap.mp hw
  exact ⟨v, hv, by simpa using hwv⟩

/-- The clause block emits only clause instances, each at its own `zipIdx`
witness. -/
private theorem mem_clauseArguments {φ : Formula3} {w : SupportTerm}
    (hw : w ∈ clauseArguments φ) :
    ∃ c j, (c, j) ∈ φ.zipIdx ∧ w = clauseArgument j c := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hw
  exact ⟨e.1, e.2, he, rfl⟩

theorem formulaArguments_nodup (φ : Formula3) :
    (rawUnitOfFormula φ).args.Nodup := by
  show (formulaArguments φ).Nodup
  rw [formulaArguments, List.nodup_append, List.nodup_append]
  refine ⟨⟨literalArguments_nodup φ, clauseArguments_nodup φ, ?_⟩, by simp, ?_⟩
  · intro x hx y hy
    obtain ⟨v, -, hxv⟩ := mem_literalArguments hx
    obtain ⟨c, j, -, rfl⟩ := mem_clauseArguments hy
    rcases hxv with rfl | rfl <;>
      simp [negativeLiteralArg, positiveLiteralArg, clauseArgument]
  · intro x hx y hy
    have hyq : y = queryArg := by simpa using hy
    subst hyq
    rcases List.mem_append.mp hx with hxA | hxB
    · obtain ⟨v, -, hxv⟩ := mem_literalArguments hxA
      rcases hxv with rfl | rfl <;>
        simp [negativeLiteralArg, positiveLiteralArg, queryArg,
          negativeLiteralLeafId, positiveLiteralLeafId, queryLeafId,
          GadgetLeaf.encode_eq_iff]
    · obtain ⟨c, j, -, rfl⟩ := mem_clauseArguments hxB
      simp [clauseArgument, queryArg]

/-! ## The signature stage

Every generated ground atom and every θ range term is a `.num` payload, and
`Sigma.sortOf` maps a `.num` payload to `some .num` without inspecting the
string — so the per-generator lemmas hold for arbitrary numeric payloads. -/

private theorem wsAtom_litAtom (s v : Nat) :
    Lara.Sigma.wsAtom m2bSigma (litAtom s v) = true := rfl

private theorem wsAtom_occAtom (s v : Nat) :
    Lara.Sigma.wsAtom m2bSigma (occAtom s v) = true := rfl

private theorem wsAtom_queryAtom :
    Lara.Sigma.wsAtom m2bSigma queryAtom = true := rfl

/-- The ground list, generator by generator. -/
private theorem groundOfFormula_eq (φ : Formula3) :
    groundOfFormula φ =
      φ.occurringVariables.flatMap (fun v => [litAtom 0 v, litAtom 1 v]) ++
        φ.zipIdx.flatMap (fun entry => entry.1.literals.zipIdx.map fun le =>
          occAtom (literalSign le.1) le.1.«variable») ++
        [queryAtom] := by
  simp [groundOfFormula, formulaLeafEntries, literalLeafEntries,
    occurrenceEntries, List.map_flatMap, List.map_map, Function.comp_def]

theorem groundOfFormula_wellSorted (φ : Formula3) :
    Lara.groundWellSorted m2bSigma (groundOfFormula φ) = true := by
  rw [Lara.groundWellSorted, List.all_eq_true, groundOfFormula_eq]
  intro a ha
  rcases List.mem_append.mp ha with hlit_occ | hquery
  · rcases List.mem_append.mp hlit_occ with hlit | hocc
    · obtain ⟨v, -, hav⟩ := List.mem_flatMap.mp hlit
      rcases (by simpa using hav : a = litAtom 0 v ∨ a = litAtom 1 v) with
        rfl | rfl
      · exact wsAtom_litAtom 0 v
      · exact wsAtom_litAtom 1 v
    · obtain ⟨entry, -, hae⟩ := List.mem_flatMap.mp hocc
      obtain ⟨le, -, rfl⟩ := List.mem_map.mp hae
      exact wsAtom_occAtom _ _
  · have haq : a = queryAtom := by simpa using hquery
    subst haq
    exact wsAtom_queryAtom

private theorem termWellSorted_leaf (l : LeafId) :
    Lara.termWellSorted m2bSigma m2bPolicy (.leaf l) = true := rfl

/-- The clause instance is well-sorted for arbitrary numeric payloads: the
rule lookup, its derived parameter environment, and every non-payload guard of
`thetaWellSorted` are closed computations, and every θ range term is a
numeral. -/
private theorem termWellSorted_clauseArgument (j : Nat) (c : Clause3) :
    Lara.termWellSorted m2bSigma m2bPolicy (clauseArgument j c) = true := rfl

private theorem termsWellSorted_eq_all (l : List SupportTerm) :
    Lara.termsWellSorted m2bSigma m2bPolicy l =
      l.all (Lara.termWellSorted m2bSigma m2bPolicy) := by
  induction l with
  | nil => rfl
  | cons w ws ih => rw [Lara.termsWellSorted, List.all_cons, ih]

private theorem argsWellSorted_formulaArguments (φ : Formula3) :
    Lara.argsWellSorted m2bSigma m2bPolicy (formulaArguments φ) = true := by
  rw [Lara.argsWellSorted, termsWellSorted_eq_all, List.all_eq_true]
  intro w hw
  rw [formulaArguments] at hw
  rcases List.mem_append.mp hw with hlit_clause | hquery
  · rcases List.mem_append.mp hlit_clause with hlit | hclause
    · obtain ⟨v, -, hwv⟩ := mem_literalArguments hlit
      rcases hwv with rfl | rfl <;> exact termWellSorted_leaf _
    · obtain ⟨c, j, -, rfl⟩ := mem_clauseArguments hclause
      exact termWellSorted_clauseArgument j c
  · have hwq : w = queryArg := by simpa using hquery
    subst hwq
    exact termWellSorted_leaf _

theorem formulaArguments_wellSorted (φ : Formula3) :
    Lara.argsWellSorted m2bSigma m2bPolicy (rawUnitOfFormula φ).args = true :=
  argsWellSorted_formulaArguments φ

theorem signatureStage_formula_none (φ : Formula3) :
    Check.Unit.signatureStage (groundOfFormula φ) (rawUnitOfFormula φ) =
      none := by
  unfold Check.Unit.signatureStage
  rw [show (rawUnitOfFormula φ).sigma = m2bSigma from rfl,
    show (rawUnitOfFormula φ).policy = m2bPolicy from rfl,
    show (rawUnitOfFormula φ).args = formulaArguments φ from rfl]
  simp [m2bSigma_wellFormed, m2bPolicy_wellSorted, groundOfFormula_wellSorted,
    argsWellSorted_formulaArguments]

/-! ## Recursive support for the generated arguments

The fixed policy owns exactly one rule, so every non-recursive side condition
of `HasSupport.inst` for a clause instance — rule lookup, θ keys and domain,
premise and conclusion instantiation, the length bookkeeping, and the empty
question/discharge partition — is a closed computation over the frozen context
that reduces structurally for arbitrary numeric payloads.  The instantiation
computations are packaged as standalone `simp` lemmas parameterized by the
clause data so the attack-completeness stage can reuse them. -/

/-- The instantiated premise atoms of a clause instance, in positional
order. -/
def clausePremiseAtoms (clause : Clause3) : List Lara.Atom :=
  [ occAtom (literalSign clause.first) clause.first.«variable»
  , occAtom (literalSign clause.second) clause.second.«variable»
  , occAtom (literalSign clause.third) clause.third.«variable» ]

/-- The gadget's sole rule lookup is a closed computation over the fixed
policy. -/
@[simp] theorem m2bPolicy_ruleLookup_clause :
    m2bPolicy.ruleLookup m2bClauseRuleId = some m2bClauseRule := rfl

/-- `clauseSubst`'s seven keys are literally the clause rule's declared
parameter list, in order — the §6.1 exact-domain side condition holds
definitionally. -/
@[simp] theorem clauseSubst_keys (j : Nat) (c : Clause3) :
    (clauseSubst j c).map Prod.fst = m2bClauseRule.params := rfl

/-- Instantiating the rule's three `occ(Sᵢ, Xᵢ)` premise patterns under
`clauseSubst j c` computes — structurally, for arbitrary payloads — to the
clause's occurrence atoms. -/
@[simp] theorem instAPats_clauseSubst_premises (j : Nat) (c : Clause3) :
    instAPats (clauseSubst j c) m2bClauseRule.premises =
      some (clausePremiseAtoms c) := rfl

/-- Instantiating the rule's `clause(J)` conclusion pattern under
`clauseSubst j c` computes to `clauseAtom j`. -/
@[simp] theorem instAPat_clauseSubst_concl (j : Nat) (c : Clause3) :
    instAPat (clauseSubst j c) m2bClauseRule.concl = some (clauseAtom j) := rfl

/-- The three literal positions of a clause, with their indices. -/
private theorem clause_literals_zipIdx (c : Clause3) :
    c.literals.zipIdx = [(c.first, 0), (c.second, 1), (c.third, 2)] := rfl

/-- Every non-recursive §6.1 side condition of a clause instance, bundled.
The rule is defeasible with no questions and no certifier, so the discharge
map, hole set, and assurance obligations are all empty. -/
private theorem clauseArgument_instSide (j : Nat) (c : Clause3) :
    InstSide id m2bPolicy.ruleLookup (Support.certOkOf m2bRegistry)
      m2bClauseRuleId (clauseSubst j c) m2bClauseRule
      (c.literals.zipIdx.map fun entry =>
        .leaf (occurrenceLeafId j entry.2))
      [] [] .none
      (clausePremiseAtoms c) (clausePremiseAtoms c)
      [[], [], []] [] [] (clauseAtom j) :=
  { rule := m2bPolicy_ruleLookup_clause
    θNodup := by rw [clauseSubst_keys]; decide
    θDom := fun x => by rw [clauseSubst_keys]
    prems := instAPats_clauseSubst_premises j c
    concl := instAPat_clauseSubst_concl j c
    lenAs := rfl
    lenCs := rfl
    lenOs := rfl
    premEq := fun _ A B hA hB => by
      cases Option.some.inj (hA.symm.trans hB); rfl
    lenDCs := rfl
    lenDOs := rfl
    ans := fun _ _ _ _ hD _ => nomatch hD
    qNodup := List.Pairwise.nil
    dNodup := List.Pairwise.nil
    hNodup := List.Pairwise.nil
    cover := fun _ hqd => nomatch hqd
    disj := fun _ hn => nomatch hn
    keysD := fun _ hn => nomatch hn
    keysH := fun _ hn => nomatch hn
    strictNoQ := fun _ => ⟨rfl, rfl⟩
    assur := AssuranceOk.defeasible rfl }

/-- Leaf support: every declared leaf is supported by its Γ conclusion with no
obligations, by the `HasSupport.leaf` constructor. -/
theorem hasSupport_gadgetLeaf (φ : Formula3) {l : LeafId} {a : Lara.Atom}
    (hlookup : gammaOfFormula φ l = some a) :
    Support.HasSupport id m2bPolicy.ruleLookup (gammaOfFormula φ)
      (Support.certOkOf m2bRegistry) (.leaf l) a [] :=
  Support.HasSupport.leaf hlookup

/-- Clause-instance support: `HasSupport.inst` for the sole policy rule, with
the three occurrence leaves discharging the premises at their Γ
conclusions. -/
theorem hasSupport_clauseArgument (φ : Formula3) {c : Clause3} {j : Nat}
    (hc : (c, j) ∈ φ.zipIdx) :
    Support.HasSupport id m2bPolicy.ruleLookup (gammaOfFormula φ)
      (Support.certOkOf m2bRegistry) (clauseArgument j c) (clauseAtom j)
      [] := by
  have h1 : (c.first, 0) ∈ c.literals.zipIdx := by
    simp [clause_literals_zipIdx]
  have h2 : (c.second, 1) ∈ c.literals.zipIdx := by
    simp [clause_literals_zipIdx]
  have h3 : (c.third, 2) ∈ c.literals.zipIdx := by
    simp [clause_literals_zipIdx]
  refine Support.HasSupport.inst (clauseArgument_instSide j c) ?_ ?_
  · intro i w A O hw hA hO
    match i, hw, hA, hO with
    | 0, hw, hA, hO =>
        cases Option.some.inj hw
        cases Option.some.inj hA
        cases Option.some.inj hO
        exact hasSupport_gadgetLeaf φ (gammaOfFormula_occurrence φ hc h1)
    | 1, hw, hA, hO =>
        cases Option.some.inj hw
        cases Option.some.inj hA
        cases Option.some.inj hO
        exact hasSupport_gadgetLeaf φ (gammaOfFormula_occurrence φ hc h2)
    | 2, hw, hA, hO =>
        cases Option.some.inj hw
        cases Option.some.inj hA
        cases Option.some.inj hO
        exact hasSupport_gadgetLeaf φ (gammaOfFormula_occurrence φ hc h3)
    | i + 3, hw, _, _ =>
        exact nomatch (show (none : Option SupportTerm) = some w from hw)
  · intro _ q w _ _ hD _ _
    exact nomatch
      (show (none : Option (QuestionId × SupportTerm)) = some (q, w) from hD)

/-- Every generated argument has recursively obligation-free support: leaf
blocks by their Γ conclusions, clause instances by `hasSupport_clauseArgument`
at their own `zipIdx` witnesses. -/
theorem formulaArguments_supported (φ : Formula3) :
    ∀ w ∈ (rawUnitOfFormula φ).args, ∃ C,
      Support.HasSupport id m2bPolicy.ruleLookup (gammaOfFormula φ)
        (Support.certOkOf m2bRegistry) w C [] := by
  intro w hw
  have hw' : w ∈ formulaArguments φ := hw
  rw [formulaArguments] at hw'
  rcases List.mem_append.mp hw' with hlit_clause | hquery
  · rcases List.mem_append.mp hlit_clause with hlit | hclause
    · obtain ⟨v, hv, hwv⟩ := mem_literalArguments hlit
      rcases hwv with rfl | rfl
      · exact ⟨litAtom 0 v,
          hasSupport_gadgetLeaf φ (gammaOfFormula_negLit φ hv)⟩
      · exact ⟨litAtom 1 v,
          hasSupport_gadgetLeaf φ (gammaOfFormula_posLit φ hv)⟩
    · obtain ⟨c, j, hc, rfl⟩ := mem_clauseArguments hclause
      exact ⟨clauseAtom j, hasSupport_clauseArgument φ hc⟩
  · have hwq : w = queryArg := by simpa using hquery
    subst hwq
    exact ⟨queryAtom, hasSupport_gadgetLeaf φ (gammaOfFormula_query φ)⟩

/-! ## Typed attacks

Every generated attack is an undermine whose source is a generated argument
with a known root conclusion and whose target subterm is a declared leaf, so
`HasAttack.undermine` closes each family once the firing schema row is
exhibited.  The three rows that fire — `lit(0,X) → lit(1,X)` and
`lit(1,X) → lit(0,X)` for the mutual literal-root pair, `lit(S,X) → occ(S,X)`
at a premise path, and `clause(J) → query` — are packaged as `ContraryMatch`
lemmas parameterized by the numeric payloads so the attack-completeness stage
can reuse them.  Each holds by one explicit substitution witness with the
payload bound once; no injectivity is needed in this positive direction.  The
closed evaluations in `Lara.Complexity.Context` stay as regressions and are
not substituted for these parameterized versions. -/

/-- The `lit(0,X) → lit(1,X)` schema row fires at any variable payload. -/
theorem contraryMatch_negLit_posLit (v : Nat) :
    ContraryMatch id m2bPolicy.defeat (litAtom 0 v) (litAtom 1 v) :=
  ⟨(⟨⟨"lit"⟩, .cons (.num "0") (.cons (.var ⟨"X"⟩) .nil)⟩,
      ⟨⟨"lit"⟩, .cons (.num "1") (.cons (.var ⟨"X"⟩) .nil)⟩),
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
    [(⟨"X"⟩, numTerm v)], litAtom 0 v, litAtom 1 v, rfl, rfl, rfl, rfl⟩

/-- The `lit(1,X) → lit(0,X)` schema row fires at any variable payload. -/
theorem contraryMatch_posLit_negLit (v : Nat) :
    ContraryMatch id m2bPolicy.defeat (litAtom 1 v) (litAtom 0 v) :=
  ⟨(⟨⟨"lit"⟩, .cons (.num "1") (.cons (.var ⟨"X"⟩) .nil)⟩,
      ⟨⟨"lit"⟩, .cons (.num "0") (.cons (.var ⟨"X"⟩) .nil)⟩),
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)),
    [(⟨"X"⟩, numTerm v)], litAtom 1 v, litAtom 0 v, rfl, rfl, rfl, rfl⟩

/-- The `lit(S,X) → occ(S,X)` schema row fires at any sign and variable
payloads. -/
theorem contraryMatch_lit_occ (s v : Nat) :
    ContraryMatch id m2bPolicy.defeat (litAtom s v) (occAtom s v) :=
  ⟨(⟨⟨"lit"⟩, .cons (.var ⟨"S"⟩) (.cons (.var ⟨"X"⟩) .nil)⟩,
      ⟨⟨"occ"⟩, .cons (.var ⟨"S"⟩) (.cons (.var ⟨"X"⟩) .nil)⟩),
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))),
    [(⟨"S"⟩, numTerm s), (⟨"X"⟩, numTerm v)], litAtom s v, occAtom s v,
    rfl, rfl, rfl, rfl⟩

/-- The `clause(J) → query` schema row fires at any clause-index payload. -/
theorem contraryMatch_clause_query (j : Nat) :
    ContraryMatch id m2bPolicy.defeat (clauseAtom j) queryAtom :=
  ⟨(⟨⟨"clause"⟩, .cons (.var ⟨"J"⟩) .nil⟩, ⟨⟨"query"⟩, .nil⟩),
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))),
    [(⟨"J"⟩, numTerm j)], clauseAtom j, queryAtom, rfl, rfl, rfl, rfl⟩

/-- Every literal occurrence's variable is an occurring variable of the
formula, through the clause's `zipIdx` witness.  (Public for the axiom
audit: its `AxCheck` row is registered; no external consumer yet — external
callers with a plain `l ∈ c.literals` witness use
`Formula3.mem_occurringVariables` directly.) -/
theorem variable_mem_occurringVariables {φ : Formula3} {c : Clause3}
    {j : Nat} {l : Literal} {p : Nat}
    (hc : (c, j) ∈ φ.zipIdx) (hl : (l, p) ∈ c.literals.zipIdx) :
    l.«variable» ∈ φ.occurringVariables := by
  have hcφ : c ∈ φ :=
    List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hc)
  have hlc : l ∈ c.literals :=
    List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hl)
  exact Formula3.mem_occurringVariables (List.mem_flatMap_of_mem hcφ hlc)

/-- Γ conclusion of the signed literal leaf, uniformly in the sign. -/
theorem gammaOfFormula_literalLeaf (φ : Formula3) {l : Literal}
    (hv : l.«variable» ∈ φ.occurringVariables) :
    gammaOfFormula φ (literalLeafId l) =
      some (litAtom (literalSign l) l.«variable») := by
  by_cases hpos : l.positive
  · simp only [literalLeafId, literalSign, if_pos hpos]
    exact gammaOfFormula_posLit φ hv
  · simp only [literalLeafId, literalSign, if_neg hpos]
    exact gammaOfFormula_negLit φ hv

/-- The `[.prem p]` subterm of a clause instance is its `p`-th occurrence
leaf.  (Public for the compile-image proofs in
`Lara.Complexity.Reduction`.) -/
theorem subterm_clauseArgument_prem {c : Clause3} {j : Nat}
    {l : Literal} {p : Nat} (hl : (l, p) ∈ c.literals.zipIdx) :
    subterm (clauseArgument j c) [.prem p] =
      some (.leaf (occurrenceLeafId j p)) := by
  rw [clause_literals_zipIdx] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hl
  rcases hl with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl

/-- The mutual literal-root undermine `¬x ⟶ x`, at the root path. -/
theorem hasAttack_negLit_posLit (φ : Formula3) {v : Nat}
    (hv : v ∈ φ.occurringVariables) :
    HasAttack id m2bPolicy.ruleLookup (gammaOfFormula φ)
      (Support.certOkOf m2bRegistry) m2bPolicy.defeat
      (.undermine (negativeLiteralArg v) (positiveLiteralArg v) []) :=
  .undermine (hasSupport_gadgetLeaf φ (gammaOfFormula_negLit φ hv)) rfl
    (gammaOfFormula_posLit φ hv) (contraryMatch_negLit_posLit v)

/-- The mutual literal-root undermine `x ⟶ ¬x`, at the root path. -/
theorem hasAttack_posLit_negLit (φ : Formula3) {v : Nat}
    (hv : v ∈ φ.occurringVariables) :
    HasAttack id m2bPolicy.ruleLookup (gammaOfFormula φ)
      (Support.certOkOf m2bRegistry) m2bPolicy.defeat
      (.undermine (positiveLiteralArg v) (negativeLiteralArg v) []) :=
  .undermine (hasSupport_gadgetLeaf φ (gammaOfFormula_posLit φ hv)) rfl
    (gammaOfFormula_negLit φ hv) (contraryMatch_posLit_negLit v)

/-- The positional undermine of a clause instance by a literal root: the
`lit(S,X) → occ(S,X)` row fires between the literal root's conclusion and the
occurrence leaf's conclusion at premise path `[.prem p]`. -/
theorem hasAttack_literal_occurrence (φ : Formula3) {c : Clause3} {j : Nat}
    {l : Literal} {p : Nat}
    (hc : (c, j) ∈ φ.zipIdx) (hl : (l, p) ∈ c.literals.zipIdx) :
    HasAttack id m2bPolicy.ruleLookup (gammaOfFormula φ)
      (Support.certOkOf m2bRegistry) m2bPolicy.defeat
      (.undermine (literalArg l) (clauseArgument j c) [.prem p]) :=
  .undermine
    (hasSupport_gadgetLeaf φ
      (gammaOfFormula_literalLeaf φ (variable_mem_occurringVariables hc hl)))
    (subterm_clauseArgument_prem hl)
    (gammaOfFormula_occurrence φ hc hl)
    (contraryMatch_lit_occ (literalSign l) l.«variable»)

/-- The clause-root undermine of the query leaf, at the root path. -/
theorem hasAttack_clause_query (φ : Formula3) {c : Clause3} {j : Nat}
    (hc : (c, j) ∈ φ.zipIdx) :
    HasAttack id m2bPolicy.ruleLookup (gammaOfFormula φ)
      (Support.certOkOf m2bRegistry) m2bPolicy.defeat
      (.undermine (clauseArgument j c) queryArg []) :=
  .undermine (hasSupport_clauseArgument φ hc) rfl (gammaOfFormula_query φ)
    (contraryMatch_clause_query j)

/-- The generated attacks, attack by attack: each is one of the mutual
literal-root pair at its occurring variable, a positional occurrence
undermine at its clause and literal `zipIdx` witnesses, or the clause-root
undermine of the query.  (Public for the compile-image proofs in
`Lara.Complexity.Reduction`.) -/
theorem mem_formulaAttacks {φ : Formula3} {k : Attack}
    (hk : k ∈ formulaAttacks φ) :
    (∃ v, v ∈ φ.occurringVariables ∧
        (k = .undermine (negativeLiteralArg v) (positiveLiteralArg v) [] ∨
          k = .undermine (positiveLiteralArg v) (negativeLiteralArg v) [])) ∨
    ∃ c j, (c, j) ∈ φ.zipIdx ∧
      ((∃ l p, (l, p) ∈ c.literals.zipIdx ∧
          k = .undermine (literalArg l) (clauseArgument j c) [.prem p]) ∨
        k = .undermine (clauseArgument j c) queryArg []) := by
  rw [formulaAttacks] at hk
  rcases List.mem_append.mp hk with hlit | hclause
  · obtain ⟨v, hv, hkv⟩ := List.mem_flatMap.mp hlit
    exact Or.inl ⟨v, hv, by simpa using hkv⟩
  · obtain ⟨⟨c, j⟩, hcj, hkc⟩ := List.mem_flatMap.mp hclause
    refine Or.inr ⟨c, j, hcj, ?_⟩
    rcases List.mem_append.mp hkc with hocc | hquery
    · obtain ⟨⟨l, p⟩, hlp, rfl⟩ := List.mem_map.mp hocc
      exact Or.inl ⟨l, p, hlp, rfl⟩
    · exact Or.inr (by simpa using hquery)

/-- Every generated attack is typed: the three families close through their
schema rows via `HasAttack.undermine`. -/
theorem hasAttack_formula (φ : Formula3) :
    ∀ k ∈ (rawUnitOfFormula φ).atts,
      Attack.HasAttack id m2bPolicy.ruleLookup (gammaOfFormula φ)
        (Support.certOkOf m2bRegistry) m2bPolicy.defeat k := by
  intro k hk
  have hk' : k ∈ formulaAttacks φ := hk
  rcases mem_formulaAttacks hk' with ⟨v, hv, hkv⟩ | ⟨c, j, hc, hkc⟩
  · rcases hkv with rfl | rfl
    · exact hasAttack_negLit_posLit φ hv
    · exact hasAttack_posLit_negLit φ hv
  · rcases hkc with ⟨l, p, hlp, rfl⟩ | rfl
    · exact hasAttack_literal_occurrence φ hc hlp
    · exact hasAttack_clause_query φ hc

/-! ## Attack endpoints are generated arguments

Converse membership: each constructed term is emitted by its argument
generator at the same membership witness the attack generator consumed. -/

private theorem negativeLiteralArg_mem {φ : Formula3} {v : Nat}
    (hv : v ∈ φ.occurringVariables) :
    negativeLiteralArg v ∈ formulaArguments φ := by
  rw [formulaArguments]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap_of_mem hv (by simp)))

private theorem positiveLiteralArg_mem {φ : Formula3} {v : Nat}
    (hv : v ∈ φ.occurringVariables) :
    positiveLiteralArg v ∈ formulaArguments φ := by
  rw [formulaArguments]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap_of_mem hv (by simp)))

/-- The signed literal leaf is the block member of its variable's polarity. -/
private theorem literalArg_mem {φ : Formula3} {l : Literal}
    (hv : l.«variable» ∈ φ.occurringVariables) :
    literalArg l ∈ formulaArguments φ := by
  by_cases hpos : l.positive
  · rw [show literalArg l = positiveLiteralArg l.«variable» by
      simp [literalArg, literalLeafId, positiveLiteralArg, hpos]]
    exact positiveLiteralArg_mem hv
  · rw [show literalArg l = negativeLiteralArg l.«variable» by
      simp [literalArg, literalLeafId, negativeLiteralArg, hpos]]
    exact negativeLiteralArg_mem hv

private theorem clauseArgument_mem {φ : Formula3} {c : Clause3} {j : Nat}
    (hc : (c, j) ∈ φ.zipIdx) :
    clauseArgument j c ∈ formulaArguments φ := by
  rw [formulaArguments]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨(c, j), hc, rfl⟩))

private theorem queryArg_mem (φ : Formula3) :
    queryArg ∈ formulaArguments φ := by
  rw [formulaArguments]
  exact List.mem_append_right _ List.mem_cons_self

/-- Every attack source is a generated argument: a literal root, a clause
instance, or a clause root, at the same membership witness. -/
theorem formulaAttacks_source_mem (φ : Formula3) :
    ∀ k ∈ (rawUnitOfFormula φ).atts, k.source ∈ (rawUnitOfFormula φ).args := by
  intro k hk
  have hk' : k ∈ formulaAttacks φ := hk
  show k.source ∈ formulaArguments φ
  rcases mem_formulaAttacks hk' with ⟨v, hv, hkv⟩ | ⟨c, j, hc, hkc⟩
  · rcases hkv with rfl | rfl
    · exact negativeLiteralArg_mem hv
    · exact positiveLiteralArg_mem hv
  · rcases hkc with ⟨l, p, hlp, rfl⟩ | rfl
    · exact literalArg_mem (variable_mem_occurringVariables hc hlp)
    · exact clauseArgument_mem hc

/-- Every attack target is a generated argument: a literal root, a clause
instance, or the query leaf. -/
theorem formulaAttacks_target_mem (φ : Formula3) :
    ∀ k ∈ (rawUnitOfFormula φ).atts, k.target ∈ (rawUnitOfFormula φ).args := by
  intro k hk
  have hk' : k ∈ formulaAttacks φ := hk
  show k.target ∈ formulaArguments φ
  rcases mem_formulaAttacks hk' with ⟨v, hv, hkv⟩ | ⟨c, j, hc, hkc⟩
  · rcases hkv with rfl | rfl
    · exact positiveLiteralArg_mem hv
    · exact negativeLiteralArg_mem hv
  · rcases hkc with ⟨l, p, hlp, rfl⟩ | rfl
    · exact clauseArgument_mem hc
    · exact queryArg_mem φ

/-! ## Exact attack completeness

`Compile.AttackComplete` quantifies over every supported argument pair whose
root conclusions fire a contrary schema row.  Three layers discharge it
exactly.  Root-conclusion determination inverts `HasSupport` over the three
generated blocks: a leaf's Γ lookup pins its conclusion, and a clause
instance's §6.1 side conditions pin the sole rule and hence `clauseAtom j`.
The `ContraryMatch` characterization then reduces the six schema rows over
root conclusions to the two declared families: the `d`/`b`/`a` rows and the
`lit → occ` row miss every root-conclusion predicate head, the two mutual
`lit ↔ lit` rows bind `X` once so both instantiated payloads are literally the
same term, and the `clause → query` row is immediate.  Numeral injectivity is
load-bearing in the assembly: `litAtom` payload equality must determine the
variable index (`natRepr_inj` inside `litAtom_inj`), else two distinct
variables with equal reprs would demand an undeclared attack.  Coverage
finally exhibits each firing pair's declared undermine at the root path. -/

/- The context's ground-atom builders, re-spelled through `Nat.repr` (their
`numTerm` is private to `Lara.Complexity.Context`, and this file's public
`numTerm` is deliberately not used either: `litAtom_inj` consumes the explicit
`Nat.repr` spelling directly; a drift in either builder breaks these `rfl`s at
compile time). -/

private theorem litAtom_eq (s v : Nat) :
    litAtom s v =
      .atom "lit" (.cons (.num (Nat.repr s)) (.cons (.num (Nat.repr v)) .nil)) :=
  rfl

private theorem clauseAtom_eq (j : Nat) :
    clauseAtom j = .atom "clause" (.cons (.num (Nat.repr j)) .nil) := rfl

private theorem queryAtom_eq : queryAtom = .atom "query" .nil := rfl

/-- Signed literal atoms determine their payloads, by numeral injectivity. -/
private theorem litAtom_inj {s v s' v' : Nat}
    (h : litAtom s v = litAtom s' v') : s = s' ∧ v = v' := by
  rw [litAtom_eq, litAtom_eq] at h
  simp only [Lara.Atom.atom.injEq, Lara.Terms.cons.injEq, Lara.Term.num.injEq,
    true_and, and_true] at h
  exact ⟨Numeral.natRepr_inj h.1, Numeral.natRepr_inj h.2⟩

/-- `HasSupport` inversion for a clause instance, at any obligation index:
the §6.1 side-condition record pins the sole policy rule, and the conclusion
instantiation pins `clauseAtom j`.  (Public for the compile-image proofs in
`Lara.Complexity.Reduction`.) -/
theorem clauseArgument_conclusion_eq {φ : Formula3} {c : Clause3}
    {j : Nat} {C : Lara.Atom} {O : List QuestionId}
    (hs : Support.HasSupport id m2bPolicy.ruleLookup (gammaOfFormula φ)
      (Support.certOkOf m2bRegistry)
      (.inst m2bClauseRuleId (clauseSubst j c)
        (c.literals.zipIdx.map fun entry =>
          .leaf (occurrenceLeafId j entry.2)) [] [] .none) C O) :
    C = clauseAtom j := by
  cases hs with
  | inst hside _ _ =>
      have hr := Option.some.inj
        (m2bPolicy_ruleLookup_clause.symm.trans hside.rule)
      have hconcl := hside.concl
      rw [← hr] at hconcl
      exact (Option.some.inj
        ((instAPat_clauseSubst_concl j c).symm.trans hconcl)).symm

/-- **Root-conclusion determination.**  Every supported generated argument is
one of the three block members, and `HasSupport` inversion pins its
conclusion: literal leaves and the query leaf by their Γ lookups, clause
instances by `clauseArgument_conclusion_eq`. -/
theorem formulaArgument_conclusion (φ : Formula3) {w : SupportTerm}
    {C : Lara.Atom} (hw : w ∈ (rawUnitOfFormula φ).args)
    (hs : Support.HasSupport id m2bPolicy.ruleLookup (gammaOfFormula φ)
      (Support.certOkOf m2bRegistry) w C []) :
    (∃ v ∈ φ.occurringVariables,
        (w = negativeLiteralArg v ∧ C = litAtom 0 v) ∨
        (w = positiveLiteralArg v ∧ C = litAtom 1 v)) ∨
    (∃ c j, (c, j) ∈ φ.zipIdx ∧ w = clauseArgument j c ∧ C = clauseAtom j) ∨
    (w = queryArg ∧ C = queryAtom) := by
  have hw' : w ∈ formulaArguments φ := hw
  rw [formulaArguments] at hw'
  rcases List.mem_append.mp hw' with hlit_clause | hquery
  · rcases List.mem_append.mp hlit_clause with hlit | hclause
    · obtain ⟨v, hv, hwv⟩ := mem_literalArguments hlit
      rcases hwv with rfl | rfl
      · have hs' : Support.HasSupport id m2bPolicy.ruleLookup
            (gammaOfFormula φ) (Support.certOkOf m2bRegistry)
            (.leaf (negativeLiteralLeafId v)) C [] := hs
        cases hs' with
        | leaf hΓ =>
            exact Or.inl ⟨v, hv, Or.inl ⟨rfl,
              (Option.some.inj
                ((gammaOfFormula_negLit φ hv).symm.trans hΓ)).symm⟩⟩
      · have hs' : Support.HasSupport id m2bPolicy.ruleLookup
            (gammaOfFormula φ) (Support.certOkOf m2bRegistry)
            (.leaf (positiveLiteralLeafId v)) C [] := hs
        cases hs' with
        | leaf hΓ =>
            exact Or.inl ⟨v, hv, Or.inr ⟨rfl,
              (Option.some.inj
                ((gammaOfFormula_posLit φ hv).symm.trans hΓ)).symm⟩⟩
    · obtain ⟨c, j, hcj, rfl⟩ := mem_clauseArguments hclause
      exact Or.inr (Or.inl ⟨c, j, hcj, rfl,
        clauseArgument_conclusion_eq (φ := φ) hs⟩)
  · have hwq : w = queryArg := by simpa using hquery
    subst hwq
    have hs' : Support.HasSupport id m2bPolicy.ruleLookup (gammaOfFormula φ)
        (Support.certOkOf m2bRegistry) (.leaf queryLeafId) C [] := hs
    cases hs' with
    | leaf hΓ =>
        exact Or.inr (Or.inr ⟨rfl,
          (Option.some.inj ((gammaOfFormula_query φ).symm.trans hΓ)).symm⟩)

/-- The root conclusions of the generated arguments: a signed literal atom, a
clause atom, or the query atom. -/
def RootConclusion (a : Lara.Atom) : Prop :=
  (∃ s v, a = litAtom s v) ∨ (∃ j, a = clauseAtom j) ∨ a = queryAtom

/-- Every supported generated argument concludes a root conclusion. -/
private theorem rootConclusion_of_argument {φ : Formula3} {w : SupportTerm}
    {C : Lara.Atom} (hw : w ∈ (rawUnitOfFormula φ).args)
    (hs : Support.HasSupport id m2bPolicy.ruleLookup (gammaOfFormula φ)
      (Support.certOkOf m2bRegistry) w C []) : RootConclusion C := by
  rcases formulaArgument_conclusion φ hw hs with
    ⟨v, -, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨c, j, -, -, rfl⟩ | ⟨-, rfl⟩
  · exact Or.inl ⟨0, v, rfl⟩
  · exact Or.inl ⟨1, v, rfl⟩
  · exact Or.inr (Or.inl ⟨j, rfl⟩)
  · exact Or.inr (Or.inr rfl)

/-- **`ContraryMatch` over root conclusions, exactly.**  Between root
conclusions, the fixed policy's contrary relation is precisely the two
declared gadget families: the mutual literal-root pair at one shared variable
and the clause-root undermine of the query.  The forward direction case-splits
the six schema rows; the mutual rows bind `X` once, so both instantiated
payloads are the same ground term and one variable index serves both sides. -/
theorem contraryMatch_rootConclusion_iff {p q : Lara.Atom}
    (hp : RootConclusion p) (hq : RootConclusion q) :
    ContraryMatch id m2bPolicy.defeat p q ↔
      (∃ v, p = litAtom 0 v ∧ q = litAtom 1 v) ∨
      (∃ v, p = litAtom 1 v ∧ q = litAtom 0 v) ∨
      (∃ j, p = clauseAtom j ∧ q = queryAtom) := by
  constructor
  · intro h
    obtain ⟨ab, hab, ρ, pa, pb, hpa, hpb, hep, heq⟩ := h
    rw [equiv_id_eq hep] at hpa
    rw [equiv_id_eq heq] at hpb
    clear hep heq
    rw [m2bDefeat_contraries] at hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
    rcases hab with rfl | rfl | rfl | rfl | rfl | rfl
    · -- `d → b(X)`: the source pattern head is `d`, never a root conclusion
      obtain ⟨ts, rfl⟩ := instAPat_head hpa
      rcases hp with ⟨s, v, hpv⟩ | ⟨j, hpv⟩ | hpv <;>
        simp [litAtom_eq, clauseAtom_eq, queryAtom_eq] at hpv
    · -- `b(X) → a(Y)`: head `b`
      obtain ⟨ts, rfl⟩ := instAPat_head hpa
      rcases hp with ⟨s, v, hpv⟩ | ⟨j, hpv⟩ | hpv <;>
        simp [litAtom_eq, clauseAtom_eq, queryAtom_eq] at hpv
    · -- `lit(0,X) → lit(1,X)`: `X` is bound once, both payloads are `ρ(X)`
      cases hx : lookupSubst ρ ⟨"X"⟩ with
      | none => simp [instAPat, instPats, instPat, hx] at hpa
      | some t =>
          simp only [instAPat, instPats, instPat, hx, Option.map_some,
            Option.some.injEq] at hpa hpb
          subst hpa
          subst hpb
          rcases hp with ⟨s, v, hpv⟩ | ⟨j, hpv⟩ | hpv
          · rw [litAtom_eq] at hpv
            simp only [Lara.Atom.atom.injEq, Lara.Terms.cons.injEq,
              true_and, and_true] at hpv
            obtain ⟨-, rfl⟩ := hpv
            exact Or.inl ⟨v, by rw [litAtom_eq]; rfl, by rw [litAtom_eq]; rfl⟩
          · rw [clauseAtom_eq] at hpv
            simp at hpv
          · rw [queryAtom_eq] at hpv
            simp at hpv
    · -- `lit(1,X) → lit(0,X)`: symmetric
      cases hx : lookupSubst ρ ⟨"X"⟩ with
      | none => simp [instAPat, instPats, instPat, hx] at hpa
      | some t =>
          simp only [instAPat, instPats, instPat, hx, Option.map_some,
            Option.some.injEq] at hpa hpb
          subst hpa
          subst hpb
          rcases hp with ⟨s, v, hpv⟩ | ⟨j, hpv⟩ | hpv
          · rw [litAtom_eq] at hpv
            simp only [Lara.Atom.atom.injEq, Lara.Terms.cons.injEq,
              true_and, and_true] at hpv
            obtain ⟨-, rfl⟩ := hpv
            exact Or.inr (Or.inl
              ⟨v, by rw [litAtom_eq]; rfl, by rw [litAtom_eq]; rfl⟩)
          · rw [clauseAtom_eq] at hpv
            simp at hpv
          · rw [queryAtom_eq] at hpv
            simp at hpv
    · -- `lit(S,X) → occ(S,X)`: the target pattern head is `occ`, never a
      -- root conclusion
      obtain ⟨ts, rfl⟩ := instAPat_head hpb
      rcases hq with ⟨s, v, hqv⟩ | ⟨j, hqv⟩ | hqv <;>
        simp [litAtom_eq, clauseAtom_eq, queryAtom_eq] at hqv
    · -- `clause(J) → query`
      obtain ⟨ts, rfl⟩ := instAPat_head hpa
      simp only [instAPat, instPats, Option.map_some,
        Option.some.injEq] at hpb
      rcases hp with ⟨s, v, hpv⟩ | ⟨j, hpv⟩ | hpv
      · simp [litAtom_eq] at hpv
      · exact Or.inr (Or.inr ⟨j, hpv,
          by rw [queryAtom_eq]; exact hpb.symm⟩)
      · simp [queryAtom_eq] at hpv
  · rintro (⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ | ⟨j, rfl, rfl⟩)
    · exact contraryMatch_negLit_posLit v
    · exact contraryMatch_posLit_negLit v
    · exact contraryMatch_clause_query j

/- Converse membership for the declared attack families, at the same witnesses
the argument generators consume.  (Public: the coverage step below and the
compile-image proofs in `Lara.Complexity.Reduction` both exhibit these.) -/

theorem undermine_negLit_mem {φ : Formula3} {v : Nat}
    (hv : v ∈ φ.occurringVariables) :
    Attack.Attack.undermine (negativeLiteralArg v) (positiveLiteralArg v) []
      ∈ formulaAttacks φ := by
  rw [formulaAttacks]
  exact List.mem_append_left _ (List.mem_flatMap_of_mem hv (by simp))

theorem undermine_posLit_mem {φ : Formula3} {v : Nat}
    (hv : v ∈ φ.occurringVariables) :
    Attack.Attack.undermine (positiveLiteralArg v) (negativeLiteralArg v) []
      ∈ formulaAttacks φ := by
  rw [formulaAttacks]
  exact List.mem_append_left _ (List.mem_flatMap_of_mem hv (by simp))

theorem undermine_clause_query_mem {φ : Formula3} {c : Clause3}
    {j : Nat} (hc : (c, j) ∈ φ.zipIdx) :
    Attack.Attack.undermine (clauseArgument j c) queryArg []
      ∈ formulaAttacks φ := by
  rw [formulaAttacks]
  exact List.mem_append_right _ (List.mem_flatMap_of_mem hc
    (List.mem_append_right _ List.mem_cons_self))

/-- The positional occurrence undermine is declared, at its clause and literal
`zipIdx` witnesses.  (Public for the compile-image proofs in
`Lara.Complexity.Reduction`.) -/
theorem undermine_literal_occurrence_mem {φ : Formula3} {c : Clause3}
    {j : Nat} {l : Literal} {p : Nat}
    (hc : (c, j) ∈ φ.zipIdx) (hl : (l, p) ∈ c.literals.zipIdx) :
    Attack.Attack.undermine (literalArg l) (clauseArgument j c) [.prem p]
      ∈ formulaAttacks φ := by
  rw [formulaAttacks]
  exact List.mem_append_right _ (List.mem_flatMap_of_mem hc
    (List.mem_append_left _ (List.mem_map.mpr ⟨(l, p), hl, rfl⟩)))

/-- **Exact attack completeness.**  Every contrary conflict between supported
generated arguments is covered by a declared attack: the characterization
reduces any firing pair to the mutual literal-root family or the clause-root
undermine of the query, and each is declared at the root path with the
attacked occurrence equal to the target itself. -/
theorem formulaAttacks_complete (φ : Formula3) :
    Compile.AttackComplete id m2bPolicy.ruleLookup (gammaOfFormula φ)
      (Support.certOkOf m2bRegistry) m2bPolicy.defeat
      (rawUnitOfFormula φ).args (rawUnitOfFormula φ).atts := by
  intro source hsource target htarget sC tC hsupS hsupT hcon _
  rcases (contraryMatch_rootConclusion_iff
      (rootConclusion_of_argument hsource hsupS)
      (rootConclusion_of_argument htarget hsupT)).mp hcon with
    ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ | ⟨j, rfl, rfl⟩
  · -- source concludes `lit(0,v)`, target concludes `lit(1,v)`
    rcases formulaArgument_conclusion φ hsource hsupS with
      ⟨v', hv', ⟨rfl, hCs⟩ | ⟨-, hCs⟩⟩ | ⟨c, j', -, -, hCs⟩ | ⟨-, hCs⟩
    · obtain rfl : v = v' := (litAtom_inj hCs).2
      rcases formulaArgument_conclusion φ htarget hsupT with
        ⟨u', -, ⟨-, hCt⟩ | ⟨rfl, hCt⟩⟩ | ⟨c, j', -, -, hCt⟩ | ⟨-, hCt⟩
      · exact absurd (litAtom_inj hCt).1 (by decide)
      · obtain rfl : v = u' := (litAtom_inj hCt).2
        exact ⟨Attack.Attack.undermine (negativeLiteralArg v)
            (positiveLiteralArg v) [],
          undermine_negLit_mem hv', rfl, positiveLiteralArg v, rfl,
          Compile.contains_refl _⟩
      · simp [litAtom_eq, clauseAtom_eq] at hCt
      · simp [litAtom_eq, queryAtom_eq] at hCt
    · exact absurd (litAtom_inj hCs).1 (by decide)
    · simp [litAtom_eq, clauseAtom_eq] at hCs
    · simp [litAtom_eq, queryAtom_eq] at hCs
  · -- source concludes `lit(1,v)`, target concludes `lit(0,v)`
    rcases formulaArgument_conclusion φ hsource hsupS with
      ⟨v', hv', ⟨-, hCs⟩ | ⟨rfl, hCs⟩⟩ | ⟨c, j', -, -, hCs⟩ | ⟨-, hCs⟩
    · exact absurd (litAtom_inj hCs).1 (by decide)
    · obtain rfl : v = v' := (litAtom_inj hCs).2
      rcases formulaArgument_conclusion φ htarget hsupT with
        ⟨u', -, ⟨rfl, hCt⟩ | ⟨-, hCt⟩⟩ | ⟨c, j', -, -, hCt⟩ | ⟨-, hCt⟩
      · obtain rfl : v = u' := (litAtom_inj hCt).2
        exact ⟨Attack.Attack.undermine (positiveLiteralArg v)
            (negativeLiteralArg v) [],
          undermine_posLit_mem hv', rfl, negativeLiteralArg v, rfl,
          Compile.contains_refl _⟩
      · exact absurd (litAtom_inj hCt).1 (by decide)
      · simp [litAtom_eq, clauseAtom_eq] at hCt
      · simp [litAtom_eq, queryAtom_eq] at hCt
    · simp [litAtom_eq, clauseAtom_eq] at hCs
    · simp [litAtom_eq, queryAtom_eq] at hCs
  · -- source concludes `clause(j)`, target concludes `query`
    rcases formulaArgument_conclusion φ hsource hsupS with
      ⟨v', -, ⟨-, hCs⟩ | ⟨-, hCs⟩⟩ | ⟨c, j', hcj, rfl, -⟩ | ⟨-, hCs⟩
    · simp [litAtom_eq, clauseAtom_eq] at hCs
    · simp [litAtom_eq, clauseAtom_eq] at hCs
    · rcases formulaArgument_conclusion φ htarget hsupT with
        ⟨u', -, ⟨-, hCt⟩ | ⟨-, hCt⟩⟩ | ⟨c', j'', -, -, hCt⟩ | ⟨rfl, -⟩
      · simp [litAtom_eq, queryAtom_eq] at hCt
      · simp [litAtom_eq, queryAtom_eq] at hCt
      · simp [clauseAtom_eq, queryAtom_eq] at hCt
      · exact ⟨Attack.Attack.undermine (clauseArgument j' c) queryArg [],
          undermine_clause_query_mem hcj, rfl, queryArg, rfl,
          Compile.contains_refl _⟩
    · simp [clauseAtom_eq, queryAtom_eq] at hCs

/-! ## The family-wide checker equation

Every premise of `Check.Unit.checkUnit_complete` is discharged family-wide by
the lemmas above and the fixed-context facts of `Lara.Complexity.Context`, so
acceptance assembles in one application; naming the
accepted unit then turns the existential into the executable checker equation
`Realization.checked` requires. -/

/-- Assembled acceptance: the ten discharged premises, in the checker's public
fixed order. -/
theorem checkUnit_formula_accepts (φ : Formula3) :
    ∃ accepted, Check.Unit.checkUnit (gammaOfFormula φ) m2bRegistry
      (groundOfFormula φ) (rawUnitOfFormula φ) = .ok accepted :=
  Check.Unit.checkUnit_complete
    (signatureStage_formula_none φ)
    m2bPolicy_scopesWellFormed
    ((Policy.firstDuplicateRuleId?_none_iff m2bPolicy.rules).mp
      m2bPolicy_ruleIds_unique)
    ((Policy.firstViolation_none_iff).mp m2bPolicy_noViolation)
    (formulaArguments_nodup φ)
    (formulaArguments_supported φ)
    (hasAttack_formula φ)
    (formulaAttacks_source_mem φ)
    (formulaAttacks_target_mem φ)
    (formulaAttacks_complete φ)

/-- The accepted checker output, named once for the whole generated family. -/
def acceptedUnitOfFormula (φ : Formula3) :
    Lara.Unit.CheckedUnit id (gammaOfFormula φ) (Support.certOkOf m2bRegistry) :=
  Check.Unit.okValue (checkUnit_formula_accepts φ)

/-- **The family-wide checker equation.**  For every formula, the frozen M2b
context accepts the generated raw unit through the public executable
checker. -/
theorem checkUnit_formula_ok (φ : Formula3) :
    Check.Unit.checkUnit (gammaOfFormula φ) m2bRegistry
      (groundOfFormula φ) (rawUnitOfFormula φ) = .ok (acceptedUnitOfFormula φ) :=
  Check.Unit.okValue_eq (checkUnit_formula_accepts φ)

end Lara.Complexity
