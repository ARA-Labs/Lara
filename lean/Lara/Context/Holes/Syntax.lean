import Lara.Support

/-! An additive syntax for critical-question answer holes. Core terms retain
their original meaning; only explicitly named answer slots are substituted. -/
namespace Lara.Context.Holes

open Lara.Support

structure HoleId where
  name : String
deriving DecidableEq

mutual
  inductive Template where
    | core : SupportTerm → Template
    | inst : RuleId → Subst → List Template →
        List (QuestionId × AnswerTemplate) → List QuestionId → Assurance → Template
  inductive AnswerTemplate where
    | term : Template → AnswerTemplate
    | hole : HoleId → AnswerTemplate
end

abbrev Filling := List (HoleId × SupportTerm)
abbrev HoleSignature := HoleId → Option Atom

inductive HoleError where
  | duplicate : HoleId → HoleError
  | missing : HoleId → HoleError
deriving DecidableEq

def lookupFilling : Filling → HoleId → Option SupportTerm
  | [], _ => none
  | (k, w) :: rest, h => if k = h then some w else lookupFilling rest h

def firstDuplicate : Filling → Option HoleId
  | [] => none
  | (h, _) :: rest =>
      if (rest.map Prod.fst).contains h then some h else firstDuplicate rest

def FillingNodup (ρ : Filling) : Prop := (ρ.map Prod.fst).Nodup

def DisjointFillings (ρ σ : Filling) : Prop :=
  ∀ h, h ∈ ρ.map Prod.fst → h ∉ σ.map Prod.fst

mutual
  def eraseOpen : Template → SupportTerm
    | .core w => w
    | .inst rn θ ws D H α =>
        .inst rn θ (eraseList ws) (eraseDis D) (H ++ holeKeys D) α
  def eraseList : List Template → List SupportTerm
    | [] => []
    | t :: ts => eraseOpen t :: eraseList ts
  def eraseDis : List (QuestionId × AnswerTemplate) → List (QuestionId × SupportTerm)
    | [] => []
    | (q, .term t) :: rest => (q, eraseOpen t) :: eraseDis rest
    | (_, .hole _) :: rest => eraseDis rest
  def holeKeys : List (QuestionId × AnswerTemplate) → List QuestionId
    | [] => []
    | (_, .term _) :: rest => holeKeys rest
    | (q, .hole _) :: rest => q :: holeKeys rest
end

mutual
  def subst (ρ : Filling) : Template → Template
    | .core w => .core w
    | .inst rn θ ws D H α => .inst rn θ (substList ρ ws) (substDis ρ D) H α
  def substAnswer (ρ : Filling) : AnswerTemplate → AnswerTemplate
    | .term t => .term (subst ρ t)
    | .hole h => match lookupFilling ρ h with
      | some w => .term (.core w)
      | none => .hole h
  def substList (ρ : Filling) : List Template → List Template
    | [] => []
    | t :: ts => subst ρ t :: substList ρ ts
  def substDis (ρ : Filling) : List (QuestionId × AnswerTemplate) →
      List (QuestionId × AnswerTemplate)
    | [] => []
    | (q, a) :: rest => (q, substAnswer ρ a) :: substDis ρ rest
end

mutual
  def instantiateAux (ρ : Filling) : Template → Except HoleError SupportTerm
    | .core w => .ok w
    | .inst rn θ ws D H α => do
        let ws' ← instantiateList ρ ws
        let D' ← instantiateDis ρ D
        return .inst rn θ ws' D' H α
  def instantiateAnswer (ρ : Filling) : AnswerTemplate → Except HoleError SupportTerm
    | .term t => instantiateAux ρ t
    | .hole h => match lookupFilling ρ h with
      | some w => .ok w
      | none => .error (.missing h)
  def instantiateList (ρ : Filling) : List Template → Except HoleError (List SupportTerm)
    | [] => .ok []
    | t :: ts => do
        let w ← instantiateAux ρ t
        let ws ← instantiateList ρ ts
        return w :: ws
  def instantiateDis (ρ : Filling) : List (QuestionId × AnswerTemplate) →
      Except HoleError (List (QuestionId × SupportTerm))
    | [] => .ok []
    | (q, a) :: rest => do
        let w ← instantiateAnswer ρ a
        let D ← instantiateDis ρ rest
        return (q, w) :: D
end

/-- Reject ambiguous tables before reading any slot. Type checking of the
instantiated support term remains the existing checker's responsibility. -/
def instantiate (ρ : Filling) (t : Template) : Except HoleError SupportTerm :=
  match firstDuplicate ρ with
  | some h => .error (.duplicate h)
  | none => instantiateAux ρ t

theorem firstDuplicate_none_iff (ρ : Filling) :
    firstDuplicate ρ = none ↔ FillingNodup ρ := by
  induction ρ with
  | nil => simp [firstDuplicate, FillingNodup]
  | cons p rest ih =>
    rcases p with ⟨h, w⟩
    simp only [firstDuplicate, FillingNodup, List.map_cons, List.nodup_cons] at *
    by_cases hm : h ∈ rest.map Prod.fst
    · simp [hm]
    · simp [hm, ih]

theorem instantiate_eq_aux {ρ : Filling} (hρ : FillingNodup ρ) (t : Template) :
    instantiate ρ t = instantiateAux ρ t := by
  simp [instantiate, (firstDuplicate_none_iff ρ).mpr hρ]

theorem instantiate_core {ρ : Filling} (hρ : FillingNodup ρ) (w : SupportTerm) :
    instantiate ρ (.core w) = .ok w := by
  rw [instantiate_eq_aux hρ]; rfl

theorem eraseOpen_core (w : SupportTerm) : eraseOpen (.core w) = w := rfl

theorem lookupFilling_append (ρ σ : Filling) (h : HoleId) :
    lookupFilling (ρ ++ σ) h = (lookupFilling ρ h).or (lookupFilling σ h) := by
  induction ρ with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨k, w⟩
    simp only [List.cons_append, lookupFilling]
    split <;> simp_all

/- Left-biased substitution composes even without disjointness: a supplied
core answer contains no template hole for the second substitution to change. -/
mutual
  theorem subst_append (ρ σ : Filling) (t : Template) :
      subst (ρ ++ σ) t = subst σ (subst ρ t) := by
    cases t with
    | core w => rfl
    | inst rn θ ws D H α =>
      simp only [subst, substList_append, substDis_append]
  theorem substAnswer_append (ρ σ : Filling) (a : AnswerTemplate) :
      substAnswer (ρ ++ σ) a = substAnswer σ (substAnswer ρ a) := by
    cases a with
    | term t => simp only [substAnswer, subst_append]
    | hole h =>
      simp only [substAnswer, lookupFilling_append]
      cases lookupFilling ρ h <;> simp [Option.or, substAnswer, subst]
  theorem substList_append (ρ σ : Filling) (ts : List Template) :
      substList (ρ ++ σ) ts = substList σ (substList ρ ts) := by
    cases ts with
    | nil => rfl
    | cons t ts => simp only [substList, subst_append, substList_append]
  theorem substDis_append (ρ σ : Filling) (D : List (QuestionId × AnswerTemplate)) :
      substDis (ρ ++ σ) D = substDis σ (substDis ρ D) := by
    cases D with
    | nil => rfl
    | cons p rest =>
      rcases p with ⟨q, a⟩
      simp only [substDis, substAnswer_append, substDis_append]
end

theorem fillingNodup_append {ρ σ : Filling}
    (hρ : FillingNodup ρ) (hσ : FillingNodup σ) (hd : DisjointFillings ρ σ) :
    FillingNodup (ρ ++ σ) := by
  rw [FillingNodup, List.map_append, List.nodup_append]
  exact ⟨hρ, hσ, fun h hh k hk heq => hd h hh (heq ▸ hk)⟩

end Lara.Context.Holes
