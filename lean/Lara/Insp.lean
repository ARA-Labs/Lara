/-
The static code-inspection domain-checker backend `insp@1` (design
records: `docs/strict-backend-decision.md` for the backend seam and
`docs/insp1-code-inspection-decision.md` for what an accepted step certifies).

The adapter certifies the corpus's third measured strict shape — structural
facts about referenced source — as a closed four-predicate family over
*declared exhaustive inventories*:

  * `code_absent(Src, Feat)`                    — `Feat` occurs nowhere in `Src`
  * `code_present(Src, Feat)`                   — `Feat` occurs in `Src`
  * `code_unique(Src, Feat)`                    — `Feat` is all that `Src` holds
  * `code_planned_not_shipped(Plan, Src, Feat)` — the plan-vs-shipped diff

The slot-reference sub-grammar `(prem N)` and the indexed-lookup lemma come
from `Lara.Cell`; nothing else does, because this backend has no numbers in it.
The whole development stays in core Lean: no Mathlib.

## What is being certified

The load-bearing step is the **closed-world move**.  A negative existential
over code — "the shipped module has no repair call site anywhere" — is not an
observation but an inference from an exhaustive enumeration: *given* that the
inspection covered the whole unit and enumerated everything it found, absence
follows deductively.  The enumeration arrives as an ordinary premise carrying

    inv(Src, finding(f₁, finding(f₂, no_findings)))

and `inspModels` says exactly what that premise licenses — no more.  In
particular nothing here asserts that an inventory is faithful to any bytes;
byte-level evidence admission is not part of v0.1 (spec §4.3), so an inventory
is an *evidence declared* leaf and stays defeasible.  That is the factivity
firewall for this backend, and it is why the corpus's own `plan_vs_shipped_diff`
unit still ends in a `gap`.

The `Backend` obligations are discharged the way `Lara.Ord` does it:

  * `enc` is `nf canon` itself — the identity encoding on normalized atoms —
    so `enc_iff` is exactly `equiv_iff_nf_eq`;
  * `replayFull` decodes the exact submitted certificate and runs the
    decidable structural check (`checkB`); acceptance is the proposition-level
    mirror, and `replayFull_iff` is a case split;
  * `soundFull` repackages the facts `checkB` pins down.  There is no witness
    value, so nothing has to be cancelled;
  * the certificate names its consulted slots outright, so the obligation-4
    laws (`uses_covers` / `uses_valid` / `uses_account`) follow from `checkB`
    touching the context only through those lookups.

## Premise-only slots, and how they are modelled here

The Haskell adapter rejects any certificate slot `≥ nPrem`, so a certificate
cannot cite a self-supplied theory entry as if it were an inspection result.
That guard carries more weight here than in either arithmetic sibling: the
value it protects is the closed-world premise itself, and a theory entry
asserting "I inspected everything and found nothing" would never be seen by a
leaf or admission check.

The abstract `Backend` core is handed a single context `Γ = Δ ++ T` and never
learns `Δ.length`, so the guard is not expressible at this layer.  It does not
need to be: `Lara.Driver.buildRegistry` resolves any *known* `insp@1` digest to
`[]` (an unknown digest still fails to resolve, which is a rejection), so
`Γ = Δ ++ [] = Δ` and the two sides accept exactly the same certificates — the
same modelling `ra@1` and `ord@1` already use.

## Why this family declares a contrary pair and `ord@1` does not

`Lara.Ord.ordModels_excl_of_lt` shows that a sound comparison backend can never
accept two conflicting members of its family: comparison goals are decided
against a *shared* ground truth, the numerals in the goal itself.  Inspection
goals are decided against a *declared* inventory, and two units may declare
different inventories for the same source.  Both halves are stated below:
`inspModels_excl_of_same_entry` (exclusive when the two arguments read the same
inspection leaf) and `inspModels_absent_present_sat` (jointly satisfiable when
they do not).  So `code_absent` / `code_present` must be declared a contrary
pair in the policy — the conflict is real, and only the attack layer can carry
it.
-/

import Lara.Cell

namespace Lara.Insp

open Lara.Support (SExpr CertRef)
open Lara.Strict (selectSlots sourceTermsToList)
open Lara.Cell (decodeSlot lt_of_getElem?_eq_some)

/-! ### The closed goal family

Three one-inventory members and one two-inventory diff.  The concrete
spellings live in exactly one table each (`Rel.pred`, `diffPred`). -/

/-- The closed one-inventory family: the three statements a single exhaustive
enumeration settles. -/
inductive Rel where
  | absent | present | unique
deriving DecidableEq, Repr

/-- The goal predicate spelling of each one-inventory family member. -/
def Rel.pred : Rel → String
  | .absent => "code_absent"
  | .present => "code_present"
  | .unique => "code_unique"

def Rel.all : List Rel := [.absent, .present, .unique]

/-- Recognize a one-inventory family predicate, inverse to `Rel.pred`. -/
def Rel.parse (s : String) : Option Rel := Rel.all.find? (fun r => r.pred = s)

/-- The two-inventory diff predicate — the corpus's `plan_vs_shipped_diff`
shape, spelled for the domain reader (spec §4.5 naming taste). -/
def diffPred : String := "code_planned_not_shipped"

/-- The relation each one-inventory member asserts of the enumerated findings.

`absent` over an empty inventory is the pure negative existential
(`relHolds_absent_of_nil`) — an exhaustive inspection that found nothing
certifies every absence, and that is the closed-world step this backend exists
to replay. -/
def RelHolds : Rel → List Lara.Term → Lara.Term → Prop
  | .absent, fs, f => f ∉ fs
  | .present, fs, f => f ∈ fs
  | .unique, fs, f => fs ≠ [] ∧ ∀ g ∈ fs, g = f

def relHoldsB : Rel → List Lara.Term → Lara.Term → Bool
  | .absent, fs, f => decide (f ∉ fs)
  | .present, fs, f => decide (f ∈ fs)
  | .unique, fs, f => decide (fs ≠ [] ∧ ∀ g ∈ fs, g = f)

theorem relHoldsB_iff (r : Rel) (fs : List Lara.Term) (f : Lara.Term) :
    relHoldsB r fs f = true ↔ RelHolds r fs f := by
  cases r <;> simp [relHoldsB, RelHolds]

/-! ### The goal shape -/

/-- The parsed goal: a one-inventory member over `(Src, Feat)`, or the
two-inventory diff. -/
inductive Goal where
  | one : Rel → Lara.Term → Lara.Term → Goal
  | diff : Lara.Term → Lara.Term → Lara.Term → Goal
deriving DecidableEq

/-- Parse the normalized goal.  Arity is part of the family: a one-inventory
predicate at arity 3, or the diff predicate at arity 2, is not this backend's
goal shape. -/
def parseGoal : Lara.Atom → Option Goal
  | .atom p ts =>
      match sourceTermsToList ts with
      | [src, feat] =>
          match Rel.parse p with
          | some r => some (.one r src feat)
          | none => none
      | [plan, src, feat] => if p = diffPred then some (.diff plan src feat) else none
      | _ => none

/-! ### The source-level inventory vocabulary

`Σ` fixes each constructor's arity (spec §2), so the enumeration is a cons
spine of three fixed-arity symbols rather than one variadic constructor:
`inv`/2, `finding`/2, `no_findings`/0.  A unit declares them in its signature
and the sort checker checks them; here they are reserved spellings, in exactly
one table. -/

/-- The closed set of source constructor spellings the inventory convention
reserves. -/
inductive Con where
  | inv | finding | noFindings
deriving DecidableEq, Repr

def Con.toString : Con → String
  | .inv => "inv"
  | .finding => "finding"
  | .noFindings => "no_findings"

def Con.all : List Con := [.inv, .finding, .noFindings]

def Con.parse (s : String) : Option Con := Con.all.find? (fun c => c.toString = s)

/-- A decoded inventory: the inspected source unit and the exhaustive list of
findings.  The list order is the author's; nothing in the family depends on it,
and repeated findings are harmless. -/
structure Inventory where
  src : Lara.Term
  findings : List Lara.Term
deriving DecidableEq

/-! Every `inv(…)` node anywhere in a term, outermost first.  The scan does
**not** stop at a match: a nested `inv` inside a finding is a second node, and
`premiseInventory` rejects the premise for it — which is what keeps "the
premise carries one inventory" unambiguous. -/
mutual
  def termInvNodes : Lara.Term → List Lara.Term
    | .num _ => []
    | .str _ => []
    | .con k ts =>
        (if Con.parse k = some .inv then [Lara.Term.con k ts] else []) ++
          termsInvNodes ts

  def termsInvNodes : Lara.Terms → List Lara.Term
    | .nil => []
    | .cons t ts => termInvNodes t ++ termsInvNodes ts
end

/-- Parse the finding spine `finding(F₁, finding(…, no_findings))` into the
enumerated findings.  Anything else — a wrong arity, a foreign constructor, a
literal in tail position — is a rejection: the adapter refuses to guess how far
the enumeration reached. -/
def parseFindings : Lara.Term → Option (List Lara.Term)
  | .con k .nil => if Con.parse k = some .noFindings then some [] else none
  | .con k (.cons f (.cons rest .nil)) =>
      if Con.parse k = some .finding then (parseFindings rest).map (f :: ·) else none
  | _ => none

/-- The inventory convention: the consulted context entry must contain exactly
one `inv(Src, Findings)` node anywhere in its argument terms, and that node's
second argument must be a well-formed finding spine.

The "exactly one" discipline is `Lara.Cell.premiseCell`'s, for the same reason:
an entry carrying two inventories does not say which one the certificate meant,
and guessing is how a checker becomes unsound quietly. -/
def premiseInventory : Lara.Atom → Option Inventory
  | .atom _ ts =>
      match termsInvNodes ts with
      | [.con _ (.cons src (.cons findings .nil))] =>
          (parseFindings findings).map (fun fs => ⟨src, fs⟩)
      | _ => none

/-! ### The certificate wire grammar (the closed decoder)

    cert := (inspect (prem N))                 -- the one-inventory members
          | (inspectdiff (prem N) (prem M))    -- the plan-vs-shipped diff

There is no witness value: the certificate names slots and nothing else, and
the relation is read off the goal predicate.  What the certificate *does* fix
is the arity of the step, which is why the family's two shapes get two wire
keywords — an `(inspect …)` payload under a diff goal is a rejection, not a
re-interpretation. -/

/-- The closed set of `insp@1`-specific wire keywords (`Lara.ND.Tag`
discipline).  The shared slot keyword `prem` lives in `Lara.Cell.Tag`. -/
inductive Tag where
  | inspect | inspectdiff
deriving DecidableEq, Repr

def Tag.toString : Tag → String
  | .inspect => "inspect"
  | .inspectdiff => "inspectdiff"

def Tag.all : List Tag := [.inspect, .inspectdiff]

def Tag.parse (s : String) : Option Tag :=
  Tag.all.find? (fun t => t.toString = s)

/-- A decoded certificate: the consulted slots, one shape per family arity. -/
inductive Cert where
  | one : Nat → Cert
  | diff : Nat → Nat → Cert
deriving DecidableEq, Repr

def decodeCert : SExpr → Option Cert
  | .list [.atom k, s] =>
      match Tag.parse k with
      | some .inspect => (decodeSlot s).map .one
      | _ => none
  | .list [.atom k, sP, sS] =>
      match Tag.parse k with
      | some .inspectdiff => do
          let nP ← decodeSlot sP
          let nS ← decodeSlot sS
          some (.diff nP nS)
      | _ => none
  | _ => none

/-! ### The executable check -/

/-- The decidable inspection check, mirroring the Haskell adapter's `run`: the
goal parses to the family member matching the certificate's arity, the named
slots resolve and carry inventories of the source units the goal names, and the
goal's structural statement holds of the enumerated findings.  The context is
consulted **only** through the named slots — the coverage law reads this off
the definition. -/
def checkOne (n : Nat) (Γ : List Lara.Atom) (φ : Lara.Atom) : Bool :=
  match parseGoal φ, Γ[n]? with
  | some (.one rel src feat), some p =>
      match premiseInventory p with
      | some iv => decide (iv.src = src) && relHoldsB rel iv.findings feat
      | none => false
  | _, _ => false

/-- The diff arm: the plan slot must enumerate the feature and the source slot
must not, each against the unit the goal names for it. -/
def checkDiff (n m : Nat) (Γ : List Lara.Atom) (φ : Lara.Atom) : Bool :=
  match parseGoal φ, Γ[n]?, Γ[m]? with
  | some (.diff plan src feat), some pP, some pS =>
      match premiseInventory pP, premiseInventory pS with
      | some ivP, some ivS =>
          decide (ivP.src = plan) && decide (ivS.src = src) &&
            relHoldsB .present ivP.findings feat &&
            relHoldsB .absent ivS.findings feat
      | _, _ => false
  | _, _, _ => false

/-- The replay proper: the certificate's arity selects the arm, and a
certificate whose arity does not match the goal's family member is a rejection
rather than a re-interpretation. -/
def checkB : Cert → List Lara.Atom → Lara.Atom → Bool
  | .one n, Γ, φ => checkOne n Γ φ
  | .diff n m, Γ, φ => checkDiff n m Γ φ

/-! ### The proposition layer -/

/-- Mathematical consequence for the `insp@1` backend: the goal parses as a
family member, and some context entries carry inventories of the named source
units under which the goal's structural statement holds.

Note what this does *and does not* say (the factivity firewall).  What the
context supplies is a **declared exhaustive enumeration**; the conclusion is
what follows from it deductively.  Nothing here asserts that the enumeration is
faithful to any source bytes, or that it read the version of the source the
claim is about — those stay defeasible measurement questions at the leaf and
admission layers. -/
def inspModels (Γ : List Lara.Atom) (φ : Lara.Atom) : Prop :=
  (∃ (rel : Rel) (src feat : Lara.Term) (i : Nat) (p : Lara.Atom) (iv : Inventory),
      parseGoal φ = some (.one rel src feat) ∧
      Γ[i]? = some p ∧ premiseInventory p = some iv ∧
      iv.src = src ∧ RelHolds rel iv.findings feat)
  ∨ (∃ (plan src feat : Lara.Term) (i j : Nat) (pP pS : Lara.Atom)
       (ivP ivS : Inventory),
      parseGoal φ = some (.diff plan src feat) ∧
      Γ[i]? = some pP ∧ Γ[j]? = some pS ∧
      premiseInventory pP = some ivP ∧ premiseInventory pS = some ivS ∧
      ivP.src = plan ∧ ivS.src = src ∧
      RelHolds .present ivP.findings feat ∧ RelHolds .absent ivS.findings feat)

/-- Acceptance of the exact submitted certificate. -/
def inspAccepts (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom) : Prop :=
  ∃ c, decodeCert κ.payload = some c ∧ checkB c Γ φ = true

/-- Decode and check the exact submitted certificate; no search occurs. -/
def inspReplay (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom) : Bool :=
  match decodeCert κ.payload with
  | none => false
  | some c => checkB c Γ φ

theorem inspReplay_iff (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom) :
    inspReplay κ Γ φ = true ↔ inspAccepts κ Γ φ := by
  cases hdec : decodeCert κ.payload with
  | none => simp [inspReplay, inspAccepts, hdec]
  | some c => simp [inspReplay, inspAccepts, hdec]

/-- Reported dependency slots: the slots the certificate names.  A function of
the certificate alone; an undecodable certificate reports nothing (it is never
accepted).  A same-slot diff certificate reports that slot twice here;
`selectSlots` and the Haskell `Set` both collapse it to one dependency. -/
def inspUses (κ : CertRef) : List Nat :=
  match decodeCert κ.payload with
  | none => []
  | some (.one n) => [n]
  | some (.diff n m) => [n, m]

/-! ### Extraction -/

/-- Everything a passing one-inventory `checkB` pins down, in proposition
form. -/
theorem checkB_one_extract {n : Nat} {Γ : List Lara.Atom} {φ : Lara.Atom}
    (h : checkOne n Γ φ = true) :
    ∃ (rel : Rel) (src feat : Lara.Term) (p : Lara.Atom) (iv : Inventory),
      parseGoal φ = some (.one rel src feat) ∧
      Γ[n]? = some p ∧ premiseInventory p = some iv ∧
      iv.src = src ∧ RelHolds rel iv.findings feat := by
  unfold checkOne at h
  split at h
  case _ rel src feat p hgoal hp =>
    split at h
    case _ iv hiv =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, relHoldsB_iff] at h
      exact ⟨rel, src, feat, p, iv, hgoal, hp, hiv, h.1, h.2⟩
    case _ => exact absurd h (by simp)
  case _ => exact absurd h (by simp)

/-- Everything a passing diff `checkB` pins down, in proposition form. -/
theorem checkB_diff_extract {n m : Nat} {Γ : List Lara.Atom} {φ : Lara.Atom}
    (h : checkDiff n m Γ φ = true) :
    ∃ (plan src feat : Lara.Term) (pP pS : Lara.Atom) (ivP ivS : Inventory),
      parseGoal φ = some (.diff plan src feat) ∧
      Γ[n]? = some pP ∧ Γ[m]? = some pS ∧
      premiseInventory pP = some ivP ∧ premiseInventory pS = some ivS ∧
      ivP.src = plan ∧ ivS.src = src ∧
      RelHolds .present ivP.findings feat ∧ RelHolds .absent ivS.findings feat := by
  unfold checkDiff at h
  split at h
  case _ plan src feat pP pS hgoal hP hS =>
    split at h
    case _ ivP ivS hivP hivS =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, relHoldsB_iff] at h
      obtain ⟨⟨⟨hp, hs⟩, hpres⟩, habs⟩ := h
      exact ⟨plan, src, feat, pP, pS, ivP, ivS, hgoal, hP, hS, hivP, hivS,
        hp, hs, hpres, habs⟩
    case _ => exact absurd h (by simp)
  case _ => exact absurd h (by simp)

/-- Certificate soundness: an accepted certificate's conclusion is a
mathematical consequence of the consulted context. -/
theorem inspSound (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom)
    (hacc : inspAccepts κ Γ φ) : inspModels Γ φ := by
  obtain ⟨c, _, hchk⟩ := hacc
  cases c with
  | one n =>
      obtain ⟨rel, src, feat, p, iv, hgoal, hp, hiv, hsrc, hrel⟩ :=
        checkB_one_extract hchk
      exact Or.inl ⟨rel, src, feat, n, p, iv, hgoal, hp, hiv, hsrc, hrel⟩
  | diff n m =>
      obtain ⟨plan, src, feat, pP, pS, ivP, ivS, hgoal, hP, hS, hivP, hivS,
        hp, hs, hpres, habs⟩ := checkB_diff_extract hchk
      exact Or.inr ⟨plan, src, feat, n, m, pP, pS, ivP, ivS, hgoal, hP, hS,
        hivP, hivS, hp, hs, hpres, habs⟩

/-! ### Obligation 4 -/

/-- Coverage: replay consults the context only at the reported slots —
contexts agreeing there replay identically. -/
theorem inspUses_covers (κ : CertRef) (Γ Γ' : List Lara.Atom) (φ : Lara.Atom)
    (hag : ∀ i, i ∈ inspUses κ → Γ[i]? = Γ'[i]?) :
    inspReplay κ Γ φ = inspReplay κ Γ' φ := by
  cases hdec : decodeCert κ.payload with
  | none => simp [inspReplay, hdec]
  | some c =>
    cases c with
    | one n =>
        have hn : Γ[n]? = Γ'[n]? := hag n (by simp [inspUses, hdec])
        simp only [inspReplay, hdec, checkB, checkOne, hn]
    | diff n m =>
        have hn : Γ[n]? = Γ'[n]? := hag n (by simp [inspUses, hdec])
        have hm : Γ[m]? = Γ'[m]? := hag m (by simp [inspUses, hdec])
        simp only [inspReplay, hdec, checkB, checkDiff, hn, hm]

/-- Validity: on acceptance every reported slot names an entry of the consulted
context. -/
theorem inspUses_valid (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom)
    (hacc : inspAccepts κ Γ φ) : ∀ i, i ∈ inspUses κ → i < Γ.length := by
  obtain ⟨c, hdec, hchk⟩ := hacc
  cases c with
  | one n =>
      obtain ⟨_, _, _, _, _, _, hp, _⟩ := checkB_one_extract hchk
      intro i hi
      simp only [inspUses, hdec, List.mem_cons] at hi
      rcases hi with rfl | hfalse
      · exact lt_of_getElem?_eq_some hp
      · exact absurd hfalse (List.not_mem_nil)
  | diff n m =>
      obtain ⟨_, _, _, _, _, _, _, _, hP, hS, _⟩ := checkB_diff_extract hchk
      intro i hi
      simp only [inspUses, hdec, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact lt_of_getElem?_eq_some hP
      · rcases hi with rfl | hfalse
        · exact lt_of_getElem?_eq_some hS
        · exact absurd hfalse (List.not_mem_nil)

/-- Semantic accounting: an accepted certificate's conclusion follows from just
the reported entries. -/
theorem inspUses_account (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom)
    (hacc : inspAccepts κ Γ φ) : inspModels (selectSlots Γ (inspUses κ)) φ := by
  obtain ⟨c, hdec, hchk⟩ := hacc
  cases c with
  | one n =>
      obtain ⟨rel, src, feat, p, iv, hgoal, hp, hiv, hsrc, hrel⟩ :=
        checkB_one_extract hchk
      have hsel : selectSlots Γ (inspUses κ) = [p] := by
        simp [selectSlots, inspUses, hdec, hp]
      refine Or.inl ⟨rel, src, feat, 0, p, iv, hgoal, ?_, hiv, hsrc, hrel⟩
      rw [hsel]; rfl
  | diff n m =>
      obtain ⟨plan, src, feat, pP, pS, ivP, ivS, hgoal, hP, hS, hivP, hivS,
        hp, hs, hpres, habs⟩ := checkB_diff_extract hchk
      have hsel : selectSlots Γ (inspUses κ) = [pP, pS] := by
        simp [selectSlots, inspUses, hdec, hP, hS]
      refine Or.inr ⟨plan, src, feat, 0, 1, pP, pS, ivP, ivS, hgoal, ?_, ?_,
        hivP, hivS, hp, hs, hpres, habs⟩
      · rw [hsel]; rfl
      · rw [hsel]; rfl

/-! ### The domain theory

What the family means, proved rather than asserted. -/

/-- **The closed-world step.**  An exhaustive inspection that found nothing
certifies every absence.  This is the whole reason the backend exists: the
inference from an empty enumeration to a negative existential is deductive,
where the enumeration itself is not. -/
theorem relHolds_absent_of_nil (f : Lara.Term) : RelHolds .absent [] f := by
  simp [RelHolds]

/-- Uniqueness is stronger than presence: if everything found is `f` and
something was found, then `f` was found. -/
theorem relHolds_present_of_unique {fs : List Lara.Term} {f : Lara.Term}
    (h : RelHolds .unique fs f) : RelHolds .present fs f := by
  obtain ⟨hne, hall⟩ := h
  cases fs with
  | nil => exact absurd rfl hne
  | cons g gs =>
      have hg : g ∈ g :: gs := by simp
      exact (hall g hg) ▸ hg

/-- The two polarities are exclusive **of one and the same enumeration**.  The
qualifier is the whole content: see `inspModels_excl_of_same_entry` and
`inspModels_absent_present_sat` for what it does and does not extend to. -/
theorem relHolds_polarity_excl {fs : List Lara.Term} {f : Lara.Term}
    (h1 : RelHolds .absent fs f) (h2 : RelHolds .present fs f) : False := h1 h2

/-- A uniqueness claim and an absence claim over the same enumeration are
exclusive, via presence. -/
theorem relHolds_unique_absent_excl {fs : List Lara.Term} {f : Lara.Term}
    (h1 : RelHolds .unique fs f) (h2 : RelHolds .absent fs f) : False :=
  relHolds_polarity_excl h2 (relHolds_present_of_unique h1)

/-- **The diff decomposes.**  `code_planned_not_shipped` is exactly presence in
the plan inventory together with absence from the source inventory — the two
halves the corpus's `plan_vs_shipped_diff` scheme names, and the reason the
family needs no separate semantics for it. -/
theorem inspModels_diff_halves {Γ : List Lara.Atom} {φ : Lara.Atom}
    {plan src feat : Lara.Term}
    (hm : inspModels Γ φ) (hg : parseGoal φ = some (.diff plan src feat)) :
    ∃ ivP ivS : Inventory,
      ivP.src = plan ∧ ivS.src = src ∧
      RelHolds .present ivP.findings feat ∧
      RelHolds .absent ivS.findings feat := by
  rcases hm with ⟨_, _, _, _, _, _, hgoal, _⟩ | ⟨_, _, _, _, _, _, _, ivP, ivS,
      hgoal, _, _, _, _, hp, hs, hpres, habs⟩
  · rw [hg] at hgoal; exact absurd hgoal (by simp)
  · rw [hg] at hgoal
    simp only [Option.some.injEq, Goal.diff.injEq] at hgoal
    obtain ⟨rfl, rfl, rfl⟩ := hgoal
    exact ⟨ivP, ivS, hp, hs, hpres, habs⟩

/-- The polarity a one-inventory witness pins down, at a known goal, together
with the context entry it was read from. -/
theorem inspModels_one_witness {Γ : List Lara.Atom} {φ : Lara.Atom}
    {rel : Rel} {src feat : Lara.Term}
    (hm : inspModels Γ φ) (hg : parseGoal φ = some (.one rel src feat)) :
    ∃ (i : Nat) (p : Lara.Atom) (iv : Inventory),
      Γ[i]? = some p ∧ premiseInventory p = some iv ∧
      iv.src = src ∧ RelHolds rel iv.findings feat := by
  rcases hm with ⟨_, _, _, i, p, iv, hgoal, hp, hiv, hsrc, hrel⟩ |
      ⟨_, _, _, _, _, _, _, _, _, hgoal, _⟩
  · rw [hg] at hgoal
    simp only [Option.some.injEq, Goal.one.injEq] at hgoal
    obtain ⟨rfl, rfl, rfl⟩ := hgoal
    exact ⟨i, p, iv, hp, hiv, hsrc, hrel⟩
  · rw [hg] at hgoal; exact absurd hgoal (by simp)

/-- **Intra-family exclusivity, at a shared inspection leaf.**  Two arguments
that read the *same* context entry cannot both be backed for `code_absent` and
`code_present` over the same source and feature.  This is the guarantee the
backend does give. -/
theorem inspModels_excl_of_same_entry {Γ Γ' : List Lara.Atom} {φ ψ : Lara.Atom}
    {src feat : Lara.Term} {p : Lara.Atom}
    (hm : inspModels Γ φ) (hm' : inspModels Γ' ψ)
    (hg : parseGoal φ = some (.one .absent src feat))
    (hg' : parseGoal ψ = some (.one .present src feat))
    (hΓ : ∀ (i : Nat) (q : Lara.Atom), Γ[i]? = some q → q = p)
    (hΓ' : ∀ (i : Nat) (q : Lara.Atom), Γ'[i]? = some q → q = p) : False := by
  obtain ⟨i, q, iv, hq, hiv, _, habs⟩ := inspModels_one_witness hm hg
  obtain ⟨j, r, jv, hr, hjv, _, hpres⟩ := inspModels_one_witness hm' hg'
  have hqp : q = p := hΓ i q hq
  have hrp : r = p := hΓ' j r hr
  subst hqp; subst hrp
  have : iv = jv := Option.some.inj (hiv.symm.trans hjv)
  subst this
  exact relHolds_polarity_excl habs hpres

/-- **... and no further.**  Given two *different* inspection leaves — one
enumerating the feature, one not — both polarities are backed, each against the
inventory it cites.  There is no shared ground truth to appeal to, unlike
`ord@1`'s numerals (`Lara.Ord.ordModels_excl_of_lt`), so `code_absent` /
`code_present` is a genuine contrary pair the policy must declare and the
attack layer must carry. -/
theorem inspModels_absent_present_sat {φ ψ : Lara.Atom} {src feat : Lara.Term}
    {p q : Lara.Atom} {ivp ivq : Inventory}
    (hg : parseGoal φ = some (.one .absent src feat))
    (hg' : parseGoal ψ = some (.one .present src feat))
    (hp : premiseInventory p = some ivp) (hq : premiseInventory q = some ivq)
    (hsp : ivp.src = src) (hsq : ivq.src = src)
    (hnp : feat ∉ ivp.findings) (hmq : feat ∈ ivq.findings) :
    inspModels [p] φ ∧ inspModels [q] ψ := by
  constructor
  · exact Or.inl ⟨.absent, src, feat, 0, p, ivp, hg, rfl, hp, hsp, hnp⟩
  · exact Or.inl ⟨.present, src, feat, 0, q, ivq, hg', rfl, hq, hsq, hmq⟩

/-! ### The registered adapter -/

/-- The one fixed `insp@1` backend core.  `Form` is the normalized source atom
itself — the identity encoding — so `enc_iff` is `equiv_iff_nf_eq`.  A
registered digest resolves to the empty theory (the premise-only slot rule), so
the consulted context is exactly the submitted premises. -/
def inspBackend (canon : String → String) : Lara.Strict.Backend canon where
  Form := Lara.Atom
  enc := Lara.nf canon
  enc_iff := fun p q => (Lara.equiv_iff_nf_eq canon p q).symm
  modelsFull := inspModels
  acceptsFull := inspAccepts
  replayFull := inspReplay
  replayFull_iff := inspReplay_iff
  soundFull := inspSound
  uses := inspUses
  uses_covers := fun κ Γ Γ' φ hag => inspUses_covers κ Γ Γ' φ hag
  uses_valid := inspUses_valid
  uses_account := inspUses_account

end Lara.Insp
