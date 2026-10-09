/-
In-place discharge of an open question at a located rule occurrence
(`docs/theory-core.md#holes-located-gaps-and-term-level-critical-questions` D13; issue #14).

This module is the term-level half of the `dischargeOpen` source update.  It
owns one rewrite, `dischargeAt q v π w`: at the rule occurrence `w@π` (spec §7,
`π ::= ε | π.i | π.q`) whose open set `H` contains `q`, remove `q` from `H` and
append the discharge `(q, v)` to the discharge map.  Nothing else in `w` moves.

The rewrite appends rather than prepends or sorts.  `Attack.lookupDis` returns
the first matching entry, so appending leaves every discharge lookup that
succeeded before unchanged: every position that addressed an occurrence of `w`
still addresses an occurrence of the same kind (same leaf, or same rule and
substitution) in the rewritten term, and every occurrence off the root-to-`π`
path is the identical subterm (`subterm_dischargeAt_old`).  This is what keeps
raw attack positions, and so raw endpoint alignment, meaningful across the
update.

The metatheory here is relational over `HasSupport` and independent of the
source pipeline:

* the conclusion is unchanged (`dischargeAt_conclusion`), and the rewritten
  term types whenever the original does and `v` answers the question
  (`dischargeAt_hasSupport`);
* obligations are characterized by occurrence (`mem_obligations_iff`), which
  gives the exact obligation set of the rewritten term
  (`dischargeAt_obligations_iff`): the old open mandatory questions away from
  `π`, the ones still open at `π`, and the obligations of `v`;
* hence discharging the last open mandatory question with a complete term
  closes the argument (`dischargeAt_complete`).
-/
import Lara.Compile
import Lara.BackendComposition

namespace Lara.Update.Discharge

open Lara Lara.Support Lara.Attack

/-! ### The rewrite -/

/-- Replace the first discharge entry keyed `q` (the entry `lookupDis` reads). -/
def replaceDis : List (QuestionId × SupportTerm) → QuestionId → SupportTerm →
    List (QuestionId × SupportTerm)
  | [], _, _ => []
  | (q', u) :: rest, q, u' =>
      if q' = q then (q', u') :: rest else (q', u) :: replaceDis rest q u'

/-- Close the open question `q` of a rule occurrence with the discharge `v`:
`q` leaves the open set and `(q, v)` is appended to the discharge map. -/
def closeOpen (q : QuestionId) (v : SupportTerm) : SupportTerm → Option SupportTerm
  | .inst rn θ ws D H α =>
      if q ∈ H then
        some (.inst rn θ ws (D ++ [(q, v)]) (H.filter fun n => decide (n ≠ q)) α)
      else none
  | .leaf _ => none

/-- `dischargeAt q v π w`: close `q` with `v` at the occurrence `w@π`.  Defined
exactly where `w@π` is a rule instance whose open set contains `q`
(`dischargeAt_isSome_iff`). -/
def dischargeAt (q : QuestionId) (v : SupportTerm) : Pos → SupportTerm → Option SupportTerm
  | [], w => closeOpen q v w
  | _ :: _, .leaf _ => none
  | .prem i :: π, .inst rn θ ws D H α =>
      match ws[i]? with
      | some u => (dischargeAt q v π u).map fun u' => .inst rn θ (ws.set i u') D H α
      | none => none
  | .ques q' :: π, .inst rn θ ws D H α =>
      match lookupDis D q' with
      | some u =>
          (dischargeAt q v π u).map fun u' => .inst rn θ ws (replaceDis D q' u') H α
      | none => none

/-- The site precondition of `dischargeOpen`: `w@π` is a rule instance whose
open set contains `q`. -/
def OpenAt (w : SupportTerm) (π : Pos) (q : QuestionId) : Prop :=
  ∃ rn θ ws D H α, subterm w π = some (.inst rn θ ws D H α) ∧ q ∈ H

/-- Executable decider for `OpenAt`. -/
def openAtB (w : SupportTerm) (π : Pos) (q : QuestionId) : Bool :=
  match subterm w π with
  | some (.inst _ _ _ _ H _) => decide (q ∈ H)
  | _ => false

theorem openAtB_iff (w : SupportTerm) (π : Pos) (q : QuestionId) :
    openAtB w π q = true ↔ OpenAt w π q := by
  unfold openAtB OpenAt
  split
  · rename_i rn θ ws D H α hsub
    constructor
    · intro h
      exact ⟨rn, θ, ws, D, H, α, hsub, of_decide_eq_true h⟩
    · rintro ⟨_, _, _, _, H', _, hsub', hq⟩
      rw [hsub] at hsub'
      cases hsub'
      exact decide_eq_true hq
  · rename_i hnot
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro rn θ ws D H α hsub _
    exact hnot rn θ ws D H α hsub

/-! ### Discharge-map lemmas -/

theorem lookupDis_append_of_some {D : List (QuestionId × SupportTerm)}
    {q' : QuestionId} {u : SupportTerm} (extra : List (QuestionId × SupportTerm))
    (h : lookupDis D q' = some u) :
    lookupDis (D ++ extra) q' = some u := by
  induction D with
  | nil => simp [lookupDis] at h
  | cons hd tl ih =>
      obtain ⟨k, x⟩ := hd
      simp only [lookupDis, List.cons_append] at h ⊢
      by_cases hk : k = q'
      · simpa [hk] using h
      · simp only [hk, if_false] at h ⊢
        exact ih h

theorem lookupDis_append_of_none {D : List (QuestionId × SupportTerm)}
    {q' : QuestionId} (extra : List (QuestionId × SupportTerm))
    (h : lookupDis D q' = none) :
    lookupDis (D ++ extra) q' = lookupDis extra q' := by
  induction D with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨k, x⟩ := hd
      simp only [lookupDis, List.cons_append] at h ⊢
      by_cases hk : k = q'
      · simp [hk] at h
      · simp only [hk, if_false] at h ⊢
        exact ih h

theorem lookupDis_append_cases {D : List (QuestionId × SupportTerm)}
    {q q' : QuestionId} {v x : SupportTerm}
    (h : lookupDis (D ++ [(q, v)]) q' = some x) :
    lookupDis D q' = some x ∨ (lookupDis D q' = none ∧ q' = q ∧ x = v) := by
  cases hD : lookupDis D q' with
  | some y =>
      rw [lookupDis_append_of_some _ hD] at h
      exact Or.inl h
  | none =>
      rw [lookupDis_append_of_none _ hD] at h
      simp only [lookupDis] at h
      by_cases hq : q = q'
      · subst hq
        simp only [if_true, Option.some.injEq] at h
        exact Or.inr ⟨rfl, rfl, h.symm⟩
      · simp [hq] at h

theorem lookupDis_replaceDis {D : List (QuestionId × SupportTerm)}
    {q0 : QuestionId} {u0 : SupportTerm} (u' : SupportTerm)
    (h : lookupDis D q0 = some u0) (q' : QuestionId) :
    lookupDis (replaceDis D q0 u') q' =
      if q' = q0 then some u' else lookupDis D q' := by
  induction D with
  | nil => simp [lookupDis] at h
  | cons hd tl ih =>
      obtain ⟨k, x⟩ := hd
      simp only [lookupDis] at h
      by_cases hk : k = q0
      · subst hk
        simp only [replaceDis, if_true, lookupDis]
        by_cases hq : q' = k
        · subst hq; simp
        · simp [hq, Ne.symm hq]
      · simp only [hk, if_false] at h
        simp only [replaceDis, hk, if_false, lookupDis]
        by_cases hkq : k = q'
        · subst hkq
          have hne : k ≠ q0 := hk
          simp [hne]
        · simp only [hkq, if_false]
          exact ih h

theorem replaceDis_map_fst (D : List (QuestionId × SupportTerm))
    (q0 : QuestionId) (u' : SupportTerm) :
    (replaceDis D q0 u').map Prod.fst = D.map Prod.fst := by
  induction D with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨k, x⟩ := hd
      by_cases hk : k = q0
      · simp [replaceDis, hk]
      · simp [replaceDis, hk, ih]

/-- The first entry keyed `q0` sits at a definite index, and `replaceDis`
overwrites exactly that index. -/
theorem replaceDis_eq_set {D : List (QuestionId × SupportTerm)}
    {q0 : QuestionId} {u0 : SupportTerm} (u' : SupportTerm)
    (h : lookupDis D q0 = some u0) :
    ∃ j, D[j]? = some (q0, u0) ∧ replaceDis D q0 u' = D.set j (q0, u') := by
  induction D with
  | nil => simp [lookupDis] at h
  | cons hd tl ih =>
      obtain ⟨k, x⟩ := hd
      simp only [lookupDis] at h
      by_cases hk : k = q0
      · subst hk
        simp only [if_true, Option.some.injEq] at h
        subst h
        exact ⟨0, by simp, by simp [replaceDis]⟩
      · simp only [hk, if_false] at h
        obtain ⟨j, hj, hset⟩ := ih h
        exact ⟨j + 1, by simpa using hj, by simp [replaceDis, hk, hset]⟩

theorem lookupDis_none_of_not_mem {D : List (QuestionId × SupportTerm)}
    {q : QuestionId} (h : q ∉ D.map Prod.fst) : lookupDis D q = none := by
  cases hD : lookupDis D q with
  | none => rfl
  | some u => exact absurd (Compile.lookupDis_some_mem hD) h

/-- Under duplicate-free keys, a positional entry is the entry `lookupDis`
reads. -/
theorem lookupDis_of_getElem?_nodup {D : List (QuestionId × SupportTerm)}
    (hnodup : (D.map Prod.fst).Nodup) {j : Nat} {q : QuestionId}
    {u : SupportTerm} (hj : D[j]? = some (q, u)) :
    lookupDis D q = some u := by
  induction D generalizing j with
  | nil => simp at hj
  | cons hd tl ih =>
      obtain ⟨k, x⟩ := hd
      rw [List.map_cons] at hnodup
      obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hnodup
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq,
            Prod.mk.injEq] at hj
          obtain ⟨rfl, rfl⟩ := hj
          simp [lookupDis]
      | succ j =>
          simp only [List.getElem?_cons_succ] at hj
          have hmem : q ∈ tl.map Prod.fst :=
            List.mem_map.mpr ⟨(q, u), List.mem_of_getElem? hj, rfl⟩
          have hne : k ≠ q := fun heq => hhead (heq ▸ hmem)
          simp only [lookupDis, hne, if_false]
          exact ih htail hj

/-! ### Occurrence kinds -/

/-- What a position addresses, forgetting the open set and the children: a
leaf, or a rule instance with its substitution.  Attack typing at a position
(spec §7.1) reads exactly this datum: an undercut needs a rule occurrence, an
undermine a leaf occurrence. -/
inductive OccKind where
  | leaf (l : LeafId)
  | rule (rn : RuleId) (θ : Subst)
deriving DecidableEq

def occKind : SupportTerm → OccKind
  | .leaf l => .leaf l
  | .inst rn θ _ _ _ _ => .rule rn θ

/-- The open set of an occurrence (empty at a leaf). -/
def openSet : SupportTerm → List QuestionId
  | .leaf _ => []
  | .inst _ _ _ _ H _ => H

/-! ### Structure of the rewrite -/

theorem dischargeAt_nil {q : QuestionId} {v w w' : SupportTerm}
    (h : dischargeAt q v [] w = some w') :
    ∃ rn θ ws D H α, w = .inst rn θ ws D H α ∧ q ∈ H ∧
      w' = .inst rn θ ws (D ++ [(q, v)]) (H.filter fun n => decide (n ≠ q)) α := by
  cases w with
  | leaf l => simp [dischargeAt, closeOpen] at h
  | inst rn θ ws D H α =>
      simp only [dischargeAt, closeOpen] at h
      by_cases hq : q ∈ H
      · simp only [hq, if_true, Option.some.injEq] at h
        exact ⟨rn, θ, ws, D, H, α, rfl, hq, h.symm⟩
      · simp [hq] at h

/-- `dischargeAt` is defined exactly at an open site. -/
theorem dischargeAt_isSome_iff (q : QuestionId) (v : SupportTerm) :
    ∀ (π : Pos) (w : SupportTerm),
      (dischargeAt q v π w).isSome = true ↔ OpenAt w π q := by
  intro π
  induction π with
  | nil =>
      intro w
      cases w with
      | leaf l => simp [dischargeAt, closeOpen, OpenAt, subterm]
      | inst rn θ ws D H α =>
          by_cases hq : q ∈ H
          · simp only [dischargeAt, closeOpen, hq, if_true, Option.isSome_some,
              true_iff]
            exact ⟨rn, θ, ws, D, H, α, rfl, hq⟩
          · simp only [dischargeAt, closeOpen, hq, if_false, Option.isSome_none,
              Bool.false_eq_true, false_iff]
            rintro ⟨_, _, _, _, H', _, hsub, hq'⟩
            simp only [subterm, Option.some.injEq, SupportTerm.inst.injEq] at hsub
            exact hq (hsub.2.2.2.2.1 ▸ hq')
  | cons e π ih =>
      intro w
      cases w with
      | leaf l => simp [dischargeAt, OpenAt, subterm]
      | inst rn θ ws D H α =>
          cases e with
          | prem i =>
              simp only [dischargeAt, OpenAt, subterm]
              cases hu : ws[i]? with
              | none => simp
              | some u =>
                  simp only [Option.isSome_map]
                  exact ih u
          | ques q' =>
              simp only [dischargeAt, OpenAt, subterm]
              cases hu : lookupDis D q' with
              | none => simp
              | some u =>
                  simp only [Option.isSome_map]
                  exact ih u

/-- **Old positions survive.** Every position defined in `w` stays defined in
the rewritten term and addresses an occurrence of the same kind.  Off the
discharge site its open set is unchanged, and off the root-to-site path the
occurrence is the identical subterm. -/
theorem subterm_dischargeAt_old {q : QuestionId} {v : SupportTerm} :
    ∀ {π : Pos} {w w' : SupportTerm}, dischargeAt q v π w = some w' →
      ∀ {π' : Pos} {u : SupportTerm}, subterm w π' = some u →
        ∃ u', subterm w' π' = some u' ∧ occKind u' = occKind u ∧
          (π' ≠ π → openSet u' = openSet u) ∧ (¬ π' <+: π → u' = u) := by
  intro π
  induction π with
  | nil =>
      intro w w' h π' u hsub
      obtain ⟨rn, θ, ws, D, H, α, rfl, _, rfl⟩ := dischargeAt_nil h
      cases π' with
      | nil =>
          simp only [subterm, Option.some.injEq] at hsub
          subst hsub
          exact ⟨_, rfl, rfl, fun hne => absurd rfl hne,
            fun hp => absurd (List.nil_prefix) hp⟩
      | cons e ρ =>
          refine ⟨u, ?_, rfl, fun _ => rfl, fun _ => rfl⟩
          cases e with
          | prem i => simpa [subterm] using hsub
          | ques q' =>
              simp only [subterm] at hsub ⊢
              cases hD : lookupDis D q' with
              | none => rw [hD] at hsub; cases hsub
              | some x =>
                  rw [hD] at hsub
                  rw [lookupDis_append_of_some _ hD]
                  exact hsub
  | cons e π ih =>
      intro w w' h π' u hsub
      cases w with
      | leaf l => simp [dischargeAt] at h
      | inst rn θ ws D H α =>
          cases e with
          | prem i =>
              simp only [dischargeAt] at h
              cases hc : ws[i]? with
              | none => rw [hc] at h; cases h
              | some c =>
                  simp only [hc] at h
                  cases hc' : dischargeAt q v π c with
                  | none => simp [hc'] at h
                  | some c' =>
                      simp only [hc', Option.map_some, Option.some.injEq] at h
                      subst h
                      have hlt : i < ws.length := Support.lt_of_getElem?_some hc
                      cases π' with
                      | nil =>
                          simp only [subterm, Option.some.injEq] at hsub
                          subst hsub
                          exact ⟨_, rfl, rfl, fun _ => rfl,
                            fun hp => absurd List.nil_prefix hp⟩
                      | cons e' ρ =>
                          cases e' with
                          | prem j =>
                              by_cases hij : i = j
                              · subst hij
                                simp only [subterm, hc] at hsub
                                obtain ⟨u', hu', hk, hopen, hsame⟩ := ih hc' hsub
                                refine ⟨u', ?_, hk, ?_, ?_⟩
                                · simp only [subterm, List.getElem?_set_self hlt]
                                  exact hu'
                                · intro hne
                                  exact hopen (fun hρ => hne (by rw [hρ]))
                                · intro hnp
                                  exact hsame (fun hp => hnp
                                    (List.cons_prefix_cons.mpr ⟨rfl, hp⟩))
                              · refine ⟨u, ?_, rfl, fun _ => rfl, fun _ => rfl⟩
                                simp only [subterm] at hsub ⊢
                                rw [List.getElem?_set_ne hij]
                                exact hsub
                          | ques q' =>
                              exact ⟨u, by simpa [subterm] using hsub, rfl,
                                fun _ => rfl, fun _ => rfl⟩
          | ques q0 =>
              simp only [dischargeAt] at h
              cases hc : lookupDis D q0 with
              | none => rw [hc] at h; cases h
              | some c =>
                  simp only [hc] at h
                  cases hc' : dischargeAt q v π c with
                  | none => simp [hc'] at h
                  | some c' =>
                      simp only [hc', Option.map_some, Option.some.injEq] at h
                      subst h
                      cases π' with
                      | nil =>
                          simp only [subterm, Option.some.injEq] at hsub
                          subst hsub
                          exact ⟨_, rfl, rfl, fun _ => rfl,
                            fun hp => absurd List.nil_prefix hp⟩
                      | cons e' ρ =>
                          cases e' with
                          | prem j =>
                              exact ⟨u, by simpa [subterm] using hsub, rfl,
                                fun _ => rfl, fun _ => rfl⟩
                          | ques q' =>
                              by_cases hq : q' = q0
                              · subst hq
                                simp only [subterm, hc] at hsub
                                obtain ⟨u', hu', hk, hopen, hsame⟩ := ih hc' hsub
                                refine ⟨u', ?_, hk, ?_, ?_⟩
                                · simp only [subterm]
                                  rw [lookupDis_replaceDis c' hc q']
                                  simpa using hu'
                                · intro hne
                                  exact hopen (fun hρ => hne (by rw [hρ]))
                                · intro hnp
                                  exact hsame (fun hp => hnp
                                    (List.cons_prefix_cons.mpr ⟨rfl, hp⟩))
                              · refine ⟨u, ?_, rfl, fun _ => rfl, fun _ => rfl⟩
                                simp only [subterm] at hsub ⊢
                                rw [lookupDis_replaceDis c' hc q', if_neg hq]
                                exact hsub

/-- **The discharged site.** At `π` the rewritten term has the same rule
instance with `q` removed from the open set and `(q, v)` appended to the
discharge map. -/
theorem subterm_dischargeAt_site {q : QuestionId} {v : SupportTerm} :
    ∀ {π : Pos} {w w' : SupportTerm}, dischargeAt q v π w = some w' →
      ∀ {rn θ ws D H α}, subterm w π = some (.inst rn θ ws D H α) →
        subterm w' π = some
          (.inst rn θ ws (D ++ [(q, v)]) (H.filter fun n => decide (n ≠ q)) α) := by
  intro π
  induction π with
  | nil =>
      intro w w' h rn θ ws D H α hsub
      obtain ⟨rn', θ', ws', D', H', α', rfl, _, rfl⟩ := dischargeAt_nil h
      simp only [subterm, Option.some.injEq, SupportTerm.inst.injEq] at hsub
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hsub
      rfl
  | cons e π ih =>
      intro w w' h rn θ ws D H α hsub
      cases w with
      | leaf l => simp [dischargeAt] at h
      | inst rn0 θ0 ws0 D0 H0 α0 =>
          cases e with
          | prem i =>
              simp only [dischargeAt] at h
              cases hc : ws0[i]? with
              | none => rw [hc] at h; cases h
              | some c =>
                  simp only [hc] at h
                  cases hc' : dischargeAt q v π c with
                  | none => simp [hc'] at h
                  | some c' =>
                      simp only [hc', Option.map_some, Option.some.injEq] at h
                      subst h
                      have hlt : i < ws0.length := Support.lt_of_getElem?_some hc
                      simp only [subterm, hc] at hsub
                      simp only [subterm, List.getElem?_set_self hlt]
                      exact ih hc' hsub
          | ques q0 =>
              simp only [dischargeAt] at h
              cases hc : lookupDis D0 q0 with
              | none => rw [hc] at h; cases h
              | some c =>
                  simp only [hc] at h
                  cases hc' : dischargeAt q v π c with
                  | none => simp [hc'] at h
                  | some c' =>
                      simp only [hc', Option.map_some, Option.some.injEq] at h
                      subst h
                      simp only [subterm, hc] at hsub
                      simp only [subterm]
                      rw [lookupDis_replaceDis c' hc q0, if_pos rfl]
                      exact ih hc' hsub

/-- **The new path.** When `q` had no discharge at the site (which typing
guarantees, since `q` was open), the position `π.q` is new and addresses `v`,
with every position of `v` below it. -/
theorem subterm_dischargeAt_new {q : QuestionId} {v : SupportTerm} :
    ∀ {π : Pos} {w w' : SupportTerm}, dischargeAt q v π w = some w' →
      ∀ {rn θ ws D H α}, subterm w π = some (.inst rn θ ws D H α) →
        lookupDis D q = none →
        ∀ ρ, subterm w' (π ++ .ques q :: ρ) = subterm v ρ := by
  intro π w w' h rn θ ws D H α hsub hnone ρ
  have hsite := subterm_dischargeAt_site h hsub
  -- descend to the site, then take the new discharge edge
  have hdescend : ∀ (π : Pos) (t s : SupportTerm) (ρ' : Pos),
      subterm t π = some s → subterm t (π ++ ρ') = subterm s ρ' := by
    intro π
    induction π with
    | nil => intro t s ρ' hts; simp only [subterm, Option.some.injEq] at hts; subst hts; rfl
    | cons e π ihπ =>
        intro t s ρ' hts
        cases t with
        | leaf l => simp [subterm] at hts
        | inst rn' θ' ws' D' H' α' =>
            cases e with
            | prem i =>
                simp only [subterm, List.cons_append] at hts ⊢
                cases hi : ws'[i]? with
                | none => rw [hi] at hts; cases hts
                | some c => rw [hi] at hts; exact ihπ c s ρ' hts
            | ques q' =>
                simp only [subterm, List.cons_append] at hts ⊢
                cases hi : lookupDis D' q' with
                | none => rw [hi] at hts; cases hts
                | some c => rw [hi] at hts; exact ihπ c s ρ' hts
  rw [hdescend π w' _ (.ques q :: ρ) hsite]
  simp only [subterm]
  rw [lookupDis_append_of_none _ hnone]
  simp [lookupDis]

/-- **Every occurrence of the rewritten term is accounted for.** It is either
an occurrence of `w` at the same position, of the same kind and (off the site)
the same open set, or an occurrence of `v` under the new edge `π.q`. -/
theorem subterm_dischargeAt_cases {q : QuestionId} {v : SupportTerm} :
    ∀ {π : Pos} {w w' : SupportTerm}, dischargeAt q v π w = some w' →
      ∀ {π' : Pos} {u' : SupportTerm}, subterm w' π' = some u' →
        (∃ u, subterm w π' = some u ∧ occKind u' = occKind u ∧
            (π' ≠ π → openSet u' = openSet u)) ∨
          (∃ ρ, π' = π ++ .ques q :: ρ ∧ subterm v ρ = some u') := by
  intro π
  induction π with
  | nil =>
      intro w w' h π' u' hsub
      obtain ⟨rn, θ, ws, D, H, α, rfl, _, rfl⟩ := dischargeAt_nil h
      cases π' with
      | nil =>
          simp only [subterm, Option.some.injEq] at hsub
          subst hsub
          exact Or.inl ⟨_, rfl, rfl, fun hne => absurd rfl hne⟩
      | cons e ρ =>
          cases e with
          | prem i =>
              exact Or.inl ⟨u', by simpa [subterm] using hsub, rfl, fun _ => rfl⟩
          | ques q' =>
              simp only [subterm] at hsub
              cases hx : lookupDis (D ++ [(q, v)]) q' with
              | none => rw [hx] at hsub; cases hsub
              | some x =>
                  rw [hx] at hsub
                  rcases lookupDis_append_cases hx with hD | ⟨_, rfl, rfl⟩
                  · refine Or.inl ⟨u', ?_, rfl, fun _ => rfl⟩
                    simp only [subterm, hD]
                    exact hsub
                  · exact Or.inr ⟨ρ, rfl, hsub⟩
  | cons e π ih =>
      intro w w' h π' u' hsub
      cases w with
      | leaf l => simp [dischargeAt] at h
      | inst rn θ ws D H α =>
          cases e with
          | prem i =>
              simp only [dischargeAt] at h
              cases hc : ws[i]? with
              | none => rw [hc] at h; cases h
              | some c =>
                  simp only [hc] at h
                  cases hc' : dischargeAt q v π c with
                  | none => simp [hc'] at h
                  | some c' =>
                      simp only [hc', Option.map_some, Option.some.injEq] at h
                      subst h
                      have hlt : i < ws.length := Support.lt_of_getElem?_some hc
                      cases π' with
                      | nil =>
                          simp only [subterm, Option.some.injEq] at hsub
                          subst hsub
                          exact Or.inl ⟨_, rfl, rfl, fun _ => rfl⟩
                      | cons e' ρ =>
                          cases e' with
                          | prem j =>
                              by_cases hij : i = j
                              · subst hij
                                simp only [subterm, List.getElem?_set_self hlt] at hsub
                                rcases ih hc' hsub with ⟨u, hu, hk, hopen⟩ | ⟨ρ', hρ, hv⟩
                                · refine Or.inl ⟨u, ?_, hk, ?_⟩
                                  · simp only [subterm, hc]; exact hu
                                  · intro hne
                                    exact hopen (fun hρ => hne (by rw [hρ]))
                                · exact Or.inr ⟨ρ', by rw [hρ]; rfl, hv⟩
                              · refine Or.inl ⟨u', ?_, rfl, fun _ => rfl⟩
                                simp only [subterm] at hsub ⊢
                                rw [List.getElem?_set_ne hij] at hsub
                                exact hsub
                          | ques q' =>
                              exact Or.inl ⟨u', by simpa [subterm] using hsub, rfl,
                                fun _ => rfl⟩
          | ques q0 =>
              simp only [dischargeAt] at h
              cases hc : lookupDis D q0 with
              | none => rw [hc] at h; cases h
              | some c =>
                  simp only [hc] at h
                  cases hc' : dischargeAt q v π c with
                  | none => simp [hc'] at h
                  | some c' =>
                      simp only [hc', Option.map_some, Option.some.injEq] at h
                      subst h
                      cases π' with
                      | nil =>
                          simp only [subterm, Option.some.injEq] at hsub
                          subst hsub
                          exact Or.inl ⟨_, rfl, rfl, fun _ => rfl⟩
                      | cons e' ρ =>
                          cases e' with
                          | prem j =>
                              exact Or.inl ⟨u', by simpa [subterm] using hsub, rfl,
                                fun _ => rfl⟩
                          | ques q' =>
                              simp only [subterm] at hsub
                              rw [lookupDis_replaceDis c' hc q'] at hsub
                              by_cases hq : q' = q0
                              · subst hq
                                simp only [if_true] at hsub
                                rcases ih hc' hsub with ⟨u, hu, hk, hopen⟩ | ⟨ρ', hρ, hv⟩
                                · refine Or.inl ⟨u, ?_, hk, ?_⟩
                                  · simp only [subterm, hc]; exact hu
                                  · intro hne
                                    exact hopen (fun hρ => hne (by rw [hρ]))
                                · exact Or.inr ⟨ρ', by rw [hρ]; rfl, hv⟩
                              · simp only [hq, if_false] at hsub
                                refine Or.inl ⟨u', ?_, rfl, fun _ => rfl⟩
                                simp only [subterm]
                                exact hsub

/-! ### Obligations by occurrence -/

/-- `n` is an open mandatory question of some rule occurrence of `w`. -/
def OpenMandatoryAt (Pi : RuleId → Option Rule) (w : SupportTerm)
    (n : QuestionId) : Prop :=
  ∃ π rn θ ws D H α r, subterm w π = some (.inst rn θ ws D H α) ∧
    Pi rn = some r ∧ n ∈ openMandatory r H

/-- `n` is an open mandatory question of a rule occurrence of `w` at a
position other than `π`. -/
def OpenMandatoryAway (Pi : RuleId → Option Rule) (w : SupportTerm) (π : Pos)
    (n : QuestionId) : Prop :=
  ∃ π', π' ≠ π ∧ ∃ rn θ ws D H α r, subterm w π' = some (.inst rn θ ws D H α) ∧
    Pi rn = some r ∧ n ∈ openMandatory r H

theorem mem_collectObligations_iff {Os DOs : List (List QuestionId)} {r : Rule}
    {H : List QuestionId} {n : QuestionId} :
    n ∈ collectObligations Os DOs r H ↔
      (∃ O ∈ Os, n ∈ O) ∨ (∃ O ∈ DOs, n ∈ O) ∨ n ∈ openMandatory r H := by
  rw [collectObligations, unionAll, mem_dedupQuestions, List.mem_flatten]
  constructor
  · rintro ⟨O, hO, hn⟩
    simp only [List.mem_append, List.mem_singleton] at hO
    rcases hO with (hO | hO) | rfl
    · exact Or.inl ⟨O, hO, hn⟩
    · exact Or.inr (Or.inl ⟨O, hO, hn⟩)
    · exact Or.inr (Or.inr hn)
  · rintro (⟨O, hO, hn⟩ | ⟨O, hO, hn⟩ | hn)
    · exact ⟨O, by simp [hO], hn⟩
    · exact ⟨O, by simp [hO], hn⟩
    · exact ⟨_, by simp, hn⟩

/-- **Obligations are exactly the open mandatory questions of the occurrences.**
The §6.1 union over premises and discharges unfolds to a union over every rule
occurrence of the term. -/
theorem mem_obligations_iff {canon : String → String} {Pi : RuleId → Option Rule}
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk w C O) (n : QuestionId) :
    n ∈ O ↔ OpenMandatoryAt Pi w n := by
  induction h with
  | leaf hΓ =>
      simp only [List.not_mem_nil, false_iff]
      rintro ⟨π, rn, θ, ws, D, H, α, r, hsub, _, _⟩
      cases π with
      | nil => simp [subterm] at hsub
      | cons e π => simp [subterm] at hsub
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis ihprems ihdis =>
      rw [mem_collectObligations_iff]
      constructor
      · rintro (⟨O', hO', hn⟩ | ⟨O', hO', hn⟩ | hn)
        · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hO'
          have hlt : i < Os.length := Support.lt_of_getElem?_some hi
          obtain ⟨c, hc⟩ := Support.getElem?_some_of_lt ws i
            (by have := hside.lenOs; omega)
          obtain ⟨A, hA⟩ := Support.getElem?_some_of_lt Cs i
            (by have := hside.lenOs; have := hside.lenCs; omega)
          obtain ⟨π, rn', θ', ws', D', H', α', r', hsub, hr, hm⟩ :=
            (ihprems i c A O' hc hA hi).mp hn
          exact ⟨.prem i :: π, rn', θ', ws', D', H', α', r',
            by simp only [subterm, hc]; exact hsub, hr, hm⟩
        · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hO'
          have hlt : j < DOs.length := Support.lt_of_getElem?_some hj
          obtain ⟨qc, hqc⟩ := Support.getElem?_some_of_lt D j
            (by have := hside.lenDOs; omega)
          obtain ⟨A, hA⟩ := Support.getElem?_some_of_lt DCs j
            (by have := hside.lenDOs; have := hside.lenDCs; omega)
          obtain ⟨q', c⟩ := qc
          obtain ⟨π, rn', θ', ws', D', H', α', r', hsub, hr, hm⟩ :=
            (ihdis j q' c A O' hqc hA hj).mp hn
          refine ⟨.ques q' :: π, rn', θ', ws', D', H', α', r', ?_, hr, hm⟩
          simp only [subterm, lookupDis_of_getElem?_nodup hside.dNodup hqc]
          exact hsub
        · exact ⟨[], rn, θ, ws, D, H, α, r, rfl, hside.rule, hn⟩
      · rintro ⟨π, rn', θ', ws', D', H', α', r', hsub, hr, hm⟩
        cases π with
        | nil =>
            simp only [subterm, Option.some.injEq, SupportTerm.inst.injEq] at hsub
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hsub
            have : r' = r := Option.some.inj (hr.symm.trans hside.rule)
            subst this
            exact Or.inr (Or.inr hm)
        | cons e π =>
            cases e with
            | prem i =>
                simp only [subterm] at hsub
                cases hc : ws[i]? with
                | none => rw [hc] at hsub; cases hsub
                | some c =>
                    rw [hc] at hsub
                    have hlt : i < ws.length := Support.lt_of_getElem?_some hc
                    obtain ⟨A, hA⟩ := Support.getElem?_some_of_lt Cs i
                      (by have := hside.lenCs; omega)
                    obtain ⟨O', hO'⟩ := Support.getElem?_some_of_lt Os i
                      (by have := hside.lenOs; omega)
                    exact Or.inl ⟨O', List.mem_of_getElem? hO',
                      (ihprems i c A O' hc hA hO').mpr
                        ⟨π, rn', θ', ws', D', H', α', r', hsub, hr, hm⟩⟩
            | ques q' =>
                simp only [subterm] at hsub
                cases hc : lookupDis D q' with
                | none => rw [hc] at hsub; cases hsub
                | some c =>
                    rw [hc] at hsub
                    obtain ⟨j, hj⟩ := Compile.lookupDis_some_getElem? hc
                    have hlt : j < D.length := Support.lt_of_getElem?_some hj
                    obtain ⟨A, hA⟩ := Support.getElem?_some_of_lt DCs j
                      (by have := hside.lenDCs; omega)
                    obtain ⟨O', hO'⟩ := Support.getElem?_some_of_lt DOs j
                      (by have := hside.lenDOs; omega)
                    exact Or.inr (Or.inl ⟨O', List.mem_of_getElem? hO',
                      (ihdis j q' c A O' hj hA hO').mpr
                        ⟨π, rn', θ', ws', D', H', α', r', hsub, hr, hm⟩⟩)

/-- Two typed terms whose roots have the same kind have the same conclusion:
a leaf's conclusion is its context entry, an instance's is its rule's
conclusion pattern under its substitution. -/
theorem hasSupport_concl_of_occKind {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {w w' : SupportTerm} {C C' : Atom} {O O' : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk w C O)
    (h' : HasSupport canon Pi Gamma CertOk w' C' O')
    (hk : occKind w = occKind w') : C = C' := by
  cases h with
  | leaf hΓ =>
      cases h' with
      | leaf hΓ' =>
          simp only [occKind, OccKind.leaf.injEq] at hk
          subst hk
          exact Option.some.inj (hΓ.symm.trans hΓ')
      | inst => simp [occKind] at hk
  | inst hside _ _ =>
      cases h' with
      | leaf => simp [occKind] at hk
      | inst hside' _ _ =>
          simp only [occKind, OccKind.rule.injEq] at hk
          obtain ⟨rfl, rfl⟩ := hk
          have hr := Option.some.inj (hside.rule.symm.trans hside'.rule)
          subst hr
          exact Option.some.inj (hside.concl.symm.trans hside'.concl)

/-- The rewrite keeps the root kind. -/
theorem occKind_dischargeAt {q : QuestionId} {v : SupportTerm} {π : Pos}
    {w w' : SupportTerm} (h : dischargeAt q v π w = some w') :
    occKind w' = occKind w := by
  obtain ⟨u', hu', hk, _, _⟩ := subterm_dischargeAt_old h (π' := []) rfl
  simp only [subterm, Option.some.injEq] at hu'
  subst hu'
  exact hk

/-- **The conclusion is unchanged.** -/
theorem dischargeAt_conclusion {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {q : QuestionId} {v : SupportTerm} {π : Pos} {w w' : SupportTerm}
    {C C' : Atom} {O O' : List QuestionId}
    (hdis : dischargeAt q v π w = some w')
    (hw : HasSupport canon Pi Gamma CertOk w C O)
    (hw' : HasSupport canon Pi Gamma CertOk w' C' O') : C' = C :=
  hasSupport_concl_of_occKind hw' hw (occKind_dischargeAt hdis)

/-- At a typed open site, the discharged question had no discharge entry. -/
theorem lookupDis_site_none {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {w : SupportTerm} {C : Atom} {O : List QuestionId} {π : Pos} {q : QuestionId}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
    (hw : HasSupport canon Pi Gamma CertOk w C O)
    (hsite : subterm w π = some (.inst rn θ ws D H α)) (hq : q ∈ H) :
    lookupDis D q = none := by
  obtain ⟨_, _, htyped, _⟩ := Compile.hasSupport_subterm hw hsite
  cases htyped with
  | inst hside _ _ =>
      exact lookupDis_none_of_not_mem fun hmem => hside.disj q hmem hq

/-- The open set at the site contains the discharged question. -/
theorem mem_site_of_dischargeAt {q : QuestionId} {v : SupportTerm} {π : Pos}
    {w w' : SupportTerm} (hdis : dischargeAt q v π w = some w')
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
    (hsite : subterm w π = some (.inst rn θ ws D H α)) : q ∈ H := by
  have hsome : (dischargeAt q v π w).isSome = true := by rw [hdis]; rfl
  obtain ⟨_, _, _, _, H', _, hsub, hq⟩ := (dischargeAt_isSome_iff q v π w).mp hsome
  rw [hsite] at hsub
  simp only [Option.some.injEq, SupportTerm.inst.injEq] at hsub
  rw [hsub.2.2.2.2.1]
  exact hq

private theorem mem_openMandatory_filter {r : Rule} {H : List QuestionId}
    {q n : QuestionId} :
    n ∈ openMandatory r (H.filter fun m => decide (m ≠ q)) ↔
      n ≠ q ∧ n ∈ openMandatory r H := by
  simp only [openMandatory, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun ⟨⟨hH, hne⟩, hm⟩ => ⟨hne, hH, hm⟩,
    fun ⟨hne, hH, hm⟩ => ⟨⟨hH, hne⟩, hm⟩⟩

/-- **The exact obligation set after discharge.** An obligation of the
rewritten term is an open mandatory question away from the site, one still
open at the site, or an obligation of the discharging term `v`. -/
theorem dischargeAt_obligations_iff {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {q : QuestionId} {v : SupportTerm} {π : Pos} {w w' : SupportTerm}
    {C C' Cv : Atom} {O O' Ov : List QuestionId}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
    {r : Rule}
    (hdis : dischargeAt q v π w = some w')
    (hw : HasSupport canon Pi Gamma CertOk w C O)
    (hw' : HasSupport canon Pi Gamma CertOk w' C' O')
    (hv : HasSupport canon Pi Gamma CertOk v Cv Ov)
    (hsite : subterm w π = some (.inst rn θ ws D H α)) (hr : Pi rn = some r)
    (n : QuestionId) :
    n ∈ O' ↔
      OpenMandatoryAway Pi w π n ∨ (n ≠ q ∧ n ∈ openMandatory r H) ∨ n ∈ Ov := by
  have hqH := mem_site_of_dischargeAt hdis hsite
  have hnone := lookupDis_site_none hw hsite hqH
  have hsite' := subterm_dischargeAt_site hdis hsite
  rw [mem_obligations_iff hw' n]
  constructor
  · rintro ⟨π', rn', θ', ws', D', H', α', r', hsub, hr', hm⟩
    rcases subterm_dischargeAt_cases hdis hsub with
      ⟨u, hu, hk, hopen⟩ | ⟨ρ, rfl, hvsub⟩
    · by_cases hπ : π' = π
      · subst hπ
        rw [hsite'] at hsub
        simp only [Option.some.injEq, SupportTerm.inst.injEq] at hsub
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hsub
        have : r' = r := Option.some.inj (hr'.symm.trans hr)
        subst this
        exact Or.inr (Or.inl (mem_openMandatory_filter.mp hm))
      · cases u with
        | leaf l => simp [occKind] at hk
        | inst rn'' θ'' ws'' D'' H'' α'' =>
            simp only [occKind, OccKind.rule.injEq] at hk
            obtain ⟨rfl, rfl⟩ := hk
            have hH : H' = H'' := by simpa [openSet] using hopen hπ
            subst hH
            exact Or.inl ⟨π', hπ, _, _, ws'', D'', H', α'', r', hu, hr', hm⟩
    · exact Or.inr (Or.inr ((mem_obligations_iff hv n).mpr
        ⟨ρ, rn', θ', ws', D', H', α', r', hvsub, hr', hm⟩))
  · rintro (⟨π', hπ, rn', θ', ws', D', H', α', r', hsub, hr', hm⟩ | ⟨hne, hm⟩ | hn)
    · obtain ⟨u', hu', hk, hopen, _⟩ := subterm_dischargeAt_old hdis hsub
      cases u' with
      | leaf l => simp [occKind] at hk
      | inst rn'' θ'' ws'' D'' H'' α'' =>
          simp only [occKind, OccKind.rule.injEq] at hk
          obtain ⟨rfl, rfl⟩ := hk
          have hH : H'' = H' := by simpa [openSet] using hopen hπ
          subst hH
          exact ⟨π', _, _, ws'', D'', H'', α'', r', hu', hr', hm⟩
    · exact ⟨π, rn, θ, ws, D ++ [(q, v)], H.filter fun m => decide (m ≠ q), α, r,
        hsite', hr, mem_openMandatory_filter.mpr ⟨hne, hm⟩⟩
    · obtain ⟨ρ, rn', θ', ws', D', H', α', r', hsub, hr', hm⟩ :=
        (mem_obligations_iff hv n).mp hn
      refine ⟨π ++ .ques q :: ρ, rn', θ', ws', D', H', α', r', ?_, hr', hm⟩
      rw [subterm_dischargeAt_new hdis hsite hnone ρ]
      exact hsub

/-- Discharge never adds an obligation that neither the old term nor the
discharging term carried. -/
theorem dischargeAt_obligations_subset {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {q : QuestionId} {v : SupportTerm} {π : Pos} {w w' : SupportTerm}
    {C C' Cv : Atom} {O O' Ov : List QuestionId}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
    {r : Rule}
    (hdis : dischargeAt q v π w = some w')
    (hw : HasSupport canon Pi Gamma CertOk w C O)
    (hw' : HasSupport canon Pi Gamma CertOk w' C' O')
    (hv : HasSupport canon Pi Gamma CertOk v Cv Ov)
    (hsite : subterm w π = some (.inst rn θ ws D H α)) (hr : Pi rn = some r)
    {n : QuestionId} (hn : n ∈ O') : n ∈ O ∨ n ∈ Ov := by
  rcases (dischargeAt_obligations_iff hdis hw hw' hv hsite hr n).mp hn with
    ⟨π', _, rn', θ', ws', D', H', α', r', hsub, hr', hm⟩ | ⟨_, hm⟩ | hv'
  · exact Or.inl ((mem_obligations_iff hw n).mpr
      ⟨π', rn', θ', ws', D', H', α', r', hsub, hr', hm⟩)
  · exact Or.inl ((mem_obligations_iff hw n).mpr
      ⟨π, rn, θ, ws, D, H, α, r, hsite, hr, hm⟩)
  · exact Or.inr hv'

/-- Every other obligation survives the discharge. -/
theorem dischargeAt_obligations_retained {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {q : QuestionId} {v : SupportTerm} {π : Pos} {w w' : SupportTerm}
    {C C' Cv : Atom} {O O' Ov : List QuestionId}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
    {r : Rule}
    (hdis : dischargeAt q v π w = some w')
    (hw : HasSupport canon Pi Gamma CertOk w C O)
    (hw' : HasSupport canon Pi Gamma CertOk w' C' O')
    (hv : HasSupport canon Pi Gamma CertOk v Cv Ov)
    (hsite : subterm w π = some (.inst rn θ ws D H α)) (hr : Pi rn = some r)
    {n : QuestionId} (hn : n ∈ O) (hne : n ≠ q) : n ∈ O' := by
  apply (dischargeAt_obligations_iff hdis hw hw' hv hsite hr n).mpr
  obtain ⟨π', rn', θ', ws', D', H', α', r', hsub, hr', hm⟩ :=
    (mem_obligations_iff hw n).mp hn
  by_cases hπ : π' = π
  · subst hπ
    rw [hsite] at hsub
    simp only [Option.some.injEq, SupportTerm.inst.injEq] at hsub
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hsub
    have : r' = r := Option.some.inj (hr'.symm.trans hr)
    subst this
    exact Or.inr (Or.inl ⟨hne, hm⟩)
  · exact Or.inl ⟨π', hπ, rn', θ', ws', D', H', α', r', hsub, hr', hm⟩

/-- **Closing a question.** If the discharging term is complete and `q` is open
and mandatory at no other occurrence, `q` leaves the obligation set. -/
theorem dischargeAt_closes {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {q : QuestionId} {v : SupportTerm} {π : Pos} {w w' : SupportTerm}
    {C C' Cv : Atom} {O O' : List QuestionId}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
    {r : Rule}
    (hdis : dischargeAt q v π w = some w')
    (hw : HasSupport canon Pi Gamma CertOk w C O)
    (hw' : HasSupport canon Pi Gamma CertOk w' C' O')
    (hv : HasSupport canon Pi Gamma CertOk v Cv [])
    (hsite : subterm w π = some (.inst rn θ ws D H α)) (hr : Pi rn = some r)
    (hunique : ¬ OpenMandatoryAway Pi w π q) : q ∉ O' := by
  intro hq
  rcases (dischargeAt_obligations_iff hdis hw hw' hv hsite hr q).mp hq with
    haway | ⟨hne, _⟩ | hnil
  · exact hunique haway
  · exact hne rfl
  · simp at hnil

/-- **Discharge to completion.** Discharging the only open mandatory question
of a hole, at its only open occurrence, with a complete term yields a complete
term with the same conclusion. -/
theorem dischargeAt_complete {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {q : QuestionId} {v : SupportTerm} {π : Pos} {w w' : SupportTerm}
    {C C' Cv : Atom} {O O' : List QuestionId}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
    {r : Rule}
    (hdis : dischargeAt q v π w = some w')
    (hw : HasSupport canon Pi Gamma CertOk w C O)
    (hw' : HasSupport canon Pi Gamma CertOk w' C' O')
    (hv : HasSupport canon Pi Gamma CertOk v Cv [])
    (hsite : subterm w π = some (.inst rn θ ws D H α)) (hr : Pi rn = some r)
    (honly : ∀ n ∈ O, n = q) (hunique : ¬ OpenMandatoryAway Pi w π q) :
    O' = [] ∧ C' = C := by
  refine ⟨?_, dischargeAt_conclusion hdis hw hw'⟩
  cases hO' : O' with
  | nil => rfl
  | cons n rest =>
      exfalso
      have hn : n ∈ O' := by rw [hO']; exact List.mem_cons_self
      rcases dischargeAt_obligations_subset hdis hw hw' hv hsite hr hn with hnO | hnil
      · have hnq := honly n hnO
        subst hnq
        exact dischargeAt_closes hdis hw hw' hv hsite hr hunique hn
      · simp at hnil

/-! ### Typing is preserved when the discharge answers the question -/

/-- Replace one premise by a term with the same conclusion and any obligations:
the parent keeps its conclusion and recollects its obligations. -/
private theorem prem_replace {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
    {r : Rule} {As Cs : List Atom} {Os : List (List QuestionId)}
    {DCs : List Atom} {DOs : List (List QuestionId)} {C : Atom}
    (hside : InstSide canon Pi CertOk rn θ r ws D H α As Cs Os DCs DOs C)
    (hprems : ∀ (i : Nat) (w : SupportTerm) (A : Atom) (O : List QuestionId),
      ws[i]? = some w → Cs[i]? = some A → Os[i]? = some O →
      HasSupport canon Pi Gamma CertOk w A O)
    (hdis : ∀ (j : Nat) (q : QuestionId) (w : SupportTerm) (A : Atom)
      (O : List QuestionId), D[j]? = some (q, w) → DCs[j]? = some A →
      DOs[j]? = some O → HasSupport canon Pi Gamma CertOk w A O)
    {i : Nat} {w' : SupportTerm} {A' : Atom} {O' : List QuestionId}
    (hi : i < ws.length) (hA : Cs[i]? = some A')
    (h' : HasSupport canon Pi Gamma CertOk w' A' O') :
    HasSupport canon Pi Gamma CertOk (.inst rn θ (ws.set i w') D H α) C
      (collectObligations (Os.set i O') DOs r H) := by
  refine .inst { hside with
      lenAs := by rw [List.length_set]; exact hside.lenAs
      lenCs := by rw [List.length_set]; exact hside.lenCs
      lenOs := by rw [List.length_set, List.length_set]; exact hside.lenOs }
    ?_ hdis
  intro k wk Ak Ok hk hAk hOk
  by_cases hik : i = k
  · subst hik
    have hiO : i < Os.length := by have := hside.lenOs; omega
    rw [List.getElem?_set_self hi] at hk
    rw [List.getElem?_set_self hiO] at hOk
    obtain rfl : w' = wk := Option.some.inj hk
    obtain rfl : Ak = A' := Option.some.inj (hAk.symm.trans hA)
    obtain rfl : O' = Ok := Option.some.inj hOk
    exact h'
  · rw [List.getElem?_set_ne hik] at hk hOk
    exact hprems k wk Ak Ok hk hAk hOk

/-- Replace one discharge term by a term with the same conclusion and any
obligations, keeping its question key. -/
private theorem dis_replace {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
    {r : Rule} {As Cs : List Atom} {Os : List (List QuestionId)}
    {DCs : List Atom} {DOs : List (List QuestionId)} {C : Atom}
    (hside : InstSide canon Pi CertOk rn θ r ws D H α As Cs Os DCs DOs C)
    (hprems : ∀ (i : Nat) (w : SupportTerm) (A : Atom) (O : List QuestionId),
      ws[i]? = some w → Cs[i]? = some A → Os[i]? = some O →
      HasSupport canon Pi Gamma CertOk w A O)
    (hdis : ∀ (j : Nat) (q : QuestionId) (w : SupportTerm) (A : Atom)
      (O : List QuestionId), D[j]? = some (q, w) → DCs[j]? = some A →
      DOs[j]? = some O → HasSupport canon Pi Gamma CertOk w A O)
    {j : Nat} {q : QuestionId} {w w' : SupportTerm} {A' : Atom}
    {O' : List QuestionId}
    (hqw : D[j]? = some (q, w)) (hA : DCs[j]? = some A')
    (h' : HasSupport canon Pi Gamma CertOk w' A' O') :
    HasSupport canon Pi Gamma CertOk (.inst rn θ ws (D.set j (q, w')) H α) C
      (collectObligations Os (DOs.set j O') r H) := by
  have hjlt : j < D.length := Support.lt_of_getElem?_some hqw
  have hkeys : (D.set j (q, w')).map Prod.fst = D.map Prod.fst :=
    BackendComposition.map_fst_set_of_getElem? hqw
  have hback : ∀ (k : Nat) (q₀ : QuestionId) (u : SupportTerm),
      (D.set j (q, w'))[k]? = some (q₀, u) → ∃ u₀, D[k]? = some (q₀, u₀) := by
    intro k q₀ u hk
    by_cases hjk : j = k
    · subst hjk
      rw [List.getElem?_set_self hjlt] at hk
      obtain ⟨rfl, -⟩ : q = q₀ ∧ w' = u := by simpa using hk
      exact ⟨w, hqw⟩
    · rw [List.getElem?_set_ne hjk] at hk
      exact ⟨u, hk⟩
  refine .inst
    { rule      := hside.rule
      θNodup    := hside.θNodup
      θDom      := hside.θDom
      prems     := hside.prems
      concl     := hside.concl
      lenAs     := hside.lenAs
      lenCs     := hside.lenCs
      lenOs     := hside.lenOs
      premEq    := hside.premEq
      lenDCs    := by rw [List.length_set]; exact hside.lenDCs
      lenDOs    := by rw [List.length_set, List.length_set]; exact hside.lenDOs
      ans       := fun k q₀ u A hk hAk =>
        let ⟨u₀, hu₀⟩ := hback k q₀ u hk
        hside.ans k q₀ u₀ A hu₀ hAk
      qNodup    := hside.qNodup
      dNodup    := by rw [hkeys]; exact hside.dNodup
      hNodup    := hside.hNodup
      cover     := by rw [hkeys]; exact hside.cover
      disj      := by rw [hkeys]; exact hside.disj
      keysD     := by rw [hkeys]; exact hside.keysD
      keysH     := hside.keysH
      strictNoQ := by
        intro hm
        obtain ⟨hD, hH⟩ := hside.strictNoQ hm
        exact ⟨by rw [hD]; simp, hH⟩
      assur     := hside.assur }
    hprems ?_
  intro k q₀ u A O hk hAk hOk
  by_cases hjk : j = k
  · subst hjk
    have hjO : j < DOs.length := by have := hside.lenDOs; omega
    rw [List.getElem?_set_self hjlt] at hk
    rw [List.getElem?_set_self hjO] at hOk
    obtain ⟨-, rfl⟩ : q = q₀ ∧ w' = u := by simpa using hk
    obtain rfl : A = A' := Option.some.inj (hAk.symm.trans hA)
    obtain rfl : O' = O := Option.some.inj hOk
    exact h'
  · rw [List.getElem?_set_ne hjk] at hk hOk
    exact hdis k q₀ u A O hk hAk hOk

/-- The site step: closing an open question with a term that answers its
pattern keeps the instance typed at the same conclusion. -/
private theorem closeOpen_hasSupport {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
    {C : Atom} {O : List QuestionId} {q : QuestionId} {v : SupportTerm}
    {r : Rule} {qd : Question} {Aq Cv : Atom} {Ov : List QuestionId}
    (hw : HasSupport canon Pi Gamma CertOk (.inst rn θ ws D H α) C O)
    (hqH : q ∈ H) (hr : Pi rn = some r) (hqd : qd ∈ r.questions)
    (hname : qd.name = q) (hans : instAPat θ qd.answer = some Aq)
    (hv : HasSupport canon Pi Gamma CertOk v Cv Ov) (heq : equiv canon Cv Aq) :
    ∃ O', HasSupport canon Pi Gamma CertOk
      (.inst rn θ ws (D ++ [(q, v)]) (H.filter fun n => decide (n ≠ q)) α) C O' := by
  cases hw with
  | @inst _ _ _ _ _ _ r₀ As Cs Os DCs DOs _ hside hprems hdis =>
      have hr₀ : r₀ = r := Option.some.inj (hside.rule.symm.trans hr)
      subst hr₀
      have hqD : q ∉ D.map Prod.fst := fun hmem => hside.disj q hmem hqH
      have hlenDCs := hside.lenDCs
      have hlenDOs := hside.lenDOs
      refine ⟨_, .inst (Cs := Cs) (Os := Os) (As := As)
        (DCs := DCs ++ [Cv]) (DOs := DOs ++ [Ov])
        { rule      := hside.rule
          θNodup    := hside.θNodup
          θDom      := hside.θDom
          prems     := hside.prems
          concl     := hside.concl
          lenAs     := hside.lenAs
          lenCs     := hside.lenCs
          lenOs     := hside.lenOs
          premEq    := hside.premEq
          lenDCs    := by simp [hlenDCs]
          lenDOs    := by simp [hlenDOs]
          ans       := ?_
          qNodup    := hside.qNodup
          dNodup    := ?_
          hNodup    := hside.hNodup.filter _
          cover     := ?_
          disj      := ?_
          keysD     := ?_
          keysH     := ?_
          strictNoQ := fun hm => absurd ((hside.strictNoQ hm).2 ▸ hqH)
            List.not_mem_nil
          assur     := hside.assur }
        hprems ?_⟩
      · intro k q₀ u A hk hAk
        by_cases hkD : k < D.length
        · rw [List.getElem?_append_left hkD] at hk
          rw [List.getElem?_append_left (by omega)] at hAk
          exact hside.ans k q₀ u A hk hAk
        · have hk' := hk
          rw [List.getElem?_append_right (by omega)] at hk'
          have hkeq : k - D.length = 0 := by
            cases hsub : k - D.length with
            | zero => rfl
            | succ m => rw [hsub] at hk'; simp at hk'
          rw [hkeq] at hk'
          simp only [List.getElem?_cons_zero, Option.some.injEq,
            Prod.mk.injEq] at hk'
          obtain ⟨rfl, rfl⟩ := hk'
          rw [List.getElem?_append_right (by omega)] at hAk
          rw [show k - DCs.length = 0 by omega] at hAk
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hAk
          subst hAk
          exact ⟨qd, hqd, hname, Aq, hans, heq⟩
      · rw [List.map_append, List.nodup_append]
        refine ⟨hside.dNodup, by simp, ?_⟩
        intro a ha b hb
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        intro hab
        subst hab
        exact hqD ha
      · intro qd' hqd'
        rcases hside.cover qd' hqd' with hD | hH
        · exact Or.inl (by rw [List.map_append]; exact List.mem_append_left _ hD)
        · by_cases hn : qd'.name = q
          · exact Or.inl (by rw [List.map_append]; simp [hn])
          · exact Or.inr (List.mem_filter.mpr ⟨hH, by simpa using hn⟩)
      · intro n hn hnH
        have hnH' := (List.mem_filter.mp hnH)
        rw [List.map_append] at hn
        rcases List.mem_append.mp hn with hD | hq
        · exact hside.disj n hD hnH'.1
        · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hq
          subst hq
          simp at hnH'
      · intro n hn
        rw [List.map_append] at hn
        rcases List.mem_append.mp hn with hD | hq
        · exact hside.keysD n hD
        · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hq
          subst hq
          exact hside.keysH n hqH
      · intro n hn
        exact hside.keysH n (List.mem_filter.mp hn).1
      · intro k q₀ u A O' hk hAk hOk
        by_cases hkD : k < D.length
        · rw [List.getElem?_append_left hkD] at hk
          rw [List.getElem?_append_left (by omega)] at hAk
          rw [List.getElem?_append_left (by omega)] at hOk
          exact hdis k q₀ u A O' hk hAk hOk
        · have hk' := hk
          rw [List.getElem?_append_right (by omega)] at hk'
          have hkeq : k - D.length = 0 := by
            cases hsub : k - D.length with
            | zero => rfl
            | succ m => rw [hsub] at hk'; simp at hk'
          rw [hkeq] at hk'
          simp only [List.getElem?_cons_zero, Option.some.injEq,
            Prod.mk.injEq] at hk'
          obtain ⟨rfl, rfl⟩ := hk'
          rw [List.getElem?_append_right (by omega),
            show k - DCs.length = 0 by omega] at hAk
          rw [List.getElem?_append_right (by omega),
            show k - DOs.length = 0 by omega] at hOk
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hAk hOk
          subst hAk
          subst hOk
          exact hv

/-- **Discharge preserves typing.** If `w` types and `v` types with a
conclusion that answers question `q` of the site's rule under the site's
substitution, the rewritten term types, at the same conclusion. -/
theorem dischargeAt_hasSupport {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {q : QuestionId} {v : SupportTerm} {Cv : Atom} {Ov : List QuestionId}
    (hv : HasSupport canon Pi Gamma CertOk v Cv Ov) :
    ∀ {π : Pos} {w w' : SupportTerm} {C : Atom} {O : List QuestionId}
      {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
      {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
      {r : Rule} {qd : Question} {Aq : Atom},
      HasSupport canon Pi Gamma CertOk w C O →
      dischargeAt q v π w = some w' →
      subterm w π = some (.inst rn θ ws D H α) → Pi rn = some r →
      qd ∈ r.questions → qd.name = q → instAPat θ qd.answer = some Aq →
      equiv canon Cv Aq →
      ∃ O', HasSupport canon Pi Gamma CertOk w' C O' := by
  intro π
  induction π with
  | nil =>
      intro w w' C O rn θ ws D H α r qd Aq hw hdis hsite hr hqd hname hans heq
      obtain ⟨rn₀, θ₀, ws₀, D₀, H₀, α₀, rfl, hqH, rfl⟩ := dischargeAt_nil hdis
      simp only [subterm, Option.some.injEq, SupportTerm.inst.injEq] at hsite
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hsite
      exact closeOpen_hasSupport hw hqH hr hqd hname hans hv heq
  | cons e π ih =>
      intro w w' C O rn θ ws D H α r qd Aq hw hdis hsite hr hqd hname hans heq
      cases w with
      | leaf l => simp [dischargeAt] at hdis
      | inst rn₀ θ₀ ws₀ D₀ H₀ α₀ =>
          cases hw with
          | @inst _ _ _ _ _ _ r₀ As Cs Os DCs DOs _ hside hprems hdisT =>
              cases e with
              | prem i =>
                  simp only [dischargeAt] at hdis
                  cases hc : ws₀[i]? with
                  | none => simp [hc] at hdis
                  | some c =>
                      simp only [hc] at hdis
                      cases hc' : dischargeAt q v π c with
                      | none => simp [hc'] at hdis
                      | some c' =>
                          simp only [hc', Option.map_some, Option.some.injEq] at hdis
                          subst hdis
                          have hlt : i < ws₀.length := Support.lt_of_getElem?_some hc
                          obtain ⟨A, hA⟩ := Support.getElem?_some_of_lt Cs i
                            (by have := hside.lenCs; omega)
                          obtain ⟨Oc, hOc⟩ := Support.getElem?_some_of_lt Os i
                            (by have := hside.lenOs; omega)
                          have hcT := hprems i c A Oc hc hA hOc
                          simp only [subterm, hc] at hsite
                          obtain ⟨Oc', hc'T⟩ :=
                            ih hcT hc' hsite hr hqd hname hans heq
                          exact ⟨_, prem_replace hside hprems hdisT hlt hA hc'T⟩
              | ques q₀ =>
                  simp only [dischargeAt] at hdis
                  cases hc : lookupDis D₀ q₀ with
                  | none => simp [hc] at hdis
                  | some c =>
                      simp only [hc] at hdis
                      cases hc' : dischargeAt q v π c with
                      | none => simp [hc'] at hdis
                      | some c' =>
                          simp only [hc', Option.map_some, Option.some.injEq] at hdis
                          subst hdis
                          obtain ⟨j, hj, hset⟩ := replaceDis_eq_set c' hc
                          have hjlt : j < D₀.length := Support.lt_of_getElem?_some hj
                          obtain ⟨A, hA⟩ := Support.getElem?_some_of_lt DCs j
                            (by have := hside.lenDCs; omega)
                          obtain ⟨Oc, hOc⟩ := Support.getElem?_some_of_lt DOs j
                            (by have := hside.lenDOs; omega)
                          have hcT := hdisT j q₀ c A Oc hj hA hOc
                          simp only [subterm, hc] at hsite
                          obtain ⟨Oc', hc'T⟩ :=
                            ih hcT hc' hsite hr hqd hname hans heq
                          rw [hset]
                          exact ⟨_, dis_replace hside hprems hdisT hj hA hc'T⟩

/-! ### Leaves -/

theorem mem_leavesList_iff {ws : List SupportTerm} {l : LeafId} :
    l ∈ leavesList ws ↔ ∃ x ∈ ws, l ∈ leaves x := by
  induction ws with
  | nil => simp [leavesList]
  | cons x rest ih =>
      simp only [leavesList, List.mem_append, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨y, hy, hl⟩)
        · exact ⟨x, Or.inl rfl, h⟩
        · exact ⟨y, Or.inr hy, hl⟩
      · rintro ⟨y, rfl | hy, hl⟩
        · exact Or.inl hl
        · exact Or.inr ⟨y, hy, hl⟩

theorem mem_leavesDis_iff {D : List (QuestionId × SupportTerm)} {l : LeafId} :
    l ∈ leavesDis D ↔ ∃ e ∈ D, l ∈ leaves e.2 := by
  induction D with
  | nil => simp [leavesDis]
  | cons e rest ih =>
      obtain ⟨k, x⟩ := e
      simp only [leavesDis, List.mem_append, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨y, hy, hl⟩)
        · exact ⟨(k, x), Or.inl rfl, h⟩
        · exact ⟨y, Or.inr hy, hl⟩
      · rintro ⟨y, rfl | hy, hl⟩
        · exact Or.inl hl
        · exact Or.inr ⟨y, hy, hl⟩

/-- Membership in a list, split at one slot. -/
private theorem mem_split_at {α : Type _} {xs : List α} {i : Nat} {old : α}
    (hold : xs[i]? = some old) (P : α → Prop) :
    (∃ x ∈ xs, P x) ↔ P old ∨ (∃ j x, j ≠ i ∧ xs[j]? = some x ∧ P x) := by
  constructor
  · rintro ⟨x, hx, hP⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
    by_cases hij : j = i
    · subst hij
      rw [hold] at hj
      cases hj
      exact Or.inl hP
    · exact Or.inr ⟨j, x, hij, hj, hP⟩
  · rintro (hP | ⟨j, x, _, hj, hP⟩)
    · exact ⟨old, List.mem_of_getElem? hold, hP⟩
    · exact ⟨x, List.mem_of_getElem? hj, hP⟩

private theorem mem_set_split {α : Type _} {xs : List α} {i : Nat}
    {old new : α} (hold : xs[i]? = some old) (P : α → Prop) :
    (∃ x ∈ xs.set i new, P x) ↔ P new ∨ (∃ j x, j ≠ i ∧ xs[j]? = some x ∧ P x) := by
  have hlt : i < xs.length := Support.lt_of_getElem?_some hold
  have hnew : (xs.set i new)[i]? = some new := List.getElem?_set_self hlt
  rw [mem_split_at hnew P]
  constructor
  · rintro (hP | ⟨j, x, hji, hj, hP⟩)
    · exact Or.inl hP
    · rw [List.getElem?_set_ne (Ne.symm hji)] at hj
      exact Or.inr ⟨j, x, hji, hj, hP⟩
  · rintro (hP | ⟨j, x, hji, hj, hP⟩)
    · exact Or.inl hP
    · refine Or.inr ⟨j, x, hji, ?_, hP⟩
      rw [List.getElem?_set_ne (Ne.symm hji)]
      exact hj

/-- **Leaves after discharge.** The rewritten term uses exactly the leaves of
the old term and of the discharging term. -/
theorem leaves_dischargeAt {q : QuestionId} {v : SupportTerm} :
    ∀ {π : Pos} {w w' : SupportTerm}, dischargeAt q v π w = some w' →
      ∀ l, l ∈ leaves w' ↔ l ∈ leaves w ∨ l ∈ leaves v := by
  intro π
  induction π with
  | nil =>
      intro w w' h l
      obtain ⟨rn, θ, ws, D, H, α, rfl, _, rfl⟩ := dischargeAt_nil h
      simp only [leaves, List.mem_append, mem_leavesDis_iff, List.mem_cons,
        List.mem_nil_iff, or_false]
      constructor
      · rintro (hws | ⟨e, he | rfl, hl⟩)
        · exact Or.inl (Or.inl hws)
        · exact Or.inl (Or.inr ⟨e, he, hl⟩)
        · exact Or.inr hl
      · rintro ((hws | ⟨e, he, hl⟩) | hl)
        · exact Or.inl hws
        · exact Or.inr ⟨e, Or.inl he, hl⟩
        · exact Or.inr ⟨(q, v), Or.inr rfl, hl⟩
  | cons e π ih =>
      intro w w' h l
      cases w with
      | leaf l₀ => simp [dischargeAt] at h
      | inst rn θ ws D H α =>
          cases e with
          | prem i =>
              simp only [dischargeAt] at h
              cases hc : ws[i]? with
              | none => simp [hc] at h
              | some c =>
                  simp only [hc] at h
                  cases hc' : dischargeAt q v π c with
                  | none => simp [hc'] at h
                  | some c' =>
                      simp only [hc', Option.map_some, Option.some.injEq] at h
                      subst h
                      have hih := ih hc' l
                      simp only [leaves, List.mem_append, mem_leavesList_iff]
                      rw [mem_set_split hc (fun x => l ∈ leaves x),
                        mem_split_at hc (fun x => l ∈ leaves x), hih]
                      constructor
                      · rintro (((hc | hv) | hrest) | hD)
                        · exact Or.inl (Or.inl (Or.inl hc))
                        · exact Or.inr hv
                        · exact Or.inl (Or.inl (Or.inr hrest))
                        · exact Or.inl (Or.inr hD)
                      · rintro (((hc | hrest) | hD) | hv)
                        · exact Or.inl (Or.inl (Or.inl hc))
                        · exact Or.inl (Or.inr hrest)
                        · exact Or.inr hD
                        · exact Or.inl (Or.inl (Or.inr hv))
          | ques q₀ =>
              simp only [dischargeAt] at h
              cases hc : lookupDis D q₀ with
              | none => simp [hc] at h
              | some c =>
                  simp only [hc] at h
                  cases hc' : dischargeAt q v π c with
                  | none => simp [hc'] at h
                  | some c' =>
                      simp only [hc', Option.map_some, Option.some.injEq] at h
                      subst h
                      obtain ⟨j, hj, hset⟩ := replaceDis_eq_set c' hc
                      have hih := ih hc' l
                      simp only [leaves, List.mem_append, mem_leavesDis_iff]
                      rw [hset, mem_set_split hj (fun x => l ∈ leaves x.2),
                        mem_split_at hj (fun x => l ∈ leaves x.2)]
                      simp only
                      rw [hih]
                      constructor
                      · rintro (hws | ((hc | hv) | hrest))
                        · exact Or.inl (Or.inl hws)
                        · exact Or.inl (Or.inr (Or.inl hc))
                        · exact Or.inr hv
                        · exact Or.inl (Or.inr (Or.inr hrest))
                      · rintro ((hws | (hc | hrest)) | hv)
                        · exact Or.inl hws
                        · exact Or.inr (Or.inl (Or.inl hc))
                        · exact Or.inr (Or.inr hrest)
                        · exact Or.inr (Or.inl (Or.inr hv))

/-- The rewritten term differs from the original: the site's open set lost
`q`. -/
theorem dischargeAt_ne {q : QuestionId} {v : SupportTerm} {π : Pos}
    {w w' : SupportTerm} (h : dischargeAt q v π w = some w') : w' ≠ w := by
  intro heq
  subst heq
  have hsome : (dischargeAt q v π w').isSome = true := by rw [h]; rfl
  obtain ⟨rn, θ, ws, D, H, α, hsub, hq⟩ :=
    (dischargeAt_isSome_iff q v π w').mp hsome
  have hsite := subterm_dischargeAt_site h hsub
  rw [hsub] at hsite
  simp only [Option.some.injEq, SupportTerm.inst.injEq] at hsite
  have hH := hsite.2.2.2.2.1
  rw [hH] at hq
  simp at hq

end Lara.Update.Discharge
