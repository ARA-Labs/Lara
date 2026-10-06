/-
Mechanized compilation with subargument closure (`Lara.Compile`) — the Lean
port of the v0.1-frozen compile rules (spec §8, "Compilation rules", frozen in
the M1 lock pass), over the *concrete* §6.1/§7.1 layers rather than the opaque
carrier of `Lara/Grounded.lean`.

What this file discharges, against the exact spec figure:

* **Result 4 ("no untyped node or attack"), both halves** —
  `compile_nodes_checked`: every AF node is a complete checked support term
  (`O = ∅`); `edge_iff`: every edge decomposes into a *typed* declared attack
  whose source is the edge's tail and whose attacked occurrence is contained
  in the edge's head. Nothing untyped can appear, by construction.
* **Subargument closure, characterized concretely** — `Contains` is
  structural occurrence (`∃ π', v@π' = occ(k)`); `target_contains_occ` and
  `closure_includes_direct` show the attack's own target receives an edge, so
  closure edges *extend* (never replace) the direct attack; `attackOcc_unique`
  — the attacked occurrence is a function of the attack.
* **The N16 bridge, argument level** — `srcIn_iff_directIn` /
  `srcIn_iff_grounded`: a source-level declarative judgment
  (`SrcIn`/`SrcOut`, defined over the Prop-level closure-edge relation
  `Edge`, never running the grounded iteration) agrees with the abstract
  declarative and executable semantics of `Lara/Grounded.lean` over the
  compiled AF `toAF`.
* **The N16 bridge, claim-status level** — `SrcStatus` is the four-state
  claim status read from `SrcIn`/`SrcOut` alone (no AF, no iteration), and
  `srcStatus_iff` proves it holds iff the status equals executable
  `Grounded.statusC` over the compiled AF. Together the two levels give
  source-to-compiled
  status preservation. The residual Bool-edge obligation is now discharged:
  executable support, positional-attack, and whole-program checking construct
  `CheckedProgram`, and the general closure-edge decider `edgeB` with its
  `edgeB_faithful` proof supplies `Faithful` constructively —
  exposed oracle-free through `checkedAF`/`srcStatus_iff_checked` — closing §9
  result 6's source-vs-compiled half. Nothing else is missing at this layer.

Design notes:

* A `CheckedProgram` carries its own evidence (`complete`, `typed`) — the Lean
  analogue of "a well-formed source program": compilation is only defined
  downstream of the checker, so the structure is the checker's postcondition
  (the `StrictJudgment` convention of `Lara/Strict.lean`). Its `args` carry a
  `Nodup` invariant: spec §8's `Args(P)` is a *set* of terms, so
  term-identical declarations compile to one node (declaration names are
  report/`eraseCert` plumbing, not AF semantics — two structurally equal
  terms contain the same occurrences and receive identical edge sets).
  This remains the legacy/generic attack-*soundness* boundary: it says every
  declared attack is typed, not that all relevant conflicts were declared.
  `AttackComplete` is a separate postcondition carried by
  `Check.Program.ProgramAcceptance` and `Unit.CheckedUnit`.
* Everything stays Prop-level until the bridge; `toAF` indexes arguments by
  list position (`Grounded.Arg = Nat`), and `Faithful` ties the oracle to
  `Edge` exactly on in-range indices and forces it false off-range.
* `coveredB` is the one exact declared-edge coverage scan reused by `edgeB`.
  Accepted-unit checking obtains its retained node metadata from the checker
  cache; this compile layer never re-infers support for that flow.
-/

import Lara.Attack
import Lara.Grounded

namespace Lara.Compile

open Lara.Support

/-! ### Occurrence containment and the attacked occurrence (spec §8) -/

/-- `t` occurs in `v`: some position reaches it (`∃ π', v@π' = t`). -/
def Contains (v t : SupportTerm) : Prop :=
  ∃ π : Attack.Pos, Attack.subterm v π = some t

theorem contains_refl (v : SupportTerm) : Contains v v := ⟨[], rfl⟩

/-- `occ(k)`: the attacked occurrence — the whole target for a rebut, the
subterm at `π` for an undercut/undermine. -/
def AttackOcc : Attack.Attack → SupportTerm → Prop
  | .rebut _ u, t => t = u
  | .undercut _ u π, t => Attack.subterm u π = some t
  | .undermine _ u π, t => Attack.subterm u π = some t

/-- The attacked occurrence is a function of the attack. -/
theorem attackOcc_unique {k : Attack.Attack} {t t' : SupportTerm}
    (h : AttackOcc k t) (h' : AttackOcc k t') : t = t' := by
  cases k with
  | rebut w u =>
    simp only [AttackOcc] at h h'
    rw [h, h']
  | undercut w u π =>
    simp only [AttackOcc] at h h'
    exact Option.some.inj (h.symm.trans h')
  | undermine w u π =>
    simp only [AttackOcc] at h h'
    exact Option.some.inj (h.symm.trans h')

/-- The attack's own target contains its attacked occurrence — for a rebut the
occurrence *is* the target; for undercut/undermine the position witnesses it. -/
theorem target_contains_occ {k : Attack.Attack} {t : SupportTerm}
    (h : AttackOcc k t) : Contains k.target t := by
  cases k with
  | rebut w u =>
    simp only [AttackOcc] at h
    exact h ▸ contains_refl u
  | undercut w u π => exact ⟨π, h⟩
  | undermine w u π => exact ⟨π, h⟩

/-! ### Decidable structural closure (spec §8, executable)

`Contains` quantifies over the infinite position type, so it is not directly
decidable. `containsB` is its total Boolean twin: a structural scan over every
occurrence (premise and discharge subterms, self included). It agrees with
`Contains` on the well-formed domain (`DisNodup`), and the guard is
load-bearing — a duplicate discharge key makes the scan see a branch the
positional `lookupDis` (first-match) can never reach. -/

mutual
  /-- `containsB v t`: does `t` occur structurally in `v`? A total Boolean scan
  over `v` and its premise/discharge subterms. Uses explicit list recursion
  (Lean 4.32 cannot recurse through `SupportTerm`'s nested list fields via a
  `List.any` lambda), mirroring `leaves`/`leavesList`/`leavesDis`. -/
  def containsB : SupportTerm → SupportTerm → Bool
    | .leaf l, t => decide (.leaf l = t)
    | .inst r θ ws ds hs a, t =>
        decide (.inst r θ ws ds hs a = t) || containsBList ws t || containsBDis ds t
  def containsBList : List SupportTerm → SupportTerm → Bool
    | [], _ => false
    | w :: ws, t => containsB w t || containsBList ws t
  def containsBDis : List (QuestionId × SupportTerm) → SupportTerm → Bool
    | [], _ => false
    | (_, w) :: rest, t => containsB w t || containsBDis rest t
end

/-- `attackClosureB k target`: does the attacked occurrence of `k` occur in
`target`? For a rebut the occurrence is the whole target term; for an
undercut/undermine it is the subterm at the attack's position (`none` off
range gives `false`). This is the executable closure test behind `Edge`. -/
def attackClosureB (k : Attack.Attack) (target : SupportTerm) : Bool :=
  match k with
  | .rebut _ u => containsB target u
  | .undercut _ u π | .undermine _ u π =>
      match Attack.subterm u π with
      | some t => containsB target t
      | none => false

mutual
  /-- Recursive discharge-key distinctness: at every `inst` node the discharge
  keys are `Nodup`. This is the well-formedness the frontend cannot forge
  (guaranteed by the checker, `hasSupport_disNodup`) and exactly the domain on
  which `containsB` agrees with the positional `Contains`. -/
  def DisNodup : SupportTerm → Prop
    | .leaf _ => True
    | .inst _ _ ws D _ _ => (D.map Prod.fst).Nodup ∧ DisNodupList ws ∧ DisNodupDis D
  def DisNodupList : List SupportTerm → Prop
    | [] => True
    | w :: ws => DisNodup w ∧ DisNodupList ws
  def DisNodupDis : List (QuestionId × SupportTerm) → Prop
    | [] => True
    | (_, w) :: rest => DisNodup w ∧ DisNodupDis rest
end

/-! ### Checked programs and the compiled edge relation (spec §8, frozen) -/

variable {canon : String → String} {Pi : RuleId → Option Rule}
  {Gamma : LeafId → Option Atom}
  {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
  {dp : Attack.DefeatPolicy}

/-- **Every checked support term satisfies `DisNodup`.** By induction on
`HasSupport`: the top-level discharge keys are `Nodup` by `InstSide.dNodup`,
and the premise/discharge subterms satisfy `DisNodup` by the induction
hypotheses. The recursive `DisNodupList`/`DisNodupDis` facts are rebuilt by an
auxiliary induction on the list with index bookkeeping (mirroring
`leaves_declared`). -/
theorem hasSupport_disNodup {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk w C O) : DisNodup w := by
  induction h with
  | leaf _ => exact True.intro
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis ihprems ihdis =>
    refine ⟨hside.dNodup, ?_, ?_⟩
    · -- `DisNodupList ws` from the per-index premise IH.
      clear hprems hdis ihdis
      have hlen : Cs.length = ws.length := hside.lenCs
      have hlenO : Os.length = ws.length := hside.lenOs
      -- generalize over an index offset so `ws[i]?` lines up with the tail.
      suffices H : ∀ (ws' : List SupportTerm),
          (∀ (i : Nat) (w' : SupportTerm), ws'[i]? = some w' → DisNodup w') →
          DisNodupList ws' by
        exact H ws (fun i w' hw' => by
          have hi := lt_of_getElem?_some hw'
          obtain ⟨A, hA⟩ := getElem?_some_of_lt Cs i (by omega)
          obtain ⟨O', hO⟩ := getElem?_some_of_lt Os i (by omega)
          exact ihprems i w' A O' hw' hA hO)
      intro ws' hall
      induction ws' with
      | nil => exact True.intro
      | cons x xs ih =>
        refine ⟨hall 0 x rfl, ih (fun i w' hw' => hall (i + 1) w' (by simpa using hw'))⟩
    · -- `DisNodupDis D` from the per-index discharge IH.
      clear hprems hdis ihprems
      have hlen : DCs.length = D.length := hside.lenDCs
      have hlenO : DOs.length = D.length := hside.lenDOs
      suffices H : ∀ (D' : List (QuestionId × SupportTerm)),
          (∀ (j : Nat) (q : QuestionId) (w' : SupportTerm),
            D'[j]? = some (q, w') → DisNodup w') →
          DisNodupDis D' by
        exact H D (fun j q w' hw' => by
          have hj := lt_of_getElem?_some hw'
          obtain ⟨A, hA⟩ := getElem?_some_of_lt DCs j (by omega)
          obtain ⟨O', hO⟩ := getElem?_some_of_lt DOs j (by omega)
          exact ihdis j q w' A O' hw' hA hO)
      intro D' hall
      induction D' with
      | nil => exact True.intro
      | cons x xs ih =>
        obtain ⟨q, w'⟩ := x
        refine ⟨hall 0 q w' rfl, ih (fun j q'' w'' hw'' =>
          hall (j + 1) q'' w'' (by simpa using hw''))⟩

/-- A successful `lookupDis` names a key that is present. Used to discharge the
`containsBDis` cons lifting: a hit deeper in the list has a key distinct from
the head (by `Nodup`), so the head branch does not shadow it. -/
theorem lookupDis_some_mem {D : List (QuestionId × SupportTerm)}
    {q : QuestionId} {w : SupportTerm} (h : Attack.lookupDis D q = some w) :
    q ∈ D.map Prod.fst := by
  induction D with
  | nil => simp [Attack.lookupDis] at h
  | cons hd tl ih =>
    obtain ⟨q', w'⟩ := hd
    simp only [Attack.lookupDis] at h
    by_cases hq : q' = q
    · subst hq; simp
    · simp only [if_neg hq] at h
      exact List.mem_cons.mpr (Or.inr (ih h))

/-- A successful `lookupDis` is witnessed by a positional entry. -/
theorem lookupDis_some_getElem? {D : List (QuestionId × SupportTerm)}
    {q : QuestionId} {w : SupportTerm} (h : Attack.lookupDis D q = some w) :
    ∃ j : Nat, D[j]? = some (q, w) := by
  induction D with
  | nil => simp [Attack.lookupDis] at h
  | cons hd tl ih =>
    obtain ⟨q', w'⟩ := hd
    simp only [Attack.lookupDis] at h
    by_cases hq : q' = q
    · subst hq
      simp only [if_true, Option.some.injEq] at h
      exact ⟨0, by simp [h]⟩
    · simp only [if_neg hq] at h
      obtain ⟨j, hj⟩ := ih h
      exact ⟨j + 1, by simpa using hj⟩

private theorem mem_collectObligations {Os DOs : List (List QuestionId)}
    {r : Rule} {H : List QuestionId} {O : List QuestionId} {q : QuestionId}
    (hO : O ∈ Os ∨ O ∈ DOs) (hq : q ∈ O) :
    q ∈ collectObligations Os DOs r H := by
  rw [collectObligations, unionAll]
  apply (mem_dedupQuestions _).mpr
  rw [List.mem_flatten]
  rcases hO with hO | hO
  · exact ⟨O, by simp [hO], hq⟩
  · exact ⟨O, by simp [hO], hq⟩

/-- **Obligations propagate upward.** Every occurrence inside a typed term is
itself typed, with a root obligation set contained in the whole term's: §6.1
unions premise and discharge obligations into the instance's. -/
theorem hasSupport_subterm {v : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk v C O) :
    ∀ {π : Attack.Pos} {t : SupportTerm}, Attack.subterm v π = some t →
      ∃ C' O', HasSupport canon Pi Gamma CertOk t C' O' ∧ ∀ q ∈ O', q ∈ O := by
  induction h with
  | @leaf l p hΓ =>
    intro π t hsub
    cases π with
    | nil =>
      simp only [Attack.subterm, Option.some.injEq] at hsub
      subst hsub
      exact ⟨p, [], .leaf hΓ, fun _ hq => hq⟩
    | cons e π => simp [Attack.subterm] at hsub
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis ihprems ihdis =>
    intro π t hsub
    cases π with
    | nil =>
      simp only [Attack.subterm, Option.some.injEq] at hsub
      subst hsub
      exact ⟨C, _, .inst hside hprems hdis, fun _ hq => hq⟩
    | cons e π =>
      cases e with
      | prem i =>
        simp only [Attack.subterm] at hsub
        cases hw : ws[i]? with
        | none => rw [hw] at hsub; cases hsub
        | some w =>
          rw [hw] at hsub
          have hi := lt_of_getElem?_some hw
          obtain ⟨A, hA⟩ := getElem?_some_of_lt Cs i
            (by have := hside.lenCs; omega)
          obtain ⟨O', hO'⟩ := getElem?_some_of_lt Os i
            (by have := hside.lenOs; omega)
          obtain ⟨C'', O'', ht, hsubset⟩ := ihprems i w A O' hw hA hO' hsub
          exact ⟨C'', O'', ht, fun q hq =>
            mem_collectObligations (Or.inl (List.mem_of_getElem? hO'))
              (hsubset q hq)⟩
      | ques q =>
        simp only [Attack.subterm] at hsub
        cases hw : Attack.lookupDis D q with
        | none => rw [hw] at hsub; cases hsub
        | some w =>
          rw [hw] at hsub
          obtain ⟨j, hj⟩ := lookupDis_some_getElem? hw
          have hjlt := lt_of_getElem?_some hj
          obtain ⟨A, hA⟩ := getElem?_some_of_lt DCs j
            (by have := hside.lenDCs; omega)
          obtain ⟨O', hO'⟩ := getElem?_some_of_lt DOs j
            (by have := hside.lenDOs; omega)
          obtain ⟨C'', O'', ht, hsubset⟩ := ihdis j q w A O' hj hA hO' hsub
          exact ⟨C'', O'', ht, fun q' hq' =>
            mem_collectObligations (Or.inr (List.mem_of_getElem? hO'))
              (hsubset q' hq')⟩

/-- **Complete terms have no incomplete occurrence.** Every occurrence inside a
complete term (`O = ∅`) is itself complete. -/
theorem complete_contains_complete {v t : SupportTerm} {C : Atom}
    (hv : HasSupport canon Pi Gamma CertOk v C []) (hcontains : Contains v t) :
    ∃ C', HasSupport canon Pi Gamma CertOk t C' [] := by
  obtain ⟨π, hπ⟩ := hcontains
  obtain ⟨C', O', ht, hsubset⟩ := hasSupport_subterm hv hπ
  cases O' with
  | nil => exact ⟨C', ht⟩
  | cons q _ => exact absurd (hsubset q (by simp)) (by simp)

/-- No complete term contains a typed term with mandatory obligations: a
wrapper of a hole inherits the hole's obligations and is itself a hole. -/
theorem complete_not_contains_hole {v t : SupportTerm} {C Ct : Atom}
    {O : List QuestionId}
    (hv : HasSupport canon Pi Gamma CertOk v C [])
    (ht : HasSupport canon Pi Gamma CertOk t Ct O) (hO : O ≠ []) :
    ¬ Contains v t := by
  intro hcontains
  obtain ⟨C', ht'⟩ := complete_contains_complete hv hcontains
  exact hO (hasSupport_unique ht ht').2

/-- **`containsB` decides `Contains` on the `DisNodup` domain.** The mutual
statement over the three scanners is proved together (via the four-motive
`SupportTerm.rec`), generalized over the query. Forward: a hit in
`containsBList`/`containsBDis` yields a positional witness — for discharges the
`Nodup` key set makes `lookupDis` return exactly the branch that hit (the
load-bearing use of the guard). Reverse: a position witness reduces the
matching branch. -/
theorem containsB_iff {v : SupportTerm} (hwf : DisNodup v) (t : SupportTerm) :
    containsB v t = true ↔ Contains v t := by
  revert t hwf
  refine SupportTerm.rec
    (motive_1 := fun v => DisNodup v → ∀ t,
      containsB v t = true ↔ Contains v t)
    (motive_2 := fun ws => DisNodupList ws → ∀ t,
      containsBList ws t = true ↔ ∃ (i : Nat) (w : SupportTerm), ws[i]? = some w ∧ Contains w t)
    (motive_3 := fun D => (D.map Prod.fst).Nodup → DisNodupDis D → ∀ t,
      containsBDis D t = true ↔ ∃ q w, Attack.lookupDis D q = some w ∧ Contains w t)
    (motive_4 := fun p => DisNodup p.2 → ∀ t,
      containsB p.2 t = true ↔ Contains p.2 t)
    ?leaf ?inst ?nilL ?consL ?nilD ?consD ?pair v
  case leaf =>
    intro l _ t
    simp only [containsB]
    constructor
    · intro h
      refine ⟨[], ?_⟩
      simp only [Attack.subterm]
      exact congrArg some (of_decide_eq_true h)
    · rintro ⟨π, hπ⟩
      cases π with
      | nil => exact decide_eq_true (by simpa only [Attack.subterm, Option.some.injEq] using hπ)
      | cons e rest => simp [Attack.subterm] at hπ
  case inst =>
    intro r θ ws ds hs a ihL ihD hwf t
    obtain ⟨hnodup, hwfL, hwfD⟩ := hwf
    simp only [containsB, Bool.or_eq_true]
    rw [ihL hwfL t, ihD hnodup hwfD t]
    constructor
    · rintro ((h | ⟨i, w, hw, hc⟩) | ⟨q, w, hq, hc⟩)
      · exact ⟨[], congrArg some (of_decide_eq_true h)⟩
      · obtain ⟨π, hπ⟩ := hc
        exact ⟨.prem i :: π, by simp only [Attack.subterm, hw]; exact hπ⟩
      · obtain ⟨π, hπ⟩ := hc
        exact ⟨.ques q :: π, by simp only [Attack.subterm, hq]; exact hπ⟩
    · rintro ⟨π, hπ⟩
      cases π with
      | nil =>
        simp only [Attack.subterm, Option.some.injEq] at hπ
        exact Or.inl (Or.inl (decide_eq_true hπ))
      | cons e rest =>
        cases e with
        | prem i =>
          simp only [Attack.subterm] at hπ
          revert hπ
          cases hw : ws[i]? with
          | none => intro h; simp at h
          | some w => intro hπ; exact Or.inl (Or.inr ⟨i, w, hw, rest, hπ⟩)
        | ques q =>
          simp only [Attack.subterm] at hπ
          revert hπ
          cases hq : Attack.lookupDis ds q with
          | none => intro h; simp at h
          | some w => intro hπ; exact Or.inr ⟨q, w, hq, rest, hπ⟩
  case nilL =>
    intro _ t
    simp only [containsBList]
    constructor
    · intro h; simp at h
    · rintro ⟨i, w, hw, _⟩; simp at hw
  case consL =>
    intro x xs ihx ihxs hwf t
    obtain ⟨hwfx, hwfxs⟩ := hwf
    simp only [containsBList, Bool.or_eq_true]
    rw [ihx hwfx t, ihxs hwfxs t]
    constructor
    · rintro (h | ⟨i, w, hw, hc⟩)
      · exact ⟨0, x, rfl, h⟩
      · exact ⟨i + 1, w, by simpa using hw, hc⟩
    · rintro ⟨i, w, hw, hc⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
        exact Or.inl (by rw [hw]; exact hc)
      | succ j => exact Or.inr ⟨j, w, by simpa using hw, hc⟩
  case nilD =>
    intro _ _ t
    simp only [containsBDis]
    constructor
    · intro h; simp at h
    · rintro ⟨q, w, hq, _⟩; simp [Attack.lookupDis] at hq
  case consD =>
    intro hd tl ih4 ihtl hnodup hwf t
    obtain ⟨q0, w0⟩ := hd
    rw [List.map_cons] at hnodup
    obtain ⟨hkey, hkeys⟩ := List.nodup_cons.mp hnodup
    obtain ⟨hwf0, hwftl⟩ := hwf
    simp only [containsBDis, Bool.or_eq_true]
    rw [ih4 hwf0 t, ihtl hkeys hwftl t]
    constructor
    · rintro (hc | ⟨q, w, hq, hc⟩)
      · exact ⟨q0, w0, by simp [Attack.lookupDis], hc⟩
      · refine ⟨q, w, ?_, hc⟩
        have hqne : q0 ≠ q := fun h => hkey (by rw [h]; exact lookupDis_some_mem hq)
        simp [Attack.lookupDis, hqne, hq]
    · rintro ⟨q, w, hq, hc⟩
      simp only [Attack.lookupDis] at hq
      by_cases hqq : q0 = q
      · rw [if_pos hqq, Option.some.injEq] at hq
        exact Or.inl (by rw [hq]; exact hc)
      · rw [if_neg hqq] at hq
        exact Or.inr ⟨q, w, hq, hc⟩
  case pair =>
    intro _ w ih
    exact ih

/-- **`attackClosureB` decides the closure test.** `attackClosureB k target`
holds iff some attacked occurrence of `k` is contained in `target`. Each attack
form threads `hwf` into `containsB_iff`. -/
theorem attackClosureB_iff {target : SupportTerm} (hwf : DisNodup target)
    (k : Attack.Attack) :
    attackClosureB k target = true ↔ ∃ t, AttackOcc k t ∧ Contains target t := by
  cases k with
  | rebut w u =>
    constructor
    · intro h
      simp only [attackClosureB] at h
      exact ⟨u, rfl, (containsB_iff hwf u).mp h⟩
    · rintro ⟨t, ht, hc⟩
      simp only [AttackOcc] at ht
      subst ht
      simp only [attackClosureB]
      exact (containsB_iff hwf t).mpr hc
  | undercut w u π =>
    constructor
    · intro h
      simp only [attackClosureB] at h
      revert h
      cases hs : Attack.subterm u π with
      | none => intro h; simp at h
      | some s => intro h; exact ⟨s, hs, (containsB_iff hwf s).mp h⟩
    · rintro ⟨t, ht, hc⟩
      simp only [AttackOcc] at ht
      simp only [attackClosureB]
      rw [ht]
      exact (containsB_iff hwf t).mpr hc
  | undermine w u π =>
    constructor
    · intro h
      simp only [attackClosureB] at h
      revert h
      cases hs : Attack.subterm u π with
      | none => intro h; simp at h
      | some s => intro h; exact ⟨s, hs, (containsB_iff hwf s).mp h⟩
    · rintro ⟨t, ht, hc⟩
      simp only [AttackOcc] at ht
      simp only [attackClosureB]
      rw [ht]
      exact (containsB_iff hwf t).mpr hc

/-! ### Conflict attackability and declared-edge coverage -/

/-- A support term can be the target of a conflict attack exactly when it is a
leaf or its root rule is known defeasible. In the checked-target context where
this predicate is used, the two cases correspond to undermining (the leaf is
declared in `Gamma`, so a contrary premise attacks it) and rebutting (a
contrary conclusion attacks the defeasible root). Positional undercuts are
governed separately — by the rule at the attacked positional subterm plus its
exception declaration (`Attack.undercut_pos_defeasible`) — and can land on a
target whose root is strict, so they are deliberately not modeled here. This
predicate deliberately says nothing about a particular source or attack
reason. -/
def ConflictAttackable
    (Pi : RuleId → Option Rule) : SupportTerm → Prop
  | .leaf _ => True
  | .inst rn _ _ _ _ _ =>
      ∃ r, Pi rn = some r ∧ r.mode = .defeasible

/-- Executable counterpart of `ConflictAttackable`. -/
def conflictAttackableB
    (Pi : RuleId → Option Rule) : SupportTerm → Bool
  | .leaf _ => true
  | .inst rn _ _ _ _ _ =>
      match Pi rn with
      | some r => decide (r.mode = .defeasible)
      | none => false

theorem conflictAttackableB_iff
    (Pi : RuleId → Option Rule) (target : SupportTerm) :
    conflictAttackableB Pi target = true ↔
      ConflictAttackable Pi target := by
  cases target with
  | leaf l => simp [conflictAttackableB, ConflictAttackable]
  | inst rn θ ws D H a =>
    cases h : Pi rn with
    | none => simp [conflictAttackableB, ConflictAttackable, h]
    | some r => simp [conflictAttackableB, ConflictAttackable, h]

/-- A declared attack covers a compiled edge when it has the requested source
and its attacked occurrence is contained in the requested target. Thus one
attack can cover both its direct target and any declared wrappers containing
that occurrence. -/
def Covered (atts : List Attack.Attack)
    (source target : SupportTerm) : Prop :=
  ∃ k ∈ atts, k.source = source ∧
    ∃ t, AttackOcc k t ∧ Contains target t

/-- Executable counterpart of `Covered`. -/
def coveredB (atts : List Attack.Attack)
    (source target : SupportTerm) : Bool :=
  atts.any (fun k =>
    decide (k.source = source) && attackClosureB k target)

theorem coveredB_iff {target : SupportTerm}
    (hwf : DisNodup target)
    (atts : List Attack.Attack) (source : SupportTerm) :
    coveredB atts source target = true ↔
      Covered atts source target := by
  constructor
  · intro h
    obtain ⟨k, hk, hcovered⟩ := List.any_eq_true.mp h
    rw [Bool.and_eq_true] at hcovered
    obtain ⟨hsource, hclosure⟩ := hcovered
    obtain ⟨t, hocc, hcontains⟩ :=
      (attackClosureB_iff hwf k).mp hclosure
    exact ⟨k, hk, of_decide_eq_true hsource, t, hocc, hcontains⟩
  · rintro ⟨k, hk, hsource, t, hocc, hcontains⟩
    rw [coveredB, List.any_eq_true]
    refine ⟨k, hk, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hsource,
      (attackClosureB_iff hwf k).mpr ⟨t, hocc, hcontains⟩⟩

/-- A well-formed source program at the compile boundary: the complete
arguments `Args(P)` with evidence they are complete checked support terms
(`O = ∅`, spec §8), the located holes `Holes(P)` (spec §4.4), and the compiled
attacks — the typed declared attacks whose source is complete — with evidence
they type (§7.1). Arguments and holes are both declared; only the complete
ones are AF nodes. Compilation is defined only downstream of the checker, so
the structure *is* the checker's postcondition. `nodup` models §8's `Args(P)`
being a set of terms. -/
structure CheckedProgram (canon : String → String) (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop)
    (dp : Attack.DefeatPolicy) where
  /-- the complete declared arguments, `Args(P)`: the AF nodes -/
  args : List SupportTerm
  /-- `Args(P)` is a set: no duplicate terms -/
  nodup : args.Nodup
  /-- every AF argument is a complete checked support term -/
  complete : ∀ w ∈ args, ∃ C, HasSupport canon Pi Gamma CertOk w C []
  /-- the compiled attacks: declared attacks whose source is in `args` -/
  atts : List Attack.Attack
  /-- every compiled attack types (§7.1) -/
  typed : ∀ k ∈ atts, Attack.HasAttack canon Pi Gamma CertOk dp k
  /-- every compiled attack source is a complete declared argument: an attack
  sourced at a hole is checked but contributes no edge (spec §4.4) -/
  source_declared : ∀ k ∈ atts, k.source ∈ args
  /-- located holes, `Holes(P)` (spec §4.4): typed declared arguments with a
  nonempty root obligation set. They are never AF nodes; they are kept so a
  compiled attack may name one as its target. -/
  holes : List SupportTerm
  /-- every compiled attack target is a complete declared argument or a hole;
  an attack on an occurrence inside a hole still reaches every complete
  argument containing that occurrence (spec §8) -/
  target_declared : ∀ k ∈ atts, k.target ∈ args ∨ k.target ∈ holes

/-- Exact checked metadata for one retained argument-cache entry. The public
program representation remains intentionally lean; callers that need indexed
conclusions retain this view from the checker's cache. -/
structure CheckedNode
    (canon : String → String) (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop) where
  term       : SupportTerm
  conclusion : Atom
  valid      : HasSupport canon Pi Gamma CertOk term conclusion []

/-- Exact checked metadata for one located hole (spec §4.4): its checked
declaration index, and the conclusion and nonempty mandatory root obligation
set the support stage cached for it. -/
structure CheckedHole
    (canon : String → String) (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop) where
  index       : Nat
  term        : SupportTerm
  conclusion  : Atom
  obligations : List QuestionId
  valid       : HasSupport canon Pi Gamma CertOk term conclusion obligations
  nonempty    : obligations ≠ []

/-- **The compiled attack relation (spec §8 `Attack(P)`, v0.1-frozen).**
`Edge P a b`: both endpoints are declared complete arguments, and some
declared attack has source `a` and an attacked occurrence contained in `b` —
ASPIC+ subargument closure. -/
def Edge (P : CheckedProgram canon Pi Gamma CertOk dp)
    (source target : SupportTerm) : Prop :=
  source ∈ P.args ∧ target ∈ P.args ∧
    Covered P.atts source target

/-- Every contrary conflict between complete declared arguments whose target
can be attacked at its root is represented by a compiled closure edge.  This
is a checker postcondition rather than a field of `CheckedProgram`: the
generic compile boundary remains usable by callers that establish only the
frozen structural invariants. -/
def AttackComplete
    (canon : String → String) (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop)
    (dp : Attack.DefeatPolicy)
    (args : List SupportTerm) (atts : List Attack.Attack) : Prop :=
  ∀ source, source ∈ args →
    ∀ target, target ∈ args →
    ∀ sourceConclusion targetConclusion,
      HasSupport canon Pi Gamma CertOk source sourceConclusion [] →
      HasSupport canon Pi Gamma CertOk target targetConclusion [] →
      Attack.ContraryMatch canon dp sourceConclusion targetConclusion →
      ConflictAttackable Pi target →
      Covered atts source target

/-- The edge consequence of an independently supplied attack-completeness
witness. -/
theorem complete_conflict_edge
    (P : CheckedProgram canon Pi Gamma CertOk dp)
    (hcomplete : AttackComplete canon Pi Gamma CertOk dp P.args P.atts)
    {source target : SupportTerm}
    (hsource : source ∈ P.args) (htarget : target ∈ P.args)
    {sourceConclusion targetConclusion : Atom}
    (hsourceConclusion :
      HasSupport canon Pi Gamma CertOk source sourceConclusion [])
    (htargetConclusion :
      HasSupport canon Pi Gamma CertOk target targetConclusion [])
    (hcontrary :
      Attack.ContraryMatch canon dp sourceConclusion targetConclusion)
    (hattackable : ConflictAttackable Pi target) :
    Edge P source target :=
  ⟨hsource, htarget,
    hcomplete source hsource target htarget sourceConclusion targetConclusion
      hsourceConclusion htargetConclusion hcontrary hattackable⟩

/-! ### Result 4: no untyped node or attack in the target AF -/

/-- **Result 4, node half.** Every AF node is a complete checked support term.
(This is the `complete` field, stated as the compile invariant.) -/
theorem compile_nodes_checked (P : CheckedProgram canon Pi Gamma CertOk dp) :
    ∀ w ∈ P.args, ∃ C, HasSupport canon Pi Gamma CertOk w C [] :=
  P.complete

/-- **Result 4, edge half.** An edge exists iff both endpoints are declared
complete arguments and a declared — and *typed* — attack sources it, with its
attacked occurrence contained in the head. Untyped attacks cannot produce
edges; closure introduces edges only onto arguments containing the attacked
occurrence. -/
theorem edge_iff (P : CheckedProgram canon Pi Gamma CertOk dp)
    (a b : SupportTerm) :
    Edge P a b ↔ a ∈ P.args ∧ b ∈ P.args ∧
      ∃ k ∈ P.atts, Attack.HasAttack canon Pi Gamma CertOk dp k ∧
        k.source = a ∧ ∃ t, AttackOcc k t ∧ Contains b t := by
  constructor
  · rintro ⟨ha, hb, k, hk, hsrc, t, hocc, hcont⟩
    exact ⟨ha, hb, k, hk, P.typed k hk, hsrc, t, hocc, hcont⟩
  · rintro ⟨ha, hb, k, hk, _, hsrc, t, hocc, hcont⟩
    exact ⟨ha, hb, k, hk, hsrc, t, hocc, hcont⟩

/-- Closure extends the direct attack: a declared attack whose source and
target are both declared arguments yields the direct edge source → target. -/
theorem closure_includes_direct (P : CheckedProgram canon Pi Gamma CertOk dp)
    {k : Attack.Attack} (hk : k ∈ P.atts) (htarget : k.target ∈ P.args)
    {t : SupportTerm} (hocc : AttackOcc k t) :
    Edge P k.source k.target :=
  ⟨P.source_declared k hk, htarget,
    k, hk, rfl, t, hocc, target_contains_occ hocc⟩

/-- A hole-free program has the pre-`lara-core@0.3` endpoint boundary: every
compiled attack target is a complete declared argument. -/
theorem CheckedProgram.target_declared_of_holes_nil
    (P : CheckedProgram canon Pi Gamma CertOk dp) (h : P.holes = []) :
    ∀ k ∈ P.atts, k.target ∈ P.args := by
  intro k hk
  rcases P.target_declared k hk with htarget | hhole
  · exact htarget
  · rw [h] at hhole
    cases hhole

/-- Only complete arguments emit edges: a term outside `Args(P)`, a hole in
particular, is the source of no edge. -/
theorem no_edge_of_not_arg (P : CheckedProgram canon Pi Gamma CertOk dp)
    {a : SupportTerm} (ha : a ∉ P.args) (b : SupportTerm) : ¬ Edge P a b :=
  fun hedge => ha hedge.1

/-- **D6, positive half.** A compiled attack whose attacked occurrence is
shared by a complete argument edges onto that argument, even when the
attack's declared target is a hole. -/
theorem closure_reaches_shared_occurrence
    (P : CheckedProgram canon Pi Gamma CertOk dp)
    {k : Attack.Attack} (hk : k ∈ P.atts) {t b : SupportTerm}
    (hocc : AttackOcc k t) (hb : b ∈ P.args) (hcontains : Contains b t) :
    Edge P k.source b :=
  ⟨P.source_declared k hk, hb, k, hk, rfl, t, hocc, hcontains⟩

/-- **D6, negative half.** An attack whose attacked occurrence is a hole — a
rebut of a hole's root in particular — covers no complete argument, so it adds
no edge even when its source is complete. -/
theorem hole_occurrence_reaches_no_arg
    (P : CheckedProgram canon Pi Gamma CertOk dp)
    {k : Attack.Attack} {t : SupportTerm} {Ct : Atom} {O : List QuestionId}
    (hocc : AttackOcc k t) (ht : HasSupport canon Pi Gamma CertOk t Ct O)
    (hO : O ≠ []) :
    ∀ b ∈ P.args, ∀ t', AttackOcc k t' → ¬ Contains b t' := by
  intro b hb t' hocc' hcontains
  rw [attackOcc_unique hocc' hocc] at hcontains
  obtain ⟨C, hC⟩ := P.complete b hb
  exact complete_not_contains_hole hC ht hO hcontains

/-! ### The bridge to the abstract grounded layer (N16)

`Lara/Grounded.lean` proved declarative ≡ executable grounded semantics over
an arbitrary abstract AF, where the earlier layer characterized `compile`
without exercising it. Here we exercise it: index the checked program's arguments by list position,
compile to a `Grounded.AF`, and show a source-level declarative judgment
defined over the Prop-level closure edges agrees with the abstract one —
first per argument, then lifted to four-state claim status. The bridge below
stays oracle-parametric (`Faithful`) by design; the checker-built
`edgeB`/`edgeB_faithful` instantiate it in the "Oracle-free
result-6 wrappers" section. -/

/-- The compiled abstract AF: arguments are indices into `P.args`; the edge
relation is the supplied oracle. -/
def toAF (P : CheckedProgram canon Pi Gamma CertOk dp)
    (edgeB : Nat → Nat → Bool) : Grounded.AF where
  args := List.range P.args.length
  attack := edgeB

/-- The oracle decides exactly the frozen `Edge` relation: `agrees` on
in-range indices, and (`ranged`) no edge touches an out-of-range index —
forced because `Edge` requires both endpoints declared. -/
structure Faithful (P : CheckedProgram canon Pi Gamma CertOk dp)
    (edgeB : Nat → Nat → Bool) : Prop where
  ranged : ∀ i j, edgeB i j = true → i < P.args.length ∧ j < P.args.length
  agrees : ∀ (i j : Nat) (a b : SupportTerm),
    P.args[i]? = some a → P.args[j]? = some b →
    (edgeB i j = true ↔ Edge P a b)

/-- **The checked-program edge decider.** Indexing the checked
program's arguments by list position, `edgeB P i j` decides `Edge P a b` for the
terms `a`/`b` at those positions: out-of-range on either side is no edge, and in
range it scans the declared attacks for one sourced at `a` whose attacked
occurrence is structurally contained in `b` (`attackClosureB`). -/
def edgeB (P : CheckedProgram canon Pi Gamma CertOk dp)
    (i j : Nat) : Bool :=
  match P.args[i]?, P.args[j]? with
  | some source, some target => coveredB P.atts source target
  | _, _ => false

/-- **`edgeB` decides `Edge` on declared endpoints.** With the source/target
terms pinned by their positions, the scan agrees with the `Edge` relation; the
`DisNodup` side-condition of `attackClosureB_iff` is discharged from the
checker's completeness invariant (`hasSupport_disNodup`). -/
theorem edgeB_iff {P : CheckedProgram canon Pi Gamma CertOk dp}
    {i j : Nat} {source target : SupportTerm}
    (hsource : P.args[i]? = some source)
    (htarget : P.args[j]? = some target) :
    edgeB P i j = true ↔ Edge P source target := by
  have hmem : target ∈ P.args := List.mem_of_getElem? htarget
  obtain ⟨C, hC⟩ := P.complete target hmem
  have hdn : DisNodup target := hasSupport_disNodup hC
  constructor
  · intro h
    unfold edgeB at h
    rw [hsource, htarget] at h
    exact ⟨List.mem_of_getElem? hsource, hmem,
      (coveredB_iff hdn P.atts source).mp h⟩
  · rintro ⟨_, _, hcovered⟩
    unfold edgeB
    rw [hsource, htarget]
    exact (coveredB_iff hdn P.atts source).mpr hcovered

/-- **`edgeB` is a faithful decider.** `ranged`: an edge forces the `some,some`
branch, so both positions are in range; `agrees` is `edgeB_iff` under the
position hypotheses. This constructively discharges the `Faithful` oracle. -/
theorem edgeB_faithful (P : CheckedProgram canon Pi Gamma CertOk dp) :
    Faithful P (edgeB P) := by
  refine ⟨?_, ?_⟩
  · intro i j h
    unfold edgeB at h
    cases hi : P.args[i]? with
    | none => rw [hi] at h; simp at h
    | some source =>
      cases hj : P.args[j]? with
      | none => rw [hi, hj] at h; simp at h
      | some target => exact ⟨lt_of_getElem?_some hi, lt_of_getElem?_some hj⟩
  · intro i j a b hi hj
    exact edgeB_iff hi hj

/- Source-level declarative grounded judgment, over the *Prop-level* closure
edges — never materializing the iteration or the Bool oracle. `SrcIn P i`:
argument `i` is in, because every closure-edge attacker is out; `SrcOut P j`:
some in argument's term edges to `j`'s term. The mirror of
`Grounded.DirectIn`/`DirectOut`, read off the source program. -/
mutual
  inductive SrcIn (P : CheckedProgram canon Pi Gamma CertOk dp) : Nat → Prop where
    | intro {i : Nat} {a : SupportTerm} (ha : P.args[i]? = some a)
        (h : ∀ (j : Nat) (b : SupportTerm), P.args[j]? = some b →
          Edge P b a → SrcOut P j) :
        SrcIn P i
  inductive SrcOut (P : CheckedProgram canon Pi Gamma CertOk dp) : Nat → Prop where
    | intro {j c : Nat} {cA bA : SupportTerm} (hc : SrcIn P c)
        (hcA : P.args[c]? = some cA) (hbA : P.args[j]? = some bA)
        (hE : Edge P cA bA) : SrcOut P j
end

mutual
  /-- Source-level in ⟹ abstract in over the compiled AF. -/
  theorem srcIn_direct {P : CheckedProgram canon Pi Gamma CertOk dp}
      {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) :
      ∀ {i : Nat}, SrcIn P i → Grounded.DirectIn (toAF P edgeB) i
    | _, .intro ha h =>
      Grounded.DirectIn.intro (List.mem_range.mpr (lt_of_getElem?_some ha))
        (fun j hj hatt => by
          obtain ⟨b, hb⟩ := getElem?_some_of_lt P.args j (List.mem_range.mp hj)
          exact srcOut_direct hf (h j b hb ((hf.agrees j _ b _ hb ha).mp hatt)))
  /-- Source-level out ⟹ abstract out over the compiled AF. -/
  theorem srcOut_direct {P : CheckedProgram canon Pi Gamma CertOk dp}
      {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) :
      ∀ {j : Nat}, SrcOut P j → Grounded.DirectOut (toAF P edgeB) j
    | _, .intro hc hcA hbA hE =>
      Grounded.DirectOut.intro (srcIn_direct hf hc)
        ((hf.agrees _ _ _ _ hcA hbA).mpr hE)
end

mutual
  /-- Abstract in over the compiled AF ⟹ source-level in. -/
  theorem direct_srcIn {P : CheckedProgram canon Pi Gamma CertOk dp}
      {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) :
      ∀ {i : Nat}, Grounded.DirectIn (toAF P edgeB) i → SrcIn P i
    | i, .intro ha h => by
      obtain ⟨a, haa⟩ := getElem?_some_of_lt P.args i (List.mem_range.mp ha)
      refine SrcIn.intro haa (fun j b hb hE => ?_)
      exact direct_srcOut hf
        (h j (List.mem_range.mpr (lt_of_getElem?_some hb))
          ((hf.agrees j i b a hb haa).mpr hE))
  /-- Abstract out over the compiled AF ⟹ source-level out. -/
  theorem direct_srcOut {P : CheckedProgram canon Pi Gamma CertOk dp}
      {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) :
      ∀ {j : Nat}, Grounded.DirectOut (toAF P edgeB) j → SrcOut P j
    | j, .intro hc hcb => by
      have hr := hf.ranged _ j hcb
      obtain ⟨cA, hcA⟩ := getElem?_some_of_lt P.args _ hr.1
      obtain ⟨bA, hbA⟩ := getElem?_some_of_lt P.args j hr.2
      exact SrcOut.intro (direct_srcIn hf hc) hcA hbA
        ((hf.agrees _ j cA bA hcA hbA).mp hcb)
end

/-- **The N16 bridge, argument level (spec §9 result 6, oracle-parametric).**
The source-level declarative judgment over the frozen closure-edge relation
agrees, argument by argument, with the abstract declarative grounded
semantics over the compiled AF. -/
theorem srcIn_iff_directIn {P : CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) (i : Nat) :
    SrcIn P i ↔ Grounded.DirectIn (toAF P edgeB) i :=
  ⟨srcIn_direct hf, direct_srcIn hf⟩

/-- The out-side companion. -/
theorem srcOut_iff_directOut {P : CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) (j : Nat) :
    SrcOut P j ↔ Grounded.DirectOut (toAF P edgeB) j :=
  ⟨srcOut_direct hf, direct_srcOut hf⟩

/-- Composition with the abstract layer: source-level in agrees with the
*executable* grounded extension over the compiled AF. -/
theorem srcIn_iff_grounded {P : CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) (i : Nat) :
    SrcIn P i ↔ i ∈ Grounded.grounded (toAF P edgeB) :=
  (srcIn_iff_directIn hf i).trans (Grounded.directIn_iff i)

/-! ### The N16 bridge, claim-status level -/

/-- **Source-level four-state claim status** (spec §8 priority order), read
from `SrcIn`/`SrcOut` alone — no AF, no iteration, no oracle. A relation
rather than a function because `SrcIn` is not decidable without the oracle;
`srcStatus_iff` shows it is total and functional under `Faithful` (it holds
iff the status is the deterministic `Grounded.statusC` result). -/
inductive SrcStatus (P : CheckedProgram canon Pi Gamma CertOk dp)
    (c : Grounded.Claim) : Grounded.Status → Prop where
  | gap (h : c.support = []) : SrcStatus P c .gap
  | justified (hne : c.support ≠ []) {i : Grounded.Arg}
      (hi : i ∈ c.support) (hin : SrcIn P i) : SrcStatus P c .justified
  | contested (hne : c.support ≠ [])
      (hnoin : ∀ i ∈ c.support, ¬ SrcIn P i) {i : Grounded.Arg}
      (hi : i ∈ c.support) (hout : ¬ SrcOut P i) : SrcStatus P c .contested
  | defeated (hne : c.support ≠ [])
      (hnoin : ∀ i ∈ c.support, ¬ SrcIn P i)
      (hallout : ∀ i ∈ c.support, SrcOut P i) : SrcStatus P c .defeated

/-- **The N16 bridge, claim-status level.** The source-level status relation
holds exactly at the executable compiled status: `SrcStatus P c
(Grounded.statusC (toAF P edgeB) c)`. With `srcIn_iff_grounded` this is
source-to-compiled status preservation, oracle-parametric — instantiated
oracle-free by the constructive `Faithful` from `edgeB_faithful`
in `srcStatus_checked`. -/
theorem srcStatus_correct {P : CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) (c : Grounded.Claim) :
    SrcStatus P c (Grounded.statusC (toAF P edgeB) c) := by
  by_cases hs : c.support = []
  · rw [Grounded.statusC, if_pos hs]
    exact SrcStatus.gap hs
  · rw [Grounded.statusC, if_neg hs]
    by_cases hin : ∃ i ∈ c.support, Grounded.DirectIn (toAF P edgeB) i
    · obtain ⟨i, hi, hdi⟩ := hin
      have hany : c.support.any
          (fun a => Grounded.labelC (toAF P edgeB) a == Grounded.Label.inn) = true := by
        rw [List.any_eq_true]
        exact ⟨i, hi, by
          rw [beq_iff_eq, Grounded.labelC_inn_iff]; exact hdi⟩
      rw [if_pos hany]
      exact SrcStatus.justified hs hi ((srcIn_iff_directIn hf i).mpr hdi)
    · have hnoin : ∀ i ∈ c.support, ¬ SrcIn P i := fun i hi hsi =>
        hin ⟨i, hi, (srcIn_iff_directIn hf i).mp hsi⟩
      have hnoin' : ∀ i ∈ c.support, ¬ Grounded.DirectIn (toAF P edgeB) i :=
        fun i hi hdi => hin ⟨i, hi, hdi⟩
      have hany1 : c.support.any
          (fun a => Grounded.labelC (toAF P edgeB) a == Grounded.Label.inn) = false := by
        rw [Bool.eq_false_iff]
        intro hc
        obtain ⟨i, hi, hbeq⟩ := List.any_eq_true.mp hc
        rw [beq_iff_eq, Grounded.labelC_inn_iff] at hbeq
        exact hnoin' i hi hbeq
      rw [hany1, if_neg (by simp)]
      by_cases hun : ∃ i ∈ c.support,
          ¬ Grounded.DirectIn (toAF P edgeB) i ∧ ¬ Grounded.DirectOut (toAF P edgeB) i
      · obtain ⟨i, hi, hni, hno⟩ := hun
        have hany2 : c.support.any
            (fun a => Grounded.labelC (toAF P edgeB) a == Grounded.Label.undec) = true := by
          rw [List.any_eq_true]
          exact ⟨i, hi, by
            rw [beq_iff_eq, Grounded.labelC_undec_iff]; exact ⟨hni, hno⟩⟩
        rw [if_pos hany2]
        exact SrcStatus.contested hs hnoin hi
          (fun hso => hno ((srcOut_iff_directOut hf i).mp hso))
      · have hany2 : c.support.any
            (fun a => Grounded.labelC (toAF P edgeB) a == Grounded.Label.undec) = false := by
          rw [Bool.eq_false_iff]
          intro hc
          obtain ⟨i, hi, hbeq⟩ := List.any_eq_true.mp hc
          rw [beq_iff_eq, Grounded.labelC_undec_iff] at hbeq
          exact hun ⟨i, hi, hbeq⟩
        rw [hany2, if_neg (by simp)]
        refine SrcStatus.defeated hs hnoin (fun i hi => ?_)
        have hni := hnoin' i hi
        have : ¬ (¬ Grounded.DirectIn (toAF P edgeB) i ∧
            ¬ Grounded.DirectOut (toAF P edgeB) i) := fun hh => hun ⟨i, hi, hh⟩
        have hdo : Grounded.DirectOut (toAF P edgeB) i := by
          by_cases hdo : Grounded.DirectOut (toAF P edgeB) i
          · exact hdo
          · exact absurd ⟨hni, hdo⟩ this
        exact (srcOut_iff_directOut hf i).mpr hdo

/-- Source status is functional even before supplying an executable edge
oracle: the four priority cases are mutually exclusive by construction. -/
theorem srcStatus_unique {P : CheckedProgram canon Pi Gamma CertOk dp}
    {c : Grounded.Claim} {s₁ s₂ : Grounded.Status}
    (h₁ : SrcStatus P c s₁) (h₂ : SrcStatus P c s₂) : s₁ = s₂ := by
  cases h₁ with
  | gap hgap =>
      cases h₂ with
      | gap => rfl
      | justified hne _ _ => exact False.elim (hne hgap)
      | contested hne _ _ _ => exact False.elim (hne hgap)
      | defeated hne _ _ => exact False.elim (hne hgap)
  | justified _ hi hin =>
      cases h₂ with
      | gap hgap => exact False.elim (by contradiction)
      | justified => rfl
      | contested _ hnoin _ _ => exact False.elim (hnoin _ hi hin)
      | defeated _ hnoin _ => exact False.elim (hnoin _ hi hin)
  | contested _ hnoin hi hout =>
      cases h₂ with
      | gap hgap => exact False.elim (by contradiction)
      | justified _ hi' hin => exact False.elim (hnoin _ hi' hin)
      | contested => rfl
      | defeated _ _ hallout => exact False.elim (hout (hallout _ hi))
  | defeated _ hnoin hallout =>
      cases h₂ with
      | gap hgap => exact False.elim (by contradiction)
      | justified _ hi hin => exact False.elim (hnoin _ hi hin)
      | contested _ _ hi hout => exact False.elim (hout (hallout _ hi))
      | defeated => rfl

/-- **Exact source-to-compiled status preservation.** Under a faithful
executable edge decider, a source status derivation exists exactly for the
single status returned by compiled grounded evaluation. -/
theorem srcStatus_iff {P : CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB)
    (c : Grounded.Claim) (s : Grounded.Status) :
    SrcStatus P c s ↔ s = Grounded.statusC (toAF P edgeB) c := by
  constructor
  · intro hs
    exact srcStatus_unique hs (srcStatus_correct hf c)
  · intro hs
    subst s
    exact srcStatus_correct hf c

/-! ### Oracle-free result-6 wrappers

The generic bridge above is parametric in an arbitrary `Faithful` decider. The
following instantiate it at the checker-built `edgeB P` / `edgeB_faithful P`, so
the `Faithful` oracle is supplied *constructively*: no caller manufactures it.
This discharges §9 result 6's source-vs-compiled half. -/

/-- The compiled AF built from the checker's own edge decider — the oracle-free
counterpart of `toAF P edgeB`. -/
def checkedAF (P : CheckedProgram canon Pi Gamma CertOk dp) : Grounded.AF :=
  toAF P (edgeB P)

/-- Oracle-free source-in preservation: source-level in agrees with the
executable grounded extension over `checkedAF P`. -/
theorem srcIn_iff_checkedGrounded
    (P : CheckedProgram canon Pi Gamma CertOk dp) (i : Nat) :
    SrcIn P i ↔ i ∈ Grounded.grounded (checkedAF P) :=
  srcIn_iff_grounded (edgeB_faithful P) i

/-- Oracle-free source-to-compiled status preservation: the source status
relation holds at the executable compiled status over `checkedAF P`. -/
theorem srcStatus_checked
    (P : CheckedProgram canon Pi Gamma CertOk dp) (c : Grounded.Claim) :
    SrcStatus P c (Grounded.statusC (checkedAF P) c) :=
  srcStatus_correct (edgeB_faithful P) c

/-- Oracle-free exact status preservation: a source status derivation exists
exactly for the single status returned by compiled grounded evaluation over
`checkedAF P`. -/
theorem srcStatus_iff_checked
    (P : CheckedProgram canon Pi Gamma CertOk dp) (c : Grounded.Claim)
    (s : Grounded.Status) :
    SrcStatus P c s ↔ s = Grounded.statusC (checkedAF P) c :=
  srcStatus_iff (edgeB_faithful P) c s

/-! ### Located holes do not move status

The compiled AF reads only `args` and the closure coverage of `atts` between
them; `holes` is diagnostic data. Two statements are kept apart: the AF of a
program is unchanged by its hole list alone, and, more generally, two programs
with the same complete arguments and the same complete-to-complete closure
coverage have the same AF and so every claim the same status. The second is
the form a source edit can use; it is not unconditional, because an attack
onto an occurrence inside a hole may still cover a complete argument (D6). -/

/-- Equal complete arguments and equal complete-to-complete closure coverage
give the same checked AF. The two programs may differ in their holes, their
attacks sourced at or aimed at holes, and their typing contexts. -/
theorem checkedAF_eq_of_coverage
    {canon' : String → String} {Pi' : RuleId → Option Rule}
    {Gamma' : LeafId → Option Atom}
    {CertOk' : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {dp' : Attack.DefeatPolicy}
    (P : CheckedProgram canon Pi Gamma CertOk dp)
    (Q : CheckedProgram canon' Pi' Gamma' CertOk' dp')
    (hargs : P.args = Q.args)
    (hcoverage : ∀ a ∈ P.args, ∀ b ∈ P.args,
      Covered P.atts a b ↔ Covered Q.atts a b) :
    checkedAF P = checkedAF Q := by
  have hedge : ∀ i j, edgeB P i j = edgeB Q i j := by
    intro i j
    unfold edgeB
    rw [← hargs]
    cases hi : P.args[i]? with
    | none => rfl
    | some a =>
      cases hj : P.args[j]? with
      | none => rfl
      | some b =>
        have ha := List.mem_of_getElem? hi
        have hb := List.mem_of_getElem? hj
        obtain ⟨C, hC⟩ := P.complete b hb
        obtain ⟨C', hC'⟩ := Q.complete b (hargs ▸ hb)
        apply Bool.eq_iff_iff.mpr
        rw [coveredB_iff (hasSupport_disNodup hC),
          coveredB_iff (hasSupport_disNodup hC')]
        exact hcoverage a ha b hb
  unfold checkedAF toAF
  rw [hargs]
  congr 1
  funext i j
  exact hedge i j

/-- **Status is independent of holes.** Under equal complete arguments and
equal complete-to-complete closure coverage, every claim has the same compiled
status. -/
theorem status_independent_of_holes
    {canon' : String → String} {Pi' : RuleId → Option Rule}
    {Gamma' : LeafId → Option Atom}
    {CertOk' : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {dp' : Attack.DefeatPolicy}
    (P : CheckedProgram canon Pi Gamma CertOk dp)
    (Q : CheckedProgram canon' Pi' Gamma' CertOk' dp')
    (hargs : P.args = Q.args)
    (hcoverage : ∀ a ∈ P.args, ∀ b ∈ P.args,
      Covered P.atts a b ↔ Covered Q.atts a b)
    (c : Grounded.Claim) :
    Grounded.statusC (checkedAF P) c = Grounded.statusC (checkedAF Q) c := by
  rw [checkedAF_eq_of_coverage P Q hargs hcoverage]

/-- **Diagnostic-only holes independence.** Programs that differ only in their
recorded holes compile to the same AF. -/
theorem checkedAF_independent_of_holes
    (P Q : CheckedProgram canon Pi Gamma CertOk dp)
    (hargs : P.args = Q.args) (hatts : P.atts = Q.atts) :
    checkedAF P = checkedAF Q :=
  checkedAF_eq_of_coverage P Q hargs (fun a _ b _ => by rw [hatts])

end Lara.Compile
