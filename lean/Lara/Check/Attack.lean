/- Executable positional attack checking and its exact adequacy certificate. -/

import Lara.Check.SupportProof

namespace Lara.Check

open Lara Lara.Support Lara.Attack

def exceptionMatchB (canon : String → String) (dp : DefeatPolicy)
    (rn : RuleId) (θ : Subst) (source : Atom) : Bool :=
  dp.exceptions.any (fun entry =>
    decide (entry.1 = rn) &&
      match instAPat θ entry.2 with
      | none => false
      | some e => decide (equiv canon source e))

theorem exceptionMatchB_iff (canon : String → String) (dp : DefeatPolicy)
    (rn : RuleId) (θ : Subst) (source : Atom) :
    exceptionMatchB canon dp rn θ source = true ↔
      ∃ E, (rn, E) ∈ dp.exceptions ∧
        ∃ e, instAPat θ E = some e ∧ equiv canon source e := by
  simp only [exceptionMatchB, List.any_eq_true]
  constructor
  · rintro ⟨entry, hentry, hm⟩
    rcases entry with ⟨rn', E⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    rcases hm with ⟨hrn, hm⟩
    subst rn'
    cases hi : instAPat θ E with
    | none => simp [hi] at hm
    | some e =>
        simp [hi] at hm
        exact ⟨E, hentry, e, hi, hm⟩
  · rintro ⟨E, hentry, e, hi, heq⟩
    refine ⟨(rn, E), hentry, ?_⟩
    simp [hi, heq]

private def exceptionFailure (canon : String → String) (rn : RuleId)
    (θ : Subst) (source : Atom) (pos : Pos) :
    List (RuleId × APat) → Option AttackRelationReason → Except CheckError Unit
  | [], none => .error (.R11 .root pos .undercut (.missingException rn))
  | [], some reason => .error (.R11 .root pos .undercut reason)
  | (rn', E) :: rest, prior =>
      if rn' = rn then
        match instAPat θ E with
        | none =>
            exceptionFailure canon rn θ source pos rest
              (match prior with
              | some reason => some reason
              | none => some (.exceptionInstantiation rn E))
        | some e =>
            if equiv canon source e then .ok ()
            else exceptionFailure canon rn θ source pos rest
              (match prior with
              | some reason => some reason
              | none => some (.exceptionMismatch rn source e))
      else exceptionFailure canon rn θ source pos rest prior

private theorem exceptionFailure_ok_iff (canon : String → String)
    (rn : RuleId) (θ : Subst) (source : Atom)
    (pos : Pos) (xs : List (RuleId × APat))
    (prior : Option AttackRelationReason) :
    exceptionFailure canon rn θ source pos xs prior = .ok () ↔
      ∃ E, (rn, E) ∈ xs ∧
        ∃ e, instAPat θ E = some e ∧ equiv canon source e := by
  induction xs generalizing prior with
  | nil => cases prior <;> simp [exceptionFailure]
  | cons entry xs ih =>
      rcases entry with ⟨rn', E⟩
      by_cases hrn : rn' = rn
      · subst rn'
        cases hi : instAPat θ E with
        | none =>
            simp [exceptionFailure, hi, ih]
        | some e =>
            by_cases heq : equiv canon source e
            · simp [exceptionFailure, hi, heq]
            · simp [exceptionFailure, hi, heq, ih]
      · simp [exceptionFailure, hrn, Ne.symm hrn, ih]

private def checkAttackTarget (canon : String → String)
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (dp : DefeatPolicy) (k : Attack) (sourceConclusion : Atom) :
    Except CheckError Unit :=
  match k with
  | .rebut _ target =>
      match target with
      | .leaf _ =>
          .error (.R10 .root [] .rebut
            (.wrongOccurrenceKind .rule .leaf))
      | .inst rn θ _ _ _ _ =>
          match Pi rn with
          | none =>
              .error (.R11 .root [] .rebut (.missingTargetRule rn))
          | some r =>
              if r.mode = .defeasible then
                match instAPat θ r.concl with
                | none => .error (.R11 .root [] .rebut
                    (.targetConclusionInstantiation rn r.concl))
                | some targetConclusion =>
                    if contraryMatchB canon dp sourceConclusion targetConclusion
                    then .ok ()
                    else .error (.R11 .root [] .rebut
                      (.missingContrary sourceConclusion targetConclusion))
              else .error (.R11 .root [] .rebut (.strictTarget rn))
  | .undercut _ target pos =>
      match subterm target pos with
      | none => .error (.R10 .root pos .undercut .undefinedPosition)
      | some (.leaf _) =>
          .error (.R10 .root pos .undercut
            (.wrongOccurrenceKind .rule .leaf))
      | some (.inst rn θ _ _ _ _) =>
          match Pi rn with
          | none =>
              .error (.R11 .root pos .undercut (.missingTargetRule rn))
          | some r =>
              if r.mode = .defeasible then
                exceptionFailure canon rn θ sourceConclusion pos
                  dp.exceptions none
              else .error (.R11 .root pos .undercut (.strictTarget rn))
  | .undermine _ target pos =>
      match subterm target pos with
      | none => .error (.R10 .root pos .undermine .undefinedPosition)
      | some (.inst _ _ _ _ _ _) =>
          .error (.R10 .root pos .undermine
            (.wrongOccurrenceKind .leaf .rule))
      | some (.leaf l) =>
          match Gamma l with
          | none =>
              .error (.R11 .root pos .undermine (.missingTargetLeaf l))
          | some targetConclusion =>
              if contraryMatchB canon dp sourceConclusion targetConclusion
              then .ok ()
              else .error (.R11 .root pos .undermine
                (.missingContrary sourceConclusion targetConclusion))

private def checkAttackTargetChecked {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} (dp : DefeatPolicy) (k : Attack)
    (source : SupportResult)
    (_valid : HasSupport canon Pi Gamma (certOkOf reg) k.source
      source.conclusion source.obligations) : Except CheckError Unit :=
  checkAttackTarget canon Pi Gamma dp k source.conclusion

def checkAttackWithSource {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} (dp : DefeatPolicy)
    (k : Attack) (source : CheckedSupport canon Pi Gamma reg)
    (hsource : source.term = k.source) : Except CheckError Unit :=
  checkAttackTargetChecked dp k source.result (hsource ▸ source.valid)

def checkAttack {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (dp : DefeatPolicy)
    (k : Attack) : Except CheckError Unit :=
  match h : inferSupport Pi Gamma reg .root k.source with
  | .error e => .error e
  | .ok result =>
      checkAttackWithSource dp k
        ⟨k.source, result, inferSupport_sound h⟩ rfl

theorem checkAttackTarget_iff (canon : String → String)
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (dp : DefeatPolicy) (k : Attack) (Cw : Atom) :
    checkAttackTarget canon Pi Gamma dp k Cw = .ok () ↔
      match k with
      | .rebut _ (.inst rn θ _ _ _ _) =>
          ∃ r Cu, Pi rn = some r ∧ r.mode = .defeasible ∧
            instAPat θ r.concl = some Cu ∧ ContraryMatch canon dp Cw Cu
      | .rebut _ (.leaf _) => False
      | .undercut _ u pos =>
          ∃ rn θ ws D H a r E e,
            subterm u pos = some (.inst rn θ ws D H a) ∧
            Pi rn = some r ∧ r.mode = .defeasible ∧
            (rn, E) ∈ dp.exceptions ∧ instAPat θ E = some e ∧
            equiv canon Cw e
      | .undermine _ u pos =>
          ∃ l pl, subterm u pos = some (.leaf l) ∧
            Gamma l = some pl ∧ ContraryMatch canon dp Cw pl := by
  cases k with
  | rebut w target =>
      cases target with
      | leaf l => simp [checkAttackTarget]
      | inst rn θ ws D H a =>
          simp only [checkAttackTarget]
          cases hr : Pi rn with
          | none => simp
          | some r =>
              by_cases hd : r.mode = .defeasible
              · cases hi : instAPat θ r.concl with
                | none => simp [hd, hi]
                | some Cu =>
                    simp [hd, hi, contraryMatchB_iff]
              · simp [hd]
  | undercut w u pos =>
      cases ho : subterm u pos with
      | none => simp [checkAttackTarget, ho]
      | some occ =>
          cases occ with
          | leaf l => simp [checkAttackTarget, ho]
          | inst rn θ ws D H a =>
              cases hr : Pi rn with
              | none => simp [checkAttackTarget, ho, hr]
              | some r =>
                  by_cases hd : r.mode = .defeasible
                  · simp only [checkAttackTarget, ho, hr, hd, if_pos,
                      exceptionFailure_ok_iff]
                    constructor
                    · rintro ⟨E, he, e, hi, heq⟩
                      exact ⟨rn, θ, ws, D, H, a, r, E, e,
                        rfl, hr, hd, he, hi, heq⟩
                    · rintro ⟨rn', θ', ws', D', H', a', r', E, e,
                        hocc, hr', hd', he, hi, heq⟩
                      have hinj := Option.some.inj hocc
                      injection hinj with hrn hθ hws hD hH ha
                      subst rn'
                      subst θ'
                      have hrr : r' = r := Option.some.inj (hr'.symm.trans hr)
                      subst r'
                      exact ⟨E, he, e, hi, heq⟩
                  · simp [checkAttackTarget, ho, hr, hd]
  | undermine w u pos =>
      cases ho : subterm u pos with
      | none => simp [checkAttackTarget, ho]
      | some occ =>
          cases occ with
          | inst rn θ ws D H a => simp [checkAttackTarget, ho]
          | leaf l =>
              cases hl : Gamma l with
              | none => simp [checkAttackTarget, ho, hl]
              | some pl =>
                  simp [checkAttackTarget, contraryMatchB_iff, ho, hl]

theorem checkAttackWithSource_sound {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {k : Attack} {source : CheckedSupport canon Pi Gamma reg}
    (hsource : source.term = k.source)
    (h : checkAttackWithSource dp k source hsource = .ok ()) :
    HasAttack canon Pi Gamma (certOkOf reg) dp k := by
  have hw : HasSupport canon Pi Gamma (certOkOf reg) k.source
      source.result.conclusion source.result.obligations := by
    rw [← hsource]
    exact source.valid
  have ht := (checkAttackTarget_iff canon Pi Gamma dp k
    source.result.conclusion).mp h
  cases k with
  | rebut w target =>
      cases target with
      | leaf l => contradiction
      | inst rn θ ws D H a =>
          rcases ht with ⟨r, Cu, hr, hd, hi, hc⟩
          exact .rebut hw hr hd hi hc
  | undercut w u pos =>
      rcases ht with ⟨rn, θ, ws, D, H, a, r, E, e,
        ho, hr, hd, he, hi, heq⟩
      exact .undercut hw ho hr hd he hi heq
  | undermine w u pos =>
      rcases ht with ⟨l, pl, ho, hl, hc⟩
      exact .undermine hw ho hl hc

theorem checkAttackWithSource_complete {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {k : Attack} {source : CheckedSupport canon Pi Gamma reg}
    (hsource : source.term = k.source)
    (hk : HasAttack canon Pi Gamma (certOkOf reg) dp k) :
    checkAttackWithSource dp k source hsource = .ok () := by
  have hs : HasSupport canon Pi Gamma (certOkOf reg) k.source
      source.result.conclusion source.result.obligations := by
    rw [← hsource]
    exact source.valid
  apply (checkAttackTarget_iff canon Pi Gamma dp k
    source.result.conclusion).mpr
  cases hk with
  | @rebut w rn θ ws D H a r Cw Cu Ow hw hr hd hi hc =>
      have hC : Cw = source.result.conclusion :=
        (hasSupport_unique hw hs).1
      subst Cw
      exact ⟨r, Cu, hr, hd, hi, hc⟩
  | @undercut w u pos rn θ ws D H a r E e Cw Ow
      hw ho hr hd he hi heq =>
      have hC : Cw = source.result.conclusion :=
        (hasSupport_unique hw hs).1
      subst Cw
      exact ⟨rn, θ, ws, D, H, a, r, E, e,
        ho, hr, hd, he, hi, heq⟩
  | @undermine w u pos l pl Cw Ow hw ho hl hc =>
      have hC : Cw = source.result.conclusion :=
        (hasSupport_unique hw hs).1
      subst Cw
      exact ⟨l, pl, ho, hl, hc⟩

theorem checkAttack_sound {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy} {k : Attack}
    (h : checkAttack Pi Gamma reg dp k = .ok ()) :
    HasAttack canon Pi Gamma (certOkOf reg) dp k := by
  unfold checkAttack at h
  split at h
  · contradiction
  · exact checkAttackWithSource_sound rfl h

theorem checkAttack_complete {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy} {k : Attack}
    (hk : HasAttack canon Pi Gamma (certOkOf reg) dp k) :
    checkAttack Pi Gamma reg dp k = .ok () := by
  rcases attack_source_checked hk with ⟨C, O, hw⟩
  unfold checkAttack
  split
  · rename_i e hi
    have expected := inferSupport_complete hw .root
    rw [expected] at hi
    contradiction
  · exact checkAttackWithSource_complete rfl hk

end Lara.Check
