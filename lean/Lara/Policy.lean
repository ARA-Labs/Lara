/-
Executable policy well-formedness (`Lara.Policy`) — the Lean port of the
v0.1-frozen §8.1 Path-B restriction.

The strict-reachable patterns are exactly the conclusions of strict rules.
This is also the least set described by the spec: it contains every strict
conclusion, and following any positive-length chain of strict
premises-to-conclusion steps ends at the conclusion of a strict rule.

`wfB` decides `WellFormed`: no strict-reachable conclusion pattern can overlap
at the instance level with either side of a declared `contrary` pair.
`firstViolation?` is the located R12 diagnostic payload, retaining both the
offending rule id and contrary pair.

This file intentionally stops at the validator boundary. The rest of spec §9
result 7 (two contrary claims cannot both be justified) additionally needs an
attack-completeness invariant: the current `CheckedProgram.typed` field proves
that every declared attack is well typed, but not that every rebuttable
conflict is represented by a declared/compiled edge.
-/

import Lara.Attack

namespace Lara.Policy

open Lara.Support

/-- A finite policy rule declaration. The finite list is the decode-boundary
representation needed by the executable validator; downstream typing still
uses the derived `RuleId → Option Rule` lookup. -/
structure RuleDecl where
  id   : RuleId
  rule : Rule

/-- The policy material needed by the §8.1 validator. -/
structure Policy where
  rules  : List RuleDecl
  defeat : Attack.DefeatPolicy

/-- A pattern is strict-reachable iff it is the conclusion of a declared
strict rule. This is the finite presentation of the spec's least set. -/
inductive StrictReachable (P : Policy) : APat → Prop where
  | conclusion {d : RuleDecl}
      (hdecl : d ∈ P.rules) (hstrict : d.rule.mode = .strict) :
      StrictReachable P d.rule.concl

/-- The least set is closed under a strict premises-to-conclusion step. The
premise reachability hypothesis records the chain reading; membership follows
because the endpoint is itself a strict-rule conclusion. -/
theorem strictReachable_closed (P : Policy) {d : RuleDecl}
    (hdecl : d ∈ P.rules) (hstrict : d.rule.mode = .strict)
    (_ : ∀ p ∈ d.rule.premises, StrictReachable P p) :
    StrictReachable P d.rule.concl :=
  .conclusion hdecl hstrict

/-- The finite list used by the executable check. -/
def strictConclusions (P : Policy) : List APat :=
  (P.rules.filter (fun d => d.rule.mode == .strict)).map (·.rule.concl)

/-- The list implementation denotes exactly the relational least set. -/
theorem strictReachable_iff_mem {P : Policy} {p : APat} :
    StrictReachable P p ↔ p ∈ strictConclusions P := by
  constructor
  · intro h
    cases h with
    | conclusion hdecl hstrict =>
        apply List.mem_map.mpr
        exact ⟨_, List.mem_filter.mpr ⟨hdecl, by simp [hstrict]⟩, rfl⟩
  · intro h
    simp only [strictConclusions, List.mem_map, List.mem_filter] at h
    obtain ⟨d, ⟨hdecl, hstrict⟩, hp⟩ := h
    subst p
    exact .conclusion hdecl (by simpa using hstrict)

/-! ### Conservative instance-overlap check

Variables from a rule and a contrary declaration have independent scopes.
Consequently literal pattern equality is too weak here: `CanFly(X)` overlaps
`CanFly(tweety)` even though the two syntax trees differ.

The executable relation below is a conservative structural unifiability check.
Variables are wildcards, literals are compared after normalization, and
constructor/predicate symbols and arities must agree. It deliberately ignores
repeated-variable equality constraints, so it can reject a safe policy but
cannot accept two patterns having canonically equivalent ground instances.
That one-sided guarantee is the direction required by Path B. -/

mutual
  def patMayOverlap (canon : String → String) : Pat → Pat → Bool
    | .var _, _ => true
    | _, .var _ => true
    | .num a, .num b => canon a == canon b
    | .str a, .str b => a == b
    | .con k ps, .con l qs => k == l && patsMayOverlap canon ps qs
    | _, _ => false
  def patsMayOverlap (canon : String → String) : Pats → Pats → Bool
    | .nil, .nil => true
    | .cons p ps, .cons q qs =>
        patMayOverlap canon p q && patsMayOverlap canon ps qs
    | _, _ => false
end

def aPatMayOverlap (canon : String → String) (p q : APat) : Bool :=
  p.pred == q.pred && patsMayOverlap canon p.args q.args

/- Canonically equivalent ground instances imply a positive pattern-overlap
check. This is the soundness direction needed by the policy validator; the
converse is intentionally absent because repeated-variable constraints are
conservatively approximated. -/
mutual
  theorem patMayOverlap_of_instances {canon : String → String}
      {θ₁ θ₂ : Subst} {p q : Pat} {a b : Term}
      (hpa : instPat θ₁ p = some a) (hqb : instPat θ₂ q = some b)
      (heq : nfTerm canon a = nfTerm canon b) :
      patMayOverlap canon p q = true := by
    exact match p, q with
    | .var _, _ => by simp [patMayOverlap]
    | .num _, .var _
    | .str _, .var _
    | .con _ _, .var _ => by rfl
    | .num x, .num y => by
        simp only [instPat, Option.some.injEq] at hpa hqb
        subst a
        subst b
        simpa [patMayOverlap, nfTerm] using heq
    | .str x, .str y => by
        simp only [instPat, Option.some.injEq] at hpa hqb
        subst a
        subst b
        simpa [patMayOverlap, nfTerm] using heq
    | .con k ps, .con l qs => by
        simp only [instPat] at hpa hqb
        cases hps : instPats θ₁ ps <;> simp [hps] at hpa
        cases hqs : instPats θ₂ qs <;> simp [hqs] at hqb
        subst a
        subst b
        simp only [nfTerm, Term.con.injEq] at heq
        simp only [patMayOverlap, Bool.and_eq_true]
        exact ⟨by
          cases k
          cases l
          simpa using heq.1,
          patsMayOverlap_of_instances hps hqs heq.2⟩
    | .num _, .str _ => by
        simp only [instPat, Option.some.injEq] at hpa hqb
        subst a
        subst b
        simp [nfTerm] at heq
    | .str _, .num _ => by
        simp only [instPat, Option.some.injEq] at hpa hqb
        subst a
        subst b
        simp [nfTerm] at heq
    | .num _, .con _ qs => by
        simp only [instPat, Option.some.injEq] at hpa
        simp only [instPat] at hqb
        cases hqs : instPats θ₂ qs <;> simp [hqs] at hqb
        subst a
        subst b
        simp [nfTerm] at heq
    | .str _, .con _ qs => by
        simp only [instPat, Option.some.injEq] at hpa
        simp only [instPat] at hqb
        cases hqs : instPats θ₂ qs <;> simp [hqs] at hqb
        subst a
        subst b
        simp [nfTerm] at heq
    | .con _ ps, .num _ => by
        simp only [instPat] at hpa
        simp only [instPat, Option.some.injEq] at hqb
        cases hps : instPats θ₁ ps <;> simp [hps] at hpa
        subst a
        subst b
        simp [nfTerm] at heq
    | .con _ ps, .str _ => by
        simp only [instPat] at hpa
        simp only [instPat, Option.some.injEq] at hqb
        cases hps : instPats θ₁ ps <;> simp [hps] at hpa
        subst a
        subst b
        simp [nfTerm] at heq

  theorem patsMayOverlap_of_instances {canon : String → String}
      {θ₁ θ₂ : Subst} {ps qs : Pats} {as bs : Terms}
      (hps : instPats θ₁ ps = some as) (hqs : instPats θ₂ qs = some bs)
      (heq : nfTerms canon as = nfTerms canon bs) :
      patsMayOverlap canon ps qs = true := by
    exact match ps, qs with
    | .nil, .nil => rfl
    | .cons p ps, .cons q qs => by
        simp only [instPats] at hps hqs
        cases hp : instPat θ₁ p <;>
          cases hps' : instPats θ₁ ps <;> simp [hp, hps'] at hps
        cases hq : instPat θ₂ q <;>
          cases hqs' : instPats θ₂ qs <;> simp [hq, hqs'] at hqs
        subst as
        subst bs
        simp only [nfTerms, Terms.cons.injEq] at heq
        simp only [patsMayOverlap, Bool.and_eq_true]
        exact ⟨patMayOverlap_of_instances hp hq heq.1,
          patsMayOverlap_of_instances hps' hqs' heq.2⟩
    | .nil, .cons q qs => by
        simp only [instPats, Option.some.injEq] at hps
        simp only [instPats] at hqs
        cases hq : instPat θ₂ q <;>
          cases hqs' : instPats θ₂ qs <;> simp [hq, hqs'] at hqs
        subst as
        subst bs
        simp [nfTerms] at heq
    | .cons p ps, .nil => by
        simp only [instPats] at hps
        simp only [instPats, Option.some.injEq] at hqs
        cases hp : instPat θ₁ p <;>
          cases hps' : instPats θ₁ ps <;> simp [hp, hps'] at hps
        subst as
        subst bs
        simp [nfTerms] at heq
end

theorem aPatMayOverlap_of_instances {canon : String → String}
    {θ₁ θ₂ : Subst} {p q : APat} {a b : Atom}
    (hpa : instAPat θ₁ p = some a) (hqb : instAPat θ₂ q = some b)
    (heq : equiv canon a b) :
    aPatMayOverlap canon p q = true := by
  cases p with
  | mk pp ps =>
      cases q with
      | mk qp qs =>
          simp only [instAPat] at hpa hqb
          cases hps : instPats θ₁ ps <;> simp [hps] at hpa
          cases hqs : instPats θ₂ qs <;> simp [hqs] at hqb
          subst a
          subst b
          simp only [equiv, nf, Atom.atom.injEq] at heq
          simp only [aPatMayOverlap, Bool.and_eq_true]
          exact ⟨by
            cases pp
            cases qp
            simpa using heq.1,
            patsMayOverlap_of_instances hps hqs heq.2⟩

/-- A contrary pair is safe for a strict-reachable pattern when neither side
can share a canonically equivalent ground instance with it. -/
def safePair (canon : String → String) (p : APat)
    (ab : APat × APat) : Bool :=
  !aPatMayOverlap canon p ab.1 && !aPatMayOverlap canon p ab.2

/-- Executable `wf(Pi)` check. -/
def wfB (canon : String → String) (P : Policy) : Bool :=
  (strictConclusions P).all fun p =>
    P.defeat.contraries.all (safePair canon p)

/-- The declarative policy-well-formedness judgment decided by `wfB`. -/
def WellFormed (canon : String → String) (P : Policy) : Prop :=
  ∀ p, StrictReachable P p →
    ∀ ab ∈ P.defeat.contraries,
      aPatMayOverlap canon p ab.1 = false ∧
      aPatMayOverlap canon p ab.2 = false

/-- `wfB` is sound and complete for the §8.1 judgment. -/
theorem wfB_iff {canon : String → String} {P : Policy} :
    wfB canon P = true ↔ WellFormed canon P := by
  simp only [wfB, List.all_eq_true, safePair, Bool.and_eq_true]
  constructor
  · intro h p hp ab hab
    simpa using h p (strictReachable_iff_mem.mp hp) ab hab
  · intro h p hp ab hab
    simpa using h p (strictReachable_iff_mem.mpr hp) ab hab

/-- A well-formed policy cannot register an instantiated contrary whose first
side is canonically equivalent to an instance of a strict conclusion. -/
theorem wellFormed_no_strict_contrary_left
    {canon : String → String} {P : Policy} {p : APat}
    {θ : Subst} {a b : Atom}
    (hw : WellFormed canon P) (hr : StrictReachable P p)
    (hinst : instAPat θ p = some a) :
    ¬ Attack.ContraryMatch canon P.defeat a b := by
  intro hc
  obtain ⟨ab, hab, ρ, pa, pb, hpa, _, heqa, _⟩ := hc
  have hover : aPatMayOverlap canon p ab.1 = true :=
    aPatMayOverlap_of_instances hinst hpa (equiv_symm canon heqa)
  have hsafe : aPatMayOverlap canon p ab.1 = false :=
    (hw p hr ab hab).1
  exact Bool.noConfusion (hsafe.symm.trans hover)

/-- Symmetric boundary theorem for a strict conclusion occurring on the second
side of an instantiated contrary declaration. -/
theorem wellFormed_no_strict_contrary_right
    {canon : String → String} {P : Policy} {p : APat}
    {θ : Subst} {a b : Atom}
    (hw : WellFormed canon P) (hr : StrictReachable P p)
    (hinst : instAPat θ p = some a) :
    ¬ Attack.ContraryMatch canon P.defeat b a := by
  intro hc
  obtain ⟨ab, hab, ρ, pa, pb, _, hpb, _, heqa⟩ := hc
  have hover : aPatMayOverlap canon p ab.2 = true :=
    aPatMayOverlap_of_instances hinst hpb (equiv_symm canon heqa)
  have hsafe : aPatMayOverlap canon p ab.2 = false :=
    (hw p hr ab hab).2
  exact Bool.noConfusion (hsafe.symm.trans hover)

/-- The frozen judgment is decidable by computation, not classical search. -/
def decideWellFormed (canon : String → String) (P : Policy) :
    Decidable (WellFormed canon P) :=
  if h : wfB canon P = true then
    isTrue (wfB_iff.mp h)
  else
    isFalse (fun hw => h (wfB_iff.mpr hw))

/-- Located R12 payload. -/
structure Violation where
  ruleId    : RuleId
  consequent : APat
  contrary  : APat × APat

def touchingPair? (canon : String → String) (p : APat) :
    List (APat × APat) → Option (APat × APat)
  | [] => none
  | ab :: rest =>
      if aPatMayOverlap canon p ab.1 || aPatMayOverlap canon p ab.2 then
        some ab
      else
        touchingPair? canon p rest

def firstViolationIn? (canon : String → String)
    (contraries : List (APat × APat)) :
    List RuleDecl → Option Violation
  | [] => none
  | d :: rest =>
      if d.rule.mode = .strict then
        match touchingPair? canon d.rule.concl contraries with
        | some ab => some ⟨d.id, d.rule.concl, ab⟩
        | none => firstViolationIn? canon contraries rest
      else
        firstViolationIn? canon contraries rest

/-- The first located offending rule/contrary pair, if any. -/
def firstViolation? (canon : String → String) (P : Policy) :
    Option Violation :=
  firstViolationIn? canon P.defeat.contraries P.rules

/-! ### Regression: instance overlap without syntactic pattern equality -/

namespace Regression

def x : VarId := ⟨"x"⟩
def tweety : Pat := .con ⟨"tweety"⟩ .nil
def tweetyTerm : Term := .con "tweety" .nil
def birdX : APat := ⟨⟨"Bird"⟩, .cons (.var x) .nil⟩
def canFlyX : APat := ⟨⟨"CanFly"⟩, .cons (.var x) .nil⟩
def canFlyTweety : APat := ⟨⟨"CanFly"⟩, .cons tweety .nil⟩
def penguinTweety : APat := ⟨⟨"Penguin"⟩, .cons tweety .nil⟩
def canFlyTweetyAtom : Atom := .atom "CanFly" (.cons tweetyTerm .nil)
def penguinTweetyAtom : Atom := .atom "Penguin" (.cons tweetyTerm .nil)

def strictFly : Rule :=
  { mode := .strict
    params := [x]
    premises := [birdX]
    concl := canFlyX
    questions := []
    allowTrusted := true
    certifiers := [] }

def overlapPolicy : Policy :=
  { rules := [⟨⟨"strictFly"⟩, strictFly⟩]
    defeat := ⟨[(canFlyTweety, penguinTweety)], []⟩ }

theorem overlap_is_not_pattern_equality : canFlyX ≠ canFlyTweety := by decide

/-- The strict rule and declared contrary really do meet under the frozen
instance-level relations; this pins the premise of the review finding. -/
theorem strict_conclusion_instance :
    instAPat [(x, tweetyTerm)] canFlyX = some canFlyTweetyAtom := by decide

theorem declared_instance_is_contrary :
    Attack.ContraryMatch id overlapPolicy.defeat
      canFlyTweetyAtom penguinTweetyAtom := by
  refine ⟨(canFlyTweety, penguinTweety), by simp [overlapPolicy],
    [], canFlyTweetyAtom, penguinTweetyAtom, ?_⟩
  decide

/-- The reviewer counterexample is rejected even though the strict conclusion
and contrary side are not syntactically equal. -/
theorem instantiated_strict_contrary_rejected :
    wfB id overlapPolicy = false := by decide

end Regression

end Lara.Policy
