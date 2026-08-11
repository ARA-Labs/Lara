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

This file intentionally stops at the validator boundary. The public
`Lara.Check.Unit.checkUnit` flow first rejects duplicate rule identifiers and
then runs this R12 validator, before any program checking. Attack completeness
is deliberately not added to the legacy/generic `CheckedProgram`; it is carried
by detailed program acceptance and `Unit.CheckedUnit`. The result-7 theorem
that consumes those facts is downstream-only in `Lara.Consistency`, keeping
the dependency graph acyclic.
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

/-- A duplicate rule identifier, with both declaration positions retained for
the decode-boundary diagnostic. -/
structure DuplicateRule where
  id             : RuleId
  firstIndex     : Nat
  duplicateIndex : Nat
deriving DecidableEq

/-- The first duplicate identifier in declaration order. The outer scan fixes
the first declaration and the inner scan fixes its earliest later duplicate. -/
def firstDuplicateRuleId? (rules : List RuleDecl) : Option DuplicateRule :=
  rules.zipIdx.findSome? fun firstAt =>
    rules.zipIdx.findSome? fun duplicateAt =>
      if firstAt.2 < duplicateAt.2 && firstAt.1.id = duplicateAt.1.id then
        some ⟨firstAt.1.id, firstAt.2, duplicateAt.2⟩
      else
        none

/-- The index-level absence condition denoted by the deterministic scan. -/
private def NoDuplicateRuleIdScan (rules : List RuleDecl) : Prop :=
  ∀ firstAt ∈ rules.zipIdx, ∀ duplicateAt ∈ rules.zipIdx,
    ¬ (firstAt.2 < duplicateAt.2 ∧ firstAt.1.id = duplicateAt.1.id)

private theorem mem_zipIdx_fst_iff {α : Type} (x : α)
    (xs : List α) (n : Nat) :
    x ∈ (xs.zipIdx n).map Prod.fst ↔ x ∈ xs := by
  induction xs generalizing n with
  | nil => simp
  | cons y ys ih =>
      simp only [List.zipIdx_cons, List.map_cons, List.mem_cons]
      exact or_congr Iff.rfl (ih (n + 1))

private theorem mem_zipIdx_succ {α : Type} {entry : α × Nat}
    {xs : List α} {n : Nat} (h : entry ∈ xs.zipIdx n) :
    (entry.1, entry.2 + 1) ∈ xs.zipIdx (n + 1) := by
  induction xs generalizing n entry with
  | nil => simp at h
  | cons x xs ih =>
      simp only [List.zipIdx_cons, List.mem_cons] at h ⊢
      rcases h with h | h
      · subst entry
        simp
      · exact Or.inr (ih h)

private theorem firstDuplicateRuleId?_none_iff_scan (rules : List RuleDecl) :
    firstDuplicateRuleId? rules = none ↔ NoDuplicateRuleIdScan rules := by
  unfold firstDuplicateRuleId? NoDuplicateRuleIdScan
  rw [List.findSome?_eq_none_iff]
  constructor
  · intro h firstAt hfirstAt duplicateAt hduplicateAt hduplicate
    have hinner := h firstAt hfirstAt
    rw [List.findSome?_eq_none_iff] at hinner
    simpa [hduplicate.1, hduplicate.2] using hinner duplicateAt hduplicateAt
  · intro h firstAt hfirstAt
    rw [List.findSome?_eq_none_iff]
    intro duplicateAt hduplicateAt
    by_cases hduplicate :
        firstAt.2 < duplicateAt.2 ∧ firstAt.1.id = duplicateAt.1.id
    · exact False.elim (h firstAt hfirstAt duplicateAt hduplicateAt hduplicate)
    · simp [hduplicate]

private theorem noDuplicateRuleIdScan_iff_nodup (rules : List RuleDecl) :
    NoDuplicateRuleIdScan rules ↔ (rules.map (·.id)).Nodup := by
  constructor
  · intro hscan
    induction rules with
    | nil => simp
    | cons head rest ih =>
        rw [List.map_cons, List.nodup_cons]
        constructor
        · intro hhead
          obtain ⟨d, hd, hid⟩ := List.mem_map.mp hhead
          have hd' : d ∈ (rest.zipIdx 1).map Prod.fst :=
            (mem_zipIdx_fst_iff d rest 1).mpr hd
          obtain ⟨dAt, hdAt, hdAtEq⟩ := List.mem_map.mp hd'
          have hdAtFull : dAt ∈ (head :: rest).zipIdx := by
            simp only [List.zipIdx_cons, List.mem_cons]
            exact Or.inr hdAt
          have hindex : 0 < dAt.2 := by
            obtain ⟨hlo, _, _⟩ := List.mem_zipIdx hdAt
            omega
          apply hscan (head, 0) (by simp) dAt hdAtFull
          constructor
          · exact hindex
          · simpa [hdAtEq] using hid.symm
        · apply ih
          intro firstAt hfirstAt duplicateAt hduplicateAt hduplicate
          have hfirstShift := mem_zipIdx_succ hfirstAt
          have hduplicateShift := mem_zipIdx_succ hduplicateAt
          exact hscan (firstAt.1, firstAt.2 + 1)
            (by
              simp only [List.zipIdx_cons, List.mem_cons]
              exact Or.inr hfirstShift)
            (duplicateAt.1, duplicateAt.2 + 1)
            (by
              simp only [List.zipIdx_cons, List.mem_cons]
              exact Or.inr hduplicateShift)
            ⟨by omega, hduplicate.2⟩
  · intro hnodup firstAt hfirstAt duplicateAt hduplicateAt hduplicate
    obtain ⟨_, hfirstIndex, hfirstEq⟩ := List.mem_zipIdx hfirstAt
    obtain ⟨_, hduplicateIndex, hduplicateEq⟩ :=
      List.mem_zipIdx hduplicateAt
    have hfirstMap : firstAt.2 < (rules.map (·.id)).length := by
      simpa using hfirstIndex
    have hduplicateMap : duplicateAt.2 < (rules.map (·.id)).length := by
      simpa using hduplicateIndex
    have hsame : (rules.map (·.id))[firstAt.2] =
        (rules.map (·.id))[duplicateAt.2] := by
      simp only [List.getElem_map]
      simpa [hfirstEq, hduplicateEq] using hduplicate.2
    have hindices : firstAt.2 = duplicateAt.2 :=
      (List.getElem_inj hnodup).mp hsame
    omega

theorem firstDuplicateRuleId?_none_iff (rules : List RuleDecl) :
    firstDuplicateRuleId? rules = none ↔ (rules.map (·.id)).Nodup :=
  (firstDuplicateRuleId?_none_iff_scan rules).trans
    (noDuplicateRuleIdScan_iff_nodup rules)

/-- Declaration-order (first-match) rule lookup. Raw policies can contain
duplicates; accepted policies rule them out before relying on this function. -/
def lookupRuleDecl : List RuleDecl → RuleId → Option Rule
  | [], _ => none
  | d :: rest, id => if d.id = id then some d.rule else lookupRuleDecl rest id

def Policy.ruleLookup (P : Policy) : RuleId → Option Rule :=
  lookupRuleDecl P.rules

theorem lookupRuleDecl_some_mem {rules : List RuleDecl} {id : RuleId}
    {rule : Rule} (h : lookupRuleDecl rules id = some rule) :
    ∃ d ∈ rules, d.id = id ∧ d.rule = rule := by
  induction rules with
  | nil => simp [lookupRuleDecl] at h
  | cons d rest ih =>
      simp only [lookupRuleDecl] at h
      split at h
      · subst id
        simp_all
      · obtain ⟨d', hd', hid, hrule⟩ := ih h
        exact ⟨d', by simp [hd'], hid, hrule⟩

theorem lookupRuleDecl_of_mem_nodup {rules : List RuleDecl}
    (hnodup : (rules.map (·.id)).Nodup) {d : RuleDecl} (hd : d ∈ rules) :
    lookupRuleDecl rules d.id = some d.rule := by
  induction rules with
  | nil => simp at hd
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · simp [lookupRuleDecl]
      · have hne : head.id ≠ d.id := by
          intro heq
          apply hnodup.1
          simpa [heq] using List.mem_map.mpr ⟨d, hd, rfl⟩
        simp [lookupRuleDecl, hne, ih hnodup.2 hd]

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

/-- Located R12 payload. -/
structure Violation where
  ruleId    : RuleId
  consequent : APat
  contrary  : APat × APat
deriving DecidableEq

def touchingPair? (canon : String → String) (p : APat) :
    List (APat × APat) → Option (APat × APat)
  | [] => none
  | ab :: rest =>
      if aPatMayOverlap canon p ab.1 || aPatMayOverlap canon p ab.2 then
        some ab
      else
        touchingPair? canon p rest

/-- The single declaration-order diagnostic scan. It visits strict rules and
their contrary pairs in list order, returning the first overlap it encounters. -/
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

/-! ### Spec §4.1 rule scope — R12's second arm

Every variable in a rule's premises, conclusion, question answers, and
exception atoms must be among its declared parameters. The spec has always
required this and no checker enforced it; `lara-core@0.2` folds it in here
rather than into R2, because an out-of-scope pattern variable is perfectly
*well-sorted* — it is simply not in scope, which is policy well-formedness.
One class per stage, and R2 stays purely about sorts. -/

/-- Located §4.1 payload: the rule whose scope is violated and the offending
variable. -/
structure ScopeViolation where
  ruleId : RuleId
  param  : VarId
deriving DecidableEq

mutual
  def patEscapee? (params : List VarId) : Pat → Option VarId
    | .var x => if params.contains x then none else some x
    | .num _ => none
    | .str _ => none
    | .con _ ps => patsEscapee? params ps

  def patsEscapee? (params : List VarId) : Pats → Option VarId
    | .nil => none
    | .cons p ps =>
        match patEscapee? params p with
        | some x => some x
        | none => patsEscapee? params ps
end

def aPatEscapee? (params : List VarId) (ap : APat) : Option VarId :=
  patsEscapee? params ap.args

def aPatsEscapee? (params : List VarId) : List APat → Option VarId
  | [] => none
  | ap :: rest =>
      match aPatEscapee? params ap with
      | some x => some x
      | none => aPatsEscapee? params rest

/-- The first out-of-scope variable of one rule, in the fixed order premises,
conclusion, question answers. -/
def ruleEscapee? (r : Rule) : Option VarId :=
  match aPatsEscapee? r.params r.premises with
  | some x => some x
  | none =>
      match aPatEscapee? r.params r.concl with
      | some x => some x
      | none => aPatsEscapee? r.params (r.questions.map (·.answer))

/-- The first §4.1 scope violation in declaration order: rules first, then the
policy's exceptions against their own rule's parameters.

An exception naming an *undeclared* rule is not a scope violation: its rule id
is R1's business at the support stage, and every variable is vacuously outside
an empty parameter list, which would turn one missing declaration into a
misleading R12. -/
def firstOutOfScope? (P : Policy) : Option ScopeViolation :=
  match P.rules.findSome? (fun d => (ruleEscapee? d.rule).map (fun x => (⟨d.id, x⟩ : ScopeViolation))) with
  | some v => some v
  | none =>
      P.defeat.exceptions.findSome? (fun e =>
        match P.rules.find? (fun d => decide (d.id = e.1)) with
        | none => none
        | some d => (aPatEscapee? d.rule.params e.2).map (fun x => (⟨e.1, x⟩ : ScopeViolation)))

/-- The declarative §4.1 judgment decided by `firstOutOfScope?`. -/
def ScopesWellFormed (P : Policy) : Prop := firstOutOfScope? P = none

/-- Decidable by construction: the judgment *is* the scan. -/
instance (P : Policy) : Decidable (ScopesWellFormed P) :=
  inferInstanceAs (Decidable (_ = _))

/-- The first located offending rule/contrary pair, if any. -/
def firstViolation? (canon : String → String) (P : Policy) :
    Option Violation :=
  firstViolationIn? canon P.defeat.contraries P.rules

/-- Executable `wf(Pi)` check, derived from the very same located scan used
for diagnostics. -/
def wfB (canon : String → String) (P : Policy) : Bool :=
  (firstViolation? canon P).isNone

/-- The declarative policy-well-formedness judgment decided by `wfB`. -/
def WellFormed (canon : String → String) (P : Policy) : Prop :=
  ∀ p, StrictReachable P p →
    ∀ ab ∈ P.defeat.contraries,
      aPatMayOverlap canon p ab.1 = false ∧
      aPatMayOverlap canon p ab.2 = false

/-- A scan payload is genuine when it records a declared strict conclusion
and a declared contrary pair whose left or right side overlaps it. -/
def IsViolation (canon : String → String) (P : Policy) (v : Violation) : Prop :=
  ∃ d ∈ P.rules,
    d.rule.mode = .strict ∧
    v.ruleId = d.id ∧ v.consequent = d.rule.concl ∧
    v.contrary ∈ P.defeat.contraries ∧
    (aPatMayOverlap canon d.rule.concl v.contrary.1 = true ∨
      aPatMayOverlap canon d.rule.concl v.contrary.2 = true)

private theorem touchingPair?_none_iff (canon : String → String) (p : APat)
    (contraries : List (APat × APat)) :
    touchingPair? canon p contraries = none ↔
      ∀ ab ∈ contraries,
        aPatMayOverlap canon p ab.1 = false ∧
        aPatMayOverlap canon p ab.2 = false := by
  induction contraries with
  | nil => simp [touchingPair?]
  | cons ab rest ih =>
      constructor
      · intro h candidate hcandidate
        simp only [touchingPair?] at h
        split at h
        · simp at h
        · rename_i hno
          simp only [List.mem_cons] at hcandidate
          rcases hcandidate with hsame | hcandidate
          · subst candidate
            have hsafe :
                aPatMayOverlap canon p ab.1 = false ∧
                  aPatMayOverlap canon p ab.2 = false := by
              cases hleft : aPatMayOverlap canon p ab.1 <;>
                cases hright : aPatMayOverlap canon p ab.2 <;> simp_all
            exact hsafe
          · exact ih.mp h candidate hcandidate
      · intro hall
        simp only [touchingPair?]
        by_cases hover :
            aPatMayOverlap canon p ab.1 || aPatMayOverlap canon p ab.2
        · have hsafe := hall ab (by simp)
          cases hleft : aPatMayOverlap canon p ab.1 <;>
            cases hright : aPatMayOverlap canon p ab.2 <;> simp_all
        · rw [if_neg hover]
          apply ih.mpr
          intro candidate hcandidate
          exact hall candidate (by simp [hcandidate])

private theorem firstViolationIn?_none_iff (canon : String → String)
    (contraries : List (APat × APat)) (rules : List RuleDecl) :
    firstViolationIn? canon contraries rules = none ↔
      ∀ d ∈ rules, d.rule.mode = .strict → ∀ ab ∈ contraries,
        aPatMayOverlap canon d.rule.concl ab.1 = false ∧
        aPatMayOverlap canon d.rule.concl ab.2 = false := by
  induction rules with
  | nil => simp [firstViolationIn?]
  | cons d rest ih =>
      by_cases hstrict : d.rule.mode = .strict
      · cases hpair : touchingPair? canon d.rule.concl contraries with
        | none =>
            constructor
            · intro h e he hstrict' ab hab
              simp only [firstViolationIn?, hstrict, ↓reduceIte, hpair] at h
              have hrest := ih.mp h
              simp only [List.mem_cons] at he
              rcases he with rfl | he
              · exact (touchingPair?_none_iff _ _ _).mp hpair ab hab
              · exact hrest e he hstrict' ab hab
            · intro hall
              simp only [firstViolationIn?, hstrict, ↓reduceIte, hpair]
              apply ih.mpr
              intro e he hstrict' ab hab
              exact hall e (by simp [he]) hstrict' ab hab
        | some ab =>
            constructor
            · intro h
              simp only [firstViolationIn?, hstrict, ↓reduceIte, hpair] at h
              contradiction
            · intro hall
              exfalso
              have hnone : touchingPair? canon d.rule.concl contraries = none :=
                (touchingPair?_none_iff _ _ _).mpr
                  (fun pair hpair' => hall d (by simp) hstrict pair hpair')
              rw [hpair] at hnone
              contradiction
      · constructor
        · intro h e he hstrict' ab hab
          simp only [firstViolationIn?, hstrict, ↓reduceIte] at h
          have hrest := ih.mp h
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · simp [hstrict] at hstrict'
          · exact hrest e he hstrict' ab hab
        · intro hall
          simp only [firstViolationIn?, hstrict, ↓reduceIte]
          apply ih.mpr
          intro e he hstrict' ab hab
          exact hall e (by simp [he]) hstrict' ab hab

theorem firstViolation_none_iff {canon : String → String} {policy : Policy} :
    firstViolation? canon policy = none ↔ WellFormed canon policy := by
  unfold firstViolation? WellFormed
  rw [firstViolationIn?_none_iff]
  constructor
  · intro h p hp ab hab
    cases hp with
    | conclusion hdecl hstrict => exact h _ hdecl hstrict _ hab
  · intro h d hdecl hstrict ab hab
    exact h d.rule.concl (.conclusion hdecl hstrict) ab hab

private theorem touchingPair?_some_sound {canon : String → String}
    {p : APat} {contraries : List (APat × APat)} {ab : APat × APat}
    (h : touchingPair? canon p contraries = some ab) :
    ab ∈ contraries ∧
      (aPatMayOverlap canon p ab.1 = true ∨
        aPatMayOverlap canon p ab.2 = true) := by
  induction contraries with
  | nil => simp [touchingPair?] at h
  | cons head rest ih =>
      simp only [touchingPair?] at h
      split at h
      · rename_i hover
        have hab : head = ab := Option.some.inj h
        subst ab
        exact ⟨by simp, by simpa using hover⟩
      · obtain ⟨hmem, hover⟩ := ih h
        exact ⟨by simp [hmem], hover⟩

private theorem firstViolationIn?_some_sound
    {canon : String → String} {contraries : List (APat × APat)}
    {rules : List RuleDecl} {violation : Violation}
    (h : firstViolationIn? canon contraries rules = some violation) :
    ∃ d ∈ rules,
      d.rule.mode = .strict ∧
      violation.ruleId = d.id ∧ violation.consequent = d.rule.concl ∧
      violation.contrary ∈ contraries ∧
      (aPatMayOverlap canon d.rule.concl violation.contrary.1 = true ∨
        aPatMayOverlap canon d.rule.concl violation.contrary.2 = true) := by
  induction rules with
  | nil => simp [firstViolationIn?] at h
  | cons d rest ih =>
      by_cases hstrict : d.rule.mode = .strict
      · simp only [firstViolationIn?, hstrict, ↓reduceIte] at h
        cases hpair : touchingPair? canon d.rule.concl contraries with
        | none =>
            obtain ⟨e, he, hs, hid, hconcl, hcontra, hover⟩ :=
              ih (by simpa [hpair] using h)
            exact ⟨e, by simp [he], hs, hid, hconcl, hcontra, hover⟩
        | some ab =>
            simp only [hpair] at h
            have hviolation : violation =
                ⟨d.id, d.rule.concl, ab⟩ := Option.some.inj h.symm
            subst violation
            obtain ⟨hab, hover⟩ := touchingPair?_some_sound hpair
            exact ⟨d, by simp, hstrict, rfl, rfl, hab, hover⟩
      · simp [firstViolationIn?, hstrict] at h
        obtain ⟨e, he, hs, hid, hconcl, hcontra, hover⟩ := ih h
        exact ⟨e, by simp [he], hs, hid, hconcl, hcontra, hover⟩

theorem firstViolation_some_sound {canon : String → String} {policy : Policy}
    {violation : Violation}
    (h : firstViolation? canon policy = some violation) :
    IsViolation canon policy violation := by
  unfold IsViolation
  exact firstViolationIn?_some_sound (by simpa [firstViolation?] using h)

/-- `wfB` is sound and complete for the §8.1 judgment. -/
theorem wfB_iff {canon : String → String} {P : Policy} :
    wfB canon P = true ↔ WellFormed canon P := by
  simpa [wfB] using (firstViolation_none_iff (canon := canon) (policy := P))

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
