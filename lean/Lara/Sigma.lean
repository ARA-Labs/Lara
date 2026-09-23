/-
The many-sorted proposition signature `Σ` and well-sortedness — the Lean port of
`src/Lara/Sigma.hs` and `src/Lara/Sigma/WellSorted.hs`, and the mechanization of
`docs/mechanization-plan.md` **result 13**.

v0.1 carried Σ as an elaborator-private arity table nothing read. `lara-core@0.2`
makes it a declared, wire-carried field of `Lara.Unit` and a checked precondition
of reading the policy as patterns (`Lara.Check.Unit.checkUnit` stage 2, rejection
class R2).

Design notes, faithful to the Haskell:

* Two base sorts are built in, `TermSort.num` and `TermSort.str`: the sorts of the two
  `Term` literal constructors. They are not declarable, so `sortOf` is total on
  ground data the frontend never declared.
* TermSort equality is name equality. No subtyping, no sort variables, no sort
  constructors — this is a first-order signature and nothing more.
* Arity is *subsumed*, not replaced: it is the length of the argument-sort
  vector, so the v0.1 `[(Pred, Int)]` view is recoverable and the new object is
  strictly stronger on every axis.
* Rule parameter sorts are **derived, not declared** (spec §3.4): under a
  well-formed Σ every parameter occupies sorted positions in its own rule's
  patterns, so its sort is the unique sort of all its occurrences. Disagreeing
  occurrences are a stage-2 reject. Hence no ninth wire field and no stored
  `Rule` field.
* Everything is `Option`-valued and executable, so decidability is definitional
  and the metatheory is about the *substitution lemma*, which is the load-bearing
  content.

The three results this file carries:

| theorem | statement |
|---|---|
| `wellSorted_decidable` | the executable check decides the relation |
| `wellSorted_subst` | a checked pattern instantiated by a sort-respecting θ yields a well-sorted atom |
| `checkUnit_wellSorted` | every actual recursively reachable rule instance contributes only well-sorted instantiated atoms (`Lara.Check.Unit`) |
-/

import Lara.Support

namespace Lara.Sigma

open Lara Lara.Support

/-! ## Sorts -/

/-- A sort. `num` and `str` are the built-in base sorts; `decl` is an opaque
declared sort name. TermSort equality is name equality.

Named `TermSort`, not `TermSort`: Lean's `TermSort` is the universe of types. This is
the same collision the port already handles for `Atom` vs `Prop`. -/
inductive TermSort where
  | num
  | str
  | decl : String → TermSort
deriving DecidableEq, Repr

/-- The reserved base-sort spellings. A `sort Num` declaration is a
well-formedness reject rather than a silent shadow. -/
def baseSortNames : List String := ["Num", "Str"]

/-- The surface spelling of a sort — the one place the concrete names live. -/
def TermSort.text : TermSort → String
  | .num => "Num"
  | .str => "Str"
  | .decl n => n

/-! ## The signature -/

/-- A constructor signature `con k(s₁, …, sₙ) : s`. A nullary constant is
`⟨k, [], s⟩` — the dominant population in a real corpus, since every bare
identifier argument is a nullary `Term.con`. -/
structure ConSig where
  sym    : ConSym
  args   : List TermSort
  result : TermSort
deriving DecidableEq

/-- A predicate signature `pred p(s₁, …, sₙ)`. Predicates have no result sort —
an `Atom` is not a `Term` — which is why they are a separate table. -/
structure PredSig where
  sym  : PredSym
  args : List TermSort
deriving DecidableEq

/-- A first-order many-sorted signature: declared sorts plus separate
constructor and predicate tables (spec §2). Declaration order is retained so the
wire encoding is canonical. -/
structure Sigma where
  sorts : List String
  cons  : List ConSig
  preds : List PredSig
deriving DecidableEq

/-- The signature declaring nothing. Under strict mode every symbol is
undeclared against it, so it accepts only symbol-free units: it is the unit of
the object, not a permissive default. -/
def Sigma.empty : Sigma := ⟨[], [], []⟩

def Sigma.lookupCon (sg : Sigma) (k : ConSym) : Option ConSig :=
  sg.cons.find? (fun c => decide (c.sym = k))

def Sigma.lookupPred (sg : Sigma) (p : PredSym) : Option PredSig :=
  sg.preds.find? (fun s => decide (s.sym = p))

/-- The v0.1 `[(Pred, Int)]` view, recovered by forgetting sorts: the explicit
witness that the new object subsumes the old one. -/
def Sigma.predArities (sg : Sigma) : List (PredSym × Nat) :=
  sg.preds.map (fun s => (s.sym, s.args.length))

/-! ## Σ well-formedness -/

/-- A malformed signature, in declaration order. -/
inductive SigmaFault where
  | duplicateSort : String → SigmaFault
  | shadowsBase : String → SigmaFault
  | duplicateCon : ConSym → SigmaFault
  | duplicatePred : PredSym → SigmaFault
  | conUndeclaredSort : ConSym → String → SigmaFault
  | predUndeclaredSort : PredSym → String → SigmaFault

/-- The first sort in the list that `declared` does not contain. -/
def firstUndeclared (declared : List String) : List TermSort → Option String
  | [] => none
  | .decl n :: rest => if declared.contains n then firstUndeclared declared rest else some n
  | _ :: rest => firstUndeclared declared rest

private def scanSorts : List String → List String → Option SigmaFault
  | _, [] => none
  | seen, n :: rest =>
      if baseSortNames.contains n then some (.shadowsBase n)
      else if seen.contains n then some (.duplicateSort n)
      else scanSorts (n :: seen) rest

private def scanCons (declared : List String) :
    List ConSym → List ConSig → Option SigmaFault
  | _, [] => none
  | seen, c :: rest =>
      if seen.contains c.sym then some (.duplicateCon c.sym)
      else
        match firstUndeclared declared (c.args ++ [c.result]) with
        | some n => some (.conUndeclaredSort c.sym n)
        | none => scanCons declared (c.sym :: seen) rest

private def scanPreds (declared : List String) :
    List PredSym → List PredSig → Option SigmaFault
  | _, [] => none
  | seen, p :: rest =>
      if seen.contains p.sym then some (.duplicatePred p.sym)
      else
        match firstUndeclared declared p.args with
        | some n => some (.predUndeclaredSort p.sym n)
        | none => scanPreds declared (p.sym :: seen) rest

/-- The first Σ-well-formedness fault in declaration order: sorts (shadowing
before duplication), then constructors, then predicates. Deterministic, so both
runtimes report the same one. -/
def sigmaFault (sg : Sigma) : Option SigmaFault :=
  match scanSorts [] sg.sorts with
  | some f => some f
  | none =>
      match scanCons sg.sorts [] sg.cons with
      | some f => some f
      | none => scanPreds sg.sorts [] sg.preds

/-- Decidable Σ well-formedness, derived from the located scan. -/
def sigmaWellFormed (sg : Sigma) : Bool := (sigmaFault sg).isNone

/-! ## Ground sorting -/

/- The sort of a ground term under Σ (spec §3.4):

```
sortOf (num _)    = Num
sortOf (str _)    = Str
sortOf (con k ts) = k's result sort, provided |ts| matches k's arity and each
                    sortOf tᵢ equals k's declared i-th argument sort
```

`none` on an undeclared symbol, an arity mismatch, or an argument-sort mismatch
— the three ground clauses of the amended R2.

`expectTerms` is the pointwise companion: every term matches its expected sort,
and a length mismatch is a failure, which is exactly the arity clause. -/
mutual
  def sortOf (sg : Sigma) : Term → Option TermSort
    | .num _ => some .num
    | .str _ => some .str
    | .con k ts =>
        match sg.lookupCon ⟨k⟩ with
        | none => none
        | some sig =>
            if expectTerms sg sig.args ts then some sig.result else none

  def expectTerms (sg : Sigma) : List TermSort → Terms → Bool
    | [], .nil => true
    | s :: ss, .cons t ts =>
        match sortOf sg t with
        | some s' => s' == s && expectTerms sg ss ts
        | none => false
    | _, _ => false
end

/-- Well-sortedness of a ground atom: the head is declared, the arity matches,
and every argument has the declared sort. -/
def wsAtom (sg : Sigma) : Atom → Bool
  | .atom p ts =>
      match sg.lookupPred ⟨p⟩ with
      | none => false
      | some sig => expectTerms sg sig.args ts

/-- `wsTerm` is `sortOf` as a predicate. -/
def wsTerm (sg : Sigma) (t : Term) : Bool := (sortOf sg t).isSome

/-! ## Derived parameter sorts and pattern well-sortedness -/

/-- The sorts derived for one pattern scope, in first-occurrence order. -/
abbrev ParamSorts := List (VarId × TermSort)

def lookupParam : ParamSorts → VarId → Option TermSort
  | [], _ => none
  | (y, s) :: rest, x => if y = x then some s else lookupParam rest x

/- Check one pattern against the sort its position demands, extending the
derived parameter environment. `none` is the reject.

A `var` at a fresh position *derives* its sort; a second occurrence must agree,
which is where a disagreeing parameter is caught. `checkPats` is the
argument-list companion. -/
mutual
  def checkPat (sg : Sigma) (env : ParamSorts) (expected : TermSort) :
      Pat → Option ParamSorts
    | .var x =>
        match lookupParam env x with
        | none => some (env ++ [(x, expected)])
        | some s => if s = expected then some env else none
    | .num _ => if expected = .num then some env else none
    | .str _ => if expected = .str then some env else none
    | .con k ps =>
        match sg.lookupCon ⟨k.name⟩ with
        | none => none
        | some sig =>
            if sig.result = expected then checkPats sg env sig.args ps else none

  def checkPats (sg : Sigma) (env : ParamSorts) : List TermSort → Pats → Option ParamSorts
    | [], .nil => some env
    | s :: ss, .cons p ps =>
        match checkPat sg env s p with
        | some env' => checkPats sg env' ss ps
        | none => none
    | _, _ => none
end

/-- Check one atom pattern, extending the derived parameter environment. -/
def checkAPat (sg : Sigma) (env : ParamSorts) (ap : APat) : Option ParamSorts :=
  match sg.lookupPred ⟨ap.pred.name⟩ with
  | none => none
  | some sig => checkPats sg env sig.args ap.args

def checkAPats (sg : Sigma) (env : ParamSorts) : List APat → Option ParamSorts
  | [] => some env
  | ap :: aps =>
      match checkAPat sg env ap with
      | some env' => checkAPats sg env' aps
      | none => none

/-- Derive a rule's parameter sorts from its own patterns, in the fixed order
premises, conclusion, question answers. -/
def ruleParamSorts (sg : Sigma) (r : Rule) : Option ParamSorts :=
  match checkAPats sg [] r.premises with
  | none => none
  | some env₁ =>
      match checkAPat sg env₁ r.concl with
      | none => none
      | some env₂ => checkAPats sg env₂ (r.questions.map (·.answer))

/-- A substitution respects an environment when every parameter the environment
constrains is bound to a term of that sort. This is the hypothesis of the
substitution lemma and exactly what the per-instance half of stage 2 checks. -/
def SortRespecting (sg : Sigma) (env : ParamSorts) (θ : Subst) : Prop :=
  ∀ x s, lookupParam env x = some s →
    ∀ t, lookupSubst θ x = some t → sortOf sg t = some s


/-! ## Result 13(a): decidability

The executable check *is* the relation, so decidability is definitional. That is
the point of keeping every definition above `Option`/`Bool`-valued: nothing in
this development ever needs a classical instance to decide well-sortedness. -/

/-- Well-sortedness of a ground atom, as a proposition. -/
def WellSorted (sg : Sigma) (a : Atom) : Prop := wsAtom sg a = true

/-- **Result 13(a)** — the executable check decides the relation, with no
classical input. `#print axioms` on this instance is the audit: it reports the
empty axiom set. -/
instance wellSorted_decidable (sg : Sigma) : DecidablePred (WellSorted sg) :=
  fun a => inferInstanceAs (Decidable (wsAtom sg a = true))

/-- Σ well-formedness is decidable by the same argument. -/
instance sigmaWellFormed_decidable (sg : Sigma) :
    Decidable (sigmaWellFormed sg = true) := inferInstance

/-- The relation and the executable check are the same thing, definitionally.
Stated so downstream files can rewrite between them by name. -/
theorem wellSorted_iff (sg : Sigma) (a : Atom) :
    WellSorted sg a ↔ wsAtom sg a = true := Iff.rfl

/-! ## Result 13(b): the substitution lemma

The load-bearing metatheory of this pass. Stage 2 checks a rule's *patterns*
once, statically, and each instance's θ *range* separately. Nothing checks the
instantiated atoms — the premises, the conclusion, the answers, the exception
atoms an undercut licenses — directly. This lemma is what licenses that: pattern
well-sortedness plus a sort-respecting θ yields well-sorted atoms.

It is also what licenses the per-instance half of stage 2 being as thin as it is:
without it the θ-range check looks arbitrary; with it, its thinness is a result.
-/

theorem lookupParam_append_of_none {env : ParamSorts} {x : VarId} {s : TermSort}
    (h : lookupParam env x = none) :
    lookupParam (env ++ [(x, s)]) x = some s := by
  induction env with
  | nil => simp [lookupParam]
  | cons e rest ih =>
      simp only [lookupParam] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hne
        simp only [List.cons_append, lookupParam, hne, if_neg, reduceIte]
        exact ih h

theorem lookupParam_append_mono {env ys : ParamSorts} {x : VarId} {s : TermSort}
    (h : lookupParam env x = some s) :
    lookupParam (env ++ ys) x = some s := by
  induction env with
  | nil => simp [lookupParam] at h
  | cons e rest ih =>
      simp only [lookupParam] at h
      split at h
      · rename_i heq
        simp only [List.cons_append, lookupParam, heq, if_pos]
        exact h
      · rename_i hne
        simp only [List.cons_append, lookupParam, hne, reduceIte]
        exact ih h

/- Checking only ever *extends* the derived environment: a parameter's sort is
fixed by its first occurrence and never revised. This is what lets the
substitution lemma state its θ hypothesis against the environment the check
*ends* with — the one stage 2 validates θ against — while using it at every
intermediate step. -/
mutual
  theorem checkPat_mono {sg : Sigma} {env env' : ParamSorts} {s : TermSort} {p : Pat}
      (h : checkPat sg env s p = some env') :
      ∀ x s', lookupParam env x = some s' → lookupParam env' x = some s' := by
    intro x s' hx
    match p with
    | .var y =>
        unfold checkPat at h
        cases hy : lookupParam env y with
        | none =>
            simp only [hy, Option.some.injEq] at h
            subst h
            exact lookupParam_append_mono (ys := [(y, s)]) hx
        | some sy =>
            simp only [hy] at h
            by_cases hs : sy = s
            · simp only [hs, if_pos, Option.some.injEq] at h
              subst h
              exact hx
            · simp only [hs, reduceIte] at h
              exact absurd h (by simp)
    | .num _ =>
        unfold checkPat at h
        by_cases he : s = TermSort.num
        · simp only [he, if_pos, Option.some.injEq] at h
          subst h
          exact hx
        · simp only [he, reduceIte] at h
          exact absurd h (by simp)
    | .str _ =>
        unfold checkPat at h
        by_cases he : s = TermSort.str
        · simp only [he, if_pos, Option.some.injEq] at h
          subst h
          exact hx
        · simp only [he, reduceIte] at h
          exact absurd h (by simp)
    | .con k ps =>
        unfold checkPat at h
        cases hsig : sg.lookupCon ⟨k.name⟩ with
        | none => simp only [hsig] at h; exact absurd h (by simp)
        | some sig =>
            simp only [hsig] at h
            by_cases hr : sig.result = s
            · simp only [hr, if_pos, reduceIte] at h
              exact checkPats_mono h x s' hx
            · simp only [hr, reduceIte] at h
              exact absurd h (by simp)

  theorem checkPats_mono {sg : Sigma} {env env' : ParamSorts}
      {ss : List TermSort} {ps : Pats}
      (h : checkPats sg env ss ps = some env') :
      ∀ x s', lookupParam env x = some s' → lookupParam env' x = some s' := by
    intro x s' hx
    match ss, ps with
    | [], .nil =>
        simp only [checkPats, Option.some.injEq] at h
        subst h
        exact hx
    | [], .cons _ _ => exact absurd h (by simp [checkPats])
    | _ :: _, .nil => exact absurd h (by simp [checkPats])
    | s₀ :: ss, .cons p ps =>
        unfold checkPats at h
        cases hp : checkPat sg env s₀ p with
        | none => simp only [hp] at h; exact absurd h (by simp)
        | some env₁ =>
            simp only [hp] at h
            exact checkPats_mono h x s' (checkPat_mono hp x s' hx)
end

/- **Result 13(b), pattern level.** A pattern accepted at sort `s` under `env`,
instantiated by a θ that respects the *final* environment, produces a term of
sort `s`; and pointwise for argument lists, which is the `expectTerms` side
condition `sortOf` needs on the constructor case. -/
mutual
  theorem instPat_sortOf {sg : Sigma} {env env' : ParamSorts} {θ : Subst}
      {s : TermSort} {p : Pat} {t : Term}
      (hp : checkPat sg env s p = some env')
      (hθ : SortRespecting sg env' θ)
      (hi : instPat θ p = some t) :
      sortOf sg t = some s := by
    match p with
    | .var x =>
        simp only [instPat] at hi
        unfold checkPat at hp
        cases hx : lookupParam env x with
        | none =>
            simp only [hx, Option.some.injEq] at hp
            subst hp
            exact hθ x s (lookupParam_append_of_none hx) t hi
        | some sx =>
            simp only [hx] at hp
            by_cases hs : sx = s
            · simp only [hs, if_pos, Option.some.injEq] at hp
              subst hp
              subst hs
              exact hθ x sx hx t hi
            · simp only [hs, reduceIte] at hp
              exact absurd hp (by simp)
    | .num n =>
        simp only [instPat, Option.some.injEq] at hi
        unfold checkPat at hp
        by_cases he : s = TermSort.num
        · subst he; subst hi; rfl
        · simp only [he, reduceIte] at hp
          exact absurd hp (by simp)
    | .str n =>
        simp only [instPat, Option.some.injEq] at hi
        unfold checkPat at hp
        by_cases he : s = TermSort.str
        · subst he; subst hi; rfl
        · simp only [he, reduceIte] at hp
          exact absurd hp (by simp)
    | .con k ps =>
        unfold checkPat at hp
        cases hsig : sg.lookupCon ⟨k.name⟩ with
        | none => simp only [hsig] at hp; exact absurd hp (by simp)
        | some sig =>
            simp only [hsig] at hp
            by_cases hr : sig.result = s
            · simp only [hr, if_pos, reduceIte] at hp
              simp only [instPat, Option.map_eq_some_iff] at hi
              obtain ⟨ts, hts, ht⟩ := hi
              subst ht
              simp only [sortOf, hsig]
              rw [if_pos (instPats_expectTerms hp hθ hts)]
              exact congrArg some hr
            · simp only [hr, reduceIte] at hp
              exact absurd hp (by simp)

  theorem instPats_expectTerms {sg : Sigma} {env env' : ParamSorts} {θ : Subst}
      {ss : List TermSort} {ps : Pats} {ts : Terms}
      (hp : checkPats sg env ss ps = some env')
      (hθ : SortRespecting sg env' θ)
      (hi : instPats θ ps = some ts) :
      expectTerms sg ss ts = true := by
    match ss, ps with
    | [], .nil =>
        simp only [instPats, Option.some.injEq] at hi
        subst hi
        rfl
    | [], .cons _ _ => exact absurd hp (by simp [checkPats])
    | _ :: _, .nil => exact absurd hp (by simp [checkPats])
    | s :: ss, .cons p ps =>
        unfold checkPats at hp
        cases hcp : checkPat sg env s p with
        | none => simp only [hcp] at hp; exact absurd hp (by simp)
        | some env₁ =>
            simp only [hcp] at hp
            simp only [instPats] at hi
            cases hip : instPat θ p with
            | none => simp only [hip] at hi; exact absurd hi (by simp)
            | some t =>
                cases hips : instPats θ ps with
                | none => simp only [hip, hips] at hi; exact absurd hi (by simp)
                | some ts' =>
                    simp only [hip, hips, Option.some.injEq] at hi
                    subst hi
                    have hts : sortOf sg t = some s :=
                      instPat_sortOf hcp
                        (fun x sx hx u hu => hθ x sx (checkPats_mono hp x sx hx) u hu)
                        hip
                    simp only [expectTerms, hts, beq_self_eq_true, Bool.true_and]
                    exact instPats_expectTerms hp hθ hips
end

/-- `checkAPat` extends the environment, exactly as `checkPats` does. -/
theorem checkAPat_mono {sg : Sigma} {env env' : ParamSorts} {ap : APat}
    (h : checkAPat sg env ap = some env') :
    ∀ x s', lookupParam env x = some s' → lookupParam env' x = some s' := by
  intro x s' hx
  unfold checkAPat at h
  cases hsig : sg.lookupPred ⟨ap.pred.name⟩ with
  | none => rw [hsig] at h; exact absurd h (by simp)
  | some sig => rw [hsig] at h; exact checkPats_mono h x s' hx

/-- The list form of `checkAPat_mono`. -/
theorem checkAPats_mono {sg : Sigma} {env env' : ParamSorts} {aps : List APat}
    (h : checkAPats sg env aps = some env') :
    ∀ x s', lookupParam env x = some s' → lookupParam env' x = some s' := by
  induction aps generalizing env with
  | nil =>
      intro x s' hx
      have he : env = env' := Option.some.inj h
      subst he
      exact hx
  | cons ap aps ih =>
      intro x s' hx
      unfold checkAPats at h
      cases hca : checkAPat sg env ap with
      | none => rw [hca] at h; exact absurd h (by simp)
      | some env₁ =>
          rw [hca] at h
          exact ih h x s' (checkAPat_mono hca x s' hx)

/-- **Result 13(b).** An atom pattern accepted under Σ and instantiated by a
sort-respecting θ is a well-sorted ground atom.

This is the per-pattern substitution step for instantiated premises,
conclusions, answers, and exception atoms. `Lara.Check.Unit.checkUnit_wellSorted`
closes it recursively over the rule instances in accepted support terms. -/
theorem wellSorted_subst {sg : Sigma} {env env' : ParamSorts} {θ : Subst}
    {ap : APat} {a : Atom}
    (hp : checkAPat sg env ap = some env')
    (hθ : SortRespecting sg env' θ)
    (hi : instAPat θ ap = some a) :
    WellSorted sg a := by
  unfold checkAPat at hp
  cases hsig : sg.lookupPred ⟨ap.pred.name⟩ with
  | none => rw [hsig] at hp; exact absurd hp (by simp)
  | some sig =>
      rw [hsig] at hp
      simp only [instAPat, Option.map_eq_some_iff] at hi
      obtain ⟨ts, hts, ha⟩ := hi
      subst ha
      show wsAtom sg (.atom ap.pred.name ts) = true
      simp only [wsAtom, hsig]
      exact instPats_expectTerms hp hθ hts

/-- Every atom of a checked pattern *list* instantiated by a sort-respecting θ
is well-sorted — the premise-list and answer-list form of `wellSorted_subst`. -/
theorem wellSorted_subst_list {sg : Sigma} {env env' : ParamSorts} {θ : Subst}
    {aps : List APat} {as : List Atom}
    (hp : checkAPats sg env aps = some env')
    (hθ : SortRespecting sg env' θ)
    (hi : instAPats θ aps = some as) :
    ∀ a ∈ as, WellSorted sg a := by
  induction aps generalizing env as with
  | nil =>
      have he : ([] : List Atom) = as := Option.some.inj hi
      subst he
      simp
  | cons ap aps ih =>
      unfold checkAPats at hp
      cases hca : checkAPat sg env ap with
      | none => rw [hca] at hp; exact absurd hp (by simp)
      | some env₁ =>
          rw [hca] at hp
          simp only [instAPats] at hi
          cases hia : instAPat θ ap with
          | none => rw [hia] at hi; exact absurd hi (by simp)
          | some a =>
              cases hias : instAPats θ aps with
              | none => rw [hia, hias] at hi; exact absurd hi (by simp)
              | some rest =>
                  rw [hia, hias] at hi
                  have he : a :: rest = as := Option.some.inj hi
                  subst he
                  intro b hb
                  simp only [List.mem_cons] at hb
                  rcases hb with hb | hb
                  · subst hb
                    exact wellSorted_subst hca
                      (fun x sx hx u hu => hθ x sx (checkAPats_mono hp x sx hx) u hu) hia
                  · exact ih hp hias b hb

/-- A member of a checked pattern list is itself checked from *some*
environment the list scan passes through, and that environment is contained in
the scan's final one. This is the projection `wellSorted_rule` needs to reach a
single question answer without threading every intermediate environment. -/
theorem wellSorted_subst_mem {sg : Sigma} {env env' : ParamSorts} {θ : Subst}
    {aps : List APat} {ap : APat} {a : Atom}
    (hp : checkAPats sg env aps = some env')
    (hθ : SortRespecting sg env' θ)
    (hmem : ap ∈ aps)
    (hi : instAPat θ ap = some a) :
    WellSorted sg a := by
  induction aps generalizing env with
  | nil => simp at hmem
  | cons b bs ih =>
      unfold checkAPats at hp
      cases hcb : checkAPat sg env b with
      | none => rw [hcb] at hp; exact absurd hp (by simp)
      | some env₁ =>
          rw [hcb] at hp
          simp only [List.mem_cons] at hmem
          rcases hmem with hmem | hmem
          · subst hmem
            exact wellSorted_subst hcb
              (fun x sx hx u hu => hθ x sx (checkAPats_mono hp x sx hx) u hu) hi
          · exact ih hp hmem

/-- θ respects a rule when it respects the environment the rule's own patterns
derive. For an actual accepted instance, stage 2's range check and R3's exact
substitution-domain invariant derive this proposition in
`Lara.Check.Unit.thetaWellSorted_ruleSortRespecting`. -/
def RuleSortRespecting (sg : Sigma) (r : Rule) (θ : Subst) : Prop :=
  ∀ env, ruleParamSorts sg r = some env → SortRespecting sg env θ

/-- **Result 13(b), rule level.** Under a rule whose own patterns all pass and a
θ respecting the derived environment, *every* instantiated atom of the rule is
well-sorted: its premises, its conclusion, and every critical-question answer.

Exception patterns require a separate per-pattern application of
`wellSorted_subst`; they are not part of this rule-level conjunction. -/
theorem wellSorted_rule {sg : Sigma} {r : Rule} {θ : Subst} {env : ParamSorts}
    (hr : ruleParamSorts sg r = some env)
    (hθ : SortRespecting sg env θ) :
    (∀ as, instAPats θ r.premises = some as → ∀ a ∈ as, WellSorted sg a) ∧
    (∀ c, instAPat θ r.concl = some c → WellSorted sg c) ∧
    (∀ q ∈ r.questions, ∀ a, instAPat θ q.answer = some a → WellSorted sg a) := by
  unfold ruleParamSorts at hr
  cases hprem : checkAPats sg [] r.premises with
  | none => simp only [hprem] at hr; exact absurd hr (by simp)
  | some env₁ =>
      simp only [hprem] at hr
      cases hconcl : checkAPat sg env₁ r.concl with
      | none => simp only [hconcl] at hr; exact absurd hr (by simp)
      | some env₂ =>
          simp only [hconcl] at hr
          -- The three environments nest, so a θ respecting the last respects
          -- each earlier one (`SortRespecting` is contravariant in the
          -- environment, and checking only extends it).
          have hθ₂ : SortRespecting sg env₂ θ :=
            fun x sx hx u hu => hθ x sx (checkAPats_mono hr x sx hx) u hu
          have hθ₁ : SortRespecting sg env₁ θ :=
            fun x sx hx u hu => hθ₂ x sx (checkAPat_mono hconcl x sx hx) u hu
          refine ⟨?_, ?_, ?_⟩
          · intro as hi
            exact wellSorted_subst_list hprem hθ₁ hi
          · intro c hi
            exact wellSorted_subst hconcl hθ₂ hi
          · intro q hq a hi
            have hmem : q.answer ∈ r.questions.map (·.answer) :=
              List.mem_map.mpr ⟨q, hq, rfl⟩
            -- The answer list is checked from `env₂`; pull out the prefix whose
            -- final environment `env` is, then apply the atom-level lemma.
            exact wellSorted_subst_mem hr hθ hmem hi

end Lara.Sigma
