/-
Value expansion for the checked surface calculus: the simultaneous,
non-recursive value-binding substitution plus `{cell e}` / `{name}`
interpolation and `{{` / `}}` escape handling, mirroring the production
`Lara.Elaborate.ValueBinding.expandValueBindings` pass.

The expansion relation `ExpandsValues` is stated independently (structural
replacement over declarations and prose); the executable `expandValues`
rejects with the production error precedence (duplicate names, the reserved
`cell` name, constructor collisions, non-sorting right-hand sides, claim
formals, then prose interpolation).  Soundness, completeness (over the
reviewed `ValueBindingsWellFormed` fragment), idempotence, and declaration-id
preservation are proved against that relation.
-/
import Lara.Surface.Syntax

namespace Lara.Surface

open Lara
open Lara.Presentation

/-! ### Canonical decimal rendering (`{cell e}` interpolation output) -/

/-- The smallest `k` with `d` dividing `10^k` — the mirror of the Haskell
`Cell.decimalScale`.  The fuel parameter keeps the definition total on a zero
denominator, which the callers never produce. -/
private def decimalScaleAux (fuel : Nat) (twos fives : Nat) : Nat → Option Nat
  | 1 => some (max twos fives)
  | d =>
      if d % 2 = 0 then
        match fuel with
        | 0 => none
        | fuel + 1 => decimalScaleAux fuel (twos + 1) fives (d / 2)
      else if d % 5 = 0 then
        match fuel with
        | 0 => none
        | fuel + 1 => decimalScaleAux fuel twos (fives + 1) (d / 5)
      else none

private def decimalScale (den : Nat) : Option Nat :=
  decimalScaleAux den 0 0 den

private def padLeftZeros (width : Nat) (s : String) : String :=
  String.ofList (List.replicate (width - s.length) '0' ++ s.toList)

private def dropTrailingZeros (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile (fun c => c == '0')).reverse)

private def renderUnsigned (num den : Nat) : String :=
  match decimalScale den with
  | none => toString num ++ "/" ++ toString den
  | some k =>
      let pow := 10 ^ k
      let scaled := num * pow / den
      let whole := scaled / pow
      let frac := scaled % pow
      let padded := padLeftZeros k (toString frac)
      let fracPart := dropTrailingZeros padded
      if fracPart.isEmpty then toString whole
      else toString whole ++ "." ++ fracPart

/-- Render an exact decimal back into the canonical decimal grammar — the
mirror of the Haskell `Cell.renderDecimal`. -/
def renderDecimal (d : Lara.Cell.Dec) : String :=
  if d.num < 0 then "-" ++ renderUnsigned (-d.num).toNat d.den
  else renderUnsigned d.num.toNat d.den

/-! ### Term rendering (`{name}` interpolation output) -/

private def escapeChar : Char → String
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\t' => "\\t"
  | '\r' => "\\r"
  | c => c.toString

private def showString (s : String) : String :=
  "\"" ++ (s.toList.map escapeChar).foldl (· ++ ·) "" ++ "\""

mutual
  /-- The surface spelling of a ground term — the mirror of the Haskell
  `Lara.Prop.prettyTerm`. -/
  def prettyTerm : Term → String
    | .num s => s
    | .str s => showString s
    | .con name .nil => name
    | .con name ts => name ++ "(" ++ prettyTerms ts ++ ")"
  private def prettyTerms : Terms → String
    | .nil => ""
    | .cons t .nil => prettyTerm t
    | .cons t rest => prettyTerm t ++ ", " ++ prettyTerms rest
end

/-! ### Cell extraction for interpolation -/

/-- The consulted cell of a proposition, normalized like production
`Cell.premiseCell`: the unique numeric literal is canonicalized before the
canonical-decimal parse. -/
def cellDecimal? : Atom → Option Lara.Cell.Dec
  | .atom _ terms =>
      match Lara.Cell.termsNums terms with
      | [number] => Lara.Cell.parseDecimal (Lara.canonNum number)
      | _ => none

/-! ### The natural-language interpolation walk -/

private def valueForDirective (env : List Presentation.ValueBinding) (body : List Char) :
    Option Presentation.ValueBinding :=
  env.find? fun b => decide (b.name.val.toList = body)

private def cellForDirective (gamma : List (Presentation.LeafId × Atom)) (body : List Char) :
    Option (Presentation.LeafId × Atom) :=
  match body with
  | 'c' :: 'e' :: 'l' :: 'l' :: ' ' :: rest =>
      gamma.find? fun entry => decide (entry.1.val.toList = rest)
  | _ => none

/-- The structural interpolation relation: one left-to-right pass over the raw
brace language, emitting escaped braces as literal prose and replacing each
directive with its value.  `{{` and `}}` are the only escapes; a stray `}` is
not part of any successful expansion, and a directive name containing a close
brace would end the directive early, so such names are excluded from the
successful constructors. -/
inductive ExpandsNl (env : List Presentation.ValueBinding)
    (gamma : List (Presentation.LeafId × Atom)) : List Char → List Char → Prop where
  | nil : ExpandsNl env gamma [] []
  | char (c : Char) {rest out : List Char} (hc : c ≠ '{' ∧ c ≠ '}') :
      ExpandsNl env gamma rest out →
      ExpandsNl env gamma (c :: rest) (c :: out)
  | escLeft {rest out : List Char} :
      ExpandsNl env gamma rest out →
      ExpandsNl env gamma ('{' :: '{' :: rest) ('{' :: out)
  | escRight {rest out : List Char} :
      ExpandsNl env gamma rest out →
      ExpandsNl env gamma ('}' :: '}' :: rest) ('}' :: out)
  | value {b : Presentation.ValueBinding} {rest out : List Char}
      (henv : valueForDirective env b.name.val.toList = some b)
      (hb : ∀ c ∈ b.name.val.toList, c ≠ '}')
      (hhead : ∀ (c0 : Char) (cs0 : List Char), b.name.val.toList ≠ '{' :: cs0) :
      ExpandsNl env gamma rest out →
      ExpandsNl env gamma ('{' :: (b.name.val.toList ++ '}' :: rest))
        ((prettyTerm b.term).toList ++ out)
  | cell {leaf : Presentation.LeafId} {prop : Atom} {d : Lara.Cell.Dec} {rest out : List Char}
      (hgamma : cellForDirective gamma ("cell ".toList ++ leaf.val.toList) = some (leaf, prop))
      (hdec : cellDecimal? prop = some d)
      (hvalue : valueForDirective env ("cell ".toList ++ leaf.val.toList) = none)
      (hleaf : ∀ c ∈ leaf.val.toList, c ≠ '}') :
      ExpandsNl env gamma rest out →
      ExpandsNl env gamma
        ('{' :: ("cell ".toList ++ leaf.val.toList ++ '}' :: rest))
        ((renderDecimal d).toList ++ out)

/-- The executable interpolation walk (fuel-bounded, like `parseNlFuel`). -/
private def expandNlGo (env : List Presentation.ValueBinding)
    (gamma : List (Presentation.LeafId × Atom)) (claimId : String) :
    Nat → List Char → Except Surface.Error (List Char)
  | 0, _ => .error (.invalidValueBinding ⟨claimId⟩)
  | fuel + 1, '{' :: '{' :: rest =>
      Except.map (fun tail => '{' :: tail) (expandNlGo env gamma claimId fuel rest)
  | fuel + 1, '}' :: '}' :: rest =>
      Except.map (fun tail => '}' :: tail) (expandNlGo env gamma claimId fuel rest)
  | _, '}' :: _ => .error (.invalidValueBinding ⟨claimId⟩)
  | fuel + 1, '{' :: rest =>
      match takeDirective rest with
      | none => .error (.invalidValueBinding ⟨claimId⟩)
      | some (body, after) =>
          match valueForDirective env body with
          | some b =>
              Except.map (fun tail => (prettyTerm b.term).toList ++ tail)
                (expandNlGo env gamma claimId fuel after)
          | none =>
              match cellForDirective gamma body with
              | some (leaf, prop) =>
                  match cellDecimal? prop with
                  | some d =>
                      Except.map (fun tail => (renderDecimal d).toList ++ tail)
                        (expandNlGo env gamma claimId fuel after)
                  | none => .error (.invalidValueBinding ⟨String.ofList body⟩)
              | none => .error (.invalidValueBinding ⟨String.ofList body⟩)
  | fuel + 1, c :: rest =>
      Except.map (fun tail => c :: tail) (expandNlGo env gamma claimId fuel rest)
  | _, [] => .ok []

/-- Interpolate one claim's prose. -/
def expandNl (env : List Presentation.ValueBinding)
    (gamma : List (Presentation.LeafId × Atom)) (claimId : String) (text : String) :
    Except Surface.Error String :=
  (expandNlGo env gamma claimId (text.toList.length + 1) text.toList).map String.ofList

/-- Proof-only view of prose interpolation that retains success/failure and
exact error provenance while erasing the generated prose. -/
private def validateNlGo (env : List Presentation.ValueBinding)
    (gamma : List (Presentation.LeafId × Atom)) (claimId : String) :
    Nat → List Char → Except Surface.Error _root_.Unit
  | 0, _ => .error (.invalidValueBinding ⟨claimId⟩)
  | fuel + 1, '{' :: '{' :: rest =>
      validateNlGo env gamma claimId fuel rest
  | fuel + 1, '}' :: '}' :: rest =>
      validateNlGo env gamma claimId fuel rest
  | _, '}' :: _ => .error (.invalidValueBinding ⟨claimId⟩)
  | fuel + 1, '{' :: rest =>
      match takeDirective rest with
      | none => .error (.invalidValueBinding ⟨claimId⟩)
      | some (body, after) =>
          match valueForDirective env body with
          | some _ => validateNlGo env gamma claimId fuel after
          | none =>
              match cellForDirective gamma body with
              | some (_, prop) =>
                  match cellDecimal? prop with
                  | some _ => validateNlGo env gamma claimId fuel after
                  | none => .error (.invalidValueBinding ⟨String.ofList body⟩)
              | none => .error (.invalidValueBinding ⟨String.ofList body⟩)
  | fuel + 1, _ :: rest => validateNlGo env gamma claimId fuel rest
  | _, [] => .ok ()

private def validateNl (env : List Presentation.ValueBinding)
    (gamma : List (Presentation.LeafId × Atom)) (claimId : String)
    (text : String) : Except Surface.Error _root_.Unit :=
  validateNlGo env gamma claimId (text.toList.length + 1) text.toList

@[simp] private theorem exceptMapUnit_error (error : Surface.Error) :
    (Except.error error : Except Surface.Error α).map (fun _ => ()) =
      .error error := rfl

@[simp] private theorem exceptMapUnit_ok (value : α) :
    (Except.ok value : Except Surface.Error α).map (fun _ => ()) =
      .ok () := rfl

@[simp] private theorem exceptMapUnit_after_map
    (result : Except Surface.Error α) (f : α → β) :
    (result.map f).map (fun _ => ()) = result.map (fun _ => ()) := by
  cases result <;> rfl

private theorem expandNlGo_erase (env : List Presentation.ValueBinding)
    (gamma : List (Presentation.LeafId × Atom)) (claimId : String) :
    ∀ fuel chars,
      (expandNlGo env gamma claimId fuel chars).map (fun _ => ()) =
        validateNlGo env gamma claimId fuel chars := by
  intro fuel
  induction fuel with
  | zero => intro chars; simp [expandNlGo, validateNlGo]
  | succ fuel ih =>
      intro chars
      cases chars with
      | nil => rfl
      | cons char rest =>
          by_cases openBrace : char = '{'
          · subst char
            cases rest with
            | nil => rfl
            | cons second tail =>
                by_cases escaped : second = '{'
                · subst second
                  simp [expandNlGo, validateNlGo, ih]
                · cases taken : takeDirective (second :: tail) with
                  | none => simp [expandNlGo, validateNlGo, escaped, taken]
                  | some pair =>
                      obtain ⟨body, after⟩ := pair
                      cases value : valueForDirective env body with
                      | some binding =>
                          simp [expandNlGo, validateNlGo, escaped, taken,
                            value, ih]
                      | none =>
                          cases cell : cellForDirective gamma body with
                          | none =>
                              simp [expandNlGo, validateNlGo, escaped, taken,
                                value, cell]
                          | some entry =>
                              obtain ⟨leaf, prop⟩ := entry
                              cases decimal : cellDecimal? prop <;>
                                simp [expandNlGo, validateNlGo, escaped, taken,
                                  value, cell, decimal, ih]
          · by_cases closeBrace : char = '}'
            · subst char
              cases rest with
              | nil => rfl
              | cons second tail =>
                  by_cases escaped : second = '}'
                  · subst second
                    simp [expandNlGo, validateNlGo, ih]
                  · simp [expandNlGo, validateNlGo, escaped]
            · simp [expandNlGo, validateNlGo, openBrace, closeBrace,
                ih]

private theorem expandNl_erase (env : List Presentation.ValueBinding)
    (gamma : List (Presentation.LeafId × Atom)) (claimId : String)
    (text : String) :
    (expandNl env gamma claimId text).map (fun _ => ()) =
      validateNl env gamma claimId text := by
  unfold expandNl validateNl
  rw [← expandNlGo_erase env gamma claimId]
  cases expandNlGo env gamma claimId (text.toList.length + 1)
      text.toList <;> rfl

private theorem takeDirective_after_length_lt_early :
    ∀ chars body after,
      takeDirective chars = some (body, after) →
        after.length < chars.length
  | [], _, _, found => by simp [takeDirective] at found
  | char :: rest, body, after, found => by
      by_cases closing : char = '}'
      · subst char
        simp [takeDirective] at found
        obtain ⟨rfl, rfl⟩ := found
        simp
      · simp [takeDirective, closing] at found
        cases tailFound : takeDirective rest with
        | none => simp [tailFound] at found
        | some pair =>
            obtain ⟨tailBody, tailAfter⟩ := pair
            simp [tailFound] at found
            obtain ⟨rfl, rfl⟩ := found
            have shorter :=
              takeDirective_after_length_lt_early rest tailBody tailAfter
                tailFound
            simp
            omega

private theorem validateNlGo_eq_of_length_lt
    (env : List Presentation.ValueBinding)
    (gamma : List (Presentation.LeafId × Atom)) (claimId : String) :
    ∀ fuel chars,
      chars.length < fuel →
      ∀ other, chars.length < other →
        validateNlGo env gamma claimId fuel chars =
          validateNlGo env gamma claimId other chars := by
  intro fuel
  induction fuel with
  | zero => intro chars shorter; omega
  | succ fuel ih =>
      intro chars shorter other otherShorter
      cases other with
      | zero => omega
      | succ other =>
          cases chars with
          | nil => rfl
          | cons char rest =>
              by_cases openBrace : char = '{'
              · subst char
                cases rest with
                | nil => rfl
                | cons second tail =>
                    by_cases escaped : second = '{'
                    · subst second
                      simp only [validateNlGo]
                      apply ih tail
                      · simp only [List.length_cons] at shorter
                        omega
                      · simp only [List.length_cons] at otherShorter
                        omega
                    · cases taken : takeDirective (second :: tail) with
                      | none =>
                          simp [validateNlGo, escaped, taken]
                      | some pair =>
                          obtain ⟨body, after⟩ := pair
                          have afterStep :=
                            takeDirective_after_length_lt_early
                              (second :: tail) body after taken
                          have afterFuel : after.length < fuel := by
                            simp only [List.length_cons] at shorter afterStep
                            omega
                          have afterOther : after.length < other := by
                            simp only [List.length_cons] at otherShorter afterStep
                            omega
                          cases value : valueForDirective env body with
                          | some binding =>
                              simp [validateNlGo, escaped, taken, value,
                                ih after afterFuel other afterOther]
                          | none =>
                              cases cell : cellForDirective gamma body with
                              | none =>
                                  simp [validateNlGo, escaped, taken, value,
                                    cell]
                              | some entry =>
                                  obtain ⟨leaf, prop⟩ := entry
                                  cases decimal : cellDecimal? prop <;>
                                    simp [validateNlGo, escaped, taken, value,
                                      cell, decimal,
                                      ih after afterFuel other afterOther]
              · by_cases closeBrace : char = '}'
                · subst char
                  cases rest with
                  | nil => rfl
                  | cons second tail =>
                      by_cases escaped : second = '}'
                      · subst second
                        simp only [validateNlGo]
                        apply ih tail
                        · simp only [List.length_cons] at shorter
                          omega
                        · simp only [List.length_cons] at otherShorter
                          omega
                      · simp [validateNlGo, escaped]
                · have restFuel : rest.length < fuel := by
                    simp only [List.length_cons] at shorter
                    omega
                  have restOther : rest.length < other := by
                    simp only [List.length_cons] at otherShorter
                    omega
                  simpa [validateNlGo, openBrace, closeBrace] using
                    ih rest restFuel other restOther

private theorem takeDirective_eq_takeNlDirective_local
    (chars : List Char) :
    takeDirective chars = Binding.takeNlDirective chars := by
  induction chars with
  | nil => rfl
  | cons char rest =>
      by_cases close : char = '}'
      · subst char
        rfl
      · simp [takeDirective, Binding.takeNlDirective, close, *]

private theorem renameNlChars_eq_of_length_lt
    (ρg : Binding.GlobalRenaming) :
    ∀ fuel chars,
      chars.length < fuel →
      ∀ other, chars.length < other →
        Binding.renameNlChars ρg fuel chars =
          Binding.renameNlChars ρg other chars := by
  intro fuel
  induction fuel with
  | zero => intro chars shorter; omega
  | succ fuel ih =>
      intro chars shorter other otherShorter
      cases other with
      | zero => omega
      | succ other =>
          cases chars with
          | nil => rfl
          | cons char rest =>
              by_cases openBrace : char = '{'
              · subst char
                cases rest with
                | nil => rfl
                | cons second tail =>
                    by_cases escaped : second = '{'
                    · subst second
                      have tailFuel : tail.length < fuel := by
                        simp only [List.length_cons] at shorter
                        omega
                      have tailOther : tail.length < other := by
                        simp only [List.length_cons] at otherShorter
                        omega
                      simp [Binding.renameNlChars,
                        ih tail tailFuel other tailOther]
                    · cases taken : Binding.takeNlDirective
                          (second :: tail) with
                      | none =>
                          simp [Binding.renameNlChars, escaped, taken]
                      | some pair =>
                          obtain ⟨body, after⟩ := pair
                          have surfaceTaken :
                              takeDirective (second :: tail) =
                                some (body, after) := by
                            rw [takeDirective_eq_takeNlDirective_local]
                            exact taken
                          have afterStep :=
                            takeDirective_after_length_lt_early
                              (second :: tail) body after surfaceTaken
                          have afterFuel : after.length < fuel := by
                            simp only [List.length_cons] at shorter afterStep
                            omega
                          have afterOther : after.length < other := by
                            simp only [List.length_cons] at otherShorter afterStep
                            omega
                          simp [Binding.renameNlChars, escaped, taken,
                            ih after afterFuel other afterOther]
              · by_cases closeBrace : char = '}'
                · subst char
                  cases rest with
                  | nil => cases fuel <;> cases other <;> rfl
                  | cons second tail =>
                      by_cases escaped : second = '}'
                      · subst second
                        have tailFuel : tail.length < fuel := by
                          simp only [List.length_cons] at shorter
                          omega
                        have tailOther : tail.length < other := by
                          simp only [List.length_cons] at otherShorter
                          omega
                        simp [Binding.renameNlChars,
                          ih tail tailFuel other tailOther]
                      · have restFuel : (second :: tail).length < fuel := by
                          simp only [List.length_cons] at shorter ⊢
                          omega
                        have restOther : (second :: tail).length < other := by
                          simp only [List.length_cons] at otherShorter ⊢
                          omega
                        simp [Binding.renameNlChars, escaped,
                          ih (second :: tail) restFuel other restOther]
                · have restFuel : rest.length < fuel := by
                    simp only [List.length_cons] at shorter
                    omega
                  have restOther : rest.length < other := by
                    simp only [List.length_cons] at otherShorter
                    omega
                  simpa [Binding.renameNlChars, openBrace, closeBrace] using
                    congrArg (List.cons char)
                      (ih rest restFuel other restOther)

private theorem find?_eq_some_implies_mem {α} (p : α → Bool) {l : List α} {a : α}
    (h : l.find? p = some a) : p a = true ∧ a ∈ l := by
  induction l with
  | nil => simp [List.find?] at h
  | cons b rest ih =>
      rw [List.find?] at h
      by_cases hb : p b = true
      · simp [hb] at h
        subst b
        exact ⟨hb, by simp⟩
      · simp [hb] at h
        rcases ih h with ⟨hp, hm⟩
        exact ⟨hp, by simp [hm]⟩

private theorem takeDirective_roundtrip {body after : List Char}
    (h : ∀ c ∈ body, c ≠ '}') :
    takeDirective (body ++ '}' :: after) = some (body, after) := by
  induction body with
  | nil => rfl
  | cons c rest ih =>
      have hc : c ≠ '}' := h c (by simp)
      have hrest : ∀ x ∈ rest, x ≠ '}' := by
        intro x hx; exact h x (by simp [hx])
      by_cases hc' : c = '}'
      · exfalso; exact hc hc'
      · simp [takeDirective, ih hrest]

private theorem takeDirective_no_close : ∀ (chars : List Char) (body after : List Char),
    takeDirective chars = some (body, after) → ∀ c ∈ body, c ≠ '}'
  | [], _, _, h => by
      intro c hc
      exfalso
      simpa [takeDirective] using h
  | '}' :: rest, _, _, h => by
      intro c hc
      simp [takeDirective] at h
      rcases h with ⟨hb, _⟩
      exfalso
      simpa [hb] using hc
  | c :: rest, body, after, h => by
      intro x hx
      by_cases hc' : c = '}'
      · subst c
        exfalso
        simp [takeDirective] at h
        rcases h with ⟨hb, _⟩
        simpa [hb] using hx
      · simp [takeDirective] at h
        cases hrest : takeDirective rest with
        | none =>
            exfalso
            simp [hrest] at h
        | some pair =>
            rcases pair with ⟨body', after'⟩
            simp [hrest] at h
            rcases h with ⟨hb, ha⟩
            subst body
            subst after
            cases hx
            · exact hc'
            · exact takeDirective_no_close rest body' after' hrest x (by assumption)

/-- A successful directive parse splits the input at the first close brace. -/
private theorem takeDirective_eq_some_implies_split : ∀ (chars : List Char) (body after : List Char),
    takeDirective chars = some (body, after) → chars = body ++ '}' :: after
  | [], _, _, h => by simp [takeDirective] at h
  | '}' :: rest, _, _, h => by
      simp [takeDirective] at h
      rcases h with ⟨hb, ha⟩
      rw [hb, ← ha]
      rfl
  | c :: rest, body, after, h => by
      by_cases hc' : c = '}'
      · subst c
        simp [takeDirective] at h
        rcases h with ⟨hb, ha⟩
        rw [hb, ← ha]
        rfl
      · simp [takeDirective] at h
        cases hrest : takeDirective rest with
        | none => simp [hrest] at h
        | some pair =>
            rcases pair with ⟨body', after'⟩
            simp [hrest] at h
            rcases h with ⟨hb, ha⟩
            subst body
            subst after
            have hsplit := takeDirective_eq_some_implies_split rest body' after' hrest
            rw [hsplit]
            rfl

private theorem cellForDirective_eq_some_iff {gamma body leaf prop} :
    cellForDirective gamma body = some (leaf, prop) →
    body = "cell ".toList ++ leaf.val.toList ∧
      cellForDirective gamma ("cell ".toList ++ leaf.val.toList) = some (leaf, prop) := by
  intro h
  unfold cellForDirective at h
  cases body with
  | nil => simp at h
  | cons c1 rest1 =>
      by_cases h1 : c1 = 'c'
      · subst c1
        cases rest1 with
        | nil => simp at h
        | cons c2 rest2 =>
            by_cases h2 : c2 = 'e'
            · subst c2
              cases rest2 with
              | nil => simp at h
              | cons c3 rest3 =>
                  by_cases h3 : c3 = 'l'
                  · subst c3
                    cases rest3 with
                    | nil => simp at h
                    | cons c4 rest4 =>
                        by_cases h4 : c4 = 'l'
                        · subst c4
                          cases rest4 with
                          | nil => simp at h
                          | cons c5 rest5 =>
                              by_cases h5 : c5 = ' '
                              · subst c5
                                simp at h
                                have hm : decide (leaf.val.toList = rest5) = true ∧ (leaf, prop) ∈ gamma :=
                                  find?_eq_some_implies_mem
                                    (fun entry : Presentation.LeafId × Atom =>
                                      decide (entry.1.val.toList = rest5)) h
                                have hrest : leaf.val.toList = rest5 := of_decide_eq_true hm.1
                                constructor
                                · rw [← hrest]
                                  rfl
                                · simpa [cellForDirective, hrest] using h
                              · simp [h5] at h
                        · simp [h4] at h
                  · simp [h3] at h
            · simp [h2] at h
      · simp [h1] at h

/-- Soundness of the walk: a successful walk is a structural expansion. -/
private theorem expandNlGo_sound (env : List Presentation.ValueBinding)
    (gamma : List (Presentation.LeafId × Atom)) (claimId : String) :
    ∀ (fuel : Nat) (input out : List Char),
      expandNlGo env gamma claimId fuel input = .ok out → ExpandsNl env gamma input out
  | 0, input, out, h => by simp [expandNlGo] at h
  | fuel + 1, input, out, h => by
      cases input with
      | nil =>
          simp [expandNlGo] at h
          subst out
          exact ExpandsNl.nil
      | cons c rest =>
          by_cases hL : c = '{'
          · subst c
            cases rest with
            | nil =>
                -- `{` with no following body: the directive is unterminated
                simp [expandNlGo, takeDirective] at h
            | cons d rest' =>
                by_cases hL2 : d = '{'
                · subst d
                  simp [expandNlGo] at h
                  cases hg : expandNlGo env gamma claimId fuel rest' with
                  | error e => exfalso; simpa [Except.map, hg] using h
                  | ok tail =>
                      have hout : out = '{' :: tail := by simpa [Except.map, hg] using h.symm
                      subst out
                      exact ExpandsNl.escLeft (expandNlGo_sound env gamma claimId fuel rest' tail hg)
                · -- a directive whose body starts with a non-`{` character
                  cases htd : takeDirective (d :: rest') with
                  | none => simp [expandNlGo, hL2, htd] at h
                  | some pair =>
                      rcases pair with ⟨body, after⟩
                      simp [expandNlGo, hL2, htd] at h
                      cases hv : valueForDirective env body with
                      | some b =>
                          simp [hv] at h
                          cases hg : expandNlGo env gamma claimId fuel after with
                          | error e => exfalso; simpa [Except.map, hg] using h
                          | ok tail =>
                              have hout : out = (prettyTerm b.term).toList ++ tail := by simpa [Except.map, hg] using h.symm
                              subst out
                              have h' := expandNlGo_sound env gamma claimId fuel after tail hg
                              have hbody : body = b.name.val.toList := by
                                have hmv := find?_eq_some_implies_mem
                                  (fun b' : Presentation.ValueBinding =>
                                    decide (b'.name.val.toList = body)) hv
                                have hp : decide (b.name.val.toList = body) = true := hmv.1
                                exact (of_decide_eq_true hp).symm
                              have henv' : valueForDirective env b.name.val.toList = some b := by
                                rw [← hbody]
                                exact hv
                              have hb : ∀ x ∈ b.name.val.toList, x ≠ '}' := by
                                rw [← hbody]
                                exact takeDirective_no_close (d :: rest') body after htd
                              have hsplit : d :: rest' = body ++ '}' :: after :=
                                takeDirective_eq_some_implies_split (d :: rest') body after htd
                              have hhead : ∀ (c0 : Char) (cs0 : List Char), b.name.val.toList ≠ '{' :: cs0 := by
                                intro c0 cs0 hh
                                have hbval : b.name.val.toList = body := hbody.symm
                                rw [hbval] at hh
                                have hsplit'' : d :: rest' = '{' :: (cs0 ++ '}' :: after) := by
                                  rw [hh] at hsplit
                                  simpa using hsplit
                                exact hL2 (List.cons.inj hsplit'').1
                              rw [hsplit, hbody]
                              exact ExpandsNl.value henv' hb hhead h'
                      | none =>
                          cases hc : cellForDirective gamma body with
                          | none => simp [hv, hc] at h
                          | some cp =>
                              rcases cp with ⟨leaf, prop⟩
                              cases hd : cellDecimal? prop with
                              | none => simp [hv, hc, hd] at h
                              | some dec =>
                                  simp [hv, hc, hd] at h
                                  cases hg : expandNlGo env gamma claimId fuel after with
                                  | error e => exfalso; simpa [Except.map, hg] using h
                                  | ok tail =>
                                      have hout : out = (renderDecimal dec).toList ++ tail := by simpa [Except.map, hg] using h.symm
                                      subst out
                                      have h' := expandNlGo_sound env gamma claimId fuel after tail hg
                                      rcases cellForDirective_eq_some_iff hc with ⟨hbody, hgamma'⟩
                                      have hleaf : ∀ x ∈ leaf.val.toList, x ≠ '}' := by
                                        intro x hx
                                        exact takeDirective_no_close (d :: rest') body after htd x (by
                                          rw [hbody]
                                          exact List.mem_append.mpr (Or.inr hx))
                                      have hsplit : d :: rest' = body ++ '}' :: after :=
                                        takeDirective_eq_some_implies_split (d :: rest') body after htd
                                      have hvalue : valueForDirective env ("cell ".toList ++ leaf.val.toList) = none := by
                                        rw [← hbody]
                                        exact hv
                                      rw [hsplit, hbody]
                                      exact ExpandsNl.cell hgamma' hd hvalue hleaf h'
          · by_cases hR : c = '}'
            · subst c
              cases rest with
              | nil => simp [expandNlGo] at h
              | cons d rest' =>
                  by_cases hR2 : d = '}'
                  · subst d
                    simp [expandNlGo] at h
                    cases hg : expandNlGo env gamma claimId fuel rest' with
                    | error e => exfalso; simpa [Except.map, hg] using h
                    | ok tail =>
                        have hout : out = '}' :: tail := by simpa [Except.map, hg] using h.symm
                        subst out
                        exact ExpandsNl.escRight
                          (expandNlGo_sound env gamma claimId fuel rest' tail hg)
                  · -- `}` followed by a non-`}` is a stray close
                    simp [expandNlGo, hR2] at h
            · -- an ordinary character
              simp [expandNlGo, hL, hR] at h
              cases hg : expandNlGo env gamma claimId fuel rest with
              | error e => exfalso; simpa [Except.map, hg] using h
              | ok tail =>
                  have hout : out = c :: tail := by simpa [Except.map, hg] using h.symm
                  subst out
                  exact ExpandsNl.char c ⟨hL, hR⟩
                    (expandNlGo_sound env gamma claimId fuel rest tail hg)

/-- The walk's success output is a structural expansion. -/
theorem expandNl_sound {env gamma claimId text out}
    (h : expandNl env gamma claimId text = .ok out) :
    ExpandsNl env gamma text.toList out.toList := by
  unfold expandNl at h
  cases hgo : expandNlGo env gamma claimId (text.toList.length + 1) text.toList with
  | error e => exfalso; simp [Except.map, hgo] at h
  | ok chars =>
      simp [Except.map, hgo] at h
      subst out
      simpa [String.toList_ofList] using
        (expandNlGo_sound env gamma claimId (text.toList.length + 1) text.toList chars hgo)

/-- Completeness of the walk: every structural expansion is produced by the
walk, with the fuel large enough for the input. -/
private theorem expandNlGo_complete (env : List Presentation.ValueBinding)
    (gamma : List (Presentation.LeafId × Atom)) (claimId : String) :
    ∀ {input out : List Char} (h : ExpandsNl env gamma input out),
      ∀ fuel, input.length + 1 ≤ fuel → expandNlGo env gamma claimId fuel input = .ok out
  | _, _, ExpandsNl.nil, fuel, hfuel => by
      cases fuel with
      | zero => exfalso; simp at hfuel
      | succ fuel' => simp [expandNlGo]
  | _, _, @ExpandsNl.char _ _ c rest out hc hrest, fuel, hfuel => by
      cases fuel with
      | zero => exfalso; simp at hfuel
      | succ fuel' =>
          cases fuel' with
          | zero => exfalso; simp at hfuel
          | succ fuel'' =>
              have hlen : rest.length + 2 ≤ fuel'' + 2 := by simpa using hfuel
              have ih := expandNlGo_complete env gamma claimId hrest (fuel'' + 1) (by omega)
              by_cases hL : c = '{'
              · exfalso; exact hc.1 hL
              · by_cases hR : c = '}'
                · exfalso; exact hc.2 hR
                · simp [expandNlGo, Except.map, hL, hR, ih]
  | _, _, @ExpandsNl.escLeft _ _ rest out hrest, fuel, hfuel => by
      cases fuel with
      | zero => exfalso; simp at hfuel
      | succ fuel' =>
          cases fuel' with
          | zero => exfalso; simp at hfuel
          | succ fuel'' =>
              have hlen : rest.length + 3 ≤ fuel'' + 2 := by simpa using hfuel
              have ih := expandNlGo_complete env gamma claimId hrest (fuel'' + 1) (by omega)
              simp [expandNlGo, Except.map, ih]
  | _, _, @ExpandsNl.escRight _ _ rest out hrest, fuel, hfuel => by
      cases fuel with
      | zero => exfalso; simp at hfuel
      | succ fuel' =>
          cases fuel' with
          | zero => exfalso; simp at hfuel
          | succ fuel'' =>
              have hlen : rest.length + 3 ≤ fuel'' + 2 := by simpa using hfuel
              have ih := expandNlGo_complete env gamma claimId hrest (fuel'' + 1) (by omega)
              simp [expandNlGo, Except.map, ih]
  | _, _, @ExpandsNl.value _ _ b rest out henv hb hhead hrest, fuel, hfuel => by
      cases fuel with
      | zero => exfalso; simp at hfuel
      | succ fuel' =>
          cases fuel' with
          | zero => exfalso; simp at hfuel
          | succ fuel'' =>
              have hlen : rest.length + 1 ≤ fuel'' + 1 := by
                simp at hfuel
                omega
              have ih := expandNlGo_complete env gamma claimId hrest (fuel'' + 1) hlen
              have htd : takeDirective (b.name.val.toList ++ '}' :: rest) = some (b.name.val.toList, rest) :=
                takeDirective_roundtrip hb
              cases hnl : b.name.val.toList with
              | nil =>
                  have htd' : takeDirective ('}' :: rest) = some ([], rest) := by simpa [hnl] using htd
                  have henv' : valueForDirective env [] = some b := by simpa [hnl] using henv
                  simp [expandNlGo, Except.map, hnl]
                  simp [htd', henv', ih]
              | cons c cs =>
                  have hc : c ≠ '{' := by
                    intro hc'
                    exact hhead c cs (by rw [hnl, hc'])
                  have htd' : takeDirective (c :: (cs ++ '}' :: rest)) = some (c :: cs, rest) := by
                    simpa [hnl] using htd
                  have henv' : valueForDirective env (c :: cs) = some b := by simpa [hnl] using henv
                  simp [expandNlGo, Except.map, hnl, hc]
                  simp [htd', henv', ih]
  | _, _, @ExpandsNl.cell _ _ leaf prop d rest out hgamma hdec hvalue hleaf hrest, fuel, hfuel => by
      cases fuel with
      | zero => exfalso; simp at hfuel
      | succ fuel' =>
          cases fuel' with
          | zero => exfalso; simp at hfuel
          | succ fuel'' =>
              have hlen : rest.length + 1 ≤ fuel'' + 1 := by
                simp at hfuel
                omega
              have ih := expandNlGo_complete env gamma claimId hrest (fuel'' + 1) hlen
              have htd : takeDirective ("cell ".toList ++ leaf.val.toList ++ '}' :: rest) =
                  some ("cell ".toList ++ leaf.val.toList, rest) := by
                apply takeDirective_roundtrip
                intro x hx
                simp at hx
                rcases hx with hx | hx
                · subst x; simp
                · rcases hx with hx | hx
                  · subst x; simp
                  · rcases hx with hx | hx
                    · subst x; simp
                    · rcases hx with hx | hx
                      · subst x; simp
                      · exact hleaf x hx
              have htd' : takeDirective ('c' :: 'e' :: 'l' :: 'l' :: ' ' :: (leaf.val.toList ++ '}' :: rest)) =
                  some ('c' :: 'e' :: 'l' :: 'l' :: ' ' :: leaf.val.toList, rest) := by
                simpa using htd
              have hgamma' : cellForDirective gamma ('c' :: 'e' :: 'l' :: 'l' :: ' ' :: leaf.val.toList) =
                  some (leaf, prop) := by
                simpa using hgamma
              have hvalue' : valueForDirective env ('c' :: 'e' :: 'l' :: 'l' :: ' ' :: leaf.val.toList) = none := by
                simpa using hvalue
              simp [expandNlGo, Except.map, htd']
              simp [hgamma', hdec, hvalue', ih]

/-- Every expansion the relation describes is produced by the walk. -/
theorem expandNl_complete {env gamma claimId text out}
    (h : ExpandsNl env gamma text.toList out.toList) :
    expandNl env gamma claimId text = .ok out := by
  unfold expandNl
  have hgo := expandNlGo_complete env gamma claimId h (text.toList.length + 1) (by omega)
  simp [hgo, Except.map, String.ofList_toList]

/-! ### Simultaneous substitution over declarations -/

mutual
  def substSupportTerm (bindings : List Presentation.ValueBinding) :
      Presentation.SupportTerm → Presentation.SupportTerm
    | .leaf id => .leaf id
    | .rule rule subst premises discharges holes assurance =>
        .rule rule
          (subst.map fun pair => (pair.1, substituteValueTerm bindings pair.2))
          (substSupportTerms bindings premises)
          (substSupportDischarges bindings discharges) holes assurance
  def substSupportTerms (bindings : List Presentation.ValueBinding) :
      Presentation.SupportTerms → Presentation.SupportTerms
    | .nil => .nil
    | .cons term rest =>
        .cons (substSupportTerm bindings term) (substSupportTerms bindings rest)
  def substSupportDischarges (bindings : List Presentation.ValueBinding) :
      Presentation.Discharges → Presentation.Discharges
    | .nil => .nil
    | .cons question term rest =>
        .cons question (substSupportTerm bindings term) (substSupportDischarges bindings rest)
end

def substArgInstantiation (bindings : List Presentation.ValueBinding) :
    Presentation.ArgInstantiation → Presentation.ArgInstantiation
  | .explicitTheta term => .explicitTheta (substSupportTerm bindings term)
  | inferred@(.inferTheta _ _ _ _ _) => inferred

/-- Substitute the value environment over one declaration: leaves and claims
in their propositions, explicit support terms recursively (never inside opaque
certificate payloads), comparison conclusions, and nothing else. -/
def substDecl (bindings : List Presentation.ValueBinding) :
    Presentation.Decl → Presentation.Decl
  | .leaf leaf => .leaf { leaf with prop := substituteValueAtom bindings leaf.prop }
  | .claim claim => .claim { claim with formal := substituteValueAtom bindings claim.formal }
  | .arg argument =>
      .arg { argument with instantiation := substArgInstantiation bindings argument.instantiation }
  | .comparison comparison =>
      .comparison { comparison with conclusion := substituteValueAtom bindings comparison.conclusion }
  | attack@(.attack _) => attack
  | status@(.status _) => status
  | group@(.group _) => group

/-! ### The structural declaration relation -/

inductive DeclsExpand (env : List Presentation.ValueBinding)
    (gamma : List (Presentation.LeafId × Atom)) : List Decl → List Decl → Prop where
  | nil : DeclsExpand env gamma [] []
  | leaf {leaf : Leaf} {ds ts : List Decl} :
      DeclsExpand env gamma ds ts →
      DeclsExpand env gamma (.leaf leaf :: ds)
        (.leaf { leaf with prop := substituteValueAtom env leaf.prop } :: ts)
  | claim {claim : Claim} {nl' : String} {ds ts : List Decl} :
      ExpandsNl env gamma claim.nl.toList nl'.toList →
      DeclsExpand env gamma ds ts →
      DeclsExpand env gamma (.claim claim :: ds)
        (.claim { claim with formal := substituteValueAtom env claim.formal, nl := nl' } :: ts)
  | arg {argument : Arg} {ds ts : List Decl} :
      DeclsExpand env gamma ds ts →
      DeclsExpand env gamma (.arg argument :: ds)
        (.arg { argument with instantiation := substArgInstantiation env argument.instantiation } :: ts)
  | comparison {comparison : Comparison} {nl' : String} {ds ts : List Decl} :
      ExpandsNl env gamma comparison.claim.nlRaw.toList nl'.toList →
      DeclsExpand env gamma ds ts →
      DeclsExpand env gamma (.comparison comparison :: ds)
        (.comparison { comparison with
          conclusion := substituteValueAtom env comparison.conclusion,
          claim := { comparison.claim with nlRaw := nl' } } :: ts)
  | attack {attack : SurfaceAttack} {ds ts : List Decl} :
      DeclsExpand env gamma ds ts →
      DeclsExpand env gamma (.attack attack :: ds) (.attack attack :: ts)
  | status {id : PropId} {ds ts : List Decl} :
      DeclsExpand env gamma ds ts →
      DeclsExpand env gamma (.status id :: ds) (.status id :: ts)
  | group {group : DupGroup} {ds ts : List Decl} :
      DeclsExpand env gamma ds ts →
      DeclsExpand env gamma (.group group :: ds) (.group group :: ts)

/-- The independent value-expansion relation: the target is the source with
every value-name nullary occurrence replaced by its binding right-hand side
(simultaneously, non-recursively), every claim's prose interpolated, and the
binding table cleared. -/
inductive ExpandsValues (source target : Presentation.Program) : Prop where
  | intro {env : List Presentation.ValueBinding}
      {gamma : List (Presentation.LeafId × Atom)}
      (henv : env = source.valueBindings)
      (hgamma : gamma = declaredLeaves { source with decls := source.decls.map (substDecl env) })
      (hbindings : target.valueBindings = [])
      (hartifact : target.artifact = source.artifact)
      (hdigest : target.digest = source.digest)
      (hpolicy : target.policy = source.policy)
      (hbackends : target.backends = source.backends)
      (hdecls : DeclsExpand env gamma source.decls target.decls) :
      ExpandsValues source target

/-! ### The executable pass -/

private def firstDuplicateNameAux :
    List Presentation.ValueName → List Presentation.ValueName →
      Option Presentation.ValueName
  | [], _ => none
  | name :: rest, seen =>
      if name ∈ seen then some name
      else firstDuplicateNameAux rest (name :: seen)

/-- The first repeated value name in declaration order. -/
def duplicateName? (bindings : List Presentation.ValueBinding) :
    Option Presentation.ValueName :=
  firstDuplicateNameAux (bindings.map (·.name)) []

def valueBindingErrors (policy : Presentation.Policy) (program : Presentation.Program) :
    Option Surface.Error :=
  let bindings := program.valueBindings
  match duplicateName? bindings with
  | some name => some (.duplicateValueName name)
  | none =>
  match bindings.find? (fun b => decide (b.name.val = "cell")) with
  | some binding => some (.invalidValueBinding binding.name)
  | none =>
  match bindings.find? (fun b =>
      policy.sigma.cons.any (fun con => decide (con.sym.name = b.name.val))) with
  | some binding => some (.invalidValueBinding binding.name)
  | none =>
  match bindings.find? (fun b => (Lara.Sigma.sortOf policy.sigma b.term).isNone) with
  | some binding => some (.invalidValueBinding binding.name)
  | none => none

namespace Renaming

def renameValueBindingError (ρg : Binding.GlobalRenaming) : Surface.Error → Surface.Error
  | .duplicateValueName name => .duplicateValueName (ρg.valueName name)
  | .invalidValueBinding name => .invalidValueBinding (ρg.valueName name)
  | error => error

private theorem firstDuplicateNameAux_map (f : Presentation.ValueName → Presentation.ValueName)
    (injective : Function.Injective f) (names seen : List Presentation.ValueName) :
    firstDuplicateNameAux (names.map f) (seen.map f) =
      (firstDuplicateNameAux names seen).map f := by
  induction names generalizing seen with
  | nil => rfl
  | cons name rest ih =>
      simp only [List.map_cons, firstDuplicateNameAux]
      have member : f name ∈ seen.map f ↔ name ∈ seen := by
        simp [injective.eq_iff]
      by_cases present : name ∈ seen
      · have mapped : f name ∈ seen.map f := member.mpr present
        simp [present, mapped]
      · have mapped : f name ∉ seen.map f := by
          simpa [member] using present
        rw [if_neg mapped, if_neg present]
        simpa using ih (name :: seen)

theorem duplicateName?_rename (ρg : Binding.GlobalRenaming)
    (bindings : List Presentation.ValueBinding) :
    duplicateName? (bindings.map fun binding =>
        { binding with name := ρg.valueName binding.name }) =
      (duplicateName? bindings).map ρg.valueName := by
  unfold duplicateName?
  simpa [List.map_map, Function.comp_def] using
    firstDuplicateNameAux_map ρg.valueName ρg.valueName_injective
      (bindings.map (·.name)) []

private theorem find?_map_eq_map_find? {α β} (f : α → β)
    (source : α → Bool) (target : β → Bool) (items : List α)
    (predicate : ∀ item, target (f item) = source item) :
    (items.map f).find? target = (items.find? source).map f := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.map_cons, List.find?_cons]
      rw [predicate item]
      by_cases selected : source item = true
      · simp [selected]
      · simp [selected, ih]

theorem valueBindingErrors_rename (sound : RenamingSound ρg program policy) :
    valueBindingErrors (Binding.renamePolicy ρg policy)
        (Binding.renameProgram ρg program) =
      (valueBindingErrors policy program).map (renameValueBindingError ρg) := by
  let renameBinding : Presentation.ValueBinding → Presentation.ValueBinding :=
    fun binding => { binding with name := ρg.valueName binding.name }
  have duplicate :
      duplicateName? (program.valueBindings.map renameBinding) =
        (duplicateName? program.valueBindings).map ρg.valueName := by
    exact duplicateName?_rename ρg program.valueBindings
  have reservedPredicate : ∀ binding : Presentation.ValueBinding,
      decide ((renameBinding binding).name.val = "cell") =
        decide (binding.name.val = "cell") := by
    intro binding
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [ρg.valueName_coherent]
    change Binding.renameText ρg binding.name.val = "cell" ↔
      binding.name.val = "cell"
    constructor
    · intro equal
      apply Binding.renameText_injective ρg
      exact equal.trans sound.cell_spelling.symm
    · intro equal
      rw [equal, sound.cell_spelling]
  have reserved :
      (program.valueBindings.map renameBinding).find?
          (fun binding => decide (binding.name.val = "cell")) =
        (program.valueBindings.find?
          (fun binding => decide (binding.name.val = "cell"))).map renameBinding := by
    exact find?_map_eq_map_find? renameBinding _ _ _ reservedPredicate
  have collisionPredicate : ∀ binding : Presentation.ValueBinding,
      policy.sigma.cons.any
          (fun con => decide (con.sym.name = (renameBinding binding).name.val)) =
        policy.sigma.cons.any
          (fun con => decide (con.sym.name = binding.name.val)) := by
    intro binding
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨con, member, equal⟩
      refine ⟨con, member, ?_⟩
      rw [ρg.valueName_coherent] at equal
      change con.sym.name = Binding.renameText ρg binding.name.val at equal
      apply Binding.renameText_injective ρg
      rw [sound.sigma con member]
      exact equal
    · rintro ⟨con, member, equal⟩
      refine ⟨con, member, ?_⟩
      change con.sym.name = (ρg.valueName binding.name).val
      rw [ρg.valueName_coherent]
      change con.sym.name = Binding.renameText ρg binding.name.val
      rw [← equal, sound.sigma con member]
  have collision :
      (program.valueBindings.map renameBinding).find?
          (fun binding => policy.sigma.cons.any
            (fun con => decide (con.sym.name = binding.name.val))) =
        (program.valueBindings.find?
          (fun binding => policy.sigma.cons.any
            (fun con => decide (con.sym.name = binding.name.val)))).map renameBinding := by
    exact find?_map_eq_map_find? renameBinding _ _ _ collisionPredicate
  have sorting :
      (program.valueBindings.map renameBinding).find?
          (fun binding => (Lara.Sigma.sortOf policy.sigma binding.term).isNone) =
        (program.valueBindings.find?
          (fun binding => (Lara.Sigma.sortOf policy.sigma binding.term).isNone)).map
            renameBinding := by
    exact find?_map_eq_map_find? renameBinding _ _ _ (fun _ => rfl)
  unfold valueBindingErrors
  simp only [Binding.renameProgram, Binding.renamePolicy]
  rw [duplicate, reserved, collision, sorting]
  cases duplicateName? program.valueBindings <;>
    cases program.valueBindings.find?
      (fun binding => decide (binding.name.val = "cell")) <;>
    cases program.valueBindings.find?
      (fun binding => policy.sigma.cons.any
        (fun con => decide (con.sym.name = binding.name.val))) <;>
    cases program.valueBindings.find?
      (fun binding => (Lara.Sigma.sortOf policy.sigma binding.term).isNone) <;>
    simp [renameBinding, renameValueBindingError]

theorem valueBindingErrors_some_cases
    (h : valueBindingErrors policy program = some error) :
    (∃ name, error = .duplicateValueName name) ∨
      (∃ name, error = .invalidValueBinding name) := by
  unfold valueBindingErrors at h
  dsimp only at h
  cases hdup : duplicateName? program.valueBindings with
  | some name => simp [hdup] at h; exact Or.inl ⟨name, h.symm⟩
  | none =>
    simp only [hdup] at h
    cases hreserved : program.valueBindings.find?
        (fun b => decide (b.name.val = "cell")) with
    | some binding =>
      simp [hreserved] at h
      exact Or.inr ⟨binding.name, h.symm⟩
    | none =>
      simp only [hreserved] at h
      cases hcollision : program.valueBindings.find? (fun b =>
          policy.sigma.cons.any fun con => decide (con.sym.name = b.name.val)) with
      | some binding =>
        simp [hcollision] at h
        exact Or.inr ⟨binding.name, h.symm⟩
      | none =>
        simp only [hcollision] at h
        cases hsort : program.valueBindings.find?
            (fun b => (Lara.Sigma.sortOf policy.sigma b.term).isNone) with
        | some binding =>
          simp [hsort] at h
          exact Or.inr ⟨binding.name, h.symm⟩
        | none => simp [hsort] at h

end Renaming

private def firstInvalidClaimId? (sigma : Lara.Sigma.Sigma)
    (declarations : List Presentation.Decl) : Option String :=
  declarations.findSome? fun declaration =>
    match declaration with
    | .claim claim =>
        if !Lara.Sigma.wsAtom sigma claim.formal then some claim.id.val else none
    | _ => none

def claimFormalErrors (policy : Presentation.Policy)
    (bindings : List Presentation.ValueBinding) (substituted : Presentation.Program) :
    Option Surface.Error :=
  if bindings.isEmpty then none
  else
    match firstInvalidClaimId? policy.sigma substituted.decls with
    | some claimId => some (.invalidValueBinding ⟨claimId⟩)
    | none => none

def expandDeclNls (env : List Presentation.ValueBinding)
    (gamma : List (Presentation.LeafId × Atom)) : List Decl → Except Surface.Error (List Decl)
  | [] => .ok []
  | .claim claim :: rest => do
      let prose ← expandNl env gamma claim.id.val claim.nl
      let tail ← expandDeclNls env gamma rest
      .ok (.claim { claim with nl := prose } :: tail)
  | .comparison comparison :: rest => do
      let prose ← expandNl env gamma comparison.claim.id.val comparison.claim.nlRaw
      let tail ← expandDeclNls env gamma rest
      .ok (.comparison { comparison with claim := { comparison.claim with nlRaw := prose } } :: tail)
  | declaration :: rest => do
      let tail ← expandDeclNls env gamma rest
      .ok (declaration :: tail)

/-- Expand (and consume) the value-binding table of a program, with the
production error precedence: duplicate names, the reserved `cell` name,
constructor collisions, non-sorting right-hand sides, post-substitution claim
formals, then prose interpolation. -/
def expandValues (policy : Presentation.Policy) (program : Presentation.Program) :
    Except Surface.Error Presentation.Program :=
  match valueBindingErrors policy program with
  | some error => .error error
  | none =>
      let bindings := program.valueBindings
      let substituted : Presentation.Program :=
        { program with decls := program.decls.map (substDecl bindings) }
      match claimFormalErrors policy bindings substituted with
      | some error => .error error
      | none =>
          let gamma := declaredLeaves substituted
          match expandDeclNls bindings gamma substituted.decls with
          | .error error => .error error
          | .ok decls => .ok { substituted with valueBindings := [], decls := decls }

namespace Renaming

/-- Remove prose from one semantic declaration while preserving every
executable field. -/
def eraseDeclNl : Presentation.Decl → Presentation.Decl
  | .claim claim => .claim { claim with nl := "" }
  | .comparison comparison =>
      .comparison
        { comparison with
          claim := { comparison.claim with nlRaw := "" } }
  | declaration => declaration

/-- Remove all claim prose from a semantic program. -/
def eraseProgramNl (program : Presentation.Program) : Presentation.Program :=
  { program with decls := program.decls.map eraseDeclNl }

/-- Renamed semantic programs agree on every executable field; expanded prose
is intentionally outside this relation because interpolation can synthesize
directive-shaped text. -/
def SemanticProgramRelated (ρg : Binding.GlobalRenaming)
    (source target : Presentation.Program) : Prop :=
  eraseProgramNl target = eraseProgramNl (Binding.renameProgram ρg source)

/-- Relate two exception computations with pass-specific error and success
relations. -/
inductive RenamedExcept (errorRelated : ε → ε' → Prop)
    (valueRelated : α → β → Prop) :
    Except ε α → Except ε' β → Prop where
  | error {source target} :
      errorRelated source target →
      RenamedExcept errorRelated valueRelated (.error source) (.error target)
  | ok {source target} :
      valueRelated source target →
      RenamedExcept errorRelated valueRelated (.ok source) (.ok target)

/-- Exact value-expansion error provenance. Invalid-binding payloads retain
whether they name a binding, a claim, or an interpolated directive body. -/
inductive ExpandValuesErrorRelated (ρg : Binding.GlobalRenaming) :
    Surface.Error → Surface.Error → Prop where
  | duplicateBinding (name : Presentation.ValueName) :
      ExpandValuesErrorRelated ρg
        (.duplicateValueName name) (.duplicateValueName (ρg.valueName name))
  | invalidBinding (name : Presentation.ValueName) :
      ExpandValuesErrorRelated ρg
        (.invalidValueBinding name) (.invalidValueBinding (ρg.valueName name))
  | invalidClaim (claimId : Presentation.PropId) :
      ExpandValuesErrorRelated ρg
        (.invalidValueBinding ⟨claimId.val⟩)
        (.invalidValueBinding ⟨(ρg.prop claimId).val⟩)
  | invalidDirective (body : List Char) :
      ExpandValuesErrorRelated ρg
        (.invalidValueBinding ⟨String.ofList body⟩)
        (.invalidValueBinding
          ⟨String.ofList (Binding.renameDirective ρg body)⟩)

private theorem stripPrefixChars_some_prefix_local
    (found : Binding.stripPrefixChars expected input = some suffix) :
    expected <+: input := by
  induction expected generalizing input suffix with
  | nil => simp
  | cons expected rest ih =>
      cases input with
      | nil => simp [Binding.stripPrefixChars] at found
      | cons actual tail =>
          unfold Binding.stripPrefixChars at found
          split at found
          · subst actual
            exact List.cons_prefix_cons.mpr ⟨rfl, ih found⟩
          · simp at found

private theorem valueDirectiveCandidate_mem
    (binding : Presentation.ValueBinding)
    (member : binding ∈ program.valueBindings) :
    binding.name.val.toList ∈ programDirectiveBodies program := by
  simp only [programDirectiveBodies, List.mem_append, List.mem_map]
  have nameMember : binding.name ∈ valueNames program := by
    unfold valueNames
    exact List.mem_map.mpr ⟨binding, member, rfl⟩
  exact Or.inl (Or.inr ⟨binding.name, nameMember, rfl⟩)

private theorem cellDirectiveCandidate_mem
    (leaf : Presentation.LeafId) (member : leaf ∈ leafIds program) :
    "cell ".toList ++ leaf.val.toList ∈ programDirectiveBodies program := by
  simp only [programDirectiveBodies, List.mem_append, List.mem_map]
  exact Or.inr ⟨leaf, member, rfl⟩

private theorem renameDirective_valueName
    (sound : RenamingSound ρg program policy)
    (binding : Presentation.ValueBinding)
    (member : binding ∈ program.valueBindings) :
    Binding.renameDirective ρg binding.name.val.toList =
      (ρg.valueName binding.name).val.toList := by
  unfold Binding.renameDirective
  cases found : Binding.stripPrefixChars "cell ".toList
      binding.name.val.toList with
  | none => simp [Binding.renameText]
  | some suffix =>
      have hasPrefix := stripPrefixChars_some_prefix_local found
      have starts : binding.name.val.startsWith "cell " = true :=
        String.startsWith_string_iff.mpr hasPrefix
      have nameMember : binding.name ∈ valueNames program := by
        unfold valueNames
        exact List.mem_map.mpr ⟨binding, member, rfl⟩
      rw [sound.noCellValues binding.name nameMember] at starts
      contradiction

private theorem renameDirective_cellLeaf
    (ρg : Binding.GlobalRenaming) (leaf : Presentation.LeafId) :
    Binding.renameDirective ρg
        ("cell ".toList ++ leaf.val.toList) =
      "cell ".toList ++ (ρg.leaf leaf).val.toList := by
  simp [Binding.renameDirective, Binding.stripPrefixChars,
    Binding.renameText]

private theorem renameDirective_eq_iff
    (sound : RenamingSound ρg program policy)
    (left : List Char) (leftMember : left ∈ programDirectiveBodies program)
    (right : List Char) (rightMember : right ∈ programDirectiveBodies program) :
    Binding.renameDirective ρg left = Binding.renameDirective ρg right ↔
      left = right := by
  constructor
  · exact sound.directiveInjective left leftMember right rightMember
  · intro equal
    cases equal
    rfl

private theorem find?_map_eq_map_find?_of_mem
    (mapValue : α → β) (sourcePredicate : α → Bool)
    (targetPredicate : β → Bool) (values : List α)
    (predicateEq : ∀ value ∈ values,
      targetPredicate (mapValue value) = sourcePredicate value) :
    (values.map mapValue).find? targetPredicate =
      (values.find? sourcePredicate).map mapValue := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.map_cons, List.find?_cons]
      rw [predicateEq value (by simp)]
      by_cases selected : sourcePredicate value = true
      · simp [selected]
      · simp [selected, ih (fun candidate member =>
          predicateEq candidate (by simp [member]))]

private theorem valueForDirective_rename
    (sound : RenamingSound ρg program policy)
    (body : List Char) (bodyMember : body ∈ programDirectiveBodies program) :
    valueForDirective
        ((Binding.renameProgram ρg program).valueBindings)
        (Binding.renameDirective ρg body) =
      (valueForDirective program.valueBindings body).map
        (fun binding => { binding with name := ρg.valueName binding.name }) := by
  unfold valueForDirective
  simp only [Binding.renameProgram]
  apply find?_map_eq_map_find?_of_mem
  intro binding bindingMember
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [← renameDirective_valueName sound binding bindingMember]
  exact renameDirective_eq_iff sound _
    (valueDirectiveCandidate_mem binding bindingMember) _ bodyMember

private theorem cellForDirective_rename
    (sound : RenamingSound ρg program policy)
    (gamma : List (Presentation.LeafId × Atom))
    (gammaLeaves : ∀ entry ∈ gamma, entry.1 ∈ leafIds program)
    (body : List Char) (bodyMember : body ∈ programDirectiveBodies program) :
    cellForDirective
        (gamma.map fun entry => (ρg.leaf entry.1, entry.2))
        (Binding.renameDirective ρg body) =
      (cellForDirective gamma body).map fun entry =>
        (ρg.leaf entry.1, entry.2) := by
  cases sourceFound : cellForDirective gamma body with
  | some sourceEntry =>
      obtain ⟨leaf, atom⟩ := sourceEntry
      have sourceShape := cellForDirective_eq_some_iff sourceFound
      have transport := find?_map_eq_map_find?_of_mem
        (fun entry : Presentation.LeafId × Atom =>
          (ρg.leaf entry.1, entry.2))
        (fun entry : Presentation.LeafId × Atom =>
          decide (entry.1.val.toList = leaf.val.toList))
        (fun entry : Presentation.LeafId × Atom =>
          decide (entry.1.val.toList = (ρg.leaf leaf).val.toList))
        gamma (by
          intro entry entryMember
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          constructor
          · intro equal
            have mappedVal : (ρg.leaf entry.1).val =
                (ρg.leaf leaf).val := by
              simpa using congrArg String.ofList equal
            have mappedId : ρg.leaf entry.1 = ρg.leaf leaf :=
              congrArg Presentation.LeafId.mk mappedVal
            exact congrArg (fun id : Presentation.LeafId => id.val.toList)
              (ρg.leaf_injective mappedId)
          · intro equal
            have sourceVal : entry.1.val = leaf.val := by
              simpa using congrArg String.ofList equal
            have sourceId : entry.1 = leaf :=
              congrArg Presentation.LeafId.mk sourceVal
            exact congrArg (fun id : Presentation.LeafId => id.val.toList)
              (congrArg ρg.leaf sourceId))
      have sourceCandidate :
          gamma.find? (fun entry =>
            decide (entry.1.val.toList = leaf.val.toList)) =
            some (leaf, atom) := by
        simpa [cellForDirective] using sourceShape.2
      rw [sourceCandidate] at transport
      rw [sourceShape.1, renameDirective_cellLeaf]
      simpa [cellForDirective] using transport
  | none =>
      cases targetFound : cellForDirective
          (gamma.map fun entry => (ρg.leaf entry.1, entry.2))
          (Binding.renameDirective ρg body) with
      | none => rfl
      | some targetEntry =>
          have targetShape := cellForDirective_eq_some_iff targetFound
          have targetFoundCandidate := targetFound
          rw [targetShape.1] at targetFoundCandidate
          have targetMember : targetEntry ∈
              gamma.map (fun entry => (ρg.leaf entry.1, entry.2)) := by
            apply List.mem_of_find?_eq_some
            simpa [cellForDirective] using targetFoundCandidate
          obtain ⟨sourceEntry, sourceMember, rfl⟩ :=
            List.mem_map.mp targetMember
          have sourceLeafMember := gammaLeaves sourceEntry sourceMember
          have candidateMember :=
            cellDirectiveCandidate_mem sourceEntry.1 sourceLeafMember
          have targetBodyEq :
              Binding.renameDirective ρg body =
                Binding.renameDirective ρg
                  ("cell ".toList ++ sourceEntry.1.val.toList) := by
            rw [renameDirective_cellLeaf]
            exact targetShape.1
          have sourceBodyEq :
              body = "cell ".toList ++ sourceEntry.1.val.toList :=
            (renameDirective_eq_iff sound body bodyMember _ candidateMember).mp
              targetBodyEq
          have sourceIsSome : (cellForDirective gamma body).isSome := by
            rw [sourceBodyEq]
            apply List.find?_isSome.mpr
            refine ⟨sourceEntry, sourceMember, ?_⟩
            simp
          simp [sourceFound] at sourceIsSome

private theorem validateNlGo_directive_step
    (env : List Presentation.ValueBinding)
    (gamma : List (Presentation.LeafId × Atom)) (claimId : String)
    (fuel : Nat) (body after : List Char)
    (headFresh : body.head? ≠ some '{') (closeFresh : '}' ∉ body) :
    validateNlGo env gamma claimId (fuel + 1)
        ('{' :: (body ++ '}' :: after)) =
      match valueForDirective env body with
      | some _ => validateNlGo env gamma claimId fuel after
      | none =>
          match cellForDirective gamma body with
          | some (_, prop) =>
              match cellDecimal? prop with
              | some _ => validateNlGo env gamma claimId fuel after
              | none => .error (.invalidValueBinding ⟨String.ofList body⟩)
          | none => .error (.invalidValueBinding ⟨String.ofList body⟩) := by
  have taken : takeDirective (body ++ '}' :: after) = some (body, after) :=
    takeDirective_roundtrip (by
      intro char member equal
      subst char
      exact closeFresh member)
  cases shape : body with
  | nil =>
      subst body
      rfl
  | cons head tail =>
      subst body
      have headNotOpen : head ≠ '{' := by
        intro equal
        apply headFresh
        simp [equal]
      have takenCons :
          takeDirective (head :: (tail ++ '}' :: after)) =
            some (head :: tail, after) := by
        simpa using taken
      simp [validateNlGo, headNotOpen, takenCons]

private theorem renameNlChars_head?
    (ρg : Binding.GlobalRenaming) (fuel : Nat) (chars : List Char) :
    (Binding.renameNlChars ρg fuel chars).head? = chars.head? := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases chars with
      | nil => rfl
      | cons char rest =>
          by_cases openBrace : char = '{'
          · subst char
            cases rest with
            | nil => rfl
            | cons second tail =>
                by_cases escaped : second = '{'
                · subst second
                  rfl
                · cases taken : Binding.takeNlDirective (second :: tail) <;>
                    simp [Binding.renameNlChars, escaped, taken]
          · by_cases closeBrace : char = '}'
            · subst char
              cases rest with
              | nil => rfl
              | cons second tail =>
                  by_cases escaped : second = '}'
                  · subst second
                    rfl
                  · simp [Binding.renameNlChars, escaped]
            · simp [Binding.renameNlChars, openBrace, closeBrace]

private theorem validateNlGo_stray_close
    (env : List Presentation.ValueBinding)
    (gamma : List (Presentation.LeafId × Atom)) (claimId : String)
    (fuel : Nat) (rest : List Char) (headFresh : rest.head? ≠ some '}') :
    validateNlGo env gamma claimId (fuel + 1) ('}' :: rest) =
      .error (.invalidValueBinding ⟨claimId⟩) := by
  cases shape : rest with
  | nil => rfl
  | cons head tail =>
      have headNotClose : head ≠ '}' := by
        intro equal
        apply headFresh
        simp [shape, equal]
      simp [validateNlGo, shape, headNotClose]

/-- Validation of one fuel-bounded prose fragment commutes with a sound
global renaming.  The success payload is deliberately erased: only the exact
failure provenance is retained. -/
private theorem validateNlGo_rename_related
    (sound : RenamingSound ρg program policy)
    (gamma : List (Presentation.LeafId × Atom))
    (gammaLeaves : ∀ entry ∈ gamma, entry.1 ∈ leafIds program)
    (claimId : Presentation.PropId) :
    ∀ fuel chars,
      chars.length < fuel →
      (∀ body ∈ nlDirectiveBodiesFuel fuel chars,
        body ∈ programNlDirectiveBodies program) →
      ∀ targetFuel,
        (Binding.renameNlChars ρg fuel chars).length < targetFuel →
        RenamedExcept (ExpandValuesErrorRelated ρg) (fun _ _ => True)
          (validateNlGo program.valueBindings gamma claimId.val fuel chars)
          (validateNlGo
            (Binding.renameProgram ρg program).valueBindings
            (gamma.map fun entry => (ρg.leaf entry.1, entry.2))
            (ρg.prop claimId).val targetFuel
            (Binding.renameNlChars ρg fuel chars)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro chars sourceBound
      omega
  | succ fuel ih =>
      intro chars sourceBound bodyInventory targetFuel targetBound
      cases targetFuel with
      | zero => omega
      | succ targetFuel =>
        cases chars with
        | nil =>
            exact RenamedExcept.ok trivial
        | cons char rest =>
          by_cases openBrace : char = '{'
          · subst char
            cases rest with
            | nil =>
                exact RenamedExcept.error
                  (ExpandValuesErrorRelated.invalidClaim claimId)
            | cons second tail =>
              by_cases escaped : second = '{'
              · subst second
                have tailBound : tail.length < fuel := by
                  simp only [List.length_cons] at sourceBound
                  omega
                have tailInventory :
                    ∀ body ∈ nlDirectiveBodiesFuel fuel tail,
                      body ∈ programNlDirectiveBodies program := by
                  intro body member
                  exact bodyInventory body (by
                    simpa [nlDirectiveBodiesFuel] using member)
                have targetTailBound :
                    (Binding.renameNlChars ρg fuel tail).length <
                      targetFuel := by
                  simp only [Binding.renameNlChars, List.length_cons]
                    at targetBound
                  omega
                simpa [validateNlGo, Binding.renameNlChars] using
                  ih tail tailBound tailInventory targetFuel targetTailBound
              · cases taken : takeDirective (second :: tail) with
                | none =>
                    have bindingTaken :
                        Binding.takeNlDirective (second :: tail) = none := by
                      rw [← takeDirective_eq_takeNlDirective_local]
                      exact taken
                    simpa [validateNlGo, Binding.renameNlChars, escaped,
                      taken, bindingTaken] using
                      (RenamedExcept.error
                        (ExpandValuesErrorRelated.invalidClaim
                          (ρg := ρg) claimId))
                | some pair =>
                  obtain ⟨body, after⟩ := pair
                  have bindingTaken :
                      Binding.takeNlDirective (second :: tail) =
                        some (body, after) := by
                    rw [← takeDirective_eq_takeNlDirective_local]
                    exact taken
                  have afterShorter :=
                    takeDirective_after_length_lt_early
                      (second :: tail) body after taken
                  have afterBound : after.length < fuel := by
                    simp only [List.length_cons] at sourceBound afterShorter
                    omega
                  have bodyMemberNl :
                      body ∈ programNlDirectiveBodies program := by
                    exact bodyInventory body (by
                      simp [nlDirectiveBodiesFuel, escaped, taken])
                  have bodyMember : body ∈ programDirectiveBodies program := by
                    simp [programDirectiveBodies, bodyMemberNl]
                  have afterInventory :
                      ∀ candidate ∈ nlDirectiveBodiesFuel fuel after,
                        candidate ∈ programNlDirectiveBodies program := by
                    intro candidate member
                    exact bodyInventory candidate (by
                      simp [nlDirectiveBodiesFuel, escaped, taken, member])
                  let renamedBody := Binding.renameDirective ρg body
                  let renamedAfter := Binding.renameNlChars ρg fuel after
                  have bodyFresh :
                      renamedBody.head? ≠ some '{' ∧ '}' ∉ renamedBody :=
                    sound.directiveDelimiterFresh body bodyMemberNl
                  have sourceNoClose : '}' ∉ body :=
                    (by
                      intro member
                      exact takeDirective_no_close
                        (second :: tail) body after taken '}' member rfl)
                  have sourceHeadFresh : body.head? ≠ some '{' := by
                    have split := takeDirective_eq_some_implies_split
                      (second :: tail) body after taken
                    intro headOpen
                    cases body with
                    | nil => simp at headOpen
                    | cons head bodyTail =>
                        have headEq : head = '{' := by
                          simpa using headOpen
                        have secondEq : second = head := by
                          simpa using congrArg List.head? split
                        have secondOpen : second = '{' := by
                          exact secondEq.trans headEq
                        exact escaped secondOpen
                  have sourceSplit :
                      second :: tail = body ++ '}' :: after :=
                    takeDirective_eq_some_implies_split
                      (second :: tail) body after taken
                  have sourceStep := validateNlGo_directive_step
                    program.valueBindings gamma claimId.val fuel body after
                    sourceHeadFresh sourceNoClose
                  have sourceWhole :
                      validateNlGo program.valueBindings gamma claimId.val
                          (fuel + 1) ('{' :: second :: tail) =
                        match valueForDirective program.valueBindings body with
                        | some _ =>
                            validateNlGo program.valueBindings gamma claimId.val
                              fuel after
                        | none =>
                            match cellForDirective gamma body with
                            | some (_, prop) =>
                                match cellDecimal? prop with
                                | some _ =>
                                    validateNlGo program.valueBindings gamma
                                      claimId.val fuel after
                                | none => .error (.invalidValueBinding
                                    ⟨String.ofList body⟩)
                            | none => .error (.invalidValueBinding
                                ⟨String.ofList body⟩) := by
                    rw [sourceSplit]
                    exact sourceStep
                  have targetStep := validateNlGo_directive_step
                    (Binding.renameProgram ρg program).valueBindings
                    (gamma.map fun entry => (ρg.leaf entry.1, entry.2))
                    (ρg.prop claimId).val targetFuel renamedBody renamedAfter
                    bodyFresh.1 bodyFresh.2
                  have targetShape :
                      Binding.renameNlChars ρg (fuel + 1)
                          ('{' :: second :: tail) =
                        '{' :: (renamedBody ++ '}' :: renamedAfter) := by
                    simp [Binding.renameNlChars, escaped, bindingTaken,
                      renamedBody, renamedAfter]
                  have targetAfterBound : renamedAfter.length < targetFuel := by
                    rw [targetShape] at targetBound
                    simp only [List.length_cons, List.length_append]
                      at targetBound
                    omega
                  have afterRelated :=
                    ih after afterBound afterInventory targetFuel
                      targetAfterBound
                  have valueLookup := valueForDirective_rename sound body
                    bodyMember
                  have cellLookup := cellForDirective_rename sound gamma
                    gammaLeaves body bodyMember
                  rw [sourceWhole, targetShape, targetStep]
                  cases sourceValue : valueForDirective
                      program.valueBindings body with
                  | some binding =>
                      have targetValue :
                          valueForDirective
                              (Binding.renameProgram ρg program).valueBindings
                              renamedBody =
                            some { binding with
                              name := ρg.valueName binding.name } := by
                        simpa [renamedBody, sourceValue] using valueLookup
                      simpa [sourceValue, targetValue] using afterRelated
                  | none =>
                    have targetValue :
                        valueForDirective
                            (Binding.renameProgram ρg program).valueBindings
                            renamedBody = none := by
                      simpa [renamedBody, sourceValue] using valueLookup
                    simp only [targetValue]
                    cases sourceCell : cellForDirective gamma body with
                    | none =>
                        have targetCell :
                            cellForDirective
                                (gamma.map fun entry =>
                                  (ρg.leaf entry.1, entry.2))
                                renamedBody = none := by
                          simpa [renamedBody, sourceCell] using cellLookup
                        simp only [targetCell]
                        exact RenamedExcept.error
                          (ExpandValuesErrorRelated.invalidDirective
                            (ρg := ρg) body)
                    | some entry =>
                      obtain ⟨leaf, atom⟩ := entry
                      have targetCell :
                          cellForDirective
                              (gamma.map fun entry =>
                                (ρg.leaf entry.1, entry.2))
                              renamedBody =
                            some (ρg.leaf leaf, atom) := by
                        simpa [renamedBody, sourceCell] using cellLookup
                      simp only [targetCell]
                      cases decimal : cellDecimal? atom with
                      | none =>
                          exact RenamedExcept.error
                            (ExpandValuesErrorRelated.invalidDirective
                              (ρg := ρg) body)
                      | some value =>
                          simpa [decimal] using afterRelated
          · by_cases closeBrace : char = '}'
            · subst char
              cases rest with
              | nil =>
                  let targetRest := Binding.renameNlChars ρg fuel []
                  have sourceInvalid := validateNlGo_stray_close
                    program.valueBindings gamma claimId.val fuel [] (by simp)
                  have targetHeadFresh : targetRest.head? ≠ some '}' := by
                    rw [renameNlChars_head?]
                    simp
                  have targetInvalid := validateNlGo_stray_close
                    (Binding.renameProgram ρg program).valueBindings
                    (gamma.map fun entry => (ρg.leaf entry.1, entry.2))
                    (ρg.prop claimId).val targetFuel targetRest
                    targetHeadFresh
                  have targetShape :
                      Binding.renameNlChars ρg (fuel + 1) ['}'] =
                        '}' :: targetRest := by
                    rfl
                  rw [sourceInvalid, targetShape, targetInvalid]
                  exact RenamedExcept.error
                    (ExpandValuesErrorRelated.invalidClaim
                      (ρg := ρg) claimId)
              | cons second tail =>
                by_cases escaped : second = '}'
                · subst second
                  have tailBound : tail.length < fuel := by
                    simp only [List.length_cons] at sourceBound
                    omega
                  have tailInventory :
                      ∀ body ∈ nlDirectiveBodiesFuel fuel tail,
                        body ∈ programNlDirectiveBodies program := by
                    intro body member
                    exact bodyInventory body (by
                      simpa [nlDirectiveBodiesFuel] using member)
                  have targetTailBound :
                      (Binding.renameNlChars ρg fuel tail).length <
                        targetFuel := by
                    simp only [Binding.renameNlChars, List.length_cons]
                      at targetBound
                    omega
                  simpa [validateNlGo, Binding.renameNlChars] using
                    ih tail tailBound tailInventory targetFuel targetTailBound
                · let sourceRest := second :: tail
                  let targetRest := Binding.renameNlChars ρg fuel sourceRest
                  have sourceHeadFresh : sourceRest.head? ≠ some '}' := by
                    simp [sourceRest, escaped]
                  have targetHeadFresh : targetRest.head? ≠ some '}' := by
                    rw [renameNlChars_head?]
                    exact sourceHeadFresh
                  have sourceInvalid := validateNlGo_stray_close
                    program.valueBindings gamma claimId.val fuel sourceRest
                    sourceHeadFresh
                  have targetInvalid := validateNlGo_stray_close
                    (Binding.renameProgram ρg program).valueBindings
                    (gamma.map fun entry => (ρg.leaf entry.1, entry.2))
                    (ρg.prop claimId).val targetFuel targetRest
                    targetHeadFresh
                  have targetShape :
                      Binding.renameNlChars ρg (fuel + 1)
                          ('}' :: second :: tail) =
                        '}' :: targetRest := by
                    simp [Binding.renameNlChars, escaped, sourceRest,
                      targetRest]
                  change RenamedExcept (ExpandValuesErrorRelated ρg)
                    (fun _ _ => True)
                    (validateNlGo program.valueBindings gamma claimId.val
                      (fuel + 1) ('}' :: sourceRest))
                    (validateNlGo
                      (Binding.renameProgram ρg program).valueBindings
                      (gamma.map fun entry => (ρg.leaf entry.1, entry.2))
                      (ρg.prop claimId).val (targetFuel + 1)
                      (Binding.renameNlChars ρg (fuel + 1)
                        ('}' :: sourceRest)))
                  rw [sourceInvalid, targetShape, targetInvalid]
                  exact RenamedExcept.error
                    (ExpandValuesErrorRelated.invalidClaim
                      (ρg := ρg) claimId)
            · have restBound : rest.length < fuel := by
                simp only [List.length_cons] at sourceBound
                omega
              have restInventory :
                  ∀ body ∈ nlDirectiveBodiesFuel fuel rest,
                    body ∈ programNlDirectiveBodies program := by
                intro body member
                exact bodyInventory body (by
                  simpa [nlDirectiveBodiesFuel, openBrace, closeBrace]
                    using member)
              have targetRestBound :
                  (Binding.renameNlChars ρg fuel rest).length <
                    targetFuel := by
                have targetShape :
                    Binding.renameNlChars ρg (fuel + 1) (char :: rest) =
                      char :: Binding.renameNlChars ρg fuel rest := by
                  simp [Binding.renameNlChars, openBrace, closeBrace]
                rw [targetShape] at targetBound
                simp only [List.length_cons] at targetBound
                omega
              simpa [validateNlGo, Binding.renameNlChars, openBrace,
                closeBrace] using
                ih rest restBound restInventory targetFuel targetRestBound

private theorem validateNl_rename_related
    (sound : RenamingSound ρg program policy)
    (gamma : List (Presentation.LeafId × Atom))
    (gammaLeaves : ∀ entry ∈ gamma, entry.1 ∈ leafIds program)
    (claimId : Presentation.PropId) (text : String)
    (textMember : text ∈ claimNls program) :
    RenamedExcept (ExpandValuesErrorRelated ρg) (fun _ _ => True)
      (validateNl program.valueBindings gamma claimId.val text)
      (validateNl
        (Binding.renameProgram ρg program).valueBindings
        (gamma.map fun entry => (ρg.leaf entry.1, entry.2))
        (ρg.prop claimId).val (Binding.renameNl ρg text)) := by
  let sourceFuel := text.toList.length + 1
  let renamedChars := Binding.renameNlChars ρg sourceFuel text.toList
  have bodyInventory :
      ∀ body ∈ nlDirectiveBodiesFuel sourceFuel text.toList,
        body ∈ programNlDirectiveBodies program := by
    intro body bodyMember
    simp only [programNlDirectiveBodies, List.mem_flatMap]
    exact ⟨text, textMember, by
      simpa [nlDirectiveBodies, sourceFuel] using bodyMember⟩
  have related := validateNlGo_rename_related sound gamma gammaLeaves claimId
    sourceFuel text.toList (by simp [sourceFuel]) bodyInventory
    (renamedChars.length + 1) (by
      simpa [renamedChars] using
        Nat.lt_succ_self
          (Binding.renameNlChars ρg sourceFuel text.toList).length)
  unfold validateNl Binding.renameNl
  simpa [sourceFuel, renamedChars] using related

/-- Executable prose interpolation preserves exact success/failure shape and
failure provenance under a sound all-namespace renaming.  Generated prose is
intentionally related propositionally rather than by a false string equality. -/
theorem expandNl_rename_related
    (sound : RenamingSound ρg program policy)
    (gamma : List (Presentation.LeafId × Atom))
    (gammaLeaves : ∀ entry ∈ gamma, entry.1 ∈ leafIds program)
    (claimId : Presentation.PropId) (text : String)
    (textMember : text ∈ claimNls program) :
    RenamedExcept (ExpandValuesErrorRelated ρg) (fun _ _ => True)
      (expandNl program.valueBindings gamma claimId.val text)
      (expandNl
        (Binding.renameProgram ρg program).valueBindings
        (gamma.map fun entry => (ρg.leaf entry.1, entry.2))
        (ρg.prop claimId).val (Binding.renameNl ρg text)) := by
  have related := validateNl_rename_related sound gamma gammaLeaves claimId
    text textMember
  rw [← expandNl_erase program.valueBindings gamma claimId.val text,
    ← expandNl_erase
      (Binding.renameProgram ρg program).valueBindings
      (gamma.map fun entry => (ρg.leaf entry.1, entry.2))
      (ρg.prop claimId).val (Binding.renameNl ρg text)] at related
  cases sourceResult : expandNl program.valueBindings gamma claimId.val text with
  | error sourceError =>
      cases targetResult : expandNl
          (Binding.renameProgram ρg program).valueBindings
          (gamma.map fun entry => (ρg.leaf entry.1, entry.2))
          (ρg.prop claimId).val (Binding.renameNl ρg text) with
      | error targetError =>
          simp only [sourceResult, targetResult, Except.map] at related
          cases related with
          | error errorRelated =>
              exact RenamedExcept.error errorRelated
      | ok targetText =>
          simp only [sourceResult, targetResult, Except.map] at related
          cases related
  | ok sourceText =>
      cases targetResult : expandNl
          (Binding.renameProgram ρg program).valueBindings
          (gamma.map fun entry => (ρg.leaf entry.1, entry.2))
          (ρg.prop claimId).val (Binding.renameNl ρg text) with
      | error targetError =>
          simp only [sourceResult, targetResult, Except.map] at related
          cases related
      | ok targetText =>
          exact RenamedExcept.ok trivial

mutual
  @[simp] private theorem renameValueTerm_empty
      (ρg : Binding.GlobalRenaming) :
      ∀ term : Term, Binding.renameValueTerm ρg [] term = term
    | .num _ => rfl
    | .str _ => rfl
    | .con name .nil => by simp [Binding.renameValueTerm]
    | .con name (.cons term rest) => by
        simp only [Binding.renameValueTerm, Binding.renameValueTerms]
        rw [renameValueTerm_empty ρg term, renameValueTerms_empty ρg rest]
  @[simp] private theorem renameValueTerms_empty
      (ρg : Binding.GlobalRenaming) :
      ∀ terms : Terms, Binding.renameValueTerms ρg [] terms = terms
    | .nil => rfl
    | .cons term rest => by
        simp [Binding.renameValueTerms, renameValueTerm_empty ρg term,
          renameValueTerms_empty ρg rest]
end

@[simp] private theorem renameValueAtom_empty
    (ρg : Binding.GlobalRenaming) (atom : Atom) :
    Binding.renameValueAtom ρg [] atom = atom := by
  cases atom
  simp [Binding.renameValueAtom]

mutual
  private theorem substSupportTerm_rename
      (sound : RenamingSound ρg program policy)
      (term : Presentation.SupportTerm)
      (fixed : SupportTermFixed ρg (programValues program) term) :
      substSupportTerm (Binding.renameProgram ρg program).valueBindings
          (Binding.renameSupportTerm ρg (programValues program) term) =
        Binding.renameSupportTerm ρg []
          (substSupportTerm program.valueBindings term) := by
    cases term with
    | leaf leaf => rfl
    | rule rule subst premises discharges holes assurance =>
        have substEqual :
            (Binding.renameSubstValues ρg (programValues program) subst).map
                (fun pair => (pair.1,
                  substituteValueTerm
                    (Binding.renameProgram ρg program).valueBindings
                    pair.2)) =
              Binding.renameSubstValues ρg []
                (subst.map fun pair => (pair.1,
                  substituteValueTerm program.valueBindings pair.2)) := by
          simp only [Binding.renameSubstValues, List.map_map,
            Function.comp_apply]
          apply List.map_congr_left
          intro entry entryMember
          obtain ⟨parameter, value⟩ := entry
          have valueFixed :
              TermFixed ρg (programValues program) value := by
            intro spelling spellingMember notValue
            exact fixed spelling (by
              simp only [supportTermNullaryCons, List.mem_append]
              exact Or.inl (Or.inl
                (List.mem_flatMap.mpr
                  ⟨(parameter, value), entryMember, spellingMember⟩))) notValue
          change
            (parameter,
              substituteValueTerm
                (Binding.renameProgram ρg program).valueBindings
                (Binding.renameValueTerm ρg (programValues program) value)) =
              (parameter,
                Binding.renameValueTerm ρg []
                  (substituteValueTerm program.valueBindings value))
          rw [substituteValueTerm_rename ρg program value valueFixed]
          simp
        have premisesFixed :
            ∀ spelling, spelling ∈ supportTermsNullaryCons premises →
              spelling ∉ (programValues program).map (·.val) →
                Binding.renameText ρg spelling = spelling := by
          intro spelling member notValue
          exact fixed spelling (by
            simp [supportTermNullaryCons]
            exact Or.inr (Or.inl member)) notValue
        have dischargesFixed :
            ∀ spelling, spelling ∈ supportDischargesNullaryCons discharges →
              spelling ∉ (programValues program).map (·.val) →
                Binding.renameText ρg spelling = spelling := by
          intro spelling member notValue
          exact fixed spelling (by
            simp [supportTermNullaryCons]
            exact Or.inr (Or.inr member)) notValue
        simp only [substSupportTerm, Binding.renameSupportTerm]
        rw [substEqual]
        rw [substSupportTerms_rename sound premises premisesFixed]
        rw [substSupportDischarges_rename sound discharges dischargesFixed]
  private theorem substSupportTerms_rename
      (sound : RenamingSound ρg program policy) :
      ∀ (terms : Presentation.SupportTerms),
        (∀ spelling, spelling ∈ supportTermsNullaryCons terms →
          spelling ∉ (programValues program).map (·.val) →
            Binding.renameText ρg spelling = spelling) →
        substSupportTerms (Binding.renameProgram ρg program).valueBindings
            (Binding.renameSupportTerms ρg (programValues program) terms) =
          Binding.renameSupportTerms ρg []
            (substSupportTerms program.valueBindings terms)
    | .nil, _ => rfl
    | .cons term rest, fixed => by
        have headFixed :
            SupportTermFixed ρg (programValues program) term := by
          intro spelling member notValue
          exact fixed spelling (by
            simp [supportTermsNullaryCons]
            exact Or.inl member) notValue
        have tailFixed :
            ∀ spelling, spelling ∈ supportTermsNullaryCons rest →
              spelling ∉ (programValues program).map (·.val) →
                Binding.renameText ρg spelling = spelling := by
          intro spelling member notValue
          exact fixed spelling (by
            simp [supportTermsNullaryCons]
            exact Or.inr member) notValue
        simp only [substSupportTerms, Binding.renameSupportTerms]
        rw [substSupportTerm_rename sound term headFixed]
        rw [substSupportTerms_rename sound rest tailFixed]
  private theorem substSupportDischarges_rename
      (sound : RenamingSound ρg program policy) :
      ∀ (discharges : Presentation.Discharges),
        (∀ spelling, spelling ∈ supportDischargesNullaryCons discharges →
          spelling ∉ (programValues program).map (·.val) →
            Binding.renameText ρg spelling = spelling) →
        substSupportDischarges
            (Binding.renameProgram ρg program).valueBindings
            (Binding.renameDischarges ρg (programValues program) discharges) =
          Binding.renameDischarges ρg []
            (substSupportDischarges program.valueBindings discharges)
    | .nil, _ => rfl
    | .cons question term rest, fixed => by
        have headFixed :
            SupportTermFixed ρg (programValues program) term := by
          intro spelling member notValue
          exact fixed spelling (by
            simp [supportDischargesNullaryCons]
            exact Or.inl member) notValue
        have tailFixed :
            ∀ spelling, spelling ∈ supportDischargesNullaryCons rest →
              spelling ∉ (programValues program).map (·.val) →
                Binding.renameText ρg spelling = spelling := by
          intro spelling member notValue
          exact fixed spelling (by
            simp [supportDischargesNullaryCons]
            exact Or.inr member) notValue
        simp only [substSupportDischarges, Binding.renameDischarges]
        rw [substSupportTerm_rename sound term headFixed]
        rw [substSupportDischarges_rename sound rest tailFixed]
end

private theorem substArgInstantiation_rename
    (sound : RenamingSound ρg program policy)
    (argument : Presentation.Arg) (member : .arg argument ∈ program.decls) :
    substArgInstantiation (Binding.renameProgram ρg program).valueBindings
        (Binding.renameArgInstantiation ρg (programValues program)
          argument.instantiation) =
      Binding.renameArgInstantiation ρg []
        (substArgInstantiation program.valueBindings argument.instantiation) := by
  cases instantiation : argument.instantiation with
  | explicitTheta term =>
      have fixed := supportTermFixed_of_explicitArg sound argument term member
        instantiation
      simp [substArgInstantiation, Binding.renameArgInstantiation,
        substSupportTerm_rename sound term fixed]
  | inferTheta rule refs discharges obligations assurance =>
      rfl

/-- Substitution after renaming is the identifier-only renaming of source
substitution.  Value RHS terms are intentionally shared by both sides. -/
private theorem substDecl_rename
    (sound : RenamingSound ρg program policy)
    (declaration : Presentation.Decl)
    (member : declaration ∈ program.decls) :
    substDecl (Binding.renameProgram ρg program).valueBindings
        (Binding.renameDecl ρg (programValues program) declaration) =
      Binding.renameDecl ρg []
        (substDecl program.valueBindings declaration) := by
  cases declaration with
  | leaf leaf =>
      have fixed := atomFixed_of_decl sound.toComparison (.leaf leaf) member
        leaf.prop (by simp [declNullaryCons])
      simp [substDecl, Binding.renameDecl,
        substituteValueAtom_rename ρg program leaf.prop fixed]
  | claim claim =>
      have fixed := atomFixed_of_decl sound.toComparison (.claim claim) member
        claim.formal (by simp [declNullaryCons])
      simp [substDecl, Binding.renameDecl,
        substituteValueAtom_rename ρg program claim.formal fixed]
  | arg argument =>
      simp [substDecl, Binding.renameDecl, Binding.renameArg,
        substArgInstantiation_rename sound argument member]
  | comparison comparison =>
      have fixed := atomFixed_of_decl sound.toComparison
        (.comparison comparison) member comparison.conclusion
        (by simp [declNullaryCons])
      simp [substDecl, Binding.renameDecl, Binding.renameComparison,
        substituteValueAtom_rename ρg program comparison.conclusion fixed]
  | attack attack => rfl
  | status status => rfl
  | group group => rfl

/-- The non-prose value-expansion prefix commutes with a sound global
renaming.  The subsequent interpolation pass deliberately requires the
weaker `SemanticProgramRelated` relation, since generated prose is not an
exactly renamed string. -/
theorem substitutedDecls_rename
    (sound : RenamingSound ρg program policy) :
    (Binding.renameProgram ρg program).decls.map
        (substDecl (Binding.renameProgram ρg program).valueBindings) =
      (program.decls.map (substDecl program.valueBindings)).map
        (Binding.renameDecl ρg []) := by
  change
    (program.decls.map (Binding.renameDecl ρg (programValues program))).map
        (substDecl (Binding.renameProgram ρg program).valueBindings) = _
  simp only [List.map_map]
  apply List.map_congr_left
  intro declaration member
  exact substDecl_rename sound declaration member

end Renaming

/-- Reduce a `do`-block whose bind source is an `Except.error`: the whole
block is that error.  (`Except.bind` is not a default simp lemma, so the
executable pass's `do` notation needs this explicit step.) -/
private theorem bind_error_reduce {α β} (e : Surface.Error) (f : α → Except Surface.Error β) :
    (do let x ← (Except.error e : Except Surface.Error α); f x) = Except.error e := rfl

/-- Reduce a `do`-block whose bind source is an `Except.ok` to its body. -/
theorem bind_ok_reduce {α β} (a : α) (f : α → Except Surface.Error β) :
    (do let x ← (Except.ok a : Except Surface.Error α); f x) = f a := rfl

private theorem expandDeclNls_subst_decls_sound {env gamma ds ts}
    (h : expandDeclNls env gamma (ds.map (substDecl env)) = .ok ts) : DeclsExpand env gamma ds ts := by
  induction ds generalizing ts with
  | nil =>
      simp [expandDeclNls] at h
      subst ts
      exact DeclsExpand.nil
  | cons declaration rest ih =>
      cases declaration with
      | leaf leaf =>
          simp [expandDeclNls, substDecl] at h
          cases hrest : expandDeclNls env gamma (rest.map (substDecl env)) with
          | error e => exfalso; simpa [Except.map, hrest, bind_error_reduce] using h
          | ok tail =>
              simp [Except.map, hrest, bind_ok_reduce] at h
              subst ts
              exact DeclsExpand.leaf (ih hrest)
      | claim claim =>
          simp [expandDeclNls, substDecl] at h
          cases hnl : expandNl env gamma claim.id.val claim.nl with
          | error e => simp [expandDeclNls, hnl, bind_error_reduce] at h
          | ok prose =>
              simp [Except.map, expandDeclNls, hnl, bind_ok_reduce] at h
              cases hrest : expandDeclNls env gamma (rest.map (substDecl env)) with
              | error e => exfalso; simpa [Except.map, hrest, bind_error_reduce] using h
              | ok tail =>
                  simp [Except.map, hrest, bind_ok_reduce] at h
                  subst ts
                  exact DeclsExpand.claim (expandNl_sound hnl) (ih hrest)
      | arg argument =>
          simp [expandDeclNls, substDecl, substArgInstantiation] at h
          cases hrest : expandDeclNls env gamma (rest.map (substDecl env)) with
          | error e => exfalso; simpa [Except.map, hrest, bind_error_reduce] using h
          | ok tail =>
              simp [Except.map, hrest, bind_ok_reduce] at h
              subst ts
              exact DeclsExpand.arg (ih hrest)
      | attack attack =>
          simp [expandDeclNls, substDecl] at h
          cases hrest : expandDeclNls env gamma (rest.map (substDecl env)) with
          | error e => exfalso; simpa [Except.map, hrest, bind_error_reduce] using h
          | ok tail =>
              simp [Except.map, hrest, bind_ok_reduce] at h
              subst ts
              exact DeclsExpand.attack (ih hrest)
      | status id =>
          simp [expandDeclNls, substDecl] at h
          cases hrest : expandDeclNls env gamma (rest.map (substDecl env)) with
          | error e => exfalso; simpa [Except.map, hrest, bind_error_reduce] using h
          | ok tail =>
              simp [Except.map, hrest, bind_ok_reduce] at h
              subst ts
              exact DeclsExpand.status (ih hrest)
      | group group =>
          simp [expandDeclNls, substDecl] at h
          cases hrest : expandDeclNls env gamma (rest.map (substDecl env)) with
          | error e => exfalso; simpa [Except.map, hrest, bind_error_reduce] using h
          | ok tail =>
              simp [Except.map, hrest, bind_ok_reduce] at h
              subst ts
              exact DeclsExpand.group (ih hrest)
      | comparison comparison =>
          simp [expandDeclNls, substDecl] at h
          cases hnl : expandNl env gamma comparison.claim.id.val comparison.claim.nlRaw with
          | error e => simp [expandDeclNls, hnl, bind_error_reduce] at h
          | ok prose =>
              simp [Except.map, expandDeclNls, hnl, bind_ok_reduce] at h
              cases hrest : expandDeclNls env gamma (rest.map (substDecl env)) with
              | error e => exfalso; simpa [Except.map, hrest, bind_error_reduce] using h
              | ok tail =>
                  simp [Except.map, hrest, bind_ok_reduce] at h
                  subst ts
                  exact DeclsExpand.comparison (expandNl_sound hnl) (ih hrest)

private theorem expandDeclNls_subst_decls_complete {env gamma ds ts}
    (h : DeclsExpand env gamma ds ts) :
    expandDeclNls env gamma (ds.map (substDecl env)) = .ok ts := by
  induction h with
  | nil => rfl
  | leaf _ ih => simp [expandDeclNls, substDecl, ih, bind_ok_reduce]
  | claim hexp _ ih => simp [expandDeclNls, substDecl, expandNl_complete hexp, ih, bind_ok_reduce]
  | arg _ ih => simp [expandDeclNls, substDecl, substArgInstantiation, ih, bind_ok_reduce]
  | comparison hexp _ ih => simp [expandDeclNls, substDecl, expandNl_complete hexp, ih, bind_ok_reduce]
  | attack _ ih => simp [expandDeclNls, substDecl, ih, bind_ok_reduce]
  | status _ ih => simp [expandDeclNls, substDecl, ih, bind_ok_reduce]
  | group _ ih => simp [expandDeclNls, substDecl, ih, bind_ok_reduce]

/-! ### The soundness and completeness theorems -/

private theorem firstDuplicateNameAux_none_of_nodup
    (names seen : List Presentation.ValueName) (hnodup : names.Nodup)
    (hdisjoint : ∀ name ∈ names, name ∉ seen) :
    firstDuplicateNameAux names seen = none := by
  induction names generalizing seen with
  | nil => rfl
  | cons head tail ih =>
      have hhead : head ∉ seen := hdisjoint head (by simp)
      have htailNodup := (List.nodup_cons.mp hnodup).2
      have htailDisjoint : ∀ name ∈ tail, name ∉ head :: seen := by
        intro name hname hmem
        rcases List.mem_cons.mp hmem with heq | hseen
        · exact (List.nodup_cons.mp hnodup).1 (heq ▸ hname)
        · exact hdisjoint name (by simp [hname]) hseen
      simp [firstDuplicateNameAux, hhead,
        ih (head :: seen) htailNodup htailDisjoint]

private theorem duplicateName?_eq_none_of_nodup
    {bindings : List Presentation.ValueBinding}
    (h : (bindings.map (·.name)).Nodup) : duplicateName? bindings = none := by
  apply firstDuplicateNameAux_none_of_nodup _ [] h
  simp

private theorem wsAtom_substituted_decls (policy : Presentation.Policy)
    (program : Presentation.Program) (bindings : List Presentation.ValueBinding)
    (h : ∀ d ∈ program.decls,
      match d with
      | .claim claim =>
          Lara.Sigma.wsAtom policy.sigma (substituteValueAtom bindings claim.formal) = true
      | _ => True) :
    ∀ d' ∈ (program.decls.map (substDecl bindings)),
      match d' with
      | .claim claim => Lara.Sigma.wsAtom policy.sigma claim.formal = true
      | _ => True := by
  intro d' hd'
  rcases List.mem_map.mp hd' with ⟨d, hmem, hsubst⟩
  subst d'
  cases d with
  | claim claim =>
      simp [substDecl]
      exact h (.claim claim) hmem
  | _ => trivial

theorem expandValues_eq_of_none_checks (policy : Presentation.Policy)
    (program : Presentation.Program) (decls : List Decl)
    (hchecks : valueBindingErrors policy program = none)
    (hclaim : claimFormalErrors policy program.valueBindings
      { program with decls := program.decls.map (substDecl program.valueBindings) } = none)
    (hnl : expandDeclNls program.valueBindings
      (declaredLeaves { program with decls := program.decls.map (substDecl program.valueBindings) })
      ({ program with decls := program.decls.map (substDecl program.valueBindings) }.decls) = .ok decls) :
    expandValues policy program = .ok
      { { program with decls := program.decls.map (substDecl program.valueBindings) } with
        valueBindings := [], decls := decls } := by
  simp [expandValues, hchecks, hclaim, hnl]

theorem expandValues_sound (policy : Presentation.Policy) {program out : Presentation.Program}
    (h : expandValues policy program = .ok out) : ExpandsValues program out := by
  unfold expandValues at h
  cases hchecks : valueBindingErrors policy program with
  | some error => exfalso; simp [hchecks] at h
  | none =>
      cases hclaim : claimFormalErrors policy program.valueBindings
        { program with decls := program.decls.map (substDecl program.valueBindings) } with
      | some error => exfalso; simp [hclaim, hchecks] at h
      | none =>
          cases hnl : expandDeclNls program.valueBindings
            (declaredLeaves { program with decls := program.decls.map (substDecl program.valueBindings) })
            ({ program with decls := program.decls.map (substDecl program.valueBindings) }.decls) with
          | error error => exfalso; simp [hnl, hclaim, hchecks] at h
          | ok decls =>
              simp [hnl, hclaim, hchecks] at h
              have hout : decls = out.decls := by
                simpa using (congrArg Program.decls h)
              have hdecls : DeclsExpand program.valueBindings
                  (declaredLeaves { program with decls := program.decls.map (substDecl program.valueBindings) })
                  program.decls out.decls := by
                simpa [hout] using (expandDeclNls_subst_decls_sound hnl)
              refine ExpandsValues.intro (env := program.valueBindings)
                (gamma := declaredLeaves { program with decls := program.decls.map (substDecl program.valueBindings) })
                rfl rfl ?_ ?_ ?_ ?_ ?_ hdecls
              · simpa using (congrArg Program.valueBindings h).symm
              · simpa using (congrArg Program.artifact h).symm
              · simpa using (congrArg Program.digest h).symm
              · simpa using (congrArg Program.policy h).symm
              · simpa using (congrArg Program.backends h).symm

private theorem findSome?_eq_none_of_forall {α} (f : α → Option β) {l : List α}
    (h : ∀ a ∈ l, f a = none) : l.findSome? f = none := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      have ha : f a = none := h a (by simp)
      have hrest : ∀ a' ∈ rest, f a' = none := by
        intro a' ha'; exact h a' (by simp [ha'])
      simp [List.findSome?, ha, ih hrest]

theorem expandValues_complete (policy : Presentation.Policy) {program out : Presentation.Program}
    (hwf : ValueBindingsWellFormed ⟨program, policy⟩)
    (hexp : ExpandsValues program out) :
    expandValues policy program = .ok out := by
  cases hexp with
  | intro henv hgamma hbindings hartifact hdigest hpolicy hbackends hdecls =>
  rcases hwf with ⟨⟨⟨⟨⟨hnames, hreserved⟩, hcollisions⟩, hsorts⟩, hclaims⟩, _hnl⟩
  have hchecks : valueBindingErrors policy program = none := by
    unfold valueBindingErrors
    have hdup : duplicateName? program.valueBindings = none := by
      apply duplicateName?_eq_none_of_nodup
      simpa [valueNames] using hnames
    simp [hdup]
    have hres : program.valueBindings.find? (fun b => decide (b.name.val = "cell")) = none := by
      rw [List.find?_eq_none]
      intro b hb hbeq
      exact hreserved b hb (of_decide_eq_true hbeq)
    simp [hres]
    have hcol : program.valueBindings.find? (fun b =>
        policy.sigma.cons.any (fun con => decide (con.sym.name = b.name.val))) = none := by
      rw [List.find?_eq_none]
      intro b hb hany
      rw [List.any_eq_true] at hany
      rcases hany with ⟨con, hcon, hdec⟩
      exact hcollisions b hb con hcon (of_decide_eq_true hdec).symm
    simp [hcol]
    have hsrt : program.valueBindings.find? (fun b => (Lara.Sigma.sortOf policy.sigma b.term).isNone) = none := by
      rw [List.find?_eq_none]
      intro b hb hnone
      have hsort := hsorts b hb
      cases hs : Lara.Sigma.sortOf policy.sigma b.term with
      | none => simp [hs] at hsort
      | some _ => simp [hs] at hnone
    simp [hsrt]
  have hclaim : claimFormalErrors policy program.valueBindings
      { program with decls := program.decls.map (substDecl program.valueBindings) } = none := by
    unfold claimFormalErrors
    by_cases hempty : program.valueBindings.isEmpty
    · simp [hempty]
    · simp [hempty]
      have hforall : ∀ d ∈ program.decls,
        match d with
        | .claim claim =>
            Lara.Sigma.wsAtom policy.sigma (substituteValueAtom program.valueBindings claim.formal) = true
        | _ => True := by
        rcases hclaims with hnil | hforall
        · exfalso
          exact hempty (by simpa using hnil)
        · exact hforall
      have hsub : ∀ d' ∈ (program.decls.map (substDecl program.valueBindings)),
          match d' with
          | .claim claim => Lara.Sigma.wsAtom policy.sigma claim.formal = true
          | _ => True :=
        wsAtom_substituted_decls policy program program.valueBindings hforall
      have hfind : ({ program with decls := program.decls.map (substDecl program.valueBindings) }.decls).findSome? (fun declaration =>
          match declaration with
          | Decl.claim claim => if (Lara.Sigma.wsAtom policy.sigma claim.formal) = false then some claim.id.val else none
          | _ => none) = none := by
        change (program.decls.map (substDecl program.valueBindings)).findSome? (fun declaration =>
          match declaration with
          | Decl.claim claim => if (Lara.Sigma.wsAtom policy.sigma claim.formal) = false then some claim.id.val else none
          | _ => none) = none
        apply findSome?_eq_none_of_forall
        intro d hd
        cases d with
        | claim claim =>
            have hw := hsub (.claim claim) hd
            simp [hw]
        | _ => rfl
      have hfirst : firstInvalidClaimId? policy.sigma
          (program.decls.map (substDecl program.valueBindings)) = none := by
        simpa [firstInvalidClaimId?] using hfind
      simp [hfirst]
  have hnl : expandDeclNls program.valueBindings
      (declaredLeaves { program with decls := program.decls.map (substDecl program.valueBindings) })
      ({ program with decls := program.decls.map (substDecl program.valueBindings) }.decls) = .ok out.decls := by
    have hnl' := expandDeclNls_subst_decls_complete hdecls
    simpa [henv, hgamma] using hnl'
  rw [expandValues_eq_of_none_checks policy program out.decls hchecks hclaim hnl]
  congr 1
  cases out with
  | mk artifact digest policy backends valueBindings decls =>
      simp at hbindings hartifact hdigest hpolicy hbackends
      simp [hbindings, hartifact, hdigest, hpolicy, hbackends]

private theorem declIds_preserved_of_DeclsExpand {env gamma ds ts}
    (h : DeclsExpand env gamma ds ts) :
    (ds.filterMap (fun d => match d with | .leaf l => some l.id | _ => none) =
      ts.filterMap (fun d => match d with | .leaf l => some l.id | _ => none)) ∧
    (ds.flatMap (fun d => match d with | .arg a => [a.id] | .comparison c => [c.recheckArg, c.bridgeArg] | _ => []) =
      ts.flatMap (fun d => match d with | .arg a => [a.id] | .comparison c => [c.recheckArg, c.bridgeArg] | _ => [])) ∧
    (ds.filterMap (fun d => match d with | .claim c => some c.id | .comparison c => some c.claim.id | _ => none) =
      ts.filterMap (fun d => match d with | .claim c => some c.id | .comparison c => some c.claim.id | _ => none)) := by
  induction h with
  | nil => simp
  | leaf _ ih => simp [ih]
  | claim _ _ ih => simp [ih]
  | arg _ ih => simp [ih]
  | comparison _ _ ih => simp [ih]
  | attack _ ih => simp [ih]
  | status _ ih => simp [ih]
  | group _ ih => simp [ih]

theorem expandValues_preserves_decl_ids (policy : Presentation.Policy)
    {program out : Presentation.Program} (h : expandValues policy program = .ok out) :
    leafIds out = leafIds program ∧ argIds out = argIds program ∧ claimIds out = claimIds program := by
  have hsound := expandValues_sound policy h
  cases hsound with
  | intro henv hgamma hbindings hartifact hdigest hpolicy hbackends hdecls =>
      have hids := declIds_preserved_of_DeclsExpand hdecls
      simp [leafIds, argIds, claimIds]
      exact ⟨hids.1.symm, hids.2.1.symm, hids.2.2.symm⟩

/-! ### Idempotence -/

/-- A declaration whose prose carries no brace syntax: re-expansion of an
already-expanded program's declarations is a no-op on it. -/
def NlBraceFree (d : Decl) : Prop :=
  match d with
  | .claim claim => ∀ c ∈ claim.nl.toList, c ≠ '{' ∧ c ≠ '}'
  | .comparison comparison => ∀ c ∈ comparison.claim.nlRaw.toList, c ≠ '{' ∧ c ≠ '}'
  | _ => True

private theorem expandNlGo_identity_of_brace_free (gamma : List (Presentation.LeafId × Atom))
    (claimId : String) :
    ∀ (fuel : Nat) (input : List Char),
      input.length + 1 ≤ fuel →
      (∀ c ∈ input, c ≠ '{' ∧ c ≠ '}') →
      expandNlGo [] gamma claimId fuel input = .ok input
  | 0, input, hfuel, h => by exfalso; omega
  | fuel + 1, [], hfuel, h => by simp [expandNlGo]
  | fuel + 1, c :: rest, hfuel, h => by
      have hc : c ≠ '{' ∧ c ≠ '}' := h c (by simp)
      have hrest : ∀ x ∈ rest, x ≠ '{' ∧ x ≠ '}' := by
        intro x hx; exact h x (by simp [hx])
      by_cases hL : c = '{'
      · exfalso; exact hc.1 hL
      · by_cases hR : c = '}'
        · exfalso; exact hc.2 hR
        · have ih := expandNlGo_identity_of_brace_free gamma claimId fuel rest (by simpa using hfuel) hrest
          simp [expandNlGo, Except.map, hL, hR, ih]

private theorem expandNl_identity_of_brace_free (gamma : List (Presentation.LeafId × Atom))
    (claimId : String) {text : String} (h : ∀ c ∈ text.toList, c ≠ '{' ∧ c ≠ '}') :
    expandNl [] gamma claimId text = .ok text := by
  unfold expandNl
  have hgo := expandNlGo_identity_of_brace_free gamma claimId (text.toList.length + 1) text.toList
    (by omega) h
  simp [hgo, Except.map, String.ofList_toList]

private theorem expandDeclNls_identity_of_brace_free (gamma : List (Presentation.LeafId × Atom))
    : ∀ (ds : List Decl),
      (∀ d ∈ ds, NlBraceFree d) →
      expandDeclNls [] gamma ds = .ok ds
  | [], _ => rfl
  | .claim claim :: rest, h => by
      have hc : NlBraceFree (.claim claim) := h (.claim claim) (by simp)
      have hrest : ∀ d ∈ rest, NlBraceFree d := by
        intro d hd; exact h d (by simp [hd])
      have hnl : expandNl [] gamma claim.id.val claim.nl = .ok claim.nl :=
        expandNl_identity_of_brace_free gamma claim.id.val hc
      simp [expandDeclNls, hnl, expandDeclNls_identity_of_brace_free gamma rest hrest, bind_ok_reduce]
  | .comparison comparison :: rest, h => by
      have hc : NlBraceFree (.comparison comparison) := h (.comparison comparison) (by simp)
      have hrest : ∀ d ∈ rest, NlBraceFree d := by
        intro d hd; exact h d (by simp [hd])
      have hnl : expandNl [] gamma comparison.claim.id.val comparison.claim.nlRaw = .ok comparison.claim.nlRaw :=
        expandNl_identity_of_brace_free gamma comparison.claim.id.val hc
      simp [expandDeclNls, hnl, expandDeclNls_identity_of_brace_free gamma rest hrest, bind_ok_reduce]
  | declaration :: rest, h => by
      have hrest : ∀ d ∈ rest, NlBraceFree d := by
        intro d hd; exact h d (by simp [hd])
      cases declaration with
      | leaf leaf =>
          simp [expandDeclNls, expandDeclNls_identity_of_brace_free gamma rest hrest, bind_ok_reduce]
      | arg argument =>
          simp [expandDeclNls, expandDeclNls_identity_of_brace_free gamma rest hrest, bind_ok_reduce]
      | attack attack =>
          simp [expandDeclNls, expandDeclNls_identity_of_brace_free gamma rest hrest, bind_ok_reduce]
      | status id =>
          simp [expandDeclNls, expandDeclNls_identity_of_brace_free gamma rest hrest, bind_ok_reduce]
      | group group =>
          simp [expandDeclNls, expandDeclNls_identity_of_brace_free gamma rest hrest, bind_ok_reduce]
      | claim claim =>
          have hc : NlBraceFree (.claim claim) := h (.claim claim) (by simp)
          have hnl : expandNl [] gamma claim.id.val claim.nl = .ok claim.nl :=
            expandNl_identity_of_brace_free gamma claim.id.val hc
          simp [expandDeclNls, hnl, expandDeclNls_identity_of_brace_free gamma rest hrest, bind_ok_reduce]
      | comparison comparison =>
          have hc : NlBraceFree (.comparison comparison) := h (.comparison comparison) (by simp)
          have hnl : expandNl [] gamma comparison.claim.id.val comparison.claim.nlRaw = .ok comparison.claim.nlRaw :=
            expandNl_identity_of_brace_free gamma comparison.claim.id.val hc
          simp [expandDeclNls, hnl, expandDeclNls_identity_of_brace_free gamma rest hrest, bind_ok_reduce]

mutual
  private theorem substituteValueTerm_nil (t : Term) : substituteValueTerm [] t = t := by
    cases t with
    | num s => rfl
    | str s => rfl
    | con name ts =>
        cases ts with
        | nil =>
            simp [substituteValueTerm, lookupValue]
        | cons t rest =>
            have h := substituteValueTerms_nil (.cons t rest)
            simp [substituteValueTerm, h]
  private theorem substituteValueTerms_nil (ts : Terms) : substituteValueTerms [] ts = ts := by
    cases ts with
    | nil => rfl
    | cons t rest =>
        simp [substituteValueTerms, substituteValueTerm_nil t, substituteValueTerms_nil rest]
end

mutual
  private theorem substSupportTerm_nil (t : Presentation.SupportTerm) : substSupportTerm [] t = t := by
    cases t with
    | leaf id => rfl
    | rule rule subst premises discharges holes assurance =>
        have h1 : subst.map (fun pair => (pair.1, substituteValueTerm [] pair.2)) = subst := by
          induction subst with
          | nil => rfl
          | cons p rest ih =>
              cases p with
              | mk param term =>
                  have hs : substituteValueTerm [] term = term := substituteValueTerm_nil term
                  simp [hs, ih]
        have h2 := substSupportTerms_nil premises
        have h3 := substSupportDischarges_nil discharges
        simp [substSupportTerm, h1, h2, h3]
  private theorem substSupportTerms_nil (ts : Presentation.SupportTerms) : substSupportTerms [] ts = ts := by
    cases ts with
    | nil => rfl
    | cons t rest =>
        simp [substSupportTerms, substSupportTerm_nil t, substSupportTerms_nil rest]
  private theorem substSupportDischarges_nil (ds : Presentation.Discharges) : substSupportDischarges [] ds = ds := by
    cases ds with
    | nil => rfl
    | cons q t rest =>
        simp [substSupportDischarges, substSupportTerm_nil t, substSupportDischarges_nil rest]
end

private theorem substArgInstantiation_nil (i : Presentation.ArgInstantiation) :
    substArgInstantiation [] i = i := by
  cases i with
  | explicitTheta term =>
      simp [substArgInstantiation, substSupportTerm_nil term]
  | inferTheta rule refs discharge obligations assurance => rfl

private theorem substDecl_nil (d : Presentation.Decl) : substDecl [] d = d := by
  cases d with
  | leaf leaf => simp [substDecl, substituteValueAtom, substituteValueTerms_nil]
  | claim claim => simp [substDecl, substituteValueAtom, substituteValueTerms_nil]
  | arg argument => simp [substDecl, substArgInstantiation_nil]
  | comparison comparison => simp [substDecl, substituteValueAtom, substituteValueTerms_nil]
  | attack _ => rfl
  | status _ => rfl
  | group _ => rfl

/-- A program that already carries no bindings and no brace syntax in its
prose is a fixed point of value expansion. -/
theorem expandValues_fixed_point (policy : Presentation.Policy) {program : Presentation.Program}
    (hbindings : program.valueBindings = [])
    (hstable : ∀ d ∈ program.decls, NlBraceFree d) :
    expandValues policy program = .ok program := by
  have hchecks : valueBindingErrors policy program = none := by
    unfold valueBindingErrors
    simp [hbindings, duplicateName?, firstDuplicateNameAux]
  have hclaim : claimFormalErrors policy program.valueBindings
      { program with decls := program.decls.map (substDecl program.valueBindings) } = none := by
    unfold claimFormalErrors
    simp [hbindings]
  have hmap : program.decls.map (substDecl []) = program.decls := by
    simpa [List.map_id] using
      (List.map_congr_left (fun d hd => substDecl_nil d) : program.decls.map (substDecl []) = program.decls.map id)
  have hgamma : declaredLeaves { program with decls := program.decls.map (substDecl program.valueBindings) }
      = declaredLeaves program := by
    simp [declaredLeaves, hbindings, hmap]
  have hnl : expandDeclNls [] (declaredLeaves program) program.decls = .ok program.decls :=
    expandDeclNls_identity_of_brace_free (declaredLeaves program) program.decls hstable
  rw [expandValues_eq_of_none_checks policy program program.decls hchecks hclaim]
  · congr 1
    cases program with
    | mk artifact digest policy backends valueBindings decls =>
        simp at hbindings hmap
        simp [hbindings, hmap]
  · simpa [declaredLeaves, hbindings, hmap, hgamma] using hnl

namespace Renaming

mutual
  private theorem termNullaryCons_of_sortOf_some_aux
      (sigma : Sigma) :
      ∀ (term : Term) (sort : TermSort) (spelling : String),
        Lara.Sigma.sortOf sigma term = some sort →
        spelling ∈ termNullaryCons term →
        ∃ constructor ∈ sigma.cons, constructor.sym.name = spelling
    | .num _, _, _, _, member => by simp [termNullaryCons] at member
    | .str _, _, _, _, member => by simp [termNullaryCons] at member
    | .con name terms, sort, spelling, hsort, member => by
        cases found : sigma.lookupCon ⟨name⟩ with
        | none => simp [Lara.Sigma.sortOf, found] at hsort
        | some constructor =>
            cases terms with
            | nil =>
                simp [termNullaryCons] at member
                subst spelling
                exact ⟨constructor,
                  List.mem_of_find?_eq_some found,
                  by
                    have selected := List.find?_some found
                    have symbolEq : constructor.sym = ⟨name⟩ := by
                      simpa using selected
                    exact congrArg (fun symbol => symbol.name) symbolEq⟩
            | cons head rest =>
                have expanded :
                    Lara.Sigma.expectTerms sigma constructor.args
                          (.cons head rest) = true ∧
                      constructor.result = sort := by
                  simpa [Lara.Sigma.sortOf, found] using hsort
                exact termsNullaryCons_of_expectTerms_aux sigma
                  constructor.args (.cons head rest) spelling expanded.1 member
  private theorem termsNullaryCons_of_expectTerms_aux
      (sigma : Sigma) :
      ∀ (sorts : List TermSort) (terms : Terms) (spelling : String),
        Lara.Sigma.expectTerms sigma sorts terms = true →
        spelling ∈ termsNullaryCons terms →
        ∃ constructor ∈ sigma.cons, constructor.sym.name = spelling
    | [], .nil, _, _, member => by simp [termsNullaryCons] at member
    | [], .cons _ _, _, expected, _ => by
        simp [Lara.Sigma.expectTerms] at expected
    | _ :: _, .nil, _, expected, _ => by
        simp [Lara.Sigma.expectTerms] at expected
    | sort :: sorts, .cons term rest, spelling, expected, member => by
        cases termSort : Lara.Sigma.sortOf sigma term with
        | none => simp [Lara.Sigma.expectTerms, termSort] at expected
        | some actual =>
            have reduced :
                ((actual == sort) &&
                  Lara.Sigma.expectTerms sigma sorts rest) = true := by
              simpa [Lara.Sigma.expectTerms, termSort] using expected
            have both := Bool.and_eq_true_iff.mp reduced
            simp [termsNullaryCons] at member
            rcases member with member | member
            · exact termNullaryCons_of_sortOf_some_aux sigma term actual spelling
                termSort member
            · exact termsNullaryCons_of_expectTerms_aux sigma sorts rest spelling
                both.2 member
end

/-- A nullary constructor occurring in a sorted term is declared by the
policy signature. -/
theorem termNullaryCons_of_sortOf_some
    {policy : Presentation.Policy} {term : Term} {sort : TermSort}
    {spelling : String}
    (hsort : Lara.Sigma.sortOf policy.sigma term = some sort)
    (member : spelling ∈ termNullaryCons term) :
    ∃ constructor ∈ policy.sigma.cons, constructor.sym.name = spelling :=
  termNullaryCons_of_sortOf_some_aux policy.sigma term sort spelling hsort member

private theorem firstInvalidClaimId?_rename
    {ρg : Binding.GlobalRenaming} {program : Presentation.Program}
    {policy : Presentation.Policy}
    (sound : RenamingSound ρg program policy)
    (declarations : List Presentation.Decl)
    (contained : ∀ declaration ∈ declarations,
      declaration ∈ program.decls) :
    firstInvalidClaimId? policy.sigma
        ((declarations.map
          (Binding.renameDecl ρg (programValues program))).map
            (substDecl
              (Binding.renameProgram ρg program).valueBindings)) =
      (firstInvalidClaimId? policy.sigma
        (declarations.map (substDecl program.valueBindings))).map
          (fun name =>
            (ρg.prop (⟨name⟩ : Presentation.PropId)).val) := by
  change
    (((declarations.map
      (Binding.renameDecl ρg (programValues program))).map
        (substDecl
          (Binding.renameProgram ρg program).valueBindings)).findSome?
      (fun declaration =>
        match declaration with
        | .claim claim =>
            if !Lara.Sigma.wsAtom policy.sigma claim.formal then
              some claim.id.val
            else none
        | _ => none)) =
      ((declarations.map
        (substDecl program.valueBindings)).findSome?
        (fun declaration =>
          match declaration with
          | .claim claim =>
              if !Lara.Sigma.wsAtom policy.sigma claim.formal then
                some claim.id.val
              else none
          | _ => none)).map
        (fun name =>
          (ρg.prop (⟨name⟩ : Presentation.PropId)).val)
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
      have headMember : declaration ∈ program.decls :=
        contained declaration (by simp)
      have tailContained : ∀ candidate ∈ rest,
          candidate ∈ program.decls := by
        intro candidate member
        exact contained candidate (by simp [member])
      cases declaration with
      | claim claim =>
          have fixed := atomFixed_of_decl sound.toComparison (.claim claim)
            headMember claim.formal (by simp [declNullaryCons])
          simp only [List.map_cons, Binding.renameDecl, substDecl,
            List.findSome?_cons]
          rw [substituteValueAtom_rename ρg program claim.formal fixed]
          rw [ih tailContained]
          cases Lara.Sigma.wsAtom policy.sigma
              (substituteValueAtom program.valueBindings claim.formal) <;>
            simp
      | leaf leaf =>
          simpa [Binding.renameDecl, substDecl]
            using ih tailContained
      | arg argument =>
          simpa [Binding.renameDecl, substDecl]
            using ih tailContained
      | comparison comparison =>
          simpa [Binding.renameDecl, substDecl]
            using ih tailContained
      | attack attack =>
          simpa [Binding.renameDecl, substDecl]
            using ih tailContained
      | status status =>
          simpa [Binding.renameDecl, substDecl]
            using ih tailContained
      | group group =>
          simpa [Binding.renameDecl, substDecl]
            using ih tailContained

private theorem claimFormalErrors_rename
    {ρg : Binding.GlobalRenaming} {program : Presentation.Program}
    {policy : Presentation.Policy}
    (sound : RenamingSound ρg program policy) :
    claimFormalErrors (Binding.renamePolicy ρg policy)
        (Binding.renameProgram ρg program).valueBindings
        ({ (Binding.renameProgram ρg program) with
          decls :=
            (Binding.renameProgram ρg program).decls.map
              (substDecl
                (Binding.renameProgram ρg program).valueBindings) }) =
      (claimFormalErrors policy program.valueBindings
        ({ program with
          decls := program.decls.map
            (substDecl program.valueBindings) })).map
        (fun error => match error with
          | .invalidValueBinding name =>
              .invalidValueBinding
                ⟨(ρg.prop (⟨name.val⟩ : Presentation.PropId)).val⟩
          | other => other) := by
  change claimFormalErrors policy
        (Binding.renameProgram ρg program).valueBindings
        ({ (Binding.renameProgram ρg program) with
          decls :=
            (Binding.renameProgram ρg program).decls.map
              (substDecl
                (Binding.renameProgram ρg program).valueBindings) }) = _
  unfold claimFormalErrors
  have emptyEq :
      (Binding.renameProgram ρg program).valueBindings.isEmpty =
        program.valueBindings.isEmpty := by
    simp [Binding.renameProgram]
  rw [emptyEq]
  dsimp only
  rw [show (Binding.renameProgram ρg program).decls =
    program.decls.map
      (Binding.renameDecl ρg (programValues program)) by rfl]
  cases empty : program.valueBindings.isEmpty with
  | true => simp [empty]
  | false =>
      simp only [empty, Bool.false_eq_true, if_false]
      have hfirst :=
        firstInvalidClaimId?_rename sound program.decls (by simp)
      cases sourceFound : firstInvalidClaimId? policy.sigma
          (program.decls.map (substDecl program.valueBindings)) with
      | none =>
          rw [sourceFound] at hfirst
          simp only [Option.map_none] at hfirst
          rw [hfirst]
          simp [sourceFound]
      | some name =>
          rw [sourceFound] at hfirst
          simp only [Option.map_some] at hfirst
          rw [hfirst]
          simp [sourceFound]

end Renaming

theorem expandValues_idempotent (policy : Presentation.Policy) {program out : Presentation.Program}
    (h : expandValues policy program = .ok out)
    (hstable : ∀ d ∈ out.decls, NlBraceFree d) :
    expandValues policy out = .ok out := by
  have hsound := expandValues_sound policy h
  cases hsound with
  | intro henv hgamma hbindings hartifact hdigest hpolicy hbackends hdecls =>
      exact expandValues_fixed_point policy hbindings hstable

end Lara.Surface
