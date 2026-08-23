/-
Named proof-term lowering for `nd@1` (`lara-syntax@0.9`, #132).

This is a Lean mirror of the pure presentation pass in
`Lara.Elaborate.NDNamed`, not a verification of the Haskell implementation.
It deliberately abstracts the source identifier classifier and premise-name
resolver: those remain validated-not-verified boundary logic.  Every Haskell
error kind is represented uniformly by `none`.

The pass has two modes.  A payload containing no named marker is returned
byte-identically, leaving even malformed kernel syntax for the strict decoder.
Once a marker selects named mode, premise and theory references and named
binders are lowered to kernel de Bruijn indices; numeric hypotheses are then
rejected, binder names must be fresh, and a final scan rejects any marker that
survived in an opaque formula or unknown subtree.
-/

import Lara.ND
import Lara.Cell

namespace Lara.NDNamed

open Lara.Support (SExpr)
open Lara.Cell (parseCanonNat)

/-! ### Closed wire vocabulary and node recognizers -/

/-- The named extension owns one keyword.  Kernel tags stay in `ND.Tag`, and
`prem` stays in `Cell.Tag`. -/
inductive NamedTag where
  | thy
deriving DecidableEq, Repr

def NamedTag.toString : NamedTag → String
  | .thy => "thy"

def NamedTag.all : List NamedTag := [.thy]

def NamedTag.parse (s : String) : Option NamedTag :=
  NamedTag.all.find? (fun t => t.toString = s)

@[simp] theorem NamedTag.parse_toString (t : NamedTag) :
    NamedTag.parse t.toString = some t := by
  cases t <;> rfl

def premiseSource : SExpr → Option String
  | .list [.atom k, .atom source] =>
      if Lara.Cell.Tag.parse k = some .prem then some source else none
  | _ => none

def theorySource : SExpr → Option String
  | .list [.atom k, .atom source] =>
      if NamedTag.parse k = some .thy then some source else none
  | _ => none

def hypothesisSource : SExpr → Option String
  | .list [.atom k, .atom source] =>
      if Lara.ND.Tag.parse k = some .hyp then some source else none
  | _ => none

def namedHypSource (startsIdent : String → Bool) (e : SExpr) : Option String := do
  let source ← hypothesisSource e
  if startsIdent source then some source else none

def namedAbstraction : SExpr → Option (SExpr × SExpr × SExpr)
  | .list [.atom k, binder, formula, body] =>
      if Lara.ND.Tag.parse k = some .lam then some (binder, formula, body) else none
  | _ => none

def markerHere (startsIdent : String → Bool) (e : SExpr) : Option String :=
  match premiseSource e with
  | some source => some source
  | none =>
      match theorySource e with
      | some source => some source
      | none =>
          match namedHypSource startsIdent e with
          | some source => some source
          | none =>
              match namedAbstraction e with
              | some (binder, _, _) =>
                  match binder with
                  | .atom source => some source
                  | _ => some "<malformed-binder>"
              | none => none

/- The first named marker in leftmost-outermost order.  The same scan selects
named mode and detects residual markers. -/
mutual
  def firstNamedMarker (startsIdent : String → Bool) : SExpr → Option String
    | .atom atom => markerHere startsIdent (.atom atom)
    | .list children =>
        match markerHere startsIdent (.list children) with
        | some source => some source
        | none => firstNamedMarkerList startsIdent children

  def firstNamedMarkerList (startsIdent : String → Bool) :
      List SExpr → Option String
    | [] => none
    | e :: es =>
        match firstNamedMarker startsIdent e with
        | some source => some source
        | none => firstNamedMarkerList startsIdent es
end

/-! ### Binding indices and lowering -/

def binderIndex (sought : String) : List (Option String) → Option Nat
  | [] => none
  | some name :: rest =>
      if name = sought then some 0 else (binderIndex sought rest).map Nat.succ
  | none :: rest => (binderIndex sought rest).map Nat.succ

/-- Current de Bruijn binder depth, including anonymous binders. -/
def depth (binders : List (Option String)) : Nat := binders.length

def kernelHypothesis (index : Nat) : SExpr :=
  .list [.atom Lara.ND.Tag.hyp.toString, .atom (Nat.repr index)]

def premNode (source : String) : SExpr :=
  .list [.atom Lara.Cell.Tag.prem.toString, .atom source]

def thyNode (source : String) : SExpr :=
  .list [.atom NamedTag.thy.toString, .atom source]

@[simp] private theorem parseCanonNat_repr (n : Nat) :
    parseCanonNat (Nat.repr n) = some n := by
  simp [parseCanonNat]

private theorem parseCanonNat_some_canonical {source : String} {n : Nat}
    (h : parseCanonNat source = some n) : source = Nat.repr n := by
  apply Lara.ND.decodeNat_some_canonical
  unfold Lara.ND.decodeNat
  unfold parseCanonNat at h
  cases hs : source.toNat? with
  | none => simp [hs] at h
  | some m => simpa [hs] using h

private theorem parseCanonNat_none_of_identifier
    (startsIdent : String → Bool)
    (hNat : ∀ n, startsIdent (Nat.repr n) = false)
    {source : String} (hsource : startsIdent source = true) :
    parseCanonNat source = none := by
  cases hparse : parseCanonNat source with
  | none => rfl
  | some n =>
      have hcanon := parseCanonNat_some_canonical hparse
      rw [hcanon, hNat n] at hsource
      contradiction

/-- Named-mode recursive lowering.  Branch order is the Haskell pass order;
formula positions in `lam` and `abort` remain opaque. -/
def lowerNamedExpr (startsIdent : String → Bool) (ρ : String → Option Nat)
    (nPrem : Nat) : List (Option String) → SExpr → Option SExpr
  | _, expr@(.atom _) => some expr
  | binders, expr@(.list [.atom k, .atom source]) =>
      if Lara.Cell.Tag.parse k = some .prem then
        match parseCanonNat source with
        | some slot =>
            if slot < nPrem then some (kernelHypothesis (depth binders + slot))
            else none
        | none =>
            if startsIdent source then
              (ρ source).map (fun slot => kernelHypothesis (depth binders + slot))
            else none
      else if NamedTag.parse k = some .thy then
        match parseCanonNat source with
        | some slot => some (kernelHypothesis (depth binders + nPrem + slot))
        | none => none
      else if Lara.ND.Tag.parse k = some .hyp then
        match parseCanonNat source with
        | some _ => none
        | none =>
            if startsIdent source then
              (binderIndex source binders).map kernelHypothesis
            else none
      else some expr
  | binders, expr@(.list [.atom k, formula, body]) =>
      if Lara.ND.Tag.parse k = some .lam then do
        let body' ← lowerNamedExpr startsIdent ρ nPrem (none :: binders) body
        pure (.list [.atom Lara.ND.Tag.lam.toString, formula, body'])
      else if Lara.ND.Tag.parse k = some .app then do
        let fn' ← lowerNamedExpr startsIdent ρ nPrem binders formula
        let arg' ← lowerNamedExpr startsIdent ρ nPrem binders body
        pure (.list [.atom Lara.ND.Tag.app.toString, fn', arg'])
      else if Lara.ND.Tag.parse k = some .abort then do
        let body' ← lowerNamedExpr startsIdent ρ nPrem binders body
        pure (.list [.atom Lara.ND.Tag.abort.toString, formula, body'])
      else some expr
  | binders, expr@(.list [.atom k, binder, formula, body]) =>
      if Lara.ND.Tag.parse k = some .lam then
        match binder with
        | .atom name =>
            if startsIdent name then
              match binderIndex name binders with
              | some _ => none
              | none =>
                  match ρ name with
                  | some _ => none
                  | none => do
                      let body' ← lowerNamedExpr startsIdent ρ nPrem
                        (some name :: binders) body
                      pure (.list [.atom Lara.ND.Tag.lam.toString, formula, body'])
            else none
        | _ => none
      else some expr
  | _, expr@(.list _) => some expr
termination_by _ expr => sizeOf expr

/-- The complete pass: marker-free identity, named recursion, then the same
scan as a residual-marker guard.  Every failure kind is `none`. -/
def lowerNamed (startsIdent : String → Bool) (ρ : String → Option Nat)
    (nPrem : Nat) (binders : List (Option String)) (payload : SExpr) :
    Option SExpr :=
  match firstNamedMarker startsIdent payload with
  | none => some payload
  | some _ => do
      let lowered ← lowerNamedExpr startsIdent ρ nPrem binders payload
      match firstNamedMarker startsIdent lowered with
      | none => some lowered
      | some _ => none

/-! ### Kernel encoders and conservativity -/

/-- The frozen formula wire image, inverse in shape to `ND.decodeFormula`.
In particular an atom key renders as `(atom KEY)`, never as a bare key. -/
def encodeFormula : Lara.ND.Formula → SExpr
  | .atom key => .list [.atom Lara.ND.Tag.atom.toString, .atom key]
  | .fls => .atom Lara.ND.Tag.fls.toString
  | .imp a b => .list [.atom Lara.ND.Tag.imp.toString,
      encodeFormula a, encodeFormula b]

def encodeCert : Lara.ND.Cert → SExpr
  | .hyp index => kernelHypothesis index
  | .lam formula body => .list [.atom Lara.ND.Tag.lam.toString,
      encodeFormula formula, encodeCert body]
  | .app fn arg => .list [.atom Lara.ND.Tag.app.toString,
      encodeCert fn, encodeCert arg]
  | .abort formula body => .list [.atom Lara.ND.Tag.abort.toString,
      encodeFormula formula, encodeCert body]

theorem decodeFormula_encodeFormula (formula : Lara.ND.Formula) :
    Lara.ND.decodeFormula (encodeFormula formula) = some formula := by
  induction formula <;> simp_all [encodeFormula, Lara.ND.decodeFormula,
    Lara.ND.Tag.toString, Lara.ND.Tag.parse]

theorem decodeCert_encodeCert (cert : Lara.ND.Cert) :
    Lara.ND.decodeCert (encodeCert cert) = some cert := by
  induction cert <;> simp_all [encodeCert, kernelHypothesis,
    Lara.ND.decodeCert, Lara.ND.Tag.toString, Lara.ND.Tag.parse,
    Lara.ND.decodeNat_repr, decodeFormula_encodeFormula]

theorem encodeFormula_markerFree (startsIdent : String → Bool)
    (formula : Lara.ND.Formula) :
    firstNamedMarker startsIdent (encodeFormula formula) = none := by
  induction formula <;> simp_all [encodeFormula, firstNamedMarker,
    firstNamedMarkerList, markerHere, premiseSource, theorySource,
    namedHypSource, hypothesisSource, namedAbstraction, NamedTag.parse,
    NamedTag.all, NamedTag.toString, Lara.Cell.Tag.parse, Lara.Cell.Tag.all,
    Lara.Cell.Tag.toString, Lara.ND.Tag.parse, Lara.ND.Tag.toString]

/-- Kernel certificates contain no named marker when canonical numerals do not
start source identifiers. -/
theorem encodeCert_markerFree (startsIdent : String → Bool)
    (hNat : ∀ n, startsIdent (Nat.repr n) = false) :
    ∀ cert, firstNamedMarker startsIdent (encodeCert cert) = none := by
  intro cert
  induction cert <;> simp_all [encodeCert, kernelHypothesis,
    firstNamedMarker, firstNamedMarkerList, markerHere, premiseSource,
    theorySource, namedHypSource, hypothesisSource, namedAbstraction,
    NamedTag.parse, NamedTag.all, NamedTag.toString, Lara.Cell.Tag.parse,
    Lara.Cell.Tag.all, Lara.Cell.Tag.toString, Lara.ND.Tag.parse,
    Lara.ND.Tag.toString, encodeFormula_markerFree]

/-- **Conservativity.** The pass is byte-identical on every kernel certificate,
through the marker-free mode branch. -/
theorem lowerNamed_id_of_kernel (startsIdent : String → Bool)
    (ρ : String → Option Nat) (nPrem : Nat)
    (hNat : ∀ n, startsIdent (Nat.repr n) = false) :
    ∀ cert binders,
      lowerNamed startsIdent ρ nPrem binders (encodeCert cert) =
        some (encodeCert cert) := by
  intro cert binders
  simp [lowerNamed, encodeCert_markerFree startsIdent hNat cert]

/-! ### Declarative named terms and translation -/

inductive NCert where
  | hypX : String → NCert
  | prem : Nat ⊕ String → NCert
  | thy : Nat → NCert
  | lam : Option String → Lara.ND.Formula → NCert → NCert
  | app : NCert → NCert → NCert
  | abort : Lara.ND.Formula → NCert → NCert
deriving DecidableEq, Repr

def render : NCert → SExpr
  | .hypX name => .list [.atom Lara.ND.Tag.hyp.toString, .atom name]
  | .prem (.inl slot) => premNode (Nat.repr slot)
  | .prem (.inr name) => premNode name
  | .thy slot => thyNode (Nat.repr slot)
  | .lam none formula body => .list [.atom Lara.ND.Tag.lam.toString,
      encodeFormula formula, render body]
  | .lam (some name) formula body => .list [.atom Lara.ND.Tag.lam.toString,
      .atom name, encodeFormula formula, render body]
  | .app fn arg => .list [.atom Lara.ND.Tag.app.toString, render fn, render arg]
  | .abort formula body => .list [.atom Lara.ND.Tag.abort.toString,
      encodeFormula formula, render body]

def toDB (ρ : String → Option Nat) (nPrem : Nat) :
    List (Option String) → NCert → Option Lara.ND.Cert
  | binders, .hypX name => (binderIndex name binders).map Lara.ND.Cert.hyp
  | binders, .prem (.inl slot) =>
      if slot < nPrem then some (.hyp (depth binders + slot)) else none
  | binders, .prem (.inr name) =>
      (ρ name).map (fun slot => .hyp (depth binders + slot))
  | binders, .thy slot => some (.hyp (depth binders + nPrem + slot))
  | binders, .lam binder formula body => do
      let body' ← toDB ρ nPrem (binder :: binders) body
      pure (.lam formula body')
  | binders, .app fn arg => do
      let fn' ← toDB ρ nPrem binders fn
      let arg' ← toDB ρ nPrem binders arg
      pure (.app fn' arg')
  | binders, .abort formula body => do
      let body' ← toDB ρ nPrem binders body
      pure (.abort formula body')

/-- Real source-side success conditions: identifier hypotheses are bound;
numeric and symbolic premises are in range; named binders neither shadow a
local binder nor collide with a resolvable premise name. -/
inductive WellFormed (startsIdent : String → Bool) (ρ : String → Option Nat)
    (nPrem : Nat) : List (Option String) → NCert → Prop where
  | hypX {binders name index} :
      startsIdent name = true → binderIndex name binders = some index →
      WellFormed startsIdent ρ nPrem binders (.hypX name)
  | premNat {binders slot} : slot < nPrem →
      WellFormed startsIdent ρ nPrem binders (.prem (.inl slot))
  | premName {binders name slot} :
      startsIdent name = true → ρ name = some slot → slot < nPrem →
      WellFormed startsIdent ρ nPrem binders (.prem (.inr name))
  | thy {binders slot} :
      WellFormed startsIdent ρ nPrem binders (.thy slot)
  | lamAnon {binders formula body} :
      WellFormed startsIdent ρ nPrem (none :: binders) body →
      WellFormed startsIdent ρ nPrem binders (.lam none formula body)
  | lamNamed {binders name formula body} :
      startsIdent name = true → binderIndex name binders = none → ρ name = none →
      WellFormed startsIdent ρ nPrem (some name :: binders) body →
      WellFormed startsIdent ρ nPrem binders (.lam (some name) formula body)
  | app {binders fn arg} :
      WellFormed startsIdent ρ nPrem binders fn →
      WellFormed startsIdent ρ nPrem binders arg →
      WellFormed startsIdent ρ nPrem binders (.app fn arg)
  | abort {binders formula body} :
      WellFormed startsIdent ρ nPrem binders body →
      WellFormed startsIdent ρ nPrem binders (.abort formula body)

private theorem toDB_eq_some_of_wellFormed
    (startsIdent : String → Bool) (ρ : String → Option Nat) (nPrem : Nat)
    {binders : List (Option String)} {term : NCert}
    (wf : WellFormed startsIdent ρ nPrem binders term) :
    ∃ cert, toDB ρ nPrem binders term = some cert := by
  induction wf with
  | hypX _ hindex => simp [toDB, hindex]
  | premNat hslot => simp [toDB, hslot]
  | premName _ hresolve _ => simp [toDB, hresolve]
  | thy => simp [toDB]
  | lamAnon wf ih =>
      obtain ⟨body, hbody⟩ := ih
      simp [toDB, hbody]
  | lamNamed _ _ _ wf ih =>
      obtain ⟨body, hbody⟩ := ih
      simp [toDB, hbody]
  | app wfFn wfArg ihFn ihArg =>
      obtain ⟨fn, hfn⟩ := ihFn
      obtain ⟨arg, harg⟩ := ihArg
      exact ⟨.app fn arg, by simp [toDB, hfn, harg]⟩
  | abort wf ih =>
      obtain ⟨body, hbody⟩ := ih
      simp [toDB, hbody]

private theorem lowerNamedExpr_eq_translation
    (startsIdent : String → Bool) (ρ : String → Option Nat) (nPrem : Nat)
    (hNat : ∀ n, startsIdent (Nat.repr n) = false)
    {binders : List (Option String)} {term : NCert}
    (wf : WellFormed startsIdent ρ nPrem binders term) :
    lowerNamedExpr startsIdent ρ nPrem binders (render term) =
      (toDB ρ nPrem binders term).map encodeCert := by
  induction wf with
  | hypX hsource hindex =>
      have hparse := parseCanonNat_none_of_identifier startsIdent hNat hsource
      simp [render, lowerNamedExpr, toDB, encodeCert, kernelHypothesis,
        Lara.Cell.Tag.parse, Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
        NamedTag.parse, NamedTag.all, NamedTag.toString, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString, hparse, hsource, hindex]
  | premNat hslot =>
      simp [render, premNode, lowerNamedExpr, toDB, encodeCert, kernelHypothesis,
        Lara.Cell.Tag.parse, Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
        Lara.ND.Tag.toString, hslot]
  | premName hsource hresolve hrange =>
      have hparse := parseCanonNat_none_of_identifier startsIdent hNat hsource
      simp [render, premNode, lowerNamedExpr, toDB, encodeCert, kernelHypothesis,
        Lara.Cell.Tag.parse, Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
        Lara.ND.Tag.toString, hparse, hsource, hresolve]
  | thy =>
      simp [render, thyNode, lowerNamedExpr, toDB, encodeCert, kernelHypothesis,
        Lara.Cell.Tag.parse, Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
        NamedTag.parse, NamedTag.all, NamedTag.toString, Lara.ND.Tag.toString]
  | lamAnon wf ih =>
      obtain ⟨body, hbody⟩ :=
        toDB_eq_some_of_wellFormed startsIdent ρ nPrem wf
      simp [render, lowerNamedExpr, toDB, encodeCert, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString, hbody, ih]
  | lamNamed hsource hfresh hρ wf ih =>
      obtain ⟨body, hbody⟩ :=
        toDB_eq_some_of_wellFormed startsIdent ρ nPrem wf
      simp [render, lowerNamedExpr, toDB, encodeCert, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString, hsource, hfresh, hρ, hbody, ih]
  | app wfFn wfArg ihFn ihArg =>
      obtain ⟨fn, hfn⟩ :=
        toDB_eq_some_of_wellFormed startsIdent ρ nPrem wfFn
      obtain ⟨arg, harg⟩ :=
        toDB_eq_some_of_wellFormed startsIdent ρ nPrem wfArg
      simp [render, lowerNamedExpr, toDB, encodeCert, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString, hfn, harg, ihFn, ihArg]
  | abort wf ih =>
      obtain ⟨body, hbody⟩ :=
        toDB_eq_some_of_wellFormed startsIdent ρ nPrem wf
      simp [render, lowerNamedExpr, toDB, encodeCert, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString, hbody, ih]

private theorem firstNamedMarker_render_some
    (startsIdent : String → Bool) (ρ : String → Option Nat) (nPrem : Nat)
    {binders : List (Option String)} {term : NCert}
    (wf : WellFormed startsIdent ρ nPrem binders term) :
    ∃ source, firstNamedMarker startsIdent (render term) = some source := by
  induction wf with
  | hypX hsource _ =>
      simp [render, firstNamedMarker, markerHere, premiseSource,
        theorySource, namedHypSource, hypothesisSource,
        Lara.Cell.Tag.parse, Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
        NamedTag.parse, NamedTag.all, NamedTag.toString, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString, hsource]
  | premNat _ =>
      simp [render, premNode, firstNamedMarker,
        markerHere, premiseSource, Lara.Cell.Tag.parse, Lara.Cell.Tag.all,
        Lara.Cell.Tag.toString]
  | premName _ _ _ =>
      simp [render, premNode, firstNamedMarker, markerHere,
        premiseSource, Lara.Cell.Tag.parse, Lara.Cell.Tag.all,
        Lara.Cell.Tag.toString]
  | thy =>
      simp [render, thyNode, firstNamedMarker,
        markerHere, premiseSource, theorySource, Lara.Cell.Tag.parse,
        Lara.Cell.Tag.all, Lara.Cell.Tag.toString, NamedTag.parse,
        NamedTag.all, NamedTag.toString]
  | lamAnon wf ih =>
      obtain ⟨source, hsource⟩ := ih
      exact ⟨source, by simp [render, firstNamedMarker, firstNamedMarkerList,
        markerHere, premiseSource, theorySource, namedHypSource,
        hypothesisSource, namedAbstraction, encodeFormula_markerFree, hsource]⟩
  | lamNamed =>
      simp [render, firstNamedMarker, markerHere,
        premiseSource, theorySource, namedHypSource, hypothesisSource,
        namedAbstraction, Lara.ND.Tag.parse, Lara.ND.Tag.toString]
  | app wfFn wfArg ihFn ihArg =>
      obtain ⟨source, hsource⟩ := ihFn
      exact ⟨source, by simp [render, firstNamedMarker, firstNamedMarkerList,
        markerHere, premiseSource, theorySource, namedHypSource,
        hypothesisSource, namedAbstraction, hsource]⟩
  | abort wf ih =>
      obtain ⟨source, hsource⟩ := ih
      exact ⟨source, by simp [render, firstNamedMarker, firstNamedMarkerList,
        markerHere, premiseSource, theorySource, namedHypSource,
        hypothesisSource, namedAbstraction, encodeFormula_markerFree, hsource]⟩

/-- **Translation.** Every well-formed named term lowers to exactly the
independent de Bruijn translation, encoded in the strict kernel wire image. -/
theorem lowerNamed_eq_translation (startsIdent : String → Bool)
    (ρ : String → Option Nat) (nPrem : Nat) {binders : List (Option String)}
    {term : NCert} (hNat : ∀ n, startsIdent (Nat.repr n) = false)
    (wf : WellFormed startsIdent ρ nPrem binders term) :
    lowerNamed startsIdent ρ nPrem binders (render term) =
      (toDB ρ nPrem binders term).map encodeCert := by
  obtain ⟨cert, hcert⟩ := toDB_eq_some_of_wellFormed startsIdent ρ nPrem wf
  obtain ⟨source, hmarker⟩ :=
    firstNamedMarker_render_some startsIdent ρ nPrem wf
  rw [lowerNamed]
  simp only [hmarker]
  rw [lowerNamedExpr_eq_translation startsIdent ρ nPrem hNat wf, hcert]
  simp [encodeCert_markerFree startsIdent hNat cert]

/-! ### Executable conformance vectors 1–7 and 17–21 -/

private def vectorStarts (source : String) : Bool :=
  ["a", "b", "h", "k", "é!"].contains source

private def vectorResolver : String → Option Nat
  | "a" => some 0
  | "b" => some 1
  | _ => none

private def atomFormula (key : String) : SExpr := encodeFormula (.atom key)

#guard lowerNamed vectorStarts vectorResolver 2 [] (kernelHypothesis 0) ==
  some (kernelHypothesis 0)

#guard lowerNamed vectorStarts vectorResolver 2 [] (premNode "1") ==
  some (kernelHypothesis 1)

#guard lowerNamed vectorStarts vectorResolver 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>", premNode "b"]) ==
  some (.list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>",
    kernelHypothesis 2])

#guard lowerNamed vectorStarts vectorResolver 2 []
    (.list [.atom Lara.ND.Tag.app.toString,
      .list [.atom Lara.ND.Tag.lam.toString, .atom "h", atomFormula "<F>",
        .list [.atom Lara.ND.Tag.hyp.toString, .atom "h"]],
      premNode "a"]) ==
  some (.list [.atom Lara.ND.Tag.app.toString,
    .list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>",
      kernelHypothesis 0], kernelHypothesis 0])

#guard lowerNamed vectorStarts vectorResolver 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, .atom "h", atomFormula "<F>",
      .list [.atom Lara.ND.Tag.lam.toString, .atom "k", atomFormula "<G>",
        .list [.atom Lara.ND.Tag.hyp.toString, .atom "h"]]]) ==
  some (.list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>",
    .list [.atom Lara.ND.Tag.lam.toString, atomFormula "<G>",
      kernelHypothesis 1]])

#guard lowerNamed vectorStarts vectorResolver 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>", thyNode "0"]) ==
  some (.list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>",
    kernelHypothesis 3])

#guard lowerNamed vectorStarts vectorResolver 2 [] (premNode "2") == none

-- D9: once named mode is selected, a numeric kernel hypothesis is rejected.
#guard lowerNamed vectorStarts vectorResolver 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, .atom "h", atomFormula "<F>",
      kernelHypothesis 0]) == none

#guard lowerNamed vectorStarts vectorResolver 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, .atom "h", atomFormula "<F>",
      premNode "0"]) ==
  some (.list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>",
    kernelHypothesis 1])

#guard lowerNamed vectorStarts vectorResolver 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, .atom "é!", atomFormula "<F>",
      .list [.atom Lara.ND.Tag.hyp.toString, .atom "é!"]]) ==
  some (.list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>",
    kernelHypothesis 0])

-- D10: a named binder may not collide with a resolvable premise name.
#guard lowerNamed vectorStarts vectorResolver 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, .atom "a", atomFormula "<F>",
      premNode "b"]) == none

#guard lowerNamed vectorStarts vectorResolver 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, .atom "h", atomFormula "<F>",
      .list [.atom Lara.ND.Tag.hyp.toString, .atom "007"]]) == none

end Lara.NDNamed
