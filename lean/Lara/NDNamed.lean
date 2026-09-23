/-
Named proof-term lowering for `nd@1` (`lara-syntax@0.9`; source-authored
formula annotations `lara-syntax@0.10`).

This is a Lean mirror of the pure presentation pass in
`Lara.Elaborate.NDNamed`, not a verification of the Haskell implementation.
It deliberately abstracts the source identifier classifier, the premise-name
resolver, and — new at `@0.10` — the proposition encoder `encodeProp`, the
composition of the surface proposition parser with `encodeAtomKey ∘ nf` whose
Haskell implementation remains validated-not-verified boundary logic.  Every
Haskell error kind is represented uniformly by `none`.

The pass has two modes.  A payload containing no named marker is returned
byte-identically, leaving even malformed kernel syntax for the strict decoder.
Once a marker selects named mode, premise and theory references and named
binders are lowered to kernel de Bruijn indices, `(prop TEXT)` formula
annotations are lowered to the backend's opaque `(atom KEY)` encoding, numeric
hypotheses are then rejected, binder names must be fresh, and a final scan
rejects any marker that survived in an opaque or unknown subtree.
-/

import Lara.ND
import Lara.Cell

namespace Lara.NDNamed

open Lara.Support (SExpr)
open Lara.Cell (parseCanonNat)

/-! ### Closed wire vocabulary and node recognizers -/

/-- The named extension owns two keywords.  Kernel tags stay in `ND.Tag`, and
`prem` stays in `Cell.Tag`. -/
inductive NamedTag where
  | thy
  | prop
deriving DecidableEq, Repr

def NamedTag.toString : NamedTag → String
  | .thy => "thy"
  | .prop => "prop"

def NamedTag.all : List NamedTag := [.thy, .prop]

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

/-- A source-authored formula annotation.  Like `prem` and `thy`, only the
exact two-field atom shape is a marker: a `prop` head with any other arity or
a non-atom payload is inert junk owned by the strict decoder. -/
def propSource : SExpr → Option String
  | .list [.atom k, .atom source] =>
      if NamedTag.parse k = some .prop then some source else none
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
          match propSource e with
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

def propNode (text : String) : SExpr :=
  .list [.atom NamedTag.prop.toString, .atom text]

def atomNode (key : String) : SExpr :=
  .list [.atom Lara.ND.Tag.atom.toString, .atom key]

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

/-- Formula-annotation lowering.  A `(prop TEXT)` node becomes the backend's
`(atom KEY)` node through the abstract proposition encoder; an `imp` node is
traversed to reach nested `prop` spellings and rebuilds byte-identically when
none occur; everything else — `false`, `(atom KEY)`, junk — passes through
for the strict decoder to judge. -/
def lowerFormula (encodeProp : String → Option String) : SExpr → Option SExpr
  | e@(.list [.atom k, .atom source]) =>
      if NamedTag.parse k = some .prop then
        (encodeProp source).map atomNode
      else some e
  | e@(.list [.atom k, a, b]) =>
      if Lara.ND.Tag.parse k = some .imp then do
        let a' ← lowerFormula encodeProp a
        let b' ← lowerFormula encodeProp b
        pure (.list [.atom Lara.ND.Tag.imp.toString, a', b'])
      else some e
  | e => some e
termination_by e => sizeOf e

/-- Named-mode recursive lowering.  Branch order is the Haskell pass order;
`lam` and `abort` formula positions are lowered by `lowerFormula`. -/
def lowerNamedExpr (startsIdent : String → Bool) (ρ : String → Option Nat)
    (encodeProp : String → Option String) (nPrem : Nat) :
    List (Option String) → SExpr → Option SExpr
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
        let formula' ← lowerFormula encodeProp formula
        let body' ← lowerNamedExpr startsIdent ρ encodeProp nPrem (none :: binders) body
        pure (.list [.atom Lara.ND.Tag.lam.toString, formula', body'])
      else if Lara.ND.Tag.parse k = some .app then do
        let fn' ← lowerNamedExpr startsIdent ρ encodeProp nPrem binders formula
        let arg' ← lowerNamedExpr startsIdent ρ encodeProp nPrem binders body
        pure (.list [.atom Lara.ND.Tag.app.toString, fn', arg'])
      else if Lara.ND.Tag.parse k = some .abort then do
        let formula' ← lowerFormula encodeProp formula
        let body' ← lowerNamedExpr startsIdent ρ encodeProp nPrem binders body
        pure (.list [.atom Lara.ND.Tag.abort.toString, formula', body'])
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
                      let formula' ← lowerFormula encodeProp formula
                      let body' ← lowerNamedExpr startsIdent ρ encodeProp nPrem
                        (some name :: binders) body
                      pure (.list [.atom Lara.ND.Tag.lam.toString, formula', body'])
            else none
        | _ => none
      else some expr
  | _, expr@(.list _) => some expr
termination_by _ expr => sizeOf expr

/-- The complete pass: marker-free identity, named recursion, then the same
scan as a residual-marker guard.  Every failure kind is `none`. -/
def lowerNamed (startsIdent : String → Bool) (ρ : String → Option Nat)
    (encodeProp : String → Option String) (nPrem : Nat)
    (binders : List (Option String)) (payload : SExpr) : Option SExpr :=
  match firstNamedMarker startsIdent payload with
  | none => some payload
  | some _ => do
      let lowered ← lowerNamedExpr startsIdent ρ encodeProp nPrem binders payload
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
    firstNamedMarkerList, markerHere, premiseSource, theorySource, propSource,
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
    theorySource, propSource, namedHypSource, hypothesisSource,
    namedAbstraction, NamedTag.parse, NamedTag.all, NamedTag.toString,
    Lara.Cell.Tag.parse, Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
    Lara.ND.Tag.parse, Lara.ND.Tag.toString, encodeFormula_markerFree]

/-- **Conservativity.** The pass is byte-identical on every kernel certificate,
through the marker-free mode branch. -/
theorem lowerNamed_id_of_kernel (startsIdent : String → Bool)
    (ρ : String → Option Nat) (encodeProp : String → Option String)
    (nPrem : Nat) (hNat : ∀ n, startsIdent (Nat.repr n) = false) :
    ∀ cert binders,
      lowerNamed startsIdent ρ encodeProp nPrem binders (encodeCert cert) =
        some (encodeCert cert) := by
  intro cert binders
  simp [lowerNamed, encodeCert_markerFree startsIdent hNat cert]

/-! ### Declarative named formulas, named terms, and translation -/

/-- The named-mode formula presentation: the frozen spellings plus the
source-authored `(prop TEXT)` annotation. -/
inductive NFormula where
  | fls : NFormula
  | atomKey : String → NFormula
  | prop : String → NFormula
  | imp : NFormula → NFormula → NFormula
deriving DecidableEq, Repr

def renderFormula : NFormula → SExpr
  | .fls => .atom Lara.ND.Tag.fls.toString
  | .atomKey key => atomNode key
  | .prop text => propNode text
  | .imp a b => .list [.atom Lara.ND.Tag.imp.toString,
      renderFormula a, renderFormula b]

/-- The independent formula translation: `(prop TEXT)` encodes through the
abstract proposition encoder, everything else is already kernel material. -/
def toFormula (encodeProp : String → Option String) :
    NFormula → Option Lara.ND.Formula
  | .fls => some .fls
  | .atomKey key => some (.atom key)
  | .prop text => (encodeProp text).map .atom
  | .imp a b => do
      let a' ← toFormula encodeProp a
      let b' ← toFormula encodeProp b
      pure (.imp a' b')

/-- A named formula is well formed when every authored proposition text is
accepted by the encoder. -/
inductive WFFormula (encodeProp : String → Option String) : NFormula → Prop where
  | fls : WFFormula encodeProp .fls
  | atomKey {key} : WFFormula encodeProp (.atomKey key)
  | prop {text key} : encodeProp text = some key →
      WFFormula encodeProp (.prop text)
  | imp {a b} : WFFormula encodeProp a → WFFormula encodeProp b →
      WFFormula encodeProp (.imp a b)

private theorem toFormula_eq_some_of_wf
    (encodeProp : String → Option String) {formula : NFormula}
    (wf : WFFormula encodeProp formula) :
    ∃ result, toFormula encodeProp formula = some result := by
  induction wf with
  | fls => exact ⟨.fls, rfl⟩
  | atomKey => exact ⟨_, rfl⟩
  | @prop text key henc => exact ⟨.atom key, by simp [toFormula, henc]⟩
  | imp _ _ iha ihb =>
      obtain ⟨a', ha⟩ := iha
      obtain ⟨b', hb⟩ := ihb
      exact ⟨.imp a' b', by simp [toFormula, ha, hb]⟩

/-- **Formula translation.** Every well-formed named formula lowers to exactly
the kernel wire image of its independent translation. -/
theorem lowerFormula_eq_translation
    (encodeProp : String → Option String) {formula : NFormula}
    (wf : WFFormula encodeProp formula) :
    lowerFormula encodeProp (renderFormula formula) =
      (toFormula encodeProp formula).map encodeFormula := by
  induction wf with
  | fls =>
      simp [renderFormula, lowerFormula, toFormula, encodeFormula]
  | atomKey =>
      simp [renderFormula, atomNode, lowerFormula, toFormula, encodeFormula,
        NamedTag.parse, NamedTag.all, NamedTag.toString, Lara.ND.Tag.toString]
  | prop henc =>
      simp [renderFormula, propNode, atomNode, lowerFormula, toFormula,
        encodeFormula, NamedTag.parse, NamedTag.all, NamedTag.toString, henc]
  | imp wfa wfb iha ihb =>
      obtain ⟨a', ha⟩ := toFormula_eq_some_of_wf encodeProp wfa
      obtain ⟨b', hb⟩ := toFormula_eq_some_of_wf encodeProp wfb
      simp [renderFormula, lowerFormula, toFormula, encodeFormula,
        Lara.ND.Tag.parse, Lara.ND.Tag.toString, ha, hb, iha, ihb]

inductive NCert where
  | hypX : String → NCert
  | prem : Nat ⊕ String → NCert
  | thy : Nat → NCert
  | lam : Option String → NFormula → NCert → NCert
  | app : NCert → NCert → NCert
  | abort : NFormula → NCert → NCert
deriving DecidableEq, Repr

def render : NCert → SExpr
  | .hypX name => .list [.atom Lara.ND.Tag.hyp.toString, .atom name]
  | .prem (.inl slot) => premNode (Nat.repr slot)
  | .prem (.inr name) => premNode name
  | .thy slot => thyNode (Nat.repr slot)
  | .lam none formula body => .list [.atom Lara.ND.Tag.lam.toString,
      renderFormula formula, render body]
  | .lam (some name) formula body => .list [.atom Lara.ND.Tag.lam.toString,
      .atom name, renderFormula formula, render body]
  | .app fn arg => .list [.atom Lara.ND.Tag.app.toString, render fn, render arg]
  | .abort formula body => .list [.atom Lara.ND.Tag.abort.toString,
      renderFormula formula, render body]

def toDB (ρ : String → Option Nat) (encodeProp : String → Option String)
    (nPrem : Nat) : List (Option String) → NCert → Option Lara.ND.Cert
  | binders, .hypX name => (binderIndex name binders).map Lara.ND.Cert.hyp
  | binders, .prem (.inl slot) =>
      if slot < nPrem then some (.hyp (depth binders + slot)) else none
  | binders, .prem (.inr name) =>
      (ρ name).map (fun slot => .hyp (depth binders + slot))
  | binders, .thy slot => some (.hyp (depth binders + nPrem + slot))
  | binders, .lam binder formula body => do
      let formula' ← toFormula encodeProp formula
      let body' ← toDB ρ encodeProp nPrem (binder :: binders) body
      pure (.lam formula' body')
  | binders, .app fn arg => do
      let fn' ← toDB ρ encodeProp nPrem binders fn
      let arg' ← toDB ρ encodeProp nPrem binders arg
      pure (.app fn' arg')
  | binders, .abort formula body => do
      let formula' ← toFormula encodeProp formula
      let body' ← toDB ρ encodeProp nPrem binders body
      pure (.abort formula' body')

/-- Real source-side success conditions: identifier hypotheses are bound;
numeric and symbolic premises are in range; named binders neither shadow a
local binder nor collide with a resolvable premise name; formula annotations
are well formed. -/
inductive WellFormed (startsIdent : String → Bool) (ρ : String → Option Nat)
    (encodeProp : String → Option String) (nPrem : Nat) :
    List (Option String) → NCert → Prop where
  | hypX {binders name index} :
      startsIdent name = true → binderIndex name binders = some index →
      WellFormed startsIdent ρ encodeProp nPrem binders (.hypX name)
  | premNat {binders slot} : slot < nPrem →
      WellFormed startsIdent ρ encodeProp nPrem binders (.prem (.inl slot))
  | premName {binders name slot} :
      startsIdent name = true → ρ name = some slot → slot < nPrem →
      WellFormed startsIdent ρ encodeProp nPrem binders (.prem (.inr name))
  | thy {binders slot} :
      WellFormed startsIdent ρ encodeProp nPrem binders (.thy slot)
  | lamAnon {binders formula body} :
      WFFormula encodeProp formula →
      WellFormed startsIdent ρ encodeProp nPrem (none :: binders) body →
      WellFormed startsIdent ρ encodeProp nPrem binders (.lam none formula body)
  | lamNamed {binders name formula body} :
      startsIdent name = true → binderIndex name binders = none → ρ name = none →
      WFFormula encodeProp formula →
      WellFormed startsIdent ρ encodeProp nPrem (some name :: binders) body →
      WellFormed startsIdent ρ encodeProp nPrem binders (.lam (some name) formula body)
  | app {binders fn arg} :
      WellFormed startsIdent ρ encodeProp nPrem binders fn →
      WellFormed startsIdent ρ encodeProp nPrem binders arg →
      WellFormed startsIdent ρ encodeProp nPrem binders (.app fn arg)
  | abort {binders formula body} :
      WFFormula encodeProp formula →
      WellFormed startsIdent ρ encodeProp nPrem binders body →
      WellFormed startsIdent ρ encodeProp nPrem binders (.abort formula body)

private theorem toDB_eq_some_of_wellFormed
    (startsIdent : String → Bool) (ρ : String → Option Nat)
    (encodeProp : String → Option String) (nPrem : Nat)
    {binders : List (Option String)} {term : NCert}
    (wf : WellFormed startsIdent ρ encodeProp nPrem binders term) :
    ∃ cert, toDB ρ encodeProp nPrem binders term = some cert := by
  induction wf with
  | hypX _ hindex => simp [toDB, hindex]
  | premNat hslot => simp [toDB, hslot]
  | premName _ hresolve _ => simp [toDB, hresolve]
  | thy => simp [toDB]
  | lamAnon wff wf ih =>
      obtain ⟨formula, hformula⟩ := toFormula_eq_some_of_wf encodeProp wff
      obtain ⟨body, hbody⟩ := ih
      simp [toDB, hformula, hbody]
  | lamNamed _ _ _ wff wf ih =>
      obtain ⟨formula, hformula⟩ := toFormula_eq_some_of_wf encodeProp wff
      obtain ⟨body, hbody⟩ := ih
      simp [toDB, hformula, hbody]
  | app wfFn wfArg ihFn ihArg =>
      obtain ⟨fn, hfn⟩ := ihFn
      obtain ⟨arg, harg⟩ := ihArg
      exact ⟨.app fn arg, by simp [toDB, hfn, harg]⟩
  | abort wff wf ih =>
      obtain ⟨formula, hformula⟩ := toFormula_eq_some_of_wf encodeProp wff
      obtain ⟨body, hbody⟩ := ih
      simp [toDB, hformula, hbody]

private theorem lowerNamedExpr_eq_translation
    (startsIdent : String → Bool) (ρ : String → Option Nat)
    (encodeProp : String → Option String) (nPrem : Nat)
    (hNat : ∀ n, startsIdent (Nat.repr n) = false)
    {binders : List (Option String)} {term : NCert}
    (wf : WellFormed startsIdent ρ encodeProp nPrem binders term) :
    lowerNamedExpr startsIdent ρ encodeProp nPrem binders (render term) =
      (toDB ρ encodeProp nPrem binders term).map encodeCert := by
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
  | lamAnon wff wf ih =>
      obtain ⟨formula', hformula⟩ := toFormula_eq_some_of_wf encodeProp wff
      obtain ⟨body, hbody⟩ :=
        toDB_eq_some_of_wellFormed startsIdent ρ encodeProp nPrem wf
      have hlow := lowerFormula_eq_translation encodeProp wff
      simp [render, lowerNamedExpr, toDB, encodeCert, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString, hformula, hbody, hlow, ih]
  | lamNamed hsource hfresh hρ wff wf ih =>
      obtain ⟨formula', hformula⟩ := toFormula_eq_some_of_wf encodeProp wff
      obtain ⟨body, hbody⟩ :=
        toDB_eq_some_of_wellFormed startsIdent ρ encodeProp nPrem wf
      have hlow := lowerFormula_eq_translation encodeProp wff
      simp [render, lowerNamedExpr, toDB, encodeCert, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString, hsource, hfresh, hρ, hformula, hbody, hlow, ih]
  | app wfFn wfArg ihFn ihArg =>
      obtain ⟨fn, hfn⟩ :=
        toDB_eq_some_of_wellFormed startsIdent ρ encodeProp nPrem wfFn
      obtain ⟨arg, harg⟩ :=
        toDB_eq_some_of_wellFormed startsIdent ρ encodeProp nPrem wfArg
      simp [render, lowerNamedExpr, toDB, encodeCert, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString, hfn, harg, ihFn, ihArg]
  | abort wff wf ih =>
      obtain ⟨formula', hformula⟩ := toFormula_eq_some_of_wf encodeProp wff
      obtain ⟨body, hbody⟩ :=
        toDB_eq_some_of_wellFormed startsIdent ρ encodeProp nPrem wf
      have hlow := lowerFormula_eq_translation encodeProp wff
      simp [render, lowerNamedExpr, toDB, encodeCert, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString, hformula, hbody, hlow, ih]

private theorem firstNamedMarker_render_some
    (startsIdent : String → Bool) (ρ : String → Option Nat)
    (encodeProp : String → Option String) (nPrem : Nat)
    {binders : List (Option String)} {term : NCert}
    (wf : WellFormed startsIdent ρ encodeProp nPrem binders term) :
    ∃ source, firstNamedMarker startsIdent (render term) = some source := by
  induction wf with
  | hypX hsource _ =>
      simp [render, firstNamedMarker, markerHere, premiseSource,
        theorySource, propSource, namedHypSource, hypothesisSource,
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
  | @lamAnon binders formula body _ _ ih =>
      obtain ⟨source, hsource⟩ := ih
      cases hf : firstNamedMarker startsIdent (renderFormula formula) with
      | some formulaSource =>
          exact ⟨formulaSource, by
            simp [render, firstNamedMarker, firstNamedMarkerList, markerHere,
              premiseSource, theorySource, propSource, namedHypSource,
              hypothesisSource, namedAbstraction, hf]⟩
      | none =>
          exact ⟨source, by
            simp [render, firstNamedMarker, firstNamedMarkerList, markerHere,
              premiseSource, theorySource, propSource, namedHypSource,
              hypothesisSource, namedAbstraction, hf, hsource]⟩
  | lamNamed =>
      simp [render, firstNamedMarker, markerHere,
        premiseSource, theorySource, propSource, namedHypSource,
        hypothesisSource, namedAbstraction, Lara.ND.Tag.parse,
        Lara.ND.Tag.toString]
  | app wfFn wfArg ihFn ihArg =>
      obtain ⟨source, hsource⟩ := ihFn
      exact ⟨source, by simp [render, firstNamedMarker, firstNamedMarkerList,
        markerHere, premiseSource, theorySource, propSource, namedHypSource,
        hypothesisSource, namedAbstraction, hsource]⟩
  | @abort binders formula body _ _ ih =>
      obtain ⟨source, hsource⟩ := ih
      cases hf : firstNamedMarker startsIdent (renderFormula formula) with
      | some formulaSource =>
          exact ⟨formulaSource, by
            simp [render, firstNamedMarker, firstNamedMarkerList, markerHere,
              premiseSource, theorySource, propSource, namedHypSource,
              hypothesisSource, namedAbstraction, hf]⟩
      | none =>
          exact ⟨source, by
            simp [render, firstNamedMarker, firstNamedMarkerList, markerHere,
              premiseSource, theorySource, propSource, namedHypSource,
              hypothesisSource, namedAbstraction, hf, hsource]⟩

/-- Lowered kernel material is marker-free, so the residual guard passes. -/
private theorem encodeCert_toDB_markerFree
    (startsIdent : String → Bool)
    (hNat : ∀ n, startsIdent (Nat.repr n) = false)
    (cert : Lara.ND.Cert) :
    firstNamedMarker startsIdent (encodeCert cert) = none :=
  encodeCert_markerFree startsIdent hNat cert

/-- **Translation.** Every well-formed named term lowers to exactly the
independent de Bruijn translation, encoded in the strict kernel wire image. -/
theorem lowerNamed_eq_translation (startsIdent : String → Bool)
    (ρ : String → Option Nat) (encodeProp : String → Option String)
    (nPrem : Nat) {binders : List (Option String)} {term : NCert}
    (hNat : ∀ n, startsIdent (Nat.repr n) = false)
    (wf : WellFormed startsIdent ρ encodeProp nPrem binders term) :
    lowerNamed startsIdent ρ encodeProp nPrem binders (render term) =
      (toDB ρ encodeProp nPrem binders term).map encodeCert := by
  obtain ⟨cert, hcert⟩ :=
    toDB_eq_some_of_wellFormed startsIdent ρ encodeProp nPrem wf
  obtain ⟨source, hmarker⟩ :=
    firstNamedMarker_render_some startsIdent ρ encodeProp nPrem wf
  rw [lowerNamed]
  simp only [hmarker]
  rw [lowerNamedExpr_eq_translation startsIdent ρ encodeProp nPrem hNat wf, hcert]
  simp [encodeCert_toDB_markerFree startsIdent hNat cert]

/-! ### Alpha-equivalence of named binders -/

/-- A binder-erased view of a named certificate.  Bound hypotheses are
represented by their de Bruijn index; genuinely free hypothesis names remain
names.  The Boolean on `lam` records whether the source binder was anonymous,
because anonymous and named abstractions are different presentation forms. -/
inductive AlphaView where
  | hyp : Nat ⊕ String → AlphaView
  | prem : Nat ⊕ String → AlphaView
  | thy : Nat → AlphaView
  | lam : Bool → NFormula → AlphaView → AlphaView
  | app : AlphaView → AlphaView → AlphaView
  | abort : NFormula → AlphaView → AlphaView
deriving DecidableEq, Repr

def alphaView : List (Option String) → NCert → AlphaView
  | binders, .hypX name =>
      match binderIndex name binders with
      | some index => .hyp (.inl index)
      | none => .hyp (.inr name)
  | _, .prem source => .prem source
  | _, .thy slot => .thy slot
  | binders, .lam none formula body =>
      .lam false formula (alphaView (none :: binders) body)
  | binders, .lam (some name) formula body =>
      .lam true formula (alphaView (some name :: binders) body)
  | binders, .app fn arg =>
      .app (alphaView binders fn) (alphaView binders arg)
  | binders, .abort formula body =>
      .abort formula (alphaView binders body)

/-- Named certificates are alpha-equivalent exactly when erasing their named
binders yields the same binder-indexed view.  This keeps numeric and symbolic
premises, theory slots, formulas, and anonymous binders byte-for-byte fixed. -/
def Alpha (left right : NCert) : Prop :=
  alphaView [] left = alphaView [] right

theorem alpha_refl (term : NCert) : Alpha term term := rfl

theorem alpha_symm {left right : NCert} :
    Alpha left right → Alpha right left :=
  Eq.symm

theorem alpha_trans {left middle right : NCert} :
    Alpha left middle → Alpha middle right → Alpha left right :=
  Eq.trans

private def AlphaView.toDB (ρ : String → Option Nat)
    (encodeProp : String → Option String) (nPrem depth : Nat) :
    AlphaView → Option Lara.ND.Cert
  | .hyp (.inl index) => some (.hyp index)
  | .hyp (.inr _) => none
  | .prem (.inl slot) =>
      if slot < nPrem then some (.hyp (depth + slot)) else none
  | .prem (.inr name) =>
      (ρ name).map (fun slot => .hyp (depth + slot))
  | .thy slot => some (.hyp (depth + nPrem + slot))
  | .lam _ formula body => do
      let formula' ← toFormula encodeProp formula
      let body' ← body.toDB ρ encodeProp nPrem (depth + 1)
      pure (.lam formula' body')
  | .app fn arg => do
      let fn' ← fn.toDB ρ encodeProp nPrem depth
      let arg' ← arg.toDB ρ encodeProp nPrem depth
      pure (.app fn' arg')
  | .abort formula body => do
      let formula' ← toFormula encodeProp formula
      let body' ← body.toDB ρ encodeProp nPrem depth
      pure (.abort formula' body')

private theorem toDB_eq_alphaView
    (ρ : String → Option Nat) (encodeProp : String → Option String)
    (nPrem : Nat) (binders : List (Option String)) (term : NCert) :
    toDB ρ encodeProp nPrem binders term =
      (alphaView binders term).toDB ρ encodeProp nPrem binders.length := by
  induction term generalizing binders with
  | hypX name =>
      simp [toDB, alphaView]
      split <;> simp_all [AlphaView.toDB]
  | prem source =>
      cases source <;> simp [toDB, alphaView, AlphaView.toDB, depth]
  | thy slot =>
      simp [toDB, alphaView, AlphaView.toDB, depth]
  | lam binder formula body ih =>
      cases binder with
      | none =>
          simp [toDB, alphaView, AlphaView.toDB, ih]
      | some name =>
          simp [toDB, alphaView, AlphaView.toDB, ih]
  | app fn arg ihFn ihArg =>
      simp [toDB, alphaView, AlphaView.toDB, ihFn, ihArg]
  | abort formula body ih =>
      simp [toDB, alphaView, AlphaView.toDB, ih]

/-- Alpha-equivalent named certificates lower to the same kernel de Bruijn
certificate. -/
theorem toDB_eq_of_alpha
    (ρ : String → Option Nat) (encodeProp : String → Option String)
    (nPrem : Nat) {left right : NCert} (h : Alpha left right) :
    toDB ρ encodeProp nPrem [] left = toDB ρ encodeProp nPrem [] right := by
  rw [toDB_eq_alphaView, toDB_eq_alphaView, h]

/-- Rendering and running the production named pass is invariant under alpha
renaming for well-formed closed named certificates. -/
theorem lowerNamed_eq_of_alpha
    (startsIdent : String → Bool) (ρ : String → Option Nat)
    (encodeProp : String → Option String) (nPrem : Nat)
    (hNat : ∀ n, startsIdent (Nat.repr n) = false)
    {left right : NCert}
    (leftWF : WellFormed startsIdent ρ encodeProp nPrem [] left)
    (rightWF : WellFormed startsIdent ρ encodeProp nPrem [] right)
    (h : Alpha left right) :
    lowerNamed startsIdent ρ encodeProp nPrem [] (render left) =
      lowerNamed startsIdent ρ encodeProp nPrem [] (render right) := by
  rw [lowerNamed_eq_translation startsIdent ρ encodeProp nPrem hNat leftWF,
    lowerNamed_eq_translation startsIdent ρ encodeProp nPrem hNat rightWF,
    toDB_eq_of_alpha ρ encodeProp nPrem h]

/-! ### Executable conformance vectors 1–7 and 17–28 -/

private def vectorStarts (source : String) : Bool :=
  ["a", "b", "h", "k", "é!"].contains source

private def vectorResolver : String → Option Nat
  | "a" => some 0
  | "b" => some 1
  | _ => none

/-- The vector proposition encoder: two encodable texts, everything else is a
parse failure. -/
private def vectorEncode : String → Option String
  | "p(a)" => some "<KEY-p-a>"
  | "p" => some "<KEY-p>"
  | _ => none

private def atomFormula (key : String) : SExpr := encodeFormula (.atom key)

#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 [] (kernelHypothesis 0) ==
  some (kernelHypothesis 0)

#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 [] (premNode "1") ==
  some (kernelHypothesis 1)

#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>", premNode "b"]) ==
  some (.list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>",
    kernelHypothesis 2])

#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.app.toString,
      .list [.atom Lara.ND.Tag.lam.toString, .atom "h", atomFormula "<F>",
        .list [.atom Lara.ND.Tag.hyp.toString, .atom "h"]],
      premNode "a"]) ==
  some (.list [.atom Lara.ND.Tag.app.toString,
    .list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>",
      kernelHypothesis 0], kernelHypothesis 0])

#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, .atom "h", atomFormula "<F>",
      .list [.atom Lara.ND.Tag.lam.toString, .atom "k", atomFormula "<G>",
        .list [.atom Lara.ND.Tag.hyp.toString, .atom "h"]]]) ==
  some (.list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>",
    .list [.atom Lara.ND.Tag.lam.toString, atomFormula "<G>",
      kernelHypothesis 1]])

#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>", thyNode "0"]) ==
  some (.list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>",
    kernelHypothesis 3])

#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 [] (premNode "2") == none

-- D9: once named mode is selected, a numeric kernel hypothesis is rejected.
#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, .atom "h", atomFormula "<F>",
      kernelHypothesis 0]) == none

#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, .atom "h", atomFormula "<F>",
      premNode "0"]) ==
  some (.list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>",
    kernelHypothesis 1])

#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, .atom "é!", atomFormula "<F>",
      .list [.atom Lara.ND.Tag.hyp.toString, .atom "é!"]]) ==
  some (.list [.atom Lara.ND.Tag.lam.toString, atomFormula "<F>",
    kernelHypothesis 0])

-- D10: a named binder may not collide with a resolvable premise name.
#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, .atom "a", atomFormula "<F>",
      premNode "b"]) == none

#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, .atom "h", atomFormula "<F>",
      .list [.atom Lara.ND.Tag.hyp.toString, .atom "007"]]) == none

-- A source formula annotation lowers to the encoder's atom node.
#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, propNode "p(a)", premNode "0"]) ==
  some (.list [.atom Lara.ND.Tag.lam.toString, atomNode "<KEY-p-a>",
    kernelHypothesis 1])

-- Named-binder and abort formula positions lower the same way.
#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, .atom "h", propNode "p(a)",
      .list [.atom Lara.ND.Tag.hyp.toString, .atom "h"]]) ==
  some (.list [.atom Lara.ND.Tag.lam.toString, atomNode "<KEY-p-a>",
    kernelHypothesis 0])

#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.abort.toString, propNode "p", premNode "0"]) ==
  some (.list [.atom Lara.ND.Tag.abort.toString, atomNode "<KEY-p>",
    kernelHypothesis 0])

-- Imp recursion reaches a nested source formula.
#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.lam.toString,
      .list [.atom Lara.ND.Tag.imp.toString, propNode "p",
        .atom Lara.ND.Tag.fls.toString],
      premNode "0"]) ==
  some (.list [.atom Lara.ND.Tag.lam.toString,
    .list [.atom Lara.ND.Tag.imp.toString, atomNode "<KEY-p>",
      .atom Lara.ND.Tag.fls.toString],
    kernelHypothesis 1])

-- A source formula alone selects named mode, so a numeric kernel
-- hypothesis in its body is rejected.
#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, propNode "p(a)",
      kernelHypothesis 0]) == none

-- An unencodable proposition text fails.
#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.lam.toString, propNode "p(", premNode "0"]) == none

-- A prop node in certificate position is residual.
#guard lowerNamed vectorStarts vectorResolver vectorEncode 2 []
    (.list [.atom Lara.ND.Tag.app.toString, propNode "p", premNode "0"]) == none

end Lara.NDNamed
