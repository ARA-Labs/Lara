/-
Mechanized reference semantics for the LARA natural-deduction strict backend
(`Lara.Strict.ND`). This is the Lean 4 port of the frozen carve-out-2 reference
adapter (`src/Lara/Strict/ND.hs`) and discharges spec §9 **result 10**
(reference-adapter soundness + dependency exactness) and part of **result 8**
(strict-certificate soundness, via `Lara/Strict.lean`).

Following the project discipline "mechanize what we can after each stage": the ND
adapter's grammar, typing rules, and Boolean semantics are frozen (decision doc
§4.1), corpus-independent, and were already Haskell property-tested — so they can
be mechanized now, converting the QuickCheck conformance evidence into a real
machine-checked soundness proof.

What is proved here (all `#print axioms`-clean in `AxCheck.lean`):

* **`nd_sound` — Theorem 4.** A well-typed certificate is Boolean-valid: every
  valuation satisfying its context satisfies its conclusion. (Induction on typing.)
* **`nd_relevance` — the operational core of Lemma 5.** Only the *free* de Bruijn
  slots matter: a valuation satisfying just the context entries the certificate's
  free variables point at already forces the conclusion. This is what makes those
  slots *exactly* the dependencies, not merely an over-approximation.
* **`fv_in_range` — Lemma 5, in-range half.** Every free de Bruijn index of a
  well-typed certificate points at a real context slot; equivalently, an
  out-of-range index is not typable (`hyp_out_of_range_untypable`), which is the
  checker's out-of-range rejection.

Layer C — the *algorithm* vs the *relation*. Everything above reasons about
`HasType`, a declarative typing **relation**. The Haskell checker ships
`inferType`, a **decision procedure**. `infer` is that procedure ported to Lean,
and the bridge theorems prove the code — not merely an idealized relation — is
sound, complete, and reports exactly the right dependencies:

* **`infer_sound` / `infer_complete` / `infer_iff`.** `infer` accepts with type
  `φ` iff `HasType` derives `φ`. So `nd_sound`/`fv_in_range` (proved about the
  relation) transfer to the algorithm the checker actually runs.
* **`infer_deps_eq_fv`.** The dependency list `infer` returns is exactly `fv e` —
  the algorithmic form of Lemma 5's exactness.
* **`hasType_unique`.** Typing is deterministic (derived from adequacy, since
  `infer` is a function).

Design notes (faithful to the Haskell `inferType [] free`):

* De Bruijn indices: `hyp i` counts enclosing `lam` binders outward; an index at
  or beyond the binder depth points into the free context. `fv`/`shiftDown` compute
  exactly the free-slot list the Haskell returns as its dependency set.
* Context lookup is a self-contained `lookup` (not `List.get?`) so the development
  stays free of deprecated-API churn and every lemma is elementary.
* Formula atoms are `String` keys — the injective serialization of a normalized
  source proposition (`encode_ND = atom ∘ canonicalSerialize ∘ nf`), so this layer
  reasons purely about the backend logic, exactly as the Haskell adapter does.
-/

import Std.Data.String.ToNat
import Lara.Certificate

namespace Lara.ND

/-- Backend formulas: an atom (the serialized normalized source proposition),
falsum, and implication. Mirrors `Lara.Strict.ND.Formula`. -/
inductive Formula where
  | atom : String → Formula
  | fls  : Formula
  | imp  : Formula → Formula → Formula
deriving DecidableEq, Repr

/-- A natural-deduction certificate in de Bruijn form. Mirrors
`Lara.Strict.ND.Cert`. -/
inductive Cert where
  | hyp   : Nat → Cert
  | lam   : Formula → Cert → Cert
  | app   : Cert → Cert → Cert
  | abort : Formula → Cert → Cert
deriving DecidableEq, Repr

/-! ### Closed symbolic wire decoder

The concrete spellings are centralized in `Tag`; parsing never treats an
unrecognized string as a keyword.  Natural-number indices use Lean's canonical
decimal representation, so signs, separators, and leading zeroes are rejected.
-/

inductive Tag where
  | atom | fls | imp | hyp | lam | app | abort
deriving DecidableEq, Repr

def Tag.toString : Tag → String
  | .atom => "atom"
  | .fls => "false"
  | .imp => "imp"
  | .hyp => "hyp"
  | .lam => "lam"
  | .app => "app"
  | .abort => "abort"

def Tag.parse : String → Option Tag
  | "atom" => some .atom
  | "false" => some .fls
  | "imp" => some .imp
  | "hyp" => some .hyp
  | "lam" => some .lam
  | "app" => some .app
  | "abort" => some .abort
  | _ => none

@[simp] theorem Tag.parse_toString (t : Tag) : Tag.parse t.toString = some t := by
  cases t <;> rfl

def decodeNat (s : String) : Option Nat := do
  let n ← s.toNat?
  if s = Nat.repr n then some n else none

@[simp] theorem decodeNat_repr (n : Nat) : decodeNat (Nat.repr n) = some n := by
  simp [decodeNat]

theorem decodeNat_leading_zero_01 : decodeNat "01" = none := by
  have hn : "01".toNat? = some 1 := by
    rw [String.toNat?_eq_some_ofDigitChars (by
      apply String.isNat_of_isDigit
      · simp
      · intro c hc
        simp at hc
        rcases hc with rfl | rfl <;> rfl)]
    rfl
  unfold decodeNat
  rw [hn]
  change (if "01" = Nat.repr 1 then some 1 else none) = none
  rw [if_neg]
  intro h
  have hh := congrArg String.toList h
  change ['0', '1'] = ['1'] at hh
  contradiction

theorem decodeNat_some_canonical {s : String} {n : Nat}
    (h : decodeNat s = some n) : s = Nat.repr n := by
  unfold decodeNat at h
  cases hs : s.toNat? with
  | none => simp [hs] at h
  | some m =>
    rw [hs] at h
    change (if s = Nat.repr m then some m else none) = some n at h
    split at h
    · rename_i hc
      have hm : m = n := Option.some.inj h
      exact hm ▸ hc
    · simp at h

open Lara.Support

mutual
  def decodeFormula : SExpr → Option Formula
    | .atom k =>
        if Tag.parse k = some .fls then some .fls else none
    | .list [.atom k, .atom a] =>
        if Tag.parse k = some .atom then some (.atom a) else none
    | .list [.atom k, a, b] =>
        if Tag.parse k = some .imp then
          return .imp (← decodeFormula a) (← decodeFormula b)
        else none
    | _ => none

  def decodeCert : SExpr → Option Cert
    | .list [.atom k, .atom n] =>
        if Tag.parse k = some .hyp then return .hyp (← decodeNat n) else none
    | .list [.atom k, φ, e] =>
        match Tag.parse k with
        | some .lam => return .lam (← decodeFormula φ) (← decodeCert e)
        | some .app => return .app (← decodeCert φ) (← decodeCert e)
        | some .abort => return .abort (← decodeFormula φ) (← decodeCert e)
        | _ => none
    | _ => none
end

theorem decodeFormula_list_bad_arity (t : Tag) (xs : List SExpr)
    (h : (t = .atom → xs.length ≠ 1) ∧
      (t = .imp → xs.length ≠ 2)) :
    decodeFormula (.list (.atom t.toString :: xs)) = none := by
  cases t <;>
    cases xs with
    | nil => simp_all [decodeFormula]
    | cons x xs =>
      cases xs with
      | nil => cases x <;> simp_all [decodeFormula, Tag.toString, Tag.parse]
      | cons y xs =>
        cases xs with
        | nil =>
          cases x <;> cases y <;>
            simp_all [decodeFormula, Tag.toString, Tag.parse]
        | cons z xs => simp_all [decodeFormula, Tag.toString]

theorem decodeCert_list_bad_arity (t : Tag) (xs : List SExpr)
    (h : (t = .hyp → xs.length ≠ 1) ∧
      (t = .lam ∨ t = .app ∨ t = .abort → xs.length ≠ 2)) :
    decodeCert (.list (.atom t.toString :: xs)) = none := by
  cases t <;>
    cases xs with
    | nil => simp_all [decodeCert]
    | cons x xs =>
      cases xs with
      | nil =>
        cases x <;> simp_all [decodeCert, Tag.toString, Tag.parse]
      | cons y xs =>
        cases xs with
        | nil =>
          cases x <;> cases y <;>
            simp_all [decodeCert, Tag.toString, Tag.parse]
        | cons z xs => simp_all [decodeCert, Tag.toString]

/-- A bare atom outside the closed keyword vocabulary cannot be decoded as a
formula (in particular, it cannot alias the distinguished `false` atom). -/
theorem decodeFormula_unknown_atom {k : String} (h : Tag.parse k = none) :
    decodeFormula (.atom k) = none := by
  simp [decodeFormula, h]

/-- An unknown head tag is rejected at every formula-list arity. -/
theorem decodeFormula_unknown_list {k : String} (xs : List SExpr)
    (h : Tag.parse k = none) :
    decodeFormula (.list (.atom k :: xs)) = none := by
  cases xs with
  | nil => simp [decodeFormula]
  | cons x xs =>
    cases xs with
    | nil => cases x <;> simp [decodeFormula, h]
    | cons y xs =>
      cases xs with
      | nil => cases x <;> cases y <;> simp [decodeFormula, h]
      | cons z xs => simp [decodeFormula]

/-- An unknown head tag is rejected at every certificate-list arity. -/
theorem decodeCert_unknown_list {k : String} (xs : List SExpr)
    (h : Tag.parse k = none) :
    decodeCert (.list (.atom k :: xs)) = none := by
  cases xs with
  | nil => simp [decodeCert]
  | cons x xs =>
    cases xs with
    | nil => cases x <;> simp [decodeCert, h]
    | cons y xs =>
      cases xs with
      | nil => cases x <;> cases y <;> simp [decodeCert, h]
      | cons z xs => simp [decodeCert]

/-- Positional context lookup (de Bruijn): index `0` is the innermost binding. -/
def lookup : List Formula → Nat → Option Formula
  | [],     _     => none
  | φ :: _,  0     => some φ
  | _ :: Γ, n + 1 => lookup Γ n

/-- The typing judgment `Γ ⊢ e : φ`, the exact rules of decision doc §4.1. The
context `Γ` holds the enclosing binders (innermost first) followed by the free
context (premise/theory encodings). -/
inductive HasType : List Formula → Cert → Formula → Prop where
  | hyp {Γ i φ} :
      lookup Γ i = some φ → HasType Γ (.hyp i) φ
  | lam {Γ φ ψ e} :
      HasType (φ :: Γ) e ψ → HasType Γ (.lam φ e) (.imp φ ψ)
  | app {Γ e₁ e₂ φ ψ} :
      HasType Γ e₁ (.imp φ ψ) → HasType Γ e₂ φ → HasType Γ (.app e₁ e₂) ψ
  | abort {Γ φ e} :
      HasType Γ e .fls → HasType Γ (.abort φ e) φ

/-- Boolean semantics: `satisfies v φ` holds when valuation `v` makes `φ` true.
`T ; Δ ⊨_ND φ` of the decision doc is `∀ v, (∀ ψ ∈ Δ ∪ T, satisfies v ψ) →
satisfies v φ`. -/
def satisfies (v : String → Bool) : Formula → Prop
  | .atom a  => v a = true
  | .fls     => False
  | .imp φ ψ => satisfies v φ → satisfies v ψ

/-! ### Free de Bruijn variables (the dependency set) -/

/-- Decrement every positive index and drop the zeros — the effect of stepping out
through one `lam` binder. -/
def shiftDown : List Nat → List Nat
  | []           => []
  | 0 :: rest     => shiftDown rest
  | (n + 1) :: rest => n :: shiftDown rest

/-- Free de Bruijn indices of a certificate, as absolute free-context slots. This
is exactly the dependency list the Haskell `inferType [] free` returns. -/
def fv : Cert → List Nat
  | .hyp i    => [i]
  | .lam _ e  => shiftDown (fv e)
  | .app f x  => fv f ++ fv x
  | .abort _ e => fv e

/-- Membership characterization of `shiftDown`: `n` is free after stepping out of a
binder iff `n+1` was free inside it. -/
theorem mem_shiftDown {n : Nat} {l : List Nat} :
    n ∈ shiftDown l ↔ (n + 1) ∈ l := by
  induction l with
  | nil => simp [shiftDown]
  | cons m rest ih =>
    cases m with
    | zero =>
      simp only [shiftDown]
      constructor
      · intro h; exact List.mem_cons.mpr (Or.inr (ih.mp h))
      · intro h
        rcases List.mem_cons.mp h with h0 | hrest
        · exact absurd h0 (by simp)
        · exact ih.mpr hrest
    | succ k =>
      simp only [shiftDown]
      constructor
      · intro h
        rcases List.mem_cons.mp h with h0 | hrest
        · exact List.mem_cons.mpr (Or.inl (by simp [h0]))
        · exact List.mem_cons.mpr (Or.inr (ih.mp hrest))
      · intro h
        rcases List.mem_cons.mp h with h0 | hrest
        · have : n = k := by simpa using h0
          exact List.mem_cons.mpr (Or.inl (by simp [this]))
        · exact List.mem_cons.mpr (Or.inr (ih.mpr hrest))

/-! ### Auxiliary lemmas on `lookup` -/

/-- A successful lookup yields a member of the context. -/
theorem lookup_mem {Γ : List Formula} {i : Nat} {φ : Formula}
    (h : lookup Γ i = some φ) : φ ∈ Γ := by
  induction Γ generalizing i with
  | nil => cases i <;> simp [lookup] at h
  | cons ψ rest ih =>
    cases i with
    | zero =>
      have : φ = ψ := by simpa [lookup] using h.symm
      exact this ▸ List.mem_cons_self ..
    | succ k =>
      exact List.mem_cons.mpr (Or.inr (ih (by simpa [lookup] using h)))

/-- A successful lookup means the index is in range. -/
theorem lookup_lt {Γ : List Formula} {i : Nat} {φ : Formula}
    (h : lookup Γ i = some φ) : i < Γ.length := by
  induction Γ generalizing i with
  | nil => cases i <;> simp [lookup] at h
  | cons ψ rest ih =>
    cases i with
    | zero => simp
    | succ k =>
      have := ih (i := k) (by simpa [lookup] using h)
      simpa using Nat.succ_lt_succ this

/-- `lookup` is positional indexing: the self-contained lookup agrees with the
standard `Γ[i]?`, so dependency slots can be read against either. -/
theorem lookup_eq_getElem? : ∀ (Γ : List Formula) (i : Nat), lookup Γ i = Γ[i]? := by
  intro Γ
  induction Γ with
  | nil => intro i; cases i <;> rfl
  | cons φ rest ih =>
    intro i
    cases i with
    | zero => rfl
    | succ k => simpa [lookup] using ih k

/-! ### The theorems -/

/-- **Lemma 5 (operational core).** Only the free-variable slots of a certificate
are consulted: any valuation `v` that satisfies exactly the context entries the
*free* de Bruijn indices point at already satisfies the conclusion. Hence those
slots are precisely the dependencies (not an over-approximation). -/
theorem nd_relevance {Γ : List Formula} {e : Cert} {φ : Formula}
    (h : HasType Γ e φ) (v : String → Bool)
    (hfree : ∀ i ψ, i ∈ fv e → lookup Γ i = some ψ → satisfies v ψ) :
    satisfies v φ := by
  induction h with
  | @hyp Γ i φ hlook =>
    exact hfree i φ (by simp [fv]) hlook
  | @lam Γ φ ψ e _ ih =>
    -- goal: satisfies v (imp φ ψ) = (satisfies v φ → satisfies v ψ)
    intro hφ
    apply ih
    intro i χ hi hlook
    cases i with
    | zero =>
      -- lookup (φ :: Γ) 0 = some φ, so χ = φ, and hφ gives it
      have : χ = φ := by simpa [lookup] using hlook.symm
      exact this ▸ hφ
    | succ k =>
      -- k+1 ∈ fv e ⇒ k ∈ shiftDown (fv e) = fv (lam φ e); lookup steps to Γ
      have hk : k ∈ fv (.lam φ e) := by
        simp only [fv]; exact mem_shiftDown.mpr hi
      exact hfree k χ hk (by simpa [lookup] using hlook)
  | @app Γ e₁ e₂ φ ψ _ _ ih₁ ih₂ =>
    have h₁ : satisfies v (.imp φ ψ) :=
      ih₁ (fun i χ hi hlk => hfree i χ (by simp [fv]; exact Or.inl hi) hlk)
    have h₂ : satisfies v φ :=
      ih₂ (fun i χ hi hlk => hfree i χ (by simp [fv]; exact Or.inr hi) hlk)
    exact h₁ h₂
  | @abort Γ φ e _ ih =>
    have hfls : satisfies v .fls :=
      ih (fun i χ hi hlk => hfree i χ (by simpa [fv] using hi) hlk)
    exact (hfls).elim

/-- **Theorem 4 (soundness of the ND adapter).** If `Γ ⊢ e : φ`, every valuation
satisfying all of `Γ` satisfies `φ`. Follows from `nd_relevance` by ignoring the
free-variable restriction. -/
theorem nd_sound {Γ : List Formula} {e : Cert} {φ : Formula}
    (h : HasType Γ e φ) (v : String → Bool)
    (hΓ : ∀ ψ, ψ ∈ Γ → satisfies v ψ) :
    satisfies v φ :=
  nd_relevance h v (fun _ ψ _ hlook => hΓ ψ (lookup_mem hlook))

/-- **Lemma 5 (in-range half).** Every free de Bruijn index of a well-typed
certificate points at a real context slot. -/
theorem fv_in_range {Γ : List Formula} {e : Cert} {φ : Formula}
    (h : HasType Γ e φ) : ∀ i, i ∈ fv e → i < Γ.length := by
  induction h with
  | @hyp Γ i φ hlook =>
    intro j hj
    have : j = i := by simpa [fv] using hj
    exact this ▸ lookup_lt hlook
  | @lam Γ φ ψ e _ ih =>
    intro j hj
    -- j ∈ shiftDown (fv e) ⇒ j+1 ∈ fv e ⇒ j+1 < (φ :: Γ).length = Γ.length + 1
    have hj' : (j + 1) ∈ fv e := by
      have : j ∈ shiftDown (fv e) := by simpa [fv] using hj
      exact mem_shiftDown.mp this
    have := ih (j + 1) hj'
    simpa using Nat.lt_of_succ_lt_succ (by simpa using this)
  | @app Γ e₁ e₂ φ ψ _ _ ih₁ ih₂ =>
    intro j hj
    rcases List.mem_append.mp (by simpa [fv] using hj) with h1 | h2
    · exact ih₁ j h1
    · exact ih₂ j h2
  | @abort Γ φ e _ ih =>
    intro j hj
    exact ih j (by simpa [fv] using hj)

/-- The checker's out-of-range rejection, as a corollary: a `hyp i` whose index is
at or beyond the context length is not typable. -/
theorem hyp_out_of_range_untypable {Γ : List Formula} {i : Nat} {φ : Formula}
    (hi : Γ.length ≤ i) : ¬ HasType Γ (.hyp i) φ := by
  intro h
  have := fv_in_range h i (by simp [fv])
  exact absurd this (Nat.not_lt.mpr hi)

/-! ## Closing Layer C: the *algorithm* `infer` decides the *relation* `HasType`

Everything above reasons about `HasType`, a declarative typing **relation**. The
Haskell checker ships `inferType`, a **decision procedure** returning
`Either String (Formula, deps)`. A theorem about the relation does not, on its
own, say the algorithm is correct. This section closes that gap: `infer` is a
faithful Lean port of the Haskell `inferType`, and `infer_iff` proves it accepts
a step with type `φ` **iff** the relation `HasType` derives `φ`. So the code the
checker actually runs — not merely an idealized relation — is sound and complete.

`infer free ls e` threads the two lists the Haskell does: `ls` are the binders
introduced by enclosing `lam`s (innermost first) and `free` is the fixed free
context (premise/theory encodings). A de Bruijn index below `ls.length` is a
local binding (no dependency); at or above it points into `free` at slot
`i - ls.length`. The whole context seen by the relation is `ls ++ free`. -/

/-- Faithful Lean port of the Haskell `inferType locals free`: total, returns the
inferred formula and the free-context dependency slots, or `none` on any
ill-typed / out-of-range certificate. -/
def infer (free : List Formula) : List Formula → Cert → Option (Formula × List Nat)
  | ls, .hyp i =>
      match lookup ls i with
      | some φ => some (φ, [])                       -- local binding: not a dependency
      | none =>
          match lookup free (i - ls.length) with
          | some φ => some (φ, [i - ls.length])      -- into the free context
          | none => none                             -- out of range: reject
  | ls, .lam φ e =>
      match infer free (φ :: ls) e with
      | some (ψ, ds) => some (.imp φ ψ, ds)
      | none => none
  | ls, .app f x =>
      match infer free ls f with
      | some (.imp a b, fds) =>
          match infer free ls x with
          | some (xt, xds) => if a = xt then some (b, fds ++ xds) else none
          | none => none
      | _ => none
  | ls, .abort φ e =>
      match infer free ls e with
      | some (.fls, ds) => some (φ, ds)
      | _ => none

/-! ### Context-splitting lemmas for `lookup` over `ls ++ free` -/

/-- Below the local depth, lookup stays in the local segment. -/
theorem lookup_append_lt : ∀ {ls : List Formula} {i} (free : List Formula),
    i < ls.length → lookup (ls ++ free) i = lookup ls i := by
  intro ls
  induction ls with
  | nil => intro i free h; simp at h
  | cons ψ rest ih =>
    intro i free h
    cases i with
    | zero => rfl
    | succ k =>
      have hk : k < rest.length := by
        rw [List.length_cons] at h; exact Nat.lt_of_succ_lt_succ h
      simp only [List.cons_append, lookup]
      exact ih free hk

/-- At or above the local depth, lookup falls through into the free segment. -/
theorem lookup_append_ge : ∀ {ls : List Formula} {i} (free : List Formula),
    ls.length ≤ i → lookup (ls ++ free) i = lookup free (i - ls.length) := by
  intro ls
  induction ls with
  | nil => intro i free _; rfl
  | cons ψ rest ih =>
    intro i free h
    cases i with
    | zero => rw [List.length_cons] at h; exact absurd h (Nat.not_succ_le_zero _)
    | succ k =>
      have hk : rest.length ≤ k := by
        rw [List.length_cons] at h; exact Nat.le_of_succ_le_succ h
      simp only [List.cons_append, lookup, List.length_cons, Nat.succ_sub_succ]
      exact ih free hk

/-- A successful in-range lookup exists whenever the index is in range. -/
theorem lookup_of_lt : ∀ {Γ : List Formula} {i : Nat}, i < Γ.length →
    ∃ φ, lookup Γ i = some φ := by
  intro Γ
  induction Γ with
  | nil => intro i h; simp at h
  | cons ψ rest ih =>
    intro i h
    cases i with
    | zero => exact ⟨ψ, rfl⟩
    | succ k =>
      have hk : k < rest.length := by
        rw [List.length_cons] at h; exact Nat.lt_of_succ_lt_succ h
      obtain ⟨φ, hφ⟩ := ih hk
      exact ⟨φ, hφ⟩

/-- Out of range, lookup fails. -/
theorem lookup_none_of_ge : ∀ {Γ : List Formula} {i : Nat}, Γ.length ≤ i →
    lookup Γ i = none := by
  intro Γ
  induction Γ with
  | nil => intro i _; rfl
  | cons ψ rest ih =>
    intro i h
    cases i with
    | zero => rw [List.length_cons] at h; exact absurd h (Nat.not_succ_le_zero _)
    | succ k =>
      have hk : rest.length ≤ k := by
        rw [List.length_cons] at h; exact Nat.le_of_succ_le_succ h
      show lookup rest k = none
      exact ih hk

/-! ### Adequacy: `infer` is sound and complete for `HasType` -/

/-- **Soundness of the algorithm.** If `infer` accepts with type `φ`, the relation
derives `φ` over the full context `ls ++ free`. -/
theorem infer_sound {free : List Formula} :
    ∀ (ls : List Formula) (e : Cert) (φ : Formula) (ds : List Nat),
      infer free ls e = some (φ, ds) → HasType (ls ++ free) e φ := by
  intro ls e
  induction e generalizing ls with
  | hyp i =>
    intro φ ds h
    simp only [infer] at h
    cases hloc : lookup ls i with
    | some φ' =>
      simp only [hloc] at h
      obtain ⟨hφ, _⟩ := Prod.mk.inj (Option.some.inj h)
      subst hφ
      exact HasType.hyp (by rw [lookup_append_lt free (lookup_lt hloc)]; exact hloc)
    | none =>
      simp only [hloc] at h
      cases hfree : lookup free (i - ls.length) with
      | some φ' =>
        simp only [hfree] at h
        obtain ⟨hφ, _⟩ := Prod.mk.inj (Option.some.inj h)
        subst hφ
        have hge : ls.length ≤ i := by
          rcases Nat.lt_or_ge i ls.length with hlt | hge
          · obtain ⟨ψ, hψ⟩ := lookup_of_lt hlt
            rw [hψ] at hloc; simp at hloc
          · exact hge
        exact HasType.hyp (by rw [lookup_append_ge free hge]; exact hfree)
      | none => simp [hfree] at h
  | lam ψ0 e ih =>
    intro φ ds h
    simp only [infer] at h
    cases hbody : infer free (ψ0 :: ls) e with
    | some p =>
      obtain ⟨ψ, ds'⟩ := p
      simp only [hbody] at h
      obtain ⟨hφ, _⟩ := Prod.mk.inj (Option.some.inj h)
      subst hφ
      exact HasType.lam (by simpa using ih (ψ0 :: ls) ψ ds' hbody)
    | none => simp [hbody] at h
  | app f x ihf ihx =>
    intro φ ds h
    simp only [infer] at h
    cases hf : infer free ls f with
    | some p =>
      obtain ⟨ft, fds⟩ := p
      simp only [hf] at h
      cases ft with
      | imp a b =>
        cases hx : infer free ls x with
        | some q =>
          obtain ⟨xt, xds⟩ := q
          simp only [hx] at h
          by_cases hcond : a = xt
          · rw [if_pos hcond] at h
            obtain ⟨hφ, _⟩ := Prod.mk.inj (Option.some.inj h)
            subst hφ
            have hjf := ihf ls (.imp a b) fds hf
            have hjx := ihx ls xt xds hx
            rw [← hcond] at hjx
            exact HasType.app hjf hjx
          · rw [if_neg hcond] at h; simp at h
        | none => simp [hx] at h
      | atom _ => simp at h
      | fls => simp at h
    | none => simp [hf] at h
  | abort ψ0 e ih =>
    intro φ ds h
    simp only [infer] at h
    cases hbody : infer free ls e with
    | some p =>
      obtain ⟨bt, ds'⟩ := p
      simp only [hbody] at h
      cases bt with
      | fls =>
        obtain ⟨hφ, _⟩ := Prod.mk.inj (Option.some.inj h)
        subst hφ
        exact HasType.abort (ih ls .fls ds' hbody)
      | atom _ => simp at h
      | imp _ _ => simp at h
    | none => simp [hbody] at h

/-- **Completeness of the algorithm.** If the relation derives `φ` over
`ls ++ free`, `infer` accepts and returns `φ` (with some dependency list). -/
theorem infer_complete {free : List Formula} :
    ∀ (ls : List Formula) (e : Cert) (φ : Formula),
      HasType (ls ++ free) e φ → ∃ ds, infer free ls e = some (φ, ds) := by
  intro ls e
  induction e generalizing ls with
  | hyp i =>
    intro φ h
    cases h with
    | hyp hl =>
      by_cases hlt : i < ls.length
      · refine ⟨[], ?_⟩
        simp only [infer]
        rw [lookup_append_lt free hlt] at hl
        rw [hl]
      · have hge : ls.length ≤ i := Nat.le_of_not_lt hlt
        refine ⟨[i - ls.length], ?_⟩
        simp only [infer]
        rw [lookup_none_of_ge hge]
        rw [lookup_append_ge free hge] at hl
        rw [hl]
  | lam ψ0 body ih =>
    intro φ h
    cases h with
    | lam hbody =>
      obtain ⟨ds, hds⟩ := ih (ψ0 :: ls) _ (by simpa using hbody)
      exact ⟨ds, by simp only [infer, hds]⟩
  | app f x ihf ihx =>
    intro φ h
    cases h with
    | app hf hx =>
      obtain ⟨fds, hfds⟩ := ihf ls _ hf
      obtain ⟨xds, hxds⟩ := ihx ls _ hx
      refine ⟨fds ++ xds, ?_⟩
      simp [infer, hfds, hxds]
  | abort ψ0 body ih =>
    intro φ h
    cases h with
    | abort hbody =>
      obtain ⟨ds, hds⟩ := ih ls _ hbody
      exact ⟨ds, by simp only [infer, hds]⟩

/-- Drop the de Bruijn indices below `n` and shift the rest down by `n` — the
projection from a full-context dependency list to free-context slots when `n`
binders are in scope. `depProj 0` is the identity. -/
def depProj (n : Nat) (l : List Nat) : List Nat :=
  l.filterMap (fun i => if i < n then none else some (i - n))

@[simp] theorem depProj_zero (l : List Nat) : depProj 0 l = l := by
  simp [depProj]

@[simp] theorem depProj_append (n : Nat) (l₁ l₂ : List Nat) :
    depProj n (l₁ ++ l₂) = depProj n l₁ ++ depProj n l₂ := by
  simp [depProj, List.filterMap_append]

/-- Stepping out through one binder commutes: projecting with `n+1` binders over a
list equals projecting with `n` binders over its `shiftDown`. This is the single
bookkeeping fact the `lam` case of `infer_deps_eq_fv` needs. -/
theorem depProj_succ_shiftDown (n : Nat) (l : List Nat) :
    depProj (n + 1) l = depProj n (shiftDown l) := by
  induction l with
  | nil => simp [depProj, shiftDown]
  | cons j rest ih =>
    cases j with
    | zero =>
      simp only [depProj, shiftDown, List.filterMap_cons, Nat.zero_lt_succ, if_true]
      simpa [depProj] using ih
    | succ k =>
      simp only [depProj, shiftDown, List.filterMap_cons]
      by_cases hk : k < n
      · simp only [Nat.succ_lt_succ hk, hk, if_true]
        simpa [depProj] using ih
      · simp only [Nat.succ_lt_succ_iff, hk, if_false, Nat.succ_sub_succ]
        simpa [depProj] using ih

/-- **The algorithm's dependency output is exactly `fv`.** Whenever `infer`
accepts at top level (`ls = []`), the dependency list it returns is precisely the
certificate's free de Bruijn variables. Combined with `infer_sound`/`fv_in_range`
this is the algorithmic form of Lemma 5: the running checker's reported
dependencies coincide with the mechanized `fv`. -/
theorem infer_deps_eq_fv {free : List Formula} :
    ∀ (e : Cert) (φ : Formula) (ds : List Nat),
      infer free [] e = some (φ, ds) → ds = fv e := by
  -- generalize over an arbitrary local context, proving ds = depProj ls.length (fv e)
  suffices h : ∀ (ls : List Formula) (e : Cert) (φ : Formula) (ds : List Nat),
      infer free ls e = some (φ, ds) → ds = depProj ls.length (fv e) by
    intro e φ ds hinf
    have := h [] e φ ds hinf
    simpa using this
  intro ls e
  induction e generalizing ls with
  | hyp i =>
    intro φ ds hinf
    simp only [infer] at hinf
    cases hloc : lookup ls i with
    | some φ' =>
      simp only [hloc] at hinf
      obtain ⟨_, hds⟩ := Prod.mk.inj (Option.some.inj hinf)
      have hlt : i < ls.length := lookup_lt hloc
      simp [fv, depProj, ← hds, hlt]
    | none =>
      simp only [hloc] at hinf
      cases hfree : lookup free (i - ls.length) with
      | some φ' =>
        simp only [hfree] at hinf
        obtain ⟨_, hds⟩ := Prod.mk.inj (Option.some.inj hinf)
        have hge : ls.length ≤ i := by
          rcases Nat.lt_or_ge i ls.length with hlt | hge
          · obtain ⟨ψ, hψ⟩ := lookup_of_lt hlt; rw [hψ] at hloc; simp at hloc
          · exact hge
        simp [fv, depProj, ← hds, Nat.not_lt.mpr hge]
      | none => simp [hfree] at hinf
  | lam ψ0 e ih =>
    intro φ ds hinf
    simp only [infer] at hinf
    cases hbody : infer free (ψ0 :: ls) e with
    | some p =>
      obtain ⟨ψ, ds'⟩ := p
      simp only [hbody] at hinf
      obtain ⟨_, hds⟩ := Prod.mk.inj (Option.some.inj hinf)
      subst hds
      -- ds' = depProj (ls.length+1) (fv e); goal deps = depProj ls.length (fv (lam)) = depProj ls.length (shiftDown (fv e))
      rw [ih (ψ0 :: ls) ψ ds' hbody, fv, List.length_cons, depProj_succ_shiftDown]
    | none => simp [hbody] at hinf
  | app f x ihf ihx =>
    intro φ ds hinf
    simp only [infer] at hinf
    cases hf : infer free ls f with
    | some p =>
      obtain ⟨ft, fds⟩ := p
      simp only [hf] at hinf
      cases ft with
      | imp a b =>
        cases hx : infer free ls x with
        | some q =>
          obtain ⟨xt, xds⟩ := q
          simp only [hx] at hinf
          by_cases hcond : a = xt
          · rw [if_pos hcond] at hinf
            obtain ⟨_, hds⟩ := Prod.mk.inj (Option.some.inj hinf)
            subst hds
            rw [ihf ls (.imp a b) fds hf, ihx ls xt xds hx, fv, depProj_append]
          · rw [if_neg hcond] at hinf; simp at hinf
        | none => simp [hx] at hinf
      | atom _ => simp at hinf
      | fls => simp at hinf
    | none => simp [hf] at hinf
  | abort ψ0 e ih =>
    intro φ ds hinf
    simp only [infer] at hinf
    cases hbody : infer free ls e with
    | some p =>
      obtain ⟨bt, ds'⟩ := p
      simp only [hbody] at hinf
      cases bt with
      | fls =>
        obtain ⟨_, hds⟩ := Prod.mk.inj (Option.some.inj hinf)
        subst hds
        rw [ih ls .fls ds' hbody, fv]
      | atom _ => simp at hinf
      | imp _ _ => simp at hinf
    | none => simp [hbody] at hinf

/-- **Congruence on unreported slots.** `infer` consults the free context only
at the projected free-variable slots: two free contexts that agree there (both
values and both failures) produce identical results — the extensional form of
"every consulted premise or theory entry is reported" (decision doc §2,
obligation 4 coverage clause). -/
theorem infer_agree {free free' : List Formula} :
    ∀ (ls : List Formula) (e : Cert),
      (∀ j, j ∈ depProj ls.length (fv e) → lookup free j = lookup free' j) →
      infer free ls e = infer free' ls e := by
  intro ls e
  induction e generalizing ls with
  | hyp i =>
    intro hag
    simp only [infer]
    cases hloc : lookup ls i with
    | some φ => rfl
    | none =>
      have hge : ls.length ≤ i := by
        rcases Nat.lt_or_ge i ls.length with hlt | hge
        · obtain ⟨ψ, hψ⟩ := lookup_of_lt hlt
          rw [hψ] at hloc
          simp at hloc
        · exact hge
      have hmem : i - ls.length ∈ depProj ls.length (fv (.hyp i)) := by
        simp [fv, depProj, Nat.not_lt.mpr hge]
      rw [hag (i - ls.length) hmem]
  | lam ψ0 e ih =>
    intro hag
    simp only [infer]
    rw [ih (ψ0 :: ls) (by
      intro j hj
      refine hag j ?_
      rw [fv, ← depProj_succ_shiftDown]
      simpa using hj)]
  | app f x ihf ihx =>
    intro hag
    simp only [infer]
    rw [ihf ls (fun j hj => hag j (by
          simp only [fv, depProj_append, List.mem_append]
          exact Or.inl hj)),
        ihx ls (fun j hj => hag j (by
          simp only [fv, depProj_append, List.mem_append]
          exact Or.inr hj))]
  | abort ψ0 e ih =>
    intro hag
    simp only [infer]
    rw [ih ls (fun j hj => hag j (by simpa [fv] using hj))]

/-- **Layer-C bridge (type adequacy).** At the top level (`ls = []`, the Haskell
`inferType []`), the algorithm accepts with type `φ` exactly when the relation
derives `φ`. This is the statement that ties the running checker to the
mechanized metatheory: `nd_sound`/`fv_in_range` are proved about `HasType`, and
this shows `infer` — the algorithm — coincides with it. -/
theorem infer_iff {free : List Formula} {e : Cert} {φ : Formula} :
    (∃ ds, infer free [] e = some (φ, ds)) ↔ HasType free e φ := by
  constructor
  · rintro ⟨ds, h⟩
    have := infer_sound [] e φ ds h
    simpa using this
  · intro h
    obtain ⟨ds, hds⟩ := infer_complete [] e φ (by simpa using h)
    exact ⟨ds, hds⟩

/-- Typing is deterministic: the relation assigns at most one formula, so the
`φ` in `infer_iff` is unambiguous. Derived from adequacy — `infer` is a function,
so two derivations for the same certificate route through the same `infer`
result. -/
theorem hasType_unique {Γ : List Formula} {e : Cert} {φ ψ : Formula}
    (h1 : HasType Γ e φ) (h2 : HasType Γ e ψ) : φ = ψ := by
  obtain ⟨_, hφ⟩ := infer_complete (free := Γ) [] e φ (by simpa using h1)
  obtain ⟨_, hψ⟩ := infer_complete (free := Γ) [] e ψ (by simpa using h2)
  rw [hφ] at hψ
  exact (Prod.mk.injEq .. ▸ Option.some.inj hψ).1

end Lara.ND
