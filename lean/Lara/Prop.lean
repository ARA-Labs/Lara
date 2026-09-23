/-
Mechanized reference semantics for LARA proposition normalization (`nf`) and the
trusted identity relation (`≡`). This is the Lean 4 port of the frozen `Lara.Prop`
Haskell carve-out (`src/Lara/Prop.hs`) and discharges spec §9 **result 11**
(support adequacy at the identity level) and the algebraic laws behind claim C01.

It is the low-risk mechanization warm-up sanctioned by `docs/mechanization-plan.md`
§6: the `nf`/`≡` carve-out is corpus-independent and already frozen, so proving it
now validates the toolchain and the shared-core AST *before* the corpus-gated
definitions land at M1.

Design notes (faithful to the Haskell):

* The proposition type is named `Atom` (not `Prop`, Lean's sort of propositions):
  the spec's support-level propositions are ground first-order atoms `pred(g₁,…,gₙ)`.
* A constructor's argument list is a bespoke `Terms` type mutual with `Term`, rather
  than `List Term`. Lean's `deriving DecidableEq` does not support nested recursion
  through `List`, but supports mutual inductives directly — and a mechanized AST
  wants derived `DecidableEq` (it *is* the `≡`-decidability the spec claims). `Terms`
  is a plain cons-list; the Haskell `[Term]` maps to it directly.
* The structural definitions retain an explicit literal canonicalizer parameter
  `canon : String → String`, and idempotence lemmas take the corresponding
  hypothesis `∀ s, canon (canon s) = canon s`. The executable `canonNum` below is
  the byte-for-byte driver canonicalizer shared with Haskell; keeping the core
  parameterized lets the metatheory state exactly which property it consumes.
* `canonId = id` in the Haskell (Unicode NFC is the deferred extension point), so
  constructor/predicate names are not normalized here either.
-/

namespace Lara

/-! ## Executable decimal canonicalization

This is the Lean counterpart of `Lara.Prop.canonNum`. It deliberately mirrors
the Haskell function even on malformed input: strip one leading sign, normalize
the portion before the first dot, trim trailing zeroes after that dot, and make
zero unsigned. The wire decoder validates decimal syntax separately, but total
agreement here keeps the two production drivers on one identity relation. -/

private def stripLeadingZeros (chars : List Char) : List Char :=
  match chars.dropWhile (fun c => c == '0') with
  | [] => ['0']
  | rest => rest

private def stripTrailingZeros (chars : List Char) : List Char :=
  (chars.reverse.dropWhile (fun c => c == '0')).reverse

private def canonUnsigned (chars : List Char) : List Char :=
  let (intPart, dotFrac) := chars.span (fun c => c != '.')
  let normalizedInt := stripLeadingZeros intPart
  let frac := match dotFrac with
    | '.' :: rest => stripTrailingZeros rest
    | _ => []
  if frac.isEmpty then normalizedInt else normalizedInt ++ '.' :: frac

/-- Canonicalize a decimal literal exactly as Haskell `Lara.Prop.canonNum`. -/
def canonNum (s : String) : String :=
  match s.toList with
  | '+' :: rest => String.ofList (canonUnsigned rest)
  | '-' :: rest =>
      let normalized := canonUnsigned rest
      if normalized == ['0'] then "0" else String.ofList ('-' :: normalized)
  | chars => String.ofList (canonUnsigned chars)

/- Ground terms and their argument lists (mutual so `deriving` works through the
recursion). `Term` mirrors `Lara.Term` (`TNum`/`TStr`/`TCon`); `Terms` is the
argument list `[Term]`. -/
mutual
  inductive Term where
    | num : String → Term
    | str : String → Term
    | con : String → Terms → Term
  inductive Terms where
    | nil  : Terms
    | cons : Term → Terms → Terms
end
deriving instance DecidableEq for Term, Terms

/- A proposition: a predicate applied to ground argument terms. The nullary case
`atom p .nil` is the Phase-0 opaque identifier. Named `Atom` to avoid Lean's `Prop`. -/
inductive Atom where
  | atom : String → Terms → Atom
deriving DecidableEq

/- Normal form of a term: `canon` on numeric literals, structural recursion into
constructors, argument order preserved. Constructor names are not normalized
(`canonId = id`). -/
mutual
  def nfTerm (canon : String → String) : Term → Term
    | .num s => .num (canon s)
    | .str s => .str s
    | .con k ts => .con k (nfTerms canon ts)
  def nfTerms (canon : String → String) : Terms → Terms
    | .nil => .nil
    | .cons t ts => .cons (nfTerm canon t) (nfTerms canon ts)
end

/- Normal form of a proposition: `nf(pred(g₁,…,gₙ)) = pred(nf g₁, …, nf gₙ)`. -/
def nf (canon : String → String) : Atom → Atom
  | .atom p ts => .atom p (nfTerms canon ts)

/-- The trusted identity relation: `p ≡ q  iff  nf p = nf q`. -/
def equiv (canon : String → String) (a b : Atom) : Prop := nf canon a = nf canon b

/-! ## Result 11 / C01: the algebraic laws of `≡` and `nf`.

`≡` is decidable, total, reflexive, symmetric, transitive, and `nf`-equality; `nf`
is idempotent (given `canon` idempotent); and `nf` does not reorder arguments. -/

/-- `≡` is exactly `nf`-equality — by definition. -/
theorem equiv_iff_nf_eq (canon : String → String) (a b : Atom) :
    equiv canon a b ↔ nf canon a = nf canon b := Iff.rfl

/-- Reflexivity. -/
@[refl] theorem equiv_refl (canon : String → String) (a : Atom) :
    equiv canon a a := rfl

/-- Symmetry. -/
theorem equiv_symm (canon : String → String) {a b : Atom}
    (h : equiv canon a b) : equiv canon b a := h.symm

/-- Transitivity. -/
theorem equiv_trans (canon : String → String) {a b c : Atom}
    (h₁ : equiv canon a b) (h₂ : equiv canon b c) : equiv canon a c := h₁.trans h₂

/-- `≡` is decidable (it reduces to decidable equality of normal forms). -/
instance (canon : String → String) (a b : Atom) : Decidable (equiv canon a b) :=
  decEq (nf canon a) (nf canon b)

/- Idempotence of term/list normalization, given `canon` idempotent. -/
mutual
  theorem nfTerm_idem {canon : String → String}
      (hcanon : ∀ s, canon (canon s) = canon s) (t : Term) :
      nfTerm canon (nfTerm canon t) = nfTerm canon t := by
    match t with
    | .num s => simp [nfTerm, hcanon]
    | .str _ => simp [nfTerm]
    | .con k ts => simp [nfTerm, nfTerms_idem hcanon ts]
  theorem nfTerms_idem {canon : String → String}
      (hcanon : ∀ s, canon (canon s) = canon s) (ts : Terms) :
      nfTerms canon (nfTerms canon ts) = nfTerms canon ts := by
    match ts with
    | .nil => simp [nfTerms]
    | .cons t rest =>
      simp [nfTerms, nfTerm_idem hcanon t, nfTerms_idem hcanon rest]
end

/-- Idempotence of `nf`: `nf (nf p) = nf p`, given `canon` idempotent. -/
theorem nf_idem {canon : String → String}
    (hcanon : ∀ s, canon (canon s) = canon s) (a : Atom) :
    nf canon (nf canon a) = nf canon a := by
  cases a with
  | atom p ts => simp [nf, nfTerms_idem hcanon ts]

/-- Idempotence stated through `equiv`: the normal form of any atom is `≡`-identical
to the atom. -/
theorem equiv_nf {canon : String → String}
    (hcanon : ∀ s, canon (canon s) = canon s) (a : Atom) :
    equiv canon (nf canon a) a := by
  simpa [equiv] using nf_idem hcanon a

/-! ## The identity-canonicalizer collapse

`canonId = id` in the frozen v0.1 (Unicode NFC is the deferred extension
point), and the M2b complexity development works throughout under the identity
canonicalizer, where `nf` collapses to the identity and `≡` to plain equality.
Owned here, next to `nf`/`equiv`, so the gadget and witness modules consume one
copy instead of each re-proving the collapse. -/

mutual
  theorem nfTerm_id (t : Term) : nfTerm id t = t := by
    match t with
    | .num s => simp [nfTerm]
    | .str _ => simp [nfTerm]
    | .con k ts => simp [nfTerm, nfTerms_id ts]
  theorem nfTerms_id (ts : Terms) : nfTerms id ts = ts := by
    match ts with
    | .nil => simp [nfTerms]
    | .cons t rest => simp [nfTerms, nfTerm_id t, nfTerms_id rest]
end

/-- `nf id` is the identity. -/
theorem nf_id (a : Atom) : nf id a = a := by
  cases a with
  | atom p ts => simp [nf, nfTerms_id]

/-- Under the identity canonicalizer, `≡` is plain equality. -/
theorem equiv_id_eq {a b : Atom} (h : equiv id a b) : a = b := by
  have h' : nf id a = nf id b := h
  rwa [nf_id, nf_id] at h'

/-- **No argument reordering** (spec §3.2, the load-bearing non-property): a binary
predicate's two argument orders are `≡` iff the two normalized arguments coincide.
So `p(a,b) ≢ p(b,a)` whenever `a` and `b` differ after normalization — no predicate
is treated as commutative/symmetric in v0.1. -/
theorem no_reorder (canon : String → String) (p : String) (a b : Term) :
    equiv canon (.atom p (.cons a (.cons b .nil))) (.atom p (.cons b (.cons a .nil)))
      ↔ nfTerm canon a = nfTerm canon b := by
  constructor
  · intro h
    simp [equiv, nf, nfTerms] at h
    exact h.1
  · intro h
    simp [equiv, nf, nfTerms, h]

end Lara
