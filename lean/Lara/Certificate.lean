/-
Shared symbolic certificate identifiers.

This tiny module sits below both `Lara.Strict` and `Lara.Support`: the abstract
backend must consume the exact certificate reference submitted at the source
boundary, while the support calculus must carry that same closed identifier
without introducing an import cycle.
-/

namespace Lara.Support

/-- The symbolic certificate wire representation shared with Haskell.  This is
an abstract syntax value, not a textual S-expression reader. -/
inductive SExpr where
  | atom : String → SExpr
  | list : List SExpr → SExpr

/- Lean 4.32 cannot synthesize `DecidableEq SExpr` through the nested
`List SExpr`.  Keep the public wire representation as `List SExpr` and decide
the two mutually recursive equalities directly. -/
mutual
  def SExpr.decEq : (a b : SExpr) → Decidable (a = b)
    | .atom x, .atom y =>
        match _root_.decEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)
    | .atom _, .list _ => isFalse (by intro h; cases h)
    | .list _, .atom _ => isFalse (by intro h; cases h)
    | .list xs, .list ys =>
        match SExpr.decEqList xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)

  def SExpr.decEqList : (xs ys : List SExpr) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | x :: xs, y :: ys =>
        match SExpr.decEq x y with
        | isFalse h => isFalse (by intro hxy; injection hxy with hxy _; exact h hxy)
        | isTrue h =>
            match SExpr.decEqList xs ys with
            | isTrue hs => isTrue (by cases h; cases hs; rfl)
            | isFalse hs =>
                isFalse (by intro hxy; injection hxy with _ hrest; exact hs hrest)
end

instance : DecidableEq SExpr := SExpr.decEq

/-- Opaque strict-certificate reference (`kappa`). The symbolic payload is never
inspected by the source calculus — only handed unchanged to backend replay. -/
structure CertRef where
  payload : SExpr
deriving DecidableEq

end Lara.Support
