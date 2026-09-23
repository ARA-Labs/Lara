/-
The fixed host for the PW file example. The file supplies declarations and
queries; the host supplies two contexts and one checked world in each. This
module does not assert leaf/certificate transport obligations for arbitrary
file-authored maps. Its accepted relation is explicitly chosen by this host.
-/
import Lara.Examples.PWSorted
import Lara.PW.Declared
import Lara.PW.Finite

namespace Lara.Examples.PWFileHost
open Lara.PW Lara.PW.Instance Lara.PW.Surface Lara.PW.Surface.Declared
open Lara.Examples.PW Lara.Examples.PWSorted

/-- Context identity is resolved independently of the authored bridge list. -/
def host : Host where
  K := Field
  ctx := ctxOf
  ctxName := fun k => match k with
    | .source => ⟨"src"⟩
    | .target => ⟨"tgt"⟩
  ctxOf := fun n =>
    if n = ⟨"src"⟩ then some .source
    else if n = ⟨"tgt"⟩ then some .target else none
  ctxOf_ctxName := by intro k; cases k <;> rfl
  ctxName_of_ctxOf := by
    intro n k h
    by_cases hs : n = ⟨"src"⟩
    · subst n; simp at h; subst k; rfl
    · by_cases ht : n = ⟨"tgt"⟩
      · subst n; simp at h; subst k; rfl
      · simp [hs, ht] at h
  canon_shared := by intro k l; cases k <;> cases l <;> rfl

/-- Each context has one host-selected checked state. -/
def worldAt : (k : host.K) → World (host.ctx k)
  | .source => wT7src
  | .target => wOverlap

def relation (r : Resolved host) (_ : World (host.ctx r.source))
    (v : World (host.ctx r.target)) : Prop := v = worldAt r.target

def acceptance (r : Resolved host) (_ : World (host.ctx r.source))
    (_ : World (host.ctx r.target)) : Prop := True

def data (E : Registry host) : Sorted.SortedBridgeData := E.data relation acceptance

def naming (E : Registry host) : Naming (data E) := E.naming relation acceptance

def finite (E : Registry host) : Finite (data E).frame where
  successors := fun b _ => [worldAt (E.get b).target]
  mem_successors := by
    intro b w v
    change v ∈ [worldAt (E.get b).target] ↔ v = worldAt (E.get b).target ∧ True
    exact ⟨fun h => ⟨List.mem_singleton.mp h, trivial⟩,
      fun h => List.mem_singleton.mpr h.1⟩

def observation (E : Registry host) : Observation (data E).frame :=
  fun w c s => decide (cmpStatus w c.val = s)

/-- The example's Boolean answer is exactly satisfaction in its declared frame. -/
theorem evaluates_iff (E : Registry host) {k : (data E).frame.K}
    (φ : Form (data E).frame k) (w : (data E).frame.World k) :
    evalFinite (finite E) (observation E) φ w = true ↔
      Sat (data E).frame (Sorted.cmpVal (data E)) φ w := by
  apply (evalFinite_iff (finite E) (observation E) φ w).trans
  apply sat_congr
  intro k v c s
  change decide (cmpStatus v c.val = s) = true ↔ cmpStatus v c.val = s
  exact ⟨of_decide_eq_true, decide_eq_true⟩

/-- A separate source-claim comparison through precisely the frame's declared
symbol map. This operation is not the interpretation of a primitive modality. -/
def compareProbe (E : Registry host) (b : E.B) (claim : Atom) : Sorted.SortedResult :=
  Sorted.crossComparePosed (host.ctx (E.get b).source).sigma
    (host.ctx (E.get b).target).sigma ((data E).sym b) claim
    [worldAt (E.get b).target] (fun _ => true) (fun v q => cmpStatus v q.val)

end Lara.Examples.PWFileHost
