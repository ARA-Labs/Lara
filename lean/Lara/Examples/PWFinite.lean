/- Finite modal evaluation: empty edges, Boolean connectives, and nesting. -/
import Lara.PW.Finite

namespace Lara.Examples.PWFinite
open Lara.PW

/-- A legal frame with no accepted edges. -/
abbrev emptyFrame : Frame where
  K := OneCtx
  B := OneBridge
  src := fun _ => .it
  tgt := fun _ => .it
  World := fun _ => Bool
  Query := fun _ => Nat
  R := fun _ _ _ => False
  accept := fun _ _ _ => True
  translate := fun _ c => some c

def emptyFinite : Finite emptyFrame where
  successors := fun _ _ => []
  mem_successors := by intros; simp only [List.not_mem_nil, Frame.A, emptyFrame, false_and]

def obs : Observation emptyFrame := fun w c s =>
  w && decide (c = 0) && decide (s = .justified)

theorem empty_box :
    evalFinite emptyFinite obs (.box OneBridge.it (.neg .top)) true = true := by decide

theorem empty_dia :
    evalFinite emptyFinite obs (.dia OneBridge.it .top) true = false := by decide

theorem local_and_neg :
    evalFinite emptyFinite obs (κ := OneCtx.it)
      (.conj (.status .justified 0) (.neg (.status .gap 0))) true = true := by decide

/-- An identity relation, with a repeated candidate to exercise list semantics. -/
abbrev loopFrame : Frame := { emptyFrame with R := fun _ w v => v = w }

def loopFinite : Finite loopFrame where
  successors := fun _ w => [w, w]
  mem_successors := by intros; simp only [List.mem_cons, List.not_mem_nil, or_false, or_self, Frame.A, loopFrame, emptyFrame, and_true]

def loopObs : Observation loopFrame := fun w c s =>
  w && decide (c = 0) && decide (s = .justified)

theorem nested_modal :
    evalFinite loopFinite loopObs
      (.box OneBridge.it (.dia OneBridge.it (.status .justified 0))) true = true := by decide

theorem nested_modal_false :
    evalFinite loopFinite loopObs
      (.dia OneBridge.it (.box OneBridge.it (.status .justified 0))) false = false := by decide

end Lara.Examples.PWFinite
