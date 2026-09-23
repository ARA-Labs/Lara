/-
PW0 T3 — uniform-language reduction.

With one shared language (a single context), total identity claim translation,
and fixed accepted relations, the typed outer clauses reduce to ordinary
labelled multimodal Kripke semantics over Lara status valuations. Mechanized
as a two-sided construction: an ordinary multimodal Kripke model embeds into a
one-context frame (`Kripke.frame`, with `accept := True` — the "fixed accepted
relations" hypothesis — and `translate := some` — the "total identity
translation" hypothesis, made structural), formulas lift, and satisfaction
agrees clause by clause (`sat_lift`).

Note the primitive modalities never consult `translate`, so the identity
translation matters to the *derived* formulas of the design (`[b]Justified(τ c)`
collapses to `[b]Justified(c)`), which the structural `translate := some`
witnesses definitionally.

`KForm`/`KSat` duplicate the shape of `Form`/`Sat` on purpose. Defining the
"ordinary" semantics in terms of the typed one would make `sat_lift` vacuous;
the reduction is only evidence that PW0 invented no new logic if the thing it
reduces to was defined independently. Same argument as gate 2 for T1.
-/

import Lara.PW.Outer

namespace Lara.PW

open Lara.Grounded (Status)

/-- An ordinary labelled multimodal Kripke model over status valuations:
one type of worlds, one query language, a relation per label. -/
structure Kripke where
  World : Type
  B : Type
  Rel : B → World → World → Prop
  Query : Type

/-- Ordinary (unsorted) formulas over a Kripke model. -/
inductive KForm (U : Kripke) : Type where
  | status (s : Status) (c : U.Query) : KForm U
  | top : KForm U
  | neg (φ : KForm U) : KForm U
  | conj (φ ψ : KForm U) : KForm U
  | box (b : U.B) (φ : KForm U) : KForm U
  | dia (b : U.B) (φ : KForm U) : KForm U

/-- Ordinary Kripke valuation. -/
def KVal (U : Kripke) : Type := U.World → U.Query → Status → Prop

/-- Ordinary Kripke satisfaction. Formula-first for the same reason as
`Sat` (see its doc comment), so the two sides of `sat_lift` read alike. -/
def KSat (U : Kripke) (V : KVal U) : KForm U → U.World → Prop
  | .status s c, w => V w c s
  | .top, _ => True
  | .neg φ, w => ¬ KSat U V φ w
  | .conj φ ψ, w => KSat U V φ w ∧ KSat U V ψ w
  | .box b φ, w => ∀ v, U.Rel b w v → KSat U V φ v
  | .dia b φ, w => ∃ v, U.Rel b w v ∧ KSat U V φ v

/-- The one-context frame a Kripke model induces: every bridge is an
endobridge on the single context, every candidate edge is accepted, and the
claim translation is total identity. `OneCtx` rather than `Unit` — see
`OneCtx`'s doc comment; this module does not import `Lara.Unit` today, but a
future import would silently capture a bare `Unit` here. -/
def Kripke.frame (U : Kripke) : Frame where
  K := OneCtx
  B := U.B
  src := fun _ => .it
  tgt := fun _ => .it
  World := fun _ => U.World
  Query := fun _ => U.Query
  R := U.Rel
  accept := fun _ _ _ => True
  translate := fun _ => some

/-- Formula lifting into the one-context frame. -/
def KForm.lift {U : Kripke} : KForm U → Form U.frame .it
  | .status s c => .status s c
  | .top => .top
  | .neg φ => .neg φ.lift
  | .conj φ ψ => .conj φ.lift ψ.lift
  | .box b φ => .box b φ.lift
  | .dia b φ => .dia b φ.lift

/-- Valuation lifting (the two types agree up to the trivial context index). -/
def KVal.lift {U : Kripke} (V : KVal U) : Valuation U.frame :=
  fun {_} w c s => V w c s

/-- **T3.** Under the induced one-context frame, typed outer satisfaction of a
lifted formula is ordinary multimodal Kripke satisfaction. The `accept := True`
conjunct is discharged trivially in both modal cases — that is the "fixed
accepted relations" hypothesis doing its work. -/
theorem sat_lift (U : Kripke) (V : KVal U) :
    ∀ (φ : KForm U) (w : U.World),
      Sat U.frame V.lift φ.lift w ↔ KSat U V φ w := by
  intro φ
  induction φ with
  | status s c => exact fun _ => Iff.rfl
  | top => exact fun _ => Iff.rfl
  | neg φ ih => exact fun w => not_congr (ih w)
  | conj φ ψ ihφ ihψ => exact fun w => and_congr (ihφ w) (ihψ w)
  | box b φ ih =>
    intro w
    constructor
    · intro h v hR
      exact (ih v).mp (h v ⟨hR, trivial⟩)
    · intro h v hA
      exact (ih v).mpr (h v hA.1)
  | dia b φ ih =>
    intro w
    constructor
    · rintro ⟨v, hA, hv⟩
      exact ⟨v, hA.1, (ih v).mp hv⟩
    · rintro ⟨v, hR, hv⟩
      exact ⟨v, ⟨hR, trivial⟩, (ih v).mpr hv⟩

end Lara.PW
