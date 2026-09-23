/-
Finite evaluation of the existing outer grammar. A host supplies an exact list
of accepted successors at each bridge/world; this is an explicit presentation
of the abstract relation, not a finiteness assumption on every PW frame.
-/
import Lara.PW.Outer

namespace Lara.PW

/-- A finite presentation of accepted successors. Duplicates are harmless for
Boolean modal evaluation; membership, not multiplicity, presents the relation. -/
structure Finite (F : Frame) where
  successors : (b : F.B) → F.World (F.src b) → List (F.World (F.tgt b))
  mem_successors : ∀ b w v, v ∈ successors b w ↔ F.A b w v

/-- A decidable local observation, supplied by the host. -/
def Observation (F : Frame) :=
  {κ : F.K} → F.World κ → F.Query κ → Lara.Grounded.Status → Bool

/-- Executable satisfaction. Primitive modalities do not translate operands. -/
def evalFinite {F : Frame} (M : Finite F) (obs : Observation F) :
    {κ : F.K} → Form F κ → F.World κ → Bool
  | _, .status s c, w => obs w c s
  | _, .top, _ => true
  | _, .neg φ, w => !(evalFinite M obs φ w)
  | _, .conj φ ψ, w => evalFinite M obs φ w && evalFinite M obs ψ w
  | _, .box b φ, w => (M.successors b w).all (evalFinite M obs φ)
  | _, .dia b φ, w => (M.successors b w).any (evalFinite M obs φ)

/-- Finite execution agrees with the unchanged proposition-valued semantics,
provided the successor lists present exactly the accepted relation. -/
theorem evalFinite_iff {F : Frame} (M : Finite F) (obs : Observation F)
    {κ : F.K} (φ : Form F κ) (w : F.World κ) :
    evalFinite M obs φ w = true ↔
      Sat F (fun w c s => obs w c s = true) φ w := by
  induction φ with
  | status s c => rfl
  | top => simp [evalFinite, Sat]
  | neg φ ih => simpa [evalFinite, Sat, Bool.not_eq_true] using not_congr (ih w)
  | conj φ ψ ihφ ihψ => simp [evalFinite, Sat, ihφ w, ihψ w]
  | box b φ ih =>
    simp only [evalFinite, List.all_eq_true, Sat]
    constructor
    · intro h v hv
      exact (ih v).mp (h v ((M.mem_successors b w v).mpr hv))
    · intro h v hv
      exact (ih v).mpr (h v ((M.mem_successors b w v).mp hv))
  | dia b φ ih =>
    simp only [evalFinite, List.any_eq_true, Sat]
    constructor
    · rintro ⟨v, hv, hφ⟩
      exact ⟨v, (M.mem_successors b w v).mp hv, (ih v).mp hφ⟩
    · rintro ⟨v, hv, hφ⟩
      exact ⟨v, (M.mem_successors b w v).mpr hv, (ih v).mpr hφ⟩

end Lara.PW
