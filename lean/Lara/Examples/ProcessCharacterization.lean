import Lara.Process.Characterization
import Lara.Examples.ProcessOrder

/-!
Witnesses for the Hennessy–Milner characterization over process histories.

The alphabet holds the plan commit, the evaluation read and the run; the atom
is precommitment of the run. After the commit and the read, in either order,
the formula "after the run event, the run is precommitted" holds for the
commit-first history and fails for the read-first one. So the two histories are
not formula-equivalent and hence not bisimilar, although they have the same
event multiset and no atom tells them apart before the run. This uses the easy
direction of the characterization (bisimilar states are formula-equivalent);
the converse is the general theorem `formulaEquivalent_iff_bisimilar`.
-/

namespace Lara.Examples.ProcessCharacterization

open Lara.Process
open Lara.Examples.ProcessOrder

/-- The only atom: precommitment of `run0`. -/
abbrev atoms : Unit → ProcessHistory → Prop := fun _ h => RunPrecommitted h run0

def system : TransitionSystem ProcessHistory Stamped Unit := processSystem [commit, read, run] atoms

def precommittedAfterRun : ProfileFormula Stamped Unit := .dia run (.atom ())

theorem formula_separates :
    precommittedAfterRun.sat system [commit, read] ∧ ¬ precommittedAfterRun.sat system [read, commit] := by
  constructor
  · exact ⟨[commit, read, run], ⟨by decide, rfl, by decide⟩,
      show RunPrecommitted [commit, read, run] run0 by decide⟩
  · rintro ⟨h', ⟨_, rfl, _⟩, sat⟩
    exact absurd (show RunPrecommitted ([read, commit] ++ [run]) run0 from sat) (by decide)

/-- Before the run, the atom holds vacuously in both histories: no atom
separates them, yet a formula does. -/
theorem atoms_agree_before_run : atoms () [commit, read] ∧ atoms () [read, commit] :=
  ⟨show RunPrecommitted [commit, read] run0 by decide,
    show RunPrecommitted [read, commit] run0 by decide⟩

theorem not_bisimilar : ¬ Bisimilar system [commit, read] [read, commit] := by
  intro bisim
  have eqv := (process_characterization [commit, read, run] atoms _ _).mpr bisim
  exact formula_separates.2 ((eqv precommittedAfterRun).mp formula_separates.1)

end Lara.Examples.ProcessCharacterization
