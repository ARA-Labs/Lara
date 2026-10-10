import Lara.Grounded
import Lara.Process.Contract

/-!
R0 of the research-process layer: refutations of six tempting laws.

Each theorem is a small decidable countermodel. They fix which positive laws
later stages may attempt:

* `stricter_profile_reinstates`: a stricter evidence profile can entitle *more*
  claims, so R2 proves only the directional version.
* `quarantine_reinstates`: quarantine can add warrant, so R5's iff is restricted
  to the support-only fragment.
* `unchanged_status_different_basis`: equal public status does not mean equal
  justification, so entitlement is keyed by witness.
* `empty_compatible_vacuous`: supervaluation over an empty set makes every
  property and its negation certain, so verdicts have an `inconsistent` case.
* `past_completion_not_future`: completing the past differs from continuing into
  the future, so `compat` and `continues` stay separate.
* `multiset_forgets_plan_order`: no predicate of the event multiset decides
  whether a plan was committed before the data was read, so order predicates
  are stated over ordered histories.

The first three use only the core grounded semantics.
-/

namespace Lara.Examples.ProcessFalseLaws

open Lara.Grounded
open Lara.Process

/-! ### 1. A stricter profile can entitle more claims -/

/-- Argument `0` supports the claim; argument `1` attacks it. -/
def kindedAF : AF := ⟨[0, 1], fun a b => a == 1 && b == 0⟩

/-- The claim's own argument is observed; its attacker is merely supported. -/
def kindOf : Arg → EvidenceKind
  | 0 => .observed
  | _ => .supported

/-- The framework seen by a profile admitting `admissible` evidence kinds. -/
def underKinds (F : AF) (admissible : Finset EvidenceKind) : AF :=
  ⟨F.args.filter fun a => decide (kindOf a ∈ admissible), F.attack⟩

def claim : Claim := ⟨[0], []⟩

def laxKinds : Finset EvidenceKind := {.supported, .observed}
def strictKinds : Finset EvidenceKind := {.observed}

/-- Removing the admissible kind `supported` deletes the attacker and turns a
defeated claim into a justified one. "A stricter profile entitles fewer claims"
is false without a directionality side condition. -/
theorem stricter_profile_reinstates :
    strictKinds ⊆ laxKinds ∧
      statusC (underKinds kindedAF laxKinds) claim = .defeated ∧
      statusC (underKinds kindedAF strictKinds) claim = .justified := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### 2. Quarantine can reinstate a claim -/

/-- The source leaves each argument's support uses: the attacker `1` rests on
leaf `7`. -/
def leavesOf : Arg → List Nat
  | 1 => [7]
  | _ => [3]

/-- Quarantine removes every argument whose support uses a quarantined leaf. -/
def quarantine (F : AF) (Q : List Nat) : AF :=
  ⟨F.args.filter fun a => (leavesOf a).all fun leaf => !(Q.contains leaf), F.attack⟩

/-- Quarantining the defeater's support reinstates its target: quarantine does
not only remove warrant. -/
theorem quarantine_reinstates :
    statusC kindedAF claim = .defeated ∧
      statusC (quarantine kindedAF [7]) claim = .justified := by
  refine ⟨by decide, by decide⟩

/-! ### 3. Equal status, different justification -/

/-- Before the update: `1` attacks the claim's argument `0` and `3` defends it. -/
def beforeAF : AF := ⟨[0, 1, 3], fun a b => (a == 1 && b == 0) || (a == 3 && b == 1)⟩

/-- After the update: the defender `3` is replaced by a different defender `2`. -/
def afterAF : AF := ⟨[0, 1, 2], fun a b => (a == 1 && b == 0) || (a == 2 && b == 1)⟩

/-- Remove one argument from a framework. -/
def removeArg (F : AF) (x : Arg) : AF := ⟨F.args.filter (· != x), F.attack⟩

/-- The claim stays `justified` across the update, but through a different
defender: removing `2` leaves the old status unchanged and defeats the new one.
Unchanged status does not transport warrant. -/
theorem unchanged_status_different_basis :
    statusC beforeAF claim = .justified ∧ statusC afterAF claim = .justified ∧
      statusC (removeArg beforeAF 2) claim = .justified ∧
      statusC (removeArg afterAF 2) claim = .defeated := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ### 4. An empty compatible set is not harmless -/

/-- A record no history is compatible with, for example one with contradictory
admitted constraints. -/
def noCompat : Bool → Prop := fun _ => False

instance : DecidablePred noCompat := fun _ => isFalse id

/-- Naive supervaluation certifies a property and its negation at once, while
the verdict reports the record as inconsistent. -/
theorem empty_compatible_vacuous :
    (∀ x, noCompat x → x = true) ∧ (∀ x, noCompat x → ¬ x = true) ∧
      verdict noCompat (fun x => x = true) = .inconsistent := by
  refine ⟨fun _ h => h.elim, fun _ h => h.elim, by decide⟩

/-! ### 5. Completing the past is not continuing the future -/

def claimC : ClaimId := ⟨0⟩
def sourceS : SourceId := ⟨0⟩
def witnessW : WitnessId := ⟨0⟩

/-- The submitted history: the claim was asserted. -/
def asserted : ProcessHistory := [⟨⟨0⟩, .assert claimC witnessW⟩]

/-- A later continuation in which the claim's source is retracted. -/
def retracted : ProcessHistory := asserted ++ [⟨⟨1⟩, .retract sourceS⟩]

/-- The claim is warranted while its source is unretracted. -/
def warranted (h : ProcessHistory) : Prop := ∀ e ∈ h, e.event ≠ .retract sourceS

instance (h : ProcessHistory) : Decidable (warranted h) := by
  unfold warranted; infer_instance

/-- The two candidate histories of this tiny model. -/
inductive Candidate where
  | now
  | later
  deriving DecidableEq, Repr, Fintype

def Candidate.history : Candidate → ProcessHistory
  | .now => asserted
  | .later => retracted

/-- Past completions of the submitted record: the submission cutoff is the
asserted history, so only `now` completes it. -/
def pastCompat (x : Candidate) : Prop := x.history = asserted

instance : DecidablePred pastCompat := fun _ => inferInstanceAs (Decidable (_ = _))

def future : FutureSemantics Candidate :=
  ⟨fun x y => x.history <+: y.history ∧ x ≠ y⟩

/-- Every past completion warrants the claim, yet a future continuation of a
compatible history defeats it. Merging `continues` into `compat` would change
the verdict. -/
theorem past_completion_not_future :
    verdict pastCompat (fun x => warranted x.history) = .certainTrue ∧
      future.continues .now .later ∧ ¬ warranted Candidate.later.history := by
  refine ⟨by decide, ⟨⟨_, rfl⟩, by decide⟩, by decide⟩

/-! ### 6. The event multiset forgets plan order -/

def plan : PlanId := ⟨0⟩
def actor : ActorId := ⟨0⟩
def testData : DataId := ⟨1⟩

def commitEvent : Stamped := ⟨⟨0⟩, .commitPlan actor plan ⟨0⟩⟩
def readEvent : Stamped := ⟨⟨1⟩, .access actor testData .evaluation⟩

/-- Plan committed, then evaluation data read. -/
def committedFirst : ProcessHistory := [commitEvent, readEvent]

/-- Evaluation data read, then plan committed. -/
def readFirst : ProcessHistory := [readEvent, commitEvent]

/-- The commit occurs at an earlier position than the read. -/
def commitPrecedesRead (h : ProcessHistory) : Prop :=
  ∃ i j : Fin h.length, i < j ∧ h[i] = commitEvent ∧ h[j] = readEvent

instance (h : ProcessHistory) : Decidable (commitPrecedesRead h) := by
  unfold commitPrecedesRead; infer_instance

/-- The two histories have the same event multiset, but only one commits the
plan before reading the evaluation data. So no predicate of the multiset (the
shape of `Lara.BHL.History`) can state plan precommitment. -/
theorem multiset_forgets_plan_order :
    (committedFirst : Multiset Stamped) = readFirst ∧
      commitPrecedesRead committedFirst ∧ ¬ commitPrecedesRead readFirst ∧
      ¬ ∃ P : Multiset Stamped → Prop, ∀ h : ProcessHistory, P h ↔ commitPrecedesRead h := by
  have same : (committedFirst : Multiset Stamped) = readFirst :=
    Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ [])
  have yes : commitPrecedesRead committedFirst := by decide
  have no : ¬ commitPrecedesRead readFirst := by decide
  refine ⟨same, yes, no, ?_⟩
  rintro ⟨P, hP⟩
  exact no ((hP readFirst).mp (same ▸ (hP committedFirst).mpr yes))

end Lara.Examples.ProcessFalseLaws
