/-
Executable construction of proof-bearing checked programs.

The argument pass retains the checked support result for each source
declaration.  The attack pass resolves its source from that cache and invokes
`checkAttackWithSource`; it never re-infers a source term.  Open obligations
are a program-boundary gap, not a frozen rejection class, and therefore have a
separate `ProgramError` constructor.
-/

import Lara.Compile
import Lara.Check.Attack

namespace Lara.Check

open Lara Lara.Support Lara.Attack

inductive DeclLoc where
  | argument : Nat → DeclLoc
  | attack : Nat → DeclLoc
deriving DecidableEq

inductive ProgramError where
  | rejection : DeclLoc → CheckError → ProgramError
  | duplicateArgument : Nat → Nat → ProgramError
  | incompleteArgument : Nat → List QuestionId → ProgramError
deriving DecidableEq

/-- Only wrapped frozen checker failures have an R-class.  Structural
duplicates and valid-but-incomplete arguments are program-boundary outcomes. -/
def ProgramError.rejectClass : ProgramError → Option RejectClass
  | .rejection _ e => some e.rejectClass
  | .duplicateArgument _ _ => none
  | .incompleteArgument _ _ => none

theorem incompleteArgument_no_rejectClass (i : Nat)
    (obligations : List QuestionId) :
    (ProgramError.incompleteArgument i obligations).rejectClass = none :=
  rfl

/-! ### Deterministic structural duplicate detection -/

private def firstEqualIndex (w : SupportTerm) :
    Nat → List SupportTerm → Option Nat
  | _, [] => none
  | i, x :: xs => if w = x then some i else firstEqualIndex w (i + 1) xs

private theorem firstEqualIndex_none_iff (w : SupportTerm) :
    ∀ (i : Nat) (xs : List SupportTerm),
      firstEqualIndex w i xs = none ↔ w ∉ xs := by
  intro i xs
  induction xs generalizing i with
  | nil => simp [firstEqualIndex]
  | cons x xs ih =>
      by_cases h : w = x
      · simp [firstEqualIndex, h]
      · simp [firstEqualIndex, h, ih]

private def firstDuplicateFrom :
    Nat → List SupportTerm → Option (Nat × Nat)
  | _, [] => none
  | i, w :: ws =>
      match firstEqualIndex w (i + 1) ws with
      | some j => some (i, j)
      | none => firstDuplicateFrom (i + 1) ws

def firstDuplicate (args : List SupportTerm) : Option (Nat × Nat) :=
  firstDuplicateFrom 0 args

private theorem firstDuplicateFrom_none_iff
    (i : Nat) (args : List SupportTerm) :
    firstDuplicateFrom i args = none ↔ args.Nodup := by
  cases args with
  | nil => simp [firstDuplicateFrom]
  | cons w ws =>
      simp only [firstDuplicateFrom]
      cases hfind : firstEqualIndex w (i + 1) ws with
      | some j =>
          have hmem : w ∈ ws := by
            by_cases hmem : w ∈ ws
            · exact hmem
            · have hnone :=
                (firstEqualIndex_none_iff w (i + 1) ws).mpr hmem
              rw [hfind] at hnone
              contradiction
          simp [hmem]
      | none =>
          have hnot : w ∉ ws :=
            (firstEqualIndex_none_iff w (i + 1) ws).mp hfind
          simp only [hnot, List.nodup_cons, not_false_eq_true, true_and]
          exact firstDuplicateFrom_none_iff (i + 1) ws
termination_by args.length
decreasing_by simp

theorem firstDuplicate_none_iff (args : List SupportTerm) :
    firstDuplicate args = none ↔ args.Nodup :=
  firstDuplicateFrom_none_iff 0 args

/-! ### Checked argument cache -/

structure CheckedArguments {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (args : List SupportTerm) where
  cache : List (CheckedSupport canon Pi Gamma reg)
  aligned : cache.map (·.term) = args
  complete :
    ∀ entry ∈ cache, entry.result.obligations = []

/-- Alignment transports the program's no-duplicate boundary to cache keys,
so the term-keyed lookup cannot have two source occurrences. -/
theorem CheckedArguments.cache_nodup {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {args : List SupportTerm}
    (checked : CheckedArguments Pi Gamma reg args) (h : args.Nodup) :
    (checked.cache.map (·.term)).Nodup := by
  rw [checked.aligned]
  exact h

private def checkArguments {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) :
    (i : Nat) → (args : List SupportTerm) →
      Except ProgramError (CheckedArguments Pi Gamma reg args)
  | _, [] => .ok ⟨[], rfl, by simp⟩
  | i, w :: ws =>
      match hresult : inferSupport Pi Gamma reg .root w with
      | .error e => .error (.rejection (.argument i) e)
      | .ok result =>
          match hobligations : result.obligations with
          | _ :: _ =>
              .error (.incompleteArgument i result.obligations)
          | [] =>
              match checkArguments Pi Gamma reg (i + 1) ws with
              | .error e => .error e
              | .ok rest =>
                  let entry : CheckedSupport canon Pi Gamma reg :=
                    ⟨w, result, inferSupport_sound hresult⟩
                  .ok
                    { cache := entry :: rest.cache
                    , aligned := by simp [entry, rest.aligned]
                    , complete := by
                        intro candidate hcandidate
                        simp only [List.mem_cons] at hcandidate
                        rcases hcandidate with rfl | htail
                        · exact hobligations
                        · exact rest.complete candidate htail }

def lookupChecked {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} (requested : SupportTerm) :
    List (CheckedSupport canon Pi Gamma reg) →
      Option (CheckedSupport canon Pi Gamma reg)
  | [] => none
  | entry :: entries =>
      if entry.term = requested then some entry
      else lookupChecked requested entries

theorem lookupChecked_term {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {requested : SupportTerm}
    {cache : List (CheckedSupport canon Pi Gamma reg)}
    {entry : CheckedSupport canon Pi Gamma reg}
    (h : lookupChecked requested cache = some entry) :
    entry.term = requested := by
  induction cache with
  | nil => simp [lookupChecked] at h
  | cons head tail ih =>
      by_cases heq : head.term = requested
      · simp [lookupChecked, heq] at h
        subst entry
        exact heq
      · simp [lookupChecked, heq] at h
        exact ih h

theorem lookupChecked_complete {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {requested : SupportTerm}
    {cache : List (CheckedSupport canon Pi Gamma reg)}
    (hmem : requested ∈ cache.map (·.term)) :
    ∃ entry, lookupChecked requested cache = some entry := by
  induction cache with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with heq | htail
      · refine ⟨head, ?_⟩
        simp [lookupChecked, heq]
      · by_cases heq : head.term = requested
        · exact ⟨head, by simp [lookupChecked, heq]⟩
        · obtain ⟨entry, hentry⟩ := ih htail
          exact ⟨entry, by simp [lookupChecked, heq, hentry]⟩

/-! ### Attack pass over the retained cache -/

structure CheckedAttacks {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (dp : DefeatPolicy)
    (args : List SupportTerm) (atts : List Attack) : Type where
  typed :
    ∀ k ∈ atts, HasAttack canon Pi Gamma (certOkOf reg) dp k
  source_declared : ∀ k ∈ atts, k.source ∈ args
  target_declared : ∀ k ∈ atts, k.target ∈ args

private def checkAttacks {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (dp : DefeatPolicy)
    (args : List SupportTerm)
    (cache : List (CheckedSupport canon Pi Gamma reg))
    (aligned : cache.map (·.term) = args) :
    (i : Nat) → (atts : List Attack) →
      Except ProgramError (CheckedAttacks Pi Gamma reg dp args atts)
  | _, [] => .ok ⟨by simp, by simp, by simp⟩
  | i, k :: ks =>
      if hsource : k.source ∈ args then
        if htarget : k.target ∈ args then
          match hlookup : lookupChecked k.source cache with
          | none =>
              .error (.rejection (.attack i)
                (.R1 .root (.undeclaredAttackSource k.source)))
          | some source =>
              let source_eq : source.term = k.source :=
                lookupChecked_term hlookup
              match hchecked :
                  checkAttackWithSource dp k source source_eq with
              | .error e => .error (.rejection (.attack i) e)
              | .ok () =>
                  match checkAttacks Pi Gamma reg dp args cache aligned
                      (i + 1) ks with
                  | .error e => .error e
                  | .ok rest =>
                      .ok
                        { typed := by
                            intro candidate hcandidate
                            simp only [List.mem_cons] at hcandidate
                            rcases hcandidate with rfl | htail
                            · exact checkAttackWithSource_sound source_eq hchecked
                            · exact rest.typed candidate htail
                        , source_declared := by
                            intro candidate hcandidate
                            simp only [List.mem_cons] at hcandidate
                            rcases hcandidate with rfl | htail
                            · exact hsource
                            · exact rest.source_declared candidate htail
                        , target_declared := by
                            intro candidate hcandidate
                            simp only [List.mem_cons] at hcandidate
                            rcases hcandidate with rfl | htail
                            · exact htarget
                            · exact rest.target_declared candidate htail }
        else
          .error (.rejection (.attack i)
            (.R1 .root (.undeclaredAttackTarget k.target)))
      else
        .error (.rejection (.attack i)
          (.R1 .root (.undeclaredAttackSource k.source)))

/-! ### Public program checker and exact adequacy -/

def checkProgram {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (dp : DefeatPolicy)
    (args : List SupportTerm) (atts : List Attack) :
    Except ProgramError
      (Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp) :=
  -- args -> checked/aligned cache -> attack source cache lookup -> CheckedProgram
  match hduplicate : firstDuplicate args with
  | some (i, j) => .error (.duplicateArgument i j)
  | none =>
      match checkArguments Pi Gamma reg 0 args with
      | .error e => .error e
      | .ok checkedArgs =>
          match checkAttacks Pi Gamma reg dp args checkedArgs.cache
              checkedArgs.aligned 0 atts with
          | .error e => .error e
          | .ok checkedAttacks =>
              .ok
                { args := args
                , nodup := (firstDuplicate_none_iff args).mp hduplicate
                , complete := by
                    intro w hw
                    have hcache : w ∈ checkedArgs.cache.map (·.term) := by
                      rw [checkedArgs.aligned]
                      exact hw
                    obtain ⟨entry, hentry, hterm⟩ :=
                      List.mem_map.mp hcache
                    refine ⟨entry.result.conclusion, ?_⟩
                    have hobligations :=
                      checkedArgs.complete entry hentry
                    simpa [hterm, hobligations] using entry.valid
                , atts := atts
                , typed := checkedAttacks.typed
                , source_declared := checkedAttacks.source_declared
                , target_declared := checkedAttacks.target_declared }

private theorem checkArguments_complete {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) :
    ∀ (i : Nat) (args : List SupportTerm),
      (∀ w ∈ args, ∃ C,
        HasSupport canon Pi Gamma (certOkOf reg) w C []) →
      ∃ checked, checkArguments Pi Gamma reg i args = .ok checked := by
  intro i args
  induction args generalizing i with
  | nil =>
      intro _
      exact ⟨⟨[], rfl, by simp⟩, rfl⟩
  | cons w ws ih =>
      intro hcomplete
      obtain ⟨C, hw⟩ := hcomplete w (by simp)
      have hinfer := inferSupport_complete hw .root
      obtain ⟨rest, hrest⟩ := ih (i + 1) (by
        intro x hx
        exact hcomplete x (by simp [hx]))
      simp only [checkArguments]
      split
      · rename_i e herror
        rw [hinfer] at herror
        contradiction
      · rename_i result hok
        have hresult : result = ⟨C, []⟩ :=
          Except.ok.inj (hok.symm.trans hinfer)
        subst result
        simp only
        split
        · rename_i e herror
          rw [hrest] at herror
          contradiction
        · rename_i tail hoktail
          have htail : tail = rest :=
            Except.ok.inj (hoktail.symm.trans hrest)
          subst tail
          exact ⟨_, rfl⟩

private theorem checkAttacks_complete {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (dp : DefeatPolicy)
    (args : List SupportTerm)
    (cache : List (CheckedSupport canon Pi Gamma reg))
    (aligned : cache.map (·.term) = args) :
    ∀ (i : Nat) (atts : List Attack),
      (∀ k ∈ atts, HasAttack canon Pi Gamma (certOkOf reg) dp k) →
      (∀ k ∈ atts, k.source ∈ args) →
      (∀ k ∈ atts, k.target ∈ args) →
      ∃ checked,
        checkAttacks Pi Gamma reg dp args cache aligned i atts =
          .ok checked := by
  intro i atts
  induction atts generalizing i with
  | nil =>
      intro _ _ _
      exact ⟨⟨by simp, by simp, by simp⟩, rfl⟩
  | cons k ks ih =>
      intro htyped hsource htarget
      have hsrc : k.source ∈ args := hsource k (by simp)
      have htgt : k.target ∈ args := htarget k (by simp)
      have hcache : k.source ∈ cache.map (·.term) := by
        rw [aligned]
        exact hsrc
      obtain ⟨source, hlookup⟩ := lookupChecked_complete hcache
      have source_eq : source.term = k.source :=
        lookupChecked_term hlookup
      have hchecked := checkAttackWithSource_complete source_eq
        (htyped k (by simp))
      obtain ⟨rest, hrest⟩ := ih (i + 1)
        (by
          intro candidate hc
          exact htyped candidate (by simp [hc]))
        (by
          intro candidate hc
          exact hsource candidate (by simp [hc]))
        (by
          intro candidate hc
          exact htarget candidate (by simp [hc]))
      simp only [checkAttacks]
      rw [dif_pos hsrc, dif_pos htgt]
      split
      · rename_i hnone
        rw [hlookup] at hnone
        contradiction
      · rename_i found hfound
        have hfound_eq : found = source :=
          Option.some.inj (hfound.symm.trans hlookup)
        subst found
        split
        · rename_i e herror
          have hchecked' :
              checkAttackWithSource dp k source
                (lookupChecked_term hfound) = .ok () := by
            simpa using hchecked
          rw [hchecked'] at herror
          contradiction
        · rename_i hok
          split
          · rename_i e herror
            rw [hrest] at herror
            contradiction
          · rename_i tail hoktail
            have htail : tail = rest :=
              Except.ok.inj (hoktail.symm.trans hrest)
            subst tail
            exact ⟨_, rfl⟩

/-- Every successful result exposes all compile-boundary invariants, and its
raw declaration lists are exactly those supplied to the checker. -/
theorem checkProgram_sound {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    {program : Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp}
    (h : checkProgram Pi Gamma reg dp args atts = .ok program) :
    program.args = args ∧ program.atts = atts ∧
      args.Nodup ∧
      (∀ w ∈ args, ∃ C,
        HasSupport canon Pi Gamma (certOkOf reg) w C []) ∧
      (∀ k ∈ atts,
        HasAttack canon Pi Gamma (certOkOf reg) dp k) ∧
      (∀ k ∈ atts, k.source ∈ args) ∧
      (∀ k ∈ atts, k.target ∈ args) := by
  unfold checkProgram at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · simp only [Except.ok.injEq] at h
        have hargs : program.args = args :=
          (congrArg Compile.CheckedProgram.args h).symm
        have hatts : program.atts = atts :=
          (congrArg Compile.CheckedProgram.atts h).symm
        refine ⟨hargs, hatts, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [hargs] using program.nodup
        · intro w hw
          apply program.complete w
          simpa [hargs] using hw
        · intro k hk
          apply program.typed k
          simpa [hatts] using hk
        · intro k hk
          have hk' : k ∈ program.atts := by
            simpa [hatts] using hk
          have := program.source_declared k hk'
          simpa [hargs] using this
        · intro k hk
          have hk' : k ∈ program.atts := by
            simpa [hatts] using hk
          have := program.target_declared k hk'
          simpa [hargs] using this

/-- Exact completeness for the dependent output: every raw declaration list
satisfying the strengthened relational compile boundary produces some checked
program carrying those declarations. -/
theorem checkProgram_complete {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    (hnodup : args.Nodup)
    (hcomplete : ∀ w ∈ args, ∃ C,
      HasSupport canon Pi Gamma (certOkOf reg) w C [])
    (htyped : ∀ k ∈ atts,
      HasAttack canon Pi Gamma (certOkOf reg) dp k)
    (hsource : ∀ k ∈ atts, k.source ∈ args)
    (htarget : ∀ k ∈ atts, k.target ∈ args) :
    ∃ program, checkProgram Pi Gamma reg dp args atts = .ok program := by
  have hduplicate : firstDuplicate args = none :=
    (firstDuplicate_none_iff args).mpr hnodup
  obtain ⟨checkedArgs, hargs⟩ :=
    checkArguments_complete Pi Gamma reg 0 args hcomplete
  obtain ⟨checkedAttacks, hatts⟩ :=
    checkAttacks_complete Pi Gamma reg dp args checkedArgs.cache
      checkedArgs.aligned 0 atts htyped hsource htarget
  unfold checkProgram
  split
  · rename_i pair hpair
    rw [hduplicate] at hpair
    contradiction
  · split
    · rename_i e herror
      rw [hargs] at herror
      contradiction
    · rename_i found hfound
      have hfound_eq : found = checkedArgs :=
        Except.ok.inj (hfound.symm.trans hargs)
      subst found
      split
      · rename_i e herror
        rw [hatts] at herror
        contradiction
      · rename_i foundAttacks hfoundAttacks
        have hfoundAttacks_eq : foundAttacks = checkedAttacks :=
          Except.ok.inj (hfoundAttacks.symm.trans hatts)
        subst foundAttacks
        exact ⟨_, rfl⟩

theorem checkProgram_accepted_source_declared {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    {program : Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp}
    (h : checkProgram Pi Gamma reg dp args atts = .ok program) :
    ∀ k ∈ atts, k.source ∈ args :=
  (checkProgram_sound h).2.2.2.2.2.1

theorem checkProgram_accepted_target_declared {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    {program : Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp}
    (h : checkProgram Pi Gamma reg dp args atts = .ok program) :
    ∀ k ∈ atts, k.target ∈ args :=
  (checkProgram_sound h).2.2.2.2.2.2

/-- An accepted AF node always has empty obligations; incompleteness can only
leave through `ProgramError.incompleteArgument`, never through a checked
program. -/
theorem checkProgram_nodes_complete {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    {program : Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp}
    (h : checkProgram Pi Gamma reg dp args atts = .ok program) :
    ∀ w ∈ args, ∃ C,
      HasSupport canon Pi Gamma (certOkOf reg) w C [] :=
  (checkProgram_sound h).2.2.2.1

end Lara.Check
