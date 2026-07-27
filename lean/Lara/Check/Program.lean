/-
Executable construction of proof-bearing checked programs.

The legacy `checkProgram` projection preserves its generic behavior and
attack-soundness-only `CheckedProgram` result. The detailed acceptance path
runs duplicate arguments, support, typed attacks, then missing-conflict
coverage, in that fixed order. Its argument pass retains the checked support
result for every source declaration; both typed-attack checking and the final
conflict scan derive their nodes from that cache and never re-infer support.
`ProgramAcceptance` carries the additional attack-completeness witness and
retained nodes needed by the public `checkUnit` boundary. Open obligations are
a program-boundary gap, not a frozen rejection class, and therefore have a
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

structure MissingConflict where
  sourceIndex : Nat
  targetIndex : Nat
  sourceConclusion : Atom
  targetConclusion : Atom
deriving DecidableEq

inductive ProgramError where
  | rejection : DeclLoc → CheckError → ProgramError
  | duplicateArgument : Nat → Nat → ProgramError
  | incompleteArgument : Nat → List QuestionId → ProgramError
  | missingConflict : MissingConflict → ProgramError
deriving DecidableEq

/-- Only wrapped frozen checker failures have an R-class.  Structural
duplicates and valid-but-incomplete arguments are program-boundary outcomes. -/
def ProgramError.rejectClass : ProgramError → Option RejectClass
  | .rejection _ e => some e.rejectClass
  | .duplicateArgument _ _ => none
  | .incompleteArgument _ _ => none
  | .missingConflict _ => none

theorem incompleteArgument_no_rejectClass (i : Nat)
    (obligations : List QuestionId) :
    (ProgramError.incompleteArgument i obligations).rejectClass = none :=
  rfl

theorem missingConflict_no_rejectClass (missing : MissingConflict) :
    (ProgramError.missingConflict missing).rejectClass = none :=
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

/-- Repackage a complete support-check result as the exact public node view.
This is a lossless conversion: the conclusion and validity proof are the ones
already produced by `inferSupport`; only the now-known empty obligations are
specialized. -/
def CheckedSupport.toCheckedNode {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon}
    (entry : CheckedSupport canon Pi Gamma reg)
    (hcomplete : entry.result.obligations = []) :
    Compile.CheckedNode canon Pi Gamma (certOkOf reg) :=
  { term := entry.term
  , conclusion := entry.result.conclusion
  , valid := by simpa [hcomplete] using entry.valid }

/-- The retained indexed node view, derived directly from the argument cache.
No support term is checked again and no conclusion is recomputed. -/
def CheckedArguments.nodes {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {args : List SupportTerm}
    (checked : CheckedArguments Pi Gamma reg args) :
    List (Compile.CheckedNode canon Pi Gamma (certOkOf reg)) :=
  checked.cache.attach.map fun entry =>
    entry.val.toCheckedNode (checked.complete entry.val entry.property)

/-- The cache-derived node view preserves argument order and identity exactly. -/
theorem CheckedArguments.nodes_terms {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {args : List SupportTerm}
    (checked : CheckedArguments Pi Gamma reg args) :
    (checked.nodes.map (·.term)) = args := by
  simp [CheckedArguments.nodes, CheckedSupport.toCheckedNode, checked.aligned]

/-! ### Indexed conflict scan cache -/

/-- One immutable entry used by the completeness scan. Conclusions and their
proofs come from the retained support-check cache; attackability and the exact
bucket of attacks sourced at this term are computed once here. -/
structure ConflictNode
    (canon : String → String) (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop)
    (atts : List Attack) where
  index : Nat
  term : SupportTerm
  conclusion : Atom
  valid : HasSupport canon Pi Gamma CertOk term conclusion []
  disNodup : Compile.DisNodup term
  attackable : Bool
  attackable_eq : attackable = Compile.conflictAttackableB Pi term
  attacks : List Attack
  attacks_adequate :
    ∀ k, k ∈ attacks ↔ k ∈ atts ∧ k.source = term

/-- Public name for the exactness invariant of a precomputed source bucket. -/
theorem sourceAttackBucket_mem_iff
    {canon : String → String} {Pi : RuleId → Option Rule}
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {atts : List Attack}
    (source : ConflictNode canon Pi Gamma CertOk atts) (k : Attack) :
    k ∈ source.attacks ↔ k ∈ atts ∧ k.source = source.term :=
  source.attacks_adequate k

/-- Derive the scan cache in declaration order. `zipIdx` fixes the reported
locations while each node's filter creates its immutable source bucket. -/
def conflictCache
    {canon : String → String} (Pi : RuleId → Option Rule)
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (atts : List Attack)
    (nodes : List (Compile.CheckedNode canon Pi Gamma CertOk)) :
    List (ConflictNode canon Pi Gamma CertOk atts) :=
  nodes.zipIdx.map fun entry =>
    let node := entry.1
    let i := entry.2
    let bucket := atts.filter fun k => decide (k.source = node.term)
    { index := i
    , term := node.term
    , conclusion := node.conclusion
    , valid := node.valid
    , disNodup := Compile.hasSupport_disNodup node.valid
    , attackable := Compile.conflictAttackableB Pi node.term
    , attackable_eq := rfl
    , attacks := bucket
    , attacks_adequate := by
        intro k
        simp [bucket] }

theorem conflictCache_terms
    {canon : String → String} (Pi : RuleId → Option Rule)
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (atts : List Attack)
    (nodes : List (Compile.CheckedNode canon Pi Gamma CertOk)) :
    (conflictCache Pi atts nodes).map (·.term) = nodes.map (·.term) := by
  have hzip : ∀ n, (nodes.zipIdx n).map (fun entry => entry.1.term) =
      nodes.map (·.term) := by
    intro n
    induction nodes generalizing n with
    | nil => rfl
    | cons node rest ih =>
      simp only [List.zipIdx_cons, List.map_cons]
      exact congrArg (node.term :: ·) (ih (n + 1))
  unfold conflictCache
  rw [List.map_map]
  change (nodes.zipIdx.map (fun entry => entry.1.term)) =
    nodes.map (·.term)
  exact hzip 0

private theorem mem_map_fst_zipIdx_iff {α : Type} (x : α)
    (xs : List α) (n : Nat) :
    x ∈ (xs.zipIdx n).map Prod.fst ↔ x ∈ xs := by
  induction xs generalizing n with
  | nil => simp
  | cons y ys ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.mem_cons]
    exact or_congr Iff.rfl (ih (n + 1))

/-- Restricting coverage to a source's precomputed attack bucket changes
nothing for an edge with that source. -/
theorem sourceAttackBucket_coveredB_iff
    {canon : String → String} {Pi : RuleId → Option Rule}
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {atts : List Attack}
    (source target : ConflictNode canon Pi Gamma CertOk atts) :
    Compile.coveredB source.attacks source.term target.term = true ↔
      Compile.Covered atts source.term target.term := by
  rw [Compile.coveredB_iff target.disNodup]
  constructor
  · rintro ⟨k, hk, hsource, t, hocc, hcontains⟩
    exact ⟨k, (sourceAttackBucket_mem_iff source k).mp hk |>.1,
      hsource, t, hocc, hcontains⟩
  · rintro ⟨k, hk, hsource, t, hocc, hcontains⟩
    exact ⟨k, (sourceAttackBucket_mem_iff source k).mpr ⟨hk, hsource⟩,
      hsource, t, hocc, hcontains⟩

/-- Source-major, target-major search for the first uncovered attackable
contrary pair. Both traversals restart from the same immutable indexed cache,
so ordered self-pairs are included and diagnostics are lexicographic. -/
def firstMissingConflict?
    {canon : String → String} {Pi : RuleId → Option Rule}
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {atts : List Attack}
    (dp : DefeatPolicy)
    (cache : List (ConflictNode canon Pi Gamma CertOk atts)) :
    Option MissingConflict :=
  cache.zipIdx.findSome? fun sourceAt =>
    cache.zipIdx.findSome? fun targetAt =>
      let source := sourceAt.1
      let target := targetAt.1
      if Attack.contraryMatchB canon dp
          source.conclusion target.conclusion then
        if target.attackable then
          if Compile.coveredB source.attacks source.term target.term then
            none
          else
            some
              { sourceIndex := source.index
              , targetIndex := target.index
              , sourceConclusion := source.conclusion
              , targetConclusion := target.conclusion }
        else none
      else none

/-- Exact adequacy of the single diagnostic scan. `none` means precisely that
every attackable contrary pair represented by the retained node cache is
covered by a declared compiled edge. -/
theorem firstMissingConflict_none_iff
    {canon : String → String} {Pi : RuleId → Option Rule}
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {atts : List Attack}
    (dp : DefeatPolicy)
    (cache : List (ConflictNode canon Pi Gamma CertOk atts)) :
    firstMissingConflict? dp cache = none ↔
      ∀ source ∈ cache, ∀ target ∈ cache,
        Attack.ContraryMatch canon dp
          source.conclusion target.conclusion →
        Compile.ConflictAttackable Pi target.term →
        Compile.Covered atts source.term target.term := by
  unfold firstMissingConflict?
  rw [List.findSome?_eq_none_iff]
  constructor
  · intro hnone source hsource target htarget hcontrary hattackable
    have hsource' : source ∈ (cache.zipIdx).map Prod.fst :=
      (mem_map_fst_zipIdx_iff source cache 0).mpr hsource
    obtain ⟨sourceAt, hsourceAt, rfl⟩ := List.mem_map.mp hsource'
    have htarget' : target ∈ (cache.zipIdx).map Prod.fst :=
      (mem_map_fst_zipIdx_iff target cache 0).mpr htarget
    obtain ⟨targetAt, htargetAt, rfl⟩ := List.mem_map.mp htarget'
    have hinner := hnone sourceAt hsourceAt
    rw [List.findSome?_eq_none_iff] at hinner
    have hpair := hinner targetAt htargetAt
    have hcontraryB :
        Attack.contraryMatchB canon dp sourceAt.1.conclusion
          targetAt.1.conclusion = true :=
      (Attack.contraryMatchB_iff canon dp _ _).mpr hcontrary
    have hattackableB : targetAt.1.attackable = true := by
      rw [targetAt.1.attackable_eq]
      exact (Compile.conflictAttackableB_iff Pi targetAt.1.term).mpr
        hattackable
    simp only [hcontraryB, hattackableB, ↓reduceIte] at hpair
    cases hcovered :
        Compile.coveredB sourceAt.1.attacks sourceAt.1.term
          targetAt.1.term with
    | false => simp [hcovered] at hpair
    | true =>
        exact (sourceAttackBucket_coveredB_iff sourceAt.1 targetAt.1).mp
          hcovered
  · intro hall sourceAt hsourceAt
    rw [List.findSome?_eq_none_iff]
    intro targetAt htargetAt
    by_cases hcontraryB :
        Attack.contraryMatchB canon dp sourceAt.1.conclusion
          targetAt.1.conclusion = true
    · by_cases hattackableB : targetAt.1.attackable = true
      · have hsource : sourceAt.1 ∈ cache := by
          apply (mem_map_fst_zipIdx_iff sourceAt.1 cache 0).mp
          exact List.mem_map.mpr ⟨sourceAt, hsourceAt, rfl⟩
        have htarget : targetAt.1 ∈ cache := by
          apply (mem_map_fst_zipIdx_iff targetAt.1 cache 0).mp
          exact List.mem_map.mpr ⟨targetAt, htargetAt, rfl⟩
        have hcontrary :=
          (Attack.contraryMatchB_iff canon dp _ _).mp hcontraryB
        have hattackable : Compile.ConflictAttackable Pi targetAt.1.term := by
          apply (Compile.conflictAttackableB_iff Pi targetAt.1.term).mp
          simpa [targetAt.1.attackable_eq] using hattackableB
        have hcovered :=
          hall sourceAt.1 hsource targetAt.1 htarget hcontrary hattackable
        have hcoveredB :=
          (sourceAttackBucket_coveredB_iff sourceAt.1 targetAt.1).mpr
            hcovered
        simp [hcontraryB, hattackableB, hcoveredB]
      · simp [hcontraryB, hattackableB]
    · simp [hcontraryB]

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

private structure ProgramBase {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (dp : DefeatPolicy)
    (args : List SupportTerm) (atts : List Attack) where
  program : Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp
  arguments_eq : program.args = args
  attacks_eq : program.atts = atts
  nodes : List (Compile.CheckedNode canon Pi Gamma (certOkOf reg))
  nodes_terms : nodes.map (·.term) = program.args

/-- The shared prefix of the legacy and detailed checkers. It retains the
checked argument cache through typed-attack validation, but exposes no new
public acceptance behavior by itself. -/
private def checkProgramBase {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (dp : DefeatPolicy)
    (args : List SupportTerm) (atts : List Attack) :
    Except ProgramError
      (ProgramBase Pi Gamma reg dp args atts) :=
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
              let program :
                  Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp :=
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
              .ok
                { program := program
                , arguments_eq := rfl
                , attacks_eq := rfl
                , nodes := checkedArgs.nodes
                , nodes_terms := by
                    simpa [program] using checkedArgs.nodes_terms }

/-- Legacy projection of the shared checker prefix. Its signature and
observable success/error behavior are unchanged. -/
def checkProgram {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (dp : DefeatPolicy)
    (args : List SupportTerm) (atts : List Attack) :
    Except ProgramError
      (Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp) :=
  match checkProgramBase Pi Gamma reg dp args atts with
  | .error e => .error e
  | .ok base => .ok base.program

/-- Named successful result of the detailed checker. Unlike the legacy
projection, it retains executable checked nodes and the independently proved
conflict-completeness postcondition. -/
structure ProgramAcceptance {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (dp : DefeatPolicy)
    (args : List SupportTerm) (atts : List Attack) where
  program : Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp
  attack_complete :
    Compile.AttackComplete canon Pi Gamma (certOkOf reg) dp
      program.args program.atts
  arguments_eq : program.args = args
  attacks_eq : program.atts = atts
  nodes : List (Compile.CheckedNode canon Pi Gamma (certOkOf reg))
  nodes_terms : nodes.map (·.term) = program.args

private theorem attackComplete_of_firstMissingConflict_none
    {canon : String → String} {Pi : RuleId → Option Rule}
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {dp : DefeatPolicy} {args : List SupportTerm} {atts : List Attack}
    (cache : List (ConflictNode canon Pi Gamma CertOk atts))
    (hterms : cache.map (·.term) = args)
    (hnone : firstMissingConflict? dp cache = none) :
    Compile.AttackComplete canon Pi Gamma CertOk dp args atts := by
  intro source hsource target htarget sourceConclusion targetConclusion
    hsourceValid htargetValid hcontrary hattackable
  have hsourceCache : source ∈ cache.map (·.term) := by
    rw [hterms]
    exact hsource
  obtain ⟨sourceNode, hsourceNode, hsourceTerm⟩ :=
    List.mem_map.mp hsourceCache
  have htargetCache : target ∈ cache.map (·.term) := by
    rw [hterms]
    exact htarget
  obtain ⟨targetNode, htargetNode, htargetTerm⟩ :=
    List.mem_map.mp htargetCache
  have hsourceExact :
      sourceNode.conclusion = sourceConclusion := by
    exact (hasSupport_unique sourceNode.valid
      (by simpa [hsourceTerm] using hsourceValid)).1
  have htargetExact :
      targetNode.conclusion = targetConclusion := by
    exact (hasSupport_unique targetNode.valid
      (by simpa [htargetTerm] using htargetValid)).1
  have hscan :=
    (firstMissingConflict_none_iff dp cache).mp hnone
      sourceNode hsourceNode targetNode htargetNode
  have hcovered := hscan
    (by simpa [hsourceExact, htargetExact] using hcontrary)
    (by simpa [htargetTerm] using hattackable)
  simpa [hsourceTerm, htargetTerm] using hcovered

/-- Detailed checker: run the exact legacy prefix, then reject only the first
uncovered attackable contrary pair. -/
def checkProgramDetailed {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (dp : DefeatPolicy)
    (args : List SupportTerm) (atts : List Attack) :
    Except ProgramError (ProgramAcceptance Pi Gamma reg dp args atts) :=
  match checkProgramBase Pi Gamma reg dp args atts with
  | .error e => .error e
  | .ok base =>
      let cache := conflictCache Pi atts base.nodes
      match hmissing : firstMissingConflict? dp cache with
      | some missing => .error (.missingConflict missing)
      | none =>
          .ok
            { program := base.program
            , attack_complete := by
                have hraw :=
                  attackComplete_of_firstMissingConflict_none cache
                    ((conflictCache_terms Pi atts base.nodes).trans
                      (base.nodes_terms.trans base.arguments_eq))
                    hmissing
                simpa [base.arguments_eq, base.attacks_eq] using hraw
            , arguments_eq := base.arguments_eq
            , attacks_eq := base.attacks_eq
            , nodes := base.nodes
            , nodes_terms := base.nodes_terms }

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

private theorem checkProgramBase_complete {canon : String → String}
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
    ∃ base, checkProgramBase Pi Gamma reg dp args atts = .ok base := by
  have hduplicate : firstDuplicate args = none :=
    (firstDuplicate_none_iff args).mpr hnodup
  obtain ⟨checkedArgs, hargs⟩ :=
    checkArguments_complete Pi Gamma reg 0 args hcomplete
  obtain ⟨checkedAttacks, hatts⟩ :=
    checkAttacks_complete Pi Gamma reg dp args checkedArgs.cache
      checkedArgs.aligned 0 atts htyped hsource htarget
  unfold checkProgramBase
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
  · rename_i base hbase
    have hprogram : program = base.program :=
      Except.ok.inj h |>.symm
    subst program
    have hargs := base.arguments_eq
    have hatts := base.attacks_eq
    refine ⟨hargs, hatts, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hargs] using base.program.nodup
    · intro w hw
      apply base.program.complete w
      simpa [hargs] using hw
    · intro k hk
      apply base.program.typed k
      simpa [hatts] using hk
    · intro k hk
      have hk' : k ∈ base.program.atts := by
        simpa [hatts] using hk
      have := base.program.source_declared k hk'
      simpa [hargs] using this
    · intro k hk
      have hk' : k ∈ base.program.atts := by
        simpa [hatts] using hk
      have := base.program.target_declared k hk'
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
  obtain ⟨base, hbase⟩ :=
    checkProgramBase_complete hnodup hcomplete htyped hsource htarget
  exact ⟨base.program, by simp [checkProgram, hbase]⟩

/-- A successful detailed result exposes its named semantic and executable
postconditions without recovering anything from the legacy projection. -/
theorem checkProgramDetailed_sound {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    {accepted : ProgramAcceptance Pi Gamma reg dp args atts}
    (_h : checkProgramDetailed Pi Gamma reg dp args atts = .ok accepted) :
    accepted.program.args = args ∧
    accepted.program.atts = atts ∧
    Compile.AttackComplete canon Pi Gamma (certOkOf reg) dp
      accepted.program.args accepted.program.atts ∧
    accepted.nodes.map (·.term) = accepted.program.args :=
  ⟨accepted.arguments_eq, accepted.attacks_eq, accepted.attack_complete,
    accepted.nodes_terms⟩

/-- Exact completeness of the detailed checker. The original compile-boundary
conditions reach the retained base result; attack completeness then proves
that the diagnostic scan has no witness. -/
theorem checkProgramDetailed_complete {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    (hnodup : args.Nodup)
    (hcomplete : ∀ w ∈ args, ∃ C,
      HasSupport canon Pi Gamma (certOkOf reg) w C [])
    (htyped : ∀ k ∈ atts,
      HasAttack canon Pi Gamma (certOkOf reg) dp k)
    (hsource : ∀ k ∈ atts, k.source ∈ args)
    (htarget : ∀ k ∈ atts, k.target ∈ args)
    (hattackComplete :
      Compile.AttackComplete canon Pi Gamma (certOkOf reg) dp args atts) :
    ∃ accepted,
      checkProgramDetailed Pi Gamma reg dp args atts = .ok accepted := by
  obtain ⟨base, hbase⟩ :=
    checkProgramBase_complete hnodup hcomplete htyped hsource htarget
  let cache := conflictCache Pi atts base.nodes
  have hterms : cache.map (·.term) = args :=
    (conflictCache_terms Pi atts base.nodes).trans
      (base.nodes_terms.trans base.arguments_eq)
  have hmissing : firstMissingConflict? dp cache = none := by
    apply (firstMissingConflict_none_iff dp cache).mpr
    intro source hsourceCache target htargetCache hcontrary hattackable
    have hsourceMem : source.term ∈ args := by
      rw [← hterms]
      exact List.mem_map.mpr ⟨source, hsourceCache, rfl⟩
    have htargetMem : target.term ∈ args := by
      rw [← hterms]
      exact List.mem_map.mpr ⟨target, htargetCache, rfl⟩
    exact hattackComplete source.term hsourceMem target.term htargetMem
      source.conclusion target.conclusion source.valid target.valid
      hcontrary hattackable
  unfold checkProgramDetailed
  split
  · rename_i e herror
    rw [hbase] at herror
    contradiction
  · rename_i found hfound
    have hfound_eq : found = base :=
      Except.ok.inj (hfound.symm.trans hbase)
    subst found
    dsimp only
    split
    · rename_i missing hsome
      rw [hmissing] at hsome
      contradiction
    · exact ⟨_, rfl⟩

theorem checkProgram_accepted_source_declared {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    {program : Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp}
    (h : checkProgram Pi Gamma reg dp args atts = .ok program) :
    ∀ k ∈ atts, k.source ∈ args := by
  rcases checkProgram_sound h with ⟨_, _, _, _, _, hsource, _⟩
  exact hsource

theorem checkProgram_accepted_target_declared {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    {program : Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp}
    (h : checkProgram Pi Gamma reg dp args atts = .ok program) :
    ∀ k ∈ atts, k.target ∈ args := by
  rcases checkProgram_sound h with ⟨_, _, _, _, _, _, htarget⟩
  exact htarget

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
      HasSupport canon Pi Gamma (certOkOf reg) w C [] := by
  rcases checkProgram_sound h with ⟨_, _, _, hcomplete, _⟩
  exact hcomplete

end Lara.Check
