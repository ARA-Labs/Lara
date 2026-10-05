/-
Executable construction of proof-bearing checked programs.

The legacy `checkProgram` projection preserves its generic behavior and
attack-soundness-only `CheckedProgram` result. The detailed acceptance path
runs duplicate arguments, support, typed attacks, then missing-conflict
coverage, in that fixed order. Its argument pass retains the checked support
result for every source declaration; both typed-attack checking and the final
conflict scan derive their nodes from that cache and never re-infer support.
`ProgramAcceptance` carries the additional attack-completeness witness and
retained nodes needed by the public `checkUnit` boundary.

Since `lara-core@0.3` an open mandatory obligation is not a rejection (spec
§4.4). The support stage rejects only on an inference failure; the retained
cache is then partitioned once into complete nodes, which become the AF, and
located holes, which do not. Every raw attack is still typed against every
checked declaration; only attacks whose source is complete compile, and the
conflict scan runs over complete nodes alone. The specification views of that
partition (`completeArgs`, `holeArgs`, `liveAttacks`) and its exact shape
(`DeclPartition`) live in `Lara.Check.Holes`; the checker never evaluates the
views and instead proves that its cache-derived partition agrees with them.
-/

import Lara.Check.Holes
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
  | missingConflict : MissingConflict → ProgramError
deriving DecidableEq

/-- Only wrapped frozen checker failures have an R-class.  Structural
duplicates and missing conflicts are program-boundary outcomes. -/
def ProgramError.rejectClass : ProgramError → Option RejectClass
  | .rejection _ e => some e.rejectClass
  | .duplicateArgument _ _ => none
  | .missingConflict _ => none

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

/-! ### Checked argument cache and its partition -/

structure CheckedArguments {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (args : List SupportTerm) where
  cache : List (CheckedSupport canon Pi Gamma reg)
  aligned : cache.map (·.term) = args

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

/-- The node view of one cache entry, present exactly when it is complete. -/
def CheckedSupport.toNode? {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon}
    (entry : CheckedSupport canon Pi Gamma reg) :
    Option (Compile.CheckedNode canon Pi Gamma (certOkOf reg)) :=
  if h : entry.result.obligations = [] then some (entry.toCheckedNode h)
  else none

/-- Repackage an incomplete support-check result, at checked declaration
`index`, as a located hole. The conclusion and obligations are the cached
ones. -/
def CheckedSupport.toHole {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon}
    (entry : CheckedSupport canon Pi Gamma reg) (index : Nat)
    (hopen : entry.result.obligations ≠ []) :
    Compile.CheckedHole canon Pi Gamma (certOkOf reg) :=
  { index := index
  , term := entry.term
  , conclusion := entry.result.conclusion
  , obligations := entry.result.obligations
  , valid := entry.valid
  , nonempty := hopen }

/-- Checked declaration indices of the complete entries, from offset `i`. -/
def nodeDeclsFrom {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} :
    Nat → List (CheckedSupport canon Pi Gamma reg) → List Nat
  | _, [] => []
  | i, entry :: entries =>
      if entry.result.obligations = [] then i :: nodeDeclsFrom (i + 1) entries
      else nodeDeclsFrom (i + 1) entries

/-- The located holes among the entries, from offset `i`. -/
def holesFrom {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} :
    Nat → List (CheckedSupport canon Pi Gamma reg) →
      List (Compile.CheckedHole canon Pi Gamma (certOkOf reg))
  | _, [] => []
  | i, entry :: entries =>
      if h : entry.result.obligations = [] then holesFrom (i + 1) entries
      else entry.toHole i h :: holesFrom (i + 1) entries

/-- The retained AF node view, derived directly from the argument cache. No
support term is checked again and no conclusion is recomputed. Only complete
entries become nodes. -/
def CheckedArguments.nodes {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {args : List SupportTerm}
    (checked : CheckedArguments Pi Gamma reg args) :
    List (Compile.CheckedNode canon Pi Gamma (certOkOf reg)) :=
  checked.cache.filterMap (·.toNode?)

/-- The AF-to-checked-declaration map: entry `n` is the checked declaration
index of AF node `n`. -/
def CheckedArguments.nodeDecls {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {args : List SupportTerm}
    (checked : CheckedArguments Pi Gamma reg args) : List Nat :=
  nodeDeclsFrom 0 checked.cache

/-- The located holes, in checked declaration order, with their cached
conclusions and obligations. -/
def CheckedArguments.holes {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {args : List SupportTerm}
    (checked : CheckedArguments Pi Gamma reg args) :
    List (Compile.CheckedHole canon Pi Gamma (certOkOf reg)) :=
  holesFrom 0 checked.cache

section CachePartition

variable {canon : String → String} {Pi : RuleId → Option Rule}
  {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}

private theorem filterMap_toNode?_terms :
    ∀ (cache : List (CheckedSupport canon Pi Gamma reg)),
      (cache.filterMap (·.toNode?)).map (·.term) =
        (cache.map (·.term)).filter (argComplete Pi Gamma reg)
  | [] => rfl
  | e :: es => by
      have ih := filterMap_toNode?_terms es
      have hac := argComplete_of_hasSupport (reg := reg) e.valid
      by_cases hob : e.result.obligations = []
      · have hnode : e.toNode? = some (e.toCheckedNode hob) := by
          simp [CheckedSupport.toNode?, hob]
        simp only [List.filterMap_cons, hnode, List.map_cons, List.filter_cons,
          hac, hob, List.isEmpty_nil, if_true, ih]
        rfl
      · have hnode : e.toNode? = none := by
          simp [CheckedSupport.toNode?, hob]
        have hfalse : e.result.obligations.isEmpty = false := by
          cases h : e.result.obligations with
          | nil => exact absurd h hob
          | cons _ _ => rfl
        simp only [List.filterMap_cons, hnode, List.map_cons, List.filter_cons,
          hac, hfalse, ih]
        rfl

private theorem holesFrom_terms :
    ∀ (i : Nat) (cache : List (CheckedSupport canon Pi Gamma reg)),
      (holesFrom i cache).map (·.term) =
        (cache.map (·.term)).filter (argHole Pi Gamma reg)
  | _, [] => rfl
  | i, e :: es => by
      have ih := holesFrom_terms (i + 1) es
      have hah := argHole_of_hasSupport (reg := reg) e.valid
      by_cases hob : e.result.obligations = []
      · simp only [holesFrom, hob, dif_pos, List.map_cons, List.filter_cons,
          hah, List.isEmpty_nil, Bool.not_true, ih]
        rfl
      · have htrue : (!e.result.obligations.isEmpty) = true := by
          cases h : e.result.obligations with
          | nil => exact absurd h hob
          | cons _ _ => rfl
        simp only [holesFrom, hob, dif_neg, not_false_eq_true, List.map_cons,
          List.filter_cons, hah, htrue, if_true, ih]
        rfl

private theorem nodeDeclsFrom_ge :
    ∀ (i : Nat) (cache : List (CheckedSupport canon Pi Gamma reg)) (j : Nat),
      j ∈ nodeDeclsFrom i cache → i ≤ j
  | _, [], _, h => by simp [nodeDeclsFrom] at h
  | i, e :: es, j, h => by
      unfold nodeDeclsFrom at h
      split at h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Nat.le_refl _
        · have := nodeDeclsFrom_ge (i + 1) es j h
          omega
      · have := nodeDeclsFrom_ge (i + 1) es j h
        omega

private theorem holesFrom_ge :
    ∀ (i : Nat) (cache : List (CheckedSupport canon Pi Gamma reg)),
      ∀ h ∈ holesFrom i cache, i ≤ h.index
  | _, [], _, hh => by simp [holesFrom] at hh
  | i, e :: es, h, hh => by
      unfold holesFrom at hh
      split at hh
      · have := holesFrom_ge (i + 1) es h hh
        omega
      · rcases List.mem_cons.mp hh with rfl | hh
        · exact Nat.le_refl _
        · have := holesFrom_ge (i + 1) es h hh
          omega

private theorem nodeDeclsFrom_sorted :
    ∀ (i : Nat) (cache : List (CheckedSupport canon Pi Gamma reg)),
      (nodeDeclsFrom i cache).Pairwise (· < ·)
  | _, [] => by simp [nodeDeclsFrom]
  | i, e :: es => by
      unfold nodeDeclsFrom
      split
      · refine List.pairwise_cons.mpr ⟨fun j hj => ?_, nodeDeclsFrom_sorted _ es⟩
        have := nodeDeclsFrom_ge (i + 1) es j hj
        omega
      · exact nodeDeclsFrom_sorted _ es

private theorem holesFrom_sorted :
    ∀ (i : Nat) (cache : List (CheckedSupport canon Pi Gamma reg)),
      ((holesFrom i cache).map (·.index)).Pairwise (· < ·)
  | _, [] => by simp [holesFrom]
  | i, e :: es => by
      unfold holesFrom
      split
      · exact holesFrom_sorted _ es
      · rw [List.map_cons]
        refine List.pairwise_cons.mpr ⟨fun j hj => ?_, holesFrom_sorted _ es⟩
        obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hj
        have := holesFrom_ge (i + 1) es h hh
        simp only [CheckedSupport.toHole]
        omega

private theorem partition_cover :
    ∀ (i : Nat) (cache : List (CheckedSupport canon Pi Gamma reg)) (j : Nat),
      (j ∈ nodeDeclsFrom i cache ∨ ∃ h ∈ holesFrom i cache, h.index = j) ↔
        i ≤ j ∧ j < i + cache.length
  | i, [], j => by simp [nodeDeclsFrom, holesFrom]
  | i, e :: es, j => by
      have ih := partition_cover (i + 1) es j
      simp only [List.length_cons]
      by_cases hob : e.result.obligations = []
      · simp only [nodeDeclsFrom, holesFrom, hob, if_true, dif_pos,
          List.mem_cons]
        constructor
        · rintro ((rfl | hj) | hh)
          · omega
          · have := ih.mp (Or.inl hj); omega
          · have := ih.mp (Or.inr hh); omega
        · intro hj
          by_cases hji : j = i
          · exact Or.inl (Or.inl hji)
          · rcases ih.mpr (by omega) with hj | hh
            · exact Or.inl (Or.inr hj)
            · exact Or.inr hh
      · simp only [nodeDeclsFrom, holesFrom, hob, if_false, dif_neg,
          not_false_eq_true, List.mem_cons, exists_eq_or_imp]
        constructor
        · rintro (hj | (hidx | hh))
          · have := ih.mp (Or.inl hj); omega
          · simp only [CheckedSupport.toHole] at hidx; omega
          · have := ih.mp (Or.inr hh); omega
        · intro hj
          by_cases hji : j = i
          · exact Or.inr (Or.inl (by simp [CheckedSupport.toHole, hji]))
          · rcases ih.mpr (by omega) with hj | hh
            · exact Or.inl hj
            · exact Or.inr (Or.inr hh)

private theorem partition_disjoint :
    ∀ (i : Nat) (cache : List (CheckedSupport canon Pi Gamma reg)),
      ∀ j ∈ nodeDeclsFrom i cache, ¬ ∃ h ∈ holesFrom i cache, h.index = j
  | _, [], j, hj => by simp [nodeDeclsFrom] at hj
  | i, e :: es, j, hj => by
      by_cases hob : e.result.obligations = []
      · simp only [nodeDeclsFrom, hob, if_true, List.mem_cons] at hj
        simp only [holesFrom, hob, dif_pos]
        rcases hj with rfl | hj
        · rintro ⟨h, hh, hidx⟩
          have := holesFrom_ge (j + 1) es h hh
          omega
        · exact partition_disjoint (i + 1) es j hj
      · simp only [nodeDeclsFrom, hob, if_false] at hj
        simp only [holesFrom, hob, dif_neg, not_false_eq_true, List.mem_cons,
          exists_eq_or_imp, not_or]
        refine ⟨?_, partition_disjoint (i + 1) es j hj⟩
        have := nodeDeclsFrom_ge (i + 1) es j hj
        simp only [CheckedSupport.toHole]
        omega

private theorem nodeDeclsFrom_lookup :
    ∀ (i : Nat) (cache : List (CheckedSupport canon Pi Gamma reg))
      (pre : List SupportTerm), pre.length = i →
      (nodeDeclsFrom i cache).map (fun j => (pre ++ cache.map (·.term))[j]?) =
        (cache.filterMap (·.toNode?)).map (some ·.term)
  | _, [], _, _ => by simp [nodeDeclsFrom]
  | i, e :: es, pre, hpre => by
      have ih := nodeDeclsFrom_lookup (i + 1) es (pre ++ [e.term])
        (by simp [hpre])
      have hsplit : pre ++ (e :: es).map (·.term) =
          (pre ++ [e.term]) ++ es.map (·.term) := by simp
      rw [hsplit]
      by_cases hob : e.result.obligations = []
      · have hnode : e.toNode? = some (e.toCheckedNode hob) := by
          simp [CheckedSupport.toNode?, hob]
        simp only [nodeDeclsFrom, hob, if_true, List.map_cons,
          List.filterMap_cons, hnode, ih]
        congr 1
        rw [List.getElem?_append_left (by simp [hpre]),
          List.getElem?_append_right (by omega)]
        simp [hpre, CheckedSupport.toCheckedNode]
      · have hnode : e.toNode? = none := by
          simp [CheckedSupport.toNode?, hob]
        simp only [nodeDeclsFrom, hob, if_false, List.filterMap_cons, hnode,
          ih]

private theorem holesFrom_lookup :
    ∀ (i : Nat) (cache : List (CheckedSupport canon Pi Gamma reg))
      (pre : List SupportTerm), pre.length = i →
      ∀ h ∈ holesFrom i cache,
        (pre ++ cache.map (·.term))[h.index]? = some h.term
  | _, [], _, _, h, hh => by simp [holesFrom] at hh
  | i, e :: es, pre, hpre, h, hh => by
      have ih := holesFrom_lookup (i + 1) es (pre ++ [e.term])
        (by simp [hpre])
      have hsplit : pre ++ (e :: es).map (·.term) =
          (pre ++ [e.term]) ++ es.map (·.term) := by simp
      rw [hsplit]
      unfold holesFrom at hh
      split at hh
      · exact ih h hh
      · rcases List.mem_cons.mp hh with rfl | hh
        · rw [List.getElem?_append_left (by simp [hpre, CheckedSupport.toHole]),
            List.getElem?_append_right (by simp [hpre, CheckedSupport.toHole])]
          simp [hpre, CheckedSupport.toHole]
        · exact ih h hh

/-- The cache-derived node view is exactly the complete arguments, in
declaration order. -/
theorem CheckedArguments.nodes_terms {args : List SupportTerm}
    (checked : CheckedArguments Pi Gamma reg args) :
    checked.nodes.map (·.term) = completeArgs Pi Gamma reg args := by
  have h := filterMap_toNode?_terms checked.cache
  rw [checked.aligned] at h
  exact h

/-- The cache-derived hole view is exactly the holes, in declaration order. -/
theorem CheckedArguments.holes_terms {args : List SupportTerm}
    (checked : CheckedArguments Pi Gamma reg args) :
    checked.holes.map (·.term) = holeArgs Pi Gamma reg args := by
  have h := holesFrom_terms 0 checked.cache
  rw [checked.aligned] at h
  exact h

/-- **The cache partition.** Nodes, holes and the AF-to-declaration map
derived from the cache partition the checked declarations exactly. -/
theorem CheckedArguments.partition {args : List SupportTerm}
    (checked : CheckedArguments Pi Gamma reg args) :
    DeclPartition args checked.nodes checked.nodeDecls checked.holes := by
  have hlen : checked.cache.length = args.length := by
    simpa using congrArg List.length checked.aligned
  refine
    { node_decls := ?_
    , hole_decls := ?_
    , cover := ?_
    , disjoint := partition_disjoint 0 checked.cache
    , nodeDecls_sorted := nodeDeclsFrom_sorted 0 checked.cache
    , holes_sorted := holesFrom_sorted 0 checked.cache }
  · have h := nodeDeclsFrom_lookup 0 checked.cache [] rfl
    simpa [CheckedArguments.nodeDecls, CheckedArguments.nodes,
      checked.aligned] using h
  · intro h hh
    have := holesFrom_lookup 0 checked.cache [] rfl h hh
    simpa [checked.aligned] using this
  · intro i
    show i < args.length ↔ i ∈ nodeDeclsFrom 0 checked.cache ∨
      ∃ h ∈ holesFrom 0 checked.cache, h.index = i
    rw [partition_cover 0 checked.cache i, hlen]
    omega

/-- Every cached declaration type-checks; holes included. -/
theorem CheckedArguments.typed {args : List SupportTerm}
    (checked : CheckedArguments Pi Gamma reg args) :
    ∀ w ∈ args, ∃ C O, HasSupport canon Pi Gamma (certOkOf reg) w C O := by
  intro w hw
  rw [← checked.aligned] at hw
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hw
  exact ⟨_, _, entry.valid⟩

end CachePartition

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

/-- The cache records each node's own conclusion: the `(term, conclusion)`
projection of the scan cache is that of the checked nodes. With
`conflictCache_terms` this is what lets `Lara.Context` prove that the
conclusions its saturation infers *before* checking are the ones this cache
reads off *after* acceptance (`Lara.Context.conclusionCache_eq_conflictCache`). -/
theorem conflictCache_conclusions
    {canon : String → String} (Pi : RuleId → Option Rule)
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (atts : List Attack)
    (nodes : List (Compile.CheckedNode canon Pi Gamma CertOk)) :
    (conflictCache Pi atts nodes).map (fun n => (n.term, n.conclusion))
      = nodes.map (fun n => (n.term, n.conclusion)) := by
  have hzip : ∀ n, (nodes.zipIdx n).map (fun entry => (entry.1.term, entry.1.conclusion)) =
      nodes.map (fun n => (n.term, n.conclusion)) := by
    intro n
    induction nodes generalizing n with
    | nil => rfl
    | cons node rest ih =>
      simp only [List.zipIdx_cons, List.map_cons]
      exact congrArg ((node.term, node.conclusion) :: ·) (ih (n + 1))
  unfold conflictCache
  rw [List.map_map]
  change (nodes.zipIdx.map (fun entry => (entry.1.term, entry.1.conclusion))) =
    nodes.map (fun n => (n.term, n.conclusion))
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

/-- The support stage. It rejects only on an inference failure; an entry with
a nonempty obligation set is retained and later classified as a hole. -/
private def checkArguments {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) :
    (i : Nat) → (args : List SupportTerm) →
      Except ProgramError (CheckedArguments Pi Gamma reg args)
  | _, [] => .ok ⟨[], rfl⟩
  | i, w :: ws =>
      match hresult : inferSupport Pi Gamma reg .root w with
      | .error e => .error (.rejection (.argument i) e)
      | .ok result =>
          match checkArguments Pi Gamma reg (i + 1) ws with
          | .error e => .error e
          | .ok rest =>
              let entry : CheckedSupport canon Pi Gamma reg :=
                ⟨w, result, inferSupport_sound hresult⟩
              .ok
                { cache := entry :: rest.cache
                , aligned := by simp [entry, rest.aligned] }

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
  arguments_eq : program.args = completeArgs Pi Gamma reg args
  holes_eq : program.holes = holeArgs Pi Gamma reg args
  attacks_eq : program.atts = liveAttacks program.args atts
  nodes : List (Compile.CheckedNode canon Pi Gamma (certOkOf reg))
  nodes_terms : nodes.map (·.term) = program.args
  nodeDecls : List Nat
  holes : List (Compile.CheckedHole canon Pi Gamma (certOkOf reg))
  holes_terms : holes.map (·.term) = program.holes
  partition : DeclPartition args nodes nodeDecls holes
  raw_nodup : args.Nodup
  raw_support :
    ∀ w ∈ args, ∃ C O, HasSupport canon Pi Gamma (certOkOf reg) w C O
  raw_attacks : CheckedAttacks Pi Gamma reg dp args atts

/-- The shared prefix of the legacy and detailed checkers. It retains the
checked argument cache through typed-attack validation, and partitions it once
into complete nodes and located holes. Every raw attack is typed against every
checked declaration before attacks sourced at holes are dropped. -/
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
              let live := checkedArgs.nodes.map (·.term)
              have hlive : live = completeArgs Pi Gamma reg args :=
                checkedArgs.nodes_terms
              have hnodup : args.Nodup :=
                (firstDuplicate_none_iff args).mp hduplicate
              let program :
                  Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp :=
                { args := live
                , nodup := by
                    rw [hlive]
                    exact hnodup.sublist (completeArgs_sublist args)
                , complete := by
                    intro w hw
                    obtain ⟨node, _, rfl⟩ := List.mem_map.mp hw
                    exact ⟨node.conclusion, node.valid⟩
                , atts := liveAttacks live atts
                , typed := fun k hk =>
                    checkedAttacks.typed k (mem_liveAttacks_iff.mp hk).1
                , source_declared := fun k hk =>
                    (mem_liveAttacks_iff.mp hk).2
                , holes := checkedArgs.holes.map (·.term)
                , target_declared := by
                    intro k hk
                    have hmem : k.target ∈ args :=
                      checkedAttacks.target_declared k
                        (mem_liveAttacks_iff.mp hk).1
                    rw [hlive, checkedArgs.holes_terms]
                    exact mem_completeArgs_or_holeArgs hmem
                      (checkedArgs.typed k.target hmem) }
              .ok
                { program := program
                , arguments_eq := hlive
                , holes_eq := checkedArgs.holes_terms
                , attacks_eq := rfl
                , nodes := checkedArgs.nodes
                , nodes_terms := rfl
                , nodeDecls := checkedArgs.nodeDecls
                , holes := checkedArgs.holes
                , holes_terms := rfl
                , partition := checkedArgs.partition
                , raw_nodup := hnodup
                , raw_support := checkedArgs.typed
                , raw_attacks := checkedAttacks }

/-- Legacy projection of the shared checker prefix. Its signature is
unchanged. Since `lara-core@0.3` it accepts programs with located holes, which
up to `lara-core@0.2` it rejected as `incompleteArgument`. -/
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
projection, it retains executable checked nodes, the located holes and their
partition of the declarations, the raw facts the checker established, and the
independently proved conflict-completeness postcondition. -/
structure ProgramAcceptance {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (dp : DefeatPolicy)
    (args : List SupportTerm) (atts : List Attack) where
  program : Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp
  attack_complete :
    Compile.AttackComplete canon Pi Gamma (certOkOf reg) dp
      program.args program.atts
  arguments_eq : program.args = completeArgs Pi Gamma reg args
  holes_eq : program.holes = holeArgs Pi Gamma reg args
  attacks_eq : program.atts = liveAttacks program.args atts
  nodes : List (Compile.CheckedNode canon Pi Gamma (certOkOf reg))
  nodes_terms : nodes.map (·.term) = program.args
  nodeDecls : List Nat
  holes : List (Compile.CheckedHole canon Pi Gamma (certOkOf reg))
  holes_terms : holes.map (·.term) = program.holes
  partition : DeclPartition args nodes nodeDecls holes
  raw_nodup : args.Nodup
  raw_support :
    ∀ w ∈ args, ∃ C O, HasSupport canon Pi Gamma (certOkOf reg) w C O
  raw_typed : ∀ k ∈ atts, HasAttack canon Pi Gamma (certOkOf reg) dp k
  raw_source : ∀ k ∈ atts, k.source ∈ args
  raw_target : ∀ k ∈ atts, k.target ∈ args

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
uncovered attackable contrary pair between complete nodes. -/
def checkProgramDetailed {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (dp : DefeatPolicy)
    (args : List SupportTerm) (atts : List Attack) :
    Except ProgramError (ProgramAcceptance Pi Gamma reg dp args atts) :=
  match checkProgramBase Pi Gamma reg dp args atts with
  | .error e => .error e
  | .ok base =>
      let cache := conflictCache Pi base.program.atts base.nodes
      match hmissing : firstMissingConflict? dp cache with
      | some missing => .error (.missingConflict missing)
      | none =>
          .ok
            { program := base.program
            , attack_complete :=
                attackComplete_of_firstMissingConflict_none cache
                  ((conflictCache_terms Pi base.program.atts base.nodes).trans
                    base.nodes_terms)
                  hmissing
            , arguments_eq := base.arguments_eq
            , holes_eq := base.holes_eq
            , attacks_eq := base.attacks_eq
            , nodes := base.nodes
            , nodes_terms := base.nodes_terms
            , nodeDecls := base.nodeDecls
            , holes := base.holes
            , holes_terms := base.holes_terms
            , partition := base.partition
            , raw_nodup := base.raw_nodup
            , raw_support := base.raw_support
            , raw_typed := base.raw_attacks.typed
            , raw_source := base.raw_attacks.source_declared
            , raw_target := base.raw_attacks.target_declared }

private theorem checkArguments_complete {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) :
    ∀ (i : Nat) (args : List SupportTerm),
      (∀ w ∈ args, ∃ C O,
        HasSupport canon Pi Gamma (certOkOf reg) w C O) →
      ∃ checked, checkArguments Pi Gamma reg i args = .ok checked := by
  intro i args
  induction args generalizing i with
  | nil =>
      intro _
      exact ⟨⟨[], rfl⟩, rfl⟩
  | cons w ws ih =>
      intro htyped
      obtain ⟨C, O, hw⟩ := htyped w (by simp)
      have hinfer := inferSupport_complete hw .root
      obtain ⟨rest, hrest⟩ := ih (i + 1) (by
        intro x hx
        exact htyped x (by simp [hx]))
      simp only [checkArguments]
      split
      · rename_i e herror
        rw [hinfer] at herror
        contradiction
      · split
        · rename_i e herror
          rw [hrest] at herror
          contradiction
        · exact ⟨_, rfl⟩

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
    (hsupport : ∀ w ∈ args, ∃ C O,
      HasSupport canon Pi Gamma (certOkOf reg) w C O)
    (htyped : ∀ k ∈ atts,
      HasAttack canon Pi Gamma (certOkOf reg) dp k)
    (hsource : ∀ k ∈ atts, k.source ∈ args)
    (htarget : ∀ k ∈ atts, k.target ∈ args) :
    ∃ base, checkProgramBase Pi Gamma reg dp args atts = .ok base := by
  have hduplicate : firstDuplicate args = none :=
    (firstDuplicate_none_iff args).mpr hnodup
  obtain ⟨checkedArgs, hargs⟩ :=
    checkArguments_complete Pi Gamma reg 0 args hsupport
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

/-- Every successful result exposes all compile-boundary invariants: the AF
arguments are the complete declarations, the holes are the typed incomplete
ones, the AF attacks are those with a complete source, and every raw
declaration and raw attack is checked. -/
theorem checkProgram_sound {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    {program : Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp}
    (h : checkProgram Pi Gamma reg dp args atts = .ok program) :
    program.args = completeArgs Pi Gamma reg args ∧
      program.holes = holeArgs Pi Gamma reg args ∧
      program.atts = liveAttacks program.args atts ∧
      args.Nodup ∧
      (∀ w ∈ args, ∃ C O,
        HasSupport canon Pi Gamma (certOkOf reg) w C O) ∧
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
    exact ⟨base.arguments_eq, base.holes_eq, base.attacks_eq, base.raw_nodup,
      base.raw_support, base.raw_attacks.typed,
      base.raw_attacks.source_declared, base.raw_attacks.target_declared⟩

/-- Exact completeness of the legacy projection with located holes: every raw
declaration list whose arguments all type, complete or not, and whose attacks
all type with declared endpoints, produces a checked program. -/
theorem checkProgram_complete_holes {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    (hnodup : args.Nodup)
    (hsupport : ∀ w ∈ args, ∃ C O,
      HasSupport canon Pi Gamma (certOkOf reg) w C O)
    (htyped : ∀ k ∈ atts,
      HasAttack canon Pi Gamma (certOkOf reg) dp k)
    (hsource : ∀ k ∈ atts, k.source ∈ args)
    (htarget : ∀ k ∈ atts, k.target ∈ args) :
    ∃ program, checkProgram Pi Gamma reg dp args atts = .ok program := by
  obtain ⟨base, hbase⟩ :=
    checkProgramBase_complete hnodup hsupport htyped hsource htarget
  exact ⟨base.program, by simp [checkProgram, hbase]⟩

/-- The all-complete corollary of `checkProgram_complete_holes`. -/
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
    ∃ program, checkProgram Pi Gamma reg dp args atts = .ok program :=
  checkProgram_complete_holes hnodup
    (fun w hw => let ⟨C, hC⟩ := hcomplete w hw; ⟨C, [], hC⟩)
    htyped hsource htarget

/-- A successful detailed result exposes its named semantic and executable
postconditions without recovering anything from the legacy projection. -/
theorem checkProgramDetailed_sound {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    {accepted : ProgramAcceptance Pi Gamma reg dp args atts}
    (_h : checkProgramDetailed Pi Gamma reg dp args atts = .ok accepted) :
    accepted.program.args = completeArgs Pi Gamma reg args ∧
    accepted.program.holes = holeArgs Pi Gamma reg args ∧
    accepted.program.atts = liveAttacks accepted.program.args atts ∧
    Compile.AttackComplete canon Pi Gamma (certOkOf reg) dp
      accepted.program.args accepted.program.atts ∧
    accepted.nodes.map (·.term) = accepted.program.args ∧
    DeclPartition args accepted.nodes accepted.nodeDecls accepted.holes :=
  ⟨accepted.arguments_eq, accepted.holes_eq, accepted.attacks_eq,
    accepted.attack_complete, accepted.nodes_terms, accepted.partition⟩

/-- Exact completeness of the detailed checker with located holes. Every
argument must type, complete or not; attack completeness is required only
between complete arguments, which is all `AttackComplete` ever asks for. -/
theorem checkProgramDetailed_complete_holes {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    (hnodup : args.Nodup)
    (hsupport : ∀ w ∈ args, ∃ C O,
      HasSupport canon Pi Gamma (certOkOf reg) w C O)
    (htyped : ∀ k ∈ atts,
      HasAttack canon Pi Gamma (certOkOf reg) dp k)
    (hsource : ∀ k ∈ atts, k.source ∈ args)
    (htarget : ∀ k ∈ atts, k.target ∈ args)
    (hattackComplete :
      Compile.AttackComplete canon Pi Gamma (certOkOf reg) dp args atts) :
    ∃ accepted,
      checkProgramDetailed Pi Gamma reg dp args atts = .ok accepted := by
  obtain ⟨base, hbase⟩ :=
    checkProgramBase_complete hnodup hsupport htyped hsource htarget
  have hcomplete :
      Compile.AttackComplete canon Pi Gamma (certOkOf reg) dp
        base.program.args base.program.atts := by
    rw [base.attacks_eq, attackComplete_iff_complete_live, base.arguments_eq,
      attackComplete_completeArgs_iff]
    exact hattackComplete
  let cache := conflictCache Pi base.program.atts base.nodes
  have hterms : cache.map (·.term) = base.program.args :=
    (conflictCache_terms Pi base.program.atts base.nodes).trans
      base.nodes_terms
  have hmissing : firstMissingConflict? dp cache = none := by
    apply (firstMissingConflict_none_iff dp cache).mpr
    intro source hsourceCache target htargetCache hcontrary hattackable
    have hsourceMem : source.term ∈ base.program.args := by
      rw [← hterms]
      exact List.mem_map.mpr ⟨source, hsourceCache, rfl⟩
    have htargetMem : target.term ∈ base.program.args := by
      rw [← hterms]
      exact List.mem_map.mpr ⟨target, htargetCache, rfl⟩
    exact hcomplete source.term hsourceMem target.term htargetMem
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

/-- The all-complete corollary of `checkProgramDetailed_complete_holes`. -/
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
      checkProgramDetailed Pi Gamma reg dp args atts = .ok accepted :=
  checkProgramDetailed_complete_holes hnodup
    (fun w hw => let ⟨C, hC⟩ := hcomplete w hw; ⟨C, [], hC⟩)
    htyped hsource htarget hattackComplete

theorem checkProgram_accepted_source_declared {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    {program : Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp}
    (h : checkProgram Pi Gamma reg dp args atts = .ok program) :
    ∀ k ∈ atts, k.source ∈ args := by
  rcases checkProgram_sound h with ⟨_, _, _, _, _, _, hsource, _⟩
  exact hsource

theorem checkProgram_accepted_target_declared {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    {program : Compile.CheckedProgram canon Pi Gamma (certOkOf reg) dp}
    (h : checkProgram Pi Gamma reg dp args atts = .ok program) :
    ∀ k ∈ atts, k.target ∈ args := by
  rcases checkProgram_sound h with ⟨_, _, _, _, _, _, _, htarget⟩
  exact htarget

end Lara.Check
