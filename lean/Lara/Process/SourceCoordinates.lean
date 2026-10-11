import Lara.BHL.LaraBridge
import Lara.Process.SourceGraph
import Mathlib.Data.List.Nodup

namespace Lara.Process.Source

open Lara.Support

namespace Coordinates

variable {canon : String → String} {registry : BackendRegistry canon}
  {state : Update.SourceState}

theorem partition (run : Update.AcceptedRun registry state) :
    Check.DeclPartition (run.admission.prune.keptArgs.map Prod.snd)
      run.checked.nodes run.checked.nodeDecls run.checked.holes :=
  (Check.Unit.checkUnit_sound run.check_ok).partition

theorem nodeDecl_bound (run : Update.AcceptedRun registry state) (declaration : Nat)
    (member : declaration ∈ run.checked.nodeDecls) :
    declaration < run.admission.prune.keptArgs.length := by
  have bound := ((partition run).cover declaration).mpr (Or.inl member)
  simpa using bound

/-- The checker-supplied declaration map selects a retained declaration. No
fallback name or stale checked index is used when an earlier declaration is pruned. -/
def row (run : Update.AcceptedRun registry state)
    (declaration : {n // n ∈ run.checked.nodeDecls}) : String × SupportTerm :=
  run.admission.prune.keptArgs[declaration.val]'(nodeDecl_bound run declaration.val declaration.property)

def rows (run : Update.AcceptedRun registry state) : List (String × SupportTerm) :=
  let retained := run.admission.prune.keptArgs.toArray
  run.checked.nodeDecls.attach.map fun declaration =>
    retained[declaration.val]'(by
      simpa [retained] using nodeDecl_bound run declaration.val declaration.property)

theorem rows_eq_reference (run : Update.AcceptedRun registry state) :
    rows run = run.checked.nodeDecls.attach.map (row run) := by
  simp [rows, row]

def names (run : Update.AcceptedRun registry state) : List Presentation.ArgId :=
  (rows run).map fun row => ⟨row.1⟩

theorem rows_length (run : Update.AcceptedRun registry state) :
    (rows run).length = run.checked.nodeDecls.length := by simp [rows]

theorem rows_terms (run : Update.AcceptedRun registry state) :
    (rows run).map Prod.snd = run.checked.program.args := by
  have source := (partition run).node_decls
  have wrapped : ((rows run).map Prod.snd).map some =
      run.checked.nodeDecls.map (fun i => (run.admission.prune.keptArgs.map Prod.snd)[i]?) := by
    simp only [rows_eq_reference, List.map_map]
    conv_rhs => rw [← List.attach_map_val]
    apply List.map_congr_left
    intro declaration member
    simp [row, List.getElem?_eq_getElem (nodeDecl_bound run declaration.val declaration.property)]
  rw [source] at wrapped
  have terms : (rows run).map Prod.snd = run.checked.nodes.map (·.term) := by
    apply (List.map_inj_right (fun _ _ h => Option.some.inj h)).mp
    simpa only [List.map_map, Function.comp_def] using wrapped
  exact terms.trans run.checked.nodes_terms

theorem names_length (run : Update.AcceptedRun registry state) :
    (names run).length = run.checked.program.args.length := by
  have length := congrArg List.length (rows_terms run)
  simpa [names] using length

theorem kept_names_nodup (run : Update.AcceptedRun registry state) :
    (run.admission.prune.keptArgs.map Prod.fst).Nodup := by
  have prune := Admission.accepted_prune_eq canon state.table state.metas state.leaves
    state.argsRaw state.rawAtts state.groups run.declared run.admission_ok
  rw [prune]
  exact run.declared.ids_nodup.sublist ((List.filter_sublist).map Prod.fst)

theorem names_nodup (run : Update.AcceptedRun registry state) :
    (names run).Nodup := by
  have distinct : run.checked.nodeDecls.Nodup :=
    (partition run).nodeDecls_sorted.imp (fun h => Nat.ne_of_lt h)
  unfold names
  rw [rows_eq_reference, List.map_map]
  apply List.Nodup.map_on _ distinct.attach
  intro i hi j hj equal
  apply Subtype.ext
  have nameEq : (run.admission.prune.keptArgs.map Prod.fst)[i.val]'(by
        simpa using nodeDecl_bound run i.val i.property) =
      (run.admission.prune.keptArgs.map Prod.fst)[j.val]'(by
        simpa using nodeDecl_bound run j.val j.property) := by
    simpa [row] using congrArg Presentation.ArgId.val equal
  exact (List.Nodup.getElem_inj_iff (kept_names_nodup run)).mp nameEq

/-- The out-of-carrier value is never an AF node; it does not name any
declaration. Every live node resolves through the checked declaration map. -/
def identity (run : Update.AcceptedRun registry state) (carrier : List Presentation.ArgId)
    (node : Nat) : Nat :=
  match (names run)[node]? with
  | some name => carrier.idxOf name
  | none => carrier.length

theorem identity_injective (run : Update.AcceptedRun registry state)
    (carrier : List Presentation.ArgId) (covers : ∀ name ∈ names run, name ∈ carrier)
    (a b : Nat) (ha : a ∈ (Compile.checkedAF run.checked.program).args)
    (hb : b ∈ (Compile.checkedAF run.checked.program).args)
    (equal : identity run carrier a = identity run carrier b) : a = b := by
  have ba : a < (names run).length := by
    rw [names_length]
    exact List.mem_range.mp ha
  have bb : b < (names run).length := by
    rw [names_length]
    exact List.mem_range.mp hb
  simp only [identity, List.getElem?_eq_getElem ba, List.getElem?_eq_getElem bb] at equal
  have nameEq := (List.idxOf_inj (covers _ (List.getElem_mem ba))).mp equal
  exact (List.Nodup.getElem_inj_iff (names_nodup run)).mp nameEq

def graph (run : Update.AcceptedRun registry state) (carrier : List Presentation.ArgId) :=
  let coordinates := ((names run).map carrier.idxOf).toArray
  liftGraph (Compile.checkedAF run.checked.program) fun node =>
    coordinates[node]?.getD carrier.length

theorem graph_eq_reference (run : Update.AcceptedRun registry state)
    (carrier : List Presentation.ArgId) :
    graph run carrier = liftGraph (Compile.checkedAF run.checked.program) (identity run carrier) := by
  unfold graph
  dsimp only
  congr 1
  funext node
  simp only [List.getElem?_toArray, List.getElem?_map, identity]
  cases (names run)[node]? <;> rfl

theorem graph_label (run : Update.AcceptedRun registry state)
    (carrier : List Presentation.ArgId) (covers : ∀ name ∈ names run, name ∈ carrier)
    {node : Nat} (member : node ∈ (Compile.checkedAF run.checked.program).args) :
    Grounded.labelC (graph run carrier) (identity run carrier node) =
      Grounded.labelC (Compile.checkedAF run.checked.program) node := by
  rw [graph_eq_reference]
  exact liftGraph_label _ _ (identity_injective run carrier covers) member

/-- Query support follows normalized checked conclusions, never a mutable
presentation claim label or a remembered compact node index. -/
def supports (run : Update.AcceptedRun registry state) (query : Atom) : List Presentation.ArgId :=
  let nodeNames := (names run).toArray
  (Consistency.claimSupportFor run.checked query).filterMap fun node => nodeNames[node]?

theorem supports_exact (run : Update.AcceptedRun registry state) (query : Atom)
    (name : Presentation.ArgId) :
    name ∈ supports run query ↔ ∃ (index : Nat), ∃ node,
      (names run)[index]? = some name ∧ run.checked.nodes[index]? = some node ∧
        equiv canon node.conclusion query := by
  simp only [supports, List.getElem?_toArray, List.mem_filterMap, Consistency.mem_claimSupportFor_iff]
  constructor
  · rintro ⟨index, ⟨node, checked, equivalent⟩, named⟩
    exact ⟨index, node, named, checked, equivalent⟩
  · rintro ⟨index, node, named, checked, equivalent⟩
    exact ⟨index, ⟨node, checked, equivalent⟩, named⟩

end Coordinates
end Lara.Process.Source
