import Lara.Process.Source
import Lara.Process.SourceCoordinates
import Lara.Process.Vocabulary

namespace Lara.Process.Source

structure ClaimBinding where
  claim : ClaimId
  declaration : Presentation.PropId
  query : Atom
  deriving DecidableEq

structure SupportBinding where
  argument : Presentation.ArgId
  query : Atom
  deriving DecidableEq

inductive SupportFault where
  | absent
  | inference : Check.CheckError → SupportFault
  | incomplete : List Support.QuestionId → SupportFault
  | differentConclusion
  | notRetained
  | absentNode
  | nodeMismatch
  | blocked
  deriving DecidableEq

structure ResolvedSupport {input : SourceInput} (observation : AcceptedObservation input)
    (binding : SupportBinding) where
  ref : BHL.SupportRef
  raw : BHL.RawSupport (sourceEnv input).registry observation.state ref
  name : ref.row.1 = binding.argument.val
  query : ref.query = binding.query
  retained : ref.row ∈ observation.run.admission.prune.keptArgs
  node : ∃ node, observation.run.checked.nodes[ref.checkedIndex]? = some node ∧
    node.term = ref.row.2 ∧ node.conclusion = ref.conclusion
  unblocked : ref.query ∉ Update.blockedQueriesForRun observation.run [ref.query]

/-- Infer against declared leaves independently of the admitted checked node.
The fresh checked coordinate must then name that same complete support. -/
def resolveSupport {input : SourceInput} (observation : AcceptedObservation input)
    (binding : SupportBinding) : Except SupportFault (ResolvedSupport observation binding) :=
  let rawIndex := observation.state.argsRaw.findIdx fun row => row.1 == binding.argument.val
  match occurrence : observation.state.argsRaw[rawIndex]? with
  | none => .error .absent
  | some row =>
    if name : row.1 = binding.argument.val then
      match inferred : Check.inferSupport observation.state.policy.ruleLookup
          (Admission.buildGamma observation.state.leaves) (sourceEnv input).registry .root row.2 with
      | .error error => .error (.inference error)
      | .ok result =>
        if complete : result.obligations = [] then
          if equivalent : equiv canonNum result.conclusion binding.query then
            if retained : row ∈ observation.run.admission.prune.keptArgs then
              let checkedIndex := (Coordinates.names observation.run).findIdx (· == binding.argument)
              match nodeAt : observation.run.checked.nodes[checkedIndex]? with
              | none => .error .absentNode
              | some node =>
                if exactNode : node.term = row.2 ∧ node.conclusion = result.conclusion then
                  if unblocked : binding.query ∉ Update.blockedQueriesForRun observation.run [binding.query] then
                    .ok
                      { ref := ⟨rawIndex, row, result.conclusion, binding.query, checkedIndex⟩
                        raw := ⟨occurrence, by
                          simpa only [complete] using Check.inferSupport_sound inferred, equivalent⟩
                        name := name
                        query := rfl
                        retained := retained
                        node := ⟨node, nodeAt, exactNode.1, exactNode.2⟩
                        unblocked := unblocked }
                  else .error .blocked
                else .error .nodeMismatch
            else .error .notRetained
          else .error .differentConclusion
        else .error (.incomplete result.obligations)
    else .error .absent

theorem ResolvedSupport.exact_raw {input : SourceInput}
    {observation : AcceptedObservation input} {binding : SupportBinding}
    (resolved : ResolvedSupport observation binding) :
    observation.state.argsRaw[resolved.ref.rawIndex]? = some resolved.ref.row ∧
      Support.HasSupport canonNum observation.state.policy.ruleLookup
        (Admission.buildGamma observation.state.leaves) (Support.certOkOf (sourceEnv input).registry)
        resolved.ref.row.2 resolved.ref.conclusion [] ∧
      equiv canonNum resolved.ref.conclusion binding.query :=
  ⟨resolved.raw.occurrence, resolved.raw.typed, resolved.query ▸ resolved.raw.equivalent⟩

theorem ResolvedSupport.warrant_of_label {input : SourceInput}
    {observation : AcceptedObservation input} {binding : SupportBinding}
    (resolved : ResolvedSupport observation binding)
    (label : Grounded.labelC (Compile.checkedAF observation.run.checked.program)
      resolved.ref.checkedIndex = .inn) :
    BHL.SupportWarrant observation.run resolved.ref := by
  obtain ⟨node, atNode, term, conclusion⟩ := resolved.node
  refine ⟨resolved.raw, resolved.retained, ?_, ⟨node, atNode, term, conclusion⟩,
    ?_, label, resolved.unblocked⟩
  · simpa only [term, conclusion] using node.valid
  · obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp atNode
    have length : observation.run.checked.nodes.length =
        observation.run.checked.program.args.length := by
      simpa using congrArg List.length observation.run.checked.nodes_terms
    apply List.mem_range.mpr
    rw [← length]
    exact bound

end Lara.Process.Source
