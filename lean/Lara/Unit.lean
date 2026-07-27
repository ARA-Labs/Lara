/-
The proof-bearing public unit boundary.

A raw `Unit` is deliberately neutral data: one finite policy, one argument
list, and one attack list. `CheckedUnit` is the accepted-program abstraction.
`Lara.Check.Unit.checkUnit` is its canonical executable constructor; manual
proof-level construction remains possible only by supplying every structure
invariant. It retains the policy-derived lookup used to check the program,
unique rule identifiers, Path-B well-formedness, attack completeness, and the
exact checked-node cache produced by the executable checker. No support
re-inference is needed downstream.
-/

import Lara.Compile
import Lara.Policy

namespace Lara

open Support

/-- Neutral input at the whole-unit boundary. -/
structure Unit where
  policy : Policy.Policy
  args   : List Support.SupportTerm
  atts   : List Attack.Attack

namespace Unit

/-- A unit accepted against its own policy-derived rule lookup. -/
structure CheckedUnit
    (canon : String → String) (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop) where
  policy : Policy.Policy
  ruleIds_nodup : (policy.rules.map (·.id)).Nodup
  policy_wf : Policy.WellFormed canon policy
  program :
    Compile.CheckedProgram canon policy.ruleLookup Gamma CertOk policy.defeat
  attack_complete :
    Compile.AttackComplete canon policy.ruleLookup Gamma CertOk
      policy.defeat program.args program.atts
  nodes :
    List (Compile.CheckedNode canon policy.ruleLookup Gamma CertOk)
  nodes_terms : nodes.map (·.term) = program.args

end Unit
end Lara
