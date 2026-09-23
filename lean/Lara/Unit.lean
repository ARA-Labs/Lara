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
import Lara.Sigma

namespace Lara

open Support

/-! ### Σ against the policy (spec §3.4, rejection class R2)

`checkUnit`'s stage 2 splits in two. The half below is *static*: Σ itself, and
every pattern the policy declares, read under each rule's derived parameter
sorts. The other half is per-instance — θ's range terms — and lives with the
argument list, since θ is authored and not drawn from Γ.

Exception atoms are checked in their own rule's derived environment, so an
exception that mentions the rule's parameters is sorted the same way the
undercut licensing will instantiate it. An exception naming an unknown rule is
checked in the empty environment: its rule id is R1's business at the support
stage, and treating it as a scope failure here would turn one missing
declaration into a misleading R2. -/

/-- The derived parameter environment of the rule an exception names, or the
empty environment when it names none. -/
def exceptionEnv (sg : Sigma.Sigma) (P : Policy.Policy) (rn : Support.RuleId) :
    Sigma.ParamSorts :=
  match P.rules.find? (fun rd => decide (rd.id = rn)) with
  | some rd => (Sigma.ruleParamSorts sg rd.rule).getD []
  | none => []

/-- Σ against the policy: every rule's premises, conclusion, and answers under
its derived parameter sorts; every exception atom; and both sides of every
contrary pair under one shared environment (a contrary's variables are
universally quantified, but the two sides share them). -/
def policyWellSorted (sg : Sigma.Sigma) (P : Policy.Policy) : Bool :=
  P.rules.all (fun rd => (Sigma.ruleParamSorts sg rd.rule).isSome)
    && P.defeat.exceptions.all
        (fun e => (Sigma.checkAPat sg (exceptionEnv sg P e.1) e.2).isSome)
    && P.defeat.contraries.all
        (fun ab => (Sigma.checkAPats sg [] [ab.1, ab.2]).isSome)

/-- Σ against a θ: every range term is well-sorted, and at a key that is a
declared parameter with a derived sort it has exactly that sort.

A key *off* the parameter list is R3's business (domain totality), not this
stage's — the distinction is what keeps the `wrong-subst-domain` mutants R3. -/
def thetaWellSorted (sg : Sigma.Sigma) (r : Support.Rule) (env : Sigma.ParamSorts)
    (θ : Support.Subst) : Bool :=
  θ.all (fun b =>
    -- A key OFF the parameter list is skipped entirely, term and all: θ's
    -- domain is R3's business and this stage says nothing about it. Inspecting
    -- the term at such a key would make `wrong-subst-domain` mutants R2 instead
    -- of R3 and move the paper's per-class table -- the exact reclassification
    -- §2.3 rule 3 exists to prevent.
    if r.params.contains b.1 then
      match Sigma.sortOf sg b.2 with
      | none => false
      | some s' =>
          match Sigma.lookupParam env b.1 with
          | none => true
          | some s => decide (s' = s)
    else true)

/- Σ against the support terms: every rule instance whose rule id resolves has a
well-sorted θ. An unresolved rule id is left to R1 at the support stage — the
executable pin that a hidden rule stays an R1 failure and does not become a
stage-2 lookup error.

Mutually recursive over the three shapes `SupportTerm` nests through, as the
rest of this development is. -/
mutual
  def termWellSorted (sg : Sigma.Sigma) (P : Policy.Policy) :
      Support.SupportTerm → Bool
    | .leaf _ => true
    | .inst rn θ ws D _ _ =>
        (match P.ruleLookup rn with
         | none => true
         | some r =>
             match Sigma.ruleParamSorts sg r with
             | none => false
             | some env => thetaWellSorted sg r env θ)
          && termsWellSorted sg P ws
          && dischargesWellSorted sg P D

  def termsWellSorted (sg : Sigma.Sigma) (P : Policy.Policy) :
      List Support.SupportTerm → Bool
    | [] => true
    | w :: ws => termWellSorted sg P w && termsWellSorted sg P ws

  def dischargesWellSorted (sg : Sigma.Sigma) (P : Policy.Policy) :
      List (Support.QuestionId × Support.SupportTerm) → Bool
    | [] => true
    | d :: ds => termWellSorted sg P d.2 && dischargesWellSorted sg P ds
end

/-- Σ against the whole declared argument list. -/
def argsWellSorted (sg : Sigma.Sigma) (P : Policy.Policy)
    (args : List Support.SupportTerm) : Bool :=
  termsWellSorted sg P args

/-- The instantiated atoms contributed by one actual rule instance are
well-sorted: premises, conclusion, and critical-question answers. -/
def InstanceAtomsWellSorted (sg : Sigma.Sigma) (r : Support.Rule)
    (θ : Support.Subst) : Prop :=
  (∀ as, Support.instAPats θ r.premises = some as →
    ∀ a ∈ as, Sigma.WellSorted sg a) ∧
  (∀ c, Support.instAPat θ r.concl = some c → Sigma.WellSorted sg c) ∧
  (∀ q ∈ r.questions, ∀ a, Support.instAPat θ q.answer = some a →
    Sigma.WellSorted sg a)

/- Every rule instance recursively reachable through a support term contributes
only well-sorted instantiated atoms. The mutually recursive list predicates
follow the recursive support-term spine exactly. -/
mutual
  def AllInstancesWellSorted (sg : Sigma.Sigma)
      (Pi : Support.RuleId → Option Support.Rule) : Support.SupportTerm → Prop
    | .leaf _ => True
    | .inst rn θ ws D _ _ =>
        (∀ r, Pi rn = some r → InstanceAtomsWellSorted sg r θ) ∧
        AllInstancesWellSortedList sg Pi ws ∧
        AllInstancesWellSortedDischarges sg Pi D

  def AllInstancesWellSortedList (sg : Sigma.Sigma)
      (Pi : Support.RuleId → Option Support.Rule) :
      List Support.SupportTerm → Prop
    | [] => True
    | w :: ws =>
        AllInstancesWellSorted sg Pi w ∧
        AllInstancesWellSortedList sg Pi ws

  def AllInstancesWellSortedDischarges (sg : Sigma.Sigma)
      (Pi : Support.RuleId → Option Support.Rule) :
      List (Support.QuestionId × Support.SupportTerm) → Prop
    | [] => True
    | (_, w) :: rest =>
        AllInstancesWellSorted sg Pi w ∧
        AllInstancesWellSortedDischarges sg Pi rest
end

/-- Σ against the finite ground atoms the unit's environment contributes: the
leaf conclusions of Γ, the backend theory table, and the queried claim atoms.
They are passed to `checkUnit` explicitly rather than stored on `Unit`, because
`Unit` deliberately carries Γ as a *function* and the stage needs the finite
list the decode boundary already has. -/
def groundWellSorted (sg : Sigma.Sigma) (ground : List Atom) : Bool :=
  ground.all (Sigma.wsAtom sg)

/-- Neutral input at the whole-unit boundary. -/
structure Unit where
  /-- The declared many-sorted proposition signature (spec §2, §3.4). Carried by
  the `sigma` wire section from `lara-core@0.2` and enforced by `checkUnit`
  stage 2 as rejection class R2. -/
  sigma  : Sigma.Sigma
  policy : Policy.Policy
  args   : List Support.SupportTerm
  atts   : List Attack.Attack

namespace Unit

/-- A unit accepted against its own policy-derived rule lookup. -/
structure CheckedUnit
    (canon : String → String) (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop) where
  sigma : Sigma.Sigma
  policy : Policy.Policy
  ruleIds_nodup : (policy.rules.map (·.id)).Nodup
  /-- Σ is well-formed: no duplicate declaration, no declaration shadowing a
  base-sort name, no signature naming an undeclared sort. -/
  sigma_wf : Sigma.sigmaWellFormed sigma = true
  /-- Every pattern the policy declares is well-sorted under Σ extended with
  each rule's derived parameter sorts. -/
  policy_well_sorted : policyWellSorted sigma policy = true
  /-- Spec §4.1: every pattern variable is among its rule's declared
  parameters — R12's second arm, enforced for the first time at
  `lara-core@0.2`. -/
  scopes_wf : Policy.ScopesWellFormed policy
  policy_wf : Policy.WellFormed canon policy
  program :
    Compile.CheckedProgram canon policy.ruleLookup Gamma CertOk policy.defeat
  attack_complete :
    Compile.AttackComplete canon policy.ruleLookup Gamma CertOk
      policy.defeat program.args program.atts
  nodes :
    List (Compile.CheckedNode canon policy.ruleLookup Gamma CertOk)
  nodes_terms : nodes.map (·.term) = program.args
  /-- Every θ in the argument list is sort-respecting at the parameters its
  rule declares — the per-instance half of stage 2. Required, and not merely
  thorough: θ's range terms are *authored*, not drawn from Γ, and a rule
  instance's conclusion is θ-instantiated, so an ill-sorted range value would
  produce an ill-sorted argument conclusion no other stage sees. -/
  args_well_sorted : argsWellSorted sigma policy program.args = true

end Unit
end Lara
