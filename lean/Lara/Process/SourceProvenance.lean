import Lara.Process.Source
import Lara.Process.SourceKinds
import Lara.Process.SourceCoordinates

namespace Lara.Process.Source.Provenance

inductive Error where
  | shape
  | missingRule : Presentation.RuleId → Error
  | unresolvedReference : Presentation.ArgRef → Error
  | implicitMatch
  | missingArgument : Presentation.ArgId → Error
  | duplicateArgument : Presentation.ArgId → Error
  | missingNode : Nat → Error
  deriving DecidableEq

/-- A source occurrence and the exact presentation term retained for it. -/
inductive Reference where
  | named : Presentation.ArgRef → Presentation.SupportTerm → Reference
  | implicit : Atom → Presentation.SupportTerm → Reference

structure Candidate where
  term : Presentation.SupportTerm
  argument : Option Presentation.ArgId
  deriving DecidableEq

/-- Tags preserve the distinction which inlining erases. Duplicates are not
collapsed: production omitted-premise inference requires exactly one match. -/
def candidates (canon : String → String) (program : Presentation.Program)
    (priors : List Surface.PriorArgument) (ground : Atom) : List Candidate :=
  (Surface.declaredLeaves program).filterMap (fun entry =>
    if equiv canon entry.2 ground then some ⟨.leaf entry.1, none⟩ else none) ++
  priors.filterMap (fun prior =>
    if equiv canon prior.conclusion ground then some ⟨prior.term, some prior.id⟩ else none)

theorem candidates_terms (canon : String → String) (program : Presentation.Program)
    (priors : List Surface.PriorArgument) (ground : Atom) :
    (candidates canon program priors ground).map Candidate.term =
      Surface.premiseMatches canon program priors ground := by
  simp only [candidates, Surface.premiseMatches, List.map_append, List.map_filterMap]
  congr 1 <;> apply List.filterMap_congr <;> intro x hx <;> split <;> rfl

/-- Independent reference semantics: named references use the existing
source calculus; omitted premises require a unique leaf-or-prior match. -/
inductive Resolves (canon : String → String) (program : Presentation.Program)
    (priors : List Surface.PriorArgument) : Reference → Option Presentation.ArgId → Prop where
  | named {reference retained resolved}
      (source : Surface.ChecksReference program priors reference resolved)
      (retained_eq : resolved.term = retained) :
      Resolves canon program priors (.named reference retained) resolved.argumentSource
  | implicit {ground retained candidate}
      (unique : candidates canon program priors ground = [candidate])
      (retained_eq : candidate.term = retained) :
      Resolves canon program priors (.implicit ground retained) candidate.argument

def RefersTo (canon : String → String) (program : Presentation.Program)
    (priors : List Surface.PriorArgument) (reference : Reference)
    (argument : Presentation.ArgId) : Prop :=
  Resolves canon program priors reference (some argument)

def resolve (canon : String → String) (program : Presentation.Program)
    (priors : List Surface.PriorArgument) (reference : Reference) :
    Except Error {argument // Resolves canon program priors reference argument} :=
  match reference with
  | .named name retained =>
    match h : Surface.resolveReference program priors name with
    | none => .error (.unresolvedReference name)
    | some resolved =>
      if eq : resolved.term = retained then
        .ok ⟨resolved.argumentSource, .named (Surface.resolveReference_sound h) eq⟩
      else .error .shape
  | .implicit ground retained =>
    match h : candidates canon program priors ground with
    | [candidate] =>
      if eq : candidate.term = retained then .ok ⟨candidate.argument, .implicit h eq⟩
      else .error .shape
    | _ => .error .implicitMatch

theorem resolves_unique {canon program priors reference a b}
    (ha : Resolves canon program priors reference a)
    (hb : Resolves canon program priors reference b) : a = b := by
  cases ha with
  | named source retained_eq =>
    cases hb with
    | named other _ =>
      have eq := (Surface.resolveReference_complete source).symm.trans
        (Surface.resolveReference_complete other)
      cases Option.some.inj eq
      rfl
  | implicit unique retained_eq =>
    cases hb with
    | implicit other _ =>
      have eq := unique.symm.trans other
      cases List.cons.inj eq |>.1
      rfl

inductive ImplicitReferences (canon : String → String) (theta : Surface.SurfaceSubst) :
    List Presentation.AtomPat → Presentation.SupportTerms → List Reference → Prop where
  | nil : ImplicitReferences canon theta [] .nil []
  | cons (grounded : Surface.instantiateSurfaceAtom theta pattern = some ground)
      (tail : ImplicitReferences canon theta patterns builts rest) :
      ImplicitReferences canon theta (pattern :: patterns) (.cons built builts)
        (.implicit ground built :: rest)

inductive DischargeReferences :
    Presentation.Discharges → Presentation.Discharges → List Reference → Prop where
  | nil : DischargeReferences .nil .nil []
  | cons (tail : DischargeReferences authored retained refs) :
      DischargeReferences (.cons question (.leaf leaf) authored)
        (.cons question built retained) (.named ⟨leaf.val⟩ built :: refs)

/- A logical source-use relation, independent of key propagation. -/
mutual
  inductive TermReferences (canon : String → String) (policy : Presentation.Policy) :
      Presentation.SupportTerm → Presentation.SupportTerm → List Reference → Prop where
    | leaf : TermReferences canon policy (.leaf leaf) (.leaf leaf) []
    | omitted {id : Presentation.RuleId}
        (rule : Surface.ruleById policy id = some scheme)
        (premises : ImplicitReferences canon theta scheme.premises builtPremises refs)
        (discharges : DischargeReferences authoredDischarges builtDischarges dischargeRefs) :
        TermReferences canon policy
          (.rule id authoredTheta .nil authoredDischarges holes assurance)
          (.rule id theta builtPremises builtDischarges builtHoles builtAssurance)
          (refs ++ dischargeRefs)
    | explicit {id : Presentation.RuleId}
        (premises : TermsReferences canon policy (.cons term terms) builtPremises refs)
        (discharges : DischargeReferences authoredDischarges builtDischarges dischargeRefs) :
        TermReferences canon policy
          (.rule id authoredTheta (.cons term terms) authoredDischarges holes assurance)
          (.rule id theta builtPremises builtDischarges builtHoles builtAssurance)
          (refs ++ dischargeRefs)
  inductive TermsReferences (canon : String → String) (policy : Presentation.Policy) :
      Presentation.SupportTerms → Presentation.SupportTerms → List Reference → Prop where
    | nil : TermsReferences canon policy .nil .nil []
    | cons (head : TermReferences canon policy term built refs)
        (tail : TermsReferences canon policy terms builts rest) :
        TermsReferences canon policy (.cons term terms) (.cons built builts) (refs ++ rest)
end

def implicitReferences (canon : String → String) (theta : Surface.SurfaceSubst) :
    (patterns : List Presentation.AtomPat) → (built : Presentation.SupportTerms) →
    Except Error {refs // ImplicitReferences canon theta patterns built refs}
  | [], .nil => .ok ⟨[], .nil⟩
  | pattern :: patterns, .cons term terms => do
    match h : Surface.instantiateSurfaceAtom theta pattern with
    | none => .error .implicitMatch
    | some ground =>
      let rest ← implicitReferences canon theta patterns terms
      return ⟨.implicit ground term :: rest.val, .cons h rest.property⟩
  | _, _ => .error .shape

def dischargeReferences : (authored retained : Presentation.Discharges) →
    Except Error {refs // DischargeReferences authored retained refs}
  | .nil, .nil => .ok ⟨[], .nil⟩
  | .cons question (.leaf leaf) rest, .cons question' term terms => do
    if h : question = question' then
      let refs ← dischargeReferences rest terms
      return ⟨.named ⟨leaf.val⟩ term :: refs.val, h ▸ .cons refs.property⟩
    else .error .shape
  | _, _ => .error .shape

mutual
  def termReferences (canon : String → String) (policy : Presentation.Policy) :
      (authored retained : Presentation.SupportTerm) →
      Except Error {refs // TermReferences canon policy authored retained refs}
    | .leaf leaf, .leaf leaf' =>
      if h : leaf = leaf' then .ok ⟨[], h ▸ .leaf⟩ else .error .shape
    | .rule id theta premises discharges holes assurance,
        .rule id' theta' premises' discharges' holes' assurance' => do
      if h : id = id' then
        let ds ← dischargeReferences discharges discharges'
        match hp : premises with
        | .nil =>
          match hr : Surface.ruleById policy id with
          | none => .error (.missingRule id)
          | some scheme =>
            let ps ← implicitReferences canon theta' scheme.premises premises'
            return ⟨ps.val ++ ds.val, by
              subst id'
              simpa only [hp] using
                (TermReferences.omitted (authoredTheta := theta) (holes := holes)
                  (assurance := assurance) (builtHoles := holes') (builtAssurance := assurance')
                  hr ps.property ds.property)⟩
        | .cons term terms =>
          let ps ← termsReferences canon policy (.cons term terms) premises'
          return ⟨ps.val ++ ds.val, by
            subst id'
            simpa only [hp] using
              (TermReferences.explicit (id := id) (authoredTheta := theta) (holes := holes)
                (assurance := assurance) (theta := theta') (builtHoles := holes')
                (builtAssurance := assurance') ps.property ds.property)⟩
      else .error .shape
    | _, _ => .error .shape
  def termsReferences (canon : String → String) (policy : Presentation.Policy) :
      (authored retained : Presentation.SupportTerms) →
      Except Error {refs // TermsReferences canon policy authored retained refs}
    | .nil, .nil => .ok ⟨[], .nil⟩
    | .cons term terms, .cons term' terms' => do
      let first ← termReferences canon policy term term'
      let rest ← termsReferences canon policy terms terms'
      return ⟨first.val ++ rest.val, .cons first.property rest.property⟩
    | _, _ => .error .shape
end

inductive NamedReferences : List Presentation.ArgRef → Presentation.SupportTerms →
    List Reference → Prop where
  | nil : NamedReferences [] .nil []
  | cons (tail : NamedReferences refs terms rest) :
      NamedReferences (reference :: refs) (.cons term terms) (.named reference term :: rest)

def namedReferences : (refs : List Presentation.ArgRef) → (terms : Presentation.SupportTerms) →
    Except Error {uses // NamedReferences refs terms uses}
  | [], .nil => .ok ⟨[], .nil⟩
  | reference :: refs, .cons term terms => do
    let rest ← namedReferences refs terms
    return ⟨.named reference term :: rest.val, .cons rest.property⟩
  | _, _ => .error .shape

inductive NamedDischargeReferences : Presentation.ArgDischarge → Presentation.Discharges →
    List Reference → Prop where
  | nil : NamedDischargeReferences [] .nil []
  | cons (tail : NamedDischargeReferences refs terms rest) :
      NamedDischargeReferences ((question, reference) :: refs) (.cons question term terms)
        (.named reference term :: rest)

def namedDischargeReferences : (refs : Presentation.ArgDischarge) →
    (terms : Presentation.Discharges) →
    Except Error {uses // NamedDischargeReferences refs terms uses}
  | [], .nil => .ok ⟨[], .nil⟩
  | (question, reference) :: refs, .cons question' term terms => do
    if h : question = question' then
      let rest ← namedDischargeReferences refs terms
      return ⟨.named reference term :: rest.val, h ▸ .cons rest.property⟩
    else .error .shape
  | _, _ => .error .shape

inductive ArgumentReferences (canon : String → String) (policy : Presentation.Policy) :
    Presentation.ArgInstantiation → Presentation.SupportTerm → List Reference → Prop where
  | explicit (source : TermReferences canon policy authored retained refs) :
      ArgumentReferences canon policy (.explicitTheta authored) retained refs
  | inferred {id : Presentation.RuleId} (premises : NamedReferences authoredRefs retainedPremises refs)
      (discharges : NamedDischargeReferences authoredDischarges retainedDischarges ds) :
      ArgumentReferences canon policy (.inferTheta id authoredRefs authoredDischarges holes assurance)
        (.rule id theta retainedPremises retainedDischarges retainedHoles retainedAssurance) (refs ++ ds)

def instantiationReferences (canon : String → String) (policy : Presentation.Policy) :
    (authored : Presentation.ArgInstantiation) → (retained : Presentation.SupportTerm) →
    Except Error {refs // ArgumentReferences canon policy authored retained refs}
  | .explicitTheta term, retained => do
    let refs ← termReferences canon policy term retained
    return ⟨refs.val, .explicit refs.property⟩
  | .inferTheta id refs ds _ _, .rule id' _ ps' ds' _ _ => do
    if h : id = id' then
      let ps ← namedReferences refs ps'
      let ds ← namedDischargeReferences ds ds'
      return ⟨ps.val ++ ds.val, h ▸ .inferred ps.property ds.property⟩
    else .error .shape
  | _, _ => .error .shape

def argumentReferences (canon : String → String) (policy : Presentation.Policy)
    (argument : Presentation.Arg) (built : Surface.PriorArgument) :
    Except Error {refs // ArgumentReferences canon policy argument.instantiation built.term refs} := do
  if argument.id ≠ built.id then throw .shape
  instantiationReferences canon policy argument.instantiation built.term

/-- Membership is defined by source resolution, not core subterm inclusion. -/
def DependsOn (canon : String → String) (program : Presentation.Program)
    (priors : List Surface.PriorArgument) (refs : List Reference) (argument : Presentation.ArgId) : Prop :=
  ∃ reference ∈ refs, RefersTo canon program priors reference argument

def resolveAll (canon : String → String) (program : Presentation.Program)
    (priors : List Surface.PriorArgument) : (refs : List Reference) →
    Except Error {deps : List Presentation.ArgId //
      ∀ argument, argument ∈ deps ↔ DependsOn canon program priors refs argument}
  | [] => .ok ⟨[], by simp [DependsOn]⟩
  | reference :: refs => do
    let first ← resolve canon program priors reference
    let rest ← resolveAll canon program priors refs
    return ⟨first.val.toList ++ rest.val, by
      intro argument
      have first_iff : argument ∈ first.val.toList ↔
          RefersTo canon program priors reference argument := by
        constructor
        · intro member
          have eq : first.val = some argument := by simpa using member
          exact (show Resolves canon program priors reference (some argument) from
            eq ▸ first.property)
        · intro source
          have eq := resolves_unique first.property source
          simp [eq]
      simp only [List.mem_append, first_iff, rest.property, DependsOn, List.mem_cons]
      grind⟩

structure Direct (canon : String → String) (program : Presentation.Program)
    (policy : Presentation.Policy) (priors : List Surface.PriorArgument)
    (pair : Surface.ReconstructedArgument) where
  references : List Reference
  authored : ArgumentReferences canon policy pair.argument.instantiation pair.built.term references
  arguments : List Presentation.ArgId
  correspondence : ∀ argument, argument ∈ arguments ↔
    DependsOn canon program priors references argument

def directDependencies (canon : String → String) (program : Presentation.Program)
    (policy : Presentation.Policy) (priors : List Surface.PriorArgument)
    (pair : Surface.ReconstructedArgument) : Except Error (Direct canon program policy priors pair) := do
  let refs ← argumentReferences canon policy pair.argument pair.built
  let deps ← resolveAll canon program priors refs.val
  return ⟨refs.val, refs.property, deps.val, deps.property⟩

theorem direct_dependency_iff {canon program policy priors pair}
    (direct : Direct canon program policy priors pair) (argument : Presentation.ArgId) :
    argument ∈ direct.arguments ↔ DependsOn canon program priors direct.references argument :=
  direct.correspondence argument

structure Row where
  argument : Presentation.ArgId
  keys : List KindKey
  deriving DecidableEq

abbrev Table := List Row

def lookup (table : Table) (argument : Presentation.ArgId) : Except Error (List KindKey) :=
  match table.find? (fun row => decide (row.argument = argument)) with
  | none => .error (.missingArgument argument)
  | some row => .ok row.keys

def inherited (table : Table) : List Presentation.ArgId → Except Error (List KindKey)
  | [] => .ok []
  | argument :: rest => do
    let keys ← lookup table argument
    let tail ← inherited table rest
    return keys ++ tail

def ownKeys (pair : Surface.ReconstructedArgument) : List KindKey :=
  .argument pair.argument.id :: supportKeys pair.core

/-- The semantic ordered-table step states every inherited key explicitly. -/
inductive Ordered (canon : String → String) (program : Presentation.Program)
    (policy : Presentation.Policy) : List Surface.PriorArgument → Table →
    List Surface.ReconstructedArgument → Table → Prop where
  | nil : Ordered canon program policy priors table [] table
  | cons (direct : Direct canon program policy priors pair)
      (fresh : ∀ row ∈ table, row.argument ≠ pair.argument.id)
      (inherited_keys : inherited table direct.arguments = .ok inheritedKeys)
      (tail : Ordered canon program policy (priors ++ [pair.built])
        (table ++ [⟨pair.argument.id, ownKeys pair ++ inheritedKeys⟩]) pairs result) :
      Ordered canon program policy priors table (pair :: pairs) result

def build (canon : String → String) (program : Presentation.Program) (policy : Presentation.Policy) :
    (priors : List Surface.PriorArgument) → (table : Table) →
    (pairs : List Surface.ReconstructedArgument) →
    Except Error {result // Ordered canon program policy priors table pairs result}
  | _, table, [] => .ok ⟨table, .nil⟩
  | priors, table, pair :: pairs => do
    if fresh : ∀ row ∈ table, row.argument ≠ pair.argument.id then
      let direct ← directDependencies canon program policy priors pair
      match hi : inherited table direct.arguments with
      | .error error => .error error
      | .ok keys =>
        let rest ← build canon program policy (priors ++ [pair.built])
          (table ++ [⟨pair.argument.id, ownKeys pair ++ keys⟩]) pairs
        return ⟨rest.val, .cons direct fresh hi rest.property⟩
    else .error (.duplicateArgument pair.argument.id)

def ofObservation {input : SourceInput} (observation : AcceptedObservation input) : Except Error Table :=
  (build canonNum observation.accepted.audit.declared.semanticProgram input.surface.policy [] []
    observation.accepted.audit.declared.pairs).map Subtype.val

def checkedKeys {input : SourceInput} (observation : AcceptedObservation input)
    (table : Table) (node : Nat) : Except Error (List KindKey) :=
  match (Coordinates.names observation.run)[node]? with
  | none => .error (.missingNode node)
  | some argument => lookup table argument

theorem inherited_member {table dependencies keys argument used}
    (result : inherited table dependencies = .ok keys)
    (dependency : argument ∈ dependencies) (found : lookup table argument = .ok used) :
    ∀ key ∈ used, key ∈ keys := by
  induction dependencies generalizing keys with
  | nil => simp at dependency
  | cons head rest ih =>
    simp only [inherited] at result
    cases hhead : lookup table head with
    | error error => simp [hhead] at result
    | ok first =>
      cases htail : inherited table rest with
      | error error => simp [hhead, htail] at result
      | ok tail =>
        have eq : first ++ tail = keys := by
          simpa [hhead, htail, Except.bind, Except.pure] using result
        subst keys
        rcases List.mem_cons.mp dependency with equal | member
        · subst argument
          have eq := Except.ok.inj (hhead.symm.trans found)
          subst used
          intro key member
          exact List.mem_append_left _ member
        · intro key usedKey
          exact List.mem_append_right _ (ih htail member key usedKey)

/-- Every table row is preserved, in order, by subsequent steps. -/
theorem ordered_prefix {canon program policy priors table pairs result}
    (ordered : Ordered canon program policy priors table pairs result) :
    ∃ suffix, result = table ++ suffix := by
  induction ordered with
  | nil => exact ⟨[], by simp⟩
  | cons direct fresh inherited tail ih =>
    obtain ⟨suffix, eq⟩ := ih
    exact ⟨_ :: suffix, by simpa [List.append_assoc] using eq⟩

def Carries (table : Table) (argument : Presentation.ArgId) (key : KindKey) : Prop :=
  ∃ row ∈ table, row.argument = argument ∧ key ∈ row.keys

/-- Paths are made of actual authored edges in the ordered reconstruction. -/
inductive DependencyPath (edges : Presentation.ArgId → Presentation.ArgId → Prop) :
    Presentation.ArgId → Presentation.ArgId → Prop where
  | refl : DependencyPath edges argument argument
  | step (edge : edges dependent prior) (tail : DependencyPath edges prior origin) :
      DependencyPath edges dependent origin

theorem propagation_along_path {edges : Presentation.ArgId → Presentation.ArgId → Prop}
    {table : Table} (closed : ∀ dependent prior, edges dependent prior →
      ∀ key, Carries table prior key → Carries table dependent key)
    {dependent origin} (path : DependencyPath edges dependent origin) {key}
    (contributed : Carries table origin key) : Carries table dependent key := by
  induction path with
  | refl => exact contributed
  | step edge tail ih => exact closed _ _ edge key (ih contributed)

/-- Successful extraction exposes a source-ordered dependency relation. -/
inductive Ordered.edges {canon program policy} :
    {priors : List Surface.PriorArgument} → {table : Table} →
    {pairs : List Surface.ReconstructedArgument} → {result : Table} →
    Ordered canon program policy priors table pairs result →
    Presentation.ArgId → Presentation.ArgId → Prop where
  | here (direct : Direct canon program policy priors pair)
      (fresh : ∀ row ∈ table, row.argument ≠ pair.argument.id)
      (inherited : inherited table direct.arguments = .ok inheritedKeys)
      (tail : Ordered canon program policy (priors ++ [pair.built])
        (table ++ [⟨pair.argument.id, ownKeys pair ++ inheritedKeys⟩]) pairs result)
      (member : prior ∈ direct.arguments) :
      edges (Ordered.cons direct fresh inherited tail) pair.argument.id prior
  | there (direct : Direct canon program policy priors pair)
      (fresh : ∀ row ∈ table, row.argument ≠ pair.argument.id)
      (inherited : inherited table direct.arguments = .ok inheritedKeys)
      (tail : Ordered canon program policy (priors ++ [pair.built])
        (table ++ [⟨pair.argument.id, ownKeys pair ++ inheritedKeys⟩]) pairs result)
      (edge : edges tail dependent prior) :
      edges (Ordered.cons direct fresh inherited tail) dependent prior

def Consistent (table : Table) : Prop :=
  ∀ a ∈ table, ∀ b ∈ table, a.argument = b.argument → a.keys = b.keys

theorem consistent_append {table : Table} {row : Row} (consistent : Consistent table)
    (fresh : ∀ old ∈ table, old.argument ≠ row.argument) :
    Consistent (table ++ [row]) := by
  intro a ha b hb equal
  simp only [List.mem_append, List.mem_singleton] at ha hb
  rcases ha with ha | rfl <;> rcases hb with hb | rfl
  · exact consistent a ha b hb equal
  · exact False.elim (fresh a ha equal)
  · exact False.elim (fresh b hb equal.symm)
  · rfl

theorem lookup_member {table argument keys} (found : lookup table argument = .ok keys) :
    ∃ row ∈ table, row.argument = argument ∧ row.keys = keys := by
  unfold lookup at found
  cases h : table.find? (fun row => decide (row.argument = argument)) with
  | none => simp [h] at found
  | some row =>
    have eq : row.keys = keys := by simpa [h] using found
    have argumentEq : row.argument = argument := by simpa using List.find?_some h
    exact ⟨row, List.mem_of_find?_eq_some h, argumentEq, eq⟩

theorem lookup_of_member {table : Table} (consistent : Consistent table)
    {row : Row} (member : row ∈ table) : lookup table row.argument = .ok row.keys := by
  unfold lookup
  cases h : table.find? (fun candidate => decide (candidate.argument = row.argument)) with
  | none =>
    have impossible := List.find?_eq_none.mp h row member
    simp at impossible
  | some selected =>
    have selectedId : selected.argument = row.argument := by simpa using List.find?_some h
    exact congrArg Except.ok
      (consistent selected (List.mem_of_find?_eq_some h) row member selectedId)

theorem inherited_resolves {table dependencies keys}
    (result : inherited table dependencies = .ok keys) {argument}
    (member : argument ∈ dependencies) : ∃ used, lookup table argument = .ok used := by
  induction dependencies generalizing keys with
  | nil => simp at member
  | cons head rest ih =>
    cases hh : lookup table head with
    | error error => simp [inherited, hh] at result
    | ok used =>
      cases ht : inherited table rest with
      | error error => simp [inherited, hh, ht] at result
      | ok tail =>
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨used, hh⟩
        · exact ih ht member

theorem ordered_consistent {canon program policy priors table pairs result}
    (ordered : Ordered canon program policy priors table pairs result)
    (consistent : Consistent table) : Consistent result := by
  induction ordered with
  | nil => exact consistent
  | cons direct fresh inherited tail ih =>
    exact ih (consistent_append consistent fresh)

theorem ordered_arguments {canon program policy priors table pairs result}
    (ordered : Ordered canon program policy priors table pairs result) :
    result.map Row.argument = table.map Row.argument ++ pairs.map (fun pair => pair.argument.id) := by
  induction ordered with
  | nil => simp
  | cons direct fresh inherited tail ih =>
    simpa [List.map_append, List.append_assoc] using ih

theorem ordered_own_keys {canon program policy priors table pairs result}
    (ordered : Ordered canon program policy priors table pairs result)
    {pair : Surface.ReconstructedArgument} (member : pair ∈ pairs)
    {key} (used : key ∈ ownKeys pair) : Carries result pair.argument.id key := by
  induction ordered with
  | nil => simp at member
  | @cons priors table head inheritedKeys pairs result direct fresh inherited tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨suffix, eq⟩ := ordered_prefix tail
      rw [eq]
      exact ⟨⟨pair.argument.id, ownKeys pair ++ inheritedKeys⟩,
        by simp, rfl, List.mem_append_left _ used⟩
    · exact ih member

theorem ordered_edge_propagation {canon program policy priors table pairs result}
    (ordered : Ordered canon program policy priors table pairs result)
    (consistent : Consistent table) {dependent prior}
    (edge : ordered.edges dependent prior) {key}
    (contributed : Carries result prior key) : Carries result dependent key := by
  induction edge with
  | @here priors pair table inheritedKeys pairs result prior direct fresh inherited tail member =>
    obtain ⟨used, found⟩ := inherited_resolves inherited member
    obtain ⟨priorRow, priorMember, priorId, priorKeys⟩ := lookup_member found
    obtain ⟨contributor, contributorMember, contributorId, contributedKey⟩ := contributed
    obtain ⟨suffix, eq⟩ := ordered_prefix tail
    have finalConsistent := ordered_consistent tail (consistent_append consistent fresh)
    have priorFinal := List.mem_append_left suffix
      (List.mem_append_left [⟨pair.argument.id, ownKeys pair ++ inheritedKeys⟩] priorMember)
    rw [← eq] at priorFinal
    have keysEq := finalConsistent contributor contributorMember priorRow priorFinal
      (contributorId.trans priorId.symm)
    have usedKey : key ∈ used := by
      rw [← priorKeys, ← keysEq]
      exact contributedKey
    have inheritedKey := inherited_member inherited member found key usedKey
    rw [eq]
    refine ⟨⟨pair.argument.id, ownKeys pair ++ inheritedKeys⟩,
      ?_, rfl, List.mem_append_right _ inheritedKey⟩
    simp
  | there direct fresh inherited tail edge ih =>
    exact ih (consistent_append consistent fresh) contributed

theorem ordered_path_propagation {canon program policy priors table pairs result}
    (ordered : Ordered canon program policy priors table pairs result)
    (consistent : Consistent table) {dependent origin}
    (path : DependencyPath ordered.edges dependent origin) {key}
    (contributed : Carries result origin key) : Carries result dependent key :=
  propagation_along_path
    (fun _ _ edge _ carried => ordered_edge_propagation ordered consistent edge carried)
    path contributed

/-- The scalar meet cannot exceed any actual leaf, rule, or prior argument key. -/
def scalar (kind : KindKey → EvidenceKind × Bool) (keys : List KindKey) : EvidenceKind × Bool :=
  meetKinds (keys.map kind)

theorem scalar_le_key (kind : KindKey → EvidenceKind × Bool) {keys key}
    (used : key ∈ keys) : (scalar kind keys).1 ≤ (kind key).1 :=
  meetKinds_le_input (List.mem_map_of_mem used)

theorem scalar_complete (kind : KindKey → EvidenceKind × Bool) (keys : List KindKey) :
    (scalar kind keys).2 = true ↔ ∀ key ∈ keys, (kind key).2 = true := by
  simp [scalar, meetKinds_complete]

theorem scalar_no_promotion (kind : KindKey → EvidenceKind × Bool) {keys key}
    (used : key ∈ keys) (cap : (kind key).1 = .hypothetical) :
    (scalar kind keys).1 = .hypothetical := by
  apply le_antisymm _ bot_le
  have bound := scalar_le_key kind used
  rw [cap] at bound
  exact bound

theorem scalar_conditional_cap (kind : KindKey → EvidenceKind × Bool) {keys key}
    (used : key ∈ keys) (cap : (kind key).1 ≤ .conditional) :
    (scalar kind keys).1 ≤ .conditional :=
  le_trans (scalar_le_key kind used) cap

theorem scalar_inputKind_no_promotion (source : SourceInput) (history : ProcessHistory)
    (specs : List KindSpec) (assumptions : List CaptureAssumption) (admitted : List AdmissionBasis)
    (hypothetical : List KindKey) {keys key} (used : key ∈ keys) (slot : key ∈ hypothetical) :
    (scalar (inputKind source history specs assumptions admitted hypothetical) keys).1 = .hypothetical :=
  scalar_no_promotion _ used
    (inputKind_hypothetical source history specs assumptions admitted hypothetical key slot)

theorem ofObservation_ordered {input : SourceInput} (observation : AcceptedObservation input)
    {table} (accepted : ofObservation observation = .ok table) :
    Ordered canonNum observation.accepted.audit.declared.semanticProgram input.surface.policy
      [] [] observation.accepted.audit.declared.pairs table := by
  unfold ofObservation at accepted
  cases h : build canonNum observation.accepted.audit.declared.semanticProgram
      input.surface.policy [] [] observation.accepted.audit.declared.pairs with
  | error error => simp [h, Except.map] at accepted
  | ok result =>
    have eq : result.val = table := by simpa [h, Except.map] using accepted
    exact eq ▸ result.property

theorem carries_lookup {table argument key keys}
    (consistent : Consistent table) (carried : Carries table argument key)
    (found : lookup table argument = .ok keys) : key ∈ keys := by
  obtain ⟨row, member, arg, used⟩ := carried
  obtain ⟨selected, selectedMember, selectedArg, selectedKeys⟩ := lookup_member found
  have equal := consistent row member selected selectedMember (arg.trans selectedArg.symm)
  rwa [equal, selectedKeys] at used

/-- All actual own-support inputs, including leaf and rule keys, flow through
every authored prior-argument path. The only kind premise is the input cap. -/
theorem ordered_input_bound {canon program policy priors table pairs result}
    (ordered : Ordered canon program policy priors table pairs result)
    (consistent : Consistent table) {origin : Surface.ReconstructedArgument}
    (declared : origin ∈ pairs) {dependent key keys}
    (path : DependencyPath ordered.edges dependent origin.argument.id)
    (input : key ∈ ownKeys origin) (found : lookup result dependent = .ok keys)
    (kind : KindKey → EvidenceKind × Bool) :
    (scalar kind keys).1 ≤ (kind key).1 := by
  have originKey := ordered_own_keys ordered declared input
  have targetKey := ordered_path_propagation ordered consistent path originKey
  exact scalar_le_key kind
    (carries_lookup (ordered_consistent ordered consistent) targetKey found)

theorem ordered_path_no_promotion {canon program policy priors table pairs result}
    (ordered : Ordered canon program policy priors table pairs result)
    (consistent : Consistent table) {origin : Surface.ReconstructedArgument}
    (declared : origin ∈ pairs) {dependent key keys}
    (path : DependencyPath ordered.edges dependent origin.argument.id)
    (input : key ∈ ownKeys origin) (found : lookup result dependent = .ok keys)
    (kind : KindKey → EvidenceKind × Bool) (cap : (kind key).1 = .hypothetical) :
    (scalar kind keys).1 = .hypothetical := by
  apply le_antisymm _ bot_le
  have bound := ordered_input_bound ordered consistent declared path input found kind
  rw [cap] at bound
  exact bound

theorem ordered_path_conditional_cap {canon program policy priors table pairs result}
    (ordered : Ordered canon program policy priors table pairs result)
    (consistent : Consistent table) {origin : Surface.ReconstructedArgument}
    (declared : origin ∈ pairs) {dependent key keys}
    (path : DependencyPath ordered.edges dependent origin.argument.id)
    (input : key ∈ ownKeys origin) (found : lookup result dependent = .ok keys)
    (kind : KindKey → EvidenceKind × Bool) (cap : (kind key).1 ≤ .conditional) :
    (scalar kind keys).1 ≤ .conditional :=
  le_trans (ordered_input_bound ordered consistent declared path input found kind) cap

theorem checkedKeys_stable {input : SourceInput} (observation : AcceptedObservation input)
    (table : Table) {node argument}
    (stable : (Coordinates.names observation.run)[node]? = some argument) :
    checkedKeys observation table node = lookup table argument := by
  simp [checkedKeys, stable]

theorem lookup_missing {table argument}
    (missing : table.find? (fun row => decide (row.argument = argument)) = none) :
    lookup table argument = .error (.missingArgument argument) := by
  simp [lookup, missing]

theorem implicitReferences_unique {canon theta patterns built refs other}
    (first : ImplicitReferences canon theta patterns built refs)
    (second : ImplicitReferences canon theta patterns built other) : refs = other := by
  induction first generalizing other with
  | nil => cases second; rfl
  | cons grounded tail ih =>
    cases second with
    | cons otherGrounded otherTail =>
      have equal := Option.some.inj (grounded.symm.trans otherGrounded)
      subst equal
      rw [ih otherTail]

theorem dischargeReferences_unique {authored built refs other}
    (first : DischargeReferences authored built refs)
    (second : DischargeReferences authored built other) : refs = other := by
  induction first generalizing other with
  | nil => cases second; rfl
  | cons tail ih => cases second with
    | cons otherTail => rw [ih otherTail]

theorem termReferences_unique {canon policy authored built refs}
    (first : TermReferences canon policy authored built refs) :
    ∀ other, TermReferences canon policy authored built other → refs = other := by
  induction first using TermReferences.rec
    (motive_2 := fun authored built refs _ =>
      ∀ other, TermsReferences canon policy authored built other → refs = other) with
  | leaf =>
    intro other second
    cases second
    rfl
  | omitted rule premises discharges =>
    intro other second
    cases second with
    | omitted otherRule otherPremises otherDischarges =>
      have equal := Option.some.inj (rule.symm.trans otherRule)
      subst equal
      rw [implicitReferences_unique premises otherPremises,
        dischargeReferences_unique discharges otherDischarges]
  | explicit premises discharges ih =>
    intro other second
    cases second with
    | explicit otherPremises otherDischarges =>
      rw [ih _ otherPremises, dischargeReferences_unique discharges otherDischarges]
  | nil =>
    rename_i other second
    cases second
    rfl
  | cons head tail ihHead ihTail =>
    rename_i other second
    cases second with
    | cons otherHead otherTail => rw [ihHead _ otherHead, ihTail _ otherTail]

theorem namedReferences_unique {authored built refs other}
    (first : NamedReferences authored built refs)
    (second : NamedReferences authored built other) : refs = other := by
  induction first generalizing other with
  | nil => cases second; rfl
  | cons tail ih => cases second with
    | cons otherTail => rw [ih otherTail]

theorem namedDischargeReferences_unique {authored built refs other}
    (first : NamedDischargeReferences authored built refs)
    (second : NamedDischargeReferences authored built other) : refs = other := by
  induction first generalizing other with
  | nil => cases second; rfl
  | cons tail ih => cases second with
    | cons otherTail => rw [ih otherTail]

theorem argumentReferences_unique {canon policy authored built refs other}
    (first : ArgumentReferences canon policy authored built refs)
    (second : ArgumentReferences canon policy authored built other) : refs = other := by
  cases first with
  | explicit term =>
    cases second with
    | explicit otherTerm => exact termReferences_unique term _ otherTerm
  | inferred premises discharges =>
    cases second with
    | inferred otherPremises otherDischarges =>
      rw [namedReferences_unique premises otherPremises,
        namedDischargeReferences_unique discharges otherDischarges]

/-- An authored dependency admits a syntax-directed occurrence derivation and
an independent source-reference resolution. No executable dependency list is a premise. -/
def SourceDependency (canon : String → String) (program : Presentation.Program)
    (policy : Presentation.Policy) (priors : List Surface.PriorArgument)
    (pair : Surface.ReconstructedArgument) (argument : Presentation.ArgId) : Prop :=
  ∃ refs, ArgumentReferences canon policy pair.argument.instantiation pair.built.term refs ∧
    DependsOn canon program priors refs argument

theorem direct_source_correspondence {canon program policy priors pair}
    (direct : Direct canon program policy priors pair) (argument : Presentation.ArgId) :
    argument ∈ direct.arguments ↔ SourceDependency canon program policy priors pair argument := by
  rw [direct.correspondence]
  constructor
  · intro depends
    exact ⟨direct.references, direct.authored, depends⟩
  · rintro ⟨refs, authored, depends⟩
    have equal := argumentReferences_unique direct.authored authored
    simpa only [equal] using depends

/-- Actual core inputs follow constructor edges, including discharged supports. -/
inductive CoreInput : Support.SupportTerm → KindKey → Prop where
  | leaf : CoreInput (.leaf leaf) (.leaf ⟨leaf.name⟩)
  | method : CoreInput (.inst rule theta premises discharges holes assurance) (.method rule)
  | premise (member : term ∈ premises) (input : CoreInput term key) :
      CoreInput (.inst rule theta premises discharges holes assurance) key
  | discharge (member : entry ∈ discharges) (input : CoreInput entry.2 key) :
      CoreInput (.inst rule theta premises discharges holes assurance) key

theorem premiseKeys_member {terms : List Support.SupportTerm} {term key}
    (member : term ∈ terms) (used : key ∈ supportKeys term) : key ∈ premiseKeys terms := by
  induction terms with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_append_left _ used
    · exact List.mem_append_right _ (ih member)

theorem dischargeKeys_member {terms : List (Support.QuestionId × Support.SupportTerm)} {entry key}
    (member : entry ∈ terms) (used : key ∈ supportKeys entry.2) : key ∈ dischargeKeys terms := by
  induction terms with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_append_left _ used
    · exact List.mem_append_right _ (ih member)

theorem coreInput_keys {term key} (input : CoreInput term key) : key ∈ supportKeys term := by
  induction input with
  | leaf => simp [supportKeys]
  | method => simp [supportKeys]
  | premise member input ih =>
    exact List.mem_cons_of_mem _ (List.mem_append_left _ (premiseKeys_member member ih))
  | discharge member input ih =>
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (dischargeKeys_member member ih))

theorem ordered_core_input_bound {canon program policy priors table pairs result}
    (ordered : Ordered canon program policy priors table pairs result)
    (consistent : Consistent table) {origin : Surface.ReconstructedArgument}
    (declared : origin ∈ pairs) {dependent key keys}
    (path : DependencyPath ordered.edges dependent origin.argument.id)
    (input : CoreInput origin.core key) (found : lookup result dependent = .ok keys)
    (kind : KindKey → EvidenceKind × Bool) :
    (scalar kind keys).1 ≤ (kind key).1 :=
  ordered_input_bound ordered consistent declared path
    (List.mem_cons_of_mem _ (coreInput_keys input)) found kind

theorem ordered_prior_method_bound {canon program policy priors table pairs result}
    (ordered : Ordered canon program policy priors table pairs result)
    (consistent : Consistent table) {origin : Surface.ReconstructedArgument}
    (declared : origin ∈ pairs) {dependent keys}
    (path : DependencyPath ordered.edges dependent origin.argument.id)
    (found : lookup result dependent = .ok keys) (kind : KindKey → EvidenceKind × Bool) :
    (scalar kind keys).1 ≤ (kind (.argument origin.argument.id)).1 :=
  ordered_input_bound ordered consistent declared path (List.mem_cons_self) found kind

end Lara.Process.Source.Provenance
