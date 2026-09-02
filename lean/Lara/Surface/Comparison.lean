/-
Comparison-block expansion for the checked surface calculus: each authored
`comparison` block is replaced, in place, by the three declarations it stands
for — the generated sub-claim, the strict recheck argument (with the `ord@1`
certificate over the two 0-based premise slots), and the defeasible bridge
argument — mirroring the production `Lara.Elaborate.Comparison.expandSurface`
pass.

The expansion relation `ExpandsComparisons` is stated independently (structural
replacement over declarations); the executable `expandComparisons` rejects with
the production check order: generated-id collisions, duplicate blocks, then
per-block expansion failures, each reported as the coarse `invalidComparison`
error naming the offending block's claim id.  Soundness, completeness (over the
`ComparisonsWellFormed` fragment with fresh generated ids), declaration-order
preservation, exact generated-id accounting, and elimination of every
`Decl.comparison` in the semantic program are proved against that relation.
-/
import Lara.Surface.Syntax
import Lara.Surface.ValueBinding

namespace Lara.Surface

open Lara
open Lara.Presentation

/-! ### Generated-argument provenance -/

/-- The role a generated argument plays in its block's expansion. -/
inductive GeneratedRole where
  | recheck
  | bridge
deriving DecidableEq

/-- One argument a `comparison` block minted: the block's claim id, the
generated argument id, and the role.  Diagnostic metadata beside the semantic
program, mirroring `Lara.Elaborate.Comparison.GeneratedArg`. -/
structure GeneratedArg where
  comparisonClaim : Presentation.PropId
  arg : Presentation.ArgId
  role : GeneratedRole
deriving DecidableEq

/-! ### The generated declarations -/

/-- The on-the-wire premise-slot reference `(prem N)`. -/
def premRef (i : Nat) : Sx :=
  .node "prem" (.cons (.str (toString i)) .nil)

/-- The `ord@1` certificate payload `(ordcmp (prem L) (prem R))`. -/
def ordcmpPayload (left right : Nat) : Sx :=
  .node "ordcmp" (.cons (premRef left) (.cons (premRef right) .nil))

/-- Restrict a substitution to the parameters of a rule, in the rule's own
parameter order — the positional θ the emitted rule support term carries. -/
def thetaFor (theta : SurfaceSubst) (rule : Presentation.Rule) : Subst :=
  rule.params.filterMap (fun p => (lookupSurfaceSubst theta p).map (fun t => (p, t)))

/-- The generated sub-claim: authored `nl` and `binding`, generated `formal`. -/
def generatedSubClaim (data : ComparisonExpansionData) (c : Presentation.Comparison) : Claim :=
  { id := c.claim.id
    nl := c.claim.nlRaw
    formal := data.goal
    binding := c.claim.binding }

/-- The generated recheck support term: the recheck rule under its θ with the
`ord@1` certificate over the two premise slots. -/
def generatedRecheckTerm (data : ComparisonExpansionData) : Presentation.SupportTerm :=
  .rule data.recheck.id (thetaFor data.thetaRecheck data.recheck) .nil .nil []
    (.cert ⟨data.certRef.backend, data.certRef.version, data.certRef.theory,
      ordcmpPayload data.slotLeft data.slotRight⟩)

/-- The bridge's premise slots, in slot order: the comparison slot carries the
recheck term, the binding slot the named binding leaf.  Valid expansion data
has exactly two premises and the two slots are distinct, so every slot is one
of the two. -/
private def bridgePremisesAux (data : ComparisonExpansionData) (c : Presentation.Comparison)
    (recheckTerm : Presentation.SupportTerm) : Nat → SupportTerms → SupportTerms
  | 0, acc => acc
  | n + 1, acc =>
      let term := if n = data.bridgeComparisonSlot then recheckTerm else .leaf c.binding
      bridgePremisesAux data c recheckTerm n (.cons term acc)

private def bridgePremises (data : ComparisonExpansionData) (c : Presentation.Comparison)
    (recheckTerm : Presentation.SupportTerm) : SupportTerms :=
  bridgePremisesAux data c recheckTerm data.bridge.premises.length .nil

/-- The generated bridge argument: the bridge rule under its θ, its binding
premise fed the named binding leaf and its comparison premise the recheck term. -/
def generatedBridgeArg (data : ComparisonExpansionData) (c : Presentation.Comparison) : Arg :=
  ⟨c.bridgeArg,
    match c.supports with
    | none => .supportsDerived ⟨c.bridgeArg.val⟩
    | some claim => .supportsClaim claim,
    .explicitTheta
      (.rule data.bridge.id (thetaFor data.thetaBridge data.bridge)
        (bridgePremises data c (generatedRecheckTerm data)) .nil [] .none)⟩

/-- The recheck argument of a block. -/
def generatedRecheckArg (data : ComparisonExpansionData) (c : Presentation.Comparison) : Arg :=
  ⟨c.recheckArg, .supportsClaim c.claim.id, .explicitTheta (generatedRecheckTerm data)⟩

/-- The three declarations one `comparison` block expands to, in order:
sub-claim, recheck argument, bridge argument. -/
def generatedDecls (data : ComparisonExpansionData) (c : Presentation.Comparison) : List Decl :=
  [.claim (generatedSubClaim data c), .arg (generatedRecheckArg data c),
    .arg (generatedBridgeArg data c)]

/-- The two provenance crumbs one block mints, in declaration order. -/
def generatedArgs (c : Presentation.Comparison) : List GeneratedArg :=
  [⟨c.claim.id, c.recheckArg, .recheck⟩, ⟨c.claim.id, c.bridgeArg, .bridge⟩]

/-! ### The independent relation -/

/-- Whether a declaration is a `comparison` block (the only kind the expansion
rewrites). -/
def isComparison : Decl → Bool
  | .comparison _ => true
  | _ => false

/-- The structural declaration relation: a `comparison` block is replaced by its
three generated declarations, every other declaration is kept unchanged, in the
same relative order. -/
inductive DeclsExpandComparisons (policy : Presentation.Policy)
    (program : Presentation.Program) : List Decl → List Decl → List GeneratedArg → Prop where
  | nil : DeclsExpandComparisons policy program [] [] []
  | keep {d : Decl} {ds ts : List Decl} {gs : List GeneratedArg}
      (hkeep : isComparison d = false) :
      DeclsExpandComparisons policy program ds ts gs →
      DeclsExpandComparisons policy program (d :: ds) (d :: ts) gs
  | expand {c : Presentation.Comparison} {data : ComparisonExpansionData}
      {ds ts : List Decl} {gs : List GeneratedArg}
      (hdata : ComparisonExpansionSpec program policy c data) :
      DeclsExpandComparisons policy program ds ts gs →
      DeclsExpandComparisons policy program (.comparison c :: ds)
        (generatedDecls data c ++ ts) (generatedArgs c ++ gs)

/-- The independent comparison-expansion relation: the target is the source
with every `comparison` block replaced by its generated declarations, in place,
and the provenance list is exactly the blocks' recheck/bridge crumbs in
declaration order. -/
inductive ExpandsComparisons (policy : Presentation.Policy)
    (source target : Presentation.Program) (generated : List GeneratedArg) : Prop where
  | intro (hdecls : DeclsExpandComparisons policy source source.decls target.decls generated)
      (hartifact : target.artifact = source.artifact)
      (hdigest : target.digest = source.digest)
      (hpolicy : target.policy = source.policy)
      (hbackends : target.backends = source.backends)
      (hbindings : target.valueBindings = source.valueBindings) :
      ExpandsComparisons policy source target generated

/-! ### The executable pass -/

/-- Scan comparison blocks from left to right for a generated/generated or
generated/authored identifier collision.  Duplicates solely among authored
declarations are intentionally outside this phase. -/
private def generatedIdCollisionClaimAux
    (declaredArgs : List Presentation.ArgId)
    (declaredClaims : List Presentation.PropId)
    (seenArgs : List Presentation.ArgId)
    (seenClaims : List Presentation.PropId) :
    List Presentation.Comparison → Option Presentation.PropId
  | [] => none
  | comparison :: rest =>
      if comparison.recheckArg = comparison.bridgeArg ||
          declaredArgs.contains comparison.recheckArg ||
          declaredArgs.contains comparison.bridgeArg ||
          seenArgs.contains comparison.recheckArg ||
          seenArgs.contains comparison.bridgeArg ||
          declaredClaims.contains comparison.claim.id ||
          seenClaims.contains comparison.claim.id then
        some comparison.claim.id
      else
        generatedIdCollisionClaimAux declaredArgs declaredClaims
          (comparison.bridgeArg :: comparison.recheckArg :: seenArgs)
          (comparison.claim.id :: seenClaims) rest

/-- The current block whose generated identifiers first collide while scanning
comparison blocks from left to right. -/
def generatedIdCollisionClaim? (program : Presentation.Program) :
    Option Presentation.PropId :=
  generatedIdCollisionClaimAux
    (program.decls.filterMap fun d => match d with | .arg a => some a.id | _ => none)
    (program.decls.filterMap fun d => match d with | .claim c => some c.id | _ => none)
    [] [] (comparisonDecls program)

/-- Generated identifiers are fresh exactly when the ordered collision scan
finds no offender. -/
def GeneratedIdsFresh (program : Presentation.Program) : Bool :=
  (generatedIdCollisionClaim? program).isNone

private theorem generatedIdCollisionClaimAux_none_properties
    (declaredArgs : List Presentation.ArgId)
    (declaredClaims : List Presentation.PropId)
    (seenArgs : List Presentation.ArgId)
    (seenClaims : List Presentation.PropId)
    (blocks : List Presentation.Comparison)
    (h : generatedIdCollisionClaimAux declaredArgs declaredClaims
      seenArgs seenClaims blocks = none) :
    let args := blocks.flatMap (fun c => [c.recheckArg, c.bridgeArg])
    let claims := blocks.map (·.claim.id)
    args.Nodup ∧
      (∀ id ∈ args, id ∉ declaredArgs) ∧
      (∀ id ∈ args, id ∉ seenArgs) ∧
      claims.Nodup ∧
      (∀ id ∈ claims, id ∉ declaredClaims) ∧
      (∀ id ∈ claims, id ∉ seenClaims) := by
  induction blocks generalizing seenArgs seenClaims with
  | nil => simp
  | cons comparison rest ih =>
      simp only [generatedIdCollisionClaimAux] at h
      split at h
      · contradiction
      · have htail := ih
          (comparison.bridgeArg :: comparison.recheckArg :: seenArgs)
          (comparison.claim.id :: seenClaims) h
        simp_all [List.nodup_cons]
        constructor
        · constructor
          · intro x hx
            have hr := htail.2.2.1 x.recheckArg x hx (Or.inl rfl)
            have hb := htail.2.2.1 x.bridgeArg x hx (Or.inr rfl)
            exact ⟨Ne.symm hr.2.1, Ne.symm hb.2.1⟩
          · intro x hx
            have hr := htail.2.2.1 x.recheckArg x hx (Or.inl rfl)
            have hb := htail.2.2.1 x.bridgeArg x hx (Or.inr rfl)
            exact ⟨Ne.symm hr.1, Ne.symm hb.1⟩
        · constructor
          · exact htail.2.1
          · intro id x hx hid
            exact (htail.2.2.1 id x hx hid).2.2


private theorem generatedIdCollisionClaimAux_none_of_properties
    (declaredArgs : List Presentation.ArgId)
    (declaredClaims : List Presentation.PropId)
    (seenArgs : List Presentation.ArgId)
    (seenClaims : List Presentation.PropId)
    (blocks : List Presentation.Comparison)
    (hargs : (blocks.flatMap fun c => [c.recheckArg, c.bridgeArg]).Nodup)
    (hargsDeclared : ∀ id ∈ blocks.flatMap (fun c => [c.recheckArg, c.bridgeArg]),
      id ∉ declaredArgs)
    (hargsSeen : ∀ id ∈ blocks.flatMap (fun c => [c.recheckArg, c.bridgeArg]),
      id ∉ seenArgs)
    (hclaims : (blocks.map (·.claim.id)).Nodup)
    (hclaimsDeclared : ∀ id ∈ blocks.map (·.claim.id), id ∉ declaredClaims)
    (hclaimsSeen : ∀ id ∈ blocks.map (·.claim.id), id ∉ seenClaims) :
    generatedIdCollisionClaimAux declaredArgs declaredClaims
      seenArgs seenClaims blocks = none := by
  induction blocks generalizing seenArgs seenClaims with
  | nil => rfl
  | cons comparison rest ih =>
      simp only [List.flatMap_cons, List.map_cons] at hargs hclaims
      change (comparison.recheckArg :: comparison.bridgeArg ::
        rest.flatMap (fun c => [c.recheckArg, c.bridgeArg])).Nodup at hargs
      simp only [List.nodup_cons] at hargs hclaims
      simp only [generatedIdCollisionClaimAux]
      have hrecheckBridge : comparison.recheckArg ≠ comparison.bridgeArg := by
        intro heq
        exact hargs.1 (by simp [heq])
      have hrecheckDeclared := hargsDeclared comparison.recheckArg
        (by simp)
      have hbridgeDeclared := hargsDeclared comparison.bridgeArg
        (by simp)
      have hrecheckSeen := hargsSeen comparison.recheckArg (by simp)
      have hbridgeSeen := hargsSeen comparison.bridgeArg (by simp)
      have hclaimDeclared := hclaimsDeclared comparison.claim.id (by simp)
      have hclaimSeen := hclaimsSeen comparison.claim.id (by simp)
      simp [hrecheckBridge, hrecheckDeclared, hbridgeDeclared,
        hrecheckSeen, hbridgeSeen, hclaimDeclared, hclaimSeen]
      apply ih (seenArgs := comparison.bridgeArg :: comparison.recheckArg :: seenArgs)
        (seenClaims := comparison.claim.id :: seenClaims) hargs.2.2
      · intro id hid
        exact hargsDeclared id (by simp [hid])
      · intro id hid
        simp only [List.mem_cons, not_or]
        exact ⟨fun heq => hargs.2.1 (by simpa [heq] using hid),
          ⟨fun heq => hargs.1
              (List.mem_cons_of_mem _ (heq ▸ hid)),
            hargsSeen id (by simp [hid])⟩⟩
      · exact hclaims.2
      · intro id hid
        exact hclaimsDeclared id (by simp [hid])
      · intro id hid
        simp only [List.mem_cons, not_or]
        exact ⟨fun heq => hclaims.1 (heq ▸ hid),
          hclaimsSeen id (by simp [hid])⟩
private theorem generatedIdsFresh_properties {program : Presentation.Program}
    (hf : GeneratedIdsFresh program = true) :
    let args := (comparisonDecls program).flatMap
      (fun c => [c.recheckArg, c.bridgeArg])
    let declaredArgs := program.decls.filterMap
      (fun d => match d with | .arg a => some a.id | _ => none)
    let claims := (comparisonDecls program).map (·.claim.id)
    let declaredClaims := program.decls.filterMap
      (fun d => match d with | .claim c => some c.id | _ => none)
    args.Nodup ∧
      (∀ id ∈ args, id ∉ declaredArgs) ∧
      claims.Nodup ∧
      (∀ id ∈ claims, id ∉ declaredClaims) := by
  have hnone : generatedIdCollisionClaim? program = none := by
    simpa [GeneratedIdsFresh] using hf
  have haux : generatedIdCollisionClaimAux
      (program.decls.filterMap fun d => match d with | .arg a => some a.id | _ => none)
      (program.decls.filterMap fun d => match d with | .claim c => some c.id | _ => none)
      [] [] (comparisonDecls program) = none := by
    simpa [generatedIdCollisionClaim?] using hnone
  have hprops := generatedIdCollisionClaimAux_none_properties
    (program.decls.filterMap fun d => match d with | .arg a => some a.id | _ => none)
    (program.decls.filterMap fun d => match d with | .claim c => some c.id | _ => none)
    [] [] (comparisonDecls program) haux
  exact ⟨hprops.1, hprops.2.1, hprops.2.2.2.1, hprops.2.2.2.2.1⟩

private def declaredArgIds (decls : List Presentation.Decl) :
    List Presentation.ArgId :=
  decls.filterMap fun
    | .arg argument => some argument.id
    | _ => none

private def generatedArgIds (comparisons : List Presentation.Comparison) :
    List Presentation.ArgId :=
  comparisons.flatMap fun comparison =>
    [comparison.recheckArg, comparison.bridgeArg]

private def declaredClaimIds (decls : List Presentation.Decl) :
    List Presentation.PropId :=
  decls.filterMap fun
    | .claim claim => some claim.id
    | _ => none

private def generatedClaimIds (comparisons : List Presentation.Comparison) :
    List Presentation.PropId :=
  comparisons.map (·.claim.id)

private theorem argIds_perm_partition (decls : List Presentation.Decl) :
    (decls.flatMap fun
      | .arg argument => [argument.id]
      | .comparison comparison => [comparison.recheckArg, comparison.bridgeArg]
      | _ => []).Perm
      (declaredArgIds decls ++ generatedArgIds
        (decls.filterMap fun
          | .comparison comparison => some comparison
          | _ => none)) := by
  induction decls with
  | nil => rfl
  | cons d ds ih =>
      cases d with
      | comparison comparison =>
          simp only [List.flatMap_cons, List.filterMap_cons,
            List.nil_append, List.cons_append]
          refine (List.Perm.cons comparison.recheckArg
            (List.Perm.cons comparison.bridgeArg ih)).trans ?_
          have hmove := List.Perm.append_right
            (generatedArgIds
              (List.filterMap (fun x => match x with
                | .comparison comparison => some comparison
                | _ => none) ds))
            (List.perm_append_comm :
              ([comparison.recheckArg, comparison.bridgeArg] ++ declaredArgIds ds).Perm
                (declaredArgIds ds ++
                  [comparison.recheckArg, comparison.bridgeArg]))
          simpa [declaredArgIds, generatedArgIds, List.append_assoc] using hmove
      | leaf leaf => simpa [declaredArgIds, generatedArgIds] using ih
      | claim claim => simpa [declaredArgIds, generatedArgIds] using ih
      | arg argument =>
          simpa [declaredArgIds, generatedArgIds] using ih.cons argument.id
      | attack attack => simpa [declaredArgIds, generatedArgIds] using ih
      | status status => simpa [declaredArgIds, generatedArgIds] using ih
      | group group => simpa [declaredArgIds, generatedArgIds] using ih

private theorem claimIds_perm_partition (decls : List Presentation.Decl) :
    (decls.filterMap fun
      | .claim claim => some claim.id
      | .comparison comparison => some comparison.claim.id
      | _ => none).Perm
      (declaredClaimIds decls ++ generatedClaimIds
        (decls.filterMap fun
          | .comparison comparison => some comparison
          | _ => none)) := by
  induction decls with
  | nil => rfl
  | cons d ds ih =>
      cases d with
      | comparison comparison =>
          refine (ih.cons comparison.claim.id).trans ?_
          have hmove := List.Perm.append_right
            (generatedClaimIds
              (List.filterMap (fun x => match x with
                | .comparison comparison => some comparison
                | _ => none) ds))
            (List.perm_append_comm :
              ([comparison.claim.id] ++ declaredClaimIds ds).Perm
                (declaredClaimIds ds ++ [comparison.claim.id]))
          simpa [declaredClaimIds, generatedClaimIds, List.append_assoc] using hmove
      | leaf leaf => simpa [declaredClaimIds, generatedClaimIds] using ih
      | claim claim =>
          simpa [declaredClaimIds, generatedClaimIds] using ih.cons claim.id
      | arg argument => simpa [declaredClaimIds, generatedClaimIds] using ih
      | attack attack => simpa [declaredClaimIds, generatedClaimIds] using ih
      | status status => simpa [declaredClaimIds, generatedClaimIds] using ih
      | group group => simpa [declaredClaimIds, generatedClaimIds] using ih

/-- If the complete argument and claim namespaces are duplicate-free, the
comparison-generated subnamespaces are fresh against authored declarations and
against one another. -/
theorem generatedIdsFresh_of_ids_nodup {program : Presentation.Program}
    (hargs : (argIds program).Nodup)
    (hclaims : (claimIds program).Nodup) :
    GeneratedIdsFresh program = true := by
  have hargsPartition :
      (declaredArgIds program.decls ++
        generatedArgIds (comparisonDecls program)).Nodup := by
    apply (argIds_perm_partition program.decls).nodup_iff.mp
    exact hargs
  have hclaimsPartition :
      (declaredClaimIds program.decls ++
        generatedClaimIds (comparisonDecls program)).Nodup := by
    apply (claimIds_perm_partition program.decls).nodup_iff.mp
    exact hclaims
  rw [List.nodup_append] at hargsPartition hclaimsPartition
  have hnone := generatedIdCollisionClaimAux_none_of_properties
    (declaredArgIds program.decls) (declaredClaimIds program.decls)
    [] [] (comparisonDecls program)
    hargsPartition.2.1
    (by
      intro id hid hdeclared
      exact hargsPartition.2.2 id hdeclared id hid rfl)
    (by simp)
    hclaimsPartition.2.1
    (by
      intro id hid hdeclared
      exact hclaimsPartition.2.2 id hdeclared id hid rfl)
    (by simp)
  simpa [GeneratedIdsFresh, generatedIdCollisionClaim?,
    declaredArgIds, declaredClaimIds] using hnone

private abbrev ComparisonKey :=
  Presentation.LeafId × Presentation.LeafId × Presentation.MeasurandId ×
    Presentation.DatasetId × Presentation.Relation

private def duplicateComparisonClaimAux (seen : List ComparisonKey) :
    List Presentation.Comparison → Option Presentation.PropId
  | [] => none
  | comparison :: rest =>
      if comparisonKey comparison ∈ seen then some comparison.claim.id
      else duplicateComparisonClaimAux (comparisonKey comparison :: seen) rest

/-- The later block that first repeats an earlier comparison key. -/
def duplicateComparisonClaim? (program : Presentation.Program) :
    Option Presentation.PropId :=
  duplicateComparisonClaimAux [] (comparisonDecls program)

private theorem duplicateComparisonClaimAux_none_properties
    (seen : List ComparisonKey) (blocks : List Presentation.Comparison)
    (h : duplicateComparisonClaimAux seen blocks = none) :
    let keys := blocks.map comparisonKey
    keys.Nodup ∧ ∀ key ∈ keys, key ∉ seen := by
  induction blocks generalizing seen with
  | nil => simp
  | cons comparison rest ih =>
      simp only [duplicateComparisonClaimAux] at h
      split at h
      · contradiction
      · have htail := ih (comparisonKey comparison :: seen) h
        simp_all [List.nodup_cons]

private theorem duplicateComparisonClaimAux_none_of_nodup
    (seen : List ComparisonKey) (blocks : List Presentation.Comparison)
    (hnodup : (blocks.map comparisonKey).Nodup)
    (hfresh : ∀ key ∈ blocks.map comparisonKey, key ∉ seen) :
    duplicateComparisonClaimAux seen blocks = none := by
  induction blocks generalizing seen with
  | nil => rfl
  | cons comparison rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      simp only [duplicateComparisonClaimAux]
      rw [if_neg (hfresh _ (by simp))]
      apply ih (comparisonKey comparison :: seen) hnodup.2
      intro key hkey
      simp only [List.mem_cons, not_or]
      exact ⟨fun heq => hnodup.1 (heq ▸ hkey),
        hfresh key (by simp [hkey])⟩

theorem duplicateComparisonClaim?_eq_none_iff (program : Presentation.Program) :
    duplicateComparisonClaim? program = none ↔
      (comparisonKeys program).Nodup := by
  constructor
  · intro h
    exact (duplicateComparisonClaimAux_none_properties
      [] (comparisonDecls program) (by simpa [duplicateComparisonClaim?] using h)).1
  · intro h
    exact duplicateComparisonClaimAux_none_of_nodup
      [] (comparisonDecls program) h (by simp)

/-- Expand one declaration: a `comparison` block becomes its generated
declarations, anything else is kept. -/
def expandDecls (policy : Presentation.Policy) (program : Presentation.Program) :
    List Decl → Except Surface.Error (List Decl × List GeneratedArg)
  | [] => .ok ([], [])
  | .comparison c :: rest =>
      match comparisonExpansion? program policy c with
      | none => .error (.invalidComparison c.claim.id)
      | some data =>
          match expandDecls policy program rest with
          | .error e => .error e
          | .ok (tail, tailGs) => .ok (generatedDecls data c ++ tail, generatedArgs c ++ tailGs)
  | d :: rest =>
      match expandDecls policy program rest with
      | .error e => .error e
      | .ok (tail, tailGs) => .ok (d :: tail, tailGs)

/-- Expand (and consume) every `comparison` block of a program, with the
production check order: generated-id collisions, duplicate blocks, then
per-block expansion failures.  The returned provenance list accompanies, never
enters, the semantic program. -/
def expandComparisons (policy : Presentation.Policy) (program : Presentation.Program) :
    Except Surface.Error (Presentation.Program × List GeneratedArg) :=
  match generatedIdCollisionClaim? program with
  | some claim => .error (.invalidComparison claim)
  | none =>
      match duplicateComparisonClaim? program with
      | some claim => .error (.invalidComparison claim)
      | none =>
          match expandDecls policy program program.decls with
          | .error e => .error e
          | .ok (decls, gs) => .ok ({ program with decls := decls }, gs)

/-! ### Soundness and completeness -/

private theorem expandDecls_sound (policy : Presentation.Policy) (program : Presentation.Program)
    {ds ts : List Decl} {gs : List GeneratedArg}
    (h : expandDecls policy program ds = .ok (ts, gs)) : DeclsExpandComparisons policy program ds ts gs := by
  induction ds generalizing ts gs with
  | nil =>
      simp [expandDecls] at h
      rcases h with ⟨hts, hgs⟩
      subst ts; subst gs
      exact DeclsExpandComparisons.nil
  | cons d rest ih =>
      by_cases hc : isComparison d = true
      · cases d with
        | comparison c =>
            simp [expandDecls] at h
            cases hdata : comparisonExpansion? program policy c with
            | none => exfalso; simp [hdata] at h
            | some data =>
                simp [hdata] at h
                cases hrest : expandDecls policy program rest with
                | error e => exfalso; simp [hrest] at h
                | ok pair =>
                    rcases pair with ⟨tail, tailGs⟩
                    simp [hrest] at h
                    rcases h with ⟨hts, hgs⟩
                    subst ts; subst gs
                    exact DeclsExpandComparisons.expand
                      (comparisonExpansion?_sound hdata) (ih hrest)
        | _ => simp [isComparison] at hc
      · have hkeep : isComparison d = false := by
          cases hb : isComparison d with
          | true => exfalso; exact hc hb
          | false => rfl
        cases d with
        | comparison c => simp [isComparison] at hkeep
        | leaf leaf =>
            simp [expandDecls] at h
            cases hrest : expandDecls policy program rest with
            | error e => exfalso; simp [hrest] at h
            | ok pair =>
                rcases pair with ⟨tail, tailGs⟩
                simp [hrest] at h
                rcases h with ⟨hts, hgs⟩
                subst ts; subst gs
                exact DeclsExpandComparisons.keep hkeep (ih hrest)
        | claim claim =>
            simp [expandDecls] at h
            cases hrest : expandDecls policy program rest with
            | error e => exfalso; simp [hrest] at h
            | ok pair =>
                rcases pair with ⟨tail, tailGs⟩
                simp [hrest] at h
                rcases h with ⟨hts, hgs⟩
                subst ts; subst gs
                exact DeclsExpandComparisons.keep hkeep (ih hrest)
        | arg argument =>
            simp [expandDecls] at h
            cases hrest : expandDecls policy program rest with
            | error e => exfalso; simp [hrest] at h
            | ok pair =>
                rcases pair with ⟨tail, tailGs⟩
                simp [hrest] at h
                rcases h with ⟨hts, hgs⟩
                subst ts; subst gs
                exact DeclsExpandComparisons.keep hkeep (ih hrest)
        | attack attack =>
            simp [expandDecls] at h
            cases hrest : expandDecls policy program rest with
            | error e => exfalso; simp [hrest] at h
            | ok pair =>
                rcases pair with ⟨tail, tailGs⟩
                simp [hrest] at h
                rcases h with ⟨hts, hgs⟩
                subst ts; subst gs
                exact DeclsExpandComparisons.keep hkeep (ih hrest)
        | status id =>
            simp [expandDecls] at h
            cases hrest : expandDecls policy program rest with
            | error e => exfalso; simp [hrest] at h
            | ok pair =>
                rcases pair with ⟨tail, tailGs⟩
                simp [hrest] at h
                rcases h with ⟨hts, hgs⟩
                subst ts; subst gs
                exact DeclsExpandComparisons.keep hkeep (ih hrest)
        | group group =>
            simp [expandDecls] at h
            cases hrest : expandDecls policy program rest with
            | error e => exfalso; simp [hrest] at h
            | ok pair =>
                rcases pair with ⟨tail, tailGs⟩
                simp [hrest] at h
                rcases h with ⟨hts, hgs⟩
                subst ts; subst gs
                exact DeclsExpandComparisons.keep hkeep (ih hrest)

private theorem expandDecls_complete (policy : Presentation.Policy) (program : Presentation.Program)
    {ds ts : List Decl} {gs : List GeneratedArg}
    (h : DeclsExpandComparisons policy program ds ts gs) :
    expandDecls policy program ds = .ok (ts, gs) := by
  induction h with
  | nil => rfl
  | @keep d ds ts gs hkeep hrest ih =>
      cases d with
      | comparison c => simp [isComparison] at hkeep
      | leaf leaf => simp [expandDecls, ih]
      | claim claim => simp [expandDecls, ih]
      | arg argument => simp [expandDecls, ih]
      | attack attack => simp [expandDecls, ih]
      | status id => simp [expandDecls, ih]
      | group group => simp [expandDecls, ih]
  | expand hdata hrest ih =>
      simp [expandDecls, comparisonExpansion?_complete hdata, ih]

/-- One case analysis over a successful comparison expansion, exposing the
check results and the declaration walk. -/
private theorem expandComparisons_ok_cases (policy : Presentation.Policy)
    {program target : Presentation.Program} {gs : List GeneratedArg}
    (h : expandComparisons policy program = .ok (target, gs)) :
    GeneratedIdsFresh program = true ∧ decide (comparisonKeys program).Nodup = true ∧
      ∃ decls, expandDecls policy program program.decls = .ok (decls, gs) ∧
        target = { program with decls := decls } := by
  unfold expandComparisons at h
  cases hfresh : generatedIdCollisionClaim? program with
  | some claim => simp [hfresh] at h
  | none =>
      have hfresh' : GeneratedIdsFresh program = true := by
        simpa [GeneratedIdsFresh] using hfresh
      cases hduplicate : duplicateComparisonClaim? program with
      | some claim => simp [hfresh, hduplicate] at h
      | none =>
          have hkeys : decide (comparisonKeys program).Nodup = true :=
            decide_eq_true (duplicateComparisonClaim?_eq_none_iff program |>.mp hduplicate)
          cases hgo : expandDecls policy program program.decls with
          | error e => exfalso; simp [hfresh, hduplicate, hgo] at h
          | ok pair =>
              rcases pair with ⟨decls, gs'⟩
              simp [hfresh, hduplicate, hgo] at h
              rcases h with ⟨htarget, hgs⟩
              exact ⟨hfresh', hkeys, decls, by simp [hgs] at hgo ⊢, htarget.symm⟩

theorem expandComparisons_sound (policy : Presentation.Policy)
    {program target : Presentation.Program} {gs : List GeneratedArg}
    (h : expandComparisons policy program = .ok (target, gs)) :
    ExpandsComparisons policy program target gs := by
  rcases expandComparisons_ok_cases policy h with ⟨hfresh, hkeys, decls, hgo, htarget⟩
  subst target
  have hdecls : DeclsExpandComparisons policy program program.decls decls gs :=
    expandDecls_sound policy program hgo
  refine ExpandsComparisons.intro hdecls ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem expandComparisons_eq_of_ok (policy : Presentation.Policy)
    (program target : Presentation.Program) (gs : List GeneratedArg)
    (hfresh : GeneratedIdsFresh program = true)
    (hkeys : decide (comparisonKeys program).Nodup = true)
    (hdecls : DeclsExpandComparisons policy program program.decls target.decls gs)
    (hartifact : target.artifact = program.artifact)
    (hdigest : target.digest = program.digest)
    (hpolicy : target.policy = program.policy)
    (hbackends : target.backends = program.backends)
    (hbindings : target.valueBindings = program.valueBindings) :
    expandComparisons policy program = .ok (target, gs) := by
  have hgo : expandDecls policy program program.decls = .ok (target.decls, gs) :=
    expandDecls_complete policy program hdecls
  have hcollision : generatedIdCollisionClaim? program = none := by
    simpa [GeneratedIdsFresh] using hfresh
  have hduplicate : duplicateComparisonClaim? program = none :=
    duplicateComparisonClaim?_eq_none_iff program |>.mpr (of_decide_eq_true hkeys)
  unfold expandComparisons
  simp [hcollision, hduplicate, hgo]
  cases target with
  | mk artifact digest policy backends valueBindings decls =>
      simp at hartifact hdigest hpolicy hbackends hbindings
      simp [hartifact, hdigest, hpolicy, hbackends, hbindings]

theorem expandComparisons_complete (policy : Presentation.Policy)
    {program target : Presentation.Program} {gs : List GeneratedArg}
    (hfresh : GeneratedIdsFresh program = true)
    (hwf : ComparisonsWellFormed program policy)
    (hexp : ExpandsComparisons policy program target gs) :
    expandComparisons policy program = .ok (target, gs) := by
  rcases hexp with ⟨hdecls, hartifact, hdigest, hpolicy, hbackends, hbindings⟩
  exact expandComparisons_eq_of_ok policy program target gs hfresh
    (decide_eq_true hwf.1) hdecls hartifact hdigest hpolicy hbackends hbindings

/-! ### Declaration-order preservation -/

/-- Whether a target declaration is one the expansion generated: a sub-claim or
a recheck/bridge argument. -/
def isGeneratedDecl (program : Presentation.Program) (d : Decl) : Bool :=
  match d with
  | .arg a => decide (a.id ∈ (comparisonDecls program).flatMap (fun c => [c.recheckArg, c.bridgeArg]))
  | .claim c => decide (c.id ∈ (comparisonDecls program).map (·.claim.id))
  | _ => false

private theorem isGeneratedDecl_false_of_keep {program : Presentation.Program} {d : Decl}
    (hf : GeneratedIdsFresh program = true) (hd : d ∈ program.decls)
    (hkeep : isComparison d = false) : isGeneratedDecl program d = false := by
  cases d with
  | comparison c => simp [isComparison] at hkeep
  | leaf leaf => rfl
  | claim c =>
      have hmem : c.id ∉ (comparisonDecls program).map (·.claim.id) := by
        intro hm
        have hdecl : c.id ∈ program.decls.filterMap
            (fun d => match d with | .claim c => some c.id | _ => none) := by
          exact List.mem_filterMap.mpr ⟨.claim c, hd, rfl⟩
        have hprops := generatedIdsFresh_properties hf
        exact (hprops.2.2.2 c.id hm) hdecl
      simp [isGeneratedDecl, hmem]
  | arg a =>
      have hmem : a.id ∉ (comparisonDecls program).flatMap (fun c => [c.recheckArg, c.bridgeArg]) := by
        intro hm
        have hdecl : a.id ∈ program.decls.filterMap
            (fun d => match d with | .arg a => some a.id | _ => none) := by
          exact List.mem_filterMap.mpr ⟨.arg a, hd, rfl⟩
        have hprops := generatedIdsFresh_properties hf
        exact (hprops.2.1 a.id hm) hdecl
      simp [isGeneratedDecl, hmem]
  | attack attack => rfl
  | status id => rfl
  | group group => rfl

private theorem keptDecls_eq_of_DeclsExpandComparisons {policy program ds ts gs}
    (hsub : ∀ d ∈ ds, d ∈ program.decls)
    (hf : GeneratedIdsFresh program = true)
    (h : DeclsExpandComparisons policy program ds ts gs) :
    ds.filter (fun d => !isComparison d) = ts.filter (fun d => !isGeneratedDecl program d) := by
  induction h with
  | nil => simp
  | @keep d ds ts gs hkeep hrest ih =>
      have hd : d ∈ program.decls := hsub d (by simp)
      have hgen : isGeneratedDecl program d = false := isGeneratedDecl_false_of_keep hf hd hkeep
      have hsub' : ∀ d' ∈ ds, d' ∈ program.decls := by
        intro d' hd'; exact hsub d' (List.mem_cons.mpr (Or.inr hd'))
      have hih := ih hsub'
      simp [hkeep, hgen, hih]
  | @expand c data ds ts gs hdata hrest ih =>
      have hc : c ∈ comparisonDecls program := by
        exact List.mem_filterMap.mpr ⟨.comparison c, hsub (.comparison c) (by simp), rfl⟩
      have hgenSub : isGeneratedDecl program (.claim (generatedSubClaim data c)) = true := by
        change decide (c.claim.id ∈ (comparisonDecls program).map (·.claim.id)) = true
        exact decide_eq_true (List.mem_map.mpr ⟨c, hc, rfl⟩)
      have hgenRecheck : isGeneratedDecl program (.arg (generatedRecheckArg data c)) = true := by
        change decide (c.recheckArg ∈ (comparisonDecls program).flatMap (fun c => [c.recheckArg, c.bridgeArg])) = true
        exact decide_eq_true (List.mem_flatMap.mpr ⟨c, hc, by simp⟩)
      have hgenBridge : isGeneratedDecl program (.arg (generatedBridgeArg data c)) = true := by
        change decide (c.bridgeArg ∈ (comparisonDecls program).flatMap (fun c => [c.recheckArg, c.bridgeArg])) = true
        exact decide_eq_true (List.mem_flatMap.mpr ⟨c, hc, by simp⟩)
      have hsub' : ∀ d' ∈ ds, d' ∈ program.decls := by
        intro d' hd'; exact hsub d' (List.mem_cons.mpr (Or.inr hd'))
      have hih := ih hsub'
      have hL : (.comparison c :: ds).filter (fun d => !isComparison d) =
          ds.filter (fun d => !isComparison d) := by
        simp [isComparison]
      have hR : (generatedDecls data c ++ ts).filter (fun d => !isGeneratedDecl program d) =
          ts.filter (fun d => !isGeneratedDecl program d) := by
        rw [List.filter_append]
        simp [generatedDecls, hgenSub, hgenRecheck, hgenBridge]
      rw [hL, hR]
      exact hih

theorem expandComparisons_preserves_order (policy : Presentation.Policy)
    {program target : Presentation.Program} {gs : List GeneratedArg}
    (h : expandComparisons policy program = .ok (target, gs)) :
    program.decls.filter (fun d => !isComparison d) =
      target.decls.filter (fun d => !isGeneratedDecl program d) := by
  rcases expandComparisons_ok_cases policy h with ⟨hfresh, hkeys, decls, hgo, htarget⟩
  subst target
  have hdecls : DeclsExpandComparisons policy program program.decls decls gs :=
    expandDecls_sound policy program hgo
  exact keptDecls_eq_of_DeclsExpandComparisons (fun d hd => hd) hfresh hdecls

/-! ### Generated-id accounting -/

private theorem generatedArgs_eq_of_DeclsExpandComparisons {policy program ds ts gs}
    (h : DeclsExpandComparisons policy program ds ts gs) :
    gs = (ds.filterMap (fun d => match d with | .comparison c => some c | _ => none)).flatMap
      (fun c => [⟨c.claim.id, c.recheckArg, .recheck⟩, ⟨c.claim.id, c.bridgeArg, .bridge⟩]) := by
  induction h with
  | nil => rfl
  | @keep d ds ts gs hkeep hrest ih =>
      cases d with
      | comparison c => simp [isComparison] at hkeep
      | leaf leaf => simp [ih]
      | claim claim => simp [ih]
      | arg argument => simp [ih]
      | attack attack => simp [ih]
      | status id => simp [ih]
      | group group => simp [ih]
  | expand hdata hrest ih => simp [generatedArgs, ih]

private theorem generatedArgs_nodup_of_fresh {program : Presentation.Program}
    (hf : GeneratedIdsFresh program = true) :
    ((comparisonDecls program).flatMap (fun c => [c.recheckArg, c.bridgeArg])).Nodup := by
  exact (generatedIdsFresh_properties hf).1

theorem expandComparisons_generated_ids (policy : Presentation.Policy)
    {program target : Presentation.Program} {gs : List GeneratedArg}
    (h : expandComparisons policy program = .ok (target, gs)) :
    gs = (comparisonDecls program).flatMap
      (fun c => [⟨c.claim.id, c.recheckArg, .recheck⟩, ⟨c.claim.id, c.bridgeArg, .bridge⟩]) ∧
    (gs.map (·.arg)).Nodup := by
  rcases expandComparisons_ok_cases policy h with ⟨hfresh, hkeys, decls, hgo, htarget⟩
  have hdecls : DeclsExpandComparisons policy program program.decls decls gs :=
    expandDecls_sound policy program hgo
  have hgs := generatedArgs_eq_of_DeclsExpandComparisons hdecls
  constructor
  · rw [hgs]
    congr 1
  · have hnodup := generatedArgs_nodup_of_fresh hfresh
    have hmap : gs.map (·.arg) =
        (comparisonDecls program).flatMap (fun c => [c.recheckArg, c.bridgeArg]) := by
      rw [hgs]
      simp [List.map_flatMap]
      congr 1
    rw [hmap]
    exact hnodup

/-! ### Elimination -/

private theorem no_comparison_of_DeclsExpandComparisons {policy program ds ts gs}
    (h : DeclsExpandComparisons policy program ds ts gs) :
    ts.all (fun d => !isComparison d) := by
  induction h with
  | nil => rfl
  | keep hkeep hrest ih => simp [hkeep, ih]
  | @expand c data _ _ _ hdata hrest ih =>
      rw [List.all_append]
      have hg : (generatedDecls data c).all (fun d => !isComparison d) = true := by
        simp [generatedDecls, isComparison]
      rw [hg]
      -- goal: ts.all (fun d => !isComparison d) = true
      exact ih

theorem expandComparisons_eliminates (policy : Presentation.Policy)
    {program target : Presentation.Program} {gs : List GeneratedArg}
    (h : expandComparisons policy program = .ok (target, gs)) :
    target.decls.all (fun d => !isComparison d) := by
  rcases expandComparisons_ok_cases policy h with ⟨hfresh, hkeys, decls, hgo, htarget⟩
  subst target
  have hdecls : DeclsExpandComparisons policy program program.decls decls gs :=
    expandDecls_sound policy program hgo
  exact no_comparison_of_DeclsExpandComparisons hdecls


namespace Renaming

/-- Comparison expansion reports only the typed comparison-claim id. -/
inductive ExpandComparisonsErrorRelated (ρg : Binding.GlobalRenaming) :
    Surface.Error → Surface.Error → Prop where
  | invalidComparison (claimId : Presentation.PropId) :
      ExpandComparisonsErrorRelated ρg
        (.invalidComparison claimId) (.invalidComparison (ρg.prop claimId))

/-- Rename the typed provenance emitted for one generated comparison
argument. -/
def renameGeneratedArg (ρg : Binding.GlobalRenaming)
    (generated : GeneratedArg) : GeneratedArg :=
  { generated with
    comparisonClaim := ρg.prop generated.comparisonClaim
    arg := ρg.arg generated.arg }

/-- Comparison expansion relates both the semantic program and the ordered
generated-argument provenance. -/
def GeneratedResultsRelated (ρg : Binding.GlobalRenaming)
    (source target : Presentation.Program × List GeneratedArg) : Prop :=
  SemanticProgramRelated ρg source.1 target.1 ∧
    target.2 = source.2.map (renameGeneratedArg ρg)

private def renameComparisonKey (ρg : Binding.GlobalRenaming)
    (key : ComparisonKey) : ComparisonKey :=
  (ρg.leaf key.1, ρg.leaf key.2.1, ρg.measurand key.2.2.1,
    ρg.dataset key.2.2.2.1, key.2.2.2.2)

private theorem renameComparisonKey_injective
    (ρg : Binding.GlobalRenaming) :
    Function.Injective (renameComparisonKey ρg) := by
  rintro ⟨result₁, baseline₁, measurand₁, dataset₁, relation₁⟩
    ⟨result₂, baseline₂, measurand₂, dataset₂, relation₂⟩ equal
  simp only [renameComparisonKey, Prod.mk.injEq] at equal ⊢
  exact
    ⟨ρg.leaf_injective equal.1,
      ρg.leaf_injective equal.2.1,
      ρg.measurand_injective equal.2.2.1,
      ρg.dataset_injective equal.2.2.2.1,
      equal.2.2.2.2⟩

private theorem comparisonKey_rename
    (ρg : Binding.GlobalRenaming) (values : List Presentation.ValueName)
    (comparison : Presentation.Comparison) :
    comparisonKey (Binding.renameComparison ρg values comparison) =
      renameComparisonKey ρg (comparisonKey comparison) := by
  rfl

private theorem contains_map_of_injective
    {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (injective : Function.Injective f)
    (values : List α) (value : α) :
    (values.map f).contains (f value) = values.contains value := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨candidate, member, equal⟩
    simpa [injective equal] using member
  · intro member
    exact ⟨value, member, rfl⟩

private theorem generatedIdCollisionClaimAux_rename
    (ρg : Binding.GlobalRenaming) (values : List Presentation.ValueName)
    (declaredArgs seenArgs : List Presentation.ArgId)
    (declaredClaims seenClaims : List Presentation.PropId)
    (comparisons : List Presentation.Comparison) :
    generatedIdCollisionClaimAux
        (declaredArgs.map ρg.arg) (declaredClaims.map ρg.prop)
        (seenArgs.map ρg.arg) (seenClaims.map ρg.prop)
        (comparisons.map (Binding.renameComparison ρg values)) =
      (generatedIdCollisionClaimAux declaredArgs declaredClaims
        seenArgs seenClaims comparisons).map ρg.prop := by
  induction comparisons generalizing seenArgs seenClaims with
  | nil => rfl
  | cons comparison rest ih =>
      simp only [List.map_cons, generatedIdCollisionClaimAux,
        Binding.renameComparison]
      have renamedEq :
          (decide
              (ρg.arg comparison.recheckArg =
                ρg.arg comparison.bridgeArg) : Bool) =
            decide (comparison.recheckArg = comparison.bridgeArg) :=
        decide_eq_decide.mpr ρg.arg_injective.eq_iff
      rw [renamedEq,
        contains_map_of_injective ρg.arg ρg.arg_injective,
        contains_map_of_injective ρg.arg ρg.arg_injective,
        contains_map_of_injective ρg.arg ρg.arg_injective,
        contains_map_of_injective ρg.arg ρg.arg_injective,
        contains_map_of_injective ρg.prop ρg.prop_injective,
        contains_map_of_injective ρg.prop ρg.prop_injective]
      split
      · rfl
      · simpa only [List.map_cons] using
          ih (comparison.bridgeArg :: comparison.recheckArg :: seenArgs)
            (comparison.claim.id :: seenClaims)

theorem generatedIdCollisionClaim?_rename
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program) :
    generatedIdCollisionClaim? (Binding.renameProgram ρg program) =
      (generatedIdCollisionClaim? program).map ρg.prop := by
  have args :
      ((Binding.renameProgram ρg program).decls.filterMap fun
        | .arg argument => some argument.id
        | _ => none) =
        (program.decls.filterMap fun
          | .arg argument => some argument.id
          | _ => none).map ρg.arg := by
    simp only [Binding.renameProgram]
    induction program.decls with
    | nil => rfl
    | cons declaration rest ih =>
        cases declaration <;>
          simp [Binding.renameDecl, Binding.renameArg, ih]
  have claims :
      ((Binding.renameProgram ρg program).decls.filterMap fun
        | .claim claim => some claim.id
        | _ => none) =
        (program.decls.filterMap fun
          | .claim claim => some claim.id
          | _ => none).map ρg.prop := by
    simp only [Binding.renameProgram]
    induction program.decls with
    | nil => rfl
    | cons declaration rest ih =>
        cases declaration <;>
          simp [Binding.renameDecl, ih]
  unfold generatedIdCollisionClaim?
  rw [args, claims, comparisonDecls_renameProgram]
  exact generatedIdCollisionClaimAux_rename ρg (programValues program)
    _ [] _ [] (comparisonDecls program)

private theorem duplicateComparisonClaimAux_rename
    (ρg : Binding.GlobalRenaming) (values : List Presentation.ValueName)
    (seen : List ComparisonKey)
    (comparisons : List Presentation.Comparison) :
    duplicateComparisonClaimAux (seen.map (renameComparisonKey ρg))
        (comparisons.map (Binding.renameComparison ρg values)) =
      (duplicateComparisonClaimAux seen comparisons).map ρg.prop := by
  induction comparisons generalizing seen with
  | nil => rfl
  | cons comparison rest ih =>
      simp only [List.map_cons, duplicateComparisonClaimAux,
        comparisonKey_rename]
      have member :
          renameComparisonKey ρg (comparisonKey comparison) ∈
              seen.map (renameComparisonKey ρg) ↔
            comparisonKey comparison ∈ seen := by
        simp [renameComparisonKey_injective ρg |>.eq_iff]
      by_cases duplicate : comparisonKey comparison ∈ seen
      · simp [duplicate, member.mpr duplicate, Binding.renameComparison]
      · have renamedDuplicate :
            renameComparisonKey ρg (comparisonKey comparison) ∉
              seen.map (renameComparisonKey ρg) := by
          simpa [member] using duplicate
        rw [if_neg renamedDuplicate, if_neg duplicate]
        simpa using ih (comparisonKey comparison :: seen)

theorem duplicateComparisonClaim?_rename
    (ρg : Binding.GlobalRenaming) (program : Presentation.Program) :
    duplicateComparisonClaim? (Binding.renameProgram ρg program) =
      (duplicateComparisonClaim? program).map ρg.prop := by
  unfold duplicateComparisonClaim?
  rw [comparisonDecls_renameProgram]
  exact duplicateComparisonClaimAux_rename ρg (programValues program)
    [] (comparisonDecls program)

private theorem thetaFor_rename
    (ρg : Binding.GlobalRenaming) (values : List Presentation.ValueName)
    (theta : SurfaceSubst) (rule : Presentation.Rule) :
    thetaFor (Binding.renameSubstValues ρg values theta)
        (Binding.renameRule ρg rule) =
      Binding.renameSubstValues ρg values (thetaFor theta rule) := by
  unfold thetaFor
  simp only [Binding.renameRule]
  induction rule.params with
  | nil => rfl
  | cons param rest ih =>
      simp only [List.filterMap_cons]
      rw [lookupSurfaceSubst_rename]
      cases found : lookupSurfaceSubst theta param with
      | none => simpa only [found, Option.map_none] using ih
      | some term =>
          simpa only [found, Option.map_some, Binding.renameSubstValues,
            List.map_cons] using
              congrArg
                (List.cons
                  (param, Binding.renameValueTerm ρg values term)) ih

private theorem bridgePremisesAux_rename
    (ρg : Binding.GlobalRenaming) (values : List Presentation.ValueName)
    (data : ComparisonExpansionData) (comparison : Presentation.Comparison)
    (recheck : Presentation.SupportTerm) (n : Nat)
    (acc : Presentation.SupportTerms) :
    bridgePremisesAux (renameComparisonExpansionData ρg values data)
        (Binding.renameComparison ρg values comparison)
        (Binding.renameSupportTerm ρg values recheck) n
        (Binding.renameSupportTerms ρg values acc) =
      Binding.renameSupportTerms ρg values
        (bridgePremisesAux data comparison recheck n acc) := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
      simp only [bridgePremisesAux]
      by_cases slot : n = data.bridgeComparisonSlot
      · have renamedSlot :
            n =
              (renameComparisonExpansionData ρg values data).bridgeComparisonSlot := by
          simpa [renameComparisonExpansionData] using slot
        rw [if_pos slot, if_pos renamedSlot]
        simpa [Binding.renameSupportTerm, Binding.renameSupportTerms] using
          ih (.cons recheck acc)
      · have renamedSlot :
            n ≠
              (renameComparisonExpansionData ρg values data).bridgeComparisonSlot := by
          simpa [renameComparisonExpansionData] using slot
        rw [if_neg slot, if_neg renamedSlot]
        simpa [Binding.renameComparison, Binding.renameSupportTerm,
          Binding.renameSupportTerms] using
            ih (.cons (.leaf comparison.binding) acc)

private theorem bridgePremises_rename
    (ρg : Binding.GlobalRenaming) (values : List Presentation.ValueName)
    (data : ComparisonExpansionData) (comparison : Presentation.Comparison)
    (recheck : Presentation.SupportTerm) :
    bridgePremises (renameComparisonExpansionData ρg values data)
        (Binding.renameComparison ρg values comparison)
        (Binding.renameSupportTerm ρg values recheck) =
      Binding.renameSupportTerms ρg values
        (bridgePremises data comparison recheck) := by
  unfold bridgePremises
  simp only [renameComparisonExpansionData, Binding.renameRule]
  exact bridgePremisesAux_rename ρg values data comparison recheck
    data.bridge.premises.length .nil

private theorem bridgePremisesAux_eraseNl
    (data : ComparisonExpansionData) (comparison : Presentation.Comparison)
    (recheck : Presentation.SupportTerm) :
    ∀ (n : Nat) (acc : Presentation.SupportTerms),
      bridgePremisesAux data
          { comparison with
            claim := { comparison.claim with nlRaw := "" } }
          recheck n acc =
        bridgePremisesAux data comparison recheck n acc
  | 0, _ => rfl
  | n + 1, acc => by
      simp only [bridgePremisesAux]
      split <;> exact bridgePremisesAux_eraseNl data comparison recheck n _

private theorem bridgePremises_eraseNl
    (data : ComparisonExpansionData) (comparison : Presentation.Comparison)
    (recheck : Presentation.SupportTerm) :
    bridgePremises data
        { comparison with
          claim := { comparison.claim with nlRaw := "" } }
        recheck =
      bridgePremises data comparison recheck := by
  unfold bridgePremises
  exact bridgePremisesAux_eraseNl data comparison recheck _ _

/-- Erasing an authored comparison's prose erases exactly the generated
sub-claim prose; the generated support declarations are unchanged. -/
theorem generatedDecls_eraseNl
    (data : ComparisonExpansionData)
    (comparison : Presentation.Comparison) :
    generatedDecls data
        { comparison with
          claim := { comparison.claim with nlRaw := "" } } =
      (generatedDecls data comparison).map eraseDeclNl := by
  simp only [generatedDecls, generatedSubClaim, generatedRecheckArg,
    generatedBridgeArg, eraseDeclNl, List.map_cons, List.map_nil]
  rw [bridgePremises_eraseNl]

private theorem generatedRecheckTerm_rename
    (ρg : Binding.GlobalRenaming) (values : List Presentation.ValueName)
    (data : ComparisonExpansionData) :
    generatedRecheckTerm (renameComparisonExpansionData ρg values data) =
      Binding.renameSupportTerm ρg values (generatedRecheckTerm data) := by
  unfold generatedRecheckTerm
  simp only [renameComparisonExpansionData]
  rw [thetaFor_rename]
  simp [Binding.renameRule, Binding.renameSupportTerm,
    Binding.renameSupportTerms, Binding.renameDischarges,
    Binding.renameAssurance, Binding.renameCertPayload, ordcmpPayload]

theorem generatedDecls_rename
    (ρg : Binding.GlobalRenaming) (values : List Presentation.ValueName)
    (data : ComparisonExpansionData)
    (comparison : Presentation.Comparison) :
    generatedDecls (renameComparisonExpansionData ρg values data)
        (Binding.renameComparison ρg values comparison) =
      (generatedDecls data comparison).map
        (Binding.renameDecl ρg values) := by
  simp only [generatedDecls, List.map_cons, List.map_nil,
    generatedSubClaim, generatedRecheckArg, generatedBridgeArg,
    Binding.renameDecl, Binding.renameArg]
  rw [generatedRecheckTerm_rename]
  rw [bridgePremises_rename]
  simp only [renameComparisonExpansionData]
  rw [thetaFor_rename]
  cases supports : comparison.supports <;>
    simp [supports, Binding.renameComparison, Binding.renameArgConcl,
      Binding.renameArgInstantiation, Binding.renameRule,
      Binding.renameSupportTerm, Binding.renameDischarges,
      Binding.renameAssurance]

private theorem termsFixed_nil_spelling
    (fixed : TermsFixed ρg [] terms)
    (member : spelling ∈ termsNullaryCons terms) :
    Binding.renameText ρg spelling = spelling := by
  cases terms with
  | nil => simp [termsNullaryCons] at member
  | cons term rest =>
      simp only [termsNullaryCons, List.mem_append] at member
      rcases member with headMember | tailMember
      · exact fixed term (by
          change term ∈ term :: _
          exact List.mem_cons_self) spelling headMember (by simp)
      · exact termsFixed_nil_spelling (by
          intro nested nestedMember
          exact fixed nested (by
            change nested ∈ term :: _
            exact List.mem_cons_of_mem term nestedMember)) tailMember
termination_by terms

private theorem termFixed_of_lookupSurfaceSubst
    (fixed : SubstFixed ρg [] subst)
    (found : lookupSurfaceSubst subst param = some term) :
    TermFixed ρg [] term := by
  induction subst with
  | nil => simp [lookupSurfaceSubst] at found
  | cons entry rest ih =>
      simp only [lookupSurfaceSubst, List.findSome?_cons] at found
      by_cases equal : entry.1 = param
      · rw [if_pos equal] at found
        cases found
        exact fixed entry (by simp)
      · rw [if_neg equal] at found
        exact ih (by
          intro candidate candidateMember
          exact fixed candidate (by simp [candidateMember])) found

private theorem substFixed_thetaFor
    (fixed : SubstFixed ρg [] subst) :
    SubstFixed ρg [] (thetaFor subst rule) := by
  intro entry member
  unfold thetaFor at member
  obtain ⟨param, _, selected⟩ := List.mem_filterMap.mp member
  cases found : lookupSurfaceSubst subst param with
  | none => simp [found] at selected
  | some term =>
      simp [found] at selected
      subst entry
      exact termFixed_of_lookupSurfaceSubst fixed found

private theorem bridgePremisesAux_nullaries_fixed
    (recheckFixed : SupportTermFixed ρg [] recheck)
    (accFixed : ∀ spelling ∈ supportTermsNullaryCons acc,
      Binding.renameText ρg spelling = spelling) :
    ∀ spelling ∈ supportTermsNullaryCons
        (bridgePremisesAux data comparison recheck n acc),
      Binding.renameText ρg spelling = spelling := by
  induction n generalizing acc with
  | zero => exact accFixed
  | succ n ih =>
      simp only [bridgePremisesAux]
      split
      · apply ih
        intro spelling member
        simp only [supportTermsNullaryCons, List.mem_append] at member
        rcases member with headMember | tailMember
        · exact recheckFixed spelling headMember (by simp)
        · exact accFixed spelling tailMember
      · apply ih
        intro spelling member
        simp only [supportTermsNullaryCons, supportTermNullaryCons,
          List.mem_append] at member
        rcases member with headMember | tailMember
        · contradiction
        · exact accFixed spelling tailMember

private theorem bridgePremises_nullaries_fixed
    (recheckFixed : SupportTermFixed ρg [] recheck) :
    ∀ spelling ∈ supportTermsNullaryCons
        (bridgePremises data comparison recheck),
      Binding.renameText ρg spelling = spelling := by
  unfold bridgePremises
  exact bridgePremisesAux_nullaries_fixed recheckFixed (by
    intro spelling member
    simp [supportTermsNullaryCons] at member)

private theorem bridgePremisesAux_binders_fixed
    (recheckFixed : ∀ spelling ∈ supportTermBinderSpellings recheck,
      Binding.renameText ρg spelling = spelling)
    (accFixed : ∀ spelling ∈ supportTermsBinderSpellings acc,
      Binding.renameText ρg spelling = spelling) :
    ∀ spelling ∈ supportTermsBinderSpellings
        (bridgePremisesAux data comparison recheck n acc),
      Binding.renameText ρg spelling = spelling := by
  induction n generalizing acc with
  | zero => exact accFixed
  | succ n ih =>
      simp only [bridgePremisesAux]
      split
      · apply ih
        intro spelling member
        simp only [supportTermsBinderSpellings, List.mem_append] at member
        exact member.elim (recheckFixed spelling) (accFixed spelling)
      · apply ih
        intro spelling member
        simp only [supportTermsBinderSpellings, supportTermBinderSpellings,
          List.mem_append] at member
        exact member.elim (fun impossible => False.elim (by simpa using impossible))
          (accFixed spelling)

private theorem bridgePremisesAux_opaque_fixed
    (recheckFixed : ∀ spelling ∈
      supportTermOpaqueCertPremiseSpellings recheck,
      Binding.renameText ρg spelling = spelling)
    (accFixed : ∀ spelling ∈
      supportTermsOpaqueCertPremiseSpellings acc,
      Binding.renameText ρg spelling = spelling) :
    ∀ spelling ∈ supportTermsOpaqueCertPremiseSpellings
        (bridgePremisesAux data comparison recheck n acc),
      Binding.renameText ρg spelling = spelling := by
  induction n generalizing acc with
  | zero => exact accFixed
  | succ n ih =>
      simp only [bridgePremisesAux]
      split
      · apply ih
        intro spelling member
        simp only [supportTermsOpaqueCertPremiseSpellings,
          List.mem_append] at member
        exact member.elim (recheckFixed spelling) (accFixed spelling)
      · apply ih
        intro spelling member
        simp only [supportTermsOpaqueCertPremiseSpellings,
          supportTermOpaqueCertPremiseSpellings, List.mem_append] at member
        exact member.elim (fun impossible => False.elim (by simpa using impossible))
          (accFixed spelling)

/-- Every declaration emitted by the production comparison expansion is safe
for post-expansion reconstruction.  The two complete substitutions and the
generated goal come from `ComparisonExpansionData`; the actual `ord@1`
payload contributes exactly its two numeric premise-slot spellings. -/
theorem generatedDecls_reconstruction_safe
    (numeric : ∀ n : Nat,
      Binding.renameText ρg (Nat.repr n) = Nat.repr n)
    (dataFixed : AtomFixed ρg [] data.goal ∧
      SubstFixed ρg [] data.thetaRecheck ∧
      SubstFixed ρg [] data.thetaBridge)
    (declaration : Presentation.Decl)
    (member : declaration ∈ generatedDecls data comparison) :
    (∀ spelling ∈ declNullaryCons declaration,
        Binding.renameText ρg spelling = spelling) ∧
      match declaration with
      | .arg argument =>
          (∀ spelling ∈ argBinderSpellings argument,
            Binding.renameText ρg spelling = spelling) ∧
          (∀ spelling ∈ argOpaqueCertPremiseSpellings argument,
            Binding.renameText ρg spelling = spelling)
      | _ => True := by
  have recheckThetaFixed :=
    substFixed_thetaFor (rule := data.recheck) dataFixed.2.1
  have bridgeThetaFixed :=
    substFixed_thetaFor (rule := data.bridge) dataFixed.2.2
  have recheckFixed : SupportTermFixed ρg [] (generatedRecheckTerm data) := by
    intro spelling spellingMember _
    simp only [generatedRecheckTerm, supportTermNullaryCons,
      supportTermsNullaryCons, supportDischargesNullaryCons,
      List.append_nil, List.mem_append] at spellingMember
    obtain ⟨entry, entryMember, termMember⟩ :=
      List.mem_flatMap.mp spellingMember
    exact recheckThetaFixed entry entryMember spelling termMember (by simp)
  have recheckBindersFixed : ∀ spelling ∈
      supportTermBinderSpellings (generatedRecheckTerm data),
      Binding.renameText ρg spelling = spelling := by
    intro spelling spellingMember
    simp only [generatedRecheckTerm, supportTermBinderSpellings,
      supportTermsBinderSpellings, supportDischargesBinderSpellings,
      assuranceBinderSpellings, payloadBinderSpellings,
      sxListBinderSpellings, ordcmpPayload, premRef,
      List.nil_append, List.append_nil] at spellingMember
    contradiction
  have recheckOpaqueFixed : ∀ spelling ∈
      supportTermOpaqueCertPremiseSpellings (generatedRecheckTerm data),
      Binding.renameText ρg spelling = spelling := by
    intro spelling spellingMember
    change spelling ∈ [Nat.repr data.slotLeft, Nat.repr data.slotRight] at spellingMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at spellingMember
    rcases spellingMember with rfl | rfl
    · exact numeric data.slotLeft
    · exact numeric data.slotRight
  have bridgePremisesFixed :=
    bridgePremises_nullaries_fixed (data := data) (comparison := comparison)
      recheckFixed
  have bridgeBindersFixed : ∀ spelling ∈ supportTermsBinderSpellings
      (bridgePremises data comparison (generatedRecheckTerm data)),
      Binding.renameText ρg spelling = spelling := by
    unfold bridgePremises
    exact bridgePremisesAux_binders_fixed recheckBindersFixed (by
      intro spelling member
      simp [supportTermsBinderSpellings] at member)
  have bridgeOpaqueFixed : ∀ spelling ∈
      supportTermsOpaqueCertPremiseSpellings
        (bridgePremises data comparison (generatedRecheckTerm data)),
      Binding.renameText ρg spelling = spelling := by
    unfold bridgePremises
    exact bridgePremisesAux_opaque_fixed recheckOpaqueFixed (by
      intro spelling member
      simp [supportTermsOpaqueCertPremiseSpellings] at member)
  have bridgeFixed : SupportTermFixed ρg []
      (.rule data.bridge.id (thetaFor data.thetaBridge data.bridge)
        (bridgePremises data comparison (generatedRecheckTerm data))
        .nil [] .none) := by
    intro spelling spellingMember _
    simp only [supportTermNullaryCons, supportDischargesNullaryCons,
      List.append_nil, List.mem_append] at spellingMember
    rcases spellingMember with substMember | premiseMember
    · obtain ⟨entry, entryMember, termMember⟩ :=
        List.mem_flatMap.mp substMember
      exact bridgeThetaFixed entry entryMember spelling termMember (by simp)
    · exact bridgePremisesFixed spelling premiseMember
  simp only [generatedDecls, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl
  · constructor
    · intro spelling spellingMember
      simp only [generatedSubClaim, declNullaryCons] at spellingMember
      cases data.goal with
      | atom predicate terms =>
          exact termsFixed_nil_spelling dataFixed.1 spellingMember
    · trivial
  · constructor
    · intro spelling spellingMember
      exact recheckFixed spelling (by
        simpa [declNullaryCons, generatedRecheckArg, argNullaryCons] using
          spellingMember) (by simp)
    · constructor
      · simpa [generatedRecheckArg, argBinderSpellings] using
          recheckBindersFixed
      · simpa [generatedRecheckArg, argOpaqueCertPremiseSpellings] using
          recheckOpaqueFixed
  · constructor
    · intro spelling spellingMember
      exact bridgeFixed spelling (by
        simpa [declNullaryCons, generatedBridgeArg, argNullaryCons] using
          spellingMember) (by simp)
    · constructor
      · intro spelling spellingMember
        simp only [generatedBridgeArg, argBinderSpellings,
          supportTermBinderSpellings, assuranceBinderSpellings,
          supportDischargesBinderSpellings, List.nil_append,
          List.append_nil] at spellingMember
        exact bridgeBindersFixed spelling spellingMember
      · intro spelling spellingMember
        simp only [generatedBridgeArg, argOpaqueCertPremiseSpellings,
          supportTermOpaqueCertPremiseSpellings,
          assuranceOpaqueCertPremiseSpellings,
          dischargeOpaqueCertPremiseSpellings, List.nil_append,
          List.append_nil] at spellingMember
        exact bridgeOpaqueFixed spelling spellingMember

theorem generatedArgs_rename
    (ρg : Binding.GlobalRenaming) (values : List Presentation.ValueName)
    (comparison : Presentation.Comparison) :
    generatedArgs (Binding.renameComparison ρg values comparison) =
      (generatedArgs comparison).map fun generated =>
        { generated with
          comparisonClaim := ρg.prop generated.comparisonClaim
          arg := ρg.arg generated.arg } := by
  simp [generatedArgs, Binding.renameComparison]

end Renaming

end Lara.Surface
