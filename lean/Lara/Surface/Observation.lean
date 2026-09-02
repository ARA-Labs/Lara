/-
Direct surface observation and coherence with checked compilation.

The direct framework reads only the retained surface carrier: its argument
declaration order, lowered argument rows, and resolved surface attacks.  It is
therefore available before framework compilation.  The accepted surface
derivation and unit-check result then prove that this independently constructed
framework agrees with the compiled core on its carrier and attacks.
-/

import Lara.Surface.Correctness
import Lara.Observation

namespace Lara.Surface

open Lara
open Lara.Grounded
open Lara.Semantics

variable {canon : String → String}

/-! ### Direct surface framework and claim -/

/-- The surface attack decision at two retained declaration-order positions.
It consumes the resolved surface attacks directly. -/
def directAttack (output : Elaborated canon) (i j : Nat) : Bool :=
  match output.unit.args[i]?, output.unit.args[j]? with
  | some source, some target =>
      Compile.coveredB output.resolvedAttacks source target
  | _, _ => false

/-- The AF exposed by an accepted surface derivation before framework
compilation. Node identity is the retained surface declaration position. -/
def directAF {env : Env canon} {input : Input} {output : Elaborated canon}
    (_h : Checks env input output) : AF where
  args := List.range output.argIds.length
  attack := directAttack output

/-- Optional lookup shared only as a list primitive; the direct and core
ledgers supplied to it are independently defined. -/
def lookupClaim? (claims : List (Presentation.PropId × Claim))
    (claimId : Presentation.PropId) : Option Claim :=
  (claims.find? fun row => decide (row.1 = claimId)).map Prod.snd

/-- Core-side optional lookup over the retained elaborated claim ledger. -/
def coreClaim? (output : Elaborated canon)
    (claimId : Presentation.PropId) : Option Claim :=
  lookupClaim? output.claims claimId

/-- Independently recompute the surface claim ledger from the derivation's
semantic program and source reconstruction. No field reads `output.claims`. -/
def directClaims (env : Env canon) (input : Input)
    (output : Elaborated canon) : List (Presentation.PropId × Claim) :=
  match reconstructArgs env output.semanticProgram input.policy
      output.semanticProgram.decls [] with
  | .error _ => []
  | .ok pairs =>
      claimsOf (keptReconstructed canon input.policy output.semanticProgram pairs)
        output.semanticProgram

/-- Surface-side optional lookup. A missing declaration stays `none`; it is
not converted into an empty-support `gap` claim. -/
def directClaim {env : Env canon} {input : Input} {output : Elaborated canon}
    (_h : Checks env input output)
    (claimId : Presentation.PropId) : Option Claim :=
  lookupClaim? (directClaims env input output) claimId

/-- The direct carrier is exactly the declaration-order index range of the
retained surface argument identifiers. -/
theorem directAF_args {env : Env canon} {input : Input} {output : Elaborated canon}
    (h : Checks env input output) :
    (directAF h).args = List.range output.argIds.length :=
  rfl

/-- Unfolding a direct edge exposes only the retained lowered arguments and the
resolved surface attacks. -/
theorem directAF_attack_iff {env : Env canon} {input : Input}
    {output : Elaborated canon} (h : Checks env input output) (i j : Nat) :
    (directAF h).attack i j = true ↔
      (match output.unit.args[i]?, output.unit.args[j]? with
       | some source, some target =>
           Compile.coveredB output.resolvedAttacks source target = true
       | _, _ => False) := by
  cases hsource : output.unit.args[i]? <;>
    cases htarget : output.unit.args[j]? <;>
  simp [directAF, directAttack, hsource, htarget]

/-! ### Alignment supplied by an accepted surface derivation -/

private theorem claimsOf_support_lt
    (pairs : List ReconstructedArgument) (program : Presentation.Program)
    {claimId : Presentation.PropId} {claim : Claim}
    (hclaim : (claimId, claim) ∈ claimsOf pairs program) :
    ∀ i ∈ claim.support, i < pairs.length := by
  unfold claimsOf at hclaim
  obtain ⟨declaration, _, hrow⟩ := List.mem_map.mp hclaim
  cases hrow
  intro i hi
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hi
  have hsupporting : entry ∈
      pairs.zipIdx.filter fun (pair, _) =>
        argSupportsClaim declaration.id pair.argument.concl :=
    (List.mem_filter.mp hentry).1
  have hzip : entry ∈ pairs.zipIdx := (List.mem_filter.mp hsupporting).1
  exact List.snd_lt_of_mem_zipIdx hzip

private theorem af_eq {F G : AF} (hargs : F.args = G.args)
    (hattack : F.attack = G.attack) : F = G := by
  cases F
  cases G
  simp_all

/-- The independently reconstructed surface ledger agrees with the retained
core-side ledger on an accepted derivation. -/
theorem directClaims_eq_claims {env : Env canon} {input : Input}
    {output : Elaborated canon} (h : Checks env input output) :
    directClaims env input output = output.claims := by
  rcases h.program with
    ⟨pairs, _, hprogram, _, _, _, _, _, hclaims, _⟩
  have hfold := reconstructArgs_complete hprogram
  simp [directClaims, hfold, hclaims]

theorem directClaim_eq_coreClaim? {env : Env canon} {input : Input}
    {output : Elaborated canon} (h : Checks env input output)
    (claimId : Presentation.PropId) :
    directClaim h claimId = coreClaim? output claimId := by
  simp [directClaim, coreClaim?, directClaims_eq_claims h]

/-- Every argument supporting a direct claim is inside the direct carrier.  The
bound is derived from `Checks`: both the claim indices and the argument-ID order
come from the same retained reconstructed rows. -/
theorem directClaim_support_bound {env : Env canon} {input : Input}
    {output : Elaborated canon} (h : Checks env input output)
    (claimId : Presentation.PropId) {claim : Claim}
    (hclaim : directClaim h claimId = some claim) :
    ∀ i ∈ claim.support, i ∈ (directAF h).args := by
  rcases h.program with
    ⟨pairs, _, _, _, _, _, hids, _, hclaims, _⟩
  rw [directClaim_eq_coreClaim? h] at hclaim
  unfold coreClaim? lookupClaim? at hclaim
  cases hfind : output.claims.find? (fun row => decide (row.1 = claimId)) with
  | none => simp [hfind] at hclaim
  | some row =>
    simp only [hfind, Option.map_some, Option.some.injEq] at hclaim
    subst claim
    intro i hi
    have hrow : row ∈ output.claims := List.mem_of_find?_eq_some hfind
    have hrow' : row ∈ claimsOf
        (keptReconstructed canon input.policy output.semanticProgram pairs)
        output.semanticProgram := by
      rw [hclaims]
      exact hrow
    have hlt := claimsOf_support_lt _ _ hrow' i hi
    rw [directAF_args h, List.mem_range]
    rw [← hids, List.length_map]
    exact hlt

/-- The direct surface framework and checked compilation are exactly equal.
The equality is earned from the surface argument-order/attack preservation
fields and the accepted unit's raw-list correspondence. -/
theorem direct_compiled_agree {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked) :
    directAF hsurface = Compile.checkedAF checked.program := by
  rcases hsurface.program with
    ⟨pairs, _, _, _, _, _, hids, hargs, _, _⟩
  rcases Check.Unit.checkUnit_sound hchecked with
    ⟨_, _, _, _, _, _, _, _, hcheckedArgs, hcheckedAttacks, _, _⟩
  have hlength : output.argIds.length = output.unit.args.length := by
    rw [← hids, ← hargs, List.length_map, List.length_map]
  apply af_eq
  · simp [directAF, Compile.checkedAF, Compile.toAF, hcheckedArgs, hlength]
  · funext i j
    simp [directAF, directAttack, Compile.checkedAF, Compile.toAF,
      Compile.edgeB, hcheckedArgs, hcheckedAttacks,
      ← hsurface.unitAttacks]
    rfl

/-! ### Semantics-parametric observation coherence -/

/-- Optional direct surface observation. Missing claims remain missing. -/
def observe (sem : ExtensionSemantics)
    {env : Env canon} {input : Input} {output : Elaborated canon}
    (h : Checks env input output) (claimId : Presentation.PropId) :
    Option ClaimObservation :=
  (directClaim h claimId).map (Semantics.observe sem (directAF h))

/-- Direct surface observation agrees with checked compilation for every
carrier-local extension semantics. -/
theorem observe_coherent (sem : ExtensionSemantics)
    (hext : Observation.AttackExtensional sem.spec)
    {env : Env canon} {input : Input} {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    (claimId : Presentation.PropId) :
    Lara.Surface.observe sem hsurface claimId =
      (coreClaim? output claimId).map
        (Semantics.observe sem (Compile.checkedAF checked.program)) := by
  unfold Lara.Surface.observe
  rw [directClaim_eq_coreClaim? hsurface,
    direct_compiled_agree hsurface hchecked]

/-- Grounded observation coherence (`groundedSem.spec` is `LeastComplete`). -/
theorem observe_grounded_coherent {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    (claimId : Presentation.PropId) :
    Lara.Surface.observe groundedSem hsurface claimId =
      (coreClaim? output claimId).map
        (Semantics.observe groundedSem (Compile.checkedAF checked.program)) :=
  observe_coherent groundedSem Observation.attackExtensional_leastComplete
    hsurface hchecked claimId

/-- Complete-semantics observation coherence. -/
theorem observe_complete_coherent {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    (claimId : Presentation.PropId) :
    Lara.Surface.observe completeSem hsurface claimId =
      (coreClaim? output claimId).map
        (Semantics.observe completeSem (Compile.checkedAF checked.program)) :=
  observe_coherent completeSem Observation.attackExtensional_complete
    hsurface hchecked claimId

/-- Preferred-semantics observation coherence. -/
theorem observe_preferred_coherent {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    (claimId : Presentation.PropId) :
    Lara.Surface.observe preferredSem hsurface claimId =
      (coreClaim? output claimId).map
        (Semantics.observe preferredSem (Compile.checkedAF checked.program)) :=
  observe_coherent preferredSem Observation.attackExtensional_preferred
    hsurface hchecked claimId

/-- Stable-semantics observation coherence, including `noExtension`. -/
theorem observe_stable_coherent {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    (claimId : Presentation.PropId) :
    Lara.Surface.observe stableSem hsurface claimId =
      (coreClaim? output claimId).map
        (Semantics.observe stableSem (Compile.checkedAF checked.program)) :=
  observe_coherent stableSem Observation.attackExtensional_stable
    hsurface hchecked claimId

/-- Semi-stable-semantics observation coherence. -/
theorem observe_semiStable_coherent {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    (claimId : Presentation.PropId) :
    Lara.Surface.observe semiStableSem hsurface claimId =
      (coreClaim? output claimId).map
        (Semantics.observe semiStableSem (Compile.checkedAF checked.program)) :=
  observe_coherent semiStableSem Observation.attackExtensional_semiStable
    hsurface hchecked claimId

/-! ### The support premise is load-bearing -/

/-- A would-be direct claim whose sole support lies outside the retained
carrier used by the generic congruence counterexample. -/
def unboundedDirectClaim : Claim := Observation.claimJunkSupport

/-- The witness really violates the support premise: argument `7` is not in the
retained carrier `[0]`. -/
theorem unboundedDirectClaim_support_unaligned :
    ¬ (∀ i ∈ unboundedDirectClaim.support,
        i ∈ Observation.oneNoAttack.args) := by
  decide

/-- Dropping direct support alignment makes observation coherence false even
when the two frameworks have the same carrier and agree on every carrier edge. -/
theorem not_observe_coherent_of_unbounded_support :
    Semantics.observe groundedSem Observation.oneNoAttack unboundedDirectClaim ≠
      Semantics.observe groundedSem Observation.oneAttacksJunk unboundedDirectClaim :=
  Observation.not_observe_congr_of_unbounded_support

end Lara.Surface
