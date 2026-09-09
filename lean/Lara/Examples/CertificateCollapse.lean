/-
# A collapsing certificate relation changes a grounded observation (#275)

Two defeasible wrappers differ only in their nested certificate payload. An
explicit undercut defeats one wrapper. Collapsing the payloads identifies the
wrappers, so the remaining support for the export disappears. The fixture
backend is a sound ND adapter that interprets every payload as `slot1Cert`;
its replay, soundness, and dependency accounting all inherit that interpretation.
It is an example registry, not a change to the production ND decoder.
-/
import Lara.Examples.Linking
import Lara.Context.Parametricity

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Lara.Examples.CertificateCollapse

open Lara.Support Lara.Attack Lara.Compile Lara.Check Lara.Erase
open Lara.Context hiding Context
open Lara.Examples.Linking

/-- Direct replay of the fixed decoded certificate avoids decimal-parser opacity. -/
def replaySlot (Γ : List Lara.ND.Formula) (φ : Lara.ND.Formula) : Bool :=
  match Lara.ND.infer Γ [] (.hyp 1) with
  | some (conclusion, _) => conclusion == φ
  | none => false

theorem replaySlot_eq (Γ : List Lara.ND.Formula) (φ : Lara.ND.Formula) :
    replaySlot Γ φ = Lara.Strict.ndReplay slot1Cert Γ φ := by
  have hn : Lara.ND.decodeNat "1" = some 1 := Lara.ND.decodeNat_repr 1
  simp [Lara.Strict.ndReplay, slot1Cert, Lara.ND.decodeCert, Lara.ND.Tag.parse, hn,
    replaySlot]
  rfl

/-- A deliberately non-injective certificate representation, with ND soundness. -/
def aliasCore : Lara.Strict.Backend id :=
  { Lara.Strict.ndBackend id with
    acceptsFull := fun _ => (Lara.Strict.ndBackend id).acceptsFull slot1Cert
    replayFull := fun _ => replaySlot
    replayFull_iff := fun _ Γ φ => by
      rw [replaySlot_eq]; exact (Lara.Strict.ndBackend id).replayFull_iff slot1Cert Γ φ
    soundFull := fun _ => (Lara.Strict.ndBackend id).soundFull slot1Cert
    uses := fun _ => (Lara.Strict.ndBackend id).uses slot1Cert
    uses_covers := fun _ Γ Γ' φ h => by
      rw [replaySlot_eq, replaySlot_eq]
      exact (Lara.Strict.ndBackend id).uses_covers slot1Cert Γ Γ' φ h
    uses_valid := fun _ => (Lara.Strict.ndBackend id).uses_valid slot1Cert
    uses_account := fun _ => (Lara.Strict.ndBackend id).uses_account slot1Cert }

def aliasRegistered : RegisteredBackend id :=
  { core := aliasCore, resolveTheory := ndRegistered.resolveTheory }

def registry : BackendRegistry id := fun _ => some aliasRegistered

/-- Keep identities and digests fixed; only the payload loses information. -/
def collapse : Assurance → Assurance
  | .cert β h _ => .cert β h slot1Cert
  | α => α

def wrapRule : Rule := { ruleWrap with premises := [apB], concl := apA }

def policy : Policy.Policy :=
  { rules := [⟨rCertId, ruleCertBoth⟩, ⟨rWrapId, wrapRule⟩]
    defeat := ⟨[], [(rWrapId, apS)]⟩ }

def certified (κ : CertRef) : SupportTerm :=
  .inst rCertId [] [.leaf l1] [] [] (.cert ndId digestA κ)

def wrapped (κ : CertRef) : SupportTerm :=
  .inst rWrapId [] [certified κ] [] [] .none

def ctx : Lara.Context.Context :=
  ⟨{ certCtx.frame with policy := policy, args := [] }⟩

def sourceFrag : Fragment :=
  { certFrag with
    policy := policy
    args := [wrapped slot1Cert, wrapped rejectCert, .leaf l3]
    atts := [.undercut (.leaf l3) (wrapped slot1Cert) []]
    imports := ⟨[l1, l3]⟩, exports := [pA] }

def targetFrag : Fragment := mapAssurFrag collapse sourceFrag


/-- Both sides reach the semantic projection, and the same export changes status. -/
theorem observations :
    obs registry ctx sourceFrag = .observed [Grounded.Status.justified] ∧
    obs registry ctx targetFrag = .observed [Grounded.Status.defeated] ∧
    obs registry ctx sourceFrag ≠ obs registry ctx targetFrag := by decide

/-- The collapse preserves acceptance even for arbitrary rule declarations. -/
theorem preserving :
    RelPreserving (graphOf collapse) (certOkOf registry) (certOkOf registry) := by
  apply relPreserving_graphOf
  intro r As C α h
  cases h with
  | defeasible hm => exact .defeasible hm
  | trusted hm ht => exact .trusted hm ht
  | cert hm ha hc => exact .cert hm ha hc

/-- The relation is single-valued, but it does not reflect equality. -/
theorem not_relInj : ¬ RelInj (graphOf collapse) := by
  intro h
  have heq := (h (.cert ndId digestA slot1Cert) (.cert ndId digestA rejectCert)
    (.cert ndId digestA slot1Cert) (.cert ndId digestA slot1Cert) rfl rfl).mpr rfl
  exact absurd heq (by decide)

theorem related : RelFrag (graphOf collapse) sourceFrag targetFrag :=
  relFrag_graphOf collapse sourceFrag

theorem fixes_context : RelFixesContext (graphOf collapse) ctx :=
  ⟨.nil, .nil⟩

/-- All source arguments check, including both distinct certificate payloads. -/
theorem source_support :
    ∀ w ∈ sourceFrag.args, ∃ C,
      HasSupport id policy.ruleLookup (linkGamma ctx sourceFrag) (certOkOf registry) w C [] := by
  intro w hw
  have h : w = wrapped slot1Cert ∨ w = wrapped rejectCert ∨ w = .leaf l3 := by
    simpa [sourceFrag] using hw
  rcases h with rfl | rfl | rfl
  · refine ⟨pA, ?_⟩
    exact inferSupport_sound (loc := .root) (result := ⟨pA, []⟩) (by rfl)
  · refine ⟨pA, ?_⟩
    exact inferSupport_sound (loc := .root) (result := ⟨pA, []⟩) (by rfl)
  · refine ⟨pC, ?_⟩
    exact inferSupport_sound (loc := .root) (result := ⟨pC, []⟩) (by rfl)

/-- No root contrary pairs exist. The explicitly declared undercut is typed;
attack completeness does not require saturation of every possible exception. -/
theorem source_sideOk :
    SideOk id registry (linkGamma ctx sourceFrag) policy sourceFrag.args sourceFrag.atts where
  support := source_support
  typed := by
    intro k hk
    have h : k = .undercut (.leaf l3) (wrapped slot1Cert) [] := by
      simpa [sourceFrag] using hk
    subst h
    exact checkAttack_sound (by rfl)
  source_declared := by
    intro k hk
    simp [sourceFrag] at hk
    subst k
    simp [Attack.source, sourceFrag]
  target_declared := by
    intro k hk
    simp [sourceFrag] at hk
    subst k
    simp [Attack.target, sourceFrag]
  attack_complete := by
    intro source hs target ht Cs Ct hCs hCt hcontrary _
    simp [ContraryMatch, policy] at hcontrary

/-- The source satisfies every admissibility premise of parametricity. -/
theorem admissible : Admissible registry ctx sourceFrag where
  guard := by decide
  ctx := {
    support := by intro w hw; simp [ctx] at hw
    typed := by intro k hk; simp [ctx, certCtx] at hk
    source_declared := by intro k hk; simp [ctx, certCtx] at hk
    target_declared := by intro k hk; simp [ctx, certCtx] at hk
    attack_complete := by intro source hs; simp [ctx] at hs }
  frag := source_sideOk
  signature := signatureStage_link (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  scope := by decide
  ruleIds := by decide
  policy := Policy.firstViolation_none_iff.mp (by decide)

/-- Both links are accepted; the separation is neither a guard nor checker failure. -/
theorem accepted :
    (Unit.checkUnit (linkGamma ctx sourceFrag) registry (linkGround ctx sourceFrag)
      (linkedUnit registry ctx sourceFrag)).isOk = true ∧
    (Unit.checkUnit (linkGamma ctx targetFrag) registry (linkGround ctx targetFrag)
      (linkedUnit registry ctx targetFrag)).isOk = true := by decide

/-- Three source arguments become two, while the attacked wrapper remains. -/
theorem linked_shape :
    (linkedUnit registry ctx sourceFrag).args =
      [wrapped slot1Cert, wrapped rejectCert, .leaf l3] ∧
    (linkedUnit registry ctx targetFrag).args = [wrapped slot1Cert, .leaf l3] ∧
    sourceFrag.exports = targetFrag.exports := by decide

/-- Every premise except `RelInj`, together with the negated conclusion. -/
theorem relInj_observationally_necessary :
    ¬ RelInj (graphOf collapse) ∧
    RelPreserving (graphOf collapse) (certOkOf registry) (certOkOf registry) ∧
    Admissible registry ctx sourceFrag ∧
    RelFrag (graphOf collapse) sourceFrag targetFrag ∧
    RelFixesContext (graphOf collapse) ctx ∧
    obs registry ctx sourceFrag ≠ obs registry ctx targetFrag :=
  ⟨not_relInj, preserving, admissible, related, fixes_context, observations.2.2⟩

end Lara.Examples.CertificateCollapse
