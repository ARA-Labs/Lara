/-
# PW-T9 witnesses

Executable examples for exact path composition, direct/path commuting
triangles (positive two- and three-edge, plus isolated negative triangles),
checker applicability and accepted-edge separation, certificate composition,
mid-path vocabulary failure, and non-empty translation lifts.
-/

import Lara.PW.Compose
import Lara.Examples.PWStructural

namespace Lara.Examples.PW.Compose

open Lara.Support
open Lara.PW
open Lara.Grounded (Status)
open Lara.Examples.PW

/-! ### A live two-leg renaming path -/

/-- The second renaming leg sends the first leg's predicate and constructor
images onward. Only the fixture constructor is in its constructor vocabulary. -/
def ren2Sym : SymMap :=
  { predMap := fun s =>
      if s = "p_r" then some "p_rr"
      else if s = "e_r" then some "e_rr"
      else none
  , conMap := fun s => if s = "payload" then some "payload_r" else none }

/-- The third policy is the second-leg translation of the intermediate policy. -/
def piRenTgt2 : RuleId → Option Rule :=
  fun rn => (piRenTgt rn).bind (trRule ren2Sym)

/-- The second leg performs another concrete leaf rename. -/
def leafMapRen2 : LeafId → LeafId := fun l => ⟨l.name ++ "-tgt2"⟩

/-- The third evidence environment admits only the twice-renamed fixture leaf. -/
def gammaRenTgt2 : LeafId → Option Atom :=
  fun l =>
    if l = leafMapRen2 (leafMapRen lRen) then some (.atom "e_rr" .nil)
    else none

/-- The rule after T6's first renaming leg. -/
def ruleRenTgt : Rule :=
  { mode := .defeasible, params := [], premises := [⟨⟨"e_r"⟩, .nil⟩]
  , concl := ⟨⟨"p_r"⟩, .nil⟩, questions := [], allowTrusted := false
  , certifiers := [] }

/-- The rule after both renaming legs. -/
def ruleRenTgt2 : Rule :=
  { mode := .defeasible, params := [], premises := [⟨⟨"e_rr"⟩, .nil⟩]
  , concl := ⟨⟨"p_rr"⟩, .nil⟩, questions := [], allowTrusted := false
  , certifiers := [] }

/-- The second structural edge, from T6's target to the twice-renamed world. -/
def bridgeRen2 :
    StructuralBridge id piRenTgt piRenTgt2 gammaRenTgt gammaRenTgt2
      certRen certRen where
  sym := ren2Sym
  leafMap := leafMapRen2
  leaf_ok := fun l p h => by
    unfold gammaRenTgt at h
    by_cases hl : l = leafMapRen lRen
    · rw [if_pos hl] at h
      cases h
      refine ⟨.atom "e_rr" .nil, rfl, ?_⟩
      rw [hl]
      unfold gammaRenTgt2
      rw [if_pos rfl]
    · rw [if_neg hl] at h
      exact nomatch h
  rule_ok := fun rn r h => by
    unfold piRenTgt piRenSrc at h
    by_cases hrn : rn = rnRen
    · rw [if_pos hrn] at h
      have h' : some ruleRenTgt = some r := h
      cases h'
      refine ⟨ruleRenTgt2, rfl, ?_⟩
      unfold piRenTgt2 piRenTgt piRenSrc
      rw [if_pos hrn]
      rfl
    · rw [if_neg hrn] at h
      exact nomatch h
  cert_ok := fun _ _ _ _ _ _ _ _ _ h => h.elim

/-- The chosen path records both live structural edges. -/
def pathRen :
    BridgePath id piRenSrc piRenTgt2 gammaRenSrc gammaRenTgt2 certRen certRen :=
  .cons bridgeRen (.cons bridgeRen2 .nil)

/-- The named direct source-to-final bridge has exactly the two-edge path's
symbol and leaf maps. Its contract is the already-proved binary composite
contract. -/
def bridgeRenDirect :
    StructuralBridge id piRenSrc piRenTgt2 gammaRenSrc gammaRenTgt2
      certRen certRen :=
  bridgeRen2.comp bridgeRen

/-- The support term after both concrete leaf renames. -/
def wRenTgt2 : SupportTerm :=
  .inst rnRen [] [.leaf (leafMapRen2 (leafMapRen lRen))] [] [] .none

/-- The second leg translates the intermediate conclusion explicitly. -/
theorem ren2_conclusion :
    trAtom ren2Sym (.atom "p_r" .nil) = some (.atom "p_rr" .nil) := rfl

/-- Stepwise path transport computes to the twice-renamed term. -/
theorem ren_path_trans :
    pathRen.trans wRen = some wRenTgt2 ∧ wRenTgt2 ≠ wRenTgt :=
  ⟨rfl, by decide⟩

/-- The live T6 derivation crosses both edges and concludes `p_rr`. -/
theorem ren_path_transport :
    HasSupport id piRenTgt2 gammaRenTgt2 certRen wRenTgt2
      (.atom "p_rr" .nil) [] := by
  obtain ⟨C', hC, h⟩ :=
    path_support_transport pathRen hasSupport_ren (w' := wRenTgt2) rfl
  have hsym : pathRen.compose.sym = ren2Sym.comp renSym := by
    change (SymMap.id.comp ren2Sym).comp renSym = ren2Sym.comp renSym
    rw [SymMap.id_comp]
  have hC' : some (Atom.atom "p_rr" .nil) = some C' := by
    rw [← hC, hsym, trAtom_comp, ren_conclusion, Option.bind_some,
      ren2_conclusion]
  cases hC'
  exact h

/-- The named direct renaming bridge commutes with the chosen live path. -/
theorem ren_path_commutes : Commutes bridgeRenDirect pathRen :=
  Commutes.of_maps_eq.mpr
    ⟨by
      change ren2Sym.comp renSym =
        (SymMap.id.comp ren2Sym).comp renSym
      rw [SymMap.id_comp],
    rfl⟩

/-- The commuting triangle makes direct and stepwise transport agree on the
live derivation: both translations conclude `p_rr`, and the common result
checks in the twice-renamed target environment. -/
theorem ren_direct_transport_agrees :
    trSupport bridgeRenDirect.sym bridgeRenDirect.leafMap wRen =
        some wRenTgt2 ∧
      trAtom bridgeRenDirect.sym (.atom "p" .nil) =
        some (.atom "p_rr" .nil) ∧
      trAtom pathRen.compose.sym (.atom "p" .nil) =
        some (.atom "p_rr" .nil) ∧
      HasSupport id piRenTgt2 gammaRenTgt2 certRen wRenTgt2
        (.atom "p_rr" .nil) [] := by
  obtain ⟨hw, C', hdirect, hpath, hchecked⟩ :=
    direct_transport_agrees bridgeRenDirect pathRen ren_path_commutes
      hasSupport_ren ren_path_trans.1
  have htarget :
      trAtom bridgeRenDirect.sym (.atom "p" .nil) =
        some (.atom "p_rr" .nil) := rfl
  rw [hdirect] at htarget
  have hC : C' = .atom "p_rr" .nil := Option.some.inj htarget
  cases hC
  exact ⟨hw, hdirect, hpath, hchecked⟩

/-! ### Length-three and theorem-level composition witnesses -/

/-- The live renaming route extended by a reflexive edge at its final
environment. The constructor shape intentionally records three edges. -/
def pathRen3 :
    BridgePath id piRenSrc piRenTgt2 gammaRenSrc gammaRenTgt2 certRen certRen :=
  .cons bridgeRen
    (.cons bridgeRen2
      (.cons
        (StructuralBridge.refl id piRenTgt2 gammaRenTgt2 certRen)
        .nil))

/-- The direct two-rename bridge commutes with the three-edge route whose
last edge is reflexive. -/
theorem ren_path3_commutes : Commutes bridgeRenDirect pathRen3 := by
  apply Commutes.of_maps_eq.mpr
  constructor
  · change bridgeRen2.sym.comp bridgeRen.sym =
      ((SymMap.id.comp SymMap.id).comp bridgeRen2.sym).comp bridgeRen.sym
    rw [SymMap.id_comp, SymMap.id_comp]
  · rfl

/-- Direct and three-step transport agree on the live support and translated
claim, including the common checked target judgment. -/
theorem ren_path3_transport_agrees :
    pathRen3.trans wRen = some wRenTgt2 ∧
      trSupport bridgeRenDirect.sym bridgeRenDirect.leafMap wRen =
        some wRenTgt2 ∧
      trAtom bridgeRenDirect.sym (.atom "p" .nil) =
        some (.atom "p_rr" .nil) ∧
      trAtom pathRen3.compose.sym (.atom "p" .nil) =
        some (.atom "p_rr" .nil) ∧
      HasSupport id piRenTgt2 gammaRenTgt2 certRen wRenTgt2
        (.atom "p_rr" .nil) [] := by
  have hpath : pathRen3.trans wRen = some wRenTgt2 := rfl
  obtain ⟨hdirect, C', hdirectClaim, hpathClaim, hchecked⟩ :=
    direct_transport_agrees bridgeRenDirect pathRen3 ren_path3_commutes
      hasSupport_ren hpath
  have htarget :
      trAtom bridgeRenDirect.sym (.atom "p" .nil) =
        some (.atom "p_rr" .nil) := rfl
  rw [hdirectClaim] at htarget
  have hC : C' = .atom "p_rr" .nil := Option.some.inj htarget
  cases hC
  exact ⟨hpath, hdirect, hdirectClaim, hpathClaim, hchecked⟩

/-- `support_transport_comp` exposes both live translations and both checked
judgments instead of hiding the intermediate environment. -/
theorem ren_support_transport_comp :
    trSupport bridgeRen.sym bridgeRen.leafMap wRen = some wRenTgt ∧
      trSupport bridgeRen2.sym bridgeRen2.leafMap wRenTgt =
        some wRenTgt2 ∧
      trSupport (bridgeRen2.comp bridgeRen).sym
          (bridgeRen2.comp bridgeRen).leafMap wRen =
        some wRenTgt2 ∧
      trAtom bridgeRen.sym (.atom "p" .nil) =
        some (.atom "p_r" .nil) ∧
      trAtom bridgeRen2.sym (.atom "p_r" .nil) =
        some (.atom "p_rr" .nil) ∧
      trAtom (bridgeRen2.comp bridgeRen).sym (.atom "p" .nil) =
        some (.atom "p_rr" .nil) ∧
      HasSupport id piRenTgt gammaRenTgt certRen wRenTgt
          (.atom "p_r" .nil) [] ∧
      HasSupport id piRenTgt2 gammaRenTgt2 certRen wRenTgt2
        (.atom "p_rr" .nil) [] := by
  have hw₁ :
      trSupport bridgeRen.sym bridgeRen.leafMap wRen = some wRenTgt := rfl
  have hw₂ :
      trSupport bridgeRen2.sym bridgeRen2.leafMap wRenTgt =
        some wRenTgt2 := rfl
  obtain ⟨hcomp, C', C'', hC₁, hC₂, hCcomp, hmid, hfinal⟩ :=
    support_transport_comp bridgeRen2 bridgeRen hasSupport_ren hw₁ hw₂
  have hC' : C' = .atom "p_r" .nil := by
    apply Option.some.inj
    exact hC₁.symm.trans rfl
  subst C'
  have hC'' : C'' = .atom "p_rr" .nil := by
    apply Option.some.inj
    exact hC₂.symm.trans rfl
  subst C''
  exact ⟨hw₁, hw₂, hcomp, hC₁, hC₂, hCcomp, hmid, hfinal⟩

/-- The common target policy makes direct and path-composite translations of
the live source rule equal. -/
theorem ren_commutes_on_rule :
    piRenSrc rnRen = some ruleRen ∧
      trRule bridgeRenDirect.sym ruleRen =
        trRule pathRen.compose.sym ruleRen := by
  have hsrc : piRenSrc rnRen = some ruleRen := by
    simp [piRenSrc]
  exact ⟨hsrc, commutes_on_rules bridgeRenDirect pathRen hsrc⟩

/-- The admitted source leaf and its known map equality make direct and
path-composite translations of the live evidence atom equal. -/
theorem ren_commutes_on_leaf :
    gammaRenSrc lRen = some (.atom "e" .nil) ∧
      bridgeRenDirect.leafMap lRen = pathRen.compose.leafMap lRen ∧
      trAtom bridgeRenDirect.sym (.atom "e" .nil) =
        trAtom pathRen.compose.sym (.atom "e" .nil) := by
  have hsrc : gammaRenSrc lRen = some (.atom "e" .nil) := by
    simp [gammaRenSrc]
  have hleaf :
      bridgeRenDirect.leafMap lRen = pathRen.compose.leafMap lRen :=
    ren_path_commutes.leafMap_eq lRen
  exact
    ⟨hsrc, hleaf,
      commutes_on_leaves bridgeRenDirect pathRen hleaf hsrc⟩

/-- The live rename exercises the predicate-map and full symbol-map equalities
extracted from `Commutes`. -/
theorem ren_commutes_on_symbol_maps :
    bridgeRenDirect.sym.predMap "p" = pathRen.compose.sym.predMap "p" ∧
      bridgeRenDirect.sym.predMap "e" = pathRen.compose.sym.predMap "e" ∧
      bridgeRenDirect.sym = pathRen.compose.sym :=
  ⟨ren_path_commutes.predMap_eq "p", ren_path_commutes.predMap_eq "e",
    ren_path_commutes.sym_eq⟩

/-! ### Concrete applicability and accepted-edge witnesses -/

/-- The identity structural bridge over the existing T7 checking context. -/
def bridgeIdT7 :
    StructuralBridge ctxT7.canon ctxT7.policy.ruleLookup
      ctxT7.policy.ruleLookup ctxT7.Gamma ctxT7.Gamma
      ctxT7.CertOk ctxT7.CertOk :=
  .refl ctxT7.canon ctxT7.policy.ruleLookup ctxT7.Gamma ctxT7.CertOk

/-- Two explicit identity edges over the existing T7 checking context. -/
def pathIdT7 :
    BridgePath ctxT7.canon ctxT7.policy.ruleLookup ctxT7.policy.ruleLookup
      ctxT7.Gamma ctxT7.Gamma ctxT7.CertOk ctxT7.CertOk :=
  .cons bridgeIdT7 (.cons bridgeIdT7 .nil)

/-- The target T7 world admits itself under identity translation. -/
theorem admitsSelfT7 :
    Admits bridgeIdT7.sym bridgeIdT7.leafMap wT7tgt wT7tgt := by
  intro t ht
  refine ⟨t, ?_, ht⟩
  simpa [bridgeIdT7, StructuralBridge.refl] using trSupport_id t

/-- The chosen middle world and both admitted identity legs instantiate
`admits_steps_of_intermediate`. -/
theorem t7_admits_steps_of_intermediate :
    Admits bridgeIdT7.sym bridgeIdT7.leafMap wT7src wT7tgt ∧
      Admits bridgeIdT7.sym bridgeIdT7.leafMap wT7tgt wT7tgt ∧
      AdmitsSteps bridgeIdT7 bridgeIdT7 wT7src wT7tgt := by
  have hsrc :
      Admits bridgeIdT7.sym bridgeIdT7.leafMap wT7src wT7tgt := by
    simpa [bridgeIdT7, StructuralBridge.refl] using admitsIdT7
  exact
    ⟨hsrc, admitsSelfT7,
      admits_steps_of_intermediate bridgeIdT7 bridgeIdT7 wT7tgt
        hsrc admitsSelfT7⟩

/-- Composite applicability is exactly the explicit two-step predicate for
the two T7 identity bridges. -/
theorem t7_admits_comp_iff :
    Admits (bridgeIdT7.comp bridgeIdT7).sym
        (bridgeIdT7.comp bridgeIdT7).leafMap wT7src wT7tgt ↔
      AdmitsSteps bridgeIdT7 bridgeIdT7 wT7src wT7tgt := by
  exact admits_comp bridgeIdT7 bridgeIdT7 wT7src wT7tgt

/-- The reverse direction of `admits_comp` gives an inhabited composite
applicability judgment. -/
theorem t7_admits_composite :
    Admits (bridgeIdT7.comp bridgeIdT7).sym
      (bridgeIdT7.comp bridgeIdT7).leafMap wT7src wT7tgt := by
  exact t7_admits_comp_iff.mpr t7_admits_steps_of_intermediate.2.2

/-- The direct identity edge commutes with the explicit two-edge identity
path. -/
theorem t7_identity_path_commutes : Commutes bridgeIdT7 pathIdT7 := by
  apply Commutes.of_maps_eq.mpr
  constructor
  · change SymMap.id = (SymMap.id.comp SymMap.id).comp SymMap.id
    rw [SymMap.id_comp, SymMap.id_comp]
  · rfl

/-- Direct and path applicability are equivalent at the existing T7 source
and target worlds. -/
theorem t7_admits_iff_of_commutes :
    Admits bridgeIdT7.sym bridgeIdT7.leafMap wT7src wT7tgt ↔
      Admits pathIdT7.compose.sym pathIdT7.compose.leafMap wT7src wT7tgt := by
  exact
    admits_iff_of_commutes t7_identity_path_commutes wT7src wT7tgt

/-- The caller-owned direct candidate relation used by the positive acceptance
witness. It is independent of checker-tied applicability. -/
def candidateDirectT7 :
    Instance.World ctxT7 → Instance.World ctxT7 → Prop :=
  fun _ _ => True

/-- The matching path candidate relation used by the positive equivalence. -/
def candidatePathT7 :
    Instance.World ctxT7 → Instance.World ctxT7 → Prop :=
  fun _ _ => True

/-- Candidate-relation coherence is supplied independently of bridge
commutation. -/
theorem t7_candidate_relations_agree :
    candidateDirectT7 wT7src wT7tgt ↔ candidatePathT7 wT7src wT7tgt := by
  simp [candidateDirectT7, candidatePathT7]

/-- `accepted_iff_of_commutes` combines the separately supplied candidate
clause with path applicability; the right side displays `R ∧ Admits`
explicitly. -/
theorem t7_accepted_iff_of_commutes :
    Accepted candidateDirectT7 bridgeIdT7.sym bridgeIdT7.leafMap
        wT7src wT7tgt ↔
      candidatePathT7 wT7src wT7tgt ∧
        Admits pathIdT7.compose.sym pathIdT7.compose.leafMap
          wT7src wT7tgt := by
  change
    Accepted candidateDirectT7 bridgeIdT7.sym bridgeIdT7.leafMap
        wT7src wT7tgt ↔
      Accepted candidatePathT7 pathIdT7.compose.sym
        pathIdT7.compose.leafMap wT7src wT7tgt
  exact
    accepted_iff_of_commutes t7_identity_path_commutes
      candidateDirectT7 candidatePathT7 wT7src wT7tgt
      t7_candidate_relations_agree

/-- Both accepted sides are inhabited: candidate truth and applicability are
proved independently before being combined. -/
theorem t7_accepted_inhabited :
    Accepted candidateDirectT7 bridgeIdT7.sym bridgeIdT7.leafMap
        wT7src wT7tgt ∧
      Accepted candidatePathT7 pathIdT7.compose.sym pathIdT7.compose.leafMap
        wT7src wT7tgt := by
  have hsrc :
      Admits bridgeIdT7.sym bridgeIdT7.leafMap wT7src wT7tgt := by
    simpa [bridgeIdT7, StructuralBridge.refl] using admitsIdT7
  refine ⟨⟨?_, hsrc⟩, ⟨?_, t7_admits_iff_of_commutes.mp hsrc⟩⟩
  · simp [candidateDirectT7]
  · simp [candidatePathT7]

/-- A commuting path does not make caller-owned candidate relations agree:
applicability holds on both routes, but a false path relation still prevents
acceptance. -/
def candidatePathFalseT7 :
    Instance.World ctxT7 → Instance.World ctxT7 → Prop :=
  fun _ _ => False

theorem t7_accepted_needs_candidate_coherence :
    Commutes bridgeIdT7 pathIdT7 ∧
      Accepted candidateDirectT7 bridgeIdT7.sym bridgeIdT7.leafMap
        wT7src wT7tgt ∧
      ¬ Accepted candidatePathFalseT7 pathIdT7.compose.sym
        pathIdT7.compose.leafMap wT7src wT7tgt := by
  refine ⟨t7_identity_path_commutes, t7_accepted_inhabited.1, ?_⟩
  intro h
  exact h.1

/-! ### Failing path triangles isolate the content of `Commutes` -/

/-- The first admitted leaf in the twin-leaf fixture. -/
def lA : LeafId := ⟨"tw-a"⟩

/-- The second admitted leaf in the twin-leaf fixture. -/
def lB : LeafId := ⟨"tw-b"⟩

/-- Two leaves carrying the same non-vacuous evidence atom. -/
def gammaTwin : LeafId → Option Atom :=
  fun l =>
    if l = lA then some (.atom "e" .nil)
    else if l = lB then some (.atom "e" .nil)
    else none

/-- The empty policy isolates evidence-leaf behavior. -/
def piEmpty : RuleId → Option Rule := fun _ => none

/-- A contract-valid endobridge that swaps the equally typed twin leaves. -/
def bridgeSwap :
    StructuralBridge id piEmpty piEmpty gammaTwin gammaTwin certRen certRen where
  sym := SymMap.id
  leafMap := fun l => if l = lA then lB else if l = lB then lA else l
  leaf_ok := fun l p h => by
    unfold gammaTwin at h ⊢
    by_cases ha : l = lA
    · rw [if_pos ha] at h
      cases h
      exact ⟨_, trAtom_id _, by simp [ha, lA, lB]⟩
    · rw [if_neg ha] at h
      by_cases hb : l = lB
      · rw [if_pos hb] at h
        cases h
        exact ⟨_, trAtom_id _, by simp [hb, lA, lB]⟩
      · rw [if_neg hb] at h
        exact nomatch h
  rule_ok := fun _ _ h => nomatch h
  cert_ok := fun _ _ _ _ _ _ _ _ _ h => h.elim

/-- The competing twin-leaf route consists of two explicit identity edges. -/
def twinIdentityPath :
    BridgePath id piEmpty piEmpty gammaTwin gammaTwin certRen certRen :=
  .cons (StructuralBridge.refl id piEmpty gammaTwin certRen)
    (.cons (StructuralBridge.refl id piEmpty gammaTwin certRen) .nil)

/-- The leaf witness isolates the support-map equation required by
`Commutes`: both routes succeed and check, but choose different leaves. -/
theorem direct_ne_composed_support :
    twinIdentityPath.trans (.leaf lA) = some (.leaf lA) ∧
      trSupport bridgeSwap.sym bridgeSwap.leafMap (.leaf lA) =
        some (.leaf lB) ∧
      (SupportTerm.leaf lB) ≠ .leaf lA ∧
      HasSupport id piEmpty gammaTwin certRen (.leaf lA)
        (.atom "e" .nil) [] ∧
      HasSupport id piEmpty gammaTwin certRen (.leaf lB)
        (.atom "e" .nil) [] ∧
      ¬ Commutes bridgeSwap twinIdentityPath := by
  refine ⟨rfl, ?_, by decide, .leaf ?_, .leaf ?_, ?_⟩
  · simp [trSupport, bridgeSwap, lA, lB]
  · simp [gammaTwin]
  · simp [gammaTwin, lA, lB]
  · intro hc
    have h := hc.support_eq (.leaf lA)
    change some (SupportTerm.leaf lB) = some (SupportTerm.leaf lA) at h
    have hne : (some (SupportTerm.leaf lB) : Option SupportTerm) ≠
        some (SupportTerm.leaf lA) := by decide
    exact hne h


/-! ### Non-vacuous certificate composition -/

/-- The third certificate judgment accepts only the twice-translated step. -/
def certCertTgt2 :
    BackendId → Digest → CertRef → List Atom → Atom → Prop :=
  fun β hd κ As C =>
    β = βRen ∧ hd = hdRen ∧ κ = κRen ∧
      As = [.atom "e_rr" .nil] ∧ C = .atom "p_rr" .nil

/-- The second certificate edge translates another live acceptance point. -/
def bridgeCert2 :
    StructuralBridge id piCertTgt
      (fun rn => (piCertTgt rn).bind (trRule ren2Sym))
      gammaRenTgt gammaRenTgt2 certCertTgt certCertTgt2 where
  sym := ren2Sym
  leafMap := leafMapRen2
  leaf_ok := fun l p h => by
    unfold gammaRenTgt at h
    by_cases hl : l = leafMapRen lRen
    · rw [if_pos hl] at h
      cases h
      refine ⟨.atom "e_rr" .nil, rfl, ?_⟩
      rw [hl]
      unfold gammaRenTgt2
      rw [if_pos rfl]
    · rw [if_neg hl] at h
      exact nomatch h
  rule_ok := fun rn r h => by
    unfold piCertTgt piCertSrc at h
    by_cases hrn : rn = rnCert
    · rw [if_pos hrn] at h
      cases h
      refine ⟨_, rfl, ?_⟩
      unfold piCertTgt piCertSrc
      rw [if_pos hrn]
      rfl
    · rw [if_neg hrn] at h
      exact nomatch h
  cert_ok := fun β hd κ As C As' C' hAs hC hacc => by
    obtain ⟨hβ, hhd, hκ, hAs0, hC0⟩ := hacc
    subst hβ; subst hhd; subst hκ; subst hAs0; subst hC0
    have hAs' : As' = [.atom "e_rr" .nil] := by
      have he : trAtoms ren2Sym [.atom "e_r" .nil] =
          some [.atom "e_rr" .nil] := rfl
      rw [he] at hAs
      exact (Option.some.inj hAs).symm
    have hC' : C' = .atom "p_rr" .nil := by
      have hp : trAtom ren2Sym (.atom "p_r" .nil) =
          some (.atom "p_rr" .nil) := rfl
      rw [hp] at hC
      exact (Option.some.inj hC).symm
    exact ⟨rfl, rfl, rfl, hAs', hC'⟩

/-- Two live certificate edges composed through the intermediate acceptance. -/
def certCompBridge :
    StructuralBridge id piCertSrc
      (fun rn => (piCertTgt rn).bind (trRule ren2Sym))
      gammaRenSrc gammaRenTgt2 certCertSrc certCertTgt2 :=
  bridgeCert2.comp bridgeCert

/-- The composite `cert_ok` chains two substantive certificate judgments. -/
theorem certComp_two_live_legs :
    certCertSrc βRen hdRen κRen [.atom "e" .nil] (.atom "p" .nil) ∧
      certCertTgt2 βRen hdRen κRen
        [.atom "e_rr" .nil] (.atom "p_rr" .nil) := by
  have hsrc :
      certCertSrc βRen hdRen κRen [.atom "e" .nil] (.atom "p" .nil) :=
    cert_accept_translated.2.2.1
  refine ⟨hsrc, ?_⟩
  exact certCompBridge.cert_ok βRen hdRen κRen
    [.atom "e" .nil] (.atom "p" .nil)
    [.atom "e_rr" .nil] (.atom "p_rr" .nil) rfl rfl hsrc

/-! ### A real path with a mid-path vocabulary gap -/

/-- The gap edge recognizes `p_r`, omits `e_r`, and rejects the constructor
image produced by `ren2Sym`. -/
def gapSym : SymMap :=
  { predMap := fun s => if s = "p_r" then some "p_g" else none
  , conMap := fun s => if s = "payload_r" then none else some s }

/-- Empty policy used to isolate the path's vocabulary behavior. -/
def piGapEmpty : RuleId → Option Rule := fun _ => none

/-- Empty evidence environment used to isolate vocabulary behavior. -/
def gammaGapEmpty : LeafId → Option Atom := fun _ => none

/-- Empty certificate environment used by both gap-path edges. -/
def certGapEmpty : BackendId → Digest → CertRef → List Atom → Atom → Prop :=
  fun _ _ _ _ _ => False

/-- A direct symbol map that changes only predicate translation. Constructor
translation remains the identity used by the competing path. -/
def claimOnlySym : SymMap :=
  { predMap := fun s => if s = "e" then some "e2" else some s
  , conMap := some }

/-- A vacuous-environment bridge whose leaf and constructor maps are identity;
only its predicate map differs from the competing path. -/
def claimOnlyBridge :
    StructuralBridge id piGapEmpty piGapEmpty gammaGapEmpty gammaGapEmpty
      certGapEmpty certGapEmpty where
  sym := claimOnlySym
  leafMap := id
  leaf_ok := fun _ _ h => by simp [gammaGapEmpty] at h
  rule_ok := fun _ _ h => by simp [piGapEmpty] at h
  cert_ok := fun _ _ _ _ _ _ _ _ _ h => h.elim

/-- The competing claim route consists of two explicit identity edges. -/
def claimIdentityPath :
    BridgePath id piGapEmpty piGapEmpty gammaGapEmpty gammaGapEmpty
      certGapEmpty certGapEmpty :=
  .cons
    (StructuralBridge.refl id piGapEmpty gammaGapEmpty certGapEmpty)
    (.cons
      (StructuralBridge.refl id piGapEmpty gammaGapEmpty certGapEmpty) .nil)

/-- The negative claim triangle isolates `Commutes.atom_eq`: leaf maps and
constructor maps agree, a constructor-bearing support translates identically,
and only predicate translation differs. -/
theorem direct_ne_composed_claim :
    claimOnlyBridge.leafMap = claimIdentityPath.compose.leafMap ∧
      claimOnlyBridge.sym.conMap = claimIdentityPath.compose.sym.conMap ∧
      trSupport claimOnlyBridge.sym claimOnlyBridge.leafMap
        (.inst ⟨"r"⟩ [(⟨"X"⟩, .con "k" .nil)] [] [] [] .none) =
        some (.inst ⟨"r"⟩ [(⟨"X"⟩, .con "k" .nil)] [] [] [] .none) ∧
      claimIdentityPath.trans
        (.inst ⟨"r"⟩ [(⟨"X"⟩, .con "k" .nil)] [] [] [] .none) =
        some (.inst ⟨"r"⟩ [(⟨"X"⟩, .con "k" .nil)] [] [] [] .none) ∧
      trAtom claimOnlyBridge.sym (.atom "e" .nil) =
        some (.atom "e2" .nil) ∧
      trAtom claimIdentityPath.compose.sym (.atom "e" .nil) =
        some (.atom "e" .nil) ∧
      ¬ Commutes claimOnlyBridge claimIdentityPath := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · funext k
    rfl
  · intro hc
    have h := hc.atom_eq (.atom "e" .nil)
    change some (Atom.atom "e2" .nil) = some (Atom.atom "e" .nil) at h
    have hne : (some (Atom.atom "e2" .nil) : Option Atom) ≠
        some (Atom.atom "e" .nil) := by decide
    exact hne h

/-- A vacuous structural edge carrying T6's real first renaming map. -/
def gapBridgeRen :
    StructuralBridge id piGapEmpty piGapEmpty gammaGapEmpty gammaGapEmpty
      certGapEmpty certGapEmpty where
  sym := renSym
  leafMap := id
  leaf_ok := fun _ _ h => by simp [gammaGapEmpty] at h
  rule_ok := fun _ _ h => by simp [piGapEmpty] at h
  cert_ok := fun _ _ _ _ _ _ _ _ _ h => h.elim

/-- A vacuous structural edge carrying the second renaming map. -/
def gapBridgeRen2 :
    StructuralBridge id piGapEmpty piGapEmpty gammaGapEmpty gammaGapEmpty
      certGapEmpty certGapEmpty where
  sym := ren2Sym
  leafMap := id
  leaf_ok := fun _ _ h => by simp [gammaGapEmpty] at h
  rule_ok := fun _ _ h => by simp [piGapEmpty] at h
  cert_ok := fun _ _ _ _ _ _ _ _ _ h => h.elim

/-- The second structural edge carries the map with the `e_r` vocabulary gap. -/
def gapBridgeDrop :
    StructuralBridge id piGapEmpty piGapEmpty gammaGapEmpty gammaGapEmpty
      certGapEmpty certGapEmpty where
  sym := gapSym
  leafMap := id
  leaf_ok := fun _ _ h => by simp [gammaGapEmpty] at h
  rule_ok := fun _ _ h => by simp [piGapEmpty] at h
  cert_ok := fun _ _ _ _ _ _ _ _ _ h => h.elim

/-- First applicability edge: rename the constructor carried by a checked
substitution from `gap-src` to `gap-mid`. -/
def gapConFirstSym : SymMap :=
  { predMap := some
  , conMap := fun k => if k = "gap-src" then some "gap-mid" else some k }

/-- Second applicability edge: deliberately omit the first edge's constructor
image from its vocabulary. -/
def gapConDropSym : SymMap :=
  { predMap := some
  , conMap := fun k => if k = "gap-mid" then none else some k }


/-- Minimal checked rule whose substitution carries the constructor used by
the applicability-gap witness. -/
def gapAppRuleId : RuleId := ⟨"gap-app"⟩
def gapAppVar : VarId := ⟨"X"⟩
def gapAppRule : Rule :=
  { mode := .defeasible
  , params := [gapAppVar]
  , premises := []
  , concl := ⟨⟨"gap-p"⟩, .cons (.var gapAppVar) .nil⟩
  , questions := []
  , allowTrusted := false
  , certifiers := [] }

def gapAppSigma : Lara.Sigma.Sigma :=
  { sorts := ["GapItem"]
  , cons :=
      [ ⟨⟨"gap-src"⟩, [], .decl "GapItem"⟩
      , ⟨⟨"gap-mid"⟩, [], .decl "GapItem"⟩ ]
  , preds := [⟨⟨"gap-p"⟩, [.decl "GapItem"]⟩] }

def gapAppPolicy : Lara.Policy.Policy :=
  { rules := [⟨gapAppRuleId, gapAppRule⟩]
  , defeat := ⟨[], []⟩ }

def gapAppSupport : SupportTerm :=
  .inst gapAppRuleId [(gapAppVar, .con "gap-src" .nil)] [] [] [] .none

def gapAppAtom : Atom :=
  .atom "gap-p" (.cons (.con "gap-src" .nil) .nil)

def gapAppRegistry : BackendRegistry id := fun _ => none

def gapAppUnit : Lara.Unit :=
  { sigma := gapAppSigma
  , policy := gapAppPolicy
  , args := [gapAppSupport]
  , atts := [] }

def gapAppUnitCheck :=
  Lara.Check.Unit.checkUnit gammaGapEmpty gapAppRegistry [gapAppAtom] gapAppUnit

theorem gapAppUnit_accepted : gapAppUnitCheck.isOk = true := by decide

def gapAppAccepted :
    Lara.Unit.CheckedUnit id gammaGapEmpty (certOkOf gapAppRegistry) :=
  gapAppUnitCheck.toOption.get (by decide)

def gapAppContext : Instance.Context :=
  { canon := id
  , Gamma := gammaGapEmpty
  , CertOk := certOkOf gapAppRegistry
  , sigma := gapAppSigma
  , policy := gapAppPolicy }

/-- The first applicability bridge uses the checked world's actual policy,
evidence environment, and certificate relation at both endpoints. -/
def gapConFirstBridge :
    StructuralBridge gapAppContext.canon
      gapAppContext.policy.ruleLookup gapAppContext.policy.ruleLookup
      gapAppContext.Gamma gapAppContext.Gamma
      gapAppContext.CertOk gapAppContext.CertOk where
  sym := gapConFirstSym
  leafMap := id
  leaf_ok := fun _ _ h => by
    simp [gapAppContext, gammaGapEmpty] at h
  rule_ok := fun rn r h => by
    by_cases hrn : rn = gapAppRuleId
    · subst rn
      simp [gapAppContext, gapAppPolicy, Lara.Policy.Policy.ruleLookup,
        Lara.Policy.lookupRuleDecl] at h
      subst r
      refine ⟨gapAppRule, rfl, ?_⟩
      simp [gapAppContext, gapAppPolicy, Lara.Policy.Policy.ruleLookup,
        Lara.Policy.lookupRuleDecl]
    · have hcontra : gapAppRuleId ≠ rn := fun heq => hrn heq.symm
      simp [gapAppContext, gapAppPolicy, Lara.Policy.Policy.ruleLookup,
        Lara.Policy.lookupRuleDecl, hcontra] at h
  cert_ok := fun _ _ _ _ _ _ _ _ _ h => by
    simp [gapAppContext, gapAppRegistry, certOkOf] at h

/-- The second applicability bridge is tied to the same checked context while
omitting the first edge's constructor image. -/
def gapConDropBridge :
    StructuralBridge gapAppContext.canon
      gapAppContext.policy.ruleLookup gapAppContext.policy.ruleLookup
      gapAppContext.Gamma gapAppContext.Gamma
      gapAppContext.CertOk gapAppContext.CertOk where
  sym := gapConDropSym
  leafMap := id
  leaf_ok := fun _ _ h => by
    simp [gapAppContext, gammaGapEmpty] at h
  rule_ok := fun rn r h => by
    by_cases hrn : rn = gapAppRuleId
    · subst rn
      simp [gapAppContext, gapAppPolicy, Lara.Policy.Policy.ruleLookup,
        Lara.Policy.lookupRuleDecl] at h
      subst r
      refine ⟨gapAppRule, rfl, ?_⟩
      simp [gapAppContext, gapAppPolicy, Lara.Policy.Policy.ruleLookup,
        Lara.Policy.lookupRuleDecl]
    · have hcontra : gapAppRuleId ≠ rn := fun heq => hrn heq.symm
      simp [gapAppContext, gapAppPolicy, Lara.Policy.Policy.ruleLookup,
        Lara.Policy.lookupRuleDecl, hcontra] at h
  cert_ok := fun _ _ _ _ _ _ _ _ _ h => by
    simp [gapAppContext, gapAppRegistry, certOkOf] at h

def gapAppWorld : Instance.World gapAppContext :=
  { unit := gapAppAccepted, sigma_eq := rfl, policy_eq := rfl }

def gapAppSupportMid : SupportTerm :=
  .inst gapAppRuleId [(gapAppVar, .con "gap-mid" .nil)] [] [] [] .none

/-- Exact applicability fails when the first edge translates a checked
constructor-bearing support and the second edge omits that constructor image.
The explicit step predicate and the composite `Admits` judgment fail together.
-/
theorem gap_admits_comp_fails :
    trSupport gapConFirstBridge.sym gapConFirstBridge.leafMap gapAppSupport =
        some gapAppSupportMid ∧
      trSupport gapConDropBridge.sym gapConDropBridge.leafMap gapAppSupportMid =
        none ∧
      ¬ AdmitsSteps gapConDropBridge gapConFirstBridge gapAppWorld gapAppWorld ∧
      ¬ Admits (gapConDropBridge.comp gapConFirstBridge).sym
        (gapConDropBridge.comp gapConFirstBridge).leafMap
        gapAppWorld gapAppWorld := by
  have hnotSteps :
      ¬ AdmitsSteps gapConDropBridge gapConFirstBridge
        gapAppWorld gapAppWorld := by
    intro hsteps
    obtain ⟨t', t'', ht₁, ht₂, _⟩ :=
      hsteps gapAppSupport (by decide)
    change some gapAppSupportMid = some t' at ht₁
    have ht' : t' = gapAppSupportMid := (Option.some.inj ht₁).symm
    subst t'
    change none = some t'' at ht₂
    exact nomatch ht₂
  refine ⟨rfl, rfl, hnotSteps, ?_⟩
  intro hadm
  exact hnotSteps
    ((admits_comp gapConDropBridge gapConFirstBridge
      gapAppWorld gapAppWorld).mp hadm)

/-- A typed two-edge path whose gap occurs only after the first edge succeeds. -/
def gapPath :
    BridgePath id piGapEmpty piGapEmpty gammaGapEmpty gammaGapEmpty
      certGapEmpty certGapEmpty :=
  .cons gapBridgeRen (.cons gapBridgeDrop .nil)

/-- A three-edge path whose final edge rejects the constructor image produced
by the first two edges. -/
def gapSupportPath :
    BridgePath id piGapEmpty piGapEmpty gammaGapEmpty gammaGapEmpty
      certGapEmpty certGapEmpty :=
  .cons gapBridgeRen (.cons gapBridgeRen2 (.cons gapBridgeDrop .nil))

/-- The first edge succeeds, the second rejects its image, and the named path
composite therefore rejects the source atom. -/
theorem mid_path_out_of_vocabulary :
    trAtom renSym (.atom "e" .nil) = some (.atom "e_r" .nil) ∧
      trAtom gapSym (.atom "e_r" .nil) = none ∧
      trAtom gapPath.compose.sym (.atom "e" .nil) = none :=
  ⟨rfl, rfl, rfl⟩

/-- The comparison layer reports a translation gap as incomparability. -/
theorem mid_path_translationUndefined {W : Type}
    (candidates : List W) (acceptB : W → Bool)
    (statusOf : W → Atom → Status) :
    crossCompare (trAtom gapPath.compose.sym (.atom "e" .nil)) candidates
      acceptB statusOf = .incomparable .translationUndefined := by
  rw [mid_path_out_of_vocabulary.2.2]
  exact compare_none candidates acceptB statusOf

/-! ### Non-empty computations for the lifted maps -/

/-- A non-empty ground substitution carried through both renaming maps. -/
def substRenSrc : Subst :=
  [(⟨"X"⟩, .con "payload" (.cons (.str "value") .nil))]

/-- The first-leg substitution result (constructors are retained by `renSym`). -/
def substRenTgt : Subst :=
  [(⟨"X"⟩, .con "payload" (.cons (.str "value") .nil))]

/-- The second-leg substitution result has a genuinely renamed constructor. -/
def substRenTgt2 : Subst :=
  [(⟨"X"⟩, .con "payload_r" (.cons (.str "value") .nil))]

/-- Both legs and their composite execute on a genuinely non-empty substitution. -/
theorem trSubst_nonempty_computes :
    trSubst renSym substRenSrc = some substRenTgt ∧
      trSubst ren2Sym substRenTgt = some substRenTgt2 ∧
      trSubst (ren2Sym.comp renSym) substRenSrc = some substRenTgt2 ∧
      trSubst (ren2Sym.comp renSym) substRenSrc =
        (trSubst renSym substRenSrc).bind (trSubst ren2Sym) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A constructor pattern containing a variable, before either edge. -/
def patRenSrc : Pat :=
  .con ⟨"payload"⟩ (.cons (.var ⟨"Y"⟩) .nil)

/-- The first edge retains the constructor pattern. -/
def patRenTgt : Pat :=
  .con ⟨"payload"⟩ (.cons (.var ⟨"Y"⟩) .nil)

/-- The second edge renames the constructor while retaining the variable. -/
def patRenTgt2 : Pat :=
  .con ⟨"payload_r"⟩ (.cons (.var ⟨"Y"⟩) .nil)

/-- The pattern lifts execute their constructor, variable, and non-empty-list
branches, and the composite agrees with the two legs. -/
theorem trPat_nonempty_computes :
    trPat renSym patRenSrc = some patRenTgt ∧
      trPat ren2Sym patRenTgt = some patRenTgt2 ∧
      trPat (ren2Sym.comp renSym) patRenSrc =
        (trPat renSym patRenSrc).bind (trPat ren2Sym) ∧
      trPats (ren2Sym.comp renSym) (.cons patRenSrc .nil) =
        (trPats renSym (.cons patRenSrc .nil)).bind (trPats ren2Sym) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Support transport succeeds through both renaming edges, then fails when
the third edge rejects the running substitution's constructor image. -/
theorem mid_path_support_undefined :
    trSupport renSym id
        (.inst rnRen substRenSrc [.leaf lRen] [] [] .none) =
        some (.inst rnRen substRenTgt [.leaf lRen] [] [] .none) ∧
      trSupport ren2Sym id
          (.inst rnRen substRenTgt [.leaf lRen] [] [] .none) =
        some (.inst rnRen substRenTgt2 [.leaf lRen] [] [] .none) ∧
      trSupport gapSym id
          (.inst rnRen substRenTgt2 [.leaf lRen] [] [] .none) = none ∧
      gapSupportPath.trans
          (.inst rnRen substRenSrc [.leaf lRen] [] [] .none) = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A non-empty question whose answer predicate is renamed on each edge. -/
def questionRenSrc : Question :=
  { name := ⟨"q-ren"⟩, answer := ⟨⟨"e"⟩, .nil⟩, mandatory := true }

/-- The question after T6's first predicate renaming. -/
def questionRenTgt : Question :=
  { name := ⟨"q-ren"⟩, answer := ⟨⟨"e_r"⟩, .nil⟩, mandatory := true }

/-- The question after the second predicate renaming. -/
def questionRenTgt2 : Question :=
  { name := ⟨"q-ren"⟩, answer := ⟨⟨"e_rr"⟩, .nil⟩, mandatory := true }

/-- Both legs and their composite execute on a non-empty question list. -/
theorem trQuestions_nonempty_computes :
    trQuestions renSym [questionRenSrc] = some [questionRenTgt] ∧
      trQuestions ren2Sym [questionRenTgt] = some [questionRenTgt2] ∧
      trQuestions (ren2Sym.comp renSym) [questionRenSrc] =
        some [questionRenTgt2] ∧
      trQuestions (ren2Sym.comp renSym) [questionRenSrc] =
        (trQuestions renSym [questionRenSrc]).bind (trQuestions ren2Sym) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A concrete non-empty discharge map at the source leaf. -/
def supportDisRenSrc : List (QuestionId × SupportTerm) :=
  [(⟨"q-ren"⟩, .leaf lRen)]

/-- The discharge map after the first leaf renaming. -/
def supportDisRenTgt : List (QuestionId × SupportTerm) :=
  [(⟨"q-ren"⟩, .leaf (leafMapRen lRen))]

/-- The discharge map after both leaf renamings. -/
def supportDisRenTgt2 : List (QuestionId × SupportTerm) :=
  [(⟨"q-ren"⟩, .leaf (leafMapRen2 (leafMapRen lRen)))]

/-- Both legs and their composite execute on a non-empty discharge list. -/
theorem trSupportDis_nonempty_computes :
    trSupportDis renSym leafMapRen supportDisRenSrc = some supportDisRenTgt ∧
      trSupportDis ren2Sym leafMapRen2 supportDisRenTgt =
        some supportDisRenTgt2 ∧
      trSupportDis (ren2Sym.comp renSym) (leafMapRen2 ∘ leafMapRen)
        supportDisRenSrc = some supportDisRenTgt2 ∧
      trSupportDis (ren2Sym.comp renSym) (leafMapRen2 ∘ leafMapRen)
          supportDisRenSrc =
        (trSupportDis renSym leafMapRen supportDisRenSrc).bind
          (trSupportDis ren2Sym leafMapRen2) :=
  ⟨rfl, rfl, rfl, rfl⟩


/-! ### Focused witnesses for the remaining composition laws (issue #235) -/

/-- `trAtom_comp_none_left` on a concrete first-leg vocabulary gap: `q` is
outside `renSym`'s predicate vocabulary, and the gap survives composition
with `ren2Sym` — by computation. -/
theorem first_leg_gap_computes :
    trAtom renSym (.atom "q" .nil) = none ∧
      trAtom (ren2Sym.comp renSym) (.atom "q" .nil) = none :=
  ⟨rfl, rfl⟩

/-- The same composite gap, this time *derived* by `trAtom_comp_none_left`
from the first-leg gap, pinning the law itself on concrete data. -/
theorem first_leg_gap_law :
    trAtom (ren2Sym.comp renSym) (.atom "q" .nil) = none :=
  trAtom_comp_none_left (m₂ := ren2Sym) first_leg_gap_computes.1

/-- `SymMap.id_comp` at the non-identity partial map `ren2Sym`, with the
composite's action pinned on a predicate hit, a predicate miss, a
constructor hit, and a constructor miss. -/
theorem id_comp_ren2 :
    SymMap.id.comp ren2Sym = ren2Sym ∧
      (SymMap.id.comp ren2Sym).predMap "p_r" = some "p_rr" ∧
      (SymMap.id.comp ren2Sym).predMap "ghost" = none ∧
      (SymMap.id.comp ren2Sym).conMap "payload" = some "payload_r" ∧
      (SymMap.id.comp ren2Sym).conMap "ghost" = none :=
  ⟨SymMap.id_comp ren2Sym, rfl, rfl, rfl, rfl⟩

/-- `SymMap.comp_id` at the same non-identity partial map, same four pins. -/
theorem comp_id_ren2 :
    ren2Sym.comp SymMap.id = ren2Sym ∧
      (ren2Sym.comp SymMap.id).predMap "p_r" = some "p_rr" ∧
      (ren2Sym.comp SymMap.id).predMap "ghost" = none ∧
      (ren2Sym.comp SymMap.id).conMap "payload" = some "payload_r" ∧
      (ren2Sym.comp SymMap.id).conMap "ghost" = none :=
  ⟨SymMap.comp_id ren2Sym, rfl, rfl, rfl, rfl⟩
end Lara.Examples.PW.Compose
