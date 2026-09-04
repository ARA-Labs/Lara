/-
# PW-T9 foundation witnesses

Executable examples for two-edge structural paths, certificate composition,
mid-path vocabulary failure, and the non-empty translation lifts.
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

end Lara.Examples.PW.Compose
