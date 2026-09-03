/-
# PW-T6 executable examples (issue #191, tracker #189)

Two instances of the structural-bridge contract, one boundary fact, and the
translation-domain negative.

**The identity endobridge at the T7 pair.** `StructuralBridge.refl` at
`ctxT7`'s environment, with `Admits` discharged by the T7 fixtures: every
argument of the source program transports (identically) into the target
program. `t7_t6_boundary` then packages the T6/T8 boundary at a live
instance: exact checked-support transport *succeeds* across this bridge and
grounded status *still* flips from `justified` to `defeated` — T6 is
necessary, not sufficient, for status preservation, exactly what
`t7_witness` showed before T6 existed.

**A genuine renaming bridge.** A one-rule environment whose target policy is
the *translated* policy under a predicate renaming `p ↦ p_r`, `e ↦ e_r`, and
whose evidence typing carries a *renamed* leaf. The transport theorem carries
the source instance derivation across, concluding the renamed claim in the
target environment — the vocabulary machinery of `Lara.PW.Translation`
exercised off the identity. Two of the contract's three clauses are
discharged non-vacuously here: `rule_ok` by the translated policy and
`leaf_ok` by the renamed leaf at the translated atom. `cert_ok` still has no
off-identity witness — it needs a strict rule with a live certifier
allowlist, tracked as #224.

**The domain negative.** The renaming is partial: the source-only claim `q`
has no translation, and the executable comparison reports exactly
`translationUndefined` — the bridge-domain arm of PW0's `gap` separation,
now reachable from a structural bridge's own translation.
-/

import Lara.PW.Structural
import Lara.Examples.PW

namespace Lara.Examples.PW

open Lara.Support Lara.Check.Unit
open Lara.PW Lara.PW.Instance
open Lara.Grounded (Status)

/-! ### The identity endobridge at the T7 pair -/

/-- The T7 pair admits the identity transport: the source program's one
argument, `leaf l1`, is (identically) an argument of the target program. -/
theorem admitsIdT7 :
    Admits SymMap.id (fun l => l) wT7src wT7tgt := by
  intro t hmem
  refine ⟨t, trSupport_id t, ?_⟩
  have hmem' : t ∈ acceptedT7src.program.args := hmem
  have hsrc : acceptedT7src.program.args = [.leaf l1] := by decide
  rw [hsrc] at hmem'
  show t ∈ acceptedT7tgt.program.args
  rw [List.mem_singleton.mp hmem']
  exact t7_transport_wellFormed

/-- **T6 at the T7 pair.** Across the identity endobridge, every argument of
the source world's accepted program transports to a checked, complete member
of the target world's accepted program with the (identity-)translated
conclusion. -/
theorem t7_t6_transport :
    ∀ t, t ∈ wT7src.unit.program.args →
      ∃ t' C C', t' ∈ wT7tgt.unit.program.args ∧
        trSupport SymMap.id (fun l => l) t = some t' ∧
        trAtom SymMap.id C = some C' ∧
        HasSupport ctxT7.canon ctxT7.policy.ruleLookup ctxT7.Gamma
          ctxT7.CertOk t C [] ∧
        HasSupport ctxT7.canon ctxT7.policy.ruleLookup ctxT7.Gamma
          ctxT7.CertOk t' C' [] :=
  admits_transport (κ := ctxT7) (lam := ctxT7) rfl
    (.refl ctxT7.canon ctxT7.policy.ruleLookup ctxT7.Gamma ctxT7.CertOk)
    admitsIdT7

/-- **The T6/T8 boundary, packaged at a live instance.** Exact checked-
support transport holds across the accepted T7 edge — and grounded status
still flips from `justified` to `defeated`. Support transport (T6) is
necessary but not sufficient for status preservation (T8, #193): any
status-preservation theorem must quantify over the target's attackers, not
over the transported term. -/
theorem t7_t6_boundary :
    Admits SymMap.id (fun l => l) wT7src wT7tgt ∧
      cmpStatus wT7src pA = Status.justified ∧
      cmpStatus wT7tgt pA = Status.defeated :=
  ⟨admitsIdT7, t7_src_justified, t7_tgt_defeated⟩

/-! ### A genuine renaming bridge -/

/-- The renaming: the claim predicate `p` becomes `p_r` and the evidence
predicate `e` becomes `e_r`; every other predicate is out of vocabulary;
constructor names are in vocabulary unchanged. -/
def renSym : SymMap :=
  { predMap := fun s =>
      if s = "p" then some "p_r"
      else if s = "e" then some "e_r"
      else none
  , conMap := some }

/-- Source rule: concludes `p` from the single evidence premise `e`,
defeasibly, no questions. The premise is what gives the support term a
subterm whose translation is not the identity. -/
def ruleRen : Rule :=
  { mode := .defeasible, params := [], premises := [⟨⟨"e"⟩, .nil⟩]
  , concl := ⟨⟨"p"⟩, .nil⟩, questions := [], allowTrusted := false
  , certifiers := [] }

/-- The rule identifier of the renaming example. -/
def rnRen : RuleId := ⟨"ren"⟩

/-- Source policy lookup: the one rule. -/
def piRenSrc : RuleId → Option Rule :=
  fun rn => if rn = rnRen then some ruleRen else none

/-- Target policy lookup: the *translated* source policy — the target
carries, at each identifier, exactly the renamed rule. -/
def piRenTgt : RuleId → Option Rule :=
  fun rn => (piRenSrc rn).bind (trRule renSym)

/-- The evidence leaf of the renaming example. -/
def lRen : LeafId := ⟨"e-src"⟩

/-- The bridge's leaf renaming — deliberately not the identity, so the
transported support term is a genuinely different term rather than the
source term reused. -/
def leafMapRen : LeafId → LeafId := fun l => ⟨l.name ++ "-tgt"⟩

/-- Source evidence typing: the one leaf is admitted at `e`. -/
def gammaRenSrc : LeafId → Option Atom :=
  fun l => if l = lRen then some (.atom "e" .nil) else none

/-- Target evidence typing: the *renamed* leaf is admitted at the
*translated* atom. Both halves are non-trivial, which is what makes
`leaf_ok` a real proof obligation here rather than a vacuous one. -/
def gammaRenTgt : LeafId → Option Atom :=
  fun l => if l = leafMapRen lRen then some (.atom "e_r" .nil) else none

/-- No certificate judgment on either side (the example rule is defeasible,
so no `AssuranceOk.cert` arm is reachable). Exercising `cert_ok` off the
identity needs a strict rule carrying a live certifier allowlist and a
certificate-accepting environment on both sides; deferred to #224. -/
def certRen : BackendId → Digest → CertRef → List Atom → Atom → Prop :=
  fun _ _ _ _ _ => False

/-- The renaming bridge. `rule_ok` holds by construction of the target
policy, and `leaf_ok` discharges a real translation step at a renamed leaf;
only the certificate clause is vacuous (#224). -/
def bridgeRen :
    StructuralBridge id piRenSrc piRenTgt gammaRenSrc gammaRenTgt
      certRen certRen
    where
  sym := renSym
  leafMap := leafMapRen
  leaf_ok := fun l p h => by
    unfold gammaRenSrc at h
    by_cases hl : l = lRen
    · rw [if_pos hl] at h
      cases h
      refine ⟨.atom "e_r" .nil, rfl, ?_⟩
      rw [hl]
      unfold gammaRenTgt
      rw [if_pos rfl]
    · rw [if_neg hl] at h
      exact nomatch h
  rule_ok := fun rn r h => by
    unfold piRenSrc at h
    by_cases hrn : rn = rnRen
    · rw [if_pos hrn] at h
      cases h
      refine ⟨_, rfl, ?_⟩
      unfold piRenTgt piRenSrc
      rw [if_pos hrn]
      rfl
    · rw [if_neg hrn] at h
      exact nomatch h
  cert_ok := fun _ _ _ _ _ _ _ _ _ h => h.elim

/-- The source support term: one instance of the rule, its single evidence
premise discharged by the admitted leaf, no question discharges, no holes,
defeasible assurance. -/
def wRen : SupportTerm := .inst rnRen [] [.leaf lRen] [] [] .none

/-- The transported support term: the same instance over the *renamed* leaf.
-/
def wRenTgt : SupportTerm :=
  .inst rnRen [] [.leaf (leafMapRen lRen)] [] [] .none

/-- The support translation genuinely renames: the transported term is not
the source term. Without this the transport theorem below would hold at a
term the bridge left untouched. -/
theorem ren_support_renamed :
    trSupport renSym leafMapRen wRen = some wRenTgt ∧ wRenTgt ≠ wRen :=
  ⟨rfl, by decide⟩

/-- `leaf_ok` off the identity: the admitted leaf is renamed, its atom is
translated, and the target environment types the renamed leaf at exactly the
translated atom. -/
theorem ren_leaf_translated :
    gammaRenSrc lRen = some (.atom "e" .nil) ∧
      leafMapRen lRen ≠ lRen ∧
      trAtom renSym (.atom "e" .nil) = some (.atom "e_r" .nil) ∧
      gammaRenTgt (leafMapRen lRen) = some (.atom "e_r" .nil) :=
  ⟨by decide, by decide, rfl, by decide⟩

/-- The source derivation: `wRen` supports `p` completely in the source
environment. -/
theorem hasSupport_ren :
    HasSupport id piRenSrc gammaRenSrc certRen wRen (.atom "p" .nil) [] := by
  have hside : InstSide id piRenSrc certRen rnRen [] ruleRen [.leaf lRen] []
      []  .none [.atom "e" .nil] [.atom "e" .nil] [[]] [] []
      (.atom "p" .nil) :=
    { rule := by unfold piRenSrc; rw [if_pos rfl]
      θNodup := List.nodup_nil
      θDom := fun _ => Iff.rfl
      prems := rfl
      concl := rfl
      lenAs := rfl
      lenCs := rfl
      lenOs := rfl
      premEq := by
        intro i A B hA hB
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hA hB
          subst hA; subst hB
          exact equiv_refl id _
        | succ j => simp at hA
      lenDCs := rfl
      lenDOs := rfl
      ans := fun _ _ _ _ h => nomatch h
      qNodup := List.nodup_nil
      dNodup := List.nodup_nil
      hNodup := List.nodup_nil
      cover := fun _ h => nomatch h
      disj := fun _ h => nomatch h
      keysD := fun _ h => nomatch h
      keysH := fun _ h => nomatch h
      strictNoQ := fun h => nomatch h
      assur := .defeasible rfl }
  have hleaf : HasSupport id piRenSrc gammaRenSrc certRen (.leaf lRen)
      (.atom "e" .nil) [] :=
    .leaf (by unfold gammaRenSrc; rw [if_pos rfl])
  have h := HasSupport.inst (canon := id) (Gamma := gammaRenSrc) hside
    (by
      intro i w A O hw hA hO
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hA hO
        subst hw; subst hA; subst hO
        exact hleaf
      | succ j => simp at hw)
    (fun _ _ _ _ _ h => nomatch h)
  exact h

/-- The renamed conclusion: `τ(p) = p_r`. -/
theorem ren_conclusion :
    trAtom renSym (.atom "p" .nil) = some (.atom "p_r" .nil) := rfl

/-- **The transported derivation.** `support_transport` carries the source
instance across the renaming bridge: the support term keeps its rule
identifier, empty substitution, and assurance, its evidence leaf is renamed,
and it supports the *renamed* claim `p_r`, completely, in the target
environment — whose policy carries the translated rule and whose evidence
typing carries the renamed leaf. -/
theorem ren_transport :
    HasSupport id piRenTgt gammaRenTgt certRen wRenTgt (.atom "p_r" .nil)
      [] := by
  obtain ⟨C', hC, h⟩ := support_transport bridgeRen hasSupport_ren
    (w' := wRenTgt) rfl
  have hC' : trAtom renSym (.atom "p" .nil) = some C' := hC
  rw [ren_conclusion] at hC'
  cases hC'
  exact h

/-! ### The domain negative -/

/-- The renaming is partial: `q` is out of vocabulary, so the bridge's claim
translation is undefined at it — the explicit translation-domain evidence
fails, and no transport of a `q`-support exists through this bridge. -/
theorem ren_out_of_vocabulary : trAtom renSym (.atom "q" .nil) = none := rfl

/-- The executable comparison reports the out-of-vocabulary claim as exactly
`translationUndefined`, never as a status: the bridge-domain arm of PW0's
`gap` separation, reached from a structural bridge's own translation. -/
theorem ren_translationUndefined {W : Type}
    (candidates : List W) (acceptB : W → Bool)
    (statusOf : W → Atom → Status) :
    crossCompare (trAtom renSym (.atom "q" .nil)) candidates acceptB
      statusOf = .incomparable .translationUndefined := by
  rw [ren_out_of_vocabulary]
  exact compare_none candidates acceptB statusOf

end Lara.Examples.PW
