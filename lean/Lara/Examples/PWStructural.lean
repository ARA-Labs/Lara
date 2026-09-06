/-
# PW-T6 executable examples (issue #191, tracker #189)

Three instances of the structural-bridge contract, one boundary fact, and the
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
`leaf_ok` by the renamed leaf at the translated atom. Its `CertOk` judgment
is empty on both sides — the defeasible rule makes no `AssuranceOk.cert` arm
reachable — so this bridge closes `cert_ok` vacuously.

**The strict-certificate renaming bridge (#224).** The same renaming over a
*strict* rule with a live certifier allowlist and `allowTrusted` off, so the
only reachable assurance is a backend-accepted certificate. The `CertOk`
pair holds exactly at the fixture's encoded step on each side — the
instantiated premise and conclusion, source-vocabulary at the source,
translated at the target — which makes `cert_ok` a real translation proof:
acceptance at `([e], p)` is carried to acceptance at `([e_r], p_r)`. The
transported derivation then runs the `AssuranceOk.cert` arm off the
identity, with the frozen `(β, hd, κ)` triple preserved verbatim.

**The strict fixture's drift guards (#231).** The transport theorem runs at
one certifier triple and one encoded step, so on its own it survives two
mutations that would make the paragraph above false. Both are closed:
`cert_reject_mismatched_certifier` pins that each component of `(β, hd, κ)`
is read on each side, and `cert_only_assurance` (with `cert_target_rule`)
pins `allowTrusted` off in both environments, leaving the certificate arm the
only reachable assurance.

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
so no `AssuranceOk.cert` arm is reachable). The strict-certificate bridge
below (`bridgeCert`, #224) is where `cert_ok` is exercised off the
identity. -/
def certRen : BackendId → Digest → CertRef → List Atom → Atom → Prop :=
  fun _ _ _ _ _ => False

/-- The renaming bridge. `rule_ok` holds by construction of the target
policy, and `leaf_ok` discharges a real translation step at a renamed leaf;
only the certificate clause is vacuous here (see `bridgeCert` for the
non-vacuous discharge). -/
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

/-! ### The strict-certificate renaming bridge (#224) -/

/-- The allowlisted certifier backend of the strict renaming example. -/
def βRen : BackendId := ⟨"smt", 1⟩

/-- The certifier's allowlisted theory digest. -/
def hdRen : Digest := ⟨"th-ren"⟩

/-- The opaque certificate reference the fixture submits. -/
def κRen : CertRef := ⟨.atom "cert-ren"⟩

/-- Strict source rule: concludes `p` from the evidence premise `e`, with
`(βRen, hdRen)` its one allowlisted certifier and `allowTrusted` off — the
only reachable assurance is a certificate `CertOk` accepts. -/
def ruleCert : Rule :=
  { mode := .strict, params := [], premises := [⟨⟨"e"⟩, .nil⟩]
  , concl := ⟨⟨"p"⟩, .nil⟩, questions := [], allowTrusted := false
  , certifiers := [(βRen, hdRen)] }

/-- The rule identifier of the strict renaming example. -/
def rnCert : RuleId := ⟨"cert-ren"⟩

/-- Source policy lookup: the one strict rule. -/
def piCertSrc : RuleId → Option Rule :=
  fun rn => if rn = rnCert then some ruleCert else none

/-- Target policy lookup: the translated source policy, as `rule_ok`
requires. `trRule` preserves the mode and the certifier allowlist, so the
target rule is strict with the same live allowlist. -/
def piCertTgt : RuleId → Option Rule :=
  fun rn => (piCertSrc rn).bind (trRule renSym)

/-- Source certificate acceptance: `βRen` under `hdRen` accepts `κRen` for
exactly the fixture's encoded step — instantiated premise `e`, conclusion
`p`. Non-empty by construction, unlike the defeasible example's `certRen`. -/
def certCertSrc : BackendId → Digest → CertRef → List Atom → Atom → Prop :=
  fun β hd κ As C =>
    β = βRen ∧ hd = hdRen ∧ κ = κRen ∧
      As = [.atom "e" .nil] ∧ C = .atom "p" .nil

/-- Target certificate acceptance: the same certifier triple, at the
*translated* encoded step — premise `e_r`, conclusion `p_r`. -/
def certCertTgt : BackendId → Digest → CertRef → List Atom → Atom → Prop :=
  fun β hd κ As C =>
    β = βRen ∧ hd = hdRen ∧ κ = κRen ∧
      As = [.atom "e_r" .nil] ∧ C = .atom "p_r" .nil

/-- The strict-certificate renaming bridge. All three contract clauses are
now discharged non-vacuously: `rule_ok` by the translated strict policy,
`leaf_ok` by the renamed leaf at the translated atom, and `cert_ok` by an
acceptance pair that survives the translation of its encoded step. -/
def bridgeCert :
    StructuralBridge id piCertSrc piCertTgt gammaRenSrc gammaRenTgt
      certCertSrc certCertTgt where
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
    unfold piCertSrc at h
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
    have hAs' : As' = [.atom "e_r" .nil] := by
      have he : trAtoms renSym [Atom.atom "e" .nil] =
          some [Atom.atom "e_r" .nil] := rfl
      rw [he] at hAs
      exact (Option.some.inj hAs).symm
    have hC' : C' = .atom "p_r" .nil := by
      rw [ren_conclusion] at hC
      exact (Option.some.inj hC).symm
    exact ⟨rfl, rfl, rfl, hAs', hC'⟩

/-- **The certificate step survives the renaming.** The rule is strict with a
allowlist, source acceptance holds at the fixture's encoded step, both
components of the step translate, and target acceptance holds at the
translated step. A future edit that emptied either judgment under a real
renaming breaks this theorem — the regression guard #224 asked for. -/
theorem cert_accept_translated :
    ruleCert.mode = .strict ∧ (βRen, hdRen) ∈ ruleCert.certifiers ∧
      certCertSrc βRen hdRen κRen [.atom "e" .nil] (.atom "p" .nil) ∧
      trAtoms renSym [.atom "e" .nil] = some [.atom "e_r" .nil] ∧
      trAtom renSym (.atom "p" .nil) = some (.atom "p_r" .nil) ∧
      certCertTgt βRen hdRen κRen [.atom "e_r" .nil] (.atom "p_r" .nil) :=
  ⟨rfl, List.mem_singleton.mpr rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The source and target certificate judgments reject one another's encoded
step. This pins the off-identity distinction at the acceptance boundary, so
widening either point-mass judgment to accept the untranslated step breaks the
fixture. -/
theorem cert_reject_untranslated :
    ¬ certCertTgt βRen hdRen κRen [.atom "e" .nil] (.atom "p" .nil) ∧
      ¬ certCertSrc βRen hdRen κRen [.atom "e_r" .nil] (.atom "p_r" .nil) := by
  constructor
  · rintro ⟨_, _, _, h, _⟩
    exact absurd h (by decide)
  · rintro ⟨_, _, _, h, _⟩
    exact absurd h (by decide)

/-- The source support term: one instance of the strict rule, its evidence
premise discharged by the admitted leaf, certificate assurance carrying the
frozen `(βRen, hdRen, κRen)` triple. -/
def wCert : SupportTerm :=
  .inst rnCert [] [.leaf lRen] [] [] (.cert βRen hdRen κRen)

/-- The transported support term: the renamed leaf, the *same* certificate
triple — `trSupport` carries assurances verbatim. -/
def wCertTgt : SupportTerm :=
  .inst rnCert [] [.leaf (leafMapRen lRen)] [] [] (.cert βRen hdRen κRen)

/-- The strict support translation genuinely renames, and preserves the
certificate triple on the nose. -/
theorem cert_support_renamed :
    trSupport renSym leafMapRen wCert = some wCertTgt ∧ wCertTgt ≠ wCert :=
  ⟨rfl, by decide⟩

/-- The source derivation: `wCert` supports `p` completely in the strict
source environment, through the `AssuranceOk.cert` arm. -/
theorem hasSupport_cert :
    HasSupport id piCertSrc gammaRenSrc certCertSrc wCert (.atom "p" .nil)
      [] := by
  have hside : InstSide id piCertSrc certCertSrc rnCert [] ruleCert
      [.leaf lRen] [] [] (.cert βRen hdRen κRen) [.atom "e" .nil]
      [.atom "e" .nil] [[]] [] [] (.atom "p" .nil) :=
    { rule := by unfold piCertSrc; rw [if_pos rfl]
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
      strictNoQ := fun _ => ⟨rfl, rfl⟩
      assur := .cert rfl (List.mem_singleton.mpr rfl)
        ⟨rfl, rfl, rfl, rfl, rfl⟩ }
  have hleaf : HasSupport id piCertSrc gammaRenSrc certCertSrc (.leaf lRen)
      (.atom "e" .nil) [] :=
    .leaf (by unfold gammaRenSrc; rw [if_pos rfl])
  exact HasSupport.inst (canon := id) (Gamma := gammaRenSrc) hside
    (by
      intro i w A O hw hA hO
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hA hO
        subst hw; subst hA; subst hO
        exact hleaf
      | succ j => simp at hw)
    (fun _ _ _ _ _ h => nomatch h)

/-- **The transported strict derivation.** `support_transport` carries the
certificate-assured instance across the renaming bridge: the transported
term keeps the frozen `(βRen, hdRen, κRen)` triple, its leaf is renamed, and
it supports the renamed claim `p_r`, completely, in the target environment —
whose acceptance judgment `certCertTgt` accepts the translated encoded step
through `bridgeCert.cert_ok`, exercised off the identity for the first time.
-/
theorem cert_transport :
    HasSupport id piCertTgt gammaRenTgt certCertTgt wCertTgt
      (.atom "p_r" .nil) [] := by
  obtain ⟨C', hC, h⟩ := support_transport bridgeCert hasSupport_cert
    (w' := wCertTgt) rfl
  have hC' : trAtom renSym (.atom "p" .nil) = some C' := hC
  rw [ren_conclusion] at hC'
  cases hC'
  exact h

/-! ### Fixture drift guards (#231)

`cert_transport` runs through both certificate judgments and the strict
rule's `AssuranceOk.cert` arm, but it does so at exactly one certifier triple
and one encoded step, so it stays green under two mutations that make the
prose above false: dropping `(β, hd, κ)` from the acceptance judgments
(certifier-blind acceptance) and flipping `allowTrusted` on (a second
reachable assurance). The theorems below fail under exactly those mutations.
-/

/-- A backend that is not the fixture's allowlisted one. -/
def βOther : BackendId := ⟨"smt", 2⟩

/-- A theory digest that is not the fixture's allowlisted one. -/
def hdOther : Digest := ⟨"th-other"⟩

/-- A certificate reference that is not the one the fixture submits. -/
def κOther : CertRef := ⟨.atom "cert-other"⟩

/-- **Both acceptance judgments read the certifier triple.** Each of the
three frozen components is load-bearing on each side: with the side's own
encoded step held fixed, mismatching exactly one of `β`, `hd`, `κ` is
rejected. A judgment that ignored `(β, hd, κ)` — acceptance as a predicate on
the encoded step alone — would satisfy all six applications here and break
this theorem, while `cert_accept_translated`, `cert_reject_untranslated`, and
`cert_transport` all stayed green. -/
theorem cert_reject_mismatched_certifier :
    ¬ certCertSrc βOther hdRen κRen [.atom "e" .nil] (.atom "p" .nil) ∧
      ¬ certCertSrc βRen hdOther κRen [.atom "e" .nil] (.atom "p" .nil) ∧
      ¬ certCertSrc βRen hdRen κOther [.atom "e" .nil] (.atom "p" .nil) ∧
      ¬ certCertTgt βOther hdRen κRen [.atom "e_r" .nil] (.atom "p_r" .nil) ∧
      ¬ certCertTgt βRen hdOther κRen [.atom "e_r" .nil] (.atom "p_r" .nil) ∧
      ¬ certCertTgt βRen hdRen κOther [.atom "e_r" .nil]
          (.atom "p_r" .nil) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h, _, _, _, _⟩; exact absurd h (by decide)
  · rintro ⟨_, h, _, _, _⟩; exact absurd h (by decide)
  · rintro ⟨_, _, h, _, _⟩; exact absurd h (by decide)
  · rintro ⟨h, _, _, _, _⟩; exact absurd h (by decide)
  · rintro ⟨_, h, _, _, _⟩; exact absurd h (by decide)
  · rintro ⟨_, _, h, _, _⟩; exact absurd h (by decide)

/-- The target rule of the strict example, written out rather than derived
from `ruleCert`: strict, the renamed premise and conclusion, the *same* live
allowlist, `allowTrusted` still off. Stating it independently is what makes
`cert_target_rule` a drift guard on `ruleCert` itself. -/
def ruleCertTgt : Rule :=
  { mode := .strict, params := [], premises := [⟨⟨"e_r"⟩, .nil⟩]
  , concl := ⟨⟨"p_r"⟩, .nil⟩, questions := [], allowTrusted := false
  , certifiers := [(βRen, hdRen)] }

/-- The target policy carries exactly that rule: `trRule` renames the premise
and the conclusion and carries the mode, the allowlist, and `allowTrusted`
verbatim. Any edit to `ruleCert`'s mode, allowlist, or `allowTrusted` flag
breaks this equation. -/
theorem cert_target_rule : piCertTgt rnCert = some ruleCertTgt := rfl

/-- **The certificate arm is the only reachable assurance, on both sides.**
`allowTrusted` is off and the rule is strict, so neither `.trusted` (which
needs the flag) nor `.none` (which needs a defeasible rule) can satisfy
`AssuranceOk` at the fixture's encoded step in either environment. Flipping
`ruleCert.allowTrusted` to `true` breaks this theorem — the `.trusted` arm
becomes reachable and the pinned flag equation becomes false — where
`hasSupport_cert` and `cert_transport`, which build and transport the `.cert`
arm, would not notice. -/
theorem cert_only_assurance :
    ruleCert.allowTrusted = false ∧ ruleCertTgt.allowTrusted = false ∧
      ¬ AssuranceOk certCertSrc ruleCert [.atom "e" .nil] (.atom "p" .nil)
          .trusted ∧
      ¬ AssuranceOk certCertSrc ruleCert [.atom "e" .nil] (.atom "p" .nil)
          .none ∧
      ¬ AssuranceOk certCertTgt ruleCertTgt [.atom "e_r" .nil]
          (.atom "p_r" .nil) .trusted ∧
      ¬ AssuranceOk certCertTgt ruleCertTgt [.atom "e_r" .nil]
          (.atom "p_r" .nil) .none := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro h; cases h with | trusted _ ht => exact absurd ht (by decide)
  · intro h; cases h with | defeasible hm => exact absurd hm (by decide)
  · intro h; cases h with | trusted _ ht => exact absurd ht (by decide)
  · intro h; cases h with | defeasible hm => exact absurd hm (by decide)

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
