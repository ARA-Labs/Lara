/-
# PW-T6 — exact checked-support transport (issue #191, tracker #189)

The `StructuralBridge` contract and the transport theorem. The design's
dependent partial support map `T_{b,w,v,c}` is `trSupport` under the bridge's
symbol translation and leaf map (`Lara.PW.Translation`); this module states
what a structural bridge must relate on the two checking environments and
proves that the map carries a checked source support to a checked target
support with the translated conclusion and the *same* obligation list.

**The contract is three clauses**, one per environment parameter the typing
judgment `HasSupport canon Pi Gamma CertOk` reads:

* `leaf_ok` — admitted evidence translates: a leaf typed at `p` in the source
  is typed at the translated `p` in the target under the bridge's leaf map
  (the design's "admitted evidence and artifact identity" preservation).
* `rule_ok` — the target policy maps each source rule identifier to exactly
  the translated rule (identifiers, premise order, question keys, modes,
  the trusted flag, and certifier allowlists preserved on the nose;
  premises, conclusion, and answers translated — the design's "sorts,
  substitutions, constructors, identifiers, premise order" block).
* `cert_ok` — per-occurrence certificate acceptance survives translation of
  the encoded step (the design's "backend registry entries and
  per-occurrence certificates" block).

The shared `canon` is deliberate: the source canonicalizer is the one thing
two bridged environments must agree on for their conclusions to be comparable
as claims (see `docs/theory-b0-backend-compositionality.md`, "two binders ARE
shared").

**What the theorem says** (`support_transport`): under the contract, if
`w` supports `C` with obligations `O` in the source environment and the
transport of `w` is defined, then the transported term supports the
*translated* `C` with the *same* `O` in the target environment. Obligations
transport verbatim because question keys are rule-local names the translation
preserves; completeness (`O = []`) therefore transports for free
(`support_transport_complete`) — the design's "transport of a complete
support requires preservation of empty obligations", satisfied here by
preserving obligations exactly.

**What the theorem does not say**: nothing about attacks, grounded
labelling, or claim status — `t7_witness` (`Lara.Examples.PW`) is the proof
that no such conclusion is available from support transport alone. The
theorem neither assumes nor concludes grounded status preservation; that
boundary is T8 (#193).

This module only imports; no local definition is touched.
-/

import Lara.PW.Translation
import Lara.PW.Instance
import Lara.BackendComposition

namespace Lara.PW

open Lara.Support

/-- **The structural-bridge contract** between two checking environments over
a shared source canonicalizer. Each clause is read by exactly one arm of the
transport induction; a field with no proof use would be dead weight and is
not present (issue #191's acceptance bullet). -/
structure StructuralBridge (canon : String → String)
    (Pi Pi' : RuleId → Option Rule)
    (Gamma Gamma' : LeafId → Option Atom)
    (CertOk CertOk' : BackendId → Digest → CertRef → List Atom → Atom → Prop)
    where
  /-- the bridge's partial symbol translation (claim vocabulary) -/
  sym : SymMap
  /-- the bridge's total evidence-leaf renaming -/
  leafMap : LeafId → LeafId
  /-- admitted evidence translates: leaf typing is preserved under the leaf
  map, with the leaf's atom in the translation's domain -/
  leaf_ok : ∀ l p, Gamma l = some p →
    ∃ p', trAtom sym p = some p' ∧ Gamma' (leafMap l) = some p'
  /-- the target policy carries the translated rule at the same identifier -/
  rule_ok : ∀ rn r, Pi rn = some r →
    ∃ r', trRule sym r = some r' ∧ Pi' rn = some r'
  /-- certificate acceptance survives translation of the encoded step -/
  cert_ok : ∀ β hd κ As C As' C', trAtoms sym As = some As' →
    trAtom sym C = some C' → CertOk β hd κ As C → CertOk' β hd κ As' C'

/-- Every checking environment carries the identity structural bridge to
itself: the identity translation is total and inert, so all three contract
clauses collapse to the source facts. The T7 endobridge is this bridge at
`ctxT7` — which is what lets the T7 pair be read as a structural bridge whose
transport succeeds while grounded status flips. -/
def StructuralBridge.refl (canon : String → String)
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop) :
    StructuralBridge canon Pi Pi Gamma Gamma CertOk CertOk where
  sym := SymMap.id
  leafMap := fun l => l
  leaf_ok := fun _ p h => ⟨p, trAtom_id p, h⟩
  rule_ok := fun _ r h => ⟨r, trRule_id r, h⟩
  cert_ok := fun β hd κ As C As' C' hAs hC hacc => by
    rw [trAtoms_id As] at hAs
    rw [trAtom_id C] at hC
    cases hAs
    cases hC
    exact hacc

/-- **T6, exact checked-support transport.** Under the structural-bridge
contract, the dependent partial support map carries a checked source support
to a checked target support: the conclusion is the translated conclusion
(the conclusion law `concl (T b t) = τ b (concl t)` at claim level), and the
obligation list transports verbatim. The `some` hypothesis is the design's
explicit translation-domain evidence for the support term; the conclusion's
translation definedness is derived, not assumed. -/
theorem support_transport
    {canon : String → String} {Pi Pi' : RuleId → Option Rule}
    {Gamma Gamma' : LeafId → Option Atom}
    {CertOk CertOk' : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (B : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk')
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk w C O) :
    ∀ {w' : SupportTerm}, trSupport B.sym B.leafMap w = some w' →
      ∃ C', trAtom B.sym C = some C' ∧
        HasSupport canon Pi' Gamma' CertOk' w' C' O := by
  induction h with
  | @leaf l p hΓ =>
    intro w' hw
    simp only [trSupport] at hw
    cases hw
    obtain ⟨p', hp', hΓ'⟩ := B.leaf_ok l p hΓ
    exact ⟨p', hp', .leaf hΓ'⟩
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis ihp ihd =>
    intro w' hw
    simp only [trSupport] at hw
    cases hθ : trSubst B.sym θ with
    | none => rw [hθ] at hw; exact nomatch hw
    | some θ' =>
      rw [hθ] at hw
      cases hws : trSupportList B.sym B.leafMap ws with
      | none => rw [hws] at hw; exact nomatch hw
      | some ws' =>
        rw [hws] at hw
        cases hDtr : trSupportDis B.sym B.leafMap D with
        | none => rw [hDtr] at hw; exact nomatch hw
        | some D' =>
          rw [hDtr] at hw
          cases hw
          -- the target rule and its translated components
          obtain ⟨r', hrtr, hPi'⟩ := B.rule_ok rn r hside.rule
          obtain ⟨ps', c', qs', hprem_tr, hconcl_tr, hq_tr, hre⟩ :=
            trRule_inv hrtr
          subst hre
          -- translated premise instances and conclusion
          obtain ⟨As', hAs, hprems'⟩ :=
            instAPats_tr hθ r.premises hprem_tr hside.prems
          obtain ⟨C', hC, hconcl'⟩ := instAPat_tr hθ hconcl_tr hside.concl
          -- translated premise conclusions: definedness from the children
          have hCs_def : ∀ (i : Nat) (a : Atom), Cs[i]? = some a →
              (trAtom B.sym a).isSome = true := by
            intro i a hCsi
            have hi : i < ws.length := by
              have h1 : i < Cs.length := (List.getElem?_eq_some_iff.mp hCsi).1
              rw [hside.lenCs] at h1
              exact h1
            have hiO : i < Os.length := by rw [hside.lenOs]; exact hi
            have hwi : ws[i]? = some ws[i] := List.getElem?_eq_getElem hi
            have hOi : Os[i]? = some Os[i] := List.getElem?_eq_getElem hiO
            have hi' : i < ws'.length := by
              rw [trSupportList_length hws]; exact hi
            have hb1 := trSupportList_getElem? hws i
            rw [hwi, List.getElem?_eq_getElem hi'] at hb1
            have htri : trSupport B.sym B.leafMap ws[i] = some ws'[i] :=
              hb1.symm
            obtain ⟨Ci', hCi, _⟩ := ihp i ws[i] a Os[i] hwi hCsi hOi htri
            rw [hCi]; rfl
          obtain ⟨Cs', hCs_tr⟩ := trAtoms_defined hCs_def
          -- translated discharge conclusions: definedness from the children
          have hDlen : D'.length = D.length := by
            have := congrArg List.length (trSupportDis_fst hDtr)
            simpa using this
          have hDCs_def : ∀ (j : Nat) (a : Atom), DCs[j]? = some a →
              (trAtom B.sym a).isSome = true := by
            intro j a hDCsj
            have hj : j < D.length := by
              have h1 : j < DCs.length :=
                (List.getElem?_eq_some_iff.mp hDCsj).1
              rw [hside.lenDCs] at h1
              exact h1
            have hjO : j < DOs.length := by rw [hside.lenDOs]; exact hj
            have hDj : D[j]? = some D[j] := List.getElem?_eq_getElem hj
            have hOj : DOs[j]? = some DOs[j] := List.getElem?_eq_getElem hjO
            have hj' : j < D'.length := by rw [hDlen]; exact hj
            have hb := trSupportDis_getElem? hDtr j
            rw [hDj, List.getElem?_eq_getElem hj'] at hb
            have hb' : some D'[j] =
                (trSupport B.sym B.leafMap (D[j]).2).map (((D[j]).1, ·)) := hb
            cases htrj : trSupport B.sym B.leafMap (D[j]).2 with
            | none => rw [htrj] at hb'; exact nomatch hb'
            | some wj' =>
              rw [htrj] at hb'
              obtain ⟨Cj', hCj, _⟩ :=
                ihd j (D[j]).1 (D[j]).2 a DOs[j]
                  (by rw [hDj]) hDCsj hOj htrj
              rw [hCj]; rfl
          obtain ⟨DCs', hDCs_tr⟩ := trAtoms_defined hDCs_def
          -- the target derivation
          refine ⟨C', hC, ?_⟩
          have hobl : collectObligations Os DOs
              { r with premises := ps', concl := c', questions := qs' } H =
              collectObligations Os DOs r H := by
            unfold collectObligations openMandatory
            rw [trRule_mandatoryNames hrtr]
          rw [← hobl]
          refine HasSupport.inst
            (r := { r with premises := ps', concl := c', questions := qs' })
            (As := As') (Cs := Cs') (Os := Os) (DCs := DCs') (DOs := DOs)
            ?_ ?_ ?_
          · -- the non-recursive side conditions, field by field
            refine
              { rule := hPi'
                θNodup := ?_
                θDom := ?_
                prems := hprems'
                concl := hconcl'
                lenAs := ?_
                lenCs := ?_
                lenOs := ?_
                premEq := ?_
                lenDCs := ?_
                lenDOs := ?_
                ans := ?_
                qNodup := ?_
                dNodup := ?_
                hNodup := hside.hNodup
                cover := ?_
                disj := ?_
                keysD := ?_
                keysH := ?_
                strictNoQ := ?_
                assur := ?_ }
            · rw [trSubst_fst hθ]; exact hside.θNodup
            · intro x
              rw [trSubst_fst hθ]
              exact hside.θDom x
            · rw [trSupportList_length hws, trAtoms_length hAs]
              exact hside.lenAs
            · rw [trAtoms_length hCs_tr, trSupportList_length hws]
              exact hside.lenCs
            · rw [trSupportList_length hws]; exact hside.lenOs
            · intro i A' B' hA' hB'
              have h1 := trAtoms_getElem? hCs_tr i
              have h2 := trAtoms_getElem? hAs i
              rw [hA'] at h1
              rw [hB'] at h2
              cases hCsi : Cs[i]? with
              | none => rw [hCsi] at h1; exact nomatch h1
              | some A0 =>
                rw [hCsi] at h1
                cases hAsi : As[i]? with
                | none => rw [hAsi] at h2; exact nomatch h2
                | some B0 =>
                  rw [hAsi] at h2
                  have h1' : some A' = trAtom B.sym A0 := h1
                  have h2' : some B' = trAtom B.sym B0 := h2
                  exact equiv_tr h1'.symm h2'.symm
                    (hside.premEq i A0 B0 hCsi hAsi)
            · rw [trAtoms_length hDCs_tr, hside.lenDCs, hDlen]
            · rw [hDlen]; exact hside.lenDOs
            · intro j q wj' A' hD'j hDCs'j
              have hb := trSupportDis_getElem? hDtr j
              rw [hD'j] at hb
              cases hDj : D[j]? with
              | none => rw [hDj] at hb; exact nomatch hb
              | some qw =>
                rw [hDj] at hb
                obtain ⟨q0, w0⟩ := qw
                have hb' : some (q, wj') =
                    (trSupport B.sym B.leafMap w0).map ((q0, ·)) := hb
                cases htrj : trSupport B.sym B.leafMap w0 with
                | none => rw [htrj] at hb'; exact nomatch hb'
                | some w1 =>
                  rw [htrj] at hb'
                  have hpe := Option.some.inj hb'
                  rw [Prod.mk.injEq] at hpe
                  obtain ⟨hq0, _⟩ := hpe
                  subst hq0
                  have h2 := trAtoms_getElem? hDCs_tr j
                  rw [hDCs'j] at h2
                  cases hDCsj : DCs[j]? with
                  | none => rw [hDCsj] at h2; exact nomatch h2
                  | some A0 =>
                    rw [hDCsj] at h2
                    have h2' : some A' = trAtom B.sym A0 := h2
                    obtain ⟨qd, hqmem, hqname, Aq, hAq, heq⟩ :=
                      hside.ans j q w0 A0 hDj hDCsj
                    obtain ⟨qd', hqtr, hqmem'⟩ := trQuestions_mem hq_tr hqmem
                    obtain ⟨aq', haq', hqe⟩ := trQuestion_inv hqtr
                    obtain ⟨Aq', hAqtr, hAq'⟩ := instAPat_tr hθ haq' hAq
                    refine ⟨qd', hqmem', ?_, Aq', ?_, ?_⟩
                    · rw [hqe]; exact hqname
                    · rw [hqe]; exact hAq'
                    · exact equiv_tr h2'.symm hAqtr heq
            · rw [trRule_questionNames hrtr]; exact hside.qNodup
            · rw [trSupportDis_fst hDtr]; exact hside.dNodup
            · intro qd' hmem
              obtain ⟨qd, hqmem, hqtr⟩ := trQuestions_mem_rev hq_tr hmem
              obtain ⟨aq, _, hqe⟩ := trQuestion_inv hqtr
              rw [trSupportDis_fst hDtr, hqe]
              exact hside.cover qd hqmem
            · intro n hn
              rw [trSupportDis_fst hDtr] at hn
              exact hside.disj n hn
            · intro n hn
              rw [trSupportDis_fst hDtr] at hn
              rw [trRule_questionNames hrtr]
              exact hside.keysD n hn
            · intro n hn
              rw [trRule_questionNames hrtr]
              exact hside.keysH n hn
            · intro hm
              have hm0 : r.mode = .strict := by
                rw [← trRule_mode hrtr]; exact hm
              obtain ⟨hD0, hH0⟩ := hside.strictNoQ hm0
              refine ⟨?_, hH0⟩
              have hfst := trSupportDis_fst hDtr
              rw [hD0] at hfst
              exact List.map_eq_nil_iff.mp hfst
            · cases hside.assur with
              | defeasible hmode =>
                exact .defeasible (by rw [trRule_mode hrtr]; exact hmode)
              | trusted hmode ht =>
                exact .trusted (by rw [trRule_mode hrtr]; exact hmode)
                  (by rw [trRule_allowTrusted hrtr]; exact ht)
              | cert hmode hallow hacc =>
                exact .cert (by rw [trRule_mode hrtr]; exact hmode)
                  (by rw [trRule_certifiers hrtr]; exact hallow)
                  (B.cert_ok _ _ _ _ _ _ _ hAs hC hacc)
          · -- the recursive premise obligations
            intro i wi' Ai' Oi hwi' hCi' hOi
            have hb1 := trSupportList_getElem? hws i
            rw [hwi'] at hb1
            cases hwsi : ws[i]? with
            | none => rw [hwsi] at hb1; exact nomatch hb1
            | some wi =>
              rw [hwsi] at hb1
              have hb1' : some wi' = trSupport B.sym B.leafMap wi := hb1
              have h2 := trAtoms_getElem? hCs_tr i
              rw [hCi'] at h2
              cases hCsi : Cs[i]? with
              | none => rw [hCsi] at h2; exact nomatch h2
              | some Ai =>
                rw [hCsi] at h2
                have h2' : some Ai' = trAtom B.sym Ai := h2
                obtain ⟨Ci', hCtr, hHS⟩ :=
                  ihp i wi Ai Oi hwsi hCsi hOi hb1'.symm
                rw [hCtr] at h2'
                injection h2' with h2e
                subst h2e
                exact hHS
          · -- the recursive discharge obligations
            intro j q wj' Aj' Oj hD'j hDCs'j hOj
            have hb := trSupportDis_getElem? hDtr j
            rw [hD'j] at hb
            cases hDj : D[j]? with
            | none => rw [hDj] at hb; exact nomatch hb
            | some qw =>
              rw [hDj] at hb
              obtain ⟨q0, w0⟩ := qw
              have hb' : some (q, wj') =
                  (trSupport B.sym B.leafMap w0).map ((q0, ·)) := hb
              cases htrj : trSupport B.sym B.leafMap w0 with
              | none => rw [htrj] at hb'; exact nomatch hb'
              | some w1 =>
                rw [htrj] at hb'
                have hpe := Option.some.inj hb'
                rw [Prod.mk.injEq] at hpe
                obtain ⟨hq0, hw1⟩ := hpe
                subst hq0
                subst hw1
                have h2 := trAtoms_getElem? hDCs_tr j
                rw [hDCs'j] at h2
                cases hDCsj : DCs[j]? with
                | none => rw [hDCsj] at h2; exact nomatch h2
                | some Aj =>
                  rw [hDCsj] at h2
                  have h2' : some Aj' = trAtom B.sym Aj := h2
                  obtain ⟨Cj', hCtr, hHS⟩ :=
                    ihd j q w0 Aj Oj hDj hDCsj hOj htrj
                  rw [hCtr] at h2'
                  injection h2' with h2e
                  subst h2e
                  exact hHS

/-- T6's completeness clause: a *complete* checked source support transports
to a *complete* checked target support. Immediate from `support_transport`
because obligations transport verbatim — the bridge preserves empty
obligations by preserving obligations exactly. -/
theorem support_transport_complete
    {canon : String → String} {Pi Pi' : RuleId → Option Rule}
    {Gamma Gamma' : LeafId → Option Atom}
    {CertOk CertOk' : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (B : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk')
    {w w' : SupportTerm} {C : Atom}
    (h : HasSupport canon Pi Gamma CertOk w C [])
    (hw : trSupport B.sym B.leafMap w = some w') :
    ∃ C', trAtom B.sym C = some C' ∧
      HasSupport canon Pi' Gamma' CertOk' w' C' [] :=
  support_transport B h hw

/-- Claim-level transport: `w supports p` in the source and both the term and
the claim are in the translation's domain, then the transported term supports
the translated claim in the target. The `≡`-closure at the claim boundary
survives because `≡` survives translation (`equiv_tr`). -/
theorem supports_transport
    {canon : String → String} {Pi Pi' : RuleId → Option Rule}
    {Gamma Gamma' : LeafId → Option Atom}
    {CertOk CertOk' : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (B : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk')
    {w w' : SupportTerm} {p p' : Atom}
    (hs : Supports canon Pi Gamma CertOk w p)
    (hw : trSupport B.sym B.leafMap w = some w')
    (hp : trAtom B.sym p = some p') :
    Supports canon Pi' Gamma' CertOk' w' p' := by
  obtain ⟨C, O, hHS, heq⟩ := hs
  obtain ⟨C', hC, hHS'⟩ := support_transport B hHS hw
  exact ⟨C', O, hHS', equiv_tr hC hp heq⟩

/-- **Target-side occurrences replay against the target registry** (issue
#191's acceptance bullet). Instantiating both certificate judgments from
registries, every strict occurrence of the transported term is accounted by
its own backend as registered in the *target* registry: the target policy
carries its rule, the certificate is accepted by the target instantiation,
and the occurrence-local consequence holds — B0's headline applied to the
transported derivation. -/
theorem transport_occurrences_accounted
    {canon : String → String} {Pi Pi' : RuleId → Option Rule}
    {Gamma Gamma' : LeafId → Option Atom}
    {reg reg' : BackendRegistry canon}
    (B : StructuralBridge canon Pi Pi' Gamma Gamma'
      (certOkOf reg) (certOkOf reg'))
    {w w' : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma (certOkOf reg) w C O)
    (hw : trSupport B.sym B.leafMap w = some w') :
    ∀ o : Lara.BackendComposition.CertOccurrence,
      Lara.BackendComposition.OccursIn w' o →
      ∃ r As Cn, Pi' o.rn = some r ∧ r.mode = .strict ∧
        (o.β, o.hd) ∈ r.certifiers ∧
        instAPats o.θ r.premises = some As ∧
        instAPat o.θ r.concl = some Cn ∧
        certOkOf reg' o.β o.hd o.κ As Cn ∧
        Lara.BackendComposition.OccurrenceConsequence reg' o.β o.hd o.κ
          As Cn := by
  obtain ⟨C', _, h'⟩ := support_transport B h hw
  exact Lara.BackendComposition.hetero_occurrences_accounted h'

/-! ### The induced applicability judgment

PW0 froze `accept` as an arbitrary `Prop` and recorded supplying its
connection to the checker as T6's work (`docs/theory-pw0-outer-model.md`,
limitation 1). At a structural bridge the connection is `Admits`: the target
world's accepted program carries the transport of every argument of the
source world's accepted program. Together with `support_transport` this
makes acceptance a checker-tied judgment — an accepted edge transports every
complete checked source support into the target's own accepted program, with
the translated conclusion (`admits_transport`). -/

/-- The checked applicability judgment a structural bridge induces between
two Lara worlds: every source program argument transports into the target
program. This is the `accept` a `StructuralBridge` supplies to a PW0 frame
(`Instance.BridgeData.accept`). -/
def Admits (m : SymMap) (lm : LeafId → LeafId)
    {κ lam : Instance.Context}
    (w : Instance.World κ) (v : Instance.World lam) : Prop :=
  ∀ t, t ∈ w.unit.program.args →
    ∃ t', trSupport m lm t = some t' ∧ t' ∈ v.unit.program.args

/-- At an admitted world pair under the structural-bridge contract, every
argument of the source world's accepted program transports to a member of
the target world's accepted program that carries a complete checked support
for the translated conclusion — checked in the *target* context's own
environment. The source-side judgment is returned alongside so the two
endpoints of the transport are both in evidence. -/
theorem admits_transport {κ lam : Instance.Context}
    (hcanon : lam.canon = κ.canon)
    (B : StructuralBridge κ.canon κ.policy.ruleLookup lam.policy.ruleLookup
      κ.Gamma lam.Gamma κ.CertOk lam.CertOk)
    {w : Instance.World κ} {v : Instance.World lam}
    (hadm : Admits B.sym B.leafMap w v) :
    ∀ t, t ∈ w.unit.program.args →
      ∃ t' C C', t' ∈ v.unit.program.args ∧
        trSupport B.sym B.leafMap t = some t' ∧
        trAtom B.sym C = some C' ∧
        HasSupport κ.canon κ.policy.ruleLookup κ.Gamma κ.CertOk t C [] ∧
        HasSupport lam.canon lam.policy.ruleLookup lam.Gamma lam.CertOk
          t' C' [] := by
  intro t hmem
  obtain ⟨C, hHS⟩ := w.unit.program.complete t hmem
  rw [w.policy_eq] at hHS
  obtain ⟨t', htr, hmem'⟩ := hadm t hmem
  obtain ⟨C', hC, hHS'⟩ := support_transport B hHS htr
  refine ⟨t', C, C', hmem', htr, hC, hHS, ?_⟩
  rw [hcanon]
  exact hHS'

end Lara.PW
