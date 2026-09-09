/-
# Theory M4, phase F2 — contextual adequacy of backend replacement

The milestone's headline. Result 9 (`Lara.Erase.backend_replacement`) says an
injective, acceptance-preserving relabel of one *whole program* leaves every
claim's status alone; its quantifier ranges over relabelings of a fixed
program. This module lifts that to a **congruence**: the relabel is unobservable
in every compatible well-formed context whose own assurances it fixes.

The proof is the one the plan predicted. A uniform relabel preserves the entire
occurrence profile — conclusions, root rule identities, contrary matches — so it
**commutes with the linking saturation** (`crossAtts_relabel`), and the linked
programs are then related exactly as `Erase.edgeB_relabel` needs. Because the
relabel preserves the whole profile rather than a declared interface, the
question "what is the semantic interface of a fragment?" — the obstruction that
keeps full abstraction gated — never has to be answered here.

Naming discipline (issue #187): this is **contextual representation
independence**. It is not parametricity — that would need a relational
quantification over related backends (issue #215) — and it is not full
abstraction, which needs a logical relation (Part B).

## The projection layer (issue #216)

The module also owns the layer that leaves the *reading* of the carrier open:
`obsGen` (`:562`) is `obs` with `Invariants.status canon` replaced by an
arbitrary projection, and `obsGen_congr` (`:778`) is the real proof of the
congruence — `backend_replacement_congruence` (`:817`) is that theorem
instantiated at the grounded reading, in one line.

It lives here rather than beside the semantics that instantiate it because none
of its *statements* mentions a semantics and none needs an import this module
did not already have. `Lara.Context.obsSem`
(`lean/Lara/Context/Observation.lean:119`) is the instantiation the milestone
exists for; `docs/theory-m4-generic-observation.md` §2 records the choice.
-/

import Lara.Context.Compose
import Lara.EraseTransport

namespace Lara.Context

open Lara.Support Lara.Attack Lara.Compile Lara.Erase

/-! ### Relabeling a fragment -/

/-- Relabel every assurance of a fragment's declared material. The interface is
untouched: leaf declarations, ground atoms, imports and exports carry no
certificate. -/
def mapAssurFrag (f : Assurance → Assurance) (F : Fragment) : Fragment :=
  { F with args := F.args.map (mapAssur f), atts := F.atts.map (mapAssurAtt f) }

/-- Relabel a conclusion-cache entry: the term moves, the conclusion does not. -/
def relabelEntry (f : Assurance → Assurance) (p : SupportTerm × Atom) :
    SupportTerm × Atom := (mapAssur f p.1, p.2)

section Relabel

variable {f : Assurance → Assurance} {C : Context} {F : Fragment}

@[simp] theorem mapAssurFrag_declared : (mapAssurFrag f F).declared = F.declared := rfl
@[simp] theorem mapAssurFrag_imports : (mapAssurFrag f F).imports = F.imports := rfl
@[simp] theorem mapAssurFrag_sigma : (mapAssurFrag f F).sigma = F.sigma := rfl
@[simp] theorem mapAssurFrag_policy : (mapAssurFrag f F).policy = F.policy := rfl
@[simp] theorem mapAssurFrag_exports : (mapAssurFrag f F).exports = F.exports := rfl
@[simp] theorem mapAssurFrag_args :
    (mapAssurFrag f F).args = F.args.map (mapAssur f) := rfl
@[simp] theorem mapAssurFrag_atts :
    (mapAssurFrag f F).atts = F.atts.map (mapAssurAtt f) := rfl

/-- **The guard cannot see a relabel.** Compatibility is an interface property,
so exactly the contexts that link with `F` link with its relabeling — which is
what lets the congruence quantify over one set of contexts. -/
theorem linkFault_mapAssurFrag : linkFault C (mapAssurFrag f F) = linkFault C F := rfl

theorem linkOk_mapAssurFrag : linkOk C (mapAssurFrag f F) = linkOk C F := rfl

theorem linkGamma_mapAssurFrag : linkGamma C (mapAssurFrag f F) = linkGamma C F := rfl

theorem linkGround_mapAssurFrag : linkGround C (mapAssurFrag f F) = linkGround C F := rfl

/-! ### The relabel commutes with the merge -/

theorem dedupList_map_of_injective {g : SupportTerm → SupportTerm}
    (hg : Function.Injective g) :
    ∀ (l : List SupportTerm), dedupList (l.map g) = (dedupList l).map g
  | [] => rfl
  | w :: ws => by
      simp only [List.map_cons, dedupList, dedupList_map_of_injective hg ws]
      by_cases h : w ∈ dedupList ws
      · rw [if_pos h, if_pos (List.mem_map.mpr ⟨w, h, rfl⟩)]
      · rw [if_neg h, if_neg (fun hc => h (by
          obtain ⟨w', hw', heq⟩ := List.mem_map.mp hc
          exact hg heq ▸ hw')), List.map_cons]

/-- A list fixed by a map is fixed pointwise. -/
theorem eq_of_map_eq_self {α : Type} {g : α → α} :
    ∀ {l : List α}, l.map g = l → ∀ x ∈ l, g x = x
  | [], _, _, hx => absurd hx (by simp)
  | v :: vs, h, x, hx => by
      simp only [List.map_cons, List.cons.injEq] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact h.1
      · exact eq_of_map_eq_self h.2 x hx'

/-! ### The relabel commutes with the saturation

This is the one lemma the milestone needed that did not already exist. A
uniform relabel preserves every input the saturation reads: conclusions (the
certificate payload never enters them), root rule identities (so
`conflictAttackableB` is invariant), and therefore contrary matches. -/

theorem conflictAttackableB_mapAssur (Pi : RuleId → Option Rule) (t : SupportTerm) :
    conflictAttackableB Pi (mapAssur f t) = conflictAttackableB Pi t := by
  cases t <;> rfl

theorem attackFor_mapAssur (s t : SupportTerm) :
    attackFor (mapAssur f s) (mapAssur f t) = mapAssurAtt f (attackFor s t) := by
  cases t <;> rfl

/-- **Saturation commutes with a relabel**, entry by entry. This is the one
lemma the milestone needed that did not already exist. -/
theorem crossAttsFrom_map (canon : String → String) (dp : DefeatPolicy)
    (Pi : RuleId → Option Rule) :
    ∀ (srcs tgts : List (SupportTerm × Atom)),
      crossAttsFrom canon dp Pi (srcs.map (relabelEntry f)) (tgts.map (relabelEntry f))
        = (crossAttsFrom canon dp Pi srcs tgts).map (mapAssurAtt f)
  | [], _ => rfl
  | s :: srcs, tgts => by
      have inner : ∀ (ts : List (SupportTerm × Atom)),
          (ts.map (relabelEntry f)).filterMap
              (fun t => if contraryMatchB canon dp (relabelEntry f s).2 t.2 &&
                  conflictAttackableB Pi t.1 then
                some (attackFor (relabelEntry f s).1 t.1) else none)
            = (ts.filterMap
                (fun t => if contraryMatchB canon dp s.2 t.2 &&
                    conflictAttackableB Pi t.1 then
                  some (attackFor s.1 t.1) else none)).map (mapAssurAtt f) := by
        intro ts
        rw [List.filterMap_map, List.map_filterMap]
        refine congrArg (fun g => ts.filterMap g) (funext fun t => ?_)
        simp only [Function.comp_apply, relabelEntry, conflictAttackableB_mapAssur]
        by_cases h : contraryMatchB canon dp s.2 t.2 && conflictAttackableB Pi t.1
        · rw [if_pos h, if_pos h, Option.map_some, attackFor_mapAssur]
        · rw [if_neg h, if_neg h, Option.map_none]
      have IH := crossAttsFrom_map canon dp Pi srcs tgts
      simp only [crossAttsFrom] at IH
      simp only [crossAttsFrom, List.map_cons, List.flatMap_cons, List.map_append,
        inner tgts, IH]

end Relabel

/-! ### The cache under a relabel

The saturation reads a cache, so the commutation above only bites once the two
caches correspond. They do exactly when every declared argument is complete
checked support — which is the `SideOk.support` field, and which
`Compile.CheckedProgram.complete` forces on any accepted program anyway. -/

section Cache

variable {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
  {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
  {f : Assurance → Assurance}

/-- The acceptance-preservation hypothesis of result 9, in the form
`Lara.EraseTransport` states it. -/
abbrev AssurPreserving (f : Assurance → Assurance)
    (CertOk₁ CertOk₂ : BackendId → Digest → CertRef → List Atom → Atom → Prop) : Prop :=
  ∀ (r : Rule) (As : List Atom) (C : Atom) (α : Assurance),
    AssuranceOk CertOk₁ r As C α → AssuranceOk CertOk₂ r As C (f α)

/-- On a list whose terms all check, the cache is the list — so a relabel moves
it entrywise. -/
theorem conclusionCache_map
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂)) :
    ∀ (args : List SupportTerm),
      (∀ w ∈ args, ∃ C, HasSupport canon Pi Gamma (certOkOf reg₁) w C []) →
      conclusionCache Pi Gamma reg₂ (args.map (mapAssur f))
        = (conclusionCache Pi Gamma reg₁ args).map (relabelEntry f)
  | [], _ => rfl
  | w :: ws, hsup => by
      obtain ⟨Cw, hCw⟩ := hsup w List.mem_cons_self
      have h₁ : conclusionOf Pi Gamma reg₁ w = some Cw :=
        conclusionOf_eq_some_iff.mpr hCw
      have h₂ : conclusionOf Pi Gamma reg₂ (mapAssur f w) = some Cw :=
        conclusionOf_eq_some_iff.mpr (hasSupport_mapAssur hpres hCw)
      have IH := conclusionCache_map hpres ws
        (fun v hv => hsup v (List.mem_cons_of_mem _ hv))
      simp only [conclusionCache] at IH ⊢
      simp only [List.map_cons, List.filterMap_cons, h₁, h₂, Option.map_some, IH]
      rfl

end Cache

/-! ### Stage-2 well-sortedness ignores certificates

`Lara.termWellSorted` inspects a rule instance's identifier, substitution,
premises and discharges — never its assurance. So the signature stage cannot
see a relabel, which is what lets acceptance transport. -/

section WellSorted

variable {f : Assurance → Assurance} {sg : Sigma.Sigma} {P : Policy.Policy}

mutual
  theorem termWellSorted_mapAssur :
      ∀ w : SupportTerm, termWellSorted sg P (mapAssur f w) = termWellSorted sg P w
    | .leaf _ => rfl
    | .inst rn θ ws D H α => by
        simp only [mapAssur, termWellSorted, termsWellSorted_mapAssur ws,
          dischargesWellSorted_mapAssur D]
  theorem termsWellSorted_mapAssur :
      ∀ ws : List SupportTerm,
        termsWellSorted sg P (mapAssurList f ws) = termsWellSorted sg P ws
    | [] => rfl
    | w :: ws => by
        simp only [mapAssurList, termsWellSorted, termWellSorted_mapAssur w,
          termsWellSorted_mapAssur ws]
  theorem dischargesWellSorted_mapAssur :
      ∀ D : List (QuestionId × SupportTerm),
        dischargesWellSorted sg P (mapAssurDis f D) = dischargesWellSorted sg P D
    | [] => rfl
    | (q, w) :: rest => by
        simp only [mapAssurDis, dischargesWellSorted, termWellSorted_mapAssur w,
          dischargesWellSorted_mapAssur rest]
end

theorem argsWellSorted_map (args : List SupportTerm) :
    argsWellSorted sg P (args.map (mapAssur f)) = argsWellSorted sg P args := by
  rw [argsWellSorted, argsWellSorted, ← mapAssurList_eq, termsWellSorted_mapAssur]

/-- The signature stage cannot distinguish a program from its relabeling. -/
theorem signatureStage_map {ground : List Atom} {unit₁ unit₂ : Lara.Unit}
    (hsigma : unit₂.sigma = unit₁.sigma) (hpolicy : unit₂.policy = unit₁.policy)
    (hargs : unit₂.args = unit₁.args.map (mapAssur f)) :
    Check.Unit.signatureStage ground unit₂ = Check.Unit.signatureStage ground unit₁ := by
  simp only [Check.Unit.signatureStage, hsigma, hpolicy, hargs, argsWellSorted_map]

end WellSorted

/-! ### Coverage transports along a relabel -/

section Coverage

variable {f : Assurance → Assurance}

theorem attackOcc_mapAssurAtt {k : Attack} {t : SupportTerm} (h : AttackOcc k t) :
    AttackOcc (mapAssurAtt f k) (mapAssur f t) := by
  cases k with
  | rebut w u =>
      simp only [AttackOcc] at h
      subst h
      rfl
  | undercut w u π =>
      simp only [AttackOcc, mapAssurAtt] at h ⊢
      rw [mapAssur_subterm, h]; rfl
  | undermine w u π =>
      simp only [AttackOcc, mapAssurAtt] at h ⊢
      rw [mapAssur_subterm, h]; rfl

theorem contains_mapAssur {v t : SupportTerm} (h : Contains v t) :
    Contains (mapAssur f v) (mapAssur f t) := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨π, by rw [mapAssur_subterm, hπ]; rfl⟩

/-- **Declared coverage survives a relabel.** -/
theorem covered_mapAssur {atts : List Attack} {source target : SupportTerm}
    (h : Covered atts source target) :
    Covered (atts.map (mapAssurAtt f)) (mapAssur f source) (mapAssur f target) := by
  obtain ⟨k, hk, hsrc, t, hocc, hcont⟩ := h
  exact ⟨mapAssurAtt f k, List.mem_map.mpr ⟨k, hk, rfl⟩,
    by rw [mapAssurAtt_source, hsrc], mapAssur f t,
    attackOcc_mapAssurAtt hocc, contains_mapAssur hcont⟩

theorem conflictAttackable_mapAssur {Pi : RuleId → Option Rule} {t : SupportTerm}
    (h : ConflictAttackable Pi (mapAssur f t)) : ConflictAttackable Pi t := by
  rw [← conflictAttackableB_iff] at h ⊢
  rw [← conflictAttackableB_mapAssur Pi t]
  exact h

end Coverage

/-! ### The linked program under a relabel -/

section Linked

variable {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
  {f : Assurance → Assurance} {C : Context} {F : Fragment}

/-- **The saturation commutes with the relabel.** The context's cache is
unchanged because the relabel fixes the context's material; the fragment's
cache moves entrywise; and `crossAttsFrom_map` does the rest. -/
theorem crossAtts_relabel
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hfixArgs : C.frame.args.map (mapAssur f) = C.frame.args)
    (hCsup : ∀ w ∈ C.frame.args, ∃ A,
      HasSupport canon F.policy.ruleLookup (linkGamma C F) (certOkOf reg₁) w A [])
    (hFsup : ∀ w ∈ F.args, ∃ A,
      HasSupport canon F.policy.ruleLookup (linkGamma C F) (certOkOf reg₁) w A []) :
    crossAtts reg₂ (linkGamma C F) C (mapAssurFrag f F)
      = (crossAtts reg₁ (linkGamma C F) C F).map (mapAssurAtt f) := by
  have hcc : conclusionCache F.policy.ruleLookup (linkGamma C F) reg₂ C.frame.args
      = (conclusionCache F.policy.ruleLookup (linkGamma C F) reg₁ C.frame.args).map
          (relabelEntry f) := by
    have h := conclusionCache_map hpres C.frame.args hCsup
    rw [hfixArgs] at h
    exact h
  have hcf : conclusionCache F.policy.ruleLookup (linkGamma C F) reg₂
        (F.args.map (mapAssur f))
      = (conclusionCache F.policy.ruleLookup (linkGamma C F) reg₁ F.args).map
          (relabelEntry f) := conclusionCache_map hpres F.args hFsup
  simp only [crossAtts, mapAssurFrag_args, mapAssurFrag_policy, hcc, hcf,
    crossAttsFrom_map, List.map_append]

/-- **`link_relabel_commutes`.** The linked unit of the relabeled fragment is
the relabeling of the linked unit — arguments and attacks alike. Everything the
congruence needs from `Erase.edgeB_relabel` is exactly this. -/
theorem link_relabel_commutes
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hfixArgs : C.frame.args.map (mapAssur f) = C.frame.args)
    (hfixAtts : C.frame.atts.map (mapAssurAtt f) = C.frame.atts)
    (hCsup : ∀ w ∈ C.frame.args, ∃ A,
      HasSupport canon F.policy.ruleLookup (linkGamma C F) (certOkOf reg₁) w A [])
    (hFsup : ∀ w ∈ F.args, ∃ A,
      HasSupport canon F.policy.ruleLookup (linkGamma C F) (certOkOf reg₁) w A []) :
    (linkedUnit reg₂ C (mapAssurFrag f F)).args
        = (linkedUnit reg₁ C F).args.map (mapAssur f) ∧
      (linkedUnit reg₂ C (mapAssurFrag f F)).atts
        = (linkedUnit reg₁ C F).atts.map (mapAssurAtt f) := by
  constructor
  · show dedupList (C.frame.args ++ F.args.map (mapAssur f))
        = (dedupList (C.frame.args ++ F.args)).map (mapAssur f)
    have h := dedupList_map_of_injective (mapAssur_injective hf) (C.frame.args ++ F.args)
    rw [List.map_append, hfixArgs] at h
    exact h
  · show C.frame.atts ++ F.atts.map (mapAssurAtt f)
          ++ crossAtts reg₂ (linkGamma C F) C (mapAssurFrag f F)
        = (C.frame.atts ++ F.atts ++ crossAtts reg₁ (linkGamma C F) C F).map
            (mapAssurAtt f)
    rw [crossAtts_relabel hpres hfixArgs hCsup hFsup, List.map_append, List.map_append,
      hfixAtts]

end Linked

/-! ### Acceptance transports -/

section Acceptance

variable {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
  {f : Assurance → Assurance} {Gamma : LeafId → Option Atom}

/-- **Attack completeness transports along a relabel.** The relabel preserves
conclusions, so the conflicts visible on the relabeled side are the images of
the conflicts the original side already covered. -/
theorem attackComplete_map {Pi : RuleId → Option Rule} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack}
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hcomplete : ∀ w ∈ args, ∃ A, HasSupport canon Pi Gamma (certOkOf reg₁) w A [])
    (h : AttackComplete canon Pi Gamma (certOkOf reg₁) dp args atts) :
    AttackComplete canon Pi Gamma (certOkOf reg₂) dp
      (args.map (mapAssur f)) (atts.map (mapAssurAtt f)) := by
  intro source' hs' target' ht' Cs Ct hsSup htSup hcm hca
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hs'
  obtain ⟨target, ht, rfl⟩ := List.mem_map.mp ht'
  obtain ⟨Cs₀, hCs₀⟩ := hcomplete source hs
  obtain ⟨Ct₀, hCt₀⟩ := hcomplete target ht
  have hCsEq : Cs₀ = Cs :=
    (hasSupport_unique (hasSupport_mapAssur hpres hCs₀) hsSup).1
  have hCtEq : Ct₀ = Ct :=
    (hasSupport_unique (hasSupport_mapAssur hpres hCt₀) htSup).1
  exact covered_mapAssur
    (h source hs target ht Cs₀ Ct₀ hCs₀ hCt₀ (by rw [hCsEq, hCtEq]; exact hcm)
      (conflictAttackable_mapAssur hca))

/-- The signature stage of an accepted unit fell through. -/
theorem signatureStage_of_ok {ground : List Atom} {unit : Lara.Unit}
    {reg : BackendRegistry canon}
    {accepted : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (h : Check.Unit.checkUnit Gamma reg ground unit = .ok accepted) :
    Check.Unit.signatureStage ground unit = none := by
  obtain ⟨hsigma, hwf, hpol, hground, hargs, hpolicy, -, -, hargsEq, -, -, -⟩ :=
    Check.Unit.checkUnit_sound h
  rw [Check.Unit.signatureStage, if_neg (by rw [← hsigma, hwf]; simp),
    if_neg (by rw [← hsigma, ← hpolicy, hpol]; simp),
    if_neg (by rw [← hsigma, hground]; simp),
    if_neg (by rw [← hsigma, ← hpolicy, ← hargsEq, hargs]; simp)]

/-- **Acceptance transports along an injective, acceptance-preserving
relabel.** Every premise of `Check.Unit.checkUnit_complete` is discharged from
the accepted original: the signature stage cannot see certificates, the merge's
`Nodup` survives an injective map, and support, typing and attack completeness
transport. -/
theorem checkUnit_map {ground : List Atom} {unit₁ unit₂ : Lara.Unit}
    {accepted₁ : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg₁)}
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hsigma : unit₂.sigma = unit₁.sigma) (hpolicy : unit₂.policy = unit₁.policy)
    (hargs : unit₂.args = unit₁.args.map (mapAssur f))
    (hatts : unit₂.atts = unit₁.atts.map (mapAssurAtt f))
    (h₁ : Check.Unit.checkUnit Gamma reg₁ ground unit₁ = .ok accepted₁) :
    ∃ accepted₂, Check.Unit.checkUnit Gamma reg₂ ground unit₂ = .ok accepted₂ := by
  obtain ⟨-, -, -, -, -, hpolEq, hruleIds, hpolWf, hargsEq, hattsEq,
    hattackComplete, -⟩ := Check.Unit.checkUnit_sound h₁
  have hscope : Policy.firstOutOfScope? unit₂.policy = none := by
    rw [hpolicy, ← hpolEq]; exact accepted₁.scopes_wf
  refine Check.Unit.checkUnit_complete
    (signatureStage_map hsigma hpolicy hargs ▸ signatureStage_of_ok h₁)
    hscope (by rw [hpolicy, ← hpolEq]; exact hruleIds)
    (by rw [hpolicy, ← hpolEq]; exact hpolWf)
    (by
      rw [hargs]
      have hnd : unit₁.args.Nodup := hargsEq ▸ accepted₁.program.nodup
      exact hnd.map (mapAssur f)
        (fun _ _ hab habeq => hab (mapAssur_injective hf habeq)))
    ?_ ?_ ?_ ?_ ?_
  · intro w hw
    rw [hargs] at hw
    obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.mp hw
    obtain ⟨A, hA⟩ := accepted₁.program.complete w₀ (by rw [hargsEq]; exact hw₀)
    rw [hpolicy, ← hpolEq]
    exact ⟨A, hasSupport_mapAssur hpres hA⟩
  · intro k hk
    rw [hatts] at hk
    obtain ⟨k₀, hk₀, rfl⟩ := List.mem_map.mp hk
    rw [hpolicy, ← hpolEq]
    exact hasAttack_mapAssur hpres (accepted₁.program.typed k₀ (by rw [hattsEq]; exact hk₀))
  · intro k hk
    rw [hatts] at hk
    obtain ⟨k₀, hk₀, rfl⟩ := List.mem_map.mp hk
    rw [hargs, mapAssurAtt_source]
    exact List.mem_map.mpr ⟨k₀.source,
      hargsEq ▸ accepted₁.program.source_declared k₀ (by rw [hattsEq]; exact hk₀), rfl⟩
  · intro k hk
    rw [hatts] at hk
    obtain ⟨k₀, hk₀, rfl⟩ := List.mem_map.mp hk
    rw [hargs, mapAssurAtt_target]
    exact List.mem_map.mpr ⟨k₀.target,
      hargsEq ▸ accepted₁.program.target_declared k₀ (by rw [hattsEq]; exact hk₀), rfl⟩
  · rw [hargs, hatts, hpolicy, ← hpolEq, ← hargsEq, ← hattsEq]
    exact attackComplete_map hpres accepted₁.program.complete accepted₁.attack_complete

end Acceptance

/-! ### The carrier of a linked program under a relabel -/

section Carrier

variable {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
  {f : Assurance → Assurance} {Gamma : LeafId → Option Atom}

/-- Node conclusions are certificate-independent: the relabeled unit's cache
records the same conclusion at every position. -/
theorem nodes_conclusion_map
    {acc₁ : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg₁)}
    {acc₂ : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg₂)}
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hpol : acc₂.policy.ruleLookup = acc₁.policy.ruleLookup)
    (hargs : acc₂.program.args = acc₁.program.args.map (mapAssur f)) :
    acc₂.nodes.map (·.conclusion) = acc₁.nodes.map (·.conclusion) := by
  refine List.ext_getElem? (fun i => ?_)
  have ht₁ : (acc₁.nodes.map (·.term))[i]? = acc₁.program.args[i]? := by
    rw [acc₁.nodes_terms]
  have ht₂ : (acc₂.nodes.map (·.term))[i]? = acc₂.program.args[i]? := by
    rw [acc₂.nodes_terms]
  rw [List.getElem?_map] at ht₁ ht₂
  rw [List.getElem?_map, List.getElem?_map]
  cases h₁ : acc₁.nodes[i]? with
  | none =>
      rw [h₁] at ht₁
      have hargs₁ : acc₁.program.args[i]? = none := ht₁.symm
      have hargs₂ : acc₂.program.args[i]? = none := by
        rw [hargs, List.getElem?_map, hargs₁]; rfl
      rw [hargs₂] at ht₂
      cases h₂ : acc₂.nodes[i]? with
      | none => rfl
      | some n₂ => rw [h₂] at ht₂; exact absurd ht₂ (by simp)
  | some n₁ =>
      rw [h₁] at ht₁
      have hargs₂ : acc₂.program.args[i]? = some (mapAssur f n₁.term) := by
        rw [hargs, List.getElem?_map, ← ht₁]; rfl
      rw [hargs₂] at ht₂
      cases h₂ : acc₂.nodes[i]? with
      | none => rw [h₂] at ht₂; exact absurd ht₂ (by simp)
      | some n₂ =>
          rw [h₂] at ht₂
          have hterm : n₂.term = mapAssur f n₁.term := Option.some.inj ht₂
          have hv₁ : HasSupport canon acc₂.policy.ruleLookup Gamma (certOkOf reg₂)
              (mapAssur f n₁.term) n₁.conclusion [] := by
            rw [hpol]; exact hasSupport_mapAssur hpres n₁.valid
          have hv₂ : HasSupport canon acc₂.policy.ruleLookup Gamma (certOkOf reg₂)
              (mapAssur f n₁.term) n₂.conclusion [] := hterm ▸ n₂.valid
          simp only [Option.map_some]
          exact congrArg some (hasSupport_unique hv₂ hv₁).1

/-- **The M1 carrier is relabel-invariant.** Node conclusions agree by the
lemma above; the edge relation agrees by `Erase.edgeB_relabel`, which is the
whole content of result 9's graph isomorphism. -/
theorem compileUnit_map
    {acc₁ : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg₁)}
    {acc₂ : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg₂)}
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hpol : acc₂.policy = acc₁.policy)
    (hargs : acc₂.program.args = acc₁.program.args.map (mapAssur f))
    (hatts : acc₂.program.atts = acc₁.program.atts.map (mapAssurAtt f)) :
    Invariants.compileUnit acc₂ = Invariants.compileUnit acc₁ := by
  have hedge : ∀ i j, Compile.edgeB acc₂.program i j = Compile.edgeB acc₁.program i j := by
    intro i j
    simp only [Compile.edgeB, hargs, hatts, List.getElem?_map]
    cases acc₁.program.args[i]? with
    | none => rfl
    | some source =>
        cases acc₁.program.args[j]? with
        | none => rfl
        | some target => exact coveredB_relabel hf acc₁.program.atts source target
  simp only [Invariants.compileUnit,
    nodes_conclusion_map hpres (by rw [hpol]) hargs]
  exact congrArg _ (funext fun i => funext fun j => hedge i j)

end Carrier

/-! ### The headline: contextual representation independence -/

/-- **Contextual equivalence** of two fragments under one registry: every
context produces the same detailed outcome. Incompatible links, checker
rejections, and observed status lists remain distinct; a logical relation
characterizing this relation is Part B. -/
def CtxEquiv {canon : String → String} (reg : BackendRegistry canon)
    (F₁ F₂ : Fragment) : Prop :=
  ∀ C : Context, obs reg C F₁ = obs reg C F₂

/-- The relabel leaves the context's own material alone. A backend swap inside
a fragment is not licensed to rename the *context's* certificates, and a
statement that let it would be comparing two different contexts. -/
structure FixesContext (f : Assurance → Assurance) (C : Context) : Prop where
  args : C.frame.args.map (mapAssur f) = C.frame.args
  atts : C.frame.atts.map (mapAssurAtt f) = C.frame.atts

/-- **A context admissible for a fragment**: the guard passes and both sides'
declared material is well-formed relative to the linked environment. This is
what "compatible well-formed context" means, and it is exactly the input
`link_checked` needs — nothing here mentions the conclusion. -/
structure Admissible {canon : String → String} (reg : BackendRegistry canon)
    (C : Context) (F : Fragment) : Prop where
  guard : linkOk C F = true
  ctx : SideOk canon reg (linkGamma C F) F.policy C.frame.args C.frame.atts
  frag : SideOk canon reg (linkGamma C F) F.policy F.args F.atts
  signature : Check.Unit.signatureStage (linkGround C F) (linkedUnit reg C F) = none
  scope : Policy.firstOutOfScope? F.policy = none
  ruleIds : (F.policy.rules.map (·.id)).Nodup
  policy : Policy.WellFormed canon F.policy

/-! ### The observation, parameterized by how a claim is read

`obs` is grounded-specific at exactly one point: it reads `Invariants.status`
off the linked carrier. Every step before that read — the link guard, the
whole-unit checker, the carrier itself — is already free of any semantics.
These declarations make that structural fact usable by leaving the reading a
parameter. None of these *statements* mentions a semantics; the semantics
instance is `Lara.Context.obsSem` (`lean/Lara/Context/Observation.lean:119`).

The congruence over this parameter, `obsGen_congr`, needs the relabeling
variables and so appears in the `Headline` section below (`:778`), beside the
grounded instance it now carries the proof for. -/

/-- **The observation of a link through an arbitrary projection.** The control
flow is `Lara.Context.obs`'s, verbatim (`lean/Lara/Context/Fragment.lean:459`):
guard first, then the whole-unit checker on the linked unit, then — and only
then — read the exported conclusions off the M1 carrier of the accepted unit.
The single difference is that `obs` hard-codes `Invariants.status canon` where
this takes `g`.

`g` receives the *linked* carrier, not the fragment's own: an open fragment has
no framework of its own (D10), and `fragmentCarrier`
(`lean/Lara/Context/Fragment.lean:407`) is the fragment-relative substitute.
What is projected here is always the carrier of the context-plus-fragment unit,
which is what makes the result an *observation* in the contextual sense. -/
def obsGen {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} (reg : BackendRegistry canon)
    (C : Context) (F : Fragment) : ObservationOf α :=
  match linkFault C F with
  | some fault => .incompatible fault
  | none =>
      match Check.Unit.checkUnit (linkGamma C F) reg (linkGround C F)
          (linkedUnit reg C F) with
      | .ok accepted =>
          .observed (F.exports.map (fun p => g (Invariants.compileUnit accepted) p))
      | .error error => .rejected error

/-- **The incompatible arm is projection-independent by construction.** If the
link guard fires, `obsGen` reports the fault for *every* `g` — the projection is
never consulted, because `linkFault` is matched before the checker runs and long
before any carrier exists to project.

This is worth stating as a theorem rather than leaving to `decide` at each
fixture. `decide` settles the arm for one concrete semantics at a time; this
settles it uniformly, which is what a witness quantified over all of
`ExtensionSemantics` needs (via `obsSem_incompatible`). Nothing here says which
links fault — that is `linkFault`'s business, and this theorem is indifferent to
it. -/
theorem obsGen_incompatible {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} {reg : BackendRegistry canon}
    {C : Context} {F : Fragment} {fault : LinkFault}
    (h : linkFault C F = some fault) :
    obsGen g reg C F = .incompatible fault := by
  simp only [obsGen, h]

/-- **The rejected arm is projection-independent by construction.** A compatible
link whose merged unit the whole-unit checker rejects reports that `UnitError`
for every `g`, for the same structural reason as `obsGen_incompatible`:
`Check.Unit.checkUnit` runs on the linked unit before `Invariants.compileUnit`
is ever applied, so no projection can influence — or observe — the rejection.

The `hlink` hypothesis is `linkFault C F = none` rather than `linkOk C F = true`
because that is the form the definitional match needs; `obsGen_eq_of_ok` takes
the `linkOk` spelling instead and converts, which is also the spelling its
grounded instance `obs_eq_of_ok` (`lean/Lara/Context/Equivalence.lean:675`)
exposes. -/
theorem obsGen_rejected {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} {reg : BackendRegistry canon}
    {C : Context} {F : Fragment} {error : Check.Unit.UnitError}
    (hlink : linkFault C F = none)
    (h : Check.Unit.checkUnit (linkGamma C F) reg (linkGround C F)
      (linkedUnit reg C F) = .error error) :
    obsGen g reg C F = .rejected error := by
  simp only [obsGen, hlink, h]

/-- **An accepted link observes through its carrier**, generically. This is
`obs_eq_of_ok` (`lean/Lara/Context/Equivalence.lean:675`) with the projection
left open — and it carries the proof that theorem used to run, `obs_eq_of_ok`
now being this one instantiated: `linkOk` is `Option.isNone` of `linkFault`, so
the guard hypothesis rewrites into the shape the match wants, and the two
matches then reduce.

Note the accepted unit `acc` appears in the conclusion. That is not incidental
bookkeeping: the whole-unit checker is what produces the `CheckedUnit` whose node
cache `Invariants.compileUnit` reads, so there is no way to state the observed
arm without naming it. Every congruence below works by producing an `acc` on
each side and then proving the two carriers equal. -/
theorem obsGen_eq_of_ok {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} {reg : BackendRegistry canon}
    {C : Context} {F : Fragment}
    {acc : Lara.Unit.CheckedUnit canon (linkGamma C F) (certOkOf reg)}
    (hlink : linkOk C F = true)
    (h : Check.Unit.checkUnit (linkGamma C F) reg (linkGround C F)
      (linkedUnit reg C F) = .ok acc) :
    obsGen g reg C F
      = .observed (F.exports.map (fun p => g (Invariants.compileUnit acc) p)) := by
  have hfault : linkFault C F = none := by
    simpa only [linkOk, Option.isNone_iff_eq_none] using hlink
  simp only [obsGen, hfault, h]

/-- **The frozen `obs` is `obsGen` at the grounded projection — definitionally.**
`rfl` rather than a proof is the point: the D4 observation is not being
reinterpreted, it is being read at one instantiation of a parameter that was
implicit in it all along. Everything the link contributes — the guard fault, the
checker's rejection, the accepted carrier — is shared, and this is the equation
that says so.

Stating it requires `obs` and `obsGen` to land in the *same* type, which is why
`ObservationOf` replaced the standalone `Observation` inductive
(`lean/Lara/Context/Fragment.lean`) rather than being introduced beside it. -/
theorem obs_eq_obsGen {canon : String → String} (reg : BackendRegistry canon)
    (C : Context) (F : Fragment) :
    obs reg C F = obsGen (Invariants.status canon) reg C F := rfl

section Headline

variable {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
  {f : Assurance → Assurance} {C : Context} {F : Fragment}

/-- An accepted link observes through its carrier. -/
theorem obs_eq_of_ok {reg : BackendRegistry canon}
    {acc : Lara.Unit.CheckedUnit canon (linkGamma C F) (certOkOf reg)}
    (hlink : linkOk C F = true)
    (h : Check.Unit.checkUnit (linkGamma C F) reg (linkGround C F)
      (linkedUnit reg C F) = .ok acc) :
    obs reg C F
      = .observed
          (F.exports.map (fun p => Invariants.status canon (Invariants.compileUnit acc) p)) :=
  obsGen_eq_of_ok _ hlink h

/-- An admissible context yields an accepted link. -/
theorem exists_accepted_of_admissible {reg : BackendRegistry canon}
    (hadm : Admissible reg C F) :
    ∃ acc, Check.Unit.checkUnit (linkGamma C F) reg (linkGround C F)
      (linkedUnit reg C F) = .ok acc :=
  link_checked (link_eq_some hadm.guard) hadm.signature hadm.scope hadm.ruleIds
    hadm.policy hadm.ctx hadm.frag

/-- The relabeled link is accepted too. -/
theorem exists_accepted_relabel
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F) (hfix : FixesContext f C)
    {acc₁ : Lara.Unit.CheckedUnit canon (linkGamma C F) (certOkOf reg₁)}
    (h₁ : Check.Unit.checkUnit (linkGamma C F) reg₁ (linkGround C F)
      (linkedUnit reg₁ C F) = .ok acc₁) :
    ∃ acc₂, Check.Unit.checkUnit (linkGamma C F) reg₂ (linkGround C F)
      (linkedUnit reg₂ C (mapAssurFrag f F)) = .ok acc₂ := by
  obtain ⟨hargs, hatts⟩ :=
    link_relabel_commutes hf hpres hfix.args hfix.atts hadm.ctx.support hadm.frag.support
  exact checkUnit_map (Gamma := linkGamma C F) (ground := linkGround C F)
    (unit₁ := linkedUnit reg₁ C F) (unit₂ := linkedUnit reg₂ C (mapAssurFrag f F))
    hf hpres rfl rfl hargs hatts h₁

/-- **The two links present the same carrier.** This is the whole content of
the congruence; `obs` reads statuses off it, and the surface corollary reads
the framework off it. -/
theorem compileUnit_link_relabel
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F) (hfix : FixesContext f C)
    {acc₁ : Lara.Unit.CheckedUnit canon (linkGamma C F) (certOkOf reg₁)}
    {acc₂ : Lara.Unit.CheckedUnit canon (linkGamma C F) (certOkOf reg₂)}
    (h₁ : Check.Unit.checkUnit (linkGamma C F) reg₁ (linkGround C F)
      (linkedUnit reg₁ C F) = .ok acc₁)
    (h₂ : Check.Unit.checkUnit (linkGamma C F) reg₂ (linkGround C F)
      (linkedUnit reg₂ C (mapAssurFrag f F)) = .ok acc₂) :
    Invariants.compileUnit acc₂ = Invariants.compileUnit acc₁ := by
  obtain ⟨hargs, hatts⟩ :=
    link_relabel_commutes hf hpres hfix.args hfix.atts hadm.ctx.support hadm.frag.support
  have hsound₁ := Check.Unit.checkUnit_sound h₁
  have hsound₂ := Check.Unit.checkUnit_sound h₂
  exact compileUnit_map hf hpres
    (by rw [hsound₁.2.2.2.2.2.1, hsound₂.2.2.2.2.2.1]; rfl)
    (by rw [hsound₂.2.2.2.2.2.2.2.2.1, hsound₁.2.2.2.2.2.2.2.2.1]; exact hargs)
    (by rw [hsound₂.2.2.2.2.2.2.2.2.2.1, hsound₁.2.2.2.2.2.2.2.2.2.1]; exact hatts)

/-- **Contextual representation independence, for every projection at once.**

An injective, acceptance-preserving relabel of a fragment's certificates is
unobservable in every admissible context whose own assurances the relabel fixes
— and *whatever* is read off the resulting carrier. This is
`backend_replacement_congruence` (`lean/Lara/Context/Equivalence.lean:820`) with
`Invariants.status canon` replaced by an arbitrary `g`. It carries the proof
that theorem used to carry; that theorem is now this one instantiated.

**Why the generalization is free.** The argument produces an accepted link on
each side and then appeals to `compileUnit_link_relabel`
(`lean/Lara/Context/Equivalence.lean:712`), whose conclusion is
`Invariants.compileUnit acc₂ = Invariants.compileUnit acc₁` — an equation
between carriers, not a pointwise agreement between them:

      reg₁, F                                  reg₂, mapAssurFrag f F
         |                                              |
         | linkedUnit reg₁ C F                          | linkedUnit reg₂ C (mapAssurFrag f F)
         v                                              v
      checkUnit ... = .ok acc₁                  checkUnit ... = .ok acc₂
         |                                              |
         | Invariants.compileUnit                       | Invariants.compileUnit
         \                                              /
          \____________ compileUnit_link_relabel ______/
                              |
                              v
                    one carrier  G : StructuredAF
                              |
                              |  F.exports.map (fun p => g G p)   -- any g whatsoever
                              v
                        ObservationOf.observed …

Once the two sides meet at a single `G`, the projection hanging off it is
applied to the same argument on both branches, so it cannot distinguish them.

**Why there is no `AttackExtensional` hypothesis, and why there must not be.**
`Lara.Observation.observe_congr` (`lean/Lara/Observation.lean:406`) does assume
`AttackExtensional sem.spec`, but it is solving a different problem: it moves an
observation between two *distinct* frameworks that merely agree pointwise on the
carrier, and extensionality is what licenses concluding that the extensions
agree. Here the frameworks are equal, so no such licence is needed. A generic
statement that assumed `AttackExtensional` anyway would be strictly weaker than
its grounded ancestor `backend_replacement_congruence`, which assumes nothing of
the kind — and would not deserve to be called its generalization.

The admissibility hypothesis is not removable, and the reason is stated here
rather than at the grounded instance because this is now the theorem that
carries the proof: `obsGen` reports a checker rejection separately from an
observed list, so a forward-only acceptance hypothesis — which lets `reg₂`
accept what `reg₁` rejects — could turn an observation into a rejection. An
unconditional statement would need acceptance to be two-way, which is a
different and stronger notion of backend replacement. -/
theorem obsGen_congr {α : Type} (g : Invariants.StructuredAF → Atom → α)
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F) (hfix : FixesContext f C) :
    obsGen g reg₁ C F = obsGen g reg₂ C (mapAssurFrag f F) := by
  obtain ⟨acc₁, h₁⟩ := exists_accepted_of_admissible hadm
  obtain ⟨acc₂, h₂⟩ := exists_accepted_relabel hf hpres hadm hfix h₁
  rw [obsGen_eq_of_ok g hadm.guard h₁,
    obsGen_eq_of_ok g (C := C) (F := mapAssurFrag f F)
      (by rw [linkOk_mapAssurFrag]; exact hadm.guard)
      (by rw [linkGround_mapAssurFrag]; exact h₂)]
  refine congrArg ObservationOf.observed ?_
  rw [mapAssurFrag_exports]
  exact congrArg (fun G => F.exports.map (fun p => g G p))
    (compileUnit_link_relabel hf hpres hadm hfix h₁ h₂).symm

/-- **Contextual representation independence (the M4 Part A headline).**

An injective, acceptance-preserving relabel of a fragment's certificates is
unobservable in every admissible context whose own assurances the relabel
fixes: the linked programs have the same carrier, so every exported conclusion
keeps its four-state status.

This **extends** `Erase.backend_replacement` along the context quantifier: that
result relates two whole programs given as `CheckedProgram`s, this relates a
fragment to its relabeling inside every admissible context satisfying
`FixesContext`. Neither implies the other — result 9 carries no admissibility
hypothesis — which is why it is cited rather than re-derived
(`whole_program_replacement`). It is the contextual-adequacy obligation
`docs/theory-m3-source-updates.md` deferred to M4. It is **not** parametricity
(no relational quantification over related backends — issue #215) and not full
abstraction (no logical relation — Part B).

The admissibility hypothesis is not a technicality that better proof
engineering would remove; `obsGen_congr` (`:778`), which now carries this
theorem's proof, records why. -/
theorem backend_replacement_congruence
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F) (hfix : FixesContext f C) :
    obs reg₁ C F = obs reg₂ C (mapAssurFrag f F) :=
  obsGen_congr _ hf hpres hadm hfix

end Headline

/-! ### The identity relabel, and the registry-swap generalization (D6) -/

section Identity

mutual
  theorem mapAssur_id : ∀ w : SupportTerm, mapAssur id w = w
    | .leaf _ => rfl
    | .inst rn θ ws D H α => by
        simp only [mapAssur, mapAssurList_id ws, mapAssurDis_id D, id_eq]
  theorem mapAssurList_id : ∀ ws : List SupportTerm, mapAssurList id ws = ws
    | [] => rfl
    | w :: ws => by simp only [mapAssurList, mapAssur_id w, mapAssurList_id ws]
  theorem mapAssurDis_id : ∀ D : List (QuestionId × SupportTerm), mapAssurDis id D = D
    | [] => rfl
    | (q, w) :: rest => by
        simp only [mapAssurDis, mapAssur_id w, mapAssurDis_id rest]
end

theorem mapAssurAtt_id (k : Attack) : mapAssurAtt id k = k := by
  cases k <;> simp only [mapAssurAtt, mapAssur_id]

theorem mapAssur_id_eq : mapAssur id = id := funext mapAssur_id

theorem mapAssurAtt_id_eq : mapAssurAtt id = id := funext mapAssurAtt_id

theorem mapAssurFrag_id (F : Fragment) : mapAssurFrag id F = F := by
  simp only [mapAssurFrag, mapAssur_id_eq, mapAssurAtt_id_eq, List.map_id]

theorem fixesContext_id (C : Context) : FixesContext id C :=
  ⟨by simp only [mapAssur_id_eq, List.map_id],
   by simp only [mapAssurAtt_id_eq, List.map_id]⟩

/-- **The acceptance-profile generalization (D6).** No relabel and no
injectivity: if every assurance the first registry accepts the second accepts
too, the *same* fragment reads the same way in every admissible context.

`hpres` is stated **globally**, over every rule and every assurance, rather than
over `F`'s certificate occurrences — `hasSupport_mapAssur`, which carries the
derivations across, quantifies over every rule and assurance. That is a property
of *this* theorem, not a gap in the development: a display of this result must
say "agrees globally", not "agrees on the fragment's occurrences".

The occurrence-local hypothesis is a separate theorem rather than a missing one.
`backend_replacement_parametricity_local` (`Parametricity.lean:1686`) and its
companion `backend_replacement_parametricity_local_sem` oblige acceptance only
for `α ∈ occurrences F`, by replacing the relabel function with a relation
inhabited exactly there. They are a **trade, not a strengthening**: they add
`hC` and `hA`, requiring the *context's* own occurrences to lie inside
`occurrences F`, which this theorem does not require. Neither implies the other,
so this statement's global reading stands. -/
theorem registry_swap_congruence {canon : String → String}
    {reg₁ reg₂ : BackendRegistry canon} {C : Context} {F : Fragment}
    (hpres : ∀ (r : Rule) (As : List Atom) (A : Atom) (α : Assurance),
      AssuranceOk (certOkOf reg₁) r As A α → AssuranceOk (certOkOf reg₂) r As A α)
    (hadm : Admissible reg₁ C F) :
    obs reg₁ C F = obs reg₂ C F := by
  have h := backend_replacement_congruence (f := id) (fun _ _ h => h) hpres hadm
    (fixesContext_id C)
  rwa [mapAssurFrag_id] at h

end Identity

/-! ### Congruence under composition, and the whole-program instance -/

section Closure

variable {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
  {f : Assurance → Assurance}

/-- A list is fixed by a map that fixes each of its elements. -/
theorem map_eq_self_of_mem {α : Type} {g : α → α} :
    ∀ {l : List α}, (∀ x ∈ l, g x = x) → l.map g = l
  | [], _ => rfl
  | v :: vs, h => by
      rw [List.map_cons, h v List.mem_cons_self,
        map_eq_self_of_mem (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- A relabel that fixes two contexts fixes their composite. -/
theorem fixesContext_composed {C D : Context}
    (hC : FixesContext f C) (hD : FixesContext f D) :
    FixesContext f (composedContext C D) := by
  constructor
  · show (dedupList (C.frame.args ++ D.frame.args)).map (mapAssur f)
        = dedupList (C.frame.args ++ D.frame.args)
    refine map_eq_self_of_mem (fun w hw => ?_)
    rcases List.mem_append.mp (mem_dedupList.mp hw) with h | h
    · exact eq_of_map_eq_self hC.args w h
    · exact eq_of_map_eq_self hD.args w h
  · show (C.frame.atts ++ D.frame.atts).map (mapAssurAtt f)
        = C.frame.atts ++ D.frame.atts
    rw [List.map_append, hC.atts, hD.atts]

/-- **Admissibility of a composite, assembled from its halves.** This is the
piece that makes "stable under embedding into a larger context" a statement
with content: the composite's `SideOk` is built by `sideOk_composed` from the
two halves plus their cross-coverage, rather than assumed. The cross-coverage
hypotheses are not slack — `compose` does not saturate, so conflicts *between*
the halves are covered by their own declared attacks or by nothing at all. -/
theorem admissible_composed {C D : Context} {F : Fragment}
    {reg : BackendRegistry canon}
    (guard : linkOk (composedContext C D) F = true)
    (hC : SideOk canon reg (linkGamma (composedContext C D) F) F.policy
      C.frame.args C.frame.atts)
    (hD : SideOk canon reg (linkGamma (composedContext C D) F) F.policy
      D.frame.args D.frame.atts)
    (hcross : ∀ source ∈ C.frame.args, ∀ target ∈ D.frame.args,
      ∀ Cs Ct, HasSupport canon F.policy.ruleLookup
          (linkGamma (composedContext C D) F) (certOkOf reg) source Cs [] →
        HasSupport canon F.policy.ruleLookup
          (linkGamma (composedContext C D) F) (certOkOf reg) target Ct [] →
        ContraryMatch canon F.policy.defeat Cs Ct →
        ConflictAttackable F.policy.ruleLookup target →
        Covered (C.frame.atts ++ D.frame.atts) source target)
    (hcross' : ∀ source ∈ D.frame.args, ∀ target ∈ C.frame.args,
      ∀ Cs Ct, HasSupport canon F.policy.ruleLookup
          (linkGamma (composedContext C D) F) (certOkOf reg) source Cs [] →
        HasSupport canon F.policy.ruleLookup
          (linkGamma (composedContext C D) F) (certOkOf reg) target Ct [] →
        ContraryMatch canon F.policy.defeat Cs Ct →
        ConflictAttackable F.policy.ruleLookup target →
        Covered (C.frame.atts ++ D.frame.atts) source target)
    (hF : SideOk canon reg (linkGamma (composedContext C D) F) F.policy
      F.args F.atts)
    (hsig : Check.Unit.signatureStage (linkGround (composedContext C D) F)
      (linkedUnit reg (composedContext C D) F) = none)
    (hscope : Policy.firstOutOfScope? F.policy = none)
    (hruleIds : (F.policy.rules.map (·.id)).Nodup)
    (hpolicy : Policy.WellFormed canon F.policy) :
    Admissible reg (composedContext C D) F where
  guard := guard
  ctx := sideOk_composed hC hD hcross hcross'
  frag := hF
  signature := hsig
  scope := hscope
  ruleIds := hruleIds
  policy := hpolicy

/-- **Congruence is stable under embedding into a larger context.** The
quantifier already ranges over composites, since `composedContext` produces a
`Context`; what composition buys is that the quantifier is *closed*, and
`admissible_composed` is what discharges the composite's side of the
hypothesis from the halves. -/
theorem backend_replacement_congruence_composed {C D : Context} {F : Fragment}
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ (composedContext C D) F)
    (hC : FixesContext f C) (hD : FixesContext f D) :
    obs reg₁ (composedContext C D) F
      = obs reg₂ (composedContext C D) (mapAssurFrag f F) :=
  backend_replacement_congruence hf hpres hadm (fixesContext_composed hC hD)

/-- **Result 9 as the whole-program instance.** `Erase.backend_replacement` is
kept as-is and cited, not re-derived: its proof is `rw [checkedAF_relabel …]` on
two programs already known to be checked, whereas a corollary route through the
congruence would have to carry an `Admissible` context and would therefore be
*weaker*, not stronger. The milestone's progress is the context quantifier, not
a new proof of the old statement — recording that here so the re-derivation is
never mistaken for one. -/
theorem whole_program_replacement {Pi : RuleId → Option Rule}
    {Gamma : LeafId → Option Atom}
    {CertOk₁ CertOk₂ : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {dp : DefeatPolicy}
    {P₁ : CheckedProgram canon Pi Gamma CertOk₁ dp}
    {P₂ : CheckedProgram canon Pi Gamma CertOk₂ dp}
    (hf : Function.Injective f)
    (hargs : P₂.args = P₁.args.map (mapAssur f))
    (hatts : P₂.atts = P₁.atts.map (mapAssurAtt f))
    (c : Grounded.Claim) :
    Grounded.statusC (Compile.checkedAF P₁) c = Grounded.statusC (Compile.checkedAF P₂) c :=
  Erase.backend_replacement hf hargs hatts c

end Closure

end Lara.Context
