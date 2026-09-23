import Lara.Context.Holes.Syntax
import Lara.Context.Observation

/-! Instantiate answer holes before invoking the existing checked linker.
Hole failures remain separate from its detailed incompatible/rejected outcomes. -/
set_option autoImplicit false

namespace Lara.Context.Holes
open Lara.Support Lara.Attack Lara.Compile

/-- Both stored attack endpoints may contain answer holes. -/
inductive TemplateAttack where
  | rebut : Template → Template → TemplateAttack
  | undercut : Template → Template → Pos → TemplateAttack
  | undermine : Template → Template → Pos → TemplateAttack

structure HoleFragment where
  sigma : Sigma.Sigma
  policy : Policy.Policy
  gammaFrag : List (LeafId × Atom)
  ground : List Atom
  imports : Interface
  exports : List Atom
  args : List Template
  atts : List TemplateAttack

structure HoleContext where
  frame : Lara.Context.Context
  filling : Filling

/-- Restore unchanged metadata around the substituted terms. -/
def realize (F : HoleFragment) (args : List SupportTerm) (atts : List Attack) : Fragment :=
  { sigma := F.sigma, policy := F.policy, gammaFrag := F.gammaFrag,
    ground := F.ground, imports := F.imports, exports := F.exports,
    args := args, atts := atts }

def instantiateAttack (ρ : Filling) : TemplateAttack → Except HoleError Attack
  | .rebut s t => do return .rebut (← instantiateAux ρ s) (← instantiateAux ρ t)
  | .undercut s t π => do return .undercut (← instantiateAux ρ s) (← instantiateAux ρ t) π
  | .undermine s t π => do return .undermine (← instantiateAux ρ s) (← instantiateAux ρ t) π

def instantiateAttacks (ρ : Filling) : List TemplateAttack → Except HoleError (List Attack)
  | [] => .ok []
  | a :: as => do return (← instantiateAttack ρ a) :: (← instantiateAttacks ρ as)

/-- Duplicate bindings fail even when the fragment contains no terms. -/
def instantiateFragment (ρ : Filling) (F : HoleFragment) : Except HoleError Fragment :=
  match firstDuplicate ρ with
  | some h => .error (.duplicate h)
  | none => do return realize F (← instantiateList ρ F.args) (← instantiateAttacks ρ F.atts)

def link {canon : String → String} (reg : BackendRegistry canon)
    (C : HoleContext) (F : HoleFragment) := do
  let G ← instantiateFragment C.filling F
  return Lara.Context.link reg C.frame G

def obsGen {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} (reg : BackendRegistry canon)
    (C : HoleContext) (F : HoleFragment) : Except HoleError (ObservationOf α) := do
  let G ← instantiateFragment C.filling F
  return Lara.Context.obsGen g reg C.frame G

def obs {canon : String → String} (reg : BackendRegistry canon)
    (C : HoleContext) (F : HoleFragment) : Except HoleError Observation :=
  obsGen (Invariants.status canon) reg C F

def obsSem (sem : Semantics.ExtensionSemantics) {canon : String → String}
    (reg : BackendRegistry canon) (C : HoleContext) (F : HoleFragment) :=
  obsGen (fun G p => Invariants.observeSem sem canon G p) reg C F

/-- Quantify over all surrounding frames and all finite filling tables. -/
def CtxEquiv {canon : String → String} (reg : BackendRegistry canon)
    (F G : HoleFragment) : Prop := ∀ C : HoleContext, obs reg C F = obs reg C G

def CtxEquivSem (sem : Semantics.ExtensionSemantics) {canon : String → String}
    (reg : BackendRegistry canon) (F G : HoleFragment) : Prop :=
  ∀ C : HoleContext, obsSem sem reg C F = obsSem sem reg C G

def closedAttack : Attack → TemplateAttack
  | .rebut s t => .rebut (.core s) (.core t)
  | .undercut s t π => .undercut (.core s) (.core t) π
  | .undermine s t π => .undermine (.core s) (.core t) π

def closedFragment (F : Fragment) : HoleFragment :=
  { sigma := F.sigma, policy := F.policy, gammaFrag := F.gammaFrag,
    ground := F.ground, imports := F.imports, exports := F.exports,
    args := F.args.map Template.core, atts := F.atts.map closedAttack }

def closedContext (C : Lara.Context.Context) : HoleContext := ⟨C, []⟩

theorem instantiateList_core (ρ : Filling) (ws : List SupportTerm) :
    instantiateList ρ (ws.map Template.core) = .ok ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [instantiateList, instantiateAux, ih, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem instantiateAttack_closed (ρ : Filling) (k : Attack) :
    instantiateAttack ρ (closedAttack k) = .ok k := by cases k <;> rfl

theorem instantiateAttacks_closed (ρ : Filling) (ks : List Attack) :
    instantiateAttacks ρ (ks.map closedAttack) = .ok ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [instantiateAttacks, instantiateAttack_closed, ih, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem instantiateFragment_closed {ρ : Filling} (hρ : FillingNodup ρ) (F : Fragment) :
    instantiateFragment ρ (closedFragment F) = .ok F := by
  simp [instantiateFragment, (firstDuplicate_none_iff ρ).mpr hρ,
    closedFragment, instantiateList_core, instantiateAttacks_closed, realize, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Exact preservation includes the old located failure payloads. -/
theorem obsGen_closed {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} (reg : BackendRegistry canon)
    (C : HoleContext) (hρ : FillingNodup C.filling) (F : Fragment) :
    obsGen g reg C (closedFragment F) = .ok (Lara.Context.obsGen g reg C.frame F) := by
  simp [obsGen, instantiateFragment_closed hρ, Functor.map, Except.map]

theorem obs_closed {canon : String → String} (reg : BackendRegistry canon)
    (C : HoleContext) (hρ : FillingNodup C.filling) (F : Fragment) :
    obs reg C (closedFragment F) = .ok (Lara.Context.obs reg C.frame F) := by
  rw [obs, obsGen_closed _ _ _ hρ, Lara.Context.obs_eq_obsGen]

theorem obsSem_closed (sem : Semantics.ExtensionSemantics) {canon : String → String}
    (reg : BackendRegistry canon) (C : HoleContext) (hρ : FillingNodup C.filling)
    (F : Fragment) :
    obsSem sem reg C (closedFragment F) = .ok (Lara.Context.obsSem sem reg C.frame F) :=
  obsGen_closed _ _ _ hρ _

/-- Successful substitution exposes exactly the reconstructed fragment. -/
theorem instantiateFragment_inv {ρ : Filling} {F : HoleFragment} {G : Fragment}
    (h : instantiateFragment ρ F = .ok G) :
    FillingNodup ρ ∧ ∃ ws ks, instantiateList ρ F.args = .ok ws ∧
      instantiateAttacks ρ F.atts = .ok ks ∧ G = realize F ws ks := by
  unfold instantiateFragment at h
  cases hd : firstDuplicate ρ with
  | some d => simp [hd] at h
  | none =>
    refine ⟨(firstDuplicate_none_iff _).mp hd, ?_⟩
    cases hw : instantiateList ρ F.args with
    | error e => simp [hd, hw, Bind.bind, Except.bind] at h
    | ok ws =>
      cases hk : instantiateAttacks ρ F.atts with
      | error e => simp [hd, hw, hk, Bind.bind, Except.bind] at h
      | ok ks =>
        simp [hd, hw, hk, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        exact ⟨ws, ks, rfl, rfl, h.symm⟩

/-- Successful substitution hands every remaining branch to the old observation. -/
theorem obsGen_of_instantiate {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} (reg : BackendRegistry canon)
    {C : HoleContext} {F : HoleFragment} {G : Fragment}
    (hi : instantiateFragment C.filling F = .ok G) :
    obsGen g reg C F = .ok (Lara.Context.obsGen g reg C.frame G) := by
  simp [obsGen, hi, Functor.map, Except.map]

/-- Extra bad-table contexts produce the same error on both closed fragments. -/
theorem ctxEquiv_closed_iff {canon : String → String} (reg : BackendRegistry canon)
    (F G : Fragment) :
    CtxEquiv reg (closedFragment F) (closedFragment G) ↔ Lara.Context.CtxEquiv reg F G := by
  constructor
  · intro h C
    have he := h (closedContext C)
    rw [obs_closed reg _ (by simp [closedContext, FillingNodup]),
      obs_closed reg _ (by simp [closedContext, FillingNodup])] at he
    exact Except.ok.inj he
  · intro h C
    cases hd : firstDuplicate C.filling with
    | some d => simp [obs, obsGen, instantiateFragment, hd]
    | none =>
      have hn := (firstDuplicate_none_iff _).mp hd
      rw [obs_closed reg C hn, obs_closed reg C hn, h C.frame]

theorem ctxEquivSem_closed_iff (sem : Semantics.ExtensionSemantics)
    {canon : String → String} (reg : BackendRegistry canon) (F G : Fragment) :
    CtxEquivSem sem reg (closedFragment F) (closedFragment G) ↔
      Lara.Context.CtxEquivSem sem reg F G := by
  constructor
  · intro h C
    have he := h (closedContext C)
    rw [obsSem_closed sem reg _ (by simp [closedContext, FillingNodup]),
      obsSem_closed sem reg _ (by simp [closedContext, FillingNodup])] at he
    exact Except.ok.inj he
  · intro h C
    cases hd : firstDuplicate C.filling with
    | some d => simp [obsSem, obsGen, instantiateFragment, hd]
    | none =>
      have hn := (firstDuplicate_none_iff _).mp hd
      rw [obsSem_closed sem reg C hn, obsSem_closed sem reg C hn, h C.frame]

/-- Instantiated argument membership has an actual template preimage. -/
theorem mem_instantiateList {ρ : Filling} {ts : List Template} {ws : List SupportTerm}
    (h : instantiateList ρ ts = .ok ws) {w : SupportTerm} (hw : w ∈ ws) :
    ∃ t ∈ ts, instantiateAux ρ t = .ok w := by
  induction ts generalizing ws with
  | nil => simp [instantiateList] at h; subst ws; simp at hw
  | cons t ts ih =>
    simp only [instantiateList] at h
    cases ht : instantiateAux ρ t with
    | error e => simp [ht, Bind.bind, Except.bind] at h
    | ok v =>
      cases hs : instantiateList ρ ts with
      | error e => simp [ht, hs, Bind.bind, Except.bind] at h
      | ok vs =>
        simp [ht, hs, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        subst ws
        rcases List.mem_cons.mp hw with rfl | hw
        · exact ⟨t, by simp, ht⟩
        · obtain ⟨u, hu, he⟩ := ih hs hw
          exact ⟨u, List.mem_cons_of_mem _ hu, he⟩

def substAttack (ρ : Filling) : TemplateAttack → TemplateAttack
  | .rebut s t => .rebut (subst ρ s) (subst ρ t)
  | .undercut s t π => .undercut (subst ρ s) (subst ρ t) π
  | .undermine s t π => .undermine (subst ρ s) (subst ρ t) π

def substFragment (ρ : Filling) (F : HoleFragment) : HoleFragment :=
  { F with args := substList ρ F.args, atts := F.atts.map (substAttack ρ) }

theorem substAttack_append (ρ σ : Filling) (k : TemplateAttack) :
    substAttack (ρ ++ σ) k = substAttack σ (substAttack ρ k) := by
  cases k <;> simp [substAttack, subst_append]

theorem substFragment_append (ρ σ : Filling) (F : HoleFragment) :
    substFragment (ρ ++ σ) F = substFragment σ (substFragment ρ F) := by
  simp only [substFragment, substList_append, List.map_map]
  congr 1
  exact List.map_congr_left fun k _ => substAttack_append ρ σ k

/-! Sequential partial substitution followed by total instantiation. -/
mutual
  theorem instantiateAux_subst (ρ σ : Filling) (t : Template) :
      instantiateAux σ (subst ρ t) = instantiateAux (ρ ++ σ) t := by
    cases t with
    | core w => rfl
    | inst rn θ ws D H α =>
      simp only [subst, instantiateAux, instantiateList_subst, instantiateDis_subst]
  theorem instantiateAnswer_subst (ρ σ : Filling) (a : AnswerTemplate) :
      instantiateAnswer σ (substAnswer ρ a) = instantiateAnswer (ρ ++ σ) a := by
    cases a with
    | term t => simp only [substAnswer, instantiateAnswer, instantiateAux_subst]
    | hole h =>
      simp only [substAnswer, instantiateAnswer, lookupFilling_append]
      cases lookupFilling ρ h <;> simp [Option.or, instantiateAnswer, instantiateAux]
  theorem instantiateList_subst (ρ σ : Filling) (ts : List Template) :
      instantiateList σ (substList ρ ts) = instantiateList (ρ ++ σ) ts := by
    cases ts with
    | nil => rfl
    | cons t ts =>
      simp only [substList, instantiateList, instantiateAux_subst, instantiateList_subst]
  theorem instantiateDis_subst (ρ σ : Filling) (D : List (QuestionId × AnswerTemplate)) :
      instantiateDis σ (substDis ρ D) = instantiateDis (ρ ++ σ) D := by
    cases D with
    | nil => rfl
    | cons p rest =>
      rcases p with ⟨q, a⟩
      simp only [substDis, instantiateDis, instantiateAnswer_subst, instantiateDis_subst]
end

theorem instantiateAttack_subst (ρ σ : Filling) (k : TemplateAttack) :
    instantiateAttack σ (substAttack ρ k) = instantiateAttack (ρ ++ σ) k := by
  cases k <;> simp only [substAttack, instantiateAttack, instantiateAux_subst]

theorem instantiateAttacks_subst (ρ σ : Filling) (ks : List TemplateAttack) :
    instantiateAttacks σ (ks.map (substAttack ρ)) = instantiateAttacks (ρ ++ σ) ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp only [List.map_cons, instantiateAttacks, instantiateAttack_subst, ih]

/-- Disjoint valid fillings make staged and composed total instantiation identical. -/
theorem instantiateFragment_subst {ρ σ : Filling} (hρ : FillingNodup ρ)
    (hσ : FillingNodup σ) (hd : DisjointFillings ρ σ) (F : HoleFragment) :
    instantiateFragment σ (substFragment ρ F) = instantiateFragment (ρ ++ σ) F := by
  simp only [instantiateFragment, (firstDuplicate_none_iff _).mpr hσ,
    (firstDuplicate_none_iff _).mpr (fillingNodup_append hρ hσ hd),
    substFragment, instantiateList_subst, instantiateAttacks_subst]
  rfl

/-- Old frame composition and ordered filling append, before the guards. -/
def composedContext (C D : HoleContext) : HoleContext :=
  ⟨Lara.Context.composedContext C.frame D.frame, C.filling ++ D.filling⟩

def compose (C D : HoleContext) : Except HoleError (Option HoleContext) :=
  match firstDuplicate (C.filling ++ D.filling) with
  | some h => .error (.duplicate h)
  | none => if Lara.Context.composeOk C.frame D.frame then .ok (some (composedContext C D))
      else .ok none

theorem compose_eq_some {C D : HoleContext}
    (hC : FillingNodup C.filling) (hD : FillingNodup D.filling)
    (hd : DisjointFillings C.filling D.filling)
    (hf : Lara.Context.composeOk C.frame D.frame = true) :
    compose C D = .ok (some (composedContext C D)) := by
  simp [compose, (firstDuplicate_none_iff _).mpr (fillingNodup_append hC hD hd), hf]

theorem composed_filling_assoc (C D E : HoleContext) :
    (composedContext (composedContext C D) E).filling =
      (composedContext C (composedContext D E)).filling := List.append_assoc _ _ _

/-- Identical filling tables give identical substitution at arbitrary nesting. -/
theorem composed_subst_assoc (C D E : HoleContext) (F : HoleFragment) :
    substFragment (composedContext (composedContext C D) E).filling F =
      substFragment (composedContext C (composedContext D E)).filling F := by
  rw [composed_filling_assoc]

/-- Pairwise old-frame compatibility and disjoint tables define both bracketings. -/
theorem compose_assoc_defined {C D E : HoleContext}
    (hC : FillingNodup C.filling) (hD : FillingNodup D.filling)
    (hE : FillingNodup E.filling)
    (hCD : DisjointFillings C.filling D.filling)
    (hDE : DisjointFillings D.filling E.filling)
    (hCE : DisjointFillings C.filling E.filling)
    (fCD : Lara.Context.composeOk C.frame D.frame = true)
    (fDE : Lara.Context.composeOk D.frame E.frame = true)
    (fCE : Lara.Context.composeOk C.frame E.frame = true) :
    compose (composedContext C D) E = .ok (some (composedContext (composedContext C D) E)) ∧
    compose C (composedContext D E) = .ok (some (composedContext C (composedContext D E))) := by
  constructor
  · apply compose_eq_some (fillingNodup_append hC hD hCD) hE
    · intro h hh he
      simp only [composedContext, List.map_append, List.mem_append] at hh
      exact hh.elim (fun hc => hCE h hc he) (fun hd => hDE h hd he)
    · exact Lara.Context.composeOk_assoc_left fCD fDE fCE
  · apply compose_eq_some hC (fillingNodup_append hD hE hDE)
    · intro h hc hh
      simp only [composedContext, List.map_append, List.mem_append] at hh
      exact hh.elim (fun hd => hCD h hc hd) (fun he => hCE h hc he)
    · exact Lara.Context.composeOk_assoc_right fCD fDE fCE

/-- The old frame material agrees at precisely its existing extensional scope. -/
theorem composed_frame_material_assoc (C D E : HoleContext) :
    (∀ l, l ∈ (composedContext (composedContext C D) E).frame.frame.declared ↔
      l ∈ (composedContext C (composedContext D E)).frame.frame.declared) ∧
    (∀ w, w ∈ (composedContext (composedContext C D) E).frame.frame.args ↔
      w ∈ (composedContext C (composedContext D E)).frame.frame.args) ∧
    (∀ k, k ∈ (composedContext (composedContext C D) E).frame.frame.atts ↔
      k ∈ (composedContext C (composedContext D E)).frame.frame.atts) ∧
    (∀ l, l ∈ (composedContext (composedContext C D) E).frame.frame.imports.leaves ↔
      l ∈ (composedContext C (composedContext D E)).frame.frame.imports.leaves) :=
  Lara.Context.compose_assoc_mem

/-- Equality of old frames suffices for equality of whole hole contexts. -/
theorem composed_context_assoc (C D E : HoleContext)
    (hf : Lara.Context.composedContext (Lara.Context.composedContext C.frame D.frame) E.frame =
      Lara.Context.composedContext C.frame (Lara.Context.composedContext D.frame E.frame)) :
    composedContext (composedContext C D) E = composedContext C (composedContext D E) := by
  cases C; cases D; cases E
  simp only [composedContext, List.append_assoc] at *
  rw [hf]

end Lara.Context.Holes
