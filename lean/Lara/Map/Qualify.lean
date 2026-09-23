/-
# Multi-artifact maps, part 1 — member-alias qualification

The mechanized half of `Lara.Map.Qualify`. A *map* links several
independently checked artifacts, and two of them may each declare a leaf called
`e1`. Linking is therefore preceded by a **rename**: every member's local leaf
identifiers are replaced by alias-qualified ones, and nothing else about the
member is touched.

Two obligations follow, and this module discharges both.

* **The rename is injective, and separately so per member.** The qualified key
  is the length-framed pair `renderFrames [alias, local]`, so
  `qualifiedKey_inj` recovers both halves and `qualifyLeaf_ne_of_alias_ne` gives
  disjoint images for distinct aliases.
* **The rename is invisible to the checker.** `mapLeaf` rewrites every `.leaf`
  occurrence of a support term through a leaf function and carries every other
  field verbatim; `hasSupport_mapLeaf` and `hasAttack_mapLeaf` transport the two
  typing judgments along it, `mapLeafProg` transports a whole `CheckedProgram`,
  and `checkedAF_mapLeaf` shows the compiled framework is literally the same
  object — hence the same grounded labels and the same claim statuses.

The structure is a transliteration of `Lara.Erase` / `Lara.EraseTransport`,
which prove exactly this suite for a *certificate* relabel. The single
difference is where the environment enters: `mapAssur` leaves `.leaf` alone and
rewrites the assurance, so its transport takes an assurance-preservation
hypothesis and its `.leaf` case is trivial; `mapLeaf` rewrites `.leaf` and
leaves the assurance alone, so its transport takes a Γ-renaming hypothesis and
its assurance field is trivial. Every `InstSide` field is leaf-independent and
carries over unchanged. Nothing here re-derives a fact either of those modules
already has.

`Lara.Strict`'s `frame`/`renderFrames` are reused rather than reimplemented, and
that is the opposite of what the Haskell side does. `Lara.Map.Types` keeps its
own copy because `Lara.Strict.ND`'s frames are bytes of a *frozen backend wire
key* and a map key must be free to move without perturbing them. No such
constraint exists here: this module states no byte, and what it needs is
`Lara.Strict.decodeFrames_render`, an already-proved round-trip. The two
spellings agree — `Nat.repr s.utf8ByteSize ++ ":" ++ s` on both sides — which is
why one proof serves both.
-/

import Lara.Compile
import Lara.Strict
import Lara.Admission

namespace Lara.Map

open Lara.Support Lara.Attack Lara.Compile Lara.Grounded

/-! ### The qualified key

One local name plus one member alias becomes one map-wide name. The framing is
what makes the pairing injective: without it `("pa", "x")` and `("p", "ax")`
would produce the same key. -/

/-- The map-wide spelling of one member-local name. -/
def qualifiedKey (memberAlias localName : String) : String :=
  Lara.Strict.renderFrames [memberAlias, localName]

/-- **The qualified key determines both halves.** The operational witness is
`Lara.Strict.decodeFrames`, whose round-trip is already proved; applying it to
both sides of the equation recovers the two-element list. -/
theorem qualifiedKey_inj {a l a' l' : String}
    (h : qualifiedKey a l = qualifiedKey a' l') : a = a' ∧ l = l' := by
  have hd : Lara.Strict.decodeFrames (Lara.Strict.renderFrames [a, l])
      = Lara.Strict.decodeFrames (Lara.Strict.renderFrames [a', l']) :=
    congrArg Lara.Strict.decodeFrames h
  rw [Lara.Strict.decodeFrames_render, Lara.Strict.decodeFrames_render] at hd
  have hl : [a, l] = [a', l'] := Option.some.inj hd
  exact ⟨(List.cons.inj hl).1, (List.cons.inj (List.cons.inj hl).2).1⟩

/-- Qualify one member-local leaf identifier by its member's alias. -/
def qualifyLeaf (memberAlias : String) (l : LeafId) : LeafId :=
  ⟨qualifiedKey memberAlias l.name⟩

/-- **Within one member the rename is injective**: a member cannot lose a
distinction it drew. -/
theorem qualifyLeaf_injective (memberAlias : String) :
    Function.Injective (qualifyLeaf memberAlias) := by
  intro l l' h
  have := (qualifiedKey_inj (LeafId.mk.inj h)).2
  cases l; cases l'; simp_all

/-- **Across two members the renamed namespaces are disjoint**: no member can
capture another member's leaf. -/
theorem qualifyLeaf_ne_of_alias_ne {a a' : String} (h : a ≠ a') (l l' : LeafId) :
    qualifyLeaf a l ≠ qualifyLeaf a' l' := by
  intro heq
  exact h (qualifiedKey_inj (LeafId.mk.inj heq)).1

/-! ### The uniform leaf rename

Explicit list recursion, as in `Lara.Erase.mapAssur`: Lean 4 cannot recurse
through `SupportTerm`'s nested `List` fields via a lambda. -/

mutual
  /-- Rewrite every leaf occurrence of a support term through `r`. Rule name,
  substitution, discharge *keys*, holes and assurance are carried verbatim: they
  are coordinates in the shared policy, not handles the member owns. -/
  def mapLeaf (r : LeafId → LeafId) : SupportTerm → SupportTerm
    | .leaf l => .leaf (r l)
    | .inst rn θ ws D H α =>
        .inst rn θ (mapLeafList r ws) (mapLeafDis r D) H α
  def mapLeafList (r : LeafId → LeafId) :
      List SupportTerm → List SupportTerm
    | [] => []
    | w :: ws => mapLeaf r w :: mapLeafList r ws
  def mapLeafDis (r : LeafId → LeafId) :
      List (QuestionId × SupportTerm) → List (QuestionId × SupportTerm)
    | [] => []
    | (q, w) :: rest => (q, mapLeaf r w) :: mapLeafDis r rest
end

/-- Rename the stored terms of an attack, preserving kind and position. The
position is not renamed: a premise index and a question name are policy
coordinates. -/
def mapLeafAtt (r : LeafId → LeafId) : Attack → Attack
  | .rebut w u => .rebut (mapLeaf r w) (mapLeaf r u)
  | .undercut w u π => .undercut (mapLeaf r w) (mapLeaf r u) π
  | .undermine w u π => .undermine (mapLeaf r w) (mapLeaf r u) π

section Lemmas
variable {r : LeafId → LeafId}

/-- The list helper is `List.map (mapLeaf r)`. -/
theorem mapLeafList_eq (ws : List SupportTerm) :
    mapLeafList r ws = ws.map (mapLeaf r) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [mapLeafList, List.map_cons, ih]

/-- The discharge helper maps values, keeping keys. -/
theorem mapLeafDis_eq (D : List (QuestionId × SupportTerm)) :
    mapLeafDis r D = D.map (fun p => (p.1, mapLeaf r p.2)) := by
  induction D with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨q, w⟩ := p
    simp only [mapLeafDis, List.map_cons, ih]

theorem mapLeafAtt_source (k : Attack) :
    (mapLeafAtt r k).source = mapLeaf r k.source := by
  cases k <;> rfl

theorem mapLeafAtt_target (k : Attack) :
    (mapLeafAtt r k).target = mapLeaf r k.target := by
  cases k <;> rfl

/-! ### Injectivity of a uniform rename -/

mutual
  theorem mapLeaf_inj (hr : Function.Injective r) :
      ∀ {a b : SupportTerm}, mapLeaf r a = mapLeaf r b → a = b
    | .leaf _, .leaf _, h => by
        simp only [mapLeaf, SupportTerm.leaf.injEq] at h
        simp only [SupportTerm.leaf.injEq]
        exact hr h
    | .leaf _, .inst _ _ _ _ _ _, h => by simp only [mapLeaf, reduceCtorEq] at h
    | .inst _ _ _ _ _ _, .leaf _, h => by simp only [mapLeaf, reduceCtorEq] at h
    | .inst _ _ _ _ _ _, .inst _ _ _ _ _ _, h => by
        simp only [mapLeaf, SupportTerm.inst.injEq] at h
        obtain ⟨hrn, hθ, hws, hD, hH, hα⟩ := h
        subst hrn; subst hθ; subst hH; subst hα
        rw [mapLeafList_inj hr hws, mapLeafDis_inj hr hD]
  theorem mapLeafList_inj (hr : Function.Injective r) :
      ∀ {xs ys : List SupportTerm}, mapLeafList r xs = mapLeafList r ys → xs = ys
    | [], [], _ => rfl
    | [], _ :: _, h => by simp only [mapLeafList, reduceCtorEq] at h
    | _ :: _, [], h => by simp only [mapLeafList, reduceCtorEq] at h
    | _ :: _, _ :: _, h => by
        simp only [mapLeafList, List.cons.injEq] at h
        rw [mapLeaf_inj hr h.1, mapLeafList_inj hr h.2]
  theorem mapLeafDis_inj (hr : Function.Injective r) :
      ∀ {xs ys : List (QuestionId × SupportTerm)},
        mapLeafDis r xs = mapLeafDis r ys → xs = ys
    | [], [], _ => rfl
    | [], _ :: _, h => by simp only [mapLeafDis, reduceCtorEq] at h
    | _ :: _, [], h => by simp only [mapLeafDis, reduceCtorEq] at h
    | (_, _) :: _, (_, _) :: _, h => by
        simp only [mapLeafDis, List.cons.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨hq, hx⟩, htl⟩ := h
        subst hq
        rw [mapLeaf_inj hr hx, mapLeafDis_inj hr htl]
end

theorem mapLeaf_injective (hr : Function.Injective r) :
    Function.Injective (mapLeaf r) := fun _ _ h => mapLeaf_inj hr h

theorem mapLeaf_eq_iff (hr : Function.Injective r) (a b : SupportTerm) :
    mapLeaf r a = mapLeaf r b ↔ a = b :=
  ⟨fun h => mapLeaf_injective hr h, fun h => h ▸ rfl⟩

/-! ### The rename commutes with positional navigation -/

theorem lookupDis_mapLeafDis (D : List (QuestionId × SupportTerm)) (q : QuestionId) :
    lookupDis (mapLeafDis r D) q = (lookupDis D q).map (mapLeaf r) := by
  induction D with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨q', w⟩ := p
    simp only [mapLeafDis, lookupDis, ih]
    split <;> rfl

theorem mapLeaf_subterm :
    ∀ (v : SupportTerm) (π : Pos),
      subterm (mapLeaf r v) π = (subterm v π).map (mapLeaf r) := by
  intro v π
  induction π generalizing v with
  | nil => rfl
  | cons pe π ih =>
    cases v with
    | leaf l => rfl
    | inst rn θ ws D H α =>
      cases pe with
      | prem i =>
        simp only [mapLeaf, subterm, mapLeafList_eq, List.getElem?_map]
        cases ws[i]? with
        | none => rfl
        | some w => exact ih w
      | ques q =>
        simp only [mapLeaf, subterm, lookupDis_mapLeafDis]
        cases lookupDis D q with
        | none => rfl
        | some w => exact ih w

/-! ### The rename preserves structural containment (via injectivity) -/

mutual
  theorem containsB_mapLeaf (hr : Function.Injective r) :
      ∀ (v t : SupportTerm),
        containsB (mapLeaf r v) (mapLeaf r t) = containsB v t
    | .leaf l, t =>
        decide_eq_decide.mpr (mapLeaf_eq_iff hr (.leaf l) t)
    | .inst rn θ ws D H α, t => by
        show (decide (mapLeaf r (.inst rn θ ws D H α) = mapLeaf r t)
              || containsBList (mapLeafList r ws) (mapLeaf r t)
              || containsBDis (mapLeafDis r D) (mapLeaf r t))
            = (decide (SupportTerm.inst rn θ ws D H α = t)
              || containsBList ws t || containsBDis D t)
        rw [decide_eq_decide.mpr (mapLeaf_eq_iff hr (.inst rn θ ws D H α) t),
          containsBList_mapLeaf hr ws t, containsBDis_mapLeaf hr D t]
  theorem containsBList_mapLeaf (hr : Function.Injective r) :
      ∀ (ws : List SupportTerm) (t : SupportTerm),
        containsBList (mapLeafList r ws) (mapLeaf r t) = containsBList ws t
    | [], _ => rfl
    | w :: ws, t => by
        simp only [mapLeafList, containsBList]
        rw [containsB_mapLeaf hr w t, containsBList_mapLeaf hr ws t]
  theorem containsBDis_mapLeaf (hr : Function.Injective r) :
      ∀ (D : List (QuestionId × SupportTerm)) (t : SupportTerm),
        containsBDis (mapLeafDis r D) (mapLeaf r t) = containsBDis D t
    | [], _ => rfl
    | (q, w) :: rest, t => by
        simp only [mapLeafDis, containsBDis]
        rw [containsB_mapLeaf hr w t, containsBDis_mapLeaf hr rest t]
end

theorem attackClosureB_mapLeaf (hr : Function.Injective r)
    (k : Attack) (target : SupportTerm) :
    attackClosureB (mapLeafAtt r k) (mapLeaf r target)
      = attackClosureB k target := by
  cases k with
  | rebut w u =>
    simp only [mapLeafAtt, attackClosureB]
    exact containsB_mapLeaf hr target u
  | undercut w u π =>
    simp only [mapLeafAtt, attackClosureB, mapLeaf_subterm]
    cases subterm u π with
    | none => rfl
    | some t => exact containsB_mapLeaf hr target t
  | undermine w u π =>
    simp only [mapLeafAtt, attackClosureB, mapLeaf_subterm]
    cases subterm u π with
    | none => rfl
    | some t => exact containsB_mapLeaf hr target t

theorem coveredB_mapLeaf (hr : Function.Injective r)
    (atts : List Attack) (s t : SupportTerm) :
    coveredB (atts.map (mapLeafAtt r)) (mapLeaf r s) (mapLeaf r t)
      = coveredB atts s t := by
  simp only [coveredB]
  induction atts with
  | nil => rfl
  | cons k rest ih =>
    simp only [List.map_cons, List.any_cons, ih]
    rw [mapLeafAtt_source, attackClosureB_mapLeaf hr,
      decide_eq_decide.mpr (mapLeaf_eq_iff hr k.source s)]

/-! ### Discharge-map plumbing -/

theorem mapLeafList_length (ws : List SupportTerm) :
    (mapLeafList r ws).length = ws.length := by
  rw [mapLeafList_eq, List.length_map]

theorem mapLeafDis_length (D : List (QuestionId × SupportTerm)) :
    (mapLeafDis r D).length = D.length := by
  rw [mapLeafDis_eq, List.length_map]

/-- The rename preserves discharge keys. -/
theorem mapLeafDis_keys (D : List (QuestionId × SupportTerm)) :
    (mapLeafDis r D).map Prod.fst = D.map Prod.fst := by
  rw [mapLeafDis_eq, List.map_map]; rfl

/-- Decompose a hit in a renamed premise list. -/
theorem mapLeafList_getElem?_some {ws : List SupportTerm} {i : Nat}
    {w' : SupportTerm} (h : (mapLeafList r ws)[i]? = some w') :
    ∃ w₀, ws[i]? = some w₀ ∧ w' = mapLeaf r w₀ := by
  rw [mapLeafList_eq, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨w₀, hw, hw'⟩ := h
  exact ⟨w₀, hw, hw'.symm⟩

/-- Decompose a hit in a renamed discharge list (keys preserved). -/
theorem mapLeafDis_getElem?_some {D : List (QuestionId × SupportTerm)} {j : Nat}
    {q : QuestionId} {w' : SupportTerm}
    (h : (mapLeafDis r D)[j]? = some (q, w')) :
    ∃ w₀, D[j]? = some (q, w₀) ∧ w' = mapLeaf r w₀ := by
  rw [mapLeafDis_eq, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨⟨q₀, w₀⟩, hD, hqw⟩ := h
  simp only [Prod.mk.injEq] at hqw
  obtain ⟨hq, hw'⟩ := hqw
  subst hq
  exact ⟨w₀, hD, hw'.symm⟩

end Lemmas

/-! ### Typing transport

The Γ-renaming hypothesis is the map's own qualification, read as a fact about
environments: whatever the member's own Γ said about a leaf, the linked Γ says
about that leaf's qualified name. -/

section Transport
variable {r : LeafId → LeafId}
  {canon : String → String} {Pi : RuleId → Option Rule}
  {Gamma Gamma' : LeafId → Option Atom}
  {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
  {dp : DefeatPolicy}

/-- **`HasSupport` transports along a uniform leaf rename** given a Γ that
transports with it. The conclusion `C` and obligation set `O` are unchanged —
neither reads a leaf name, only the proposition Γ assigns it. -/
theorem hasSupport_mapLeaf
    (hΓ : ∀ l p, Gamma l = some p → Gamma' (r l) = some p) :
    ∀ {w : SupportTerm} {C : Atom} {O : List QuestionId},
      HasSupport canon Pi Gamma CertOk w C O →
      HasSupport canon Pi Gamma' CertOk (mapLeaf r w) C O := by
  intro w C O h
  induction h with
  | leaf hg => exact .leaf (hΓ _ _ hg)
  | @inst rn θ ws D H α r' As Cs Os DCs DOs C hside hprems hdis ihprems ihdis =>
    have hside' : InstSide canon Pi CertOk rn θ r'
        (mapLeafList r ws) (mapLeafDis r D) H α As Cs Os DCs DOs C :=
      { rule := hside.rule
        θNodup := hside.θNodup
        θDom := hside.θDom
        prems := hside.prems
        concl := hside.concl
        lenAs := by rw [mapLeafList_length]; exact hside.lenAs
        lenCs := by rw [mapLeafList_length]; exact hside.lenCs
        lenOs := by rw [mapLeafList_length]; exact hside.lenOs
        premEq := hside.premEq
        lenDCs := by rw [mapLeafDis_length]; exact hside.lenDCs
        lenDOs := by rw [mapLeafDis_length]; exact hside.lenDOs
        ans := by
          intro j q w' A hj hA
          obtain ⟨w₀, hD, _⟩ := mapLeafDis_getElem?_some hj
          exact hside.ans j q w₀ A hD hA
        qNodup := hside.qNodup
        dNodup := by rw [mapLeafDis_keys]; exact hside.dNodup
        hNodup := hside.hNodup
        cover := by
          intro qd hqd; rw [mapLeafDis_keys]; exact hside.cover qd hqd
        disj := by
          intro n hn; rw [mapLeafDis_keys] at hn; exact hside.disj n hn
        keysD := by
          intro n hn; rw [mapLeafDis_keys] at hn; exact hside.keysD n hn
        keysH := hside.keysH
        strictNoQ := by
          intro hstrict
          obtain ⟨hDnil, hHnil⟩ := hside.strictNoQ hstrict
          exact ⟨by rw [hDnil]; rfl, hHnil⟩
        assur := hside.assur }
    refine HasSupport.inst hside' ?_ ?_
    · intro i w' A O' hi hA hO
      obtain ⟨w₀, hw, hw'⟩ := mapLeafList_getElem?_some hi
      rw [hw']; exact ihprems i w₀ A O' hw hA hO
    · intro j q w' A O' hj hA hO
      obtain ⟨w₀, hD, hw'⟩ := mapLeafDis_getElem?_some hj
      rw [hw']; exact ihdis j q w₀ A O' hD hA hO

/-- **`HasAttack` transports along a uniform leaf rename.** The source's typing
transports by `hasSupport_mapLeaf`; the target occurrence tracks
`mapLeaf_subterm`; the undermine arm's Γ lookup is the one place the renaming
hypothesis is consumed on the target side. Contrary matching is untouched,
because it reads conclusions and the conclusions do not move. -/
theorem hasAttack_mapLeaf
    (hΓ : ∀ l p, Gamma l = some p → Gamma' (r l) = some p)
    {k : Attack} (hk : HasAttack canon Pi Gamma CertOk dp k) :
    HasAttack canon Pi Gamma' CertOk dp (mapLeafAtt r k) := by
  cases hk with
  | rebut hw hrule hdef hconcl hcon =>
    simp only [mapLeafAtt, mapLeaf]
    exact .rebut (hasSupport_mapLeaf hΓ hw) hrule hdef hconcl hcon
  | undercut hw hocc hrule hdef hexc hinst heq =>
    simp only [mapLeafAtt]
    exact .undercut (hasSupport_mapLeaf hΓ hw)
      (by rw [mapLeaf_subterm, hocc]; rfl) hrule hdef hexc hinst heq
  | undermine hw hocc hl hcon =>
    simp only [mapLeafAtt]
    exact .undermine (hasSupport_mapLeaf hΓ hw)
      (by rw [mapLeaf_subterm, hocc]; rfl) (hΓ _ _ hl) hcon

/-- **A uniform injective leaf rename maps a `CheckedProgram` to a
`CheckedProgram`** over the renamed environment.

This is what makes the invariance results below non-vacuous by construction: a
qualified member is exhibited as a genuine checked program, not assumed to be
one. -/
def mapLeafProg (P : CheckedProgram canon Pi Gamma CertOk dp)
    (hr : Function.Injective r)
    (hΓ : ∀ l p, Gamma l = some p → Gamma' (r l) = some p) :
    CheckedProgram canon Pi Gamma' CertOk dp where
  args := P.args.map (mapLeaf r)
  nodup := P.nodup.map (mapLeaf r)
    (fun _ _ hab habeq => hab (mapLeaf_injective hr habeq))
  complete := by
    intro w' hw'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
    obtain ⟨C, hC⟩ := P.complete w hw
    exact ⟨C, hasSupport_mapLeaf hΓ hC⟩
  atts := P.atts.map (mapLeafAtt r)
  typed := by
    intro k' hk'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hk'
    exact hasAttack_mapLeaf hΓ (P.typed k hk)
  source_declared := by
    intro k' hk'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hk'
    rw [mapLeafAtt_source]
    exact List.mem_map.mpr ⟨k.source, P.source_declared k hk, rfl⟩
  target_declared := by
    intro k' hk'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hk'
    rw [mapLeafAtt_target]
    exact List.mem_map.mpr ⟨k.target, P.target_declared k hk, rfl⟩

@[simp] theorem mapLeafProg_args (P : CheckedProgram canon Pi Gamma CertOk dp)
    (hr : Function.Injective r)
    (hΓ : ∀ l p, Gamma l = some p → Gamma' (r l) = some p) :
    (mapLeafProg P hr hΓ).args = P.args.map (mapLeaf r) := rfl

@[simp] theorem mapLeafProg_atts (P : CheckedProgram canon Pi Gamma CertOk dp)
    (hr : Function.Injective r)
    (hΓ : ∀ l p, Gamma l = some p → Gamma' (r l) = some p) :
    (mapLeafProg P hr hΓ).atts = P.atts.map (mapLeafAtt r) := rfl

end Transport

/-! ### The compiled framework is invariant under qualification -/

section Invariance
variable {r : LeafId → LeafId}
  {canon : String → String} {Pi : RuleId → Option Rule}
  {Gamma Gamma' : LeafId → Option Atom}
  {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
  {dp : DefeatPolicy}

/-- **The compiled edge decider is rename-invariant.** Nodes are list positions,
so the node bijection is the identity. -/
theorem edgeB_mapLeaf
    {P₁ : CheckedProgram canon Pi Gamma CertOk dp}
    {P₂ : CheckedProgram canon Pi Gamma' CertOk dp}
    (hr : Function.Injective r)
    (hargs : P₂.args = P₁.args.map (mapLeaf r))
    (hatts : P₂.atts = P₁.atts.map (mapLeafAtt r)) :
    ∀ i j, edgeB P₁ i j = edgeB P₂ i j := by
  intro i j
  simp only [edgeB, hargs, hatts, List.getElem?_map]
  cases P₁.args[i]? with
  | none => rfl
  | some source =>
    cases P₁.args[j]? with
    | none => rfl
    | some target =>
      exact (coveredB_mapLeaf hr P₁.atts source target).symm

/-- **The compiled AF is rename-invariant.** Equal argument count (a `map`) plus
`edgeB_mapLeaf` gives one and the same `Grounded.AF`. -/
theorem checkedAF_mapLeaf
    {P₁ : CheckedProgram canon Pi Gamma CertOk dp}
    {P₂ : CheckedProgram canon Pi Gamma' CertOk dp}
    (hr : Function.Injective r)
    (hargs : P₂.args = P₁.args.map (mapLeaf r))
    (hatts : P₂.atts = P₁.atts.map (mapLeafAtt r)) :
    checkedAF P₁ = checkedAF P₂ := by
  have hlen : P₁.args.length = P₂.args.length := by
    rw [hargs, List.length_map]
  simp only [checkedAF, toAF]
  congr 1
  · rw [hlen]
  · funext i j; exact edgeB_mapLeaf hr hargs hatts i j

/-- The grounded labelling agrees node for node. -/
theorem labelC_mapLeaf
    {P₁ : CheckedProgram canon Pi Gamma CertOk dp}
    {P₂ : CheckedProgram canon Pi Gamma' CertOk dp}
    (hr : Function.Injective r)
    (hargs : P₂.args = P₁.args.map (mapLeaf r))
    (hatts : P₂.atts = P₁.atts.map (mapLeafAtt r))
    (a : Arg) :
    labelC (checkedAF P₁) a = labelC (checkedAF P₂) a := by
  rw [checkedAF_mapLeaf hr hargs hatts]

/-- **Qualification preserves claim status.** Renaming a member's leaves by its
alias changes no claim's four-state status, which is what entitles a map to
report a member's arguments under map-wide names. -/
theorem statusC_mapLeaf
    {P₁ : CheckedProgram canon Pi Gamma CertOk dp}
    {P₂ : CheckedProgram canon Pi Gamma' CertOk dp}
    (hr : Function.Injective r)
    (hargs : P₂.args = P₁.args.map (mapLeaf r))
    (hatts : P₂.atts = P₁.atts.map (mapLeafAtt r))
    (c : Claim) :
    statusC (checkedAF P₁) c = statusC (checkedAF P₂) c := by
  rw [checkedAF_mapLeaf hr hargs hatts]

/-- **Qualification is status-preserving by construction.** The renamed program
is exhibited, so nothing here is conditional on such a program existing. -/
theorem statusC_mapLeafProg
    (P : CheckedProgram canon Pi Gamma CertOk dp)
    (hr : Function.Injective r)
    (hΓ : ∀ l p, Gamma l = some p → Gamma' (r l) = some p)
    (c : Claim) :
    statusC (checkedAF P) c = statusC (checkedAF (mapLeafProg P hr hΓ)) c :=
  statusC_mapLeaf hr (mapLeafProg_args P hr hΓ) (mapLeafProg_atts P hr hΓ) c

end Invariance

/-! ### Qualified leaf environments

The renaming hypothesis the transport results take is not an assumption a map
makes: it is a fact about the environment qualification builds. -/

/-- Qualify a member's declared leaf list by its alias. -/
def qualifyGamma (memberAlias : String) (γ : List (LeafId × Atom)) :
    List (LeafId × Atom) :=
  γ.map (fun e => (qualifyLeaf memberAlias e.1, e.2))

/-- **The qualified environment says of a qualified name what the member's own
environment said of the local one.** This is the `hΓ` premise of
`hasSupport_mapLeaf`, discharged for the map's actual rename. -/
theorem buildGamma_qualifyGamma (memberAlias : String) (γ : List (LeafId × Atom)) :
    ∀ l p, Admission.buildGamma γ l = some p →
      Admission.buildGamma (qualifyGamma memberAlias γ) (qualifyLeaf memberAlias l) = some p := by
  intro l p
  induction γ with
  | nil => intro h; simp [Admission.buildGamma] at h
  | cons e rest ih =>
    obtain ⟨l₀, p₀⟩ := e
    by_cases hl : l₀ = l
    · subst hl
      intro h
      simp only [Admission.buildGamma, List.find?_cons, decide_true, qualifyGamma,
        List.map_cons] at h ⊢
      simpa using h
    · have hq : ¬ (qualifyLeaf memberAlias l₀ = qualifyLeaf memberAlias l) :=
        fun heq => hl (qualifyLeaf_injective memberAlias heq)
      intro h
      simp only [Admission.buildGamma, List.find?_cons, hl,
        decide_false, qualifyGamma, List.map_cons] at h ⊢
      simp only [hq, decide_false]
      exact ih h

/-- **Two members' qualified environments are disjoint.** Nothing a member
declares can shadow, or be shadowed by, anything another member declares — which
is what makes the linked environment's first-wins lookup insensitive to member
order. -/
theorem qualifyGamma_disjoint {a a' : String} (h : a ≠ a')
    (γ γ' : List (LeafId × Atom)) :
    ∀ l ∈ (qualifyGamma a γ).map Prod.fst,
      l ∉ (qualifyGamma a' γ').map Prod.fst := by
  intro l hl hl'
  simp only [qualifyGamma, List.map_map, List.mem_map] at hl hl'
  obtain ⟨e, _, he⟩ := hl
  obtain ⟨e', _, he'⟩ := hl'
  exact qualifyLeaf_ne_of_alias_ne h e.1 e'.1 (he.trans he'.symm)

end Lara.Map
