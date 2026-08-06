/-
Shared raw attack identity for the policy admission boundary (metatheory
plan, Task 1) and the wire driver.

A raw attack names its endpoints by declared argument id.  Distinct argument
ids may carry equal support terms, so endpoint-safe filtering MUST use the raw
endpoint ids and cannot identify attacks by their resolved support terms.  The
`selectAligned` combinator keeps the raw and resolved lists in lockstep — the
resolved list is the image of the raw list in the same row order — so
filtering the raw attacks by endpoint id yields exactly the aligned
projection of the already-resolved attacks.

This module is the shared home for that vocabulary, factored out of
`Lara.Driver` (which decodes wire attacks) so the admission model
(`Lara.Admission`) can consume it without the codec.  `Lara.BlockedProgram`
reuses `selectAligned` here; its theorem statements are unchanged.
-/
import Lara.Attack
import Lara.Support

namespace Lara.RawAttack

open Lara.Support Lara.Attack

/-- A wire attack with its endpoints still as declared argument ids. -/
inductive RawAttack where
  | rebut : String → String → RawAttack
  | undercut : String → String → Pos → RawAttack
  | undermine : String → String → Pos → RawAttack
deriving instance DecidableEq for RawAttack

/-- The declared-argument-id endpoints of a raw attack. -/
def RawAttack.endpoints : RawAttack → String × String
  | .rebut w u => (w, u)
  | .undercut w u _ => (w, u)
  | .undermine w u _ => (w, u)

/-- First-declaration lookup of an argument id, mirroring the wire decoder's
`find`-based endpoint resolution (duplicate argument ids are rejected at R14
before any resolution). -/
def lookupArg (argsRaw : List (String × SupportTerm)) (id : String) :
    Option SupportTerm :=
  (argsRaw.find? (fun e => e.1 == id)).map (·.2)

/-- **Unique argument ids make the first-declaration lookup exact.**  With
duplicate ids ruled out (R14), every declared row is the row its own id
resolves to — so an endpoint that names a retained argument resolves to *that*
argument's support term, and never to a same-id row the prune removed.  This is
the invariant `AlignedAttacks` carries into the admission model. -/
theorem lookupArg_of_mem_nodup :
    ∀ {argsRaw : List (String × SupportTerm)},
      (argsRaw.map (·.1)).Nodup →
      ∀ {a : String × SupportTerm}, a ∈ argsRaw → lookupArg argsRaw a.1 = some a.2 := by
  intro argsRaw
  induction argsRaw with
  | nil => intro _ a ha; simp at ha
  | cons head rest ih =>
      intro hnodup a ha
      rw [List.map_cons] at hnodup
      obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [lookupArg]
      · have hmem : a.1 ∈ rest.map (·.1) := List.mem_map.mpr ⟨a, ha, rfl⟩
        have hne : ¬ (head.1 = a.1) := by
          intro heq
          exact hhead (heq ▸ hmem)
        have hrest := ih htail ha
        unfold lookupArg at hrest ⊢
        rw [List.find?_cons_of_neg (by simpa using hne)]
        exact hrest

/-- Resolve raw attacks against the declared argument table, in row order.
Mirrors the wire decoder: an attack whose endpoint is not a declared argument
id is an error (R14); on the `.lara` path the front door validates endpoints
before a `Unit` exists. -/
def resolveAttacks (argsRaw : List (String × SupportTerm)) :
    List RawAttack → Except String (List Attack)
  | [] => .ok []
  | ra :: rest => do
      let (s, t) := ra.endpoints
      match lookupArg argsRaw s, lookupArg argsRaw t with
      | some sw, some tw => do
          let k := (match ra with
            | .rebut _ _ => Attack.rebut sw tw
            | .undercut _ _ π => Attack.undercut sw tw π
            | .undermine _ _ π => Attack.undermine sw tw π)
          let rest' ← resolveAttacks argsRaw rest
          .ok (k :: rest')
      | _, _ => .error "attacks: attack endpoint is not a declared argument"

/-- Filter a value list by the corresponding raw declaration's keep predicate.
Production uses this to drop attacks by raw endpoint id while retaining the
already-resolved `Attack` in the same row. -/
def selectAligned (keep : α → Bool) : List α → List β → List β
  | key :: keys, value :: values =>
      if keep key then value :: selectAligned keep keys values
      else selectAligned keep keys values
  | _, _ => []

/-- One `resolveAttacks` step for a rebut attack: the endpoint projections of
the destructuring let reduce away, leaving the raw lookups as the match
scrutinees.  `rfl` because the definitions are transparent. -/
theorem resolveAttacks_rebut (argsRaw : List (String × SupportTerm))
    (w u : String) (rest : List RawAttack) :
    resolveAttacks argsRaw ((RawAttack.rebut w u) :: rest) =
      match lookupArg argsRaw w, lookupArg argsRaw u with
      | some sw, some tw =>
          (resolveAttacks argsRaw rest).bind (fun rest' =>
            .ok (Attack.rebut sw tw :: rest'))
      | _, _ => .error "attacks: attack endpoint is not a declared argument" := by
  rfl

/-- One `resolveAttacks` step for an undercut attack (see `resolveAttacks_rebut`). -/
theorem resolveAttacks_undercut (argsRaw : List (String × SupportTerm))
    (w u : String) (π : Pos) (rest : List RawAttack) :
    resolveAttacks argsRaw ((RawAttack.undercut w u π) :: rest) =
      match lookupArg argsRaw w, lookupArg argsRaw u with
      | some sw, some tw =>
          (resolveAttacks argsRaw rest).bind (fun rest' =>
            .ok (Attack.undercut sw tw π :: rest'))
      | _, _ => .error "attacks: attack endpoint is not a declared argument" := by
  rfl

/-- One `resolveAttacks` step for an undermine attack (see `resolveAttacks_rebut`). -/
theorem resolveAttacks_undermine (argsRaw : List (String × SupportTerm))
    (w u : String) (π : Pos) (rest : List RawAttack) :
    resolveAttacks argsRaw ((RawAttack.undermine w u π) :: rest) =
      match lookupArg argsRaw w, lookupArg argsRaw u with
      | some sw, some tw =>
          (resolveAttacks argsRaw rest).bind (fun rest' =>
            .ok (Attack.undermine sw tw π :: rest'))
      | _, _ => .error "attacks: attack endpoint is not a declared argument" := by
  rfl

/-- Resolution commutes with raw-endpoint filtering: resolving the kept raw
attacks yields exactly the aligned projection of the full resolution,
whenever the full resolution succeeds.  (The wire boundary reports a failing
resolution as R14 before any filtering happens; on the `.lara` path endpoint
validity is a front-door precondition.) -/
theorem resolve_filter_commute (argsRaw : List (String × SupportTerm))
    (keep : RawAttack → Bool) :
    ∀ {rawAtts : List RawAttack} {atts : List Attack},
      resolveAttacks argsRaw rawAtts = .ok atts →
      resolveAttacks argsRaw (rawAtts.filter keep) =
        .ok (selectAligned keep rawAtts atts) := by
  intro rawAtts
  induction rawAtts with
  | nil =>
      intro atts h
      simp [resolveAttacks, selectAligned] at h ⊢
  | cons ra rest ih =>
      rcases ra with ⟨w, u⟩ | ⟨w, u, π⟩ | ⟨w, u, π⟩
      · intro atts h
        simp [resolveAttacks_rebut] at h
        cases hw : lookupArg argsRaw w with
        | none => simp [hw] at h
        | some sw =>
            cases hu : lookupArg argsRaw u with
            | none => simp [hw, hu] at h
            | some tw =>
                cases hr : resolveAttacks argsRaw rest with
                | error e => simp [hw, hu, hr, Except.bind] at h
                | ok restAtts =>
                    have hatts : atts = Attack.rebut sw tw :: restAtts := by
                      simp [hw, hu, hr] at h
                      injection h with h'
                      exact h'.symm
                    subst atts
                    by_cases hkeep : keep (.rebut w u) = true
                    · simp [resolveAttacks_rebut, hw, hu, List.filter,
                        selectAligned, Except.bind, hkeep, ih hr]
                    · simp [resolveAttacks_rebut, hw, hu, List.filter,
                        selectAligned, Except.bind, hkeep, ih hr]
      · intro atts h
        simp [resolveAttacks_undercut] at h
        cases hw : lookupArg argsRaw w with
        | none => simp [hw] at h
        | some sw =>
            cases hu : lookupArg argsRaw u with
            | none => simp [hw, hu] at h
            | some tw =>
                cases hr : resolveAttacks argsRaw rest with
                | error e => simp [hw, hu, hr, Except.bind] at h
                | ok restAtts =>
                    have hatts : atts = Attack.undercut sw tw π :: restAtts := by
                      simp [hw, hu, hr] at h
                      injection h with h'
                      exact h'.symm
                    subst atts
                    by_cases hkeep : keep (.undercut w u π) = true
                    · simp [resolveAttacks_undercut, hw, hu, List.filter,
                        selectAligned, Except.bind, hkeep, ih hr]
                    · simp [resolveAttacks_undercut, hw, hu, List.filter,
                        selectAligned, Except.bind, hkeep, ih hr]
      · intro atts h
        simp [resolveAttacks_undermine] at h
        cases hw : lookupArg argsRaw w with
        | none => simp [hw] at h
        | some sw =>
            cases hu : lookupArg argsRaw u with
            | none => simp [hw, hu] at h
            | some tw =>
                cases hr : resolveAttacks argsRaw rest with
                | error e => simp [hw, hu, hr, Except.bind] at h
                | ok restAtts =>
                    have hatts : atts = Attack.undermine sw tw π :: restAtts := by
                      simp [hw, hu, hr] at h
                      injection h with h'
                      exact h'.symm
                    subst atts
                    by_cases hkeep : keep (.undermine w u π) = true
                    · simp [resolveAttacks_undermine, hw, hu, List.filter,
                        selectAligned, Except.bind, hkeep, ih hr]
                    · simp [resolveAttacks_undermine, hw, hu, List.filter,
                        selectAligned, Except.bind, hkeep, ih hr]


/-- A successful endpoint lookup witnesses declaration membership by raw
argument id. This is the identity fact needed when an argument prune retains
every declaration. -/
private theorem lookupArg_some_endpoint_mem (argsRaw : List (String × SupportTerm))
    {id : String} {term : SupportTerm} (h : lookupArg argsRaw id = some term) :
    id ∈ argsRaw.map (·.1) := by
  unfold lookupArg at h
  cases hf : argsRaw.find? (fun e => e.1 == id) with
  | none => simp [hf] at h
  | some entry =>
      have hmem : entry ∈ argsRaw := List.mem_of_find?_eq_some hf
      have hpred : (entry.1 == id) = true :=
        List.find?_some (p := fun e : String × SupportTerm => e.1 == id) hf
      have hid : entry.1 = id := by simpa using hpred
      exact List.mem_map.mpr ⟨entry, hmem, hid⟩

/-- Successful resolution proves that every raw attack names two declared
argument ids. -/
theorem resolveAttacks_endpoints_mem (argsRaw : List (String × SupportTerm)) :
    ∀ {rawAtts : List RawAttack} {atts : List Attack},
      resolveAttacks argsRaw rawAtts = .ok atts →
      ∀ ra ∈ rawAtts,
        ra.endpoints.1 ∈ argsRaw.map (·.1) ∧
        ra.endpoints.2 ∈ argsRaw.map (·.1) := by
  intro rawAtts
  induction rawAtts with
  | nil => intro atts h ra hra; simp at hra
  | cons head rest ih =>
      intro atts h ra hra
      rcases head with ⟨w, u⟩ | ⟨w, u, π⟩ | ⟨w, u, π⟩ <;>
        simp only [List.mem_cons] at hra <;>
        cases hw : lookupArg argsRaw w with
        | none =>
            simp [resolveAttacks_rebut, resolveAttacks_undercut,
              resolveAttacks_undermine, hw] at h
        | some sw =>
          cases hu : lookupArg argsRaw u with
          | none =>
              simp [resolveAttacks_rebut, resolveAttacks_undercut,
                resolveAttacks_undermine, hw, hu] at h
          | some tw =>
            cases hr : resolveAttacks argsRaw rest with
            | error e =>
                simp [resolveAttacks_rebut, resolveAttacks_undercut,
                  resolveAttacks_undermine, hw, hu, hr, Except.bind] at h
            | ok restAtts =>
              rcases hra with rfl | hra
              · exact ⟨lookupArg_some_endpoint_mem argsRaw hw,
                  lookupArg_some_endpoint_mem argsRaw hu⟩
              · exact ih hr ra hra

/-- Pointwise predicate strengthening preserves every aligned selected value.
The proof follows raw keys and resolved values in lockstep, including
duplicate semantic values. -/
theorem selectAligned_mono {keep₁ keep₂ : α → Bool}
    (hmono : ∀ key, keep₂ key = true → keep₁ key = true) :
    ∀ (keys : List α) (values : List β) (value : β),
      value ∈ selectAligned keep₂ keys values →
      value ∈ selectAligned keep₁ keys values := by
  intro keys
  induction keys with
  | nil => intro values value h; simp [selectAligned] at h
  | cons key keys ih =>
      intro values value h
      cases values with
      | nil => simp [selectAligned] at h
      | cons head values =>
          by_cases hk₂ : keep₂ key = true
          · have hk₁ := hmono key hk₂
            simp only [selectAligned, hk₂, hk₁, if_true, List.mem_cons] at h ⊢
            rcases h with rfl | h
            · exact Or.inl rfl
            · exact Or.inr (ih values value h)
          · simp only [selectAligned, hk₂] at h
            by_cases hk₁ : keep₁ key = true
            · simp only [selectAligned, hk₁, if_true, List.mem_cons]
              exact Or.inr (ih values value h)
            · simp only [selectAligned, hk₁]
              exact ih values value h
end Lara.RawAttack
