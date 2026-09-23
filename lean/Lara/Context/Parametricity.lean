/-
# Theory M4 — relational parametricity over related backends

`Lara.Context.backend_replacement_congruence` quantifies over a *function*
`f : Assurance → Assurance` and relates `F` to `mapAssurFrag f F`. This module
replaces the function with a **relation** `R : Assurance → Assurance → Prop`,
lifted structurally through support terms, attacks and fragments, and relates
any two `R`-related fragments. That is the form M4's acceptance criterion
reserves the word *parametricity* for (`docs/theory-m4-contextual-adequacy.md`
§6, "Must not claim").

**The relation is not arbitrary, and cannot be.** `RelInj` below requires `R` to
reflect and preserve equality on the assurances it relates — i.e. to be a
partial bijection. Three consumers force it: the structural merge `dedupList`,
the coverage decider `coveredB`, and `checkUnit_complete`'s `Nodup` premise.
`relInj_necessary` witnesses the failure directly rather than leaving it
asserted. So the honest name is *parametricity over partial-bijective
certificate relations*.

**What the relational form buys over the functional one.** `AssurPreserving f`
quantifies over every rule and every assurance in the type — a global hypothesis
the docstrings of `registry_swap_congruence` and `registry_swap_congruence_sem`
both flag as stronger than "agrees on the fragment's occurrences".
`RelPreserving R` is conditioned on `R α β`, so a relation inhabited only where
the fragment carries certificates yields exactly the localized hypothesis. That
is the gain; it is not "arbitrary relations".

**This is not Part B.** `RelTerm` lifts a relation on *certificates*
structurally. It is not a logical relation over the contrary-visible occurrence
profile, and nothing here reopens the full-abstraction gate descoped in
`docs/theory-m4-contextual-adequacy.md` §7.

**The chain, and where the relation dies.**

```
  Layer 0 — the two side conditions
      RelPreserving R
      RelInj R ──► relTerm_inj ──► relAtt_source_inj

  Layer 1 — the judgments transport            [needs RelPreserving]
      hasSupport_rel ──► hasAttack_rel          (not siblings: hasAttack_rel
                                                 calls hasSupport_rel in all
                                                 three of its cases)

  Layer 2 — the saturation                     [needs hasSupport_rel]
      conclusionCache_rel ──► crossAtts_rel

  Layer 3 — the merge and the Bool deciders    [needs relTerm_inj]
      dedupList_rel                             [CONSUMER 1 — dedupList]
      containsB_rel ──► attackClosureB_rel ─┐
      relAtt_source_inj ───────────────────►┴► coveredB_rel
                                                [CONSUMER 2 — coveredB]

  Layer 4 — the linked unit and acceptance
      crossAtts_rel, dedupList_rel        ──► link_rel_commutes
      hasSupport_rel                      ──► attackComplete_rel
      hasSupport_rel, hasAttack_rel,
        attackComplete_rel, relTerm_inj   ──► checkUnit_rel
                                              [CONSUMER 3 — the Nodup premise]

  Layer 5 — the carrier
      link_rel_commutes, checkUnit_rel    ──► exists_accepted_rel
      hasSupport_rel                      ──► nodes_conclusion_rel
      coveredB_rel, nodes_conclusion_rel  ──► compileUnit_rel
      link_rel_commutes, compileUnit_rel  ──► compileUnit_link_rel

  ══════════════════ RELATION ERASED HERE ══════════════════
  `compileUnit_rel` concludes an EQUATION between `StructuredAF`s, so from
  here down both branches run one and the same framework. No fixpoint lemma
  is needed, and none is used.

  Layer 6 — the headline; the single root consumes exists_accepted_rel +
            compileUnit_link_rel, and every other node is an instantiation
      obsGen_parametricity                      (any projection g)
        ├─► backend_replacement_parametricity_sem   (any ExtensionSemantics)
        │     └─► backend_replacement_parametricity_local_sem
        └─► backend_replacement_parametricity     (obs — the obsGen instance at
              │                                    Invariants.status canon;
              │                                    obs_eq_obsGen makes the two
              │                                    result types the same type,
              │                                    so no separate argument is
              │                                    needed)
              ├─► backend_replacement_parametricity_local   (occurrence-local)
              └─► backend_replacement_congruence_of_parametricity  (the
                    └─► congruence_correspondence   functional theorem,
                                                    via graphOf)

  Composition: dedupList_rel + the two RelFixesContext hypotheses
      ──► relFixesContext_composed
      ──► obsGen_parametricity_composed (obsGen_parametricity at the composite)
        ├─► backend_replacement_parametricity_composed_sem
        └─► backend_replacement_parametricity_composed
      admissible_composed supplies admissibility from the halves unchanged.

  Closed-link union: occurrences_composed + mem_closedOccurrences
      closedOccRel ──► relInj_closedOccRel, relFrag_closedOccRel,
                      relFixesContext_closedOccRel
      ──► obsGen_parametricity_closed_local (instance of obsGen_parametricity)
        ├─► whole_program_parametricity_local_sem
        └─► whole_program_parametricity_local

  Already-checked whole programs, a separate carrier route:
      coveredB_rel ──► edgeB_rel ──► checkedAF_rel
        ├─► whole_program_parametricity_sem
        └─► whole_program_parametricity
      Neither admissibility nor acceptance transport is needed on this route.
```

**Diagram maintenance is part of the change.** If a lemma is added to or removed
from this chain, update the diagram in the same commit. A stale diagram is worse
than none.
-/

import Lara.ListRel
import Lara.Context.Observation

-- `lean/lakefile.toml` sets no `leanOptions`, so `autoImplicit` is ON tree-wide.
-- This module hand-authors ~40 theorem statements; a bare unopened or mistyped
-- predicate in a hypothesis position would auto-bind as an implicit of unknown
-- type and elaborate into a VACUOUS theorem that builds clean, passes
-- `scripts/check-axioms.sh` (standard trio only) and passes
-- `scripts/check-axcheck-coverage.py`. Neither CI gate can see it. Turning
-- autoImplicit off converts that silent failure into a compile error.
--
-- The shared binders are hoisted into `section`/`variable`, as in the two
-- modules this one mirrors (`Lara/Context/Equivalence.lean`,
-- `Lara/EraseTransport.lean`). A `variable` reaches a declaration only when
-- that declaration's *statement* mentions it, and hoisted binders precede the
-- declaration's own — so when editing a statement here, check the elaborated
-- signature (`#check @…`) rather than reading the binder list, and keep each
-- section's `variable` order equal to the order the statements already used.
set_option autoImplicit false

namespace Lara.Context

-- The open list matches `lean/Lara/Context/Observation.lean:97`, NOT
-- `lean/Lara/Context/Equivalence.lean:43`. `Lara.Check` and `Lara.Semantics`
-- are both required: `backend_replacement_parametricity_sem` binds
-- `(sem : ExtensionSemantics)`, which lives in `lean/Lara/Semantics.lean`.
open Lara.Support Lara.Attack Lara.Compile Lara.Check Lara.Erase Lara.Semantics


/-! ### A relation on certificates, lifted structurally

`RelTerm R` relates two support terms that are identical except that
corresponding assurance positions are `R`-related. Rule identity, substitution,
premise shape, discharge keys and hypothesis lists all match on the nose —
those are what the checker and the saturation read, and a relation that moved
them would not be a *certificate* relation. -/

mutual
  /-- Two support terms, identical up to `R`-related assurances. -/
  inductive RelTerm (R : Assurance → Assurance → Prop) :
      SupportTerm → SupportTerm → Prop where
    | leaf (l : LeafId) : RelTerm R (.leaf l) (.leaf l)
    | inst {rn : RuleId} {θ : Subst} {ws₁ ws₂ : List SupportTerm}
        {D₁ D₂ : List (QuestionId × SupportTerm)} {H : List QuestionId}
        {α₁ α₂ : Assurance}
        (hws : RelTerms R ws₁ ws₂) (hD : RelDis R D₁ D₂) (hα : R α₁ α₂) :
        RelTerm R (.inst rn θ ws₁ D₁ H α₁) (.inst rn θ ws₂ D₂ H α₂)
  /-- Pointwise `RelTerm` on premise lists. -/
  inductive RelTerms (R : Assurance → Assurance → Prop) :
      List SupportTerm → List SupportTerm → Prop where
    | nil : RelTerms R [] []
    | cons {w₁ w₂ : SupportTerm} {ws₁ ws₂ : List SupportTerm}
        (hw : RelTerm R w₁ w₂) (hws : RelTerms R ws₁ ws₂) :
        RelTerms R (w₁ :: ws₁) (w₂ :: ws₂)
  /-- Pointwise `RelTerm` on discharge lists, with question keys fixed. -/
  inductive RelDis (R : Assurance → Assurance → Prop) :
      List (QuestionId × SupportTerm) → List (QuestionId × SupportTerm) → Prop where
    | nil : RelDis R [] []
    | cons {q : QuestionId} {w₁ w₂ : SupportTerm}
        {rest₁ rest₂ : List (QuestionId × SupportTerm)}
        (hw : RelTerm R w₁ w₂) (hrest : RelDis R rest₁ rest₂) :
        RelDis R ((q, w₁) :: rest₁) ((q, w₂) :: rest₂)
end

/-- Attacks are related when their stored terms are, with kind and position
fixed. Mirrors `Erase.mapAssurAtt`. -/
inductive RelAtt (R : Assurance → Assurance → Prop) : Attack → Attack → Prop where
  | rebut {w₁ w₂ u₁ u₂ : SupportTerm} (hw : RelTerm R w₁ w₂) (hu : RelTerm R u₁ u₂) :
      RelAtt R (.rebut w₁ u₁) (.rebut w₂ u₂)
  | undercut {w₁ w₂ u₁ u₂ : SupportTerm} {π : Pos}
      (hw : RelTerm R w₁ w₂) (hu : RelTerm R u₁ u₂) :
      RelAtt R (.undercut w₁ u₁ π) (.undercut w₂ u₂ π)
  | undermine {w₁ w₂ u₁ u₂ : SupportTerm} {π : Pos}
      (hw : RelTerm R w₁ w₂) (hu : RelTerm R u₁ u₂) :
      RelAtt R (.undermine w₁ u₁ π) (.undermine w₂ u₂ π)

/-- **Two fragments related by `R`.** Everything the link guard reads — Σ,
policy, declared leaves, ground atoms, imports, exports — is equal on the nose,
which is what makes `linkFault` blind to the relation exactly as
`linkFault_mapAssurFrag` makes it blind to a relabel. Only the declared
material moves.

Both list fields are stated as `Forall₂`, not as `RelTerms`. The mutual
inductive `RelTerms` exists only because `RelTerm` must recurse through
`SupportTerm`'s nested `List` fields inside a single `mutual` block
(`Lara/Support.lean:60`).

**The development speaks both spellings, and the bridge is paid eight times, not
once.** `Forall₂` is the spelling of the two `RelFrag` fields and of everything
that reads them — `dedupList_rel`, `attackComplete_rel`, `checkUnit_rel`,
`nodes_conclusion_rel`, `compileUnit_rel`. `RelTerms` survives wherever a lemma
is stated directly against a `RelTerm.inst` premise — `conclusionCache_rel`,
`argsWellSorted_rel`, `signatureStage_rel` — and `crossAtts_rel` crosses in one
proof twice. `relTerms_iff_forall₂` is the bridge; it is cheap, but it is not
free and it is not paid once.

**`RelTerms`' list layer is reached through `Forall₂`, deliberately.** All four
`relTerms_*` list lemmas — `_length`, `_getElem?_right`, `_getElem?_left`,
`_getElem?_none` — are one-line instantiations of the corresponding
`Lara.Forall₂` lemma through the bridge, so the list reasoning lives in
`lean/Lara/ListRel.lean` and is not re-proved here. The five `RelDis` lemmas do
*not* follow this pattern: they need the shared-key structure of
`RelDis.cons`, which `Forall₂` does not carry. -/
structure RelFrag (R : Assurance → Assurance → Prop) (F₁ F₂ : Fragment) : Prop where
  sigma     : F₂.sigma = F₁.sigma
  policy    : F₂.policy = F₁.policy
  gammaFrag : F₂.gammaFrag = F₁.gammaFrag
  ground    : F₂.ground = F₁.ground
  imports   : F₂.imports = F₁.imports
  exports   : F₂.exports = F₁.exports
  args      : Forall₂ (RelTerm R) F₁.args F₂.args
  atts      : Forall₂ (RelAtt R) F₁.atts F₂.atts

/-- **`R` reflects and preserves equality on what it relates.** Equivalently:
`R` is the graph of a partial injection. `relInj_necessary` is the witness that
this cannot be dropped; `dedupList`, `coveredB` and `checkUnit_complete`'s
`Nodup` premise are the three consumers. -/
def RelInj (R : Assurance → Assurance → Prop) : Prop :=
  ∀ α₁ α₂ β₁ β₂, R α₁ β₁ → R α₂ β₂ → (α₁ = α₂ ↔ β₁ = β₂)

/-- **Acceptance transports along `R`.** The relational form of
`AssurPreserving` (`lean/Lara/Context/Equivalence.lean:168`).

The quantifier is guarded by `R α β`, and that guard is the point: where
`AssurPreserving f` obliges every assurance in the type, this obliges only the
pairs `R` actually relates. A relation inhabited exactly at a fragment's
certificate occurrences therefore yields a hypothesis about exactly those
occurrences — the localization `registry_swap_congruence`'s docstring names as
the hypothesis it does not itself carry. -/
def RelPreserving (R : Assurance → Assurance → Prop)
    (CertOk₁ CertOk₂ : BackendId → Digest → CertRef → List Atom → Atom → Prop) : Prop :=
  ∀ (r : Rule) (As : List Atom) (C : Atom) (α β : Assurance),
    R α β → AssuranceOk CertOk₁ r As C α → AssuranceOk CertOk₂ r As C β

/-- **The relational reading of `FixesContext`.** A backend swap inside the
fragment is not licensed to move the context's own certificates, so `R` must
relate the context's material to itself.

Note the consequence, recorded in `docs/theory-m4-relational-parametricity.md`:
combined with `RelInj`, this makes `R` the *identity* on the context's
occurrences. An assurance appearing in both `C` and `F` therefore cannot move.
That is inherited from `FixesContext` and is correct, but it bounds how local
the localized hypothesis can be. -/
structure RelFixesContext (R : Assurance → Assurance → Prop) (C : Context) : Prop where
  args : Forall₂ (RelTerm R) C.frame.args C.frame.args
  atts : Forall₂ (RelAtt R) C.frame.atts C.frame.atts

section Lifting

variable {R : Assurance → Assurance → Prop}

/-- `RelTerms` is `Forall₂ (RelTerm R)` — the bridge between the spelling the
mutual block forces and the spelling this development consumes. -/
theorem relTerms_iff_forall₂ {ws₁ ws₂ : List SupportTerm} :
    RelTerms R ws₁ ws₂ ↔ Forall₂ (RelTerm R) ws₁ ws₂ := by
  -- `induction` cannot eliminate `RelTerms` (it is mutually inductive with
  -- `RelTerm`), so both directions recurse on the *list* and `cases` the
  -- derivation. Same shape, no mutual recursor needed.
  constructor
  · intro h
    induction ws₁ generalizing ws₂ with
    | nil => cases h; exact .nil
    | cons _ _ ih => cases h with | cons hw hws => exact .cons hw (ih hws)
  · intro h
    induction ws₁ generalizing ws₂ with
    | nil => cases h; exact .nil
    | cons _ _ ih => cases h with | cons hw hws => exact .cons hw (ih hws)

theorem relTerms_length {ws₁ ws₂ : List SupportTerm} (h : RelTerms R ws₁ ws₂) :
    ws₁.length = ws₂.length :=
  Forall₂.length_eq (relTerms_iff_forall₂.mp h)

/-! ### `RelInj` characterized

`RelInj R` says exactly that `R` is the graph of a **partial injection**: taking
`α₁ = α₂` forces `β₁ = β₂` (single-valued), and taking `β₁ = β₂` forces
`α₁ = α₂` (injective). Both halves are cited by
`docs/theory-m4-relational-parametricity.md`; neither should be left to prose.

The single-valued half is the surprising one — a predicate named `Inj` is also
secretly a function — and it is what the strength argument starts from.

**The finite realization step is proved in `Context/FiniteExtension.lean`.**
`relFrag_exists_injective_fixesContext` constructs a total injective map
realizing the fragment and fixing the context. It extends only the finite
occurrence restriction of `R`, not all of `R`: the unrestricted assertion is
false (`not_every_relInj_has_total_extension`). Global `AssurPreserving` remains
a separate obligation; see `docs/theory-m4-relational-parametricity.md` §4. -/

theorem relInj_functional (hR : RelInj R)
    {α β₁ β₂ : Assurance} (h₁ : R α β₁) (h₂ : R α β₂) : β₁ = β₂ :=
  (hR _ _ _ _ h₁ h₂).mp rfl

theorem relInj_injective (hR : RelInj R)
    {α₁ α₂ β : Assurance} (h₁ : R α₁ β) (h₂ : R α₂ β) : α₁ = α₂ :=
  (hR _ _ _ _ h₁ h₂).mpr rfl

end Lifting


/-! ### Why the relation must reflect equality

`coveredB` decides `k.source = source` (`lean/Lara/Compile.lean:441`), so an
attack declared against one of two collapsed arguments covers *both* after the
collapse. This is the concrete form of the failure `Lara.Erase`'s header records
for the non-injective erase-to-`certified` map. -/

/-- Two distinct assurances. `BackendId` has **two** fields (`name`, `version`);
`Digest` has one (`hash`) and `CertRef` one (`payload : SExpr`). -/
private def certA : Assurance := .cert ⟨"b", 0⟩ ⟨"d1"⟩ ⟨.atom "k1"⟩
private def certB : Assurance := .cert ⟨"b", 0⟩ ⟨"d2"⟩ ⟨.atom "k2"⟩

private def leafA : SupportTerm := .leaf ⟨"a"⟩
private def instOf (α : Assurance) : SupportTerm := .inst ⟨"r"⟩ [] [] [] [] α

/-- The collapsing relation: both distinct certificates relate to `.trusted`. -/
private def collapse : Assurance → Assurance → Prop :=
  fun α β => (α = certA ∨ α = certB) ∧ β = .trusted

/-- **`RelInj` is necessary, not convenient.** These are the hypotheses of
`coveredB_rel` minus `RelInj`, and its conclusion fails. So no proof of
`coveredB_rel` can drop `hR`, and `RelInj` is forced by the theorem rather than
by the proof strategy. -/
theorem relInj_necessary :
    ∃ (R : Assurance → Assurance → Prop) (atts₁ atts₂ : List Attack.Attack)
      (s₁ s₂ t₁ t₂ : SupportTerm),
      Forall₂ (RelAtt R) atts₁ atts₂ ∧ RelTerm R s₁ s₂ ∧ RelTerm R t₁ t₂ ∧
        coveredB atts₂ s₂ t₂ ≠ coveredB atts₁ s₁ t₁ := by
  refine ⟨collapse, [.rebut leafA (instOf certA)], [.rebut leafA (instOf .trusted)],
    leafA, leafA, instOf certB, instOf .trusted, ?_, ?_, ?_, ?_⟩
  · exact .cons (.rebut (.leaf _) (.inst .nil .nil ⟨.inl rfl, rfl⟩)) .nil
  · exact .leaf _
  · exact .inst .nil .nil ⟨.inr rfl, rfl⟩
  · decide


/-! ### The functional case, as a relation

`graphOf f` is the relation the existing development uses implicitly. These
lemmas are what let the functional theorems be re-derived as corollaries
instead of leaving two parallel developments in the repository. -/

/-- The graph of a relabel function. -/
def graphOf (f : Assurance → Assurance) : Assurance → Assurance → Prop :=
  fun α β => β = f α

mutual
  theorem relTerm_graphOf (f : Assurance → Assurance) :
      ∀ w : SupportTerm, RelTerm (graphOf f) w (mapAssur f w)
    | .leaf l => .leaf l
    | .inst _ _ ws D _ _ =>
        .inst (relTerms_graphOf f ws) (relDis_graphOf f D) rfl
  theorem relTerms_graphOf (f : Assurance → Assurance) :
      ∀ ws : List SupportTerm, RelTerms (graphOf f) ws (mapAssurList f ws)
    | [] => .nil
    | w :: ws => .cons (relTerm_graphOf f w) (relTerms_graphOf f ws)
  theorem relDis_graphOf (f : Assurance → Assurance) :
      ∀ D : List (QuestionId × SupportTerm), RelDis (graphOf f) D (mapAssurDis f D)
    | [] => .nil
    | (_, w) :: rest => .cons (relTerm_graphOf f w) (relDis_graphOf f rest)
end

theorem relAtt_graphOf (f : Assurance → Assurance) (k : Attack.Attack) :
    RelAtt (graphOf f) k (mapAssurAtt f k) := by
  cases k with
  | rebut w u => exact .rebut (relTerm_graphOf f w) (relTerm_graphOf f u)
  | undercut w u π => exact .undercut (relTerm_graphOf f w) (relTerm_graphOf f u)
  | undermine w u π => exact .undermine (relTerm_graphOf f w) (relTerm_graphOf f u)

theorem relFrag_graphOf (f : Assurance → Assurance) (F : Fragment) :
    RelFrag (graphOf f) F (mapAssurFrag f F) where
  sigma := rfl
  policy := rfl
  gammaFrag := rfl
  ground := rfl
  imports := rfl
  exports := rfl
  args := by
    rw [mapAssurFrag_args, ← mapAssurList_eq]
    exact relTerms_iff_forall₂.mp (relTerms_graphOf f F.args)
  atts := by
    rw [mapAssurFrag_atts]
    exact Forall₂.of_map_right (fun k _ => relAtt_graphOf f k)

section Graph

variable {f : Assurance → Assurance}

/-- **`RelInj` is exactly injectivity, in the functional case.** -/
theorem relInj_graphOf (hf : Function.Injective f) :
    RelInj (graphOf f) := by
  intro α₁ α₂ β₁ β₂ h₁ h₂
  subst h₁; subst h₂
  exact ⟨fun h => by rw [h], fun h => hf h⟩

/-- **`RelPreserving` is exactly `AssurPreserving`, in the functional case.** -/
theorem relPreserving_graphOf
    {CertOk₁ CertOk₂ : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (hpres : AssurPreserving f CertOk₁ CertOk₂) :
    RelPreserving (graphOf f) CertOk₁ CertOk₂ := by
  intro r As C α β hR hok
  subst hR
  exact hpres r As C α hok

/-- **`RelFixesContext` follows from `FixesContext`.** -/
theorem relFixesContext_graphOf {C : Context}
    (hfix : FixesContext f C) : RelFixesContext (graphOf f) C where
  args := by
    refine Forall₂.of_same (fun w hw => ?_)
    have hEq := eq_of_map_eq_self hfix.args w hw
    have hrel := relTerm_graphOf f w
    rwa [hEq] at hrel
  atts := by
    refine Forall₂.of_same (fun k hk => ?_)
    have hEq := eq_of_map_eq_self hfix.atts k hk
    have hrel := relAtt_graphOf f k
    rwa [hEq] at hrel

end Graph


/-! ### Equality reflection

`RelInj` on assurances lifts to `RelTerm` on whole terms. This is the relational
`Erase.mapAssur_eq_iff` (`lean/Lara/Erase.lean:110`), and it is what `dedupList`
and `coveredB` consume. -/

section Reflection

variable {R : Assurance → Assurance → Prop}

mutual
  /-- **`RelTerm` reflects and preserves equality.** -/
  theorem relTerm_inj (hR : RelInj R) :
      ∀ {w₁ w₂ v₁ v₂ : SupportTerm},
        RelTerm R w₁ w₂ → RelTerm R v₁ v₂ → (w₁ = v₁ ↔ w₂ = v₂)
    | _, _, _, _, .leaf _, .leaf _ => by simp [SupportTerm.leaf.injEq]
    | _, _, _, _, .leaf _, .inst _ _ _ => by simp
    | _, _, _, _, .inst _ _ _, .leaf _ => by simp
    | _, _, _, _, .inst hws hD hα, .inst hvs hE hβ => by
        simp only [SupportTerm.inst.injEq]
        constructor
        · rintro ⟨rfl, rfl, hw, hd, rfl, hα'⟩
          exact ⟨rfl, rfl, (relTerms_inj hR hws hvs).mp hw,
            (relDis_inj hR hD hE).mp hd, rfl, (hR _ _ _ _ hα hβ).mp hα'⟩
        · rintro ⟨rfl, rfl, hw, hd, rfl, hα'⟩
          exact ⟨rfl, rfl, (relTerms_inj hR hws hvs).mpr hw,
            (relDis_inj hR hD hE).mpr hd, rfl, (hR _ _ _ _ hα hβ).mpr hα'⟩
  theorem relTerms_inj (hR : RelInj R) :
      ∀ {ws₁ ws₂ vs₁ vs₂ : List SupportTerm},
        RelTerms R ws₁ ws₂ → RelTerms R vs₁ vs₂ → (ws₁ = vs₁ ↔ ws₂ = vs₂)
    | _, _, _, _, .nil, .nil => by simp
    | _, _, _, _, .nil, .cons _ _ => by simp
    | _, _, _, _, .cons _ _, .nil => by simp
    | _, _, _, _, .cons hw hws, .cons hv hvs => by
        simp only [List.cons.injEq]
        rw [relTerm_inj hR hw hv, relTerms_inj hR hws hvs]
  theorem relDis_inj (hR : RelInj R) :
      ∀ {D₁ D₂ E₁ E₂ : List (QuestionId × SupportTerm)},
        RelDis R D₁ D₂ → RelDis R E₁ E₂ → (D₁ = E₁ ↔ D₂ = E₂)
    | _, _, _, _, .nil, .nil => by simp
    | _, _, _, _, .nil, .cons _ _ => by simp
    | _, _, _, _, .cons _ _, .nil => by simp
    | _, _, _, _, .cons hw hrest, .cons hv hrest' => by
        simp only [List.cons.injEq, Prod.mk.injEq]
        rw [relTerm_inj hR hw hv, relDis_inj hR hrest hrest']
end

/-- The attack-level consequence, used by `coveredB_rel`. -/
theorem relAtt_source_inj (hR : RelInj R)
    {k₁ k₂ : Attack.Attack} {w₁ w₂ : SupportTerm}
    (hk : RelAtt R k₁ k₂) (hw : RelTerm R w₁ w₂) :
    (k₁.source = w₁ ↔ k₂.source = w₂) := by
  cases hk <;> exact relTerm_inj hR ‹RelTerm R _ _› hw

end Reflection


/-! ### Relational transport of the typing judgment

Every list lemma below inducts on the *list* and `cases` the derivation rather
than inducting on the derivation directly: `RelTerms`/`RelDis` are mutually
inductive with `RelTerm`, and Lean 4.32's `induction` tactic cannot eliminate a
mutual inductive. The case analysis is identical either way. -/

section Transport

variable {canon : String → String} {Pi : RuleId → Option Rule}
  {Gamma : LeafId → Option Atom}
  {CertOk₁ CertOk₂ : BackendId → Digest → CertRef → List Atom → Atom → Prop}
  {dp : DefeatPolicy} {R : Assurance → Assurance → Prop}

theorem relDis_length {D₁ D₂ : List (QuestionId × SupportTerm)}
    (h : RelDis R D₁ D₂) :
    D₁.length = D₂.length := by
  induction D₁ generalizing D₂ with
  | nil => cases h; rfl
  | cons p rest ih =>
      obtain ⟨_, _⟩ := p
      cases h with
      | cons _ hrest => simp only [List.length_cons, ih hrest]

/-- Discharge *keys* are fixed by the relation — `RelDis.cons` shares `q`. This
is the relational `Erase.mapAssurDis_keys` (`lean/Lara/EraseTransport.lean:57`),
and it is what carries `dNodup`, `cover`, `disj` and `keysD` across. -/
theorem relDis_keys {D₁ D₂ : List (QuestionId × SupportTerm)}
    (h : RelDis R D₁ D₂) :
    D₂.map Prod.fst = D₁.map Prod.fst := by
  induction D₁ generalizing D₂ with
  | nil => cases h; rfl
  | cons p rest ih =>
      obtain ⟨_, _⟩ := p
      cases h with
      | cons _ hrest => simp only [List.map_cons, ih hrest]

/-- Positional lookup transports right to left: the relational
`mapAssurList_getElem?_some` (`lean/Lara/EraseTransport.lean:62`). -/
theorem relTerms_getElem?_right {ws₁ ws₂ : List SupportTerm}
    (h : RelTerms R ws₁ ws₂) {i : Nat}
    {w₂ : SupportTerm} (hi : ws₂[i]? = some w₂) :
    ∃ w₁, ws₁[i]? = some w₁ ∧ RelTerm R w₁ w₂ :=
  Forall₂.getElem?_right (relTerms_iff_forall₂.mp h) hi

/-- Positional lookup transports left to right. `relTerm_subterm` navigates
*forwards* along the relation, so it needs this direction rather than
`relTerms_getElem?_right`'s. -/
theorem relTerms_getElem?_left {ws₁ ws₂ : List SupportTerm}
    (h : RelTerms R ws₁ ws₂) {i : Nat}
    {w₁ : SupportTerm} (hi : ws₁[i]? = some w₁) :
    ∃ w₂, ws₂[i]? = some w₂ ∧ RelTerm R w₁ w₂ :=
  Forall₂.getElem?_left (relTerms_iff_forall₂.mp h) hi

/-- The discharge counterpart of `relTerms_getElem?_right`. -/
theorem relDis_getElem?_right :
    ∀ {D₁ D₂ : List (QuestionId × SupportTerm)}, RelDis R D₁ D₂ → ∀ {j : Nat}
      {q : QuestionId} {w₂ : SupportTerm}, D₂[j]? = some (q, w₂) →
      ∃ w₁, D₁[j]? = some (q, w₁) ∧ RelTerm R w₁ w₂ := by
  intro D₁
  induction D₁ with
  | nil => intro D₂ h j q w₂ hj; cases h; simp at hj
  | cons p rest ih =>
      obtain ⟨_, _⟩ := p
      intro D₂ h j q w₂ hj
      cases h with
      | cons hw hrest =>
          cases j with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq,
                Prod.mk.injEq] at hj
              obtain ⟨rfl, rfl⟩ := hj
              exact ⟨_, rfl, hw⟩
          | succ n =>
              simp only [List.getElem?_cons_succ] at hj ⊢
              exact ih hrest hj

/-- Discharge *lookup* transports, keys being shared. `relTerm_subterm`'s
`ques` case is the consumer. -/
theorem relDis_lookup :
    ∀ {D₁ D₂ : List (QuestionId × SupportTerm)}, RelDis R D₁ D₂ →
      ∀ {q : QuestionId} {w₁ : SupportTerm}, lookupDis D₁ q = some w₁ →
      ∃ w₂, lookupDis D₂ q = some w₂ ∧ RelTerm R w₁ w₂ := by
  intro D₁
  induction D₁ with
  | nil => intro D₂ h q w₁ hq; cases h; simp [lookupDis] at hq
  | cons p rest ih =>
      obtain ⟨q₀, _⟩ := p
      intro D₂ h q w₁ hq
      cases h with
      | cons hw hrest =>
          simp only [lookupDis] at hq ⊢
          by_cases hqq : q₀ = q
          · rw [if_pos hqq] at hq ⊢
            simp only [Option.some.injEq] at hq
            exact ⟨_, rfl, hq ▸ hw⟩
          · rw [if_neg hqq] at hq ⊢
            exact ih hrest hq

/-- Positional navigation commutes with the relation — the relational
`Erase.mapAssur_subterm` (`lean/Lara/Erase.lean:125`). Needed by
`hasAttack_rel`'s `undercut`/`undermine` cases and by `attackClosureB_rel`.

The plan typed the position as `List Nat` (recorded under "Deviations" in
`ara/evidence/proofs/m4_relational_parametricity.md`); the repo's `Pos` is
`List PosElem` (`lean/Lara/Attack.lean:56`), which is what is used here. -/
theorem relTerm_subterm :
    ∀ (π : Pos) {w₁ w₂ t₁ : SupportTerm},
      RelTerm R w₁ w₂ → subterm w₁ π = some t₁ →
      ∃ t₂, subterm w₂ π = some t₂ ∧ RelTerm R t₁ t₂ := by
  intro π
  induction π with
  | nil =>
      intro w₁ w₂ t₁ hrel h
      simp only [subterm, Option.some.injEq] at h
      exact ⟨w₂, rfl, h ▸ hrel⟩
  | cons pe π ih =>
      intro w₁ w₂ t₁ hrel h
      cases hrel with
      | leaf l => simp [subterm] at h
      | @inst rn θ ws₁ ws₂ D₁ D₂ H a₁ a₂ hws hD ha =>
          cases pe with
          | prem i =>
              simp only [subterm] at h ⊢
              obtain ⟨w, hi, hsub⟩ :
                  ∃ w, ws₁[i]? = some w ∧ subterm w π = some t₁ := by
                cases hi : ws₁[i]? with
                | none => rw [hi] at h; simp at h
                | some w => rw [hi] at h; exact ⟨w, rfl, h⟩
              obtain ⟨w', hw', hrel'⟩ := relTerms_getElem?_left hws hi
              rw [hw']
              exact ih hrel' hsub
          | ques q =>
              simp only [subterm] at h ⊢
              obtain ⟨w, hq, hsub⟩ :
                  ∃ w, lookupDis D₁ q = some w ∧ subterm w π = some t₁ := by
                cases hq : lookupDis D₁ q with
                | none => rw [hq] at h; simp at h
                | some w => rw [hq] at h; exact ⟨w, rfl, h⟩
              obtain ⟨w', hw', hrel'⟩ := relDis_lookup hD hq
              rw [hw']
              exact ih hrel' hsub


/-- **`HasSupport` transports along a related pair.** The relational
`hasSupport_mapAssur` (`lean/Lara/EraseTransport.lean:91`). The conclusion `C`
and obligation set `O` are unchanged: the certificate payload never enters
either, which is the same fact the functional version rests on.

`RelPreserving` is consumed exactly once, at the `assur` field, and only at the
assurance pair the node actually carries. That is why the hypothesis localizes:
the induction visits precisely the assurance positions of `w₁`, so a relation
inhabited only at `F`'s occurrences discharges every obligation this proof
raises. -/
theorem hasSupport_rel (hpres : RelPreserving R CertOk₁ CertOk₂) :
    ∀ {w₁ w₂ : SupportTerm} {C : Atom} {O : List QuestionId},
      RelTerm R w₁ w₂ →
      HasSupport canon Pi Gamma CertOk₁ w₁ C O →
      HasSupport canon Pi Gamma CertOk₂ w₂ C O := by
  intro w₁ w₂ C O hrel h
  induction h generalizing w₂ with
  | leaf hΓ => cases hrel; exact .leaf hΓ
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis ihprems ihdis =>
      cases hrel with
      | @inst _ _ _ ws₂ _ D₂ _ _ α₂ hws hD hα =>
        have hside' : InstSide canon Pi CertOk₂ rn θ r ws₂ D₂ H α₂
            As Cs Os DCs DOs C :=
          { rule := hside.rule
            θNodup := hside.θNodup
            θDom := hside.θDom
            prems := hside.prems
            concl := hside.concl
            lenAs := by rw [← relTerms_length hws]; exact hside.lenAs
            lenCs := by rw [← relTerms_length hws]; exact hside.lenCs
            lenOs := by rw [← relTerms_length hws]; exact hside.lenOs
            premEq := hside.premEq
            lenDCs := by rw [← relDis_length hD]; exact hside.lenDCs
            lenDOs := by rw [← relDis_length hD]; exact hside.lenDOs
            ans := by
              intro j q w' A hj hA
              obtain ⟨w₀, hD₀, _⟩ := relDis_getElem?_right hD hj
              exact hside.ans j q w₀ A hD₀ hA
            qNodup := hside.qNodup
            dNodup := by rw [relDis_keys hD]; exact hside.dNodup
            hNodup := hside.hNodup
            cover := by intro qd hqd; rw [relDis_keys hD]; exact hside.cover qd hqd
            disj := by intro n hn; rw [relDis_keys hD] at hn; exact hside.disj n hn
            keysD := by intro n hn; rw [relDis_keys hD] at hn; exact hside.keysD n hn
            keysH := hside.keysH
            -- The only `InstSide` field whose obligation is about the discharge
            -- list being EMPTY rather than about its keys. Route through the
            -- length rather than casing on `hD`: after `cases hD` the hypothesis
            -- reads `w₁ :: rest₁ = []` and `rw [hDnil] at *` would rewrite into
            -- `hDnil` itself.
            strictNoQ := by
              intro hstrict
              obtain ⟨hDnil, hHnil⟩ := hside.strictNoQ hstrict
              refine ⟨?_, hHnil⟩
              have hlen := relDis_length hD
              rw [hDnil] at hlen
              exact List.eq_nil_of_length_eq_zero hlen.symm
            assur := hpres r As C _ _ hα hside.assur }
        refine HasSupport.inst hside' ?_ ?_
        · intro i w' A O' hi hA hO
          obtain ⟨w₀, hw₀, hrel₀⟩ := relTerms_getElem?_right hws hi
          exact ihprems i w₀ A O' hw₀ hA hO hrel₀
        · intro j q w' A O' hj hA hO
          obtain ⟨w₀, hD₀, hrel₀⟩ := relDis_getElem?_right hD hj
          exact ihdis j q w₀ A O' hD₀ hA hO hrel₀


/-- **`HasAttack` transports along a related pair.** The relational
`hasAttack_mapAssur` (`lean/Lara/EraseTransport.lean:145`); the target
occurrence tracks the same position by `relTerm_subterm`, and the source's
typing moves by `hasSupport_rel`. Every occurrence-local `Pi`/`Gamma`/pattern
premise is assurance-independent and carries across unchanged. -/
theorem hasAttack_rel (hpres : RelPreserving R CertOk₁ CertOk₂)
    {k₁ k₂ : Attack.Attack} (hk : RelAtt R k₁ k₂)
    (h : HasAttack canon Pi Gamma CertOk₁ dp k₁) :
    HasAttack canon Pi Gamma CertOk₂ dp k₂ := by
  cases h with
  | rebut hw hrule hdef hconcl hcon =>
      cases hk with
      | rebut hwr hur =>
          cases hur with
          | inst _ _ _ =>
              exact .rebut (hasSupport_rel hpres hwr hw) hrule hdef hconcl hcon
  | undercut hw hocc hrule hdef hexc hinst heq =>
      cases hk with
      | undercut hwr hur =>
          obtain ⟨t₂, hsub, hrel⟩ := relTerm_subterm _ hur hocc
          cases hrel with
          | inst _ _ _ =>
              exact .undercut (hasSupport_rel hpres hwr hw) hsub hrule hdef hexc
                hinst heq
  | undermine hw hocc hl hcon =>
      cases hk with
      | undermine hwr hur =>
          obtain ⟨t₂, hsub, hrel⟩ := relTerm_subterm _ hur hocc
          cases hrel with
          | leaf _ =>
              exact .undermine (hasSupport_rel hpres hwr hw) hsub hl hcon

end Transport


/-! ### The saturation, relationally

Every input the saturation reads is fixed by the relation: `RelTerm` preserves
the root constructor and rule identifier, so `conflictAttackableB` and
`attackFor`'s shape choice are both invariant, and conclusions never carry a
certificate. -/

/-- A cache entry pair: the term moves, the conclusion does not. -/
def RelEntry (R : Assurance → Assurance → Prop)
    (p q : SupportTerm × Atom) : Prop := RelTerm R p.1 q.1 ∧ p.2 = q.2

section Saturation

variable {R : Assurance → Assurance → Prop}

theorem conflictAttackableB_rel
    (Pi : RuleId → Option Rule) {t₁ t₂ : SupportTerm} (h : RelTerm R t₁ t₂) :
    conflictAttackableB Pi t₂ = conflictAttackableB Pi t₁ := by
  cases h <;> rfl

theorem attackFor_rel {s₁ s₂ t₁ t₂ : SupportTerm}
    (hs : RelTerm R s₁ s₂) (ht : RelTerm R t₁ t₂) :
    RelAtt R (attackFor s₁ t₁) (attackFor s₂ t₂) := by
  cases ht with
  | leaf l => exact .undermine hs (.leaf l)
  | inst hws hD hα => exact .rebut hs (.inst hws hD hα)

/-- The inner `filterMap` of `crossAttsFrom`, one source at a time. The two
guards agree because `RelEntry` fixes the conclusion and `conflictAttackableB`
cannot see the relation; the emitted attacks are related by `attackFor_rel`. -/
theorem crossAttsFrom_inner_rel
    (canon : String → String) (dp : DefeatPolicy) (Pi : RuleId → Option Rule)
    {s₁ s₂ : SupportTerm × Atom} (hs : RelEntry R s₁ s₂) :
    ∀ {tgts₁ tgts₂ : List (SupportTerm × Atom)},
      Forall₂ (RelEntry R) tgts₁ tgts₂ →
      Forall₂ (RelAtt R)
        (tgts₁.filterMap fun t =>
          if contraryMatchB canon dp s₁.2 t.2 && conflictAttackableB Pi t.1 then
            some (attackFor s₁.1 t.1) else none)
        (tgts₂.filterMap fun t =>
          if contraryMatchB canon dp s₂.2 t.2 && conflictAttackableB Pi t.1 then
            some (attackFor s₂.1 t.1) else none) := by
  intro tgts₁ tgts₂ h
  induction h with
  | nil => exact .nil
  | @cons t₁ t₂ _ _ ht _ ih =>
      have hguard :
          (contraryMatchB canon dp s₂.2 t₂.2 && conflictAttackableB Pi t₂.1)
            = (contraryMatchB canon dp s₁.2 t₁.2 && conflictAttackableB Pi t₁.1) := by
        rw [hs.2, ht.2, conflictAttackableB_rel Pi ht.1]
      rcases Bool.eq_false_or_eq_true
          (contraryMatchB canon dp s₁.2 t₁.2 && conflictAttackableB Pi t₁.1)
        with hcond | hcond
      · rw [List.filterMap_cons_some (b := attackFor s₁.fst t₁.fst)
            (by simp [hcond]),
          List.filterMap_cons_some (b := attackFor s₂.fst t₂.fst)
            (by simp [hguard, hcond])]
        exact .cons (attackFor_rel hs.1 ht.1) ih
      · rw [List.filterMap_cons_none (by simp [hcond]),
          List.filterMap_cons_none (by simp [hguard, hcond])]
        exact ih

theorem crossAttsFrom_rel
    (canon : String → String) (dp : DefeatPolicy) (Pi : RuleId → Option Rule) :
    ∀ {srcs₁ srcs₂ tgts₁ tgts₂ : List (SupportTerm × Atom)},
      Forall₂ (RelEntry R) srcs₁ srcs₂ →
      Forall₂ (RelEntry R) tgts₁ tgts₂ →
      Forall₂ (RelAtt R)
        (crossAttsFrom canon dp Pi srcs₁ tgts₁)
        (crossAttsFrom canon dp Pi srcs₂ tgts₂) := by
  intro srcs₁ srcs₂ tgts₁ tgts₂ hsrcs htgts
  induction hsrcs with
  | nil => exact .nil
  | cons hs _ ih =>
      simp only [crossAttsFrom, List.flatMap_cons]
      exact Forall₂.append (crossAttsFrom_inner_rel canon dp Pi hs htgts) ih

end Saturation

section Cache

variable {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
  {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
  {R : Assurance → Assurance → Prop}

theorem conclusionCache_rel
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂)) :
    ∀ {args₁ args₂ : List SupportTerm},
      RelTerms R args₁ args₂ →
      (∀ w ∈ args₁, ∃ C, HasSupport canon Pi Gamma (certOkOf reg₁) w C []) →
      Forall₂ (RelEntry R)
        (conclusionCache Pi Gamma reg₁ args₁)
        (conclusionCache Pi Gamma reg₂ args₂) := by
  intro args₁
  induction args₁ with
  | nil => intro args₂ h _; cases h; exact .nil
  | cons w ws ih =>
      intro args₂ h hsup
      cases h with
      | cons hw hws =>
          obtain ⟨Cw, hCw⟩ := hsup w List.mem_cons_self
          have h₁ : conclusionOf Pi Gamma reg₁ w = some Cw :=
            conclusionOf_eq_some_iff.mpr hCw
          have h₂ : conclusionOf Pi Gamma reg₂ _ = some Cw :=
            conclusionOf_eq_some_iff.mpr (hasSupport_rel hpres hw hCw)
          have IH := ih hws (fun v hv => hsup v (List.mem_cons_of_mem _ hv))
          simp only [conclusionCache, List.filterMap_cons, h₁, h₂,
            Option.map_some]
          exact .cons ⟨hw, rfl⟩ IH

theorem crossAtts_rel {C : Context} {F₁ F₂ : Fragment}
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hF : RelFrag R F₁ F₂) (hfix : RelFixesContext R C)
    (hCsup : ∀ w ∈ C.frame.args, ∃ A,
      HasSupport canon F₁.policy.ruleLookup (linkGamma C F₁) (certOkOf reg₁) w A [])
    (hFsup : ∀ w ∈ F₁.args, ∃ A,
      HasSupport canon F₁.policy.ruleLookup (linkGamma C F₁) (certOkOf reg₁) w A []) :
    Forall₂ (RelAtt R)
      (crossAtts reg₁ (linkGamma C F₁) C F₁)
      (crossAtts reg₂ (linkGamma C F₁) C F₂) := by
  have hcc := conclusionCache_rel (canon := canon) (Pi := F₁.policy.ruleLookup)
    (Gamma := linkGamma C F₁) hpres (relTerms_iff_forall₂.mpr hfix.args) hCsup
  have hcf := conclusionCache_rel (canon := canon) (Pi := F₁.policy.ruleLookup)
    (Gamma := linkGamma C F₁) hpres (relTerms_iff_forall₂.mpr hF.args) hFsup
  simp only [crossAtts, hF.policy]
  exact Forall₂.append
    (crossAttsFrom_rel canon F₁.policy.defeat F₁.policy.ruleLookup hcc hcf)
    (crossAttsFrom_rel canon F₁.policy.defeat F₁.policy.ruleLookup hcf hcc)

end Cache


/-! ### The structural merge, relationally

`dedupList` decides membership, so this is the first consumer of `RelInj`:
without equality reflection the two sides could dedupe to lists of different
lengths, and the compiled frameworks would not even have the same node count.

The four `link*_rel` lemmas below are `rfl` in the functional development,
because `mapAssurFrag f F` shares its interface fields with `F` *definitionally*.
Relationally they are honest rewrites through `RelFrag`'s six equality fields. -/

section Linked

variable {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
  {R : Assurance → Assurance → Prop} {C : Context} {F₁ F₂ : Fragment}

theorem dedupList_rel (hR : RelInj R) :
    ∀ {l₁ l₂ : List SupportTerm},
      Forall₂ (RelTerm R) l₁ l₂ →
      Forall₂ (RelTerm R) (dedupList l₁) (dedupList l₂) := by
  intro l₁ l₂ h
  induction h with
  | nil => exact .nil
  | @cons w₁ w₂ ws₁ ws₂ hw _ ih =>
      simp only [dedupList]
      by_cases hmem : w₁ ∈ dedupList ws₁
      · have hmem₂ : w₂ ∈ dedupList ws₂ := by
          obtain ⟨v₂, hv₂, hrel⟩ := Forall₂.mem_left ih hmem
          rw [(relTerm_inj hR hw hrel).mp rfl]
          exact hv₂
        rw [if_pos hmem, if_pos hmem₂]
        exact ih
      · have hmem₂ : w₂ ∉ dedupList ws₂ := by
          intro hc
          obtain ⟨v₁, hv₁, hrel⟩ := Forall₂.mem_right ih hc
          exact hmem (by rw [(relTerm_inj hR hw hrel).mpr rfl]; exact hv₁)
        rw [if_neg hmem, if_neg hmem₂]
        exact .cons hw ih

theorem linkFault_rel (hF : RelFrag R F₁ F₂) :
    linkFault C F₂ = linkFault C F₁ := by
  simp only [linkFault, idHygieneFault, sigmaPolicyFault, Fragment.declared,
    hF.gammaFrag, hF.imports, hF.sigma, hF.policy]

theorem linkOk_rel (hF : RelFrag R F₁ F₂) : linkOk C F₂ = linkOk C F₁ := by
  simp only [linkOk, linkFault_rel hF]

theorem linkGamma_rel (hF : RelFrag R F₁ F₂) :
    linkGamma C F₂ = linkGamma C F₁ := by
  simp only [linkGamma, hF.gammaFrag]

theorem linkGround_rel (hF : RelFrag R F₁ F₂) :
    linkGround C F₂ = linkGround C F₁ := by
  simp only [linkGround, hF.ground]

/-- **The linked units are related.** The relational `link_relabel_commutes`
(`lean/Lara/Context/Equivalence.lean:319`). -/
theorem link_rel_commutes (hR : RelInj R)
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hF : RelFrag R F₁ F₂) (hfix : RelFixesContext R C)
    (hCsup : ∀ w ∈ C.frame.args, ∃ A,
      HasSupport canon F₁.policy.ruleLookup (linkGamma C F₁) (certOkOf reg₁) w A [])
    (hFsup : ∀ w ∈ F₁.args, ∃ A,
      HasSupport canon F₁.policy.ruleLookup (linkGamma C F₁) (certOkOf reg₁) w A []) :
    Forall₂ (RelTerm R)
        (linkedUnit reg₁ C F₁).args (linkedUnit reg₂ C F₂).args ∧
      Forall₂ (RelAtt R)
        (linkedUnit reg₁ C F₁).atts (linkedUnit reg₂ C F₂).atts := by
  refine ⟨?_, ?_⟩
  · show Forall₂ (RelTerm R) (dedupList (C.frame.args ++ F₁.args))
      (dedupList (C.frame.args ++ F₂.args))
    exact dedupList_rel hR (Forall₂.append hfix.args hF.args)
  · show Forall₂ (RelAtt R)
      (C.frame.atts ++ F₁.atts ++ crossAtts reg₁ (linkGamma C F₁) C F₁)
      (C.frame.atts ++ F₂.atts ++ crossAtts reg₂ (linkGamma C F₂) C F₂)
    rw [linkGamma_rel hF]
    exact Forall₂.append (Forall₂.append hfix.atts hF.atts)
      (crossAtts_rel hpres hF hfix hCsup hFsup)

end Linked


/-! ### Acceptance, relationally -/

section Acceptance

variable {R : Assurance → Assurance → Prop} {sg : Sigma.Sigma} {P : Policy.Policy}

mutual
  /-- The signature stage cannot see a certificate relation: `termWellSorted`
  inspects rule identifier, substitution, premises and discharges only. -/
  theorem termWellSorted_rel :
      ∀ {w₁ w₂ : SupportTerm}, RelTerm R w₁ w₂ →
        termWellSorted sg P w₂ = termWellSorted sg P w₁
    | _, _, .leaf _ => rfl
    | _, _, .inst hws hD _ => by
        simp only [termWellSorted, termsWellSorted_rel hws,
          dischargesWellSorted_rel hD]
  theorem termsWellSorted_rel :
      ∀ {ws₁ ws₂ : List SupportTerm}, RelTerms R ws₁ ws₂ →
        termsWellSorted sg P ws₂ = termsWellSorted sg P ws₁
    | _, _, .nil => rfl
    | _, _, .cons hw hws => by
        simp only [termsWellSorted, termWellSorted_rel hw, termsWellSorted_rel hws]
  theorem dischargesWellSorted_rel :
      ∀ {D₁ D₂ : List (QuestionId × SupportTerm)}, RelDis R D₁ D₂ →
        dischargesWellSorted sg P D₂ = dischargesWellSorted sg P D₁
    | _, _, .nil => rfl
    | _, _, .cons hw hrest => by
        simp only [dischargesWellSorted, termWellSorted_rel hw,
          dischargesWellSorted_rel hrest]
end

theorem argsWellSorted_rel {args₁ args₂ : List SupportTerm}
    (h : RelTerms R args₁ args₂) :
    argsWellSorted sg P args₂ = argsWellSorted sg P args₁ := by
  simp only [argsWellSorted, termsWellSorted_rel h]

/-- The signature stage of a related unit. The relational `signatureStage_map`
(`lean/Lara/Context/Equivalence.lean:234`). -/
theorem signatureStage_rel {ground : List Atom}
    {unit₁ unit₂ : Lara.Unit}
    (hsigma : unit₂.sigma = unit₁.sigma) (hpolicy : unit₂.policy = unit₁.policy)
    (hargs : RelTerms R unit₁.args unit₂.args) :
    Check.Unit.signatureStage ground unit₂
      = Check.Unit.signatureStage ground unit₁ := by
  simp only [Check.Unit.signatureStage, hsigma, hpolicy, argsWellSorted_rel hargs]

/-- An attack's source and target move with it. -/
theorem relAtt_source {k₁ k₂ : Attack.Attack}
    (hk : RelAtt R k₁ k₂) : RelTerm R k₁.source k₂.source := by
  cases hk <;> assumption

theorem relAtt_target {k₁ k₂ : Attack.Attack}
    (hk : RelAtt R k₁ k₂) : RelTerm R k₁.target k₂.target := by
  cases hk <;> assumption

/-- **The attacked occurrence transports, and its image is exhibited.** The
relational `attackOcc_mapAssurAtt` (`lean/Lara/Context/Equivalence.lean:248`).

The functional version can *compute* the image occurrence (`mapAssur f t`);
relationally the occurrence has to be produced, so this is stated
existentially. `attackOcc_rel` below recovers the pointwise shape the plan asked
for, at
the cost of `RelInj` — which is what pins the produced occurrence down to the
one the caller already has in hand. -/
theorem attackOcc_rel_exists
    {k₁ k₂ : Attack.Attack} {t₁ : SupportTerm} (hk : RelAtt R k₁ k₂)
    (h : AttackOcc k₁ t₁) : ∃ t₂, AttackOcc k₂ t₂ ∧ RelTerm R t₁ t₂ := by
  cases hk with
  | rebut _ hu =>
      simp only [AttackOcc] at h
      subst h
      exact ⟨_, rfl, hu⟩
  | undercut _ hu =>
      simp only [AttackOcc] at h ⊢
      obtain ⟨t₂, hsub, hrel⟩ := relTerm_subterm _ hu h
      exact ⟨t₂, hsub, hrel⟩
  | undermine _ hu =>
      simp only [AttackOcc] at h ⊢
      obtain ⟨t₂, hsub, hrel⟩ := relTerm_subterm _ hu h
      exact ⟨t₂, hsub, hrel⟩

/-- The pointwise form the plan specifies. `RelInj` is what the relational setting
costs here: the functional `attackOcc_mapAssurAtt` gets uniqueness of the image
occurrence for free, because the image is a computed function value.

**No call site, deliberately.** Every consumer in this module goes through
`attackOcc_rel_exists`, which produces the occurrence rather than requiring the
caller to have it. This form is kept because it is the statement
`docs/theory-m4-relational-parametricity.md` §2's mirror table names against
`attackOcc_mapAssurAtt`, and dropping it would leave that row unbacked. -/
theorem attackOcc_rel (hR : RelInj R)
    {k₁ k₂ : Attack.Attack} {t₁ t₂ : SupportTerm} (hk : RelAtt R k₁ k₂)
    (ht : RelTerm R t₁ t₂) (h : AttackOcc k₁ t₁) : AttackOcc k₂ t₂ := by
  obtain ⟨t₂', hocc, hrel⟩ := attackOcc_rel_exists hk h
  rwa [(relTerm_inj hR ht hrel).mp rfl]

/-- The relational `contains_mapAssur` (`lean/Lara/Context/Equivalence.lean:262`).
`RelInj` enters for the same reason as in `attackOcc_rel`. -/
theorem contains_rel (hR : RelInj R)
    {v₁ v₂ t₁ t₂ : SupportTerm}
    (hv : RelTerm R v₁ v₂) (ht : RelTerm R t₁ t₂) (h : Contains v₁ t₁) :
    Contains v₂ t₂ := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨t₂', hsub, hrel⟩ := relTerm_subterm π hv hπ
  exact ⟨π, by rwa [(relTerm_inj hR ht hrel).mp rfl]⟩

/-- **Declared coverage survives the relation.** The relational
`covered_mapAssur` (`lean/Lara/Context/Equivalence.lean:268`). -/
theorem covered_rel
    {atts₁ atts₂ : List Attack.Attack} {s₁ s₂ t₁ t₂ : SupportTerm}
    (hR : RelInj R)
    (hatts : Forall₂ (RelAtt R) atts₁ atts₂)
    (hs : RelTerm R s₁ s₂) (ht : RelTerm R t₁ t₂)
    (h : Covered atts₁ s₁ t₁) : Covered atts₂ s₂ t₂ := by
  obtain ⟨k₁, hk₁, hsrc, o₁, hocc, hcont⟩ := h
  obtain ⟨k₂, hk₂, hrelk⟩ := Forall₂.mem_left hatts hk₁
  obtain ⟨o₂, hocc₂, hrelo⟩ := attackOcc_rel_exists hrelk hocc
  exact ⟨k₂, hk₂, (relAtt_source_inj hR hrelk hs).mp hsrc, o₂, hocc₂,
    contains_rel hR ht hrelo hcont⟩

/-- `ConflictAttackable` is certificate-blind, so it transports backwards along
the relation exactly as `conflictAttackable_mapAssur` does. -/
theorem conflictAttackable_rel
    {Pi : RuleId → Option Rule} {t₁ t₂ : SupportTerm} (h : RelTerm R t₁ t₂)
    (hca : ConflictAttackable Pi t₂) : ConflictAttackable Pi t₁ := by
  rw [← conflictAttackableB_iff] at hca ⊢
  rw [← conflictAttackableB_rel Pi h]
  exact hca

end Acceptance

section AcceptedUnit

variable {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
  {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
  {dp : DefeatPolicy} {R : Assurance → Assurance → Prop}

theorem attackComplete_rel
    {args₁ args₂ : List SupportTerm} {atts₁ atts₂ : List Attack.Attack}
    (hR : RelInj R)
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hargs : Forall₂ (RelTerm R) args₁ args₂)
    (hatts : Forall₂ (RelAtt R) atts₁ atts₂)
    (hcomplete : ∀ w ∈ args₁, ∃ A, HasSupport canon Pi Gamma (certOkOf reg₁) w A [])
    (h : AttackComplete canon Pi Gamma (certOkOf reg₁) dp args₁ atts₁) :
    AttackComplete canon Pi Gamma (certOkOf reg₂) dp args₂ atts₂ := by
  intro source₂ hs₂ target₂ ht₂ Cs Ct hsSup htSup hcm hca
  obtain ⟨source₁, hs₁, hrels⟩ := Forall₂.mem_right hargs hs₂
  obtain ⟨target₁, ht₁, hrelt⟩ := Forall₂.mem_right hargs ht₂
  obtain ⟨Cs₀, hCs₀⟩ := hcomplete source₁ hs₁
  obtain ⟨Ct₀, hCt₀⟩ := hcomplete target₁ ht₁
  have hCsEq : Cs₀ = Cs :=
    (hasSupport_unique (hasSupport_rel hpres hrels hCs₀) hsSup).1
  have hCtEq : Ct₀ = Ct :=
    (hasSupport_unique (hasSupport_rel hpres hrelt hCt₀) htSup).1
  exact covered_rel hR hatts hrels hrelt
    (h source₁ hs₁ target₁ ht₁ Cs₀ Ct₀ hCs₀ hCt₀
      (by rw [hCsEq, hCtEq]; exact hcm) (conflictAttackable_rel hrelt hca))

/-- Distinctness survives the relation — `RelInj`'s second consumer, the
`Nodup` premise of `Check.Unit.checkUnit_complete`. -/
theorem nodup_rel (hR : RelInj R) :
    ∀ {l₁ l₂ : List SupportTerm}, Forall₂ (RelTerm R) l₁ l₂ →
      l₁.Nodup → l₂.Nodup := by
  intro l₁ l₂ h
  induction h with
  | nil => intro _; exact List.nodup_nil
  | @cons w₁ w₂ ws₁ ws₂ hw hws ih =>
      intro hnd
      rw [List.nodup_cons] at hnd ⊢
      refine ⟨?_, ih hnd.2⟩
      intro hc
      obtain ⟨v₁, hv₁, hrel⟩ := Forall₂.mem_right hws hc
      exact hnd.1 (by rw [(relTerm_inj hR hw hrel).mpr rfl]; exact hv₁)

/-- **Acceptance transports along a partial-bijective, acceptance-preserving
certificate relation.** The relational `checkUnit_map`
(`lean/Lara/Context/Equivalence.lean:401`). -/
theorem checkUnit_rel {ground : List Atom}
    {unit₁ unit₂ : Lara.Unit}
    {accepted₁ : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg₁)}
    (hR : RelInj R)
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hsigma : unit₂.sigma = unit₁.sigma) (hpolicy : unit₂.policy = unit₁.policy)
    (hargs : Forall₂ (RelTerm R) unit₁.args unit₂.args)
    (hatts : Forall₂ (RelAtt R) unit₁.atts unit₂.atts)
    (h₁ : Check.Unit.checkUnit Gamma reg₁ ground unit₁ = .ok accepted₁) :
    ∃ accepted₂, Check.Unit.checkUnit Gamma reg₂ ground unit₂ = .ok accepted₂ := by
  have hsound := Check.Unit.checkUnit_sound h₁
  have hpolEq := hsound.policy_eq
  have hruleIds := hsound.ruleIds_nodup
  have hpolWf := hsound.policy_wf
  have hargsEq := hsound.args_eq
  have hattsEq := hsound.atts_eq
  have hattackComplete := hsound.attack_complete
  have hscope : Policy.firstOutOfScope? unit₂.policy = none := by
    rw [hpolicy, ← hpolEq]; exact accepted₁.scopes_wf
  refine Check.Unit.checkUnit_complete
    (signatureStage_rel hsigma hpolicy (relTerms_iff_forall₂.mpr hargs) ▸
      signatureStage_of_ok h₁)
    hscope (by rw [hpolicy, ← hpolEq]; exact hruleIds)
    (by rw [hpolicy, ← hpolEq]; exact hpolWf)
    (nodup_rel hR hargs (hargsEq ▸ accepted₁.program.nodup))
    ?_ ?_ ?_ ?_ ?_
  · intro w₂ hw₂
    obtain ⟨w₁, hw₁, hrel⟩ := Forall₂.mem_right hargs hw₂
    obtain ⟨A, hA⟩ := accepted₁.program.complete w₁ (by rw [hargsEq]; exact hw₁)
    rw [hpolicy, ← hpolEq]
    exact ⟨A, hasSupport_rel hpres hrel hA⟩
  · intro k₂ hk₂
    obtain ⟨k₁, hk₁, hrel⟩ := Forall₂.mem_right hatts hk₂
    rw [hpolicy, ← hpolEq]
    exact hasAttack_rel hpres hrel
      (accepted₁.program.typed k₁ (by rw [hattsEq]; exact hk₁))
  · intro k₂ hk₂
    obtain ⟨k₁, hk₁, hrel⟩ := Forall₂.mem_right hatts hk₂
    obtain ⟨v₂, hv₂, hvrel⟩ := Forall₂.mem_left hargs
      (hargsEq ▸ accepted₁.program.source_declared k₁ (by rw [hattsEq]; exact hk₁))
    rw [(relTerm_inj hR (relAtt_source hrel) hvrel).mp rfl]
    exact hv₂
  · intro k₂ hk₂
    obtain ⟨k₁, hk₁, hrel⟩ := Forall₂.mem_right hatts hk₂
    obtain ⟨v₂, hv₂, hvrel⟩ := Forall₂.mem_left hargs
      (hargsEq ▸ accepted₁.program.target_declared k₁ (by rw [hattsEq]; exact hk₁))
    rw [(relTerm_inj hR (relAtt_target hrel) hvrel).mp rfl]
    exact hv₂
  · rw [hpolicy, ← hpolEq]
    exact attackComplete_rel hR hpres hargs hatts
      (hargsEq ▸ accepted₁.program.complete)
      (by rw [← hargsEq, ← hattsEq]; exact accepted₁.attack_complete)

end AcceptedUnit


/-! ### The carrier

`compileUnit_rel` concludes an **equation** between `StructuredAF`s, not a
pointwise agreement. That is what makes the grounded fixpoint — and every other
`ExtensionSemantics` — indifferent to the relation: `Grounded.statusC` and
`Semantics.observe` are applied to one and the same framework on both branches.
No fixpoint lemma is needed here, and none is used.

`coveredB_relabel` (`lean/Lara/Erase.lean:198`) does not stand alone. Its
dependency chain is three lemmas deep, and all three need relational mirrors:

```
coveredB_relabel        Erase.lean:198
  ├── mapAssurAtt_source                         ← relAtt_source
  ├── attackClosureB_mapAssur   Erase.lean:179   ← attackClosureB_rel
  │     ├── mapAssur_subterm                     ← relTerm_subterm
  │     └── containsB_mapAssur  Erase.lean:150   ← containsB_rel     ┐ MUTUAL
  │           └── containsBDis_mapAssur   :170   ← containsBDis_rel  ┘
  └── mapAssur_eq_iff                            ← relTerm_inj
```

`containsB`/`containsBList`/`containsBDis` are the **`Bool`-valued deciders**
and are a separate mutual definition from the `Prop`-valued `Contains` that
the `Prop`-valued `contains_rel` above mirrors. `coveredB` goes through the `Bool` side, so
both are needed. -/

section Carrier

variable {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
  {Gamma : LeafId → Option Atom} {R : Assurance → Assurance → Prop}

/-- Positional lookup off the end transports. -/
theorem relTerms_getElem?_none {ws₁ ws₂ : List SupportTerm}
    (h : RelTerms R ws₁ ws₂) {i : Nat}
    (hi : ws₁[i]? = none) : ws₂[i]? = none :=
  Forall₂.getElem?_none (relTerms_iff_forall₂.mp h) hi

/-- A discharge key absent on one side is absent on the other — `RelDis.cons`
shares the key. -/
theorem relDis_lookup_none :
    ∀ {D₁ D₂ : List (QuestionId × SupportTerm)}, RelDis R D₁ D₂ →
      ∀ {q : QuestionId}, lookupDis D₁ q = none → lookupDis D₂ q = none := by
  intro D₁
  induction D₁ with
  | nil => intro D₂ h q _; cases h; rfl
  | cons p rest ih =>
      obtain ⟨q₀, _⟩ := p
      intro D₂ h q hq
      cases h with
      | cons _ hrest =>
          simp only [lookupDis] at hq ⊢
          by_cases hqq : q₀ = q
          · rw [if_pos hqq] at hq; exact absurd hq (by simp)
          · rw [if_neg hqq] at hq ⊢
            exact ih hrest hq

/-- Navigation off the end transports. The companion of `relTerm_subterm`; the
`Bool`-valued `attackClosureB_rel` needs both branches. -/
theorem relTerm_subterm_none :
    ∀ (π : Pos) {w₁ w₂ : SupportTerm},
      RelTerm R w₁ w₂ → subterm w₁ π = none → subterm w₂ π = none := by
  intro π
  induction π with
  | nil => intro w₁ w₂ _ h; simp only [subterm, reduceCtorEq] at h
  | cons pe π ih =>
      intro w₁ w₂ hrel h
      cases hrel with
      | leaf l => rfl
      | @inst rn θ ws₁ ws₂ D₁ D₂ H a₁ a₂ hws hD _ =>
          cases pe with
          | prem i =>
              simp only [subterm] at h ⊢
              cases hi : ws₁[i]? with
              | none => rw [relTerms_getElem?_none hws hi]
              | some w =>
                  rw [hi] at h
                  obtain ⟨w', hw', hrel'⟩ := relTerms_getElem?_left hws hi
                  rw [hw']
                  exact ih hrel' h
          | ques q =>
              simp only [subterm] at h ⊢
              cases hq : lookupDis D₁ q with
              | none => rw [relDis_lookup_none hD hq]
              | some w =>
                  rw [hq] at h
                  obtain ⟨w', hw', hrel'⟩ := relDis_lookup hD hq
                  rw [hw']
                  exact ih hrel' h

mutual
  /-- The relational `Erase.containsB_mapAssur` (`lean/Lara/Erase.lean:150`). -/
  theorem containsB_rel (hR : RelInj R) :
      ∀ {w₁ w₂ t₁ t₂ : SupportTerm},
        RelTerm R w₁ w₂ → RelTerm R t₁ t₂ → containsB w₂ t₂ = containsB w₁ t₁
    | _, _, _, _, .leaf l, ht =>
        decide_eq_decide.mpr (relTerm_inj hR (RelTerm.leaf l) ht).symm
    | _, _, _, _, .inst hws hD hα, ht => by
        simp only [containsB]
        rw [decide_eq_decide.mpr
              (relTerm_inj hR (RelTerm.inst hws hD hα) ht).symm,
          containsBList_rel hR hws ht, containsBDis_rel hR hD ht]
  /-- The list arm of the `containsB` mutual block. -/
  theorem containsBList_rel (hR : RelInj R) :
      ∀ {ws₁ ws₂ : List SupportTerm} {t₁ t₂ : SupportTerm},
        RelTerms R ws₁ ws₂ → RelTerm R t₁ t₂ →
        containsBList ws₂ t₂ = containsBList ws₁ t₁
    | _, _, _, _, .nil, _ => rfl
    | _, _, _, _, .cons hw hws, ht => by
        simp only [containsBList]
        rw [containsB_rel hR hw ht, containsBList_rel hR hws ht]
  /-- The relational `Erase.containsBDis_mapAssur` (`lean/Lara/Erase.lean:170`). -/
  theorem containsBDis_rel (hR : RelInj R) :
      ∀ {D₁ D₂ : List (QuestionId × SupportTerm)} {t₁ t₂ : SupportTerm},
        RelDis R D₁ D₂ → RelTerm R t₁ t₂ →
        containsBDis D₂ t₂ = containsBDis D₁ t₁
    | _, _, _, _, .nil, _ => rfl
    | _, _, _, _, .cons hw hrest, ht => by
        simp only [containsBDis]
        rw [containsB_rel hR hw ht, containsBDis_rel hR hrest ht]
end

/-- The relational `Erase.attackClosureB_mapAssur` (`lean/Lara/Erase.lean:179`).
-/
theorem attackClosureB_rel (hR : RelInj R)
    {k₁ k₂ : Attack.Attack} {t₁ t₂ : SupportTerm}
    (hk : RelAtt R k₁ k₂) (ht : RelTerm R t₁ t₂) :
    attackClosureB k₂ t₂ = attackClosureB k₁ t₁ := by
  cases hk with
  | rebut _ hu => exact containsB_rel hR ht hu
  | @undercut _ _ u₁ u₂ π _ hu =>
      simp only [attackClosureB]
      cases hsub : subterm u₁ π with
      | none => rw [relTerm_subterm_none π hu hsub]
      | some s₁ =>
          obtain ⟨s₂, hs₂, hrel⟩ := relTerm_subterm π hu hsub
          rw [hs₂]
          exact containsB_rel hR ht hrel
  | @undermine _ _ u₁ u₂ π _ hu =>
      simp only [attackClosureB]
      cases hsub : subterm u₁ π with
      | none => rw [relTerm_subterm_none π hu hsub]
      | some s₁ =>
          obtain ⟨s₂, hs₂, hrel⟩ := relTerm_subterm π hu hsub
          rw [hs₂]
          exact containsB_rel hR ht hrel

/-- **The coverage decider is blind to a partial-bijective relation.** The
relational `Erase.coveredB_relabel` (`lean/Lara/Erase.lean:198`).
`relInj_necessary` is exactly this statement with `hR` deleted and the
conclusion negated — if this proof ever appears to go through without `hR`,
one of the two is wrong. -/
theorem coveredB_rel (hR : RelInj R)
    {atts₁ atts₂ : List Attack.Attack} {s₁ s₂ t₁ t₂ : SupportTerm}
    (hatts : Forall₂ (RelAtt R) atts₁ atts₂)
    (hs : RelTerm R s₁ s₂) (ht : RelTerm R t₁ t₂) :
    coveredB atts₂ s₂ t₂ = coveredB atts₁ s₁ t₁ := by
  simp only [coveredB]
  induction hatts with
  | nil => rfl
  | @cons k₁ k₂ _ _ hk _ ih =>
      simp only [List.any_cons, ih]
      rw [decide_eq_decide.mpr (relAtt_source_inj hR hk hs).symm,
        attackClosureB_rel hR hk ht]

theorem nodes_conclusion_rel
    {acc₁ : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg₁)}
    {acc₂ : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg₂)}
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hpol : acc₂.policy.ruleLookup = acc₁.policy.ruleLookup)
    (hargs : Forall₂ (RelTerm R) acc₁.program.args acc₂.program.args) :
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
      have hargs₂ : acc₂.program.args[i]? = none :=
        Forall₂.getElem?_none hargs ht₁.symm
      rw [hargs₂] at ht₂
      cases h₂ : acc₂.nodes[i]? with
      | none => rfl
      | some n₂ => rw [h₂] at ht₂; exact absurd ht₂ (by simp)
  | some n₁ =>
      rw [h₁] at ht₁
      obtain ⟨v₂, hv₂, hrel⟩ := Forall₂.getElem?_left hargs ht₁.symm
      rw [hv₂] at ht₂
      cases h₂ : acc₂.nodes[i]? with
      | none => rw [h₂] at ht₂; exact absurd ht₂ (by simp)
      | some n₂ =>
          rw [h₂] at ht₂
          have hterm : n₂.term = v₂ := Option.some.inj ht₂
          have hva : HasSupport canon acc₂.policy.ruleLookup Gamma
              (certOkOf reg₂) v₂ n₁.conclusion [] := by
            rw [hpol]; exact hasSupport_rel hpres hrel n₁.valid
          have hvb : HasSupport canon acc₂.policy.ruleLookup Gamma
              (certOkOf reg₂) v₂ n₂.conclusion [] := hterm ▸ n₂.valid
          simp only [Option.map_some]
          exact congrArg some (hasSupport_unique hvb hva).1

/-- **The two accepted units present the same carrier.** The relational
`compileUnit_map` (`lean/Lara/Context/Equivalence.lean:511`). This is where the
relation is erased: from here down both branches run one and the same
framework. -/
theorem compileUnit_rel
    {acc₁ : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg₁)}
    {acc₂ : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg₂)}
    (hR : RelInj R)
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hpol : acc₂.policy = acc₁.policy)
    (hargs : Forall₂ (RelTerm R) acc₁.program.args acc₂.program.args)
    (hatts : Forall₂ (RelAtt R) acc₁.program.atts acc₂.program.atts) :
    Invariants.compileUnit acc₂ = Invariants.compileUnit acc₁ := by
  have hedge : ∀ i j,
      Compile.edgeB acc₂.program i j = Compile.edgeB acc₁.program i j := by
    intro i j
    simp only [Compile.edgeB]
    cases hs : acc₁.program.args[i]? with
    | none => rw [Forall₂.getElem?_none hargs hs]
    | some source₁ =>
        obtain ⟨source₂, hs₂, hrels⟩ := Forall₂.getElem?_left hargs hs
        rw [hs₂]
        cases ht : acc₁.program.args[j]? with
        | none => rw [Forall₂.getElem?_none hargs ht]
        | some target₁ =>
            obtain ⟨target₂, ht₂, hrelt⟩ := Forall₂.getElem?_left hargs ht
            rw [ht₂]
            exact coveredB_rel hR hatts hrels hrelt
  simp only [Invariants.compileUnit,
    nodes_conclusion_rel hpres (by rw [hpol]) hargs]
  exact congrArg _ (funext fun i => funext fun j => hedge i j)

end Carrier


/-! ### The headline

Proved once over an arbitrary projection `g`, exactly as `obsGen_congr`
(`lean/Lara/Context/Equivalence.lean:795`) is, so that the semantics-parametric
form is an instantiation rather than a second proof.

One bookkeeping difference from the functional development is worth naming.
`linkGamma C (mapAssurFrag f F)` is *definitionally* `linkGamma C F`, so the
functional statements can name one Γ throughout. Relationally
`linkGamma C F₂ = linkGamma C F₁` is a propositional equality
(`linkGamma_rel`), and the accepted unit's type mentions Γ — so the two lemmas
below rewrite Γ and the ground list into `F₁`'s form before doing any work. -/

section Headline

variable {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
  {R : Assurance → Assurance → Prop} {f : Assurance → Assurance} {C : Context}
  {F₁ F₂ F : Fragment}

theorem exists_accepted_rel (hR : RelInj R)
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F₁) (hF : RelFrag R F₁ F₂)
    (hfix : RelFixesContext R C)
    {acc₁ : Lara.Unit.CheckedUnit canon (linkGamma C F₁) (certOkOf reg₁)}
    (h₁ : Check.Unit.checkUnit (linkGamma C F₁) reg₁ (linkGround C F₁)
      (linkedUnit reg₁ C F₁) = .ok acc₁) :
    ∃ acc₂, Check.Unit.checkUnit (linkGamma C F₂) reg₂ (linkGround C F₂)
      (linkedUnit reg₂ C F₂) = .ok acc₂ := by
  rw [linkGamma_rel hF, linkGround_rel hF]
  obtain ⟨hargs, hatts⟩ :=
    link_rel_commutes hR hpres hF hfix hadm.ctx.support hadm.frag.support
  exact checkUnit_rel (Gamma := linkGamma C F₁) (ground := linkGround C F₁)
    (unit₁ := linkedUnit reg₁ C F₁) (unit₂ := linkedUnit reg₂ C F₂)
    hR hpres hF.sigma hF.policy hargs hatts h₁

/-- **The two links present the same carrier.** The relational
`compileUnit_link_relabel` (`lean/Lara/Context/Equivalence.lean:723`). -/
theorem compileUnit_link_rel (hR : RelInj R)
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F₁) (hF : RelFrag R F₁ F₂)
    (hfix : RelFixesContext R C)
    {acc₁ : Lara.Unit.CheckedUnit canon (linkGamma C F₁) (certOkOf reg₁)}
    {acc₂ : Lara.Unit.CheckedUnit canon (linkGamma C F₂) (certOkOf reg₂)}
    (h₁ : Check.Unit.checkUnit (linkGamma C F₁) reg₁ (linkGround C F₁)
      (linkedUnit reg₁ C F₁) = .ok acc₁)
    (h₂ : Check.Unit.checkUnit (linkGamma C F₂) reg₂ (linkGround C F₂)
      (linkedUnit reg₂ C F₂) = .ok acc₂) :
    Invariants.compileUnit acc₂ = Invariants.compileUnit acc₁ := by
  obtain ⟨hargs, hatts⟩ :=
    link_rel_commutes hR hpres hF hfix hadm.ctx.support hadm.frag.support
  revert acc₂
  rw [linkGamma_rel hF, linkGround_rel hF]
  intro acc₂ h₂
  have hsound₁ := Check.Unit.checkUnit_sound h₁
  have hsound₂ := Check.Unit.checkUnit_sound h₂
  exact compileUnit_rel hR hpres
    (by rw [hsound₁.policy_eq, hsound₂.policy_eq]; exact hF.policy)
    (by rw [hsound₂.args_eq, hsound₁.args_eq]; exact hargs)
    (by rw [hsound₂.atts_eq, hsound₁.atts_eq]; exact hatts)

/-- **Relational parametricity over related backends, for every projection at
once.**

Two fragments related by a partial-bijective, acceptance-preserving relation `R`
on certificates are indistinguishable in every admissible context that `R` fixes
— whatever is read off the resulting carrier. This is `obsGen_congr`
(`lean/Lara/Context/Equivalence.lean:795`) with the *function* `f` replaced by a
*relation*, which is the quantifier M4's acceptance criterion names.

**Read the strength honestly.** `RelInj` makes `R` a partial injection;
`relInj_necessary` shows it cannot be dropped. What the relational form buys is
not arbitrary relations but a **localized acceptance hypothesis**:
`RelPreserving R` obliges only the pairs `R` relates, where `AssurPreserving f`
obliges every assurance in the type — the gap
`registry_swap_congruence`'s docstring records.
`backend_replacement_parametricity_local` instantiates that localized obligation;
it does not by itself witness failure of all globally preserving realizations.

**Not full abstraction.** `RelTerm` lifts a relation on certificates
structurally; it is not a logical relation over the contrary-visible occurrence
profile, and Part B stays descoped
(`docs/theory-m4-contextual-adequacy.md` §7). -/
theorem obsGen_parametricity {α : Type} (g : Invariants.StructuredAF → Atom → α)
    (hR : RelInj R)
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F₁) (hF : RelFrag R F₁ F₂)
    (hfix : RelFixesContext R C) :
    obsGen g reg₁ C F₁ = obsGen g reg₂ C F₂ := by
  obtain ⟨acc₁, h₁⟩ := exists_accepted_of_admissible hadm
  obtain ⟨acc₂, h₂⟩ := exists_accepted_rel hR hpres hadm hF hfix h₁
  rw [obsGen_eq_of_ok g hadm.guard h₁,
    obsGen_eq_of_ok g (C := C) (F := F₂)
      (by rw [linkOk_rel hF]; exact hadm.guard) h₂]
  refine congrArg ObservationOf.observed ?_
  rw [hF.exports]
  exact congrArg (fun G => F₁.exports.map (fun p => g G p))
    (compileUnit_link_rel hR hpres hadm hF hfix h₁ h₂).symm

/-- **Relational parametricity at an arbitrary extension semantics.** -/
theorem backend_replacement_parametricity_sem (sem : ExtensionSemantics)
    (hR : RelInj R)
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F₁) (hF : RelFrag R F₁ F₂)
    (hfix : RelFixesContext R C) :
    obsSem sem reg₁ C F₁ = obsSem sem reg₂ C F₂ :=
  obsGen_parametricity _ hR hpres hadm hF hfix

/-- **Relational parametricity at the grounded reading.** The `obs`-level
statement, matching `backend_replacement_congruence`'s conclusion shape.

`obs` *is* `obsGen (Invariants.status canon)` — `Observation` abbreviates
`ObservationOf Grounded.Status`, and `obs_eq_obsGen` records the collapse by
`rfl` — so this is an instantiation, exactly as `backend_replacement_congruence`
is an instantiation of `obsGen_congr`. Before the unification of the two observation
types the same statement needed its own copy of the three-line argument against
`obs_eq_of_ok`, because no equation between the two types was well-formed. -/
theorem backend_replacement_parametricity (hR : RelInj R)
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F₁) (hF : RelFrag R F₁ F₂)
    (hfix : RelFixesContext R C) :
    obs reg₁ C F₁ = obs reg₂ C F₂ :=
  obsGen_parametricity _ hR hpres hadm hF hfix

/-- **The functional congruence is the graph instance.** This is what makes the
relational development an upgrade rather than a parallel one: nothing in
`Lara.Context.Equivalence` is now stated more generally than what is proved
here. `backend_replacement_congruence` itself is retained, not replaced — it is
cited by the paper under its own name and its hypotheses read more simply. -/
theorem backend_replacement_congruence_of_parametricity
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F) (hfix : FixesContext f C) :
    obs reg₁ C F = obs reg₂ C (mapAssurFrag f F) :=
  backend_replacement_parametricity (relInj_graphOf hf)
    (relPreserving_graphOf hpres) hadm (relFrag_graphOf f F)
    (relFixesContext_graphOf hfix)

/-- **The relational corollary restates the functional theorem exactly.**

Both sides are proofs of the same `Prop`, so `rfl` holds by proof irrelevance —
what this checks is that the two *statements* coincide, because the equation is
ill-typed otherwise. That is exactly the claim being guarded.

Do not delete this as trivial. Without it, a later change to `RelFrag`,
`graphOf`, or any of the bridge lemmas could leave
`backend_replacement_congruence_of_parametricity` restating something weaker
than `backend_replacement_congruence`, with `lake build`, `check-axioms.sh` and
`check-axcheck-coverage.py` all still green. -/
theorem congruence_correspondence
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F) (hfix : FixesContext f C) :
    backend_replacement_congruence hf hpres hadm hfix
      = backend_replacement_congruence_of_parametricity hf hpres hadm hfix := rfl

end Headline


/-! ### The occurrence relation

The identity relation restricted to the assurances a fragment actually carries.
It is the witness that `RelPreserving` localizes: instantiated at `occRel F`,
the acceptance obligation ranges over `F`'s certificate occurrences and nothing
else, where `AssurPreserving f` ranges over the whole type.

The acceptance scope is the distinction. The finite structural realization is
proved by `relFrag_exists_injective_fixesContext` in `Context/FiniteExtension.lean`:
it realizes the fragment and fixes the context using one total injection.
It does not extend every pair of an arbitrary infinite `R`, and does not
establish global `AssurPreserving`. `backend_replacement_parametricity_local`
instantiates the localized obligation; it is not itself a counterexample to
existence of a globally acceptance-preserving realization. -/

mutual
  /-- Every assurance a support term carries. -/
  def occurs : SupportTerm → List Assurance
    | .leaf _ => []
    | .inst _ _ ws D _ α => α :: (occursList ws ++ occursDis D)
  def occursList : List SupportTerm → List Assurance
    | [] => []
    | w :: ws => occurs w ++ occursList ws
  def occursDis : List (QuestionId × SupportTerm) → List Assurance
    | [] => []
    | (_, w) :: rest => occurs w ++ occursDis rest
end

def occursAtt : Attack.Attack → List Assurance
  | .rebut w u => occurs w ++ occurs u
  | .undercut w u _ => occurs w ++ occurs u
  | .undermine w u _ => occurs w ++ occurs u

/-- Every assurance the fragment declares, in args and in attacks. -/
def occurrences (F : Fragment) : List Assurance :=
  occursList F.args ++ (F.atts.map occursAtt).flatten

/-- A term's occurrences are among its list's occurrences. -/
theorem mem_occursList {w : SupportTerm} {ws : List SupportTerm}
    (hw : w ∈ ws) {α : Assurance} (hα : α ∈ occurs w) :
    α ∈ occursList ws := by
  induction ws with
  | nil => simp at hw
  | cons v vs ih =>
      rcases List.mem_cons.mp hw with rfl | hw'
      · simp only [occursList, List.mem_append]; exact .inl hα
      · simp only [occursList, List.mem_append]; exact .inr (ih hw')

/-- An attack's occurrences are among its list's flattened occurrences. -/
theorem mem_occursAtts {k : Attack.Attack} {atts : List Attack.Attack}
    (hk : k ∈ atts) {α : Assurance} (hα : α ∈ occursAtt k) :
    α ∈ (atts.map occursAtt).flatten :=
  List.mem_flatten.mpr ⟨occursAtt k, List.mem_map.mpr ⟨k, hk, rfl⟩, hα⟩

section SelfRelated

variable {R : Assurance → Assurance → Prop}

mutual
  /-- A term is related to itself by any relation reflexive on its occurrences. -/
  theorem relTerm_self :
      ∀ {w : SupportTerm}, (∀ α ∈ occurs w, R α α) → RelTerm R w w
    | .leaf l, _ => .leaf l
    | .inst _ _ ws D _ α, h =>
        .inst
          (relTerms_self (fun β hβ =>
            h β (by simp only [occurs, List.mem_cons, List.mem_append]; exact .inr (.inl hβ))))
          (relDis_self (fun β hβ =>
            h β (by simp only [occurs, List.mem_cons, List.mem_append]; exact .inr (.inr hβ))))
          (h α (by simp only [occurs]; exact List.mem_cons_self))
  theorem relTerms_self :
      ∀ {ws : List SupportTerm}, (∀ α ∈ occursList ws, R α α) → RelTerms R ws ws
    | [], _ => .nil
    | _ :: _, h =>
        .cons
          (relTerm_self (fun β hβ =>
            h β (by simp only [occursList, List.mem_append]; exact .inl hβ)))
          (relTerms_self (fun β hβ =>
            h β (by simp only [occursList, List.mem_append]; exact .inr hβ)))
  theorem relDis_self :
      ∀ {D : List (QuestionId × SupportTerm)},
        (∀ α ∈ occursDis D, R α α) → RelDis R D D
    | [], _ => .nil
    | (_, _) :: _, h =>
        .cons
          (relTerm_self (fun β hβ =>
            h β (by simp only [occursDis, List.mem_append]; exact .inl hβ)))
          (relDis_self (fun β hβ =>
            h β (by simp only [occursDis, List.mem_append]; exact .inr hβ)))
end

theorem relAtt_self :
    ∀ {k : Attack.Attack}, (∀ α ∈ occursAtt k, R α α) → RelAtt R k k
  | .rebut _ _, h =>
      .rebut
        (relTerm_self (fun β hβ =>
          h β (by simp only [occursAtt, List.mem_append]; exact .inl hβ)))
        (relTerm_self (fun β hβ =>
          h β (by simp only [occursAtt, List.mem_append]; exact .inr hβ)))
  | .undercut _ _ _, h =>
      .undercut
        (relTerm_self (fun β hβ =>
          h β (by simp only [occursAtt, List.mem_append]; exact .inl hβ)))
        (relTerm_self (fun β hβ =>
          h β (by simp only [occursAtt, List.mem_append]; exact .inr hβ)))
  | .undermine _ _ _, h =>
      .undermine
        (relTerm_self (fun β hβ =>
          h β (by simp only [occursAtt, List.mem_append]; exact .inl hβ)))
        (relTerm_self (fun β hβ =>
          h β (by simp only [occursAtt, List.mem_append]; exact .inr hβ)))

end SelfRelated

/-- **The identity, restricted to `F`'s occurrences.** -/
def occRel (F : Fragment) : Assurance → Assurance → Prop :=
  fun α β => α = β ∧ α ∈ occurrences F

/-- Trivially a partial injection: it is a restriction of equality. -/
theorem relInj_occRel (F : Fragment) : RelInj (occRel F) := by
  rintro α₁ α₂ β₁ β₂ ⟨rfl, _⟩ ⟨rfl, _⟩
  exact Iff.rfl

/-- A fragment is `occRel`-related to itself. -/
theorem relFrag_occRel (F : Fragment) : RelFrag (occRel F) F F where
  sigma := rfl
  policy := rfl
  gammaFrag := rfl
  ground := rfl
  imports := rfl
  exports := rfl
  args := Forall₂.of_same (fun w hw => relTerm_self (fun α hα =>
    ⟨rfl, by
      simp only [occurrences, List.mem_append]
      exact .inl (mem_occursList hw hα)⟩))
  atts := Forall₂.of_same (fun k hk => relAtt_self (fun α hα =>
    ⟨rfl, by
      simp only [occurrences, List.mem_append]
      exact .inr (mem_occursAtts hk hα)⟩))

section OccurrenceLocal

variable {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
  {C : Context} {F : Fragment}

/-- The context is fixed, provided its own material is inside `F`'s occurrence
set — which is exactly the situation `FixesContext` describes. -/
theorem relFixesContext_occRel
    (hC : ∀ α ∈ occursList C.frame.args, α ∈ occurrences F)
    (hA : ∀ α ∈ (C.frame.atts.map occursAtt).flatten, α ∈ occurrences F) :
    RelFixesContext (occRel F) C where
  args := Forall₂.of_same (fun _ hw => relTerm_self (fun α hα =>
    ⟨rfl, hC α (mem_occursList hw hα)⟩))
  atts := Forall₂.of_same (fun _ hk => relAtt_self (fun α hα =>
    ⟨rfl, hA α (mem_occursAtts hk hα)⟩))

/-- **Representation independence under an acceptance hypothesis that ranges
only over the fragment's own certificate occurrences.**

Compare `backend_replacement_congruence`, whose `AssurPreserving f` obliges
every rule and every assurance *in the type*. This obliges only the assurances
`F` carries. That gap is what the docstrings of `registry_swap_congruence`
(`Context/Equivalence.lean:890`) and `registry_swap_congruence_sem`
(`Context/Observation.lean:345`) record as the hypothesis they do not carry, and
it is the reason the relational form is more than a restatement.

**This is a trade, not a strict strengthening.** `hlocal` is weaker than
`registry_swap_congruence`'s global `hpres`, but `hC` and `hA` are new: they
require the *context's* own occurrences to lie inside `occurrences F`. Neither
theorem implies the other, and a display of this one must say "localizes the
acceptance hypothesis at the cost of two context-containment side conditions".
The side conditions are inherited rather than incidental — `RelFixesContext`
plus `RelInj` force `R` to be the identity on the context's occurrences, so an
assurance shared between `C` and `F` cannot move whatever the relation is. -/
theorem backend_replacement_parametricity_local
    (hlocal : ∀ (r : Rule) (As : List Atom) (Cc : Atom) (α : Assurance),
      α ∈ occurrences F →
      AssuranceOk (certOkOf reg₁) r As Cc α → AssuranceOk (certOkOf reg₂) r As Cc α)
    (hadm : Admissible reg₁ C F)
    (hC : ∀ α ∈ occursList C.frame.args, α ∈ occurrences F)
    (hA : ∀ α ∈ (C.frame.atts.map occursAtt).flatten, α ∈ occurrences F) :
    obs reg₁ C F = obs reg₂ C F :=
  backend_replacement_parametricity (relInj_occRel F)
    (by rintro r As Cc α β ⟨rfl, hmem⟩ hok; exact hlocal r As Cc α hmem hok)
    hadm (relFrag_occRel F) (relFixesContext_occRel hC hA)


/-- **The occurrence-local congruence at an arbitrary extension semantics
The companion of `backend_replacement_parametricity_local` for
`obsSem`, and the localized counterpart of `registry_swap_congruence_sem`
(`lean/Lara/Context/Observation.lean:345`), whose own docstring records that its
acceptance hypothesis is stated globally rather than over the fragment's
occurrences. As at the grounded reading, this is a trade and not a strict
strengthening: `hC`/`hA` are new obligations that
`registry_swap_congruence_sem` does not carry, so neither theorem implies the
other.

**Why there is no separate `registry_swap_parametricity`.** The plan
proposed one, stated as: the same hypotheses as this, concluding
`obs reg₁ C F = obs reg₂ C F`. That is *character for character* the statement
of `backend_replacement_parametricity_local` — `registry_swap_congruence`
differs from `backend_replacement_congruence` only by moving no material, and
the occurrence-local form already moves no material. Shipping both would be two
names for one theorem, so only one is shipped: at the grounded reading it is
`backend_replacement_parametricity_local`, and at an arbitrary semantics it is
this. -/
theorem backend_replacement_parametricity_local_sem (sem : ExtensionSemantics)
    (hlocal : ∀ (r : Rule) (As : List Atom) (Cc : Atom) (α : Assurance),
      α ∈ occurrences F →
      AssuranceOk (certOkOf reg₁) r As Cc α → AssuranceOk (certOkOf reg₂) r As Cc α)
    (hadm : Admissible reg₁ C F)
    (hC : ∀ α ∈ occursList C.frame.args, α ∈ occurrences F)
    (hA : ∀ α ∈ (C.frame.atts.map occursAtt).flatten, α ∈ occurrences F) :
    obsSem sem reg₁ C F = obsSem sem reg₂ C F :=
  backend_replacement_parametricity_sem sem (relInj_occRel F)
    (by rintro r As Cc α β ⟨rfl, hmem⟩ hok; exact hlocal r As Cc α hmem hok)
    hadm (relFrag_occRel F) (relFixesContext_occRel hC hA)

end OccurrenceLocal

/-! ### Composition and whole programs

The composed form factors through `obsGen_parametricity`. Its admissibility
can be assembled unchanged with `admissible_composed`, including both directed
cross-coverage obligations. The checked-program form instead factors through
`checkedAF_rel`: checked programs need no contextual admissibility or
acceptance-preservation hypothesis. The closed-link occurrence instance below
records the context/fragment union that the contextual route actually needs. -/

/-- A partial-bijective relation fixing both contexts fixes their composite.
Argument deduplication uses the same relational merge lemma as linking. -/
theorem relFixesContext_composed {R : Assurance → Assurance → Prop}
    {C D : Context} (hR : RelInj R)
    (hC : RelFixesContext R C) (hD : RelFixesContext R D) :
    RelFixesContext R (composedContext C D) where
  args := dedupList_rel hR (Forall₂.append hC.args hD.args)
  atts := Forall₂.append hC.atts hD.atts

/-- Relational congruence under composition, for any carrier projection.
Use `admissible_composed` to discharge `hadm` from the two sides. -/
theorem obsGen_parametricity_composed {α : Type}
    (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
    {R : Assurance → Assurance → Prop} {C D : Context} {F₁ F₂ : Fragment}
    (hR : RelInj R)
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ (composedContext C D) F₁) (hF : RelFrag R F₁ F₂)
    (hC : RelFixesContext R C) (hD : RelFixesContext R D) :
    obsGen g reg₁ (composedContext C D) F₁ = obsGen g reg₂ (composedContext C D) F₂ :=
  obsGen_parametricity g hR hpres hadm hF (relFixesContext_composed hR hC hD)

/-- The composed relational companion at an arbitrary extension semantics. -/
theorem backend_replacement_parametricity_composed_sem (sem : ExtensionSemantics)
    {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
    {R : Assurance → Assurance → Prop} {C D : Context} {F₁ F₂ : Fragment}
    (hR : RelInj R)
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ (composedContext C D) F₁) (hF : RelFrag R F₁ F₂)
    (hC : RelFixesContext R C) (hD : RelFixesContext R D) :
    obsSem sem reg₁ (composedContext C D) F₁ = obsSem sem reg₂ (composedContext C D) F₂ :=
  obsGen_parametricity_composed _ hR hpres hadm hF hC hD

/-- The composed relational companion at the frozen grounded reading. -/
theorem backend_replacement_parametricity_composed
    {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
    {R : Assurance → Assurance → Prop} {C D : Context} {F₁ F₂ : Fragment}
    (hR : RelInj R)
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ (composedContext C D) F₁) (hF : RelFrag R F₁ F₂)
    (hC : RelFixesContext R C) (hD : RelFixesContext R D) :
    obs reg₁ (composedContext C D) F₁ = obs reg₂ (composedContext C D) F₂ :=
  obsGen_parametricity_composed _ hR hpres hadm hF hC hD

section CheckedRel
variable {canon : String → String} {Pi : RuleId → Option Rule}
  {Gamma : LeafId → Option Atom}
  {CertOk₁ CertOk₂ : BackendId → Digest → CertRef → List Atom → Atom → Prop}
  {dp : DefeatPolicy} {R : Assurance → Assurance → Prop}
  {P₁ : CheckedProgram canon Pi Gamma CertOk₁ dp}
  {P₂ : CheckedProgram canon Pi Gamma CertOk₂ dp}

/-- Relationally related checked programs have identical edge deciders.
Checking is already witnessed on both sides; no acceptance transport is needed. -/
theorem edgeB_rel (hR : RelInj R)
    (hargs : Forall₂ (RelTerm R) P₁.args P₂.args)
    (hatts : Forall₂ (RelAtt R) P₁.atts P₂.atts) :
    ∀ i j, edgeB P₁ i j = edgeB P₂ i j := by
  intro i j
  simp only [edgeB]
  cases hs : P₁.args[i]? with
  | none => rw [Forall₂.getElem?_none hargs hs]
  | some source₁ =>
      obtain ⟨source₂, hs₂, hrels⟩ := Forall₂.getElem?_left hargs hs
      rw [hs₂]
      cases ht : P₁.args[j]? with
      | none => rw [Forall₂.getElem?_none hargs ht]
      | some target₁ =>
          obtain ⟨target₂, ht₂, hrelt⟩ := Forall₂.getElem?_left hargs ht
          rw [ht₂]
          exact (coveredB_rel hR hatts hrels hrelt).symm

/-- The relational companion of `Erase.checkedAF_relabel`. -/
theorem checkedAF_rel (hR : RelInj R)
    (hargs : Forall₂ (RelTerm R) P₁.args P₂.args)
    (hatts : Forall₂ (RelAtt R) P₁.atts P₂.atts) :
    checkedAF P₁ = checkedAF P₂ := by
  simp only [checkedAF, toAF]
  congr 1
  · rw [Forall₂.length_eq hargs]
  · funext i j; exact edgeB_rel hR hargs hatts i j

/-- The whole checked-program relational companion, for any semantics.
Unlike a contextual corollary, this preserves the existing API's absence of
`Admissible` and `RelPreserving` premises. -/
theorem whole_program_parametricity_sem (sem : ExtensionSemantics)
    (hR : RelInj R)
    (hargs : Forall₂ (RelTerm R) P₁.args P₂.args)
    (hatts : Forall₂ (RelAtt R) P₁.atts P₂.atts)
    (c : Grounded.Claim) :
    Semantics.observe sem (checkedAF P₁) c = Semantics.observe sem (checkedAF P₂) c := by
  rw [checkedAF_rel hR hargs hatts]

/-- The whole checked-program relational companion at the grounded reading. -/
theorem whole_program_parametricity (hR : RelInj R)
    (hargs : Forall₂ (RelTerm R) P₁.args P₂.args)
    (hatts : Forall₂ (RelAtt R) P₁.atts P₂.atts)
    (c : Grounded.Claim) :
    Grounded.statusC (checkedAF P₁) c = Grounded.statusC (checkedAF P₂) c := by
  rw [checkedAF_rel hR hargs hatts]
end CheckedRel

/-- List occurrence membership exposes the term that carries the assurance. -/
theorem mem_occursList_iff {a : Assurance} {ws : List SupportTerm} :
    a ∈ occursList ws ↔ ∃ w ∈ ws, a ∈ occurs w := by
  induction ws with
  | nil => simp [occursList]
  | cons w ws ih => simp [occursList, ih]

/-- Fragment occurrences come from a declared argument or attack. -/
theorem mem_occurrences_iff {a : Assurance} {F : Fragment} :
    a ∈ occurrences F ↔
      (∃ w ∈ F.args, a ∈ occurs w) ∨ (∃ k ∈ F.atts, a ∈ occursAtt k) := by
  simp only [occurrences, List.mem_append, mem_occursList_iff]
  apply or_congr Iff.rfl
  constructor
  · intro h
    obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp h
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hxs
    exact ⟨k, hk, ha⟩
  · rintro ⟨k, hk, ha⟩
    exact mem_occursAtts hk ha

/-- Context composition takes the union of occurrences, despite deduplicating
arguments. This is a membership statement, not list equality. -/
theorem occurrences_composed {a : Assurance} {C D : Context} :
    a ∈ occurrences (composedContext C D).frame ↔
      a ∈ occurrences C.frame ∨ a ∈ occurrences D.frame := by
  simp only [mem_occurrences_iff, composed_args, composed_atts]
  constructor
  · rintro (⟨w, hw | hw, ha⟩ | ⟨k, hk | hk, ha⟩)
    · exact .inl (.inl ⟨w, hw, ha⟩)
    · exact .inr (.inl ⟨w, hw, ha⟩)
    · exact .inl (.inr ⟨k, hk, ha⟩)
    · exact .inr (.inr ⟨k, hk, ha⟩)
  · rintro ((⟨w, hw, ha⟩ | ⟨k, hk, ha⟩) | (⟨w, hw, ha⟩ | ⟨k, hk, ha⟩))
    · exact .inl ⟨w, .inl hw, ha⟩
    · exact .inr ⟨k, .inl hk, ha⟩
    · exact .inl ⟨w, .inr hw, ha⟩
    · exact .inr ⟨k, .inr hk, ha⟩

/-- Occurrences declared on both sides of a closed link. Concatenation represents
set union by membership; repeated occurrences are intentionally retained. -/
def closedOccurrences (C : Context) (F : Fragment) : List Assurance :=
  occurrences C.frame ++ occurrences F

/-- Closing a link requires both sides' occurrences, not fragment containment. -/
theorem mem_closedOccurrences {C : Context} {F : Fragment} {α : Assurance} :
    α ∈ closedOccurrences C F ↔ α ∈ occurrences C.frame ∨ α ∈ occurrences F :=
  List.mem_append

/-- The identity restricted to the closed link's occurrence union. -/
def closedOccRel (C : Context) (F : Fragment) : Assurance → Assurance → Prop :=
  fun α β => α = β ∧ α ∈ closedOccurrences C F

theorem relInj_closedOccRel (C : Context) (F : Fragment) :
    RelInj (closedOccRel C F) := by
  rintro α₁ α₂ β₁ β₂ ⟨rfl, _⟩ ⟨rfl, _⟩
  exact Iff.rfl

/-- The fragment is self-related without context-containment assumptions. -/
theorem relFrag_closedOccRel (C : Context) (F : Fragment) :
    RelFrag (closedOccRel C F) F F where
  sigma := rfl
  policy := rfl
  gammaFrag := rfl
  ground := rfl
  imports := rfl
  exports := rfl
  args := Forall₂.of_same (fun _ hw => relTerm_self (fun _ hα =>
    ⟨rfl, mem_closedOccurrences.mpr (.inr (List.mem_append.mpr
      (.inl (mem_occursList hw hα))))⟩))
  atts := Forall₂.of_same (fun _ hk => relAtt_self (fun _ hα =>
    ⟨rfl, mem_closedOccurrences.mpr (.inr (List.mem_append.mpr
      (.inr (mem_occursAtts hk hα))))⟩))

/-- The context's own occurrences are included by construction. -/
theorem relFixesContext_closedOccRel (C : Context) (F : Fragment) :
    RelFixesContext (closedOccRel C F) C where
  args := Forall₂.of_same (fun _ hw => relTerm_self (fun _ hα =>
    ⟨rfl, mem_closedOccurrences.mpr (.inl (List.mem_append.mpr
      (.inl (mem_occursList hw hα))))⟩))
  atts := Forall₂.of_same (fun _ hk => relAtt_self (fun _ hα =>
    ⟨rfl, mem_closedOccurrences.mpr (.inl (List.mem_append.mpr
      (.inr (mem_occursAtts hk hα))))⟩))

/-- The closed-link occurrence-local theorem, through the generic choke point.
Acceptance is required on the union of both sides; unlike the fragment-only
local theorem this adds no context-containment premises. -/
theorem obsGen_parametricity_closed_local {α : Type}
    (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
    {C : Context} {F : Fragment}
    (hlocal : ∀ (r : Rule) (As : List Atom) (Cc : Atom) (a : Assurance),
      a ∈ closedOccurrences C F →
      AssuranceOk (certOkOf reg₁) r As Cc a → AssuranceOk (certOkOf reg₂) r As Cc a)
    (hadm : Admissible reg₁ C F) :
    obsGen g reg₁ C F = obsGen g reg₂ C F :=
  obsGen_parametricity g (relInj_closedOccRel C F)
    (by rintro r As Cc a b ⟨rfl, hmem⟩ hok; exact hlocal r As Cc a hmem hok)
    hadm (relFrag_closedOccRel C F) (relFixesContext_closedOccRel C F)

/-- Closed-link occurrence locality at any extension semantics. -/
theorem whole_program_parametricity_local_sem (sem : ExtensionSemantics)
    {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
    {C : Context} {F : Fragment}
    (hlocal : ∀ (r : Rule) (As : List Atom) (Cc : Atom) (a : Assurance),
      a ∈ closedOccurrences C F →
      AssuranceOk (certOkOf reg₁) r As Cc a → AssuranceOk (certOkOf reg₂) r As Cc a)
    (hadm : Admissible reg₁ C F) :
    obsSem sem reg₁ C F = obsSem sem reg₂ C F :=
  obsGen_parametricity_closed_local _ hlocal hadm

/-- Closed-link occurrence locality at the grounded reading. -/
theorem whole_program_parametricity_local
    {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
    {C : Context} {F : Fragment}
    (hlocal : ∀ (r : Rule) (As : List Atom) (Cc : Atom) (a : Assurance),
      a ∈ closedOccurrences C F →
      AssuranceOk (certOkOf reg₁) r As Cc a → AssuranceOk (certOkOf reg₂) r As Cc a)
    (hadm : Admissible reg₁ C F) :
    obs reg₁ C F = obs reg₂ C F :=
  obsGen_parametricity_closed_local _ hlocal hadm

end Lara.Context
