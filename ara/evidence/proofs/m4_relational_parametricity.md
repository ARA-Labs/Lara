# Evidence — M4 relational parametricity over related backends (#215)

Branch `theory/m4-relational-parametricity`, from `3ebdbf0` to the branch head.
`b4998e0` folded `origin/main` in (picking up #274/#216, which moved
`Context/Equivalence.lean` and `Context/Observation.lean`); the commits after it
are the response to PR #278's first review round. Every gate outcome and line
count below was re-run at the branch head, not at an intermediate commit.

Lean-only; no corpus regeneration, no freeze-tag bump.

## Gate outcomes

```
Build completed successfully (158 jobs).
```

```
AxCheck coverage passed (90 declarations).
```
(over `Lara/Context/Parametricity.lean` + `Lara/ListRel.lean`)

```
AxCheck coverage passed (2619 declarations).
```
(over all 108 modules under `lean/Lara/`)

```
Axiom audit passed.
```

`scripts/test-check-axioms.sh` exit 0; `scripts/test_check_axcheck_coverage.py` exit 0.

Build-closure check (the #259 failure mode) — `comm -23` of source modules against
built `.olean`s reports only the three pre-existing driver/main modules
(`Lara/AdmissionDriver`, `Lara/AdmissionDriverMain`,
`Lara/UpdatePreconditionParityMain`); both new modules are inside the closure.

No `sorry` in either new module. No `native_decide` — it would introduce
`Lean.ofReduceBool` and fail the audit, which accepts only `propext`,
`Classical.choice`, `Quot.sound`.

## Size

`lean/Lara/Context/Parametricity.lean` 1740 lines;
`lean/Lara/ListRel.lean` 125 lines.

## The headline, verbatim

```lean
theorem obsGen_parametricity {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
    {R : Assurance → Assurance → Prop} {C : Context} {F₁ F₂ : Fragment}
    (hR : RelInj R)
    (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F₁) (hF : RelFrag R F₁ F₂)
    (hfix : RelFixesContext R C) :
    obsGen g reg₁ C F₁ = obsGen g reg₂ C F₂
```

## The exactness guard

`Context.congruence_correspondence` typechecks **by `rfl`**:

```lean
theorem congruence_correspondence ... :
    backend_replacement_congruence hf hpres hadm hfix
      = backend_replacement_congruence_of_parametricity hf hpres hadm hfix := rfl
```

Both sides are proofs of the same `Prop`, so `rfl` holds by proof irrelevance;
what it checks is that the two *statements* coincide, because the equation is
ill-typed otherwise. That is the mechanized guard that the relational development
is an upgrade rather than a fork.

## The necessity witness

`Context.relInj_necessary` is `coveredB_rel` with `hR` deleted and the conclusion
negated:

```lean
theorem relInj_necessary :
    ∃ (R : Assurance → Assurance → Prop) (atts₁ atts₂ : List Attack.Attack)
      (s₁ s₂ t₁ t₂ : SupportTerm),
      Forall₂ (RelAtt R) atts₁ atts₂ ∧ RelTerm R s₁ s₂ ∧ RelTerm R t₁ t₂ ∧
        coveredB atts₂ s₂ t₂ ≠ coveredB atts₁ s₁ t₁
```

Discharged by explicit derivations for the three relational conjuncts and
`decide` for the disequality.

## The answer to #215's own sizing question

#215 asked whether the grounded fixpoint argument needs the equality.
**It does not.** `compileUnit_rel` concludes an equation between `StructuredAF`s,
so both branches run one and the same framework and the relation is erased before
any semantics runs. No grounded-labelling lemma, no `AttackExtensional`
hypothesis, and no new fixpoint machinery appears anywhere in the development.

## Toolchain fact established this milestone

`List.Forall₂` and every `List.forall₂_*` lemma are **Mathlib** names, absent from
`leanprover/lean4:v4.32.0`. `lean/Lara/ListRel.lean` authors the family and nine
lemmas locally; the repo has no Mathlib dependency.

## Deviations from the plan, and why

1. `attackOcc_rel` and `contains_rel` carry `RelInj R`, which the plan's
   statements omitted. The functional originals may *compute* the image
   occurrence as `mapAssur f t`, so its uniqueness is free; a relation supplies
   no such image, so the occurrence has to be produced and then pinned by
   `relTerm_inj`. Every call site already carries `RelInj`.
2. `relTerm_subterm`'s position is `Pos` (= `List PosElem`), not the plan's
   `List Nat`.
3. `relTerms_iff_forall₂` moved its binders into the signature, and every
   `RelTerms`/`RelDis` lemma recurses on the *list* rather than the derivation:
   Lean 4.32's `induction` tactic cannot eliminate a mutual inductive.
4. Task 11c's proposed `registry_swap_parametricity` is character-for-character
   `backend_replacement_parametricity_local`. Per the plan's own instruction not
   to ship two names for one statement, only one ships; the genuinely new
   theorem 11c contributes is `backend_replacement_parametricity_local_sem`.
5. `Lara/ListRel.lean` gained `Forall₂.getElem?_left` and `Forall₂.getElem?_none`
   beyond the plan's seven: the carrier lemmas navigate *forwards* along the
   relation, which the right-to-left `getElem?_right` does not serve.
