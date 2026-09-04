# PW-T9 Exact Structural-Path Composition — Implementation Plan

> **STATUS (2026-09-03): PR 1 (foundation) IS EXECUTED AND LANDED. PR 2 (triangle) REMAINS.**
> Landed: original Tasks 1-5 and 9, plus T1, T2, T6, T7, T12, T15, T16, T17, T19.
> Remaining: T3, T4, T5, T8, T11, T13, T14, T18, T20 and original Task 10 (freeze record).

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Mechanize T9 (issue #190, tracker #189): checked-support transport along a chosen typed path of exact structural bridges, with direct-versus-composed agreement only under an explicit commuting triangle, and mid-path translation gaps surfacing as incomparability.

**Architecture:** One new theory module `lean/Lara/PW/Compose.lean` (Kleisli composition of the partial translation, bridge composition, typed paths, coherence and commuting-triangle theorems) plus one new example module `lean/Lara/Examples/PWCompose.lean` (a live two-leg renaming path, two "no triangle ⇒ no agreement" witnesses, a mid-path incomparability witness). Both modules only import — no local definition and no T6 module is touched, continuing PW0/T6's wrapper discipline.

**Tech Stack:** Lean 4 (core only, no Mathlib), `lake build`, the AxCheck axiom gate.

---

## Background and motivation

**Where T9 sits.** The possible-world wrapper (tracker #189) gives Lara worlds, bridges between checking environments, and an outer modal language. T6 (#191, landed as `Lara/PW/Translation.lean` + `Lara/PW/Structural.lean`) proved the single-edge result: under the three-clause `StructuralBridge` contract, the partial support map `trSupport` carries a checked source support to a checked target support with the translated conclusion and *identical* obligations (`support_transport`). T6's freeze record explicitly defers composition: `docs/theory-pw-t6-structural-transport.md` §8 limitation 4 — "`trSupport` composes as a function, but nothing here states the bridge-level coherence laws."

**Why T9 matters.** Without it, the modal layer supports exactly one hop: `[b]φ` is meaningful, `[b][d]φ` is a formula with no theorem behind it. The paper's claim that a claim checked in one scientific context can be carried across a *chain* of theory translations (Overlapping Fields → some shared fragment → GR-style context) needs: (a) transport composes; (b) the result depends on the chosen path only through its composite; (c) naming the composite as a single direct bridge is *not* free — it needs a commuting triangle, and we can exhibit failure without one; (d) a symbol that falls out of vocabulary mid-path yields incomparability, never a fabricated local status. Those are exactly issue #190's four acceptance bullets.

**Why now is the right time.** All inputs are frozen: `SymMap`, the `tr*` lifts, the three-clause contract, and `support_transport` landed with T6 and have a worked `_id` lemma family (`trTerm_id` … `trSupportDis_id`, `StructuralBridge.refl`) that is the exact syntactic template for the `_comp` family. CLAUDE.md's mechanization discipline says to prove what is provable now; T9 is corpus-independent and enabled.

**Key design decisions locked in by this plan:**

1. **Composition is Kleisli.** `SymMap.comp m₂ m₁` applies `m₁` first (the design's `τ_d ∘ τ_b`), with `predMap s = (m₁.predMap s).bind m₂.predMap`. The design's domain law `dom(τ_d∘τ_b) = {c ∈ dom τ_b | τ_b c ∈ dom τ_d}` is then not a definition but a theorem shape: every lift satisfies `trX (m₂.comp m₁) x = (trX m₁ x).bind (trX m₂)`.
2. **The path is first-class data.** An indexed inductive `BridgePath` over chains of checking environments. "State the intermediate-world dependence explicitly" is satisfied structurally: every theorem is stated *per chosen path*, and the coherence theorem `trans_eq_compose` says the transported result depends on the path only through its fold (`compose`).
3. **The commuting triangle is stated at the induced-map level** (`trAtom`/`trSupport` agreement), not raw `SymMap` equality — matching the design's bullets ("equality between direct and composed claim translations; coherence of support transport") and strictly weaker than pointwise symbol-map equality, which is provided as a sufficient condition.
4. **Two parts of the triangle are free, and we prove that.** `rule_ok` pins the target policy at each identifier, so on policy rules the direct and composed rule translations agree *automatically* (`commutes_on_rules`); similarly on admitted leaf atoms once the leaf maps agree (`commutes_on_leaves`). The genuinely needed hypotheses are the leaf renaming and the claim vocabulary outside the policy/evidence image — the witnesses in Task 8 live exactly there.
5. **Nothing touches approximation bridges.** No definition in this plan mentions error, convergence, observables, or comparison spaces; the boundary is recorded in the freeze doc (Task 10).

**Scope guard (things deliberately NOT in this plan):** categorical laws for `comp` (associativity/unit as equalities of bridges — `trans_eq_compose` already carries the semantic content of path flattening; add laws only if a client needs them, recorded as a limitation), edge-indexed translations, partial leaf maps, status preservation along paths (that is T8 #193 composed with this, not T9), any Haskell-side work (T9 is pure metatheory of the Lean wrapper).

---

## File structure

- **Create** `lean/Lara/PW/Compose.lean` — all T9 theory: `SymMap.comp`, the `_comp` lemma family (terms → atoms → patterns → substitutions → rules → supports), `StructuralBridge.comp`, `support_transport_comp`, `BridgePath` (+ `compose`, `trans`, `trans_eq_compose`, `path_support_transport`), `Commutes` + `direct_transport_agrees` + free-commuting lemmas, `admits_comp` + `admits_comp_transport`. One nameable seam: "T9 composition".
- **Create** `lean/Lara/Examples/PWCompose.lean` — the two-leg renaming path over T6's `bridgeRen`, the two no-triangle witnesses, the mid-path incomparability witness.
- **Modify** `lean/Lara.lean` — two imports + one commentary bullet in the PW block (near line 213).
- **Modify** `lean/AxCheck.lean` — two imports (after line 81) + `#print axioms` for every new theorem.
- **Modify** `.github/workflows/ci.yml` — add the two new files to the `check-axcheck-coverage.py` invocation (~line 183).
- **Create** `docs/theory-pw-t9-path-composition.md`; **modify** `docs/paper-lean-name-map.md` (new §PW-T9) and `docs/theory-pw-t6-structural-transport.md` (limitation 4 gets a "discharged by" pointer).

**Working conventions for every Lean task below:**

- Build command (from repo root): `cd lean && lake build`. A task's statements may be committed only once `sorry`-free — write statements with `sorry` locally to see them elaborate ("failing test"), then prove, then build clean, then commit.
- The tactic scripts below are best-effort against the current toolchain; if a step fails, mirror the corresponding `_id` proof in `lean/Lara/PW/Translation.lean:857-966` (same case analysis, plus a `bind` split). Useful core lemmas: `Option.some_bind`, `Option.none_bind`, `Option.bind_eq_some` (or `Option.bind_eq_some_iff` depending on toolchain — check with `#check`); fall back to `cases hx : x` when a simp lemma is missing.
- Commit messages follow repo history: `theory(PW-T9): <what> (#190)`.

---

### Task 0: Branch

- [x] **Step 1: Create the branch**

```bash
git checkout -b theory/pw-t9-path-composition
```

---

### Task 1: `SymMap.comp` and the term/atom `_comp` lemmas

**Files:**
- Create: `lean/Lara/PW/Compose.lean`

- [x] **Step 1: Create the module with header, `SymMap.comp`, and the term-level lemma statements (with `sorry`)**

```lean
/-
# PW-T9 — exact structural-path composition (issue #190, tracker #189)

Composition of the T6 layer, three levels deep:

* **Translations compose Kleisli-style** (`SymMap.comp` and the `_comp`
  lemma family): every structural lift satisfies
  `trX (m₂.comp m₁) x = (trX m₁ x).bind (trX m₂)`, which *is* the design's
  composed-domain law `dom(τ_d∘τ_b) = {c ∈ dom τ_b | τ_b c ∈ dom τ_d}` —
  the composite is defined exactly when the first leg is defined and its
  image is in the second leg's vocabulary. A mid-path vocabulary gap
  surfaces as `none`, i.e. as incomparability at the comparison layer,
  never as a local status (`trAtom_comp_none_mid`,
  `Examples.PW.Compose.mid_path_translationUndefined`).
* **Bridges compose** (`StructuralBridge.comp`): each contract clause of
  the composite is discharged by chaining the two legs' clauses through
  the intermediate environment.
* **Transport composes coherently** (`support_transport_comp`,
  `BridgePath.trans_eq_compose`, `path_support_transport`): stepwise
  transport along a chosen typed path equals transport along the path's
  folded composite, so T6's `support_transport` at the composite *is* the
  path theorem. The path is data — theorems are stated per chosen path,
  which is how intermediate-environment dependence stays explicit.
* **A named direct bridge agrees with a composite only under a commuting
  triangle** (`Commutes`, `direct_transport_agrees`). Two corners of the
  triangle are free — the target policy pins rule translations
  (`commutes_on_rules`) and, given agreeing leaf maps, evidence typing
  pins admitted-atom translations (`commutes_on_leaves`) — the witnesses
  in `Lara.Examples.PWCompose` show the remaining hypotheses are not.

Nothing here concerns approximation bridges: composition for those needs
separate domains, observables, comparison spaces, and error/convergence
laws, and remains deferred (issue #190's boundary).

This module only imports; no local definition and no T6 module is touched.
-/

import Lara.PW.Structural

namespace Lara.PW

open Lara.Support

/-- Kleisli composition of partial symbol translations: `m₂.comp m₁`
applies `m₁` first — the design's `τ_d ∘ τ_b`. A symbol is in the composed
vocabulary exactly when it is in `m₁`'s vocabulary and its image is in
`m₂`'s. -/
def SymMap.comp (m₂ m₁ : SymMap) : SymMap where
  predMap := fun s => (m₁.predMap s).bind m₂.predMap
  conMap  := fun s => (m₁.conMap s).bind m₂.conMap

mutual
  /-- `trTerm` along the composite is the Kleisli composition of the legs. -/
  theorem trTerm_comp (m₂ m₁ : SymMap) : ∀ t : Term,
      trTerm (m₂.comp m₁) t = (trTerm m₁ t).bind (trTerm m₂)
    := sorry
  /-- `trTerms` along the composite is the Kleisli composition of the legs. -/
  theorem trTerms_comp (m₂ m₁ : SymMap) : ∀ ts : Terms,
      trTerms (m₂.comp m₁) ts = (trTerms m₁ ts).bind (trTerms m₂)
    := sorry
end

/-- `trAtom` along the composite is the Kleisli composition of the legs —
the composed-domain law at claim level. -/
theorem trAtom_comp (m₂ m₁ : SymMap) (a : Atom) :
    trAtom (m₂.comp m₁) a = (trAtom m₁ a).bind (trAtom m₂) := sorry

/-- `trAtoms` along the composite is the Kleisli composition of the legs. -/
theorem trAtoms_comp (m₂ m₁ : SymMap) : ∀ as : List Atom,
    trAtoms (m₂.comp m₁) as = (trAtoms m₁ as).bind (trAtoms m₂) := sorry

/-- A first-leg gap is a composite gap. -/
theorem trAtom_comp_none_left {m₂ m₁ : SymMap} {a : Atom}
    (h : trAtom m₁ a = none) : trAtom (m₂.comp m₁) a = none := by
  rw [trAtom_comp, h]; rfl

/-- **Missing intermediate translation**: the first leg succeeds but its
image is out of the second leg's vocabulary, so the composite is undefined —
the failure mode that must surface as incomparability, not as a status. -/
theorem trAtom_comp_none_mid {m₂ m₁ : SymMap} {a a' : Atom}
    (h₁ : trAtom m₁ a = some a') (h₂ : trAtom m₂ a' = none) :
    trAtom (m₂.comp m₁) a = none := by
  rw [trAtom_comp, h₁, Option.some_bind]; exact h₂

end Lara.PW
```

- [x] **Step 2: Verify the failing state** — `cd lean && lake build` reports `sorry` warnings for the four `sorry`-bearing declarations and no other errors (statements elaborate).

- [x] **Step 3: Prove the four lemmas.** Template — case on the constructor as `trTerm_id` does (`Translation.lean:859`), then case on the first-leg pieces. For `trTerm_comp`, the `.con` arm:

```lean
    | .con k ts => by
        simp only [trTerm, SymMap.comp, trTerms_comp m₂ m₁ ts]
        cases hk : m₁.conMap k with
        | none => rfl
        | some k' =>
          cases hts : trTerms m₁ ts with
          | none => cases m₂.conMap k' <;> rfl
          | some ts' =>
            simp only [Option.some_bind, trTerm]
            cases m₂.conMap k' <;> cases trTerms m₂ ts' <;> rfl
```

`.num`/`.str` arms: the second leg re-succeeds on an unchanged literal — `rfl` (or `simp [trTerm]`). `trTerms_comp` mirrors `trTerms_id` with the same bind split; `trAtom_comp` destructs the atom (`obtain ⟨p, ts⟩ := a`) and reuses `trTerms_comp`; `trAtoms_comp` is list induction reusing `trAtom_comp`.

- [x] **Step 4: Build clean** — `cd lean && lake build`: success, zero warnings.

- [x] **Step 5: Commit**

```bash
git add lean/Lara/PW/Compose.lean
git commit -m "theory(PW-T9): SymMap composition and term/atom Kleisli laws (#190)"
```

---

### Task 2: Pattern, substitution, question, and rule `_comp` lemmas

**Files:**
- Modify: `lean/Lara/PW/Compose.lean`

- [x] **Step 1: State and prove the remaining first-order lifts.** Same statement shape for each, appended after `trAtom_comp_none_mid` (each proof mirrors its `_id` twin at `Translation.lean:888-942` plus the Task 1 bind split):

```lean
mutual
  /-- `trPat` along the composite is the Kleisli composition of the legs. -/
  theorem trPat_comp (m₂ m₁ : SymMap) : ∀ p : Pat,
      trPat (m₂.comp m₁) p = (trPat m₁ p).bind (trPat m₂) := ...
  /-- `trPats` along the composite is the Kleisli composition of the legs. -/
  theorem trPats_comp (m₂ m₁ : SymMap) : ∀ ps : Pats,
      trPats (m₂.comp m₁) ps = (trPats m₁ ps).bind (trPats m₂) := ...
end

/-- `trAPat` along the composite is the Kleisli composition of the legs. -/
theorem trAPat_comp (m₂ m₁ : SymMap) (ap : APat) :
    trAPat (m₂.comp m₁) ap = (trAPat m₁ ap).bind (trAPat m₂) := ...

/-- `trAPats` along the composite is the Kleisli composition of the legs. -/
theorem trAPats_comp (m₂ m₁ : SymMap) : ∀ aps : List APat,
    trAPats (m₂.comp m₁) aps = (trAPats m₁ aps).bind (trAPats m₂) := ...

/-- `trSubst` along the composite is the Kleisli composition of the legs. -/
theorem trSubst_comp (m₂ m₁ : SymMap) : ∀ θ : Subst,
    trSubst (m₂.comp m₁) θ = (trSubst m₁ θ).bind (trSubst m₂) := ...

/-- `trQuestion` along the composite is the Kleisli composition of the legs. -/
theorem trQuestion_comp (m₂ m₁ : SymMap) (q : Question) :
    trQuestion (m₂.comp m₁) q = (trQuestion m₁ q).bind (trQuestion m₂) := ...

/-- `trQuestions` along the composite is the Kleisli composition of the legs. -/
theorem trQuestions_comp (m₂ m₁ : SymMap) : ∀ qs : List Question,
    trQuestions (m₂.comp m₁) qs = (trQuestions m₁ qs).bind (trQuestions m₂) := ...

/-- `trRule` along the composite is the Kleisli composition of the legs:
premises, conclusion, and answers compose; mode, parameters, the trusted
flag, and the certifier allowlist are untouched by both legs. -/
theorem trRule_comp (m₂ m₁ : SymMap) (r : Rule) :
    trRule (m₂.comp m₁) r = (trRule m₁ r).bind (trRule m₂) := ...
```

Note for `trQuestion_comp`/`trRule_comp`: after the first leg succeeds, the intermediate value is a `{ q with answer := a' }` / `{ r with premises := … }` record; `simp only [trQuestion]` / `simp only [trRule]` re-exposes the second-leg match on the *updated* fields, then case as before.

- [x] **Step 2: Build clean** — `cd lean && lake build`: success.

- [x] **Step 3: Commit**

```bash
git add lean/Lara/PW/Compose.lean
git commit -m "theory(PW-T9): pattern/substitution/rule Kleisli composition laws (#190)"
```

---

### Task 3: Support-term `_comp` lemmas (the composed partial support map)

**Files:**
- Modify: `lean/Lara/PW/Compose.lean`

- [x] **Step 1: State and prove the mutual support-level lemmas** (mirror `trSupport_id` at `Translation.lean:944-966`; leaf arm is `rfl` since leaf renaming is total function composition):

```lean
mutual
  /-- **The composed dependent partial support map is the Kleisli
  composition of the legs** — T9's "coherence of support transport" at the
  level of the map itself. Defined exactly when the first leg is defined
  and its image is in the second leg's domain. -/
  theorem trSupport_comp (m₂ m₁ : SymMap) (lm₂ lm₁ : LeafId → LeafId) :
      ∀ w : SupportTerm,
        trSupport (m₂.comp m₁) (lm₂ ∘ lm₁) w =
          (trSupport m₁ lm₁ w).bind (trSupport m₂ lm₂)
    | .leaf _ => rfl
    | .inst rn θ ws D H α => by
        simp only [trSupport, trSubst_comp m₂ m₁ θ,
          trSupportList_comp m₂ m₁ lm₂ lm₁ ws,
          trSupportDis_comp m₂ m₁ lm₂ lm₁ D]
        cases trSubst m₁ θ <;> cases trSupportList m₁ lm₁ ws <;>
          cases trSupportDis m₁ lm₁ D <;>
          simp only [Option.some_bind, Option.none_bind, trSupport] <;>
          first
            | rfl
            | (cases trSubst m₂ ‹_› <;> cases trSupportList m₂ lm₂ ‹_› <;>
                cases trSupportDis m₂ lm₂ ‹_› <;> rfl)
  /-- `trSupportList` along the composite is the Kleisli composition. -/
  theorem trSupportList_comp (m₂ m₁ : SymMap) (lm₂ lm₁ : LeafId → LeafId) :
      ∀ ws : List SupportTerm,
        trSupportList (m₂.comp m₁) (lm₂ ∘ lm₁) ws =
          (trSupportList m₁ lm₁ ws).bind (trSupportList m₂ lm₂) := ...
  /-- `trSupportDis` along the composite is the Kleisli composition. -/
  theorem trSupportDis_comp (m₂ m₁ : SymMap) (lm₂ lm₁ : LeafId → LeafId) :
      ∀ D : List (QuestionId × SupportTerm),
        trSupportDis (m₂.comp m₁) (lm₂ ∘ lm₁) D =
          (trSupportDis m₁ lm₁ D).bind (trSupportDis m₂ lm₂) := ...
end
```

(The `.inst` tactic block above is indicative; if the combined `cases … <;>` chain misfires, split it into nested explicit `cases hx : …` as in `support_transport`'s own option handling, `Structural.lean:129-141`.)

- [x] **Step 2: Build clean** — `cd lean && lake build`: success.

- [x] **Step 3: Commit**

```bash
git add lean/Lara/PW/Compose.lean
git commit -m "theory(PW-T9): the composed partial support map is Kleisli composition (#190)"
```

---

### Task 4: `StructuralBridge.comp` and two-step transport coherence

**Files:**
- Modify: `lean/Lara/PW/Compose.lean`

- [x] **Step 1: Define bridge composition.** Each clause chains the legs through the intermediate environment:

```lean
/-- **Composition of structural bridges** through a shared intermediate
checking environment. The symbol translation composes Kleisli-style, the
leaf renaming composes as functions, and each contract clause is the two
legs' clauses chained through the middle. The intermediate environment
(`Pi'`, `Gamma'`, `CertOk'`) is existential history here — but transport
along the composite still factors through it, which is what
`support_transport_comp` keeps explicit. -/
def StructuralBridge.comp
    {canon : String → String} {Pi Pi' Pi'' : RuleId → Option Rule}
    {Gamma Gamma' Gamma'' : LeafId → Option Atom}
    {CertOk CertOk' CertOk'' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (B₂ : StructuralBridge canon Pi' Pi'' Gamma' Gamma'' CertOk' CertOk'')
    (B₁ : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk') :
    StructuralBridge canon Pi Pi'' Gamma Gamma'' CertOk CertOk'' where
  sym := B₂.sym.comp B₁.sym
  leafMap := B₂.leafMap ∘ B₁.leafMap
  leaf_ok := fun l p h => by
    obtain ⟨p', hp', h'⟩ := B₁.leaf_ok l p h
    obtain ⟨p'', hp'', h''⟩ := B₂.leaf_ok (B₁.leafMap l) p' h'
    exact ⟨p'', by rw [trAtom_comp, hp', Option.some_bind]; exact hp'', h''⟩
  rule_ok := fun rn r h => by
    obtain ⟨r', hr', h'⟩ := B₁.rule_ok rn r h
    obtain ⟨r'', hr'', h''⟩ := B₂.rule_ok rn r' h'
    exact ⟨r'', by rw [trRule_comp, hr', Option.some_bind]; exact hr'', h''⟩
  cert_ok := fun β hd κ As C As'' C'' hAs hC hacc => by
    rw [trAtoms_comp] at hAs
    rw [trAtom_comp] at hC
    obtain ⟨As', hAs₁, hAs₂⟩ := Option.bind_eq_some.mp hAs
    obtain ⟨C', hC₁, hC₂⟩ := Option.bind_eq_some.mp hC
    exact B₂.cert_ok β hd κ As' C' As'' C'' hAs₂ hC₂
      (B₁.cert_ok β hd κ As C As' C' hAs₁ hC₁ hacc)
```

- [x] **Step 2: State and prove two-step coherence.** This is the binary heart of T9 — the intermediate conclusion `C'` and the intermediate checked judgment appear *explicitly* in the statement:

```lean
/-- **T9, two-step form.** Stepwise transport along `B₁` then `B₂` is
transport along the composed bridge: the composite's partial support map
sends `w` to the same `w''`, the composed translated conclusion is the
translation of the translated conclusion, and both the intermediate and the
final checked judgments hold — the intermediate environment's role is in
evidence, not erased. -/
theorem support_transport_comp
    {canon : String → String} {Pi Pi' Pi'' : RuleId → Option Rule}
    {Gamma Gamma' Gamma'' : LeafId → Option Atom}
    {CertOk CertOk' CertOk'' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (B₂ : StructuralBridge canon Pi' Pi'' Gamma' Gamma'' CertOk' CertOk'')
    (B₁ : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk')
    {w w' w'' : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk w C O)
    (hw₁ : trSupport B₁.sym B₁.leafMap w = some w')
    (hw₂ : trSupport B₂.sym B₂.leafMap w' = some w'') :
    trSupport (B₂.comp B₁).sym (B₂.comp B₁).leafMap w = some w'' ∧
      ∃ C' C'', trAtom B₁.sym C = some C' ∧ trAtom B₂.sym C' = some C'' ∧
        trAtom (B₂.comp B₁).sym C = some C'' ∧
        HasSupport canon Pi' Gamma' CertOk' w' C' O ∧
        HasSupport canon Pi'' Gamma'' CertOk'' w'' C'' O := by
  obtain ⟨C', hC₁, h₁⟩ := support_transport B₁ h hw₁
  obtain ⟨C'', hC₂, h₂⟩ := support_transport B₂ h₁ hw₂
  refine ⟨?_, C', C'', hC₁, hC₂, ?_, h₁, h₂⟩
  · show trSupport (B₂.sym.comp B₁.sym) (B₂.leafMap ∘ B₁.leafMap) w = some w''
    rw [trSupport_comp, hw₁, Option.some_bind]
    exact hw₂
  · show trAtom (B₂.sym.comp B₁.sym) C = some C''
    rw [trAtom_comp, hC₁, Option.some_bind]
    exact hC₂
```

- [x] **Step 3: Build clean** — `cd lean && lake build`: success.

- [x] **Step 4: Commit**

```bash
git add lean/Lara/PW/Compose.lean
git commit -m "theory(PW-T9): bridge composition and two-step transport coherence (#190)"
```

---

### Task 5: `BridgePath` and path transport

**Files:**
- Modify: `lean/Lara/PW/Compose.lean`

- [x] **Step 1: Define the typed path, its composite, and its stepwise map**

```lean
/-- **A chosen typed path of structural bridges** between checking
environments over one shared canonicalizer. The intermediate environments
are constructor data: two paths with the same endpoints need not agree, and
every theorem below is stated per chosen path — this is how the design's
"independence from intermediate-world choices, or an explicit path in the
result" resolves here: the path is explicit in the result. (The constructor
quantifies over intermediate environments, hence `Type 1`.) -/
inductive BridgePath (canon : String → String) :
    (RuleId → Option Rule) → (RuleId → Option Rule) →
    (LeafId → Option Atom) → (LeafId → Option Atom) →
    (BackendId → Digest → CertRef → List Atom → Atom → Prop) →
    (BackendId → Digest → CertRef → List Atom → Atom → Prop) → Type 1 where
  | nil : BridgePath canon Pi Pi Gamma Gamma CertOk CertOk
  | cons :
      StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk' →
      BridgePath canon Pi' Pi'' Gamma' Gamma'' CertOk' CertOk'' →
      BridgePath canon Pi Pi'' Gamma Gamma'' CertOk CertOk''

/-- The path's named composite: fold of binary composition, the identity
endobridge at the empty path. -/
def BridgePath.compose {canon Pi Pi' Gamma Gamma' CertOk CertOk'} :
    BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk' →
      StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk'
  | .nil => .refl canon Pi Gamma CertOk
  | .cons B P => P.compose.comp B

/-- Stepwise transport along the path: the Kleisli chain of the per-edge
partial support maps, in path order. `none` as soon as any edge's
translation is undefined on the running image — a mid-path vocabulary gap
is a gap of the whole path. -/
def BridgePath.trans {canon Pi Pi' Gamma Gamma' CertOk CertOk'} :
    BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk' →
      SupportTerm → Option SupportTerm
  | .nil => fun w => some w
  | .cons B P => fun w => (trSupport B.sym B.leafMap w).bind P.trans
```

(Write the index binders explicitly if auto-bound implicits misbehave; the six index types are exactly `StructuralBridge`'s parameter types at `Structural.lean:62-65`.)

- [x] **Step 2: Prove path coherence and path transport**

```lean
/-- **Path coherence**: stepwise transport along a chosen path equals the
partial support map of the path's named composite. The transported result
depends on the chosen path only through its composite. -/
theorem BridgePath.trans_eq_compose
    {canon Pi Pi' Gamma Gamma' CertOk CertOk'}
    (P : BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk') :
    ∀ w : SupportTerm,
      P.trans w = trSupport P.compose.sym P.compose.leafMap w := by
  induction P with
  | nil => intro w; exact (trSupport_id w).symm
  | cons B P ih =>
    intro w
    show (trSupport B.sym B.leafMap w).bind P.trans =
      trSupport (P.compose.comp B).sym (P.compose.comp B).leafMap w
    rw [show (P.compose.comp B).sym = P.compose.sym.comp B.sym from rfl,
        show (P.compose.comp B).leafMap = P.compose.leafMap ∘ B.leafMap
          from rfl,
        trSupport_comp]
    cases trSupport B.sym B.leafMap w with
    | none => rfl
    | some w' => simp only [Option.some_bind]; exact ih w'

/-- **T9, path transport.** A checked source support transports along any
chosen path of exact structural bridges whose stepwise translation is
defined: the result is checked in the path's final environment, concludes
the composite-translated claim, and carries the *same* obligations — T6's
`support_transport` applied to the path's composite, which path coherence
makes the same thing as the stepwise chain. -/
theorem path_support_transport
    {canon Pi Pi' Gamma Gamma' CertOk CertOk'}
    (P : BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk')
    {w w' : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk w C O)
    (hw : P.trans w = some w') :
    ∃ C', trAtom P.compose.sym C = some C' ∧
      HasSupport canon Pi' Gamma' CertOk' w' C' O := by
  rw [P.trans_eq_compose] at hw
  exact support_transport P.compose h hw
```

- [x] **Step 3: Build clean** — `cd lean && lake build`: success.

- [x] **Step 4: Commit**

```bash
git add lean/Lara/PW/Compose.lean
git commit -m "theory(PW-T9): typed bridge paths, path coherence, path transport (#190)"
```

---

### Task 6: The commuting triangle

**Files:**
- Modify: `lean/Lara/PW/Compose.lean`

- [ ] **Step 1: Define `Commutes` and its sufficient condition**

```lean
/-- **The commuting triangle** a named direct bridge must satisfy to agree
with a chosen two-leg composite — the design's "equality between direct and
composed claim translations" (`atom_eq`) and "coherence of support
transport" (`support_eq`), stated at the level of the induced maps rather
than the raw symbol maps. Without it, agreement fails even when both
transports succeed (`Lara.Examples.PWCompose.direct_ne_composed_support`,
`direct_ne_composed_claim`). -/
structure Commutes
    {canon : String → String} {Pi Pi' Pi'' : RuleId → Option Rule}
    {Gamma Gamma' Gamma'' : LeafId → Option Atom}
    {CertOk CertOk' CertOk'' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (B₃ : StructuralBridge canon Pi Pi'' Gamma Gamma'' CertOk CertOk'')
    (B₂ : StructuralBridge canon Pi' Pi'' Gamma' Gamma'' CertOk' CertOk'')
    (B₁ : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk') :
    Prop where
  atom_eq : ∀ a, trAtom B₃.sym a = trAtom (B₂.sym.comp B₁.sym) a
  support_eq : ∀ w, trSupport B₃.sym B₃.leafMap w =
    trSupport (B₂.sym.comp B₁.sym) (B₂.leafMap ∘ B₁.leafMap) w

/-- Pointwise equality of the raw maps is sufficient for the triangle. -/
theorem Commutes.of_maps_eq
    {canon Pi Pi' Pi'' Gamma Gamma' Gamma'' CertOk CertOk' CertOk''}
    {B₃ : StructuralBridge canon Pi Pi'' Gamma Gamma'' CertOk CertOk''}
    {B₂ : StructuralBridge canon Pi' Pi'' Gamma' Gamma'' CertOk' CertOk''}
    {B₁ : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk'}
    (hsym : B₃.sym = B₂.sym.comp B₁.sym)
    (hleaf : B₃.leafMap = B₂.leafMap ∘ B₁.leafMap) :
    Commutes B₃ B₂ B₁ :=
  ⟨fun a => by rw [hsym], fun w => by rw [hsym, hleaf]⟩
```

- [ ] **Step 2: Prove the agreement theorem**

```lean
/-- **Direct agrees with composed under the triangle — and the triangle is
the price of the equality** (issue #190's acceptance): given `Commutes`, the
direct bridge transports the source support to *the same* target term the
stepwise chain produces, with the same translated conclusion, checked in the
same final environment. -/
theorem direct_transport_agrees
    {canon Pi Pi' Pi'' Gamma Gamma' Gamma'' CertOk CertOk' CertOk''}
    {B₃ : StructuralBridge canon Pi Pi'' Gamma Gamma'' CertOk CertOk''}
    {B₂ : StructuralBridge canon Pi' Pi'' Gamma' Gamma'' CertOk' CertOk''}
    {B₁ : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk'}
    (hc : Commutes B₃ B₂ B₁)
    {w w' w'' : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk w C O)
    (hw₁ : trSupport B₁.sym B₁.leafMap w = some w')
    (hw₂ : trSupport B₂.sym B₂.leafMap w' = some w'') :
    trSupport B₃.sym B₃.leafMap w = some w'' ∧
      ∃ C'', trAtom B₃.sym C = some C'' ∧
        trAtom (B₂.comp B₁).sym C = some C'' ∧
        HasSupport canon Pi'' Gamma'' CertOk'' w'' C'' O := by
  have h₃ : trSupport B₃.sym B₃.leafMap w = some w'' := by
    rw [hc.support_eq, trSupport_comp, hw₁, Option.some_bind]
    exact hw₂
  obtain ⟨C'', hC'', hHS⟩ := support_transport B₃ h h₃
  refine ⟨h₃, C'', hC'', ?_, hHS⟩
  rw [show (B₂.comp B₁).sym = B₂.sym.comp B₁.sym from rfl, ← hc.atom_eq]
  exact hC''
```

- [ ] **Step 3: Prove the free corners of the triangle**

```lean
/-- **On policy rules the triangle commutes for free**: `rule_ok` pins the
target policy at each identifier to *the* translated rule, for the direct
bridge and for the composite alike, so wherever the source policy is
defined the two rule translations are equal with no commuting hypothesis.
Genuine disagreement can only live off the policy — in the leaf renaming or
in claim vocabulary the policy does not mention. -/
theorem commutes_on_rules
    {canon Pi Pi' Pi'' Gamma Gamma' Gamma'' CertOk CertOk' CertOk''}
    (B₃ : StructuralBridge canon Pi Pi'' Gamma Gamma'' CertOk CertOk'')
    (B₂ : StructuralBridge canon Pi' Pi'' Gamma' Gamma'' CertOk' CertOk'')
    (B₁ : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk')
    {rn : RuleId} {r : Rule} (h : Pi rn = some r) :
    trRule B₃.sym r = trRule (B₂.sym.comp B₁.sym) r := by
  obtain ⟨r₃, h₃, hPi₃⟩ := B₃.rule_ok rn r h
  obtain ⟨r₁, h₁, hPi₁⟩ := B₁.rule_ok rn r h
  obtain ⟨r₂, h₂, hPi₂⟩ := B₂.rule_ok rn r₁ hPi₁
  rw [h₃, trRule_comp, h₁, Option.some_bind, h₂]
  rw [hPi₂] at hPi₃
  exact congrArg some (Option.some.inj hPi₃)

/-- Given agreeing leaf maps, admitted-atom translations also commute for
free: the target evidence typing pins the translated atom at the shared
target leaf. -/
theorem commutes_on_leaves
    {canon Pi Pi' Pi'' Gamma Gamma' Gamma'' CertOk CertOk' CertOk''}
    (B₃ : StructuralBridge canon Pi Pi'' Gamma Gamma'' CertOk CertOk'')
    (B₂ : StructuralBridge canon Pi' Pi'' Gamma' Gamma'' CertOk' CertOk'')
    (B₁ : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk')
    (hleaf : ∀ l, B₃.leafMap l = B₂.leafMap (B₁.leafMap l))
    {l : LeafId} {p : Atom} (h : Gamma l = some p) :
    trAtom B₃.sym p = trAtom (B₂.sym.comp B₁.sym) p := by
  obtain ⟨p₃, h₃, hΓ₃⟩ := B₃.leaf_ok l p h
  obtain ⟨p₁, h₁, hΓ₁⟩ := B₁.leaf_ok l p h
  obtain ⟨p₂, h₂, hΓ₂⟩ := B₂.leaf_ok (B₁.leafMap l) p₁ hΓ₁
  rw [h₃, trAtom_comp, h₁, Option.some_bind, h₂]
  rw [hleaf l, hΓ₂] at hΓ₃
  exact congrArg some (Option.some.inj hΓ₃)
```

- [ ] **Step 4: Build clean** — `cd lean && lake build`: success.

- [ ] **Step 5: Commit**

```bash
git add lean/Lara/PW/Compose.lean
git commit -m "theory(PW-T9): commuting triangle, direct-vs-composed agreement, free corners (#190)"
```

---

### Task 7: `Admits` composition — explicit intermediate worlds

**Files:**
- Modify: `lean/Lara/PW/Compose.lean`

- [ ] **Step 1: State and prove relational composition of the induced applicability judgment.** This is the "relation" corner of the design's composite conditions, at the checker-tied `Admits` level (`Structural.lean:465`); the intermediate *world* `v` is an explicit argument, never erased:

```lean
/-- **Relational composition of the induced applicability judgment**: an
admitted pair through `B₁` into a chosen intermediate world `v`, followed
by an admitted pair through `B₂` out of `v`, is an admitted pair of the
composed bridge. The composed relation is the relational composite — it
holds only by exhibiting some `v`, and this statement keeps the chosen `v`
explicit (issue #190's "state the intermediate-world dependence
explicitly"). -/
theorem admits_comp {κ lam mu : Instance.Context}
    (B₂ : StructuralBridge κ.canon lam.policy.ruleLookup
      mu.policy.ruleLookup lam.Gamma mu.Gamma lam.CertOk mu.CertOk)
    (B₁ : StructuralBridge κ.canon κ.policy.ruleLookup
      lam.policy.ruleLookup κ.Gamma lam.Gamma κ.CertOk lam.CertOk)
    {w : Instance.World κ} {v : Instance.World lam}
    {u : Instance.World mu}
    (h₁ : Admits B₁.sym B₁.leafMap w v)
    (h₂ : Admits B₂.sym B₂.leafMap v u) :
    Admits (B₂.comp B₁).sym (B₂.comp B₁).leafMap w u := by
  intro t ht
  obtain ⟨t', htr₁, hmem'⟩ := h₁ t ht
  obtain ⟨t'', htr₂, hmem''⟩ := h₂ t' hmem'
  refine ⟨t'', ?_, hmem''⟩
  show trSupport (B₂.sym.comp B₁.sym) (B₂.leafMap ∘ B₁.leafMap) t = some t''
  rw [trSupport_comp, htr₁, Option.some_bind]
  exact htr₂
```

(Note the bridge typings: both legs are stated over `κ.canon` since `StructuralBridge` fixes one shared canonicalizer; `admits_transport` at `Structural.lean:477` handles the `lam.canon = κ.canon` rewriting and is the template if the `B₂` typing needs a `hcanon ▸` cast. If elaboration fights the cast, take `hcanon₁ : lam.canon = κ.canon` and `hcanon₂ : mu.canon = lam.canon` as hypotheses and state `B₂` over `κ.canon` exactly as written — worlds never mention `canon` in `Admits`, so the proof is unaffected.)

- [ ] **Step 2: Chain `admits_transport` across the intermediate world**

```lean
/-- Three-world transport across a chosen intermediate: at an admitted
two-edge chain, every argument of the source world's program transports to
a member of the intermediate world's program and on to a member of the
final world's program, each carrying a complete checked support for its
stage's translated conclusion — the source, intermediate, and target
judgments all in evidence. -/
theorem admits_comp_transport {κ lam mu : Instance.Context}
    (hcanon₁ : lam.canon = κ.canon) (hcanon₂ : mu.canon = lam.canon)
    (B₂ : StructuralBridge κ.canon lam.policy.ruleLookup
      mu.policy.ruleLookup lam.Gamma mu.Gamma lam.CertOk mu.CertOk)
    (B₁ : StructuralBridge κ.canon κ.policy.ruleLookup
      lam.policy.ruleLookup κ.Gamma lam.Gamma κ.CertOk lam.CertOk)
    {w : Instance.World κ} {v : Instance.World lam}
    {u : Instance.World mu}
    (h₁ : Admits B₁.sym B₁.leafMap w v)
    (h₂ : Admits B₂.sym B₂.leafMap v u) :
    ∀ t, t ∈ w.unit.program.args →
      ∃ t' t'' C C' C'',
        t' ∈ v.unit.program.args ∧ t'' ∈ u.unit.program.args ∧
        trSupport B₁.sym B₁.leafMap t = some t' ∧
        trSupport B₂.sym B₂.leafMap t' = some t'' ∧
        trAtom B₁.sym C = some C' ∧ trAtom B₂.sym C' = some C'' ∧
        HasSupport κ.canon κ.policy.ruleLookup κ.Gamma κ.CertOk t C [] ∧
        HasSupport lam.canon lam.policy.ruleLookup lam.Gamma lam.CertOk
          t' C' [] ∧
        HasSupport mu.canon mu.policy.ruleLookup mu.Gamma mu.CertOk
          t'' C'' [] := by
  intro t ht
  obtain ⟨C, hHS⟩ := w.unit.program.complete t ht
  rw [w.policy_eq] at hHS
  obtain ⟨t', htr₁, hmem'⟩ := h₁ t ht
  obtain ⟨t'', htr₂, hmem''⟩ := h₂ t' hmem'
  obtain ⟨C', hC₁, hHS'⟩ := support_transport B₁ hHS htr₁
  obtain ⟨C'', hC₂, hHS''⟩ := support_transport B₂ hHS' htr₂
  exact ⟨t', t'', C, C', C'', hmem', hmem'', htr₁, htr₂, hC₁, hC₂, hHS,
    by rw [hcanon₁]; exact hHS', by rw [hcanon₂, hcanon₁]; exact hHS''⟩
```

- [ ] **Step 3: The relation corner of the triangle.** Under the triangle's support clause, the direct bridge's induced applicability relation *is* the composed bridge's — the checkable content of the design's "equality between the named and relational composite" (the PW0 `accept` field stays arbitrary; this is its checker-tied face):

```lean
/-- **The relation corner**: given the commuting triangle's support clause,
the named direct bridge and the composed bridge induce the same
applicability judgment on every world pair. Together with `admits_comp`
this says the named relation contains every relational composite going
through any intermediate world — and no more than the triangle grants. -/
theorem admits_iff_of_commutes {κ mu : Instance.Context}
    {Pi' : RuleId → Option Rule} {Gamma' : LeafId → Option Atom}
    {CertOk' : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {B₃ : StructuralBridge κ.canon κ.policy.ruleLookup
      mu.policy.ruleLookup κ.Gamma mu.Gamma κ.CertOk mu.CertOk}
    {B₂ : StructuralBridge κ.canon Pi' mu.policy.ruleLookup Gamma'
      mu.Gamma CertOk' mu.CertOk}
    {B₁ : StructuralBridge κ.canon κ.policy.ruleLookup Pi' κ.Gamma Gamma'
      κ.CertOk CertOk'}
    (hc : Commutes B₃ B₂ B₁)
    {w : Instance.World κ} {u : Instance.World mu} :
    Admits B₃.sym B₃.leafMap w u ↔
      Admits (B₂.comp B₁).sym (B₂.comp B₁).leafMap w u := by
  unfold Admits
  constructor <;> intro h t ht <;> obtain ⟨t', htr, hmem⟩ := h t ht
  · refine ⟨t', ?_, hmem⟩
    show trSupport (B₂.sym.comp B₁.sym) (B₂.leafMap ∘ B₁.leafMap) t
      = some t'
    rw [← hc.support_eq]
    exact htr
  · refine ⟨t', ?_, hmem⟩
    rw [hc.support_eq]
    exact htr
```

- [ ] **Step 4: Build clean** — `cd lean && lake build`: success.

- [ ] **Step 5: Commit**

```bash
git add lean/Lara/PW/Compose.lean
git commit -m "theory(PW-T9): Admits composes relationally with explicit intermediate worlds (#190)"
```

---

### Task 8: Example instances — the live path, the failing triangle, the mid-path gap

**Files:**
- Create: `lean/Lara/Examples/PWCompose.lean`

All examples extend T6's renaming instance (`lean/Lara/Examples/PWStructural.lean:96-282`) so composition is exercised off the identity on both legs.

- [ ] **Step 1: Create the module with the second renaming leg**

```lean
/-
# PW-T9 examples (issue #190, tracker #189)

Three live instances:

* **A two-edge renaming path** extending T6's `bridgeRen`
  (`p ↦ p_r ↦ p_rr`, leaves renamed at each hop): `path_support_transport`
  computes an actual twice-renamed checked support.
* **The failing triangle**: two endobridge witnesses over environments
  where all contracts hold and both transports are defined, yet the direct
  result differs from the composed one — once by leaf renaming
  (`direct_ne_composed_support`), once by claim translation
  (`direct_ne_composed_claim`). Agreement without `Commutes` is not a
  theorem, which is issue #190's "explicit commuting triangle" acceptance
  made checkable.
* **A mid-path vocabulary gap**: the first leg translates, the second has
  no entry for the image, the composite is `none`, and the executable
  comparison reports `.incomparable .translationUndefined` — never a local
  status.
-/

import Lara.PW.Compose
import Lara.Examples.PWStructural

namespace Lara.Examples.PW.Compose

open Lara.Support
open Lara.PW
open Lara.Grounded (Status)
open Lara.Examples.PW

/-! ### The second renaming leg: `p_r ↦ p_rr`, `e_r ↦ e_rr` -/

/-- The second leg's symbol translation. -/
def ren2Sym : SymMap :=
  { predMap := fun s =>
      if s = "p_r" then some "p_rr"
      else if s = "e_r" then some "e_rr"
      else none
  , conMap := some }

/-- Third-environment policy: the twice-translated source policy. -/
def piRenTgt2 : RuleId → Option Rule :=
  fun rn => (piRenTgt rn).bind (trRule ren2Sym)

/-- The second leg's leaf renaming — again not the identity. -/
def leafMapRen2 : LeafId → LeafId := fun l => ⟨l.name ++ "-tgt2"⟩

/-- Third-environment evidence typing: the twice-renamed leaf at the
twice-translated atom. -/
def gammaRenTgt2 : LeafId → Option Atom :=
  fun l =>
    if l = leafMapRen2 (leafMapRen lRen) then some (.atom "e_rr" .nil)
    else none

/-- The once-renamed rule — what `piRenTgt` carries at `rnRen`
(`trRule renSym ruleRen` computed). -/
def ruleRenTgt : Rule :=
  { mode := .defeasible, params := [], premises := [⟨⟨"e_r"⟩, .nil⟩]
  , concl := ⟨⟨"p_r"⟩, .nil⟩, questions := [], allowTrusted := false
  , certifiers := [] }

/-- The twice-renamed rule — what `piRenTgt2` carries at `rnRen`. -/
def ruleRenTgt2 : Rule :=
  { mode := .defeasible, params := [], premises := [⟨⟨"e_rr"⟩, .nil⟩]
  , concl := ⟨⟨"p_rr"⟩, .nil⟩, questions := [], allowTrusted := false
  , certifiers := [] }

/-- The second renaming bridge, from T6's renaming target environment into
the third environment. -/
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
      -- `(some ruleRen).bind (trRule renSym)` computes to `some ruleRenTgt`
      have h' : some ruleRenTgt = some r := h
      cases h'
      refine ⟨ruleRenTgt2, rfl, ?_⟩
      unfold piRenTgt2 piRenTgt piRenSrc
      rw [if_pos hrn]
      rfl
    · rw [if_neg hrn] at h
      exact nomatch h
  cert_ok := fun _ _ _ _ _ _ _ _ _ h => h.elim
```

(If the two `rfl`s inside `rule_ok` do not close — they ask the kernel to compute `trRule renSym ruleRen = some ruleRenTgt` and `trRule ren2Sym ruleRenTgt = some ruleRenTgt2` through `String` if-chains — replace them with `by decide` or `by simp [trRule, trAPats, trAPat, trPats, trQuestions, ruleRen, ruleRenTgt, ruleRenTgt2, renSym, ren2Sym]`; the T6 precedent that these reduce is `PWStructural.lean:266` (`ren_conclusion := rfl`).)

- [ ] **Step 2: The path and its computed transport**

```lean
/-- The chosen two-edge path `source → renamed → twice-renamed`. -/
def pathRen :
    BridgePath id piRenSrc piRenTgt2 gammaRenSrc gammaRenTgt2
      certRen certRen :=
  .cons bridgeRen (.cons bridgeRen2 .nil)

/-- The twice-transported support term. -/
def wRenTgt2 : SupportTerm :=
  .inst rnRen [] [.leaf (leafMapRen2 (leafMapRen lRen))] [] [] .none

/-- The stepwise path map computes, and genuinely renames twice. -/
theorem ren_path_trans :
    pathRen.trans wRen = some wRenTgt2 ∧ wRenTgt2 ≠ wRenTgt :=
  ⟨rfl, by decide⟩

/-- **Path transport at a live instance**: the source derivation of `p`
crosses both bridges and checks in the third environment, concluding the
twice-renamed claim `p_rr`, still with empty obligations. -/
theorem ren_path_transport :
    HasSupport id piRenTgt2 gammaRenTgt2 certRen wRenTgt2
      (.atom "p_rr" .nil) [] := by
  obtain ⟨C', hC, h⟩ :=
    path_support_transport pathRen hasSupport_ren (w' := wRenTgt2) rfl
  have hC' : some (Atom.atom "p_rr" .nil) = some C' := by
    rw [← hC]; rfl
  cases hC'
  exact h
```

(If the `rfl`s do not reduce — `pathRen.trans`/composed `trAtom` go through `Option.bind` on `if`-chains, which the kernel normally chews — use `by decide` or `by native_decide`-free `simp [BridgePath.trans, trSupport, ...]` unfolding; the T6 examples' `rfl`s at `PWStructural.lean:202,266` are precedent that these reduce.)

- [ ] **Step 3: The failing triangle, leaf corner.** Environments where every contract holds and both routes succeed, yet direct ≠ composed:

```lean
/-! ### Direct ≠ composed without the commuting triangle -/

/-- Two leaves, both admitted at the same atom. -/
def lA : LeafId := ⟨"tw-a"⟩
/-- The second leaf. -/
def lB : LeafId := ⟨"tw-b"⟩
/-- The two-leaf evidence typing. -/
def gammaTwin : LeafId → Option Atom :=
  fun l => if l = lA then some (.atom "e" .nil)
    else if l = lB then some (.atom "e" .nil) else none
/-- The empty policy: `rule_ok` is vacuous, isolating the leaf corner. -/
def piEmpty : RuleId → Option Rule := fun _ => none

/-- The leaf-swapping endobridge: identity symbols, swapped leaves. Every
clause holds — both leaves carry the same atom. -/
def bridgeSwap :
    StructuralBridge id piEmpty piEmpty gammaTwin gammaTwin
      certRen certRen where
  sym := SymMap.id
  leafMap := fun l => if l = lA then lB else if l = lB then lA else l
  leaf_ok := fun l p h => by
    unfold gammaTwin at h ⊢
    by_cases ha : l = lA
    · rw [if_pos ha] at h; cases h
      exact ⟨_, trAtom_id _, by simp [ha, lA, lB]⟩
    · rw [if_neg ha] at h
      by_cases hb : l = lB
      · rw [if_pos hb] at h; cases h
        exact ⟨_, trAtom_id _, by simp [ha, hb, lA, lB]⟩
      · rw [if_neg hb] at h; exact nomatch h
  rule_ok := fun _ _ h => nomatch h
  cert_ok := fun _ _ _ _ _ _ _ _ _ h => h.elim

/-- **The leaf corner of the triangle is not free**: composing the identity
endobridge with itself transports `.leaf lA` to itself, while the
contract-satisfying direct bridge `bridgeSwap` (same endpoints) transports
it to `.leaf lB`. Both transports are defined; the results differ; no
triangle, no agreement. -/
theorem direct_ne_composed_support :
    trSupport ((StructuralBridge.refl id piEmpty gammaTwin certRen).comp
        (StructuralBridge.refl id piEmpty gammaTwin certRen)).sym
      ((StructuralBridge.refl id piEmpty gammaTwin certRen).comp
        (StructuralBridge.refl id piEmpty gammaTwin certRen)).leafMap
      (.leaf lA) = some (.leaf lA) ∧
    trSupport bridgeSwap.sym bridgeSwap.leafMap (.leaf lA) =
      some (.leaf lB) ∧
    (SupportTerm.leaf lB) ≠ .leaf lA :=
  ⟨rfl, by simp [trSupport, bridgeSwap, lA, lB], by decide⟩
```

- [ ] **Step 4: The failing triangle, claim corner.** Same shape, disagreement in the translated conclusion:

```lean
/-- Two leaves admitted at two different atoms. -/
def gammaTwo : LeafId → Option Atom :=
  fun l => if l = lA then some (.atom "e" .nil)
    else if l = lB then some (.atom "e2" .nil) else none

/-- The predicate-swapping endobridge over `gammaTwo`: swaps `e ↔ e2` and
`lA ↔ lB` together, so `leaf_ok` holds. -/
def bridgeSwapSym :
    StructuralBridge id piEmpty piEmpty gammaTwo gammaTwo
      certRen certRen where
  sym := { predMap := fun s =>
             if s = "e" then some "e2"
             else if s = "e2" then some "e" else some s
         , conMap := some }
  leafMap := fun l => if l = lA then lB else if l = lB then lA else l
  leaf_ok := fun l p h => by
    unfold gammaTwo at h ⊢
    by_cases ha : l = lA
    · rw [if_pos ha] at h; cases h
      exact ⟨.atom "e2" .nil, rfl, by simp [ha, lA, lB]⟩
    · rw [if_neg ha] at h
      by_cases hb : l = lB
      · rw [if_pos hb] at h; cases h
        exact ⟨.atom "e" .nil, rfl, by simp [ha, hb, lA, lB]⟩
      · rw [if_neg hb] at h; exact nomatch h
  rule_ok := fun _ _ h => nomatch h
  cert_ok := fun _ _ _ _ _ _ _ _ _ h => h.elim

/-- **The claim corner of the triangle is not free**: on the checked leaf
support for `e`, the composite of identity endobridges concludes `e`, the
contract-satisfying direct `bridgeSwapSym` concludes `e2`. Both derivations
check; the translated conclusions differ. -/
theorem direct_ne_composed_claim :
    trAtom ((StructuralBridge.refl id piEmpty gammaTwo certRen).comp
      (StructuralBridge.refl id piEmpty gammaTwo certRen)).sym
      (.atom "e" .nil) = some (.atom "e" .nil) ∧
    trAtom bridgeSwapSym.sym (.atom "e" .nil) = some (.atom "e2" .nil) ∧
    (Atom.atom "e2" .nil) ≠ .atom "e" .nil :=
  ⟨rfl, rfl, by decide⟩
```

- [ ] **Step 5: The mid-path gap is incomparability.** Mirror `ren_translationUndefined` (`PWStructural.lean:497`) at a composed translation:

```lean
/-! ### A mid-path vocabulary gap is incomparability, not a status -/

/-- A second leg that has no entry for `e_r`: `p_r` translates, `e_r`
falls out of vocabulary. -/
def gapSym : SymMap :=
  { predMap := fun s => if s = "p_r" then some "p_g" else none
  , conMap := some }

/-- The first leg translates `e`, the second leg rejects the image, the
composite is undefined — the design's composed-domain law at a live gap. -/
theorem mid_path_out_of_vocabulary :
    trAtom renSym (.atom "e" .nil) = some (.atom "e_r" .nil) ∧
    trAtom gapSym (.atom "e_r" .nil) = none ∧
    trAtom (gapSym.comp renSym) (.atom "e" .nil) = none :=
  ⟨rfl, rfl, trAtom_comp_none_mid rfl rfl⟩

/-- **Gate bullet at the comparison layer**: with the composed translation
undefined mid-path, the executable comparison reports
`.incomparable .translationUndefined` for every candidate set — never a
local status. `ren_translationUndefined` (T6's domain negative) at a
composite whose *first* leg succeeded. -/
theorem mid_path_translationUndefined {W : Type}
    (candidates : List W) (acceptB : W → Bool)
    (statusOf : W → Atom → Status) :
    crossCompare (trAtom (gapSym.comp renSym) (.atom "e" .nil)) candidates
      acceptB statusOf = .incomparable .translationUndefined := by
  rw [mid_path_out_of_vocabulary.2.2]
  exact compare_none candidates acceptB statusOf

end Lara.Examples.PW.Compose
```

- [ ] **Step 6: Build clean** — `cd lean && lake build`: success, zero warnings, zero `sorry`.

- [ ] **Step 7: Commit**

```bash
git add lean/Lara/Examples/PWCompose.lean
git commit -m "theory(PW-T9): live path, failing-triangle witnesses, mid-path incomparability (#190)"
```

---

### Task 9: Wire-up and gates

**Files:**
- Modify: `lean/Lara.lean` (imports at ~line 310, commentary block at ~line 213)
- Modify: `lean/AxCheck.lean` (imports after line 81; `#print axioms` after the T6 block)
- Modify: `.github/workflows/ci.yml` (~line 183)

- [x] **Step 1: Add imports to `lean/Lara.lean`** after `import Lara.Examples.PWStructural`:

```lean
import Lara.PW.Compose
import Lara.Examples.PWCompose
```

and extend the PW commentary block (after the T6 bullet ending ~line 235) with a T9 bullet: composition is Kleisli, paths are data, transport is coherent per chosen path, direct naming costs a commuting triangle, mid-path gaps are incomparability.

- [x] **Step 2: Add to `lean/AxCheck.lean`**: the two imports, then after the T6 `#print axioms` block:

```lean
-- PW-T9 (Lara.PW.Compose): exact structural-path composition — Kleisli
-- translation laws, bridge composition, path transport, the commuting
-- triangle, and Admits composition with explicit intermediate worlds.
#print axioms Lara.PW.trTerm_comp
#print axioms Lara.PW.trTerms_comp
#print axioms Lara.PW.trAtom_comp
#print axioms Lara.PW.trAtoms_comp
#print axioms Lara.PW.trAtom_comp_none_left
#print axioms Lara.PW.trAtom_comp_none_mid
#print axioms Lara.PW.trPat_comp
#print axioms Lara.PW.trPats_comp
#print axioms Lara.PW.trAPat_comp
#print axioms Lara.PW.trAPats_comp
#print axioms Lara.PW.trSubst_comp
#print axioms Lara.PW.trQuestion_comp
#print axioms Lara.PW.trQuestions_comp
#print axioms Lara.PW.trRule_comp
#print axioms Lara.PW.trSupport_comp
#print axioms Lara.PW.trSupportList_comp
#print axioms Lara.PW.trSupportDis_comp
#print axioms Lara.PW.support_transport_comp
#print axioms Lara.PW.BridgePath.trans_eq_compose
#print axioms Lara.PW.path_support_transport
#print axioms Lara.PW.Commutes.of_maps_eq
#print axioms Lara.PW.direct_transport_agrees
#print axioms Lara.PW.commutes_on_rules
#print axioms Lara.PW.commutes_on_leaves
#print axioms Lara.PW.admits_comp
#print axioms Lara.PW.admits_comp_transport
#print axioms Lara.PW.admits_iff_of_commutes

-- PW-T9 examples (Lara.Examples.PWCompose)
#print axioms Lara.Examples.PW.Compose.ren_path_trans
#print axioms Lara.Examples.PW.Compose.ren_path_transport
#print axioms Lara.Examples.PW.Compose.direct_ne_composed_support
#print axioms Lara.Examples.PW.Compose.direct_ne_composed_claim
#print axioms Lara.Examples.PW.Compose.mid_path_out_of_vocabulary
#print axioms Lara.Examples.PW.Compose.mid_path_translationUndefined
```

(Adjust for any theorem renamed during implementation; the coverage script in Step 4 is the completeness check.)

- [x] **Step 3: Add coverage enforcement** — in `.github/workflows/ci.yml`, extend the `check-axcheck-coverage.py` file list (~line 183) with:

```
            Lara/PW/Compose.lean \
            Lara/Examples/PWCompose.lean \
```

(The pre-existing PW modules are not in the list; adding only the new ones matches the list's additive history and keeps this PR's footprint minimal.)

- [x] **Step 4: Run all gates and confirm output**

```bash
cd lean && lake build
# Expected: build succeeds, no warnings.
cd lean && python3 ../scripts/check-axcheck-coverage.py AxCheck.lean \
  Lara/PW/Compose.lean Lara/Examples/PWCompose.lean
# Expected: "AxCheck coverage passed (N declarations)."
set -o pipefail; cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh
# Expected: passes — every theorem within {propext, Classical.choice, Quot.sound},
# no sorryAx, no rogue axiom.
```

- [x] **Step 5: Commit**

```bash
git add lean/Lara.lean lean/AxCheck.lean .github/workflows/ci.yml
git commit -m "theory(PW-T9): wire Compose modules into library root and axiom gates (#190)"
```

---

### Task 10: Freeze record and cross-references

**Files:**
- Create: `docs/theory-pw-t9-path-composition.md`
- Modify: `docs/paper-lean-name-map.md` (append §PW-T9, following §PW-T6's table format)
- Modify: `docs/theory-pw-t6-structural-transport.md` (limitation 4, ~line 203)

- [ ] **Step 1: Write `docs/theory-pw-t9-path-composition.md`** following the T6 doc's structure (status banner with date/issue/tracker; intended readers; then sections). Required content:

1. **What T9 froze**: composition is Kleisli (`SymMap.comp`, first leg first, matching the design's `τ_d∘τ_b`); the composed-domain law is a theorem shape (`trX_comp` in bind form) rather than a definition; paths are first-class data (`BridgePath`, `Type 1` because intermediate environments are constructor-quantified); the composite of a path is the fold `BridgePath.compose` with `StructuralBridge.refl` at `nil`.
2. **Theorem table** (Result → Declaration), covering every declaration from Task 9's AxCheck block.
3. **The free corners**: `commutes_on_rules` / `commutes_on_leaves` — `rule_ok`'s pinning of the target policy means direct-vs-composed disagreement *cannot* live on policy rules at a shared identifier; the witnesses live on leaf renaming and off-policy claim vocabulary, and that is why the two `Commutes` fields are exactly the non-free content.
4. **Intermediate-world dependence**: how it is stated (per-path theorems; `support_transport_comp` and `admits_comp_transport` return the intermediate judgments; `trans_eq_compose` is the "depends on the path only through its composite" law).
5. **Boundary** (issue #190's): no result generalizes to approximation bridges — composition for those needs separate domains, observables, comparison spaces, and error/convergence laws, deferred per the design's Composition section.
6. **Known limitations**: (a) no categorical equalities between bridges (`comp` associativity/unit as bridge equalities unstated; `trans_eq_compose` carries the semantic content — add laws only when a client needs equalities of bridges themselves); (b) inherits T6 limitations 1, 2, 5 (bridge-global functional translation, total leaf maps, frozen question keys) — a path of bridges relaxes none of them; (c) status preservation along paths is T8 composed with T9, not proved here.

- [ ] **Step 2: Update `docs/paper-lean-name-map.md`** — append a §PW-T9 block mapping the design's T9 names to the declarations (same two-column format as §PW-T6).

- [ ] **Step 3: Update T6's limitation 4** in `docs/theory-pw-t6-structural-transport.md` (~line 203): keep the limitation text, append "Discharged by T9 (#190): see `docs/theory-pw-t9-path-composition.md`."

- [ ] **Step 4: Commit**

```bash
git add docs/theory-pw-t9-path-composition.md docs/paper-lean-name-map.md docs/theory-pw-t6-structural-transport.md
git commit -m "docs(PW-T9): freeze record, name map, T6 limitation pointer (#190)"
```

---

### Task 11: PR and session close-out

- [ ] **Step 1: Re-run all three gates** (Task 9 Step 4 commands) on the final tree; all must pass.

- [ ] **Step 2: Push and open the PR**

```bash
git push -u origin theory/pw-t9-path-composition
gh pr create --title "theory(PW-T9): prove exact structural-path composition (#190)" --body "..."
```

PR body: map each of issue #190's four acceptance bullets to its theorem(s):
- *Lean proves path transport for exact structural bridges* → `path_support_transport`, `support_transport_comp`, live at `ren_path_transport`.
- *Direct-versus-composed equality requires an explicit commuting triangle* → `direct_transport_agrees` (sufficiency) + `direct_ne_composed_support` / `direct_ne_composed_claim` (necessity witnesses) + `commutes_on_rules` / `commutes_on_leaves` (the free corners) + `admits_iff_of_commutes` (the relation corner at the checker-tied `Admits` level).
- *Missing intermediate translations fail as incomparability rather than a local status* → `trAtom_comp_none_mid`, `mid_path_translationUndefined`.
- *No result is generalized to approximation bridges* → boundary section of `docs/theory-pw-t9-path-composition.md`; no declaration mentions approximation.
Close with `Fixes #190` and the session link.

- [ ] **Step 3: Run `/research-manager`** — this session introduces a theory change (T9 mechanized), which crosses the ARA threshold in CLAUDE.md.

---

## How to check the end result

**Mechanical gates (all must pass, same commands CI runs):**

| Check | Command | Expected |
|---|---|---|
| Build | `cd lean && lake build` | success, zero warnings |
| Axiom audit | `set -o pipefail; cd lean && lake env lean AxCheck.lean \| ../scripts/check-axioms.sh` | pass; standard trio only, no `sorryAx` |
| AxCheck coverage | `cd lean && python3 ../scripts/check-axcheck-coverage.py AxCheck.lean Lara/PW/Compose.lean Lara/Examples/PWCompose.lean` | "coverage passed" |
| CI | PR checks | green |

**Acceptance-criteria audit (issue #190, bullet by bullet):** the PR-body mapping in Task 11 Step 2 is the checklist; each bullet must point at a named, `#print axioms`-audited declaration or (for the boundary bullet) at the freeze doc plus the absence of any approximation-facing declaration.

**Discipline audit:**
- `git diff main -- lean/Lara/PW/Translation.lean lean/Lara/PW/Structural.lean lean/Lara/Support.lean` is empty — T9 only adds modules that import; no frozen T6/local definition changed.
- The new modules contain no `String`-typed reasoning outside the established `SymMap` boundary and no new axioms.
- `plans/2026-09-03-theory-pw-t9-path-composition.md` (this file) is deleted in the PR once executed, with durable content living in `docs/theory-pw-t9-path-composition.md` (CLAUDE.md's `plans/` rule).

**Semantic sanity (spot checks a reviewer should be able to do):**
- `ren_path_transport` is a *computed* twice-renamed derivation — inspect `wRenTgt2` and confirm both leaf renamings and both predicate renamings actually happened (`ren_path_trans` asserts `wRenTgt2 ≠ wRenTgt`).
- The two `direct_ne_composed_*` witnesses each satisfy all three bridge-contract clauses (no vacuous cheat beyond the deliberately empty policy) while both transports succeed — confirming the commuting triangle carries real content.
- `support_transport_comp`'s statement mentions the intermediate environment's judgment (`HasSupport … Pi' Gamma' CertOk' w' C' O`) — the intermediate-world dependence is in the statement, not the proof.

---

## Implementation Tasks
Synthesized from the review's findings. Each task derives from a specific
finding. Run with Claude Code or Codex; checkbox as you ship.

**Sequencing (decided at review):** land as **two PRs**, split by time rather than
by file — the parallelization analysis found this is one sequential lane through
one module, so a file-level split would only create conflicts.

- **PR 1 (foundation):** T1, T2, T9, T10, T15, T17, T19 plus original Tasks 1-5
  (Kleisli laws, `StructuralBridge.comp`, `BridgePath`, path transport) and T6,
  T7, T12, T16 witnesses. Gives a green, reviewable base.
- **PR 2 (triangle):** T3, T4, T5, T8, T11, T13, T14 (path-level `Commutes`, the
  accepted-relation clause, and the triangle witnesses), then original Task 10's
  freeze record and T20. `docs/theory-pw-t9-path-composition.md` is written **once**,
  here, with the corrected `Commutes` characterization already settled — and the
  plan retirement (T19's `git rm`) moves to this PR.

T1 and T2 are compile-blocking; do them first regardless.

- [x] **T1 (P1, human: ~20min / CC: ~3min)** — translation-laws — Replace `Option.some_bind`/`none_bind`/`bind_eq_some` with `bind_some`/`bind_none`/`bind_eq_some_iff`
  - Surfaced by: Code Quality, Issue 5 — verified by running `lake env lean` on v4.32.0; all three are `Unknown constant` errors
  - Files: lines 45, 150, 168, 266, 325, 329, 333, 334, 368, 371, 456, 550, 577, 595, 641
  - Verify: `~/.elan/bin/lake build`
- [x] **T2 (P1, human: ~10min / CC: ~2min)** — commuting-triangle — Add `.symm` to the final `congrArg` in `commutes_on_rules` (579) and `commutes_on_leaves` (597)
  - Surfaced by: Outside voice, Issue 13 — `hPi₃` yields `some r₂ = some r₃` against a goal of `some r₃ = some r₂`
  - Verify: `~/.elan/bin/lake build`
- [ ] **T3 (P1, human: ~2 days / CC: ~2h)** — commuting-triangle — Restate `Commutes` as a path-level record against `P.compose`/`P.trans`; binary case becomes a corollary
  - Surfaced by: Outside voice, Issue 15 (cross-model tension, resolved toward codex) — `BridgePath` is n-ary, the triangle is binary-only
  - Files: `lean/Lara/PW/Compose.lean`
- [ ] **T4 (P1, human: ~1-2 days / CC: ~2h)** — admits — Add the accepted-relation composition clause and strengthen `admits_comp` to the `↔` form
  - Surfaced by: Outside voice, Issue 14 — `Outer.lean:92-96` gives `A_b = R_b ∩ accept_b`; `Admits` is only the `accept` conjunct
  - Files: `lean/Lara/PW/Compose.lean`
- [ ] **T5 (P1, human: ~4h / CC: ~30min)** — witnesses — `bridgeRenDirect` + positive `Commutes` + `direct_transport_agrees` landing on `wRenTgt2`
  - Surfaced by: Test review, Issue 9 — the triangle has two counterexamples and zero positive witnesses
- [x] **T6 (P1, human: ~3h / CC: ~25min)** — witnesses — Compose `bridgeCert` so `StructuralBridge.comp.cert_ok` runs non-vacuously
  - Surfaced by: Test review, Issue 8 — `certRen = False` (`PWStructural.lean:151`) makes composed `cert_ok` vacuous everywhere
- [x] **T7 (P1, human: ~4h / CC: ~30min)** — witnesses — Make `gapSym` a real `StructuralBridge` inside a `BridgePath`
  - Surfaced by: Outside voice, Issue 16 — the mid-path witness contains no path and no bridge
- [ ] **T8 (P2, human: ~1h / CC: ~10min)** — commuting-triangle — `Commutes.leafMap_eq` / `predMap_eq`; correct the "strictly weaker" claim at line 25
  - Surfaced by: Architecture, Issue 1 — `Translation.lean:172` and `:74-78` force pointwise `leafMap`/`predMap` equality
- [ ] **T9 (P2, human: ~30min / CC: ~5min)** — translation-laws — Add `SymMap.id_comp` / `comp_id`; narrow the scope guard at line 29
  - Surfaced by: Code Quality, Issue 6 — verified `id_comp` needs `funext`, and it is the direction singleton paths need
- [ ] **T10 (P2, human: ~20min / CC: ~5min)** — admits — Cut `admits_comp_transport` and its AxCheck line
  - Surfaced by: Architecture, Issue 3 — 9-conjunct existential serving no acceptance bullet
- [ ] **T11 (P2, human: ~1 day / CC: ~50min)** — witnesses — Witness `support_transport_comp`, `commutes_on_rules`, `commutes_on_leaves`, `admits_comp`, `admits_iff_of_commutes`
  - Surfaced by: Test review, Issue 10 — five unwitnessed theorems including "the binary heart of T9"
- [x] **T12 (P2, human: ~2h / CC: ~15min)** — witnesses — Computational facts for composed `trSubst` / `trQuestions` / `trSupportDis` on non-empty inputs
  - Surfaced by: Test review, Issue 11 — `wRen` has `θ`/`D` empty (`:190`), `ruleRen.questions` empty (`:113`)
- [ ] **T13 (P2, human: ~3h / CC: ~25min)** — witnesses — Add `HasSupport` judgments to both `direct_ne_composed_*` theorems
  - Surfaced by: Outside voice, Issue 17 — docstrings claim "both derivations check"; no `HasSupport` in either type
- [ ] **T14 (P2, human: ~2h / CC: ~20min)** — witnesses — Length-3 `BridgePath` witness (third leg may be `StructuralBridge.refl`)
  - Surfaced by: TODO 3 — path-level `Commutes` should be shown beyond the binary case it generalizes
- [x] **T15 (P2, human: ~1h / CC: ~15min)** — translation-laws — Rewrite the `trSupport_comp` `.inst` arm as explicit nested cases; delete the line-284 note
  - Surfaced by: Performance, Issue 12 — 27-branch chained tactic against house style (`Structural.lean:129-141`)
- [x] **T16 (P2, human: ~30min / CC: ~5min)** — witnesses — Add `ren2_conclusion`; use T6's `ren_transport` shape
  - Surfaced by: Code Quality, Issue 7 — diverges from `PWStructural.lean:265-282` at the plan's own flagged-fragile spot
- [x] **T17 (P2, human: ~1h / CC: ~15min)** — documentation — Four ASCII diagrams (path/fold ×2, triangle, mid-path gap)
  - Surfaced by: Architecture, Issue 4 — zero diagrams across 1188 lines
- [ ] **T18 (P2, human: ~45min / CC: ~10min)** — documentation — Relabel the "free corners" framing at lines 26, 96 and the Task 10 outline
  - Surfaced by: Architecture, Issue 2 — the two lemmas are cited in no proof and discharge no part of `Commutes`
- [x] **T19 (P2, human: ~15min / CC: ~3min)** — process — Add a Task 11 step that `git rm`s this plan, after Task 10's docs commit and before the PR push
  - Surfaced by: Outside voice, Issue 18 — the discipline audit at line 1182 requires a deletion no task performs
- [ ] **T20 (P3, human: ~30min / CC: ~10min)** — process — Open follow-up issues: traversal refactor of the `tr*` lifts; witnesses for `trAtom_comp_none_left` and the `SymMap` unit laws
  - Surfaced by: TODO 2 and TODO 3 residue — CLAUDE.md requires deferrals tracked as GitHub issues

---

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | `/codex review` | Independent 2nd opinion | 0 | — | — |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | CLEAR (PLAN) | 18 issues, 0 critical gaps |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | — |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | — |

Section breakdown: Architecture 4, Code Quality 3, Tests 4, Performance 1,
Outside voice 6. All 18 accepted; 20 implementation tasks emitted.

Test coverage before review: 13/29 theorem paths witnessed (45%), 5 silent-failure
paths. After the accepted findings land: 29/29 addressed, 0 silent-failure paths.

**CODEX:** Outside voice ran (codex, `model_reasoning_effort=high`, read-only) and
found 6 problems the four review sections missed — the absent relation-coherence
theorem (`Admits` is only the `accept` half of `A_b = R_b ∩ accept_b`), binary-only
triangle against an n-ary `BridgePath`, two backwards proofs that do not compile,
a mid-path witness containing no path or bridge, two counterexamples whose
docstrings overclaim checked transport, and a close-out that cannot satisfy its own
discipline audit. All six independently verified and accepted.

**CROSS-MODEL:** One tension, on the `Commutes` redesign. This review kept the
binary record and deferred restructuring to a follow-up issue; codex argued for one
path-level record with three clauses now. Resolved toward codex (Issue 15A) —
accepting the accepted-relation clause (14A) already pays most of the restructuring
cost, so deferring would mean re-freezing the same definitions twice. The deferred
TODO 1 is superseded. Both reviews independently identified `Commutes` as the weak
point, from different directions: this review from its strength (it collapses to
near map-equality), codex from its scope (binary against an n-ary path type).

**VERDICT:** ENG CLEARED — architecture, code quality, tests, and performance
reviewed; outside voice absorbed. CEO and Design reviews not run and not required
for a metatheory plan with no product or UI surface.

NO UNRESOLVED DECISIONS
