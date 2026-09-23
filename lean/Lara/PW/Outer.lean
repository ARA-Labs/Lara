/-
PW0 — the typed possible-world outer model.

The design adds an
outer comparison layer over unchanged local Lara judgments. This module owns
the *generic* half: a frame of scientific contexts, per-context worlds and
queries, bridges with candidate and accepted relations and typed partial claim
translations; the many-sorted outer formula language; satisfaction; the typed
normality laws (T2); the valuation coherence side conditions; and valuation
congruence — the induction that makes T4 a one-line instantiation in
`Lara.PW.Instance`.

The model is deliberately factored as frame + valuation. The design's T4
instantiates one parameterized model twice, `M[V := V^src]` and
`M[V := V^cmp]`; making the valuation a parameter of `Sat` rather than a frame
field is that parameterization, stated once instead of duplicating the model.

Nothing here mentions a checked program, a compiled framework, or a status
computation: the frame is abstract, and the Lara instantiation lives in
`Lara.PW.Instance`. That separation is gate 1 of PW0 — the wrapper must leave
every local judgment unchanged, and a module that cannot name them cannot
change them.

Translations (`translate`) are bridge-global and partial, the design's
explicitly chosen restriction; edge-dependent translation (configurations) is
the documented fallback and is out of PW0's scope. The primitive modalities do
not translate their operands — translation appears only in derived formulas,
which is what keeps each accepted relation formula-independent and hence the
logic normal (T2).

No Mathlib; core Lean 4 only. In particular `by_contra` is unavailable: the
house idiom for a classical contradiction is `Classical.byContradiction`
(see `Lara/Grounded.lean:288`).
-/

import Lara.Grounded

namespace Lara.PW

open Lara.Grounded (Status)

/-- Index of a model with exactly one scientific context.

Declared rather than spelled `Unit`: inside `namespace Lara.*` the identifier
`Unit` resolves to `Lara.Unit`, the *raw program unit*, and the capture is
silent — it typechecks at the definition site and only surfaces as a
misleading error several definitions later. A named index also states the
intent ("exactly one context") where it is used. -/
inductive OneCtx | it
deriving DecidableEq, Repr

/-- Index of a model with exactly one bridge. Same reason as `OneCtx`. -/
inductive OneBridge | it
deriving DecidableEq, Repr

/-- **The outer frame.** `K` is the type of scientific contexts (the design's
finite `K`; PW0 imposes no finiteness on `K` at all — satisfaction does not
need it, and the finiteness the executable layer needs is on the *candidate
world list of one bridge at one world*, which `Lara.PW.crossCompare` takes as
an explicit `List` input rather than reading off the frame). Each context has
its own worlds and queries; a bridge `b : B` runs from `src b` to `tgt b` and
carries a
candidate relation `R`, a checked applicability judgment `accept`, and a typed
partial claim translation `translate`.

`accept` is an arbitrary `Prop`: PW0 posits *no* connection between it and any
checker, certificate, or soundness condition. Supplying that connection is the
structural-bridge work of T6, deliberately out of scope here (see
`docs/theory-pw0-outer-model.md`). -/
structure Frame where
  /-- scientific contexts -/
  K : Type
  /-- structural claim-comparison bridges -/
  B : Type
  /-- bridge source context -/
  src : B → K
  /-- bridge target context -/
  tgt : B → K
  /-- admissible local worlds of a context -/
  World : K → Type
  /-- well-formed queries of a context -/
  Query : K → Type
  /-- candidate comparison relation of a bridge -/
  R : (b : B) → World (src b) → World (tgt b) → Prop
  /-- checked applicability judgment for a candidate edge -/
  accept : (b : B) → World (src b) → World (tgt b) → Prop
  /-- bridge-global typed partial claim translation -/
  translate : (b : B) → Query (src b) → Option (Query (tgt b))

namespace Frame

/-- **The accepted edge relation** `A_b = R_b ∩ accept_b`. Fixed per bridge and
independent of the formula being evaluated — the condition that supports
normal modal logic (T2). -/
def A (F : Frame) (b : F.B) (w : F.World (F.src b)) (v : F.World (F.tgt b)) : Prop :=
  F.R b w v ∧ F.accept b w v

end Frame

/-- **The selected local observation valuation** `V_w`: which of the four Lara
statuses a query has at a world. `Prop`-valued so the *relational* source
observation (`Compile.SrcStatus`) and the *functional* compiled observation
(`Grounded.statusC`) both fit; their agreement is T1, proved in
`Lara.PW.Instance`, not assumed here.

Being `Prop`-valued, the type alone does **not** say a query has at most one
status. `Valuation.Functional` / `Valuation.Total` below name that side
condition, and `Lara.PW.Instance` discharges both. -/
def Valuation (F : Frame) : Type :=
  {κ : F.K} → F.World κ → F.Query κ → Status → Prop

/-- **The typed outer language** (design §Typed Outer Language). One formula
sort per context; the modalities change sort along a bridge. Status atoms,
`⊤`, `¬`, `∧`, `[b]`, `⟨b⟩` — exactly the design grammar, nothing more:
no named-world operator, no dynamic operator, no approximation syntax. -/
inductive Form (F : Frame) : F.K → Type where
  /-- `Status_s(c)` — the abbreviations `Justified(c)`, `Gap(c)`, … are this
  constructor at the four `Status` values -/
  | status {κ : F.K} (s : Status) (c : F.Query κ) : Form F κ
  | top {κ : F.K} : Form F κ
  | neg {κ : F.K} (φ : Form F κ) : Form F κ
  | conj {κ : F.K} (φ ψ : Form F κ) : Form F κ
  | box (b : F.B) (φ : Form F (F.tgt b)) : Form F (F.src b)
  | dia (b : F.B) (φ : Form F (F.tgt b)) : Form F (F.src b)

namespace Form

/-- Derived implication, for stating typed K. -/
def imp {F : Frame} {κ : F.K} (φ ψ : Form F κ) : Form F κ :=
  .neg (.conj φ (.neg ψ))

end Form

/-- **Satisfaction**, parameterized by the valuation (see module header: this
parameter *is* the design's `M[V := …]` instantiation). The modal clauses
quantify over accepted target worlds and do not translate their operands.

The **formula precedes the world**, which is the reverse of the usual `w ⊨ φ`
reading. This is forced, not stylistic: with the world first, the context
index `κ` is not determined by any earlier argument (a world does not name its
context), so the `box`/`dia` arms fail to elaborate —

    Type mismatch: Form.box b φ has type Form ?m (Frame.src ?m b)
    but is expected to have type Form F ?m

Naming the index explicitly (`∀ {κ : F.K}, …`) or making it a normal explicit
binder both fail the same way. Putting the formula first lets the match refine
`κ` from the constructor. The prose notation `w ⊨ φ` corresponds to
`Sat F V φ w` here. -/
def Sat (F : Frame) (V : Valuation F) : {κ : F.K} → Form F κ → F.World κ → Prop
  | _, .status s c, w => V w c s
  | _, .top, _ => True
  | _, .neg φ, w => ¬ Sat F V φ w
  | _, .conj φ ψ, w => Sat F V φ w ∧ Sat F V ψ w
  | _, .box b φ, w => ∀ v, F.A b w v → Sat F V φ v
  | _, .dia b φ, w => ∃ v, F.A b w v ∧ Sat F V φ v

/-! ### T2 — typed normality

The minimum valid laws for each bridge: typed K, necessitation, duality, top
preservation, finite-meet preservation. No stronger frame axiom (T, 4, B, D, 5)
is assumed or proved — those belong only to bridges whose accepted relations
satisfy the corresponding relational laws, none of which PW0 posits. That
negative half is not left as a comment, for any of the five:
`Examples.PW.sat_T_fails`, `sat_D_fails`, `sat_B_fails` and `sat_5_fails`
refute T, D, B and 5 on one PW0-legal frame, and `sat_4_fails` refutes 4 on a
three-world chain (the two-world frame validates 4 vacuously), so "normal,
and no more" is a theorem. -/

/-- Semantic reading of the derived implication. Classical (`by_cases` from
core `Init`), which is why the audit reports the standard trio on this lemma
and on `sat_K`, which consumes it. Most of the T2 block is *not* classical:
`sat_nec`, `sat_box_top` and `sat_box_conj` depend on no axioms at all, and
`sat_dia_iff_not_box_neg` reports the trio for a different reason
(`Classical.byContradiction`, not `by_cases`). -/
theorem sat_imp (F : Frame) (V : Valuation F) {κ : F.K}
    (w : F.World κ) (φ ψ : Form F κ) :
    Sat F V (φ.imp ψ) w ↔ (Sat F V φ w → Sat F V ψ w) := by
  show ¬ (Sat F V φ w ∧ ¬ Sat F V ψ w) ↔ _
  constructor
  · intro h hφ
    by_cases hψ : Sat F V ψ w
    · exact hψ
    · exact absurd ⟨hφ, hψ⟩ h
  · rintro h ⟨hφ, hnψ⟩
    exact hnψ (h hφ)

/-- **T2, typed K.** `[b](φ → ψ) → ([b]φ → [b]ψ)`. -/
theorem sat_K (F : Frame) (V : Valuation F) (b : F.B)
    (w : F.World (F.src b)) (φ ψ : Form F (F.tgt b))
    (himp : Sat F V (.box b (φ.imp ψ)) w) (hφ : Sat F V (.box b φ) w) :
    Sat F V (.box b ψ) w := by
  intro v hA
  exact (sat_imp F V v φ ψ).mp (himp v hA) (hφ v hA)

/-- **T2, typed necessitation.** A formula valid at every target world is
boxed at every source world. -/
theorem sat_nec (F : Frame) (V : Valuation F) (b : F.B)
    (φ : Form F (F.tgt b)) (h : ∀ v, Sat F V φ v) :
    ∀ w, Sat F V (.box b φ) w :=
  fun _ v _ => h v

/-- **T2, duality.** `⟨b⟩φ ↔ ¬[b]¬φ`. Classical in the `mpr` direction, via
`Classical.byContradiction` — `by_contra` is a Mathlib tactic and this
development has no Mathlib. -/
theorem sat_dia_iff_not_box_neg (F : Frame) (V : Valuation F) (b : F.B)
    (w : F.World (F.src b)) (φ : Form F (F.tgt b)) :
    Sat F V (.dia b φ) w ↔ Sat F V (.neg (.box b (.neg φ))) w := by
  show (∃ v, F.A b w v ∧ Sat F V φ v) ↔ ¬ ∀ v, F.A b w v → ¬ Sat F V φ v
  constructor
  · rintro ⟨v, hA, hv⟩ hall
    exact hall v hA hv
  · intro h
    exact Classical.byContradiction fun hne =>
      h (fun v hA hv => hne ⟨v, hA, hv⟩)

/-- **T2, top preservation.** `[b]⊤` holds everywhere. -/
theorem sat_box_top (F : Frame) (V : Valuation F) (b : F.B)
    (w : F.World (F.src b)) : Sat F V (.box b .top) w :=
  fun _ _ => trivial

/-- **T2, finite-meet preservation.** `[b](φ ∧ ψ) ↔ [b]φ ∧ [b]ψ`. -/
theorem sat_box_conj (F : Frame) (V : Valuation F) (b : F.B)
    (w : F.World (F.src b)) (φ ψ : Form F (F.tgt b)) :
    Sat F V (.box b (.conj φ ψ)) w ↔
      Sat F V (.conj (.box b φ) (.box b ψ)) w := by
  constructor
  · intro h
    exact ⟨fun v hA => (h v hA).1, fun v hA => (h v hA).2⟩
  · rintro ⟨h₁, h₂⟩ v hA
    exact ⟨h₁ v hA, h₂ v hA⟩

/-! ### The T4 core — valuation congruence

The design's T4 compares one parameterized model under two valuations. The
generic content is this induction; the Lara instantiation (`Lara.PW.Instance`)
supplies the atomic case as T1. Stated over the same frame, so the accepted
relations are literally shared — the modal cases move across for free, which
is what makes T4 "a genuine lifting theorem rather than definitional
duplication" (gate 2).

Honest scope: this is a routine structural induction, and its content is that
satisfaction is extensional in the atomic valuation. It is an integration
theorem, not an independent Lara result — the substantive theorem is T1. -/

/-- Two valuations that agree at every world and atom satisfy the same
formulas. The induction is on the formula with the world abstracted: each case
returns a function of `w`, because the modal cases recurse at a *different*
world. -/
theorem sat_congr (F : Frame) (V₁ V₂ : Valuation F)
    (h : ∀ (κ : F.K) (w : F.World κ) (c : F.Query κ) (s : Status),
      V₁ w c s ↔ V₂ w c s) :
    ∀ {κ : F.K} (φ : Form F κ) (w : F.World κ),
      Sat F V₁ φ w ↔ Sat F V₂ φ w := by
  intro κ φ
  induction φ with
  | status s c => exact fun w => h _ w c s
  | top => exact fun _ => Iff.rfl
  | neg φ ih => exact fun w => not_congr (ih w)
  | conj φ ψ ihφ ihψ => exact fun w => and_congr (ihφ w) (ihψ w)
  | box b φ ih =>
    intro w
    constructor
    · intro hs v hA
      exact (ih v).mp (hs v hA)
    · intro hs v hA
      exact (ih v).mpr (hs v hA)
  | dia b φ ih =>
    intro w
    constructor
    · rintro ⟨v, hA, hv⟩
      exact ⟨v, hA, (ih v).mp hv⟩
    · rintro ⟨v, hA, hv⟩
      exact ⟨v, hA, (ih v).mpr hv⟩

/-! ### Valuation coherence — the four-state status is a function, not a set

`Valuation` is `Prop`-valued so the relational source observation and the
functional compiled one both fit (see `Valuation`). Nothing in that *type*
says a query has at most one status, so a generic model satisfying every T2
law can still make `Justified(c) ∧ Defeated(c)` true. A model in which the
four-state status is not a function is not a Lara model.

These predicates name the missing side condition. `Lara.PW.Instance`
discharges both for `V^src` and `V^cmp`, and the two discharges are *not*
symmetric: `cmpVal` is functional because it is an equation against a total
function, while `srcVal` is a relation that is functional **only through T1**.
That asymmetry is the gate-2 independence, made visible. -/

/-- At most one status per query per world. -/
def Valuation.Functional {F : Frame} (V : Valuation F) : Prop :=
  ∀ {κ : F.K} (w : F.World κ) (c : F.Query κ) (s₁ s₂ : Status),
    V w c s₁ → V w c s₂ → s₁ = s₂

/-- At least one status per query per world. -/
def Valuation.Total {F : Frame} (V : Valuation F) : Prop :=
  ∀ {κ : F.K} (w : F.World κ) (c : F.Query κ), ∃ s, V w c s

/-- **No world reports two statuses for one claim.** Under a functional
valuation, distinct statuses of the same query are jointly unsatisfiable — the
modal-layer counterpart of the four-state status being a function. -/
theorem not_sat_two_status {F : Frame} {V : Valuation F}
    (hV : V.Functional) {κ : F.K} (w : F.World κ) (c : F.Query κ)
    {s₁ s₂ : Status} (hne : s₁ ≠ s₂) :
    ¬ Sat F V (.conj (.status s₁ c) (.status s₂ c)) w := by
  rintro ⟨h₁, h₂⟩
  exact hne (hV w c s₁ s₂ h₁ h₂)

/-- Under a total valuation every query has *some* status at every world. -/
theorem exists_status_of_total {F : Frame} {V : Valuation F}
    (hV : V.Total) {κ : F.K} (w : F.World κ) (c : F.Query κ) :
    ∃ s, Sat F V (.status s c) w :=
  hV w c

end Lara.PW
