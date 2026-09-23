/-
# PW — the `Query_κ` well-sortedness refinement

PW0 froze `Query_κ` as all of `Atom` and deferred the refinement to the M5
surface layer, which has since landed. This module takes the deferral:
per-context queries become **well-sorted claims over `Σ_κ`**, and the
executable layer gains a posing stage that runs *before* any world is
consulted.

**What this narrows.** `docs/theory-pw0-outer-model.md` limitation 2 states in
print that a `gap` conflates four conditions — *out of vocabulary*,
*ill-sorted*, *not posed*, and *posed but unsupported* — so a reader must not
read `⟨b⟩Gap(c)` as "the target field considered this and found it
unsupported". After this refinement:

* the two **Σ-level** conditions are removed from `gap` by construction. An
  out-of-vocabulary head and an ill-sorted argument list are not queries at
  all, so no world ever reports a status for them; `pose` separates the two
  and names the offending predicate (`queryFault`).
* the two **world-level** conditions are proved to *coincide*, and that is a
  theorem rather than an omission. Every argument an accepted unit retains is
  complete — `Compile.CheckedNode.valid` carries the empty obligation list —
  and `statusC` gaps exactly on empty complete support
  (`Grounded.statusC_gap_iff`). So `cmpStatus_gap_iff_not_addresses` reads the
  remaining `gap` off one precise condition: *the world declares no complete
  argument concluding the query*, and `not_gap_of_addresses` says nothing else
  can produce one.

PW0's separate `translationUndefined` reason splits the same way, into *outside
the bridge's symbol map* and *the target field cannot state this*, and both
halves are **located**: `vocabFault` names the first symbol the bridge cannot
carry and `queryFault` the target's offending head. `crossCompare`'s own
`translationUndefined` is unreachable past the new guard
(`crossComparePosed_ne_translationUndefined`), so the split has no live rival.

The residue is honest and recorded: separating "posed but unsupported" from
"not posed" would need `holes(P, p)` at the instance layer, which
`Consistency.completeClaimFor` deliberately does not compute (N17 point (1),
a modeling convention). `docs/theory-pw-sorted-queries.md` §4 carries it.

**What this does not change.** PW0's frame, satisfaction, `crossCompare`,
`CrossResult` and `IncomparabilityReason` are untouched: the refinement is a
new frame *builder* and a strictly earlier guard, not an edit to the frozen
contract. `sat_erase` is the conservativity theorem — on the queries PW0
already accepted, the refined model satisfies exactly the same formulas.

No Mathlib; core Lean 4 only.
-/

import Lara.PW.Instance
import Lara.PW.Compare
import Lara.PW.Translation

namespace Lara.PW.Sorted

open Lara.Support
open Lara.Grounded (Status)

/-! ## 1. Query formation

A query of a context is a claim the context's signature can state. The two
ways an atom fails that are the two Σ-level conditions PW0's `gap` absorbed,
and they are separated here — with the offending predicate named, so the
report is *located* in the same sense `Sigma.sigmaFault` is. -/

/-- Why an atom is not a well-sorted query of a signature. Exactly the two
arms of `Sigma.wsAtom`: an undeclared head is *out of vocabulary*; a declared
head whose argument list fails `expectTerms` is *ill-sorted* (which subsumes
the arity mismatch, arity being the length of the declared sort vector). -/
inductive QueryFault where
  /-- the head predicate is not declared by `Σ_κ` -/
  | undeclaredPredicate (p : PredSym)
  /-- the head is declared, but the arguments do not have its declared sorts -/
  | illSortedArguments (p : PredSym)
deriving DecidableEq

/-- The head predicate a fault is reported against. -/
def QueryFault.pred : QueryFault → PredSym
  | .undeclaredPredicate p => p
  | .illSortedArguments p => p

/-- **Classify** an atom's head: undeclared, or declared (hence any failure is
in the arguments). The split is exactly the two arms of `Sigma.wsAtom`, which
is why no third fault can appear.

`private` deliberately. This is total, so it answers `illSortedArguments` for a
perfectly well-sorted atom — a fabricated fault the type cannot prevent. It is
only meaningful under the precondition `queryFault` enforces, so the gated
report is the public one and this is a scan helper, the same treatment
`Sigma.scanSorts` gets. -/
private def faultOf (sg : Lara.Sigma.Sigma) : Atom → QueryFault
  | .atom p _ =>
    match sg.lookupPred ⟨p⟩ with
    | none => .undeclaredPredicate ⟨p⟩
    | some _ => .illSortedArguments ⟨p⟩

/-- **The located query fault**: `none` on a well-sorted atom, and otherwise
the reason it is not one. Deterministic and executable, so both runtimes would
report the same one — the discipline `Sigma.sigmaFault` already follows for
signature well-formedness. -/
def queryFault (sg : Lara.Sigma.Sigma) (a : Atom) : Option QueryFault :=
  if Lara.Sigma.wsAtom sg a = true then none else some (faultOf sg a)

/-- No fault is exactly well-sortedness — the refinement reuses the *existing*
`Sigma` judgment rather than introducing a second one. -/
theorem queryFault_eq_none_iff (sg : Lara.Sigma.Sigma) (a : Atom) :
    queryFault sg a = none ↔ Lara.Sigma.WellSorted sg a := by
  unfold queryFault Lara.Sigma.WellSorted
  by_cases h : Lara.Sigma.wsAtom sg a = true <;> simp [h]

/-- A fault is **located**: it names the atom's own head predicate, so a
report traces back to the authored claim. Private with `faultOf`;
`queryFault_pred` is the public form of the same fact. -/
private theorem faultOf_pred (sg : Lara.Sigma.Sigma) (p : String) (ts : Terms) :
    (faultOf sg (.atom p ts)).pred = ⟨p⟩ := by
  cases hsig : sg.lookupPred ⟨p⟩ <;> simp [faultOf, QueryFault.pred, hsig]

theorem queryFault_pred (sg : Lara.Sigma.Sigma) (p : String) (ts : Terms)
    {f : QueryFault} (h : queryFault sg (.atom p ts) = some f) :
    f.pred = ⟨p⟩ := by
  unfold queryFault at h
  by_cases hw : Lara.Sigma.wsAtom sg (.atom p ts) = true
  · simp [hw] at h
  · simp [hw] at h
    subst h
    exact faultOf_pred sg p ts

/-- An undeclared head is not well-sorted: the `none` arm of `wsAtom`. -/
theorem not_wellSorted_of_lookupPred_none (sg : Lara.Sigma.Sigma)
    (p : String) (ts : Terms) (h : sg.lookupPred ⟨p⟩ = none) :
    ¬ Lara.Sigma.WellSorted sg (.atom p ts) := by
  simp [Lara.Sigma.WellSorted, Lara.Sigma.wsAtom, h]

/-- **Out of vocabulary**, pinned to exactly its condition. -/
theorem queryFault_undeclaredPredicate_iff (sg : Lara.Sigma.Sigma)
    (p : String) (ts : Terms) :
    queryFault sg (.atom p ts) = some (.undeclaredPredicate ⟨p⟩) ↔
      sg.lookupPred ⟨p⟩ = none := by
  constructor
  · intro h
    by_cases hw : Lara.Sigma.wsAtom sg (.atom p ts) = true
    · simp [queryFault, hw] at h
    · simp [queryFault, hw] at h
      cases hsig : sg.lookupPred ⟨p⟩ with
      | none => rfl
      | some sig => simp [faultOf, hsig] at h
  · intro h
    have hw : Lara.Sigma.wsAtom sg (.atom p ts) ≠ true := by
      simpa [Lara.Sigma.WellSorted] using
        not_wellSorted_of_lookupPred_none sg p ts h
    simp [queryFault, hw, faultOf, h]

/-- **Ill-sorted**, pinned to exactly its condition: the head *is* declared and
the argument list fails its declared sort vector (arity included — arity is the
length of that vector). -/
theorem queryFault_illSortedArguments_iff (sg : Lara.Sigma.Sigma)
    (p : String) (ts : Terms) :
    queryFault sg (.atom p ts) = some (.illSortedArguments ⟨p⟩) ↔
      ∃ sig, sg.lookupPred ⟨p⟩ = some sig ∧
        Lara.Sigma.expectTerms sg sig.args ts = false := by
  constructor
  · intro h
    by_cases hw : Lara.Sigma.wsAtom sg (.atom p ts) = true
    · simp [queryFault, hw] at h
    · simp [queryFault, hw] at h
      cases hsig : sg.lookupPred ⟨p⟩ with
      | none => simp [faultOf, hsig] at h
      | some sig =>
        refine ⟨sig, rfl, ?_⟩
        simpa [Lara.Sigma.wsAtom, hsig] using hw
  · rintro ⟨sig, hsig, hexp⟩
    have hw : Lara.Sigma.wsAtom sg (.atom p ts) ≠ true := by
      simp [Lara.Sigma.wsAtom, hsig, hexp]
    simp [queryFault, hw, faultOf, hsig]

/-- The two faults **exhaust** ill-formedness: an atom that is not a query
fails for one of exactly these two reasons, and there is no third. -/
theorem not_wellSorted_iff_exists_fault (sg : Lara.Sigma.Sigma) (a : Atom) :
    ¬ Lara.Sigma.WellSorted sg a ↔ ∃ f, queryFault sg a = some f := by
  rw [← queryFault_eq_none_iff]
  cases h : queryFault sg a with
  | none => simp
  | some f => simp

/-- **A query of a signature**: a claim `Σ_κ` can state. This is the design's
`Query_κ`, refined from PW0's all-of-`Atom`. -/
def Query (sg : Lara.Sigma.Sigma) : Type :=
  { c : Atom // Lara.Sigma.WellSorted sg c }

instance (sg : Lara.Sigma.Sigma) : DecidableEq (Query sg) :=
  fun c d =>
    if h : c.val = d.val then .isTrue (Subtype.ext h)
    else .isFalse (fun he => h (congrArg Subtype.val he))

/-- **Posing.** The sanctioned *decision procedure* for turning an authored
atom into a query: either it is one, or the caller is told which of the two
Σ-level conditions stopped it. No world is consulted, which is the point — see
`notPosable_world_independent`.

Not a chokepoint, and it does not need to be. `Query` is a subtype, so an
ill-sorted query is unrepresentable — `Subtype.mk` demands a real
`WellSorted` proof — and that is a stronger guarantee than a hidden
constructor. What `pose` adds is the *decision*: it computes the proof, or the
located reason there is none. Callers that already hold the proof (`trQuery`,
and the fixtures) build the subtype directly, which is sound by construction;
they would, however, bypass any behaviour later added here, so new behaviour
belongs in the `Query` type or its smart constructor, not in this function. -/
def pose (sg : Lara.Sigma.Sigma) (a : Atom) : Except QueryFault (Query sg) :=
  if h : Lara.Sigma.wsAtom sg a = true then .ok ⟨a, h⟩ else .error (faultOf sg a)

theorem pose_ok_iff (sg : Lara.Sigma.Sigma) (a : Atom) :
    (∃ c : Query sg, pose sg a = .ok c) ↔ Lara.Sigma.WellSorted sg a := by
  unfold pose Lara.Sigma.WellSorted
  by_cases h : Lara.Sigma.wsAtom sg a = true
  · exact ⟨fun _ => h, fun _ => ⟨⟨a, h⟩, by simp [h]; rfl⟩⟩
  · simp [h]

theorem pose_error_iff (sg : Lara.Sigma.Sigma) (a : Atom) (f : QueryFault) :
    pose sg a = .error f ↔ queryFault sg a = some f := by
  unfold pose queryFault
  by_cases h : Lara.Sigma.wsAtom sg a = true <;> simp [h]

/-- Posing does not rewrite the authored claim. -/
theorem pose_ok_val {sg : Lara.Sigma.Sigma} {a : Atom} {c : Query sg}
    (h : pose sg a = .ok c) : c.val = a := by
  unfold pose at h
  by_cases hw : Lara.Sigma.wsAtom sg a = true
  · rw [dif_pos hw] at h
    cases h
    rfl
  · rw [dif_neg hw] at h
    exact absurd h (by simp)

/-- A query poses as itself: posing is a section of the underlying-claim
projection. This is what lets the surface's elaboration judgment state
`q.val = c` and still be realized by the decider. -/
theorem pose_val_self {sg : Lara.Sigma.Sigma} (c : Query sg) :
    pose sg c.val = .ok c := by
  cases c with
  | mk v hv =>
    have hw : Lara.Sigma.wsAtom sg v = true := hv
    simp only [pose, dif_pos hw]

/-- A query carries no fault — the Σ-level conditions are gone by
construction, which is the entire content of refining the *type*. -/
theorem query_no_fault {sg : Lara.Sigma.Sigma} (c : Query sg) :
    queryFault sg c.val = none :=
  (queryFault_eq_none_iff sg c.val).mpr c.property

/-! ## 2. What a `gap` still means

With the Σ-level conditions removed from the query set, the remaining question
is what `gap` reports. The answer is one condition, and it is a theorem:
`Grounded.statusC` gaps exactly on empty complete support, and the complete
support of a claim at a world is the retained checker cache filtered by
canonical conclusion equivalence. So a `gap` says *the world declares no
complete argument concluding this claim*, and says nothing else. -/

open Lara.PW.Instance

/-- **The world addresses the claim**: it declares at least one complete
checked argument whose conclusion is canonically equivalent to `c`. Computed
from the retained checker cache `Lara.Consistency` already uses — no new local
machinery, PW0's gate-1 discipline. -/
def Addresses {κ : Context} (w : World κ) (c : Atom) : Prop :=
  Lara.Consistency.claimSupportFor w.unit c ≠ []

instance {κ : Context} (w : World κ) (c : Atom) : Decidable (Addresses w c) :=
  inferInstanceAs (Decidable (Lara.Consistency.claimSupportFor w.unit c ≠ []))

/-- Addressing, unfolded to the retained node it names. -/
theorem addresses_iff {κ : Context} (w : World κ) (c : Atom) :
    Addresses w c ↔ ∃ node ∈ w.unit.nodes, equiv κ.canon node.conclusion c := by
  constructor
  · intro h
    cases hl : Lara.Consistency.claimSupportFor w.unit c with
    | nil => exact absurd hl h
    | cons i is =>
      have hmem : i ∈ Lara.Consistency.claimSupportFor w.unit c := by
        rw [hl]; simp
      obtain ⟨node, hnode, heq⟩ :=
        Lara.Consistency.mem_claimSupportFor_iff.mp hmem
      exact ⟨node, List.mem_of_getElem? hnode, heq⟩
  · rintro ⟨node, hnode, heq⟩
    intro hnil
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hnode
    have hmem : i ∈ Lara.Consistency.claimSupportFor w.unit c :=
      Lara.Consistency.mem_claimSupportFor_iff.mpr ⟨node, hi, heq⟩
    rw [hnil] at hmem
    simp at hmem

/-- **What a `gap` means, exactly.** The compiled observation reports `gap` for
a claim precisely when the world declares no complete argument concluding it.
`Grounded.statusC_gap_iff` at the world — no new definition. -/
theorem cmpStatus_gap_iff_not_addresses {κ : Context} (w : World κ) (c : Atom) :
    cmpStatus w c = Status.gap ↔ ¬ Addresses w c := by
  unfold cmpStatus Addresses
  rw [Lara.Grounded.statusC_gap_iff]
  simp [claimAt, Lara.Consistency.completeClaimFor]

/-- The source observation says the same thing, through T1. -/
theorem srcStatus_gap_iff_not_addresses {κ : Context} (w : World κ) (c : Atom) :
    srcStatus w c Status.gap ↔ ¬ Addresses w c :=
  (srcStatus_iff_cmpStatus w c Status.gap).trans
    (cmpStatus_gap_iff_not_addresses w c)

/-- **"Posed but unsupported" is not a `gap` cause in this model.** Every
argument an accepted unit retains is *complete* — `Compile.CheckedNode.valid`
carries the empty obligation list — so an addressed claim has nonempty complete
support and `statusC` cannot gap on it. This is the residue of limitation 2
made precise: the fourth condition collapses into the third by theorem, not by
omission. -/
theorem not_gap_of_addresses {κ : Context} (w : World κ) (c : Atom)
    (h : Addresses w c) : cmpStatus w c ≠ Status.gap :=
  fun hg => (cmpStatus_gap_iff_not_addresses w c).mp hg h

/-- An addressed claim therefore gets one of the three *substantive* statuses. -/
theorem status_of_addresses {κ : Context} (w : World κ) (c : Atom)
    (h : Addresses w c) :
    cmpStatus w c = Status.justified ∨ cmpStatus w c = Status.contested ∨
      cmpStatus w c = Status.defeated := by
  have hne := not_gap_of_addresses w c h
  cases hs : cmpStatus w c with
  | justified => exact Or.inl rfl
  | contested => exact Or.inr (Or.inl rfl)
  | defeated => exact Or.inr (Or.inr rfl)
  | gap => exact absurd hs hne

/-! ### The refined report

`Report` is the outer layer's answer to "what does this world say about this
authored atom". PW0 could answer only with a `Status`, so all four of
limitation 2's conditions arrived as `gap`. Here the two Σ-level conditions
have their own constructors and never reach a world, and the residual `gap` is
named `unaddressed` — which is what it actually means. -/

/-- The refined answer to an authored atom at a world. -/
inductive Report where
  /-- the head predicate is not in `Σ_κ` -/
  | outOfVocabulary (p : PredSym)
  /-- the head is declared, the arguments do not fit its declared sorts -/
  | illSorted (p : PredSym)
  /-- a genuine query of `Σ_κ` that this world declares no argument for -/
  | unaddressed
  /-- a genuine query the world declares an argument for, and its status -/
  | observed (s : Status)
deriving DecidableEq

/-- **The refined observation.** Posing runs first and is world-independent;
only a claim that survives it is put to the world. -/
def report {κ : Context} (w : World κ) (a : Atom) : Report :=
  match pose κ.sigma a with
  | .error (.undeclaredPredicate p) => .outOfVocabulary p
  | .error (.illSortedArguments p) => .illSorted p
  | .ok c => if Addresses w c.val then .observed (cmpStatus w c.val) else .unaddressed

/-- `observed` is pinned to exactly its condition, and carries the unchanged
PW0 status. -/
theorem report_observed_iff {κ : Context} (w : World κ) (a : Atom) (s : Status) :
    report w a = .observed s ↔
      (Lara.Sigma.WellSorted κ.sigma a ∧ Addresses w a ∧ cmpStatus w a = s) := by
  unfold report pose
  by_cases hw : Lara.Sigma.wsAtom κ.sigma a = true
  · rw [dif_pos hw]
    by_cases haddr : Addresses w a
    · simp [haddr, Lara.Sigma.WellSorted, hw, eq_comm]
    · simp [haddr, Lara.Sigma.WellSorted, hw]
  · rw [dif_neg hw]
    have : ¬ Lara.Sigma.WellSorted κ.sigma a := hw
    cases hf : faultOf κ.sigma a <;> simp [this]

/-- `unaddressed` is pinned to exactly its condition: a genuine query the world
declares nothing for — which is the residual `gap`. -/
theorem report_unaddressed_iff {κ : Context} (w : World κ) (a : Atom) :
    report w a = .unaddressed ↔
      (Lara.Sigma.WellSorted κ.sigma a ∧ cmpStatus w a = Status.gap) := by
  unfold report pose
  by_cases hw : Lara.Sigma.wsAtom κ.sigma a = true
  · rw [dif_pos hw]
    by_cases haddr : Addresses w a
    · simp [Lara.Sigma.WellSorted, hw,
        (cmpStatus_gap_iff_not_addresses w a), haddr]
    · simp [haddr, Lara.Sigma.WellSorted, hw,
        (cmpStatus_gap_iff_not_addresses w a)]
  · rw [dif_neg hw]
    have : ¬ Lara.Sigma.WellSorted κ.sigma a := hw
    cases hf : faultOf κ.sigma a <;> simp [this]

/-- The two Σ-level constructors are pinned to the two query faults, so the
report reproduces `queryFault`'s split verbatim. -/
theorem report_outOfVocabulary_iff {κ : Context} (w : World κ) (a : Atom)
    (p : PredSym) :
    report w a = .outOfVocabulary p ↔
      queryFault κ.sigma a = some (.undeclaredPredicate p) := by
  unfold report pose queryFault
  by_cases hw : Lara.Sigma.wsAtom κ.sigma a = true
  · rw [dif_pos hw]
    by_cases haddr : Addresses w a <;> simp [haddr, hw]
  · rw [dif_neg hw]
    cases hf : faultOf κ.sigma a <;> simp [hw]

theorem report_illSorted_iff {κ : Context} (w : World κ) (a : Atom)
    (p : PredSym) :
    report w a = .illSorted p ↔
      queryFault κ.sigma a = some (.illSortedArguments p) := by
  unfold report pose queryFault
  by_cases hw : Lara.Sigma.wsAtom κ.sigma a = true
  · rw [dif_pos hw]
    by_cases haddr : Addresses w a <;> simp [haddr, hw]
  · rw [dif_neg hw]
    cases hf : faultOf κ.sigma a <;> simp [hw]

/-! ### Agreement with PW0

The refinement must *replace* PW0 answers, not invent new ones: every atom the
refined report distinguishes must be one PW0 answered `gap`. That is not free.
`Gamma` is a checker *parameter*, so an admitted evidence leaf can carry an
atom outside `Σ_κ`; at such a world an ill-sorted atom is `justified`, not
`gap`, and the refinement would be *changing* an answer rather than splitting
one. `SortedWorld` is exactly the missing condition, stated where it is used
rather than assumed silently. -/

/-- Every claim the world declares support for is well-sorted. Not automatic —
see the section note. -/
def SortedWorld {κ : Context} (w : World κ) : Prop :=
  ∀ c : Atom, Addresses w c → Lara.Sigma.WellSorted κ.sigma c

/-- Under the identity canonicalizer the condition is a finite check on the
retained nodes: `≡` is plain equality there (`equiv_id_eq`), so an addressed
claim *is* one of the declared conclusions. -/
theorem sortedWorld_of_nodes {κ : Context} (hcanon : κ.canon = id) (w : World κ)
    (h : ∀ node ∈ w.unit.nodes, Lara.Sigma.WellSorted κ.sigma node.conclusion) :
    SortedWorld w := by
  intro c haddr
  obtain ⟨node, hnode, heq⟩ := (addresses_iff w c).mp haddr
  have hc : node.conclusion = c :=
    equiv_id_eq (by rw [← hcanon]; exact heq)
  rw [← hc]
  exact h node hnode

/-- **The refinement splits PW0's `gap`; it does not move any other answer.**
At a `SortedWorld`, the three non-`observed` reports are exactly the atoms PW0
answered `gap`, and `observed` carries PW0's unchanged status. So limitation
2's conflation is resolved by *partitioning* one report, with no local judgment
redefined. -/
theorem report_ne_observed_iff_gap {κ : Context} (w : World κ)
    (hw : SortedWorld w) (a : Atom) :
    (∀ s, report w a ≠ .observed s) ↔ cmpStatus w a = Status.gap := by
  constructor
  · intro h
    by_cases hws : Lara.Sigma.WellSorted κ.sigma a
    · by_cases haddr : Addresses w a
      · exact absurd ((report_observed_iff w a (cmpStatus w a)).mpr
          ⟨hws, haddr, rfl⟩) (h _)
      · exact (cmpStatus_gap_iff_not_addresses w a).mpr haddr
    · exact (cmpStatus_gap_iff_not_addresses w a).mpr fun haddr => hws (hw a haddr)
  · intro hgap s hobs
    obtain ⟨_, haddr, _⟩ := (report_observed_iff w a s).mp hobs
    exact not_gap_of_addresses w a haddr hgap

/-! ## 3. Posing across a bridge

The executable comparison gains one guard *before* PW0's three. Its order is
still the design's — translation, candidates, acceptance — because posing is
not a fourth guard inserted among them but a stage that runs before the bridge
is consulted at all. `CrossResult` and `IncomparabilityReason` are untouched;
`SortedResult` wraps them. -/

/-! ### The bridge's vocabulary boundary, located

`trAtom` returns a bare `none` when a symbol of the claim is outside the
bridge's map, which would leave the vocabulary fault the one report that cannot
say *which* symbol — a departure from the located discipline `Sigma.SigmaFault`
and `QueryFault` follow, and it is the fault most likely to reach an author,
since a surface-declared bridge always has a finite vocabulary
(`Surface.predMapOf_eq_none`). `vocabFault` is the located scan: `trAtom`'s own
traversal, reporting the first symbol it cannot carry. -/

/-- A symbol the bridge's map does not carry. Two constructors because
`SymMap` has two namespaces: the claim's head predicate, or a constructor
occurring in its arguments. -/
inductive OutOfVocabulary where
  /-- the head predicate is outside the bridge's `predMap` -/
  | pred (p : PredSym)
  /-- a constructor in the arguments is outside the bridge's `conMap` -/
  | con (k : ConSym)
deriving DecidableEq

mutual
  /-- The first out-of-vocabulary symbol of a ground term, in `trTerm`'s own
  traversal order. -/
  def vocabFaultTerm (m : SymMap) : Term → Option OutOfVocabulary
    | .num _ => none
    | .str _ => none
    | .con k ts =>
      match m.conMap k with
      | none => some (.con ⟨k⟩)
      | some _ => vocabFaultTerms m ts
  /-- …and of an argument list, left to right. -/
  def vocabFaultTerms (m : SymMap) : Terms → Option OutOfVocabulary
    | .nil => none
    | .cons t ts =>
      match vocabFaultTerm m t with
      | some f => some f
      | none => vocabFaultTerms m ts
end

/-- **The located reason `trAtom` is undefined**: the head predicate, or the
first constructor in the arguments, that the bridge's map does not carry. -/
def vocabFault (m : SymMap) : Atom → Option OutOfVocabulary
  | .atom p ts =>
    match m.predMap p with
    | none => some (.pred ⟨p⟩)
    | some _ => vocabFaultTerms m ts

mutual
  theorem vocabFaultTerm_eq_none_iff (m : SymMap) :
      ∀ t : Term, vocabFaultTerm m t = none ↔ ∃ t', trTerm m t = some t'
    | .num _ => by simp [vocabFaultTerm, trTerm]
    | .str _ => by simp [vocabFaultTerm, trTerm]
    | .con k ts => by
        cases hk : m.conMap k with
        | none => simp [vocabFaultTerm, trTerm, hk]
        | some k' =>
          simp only [vocabFaultTerm, trTerm, hk]
          rw [vocabFaultTerms_eq_none_iff m ts]
          cases hts : trTerms m ts with
          | none => simp
          | some ts' => simp
  theorem vocabFaultTerms_eq_none_iff (m : SymMap) :
      ∀ ts : Terms, vocabFaultTerms m ts = none ↔ ∃ ts', trTerms m ts = some ts'
    | .nil => by simp [vocabFaultTerms, trTerms]
    | .cons t ts => by
        simp only [vocabFaultTerms, trTerms]
        cases ht : vocabFaultTerm m t with
        | some f =>
          have hno : ¬ (∃ t', trTerm m t = some t') := by
            rw [← vocabFaultTerm_eq_none_iff m t]
            simp [ht]
          cases htr : trTerm m t with
          | none => simp
          | some t' => exact absurd ⟨t', htr⟩ hno
        | none =>
          have ⟨t', htr⟩ : ∃ t', trTerm m t = some t' :=
            (vocabFaultTerm_eq_none_iff m t).mp ht
          rw [htr, vocabFaultTerms_eq_none_iff m ts]
          cases hts : trTerms m ts with
          | none => simp
          | some ts' => simp
end

/-- **The scan is exactly `trAtom`'s domain condition**: no located symbol is
the claim's translation being defined. This is what lets the vocabulary fault
carry a symbol without weakening `trQueryFault_eq_none_iff`. -/
theorem vocabFault_eq_none_iff (m : SymMap) (a : Atom) :
    vocabFault m a = none ↔ ∃ a', trAtom m a = some a' := by
  obtain ⟨p, ts⟩ := a
  cases hp : m.predMap p with
  | none => simp [vocabFault, trAtom, hp]
  | some p' =>
    simp only [vocabFault, trAtom, hp]
    rw [vocabFaultTerms_eq_none_iff m ts]
    cases hts : trTerms m ts with
    | none => simp
    | some ts' => simp

/-- An undefined translation always names a symbol — the located report is
total where it is needed. -/
theorem vocabFault_isSome_of_trAtom_none (m : SymMap) (a : Atom)
    (h : trAtom m a = none) : ∃ f, vocabFault m a = some f := by
  cases hv : vocabFault m a with
  | none =>
    obtain ⟨a', ha'⟩ := (vocabFault_eq_none_iff m a).mp hv
    rw [ha'] at h
    exact absurd h (by simp)
  | some f => exact ⟨f, rfl⟩

/-- Why an authored claim could not be posed as a comparison query at a bridge.
PW0 reported the first two as `gap` and the third as `translationUndefined`.
Every arm is located: each names the symbol it is reported against. -/
inductive PosingFault where
  /-- the claim is not a query of the *source* signature -/
  | sourceQuery (fault : QueryFault)
  /-- a symbol of the claim is outside the bridge's vocabulary map, and which -/
  | bridgeVocabulary (symbol : OutOfVocabulary)
  /-- the translated claim is not a query of the *target* signature -/
  | targetQuery (fault : QueryFault)
deriving DecidableEq

/-- **The sorted bridge translation** `τ_b` on queries: translate the symbols
(`Lara.PW.trAtom`), then demand the result be a query of the *target*
signature. A translated claim the target signature cannot state is not a target
query, so it is reported as such instead of being put to a target world that
would answer `gap` — the misreading limitation 2 warns about. -/
def trQuery (m : SymMap) (sgT : Lara.Sigma.Sigma) {sgS : Lara.Sigma.Sigma}
    (c : Query sgS) : Option (Query sgT) :=
  match trAtom m c.val with
  | none => none
  | some a => if h : Lara.Sigma.wsAtom sgT a = true then some ⟨a, h⟩ else none

/-- The located reason `trQuery` is undefined: out of the bridge's vocabulary —
naming the symbol, by `vocabFault` — or in it but not a query of the target
signature. -/
def trQueryFault (m : SymMap) (sgT : Lara.Sigma.Sigma) {sgS : Lara.Sigma.Sigma}
    (c : Query sgS) : Option PosingFault :=
  match trAtom m c.val with
  | none => (vocabFault m c.val).map .bridgeVocabulary
  | some a => (queryFault sgT a).map .targetQuery

/-- `trQueryFault` reports only the two *bridge*-side faults: a source-side
fault is `pose`'s business and cannot reappear here. -/
theorem trQueryFault_ne_sourceQuery (m : SymMap) (sgT : Lara.Sigma.Sigma)
    {sgS : Lara.Sigma.Sigma} (c : Query sgS) (f : QueryFault) :
    trQueryFault m sgT c ≠ some (.sourceQuery f) := by
  unfold trQueryFault
  cases hta : trAtom m c.val with
  | none => cases vocabFault m c.val <;> simp
  | some a => cases queryFault sgT a <;> simp

theorem trQueryFault_eq_none_iff (m : SymMap) (sgT : Lara.Sigma.Sigma)
    {sgS : Lara.Sigma.Sigma} (c : Query sgS) :
    trQueryFault m sgT c = none ↔ ∃ d, trQuery m sgT c = some d := by
  unfold trQueryFault trQuery
  cases hta : trAtom m c.val with
  | none =>
    obtain ⟨f, hf⟩ := vocabFault_isSome_of_trAtom_none m c.val hta
    simp [hf]
  | some a =>
    by_cases hw : Lara.Sigma.wsAtom sgT a = true
    · simp [(queryFault_eq_none_iff sgT a).mpr hw, hw]
    · have hq : queryFault sgT a = some (faultOf sgT a) := by simp [queryFault, hw]
      simp [hq, hw]

/-- The result of posing an authored claim and comparing it across a bridge.
Faults and comparison results live in different constructors and `PosingFault`
contains no `Status`, so — structurally, as in PW0's gate 3 — a fault can never
be read as a local status. -/
inductive SortedResult where
  | notPosable (fault : PosingFault)
  | compared (result : CrossResult Status)
deriving DecidableEq

theorem notPosable_ne_compared (f : PosingFault) (r : CrossResult Status) :
    (SortedResult.notPosable f) ≠ .compared r := fun h => nomatch h

/-- **The refined executable comparison.** Pose the authored claim in the
source signature, translate it into a target query, then hand the result to
PW0's unchanged `crossCompare`. -/
def crossComparePosed {W : Type} (sgS sgT : Lara.Sigma.Sigma) (m : SymMap)
    (raw : Atom) (candidates : List W) (acceptB : W → Bool)
    (statusOf : W → Query sgT → Status) : SortedResult :=
  match pose sgS raw with
  | .error f => .notPosable (.sourceQuery f)
  | .ok c =>
    match trQueryFault m sgT c with
    | some f => .notPosable f
    | none => .compared (crossCompare (trQuery m sgT c) candidates acceptB statusOf)

/-! ### Each fault is pinned to its condition, and only there -/

theorem crossComparePosed_sourceQuery_iff {W : Type} (sgS sgT : Lara.Sigma.Sigma)
    (m : SymMap) (raw : Atom) (candidates : List W) (acceptB : W → Bool)
    (statusOf : W → Query sgT → Status) (f : QueryFault) :
    crossComparePosed sgS sgT m raw candidates acceptB statusOf
        = .notPosable (.sourceQuery f)
      ↔ queryFault sgS raw = some f := by
  unfold crossComparePosed
  cases hp : pose sgS raw with
  | error g =>
    have hg : queryFault sgS raw = some g := (pose_error_iff sgS raw g).mp hp
    simp [hg]
  | ok c =>
    have hws : Lara.Sigma.WellSorted sgS raw :=
      (pose_ok_iff sgS raw).mp ⟨c, hp⟩
    have hnone : queryFault sgS raw = none := (queryFault_eq_none_iff sgS raw).mpr hws
    cases htf : trQueryFault m sgT c with
    | none => simp [hnone, htf]
    | some g =>
      cases g with
      | sourceQuery x => exact absurd htf (trQueryFault_ne_sourceQuery m sgT c x)
      | bridgeVocabulary => simp [hnone, htf]
      | targetQuery x => simp [hnone, htf]

theorem crossComparePosed_bridgeVocabulary_iff {W : Type}
    (sgS sgT : Lara.Sigma.Sigma) (m : SymMap) (raw : Atom) (candidates : List W)
    (acceptB : W → Bool) (statusOf : W → Query sgT → Status)
    (x : OutOfVocabulary) :
    crossComparePosed sgS sgT m raw candidates acceptB statusOf
        = .notPosable (.bridgeVocabulary x)
      ↔ (Lara.Sigma.WellSorted sgS raw ∧ vocabFault m raw = some x) := by
  unfold crossComparePosed
  cases hp : pose sgS raw with
  | error g =>
    have hns : ¬ Lara.Sigma.WellSorted sgS raw := by
      intro hws
      obtain ⟨c, hc⟩ := (pose_ok_iff sgS raw).mpr hws
      rw [hc] at hp
      exact absurd hp (by simp)
    simp [hns]
  | ok c =>
    have hval : c.val = raw := pose_ok_val hp
    have hws : Lara.Sigma.WellSorted sgS raw := (pose_ok_iff sgS raw).mp ⟨c, hp⟩
    subst hval
    cases hta : trAtom m c.val with
    | none =>
      obtain ⟨f, hf⟩ := vocabFault_isSome_of_trAtom_none m c.val hta
      simp [trQueryFault, hta, hf, hws, eq_comm]
    | some a =>
      have hvoc : vocabFault m c.val = none :=
        (vocabFault_eq_none_iff m c.val).mpr ⟨a, hta⟩
      cases hq : queryFault sgT a with
      | none => simp [trQueryFault, hta, hq, hvoc]
      | some g => simp [trQueryFault, hta, hq, hvoc]

theorem crossComparePosed_targetQuery_iff {W : Type} (sgS sgT : Lara.Sigma.Sigma)
    (m : SymMap) (raw : Atom) (candidates : List W) (acceptB : W → Bool)
    (statusOf : W → Query sgT → Status) (f : QueryFault) :
    crossComparePosed sgS sgT m raw candidates acceptB statusOf
        = .notPosable (.targetQuery f)
      ↔ (Lara.Sigma.WellSorted sgS raw ∧
          ∃ a, trAtom m raw = some a ∧ queryFault sgT a = some f) := by
  unfold crossComparePosed
  cases hp : pose sgS raw with
  | error g =>
    have hns : ¬ Lara.Sigma.WellSorted sgS raw := by
      intro hws
      obtain ⟨c, hc⟩ := (pose_ok_iff sgS raw).mpr hws
      rw [hc] at hp
      exact absurd hp (by simp)
    simp [hns]
  | ok c =>
    have hval : c.val = raw := pose_ok_val hp
    have hws : Lara.Sigma.WellSorted sgS raw := (pose_ok_iff sgS raw).mp ⟨c, hp⟩
    subst hval
    cases hta : trAtom m c.val with
    | none =>
      obtain ⟨x, hx⟩ := vocabFault_isSome_of_trAtom_none m c.val hta
      simp [trQueryFault, hta, hx, hws]
    | some a =>
      cases hq : queryFault sgT a with
      | none => simp [trQueryFault, hta, hq, hws]
      | some g => simp [trQueryFault, hta, hq, hws]

/-- **Conservativity.** When the authored claim is a query at both ends, the
refined interface hands PW0's unchanged `crossCompare` the translated query, so
T5 and `mem_compare_iff_sat_dia` apply verbatim. -/
theorem crossComparePosed_compared {W : Type} {sgS sgT : Lara.Sigma.Sigma}
    {m : SymMap} {raw : Atom} {candidates : List W} {acceptB : W → Bool}
    {statusOf : W → Query sgT → Status} {c : Query sgS} {d : Query sgT}
    (hpose : pose sgS raw = .ok c) (htr : trQuery m sgT c = some d) :
    crossComparePosed sgS sgT m raw candidates acceptB statusOf
      = .compared (crossCompare (some d) candidates acceptB statusOf) := by
  unfold crossComparePosed
  rw [hpose]
  have hnf : trQueryFault m sgT c = none :=
    (trQueryFault_eq_none_iff m sgT c).mpr ⟨d, htr⟩
  simp only [hnf, htr]

/-- **`translationUndefined` is unreachable here, and the split is the only
report of it.** `crossCompare` still carries PW0's reason — the type is frozen
— but the refined comparison reaches `crossCompare` only past
`trQueryFault = none`, which by `trQueryFault_eq_none_iff` hands it a defined
translation. So a consumer matching on `SortedResult` never has to choose
between `compared (.incomparable .translationUndefined)` and the two
`notPosable` arms that split it: only the latter occur. -/
theorem crossCompare_some_ne_translationUndefined {W Q : Type} (d : Q)
    (candidates : List W) (acceptB : W → Bool) (statusOf : W → Q → Status) :
    crossCompare (some d) candidates acceptB statusOf
      ≠ .incomparable .translationUndefined := by
  show (if candidates.isEmpty = true then _ else _) ≠ _
  by_cases hcand : candidates.isEmpty = true
  · rw [if_pos hcand]; exact fun h => nomatch h
  · rw [if_neg hcand]
    cases hfil : candidates.filter acceptB with
    | nil => exact fun h => nomatch h
    | cons v vs => exact fun h => nomatch h

theorem crossComparePosed_ne_translationUndefined {W : Type}
    (sgS sgT : Lara.Sigma.Sigma) (m : SymMap) (raw : Atom) (candidates : List W)
    (acceptB : W → Bool) (statusOf : W → Query sgT → Status) :
    crossComparePosed sgS sgT m raw candidates acceptB statusOf
      ≠ .compared (.incomparable .translationUndefined) := by
  unfold crossComparePosed
  cases hp : pose sgS raw with
  | error g => simp
  | ok c =>
    cases htf : trQueryFault m sgT c with
    | some g => simp [htf]
    | none =>
      obtain ⟨d, hd⟩ := (trQueryFault_eq_none_iff m sgT c).mp htf
      simp only [htf, hd]
      intro h
      exact crossCompare_some_ne_translationUndefined d candidates acceptB
        statusOf (SortedResult.compared.inj h)

/-- **No world is consulted for a posing fault.** The three faults are
statements about the two signatures and the bridge alone: the same verdict for
*any* candidate list, acceptance predicate and status function, including at a
target context with no worlds at all. This is what stops a vocabulary or
sorting mismatch from being read as "the target field considered this and found
it unsupported" — the misreading `docs/theory-pw0-outer-model.md` limitation 2
had to warn about in prose. -/
theorem notPosable_world_independent {W W' : Type} (sgS sgT : Lara.Sigma.Sigma)
    (m : SymMap) (raw : Atom)
    (candidates : List W) (acceptB : W → Bool) (statusOf : W → Query sgT → Status)
    (candidates' : List W') (acceptB' : W' → Bool)
    (statusOf' : W' → Query sgT → Status) (f : PosingFault) :
    crossComparePosed sgS sgT m raw candidates acceptB statusOf = .notPosable f ↔
      crossComparePosed sgS sgT m raw candidates' acceptB' statusOf'
        = .notPosable f := by
  unfold crossComparePosed
  cases hp : pose sgS raw with
  | error g => simp
  | ok c =>
    cases htf : trQueryFault m sgT c with
    | none => simp [htf]
    | some g => simp [htf]

/-! ## 4. The sorted frame

A second frame builder over the same Lara contexts, differing from
`Instance.BridgeData.frame` in exactly two fields: `Query` is the refined
per-context query set, and `translate` is `trQuery` rather than a free
`Option`-valued field. PW0's builder is untouched; `sat_erase` relates the
two. -/

/-- **Bridge data over sorted Lara contexts.** The bridge carries a symbol map
rather than a free claim translation: `trQuery` derives the typed partial
translation from it, which is what makes target well-sortedness a *checked*
condition instead of an assumption about the field. -/
structure SortedBridgeData where
  K : Type
  ctx : K → Context
  B : Type
  bsrc : B → K
  btgt : B → K
  R : (b : B) → World (ctx (bsrc b)) → World (ctx (btgt b)) → Prop
  accept : (b : B) → World (ctx (bsrc b)) → World (ctx (btgt b)) → Prop
  /-- the bridge's partial symbol translation (`Lara.PW.SymMap`, T6's) -/
  sym : B → SymMap

/-- The outer frame a sorted bridge datum induces. -/
def SortedBridgeData.frame (D : SortedBridgeData) : Frame where
  K := D.K
  B := D.B
  src := D.bsrc
  tgt := D.btgt
  World := fun κ => World (D.ctx κ)
  Query := fun κ => Query (D.ctx κ).sigma
  R := D.R
  accept := D.accept
  translate := fun b c => trQuery (D.sym b) (D.ctx (D.btgt b)).sigma c

/-- `V^src` at the sorted frame. -/
def srcVal (D : SortedBridgeData) : Valuation D.frame :=
  fun {_} w c s => srcStatus w c.val s

/-- `V^cmp` at the sorted frame. -/
def cmpVal (D : SortedBridgeData) : Valuation D.frame :=
  fun {_} w c s => cmpStatus w c.val = s

/-- **T4 at the sorted frame.** The refinement does not disturb the
source-compilation coherence: `sat_congr` at T1, exactly as in PW0. -/
theorem sat_src_iff_cmp (D : SortedBridgeData) {κ : D.K}
    (w : D.frame.World κ) (φ : Form D.frame κ) :
    Sat D.frame (srcVal D) φ w ↔ Sat D.frame (cmpVal D) φ w :=
  sat_congr D.frame (srcVal D) (cmpVal D)
    (fun _ w c s => srcStatus_iff_cmpStatus w c.val s) φ w

theorem cmpVal_functional (D : SortedBridgeData) :
    Valuation.Functional (cmpVal D) := fun _ _ _ _ h₁ h₂ => h₁ ▸ h₂

theorem cmpVal_total (D : SortedBridgeData) : Valuation.Total (cmpVal D) :=
  fun w c => ⟨cmpStatus w c.val, rfl⟩

theorem srcVal_functional (D : SortedBridgeData) :
    Valuation.Functional (srcVal D) := by
  intro _ w c s₁ s₂ h₁ h₂
  have e₁ := (srcStatus_iff_cmpStatus w c.val s₁).mp h₁
  have e₂ := (srcStatus_iff_cmpStatus w c.val s₂).mp h₂
  exact e₁ ▸ e₂

theorem srcVal_total (D : SortedBridgeData) : Valuation.Total (srcVal D) := by
  intro _ w c
  exact ⟨cmpStatus w c.val, (srcStatus_iff_cmpStatus w c.val _).mpr rfl⟩

/-! ### Conservativity over PW0

The refinement must not change any answer PW0 already gave. `erase` forgets the
sorting — the same contexts, worlds, candidate relation and acceptance, with
queries back to all of `Atom` and the translation back to a bare `trAtom` — and
`sat_erase` proves that the two models satisfy the same formulas. Every PW0
theorem about a query that *was* well-sorted therefore transports unchanged. -/

/-- The PW0 bridge datum underneath a sorted one. -/
def SortedBridgeData.erase (D : SortedBridgeData) : BridgeData where
  K := D.K
  ctx := D.ctx
  B := D.B
  bsrc := D.bsrc
  btgt := D.btgt
  R := D.R
  accept := D.accept
  translate := fun b a => trAtom (D.sym b) a

/-- Forget the sorting of a formula: the only change is at the status atoms,
which drop to their underlying claims. -/
def eraseForm (D : SortedBridgeData) :
    {κ : D.frame.K} → Form D.frame κ → Form D.erase.frame κ
  | _, .status s c => .status s c.val
  | _, .top => .top
  | _, .neg φ => .neg (eraseForm D φ)
  | _, .conj φ ψ => .conj (eraseForm D φ) (eraseForm D ψ)
  | _, .box b φ => Form.box (F := D.erase.frame) b (eraseForm D φ)
  | _, .dia b φ => Form.dia (F := D.erase.frame) b (eraseForm D φ)

/-- **Conservativity.** The sorted model and PW0's model satisfy the same
formulas: the refinement narrows which claims can be *asked*, and changes no
answer to a claim PW0 could already ask. The accepted relations are literally
shared, so the modal cases move across definitionally — the same shape as
`sat_congr`. -/
theorem sat_erase (D : SortedBridgeData) :
    ∀ {κ : D.frame.K} (φ : Form D.frame κ) (w : D.frame.World κ),
      Sat D.frame (cmpVal D) φ w ↔
        Sat D.erase.frame (Instance.cmpVal D.erase) (eraseForm D φ) w := by
  intro κ φ
  induction φ with
  | status s c => exact fun _ => Iff.rfl
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

/-- The same conservativity for the source valuation, through T4 on both
sides. -/
theorem sat_erase_src (D : SortedBridgeData) {κ : D.frame.K} (φ : Form D.frame κ)
    (w : D.frame.World κ) :
    Sat D.frame (srcVal D) φ w ↔
      Sat D.erase.frame (Instance.srcVal D.erase) (eraseForm D φ) w :=
  ((sat_src_iff_cmp D w φ).trans (sat_erase D φ w)).trans
    (Instance.sat_src_iff_cmp D.erase w (eraseForm D φ)).symm

end Lara.PW.Sorted
