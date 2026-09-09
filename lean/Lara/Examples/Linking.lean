/-
# Theory M4 — executable witnesses for the fragment/linking calculus

Every theorem in `Lara.Context.*` is a conditional statement about links that
succeed, sides that are well-formed, and observations that exist. This module
is the by-construction non-vacuity discipline `Lara/EraseTransport.lean`
established: each rejection class is *reached* by a concrete pair, the
saturation is shown to emit an attack that neither side declared, the
structural merge is shown to fire, and the observation is shown to take
different values in different contexts — including the `gap` flip.

The material is the closed unit fixture of `Lara.Examples` (`sigmaEx`,
`unitPolicyEx`, `registryEx`), split across a boundary: the context declares
the leaf whose conclusion is `q`, the fragment declares the leaf whose
conclusion is `p`, and `dpEx` declares `q` contrary to `p`. Nothing is
authored twice — the point of reusing `Lara.Examples` is that the linked
program lands on the same accepted unit the whole-program fixtures already pin.
-/

import Lara.Examples
import Lara.Context.Compose
import Lara.Context.Merge
import Lara.Context.Equivalence

namespace Lara.Examples.Linking

open Lara.Support Lara.Attack Lara.Compile Lara.Check
open Lara.Context hiding Context

/-! ### The split -/

/-- The context's material: it declares `l2` (conclusion `q`) and asserts it. -/
def ctxFrame : Fragment :=
  { sigma     := sigmaEx
  , policy    := unitPolicyEx
  , gammaFrag := [(l2, pB)]
  , ground    := [pB]
  , args      := [.leaf l2]
  , atts      := []
  , imports   := Interface.closed
  , exports   := [] }

def ctxEx : Lara.Context.Context := ⟨ctxFrame⟩

/-- The fragment's material: it declares `l1` (conclusion `p`), asserts it, and
exports `p`. It declares no attack, and neither does the context. -/
def fragEx : Fragment :=
  { sigma     := sigmaEx
  , policy    := unitPolicyEx
  , gammaFrag := [(l1, pA)]
  , ground    := [pA]
  , args      := [.leaf l1]
  , atts      := []
  , imports   := Interface.closed
  , exports   := [pA] }

/-- A context that asserts nothing: the same declarations, no arguments. -/
def quietCtx : Lara.Context.Context :=
  ⟨{ ctxFrame with args := [], ground := [pB] }⟩

/-! ### The guard is reached, in both directions -/

theorem link_guard_ok : linkOk ctxEx fragEx = true := by decide

theorem link_guard_ok_quiet : linkOk quietCtx fragEx = true := by decide

/-- R-L1, own duplicate: a side that declares the same identifier twice. -/
def dupFrag : Fragment := { fragEx with gammaFrag := [(l1, pA), (l1, pA)] }

theorem reject_duplicate_own_id :
    linkFault ctxEx dupFrag = some (.duplicateOwnId .right l1) := by decide

/-- R-L1, clash: both sides declare `l2`. -/
def clashFrag : Fragment := { fragEx with gammaFrag := [(l2, pB)] }

theorem reject_id_clash : linkFault ctxEx clashFrag = some (.idClash l2) := by decide

/-- R-L2: the fragment imports an identifier the context does not declare. -/
def needyFrag : Fragment := { fragEx with imports := ⟨[l3]⟩ }

theorem reject_unsatisfied_import :
    linkFault ctxEx needyFrag = some (.unsatisfiedImport .right l3) := by decide

/-- The side tag also distinguishes an import owed by the context. -/
def needyCtx : Lara.Context.Context :=
  ⟨{ ctxFrame with imports := ⟨[l3]⟩ }⟩

theorem reject_unsatisfied_context_import :
    linkFault needyCtx fragEx = some (.unsatisfiedImport .left l3) := by decide

/-- R-L3, Σ: a fragment that redeclares the signature. -/
def otherSigmaFrag : Fragment :=
  { fragEx with sigma := { sigmaEx with sorts := ["Item", "Other"] } }

theorem reject_sigma_mismatch :
    linkFault ctxEx otherSigmaFrag =
      some (.sigmaMismatch ctxFrame.sigma otherSigmaFrag.sigma) := by decide

/-- R-L3, policy: a fragment that redefines the defeat policy — the class that
enforces "a context may not redefine the fixed policy". -/
def otherPolicyFrag : Fragment :=
  { fragEx with policy := { unitPolicyEx with defeat := ⟨[], []⟩ } }

theorem reject_policy_mismatch :
    linkFault ctxEx otherPolicyFrag =
      some (.policyMismatch ctxFrame.policy otherPolicyFrag.policy) := by decide

/-- Every rejection class is reached by some pair, and an accepted link is not
vacuously accepted. -/
theorem link_rejected_of_fault :
    link registryEx ctxEx clashFrag = none :=
  link_eq_none (by decide)

/-- A rejected link reports the guard fault separately from checker rejection. -/
theorem obs_incompatible_id_clash :
    obs registryEx ctxEx clashFrag = .incompatible (.idClash l2) := by decide

/-- A malformed signature shared by both sides passes the link guard but is
rejected by the whole-unit checker. -/
def malformedSigma := { sigmaEx with sorts := ["Item", "Item"] }

def malformedCtx : Lara.Context.Context :=
  ⟨{ ctxFrame with sigma := malformedSigma }⟩

def malformedFrag : Fragment := { fragEx with sigma := malformedSigma }

theorem malformed_link_guard_ok : linkOk malformedCtx malformedFrag = true := by decide

theorem obs_rejected_signature :
    obs registryEx malformedCtx malformedFrag =
      .rejected (.signature .malformedSigma) := by decide

/-! ### Saturation emits an attack neither side declared

`ctxFrame.atts` and `fragEx.atts` are both empty, and the linked attack list is
exactly the undermine `Lara.Examples.kAtk` — the attack the whole-program
fixture had to declare by hand. -/

theorem crossAtts_nonempty :
    crossAtts registryEx (linkGamma ctxEx fragEx) ctxEx fragEx = [kAtk] := by decide

theorem linked_atts :
    (linkedUnit registryEx ctxEx fragEx).atts = [kAtk] := by decide

theorem linked_args :
    (linkedUnit registryEx ctxEx fragEx).args = [.leaf l2, .leaf l1] := by decide

/-- The linked program is accepted by the executable checker. -/
theorem linked_accepted :
    (Check.Unit.checkUnit (linkGamma ctxEx fragEx) registryEx (linkGround ctxEx fragEx)
      (linkedUnit registryEx ctxEx fragEx)).isOk = true := by decide

/-! ### The observation is context-sensitive

The same fragment, observed in two compatible contexts. Under `ctxEx` its
export is undermined and `defeated`; under `quietCtx`, which declares the same
leaf but asserts nothing, it is `justified`. Contexts distinguish — which is
what makes the congruence theorem a statement with content. -/

theorem obs_defeated :
    obs registryEx ctxEx fragEx = .observed [Grounded.Status.defeated] := by
  rfl

theorem obs_justified :
    obs registryEx quietCtx fragEx = .observed [Grounded.Status.justified] := by rfl

/-! ### The gap flip (D4)

A fragment that exports a conclusion it has no argument for is `gap`; a context
that supplies an argument for that conclusion flips it. This is exactly what
pinning the claim at fragment-definition time would have hidden. -/

/-- The fragment exports `s`, for which it has no argument. -/
def gapFrag : Fragment := { fragEx with exports := [pC], imports := ⟨[l3]⟩ }

/-- A context that declares `l3` (conclusion `s`) but does not assert it. -/
def silentSCtx : Lara.Context.Context :=
  ⟨{ ctxFrame with gammaFrag := [(l2, pB), (l3, pC)], ground := [pB, pC] }⟩

/-- A context that asserts `s`. -/
def loudSCtx : Lara.Context.Context :=
  ⟨{ ctxFrame with
      gammaFrag := [(l2, pB), (l3, pC)],
      ground := [pB, pC],
      args := [.leaf l2, .leaf l3] }⟩

theorem obs_gap : obs registryEx silentSCtx gapFrag = .observed [Grounded.Status.gap] := by
  rfl

theorem obs_gap_flipped :
    obs registryEx loudSCtx gapFrag = .observed [Grounded.Status.justified] := by rfl

/-! ### The structural merge fires (D3)

A fragment that imports `l2` may declare `.leaf l2` as an argument of its own —
identifier hygiene does not prevent *term* collision, because the term is built
from the identifier the context declares. The link merges the two occurrences
instead of rejecting, and the observation is unchanged. -/

def mergeFrag : Fragment :=
  { fragEx with args := [.leaf l2, .leaf l1], imports := ⟨[l2]⟩ }

theorem merge_link_ok : linkOk ctxEx mergeFrag = true := by decide

/-- Three declared arguments across the boundary, two after the merge. -/
theorem merge_fires :
    (ctxEx.frame.args ++ mergeFrag.args).length = 3 ∧
      (linkedUnit registryEx ctxEx mergeFrag).args = [.leaf l2, .leaf l1] :=
  ⟨rfl, rfl⟩

theorem merge_accepted :
    (Check.Unit.checkUnit (linkGamma ctxEx mergeFrag) registryEx (linkGround ctxEx mergeFrag)
      (linkedUnit registryEx ctxEx mergeFrag)).isOk = true := by decide

/-- The merge is not observable: the collided fragment reports what the
uncollided one reports. -/
theorem merge_obs_unchanged :
    obs registryEx ctxEx mergeFrag = obs registryEx ctxEx fragEx := by rfl

/-! ### Composition -/

/-- Two halves of a context, composed. The left half *is* `ctxEx` — the point
of the composition witness is that adding a second half that declares one more
leaf changes what the composite declares and owes, not what it observes. -/
def leftHalf : Lara.Context.Context := ctxEx

def rightHalf : Lara.Context.Context :=
  ⟨{ ctxFrame with
      gammaFrag := [(l3, pC)],
      ground := [pC],
      args := [],
      imports := ⟨[l1]⟩ }⟩

theorem compose_ok : composeOk leftHalf rightHalf = true := by decide

theorem reject_compose_id_clash :
    composeFault leftHalf leftHalf = some (.idClash l2) := by decide

theorem compose_rejected : compose leftHalf leftHalf = none :=
  compose_eq_none (by decide)

theorem compose_declares_both :
    (composedContext leftHalf rightHalf).frame.declared = [l2, l3] := by rfl

/-- The composite still owes `l1`, which the fragment declares. -/
theorem compose_residual :
    (composedContext leftHalf rightHalf).frame.imports.leaves = [l1] := by rfl

theorem compose_links : linkOk (composedContext leftHalf rightHalf) fragEx = true := by
  decide

/-- Linking into the composite observes what linking into the whole context
observes: composition adds a declaration, not an observation. -/
theorem compose_obs :
    obs registryEx (composedContext leftHalf rightHalf) fragEx
      = .observed [Grounded.Status.defeated] := by rfl

/-! ### A contrary conflict the saturation must *not* emit

`crossAtts` fires only where `Compile.conflictAttackableB` holds. A strict-root
target whose conclusion contrary-matches the source is therefore left alone —
which is what keeps saturation from manufacturing an edge onto an unattackable
inference. (Inside an *accepted* link the situation cannot arise at all:
`Consistency.wellFormed_contrary_target_attackable` shows a well-formed policy
forbids a strict rule whose conclusion touches a contrary side, which is
exactly the R12 violation `Lara.Examples.check_unit_r12_location` pins.) -/

theorem strict_target_contrary_matches :
    contraryMatchB id dpEx pB pA = true := by decide

theorem strict_target_not_attackable :
    conflictAttackableB PiStrict strictTarget = false := by decide

theorem crossAttsFrom_skips_strict_target :
    crossAttsFrom id dpEx PiStrict [(.leaf l2, pB)] [(strictTarget, pA)] = [] := by
  decide

/-! ### The two sides are linkable, and the link is checked *by theorem*

`link_checked` is the phase's headline conditional; without an instance of its
`SideOk` premises it says nothing about any concrete program. Here both sides
are discharged and the accepted linked unit is produced through the theorem
rather than by `decide` on the checker. Nothing in either side mentions a
certificate, so both are stated for an arbitrary registry — which is also what
lets the D6 witness below reuse them. -/

/-- The linked environment declares both leaves. -/
theorem linkGamma_l2 : linkGamma ctxEx fragEx l2 = some pB := by decide

theorem linkGamma_l1 : linkGamma ctxEx fragEx l1 = some pA := by decide

theorem leaf2_checked
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop) :
    HasSupport id unitPolicyEx.ruleLookup (linkGamma ctxEx fragEx) CertOk
      (.leaf l2) pB [] := .leaf linkGamma_l2

theorem leaf1_checked
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop) :
    HasSupport id unitPolicyEx.ruleLookup (linkGamma ctxEx fragEx) CertOk
      (.leaf l1) pA [] := .leaf linkGamma_l1

theorem sideOk_ctx (reg : BackendRegistry id) :
    SideOk id reg (linkGamma ctxEx fragEx) unitPolicyEx
      ctxEx.frame.args ctxEx.frame.atts where
  support := by
    intro w hw
    have hw2 : w = .leaf l2 := by simpa [ctxEx, ctxFrame] using hw
    exact ⟨pB, hw2 ▸ leaf2_checked _⟩
  typed := by intro k hk; simp [ctxEx, ctxFrame] at hk
  source_declared := by intro k hk; simp [ctxEx, ctxFrame] at hk
  target_declared := by intro k hk; simp [ctxEx, ctxFrame] at hk
  attack_complete := by
    intro source hs target ht Cs Ct hsSup htSup hcm _
    exfalso
    have hsEq : source = .leaf l2 := by simpa [ctxEx, ctxFrame] using hs
    have htEq : target = .leaf l2 := by simpa [ctxEx, ctxFrame] using ht
    subst hsEq; subst htEq
    have h1 : Cs = pB := (Support.hasSupport_unique hsSup (leaf2_checked _)).1
    have h2 : Ct = pB := (Support.hasSupport_unique htSup (leaf2_checked _)).1
    subst h1; subst h2
    exact absurd ((contraryMatchB_iff id unitPolicyEx.defeat pB pB).mpr hcm) (by decide)

theorem sideOk_frag (reg : BackendRegistry id) :
    SideOk id reg (linkGamma ctxEx fragEx) unitPolicyEx fragEx.args fragEx.atts where
  support := by
    intro w hw
    have hw1 : w = .leaf l1 := by simpa [fragEx] using hw
    exact ⟨pA, hw1 ▸ leaf1_checked _⟩
  typed := by intro k hk; simp [fragEx] at hk
  source_declared := by intro k hk; simp [fragEx] at hk
  target_declared := by intro k hk; simp [fragEx] at hk
  attack_complete := by
    intro source hs target ht Cs Ct hsSup htSup hcm _
    exfalso
    have hsEq : source = .leaf l1 := by simpa [fragEx] using hs
    have htEq : target = .leaf l1 := by simpa [fragEx] using ht
    subst hsEq; subst htEq
    have h1 : Cs = pA := (Support.hasSupport_unique hsSup (leaf1_checked _)).1
    have h2 : Ct = pA := (Support.hasSupport_unique htSup (leaf1_checked _)).1
    subst h1; subst h2
    exact absurd ((contraryMatchB_iff id unitPolicyEx.defeat pA pA).mpr hcm) (by decide)

/-- The context is admissible for the fragment, against any registry: the
input the congruence theorem quantifies over is inhabited. -/
theorem admissible_split (reg : BackendRegistry id) : Admissible reg ctxEx fragEx where
  guard := link_guard_ok
  ctx := sideOk_ctx reg
  frag := sideOk_frag reg
  signature :=
    signatureStage_link (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  scope := by decide
  ruleIds := by decide
  policy := Policy.firstViolation_none_iff.mp (by decide)

private theorem compositeGamma_l2 :
    linkGamma (composedContext leftHalf rightHalf) fragEx l2 = some pB := by decide

private theorem compositeGamma_l1 :
    linkGamma (composedContext leftHalf rightHalf) fragEx l1 = some pA := by decide

private theorem compositeLeaf2Checked :
    HasSupport id unitPolicyEx.ruleLookup
      (linkGamma (composedContext leftHalf rightHalf) fragEx)
      (certOkOf registryEx) (.leaf l2) pB [] :=
  .leaf compositeGamma_l2

private theorem compositeLeaf1Checked :
    HasSupport id unitPolicyEx.ruleLookup
      (linkGamma (composedContext leftHalf rightHalf) fragEx)
      (certOkOf registryEx) (.leaf l1) pA [] :=
  .leaf compositeGamma_l1

private theorem sideOk_left_composite :
    SideOk id registryEx (linkGamma (composedContext leftHalf rightHalf) fragEx)
      unitPolicyEx leftHalf.frame.args leftHalf.frame.atts where
  support := by
    intro w hw
    have hw2 : w = .leaf l2 := by simpa [leftHalf, ctxEx, ctxFrame] using hw
    exact ⟨pB, hw2 ▸ compositeLeaf2Checked⟩
  typed := by intro k hk; simp [leftHalf, ctxEx, ctxFrame] at hk
  source_declared := by intro k hk; simp [leftHalf, ctxEx, ctxFrame] at hk
  target_declared := by intro k hk; simp [leftHalf, ctxEx, ctxFrame] at hk
  attack_complete := by
    intro source hs target ht Cs Ct hsSup htSup hcm _
    exfalso
    have hsEq : source = .leaf l2 := by
      simpa [leftHalf, ctxEx, ctxFrame] using hs
    have htEq : target = .leaf l2 := by
      simpa [leftHalf, ctxEx, ctxFrame] using ht
    subst hsEq; subst htEq
    have h1 : Cs = pB := (Support.hasSupport_unique hsSup compositeLeaf2Checked).1
    have h2 : Ct = pB := (Support.hasSupport_unique htSup compositeLeaf2Checked).1
    subst h1; subst h2
    exact absurd ((contraryMatchB_iff id unitPolicyEx.defeat pB pB).mpr hcm) (by decide)

private theorem sideOk_right_composite :
    SideOk id registryEx (linkGamma (composedContext leftHalf rightHalf) fragEx)
      unitPolicyEx rightHalf.frame.args rightHalf.frame.atts where
  support := by intro w hw; simp [rightHalf] at hw
  typed := by intro k hk; simp [rightHalf, ctxFrame] at hk
  source_declared := by intro k hk; simp [rightHalf, ctxFrame] at hk
  target_declared := by intro k hk; simp [rightHalf, ctxFrame] at hk
  attack_complete := by intro source hs; simp [rightHalf] at hs

private theorem sideOk_frag_composite :
    SideOk id registryEx (linkGamma (composedContext leftHalf rightHalf) fragEx)
      unitPolicyEx fragEx.args fragEx.atts where
  support := by
    intro w hw
    have hw1 : w = .leaf l1 := by simpa [fragEx] using hw
    exact ⟨pA, hw1 ▸ compositeLeaf1Checked⟩
  typed := by intro k hk; simp [fragEx] at hk
  source_declared := by intro k hk; simp [fragEx] at hk
  target_declared := by intro k hk; simp [fragEx] at hk
  attack_complete := by
    intro source hs target ht Cs Ct hsSup htSup hcm _
    exfalso
    have hsEq : source = .leaf l1 := by simpa [fragEx] using hs
    have htEq : target = .leaf l1 := by simpa [fragEx] using ht
    subst hsEq; subst htEq
    have h1 : Cs = pA := (Support.hasSupport_unique hsSup compositeLeaf1Checked).1
    have h2 : Ct = pA := (Support.hasSupport_unique htSup compositeLeaf1Checked).1
    subst h1; subst h2
    exact absurd ((contraryMatchB_iff id unitPolicyEx.defeat pA pA).mpr hcm) (by decide)

/-- `admissible_composed`, instantiated. The right half has no arguments, so
both explicit cross-coverage premises are discharged rather than assumed. -/
theorem admissible_composite :
    Admissible registryEx (composedContext leftHalf rightHalf) fragEx :=
  admissible_composed compose_links sideOk_left_composite sideOk_right_composite
    (by intro source hs target ht; simp [rightHalf] at ht)
    (by intro source hs; simp [rightHalf] at hs)
    sideOk_frag_composite
    (signatureStage_link (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    (by decide) (by decide) (Policy.firstViolation_none_iff.mp (by decide))

/-- **`link_checked`, instantiated.** The accepted linked unit exists by the
theorem, from the two sides' linkability and the per-side signature data. -/
theorem link_checked_split :
    ∃ accepted, Check.Unit.checkUnit (linkGamma ctxEx fragEx) registryEx
      (linkGround ctxEx fragEx) (linkedUnit registryEx ctxEx fragEx) = .ok accepted :=
  exists_accepted_of_admissible (admissible_split registryEx)

/-! ### Composition associates on a concrete triple -/

/-- A third context, declaring the remaining leaf. -/
def thirdHalf : Lara.Context.Context :=
  ⟨{ ctxFrame with
      gammaFrag := [(l3, pC)],
      ground := [pC],
      args := [],
      imports := ⟨[l2]⟩ }⟩

def emptyHalf : Lara.Context.Context :=
  ⟨{ ctxFrame with gammaFrag := [], ground := [], args := [], imports := ⟨[l1]⟩ }⟩

theorem compose_triple_ok :
    composeOk (composedContext leftHalf emptyHalf) thirdHalf = true := by decide

theorem compose_triple_ok' :
    composeOk leftHalf (composedContext emptyHalf thirdHalf) = true := by decide

/-- Both bracketings declare the same leaves and owe the same imports — on the
nose here, since the concrete lists are small enough to compute. -/
theorem compose_assoc_witness :
    (composedContext (composedContext leftHalf emptyHalf) thirdHalf).frame.declared
        = (composedContext leftHalf (composedContext emptyHalf thirdHalf)).frame.declared ∧
      (composedContext (composedContext leftHalf emptyHalf) thirdHalf).frame.imports.leaves
        = (composedContext leftHalf
            (composedContext emptyHalf thirdHalf)).frame.imports.leaves := by
  decide

/-! ### Composition is not closed for linkability (issue #229)

`compose` merges material and does not saturate, so `sideOk_composed` takes
the two cross-boundary quadrants as explicit hypotheses. This section converts
that boundary from prose into a theorem. `ctxEx` asserts `l2` (conclusion `q`)
and `hostileHalf` asserts `l1` (conclusion `p`); `dpEx` declares `q` contrary
to `p`. Each half is admissible for `thirdFrag`, a fragment declaring only
`l3`, and the two halves compose — but the composite is **not** admissible for
the same fragment: the conflict from `l2` onto `l1` crosses the halves'
boundary and is covered by nothing. Neither half declared the attack, and
neither *could* have on its own — a side's attacks must have both endpoints
among its own arguments (`SideOk.target_declared`) — so the failure is the
composite's, not a defect of either half. -/

/-- A context asserting `l1`, the leaf `fragEx` normally supplies. -/
def hostileHalf : Lara.Context.Context :=
  ⟨{ ctxFrame with gammaFrag := [(l1, pA)], ground := [pA], args := [.leaf l1] }⟩

/-- A fragment declaring only the third leaf, whose conclusion `s` conflicts
with nothing. -/
def thirdFrag : Fragment :=
  { fragEx with gammaFrag := [(l3, pC)], ground := [pC], args := [.leaf l3], exports := [pC] }

/-- A side asserting one leaf and declaring no attack is well-formed under any
Γ that resolves the leaf to a conclusion not contrary to itself. -/
private theorem sideOk_singleLeaf {reg : BackendRegistry id}
    {Gamma : LeafId → Option Atom} {l : LeafId} {p : Atom}
    (hΓ : Gamma l = some p)
    (hself : contraryMatchB id unitPolicyEx.defeat p p = false) :
    SideOk id reg Gamma unitPolicyEx [.leaf l] [] where
  support := by
    intro w hw
    have hw' : w = .leaf l := by simpa using hw
    exact ⟨p, hw' ▸ .leaf hΓ⟩
  typed := by intro k hk; simp at hk
  source_declared := by intro k hk; simp at hk
  target_declared := by intro k hk; simp at hk
  attack_complete := by
    intro source hs target ht Cs Ct hsSup htSup hcm _
    exfalso
    have hsEq : source = .leaf l := by simpa using hs
    have htEq : target = .leaf l := by simpa using ht
    subst hsEq; subst htEq
    have h1 : Cs = p := (Support.hasSupport_unique hsSup (.leaf hΓ)).1
    have h2 : Ct = p := (Support.hasSupport_unique htSup (.leaf hΓ)).1
    rw [h1, h2] at hcm
    have := (contraryMatchB_iff id unitPolicyEx.defeat p p).mpr hcm
    rw [hself] at this
    exact Bool.false_ne_true this

theorem hostile_compose_ok : composeOk ctxEx hostileHalf = true := by decide

/-- The composite is hygienic and its guard passes against the fragment: the
failure below is not a rejection class. -/
theorem hostile_composite_links :
    linkOk (composedContext ctxEx hostileHalf) thirdFrag = true := by decide

/-- The left half alone is admissible for the fragment. -/
theorem hostile_left_admissible (reg : BackendRegistry id) :
    Admissible reg ctxEx thirdFrag where
  guard := by decide
  ctx := sideOk_singleLeaf (l := l2) (p := pB) (by decide) (by decide)
  frag := sideOk_singleLeaf (l := l3) (p := pC) (by decide) (by decide)
  signature :=
    signatureStage_link (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  scope := by decide
  ruleIds := by decide
  policy := Policy.firstViolation_none_iff.mp (by decide)

/-- The right half alone is admissible for the fragment. -/
theorem hostile_right_admissible (reg : BackendRegistry id) :
    Admissible reg hostileHalf thirdFrag where
  guard := by decide
  ctx := sideOk_singleLeaf (l := l1) (p := pA) (by decide) (by decide)
  frag := sideOk_singleLeaf (l := l3) (p := pC) (by decide) (by decide)
  signature :=
    signatureStage_link (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  scope := by decide
  ruleIds := by decide
  policy := Policy.firstViolation_none_iff.mp (by decide)

/-- **The composite is not well-formed as a side.** Its arguments include both
leaves, `q` is contrary to `p`, a leaf is always attackable at its root, and
the composite's attack list is the two halves' — empty. -/
theorem hostile_composite_not_sideOk (reg : BackendRegistry id) :
    ¬ SideOk id reg (linkGamma (composedContext ctxEx hostileHalf) thirdFrag)
      unitPolicyEx (composedContext ctxEx hostileHalf).frame.args
      (composedContext ctxEx hostileHalf).frame.atts := by
  intro h
  have hs : SupportTerm.leaf l2 ∈ (composedContext ctxEx hostileHalf).frame.args :=
    composed_args.mpr (Or.inl (by simp [ctxEx, ctxFrame]))
  have ht : SupportTerm.leaf l1 ∈ (composedContext ctxEx hostileHalf).frame.args :=
    composed_args.mpr (Or.inr (by simp [hostileHalf]))
  obtain ⟨k, hk, -⟩ :=
    h.attack_complete _ hs _ ht pB pA (.leaf (by decide)) (.leaf (by decide))
      ((contraryMatchB_iff id unitPolicyEx.defeat pB pA).mp (by decide)) trivial
  rcases composed_atts.mp hk with hk | hk
  · simp [ctxEx, ctxFrame] at hk
  · simp [hostileHalf, ctxFrame] at hk

/-- **Composition is not closed for linkability.** Two contexts, each
admissible for the fragment, whose composite is hygienic and passes the guard —
and is not admissible. This is the boundary `sideOk_composed`'s cross-coverage
hypotheses draw, witnessed rather than described. -/
theorem hostile_composite_not_admissible (reg : BackendRegistry id) :
    ¬ Admissible reg (composedContext ctxEx hostileHalf) thirdFrag :=
  fun h => hostile_composite_not_sideOk reg h.ctx

/-! ### All four observable statuses, and a distinguishing context -/

/-- A symmetric contrary table: `p` and `q` rebut each other, so two leaves
that assert them are mutually attacking and both `undec`. -/
def symPolicy : Policy.Policy :=
  { unitPolicyEx with defeat := ⟨[(apB, apA), (apA, apB)], []⟩ }

def symCtx : Lara.Context.Context :=
  ⟨{ ctxFrame with policy := symPolicy }⟩

def symFrag : Fragment := { fragEx with policy := symPolicy }

theorem obs_contested :
    obs registryEx symCtx symFrag = .observed [Grounded.Status.contested] := by rfl

/-- The four-state observation is fully exercised: `gap`, `justified`,
`contested`, `defeated` are all reachable through `obs`. -/
theorem obs_four_states :
    obs registryEx silentSCtx gapFrag = .observed [Grounded.Status.gap] ∧
      obs registryEx quietCtx fragEx = .observed [Grounded.Status.justified] ∧
      obs registryEx symCtx symFrag = .observed [Grounded.Status.contested] ∧
      obs registryEx ctxEx fragEx = .observed [Grounded.Status.defeated] :=
  ⟨obs_gap, obs_justified, obs_contested, obs_defeated⟩

/-- A fragment that exports `p` but supplies nothing for it. -/
def silentFrag : Fragment := { fragEx with args := [], ground := [] }

/-- **A `CtxEquiv` negative pair, with its distinguishing context.** The two
fragments export the same conclusion; `quietCtx` tells them apart. Without an
example like this, "no context distinguishes them" would be a statement about
an empty relation. -/
theorem ctxEquiv_negative : ¬ CtxEquiv registryEx fragEx silentFrag := by
  intro h
  have := h quietCtx
  rw [obs_justified] at this
  exact absurd this (by decide)

/-- A fragment with no exports observes nothing, so every context agrees about
it — stated, so that the trivial case is on the record rather than an accident
of the fixtures. -/
def noExportFrag : Fragment := { fragEx with exports := [] }

theorem obs_no_exports : obs registryEx ctxEx noExportFrag = .observed [] := by rfl

/-! ### The registry-swap generalization is not the relabel theorem (D6)

A registry that registers strictly fewer backends has the same acceptance
profile on this fragment — which declares no certificate at all — so the two
readings agree. The pair is related by no relabel of assurances: it is the same
fragment, read against two different registries. -/

/-- The `nd`-only registry. -/
def registryOnlyNd : BackendRegistry id := fun β =>
  if β = ndId then registryEx β else none

theorem registryOnlyNd_ord : registryOnlyNd ordId = none := by
  simp [registryOnlyNd, ordId, ndId]

/-- The two registries genuinely differ: one registers `ord`, the other does
not. So this is not the trivial `reg₁ = reg₂` instance. -/
theorem registryOnlyNd_ne_registryEx : registryOnlyNd ≠ registryEx := by
  intro h
  have hord : registryOnlyNd ordId = registryEx ordId := by rw [h]
  rw [registryOnlyNd_ord, registry_ord_registered] at hord
  exact absurd hord (by simp)

theorem certOk_onlyNd_le :
    ∀ β h κ As C, certOkOf registryOnlyNd β h κ As C → certOkOf registryEx β h κ As C := by
  intro β h κ As C hok
  by_cases hβ : β = ndId
  · simpa [certOkOf, registryOnlyNd, hβ] using hok
  · simp [certOkOf, registryOnlyNd, hβ] at hok

theorem assurPreserving_onlyNd :
    ∀ (r : Rule) (As : List Atom) (A : Atom) (α : Assurance),
      AssuranceOk (certOkOf registryOnlyNd) r As A α →
        AssuranceOk (certOkOf registryEx) r As A α := by
  intro r As A α h
  cases h with
  | defeasible hm => exact .defeasible hm
  | trusted hm ht => exact .trusted hm ht
  | cert hm hallow hacc => exact .cert hm hallow (certOk_onlyNd_le _ _ _ _ _ hacc)

/-- **D6, witnessed.** Two different registries, the same fragment, the same
observation. -/
theorem registry_swap_witness :
    obs registryOnlyNd ctxEx fragEx = obs registryEx ctxEx fragEx :=
  registry_swap_congruence assurPreserving_onlyNd (admissible_split registryOnlyNd)

/-- **The congruence, instantiated.** With the admissible context above, the
headline applies to a concrete link. -/
theorem congruence_witness :
    obs registryEx ctxEx fragEx = obs registryEx ctxEx (mapAssurFrag id fragEx) :=
  backend_replacement_congruence (fun _ _ h => h) (fun _ _ _ _ h => h)
    (admissible_split registryEx) (fixesContext_id ctxEx)

/-! ### A fragment that carries a real certificate

Every fixture above is assurance-free, so nothing in it can distinguish one
backend from another: `mapAssurFrag f` is the identity on a list of leaves, for
*every* `f`. The split below carries an actual `nd` certificate, so the
congruence and the acceptance-profile generalization are exercised on a
fragment whose acceptance genuinely depends on a registry.

The relabel is a real backend swap: `certSwap` exchanges the `nd` identity for
an alias registered against the same backend core, and the two fragments —
one certified by `nd`, one by the alias — are contextually indistinguishable. -/

/-- A second identity for the same registered `nd` core. -/
def aliasId : BackendId := ⟨"nd-alias", 1⟩

/-- The registry that registers the alias as well. Acceptance strictly grows,
which is exactly the D6 hypothesis. -/
def registryPlus : BackendRegistry id := fun β =>
  if β = aliasId then some ndRegistered else registryEx β

theorem registryPlus_alias : registryPlus aliasId = some ndRegistered := by
  simp [registryPlus]

theorem registryEx_alias : registryEx aliasId = none := by decide

theorem registryPlus_ne_registryEx : registryPlus ≠ registryEx := by
  intro h
  have halias : registryPlus aliasId = registryEx aliasId := by rw [h]
  rw [registryPlus_alias, registryEx_alias] at halias
  exact absurd halias (by simp)

/-- Acceptance under `registryEx` implies acceptance under `registryPlus`: the
alias adds an identity, it removes none. -/
theorem certOk_plus_le :
    ∀ β h κ As C, certOkOf registryEx β h κ As C → certOkOf registryPlus β h κ As C := by
  intro β h κ As C hok
  by_cases hβ : β = aliasId
  · subst hβ; simp [certOkOf, registryEx_alias] at hok
  · simpa [certOkOf, registryPlus, hβ] using hok

/-- Acceptance at the alias *is* acceptance at `nd`: the alias resolves to the
same registered backend, so the two identities are interchangeable payload-for-
payload. This is what makes the swap below acceptance-preserving. -/
theorem certOk_alias_of_nd {h : Digest} {κ : CertRef} {As : List Atom} {C : Atom}
    (hok : certOkOf registryEx ndId h κ As C) :
    certOkOf registryPlus aliasId h κ As C := by
  have hnd : registryEx ndId = some ndRegistered := rfl
  simpa [certOkOf, registryPlus_alias, hnd] using hok

/-- The rule that certifies `q` from `p`, allowing either identity. Its
conclusion is `q`, which `certDefeat` deliberately leaves out of the contrary
table: R12 forbids a strict rule whose conclusion touches a contrary side. -/
def ruleCertBoth : Rule :=
  { ruleCert with certifiers := [(ndId, digestA), (aliasId, digestA)] }

/-- `s` is contrary to `p`. The certified conclusion `q` is deliberately
absent: R12 forbids a strict rule whose conclusion touches a contrary side, and
`ruleCertBoth` is strict with conclusion `q`. -/
def apS : APat := ⟨⟨"s"⟩, .nil⟩

def certDefeat : Attack.DefeatPolicy := ⟨[(apS, apA)], []⟩

def certPolicy : Policy.Policy :=
  { rules := [⟨rCertId, ruleCertBoth⟩], defeat := certDefeat }

/-- The certified argument, under either identity. -/
def certArg (β : BackendId) : SupportTerm :=
  .inst rCertId [] [.leaf l1] [] [] (.cert β digestA slot1Cert)

/-- The context declares the example leaves and asserts the premise. -/
def certCtx : Lara.Context.Context :=
  ⟨{ sigma     := sigmaEx
   , policy    := certPolicy
   , gammaFrag := [(l1, pA), (l2, pB), (l3, pC)]
   , ground    := groundEx
   , args      := [.leaf l1]
   , atts      := []
   , imports   := Interface.closed
   , exports   := [] }⟩

/-- The fragment imports the premise leaf and exports the certified
conclusion. Its only argument carries the certificate. -/
def certFrag : Fragment :=
  { sigma     := sigmaEx
  , policy    := certPolicy
  , gammaFrag := []
  , ground    := []
  , args      := [certArg ndId]
  , atts      := []
  , imports   := ⟨[l1]⟩
  , exports   := [pB] }

theorem certLinkOk : linkOk certCtx certFrag = true := by decide

theorem certRuleLookup : certPolicy.ruleLookup rCertId = some ruleCertBoth := by decide

theorem certLinkGamma_l1 : linkGamma certCtx certFrag l1 = some pA := by decide

/-- The certified argument checks, under either identity, against the registry
that registers it. Built relationally rather than by evaluating the checker:
the certificate's acceptance is `Lara.Examples.registry_exact_digest_accepts`,
and every other `InstSide` field is a side condition of a strict, parameterless,
question-free rule. -/
theorem certArg_checked {β : BackendId} {reg : BackendRegistry id}
    (hallow : (β, digestA) ∈ ruleCertBoth.certifiers)
    (hacc : certOkOf reg β digestA slot1Cert [pA] pB) :
    HasSupport id certPolicy.ruleLookup (linkGamma certCtx certFrag)
      (certOkOf reg) (certArg β) pB [] := by
  refine HasSupport.inst (As := [pA]) (Cs := [pA]) (Os := [[]])
    (DCs := []) (DOs := [])
    { rule := certRuleLookup
      θNodup := by decide
      θDom := by intro x; simp [ruleCertBoth, ruleCert]
      prems := by decide
      concl := by decide
      lenAs := rfl
      lenCs := rfl
      lenOs := rfl
      premEq := by
        intro i A B hA hB
        cases i with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hA hB
            subst hA; subst hB; rfl
        | succ n => simp at hA
      lenDCs := rfl
      lenDOs := rfl
      ans := by intro j q w A hj; simp at hj
      qNodup := by decide
      dNodup := by decide
      hNodup := by decide
      cover := by intro qd hqd; simp [ruleCertBoth, ruleCert] at hqd
      disj := by intro n hn; simp at hn
      keysD := by intro n hn; simp at hn
      keysH := by intro n hn; simp at hn
      strictNoQ := fun _ => ⟨rfl, rfl⟩
      assur := .cert rfl hallow hacc } ?_ ?_
  · intro i w A O hw hA hO
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hA hO
        subst hw; subst hA; subst hO
        exact .leaf certLinkGamma_l1
    | succ n => simp at hw
  · intro j q w A O hj; simp at hj

theorem certArg_nd :
    HasSupport id certPolicy.ruleLookup (linkGamma certCtx certFrag)
      (certOkOf registryEx) (certArg ndId) pB [] :=
  certArg_checked (by decide)
    ((certOkBOf_iff registryEx ndId digestA slot1Cert [pA] pB).mp
      registry_exact_digest_accepts)

theorem certLeaf_checked (reg : BackendRegistry id) :
    HasSupport id certPolicy.ruleLookup (linkGamma certCtx certFrag)
      (certOkOf reg) (.leaf l1) pA [] := .leaf certLinkGamma_l1

/-! ### The two sides of the certified split, and the two witnesses

The certified fragment is admissible in the certified context, so the headline
applies to a link whose acceptance genuinely turns on a certificate. -/

theorem certSideOk_ctx (reg : BackendRegistry id) :
    SideOk id reg (linkGamma certCtx certFrag) certPolicy
      certCtx.frame.args certCtx.frame.atts where
  support := by
    intro w hw
    have hw1 : w = .leaf l1 := by simpa [certCtx] using hw
    exact ⟨pA, hw1 ▸ certLeaf_checked reg⟩
  typed := by intro k hk; simp [certCtx] at hk
  source_declared := by intro k hk; simp [certCtx] at hk
  target_declared := by intro k hk; simp [certCtx] at hk
  attack_complete := by
    intro source hs target ht Cs Ct hsSup htSup hcm _
    exfalso
    have hsEq : source = .leaf l1 := by simpa [certCtx] using hs
    have htEq : target = .leaf l1 := by simpa [certCtx] using ht
    subst hsEq; subst htEq
    have h1 : Cs = pA := (Support.hasSupport_unique hsSup (certLeaf_checked reg)).1
    have h2 : Ct = pA := (Support.hasSupport_unique htSup (certLeaf_checked reg)).1
    subst h1; subst h2
    exact absurd ((contraryMatchB_iff id certPolicy.defeat pA pA).mpr hcm) (by decide)

theorem certSideOk_frag {β : BackendId} {reg : BackendRegistry id}
    (hallow : (β, digestA) ∈ ruleCertBoth.certifiers)
    (hacc : certOkOf reg β digestA slot1Cert [pA] pB) :
    SideOk id reg (linkGamma certCtx certFrag) certPolicy
      [certArg β] [] where
  support := by
    intro w hw
    have hwc : w = certArg β := by simpa using hw
    exact ⟨pB, hwc ▸ certArg_checked hallow hacc⟩
  typed := by intro k hk; simp at hk
  source_declared := by intro k hk; simp at hk
  target_declared := by intro k hk; simp at hk
  attack_complete := by
    intro source hs target ht Cs Ct hsSup htSup hcm _
    exfalso
    have hsEq : source = certArg β := by simpa using hs
    have htEq : target = certArg β := by simpa using ht
    subst hsEq; subst htEq
    have h1 : Cs = pB :=
      (Support.hasSupport_unique hsSup (certArg_checked hallow hacc)).1
    have h2 : Ct = pB :=
      (Support.hasSupport_unique htSup (certArg_checked hallow hacc)).1
    subst h1; subst h2
    exact absurd ((contraryMatchB_iff id certPolicy.defeat pB pB).mpr hcm) (by decide)

/-- The certified context is admissible for the certified fragment. Unlike
`admissible_split`, discharging this *requires* the registry to accept the
fragment's certificate. -/
theorem certAdmissible : Admissible registryEx certCtx certFrag where
  guard := certLinkOk
  ctx := certSideOk_ctx registryEx
  frag := certSideOk_frag (by decide)
    ((certOkBOf_iff registryEx ndId digestA slot1Cert [pA] pB).mp
      registry_exact_digest_accepts)
  signature :=
    signatureStage_link (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  scope := by decide
  ruleIds := by decide
  policy := Policy.firstViolation_none_iff.mp (by decide)

/-- **D6 on a fragment that actually carries a certificate.** The alias
registry accepts strictly more, the fragment is unchanged, and the observation
is the same — with the certificate's acceptance genuinely in play, which is
what `registry_swap_witness` above could not exercise. -/
theorem cert_registry_swap_witness :
    obs registryEx certCtx certFrag = obs registryPlus certCtx certFrag :=
  registry_swap_congruence
    (by
      intro r As A α h
      cases h with
      | defeasible hm => exact .defeasible hm
      | trusted hm ht => exact .trusted hm ht
      | cert hm hallow hacc => exact .cert hm hallow (certOk_plus_le _ _ _ _ _ hacc))
    certAdmissible

/-! ### A genuine backend swap: renaming the certificate payload

`certSwap` wraps every certificate reference; `registryWrapped` is the same
registry read through a backend core that unwraps before replaying. The relabel
is injective and acceptance-preserving by construction, and — unlike every
identity instance above — it *moves* the fragment's argument. This is result
9's model made concrete, now under a context quantifier. -/

/-- A backend core that unwraps its certificate before replaying. Every field
passes through; the obligations transport because they all precompose with the
same function. -/
def renameCore (B : Lara.Strict.Backend id) (unren : CertRef → CertRef) :
    Lara.Strict.Backend id where
  Form := B.Form
  enc := B.enc
  enc_iff := B.enc_iff
  modelsFull := B.modelsFull
  acceptsFull := fun κ Γ φ => B.acceptsFull (unren κ) Γ φ
  replayFull := fun κ Γ φ => B.replayFull (unren κ) Γ φ
  replayFull_iff := fun κ Γ φ => B.replayFull_iff (unren κ) Γ φ
  soundFull := fun κ Γ φ h => B.soundFull (unren κ) Γ φ h
  uses := fun κ => B.uses (unren κ)
  uses_covers := fun κ Γ Γ' φ h => B.uses_covers (unren κ) Γ Γ' φ h
  uses_valid := fun κ Γ φ h => B.uses_valid (unren κ) Γ φ h
  uses_account := fun κ Γ φ h => B.uses_account (unren κ) Γ φ h

def wrapCert (κ : CertRef) : CertRef := ⟨.list [.atom "wrapped", κ.payload]⟩

def unwrapCert (κ : CertRef) : CertRef :=
  match κ.payload with
  | .list [.atom "wrapped", s] => ⟨s⟩
  | _ => κ

theorem unwrap_wrap (κ : CertRef) : unwrapCert (wrapCert κ) = κ := rfl

theorem wrapCert_injective : Function.Injective wrapCert := by
  intro κ₁ κ₂ h
  have := congrArg unwrapCert h
  rwa [unwrap_wrap, unwrap_wrap] at this

/-- The `nd` core, read through the unwrapping wrapper. Kept as a closed
definition so that the dependent `resolveTheory` field is elaborated once. -/
def wrappedNd : RegisteredBackend id :=
  { core := renameCore ndRegistered.core unwrapCert
  , resolveTheory := fun h => (ndRegistered.resolveTheory h : Option (List ndRegistered.core.Form)) }

/-- The same registry, with the `nd` identity read through the unwrapping
core. Every other identity is untouched. -/
def registryWrapped : BackendRegistry id := fun β =>
  if β = ndId then some wrappedNd else registryEx β

/-- The relabel: wrap the payload of every `nd` certificate. -/
def certSwap : Assurance → Assurance
  | .cert β h κ => if β = ndId then .cert β h (wrapCert κ) else .cert β h κ
  | α => α

/-- The inverse relabel: unwrap the payload of every `nd` certificate. -/
def certUnswap : Assurance → Assurance
  | .cert β h κ => if β = ndId then .cert β h (unwrapCert κ) else .cert β h κ
  | α => α

theorem certUnswap_certSwap : ∀ α, certUnswap (certSwap α) = α
  | .none => rfl
  | .trusted => rfl
  | .cert β h κ => by
      by_cases hβ : β = ndId
      · simp only [certSwap, certUnswap, if_pos hβ, unwrap_wrap]
      · simp only [certSwap, certUnswap, if_neg hβ]

theorem certSwap_injective : Function.Injective certSwap :=
  Function.LeftInverse.injective certUnswap_certSwap

/-- **The swap is acceptance-preserving**, by construction: the wrapped core
unwraps before replaying, so it accepts the wrapped certificate exactly where
the original accepted the original. -/
theorem certSwap_preserving :
    ∀ (r : Rule) (As : List Atom) (A : Atom) (α : Assurance),
      AssuranceOk (certOkOf registryEx) r As A α →
        AssuranceOk (certOkOf registryWrapped) r As A (certSwap α) := by
  intro r As A α h
  cases h with
  | defeasible hm => exact .defeasible hm
  | trusted hm ht => exact .trusted hm ht
  | cert hm hallow hacc =>
      rename_i β hd κ
      by_cases hβ : β = ndId
      · subst hβ
        rw [show certSwap (.cert ndId hd κ) = .cert ndId hd (wrapCert κ) by
          simp only [certSwap, if_true]]
        refine .cert hm hallow ?_
        have hnd : registryEx ndId = some ndRegistered := rfl
        simp only [certOkOf, registryWrapped, wrappedNd, hnd] at hacc ⊢
        cases hth : ndRegistered.resolveTheory hd with
        | none => rw [hth] at hacc; exact absurd hacc (by simp)
        | some T =>
            rw [hth] at hacc
            simpa [Lara.Strict.Backend.accepts, renameCore, unwrap_wrap, hth] using hacc
      · rw [show certSwap (.cert β hd κ) = .cert β hd κ by
          simp only [certSwap, if_neg hβ]]
        refine .cert hm hallow ?_
        simpa [certOkOf, registryWrapped, hβ] using hacc

/-- **The congruence, witnessed on a real backend swap.** The fragment's
certificate is genuinely relabeled — `mapAssurFrag certSwap certFrag ≠ certFrag`
— and no context can tell. -/
theorem cert_congruence_witness :
    obs registryEx certCtx certFrag
      = obs registryWrapped certCtx (mapAssurFrag certSwap certFrag) :=
  backend_replacement_congruence certSwap_injective certSwap_preserving
    certAdmissible ⟨rfl, rfl⟩

/-- The relabel is not the identity on this fragment: the witness above is not
an instance of `obs X = obs X`, which is what every other congruence instance
in this file would have been. -/
theorem cert_relabel_moves_args :
    (mapAssurFrag certSwap certFrag).args ≠ certFrag.args := by decide

theorem cert_relabel_moves : mapAssurFrag certSwap certFrag ≠ certFrag :=
  fun h => cert_relabel_moves_args (congrArg Fragment.args h)

end Lara.Examples.Linking
