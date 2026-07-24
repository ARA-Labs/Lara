/-
Mechanized compilation with subargument closure (`Lara.Compile`) — the Lean
port of the v0.1-frozen compile rules (spec §8, "Compilation rules", frozen in
the M1 lock pass), over the *concrete* §6.1/§7.1 layers rather than the opaque
carrier of `Lara/Grounded.lean`.

What this file discharges, against the exact spec figure:

* **Result 4 ("no untyped node or attack"), both halves** —
  `compile_nodes_checked`: every AF node is a complete checked support term
  (`O = ∅`); `edge_iff`: every edge decomposes into a *typed* declared attack
  whose source is the edge's tail and whose attacked occurrence is contained
  in the edge's head. Nothing untyped can appear, by construction.
* **Subargument closure, characterized concretely** — `Contains` is
  structural occurrence (`∃ π', v@π' = occ(k)`); `target_contains_occ` and
  `closure_includes_direct` show the attack's own target receives an edge, so
  closure edges *extend* (never replace) the direct attack; `attackOcc_unique`
  — the attacked occurrence is a function of the attack.
* **The N16 bridge, argument level** — `srcIn_iff_directIn` /
  `srcIn_iff_grounded`: a source-level declarative judgment
  (`SrcIn`/`SrcOut`, defined over the Prop-level closure-edge relation
  `Edge`, never running the grounded iteration) agrees with the abstract
  declarative and executable semantics of `Lara/Grounded.lean` over the
  compiled AF `toAF`.
* **The N16 bridge, claim-status level** — `SrcStatus` is the four-state
  claim status read from `SrcIn`/`SrcOut` alone (no AF, no iteration), and
  `srcStatus_iff` proves it holds iff the status equals executable
  `Grounded.statusC` over the compiled AF. Together the two levels give
  source-to-compiled
  status preservation with exactly **one** residual obligation: the Bool edge
  relation is an oracle (`Faithful`) standing in for the pending executable
  support/attack checkers. Supplying that oracle constructively (the M2
  decider slice) closes §9 result 6's source-vs-compiled half; nothing else
  is missing at this layer.

Design notes:

* A `CheckedProgram` carries its own evidence (`complete`, `typed`) — the Lean
  analogue of "a well-formed source program": compilation is only defined
  downstream of the checker, so the structure is the checker's postcondition
  (the `StrictJudgment` convention of `Lara/Strict.lean`). Its `args` carry a
  `Nodup` invariant: spec §8's `Args(P)` is a *set* of terms, so
  term-identical declarations compile to one node (declaration names are
  report/`eraseCert` plumbing, not AF semantics — two structurally equal
  terms contain the same occurrences and receive identical edge sets).
* Everything stays Prop-level until the bridge; `toAF` indexes arguments by
  list position (`Grounded.Arg = Nat`), and `Faithful` ties the oracle to
  `Edge` exactly on in-range indices and forces it false off-range.
-/

import Lara.Attack
import Lara.Grounded

namespace Lara.Compile

open Lara.Support

/-! ### Occurrence containment and the attacked occurrence (spec §8) -/

/-- `t` occurs in `v`: some position reaches it (`∃ π', v@π' = t`). -/
def Contains (v t : SupportTerm) : Prop :=
  ∃ π : Attack.Pos, Attack.subterm v π = some t

theorem contains_refl (v : SupportTerm) : Contains v v := ⟨[], rfl⟩

/-- `occ(k)`: the attacked occurrence — the whole target for a rebut, the
subterm at `π` for an undercut/undermine. -/
def AttackOcc : Attack.Attack → SupportTerm → Prop
  | .rebut _ u, t => t = u
  | .undercut _ u π, t => Attack.subterm u π = some t
  | .undermine _ u π, t => Attack.subterm u π = some t

/-- The attacked occurrence is a function of the attack. -/
theorem attackOcc_unique {k : Attack.Attack} {t t' : SupportTerm}
    (h : AttackOcc k t) (h' : AttackOcc k t') : t = t' := by
  cases k with
  | rebut w u =>
    simp only [AttackOcc] at h h'
    rw [h, h']
  | undercut w u π =>
    simp only [AttackOcc] at h h'
    exact Option.some.inj (h.symm.trans h')
  | undermine w u π =>
    simp only [AttackOcc] at h h'
    exact Option.some.inj (h.symm.trans h')

/-- The attack's own target contains its attacked occurrence — for a rebut the
occurrence *is* the target; for undercut/undermine the position witnesses it. -/
theorem target_contains_occ {k : Attack.Attack} {t : SupportTerm}
    (h : AttackOcc k t) : Contains k.target t := by
  cases k with
  | rebut w u =>
    simp only [AttackOcc] at h
    exact h ▸ contains_refl u
  | undercut w u π => exact ⟨π, h⟩
  | undermine w u π => exact ⟨π, h⟩

/-! ### Checked programs and the compiled edge relation (spec §8, frozen) -/

variable {canon : String → String} {Pi : RuleId → Option Rule}
  {Gamma : LeafId → Option Atom}
  {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
  {dp : Attack.DefeatPolicy}

/-- A well-formed source program at the compile boundary: declared arguments
with evidence they are complete checked support terms (`O = ∅`, spec §8
`Args`), and declared attacks with evidence they type (§7.1). Compilation is
defined only downstream of the checker, so the structure *is* the checker's
postcondition. `nodup` models §8's `Args(P)` being a set of terms. -/
structure CheckedProgram (canon : String → String) (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop)
    (dp : Attack.DefeatPolicy) where
  /-- declared arguments, `Args(P)` -/
  args : List SupportTerm
  /-- `Args(P)` is a set: no duplicate terms -/
  nodup : args.Nodup
  /-- every declared argument is a complete checked support term -/
  complete : ∀ w ∈ args, ∃ C, HasSupport canon Pi Gamma CertOk w C []
  /-- declared attacks -/
  atts : List Attack.Attack
  /-- every declared attack types (§7.1) -/
  typed : ∀ k ∈ atts, Attack.HasAttack canon Pi Gamma CertOk dp k

/-- **The compiled attack relation (spec §8 `Attack(P)`, v0.1-frozen).**
`Edge P a b`: both endpoints are declared complete arguments, and some
declared attack has source `a` and an attacked occurrence contained in `b` —
ASPIC+ subargument closure. -/
def Edge (P : CheckedProgram canon Pi Gamma CertOk dp)
    (a b : SupportTerm) : Prop :=
  a ∈ P.args ∧ b ∈ P.args ∧
    ∃ k ∈ P.atts, k.source = a ∧ ∃ t, AttackOcc k t ∧ Contains b t

/-! ### Result 4: no untyped node or attack in the target AF -/

/-- **Result 4, node half.** Every AF node is a complete checked support term.
(This is the `complete` field, stated as the compile invariant.) -/
theorem compile_nodes_checked (P : CheckedProgram canon Pi Gamma CertOk dp) :
    ∀ w ∈ P.args, ∃ C, HasSupport canon Pi Gamma CertOk w C [] :=
  P.complete

/-- **Result 4, edge half.** An edge exists iff both endpoints are declared
complete arguments and a declared — and *typed* — attack sources it, with its
attacked occurrence contained in the head. Untyped attacks cannot produce
edges; closure introduces edges only onto arguments containing the attacked
occurrence. -/
theorem edge_iff (P : CheckedProgram canon Pi Gamma CertOk dp)
    (a b : SupportTerm) :
    Edge P a b ↔ a ∈ P.args ∧ b ∈ P.args ∧
      ∃ k ∈ P.atts, Attack.HasAttack canon Pi Gamma CertOk dp k ∧
        k.source = a ∧ ∃ t, AttackOcc k t ∧ Contains b t := by
  constructor
  · rintro ⟨ha, hb, k, hk, hsrc, t, hocc, hcont⟩
    exact ⟨ha, hb, k, hk, P.typed k hk, hsrc, t, hocc, hcont⟩
  · rintro ⟨ha, hb, k, hk, _, hsrc, t, hocc, hcont⟩
    exact ⟨ha, hb, k, hk, hsrc, t, hocc, hcont⟩

/-- Closure extends the direct attack: a declared attack whose source and
target are both declared arguments yields the direct edge source → target. -/
theorem closure_includes_direct (P : CheckedProgram canon Pi Gamma CertOk dp)
    {k : Attack.Attack} (hk : k ∈ P.atts) {t : SupportTerm}
    (hocc : AttackOcc k t)
    (hsrc : k.source ∈ P.args) (htgt : k.target ∈ P.args) :
    Edge P k.source k.target :=
  ⟨hsrc, htgt, k, hk, rfl, t, hocc, target_contains_occ hocc⟩

/-! ### The bridge to the abstract grounded layer (N16)

`Lara/Grounded.lean` proved declarative ≡ executable grounded semantics over
an arbitrary abstract AF, where the earlier layer characterized `compile`
without exercising it. Here we exercise it: index the checked program's arguments by list position,
compile to a `Grounded.AF`, and show a source-level declarative judgment
defined over the Prop-level closure edges agrees with the abstract one —
first per argument, then lifted to four-state claim status. The Bool edge
relation is oracle-parametric (`Faithful`) until the executable checkers
land. -/

/-- The compiled abstract AF: arguments are indices into `P.args`; the edge
relation is the supplied oracle. -/
def toAF (P : CheckedProgram canon Pi Gamma CertOk dp)
    (edgeB : Nat → Nat → Bool) : Grounded.AF where
  args := List.range P.args.length
  attack := edgeB

/-- The oracle decides exactly the frozen `Edge` relation: `agrees` on
in-range indices, and (`ranged`) no edge touches an out-of-range index —
forced because `Edge` requires both endpoints declared. -/
structure Faithful (P : CheckedProgram canon Pi Gamma CertOk dp)
    (edgeB : Nat → Nat → Bool) : Prop where
  ranged : ∀ i j, edgeB i j = true → i < P.args.length ∧ j < P.args.length
  agrees : ∀ (i j : Nat) (a b : SupportTerm),
    P.args[i]? = some a → P.args[j]? = some b →
    (edgeB i j = true ↔ Edge P a b)

/- Source-level declarative grounded judgment, over the *Prop-level* closure
edges — never materializing the iteration or the Bool oracle. `SrcIn P i`:
argument `i` is in, because every closure-edge attacker is out; `SrcOut P j`:
some in argument's term edges to `j`'s term. The mirror of
`Grounded.DirectIn`/`DirectOut`, read off the source program. -/
mutual
  inductive SrcIn (P : CheckedProgram canon Pi Gamma CertOk dp) : Nat → Prop where
    | intro {i : Nat} {a : SupportTerm} (ha : P.args[i]? = some a)
        (h : ∀ (j : Nat) (b : SupportTerm), P.args[j]? = some b →
          Edge P b a → SrcOut P j) :
        SrcIn P i
  inductive SrcOut (P : CheckedProgram canon Pi Gamma CertOk dp) : Nat → Prop where
    | intro {j c : Nat} {cA bA : SupportTerm} (hc : SrcIn P c)
        (hcA : P.args[c]? = some cA) (hbA : P.args[j]? = some bA)
        (hE : Edge P cA bA) : SrcOut P j
end

mutual
  /-- Source-level in ⟹ abstract in over the compiled AF. -/
  theorem srcIn_direct {P : CheckedProgram canon Pi Gamma CertOk dp}
      {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) :
      ∀ {i : Nat}, SrcIn P i → Grounded.DirectIn (toAF P edgeB) i
    | _, .intro ha h =>
      Grounded.DirectIn.intro (List.mem_range.mpr (lt_of_getElem?_some ha))
        (fun j hj hatt => by
          obtain ⟨b, hb⟩ := getElem?_some_of_lt P.args j (List.mem_range.mp hj)
          exact srcOut_direct hf (h j b hb ((hf.agrees j _ b _ hb ha).mp hatt)))
  /-- Source-level out ⟹ abstract out over the compiled AF. -/
  theorem srcOut_direct {P : CheckedProgram canon Pi Gamma CertOk dp}
      {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) :
      ∀ {j : Nat}, SrcOut P j → Grounded.DirectOut (toAF P edgeB) j
    | _, .intro hc hcA hbA hE =>
      Grounded.DirectOut.intro (srcIn_direct hf hc)
        ((hf.agrees _ _ _ _ hcA hbA).mpr hE)
end

mutual
  /-- Abstract in over the compiled AF ⟹ source-level in. -/
  theorem direct_srcIn {P : CheckedProgram canon Pi Gamma CertOk dp}
      {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) :
      ∀ {i : Nat}, Grounded.DirectIn (toAF P edgeB) i → SrcIn P i
    | i, .intro ha h => by
      obtain ⟨a, haa⟩ := getElem?_some_of_lt P.args i (List.mem_range.mp ha)
      refine SrcIn.intro haa (fun j b hb hE => ?_)
      exact direct_srcOut hf
        (h j (List.mem_range.mpr (lt_of_getElem?_some hb))
          ((hf.agrees j i b a hb haa).mpr hE))
  /-- Abstract out over the compiled AF ⟹ source-level out. -/
  theorem direct_srcOut {P : CheckedProgram canon Pi Gamma CertOk dp}
      {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) :
      ∀ {j : Nat}, Grounded.DirectOut (toAF P edgeB) j → SrcOut P j
    | j, .intro hc hcb => by
      have hr := hf.ranged _ j hcb
      obtain ⟨cA, hcA⟩ := getElem?_some_of_lt P.args _ hr.1
      obtain ⟨bA, hbA⟩ := getElem?_some_of_lt P.args j hr.2
      exact SrcOut.intro (direct_srcIn hf hc) hcA hbA
        ((hf.agrees _ j cA bA hcA hbA).mp hcb)
end

/-- **The N16 bridge, argument level (spec §9 result 6, oracle-parametric).**
The source-level declarative judgment over the frozen closure-edge relation
agrees, argument by argument, with the abstract declarative grounded
semantics over the compiled AF. -/
theorem srcIn_iff_directIn {P : CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) (i : Nat) :
    SrcIn P i ↔ Grounded.DirectIn (toAF P edgeB) i :=
  ⟨srcIn_direct hf, direct_srcIn hf⟩

/-- The out-side companion. -/
theorem srcOut_iff_directOut {P : CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) (j : Nat) :
    SrcOut P j ↔ Grounded.DirectOut (toAF P edgeB) j :=
  ⟨srcOut_direct hf, direct_srcOut hf⟩

/-- Composition with the abstract layer: source-level in agrees with the
*executable* grounded extension over the compiled AF. -/
theorem srcIn_iff_grounded {P : CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) (i : Nat) :
    SrcIn P i ↔ i ∈ Grounded.grounded (toAF P edgeB) :=
  (srcIn_iff_directIn hf i).trans (Grounded.directIn_iff i)

/-! ### The N16 bridge, claim-status level -/

/-- **Source-level four-state claim status** (spec §8 priority order), read
from `SrcIn`/`SrcOut` alone — no AF, no iteration, no oracle. A relation
rather than a function because `SrcIn` is not decidable without the oracle;
`srcStatus_iff` shows it is total and functional under `Faithful` (it holds
iff the status is the deterministic `Grounded.statusC` result). -/
inductive SrcStatus (P : CheckedProgram canon Pi Gamma CertOk dp)
    (c : Grounded.Claim) : Grounded.Status → Prop where
  | gap (h : c.support = []) : SrcStatus P c .gap
  | justified (hne : c.support ≠ []) {i : Grounded.Arg}
      (hi : i ∈ c.support) (hin : SrcIn P i) : SrcStatus P c .justified
  | contested (hne : c.support ≠ [])
      (hnoin : ∀ i ∈ c.support, ¬ SrcIn P i) {i : Grounded.Arg}
      (hi : i ∈ c.support) (hout : ¬ SrcOut P i) : SrcStatus P c .contested
  | defeated (hne : c.support ≠ [])
      (hnoin : ∀ i ∈ c.support, ¬ SrcIn P i)
      (hallout : ∀ i ∈ c.support, SrcOut P i) : SrcStatus P c .defeated

/-- **The N16 bridge, claim-status level.** The source-level status relation
holds exactly at the executable compiled status: `SrcStatus P c
(Grounded.statusC (toAF P edgeB) c)`. With `srcIn_iff_grounded` this is
source-to-compiled status preservation, oracle-parametric — the constructive
`Faithful` from the M2 decider slice is the only remaining gap in §9 result
6's source-vs-compiled half. -/
theorem srcStatus_correct {P : CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB) (c : Grounded.Claim) :
    SrcStatus P c (Grounded.statusC (toAF P edgeB) c) := by
  by_cases hs : c.support = []
  · rw [Grounded.statusC, if_pos hs]
    exact SrcStatus.gap hs
  · rw [Grounded.statusC, if_neg hs]
    by_cases hin : ∃ i ∈ c.support, Grounded.DirectIn (toAF P edgeB) i
    · obtain ⟨i, hi, hdi⟩ := hin
      have hany : c.support.any
          (fun a => Grounded.labelC (toAF P edgeB) a == Grounded.Label.inn) = true := by
        rw [List.any_eq_true]
        exact ⟨i, hi, by
          rw [beq_iff_eq, Grounded.labelC_inn_iff]; exact hdi⟩
      rw [if_pos hany]
      exact SrcStatus.justified hs hi ((srcIn_iff_directIn hf i).mpr hdi)
    · have hnoin : ∀ i ∈ c.support, ¬ SrcIn P i := fun i hi hsi =>
        hin ⟨i, hi, (srcIn_iff_directIn hf i).mp hsi⟩
      have hnoin' : ∀ i ∈ c.support, ¬ Grounded.DirectIn (toAF P edgeB) i :=
        fun i hi hdi => hin ⟨i, hi, hdi⟩
      have hany1 : c.support.any
          (fun a => Grounded.labelC (toAF P edgeB) a == Grounded.Label.inn) = false := by
        rw [Bool.eq_false_iff]
        intro hc
        obtain ⟨i, hi, hbeq⟩ := List.any_eq_true.mp hc
        rw [beq_iff_eq, Grounded.labelC_inn_iff] at hbeq
        exact hnoin' i hi hbeq
      rw [hany1, if_neg (by simp)]
      by_cases hun : ∃ i ∈ c.support,
          ¬ Grounded.DirectIn (toAF P edgeB) i ∧ ¬ Grounded.DirectOut (toAF P edgeB) i
      · obtain ⟨i, hi, hni, hno⟩ := hun
        have hany2 : c.support.any
            (fun a => Grounded.labelC (toAF P edgeB) a == Grounded.Label.undec) = true := by
          rw [List.any_eq_true]
          exact ⟨i, hi, by
            rw [beq_iff_eq, Grounded.labelC_undec_iff]; exact ⟨hni, hno⟩⟩
        rw [if_pos hany2]
        exact SrcStatus.contested hs hnoin hi
          (fun hso => hno ((srcOut_iff_directOut hf i).mp hso))
      · have hany2 : c.support.any
            (fun a => Grounded.labelC (toAF P edgeB) a == Grounded.Label.undec) = false := by
          rw [Bool.eq_false_iff]
          intro hc
          obtain ⟨i, hi, hbeq⟩ := List.any_eq_true.mp hc
          rw [beq_iff_eq, Grounded.labelC_undec_iff] at hbeq
          exact hun ⟨i, hi, hbeq⟩
        rw [hany2, if_neg (by simp)]
        refine SrcStatus.defeated hs hnoin (fun i hi => ?_)
        have hni := hnoin' i hi
        have : ¬ (¬ Grounded.DirectIn (toAF P edgeB) i ∧
            ¬ Grounded.DirectOut (toAF P edgeB) i) := fun hh => hun ⟨i, hi, hh⟩
        have hdo : Grounded.DirectOut (toAF P edgeB) i := by
          by_cases hdo : Grounded.DirectOut (toAF P edgeB) i
          · exact hdo
          · exact absurd ⟨hni, hdo⟩ this
        exact (srcOut_iff_directOut hf i).mpr hdo

/-- Source status is functional even before supplying an executable edge
oracle: the four priority cases are mutually exclusive by construction. -/
theorem srcStatus_unique {P : CheckedProgram canon Pi Gamma CertOk dp}
    {c : Grounded.Claim} {s₁ s₂ : Grounded.Status}
    (h₁ : SrcStatus P c s₁) (h₂ : SrcStatus P c s₂) : s₁ = s₂ := by
  cases h₁ with
  | gap hgap =>
      cases h₂ with
      | gap => rfl
      | justified hne _ _ => exact False.elim (hne hgap)
      | contested hne _ _ _ => exact False.elim (hne hgap)
      | defeated hne _ _ => exact False.elim (hne hgap)
  | justified _ hi hin =>
      cases h₂ with
      | gap hgap => exact False.elim (by contradiction)
      | justified => rfl
      | contested _ hnoin _ _ => exact False.elim (hnoin _ hi hin)
      | defeated _ hnoin _ => exact False.elim (hnoin _ hi hin)
  | contested _ hnoin hi hout =>
      cases h₂ with
      | gap hgap => exact False.elim (by contradiction)
      | justified _ hi' hin => exact False.elim (hnoin _ hi' hin)
      | contested => rfl
      | defeated _ _ hallout => exact False.elim (hout (hallout _ hi))
  | defeated _ hnoin hallout =>
      cases h₂ with
      | gap hgap => exact False.elim (by contradiction)
      | justified _ hi hin => exact False.elim (hnoin _ hi hin)
      | contested _ _ hi hout => exact False.elim (hout (hallout _ hi))
      | defeated => rfl

/-- **Exact source-to-compiled status preservation.** Under a faithful
executable edge decider, a source status derivation exists exactly for the
single status returned by compiled grounded evaluation. -/
theorem srcStatus_iff {P : CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hf : Faithful P edgeB)
    (c : Grounded.Claim) (s : Grounded.Status) :
    SrcStatus P c s ↔ s = Grounded.statusC (toAF P edgeB) c := by
  constructor
  · intro hs
    exact srcStatus_unique hs (srcStatus_correct hf c)
  · intro hs
    subst s
    exact srcStatus_correct hf c

end Lara.Compile
