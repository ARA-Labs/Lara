/-
Executable StatusBridge checker.

`StatusBridge.forth`/`back` quantify over all Nat indices, but `corr_lt`
bounds every corresponded pair and `Compile.edgeB_faithful.ranged` bounds
every attacking index, so a finite scan over the two compiled programs'
index ranges decides the contract. This module only imports.

The scan is factored so each clause is written and proved once:
`admitsB`/`matchedB` are one `transportsB` test at the two argument orders;
`forthB`/`backB` are one generic directed bisimulation scan `bisimScanB`
(sound and complete under an index-boundedness hypothesis) at the two
orientations. Each clause gets named `_sound`/`_complete` lemmas, and
`statusBridgeB_iff` states that the checker decides `StatusBridge` exactly.

**Intended scale (eng review, decision 8A).** `bisimScanB` nests three
`List.range.all` scans over the two argument ranges plus an inner
`List.range.any` witness scan, so the decider is `O(n²m²)` steps, and each
step recomputes a full `trSupport` traversal (inside `corrB`) and a
`coveredB` scan over `atts` (inside `edgeB`). This runs in the *kernel*:
`decide` only, `native_decide` is banned repo-wide. That is free on the T8
conformance fixtures — every cell in `Lara/Examples/PWStatusCheck.lean`
elaborates instantly — and it is the only scale this decider is for.
Pointing it at a program with a realistic argument count will not reduce in
practical time; hoisting `trSupport` out of `corrB` would fix that but
changes `corrB`'s shape and so re-opens `corrB_iff` and both halves of
`statusBridgeB_sound`/`_complete`. Do not do that speculatively.
-/

import Lara.PW.Status

namespace Lara.PW

open Lara.Support Lara.Grounded Lara.Compile Lara.PW.Instance

section Decider
variable {κ lam : Instance.Context}

/-- Decides `Corr` at one index pair: both positions are hits and the source
term translates to the target term. Term equality is `SupportTerm`'s
hand-written decidable equality (`SupportTerm.decEq`) — structural source
equality, certificates included. -/
def corrB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) (i j : Nat) : Bool :=
  match w.unit.program.args[i]?, v.unit.program.args[j]? with
  | some t, some t' => trSupport m lm t == some t'
  | _, _ => false

theorem corrB_iff {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} {i j : Nat} :
    corrB m lm w v i j = true ↔ Corr m lm w v i j := by
  unfold corrB Corr
  cases w.unit.program.args[i]? with
  | none => simp
  | some t =>
    cases v.unit.program.args[j]? with
    | none => simp
    | some t' => simp [beq_iff_eq]

/-- The transport test both totality clauses quantify over. -/
def transportsB (m : SymMap) (lm : LeafId → LeafId)
    (t t' : SupportTerm) : Bool :=
  trSupport m lm t == some t'

theorem transportsB_iff {m : SymMap} {lm : LeafId → LeafId}
    {t t' : SupportTerm} :
    transportsB m lm t t' = true ↔ trSupport m lm t = some t' :=
  beq_iff_eq

/-- Executable `Admits`: every source argument transports to some target
argument. -/
def admitsB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Bool :=
  w.unit.program.args.all fun t =>
    v.unit.program.args.any fun t' => transportsB m lm t t'

/-- Executable `Matched` — `admitsB` with the two argument lists swapped. -/
def matchedB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Bool :=
  v.unit.program.args.all fun t' =>
    w.unit.program.args.any fun t => transportsB m lm t t'

theorem admitsB_iff {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} :
    admitsB m lm w v = true ↔ Admits m lm w v := by
  unfold admitsB Admits
  rw [List.all_eq_true]
  constructor
  · intro h t ht
    obtain ⟨t', ht', htr⟩ := List.any_eq_true.mp (h t ht)
    exact ⟨t', transportsB_iff.mp htr, ht'⟩
  · intro h t ht
    obtain ⟨t', htr, hmem⟩ := h t ht
    exact List.any_eq_true.mpr ⟨t', hmem, transportsB_iff.mpr htr⟩

theorem matchedB_iff {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} :
    matchedB m lm w v = true ↔ Matched m lm w v := by
  unfold matchedB Matched
  rw [List.all_eq_true]
  constructor
  · intro h t' ht'
    obtain ⟨t, ht, htr⟩ := List.any_eq_true.mp (h t' ht')
    exact ⟨t, ht, transportsB_iff.mp htr⟩
  · intro h t' ht'
    obtain ⟨t, ht, htr⟩ := h t' ht'
    exact List.any_eq_true.mpr ⟨t, ht, transportsB_iff.mpr htr⟩

/-- A `true` `corrB` cell is in range on both sides — `corr_lt` through the
decider. -/
theorem corrB_lt {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} {i j : Nat}
    (h : corrB m lm w v i j = true) :
    i < w.unit.program.args.length ∧ j < v.unit.program.args.length :=
  corr_lt (corrB_iff.mp h)

/-- **One directed bisimulation scan**, over abstract index relations.

    source (n)                      target (m)

        i ───────── corr ──────────► j
        ▲                            ▲
        │ eSrc k i                   │ eTgt k' j
        │                            │
        k ───────── corr ──────────► k'   (∃ k')

The scan is bounded but loses nothing: `hcorr` says a `corr` cell bounds its
own pair, `hsrc` says an edge bounds its attacker, and the completeness
witness is bounded by `hcorr` at the witnessing pair. `forthB` is this at
`(corrB, edgeB w, edgeB v, n, m)`; `backB` is this at the swap. -/
def bisimScanB (corr eSrc eTgt : Nat → Nat → Bool) (n m : Nat) : Bool :=
  (List.range n).all fun i =>
    (List.range m).all fun j =>
      (List.range n).all fun k =>
        !(corr i j && eSrc k i) ||
          (List.range m).any fun k' => corr k k' && eTgt k' j

theorem bisimScanB_sound {corr eSrc eTgt : Nat → Nat → Bool} {n m : Nat}
    (hcorr : ∀ i j, corr i j = true → i < n ∧ j < m)
    (hsrc : ∀ k i, eSrc k i = true → k < n)
    (h : bisimScanB corr eSrc eTgt n m = true) :
    ∀ i j k, corr i j = true → eSrc k i = true →
      ∃ k', corr k k' = true ∧ eTgt k' j = true := by
  intro i j k hC hE
  unfold bisimScanB at h
  simp only [List.all_eq_true, List.mem_range] at h
  have hcell := h i (hcorr i j hC).1 j (hcorr i j hC).2 k (hsrc k i hE)
  rw [Bool.or_eq_true] at hcell
  rcases hcell with hno | hyes
  · rw [Bool.not_eq_true', Bool.and_eq_false_iff] at hno
    rcases hno with hno | hno
    · rw [hC] at hno; exact Bool.noConfusion hno
    · rw [hE] at hno; exact Bool.noConfusion hno
  · obtain ⟨k', _, hkk'⟩ := List.any_eq_true.mp hyes
    rw [Bool.and_eq_true] at hkk'
    exact ⟨k', hkk'.1, hkk'.2⟩

theorem bisimScanB_complete {corr eSrc eTgt : Nat → Nat → Bool} {n m : Nat}
    (hcorr : ∀ i j, corr i j = true → i < n ∧ j < m)
    (h : ∀ i j k, corr i j = true → eSrc k i = true →
      ∃ k', corr k k' = true ∧ eTgt k' j = true) :
    bisimScanB corr eSrc eTgt n m = true := by
  unfold bisimScanB
  simp only [List.all_eq_true, List.mem_range]
  intro i _ j _ k _
  rw [Bool.or_eq_true]
  cases hguard : corr i j && eSrc k i with
  | false => left; rfl
  | true =>
    right
    rw [Bool.and_eq_true] at hguard
    obtain ⟨k', hC', hE'⟩ := h i j k hguard.1 hguard.2
    exact List.any_eq_true.mpr
      ⟨k', List.mem_range.mpr (hcorr k k' hC').2, by
        rw [Bool.and_eq_true]; exact ⟨hC', hE'⟩⟩

/-- The `forth` scan: `bisimScanB` at the source-to-target orientation. -/
def forthB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Bool :=
  bisimScanB (corrB m lm w v) (edgeB w.unit.program) (edgeB v.unit.program)
    w.unit.program.args.length v.unit.program.args.length

theorem forthB_sound {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} (h : forthB m lm w v = true) :
    ∀ i j k, Corr m lm w v i j → edgeB w.unit.program k i = true →
      ∃ k', Corr m lm w v k k' ∧ edgeB v.unit.program k' j = true := by
  intro i j k hC hE
  obtain ⟨k', hC', hE'⟩ :=
    bisimScanB_sound (fun _ _ => corrB_lt)
      (fun k i hk => ((edgeB_faithful w.unit.program).ranged k i hk).1)
      h i j k (corrB_iff.mpr hC) hE
  exact ⟨k', corrB_iff.mp hC', hE'⟩

theorem forthB_complete {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam}
    (h : ∀ i j k, Corr m lm w v i j → edgeB w.unit.program k i = true →
      ∃ k', Corr m lm w v k k' ∧ edgeB v.unit.program k' j = true) :
    forthB m lm w v = true :=
  bisimScanB_complete (fun _ _ => corrB_lt) fun i j k hC hE => by
    obtain ⟨k', hC', hE'⟩ := h i j k (corrB_iff.mp hC) hE
    exact ⟨k', corrB_iff.mpr hC', hE'⟩

/-- The `back` scan: `bisimScanB` at the transposed orientation. -/
def backB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Bool :=
  bisimScanB (fun j i => corrB m lm w v i j)
    (edgeB v.unit.program) (edgeB w.unit.program)
    v.unit.program.args.length w.unit.program.args.length

theorem backB_sound {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} (h : backB m lm w v = true) :
    ∀ i j k', Corr m lm w v i j → edgeB v.unit.program k' j = true →
      ∃ k, Corr m lm w v k k' ∧ edgeB w.unit.program k i = true := by
  intro i j k' hC hE
  obtain ⟨k, hC', hE'⟩ :=
    bisimScanB_sound (fun _ _ hb => ⟨(corrB_lt hb).2, (corrB_lt hb).1⟩)
      (fun k a hk => ((edgeB_faithful v.unit.program).ranged k a hk).1)
      h j i k' (corrB_iff.mpr hC) hE
  exact ⟨k, corrB_iff.mp hC', hE'⟩

theorem backB_complete {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam}
    (h : ∀ i j k', Corr m lm w v i j → edgeB v.unit.program k' j = true →
      ∃ k, Corr m lm w v k k' ∧ edgeB w.unit.program k i = true) :
    backB m lm w v = true :=
  bisimScanB_complete (fun _ _ hb => ⟨(corrB_lt hb).2, (corrB_lt hb).1⟩)
    fun j i k' hC hE => by
      obtain ⟨k, hC', hE'⟩ := h i j k' (corrB_iff.mp hC) hE
      exact ⟨k, corrB_iff.mpr hC', hE'⟩

/-- **The executable status-bridge checker**: the four
`StatusBridge` clauses, each scanned over the finite index ranges of the two
compiled programs. -/
def statusBridgeB (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Bool :=
  admitsB m lm w v && matchedB m lm w v && forthB m lm w v && backB m lm w v

/-- **Soundness.** A `true` scan is a `StatusBridge` — a conformance cell is
`statusBridgeB_sound (by decide)`. -/
theorem statusBridgeB_sound {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} (h : statusBridgeB m lm w v = true) :
    StatusBridge m lm w v := by
  unfold statusBridgeB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨ha, hm⟩, hf⟩, hb⟩ := h
  exact { admits := admitsB_iff.mp ha
        , matched := matchedB_iff.mp hm
        , forth := forthB_sound hf
        , back := backB_sound hb }

/-- **Completeness.** The range scan misses nothing: the `Prop` clauses' own
witnesses are in range (`corr_lt`), so a `StatusBridge` makes every scan
succeed. With soundness this also refutes: `statusBridgeB … = false` denies
`StatusBridge` by contraposition. -/
theorem statusBridgeB_complete {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} (h : StatusBridge m lm w v) :
    statusBridgeB m lm w v = true := by
  unfold statusBridgeB
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨admitsB_iff.mpr h.admits, matchedB_iff.mpr h.matched⟩,
    forthB_complete h.forth⟩, backB_complete h.back⟩

/-- The checker decides the T8 hypotheses exactly. -/
theorem statusBridgeB_iff {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} :
    statusBridgeB m lm w v = true ↔ StatusBridge m lm w v :=
  ⟨statusBridgeB_sound, statusBridgeB_complete⟩

end Decider
end Lara.PW
