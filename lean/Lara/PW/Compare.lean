/-
PW0 T5 — the tagged comparison result and its adequacy (issue #192).

The executable comparison interface returns either a nonempty status profile
or an incomparability reason. Gate 3 of #192 — "incomparability cannot
collapse into a local Lara status" — is enforced three ways: *structurally*,
because `CrossResult` keeps reasons and profiles in different constructors and
`IncomparabilityReason` contains no `Status`, so no coercion exists to build;
*behaviorally*, by the theorems pinning each reason to exactly its defining
condition (undefined translation / no candidate world / all candidates
rejected) and the profile to exactly the statuses of accepted candidate
worlds; and *semantically*, by `not_sat_dia_of_incomparable` — with the
translation defined, an incomparable result means the model has **no accepted
witness at all**, which is a condition no local status could report.

Nonemptiness of the profile is structural too: `comparable` carries a first
element and a rest, never a bare (possibly empty) list.

`crossCompare` is generic over the world and query types and takes the finite
candidate list, the decidable acceptance, and the status function as explicit
inputs — the frame's `R`/`accept` are `Prop`-valued and carry no enumeration,
and the design is explicit that no complexity or executability claim applies
to an implicit set of admissible states without an effective finite
representation.

Those explicit inputs are exactly why the adequacy section exists. Nothing in
`crossCompare`'s type says the candidate list enumerates `R_b(w, ·)` or that
`acceptB` decides `accept_b(w, ·)` — it takes them on trust. `Presents` states
that obligation, and `mem_compare_iff_sat_dia` then proves the executable
interface computes the model's `⟨b⟩`. Without it `crossCompare` and `Sat` are
two unconnected islands and `Frame.translate` is a field no definition reads.
-/

import Lara.PW.Outer

namespace Lara.PW

open Lara.Grounded (Status)

/-- Why a comparison produced no status profile. None of these is a local
Lara status, and the type contains no `Status` — see the module header. -/
inductive IncomparabilityReason where
  /-- `τ_b(c)` is undefined -/
  | translationUndefined
  /-- no candidate target world (`R_b(w, ·)` empty) -/
  | noCandidateWorld
  /-- candidates exist but none is accepted -/
  | allCandidateBridgesRejected
deriving DecidableEq, Repr

/-- The tagged comparison result. `comparable` is a *nonempty* profile by
construction (`first :: rest`). -/
inductive CrossResult (α : Type) where
  | incomparable (reason : IncomparabilityReason)
  | comparable (first : α) (rest : List α)
deriving DecidableEq, Repr

/-- **The executable comparison.** Inputs: the translated query `t = τ_b(c)`,
the finite candidate list `{v | w R_b v}`, the decidable acceptance
`accept_b(w, ·)`, and the local status function of the target context. The
guard order is the design's: translation, then candidates, then acceptance.

Named `crossCompare`, not `compare`, and the prefix is load-bearing. Core
exports `Ord.compare` into the root namespace, so a plain `compare` here is
shadowed under `open Lara.PW` — and the failure is not confined to exotic
spellings. Ordinary applications still elaborate (argument shape decides), but
`unfold compare` reports `ambiguous term, use fully qualified name`, a bare
`@compare` reports `Ambiguous term`, and an unapplied `compare` silently
resolves to `Ord.compare` instead. Since the T5 proofs below reason about
unfolding this definition, and downstream modules that `open Lara.PW` will do
the same, the collision would land on exactly the next module written against
this interface. The repository declares no `Ord` instance anywhere, so nothing
is given up by leaving `compare` to core.

The theorem names below keep the `compare_*` prefix: they are namespace
qualified, collide with nothing, and are the citation keys the docs already use. -/
def crossCompare {W Q : Type} (t : Option Q) (candidates : List W)
    (acceptB : W → Bool) (statusOf : W → Q → Status) : CrossResult Status :=
  match t with
  | none => .incomparable .translationUndefined
  | some d =>
    if candidates.isEmpty then .incomparable .noCandidateWorld
    else
      match candidates.filter acceptB with
      | [] => .incomparable .allCandidateBridgesRejected
      | v :: vs => .comparable (statusOf v d) (vs.map (statusOf · d))

/-! ### T5 — each reason is pinned to its condition, and only there

Proof note: `unfold crossCompare` leaves the outer `match some d with …`
unreduced, so a following `rw [if_neg …]` reports "did not find an occurrence
of the pattern". `show (if candidates.isEmpty = true then _ else _) = _` forces the
reduction instead. Likewise `List.noConfusion` / `CrossResult.noConfusion`
fail here with a universe mismatch (`Eq.{1}` against `Eq.{?u+2}`); `absurd h
(by simp)` and `nomatch h` are the working forms. -/

theorem compare_none {W Q : Type} (candidates : List W)
    (acceptB : W → Bool) (statusOf : W → Q → Status) :
    crossCompare none candidates acceptB statusOf =
      .incomparable .translationUndefined := rfl

theorem compare_no_candidate {W Q : Type} (d : Q)
    (acceptB : W → Bool) (statusOf : W → Q → Status) :
    crossCompare (some d) ([] : List W) acceptB statusOf =
      .incomparable .noCandidateWorld := rfl

theorem compare_all_rejected {W Q : Type} (d : Q) {candidates : List W}
    (acceptB : W → Bool) (statusOf : W → Q → Status)
    (hne : candidates ≠ []) (hrej : candidates.filter acceptB = []) :
    crossCompare (some d) candidates acceptB statusOf =
      .incomparable .allCandidateBridgesRejected := by
  show (if candidates.isEmpty = true then _ else _) = _
  rw [if_neg (by simpa [List.isEmpty_iff] using hne), hrej]

theorem compare_comparable {W Q : Type} (d : Q) {candidates : List W}
    (acceptB : W → Bool) (statusOf : W → Q → Status)
    {v : W} {vs : List W} (hacc : candidates.filter acceptB = v :: vs) :
    crossCompare (some d) candidates acceptB statusOf =
      .comparable (statusOf v d) (vs.map (statusOf · d)) := by
  have hne : candidates ≠ [] := by
    intro h
    rw [h] at hacc
    exact absurd hacc (by simp)
  show (if candidates.isEmpty = true then _ else _) = _
  rw [if_neg (by simpa [List.isEmpty_iff] using hne), hacc]

theorem mem_compare_profile_iff {W Q : Type} {d : Q} {candidates : List W}
    {acceptB : W → Bool} {statusOf : W → Q → Status}
    {s₀ : Status} {rest : List Status}
    (h : crossCompare (some d) candidates acceptB statusOf = .comparable s₀ rest)
    (s : Status) :
    s ∈ s₀ :: rest ↔
      ∃ v ∈ candidates, acceptB v = true ∧ statusOf v d = s := by
  cases hacc : candidates.filter acceptB with
  | nil =>
    by_cases hne : candidates = []
    · subst hne
      rw [compare_no_candidate] at h
      exact absurd h (by simp)
    · rw [compare_all_rejected d acceptB statusOf hne hacc] at h
      exact absurd h (by simp)
  | cons v vs =>
    rw [compare_comparable d acceptB statusOf hacc] at h
    obtain ⟨h₀, hrest⟩ := CrossResult.comparable.inj h
    subst h₀; subst hrest
    constructor
    · intro hs
      have : s ∈ (v :: vs).map (statusOf · d) := by
        simpa using hs
      obtain ⟨u, hu, hus⟩ := List.mem_map.mp this
      have hu' : u ∈ candidates.filter acceptB := by rw [hacc]; exact hu
      have := List.mem_filter.mp hu'
      exact ⟨u, this.1, this.2, hus⟩
    · rintro ⟨u, hu, huacc, hus⟩
      have hu' : u ∈ candidates.filter acceptB :=
        List.mem_filter.mpr ⟨hu, huacc⟩
      rw [hacc] at hu'
      have : s ∈ (v :: vs).map (statusOf · d) :=
        List.mem_map.mpr ⟨u, hu', hus⟩
      simpa using this

theorem incomparable_ne_comparable {α : Type} (r : IncomparabilityReason)
    (s : α) (rest : List α) :
    (CrossResult.incomparable r : CrossResult α) ≠ .comparable s rest :=
  fun h => nomatch h


/-! ### Adequacy — the executable interface computes the model's `⟨b⟩` -/

/-- The executable inputs *present* the bridge at `w`: the candidate list
enumerates `R_b(w, ·)` and the Bool acceptance decides `accept_b(w, ·)`.
Without this, `crossCompare` takes its candidate list on trust and no theorem
relates it to the frame. -/
structure Presents (F : Frame) (b : F.B) (w : F.World (F.src b))
    (candidates : List (F.World (F.tgt b)))
    (acceptB : F.World (F.tgt b) → Bool) : Prop where
  mem_iff : ∀ v, v ∈ candidates ↔ F.R b w v
  accept_iff : ∀ v, acceptB v = true ↔ F.accept b w v

/-- **Adequacy.** A status appears in the executable profile exactly when the
model satisfies `⟨b⟩Status_s(τ_b(c))`. -/
theorem mem_compare_iff_sat_dia (F : Frame) (V : Valuation F) (b : F.B)
    (w : F.World (F.src b)) (c : F.Query (F.src b)) (d : F.Query (F.tgt b))
    (candidates : List (F.World (F.tgt b)))
    (acceptB : F.World (F.tgt b) → Bool)
    (statusOf : F.World (F.tgt b) → F.Query (F.tgt b) → Status)
    (hV : ∀ v q s, V v q s ↔ statusOf v q = s)
    (hP : Presents F b w candidates acceptB)
    (htr : F.translate b c = some d) (s : Status) :
    (∃ s₀ rest,
        crossCompare (F.translate b c) candidates acceptB statusOf
          = .comparable s₀ rest ∧ s ∈ s₀ :: rest)
      ↔ Sat F V (.dia b (.status s d)) w := by
  rw [htr]
  constructor
  · rintro ⟨s₀, rest, hcmp, hs⟩
    obtain ⟨v, hv, hacc, hst⟩ := (mem_compare_profile_iff hcmp s).mp hs
    exact ⟨v, ⟨(hP.mem_iff v).mp hv, (hP.accept_iff v).mp hacc⟩,
      (hV v d s).mpr hst⟩
  · rintro ⟨v, ⟨hR, hac⟩, hVs⟩
    have hv : v ∈ candidates := (hP.mem_iff v).mpr hR
    have hacc : acceptB v = true := (hP.accept_iff v).mpr hac
    have hmem : v ∈ candidates.filter acceptB := List.mem_filter.mpr ⟨hv, hacc⟩
    cases hf : candidates.filter acceptB with
    | nil => rw [hf] at hmem; exact absurd hmem (by simp)
    | cons u us =>
      refine ⟨statusOf u d, us.map (statusOf · d),
        compare_comparable d acceptB statusOf hf, ?_⟩
      exact (mem_compare_profile_iff
        (compare_comparable d acceptB statusOf hf) s).mpr
        ⟨v, hv, hacc, (hV v d s).mp hVs⟩

/-- **Gate 3, semantically.** With the translation *defined*, an incomparable
result means the model has no accepted witness at all — for any status. So
incomparability is not merely a different constructor from a status profile;
it reports a condition no local status could report. -/
theorem not_sat_dia_of_incomparable (F : Frame) (V : Valuation F) (b : F.B)
    (w : F.World (F.src b)) (c : F.Query (F.src b)) (d : F.Query (F.tgt b))
    (candidates : List (F.World (F.tgt b)))
    (acceptB : F.World (F.tgt b) → Bool)
    (statusOf : F.World (F.tgt b) → F.Query (F.tgt b) → Status)
    (hP : Presents F b w candidates acceptB)
    (htr : F.translate b c = some d) {r : IncomparabilityReason}
    (h : crossCompare (F.translate b c) candidates acceptB statusOf
          = .incomparable r) (s : Status) :
    ¬ Sat F V (.dia b (.status s d)) w := by
  rw [htr] at h
  have hnil : candidates.filter acceptB = [] := by
    cases hf : candidates.filter acceptB with
    | nil => rfl
    | cons u us =>
      rw [compare_comparable d acceptB statusOf hf] at h
      exact absurd h (by simp)
  rintro ⟨v, ⟨hR, hac⟩, _⟩
  have hmem : v ∈ candidates.filter acceptB :=
    List.mem_filter.mpr ⟨(hP.mem_iff v).mpr hR, (hP.accept_iff v).mpr hac⟩
  rw [hnil] at hmem
  exact absurd hmem (by simp)

/-- Undefined translation is exactly the `translationUndefined` report. -/
theorem compare_translationUndefined_iff (F : Frame) (b : F.B)
    (c : F.Query (F.src b)) (candidates : List (F.World (F.tgt b)))
    (acceptB : F.World (F.tgt b) → Bool)
    (statusOf : F.World (F.tgt b) → F.Query (F.tgt b) → Status) :
    crossCompare (F.translate b c) candidates acceptB statusOf
        = .incomparable .translationUndefined
      ↔ F.translate b c = none := by
  cases htr : F.translate b c with
  | none => simp [crossCompare]
  | some d =>
    constructor
    · intro h
      exfalso
      cases hf : candidates.filter acceptB with
      | nil =>
        by_cases hne : candidates = []
        · subst hne
          rw [compare_no_candidate] at h
          exact absurd h (by simp)
        · rw [compare_all_rejected d acceptB statusOf hne hf] at h
          exact absurd h (by simp)
      | cons u us =>
        rw [compare_comparable d acceptB statusOf hf] at h
        exact absurd h (by simp)
    · intro h
      exact absurd h (by simp)

end Lara.PW
