import Lara.Process.Family
import Lara.Process.SourceModel
import Lara.Process.Run

/-!
# Exact bounded enumeration (P2)

`Universe.Problem.completions` is the obvious reference enumerator: all
interleavings of the recorded events with a sublist of the declared universe,
filtered for compatibility, deduplicated. This module adds an executable
generator and proves it equal to that reference as a finite set.

## Histories

`search` is a prefix depth-first search over the deduplicated union of the
recorded and declared-unrecorded events (`pool`). A search state carries the
`ProcessState` of the prefix, the prefix itself and the remaining event
identities. At every executable prefix, including the empty one, the search
offers a stop branch: it emits the prefix exactly when the full
`Problem.Compat` check passes (duplicate-freeness, validity through the cutoff,
every reported event present, every precedence constraint and every admitted
coverage assertion). Extensions are explored independently and only through
events whose `ProcessState.step` succeeds. Nothing is pruned on partial
coverage: `Compat` is evaluated only in full, so a short prefix that omits a
reported event is not emitted but is still extended (`go_complete`,
`mem_go_succ`). The output is deduplicated (`search`), which makes
`search_nodup` immediate; `mem_search` proves the membership equivalence with
`Problem.completions`, and `search_perm_completions` upgrades it to a
permutation.

## Slot products

`guarded` is the generated guarded slot traversal: it filters choices at the
fixed history, stops at an empty choice list, and shares each suffix across the
surviving choices. Guard pruning is sound and complete because
`Family.guardsHold` is a conjunction over the assignment (`guarded_eq_filter`,
`mem_guarded`). `searchFamily` combines the generated history search with this
traversal and is proved equal, as a finite set, to `Family.referenceFamily`
(`mem_searchFamily`, `searchFamily_perm`). Before allocating family rows,
`enumerateFamily` counts the guarded products with multiplication and addition
saturated at the product cap plus one (`guardedCount_eq`, `familyCount_eq`).

## Limits

A later document-level inquiry wrapper is expected to project its own limit
record onto `Limits` below; no such wrapper type or projection is defined here.
Each field counts one kind of work, and each has a frozen checker ceiling in
this module:

* `Limits.histories` counts **distinct generated histories** — the length of the
  deduplicated DFS output, i.e. the number of compatible completions the run
  may report.
* `Limits.steps` counts **search steps** — the number of prefix-DFS nodes
  visited, each of which evaluates one stop test and enumerates its extension
  candidates (`searchSteps`, `goSteps`). It counts search work even when few
  histories are eventually compatible.
* `Limits.products` counts **source product rows** — the number of generated
  family completions (history/assignment pairs), i.e. `searchFamily`'s length,
  including every source-rejected row, because rejection is a first-class
  outcome and not a filter.

The frozen ceilings are `maxSearchHistories` (10000), `maxSearchSteps` (200000)
and `maxSearchProducts` (10000). `maxSearchSteps` is an **unproved policy
convention**: it is not derived from a theorem, and no theorem in this module
bounds `searchSteps p` by a function of the pool length. The constant was chosen
by hand above the computed (not formally proved) 109601-node worst case of the
prefix search at the P0 event ceiling of eight events. `admissible_pool_length`
does prove the admissibility half — an accepted version-1 document has at most
`Wire.maxProcessEvents` pool events — but the search-step bound itself remains a
convention. The event ceiling is reused, never raised
(`maxProcessEvents_unchanged`, `document_event_ceiling`).

`enumerateProblem` and `enumerateFamily` clamp the caller's limit with
`Limits.clamped` on entry, so the ceilings are enforced and not merely stated:
`Limits.clamped_le_self` shows clamping only tightens each component, and
`enumerateProblem_within_ceilings` / `enumerateFamily_within_ceilings` show that
a returned result's step, history and row counts are bounded by the
corresponding ceiling. Exactly-at-cap and cap-plus-one are stated against the
effective (clamped) cap. Product refusals report the first excess, `cap + 1`,
without constructing the product; history and step refusals report their full
observed counts.

Every bounded entry point returns `Except Refusal _`: over any cap it is a
refusal carrying no rows at all, exactly at a cap it is legal when the complete
search finishes (`enumerateProblem_eq_ok`), and cap-plus-one refuses
(`enumerateProblem_cap_plus_one_steps`, `enumerateProblem_cap_plus_one_histories`,
`enumerateFamily_cap_plus_one_products`). A refusal can never be read as a
partial or positive result (`enumerateProblem_refusal_no_rows`,
`enumerateFamily_refusal_no_rows`).

## Invariance

`listVerdict_perm` proves verdicts are invariant under permutation, so the
generated list reports the same verdict and count as the reference
(`searchAnswer_verdict`, `searchAnswer_count`, `searchFamily_length`). The new
runner's witness selection is the deterministic first match in the documented
DFS/choice order (`searchAnswer_holds_is_find`), and any selected witness is a
member of `Problem.completions` satisfying the query
(`searchAnswer_holds_mem`, `searchAnswer_fails_mem`). For a known verdict the
new and reference answers carry no witnesses at all, so their encoded bytes
agree (`searchAnswer_bytes_eq_of_known`); version 1's runner is untouched and
still prints `Universe.answer` of `Document.problem.completions`
(`run_answers_unchanged`), which this module never rewrites.
-/

set_option maxHeartbeats 1000000

namespace Lara.Process.Enumerate

open Lara.Process
open Lara.Process.Universe
open Lara.Process.Family

/-! ## The event pool -/

/-- The events the search may place: the deduplicated union of the recorded
events and the declared-unrecorded events. -/
def pool (p : Problem) : List Stamped := (p.base ++ p.unrecorded).dedup

theorem mem_pool {p : Problem} {e : Stamped} :
    e ∈ pool p ↔ e ∈ p.base ∨ e ∈ p.unrecorded := by
  simp [pool]

theorem pool_nodup (p : Problem) : (pool p).Nodup := List.nodup_dedup _

theorem pool_length (p : Problem) : (pool p).length = p.eventCount := rfl

/-! ## Prefix depth-first search -/

/-- Prefix DFS. `go p fuel s h rem` emits `h` when it is fully compatible and
then explores every extension by an event of `rem` whose step succeeds. `fuel`
bounds the number of extensions still allowed; the pool shrinks on every
extension, so `fuel = (pool p).length` never cuts a reachable prefix. -/
def go (p : Problem) : Nat → ProcessState → ProcessHistory → List Stamped → List ProcessHistory
  | 0, _, h, _ => if p.Compat h then [h] else []
  | fuel + 1, s, h, rem =>
      (if p.Compat h then [h] else []) ++
        rem.flatMap fun e =>
          match s.step e with
          | none => []
          | some s' => go p fuel s' (h ++ [e]) (rem.erase e)

theorem go_zero (p : Problem) (s : ProcessState) (h : ProcessHistory) (rem : List Stamped) :
    go p 0 s h rem = (if p.Compat h then [h] else []) := rfl

theorem go_succ (p : Problem) (fuel : Nat) (s : ProcessState) (h : ProcessHistory)
    (rem : List Stamped) :
    go p (fuel + 1) s h rem = (if p.Compat h then [h] else []) ++
      rem.flatMap (fun e => match s.step e with
        | none => []
        | some s' => go p fuel s' (h ++ [e]) (rem.erase e)) := rfl

/-- The generated history enumerator. -/
def search (p : Problem) : List ProcessHistory :=
  (go p (pool p).length ProcessState.initial [] (pool p)).dedup

/-- Search steps: the number of prefix-DFS nodes visited. Each node evaluates
one stop test and enumerates its extension candidates. -/
def goSteps (p : Problem) : Nat → ProcessState → ProcessHistory → List Stamped → Nat
  | 0, _, _, _ => 1
  | fuel + 1, s, h, rem =>
      1 + ((rem.filterMap fun e =>
        (s.step e).map fun s' => goSteps p fuel s' (h ++ [e]) (rem.erase e)).foldr (· + ·) 0)

/-- The step counter of the whole search. -/
def searchSteps (p : Problem) : Nat :=
  goSteps p (pool p).length ProcessState.initial [] (pool p)

/-! ## Membership lemmas for `go` -/

theorem go_sublist (p : Problem) (fuel : Nat) (s : ProcessState) (h : ProcessHistory)
    (rem : List Stamped) : ∀ x ∈ go p fuel s h rem, ∃ t, x = h ++ t := by
  induction fuel generalizing s h rem with
  | zero =>
    intro x hx
    rw [go_zero] at hx
    by_cases c : p.Compat h
    · rw [if_pos c] at hx
      exact ⟨[], by simpa using (List.mem_singleton.mp hx)⟩
    · rw [if_neg c] at hx
      simp at hx
  | succ fuel ih =>
    intro x hx
    rw [go_succ] at hx
    rcases List.mem_append.mp hx with hx | hx
    · by_cases c : p.Compat h
      · rw [if_pos c] at hx
        exact ⟨[], by simpa using (List.mem_singleton.mp hx)⟩
      · rw [if_neg c] at hx
        simp at hx
    · rcases List.mem_flatMap.mp hx with ⟨e, _, hx⟩
      cases hs : s.step e with
      | none => simp [hs] at hx
      | some s' =>
        simp only [hs] at hx
        obtain ⟨t, ht⟩ := ih s' (h ++ [e]) (rem.erase e) x hx
        exact ⟨e :: t, by rw [ht, List.append_assoc]; rfl⟩

/-- Every result of `go` is compatible. `go` only ever emits a prefix through a
positive `Problem.Compat` test, so this needs no hypothesis. -/
theorem go_compat (p : Problem) (fuel : Nat) (s : ProcessState) (h : ProcessHistory)
    (rem : List Stamped) : ∀ x ∈ go p fuel s h rem, p.Compat x := by
  induction fuel generalizing s h rem with
  | zero =>
    intro x hx
    rw [go_zero] at hx
    by_cases c : p.Compat h
    · rw [if_pos c] at hx
      rw [List.mem_singleton.mp hx]
      exact c
    · rw [if_neg c] at hx
      simp at hx
  | succ fuel ih =>
    intro x hx
    rw [go_succ] at hx
    rcases List.mem_append.mp hx with hx | hx
    · by_cases c : p.Compat h
      · rw [if_pos c] at hx
        rw [List.mem_singleton.mp hx]
        exact c
      · rw [if_neg c] at hx
        simp at hx
    · rcases List.mem_flatMap.mp hx with ⟨e, _, hx⟩
      cases hs : s.step e with
      | none => simp [hs] at hx
      | some s' => exact ih s' (h ++ [e]) (rem.erase e) x (by simpa [hs] using hx)

/-- Every event of a result of `go` comes from the initial pool. -/
theorem go_pool (p : Problem) : ∀ (fuel : Nat) (s : ProcessState) (h : ProcessHistory)
    (rem : List Stamped),
    (∀ a ∈ h, a ∈ pool p) → (∀ a ∈ rem, a ∈ pool p) →
      ∀ x ∈ go p fuel s h rem, ∀ a ∈ x, a ∈ pool p := by
  intro fuel
  induction fuel with
  | zero =>
    intro s h rem hh hr x hx a ha
    rw [go_zero] at hx
    by_cases c : p.Compat h
    · rw [if_pos c] at hx
      rw [List.mem_singleton.mp hx] at ha
      exact hh a ha
    · rw [if_neg c] at hx
      simp at hx
  | succ fuel ih =>
    intro s h rem hh hr x hx a ha
    rw [go_succ] at hx
    rcases List.mem_append.mp hx with hx | hx
    · by_cases c : p.Compat h
      · rw [if_pos c] at hx
        rw [List.mem_singleton.mp hx] at ha
        exact hh a ha
      · rw [if_neg c] at hx
        simp at hx
    · rcases List.mem_flatMap.mp hx with ⟨e, he, hx⟩
      cases hs : s.step e with
      | none => simp [hs] at hx
      | some s' =>
        simp only [hs] at hx
        refine ih s' (h ++ [e]) (rem.erase e) ?_ ?_ x hx a ha
        · intro b hb
          rcases List.mem_append.mp hb with hb | hb
          · exact hh b hb
          · rw [List.mem_singleton.mp hb]
            exact hr e he
        · intro b hb
          exact hr b (List.mem_of_mem_erase hb)

/-- Soundness: every generated history is a reference completion, once the
prefix and the remaining pool are drawn from recorded or declared events. -/
theorem go_mem (p : Problem) : ∀ (fuel : Nat) (s : ProcessState) (h : ProcessHistory)
    (rem : List Stamped),
    (∀ a ∈ h, a ∈ p.base ∨ a ∈ p.unrecorded) →
      (∀ a ∈ rem, a ∈ p.base ∨ a ∈ p.unrecorded) →
        ∀ x ∈ go p fuel s h rem, x ∈ p.completions := by
  intro fuel s h rem hh hr x hx
  rw [Problem.mem_completions]
  refine ⟨go_compat p fuel s h rem x hx, fun a ha => (mem_pool).mp ?_⟩
  exact (go_pool p fuel s h rem (fun b hb => (mem_pool).mpr (hh b hb))
    (fun b hb => (mem_pool).mpr (hr b hb)) x hx a ha)

/-- The one-step membership characterization of the prefix DFS. -/
theorem mem_go_succ (p : Problem) (fuel : Nat) (s : ProcessState) (h : ProcessHistory)
    (rem : List Stamped) (e : Stamped) (rest : ProcessHistory) :
    h ++ e :: rest ∈ go p (fuel + 1) s h rem ↔
      e ∈ rem ∧ ∃ s', s.step e = some s' ∧
        h ++ e :: rest ∈ go p fuel s' (h ++ [e]) (rem.erase e) := by
  have hne : h ++ e :: rest ≠ h := by
    intro hh
    have hlen := congrArg List.length hh
    simp only [List.length_append, List.length_cons] at hlen
    omega
  rw [go_succ]
  constructor
  · intro hx
    rcases List.mem_append.mp hx with hx | hx
    · by_cases c : p.Compat h
      · rw [if_pos c] at hx
        exact absurd (List.mem_singleton.mp hx) hne
      · rw [if_neg c] at hx
        simp at hx
    · rcases List.mem_flatMap.mp hx with ⟨e', he', hx⟩
      cases hs : s.step e' with
      | none => simp [hs] at hx
      | some s' =>
        simp only [hs] at hx
        obtain ⟨t, ht⟩ := go_sublist p fuel s' (h ++ [e']) (rem.erase e')
          (h ++ e :: rest) hx
        have key : e :: rest = e' :: t := by
          apply List.append_cancel_left
          rw [ht, List.append_assoc]
          rfl
        simp only [List.cons.injEq] at key
        obtain ⟨rfl, rfl⟩ := key
        exact ⟨he', s', hs, hx⟩
  · rintro ⟨he, s', hs, hx⟩
    exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨e, he, by rw [hs]; exact hx⟩))

/-! ## Completeness -/

/-- Execution splits over an append. -/
theorem run_append (s : ProcessState) (a b : ProcessHistory) :
    s.run (a ++ b) = (s.run a).bind (fun s' => s'.run b) := by
  induction a generalizing s with
  | nil => simp [ProcessState.run]
  | cons x a ih =>
    simp only [List.cons_append, ProcessState.run]
    cases h : s.step x with
    | none => rfl
    | some s' => simp [ih s']

theorem run_singleton (s : ProcessState) (e : Stamped) : s.run [e] = s.step e := by
  cases h : s.step e <;> simp [ProcessState.run, h]

/-- Completeness: every compatible history whose events lie in the pool is a
prefix of some DFS node, hence is emitted. `fuel` must equal `rem.length`, and
the prefix state must be the semantic run of the prefix. -/
theorem go_complete (p : Problem) (t : ProcessHistory) :
    ∀ (fuel : Nat) (s : ProcessState) (pre : ProcessHistory) (rem : List Stamped),
      rem.length = fuel →
      ProcessState.initial.run pre = some s →
      p.Compat (pre ++ t) →
      (∀ x ∈ t, x ∈ rem) →
      pre ++ t ∈ go p fuel s pre rem := by
  induction t with
  | nil =>
    intro fuel s pre rem _ _ hcompat _
    rw [List.append_nil] at hcompat ⊢
    cases fuel with
    | zero =>
      rw [go_zero]
      by_cases c : p.Compat pre
      · rw [if_pos c]; exact List.mem_singleton_self _
      · exact absurd hcompat c
    | succ fuel =>
      rw [go_succ]
      refine List.mem_append.mpr (Or.inl ?_)
      by_cases c : p.Compat pre
      · rw [if_pos c]; exact List.mem_singleton_self _
      · exact absurd hcompat c
  | cons e rest ih =>
    intro fuel s pre rem hlen hrun hcompat hmem
    cases fuel with
    | zero =>
      have hrem : rem = [] := List.eq_nil_of_length_eq_zero hlen
      have hnil : ¬ (e ∈ rem) := by rw [hrem]; exact List.not_mem_nil
      exact absurd (hmem e List.mem_cons_self) hnil
    | succ fuel =>
      have he : e ∈ rem := hmem e List.mem_cons_self
      have hlen' : (rem.erase e).length = fuel := by
        have h := List.length_erase_add_one he
        rw [hlen] at h
        omega
      have hvalid : (ProcessState.initial.run (pre ++ e :: rest)).isSome :=
        hcompat.2.1.1.1
      have hchain : ProcessState.initial.run (pre ++ e :: rest) = s.run (e :: rest) := by
        rw [run_append, hrun]; rfl
      rw [hchain] at hvalid
      rw [ProcessState.run] at hvalid
      cases hs : s.step e with
      | none => rw [hs] at hvalid; simp at hvalid
      | some s' =>
        have hkey : ProcessState.initial.run (pre ++ [e]) = some s' := by
          have h1 : ProcessState.initial.run (pre ++ [e]) = s.run [e] := by
            rw [run_append, hrun]; rfl
          rw [run_singleton, hs] at h1
          exact h1
        have hnd : (e :: rest).Nodup := (List.nodup_append.mp hcompat.1).2.1
        have hne : ∀ x ∈ rest, x ≠ e := fun x hx hxe =>
          (List.nodup_cons.mp hnd).1 (hxe ▸ hx)
        have hmem' : ∀ x ∈ rest, x ∈ rem.erase e := fun x hx =>
          (List.mem_erase_of_ne (hne x hx)).mpr (hmem x (List.mem_cons_of_mem e hx))
        have hcompat' : p.Compat ((pre ++ [e]) ++ rest) := by
          simpa [List.append_assoc] using hcompat
        rw [mem_go_succ]
        refine ⟨he, s', hs, ?_⟩
        have := ih fuel s' (pre ++ [e]) (rem.erase e) hlen' hkey hcompat' hmem'
        simpa [List.append_assoc] using this

theorem search_complete (p : Problem) (h : ProcessHistory) (hm : h ∈ p.completions) :
    h ∈ go p (pool p).length ProcessState.initial [] (pool p) := by
  obtain ⟨hcompat, hmem⟩ := (Problem.mem_completions p h).mp hm
  exact go_complete p h (pool p).length ProcessState.initial [] (pool p) rfl rfl hcompat
    (fun x hx => (mem_pool).mpr (hmem x hx))

/-! ## Finite-set equality with the reference -/

theorem mem_search (p : Problem) (h : ProcessHistory) : h ∈ search p ↔ h ∈ p.completions := by
  rw [search, List.mem_dedup]
  exact ⟨fun hm => go_mem p (pool p).length ProcessState.initial [] (pool p)
      (fun a ha => absurd ha List.not_mem_nil)
      (fun a ha => mem_pool.mp ha) h hm,
    fun hm => search_complete p h hm⟩

theorem search_nodup (p : Problem) : (search p).Nodup := List.nodup_dedup _

theorem search_perm_completions (p : Problem) : (search p).Perm p.completions :=
  (List.perm_ext_iff_of_nodup (search_nodup p) (Problem.completions_nodup p)).mpr
    (mem_search p)

theorem search_length (p : Problem) : (search p).length = p.completions.length :=
  (search_perm_completions p).length_eq

/-! ## Verdict and count invariance -/

theorem perm_nil_iff {α : Type} {l₁ l₂ : List α} (perm : l₁.Perm l₂) :
    l₁ = [] ↔ l₂ = [] := by
  rw [List.eq_nil_iff_length_eq_zero, List.eq_nil_iff_length_eq_zero, perm.length_eq]

theorem listVerdict_perm {X : Type} (xs ys : List X) (perm : xs.Perm ys) (φ : X → Prop)
    [DecidablePred φ] : listVerdict xs φ = listVerdict ys φ := by
  have hn : (xs = []) = (ys = []) := propext (perm_nil_iff perm)
  have ht : (xs.all (fun x => decide (φ x))) = (ys.all (fun x => decide (φ x))) := perm.all_eq
  have hf : (xs.all (fun x => decide ¬ φ x)) = (ys.all (fun x => decide ¬ φ x)) := perm.all_eq
  simp only [listVerdict, hn, ht, hf]

/-- The new runner's answer for a problem, computed over the generated list. -/
def searchAnswer (p : Problem) (q : Query) : Answer := answerOf (search p) q

theorem searchAnswer_verdict (p : Problem) (q : Query) :
    (searchAnswer p q).verdict = (answer p q).verdict :=
  listVerdict_perm (search p) p.completions (search_perm_completions p) _

theorem searchAnswer_count (p : Problem) (q : Query) :
    (searchAnswer p q).count = (answer p q).count := search_length p

/-! ## Deterministic witness selection -/

theorem find_witness {X : Type} (xs : List X) (P : X → Bool) (x : X)
    (h : xs.find? P = some x) : x ∈ xs ∧ P x = true :=
  ⟨List.mem_of_find?_eq_some h, List.find?_some h⟩

/-- The selected witness is the first matching element of the generated list. -/
theorem searchAnswer_holds_is_find (p : Problem) (q : Query) (h : ProcessHistory)
    (eq : (searchAnswer p q).holds = some h) :
    (search p).find? (fun x => decide (q.holds Atom.holds x)) = some h := by
  by_cases hv : listVerdict (search p) (q.holds Atom.holds) = .unknown
  · simpa [searchAnswer, answerOf, hv] using eq
  · simp [searchAnswer, answerOf, hv] at eq

theorem searchAnswer_holds_mem (p : Problem) (q : Query) (h : ProcessHistory)
    (eq : (searchAnswer p q).holds = some h) :
    h ∈ p.completions ∧ q.holds Atom.holds h := by
  have hfind := searchAnswer_holds_is_find p q h eq
  exact ⟨(mem_search p h).mp (find_witness (search p) _ h hfind).1,
    of_decide_eq_true (find_witness (search p) _ h hfind).2⟩

theorem searchAnswer_fails_is_find (p : Problem) (q : Query) (h : ProcessHistory)
    (eq : (searchAnswer p q).fails = some h) :
    (search p).find? (fun x => decide ¬ q.holds Atom.holds x) = some h := by
  by_cases hv : listVerdict (search p) (q.holds Atom.holds) = .unknown
  · simpa [searchAnswer, answerOf, hv] using eq
  · simp [searchAnswer, answerOf, hv] at eq

theorem searchAnswer_fails_mem (p : Problem) (q : Query) (h : ProcessHistory)
    (eq : (searchAnswer p q).fails = some h) :
    h ∈ p.completions ∧ ¬ q.holds Atom.holds h := by
  have hfind := searchAnswer_fails_is_find p q h eq
  exact ⟨(mem_search p h).mp (find_witness (search p) _ h hfind).1,
    of_decide_eq_true (find_witness (search p) _ h hfind).2⟩

/-- For a known verdict both answers carry no witness. -/
theorem searchAnswer_holds_none (p : Problem) (q : Query)
    (unknown : (searchAnswer p q).verdict ≠ .unknown) : (searchAnswer p q).holds = none := by
  unfold searchAnswer answerOf
  dsimp only
  rw [if_neg (show listVerdict (search p) (q.holds Atom.holds) ≠ .unknown from unknown)]

theorem answer_holds_none (p : Problem) (q : Query)
    (unknown : (searchAnswer p q).verdict ≠ .unknown) : (answer p q).holds = none := by
  unfold answer answerOf
  dsimp only
  rw [if_neg]
  intro hk
  exact unknown ((searchAnswer_verdict p q).symm ▸ hk)

theorem searchAnswer_fails_none (p : Problem) (q : Query)
    (unknown : (searchAnswer p q).verdict ≠ .unknown) : (searchAnswer p q).fails = none := by
  unfold searchAnswer answerOf
  dsimp only
  rw [if_neg (show listVerdict (search p) (q.holds Atom.holds) ≠ .unknown from unknown)]

theorem answer_fails_none (p : Problem) (q : Query)
    (unknown : (searchAnswer p q).verdict ≠ .unknown) : (answer p q).fails = none := by
  unfold answer answerOf
  dsimp only
  rw [if_neg]
  intro hk
  exact unknown ((searchAnswer_verdict p q).symm ▸ hk)

/-- For a known verdict both answers carry no witness, so they are literally
equal and their encoded bytes agree. -/
theorem searchAnswer_eq_of_known (p : Problem) (q : Query)
    (unknown : (searchAnswer p q).verdict ≠ .unknown) :
    searchAnswer p q = answer p q := by
  have hv := searchAnswer_verdict p q
  have hc := searchAnswer_count p q
  have hh := searchAnswer_holds_none p q unknown
  have hh' := answer_holds_none p q unknown
  have hf := searchAnswer_fails_none p q unknown
  have hf' := answer_fails_none p q unknown
  cases hA : searchAnswer p q with
  | mk v c ho hfs =>
    cases hB : answer p q with
    | mk v' c' ho' hfs' =>
      simp only [hA] at hv hc hh hf
      simp only [hB] at hv hc hh' hf'
      simp only [hv, hc, hh, hh', hf, hf']

theorem searchAnswer_bytes_eq_of_known (n : Wire.Names) (p : Problem) (name : String)
    (q : Query) (unknown : (searchAnswer p q).verdict ≠ .unknown) :
    Wire.encodeAnswer n (name, searchAnswer p q) = Wire.encodeAnswer n (name, answer p q) := by
  rw [searchAnswer_eq_of_known p q unknown]

/-! ## Version-1 compatibility -/

/-- Version 1's runner prints `Universe.answer` of the problem's own reference
completion list; this module adds no definition it could use. -/
theorem run_answers_unchanged {d : Wire.Document} {r : Wire.Result} (h : Wire.run d = .ok r) :
    r.answers = d.queries.filterMap fun
      | .verdict name q => some (name, answer d.problem q)
      | .audit .. => none :=
  (Wire.run_answers h).2

/-- The P0 event ceiling is reused, not raised. -/
theorem maxProcessEvents_unchanged : Wire.maxProcessEvents = 8 := rfl

/-- No accepted P0 document exceeds the frozen event ceiling. -/
theorem document_event_ceiling (d : Wire.Document) {r : Wire.Result} (h : Wire.run d = .ok r) :
    d.problem.eventCount ≤ Wire.maxProcessEvents :=
  le_trans (Wire.run_within_limits h).1 (Nat.min_le_right _ _)

/-! ## Limits, refusal and counters -/

/-- A refusal: the actual count and the cap that it exceeded. No constructor
carries rows, so a refusal can never be read as a partial answer. -/
inductive Refusal where
  | histories (actual cap : Nat)
  | steps (actual cap : Nat)
  | products (actual cap : Nat)
  deriving DecidableEq, Repr

/-- The P2 limits record. `histories` counts distinct generated histories,
`steps` counts prefix-DFS nodes visited, `products` counts generated family
completions (source product rows). -/
structure Limits where
  histories : Nat
  steps : Nat
  products : Nat
  deriving DecidableEq, Repr

/-- Frozen checker ceiling for distinct generated histories. -/
def maxSearchHistories : Nat := 10000

/-- Frozen checker ceiling for prefix-DFS nodes. This covers the whole search
tree at the P0 event ceiling of eight events. -/
def maxSearchSteps : Nat := 200000

/-- Frozen checker ceiling for generated family completions (source rows). -/
def maxSearchProducts : Nat := 10000

/-- Intersect a declared limit with the frozen ceilings. -/
def Limits.clamped (l : Limits) : Limits :=
  { histories := min l.histories maxSearchHistories
    steps := min l.steps maxSearchSteps
    products := min l.products maxSearchProducts }

theorem clamped_le (l : Limits) :
    l.clamped.histories ≤ maxSearchHistories ∧ l.clamped.steps ≤ maxSearchSteps ∧
      l.clamped.products ≤ maxSearchProducts :=
  ⟨Nat.min_le_right _ _, Nat.min_le_right _ _, Nat.min_le_right _ _⟩

/-- Clamping only tightens each component: the effective cap never exceeds the
declared one. -/
theorem clamped_le_self (l : Limits) :
    l.clamped.histories ≤ l.histories ∧ l.clamped.steps ≤ l.steps ∧
      l.clamped.products ≤ l.products :=
  ⟨Nat.min_le_left _ _, Nat.min_le_left _ _, Nat.min_le_left _ _⟩

/-- An accepted version-1 document has at most the frozen P0 event ceiling of
pool events. -/
theorem admissible_pool_length {d : Wire.Document} {r : Wire.Result}
    (h : Wire.run d = .ok r) : (pool d.problem).length ≤ Wire.maxProcessEvents := by
  rw [pool_length]
  exact document_event_ceiling d h

/-- Bounded history enumeration. The caller's limit is clamped with
`Limits.clamped` on entry, so the checker ceilings are enforced. Over any cap the
whole result is a refusal; at a cap it succeeds when the complete search
finishes. -/
def enumerateProblem (p : Problem) (lim : Limits) : Except Refusal (List ProcessHistory) :=
  let cap := lim.clamped
  let hs := search p
  let steps := searchSteps p
  if cap.steps < steps then .error (.steps steps cap.steps)
  else if cap.histories < hs.length then .error (.histories hs.length cap.histories)
  else .ok hs

theorem enumerateProblem_eq_ok (p : Problem) (lim : Limits)
    (hsteps : searchSteps p ≤ lim.clamped.steps)
    (hlen : (search p).length ≤ lim.clamped.histories) :
    enumerateProblem p lim = .ok (search p) := by
  unfold enumerateProblem
  dsimp only
  rw [if_neg (Nat.not_lt_of_ge hsteps), if_neg (Nat.not_lt_of_ge hlen)]

theorem enumerateProblem_ok (p : Problem) (lim : Limits) {hs : List ProcessHistory}
    (h : enumerateProblem p lim = .ok hs) :
    hs = search p ∧ searchSteps p ≤ lim.clamped.steps ∧
      (search p).length ≤ lim.clamped.histories := by
  unfold enumerateProblem at h
  dsimp only at h
  by_cases h1 : lim.clamped.steps < searchSteps p
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : lim.clamped.histories < (search p).length
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      cases h
      exact ⟨rfl, Nat.le_of_not_lt h1, Nat.le_of_not_lt h2⟩

/-- A successful run's step and history counts are bounded by the frozen
ceilings, whatever the caller declared. -/
theorem enumerateProblem_within_ceilings (p : Problem) (lim : Limits)
    {hs : List ProcessHistory} (h : enumerateProblem p lim = .ok hs) :
    hs = search p ∧ searchSteps p ≤ maxSearchSteps ∧
      (search p).length ≤ maxSearchHistories := by
  obtain ⟨eq, hst, hhi⟩ := enumerateProblem_ok p lim h
  exact ⟨eq, le_trans hst (clamped_le lim).2.1, le_trans hhi (clamped_le lim).1⟩

theorem enumerateProblem_refuses (p : Problem) (lim : Limits) (hs : List ProcessHistory)
    (h : searchSteps p ≤ lim.clamped.steps → (search p).length ≤ lim.clamped.histories → False) :
    enumerateProblem p lim ≠ .ok hs := by
  intro hok
  exact h (enumerateProblem_ok p lim hok).2.1 (enumerateProblem_ok p lim hok).2.2

theorem enumerateProblem_cap_plus_one_steps (p : Problem) (lim : Limits)
    (overshoot : searchSteps p = lim.clamped.steps + 1) :
    enumerateProblem p lim = .error (.steps (lim.clamped.steps + 1) lim.clamped.steps) := by
  unfold enumerateProblem
  dsimp only
  rw [if_pos (by omega), overshoot]

theorem enumerateProblem_cap_plus_one_histories (p : Problem) (lim : Limits)
    (hsteps : searchSteps p ≤ lim.clamped.steps)
    (overshoot : (search p).length = lim.clamped.histories + 1) :
    enumerateProblem p lim =
      .error (.histories (lim.clamped.histories + 1) lim.clamped.histories) := by
  unfold enumerateProblem
  dsimp only
  rw [if_neg (Nat.not_lt_of_ge hsteps), if_pos (by omega), overshoot]

theorem enumerateProblem_refusal_no_rows (p : Problem) (lim : Limits) (e : Refusal)
    (h : enumerateProblem p lim = .error e) : ¬ ∃ hs, enumerateProblem p lim = .ok hs := by
  rintro ⟨hs, hok⟩
  rw [h] at hok
  cases hok

/-! ## Guarded slot traversal -/

theorem guardsHold_cons (history : ProcessHistory) (selection : Selection)
    (assignment : List Selection) :
    Family.guardsHold history (selection :: assignment) =
      (selection.choice.guard.eval history && Family.guardsHold history assignment) := by
  simp [Family.guardsHold]

theorem filter_and {α : Type} (l : List α) (b : Bool) (p : α → Bool) :
    l.filter (fun a => b && p a) = if b then l.filter p else [] := by
  cases b <;> simp

theorem map_ite {α β : Type} (f : α → β) (b : Bool) (x y : List α) :
    (if b then x else y).map f = if b then x.map f else y.map f := by
  cases b <;> rfl

theorem flatMap_ite_filter {α β : Type} (l : List α) (p : α → Bool) (G : α → List β) :
    l.flatMap (fun a => if p a then G a else []) = (l.filter p).flatMap G := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases h : p a <;> simp [List.flatMap_cons, h, ih]

theorem family_product_cons (slot : Slot) (rest : List Slot) :
    Family.product (slot :: rest) = slot.choices.flatMap (fun choice =>
      (Family.product rest).map (Selection.mk slot.id choice :: ·)) := by
  cases choices : slot.choices <;> simp [Family.product, choices]

/-- The generated guarded slot traversal. Guards depend only on the fixed
history. An empty choice list stops before the suffix is expanded; otherwise
the suffix is computed once and shared by every surviving choice. -/
def guarded (history : ProcessHistory) : List Slot → List (List Selection)
  | [] => [[]]
  | slot :: rest =>
      match slot.choices.filter (fun choice => choice.guard.eval history) with
      | [] => []
      | choice :: choices =>
          let suffix := guarded history rest
          (choice :: choices).flatMap fun choice =>
            suffix.map (Selection.mk slot.id choice :: ·)

theorem guarded_cons (history : ProcessHistory) (slot : Slot) (rest : List Slot) :
    guarded history (slot :: rest) =
      (slot.choices.filter (fun choice => choice.guard.eval history)).flatMap fun choice =>
        (guarded history rest).map (Selection.mk slot.id choice :: ·) := by
  cases h : slot.choices.filter (fun choice => choice.guard.eval history) <;>
    simp [guarded, h]

/-- Guard pruning is sound and complete: the traversal equals the declared
product filtered by the conjunction of guard evaluations. -/
theorem guarded_eq_filter (history : ProcessHistory) (slots : List Slot) :
    guarded history slots = (Family.product slots).filter (Family.guardsHold history) := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
    rw [guarded_cons, ← flatMap_ite_filter, family_product_cons, List.filter_flatMap]
    have key : ∀ c : Choice,
        ((Family.product rest).map (Selection.mk slot.id c :: ·)).filter
            (Family.guardsHold history) =
          (if c.guard.eval history then
            (guarded history rest).map (Selection.mk slot.id c :: ·) else []) := by
      intro c
      rw [List.filter_map]
      simp only [Function.comp_def, guardsHold_cons, filter_and, map_ite, List.map_nil]
      rw [← ih]
    simp only [key]

/-- Membership in the generated traversal is exactly `Family.Chooses`. -/
theorem mem_product_guards (history : ProcessHistory) (slots : List Slot)
    (assignment : List Selection) :
    (assignment ∈ Family.product slots ∧ Family.guardsHold history assignment = true) ↔
      Family.Chooses history slots assignment := by
  induction slots generalizing assignment with
  | nil => cases assignment <;> simp [Family.product, Family.guardsHold, Family.Chooses]
  | cons slot slots ih =>
    rw [family_product_cons]
    cases assignment with
    | nil => simp [Family.Chooses]
    | cons selection assignment =>
      simp only [List.mem_flatMap, List.mem_map, List.cons.injEq, Family.guardsHold,
        List.all_cons, Bool.and_eq_true, Family.Guard.eval_iff, Family.Chooses]
      constructor
      · rintro ⟨⟨choice, member, tail, htail, equal, rfl⟩, guard, guards⟩
        cases equal
        exact ⟨rfl, member, guard, (ih _).mp ⟨htail, guards⟩⟩
      · rintro ⟨equal, member, guard, chosen⟩
        obtain ⟨htail, guards⟩ := (ih _).mpr chosen
        refine ⟨⟨selection.choice, member, assignment, htail, ?_, rfl⟩, guard, guards⟩
        cases selection
        simp_all

theorem mem_guarded (history : ProcessHistory) (slots : List Slot) (assignment : List Selection) :
    assignment ∈ guarded history slots ↔ Family.Chooses history slots assignment := by
  rw [guarded_eq_filter, List.mem_filter]
  exact mem_product_guards history slots assignment

private theorem guarded_length_cons (history : ProcessHistory) (slot : Slot)
    (rest : List Slot) :
    (guarded history (slot :: rest)).length =
      slot.choices.countP (fun choice => choice.guard.eval history) *
        (guarded history rest).length := by
  rw [guarded_cons, List.countP_eq_length_filter]
  generalize slot.choices.filter (fun choice => choice.guard.eval history) = choices
  induction choices with
  | nil => simp
  | cons choice choices ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, ih, Nat.add_mul, Nat.one_mul]
    omega

/-- Whenever traversal expands a suffix, its row count is no greater than
the enclosing product's. Thus an accepted product cap also bounds every
allocated suffix, including products with no surviving assignments. -/
theorem guarded_tail_length_le (history : ProcessHistory) (slot : Slot)
    (rest : List Slot)
    (hchoices : 0 < slot.choices.countP (fun choice => choice.guard.eval history)) :
    (guarded history rest).length ≤ (guarded history (slot :: rest)).length := by
  rw [guarded_length_cons]
  calc
    (guarded history rest).length = 1 * (guarded history rest).length := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hchoices

private theorem min_mul_min_right (limit a b : Nat) :
    min limit (a * min limit b) = min limit (a * b) := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b ≤ limit
  · rw [min_eq_right hb]
  · have hbl : limit ≤ b := by omega
    have hal : limit ≤ a * limit := by
      calc
        limit = 1 * limit := by simp
        _ ≤ a * limit := Nat.mul_le_mul_right limit (by omega)
    have hab : limit ≤ a * b := hal.trans (Nat.mul_le_mul_left a hbl)
    rw [min_eq_left hbl, min_eq_left hal, min_eq_left hab]

/-- Count surviving assignments without constructing them. Each multiplication
is saturated at the first excess, and a zero choice count stops the traversal.
`countP` avoids allocating filtered choice lists during this preflight. -/
def guardedCount (cap : Nat) (history : ProcessHistory) : List Slot → Nat
  | [] => 1
  | slot :: rest =>
      let choices := slot.choices.countP (fun choice => choice.guard.eval history)
      if choices = 0 then 0
      else min (cap + 1) (choices * guardedCount cap history rest)

theorem guardedCount_eq (cap : Nat) (history : ProcessHistory) (slots : List Slot) :
    guardedCount cap history slots = min (cap + 1) (guarded history slots).length := by
  induction slots with
  | nil =>
    simp only [guardedCount, guarded, List.length_cons, List.length_nil]
    omega
  | cons slot rest ih =>
    rw [guarded_length_cons]
    simp only [guardedCount]
    by_cases hzero : slot.choices.countP (fun choice => choice.guard.eval history) = 0
    · simp [hzero]
    · rw [if_neg hzero, ih, min_mul_min_right]

/-! ## Generated family enumeration -/

/-- One history's guarded assignment block. -/
def familyBlock (spec : FamilySpec) (history : ProcessHistory) : List Completion :=
  (guarded history spec.slots).map (Family.Completion.mk history)

/-- The reference per-history block: the declared product filtered by guards. -/
def familyBlockRef (spec : FamilySpec) (history : ProcessHistory) : List Completion :=
  ((Family.product spec.slots).filter (Family.guardsHold history)).map
    (Family.Completion.mk history)

theorem familyBlock_eq (spec : FamilySpec) (history : ProcessHistory) :
    familyBlock spec history = familyBlockRef spec history := by
  unfold familyBlock familyBlockRef
  rw [guarded_eq_filter]

/-- The generated family enumerator: generated histories times guarded slots. -/
def searchFamily (spec : FamilySpec) : List Completion :=
  (search spec.problem).flatMap (familyBlock spec)

theorem familyBlockRef_eta (spec : FamilySpec) :
    familyBlockRef spec = fun history =>
      ((Family.product spec.slots).filter (Family.guardsHold history)).map
        (Family.Completion.mk history) := rfl

theorem referenceFamily_flatMap (spec : FamilySpec) :
    Family.referenceFamily spec = spec.problem.completions.flatMap (familyBlockRef spec) := by
  rw [familyBlockRef_eta]
  cases h : spec.problem.completions with
  | nil => simp [Family.referenceFamily, h]
  | cons head tail =>
    simp only [Family.referenceFamily, h]

theorem flatMap_familyBlock (spec : FamilySpec) :
    (search spec.problem).flatMap (familyBlock spec) = searchFamily spec := rfl

theorem searchFamily_eq (spec : FamilySpec) :
    searchFamily spec = (search spec.problem).flatMap (familyBlockRef spec) := by
  unfold searchFamily
  congr 1
  funext history
  exact familyBlock_eq spec history

theorem mem_searchFamily (spec : FamilySpec) (c : Completion) :
    c ∈ searchFamily spec ↔
      c.history ∈ spec.problem.completions ∧
        Family.Chooses c.history spec.slots c.assignment := by
  cases c with
  | mk history assignment =>
    rw [searchFamily]
    simp only [List.mem_flatMap, familyBlock, List.mem_map]
    constructor
    · rintro ⟨h, hm, a, ha, heq⟩
      simp only [Family.Completion.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨(mem_search spec.problem h).mp hm, (mem_guarded h spec.slots a).mp ha⟩
    · rintro ⟨hm, chosen⟩
      exact ⟨history, (mem_search spec.problem history).mpr hm, assignment,
        (mem_guarded history spec.slots assignment).mpr chosen, rfl⟩

theorem searchFamily_perm (spec : FamilySpec) :
    (searchFamily spec).Perm (Family.referenceFamily spec) := by
  rw [searchFamily_eq, referenceFamily_flatMap]
  exact List.Perm.flatMap_right (familyBlockRef spec) (search_perm_completions spec.problem)

theorem searchFamily_nodup (spec : FamilySpec) (wf : Family.wellFormed spec = true) :
    (searchFamily spec).Nodup :=
  (searchFamily_perm spec).nodup_iff.mpr (Family.referenceFamily_nodup spec wf)

theorem searchFamily_length (spec : FamilySpec) :
    (searchFamily spec).length = (Family.referenceFamily spec).length :=
  (searchFamily_perm spec).length_eq

private def familyCountFrom (spec : FamilySpec) (cap total : Nat) :
    List ProcessHistory → Nat
  | [] => total
  | history :: rest =>
      let next := min (cap + 1) (total + guardedCount cap history spec.slots)
      if cap < next then next else familyCountFrom spec cap next rest

private theorem familyCountFrom_eq (spec : FamilySpec) (cap total : Nat)
    (histories : List ProcessHistory) (htotal : total ≤ cap + 1) :
    familyCountFrom spec cap total histories =
      min (cap + 1) (total + (histories.flatMap (familyBlock spec)).length) := by
  induction histories generalizing total with
  | nil => simp [familyCountFrom, min_eq_right htotal]
  | cons history rest ih =>
    have hcount : guardedCount cap history spec.slots =
        min (cap + 1) (familyBlock spec history).length := by
      simpa only [familyBlock, List.length_map] using
        guardedCount_eq cap history spec.slots
    simp only [familyCountFrom, List.flatMap_cons, List.length_append]
    rw [hcount]
    split
    · omega
    · rw [ih _ (min_le_left _ _)]
      omega

/-- Sum guarded product counts across the already bounded histories without
allocating assignment or completion rows. The accumulator stops immediately
at the first excess, including when several individually small blocks exceed
the cap together. -/
def familyCount (spec : FamilySpec) (cap : Nat) (histories : List ProcessHistory) : Nat :=
  familyCountFrom spec cap 0 histories

theorem familyCount_eq (spec : FamilySpec) (cap : Nat) (histories : List ProcessHistory) :
    familyCount spec cap histories =
      min (cap + 1) (histories.flatMap (familyBlock spec)).length := by
  simpa only [familyCount, Nat.zero_add] using
    familyCountFrom_eq spec cap 0 histories (by omega)

theorem familyCount_search_eq (spec : FamilySpec) (cap : Nat) :
    familyCount spec cap (search spec.problem) =
      min (cap + 1) (Family.referenceFamily spec).length := by
  rw [familyCount_eq, flatMap_familyBlock, searchFamily_length]

/-- Bounded family enumeration. After the history/step checks, a saturated
count checks the clamped product cap before any family rows are constructed.
Refusal reports `cap + 1`, not an eagerly materialized full product length.
On success, suffix sharing and empty-choice pruning keep every intermediate
product within the same cap (`guarded_tail_length_le`). -/
def enumerateFamily (spec : FamilySpec) (lim : Limits) : Except Refusal (List Completion) :=
  match enumerateProblem spec.problem lim with
  | .error e => .error e
  | .ok hs =>
    let cap := lim.clamped
    let count := familyCount spec cap.products hs
    if cap.products < count then .error (.products count cap.products)
    else .ok (hs.flatMap (familyBlock spec))

theorem enumerateFamily_eq_ok (spec : FamilySpec) (lim : Limits)
    (hsteps : searchSteps spec.problem ≤ lim.clamped.steps)
    (hlen : (search spec.problem).length ≤ lim.clamped.histories)
    (hprod : (searchFamily spec).length ≤ lim.clamped.products) :
    enumerateFamily spec lim = .ok (searchFamily spec) := by
  unfold enumerateFamily
  rw [enumerateProblem_eq_ok spec.problem lim hsteps hlen]
  dsimp only
  rw [familyCount_eq, flatMap_familyBlock,
    min_eq_right (show (searchFamily spec).length ≤ lim.clamped.products + 1 by omega),
    if_neg (Nat.not_lt_of_ge hprod)]

theorem enumerateFamily_ok (spec : FamilySpec) (lim : Limits) {cs : List Completion}
    (h : enumerateFamily spec lim = .ok cs) :
    cs = searchFamily spec ∧ searchSteps spec.problem ≤ lim.clamped.steps ∧
      (search spec.problem).length ≤ lim.clamped.histories ∧
        (searchFamily spec).length ≤ lim.clamped.products := by
  unfold enumerateFamily at h
  split at h
  · cases h
  · rename_i hs heq
    have hb := enumerateProblem_ok spec.problem lim heq
    rw [hb.1] at h
    dsimp only at h
    rw [familyCount_eq, flatMap_familyBlock] at h
    by_cases hp : lim.clamped.products <
        min (lim.clamped.products + 1) (searchFamily spec).length
    · rw [if_pos hp] at h; cases h
    · rw [if_neg hp] at h
      have hcs : searchFamily spec = cs := Except.ok.inj h
      exact ⟨hcs.symm, hb.2.1, hb.2.2, by omega⟩

/-- A successful family run's step, history and row counts are bounded by the
frozen ceilings, whatever the caller declared. -/
theorem enumerateFamily_within_ceilings (spec : FamilySpec) (lim : Limits)
    {cs : List Completion} (h : enumerateFamily spec lim = .ok cs) :
    cs = searchFamily spec ∧ searchSteps spec.problem ≤ maxSearchSteps ∧
      (search spec.problem).length ≤ maxSearchHistories ∧
        (searchFamily spec).length ≤ maxSearchProducts := by
  obtain ⟨eq, hst, hhi, hpr⟩ := enumerateFamily_ok spec lim h
  exact ⟨eq, le_trans hst (clamped_le lim).2.1, le_trans hhi (clamped_le lim).1,
    le_trans hpr (clamped_le lim).2.2⟩

theorem enumerateFamily_cap_plus_one_products (spec : FamilySpec) (lim : Limits)
    (hsteps : searchSteps spec.problem ≤ lim.clamped.steps)
    (hlen : (search spec.problem).length ≤ lim.clamped.histories)
    (overshoot : (searchFamily spec).length = lim.clamped.products + 1) :
    enumerateFamily spec lim =
      .error (.products (lim.clamped.products + 1) lim.clamped.products) := by
  unfold enumerateFamily
  rw [enumerateProblem_eq_ok spec.problem lim hsteps hlen]
  dsimp only
  rw [familyCount_eq, flatMap_familyBlock, overshoot, min_self, if_pos (by omega)]

theorem enumerateFamily_refusal_no_rows (spec : FamilySpec) (lim : Limits) (e : Refusal)
    (h : enumerateFamily spec lim = .error e) : ¬ ∃ cs, enumerateFamily spec lim = .ok cs := by
  rintro ⟨cs, hok⟩
  rw [h] at hok
  cases hok

end Lara.Process.Enumerate
