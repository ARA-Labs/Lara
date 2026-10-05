/-
Located obligation sites: where inside a hole each open mandatory question is
left open (spec §4.4, §6.1; `docs/located-gap-decision.md` D12).

A hole's root obligation set `O` is transitive: spec §6.1 unions obligations
upward from premise and discharge subterms. A **site** of a question `q` in a
term `w` is a position `π` (spec §7) whose subterm is a rule instance that
leaves `q` open (`q ∈ H`) with `q` mandatory for its rule; every site
contributes `q` to the root obligation set.

`openSites Pi w` lists the sites of `w` in the traversal `collectObligations`
uses: the premise subterms in index order, then the discharge subterms in
discharge-map order, then the instance itself (post-order). It reads only the
term and the rule lookup, so the drivers compute it from the checked cache
(`Compile.CheckedHole.term`) and never re-run support inference.

Results:

* `openSites_sound` — every reported site is a genuine instance occurrence
  (`subterm w π`) that leaves `q` open and has `q` mandatory;
* `openSites_complete` — every such occurrence is reported (no typing needed);
* `mem_obligations_iff_sites` — for a typed `w : supports(p) ▷ O`, a question
  has a site exactly when it is in `O`, so grouping the sites by `O` loses no
  site and reports no extra question;
* `openSites_nodup` / `sitesFor_nodup` — under typing no site is reported twice,
  so the positions of one obligation are distinct;
* `sitesFor_ne_nil` — every root obligation has at least one site.
-/

import Lara.Compile

namespace Lara.Check

open Lara Lara.Support Lara.Attack

/-- A site: a question and the position of a rule occurrence leaving it open. -/
abbrev Site := QuestionId × Pos

/-- Prefix every site's position with one step. -/
def prefixSites (e : PosElem) (ss : List Site) : List Site :=
  ss.map fun s => (s.1, e :: s.2)

/-- The instance's own sites: its open mandatory questions, at the root. A rule
that does not resolve contributes none (such a term is never typed). -/
def ownSites (Pi : RuleId → Option Rule) (rn : RuleId) (H : List QuestionId) :
    List Site :=
  match Pi rn with
  | some r => (openMandatory r H).map fun q => (q, [])
  | none => []

mutual
  /-- Every site of a term, in `collectObligations` traversal order. -/
  def openSites (Pi : RuleId → Option Rule) : SupportTerm → List Site
    | .leaf _ => []
    | .inst rn _ ws D H _ =>
        openSitesList Pi 0 ws ++ openSitesDis Pi D ++ ownSites Pi rn H
  /-- The sites of premise subterms `k, k+1, …`, each under its premise step. -/
  def openSitesList (Pi : RuleId → Option Rule) :
      Nat → List SupportTerm → List Site
    | _, [] => []
    | k, w :: ws =>
        prefixSites (.prem k) (openSites Pi w) ++ openSitesList Pi (k + 1) ws
  /-- The sites of discharge subterms, each under its question step. -/
  def openSitesDis (Pi : RuleId → Option Rule) :
      List (QuestionId × SupportTerm) → List Site
    | [] => []
    | (q, w) :: rest =>
        prefixSites (.ques q) (openSites Pi w) ++ openSitesDis Pi rest
end

/-- The positions of the sites of `q`, in site order. -/
def sitesFor (sites : List Site) (q : QuestionId) : List Pos :=
  (sites.filter fun s => decide (s.1 = q)).map Prod.snd

/-- One verdict obligation row per root obligation: the question and its sites
(spec §4.4 `(obligation ID POS+)`), in the order of `O`. -/
def obligationSites (Pi : RuleId → Option Rule) (w : SupportTerm)
    (O : List QuestionId) : List (QuestionId × List Pos) :=
  let sites := openSites Pi w
  O.map fun q => (q, sitesFor sites q)

/-! ### Membership in the traversal -/

theorem mem_prefixSites {e : PosElem} {ss : List Site} {s : Site} :
    s ∈ prefixSites e ss ↔ ∃ π, s.2 = e :: π ∧ (s.1, π) ∈ ss := by
  unfold prefixSites
  constructor
  · intro h
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
    exact ⟨t.2, rfl, ht⟩
  · rintro ⟨π, hπ, hmem⟩
    exact List.mem_map.mpr ⟨(s.1, π), hmem, by
      obtain ⟨a, b⟩ := s
      simp only at hπ
      simp [hπ]⟩

theorem mem_ownSites {Pi : RuleId → Option Rule} {rn : RuleId}
    {H : List QuestionId} {s : Site} :
    s ∈ ownSites Pi rn H ↔
      ∃ r, Pi rn = some r ∧ s.2 = [] ∧ s.1 ∈ openMandatory r H := by
  unfold ownSites
  cases hr : Pi rn with
  | none => simp
  | some r =>
    constructor
    · intro h
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
      exact ⟨r, rfl, rfl, hq⟩
    · rintro ⟨r', hr', hπ, hq⟩
      cases hr'
      exact List.mem_map.mpr ⟨s.1, hq, by
        obtain ⟨a, b⟩ := s
        simp only at hπ
        simp [hπ]⟩

theorem mem_openSitesList {Pi : RuleId → Option Rule} {s : Site} :
    ∀ {ws : List SupportTerm} {k : Nat},
      s ∈ openSitesList Pi k ws ↔
        ∃ i w π, ws[i]? = some w ∧ s.2 = .prem (k + i) :: π ∧
          (s.1, π) ∈ openSites Pi w := by
  intro ws
  induction ws with
  | nil => intro k; simp [openSitesList]
  | cons w ws ih =>
    intro k
    simp only [openSitesList, List.mem_append, mem_prefixSites, ih]
    constructor
    · rintro (⟨π, hπ, hmem⟩ | ⟨i, w', π, hw', hπ, hmem⟩)
      · exact ⟨0, w, π, rfl, by simpa using hπ, hmem⟩
      · exact ⟨i + 1, w', π, by simpa using hw', by
          rw [hπ, Nat.add_assoc, Nat.add_comm 1 i], hmem⟩
    · rintro ⟨i, w', π, hw', hπ, hmem⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hw'
        subst hw'
        exact Or.inl ⟨π, by simpa using hπ, hmem⟩
      | succ j =>
        refine Or.inr ⟨j, w', π, by simpa using hw', ?_, hmem⟩
        rw [hπ, Nat.add_assoc, Nat.add_comm 1 j]

theorem mem_openSitesDis {Pi : RuleId → Option Rule} {s : Site} :
    ∀ {D : List (QuestionId × SupportTerm)},
      s ∈ openSitesDis Pi D ↔
        ∃ (j : Nat) (q : QuestionId) (w : SupportTerm) (π : Pos),
          D[j]? = some (q, w) ∧ s.2 = .ques q :: π ∧
          (s.1, π) ∈ openSites Pi w := by
  intro D
  induction D with
  | nil => simp [openSitesDis]
  | cons qw rest ih =>
    obtain ⟨q, w⟩ := qw
    simp only [openSitesDis, List.mem_append, mem_prefixSites, ih]
    constructor
    · rintro (⟨π, hπ, hmem⟩ | ⟨j, q', w', π, hw', hπ, hmem⟩)
      · exact ⟨0, q, w, π, rfl, hπ, hmem⟩
      · exact ⟨j + 1, q', w', π, by simpa using hw', hπ, hmem⟩
    · rintro ⟨j, q', w', π, hw', hπ, hmem⟩
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hw'
        obtain ⟨rfl, rfl⟩ := hw'
        exact Or.inl ⟨π, hπ, hmem⟩
      | succ j =>
        exact Or.inr ⟨j, q', w', π, by simpa using hw', hπ, hmem⟩

theorem mem_openSites_inst {Pi : RuleId → Option Rule} {rn : RuleId}
    {θ : Subst} {ws : List SupportTerm} {D : List (QuestionId × SupportTerm)}
    {H : List QuestionId} {α : Assurance} {s : Site} :
    s ∈ openSites Pi (.inst rn θ ws D H α) ↔
      (∃ i w π, ws[i]? = some w ∧ s.2 = .prem i :: π ∧
          (s.1, π) ∈ openSites Pi w) ∨
      (∃ (j : Nat) (q : QuestionId) (w : SupportTerm) (π : Pos),
          D[j]? = some (q, w) ∧ s.2 = .ques q :: π ∧
          (s.1, π) ∈ openSites Pi w) ∨
      (∃ r, Pi rn = some r ∧ s.2 = [] ∧ s.1 ∈ openMandatory r H) := by
  simp only [openSites, List.mem_append, mem_openSitesList, mem_openSitesDis,
    mem_ownSites, Nat.zero_add, or_assoc]

theorem mem_sitesFor {sites : List Site} {q : QuestionId} {π : Pos} :
    π ∈ sitesFor sites q ↔ (q, π) ∈ sites := by
  unfold sitesFor
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hs, rfl⟩ := List.mem_map.mp h
    have hmem := (List.mem_filter.mp hs).1
    have hq : a = q := of_decide_eq_true (List.mem_filter.mp hs).2
    subst hq
    exact hmem
  · intro h
    exact List.mem_map.mpr ⟨(q, π), List.mem_filter.mpr ⟨h, by simp⟩, rfl⟩

/-! ### Discharge lookup -/

theorem lookupDis_mem {D : List (QuestionId × SupportTerm)} {q : QuestionId}
    {w : SupportTerm} (h : lookupDis D q = some w) :
    ∃ j : Nat, D[j]? = some (q, w) := by
  induction D with
  | nil => simp [lookupDis] at h
  | cons qw rest ih =>
    obtain ⟨q', w'⟩ := qw
    unfold lookupDis at h
    by_cases hq : q' = q
    · subst hq
      simp only [if_true, Option.some.injEq] at h
      subst h
      exact ⟨0, rfl⟩
    · simp only [hq, if_false] at h
      obtain ⟨j, hj⟩ := ih h
      exact ⟨j + 1, by simpa using hj⟩

theorem lookupDis_of_nodup {D : List (QuestionId × SupportTerm)}
    (hnodup : (D.map Prod.fst).Nodup) {j : Nat} {q : QuestionId}
    {w : SupportTerm} (h : D[j]? = some (q, w)) :
    lookupDis D q = some w := by
  induction D generalizing j with
  | nil => simp at h
  | cons qw rest ih =>
    obtain ⟨q', w'⟩ := qw
    simp only [List.map_cons, List.nodup_cons] at hnodup
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [lookupDis]
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hne : q' ≠ q := by
        intro heq
        subst heq
        exact hnodup.1 (List.mem_map.mpr ⟨(q', w), List.mem_of_getElem? h, rfl⟩)
      simp only [lookupDis, hne, if_false]
      exact ih hnodup.2 h

/-! ### Soundness and completeness -/

section Typed

variable {canon : String → String} {Pi : RuleId → Option Rule}
  {Gamma : LeafId → Option Atom}
  {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}

/-- **Soundness.** Every reported site of a typed term is a rule occurrence
that leaves the question open, with the question mandatory for its rule. -/
theorem openSites_sound {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (hw : HasSupport canon Pi Gamma CertOk w C O) :
    ∀ {q : QuestionId} {π : Pos}, (q, π) ∈ openSites Pi w →
      ∃ rn θ ws D H α r,
        subterm w π = some (.inst rn θ ws D H α) ∧ Pi rn = some r ∧
          q ∈ H ∧ q ∈ mandatoryNames r := by
  induction hw with
  | leaf _ => intro q π h; simp [openSites] at h
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis ihprems ihdis =>
    intro q π h
    rcases mem_openSites_inst.mp h with
      ⟨i, w', π', hw', hπ, hmem⟩ | ⟨j, q', w', π', hw', hπ, hmem⟩ |
        ⟨r', hr', hπ, hq⟩
    · simp only at hπ
      subst hπ
      have hi := lt_of_getElem?_some hw'
      obtain ⟨A, hA⟩ := getElem?_some_of_lt Cs i (by have := hside.lenCs; omega)
      obtain ⟨O', hO⟩ := getElem?_some_of_lt Os i (by have := hside.lenOs; omega)
      obtain ⟨rn₁, θ₁, ws₁, D₁, H₁, α₁, r₁, hsub, hr₁, hq₁, hm₁⟩ :=
        ihprems i w' A O' hw' hA hO hmem
      exact ⟨rn₁, θ₁, ws₁, D₁, H₁, α₁, r₁, by simp [subterm, hw', hsub],
        hr₁, hq₁, hm₁⟩
    · simp only at hπ
      subst hπ
      have hj := lt_of_getElem?_some hw'
      obtain ⟨A, hA⟩ := getElem?_some_of_lt DCs j (by have := hside.lenDCs; omega)
      obtain ⟨O', hO⟩ := getElem?_some_of_lt DOs j (by have := hside.lenDOs; omega)
      obtain ⟨rn₁, θ₁, ws₁, D₁, H₁, α₁, r₁, hsub, hr₁, hq₁, hm₁⟩ :=
        ihdis j q' w' A O' hw' hA hO hmem
      have hlook := lookupDis_of_nodup hside.dNodup hw'
      exact ⟨rn₁, θ₁, ws₁, D₁, H₁, α₁, r₁, by simp [subterm, hlook, hsub],
        hr₁, hq₁, hm₁⟩
    · simp only at hπ hq
      subst hπ
      obtain ⟨hqH, hqm⟩ := List.mem_filter.mp hq
      exact ⟨rn, θ, ws, D, H, α, r', rfl, hr', hqH, memB_iff.mp hqm⟩

end Typed

/-- **Completeness.** Every rule occurrence that leaves a question open, with
the question mandatory for its rule, is reported as a site. No typing premise
is needed. -/
theorem openSites_complete {Pi : RuleId → Option Rule} :
    ∀ {π : Pos} {w : SupportTerm} {rn : RuleId} {θ : Subst}
      {ws : List SupportTerm} {D : List (QuestionId × SupportTerm)}
      {H : List QuestionId} {α : Assurance} {r : Rule} {q : QuestionId},
      subterm w π = some (.inst rn θ ws D H α) → Pi rn = some r →
        q ∈ H → q ∈ mandatoryNames r → (q, π) ∈ openSites Pi w := by
  intro π
  induction π with
  | nil =>
    intro w rn θ ws D H α r q hsub hr hq hm
    simp only [subterm, Option.some.injEq] at hsub
    subst hsub
    exact mem_openSites_inst.mpr (Or.inr (Or.inr ⟨r, hr, rfl,
      List.mem_filter.mpr ⟨hq, memB_iff.mpr hm⟩⟩))
  | cons e π ih =>
    intro w rn θ ws D H α r q hsub hr hq hm
    cases w with
    | leaf l => simp [subterm] at hsub
    | inst rn₀ θ₀ ws₀ D₀ H₀ α₀ =>
      cases e with
      | prem i =>
        simp only [subterm] at hsub
        cases hw : ws₀[i]? with
        | none => rw [hw] at hsub; cases hsub
        | some w' =>
          rw [hw] at hsub
          exact mem_openSites_inst.mpr (Or.inl ⟨i, w', π, hw, rfl,
            ih hsub hr hq hm⟩)
      | ques q' =>
        simp only [subterm] at hsub
        cases hw : lookupDis D₀ q' with
        | none => rw [hw] at hsub; cases hsub
        | some w' =>
          rw [hw] at hsub
          obtain ⟨j, hj⟩ := lookupDis_mem hw
          exact mem_openSites_inst.mpr (Or.inr (Or.inl ⟨j, q', w', π, hj, rfl,
            ih hsub hr hq hm⟩))

/-- Soundness and completeness together: under typing, the sites are exactly
the open mandatory rule occurrences. -/
theorem mem_openSites_iff {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (hw : HasSupport canon Pi Gamma CertOk w C O) {q : QuestionId} {π : Pos} :
    (q, π) ∈ openSites Pi w ↔
      ∃ rn θ ws D H α r,
        subterm w π = some (.inst rn θ ws D H α) ∧ Pi rn = some r ∧
          q ∈ H ∧ q ∈ mandatoryNames r := by
  constructor
  · exact openSites_sound hw
  · rintro ⟨rn, θ, ws, D, H, α, r, hsub, hr, hq, hm⟩
    exact openSites_complete hsub hr hq hm

/-! ### The questions of the sites are the root obligations -/

private theorem mem_collectObligations_iff {Os DOs : List (List QuestionId)}
    {r : Rule} {H : List QuestionId} {q : QuestionId} :
    q ∈ collectObligations Os DOs r H ↔
      (∃ (i : Nat) (O : List QuestionId), Os[i]? = some O ∧ q ∈ O) ∨
        (∃ (j : Nat) (O : List QuestionId), DOs[j]? = some O ∧ q ∈ O) ∨
        q ∈ openMandatory r H := by
  rw [collectObligations, unionAll, mem_dedupQuestions]
  simp only [List.mem_flatten, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨O, (hO | hO) | rfl, hq⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hO
      exact Or.inl ⟨i, O, hi, hq⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hO
      exact Or.inr (Or.inl ⟨j, O, hj, hq⟩)
    · exact Or.inr (Or.inr hq)
  · rintro (⟨i, O, hi, hq⟩ | ⟨j, O, hj, hq⟩ | hq)
    · exact ⟨O, Or.inl (Or.inl (List.mem_of_getElem? hi)), hq⟩
    · exact ⟨O, Or.inl (Or.inr (List.mem_of_getElem? hj)), hq⟩
    · exact ⟨_, Or.inr rfl, hq⟩

/-- **The site questions are the obligations.** For a typed term, a question has
a site exactly when it is a root obligation. -/
theorem mem_obligations_iff_sites {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (hw : HasSupport canon Pi Gamma CertOk w C O) :
    ∀ {q : QuestionId}, q ∈ O ↔ ∃ π, (q, π) ∈ openSites Pi w := by
  induction hw with
  | leaf _ => intro q; simp [openSites]
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis ihprems ihdis =>
    intro q
    rw [mem_collectObligations_iff]
    constructor
    · rintro (⟨i, O', hO, hq⟩ | ⟨j, O', hO, hq⟩ | hq)
      · have hi := lt_of_getElem?_some hO
        obtain ⟨w', hw'⟩ := getElem?_some_of_lt ws i
          (by have := hside.lenOs; omega)
        obtain ⟨A, hA⟩ := getElem?_some_of_lt Cs i
          (by have := hside.lenCs; have := hside.lenOs; omega)
        obtain ⟨π, hπ⟩ := (ihprems i w' A O' hw' hA hO).mp hq
        exact ⟨.prem i :: π, mem_openSites_inst.mpr
          (Or.inl ⟨i, w', π, hw', rfl, hπ⟩)⟩
      · have hj := lt_of_getElem?_some hO
        obtain ⟨⟨q', w'⟩, hw'⟩ := getElem?_some_of_lt D j
          (by have := hside.lenDOs; omega)
        obtain ⟨A, hA⟩ := getElem?_some_of_lt DCs j
          (by have := hside.lenDCs; have := hside.lenDOs; omega)
        obtain ⟨π, hπ⟩ := (ihdis j q' w' A O' hw' hA hO).mp hq
        exact ⟨.ques q' :: π, mem_openSites_inst.mpr
          (Or.inr (Or.inl ⟨j, q', w', π, hw', rfl, hπ⟩))⟩
      · exact ⟨[], mem_openSites_inst.mpr
          (Or.inr (Or.inr ⟨r, hside.rule, rfl, hq⟩))⟩
    · rintro ⟨π, hπ⟩
      rcases mem_openSites_inst.mp hπ with
        ⟨i, w', π', hw', _, hmem⟩ | ⟨j, q', w', π', hw', _, hmem⟩ |
          ⟨r', hr', _, hq⟩
      · have hi := lt_of_getElem?_some hw'
        obtain ⟨A, hA⟩ := getElem?_some_of_lt Cs i
          (by have := hside.lenCs; omega)
        obtain ⟨O', hO⟩ := getElem?_some_of_lt Os i
          (by have := hside.lenOs; omega)
        exact Or.inl ⟨i, O', hO, (ihprems i w' A O' hw' hA hO).mpr ⟨π', hmem⟩⟩
      · have hj := lt_of_getElem?_some hw'
        obtain ⟨A, hA⟩ := getElem?_some_of_lt DCs j
          (by have := hside.lenDCs; omega)
        obtain ⟨O', hO⟩ := getElem?_some_of_lt DOs j
          (by have := hside.lenDOs; omega)
        exact Or.inr (Or.inl ⟨j, O', hO,
          (ihdis j q' w' A O' hw' hA hO).mpr ⟨π', hmem⟩⟩)
      · have hr : r' = r := Option.some.inj (hr'.symm.trans hside.rule)
        subst hr
        exact Or.inr (Or.inr hq)

/-- Every root obligation of a typed term has at least one site. -/
theorem sitesFor_ne_nil {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (hw : HasSupport canon Pi Gamma CertOk w C O) {q : QuestionId}
    (hq : q ∈ O) : sitesFor (openSites Pi w) q ≠ [] := by
  obtain ⟨π, hπ⟩ := (mem_obligations_iff_sites hw).mp hq
  intro hnil
  have := mem_sitesFor.mpr hπ
  rw [hnil] at this
  cases this

/-! ### No site is reported twice -/

private theorem nodup_map_on {α β : Type _} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup →
      (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hinj, hnd => by
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, nodup_map_on (fun x hx y hy => hinj x (by simp [hx]) y
        (by simp [hy])) hnd.2⟩
      intro hmem
      obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hmem
      exact hnd.1 (hinj b (by simp [hb]) a (by simp) hfb ▸ hb)

private theorem prefixSites_nodup {e : PosElem} {ss : List Site}
    (h : ss.Nodup) : (prefixSites e ss).Nodup := by
  unfold prefixSites
  refine nodup_map_on ?_ h
  intro x _ y _ hxy
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [Prod.mk.injEq, List.cons.injEq] at hxy
  obtain ⟨rfl, -, rfl⟩ := hxy
  rfl

private theorem openSitesList_nodup {Pi : RuleId → Option Rule} :
    ∀ {ws : List SupportTerm} {k : Nat},
      (∀ w ∈ ws, (openSites Pi w).Nodup) → (openSitesList Pi k ws).Nodup := by
  intro ws
  induction ws with
  | nil => intro k _; simp [openSitesList]
  | cons w ws ih =>
    intro k h
    simp only [openSitesList]
    refine List.nodup_append.mpr ⟨prefixSites_nodup (h w (by simp)),
      ih (fun w' hw' => h w' (by simp [hw'])), ?_⟩
    intro s hs t ht hst
    subst hst
    obtain ⟨π, hπ, _⟩ := mem_prefixSites.mp hs
    obtain ⟨i, _, π', _, hπ', _⟩ := mem_openSitesList.mp ht
    rw [hπ] at hπ'
    simp only [List.cons.injEq, PosElem.prem.injEq] at hπ'
    omega

private theorem openSitesDis_nodup {Pi : RuleId → Option Rule} :
    ∀ {D : List (QuestionId × SupportTerm)}, (D.map Prod.fst).Nodup →
      (∀ qw ∈ D, (openSites Pi qw.2).Nodup) → (openSitesDis Pi D).Nodup := by
  intro D
  induction D with
  | nil => intro _ _; simp [openSitesDis]
  | cons qw rest ih =>
    intro hkeys h
    obtain ⟨q, w⟩ := qw
    simp only [List.map_cons, List.nodup_cons] at hkeys
    simp only [openSitesDis]
    refine List.nodup_append.mpr ⟨prefixSites_nodup (h (q, w) (by simp)),
      ih hkeys.2 (fun qw hqw => h qw (by simp [hqw])), ?_⟩
    intro s hs t ht hst
    subst hst
    obtain ⟨π, hπ, _⟩ := mem_prefixSites.mp hs
    obtain ⟨j, q', w', π', hj, hπ', _⟩ := mem_openSitesDis.mp ht
    rw [hπ] at hπ'
    simp only [List.cons.injEq, PosElem.ques.injEq] at hπ'
    obtain ⟨rfl, -⟩ := hπ'
    exact hkeys.1 (List.mem_map.mpr ⟨(q, w'), List.mem_of_getElem? hj, rfl⟩)

/-- **No duplicate site.** A typed term reports each (question, position) pair
at most once: premise steps are distinct indices, discharge keys are distinct
(`InstSide.dNodup`), and the open set is duplicate-free (`InstSide.hNodup`). -/
theorem openSites_nodup {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (hw : HasSupport canon Pi Gamma CertOk w C O) :
    (openSites Pi w).Nodup := by
  induction hw with
  | leaf _ => simp [openSites]
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis ihprems ihdis =>
    simp only [openSites]
    have hlist : (openSitesList Pi 0 ws).Nodup := by
      apply openSitesList_nodup
      intro w' hw'
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw'
      have hlt := lt_of_getElem?_some hi
      obtain ⟨A, hA⟩ := getElem?_some_of_lt Cs i (by have := hside.lenCs; omega)
      obtain ⟨O', hO⟩ := getElem?_some_of_lt Os i (by have := hside.lenOs; omega)
      exact ihprems i w' A O' hi hA hO
    have hdisn : (openSitesDis Pi D).Nodup := by
      apply openSitesDis_nodup hside.dNodup
      intro qw hqw
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hqw
      have hlt := lt_of_getElem?_some hj
      obtain ⟨A, hA⟩ := getElem?_some_of_lt DCs j (by have := hside.lenDCs; omega)
      obtain ⟨O', hO⟩ := getElem?_some_of_lt DOs j (by have := hside.lenDOs; omega)
      exact ihdis j qw.1 qw.2 A O' hj hA hO
    have hown : (ownSites Pi rn H).Nodup := by
      unfold ownSites
      rw [hside.rule]
      refine nodup_map_on ?_ (hside.hNodup.filter _)
      intro x _ y _ hxy
      simpa using hxy
    refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hlist, hdisn, ?_⟩,
      hown, ?_⟩
    · intro s hs t ht hst
      subst hst
      obtain ⟨i, _, π, _, hπ, _⟩ := mem_openSitesList.mp hs
      obtain ⟨j, _, _, π', _, hπ', _⟩ := mem_openSitesDis.mp ht
      rw [hπ] at hπ'
      simp at hπ'
    · intro s hs t ht hst
      subst hst
      obtain ⟨_, _, hπ, _⟩ := mem_ownSites.mp ht
      rcases List.mem_append.mp hs with hs | hs
      · obtain ⟨_, _, _, _, hπ', _⟩ := mem_openSitesList.mp hs
        rw [hπ] at hπ'
        simp at hπ'
      · obtain ⟨_, _, _, _, _, hπ', _⟩ := mem_openSitesDis.mp hs
        rw [hπ] at hπ'
        simp at hπ'

/-- The positions of one question are distinct whenever the sites are. -/
theorem sitesFor_nodup {sites : List Site} (h : sites.Nodup)
    (q : QuestionId) : (sitesFor sites q).Nodup := by
  unfold sitesFor
  refine nodup_map_on ?_ (h.filter _)
  intro x hx y hy hxy
  have hxq : x.1 = q := of_decide_eq_true (List.mem_filter.mp hx).2
  have hyq : y.1 = q := of_decide_eq_true (List.mem_filter.mp hy).2
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only at hxq hyq hxy
  subst hxq hyq hxy
  rfl

/-! ### The verdict row of a checked hole -/

/-- The obligation rows of a typed term list the root obligations in order. -/
theorem obligationSites_questions (Pi : RuleId → Option Rule)
    (w : SupportTerm) (O : List QuestionId) :
    (obligationSites Pi w O).map Prod.fst = O := by
  simp [obligationSites, Function.comp_def]

/-- **Row adequacy.** For a typed term, each obligation row carries a nonempty,
duplicate-free list of positions, each one a rule occurrence that leaves its
question open and has it mandatory; and every such occurrence of a root
obligation is listed. -/
theorem obligationSites_adequate {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (hw : HasSupport canon Pi Gamma CertOk w C O) :
    ∀ row ∈ obligationSites Pi w O,
      row.1 ∈ O ∧ row.2 ≠ [] ∧ row.2.Nodup ∧
        ∀ π, π ∈ row.2 ↔
          ∃ rn θ ws D H α r,
            subterm w π = some (.inst rn θ ws D H α) ∧ Pi rn = some r ∧
              row.1 ∈ H ∧ row.1 ∈ mandatoryNames r := by
  intro row hrow
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hrow
  exact ⟨hq, sitesFor_ne_nil hw hq, sitesFor_nodup (openSites_nodup hw) q,
    fun π => mem_sitesFor.trans (mem_openSites_iff hw)⟩

/-- The verdict obligation rows of a located hole, read from its checked term
and cached obligations, never by re-running support inference. -/
def holeObligationSites {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (h : Compile.CheckedHole canon Pi Gamma CertOk) :
    List (QuestionId × List Pos) :=
  obligationSites Pi h.term h.obligations

theorem holeObligationSites_adequate {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (h : Compile.CheckedHole canon Pi Gamma CertOk) :
    (holeObligationSites h).map Prod.fst = h.obligations ∧
      ∀ row ∈ holeObligationSites h,
        row.1 ∈ h.obligations ∧ row.2 ≠ [] ∧ row.2.Nodup ∧
          ∀ π, π ∈ row.2 ↔
            ∃ rn θ ws D H α r,
              subterm h.term π = some (.inst rn θ ws D H α) ∧ Pi rn = some r ∧
                row.1 ∈ H ∧ row.1 ∈ mandatoryNames r :=
  ⟨obligationSites_questions _ _ _, obligationSites_adequate h.valid⟩

end Lara.Check
