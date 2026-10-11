/-
Checked graph-difference locality (issue #22, plan P4).

**Scope: grounded semantics only.** Every preservation statement in this module
is about the executable grounded labelling `Grounded.labelC` and the four-state
claim status `Grounded.statusC`. Grounded labelling reads only a node's attack
ancestry, so an edit confined to nodes outside that ancestry (and to edges that
point nowhere into it) cannot move a label. That is *false* for stable
semantics, whose existence question reads the whole graph
(`Lara.Process.IsStable`): adding a self-attacking node outside every queried
ancestor can change stable-extension existence while leaving the grounded
certificate valid. This module therefore claims **no** locality for stable, or
for any other extension semantics.

**What is compared.** Two *actually checked* graphs are lifted to one common
stable-identity carrier (`Lara.Process.Source.Coordinates.graph`), so that
declaration reindexing and pruning are invisible: a helper index is never a
name. On that carrier this module defines

* the compiled edge list and each node's incoming-attacker list,
* the node and compiled-edge symmetric differences,
* finite backward reachability (`Lara.Process.Ancestry.ancestors`, added to
  `Lara.Process.Revision`) — every node from which a member of a seed set is
  attack-reachable — computed by a bounded closure proved stable within `|args|`
  steps, and proved to have exactly the `Lara.Process.Ancestor` members.

**The sufficient test.** `checkLocality` records the comparison facts
(supports, both ancestry regions, both symmetric differences) and accepts when
the support sets correspond and *both* regions carry the same members and the
same incoming-attacker lists in both graphs. Acceptance is proved equivalent to
a `Certificate`, and a `Certificate` supplies the hypotheses of the landed
directional-locality theorem `Lara.Process.grounded_directional_locality`
(worked instance: `Lara.Examples.ProcessRevision`) verbatim — hence label
equality at every support and equality of the complete claim's `statusC`,
requiring exact support correspondence. The certificate is **sufficient only**: a change inside the
region may cancel itself and leave the status alone, so a failed test does not
imply a changed status (fixtures in `Lara.Examples.ProcessLocality`).

The test is not the naive one. Comparing raw declaration names is insensitive
to the edges between them, and "no changed node lies in the old ancestry
region" is insensitive to a *new* attacker outside that region that attacks
into it. Both are recorded here as explicit weaker criteria
(`nodeDiffDisjoint`, `edgeDiffInternal`, and the examples' raw-name predicate)
so the countermodels can exhibit them passing while the status changes.
-/

import Lara.Blocked
import Lara.Process.Revision
import Lara.Process.Source
import Lara.Process.SourceCoordinates

namespace Lara.Process.Locality

open Lara.Grounded
open Lara.Process.Ancestry
open Lara.Process.Source

/-- Arguments are stable-identity carrier positions at this layer. -/
abbrev Node := Grounded.Arg

/-! ### Compiled edges and symmetric differences -/

/-- The compiled edge list of a framework, in carrier order. -/
def edges (F : AF) : List (Node × Node) :=
  F.args.flatMap fun a => (F.args.filter (fun b => F.attack a b)).map (fun b => (a, b))

theorem mem_edges {F : AF} {a b : Node} :
    (a, b) ∈ edges F ↔ a ∈ F.args ∧ b ∈ F.args ∧ F.attack a b = true := by
  unfold edges
  constructor
  · intro h
    obtain ⟨c, hc, h'⟩ := List.mem_flatMap.mp h
    obtain ⟨d, hd, he⟩ := List.mem_map.mp h'
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨hc, (List.mem_filter.mp hd).1, (List.mem_filter.mp hd).2⟩
  · rintro ⟨ha, hb, hatt⟩
    exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr
      ⟨b, List.mem_filter.mpr ⟨hb, hatt⟩, rfl⟩⟩

/-- The attackers of a node, in carrier order. -/
def incoming (F : AF) (b : Node) : List Node := F.args.filter fun a => F.attack a b

theorem mem_incoming {F : AF} {a b : Node} :
    a ∈ incoming F b ↔ a ∈ F.args ∧ F.attack a b = true := by
  simp [incoming, List.mem_filter]

/-- Node symmetric difference of two frameworks. -/
def nodeDiff (F G : AF) : List Node :=
  F.args.filter (fun a => !G.args.contains a) ++
    G.args.filter (fun a => !F.args.contains a)

theorem mem_nodeDiff {F G : AF} {a : Node} :
    a ∈ nodeDiff F G ↔
      (a ∈ F.args ∧ G.args.contains a = false) ∨ (a ∈ G.args ∧ F.args.contains a = false) := by
  simp [nodeDiff]

/-- Compiled-edge symmetric difference of two frameworks. -/
def edgeDiff (F G : AF) : List (Node × Node) :=
  (edges F).filter (fun e => !(edges G).contains e) ++
    (edges G).filter (fun e => !(edges F).contains e)

theorem mem_edgeDiff {F G : AF} {e : Node × Node} :
    e ∈ edgeDiff F G ↔
      (e ∈ edges F ∧ (edges G).contains e = false) ∨
        (e ∈ edges G ∧ (edges F).contains e = false) := by
  simp [edgeDiff]

/-! ### The sufficient test and its certificate -/

/-- Support sets correspond when they have the same members. -/
def SupportCorrespond (s t : List Node) : Prop := ∀ a, a ∈ s ↔ a ∈ t

/-- Every member of `region` is a member of both carriers and has the same
incoming-attacker list in both frameworks. -/
def Correlates (before after : AF) (region : List Node) : Prop :=
  ∀ y ∈ region, y ∈ before.args ∧ y ∈ after.args ∧ incoming before y = incoming after y

/-- The whole claim of the sufficient test: the queried supports correspond, and
both ancestry regions carry the same members and incoming attackers. -/
def LocalityClaim (before after : AF) (supportBefore supportAfter : List Node) : Prop :=
  SupportCorrespond supportBefore supportAfter ∧
    Correlates before after (ancestors before supportBefore) ∧
    Correlates before after (ancestors after supportAfter)

/-- `s` is contained in the carrier. -/
def Contained (F : AF) (s : List Node) : Bool := s.all fun a => F.args.contains a

theorem contained_iff {F : AF} {s : List Node} :
    Contained F s = true ↔ ∀ a ∈ s, a ∈ F.args := by
  simp [Contained]

/-- Executable support correspondence. -/
def supportCorresponds (s t : List Node) : Bool :=
  s.all (fun a => t.contains a) && t.all (fun a => s.contains a)

theorem supportCorresponds_iff {s t : List Node} :
    supportCorresponds s t = true ↔ SupportCorrespond s t := by
  simp only [supportCorresponds, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    SupportCorrespond]
  constructor
  · rintro ⟨h₁, h₂⟩ a
    exact ⟨fun ha => h₁ a ha, fun ha => h₂ a ha⟩
  · intro h
    exact ⟨fun a ha => (h a).mp ha, fun a ha => (h a).mpr ha⟩

/-- Executable region correspondence. -/
def correlates (before after : AF) (region : List Node) : Bool :=
  region.all fun y => before.args.contains y && after.args.contains y &&
    decide (incoming before y = incoming after y)

theorem correlates_iff {before after : AF} {region : List Node} :
    correlates before after region = true ↔ Correlates before after region := by
  simp only [correlates, List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem,
    decide_eq_true_eq, Correlates]
  constructor
  · rintro h y hy
    obtain ⟨⟨hb, ha⟩, hinc⟩ := h y hy
    exact ⟨hb, ha, hinc⟩
  · intro h y hy
    obtain ⟨hb, ha, hinc⟩ := h y hy
    exact ⟨⟨hb, ha⟩, hinc⟩

/-- The executable sufficient test. -/
def accepted (before after : AF) (supportBefore supportAfter : List Node) : Bool :=
  Contained before supportBefore && Contained after supportAfter &&
    supportCorresponds supportBefore supportAfter &&
    correlates before after (ancestors before supportBefore) &&
    correlates before after (ancestors after supportAfter)

theorem accepted_iff {before after : AF} {supportBefore supportAfter : List Node} :
    accepted before after supportBefore supportAfter = true ↔
      (∀ a ∈ supportBefore, a ∈ before.args) ∧
      (∀ a ∈ supportAfter, a ∈ after.args) ∧
      LocalityClaim before after supportBefore supportAfter := by
  simp only [accepted, Bool.and_eq_true, contained_iff, supportCorresponds_iff, correlates_iff,
    LocalityClaim]
  tauto

/-- The comparison record. It carries both supports, both symmetric
differences, both ancestry regions and the acceptance bit; `checkLocality_record`
pins each field to the comparison it names. -/
structure LocalityCheck (before after : AF) (supportBefore supportAfter : List Node) where
  supportBefore : List Node
  supportAfter : List Node
  nodeDiff : List Node
  edgeDiff : List (Node × Node)
  regionBefore : List Node
  regionAfter : List Node
  accepted : Bool

/-- Check two graphs against one query. -/
def checkLocality (before after : AF) (supportBefore supportAfter : List Node) :
    LocalityCheck before after supportBefore supportAfter :=
  { supportBefore, supportAfter
    nodeDiff := nodeDiff before after
    edgeDiff := edgeDiff before after
    regionBefore := ancestors before supportBefore
    regionAfter := ancestors after supportAfter
    accepted := accepted before after supportBefore supportAfter }

/-- The record carries exactly the comparison facts it names. -/
theorem checkLocality_record (before after : AF) (supportBefore supportAfter : List Node) :
    (checkLocality before after supportBefore supportAfter).supportBefore = supportBefore ∧
    (checkLocality before after supportBefore supportAfter).supportAfter = supportAfter ∧
    (checkLocality before after supportBefore supportAfter).nodeDiff = nodeDiff before after ∧
    (checkLocality before after supportBefore supportAfter).edgeDiff = edgeDiff before after ∧
    (checkLocality before after supportBefore supportAfter).regionBefore =
      ancestors before supportBefore ∧
    (checkLocality before after supportBefore supportAfter).regionAfter =
      ancestors after supportAfter :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A locality certificate: the facts the sufficient test claims. Acceptance of
`checkLocality` implies this certificate, and the certificate carries exactly
the claimed node/support correspondence and region agreement. -/
structure Certificate (before after : AF) (supportBefore supportAfter : List Node) : Prop where
  support_before_mem : ∀ a ∈ supportBefore, a ∈ before.args
  support_after_mem : ∀ a ∈ supportAfter, a ∈ after.args
  support_corresponds : SupportCorrespond supportBefore supportAfter
  region_before : Correlates before after (ancestors before supportBefore)
  region_after : Correlates before after (ancestors after supportAfter)

/-- Certificate acceptance is exactly the recorded acceptance bit: the check is
sound and complete for the facts it claims. -/
theorem checkLocality_accepts_iff (before after : AF) (supportBefore supportAfter : List Node) :
    (checkLocality before after supportBefore supportAfter).accepted = true ↔
      Certificate before after supportBefore supportAfter := by
  rw [show (checkLocality before after supportBefore supportAfter).accepted =
      accepted before after supportBefore supportAfter from rfl]
  constructor
  · intro h
    obtain ⟨hb, ha, hsupp, hrb, hra⟩ := accepted_iff.mp h
    exact ⟨hb, ha, hsupp, hrb, hra⟩
  · intro c
    exact accepted_iff.mpr ⟨c.support_before_mem, c.support_after_mem,
      c.support_corresponds, c.region_before, c.region_after⟩

/-! ### The certificate implies the directional-locality premises -/

/-- **The certificate supplies the hypotheses of
`Lara.Process.grounded_directional_locality` verbatim** at every reported
support: the queried argument is present, every `Ancestor` is present in the
target graph, and the incoming edges of every ancestor agree. No label equality
is assumed. -/
theorem Certificate.locality_premises (cert : Certificate before after s t) {a : Node}
    (ha : a ∈ s) : a ∈ before.args ∧
      (∀ y, Ancestor before a y → y ∈ after.args) ∧
      (∀ y, Ancestor before a y → ∀ x,
        (x ∈ before.args ∧ before.attack x y = true) ↔
          (x ∈ after.args ∧ after.attack x y = true)) := by
  have hy : ∀ y, Ancestor before a y → y ∈ ancestors before s :=
    fun y hanc => (mem_ancestors_iff cert.support_before_mem).mpr ⟨a, ha, hanc⟩
  refine ⟨cert.support_before_mem a ha, fun y h => (cert.region_before y (hy y h)).2.1, ?_⟩
  intro y h x
  obtain ⟨_, _, hinc⟩ := cert.region_before y (hy y h)
  have : x ∈ incoming before y ↔ x ∈ incoming after y := by rw [hinc]
  simpa only [mem_incoming] using this

theorem Certificate.label_eq (cert : Certificate before after s t) {a : Node}
    (ha : a ∈ s) : labelC before a = labelC after a := by
  obtain ⟨ht, members, incoming⟩ := cert.locality_premises ha
  exact grounded_directional_locality ht members incoming

/-! ### The certificate as an embedding with no sinks

The region-restricted graphs are the shape `Grounded.SinkEmbedding` describes:
the query's ancestry region in the before graph embeds into the target under the
identity, with an empty sink list, and every old attack is preserved. This is
the "exact fields `map_mem`/`mem_cases`/`old_attack`/`sink_no_out` at the
claim's support" form of the same implication. -/

/-- Restrict the carrier; the attack function is kept (labels only read
carrier members). -/
def restrict (F : AF) (R : List Node) : AF :=
  ⟨R.filter (fun a => F.args.contains a), F.attack⟩

theorem mem_restrict {F : AF} {R : List Node} {a : Node} :
    a ∈ (restrict F R).args ↔ a ∈ R ∧ a ∈ F.args := by
  simp [restrict]

/-- The certificate's region agreement is a `SinkEmbedding` of the before
region into the target region, with no sinks. -/
theorem Certificate.sinkEmbedding (cert : Certificate before after s t) :
    SinkEmbedding (restrict before (ancestors before s))
      (restrict after (ancestors before s)) id [] where
  map_mem := by
    intro a ha
    obtain ⟨haR, haF⟩ := mem_restrict.mp ha
    exact mem_restrict.mpr ⟨haR, (cert.region_before a haR).2.1⟩
  mem_cases := by
    intro b hb
    exact Or.inr ⟨b, mem_restrict.mpr ⟨(mem_restrict.mp hb).1,
      (cert.region_before b (mem_restrict.mp hb).1).1⟩, rfl⟩
  old_attack := by
    intro a ha b hb
    obtain ⟨haR, haF⟩ := mem_restrict.mp ha
    obtain ⟨hbR, hbF⟩ := mem_restrict.mp hb
    obtain ⟨_, hbaF, hinc⟩ := cert.region_before b hbR
    have hmemb : a ∈ incoming before b ↔ a ∈ incoming after b := by rw [hinc]
    have haAfter : a ∈ after.args := (cert.region_before a haR).2.1
    have hiff : before.attack a b = true ↔ after.attack a b = true := by
      rw [mem_incoming, mem_incoming] at hmemb
      exact ⟨fun h => (hmemb.mp ⟨haF, h⟩).2, fun h => (hmemb.mpr ⟨haAfter, h⟩).2⟩
    exact (Bool.eq_iff_iff.mpr hiff).symm
  sink_no_out := by intro s hs; exact absurd hs List.not_mem_nil

/-- Region agreement also makes the before-ancestry backward closed in the
target graph. -/
theorem Certificate.closed_after (cert : Certificate before after s t) :
    ∀ y ∈ ancestors before s, ∀ x ∈ after.args, after.attack x y = true →
      x ∈ ancestors before s := by
  intro y hy x hx hxy
  obtain ⟨_, _, hinc⟩ := cert.region_before y hy
  have hmem : x ∈ incoming after y := mem_incoming.mpr ⟨hx, hxy⟩
  rw [← hinc] at hmem
  exact ancestors_closed hy (mem_incoming.mp hmem).1 (mem_incoming.mp hmem).2

/-- Boolean containment agrees with membership. -/
theorem contains_eq_true {R : List Node} {a : Node} (h : a ∈ R) : R.contains a = true :=
  List.contains_iff_mem.mpr h

theorem contains_eq_false {R : List Node} {a : Node} (h : a ∉ R) : R.contains a = false := by
  cases hc : R.contains a with
  | false => rfl
  | true => exact absurd (List.contains_iff_mem.mp hc) h

theorem not_mem_of_not_contains {R : List Node} {a : Node} (h : (!(R.contains a)) = true) :
    a ∉ R := fun ha => by rw [contains_eq_true ha] at h; exact absurd h (by simp)

theorem not_contains_of_not_mem {R : List Node} {a : Node} (h : a ∉ R) :
    (!(R.contains a)) = true := by
  rw [contains_eq_false h]
  rfl

/-- Restricting to a backward-closed carrier region preserves labels: the
restriction is a `Blocked.Blocking` edit whose blocked set excludes the region. -/
theorem restrict_labelC (F : AF) (R : List Node)
    (closed : ∀ y ∈ R, ∀ x ∈ F.args, F.attack x y = true → x ∈ R)
    (subset : ∀ a ∈ R, a ∈ F.args) {a : Node} (ha : a ∈ R) :
    labelC (restrict F R) a = labelC F a := by
  classical
  have hb : Blocked.Blocking (restrict F R) F (F.args.filter (fun y => !(R.contains y))) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      exact (mem_restrict.mp hx).2
    · intro x hx hnx
      refine List.mem_filter.mpr ⟨hx, ?_⟩
      exact not_contains_of_not_mem fun hxR => hnx (mem_restrict.mpr ⟨hxR, hx⟩)
    · intro x hx y hy hxy
      have hnc : x ∉ R := not_mem_of_not_contains (List.mem_filter.mp hx).2
      have hxF : x ∈ F.args := (List.mem_filter.mp hx).1
      refine List.mem_filter.mpr ⟨hy, ?_⟩
      exact not_contains_of_not_mem fun hyR => hnc (closed y hyR x hxF hxy)
    · intro y _ _ x _; rfl
  refine Blocked.labelC_agree hb (mem_restrict.mpr ⟨ha, subset a ha⟩) ?_
  intro h
  exact not_mem_of_not_contains (List.mem_filter.mp h).2 ha

/-- **The certificate yields label equality at every reported support through
`Grounded.SinkEmbedding.label_old`** — the landed directional-locality premise,
applied to the two region restrictions. -/
theorem Certificate.label_eq_via_sink (cert : Certificate before after s t) {a : Node}
    (ha : a ∈ s) : labelC before a = labelC after a := by
  have haR : a ∈ ancestors before s := ancestors_seed (cert.support_before_mem a ha) ha
  have hbefore : labelC (restrict before (ancestors before s)) a = labelC before a :=
    restrict_labelC before _ (fun y hy x hx hxy => ancestors_closed hy hx hxy)
      (fun _ hb => ancestors_subset_args hb) haR
  have hafter : labelC (restrict after (ancestors before s)) a = labelC after a :=
    restrict_labelC after _ cert.closed_after (fun b hb => (cert.region_before b hb).2.1) haR
  have hold : labelC (restrict after (ancestors before s)) a =
      labelC (restrict before (ancestors before s)) a := by
    simpa only [id_eq] using
      (cert.sinkEmbedding).label_old (mem_restrict.mpr ⟨haR, cert.support_before_mem a ha⟩)
  exact hbefore.symm.trans (hafter ▸ hold).symm

/-! ### Label facts from compiled rows

These read a label off the compiled incoming-attacker row, so fixtures never
have to kernel-decide a whole evaluation to pin a status. -/

/-- A carrier member with an empty incoming row is labelled `in`. -/
theorem labelC_inn_of_incoming_nil {F : AF} {a : Node} (ha : a ∈ F.args)
    (h : incoming F a = []) : labelC F a = Label.inn :=
  Grounded.labelC_inn_of_unattacked ha fun b hb => by
    cases hatt : F.attack b a with
    | false => rfl
    | true =>
      have hmem : b ∈ incoming F a := mem_incoming.mpr ⟨hb, hatt⟩
      rw [h] at hmem
      exact absurd hmem List.not_mem_nil

/-- A node attacked by a labelled-`in` argument is labelled `out`. -/
theorem labelC_out_of_inn_attacker {F : AF} {a b : Node} (hba : F.attack b a = true)
    (hbinn : labelC F b = Label.inn) : labelC F a = Label.out := by
  rw [Grounded.labelC_out_iff]
  refine ⟨fun hin => Grounded.labelC_inn_no_attack hbinn
    ((Grounded.labelC_inn_iff a).mpr hin) hba, Grounded.DirectOut.intro
    ((Grounded.labelC_inn_iff b).mp hbinn) hba⟩

/-- A claim with nonempty support all of whose arguments are labelled `out` is
defeated. This is the converse of `Grounded.statusC_defeated_all_out`, which
supplies only the forward direction; fixture statuses are read off it instead of
re-deciding an evaluation. -/
theorem statusC_eq_defeated_of_all_out {F : AF} {c : Claim} (ne : c.support ≠ [])
    (hout : ∀ i ∈ c.support, labelC F i = Label.out) :
    statusC F c = Status.defeated := by
  have hnoin : c.support.any (fun a => labelC F a == Label.inn) = false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨a, ha, hbeq⟩ := List.any_eq_true.mp h
    rw [hout a ha] at hbeq
    exact absurd hbeq (by decide)
  have hnoun : c.support.any (fun a => labelC F a == Label.undec) = false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨a, ha, hbeq⟩ := List.any_eq_true.mp h
    rw [hout a ha] at hbeq
    exact absurd hbeq (by decide)
  have hnoin' : ¬ (c.support.any (fun a => labelC F a == Label.inn)) = true := by
    rw [hnoin]; decide
  have hnoun' : ¬ (c.support.any (fun a => labelC F a == Label.undec)) = true := by
    rw [hnoun]; decide
  unfold statusC
  rw [if_neg ne, if_neg hnoin', if_neg hnoun']

/-- A claim whose support is exactly one argument labelled `in` is justified. -/
theorem statusC_eq_justified_of_singleton_inn {F : AF} {i : Node} {c : Claim}
    (hs : c.support = [i]) (hinn : labelC F i = Label.inn) :
    statusC F c = Status.justified :=
  (Grounded.statusC_justified_iff F c).mpr
    ⟨i, by rw [hs]; exact List.mem_singleton_self i, hinn⟩

/-- A claim whose support is exactly one argument attacked by a labelled-`in`
argument is defeated. -/
theorem statusC_eq_defeated_of_singleton_out {F : AF} {i j : Node} {c : Claim}
    (hs : c.support = [i]) (hatt : F.attack j i = true) (hjinn : labelC F j = Label.inn) :
    statusC F c = Status.defeated :=
  statusC_eq_defeated_of_all_out (by rw [hs]; simp) (by
    intro k hk
    rw [hs] at hk
    have : k = i := by simpa using hk
    subst this
    exact labelC_out_of_inn_attacker hatt hjinn)

/-! ### Lifting label equality to complete-claim status -/

/-- Support correspondence and pointwise label equality lift to status equality
for any two claims whose supports correspond exactly. -/
theorem statusC_of_support_labels {F G : AF} {cF cG : Claim}
    (support : SupportCorrespond cF.support cG.support)
    (labels : ∀ a ∈ cF.support, labelC F a = labelC G a) :
    statusC F cF = statusC G cG := by
  have hnil : (cF.support = []) ↔ (cG.support = []) := by
    constructor
    · intro h
      refine List.eq_nil_iff_forall_not_mem.mpr fun a ha => ?_
      exact List.not_mem_nil (h ▸ (support a).mpr ha)
    · intro h
      refine List.eq_nil_iff_forall_not_mem.mpr fun a ha => ?_
      exact List.not_mem_nil (h ▸ (support a).mp ha)
  have hinn : cF.support.any (fun a => labelC F a == Label.inn) =
      cG.support.any (fun a => labelC G a == Label.inn) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨a, ha, hl⟩
      exact ⟨a, (support a).mp ha, by rw [labels a ha] at hl; exact hl⟩
    · rintro ⟨a, ha, hl⟩
      refine ⟨a, (support a).mpr ha, ?_⟩
      rw [labels a ((support a).mpr ha)]
      exact hl
  have hund : cF.support.any (fun a => labelC F a == Label.undec) =
      cG.support.any (fun a => labelC G a == Label.undec) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨a, ha, hl⟩
      exact ⟨a, (support a).mp ha, by rw [labels a ha] at hl; exact hl⟩
    · rintro ⟨a, ha, hl⟩
      refine ⟨a, (support a).mpr ha, ?_⟩
      rw [labels a ((support a).mpr ha)]
      exact hl
  unfold statusC
  rw [hinn, hund]
  exact ite_congr (propext hnil) (fun _ => rfl) (fun _ => rfl)

/-- **The certificate lifts per-support label equality to complete-claim status
equality**, requiring exact support correspondence. -/
theorem Certificate.status_eq (cert : Certificate before after s t) {cF cG : Claim}
    (hs : cF.support = s) (ht : cG.support = t) :
    statusC before cF = statusC after cG :=
  statusC_of_support_labels
    (fun a => by rw [hs, ht]; exact cert.support_corresponds a)
    (fun a ha => cert.label_eq (by rw [hs] at ha; exact ha))

/-! ### Reindexing and pure declaration-permutation invariance -/

/-- Two frameworks with mutually contained carriers and agreeing attack on the
source carrier are isomorphic under the identity. -/
theorem iso_of_same_carrier {F G : AF}
    (mem : ∀ a, a ∈ F.args ↔ a ∈ G.args)
    (attack : ∀ a b, a ∈ F.args → b ∈ F.args →
      (F.attack a b = true ↔ G.attack a b = true)) : PW.AFIso F G id where
  maps := fun a ha => (mem a).mp ha
  inj := fun _ _ _ _ h => h
  surj := fun a' ha' => ⟨a', (mem a').mpr ha', rfl⟩
  attack_iff := attack

/-- Labels transfer across such a reindexing. -/
theorem labelC_of_same_carrier {F G : AF} (h : PW.AFIso F G id) {a : Node}
    (ha : a ∈ F.args) : labelC F a = labelC G a :=
  PW.labelC_of_iso h ha

/-- **Pure permutation invariance with query identities held fixed.** If the two
carriers hold the same stable identities and the attack rows agree there, the
complete claim's status is unchanged for a corresponding support. -/
theorem statusC_of_same_carrier {F G : AF} (h : PW.AFIso F G id) {cF cG : Claim}
    (sub : ∀ a ∈ cF.support, a ∈ F.args) (support : SupportCorrespond cF.support cG.support) :
    statusC F cF = statusC G cG :=
  statusC_of_support_labels support (fun a ha => labelC_of_same_carrier h (sub a ha))

/-! ### Executable isomorphism and the refuted weaker criteria -/

/-- Executable isomorphism test: mutual carrier containment and pointwise attack
equality on the source carrier. A fixture discharges it with one kernel decide. -/
def isoCheck (F G : AF) : Bool :=
  F.args.all (fun a => G.args.contains a) &&
    G.args.all (fun a => F.args.contains a) &&
    F.args.all (fun a => F.args.all (fun b => decide (F.attack a b = G.attack a b)))

theorem isoCheck_iff {F G : AF} :
    isoCheck F G = true ↔
      (∀ a, a ∈ F.args ↔ a ∈ G.args) ∧
      (∀ a ∈ F.args, ∀ b ∈ F.args, F.attack a b = G.attack a b) := by
  simp only [isoCheck, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    exact ⟨fun a => ⟨fun ha => h₁ a ha, fun ha => h₂ a ha⟩, h₃⟩
  · rintro ⟨h₁, h₃⟩
    exact ⟨⟨fun a ha => (h₁ a).mp ha, fun a ha => (h₁ a).mpr ha⟩, h₃⟩

theorem iso_of_isoCheck {F G : AF} (h : isoCheck F G = true) : PW.AFIso F G id :=
  iso_of_same_carrier (isoCheck_iff.mp h).1
    fun a b ha hb => by rw [(isoCheck_iff.mp h).2 a ha b hb]

/-- The node difference avoids a region. -/
def nodeDiffDisjoint (F G : AF) (region : List Node) : Bool :=
  (nodeDiff F G).all fun a => !(region.contains a)

/-- Every differing compiled edge has both endpoints outside the region. -/
def edgeDiffInternal (F G : AF) (region : List Node) : Bool :=
  (edgeDiff F G).all fun e => !((region.contains e.1) && (region.contains e.2))

/-- The weaker criterion the countermodels refute: the **old** ancestry region
has no changed node and no changed edge *internal* to it. It ignores incoming
edges from outside the region, which is exactly what a new attacker supplies, so
it is not sufficient even though it mentions ancestry. -/
def oldRegionCriterion (F G : AF) (support : List Node) : Bool :=
  nodeDiffDisjoint F G (ancestors F support) &&
    edgeDiffInternal F G (ancestors F support)

/-- **Reindexing invariance.** Under any two carriers that contain the stable
names, the grounded label of a name is the same: the label is read at the
carrier position of the name, never at a declaration position. -/
theorem graph_label_reindex {canon : String → String} {registry : Lara.Support.BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun registry state)
    (C C' : List Presentation.ArgId)
    (coverC : ∀ n ∈ Coordinates.names run, n ∈ C)
    (coverC' : ∀ n ∈ Coordinates.names run, n ∈ C')
    {n : Presentation.ArgId} (hn : n ∈ Coordinates.names run) :
    labelC (Coordinates.graph run C) (C.idxOf n) =
      labelC (Coordinates.graph run C') (C'.idxOf n) := by
  have hmem : (Coordinates.names run).idxOf n ∈
      (Compile.checkedAF run.checked.program).args := by
    rw [show (Compile.checkedAF run.checked.program).args =
        List.range (Coordinates.names run).length from by
          simp [Compile.checkedAF, Compile.toAF, Coordinates.names_length]]
    exact List.mem_range.mpr (List.idxOf_lt_length_iff.mpr hn)
  have h1 := Coordinates.graph_label run C coverC hmem
  have h2 := Coordinates.graph_label run C' coverC' hmem
  have e1 : Coordinates.identity run C ((Coordinates.names run).idxOf n) = C.idxOf n := by
    simp [Coordinates.identity, List.getElem?_idxOf hn]
  have e2 : Coordinates.identity run C' ((Coordinates.names run).idxOf n) = C'.idxOf n := by
    simp [Coordinates.identity, List.getElem?_idxOf hn]
  rw [e1] at h1
  rw [e2] at h2
  exact h1.trans h2.symm

/-! ### The stable-identity lift of two checked sources

`Lara.Process.Source.Coordinates` supplies the common carrier identity. This
section records what the locality test needs from it: the lifted support is
contained in the lifted carrier, the lifted support corresponds to the checked
complete claim, and the lifted status *is* the checked status — so a certificate
about lifted graphs is a certificate about the checked sources.
-/

/-- The carrier of a comparison: both sources' checked argument names. -/
def sharedCarrier (first second : List Presentation.ArgId) : List Presentation.ArgId :=
  (first ++ second).dedup

theorem mem_sharedCarrier_left {first second : List Presentation.ArgId}
    {n : Presentation.ArgId} (h : n ∈ first) : n ∈ sharedCarrier first second := by
  simp [sharedCarrier, h]

theorem mem_sharedCarrier_right {first second : List Presentation.ArgId}
    {n : Presentation.ArgId} (h : n ∈ second) : n ∈ sharedCarrier first second := by
  simp [sharedCarrier, h]

/-- The checked arguments are `List.range` of the program's argument count. -/
theorem args_checkedAF (P : Compile.CheckedProgram canon Pi Gamma CertOk dp) :
    (Compile.checkedAF P).args = List.range P.args.length := rfl

/-- The lifted carrier arguments are the checked arguments reindexed by the
stable-identity map. -/
theorem graph_args (run : Update.AcceptedRun registry state)
    (carrier : List Presentation.ArgId) :
    (Coordinates.graph run carrier).args =
      (Compile.checkedAF run.checked.program).args.map (Coordinates.identity run carrier) := by
  rw [Coordinates.graph_eq_reference]
  rfl

/-- A list equality for the `filterMap`-then-index shape of the lifted support. -/
theorem map_filterMap_getD {α β γ : Type} (l : List α) (f : α → Option β) (g : β → γ) (d : γ)
    (h : ∀ a ∈ l, ∃ b, f a = some b) :
    (l.filterMap f).map g =
      l.map (fun a => match f a with | some b => g b | none => d) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    have has : ∀ x ∈ as, ∃ b, f x = some b := fun x hx => h x (List.mem_cons_of_mem a hx)
    rw [List.filterMap_cons_some hb, List.map_cons, List.map_cons, hb, ih has]

/-- The queried support as lifted carrier positions. -/
def querySupport (run : Update.AcceptedRun registry state) (carrier : List Presentation.ArgId)
    (query : Atom) : List Node :=
  (Coordinates.supports run query).map carrier.idxOf

/-- The complete claim of a query, read at the lifted positions. -/
def claimOf (run : Update.AcceptedRun registry state) (carrier : List Presentation.ArgId)
    (query : Atom) : Claim :=
  { support := querySupport run carrier query, holes := [] }

theorem claimOf_support_eq (run : Update.AcceptedRun registry state)
    (carrier : List Presentation.ArgId) (query : Atom) :
    (claimOf run carrier query).support = querySupport run carrier query := rfl

/-- Every checked support index has a stable name. -/
theorem checked_name_exists (run : Update.AcceptedRun registry state) (query : Atom)
    {node : Nat} (hnode : node ∈ Consistency.claimSupportFor run.checked query) :
    ∃ n, (Coordinates.names run)[node]? = some n := by
  obtain ⟨x, hx, _⟩ := Consistency.mem_claimSupportFor_iff.mp hnode
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hx
  exact Lara.Support.getElem?_some_of_lt _ _ (by
    rw [Coordinates.names_length, ← congrArg List.length run.checked.nodes_terms, List.length_map]
    exact hlt)

/-- **Checked node/support correspondence.** The lifted support is exactly the
checked complete support reindexed by the stable identity: the query is
resolved by normalized conclusion and by name, never by a remembered compact
index. -/
theorem querySupport_exact (run : Update.AcceptedRun registry state)
    (carrier : List Presentation.ArgId) (query : Atom) :
    querySupport run carrier query =
      (Consistency.claimSupportFor run.checked query).map
        (Coordinates.identity run carrier) := by
  have hsome : ∀ node ∈ Consistency.claimSupportFor run.checked query,
      ∃ n, (Coordinates.names run)[node]? = some n :=
    fun node hnode => checked_name_exists run query hnode
  simp only [querySupport, Coordinates.supports, List.getElem?_toArray]
  show (List.filterMap (fun x => (Coordinates.names run)[x]?)
      (Consistency.claimSupportFor run.checked query)).map (fun a => carrier.idxOf a) =
    (Consistency.claimSupportFor run.checked query).map
      (fun a => match (Coordinates.names run)[a]? with
        | some b => carrier.idxOf b
        | none => carrier.length)
  convert map_filterMap_getD (Consistency.claimSupportFor run.checked query)
    (fun x => (Coordinates.names run)[x]?) (fun a => carrier.idxOf a) carrier.length hsome using 1
  apply List.map_congr_left
  intro a _
  cases (Coordinates.names run)[a]? <;> rfl

/-- **The lifted support lies in the lifted carrier.** -/
theorem supports_mem_args (run : Update.AcceptedRun registry state)
    (carrier : List Presentation.ArgId) (query : Atom) {name : Presentation.ArgId}
    (hname : name ∈ Coordinates.supports run query) :
    carrier.idxOf name ∈ (Coordinates.graph run carrier).args := by
  obtain ⟨i, node, named, _, _⟩ := (Coordinates.supports_exact run query name).mp hname
  have hnamed : name ∈ Coordinates.names run := List.mem_of_getElem? named
  rw [graph_args, args_checkedAF]
  refine List.mem_map.mpr ⟨(Coordinates.names run).idxOf name, ?_, ?_⟩
  · rw [List.mem_range, ← Coordinates.names_length]
    exact List.idxOf_lt_length_iff.mpr hnamed
  · simp [Coordinates.identity, List.getElem?_idxOf hnamed]

/-- **The lifted queried support lies in the lifted carrier.** This is the form
the status lifting needs; it is `supports_mem_args` through the name map. -/
theorem querySupport_mem_args (run : Update.AcceptedRun registry state)
    (carrier : List Presentation.ArgId) (query : Atom) :
    ∀ a ∈ querySupport run carrier query, a ∈ (Coordinates.graph run carrier).args := by
  intro a ha
  obtain ⟨name, hname, rfl⟩ := List.mem_map.mp ha
  exact supports_mem_args run carrier query hname

/-- Every checked argument index is a lifted carrier argument. -/
theorem checked_mem_graph (run : Update.AcceptedRun registry state)
    (carrier : List Presentation.ArgId) {node : Nat}
    (hnode : node ∈ (Compile.checkedAF run.checked.program).args) :
    Coordinates.identity run carrier node ∈ (Coordinates.graph run carrier).args := by
  rw [graph_args]
  exact List.mem_map_of_mem hnode

/-- **The lifted status is the checked status.** The stable-identity lift is
faithful on the complete claim of a query, so locality proved over lifted graphs
is locality about the checked source. -/
theorem claimOf_status_eq_checked (run : Update.AcceptedRun registry state)
    (carrier : List Presentation.ArgId)
    (cover : ∀ n ∈ Coordinates.names run, n ∈ carrier) (query : Atom) :
    statusC (Coordinates.graph run carrier) (claimOf run carrier query) =
      statusC (Compile.checkedAF run.checked.program)
        (Consistency.completeClaimFor run.checked query) := by
  have supported : ∀ a ∈ (Consistency.completeClaimFor run.checked query).support,
      a ∈ (Compile.checkedAF run.checked.program).args := by
    intro a ha
    obtain ⟨node, hnode, _⟩ := Consistency.mem_claimSupportFor_iff.mp ha
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hnode
    rw [args_checkedAF, List.mem_range, ← congrArg List.length run.checked.nodes_terms,
      List.length_map]
    exact hlt
  have main := liftGraph_status (Compile.checkedAF run.checked.program)
    (Coordinates.identity run carrier) (Coordinates.identity_injective run carrier cover)
    (Consistency.completeClaimFor run.checked query) supported
  have hsupp : querySupport run carrier query =
      (Consistency.completeClaimFor run.checked query).support.map
        (Coordinates.identity run carrier) := by
    simpa only [Consistency.completeClaimFor] using querySupport_exact run carrier query
  have hcl : claimOf run carrier query =
      { Consistency.completeClaimFor run.checked query with
        support := (Consistency.completeClaimFor run.checked query).support.map
          (Coordinates.identity run carrier) } := by
    simp only [claimOf]
    show ({ support := querySupport run carrier query, holes := [] } : Claim) =
      { support := (Consistency.completeClaimFor run.checked query).support.map
          (Coordinates.identity run carrier), holes := [] }
    rw [hsupp]
  rw [Coordinates.graph_eq_reference, hcl, main]

/-! ### The locality comparison of two checked sources -/

/-- **The checked locality capstone.** A certificate over the two lifted graphs
gives equality of the complete grounded status of the queried atom, without
assuming any label or status equality. -/
theorem checked_status_eq {first second : SourceInput}
    (before : AcceptedObservation first) (after : AcceptedObservation second)
    (carrier : List Presentation.ArgId) (query : Atom)
    (cert : Certificate (Coordinates.graph before.run carrier)
      (Coordinates.graph after.run carrier)
      (querySupport before.run carrier query) (querySupport after.run carrier query)) :
    statusC (Coordinates.graph before.run carrier) (claimOf before.run carrier query) =
      statusC (Coordinates.graph after.run carrier) (claimOf after.run carrier query) :=
  cert.status_eq rfl rfl

/-- Acceptance of the executable comparison gives the certificate. -/
theorem checked_certificate_of_accepts {first second : SourceInput}
    (before : AcceptedObservation first) (after : AcceptedObservation second)
    (carrier : List Presentation.ArgId) (query : Atom)
    (accepts : (checkLocality (Coordinates.graph before.run carrier)
      (Coordinates.graph after.run carrier)
      (querySupport before.run carrier query)
      (querySupport after.run carrier query)).accepted = true) :
    Certificate (Coordinates.graph before.run carrier)
      (Coordinates.graph after.run carrier)
      (querySupport before.run carrier query) (querySupport after.run carrier query) :=
  (checkLocality_accepts_iff _ _ _ _).mp accepts

end Lara.Process.Locality
