import Lara.Process.Entitlement
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Minimal
import Mathlib.Data.Finset.Max

/-!
R5: revision and transport of entitlement.

Every edit puts a claim's entitlement into one of three classes:

* **survives by structure**: a minimal support avoids the quarantined sources
  (`quarantine_iff_support`, exact on the support-only fragment), the edit lies
  outside the claim's argument ancestry (`grounded_directional_locality`), or
  the derivation's recorded reads are unchanged (`verifying_trace_reuse`);
* **survives by transport**: the edit is a renaming under which warrant is
  natural (`warranted_natural`), with injectivity required exactly where a
  profile counts distinct sources (`corroboration_injective`);
* **must be re-established**: the edit changes something the derivation read.
  Lara recomputes the affected region; it never searches for a minimal repair.

With attacks, the support criterion is only necessary: quarantine can
reinstate a claim (`Lara.Examples.ProcessFalseLaws.quarantine_reinstates`) and
a claim whose support avoids the quarantine can still be defeated. Locality is
stated for grounded semantics only; it fails for stable semantics.
-/

namespace Lara.Process

open Lara.Grounded

/-! ### The support-only fragment -/

/-- A support-only (monotone) system: sources supply atoms, and Horn rules
derive conclusions from premises. There are no attacks. -/
structure SupportSystem (Src Atom : Type) where
  rules : List (List Atom × Atom)

variable {Src Atom : Type}

/-- `Derives S avail a`: atom `a` is derivable from the available source
supplies `avail` (pairs of a source and the atom it supplies). -/
inductive Derives (S : SupportSystem Src Atom) (avail : Finset (Src × Atom)) : Atom → Prop where
  | source {s : Src} {a : Atom} : (s, a) ∈ avail → Derives S avail a
  | rule {r : List Atom × Atom} : r ∈ S.rules → (∀ p ∈ r.1, Derives S avail p) →
      Derives S avail r.2

/-- Derivability is monotone in the available supplies. -/
theorem Derives.mono {S : SupportSystem Src Atom} {avail avail' : Finset (Src × Atom)}
    (sub : avail ⊆ avail') {a : Atom} (h : Derives S avail a) : Derives S avail' a := by
  induction h with
  | source mem => exact .source (sub mem)
  | rule mem _ ih => exact .rule mem ih

/-- With no available supplies and only rules that have premises, nothing is
derivable. -/
theorem not_derives_empty {S : SupportSystem Src Atom}
    (premised : ∀ r ∈ S.rules, r.1 ≠ []) {a : Atom} : ¬ Derives S ∅ a := by
  intro h
  induction h with
  | source mem => exact Finset.notMem_empty _ mem
  | rule mem _ ih =>
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (premised _ mem)
      exact ih p hp

/-- A minimal supporting set (an ATMS label environment): it derives `c` and no
proper subset does. -/
def MinimalSupport (S : SupportSystem Src Atom) (c : Atom) (env : Finset (Src × Atom)) : Prop :=
  Derives S env c ∧ ∀ env' ⊂ env, ¬ Derives S env' c

/-- Quarantine on the support-only fragment: after removing the supplies of the
quarantined sources `Q`, `c` stays derivable iff some minimal support inside the
available supplies avoids `Q`. -/
theorem quarantine_iff_support [DecidableEq Src] [DecidableEq Atom] (S : SupportSystem Src Atom)
    (avail : Finset (Src × Atom)) (Q : Finset Src) (c : Atom) :
    Derives S (avail.filter fun p => p.1 ∉ Q) c ↔
      ∃ env ⊆ avail, MinimalSupport S c env ∧ ∀ p ∈ env, p.1 ∉ Q := by
  classical
  constructor
  · intro derives
    set kept := avail.filter fun p => p.1 ∉ Q
    have nonempty : (kept.powerset.filter fun env => Derives S env c).Nonempty :=
      ⟨kept, Finset.mem_filter.mpr ⟨Finset.mem_powerset_self _, derives⟩⟩
    obtain ⟨env, mem, least⟩ := Finset.exists_min_image _ Finset.card nonempty
    obtain ⟨sub, envDerives⟩ := Finset.mem_filter.mp mem
    have subKept := Finset.mem_powerset.mp sub
    refine ⟨env, subKept.trans (Finset.filter_subset _ _), ⟨envDerives, ?_⟩, ?_⟩
    · intro env' proper d'
      have := least env' (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (proper.1.trans subKept), d'⟩)
      exact absurd (Finset.card_lt_card proper) (not_lt.mpr this)
    · intro p hp
      exact (Finset.mem_filter.mp (subKept hp)).2
  · rintro ⟨env, sub, ⟨derives, _⟩, avoids⟩
    refine derives.mono fun p hp => Finset.mem_filter.mpr ⟨sub hp, avoids p hp⟩

/-! ### Grounded directional locality -/

/-- Grounded labels are local to attack ancestry: if two frameworks contain the
same ancestors of `t` and give each ancestor the same attackers, `t` has the same
label in both. Edits elsewhere cannot change it. -/
theorem grounded_directional_locality {F G : AF} {t : Arg} (ht : t ∈ F.args)
    (members : ∀ y, Ancestor F t y → y ∈ G.args)
    (incoming : ∀ y, Ancestor F t y → ∀ x,
      (x ∈ F.args ∧ F.attack x y = true) ↔ (x ∈ G.args ∧ G.attack x y = true)) :
    labelC F t = labelC G t := by
  classical
  have inF : ∀ y, Ancestor F t y → y ∈ F.args := by
    intro y hy
    cases hy with
    | self => exact ht
    | attacker _ hx _ => exact hx
  let H : AF := ⟨F.args.filter fun y => decide (Ancestor F t y), F.attack⟩
  have memH : ∀ y, y ∈ H.args ↔ Ancestor F t y := fun y => by
    simp only [H, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨inF y h, h⟩⟩
  have tH : t ∈ H.args := (memH t).mpr .self
  -- Blocking from the ancestry restriction into `F`.
  obtain ⟨BF, blockF, notBF⟩ := ancestry_blocking (F := H) (G := F) (t := t)
    (fun a ha => inF a ((memH a).mp ha)) rfl (fun x _ hH anc => hH ((memH x).mpr anc))
  -- Blocking from the ancestry restriction into `G`.
  let BG := G.args.filter fun y => decide (¬ Ancestor F t y)
  have blockG : Blocked.Blocking H G BG :=
    { args_sub := fun a ha => members a ((memH a).mp ha)
      missing_mem := fun x hx hH => List.mem_filter.mpr
        ⟨hx, decide_eq_true fun anc => hH ((memH x).mpr anc)⟩
      closed := by
        intro x hx y hy hxy
        refine List.mem_filter.mpr ⟨hy, decide_eq_true fun anc => ?_⟩
        have hx' := List.mem_filter.mp hx
        have := ((incoming y anc x).mpr ⟨hx'.1, hxy⟩)
        exact (of_decide_eq_true hx'.2) (.attacker anc this.1 this.2)
      edge_agree := by
        intro y hy _ x hx
        have ancY := (memH y).mp hy
        have xG := members x ((memH x).mp hx)
        cases hF : F.attack x y with
        | true => exact ((incoming y ancY x).mp ⟨inF x ((memH x).mp hx), hF⟩).2.symm
        | false =>
            cases hG : G.attack x y with
            | false => rfl
            | true => exact absurd ((incoming y ancY x).mpr ⟨xG, hG⟩).2 (by simp [hF]) }
  have notBG : t ∉ BG := fun h => (of_decide_eq_true (List.mem_filter.mp h).2) .self
  exact (Blocked.labelC_agree blockF tH notBF).symm.trans (Blocked.labelC_agree blockG tH notBG)

/-- Entitlement-level locality: if two histories agree on the witness's
ancestry in the framework the profile sees, and on every other input warrant
reads (artifact check, conclusion, kind, probes, attained guarantee), the
witness warrants in one exactly when it warrants in the other. Agreement of the
argument graph alone is not enough
(`Lara.Examples.ProcessRevision.failed_sibling_changes_warrant`). -/
theorem warranted_locality {H Claim Wit Policy : Type} {M : WarrantModel H Claim Wit}
    {P : Profile Policy} {h h' : H} {c : Claim} {w : Wit}
    (members : ∀ y, Ancestor (M.underProfile P h) (M.argOf w) y → y ∈ (M.underProfile P h').args)
    (incoming : ∀ y, Ancestor (M.underProfile P h) (M.argOf w) y → ∀ x,
      (x ∈ (M.underProfile P h).args ∧ (M.underProfile P h).attack x y = true) ↔
        (x ∈ (M.underProfile P h').args ∧ (M.underProfile P h').attack x y = true))
    (artifact : M.artifact h w ↔ M.artifact h' w) (concludes : M.concludes h w c ↔ M.concludes h' w c)
    (kind : M.kind h (M.argOf w) = M.kind h' (M.argOf w)) (probed : M.probed h w = M.probed h' w)
    (achieved : M.achieved h w = M.achieved h' w)
    (present : M.argOf w ∈ (M.underProfile P h).args) :
    Warranted M P h c w ↔ Warranted M P h' c w := by
  have label := grounded_directional_locality present members incoming
  unfold Warranted ProfileChecks
  rw [artifact, concludes, kind, probed, achieved, label]

/-- Stable semantics: `S` is conflict-free and attacks every other argument. -/
def IsStable (F : AF) (S : List Arg) : Prop :=
  (∀ a ∈ S, a ∈ F.args) ∧ (∀ a ∈ S, ∀ b ∈ S, F.attack a b = false) ∧
    ∀ a ∈ F.args, a ∉ S → ∃ b ∈ S, F.attack b a = true

instance (F : AF) (S : List Arg) : Decidable (IsStable F S) := by
  unfold IsStable; infer_instance

/-- Credulous acceptance under stable semantics: some stable extension contains
`t`. Extensions are enumerated as sublists of the carrier. -/
def StableCredulous (F : AF) (t : Arg) : Prop := ∃ S ∈ F.args.sublists, IsStable F S ∧ t ∈ S

instance (F : AF) (t : Arg) : Decidable (StableCredulous F t) := by
  unfold StableCredulous; infer_instance

/-! ### Transport along renamings -/

/-- Rename the sources of available supplies. -/
def renameSupplies {Src' : Type} [DecidableEq Src'] [DecidableEq Atom] (f : Src → Src')
    (avail : Finset (Src × Atom)) : Finset (Src' × Atom) :=
  avail.image fun p => (f p.1, p.2)

/-- The same rules over renamed sources: rules never mention source identities. -/
def SupportSystem.rename {Src' : Type} (S : SupportSystem Src Atom) : SupportSystem Src' Atom :=
  ⟨S.rules⟩

/-- Naturality on the identifier-free fragment, where warrant is derivability:
no rule compares source identities, so it transports along every renaming,
injective or not. -/
theorem warranted_natural {Src' : Type} [DecidableEq Src'] [DecidableEq Atom]
    (S : SupportSystem Src Atom) (f : Src → Src') (avail : Finset (Src × Atom)) (c : Atom) :
    Derives S.rename (renameSupplies f avail) c ↔ Derives S avail c := by
  constructor
  · intro h
    induction h with
    | source mem =>
        obtain ⟨p, hp, eq⟩ := Finset.mem_image.mp mem
        cases eq
        exact .source hp
    | rule mem _ ih => exact .rule mem ih
  · intro h
    induction h with
    | source mem => exact .source (Finset.mem_image.mpr ⟨_, mem, rfl⟩)
    | rule mem _ ih => exact .rule mem ih

/-- Re-encode atoms by `g`: rules and supplies are mapped pointwise. -/
def SupportSystem.reencode {Atom' : Type} (g : Atom → Atom') (S : SupportSystem Src Atom) :
    SupportSystem Src Atom' :=
  ⟨S.rules.map fun r => (r.1.map g, g r.2)⟩

/-- Re-encode the atoms of available supplies. -/
def reencodeSupplies {Atom' : Type} [DecidableEq Src] [DecidableEq Atom'] (g : Atom → Atom')
    (avail : Finset (Src × Atom)) : Finset (Src × Atom') :=
  avail.image fun p => (p.1, g p.2)

/-- Every re-encoding preserves derivations. -/
theorem derives_reencode {Atom' : Type} [DecidableEq Src] [DecidableEq Atom'] (g : Atom → Atom')
    {S : SupportSystem Src Atom} {avail : Finset (Src × Atom)} {c : Atom} (h : Derives S avail c) :
    Derives (S.reencode g) (reencodeSupplies g avail) (g c) := by
  induction h with
  | source mem => exact .source (Finset.mem_image.mpr ⟨_, mem, rfl⟩)
  | @rule r mem _ ih =>
      refine .rule (r := (r.1.map g, g r.2)) (List.mem_map.mpr ⟨r, mem, rfl⟩) fun p hp => ?_
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact ih q hq

/-- Warrant is natural for injective re-encodings: derivability transports in
both directions. -/
theorem derives_reencode_iff {Atom' : Type} [DecidableEq Src] [DecidableEq Atom'] {g : Atom → Atom'}
    (inj : Function.Injective g) (S : SupportSystem Src Atom) (avail : Finset (Src × Atom))
    (c : Atom) : Derives (S.reencode g) (reencodeSupplies g avail) (g c) ↔ Derives S avail c := by
  refine ⟨fun h => ?_, derives_reencode g⟩
  suffices ∀ a', Derives (S.reencode g) (reencodeSupplies g avail) a' → ∀ a, a' = g a →
      Derives S avail a from this _ h c rfl
  intro a' h
  induction h with
  | source mem =>
      intro a eq
      obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp mem
      simp only [Prod.mk.injEq] at hpe
      rw [← inj (hpe.2.trans eq)]
      exact .source hp
  | @rule r' mem _ ih =>
      intro a eq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp mem
      rw [← inj eq]
      exact .rule hr fun p hp => ih (g p) (List.mem_map_of_mem hp) p rfl

/-- The number of distinct sources supplying `c`: the count a corroboration or
independence profile reads. -/
def corroboration [DecidableEq Src] [DecidableEq Atom] (avail : Finset (Src × Atom)) (c : Atom) :
    Nat :=
  ((avail.filter fun p => p.2 = c).image Prod.fst).card

/-- Transport of a corroboration count is exact relative to the class of maps:
a renaming preserves the count of sources supplying `c` iff it is injective on
those sources. -/
theorem corroboration_preserved_iff {Src' : Type} [DecidableEq Src] [DecidableEq Src']
    [DecidableEq Atom] (f : Src → Src') (avail : Finset (Src × Atom)) (c : Atom) :
    corroboration (Src := Src') (renameSupplies f avail) c = corroboration avail c ↔
      Set.InjOn f ↑((avail.filter fun p => p.2 = c).image Prod.fst) := by
  unfold corroboration renameSupplies
  rw [Finset.filter_image, Finset.image_image]
  have : (Prod.fst ∘ fun p : Src × Atom => (f p.1, p.2)) = f ∘ Prod.fst := rfl
  rw [this, ← Finset.image_image]
  exact Finset.card_image_iff

/-- Injective renamings preserve corroboration counts. -/
theorem corroboration_injective {Src' : Type} [DecidableEq Src] [DecidableEq Src']
    [DecidableEq Atom] {f : Src → Src'} (inj : Function.Injective f)
    (avail : Finset (Src × Atom)) (c : Atom) :
    corroboration (Src := Src') (renameSupplies f avail) c = corroboration avail c :=
  (corroboration_preserved_iff f avail c).mpr inj.injOn

/-! ### Verifying traces -/

/-- A check records its reads completely when its result depends only on the
recorded keys. -/
def RecordsReads {K V : Type} (check : (K → V) → Bool) (reads : Finset K) : Prop :=
  ∀ e₁ e₂ : K → V, (∀ k ∈ reads, e₁ k = e₂ k) → check e₁ = check e₂

/-- Reuse by verifying trace: if every recorded read has the same value, the
stored result is the recomputed result. The hypothesis is complete read
recording; without it reuse can be wrong
(`Lara.Examples.ProcessRevision.incomplete_reads_unsound`). -/
theorem verifying_trace_reuse {K V : Type} {check : (K → V) → Bool} {reads : Finset K}
    (recorded : RecordsReads check reads) {old new : K → V}
    (same : ∀ k ∈ reads, old k = new k) : check new = check old :=
  (recorded old new same).symm

/-! ### Update versus revision -/

/-- A warrant indexed by the dataset versions its derivation read: every read
version is published and none is known to be defective. -/
def VersionWarranted (published reads defects : List (DataId × VersionId)) : Prop :=
  ∀ r ∈ reads, r ∈ published ∧ r ∉ defects

instance (published reads defects : List (DataId × VersionId)) :
    Decidable (VersionWarranted published reads defects) := by
  unfold VersionWarranted; infer_instance

/-- An update publishes a new dataset version and declares no defect: every
warrant indexed by the versions it read survives, old versions included. -/
theorem version_update_keeps_old {published reads defects : List (DataId × VersionId)}
    (new : DataId × VersionId) (warranted : VersionWarranted published reads defects) :
    VersionWarranted (new :: published) reads defects :=
  fun r hr => ⟨List.mem_cons_of_mem _ (warranted r hr).1, (warranted r hr).2⟩

/-- A revision declares a version defective: exactly the warrants that read it
are withdrawn, and every other warrant is unchanged. -/
theorem revision_withdraws_dependents (published reads defects : List (DataId × VersionId))
    (defect : DataId × VersionId) :
    VersionWarranted published reads (defect :: defects) ↔
      VersionWarranted published reads defects ∧ defect ∉ reads := by
  unfold VersionWarranted
  constructor
  · intro h
    refine ⟨fun r hr => ⟨(h r hr).1, fun mem => (h r hr).2 (List.mem_cons_of_mem _ mem)⟩,
      fun mem => (h defect mem).2 List.mem_cons_self⟩
  · rintro ⟨h, notRead⟩ r hr
    refine ⟨(h r hr).1, fun mem => ?_⟩
    rcases List.mem_cons.mp mem with eq | mem
    · subst eq; exact notRead hr
    · exact (h r hr).2 mem

end Lara.Process
