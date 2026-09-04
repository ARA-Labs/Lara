/-
# PW-T8 — grounded status is invariant under total attack bisimulation
(issue #193, tracker #189)

Generic layer: nothing here mentions a support term, a bridge, or a world.
Two finite frameworks `F G : Grounded.AF` and a relation `Z` on argument ids.
`AttackBisim F G Z` is a *total attack bisimulation*: `Z` relates only carrier
members (`dom`), every argument on either side is related to one on the other
(`left_total`, `right_total`), a source attacker of a related argument is
matched by a related target attacker (`forth`), and a target attacker of a
related argument is matched by a related source attacker (`back`).

The proof is one mutual induction on the declarative grounded judgment
`DirectIn`/`DirectOut` (`Lara/Grounded.lean`): `back` carries `DirectIn`
across, `forth` carries `DirectOut` across, and the symmetric bisimulation
gives the other direction. `labelC_spec` then transfers the executable label.
Status (`statusC`) follows for any two claims whose complete-support index
sets correspond under `Z` (`SupportCorr`).

The design's AF isomorphism is the graph of a bijection and is a corollary
(`AFIso.toBisim`). Its `inj` field is *not* consumed by any proof: a
surjective bounded morphism already suffices, which is why the bisimulation,
not the isomorphism, is the primitive here.

No Mathlib; core Lean 4 only. `by_contra` is unavailable.
-/

import Lara.Grounded

namespace Lara.PW

open Lara.Grounded

/-- **Total attack bisimulation** between two finite frameworks. -/
structure AttackBisim (F G : AF) (Z : Arg → Arg → Prop) : Prop where
  /-- `Z` relates carrier members only -/
  dom : ∀ a a', Z a a' → a ∈ F.args ∧ a' ∈ G.args
  /-- every source argument has a related target argument -/
  left_total : ∀ a, a ∈ F.args → ∃ a', Z a a'
  /-- every target argument has a related source argument — the clause the
  T7 target violates at its unmatched attacker -/
  right_total : ∀ a', a' ∈ G.args → ∃ a, Z a a'
  /-- forth: a source attacker of `a` is matched by a related target attacker
  of `a'` -/
  forth : ∀ a a' b, Z a a' → b ∈ F.args → F.attack b a = true →
    ∃ b', Z b b' ∧ G.attack b' a' = true
  /-- back: a target attacker of `a'` is matched by a related source attacker
  of `a` -/
  back : ∀ a a' b', Z a a' → b' ∈ G.args → G.attack b' a' = true →
    ∃ b, Z b b' ∧ F.attack b a = true

/-- The converse relation is a bisimulation the other way. -/
theorem AttackBisim.symm {F G : AF} {Z : Arg → Arg → Prop}
    (h : AttackBisim F G Z) : AttackBisim G F (fun a' a => Z a a') where
  dom := fun a' a hZ => ⟨(h.dom a a' hZ).2, (h.dom a a' hZ).1⟩
  left_total := h.right_total
  right_total := h.left_total
  forth := fun a' a b' hZ hb' hatt => h.back a a' b' hZ hb' hatt
  back := fun a' a b hZ hb hatt => h.forth a a' b hZ hb hatt

/-! ### The induction -/

mutual
  /-- `DirectIn` transfers along `Z`: every target attacker of `a'` is, by
  `back`, related to a source attacker of `a`, which is directly out. -/
  theorem directIn_bisim {F G : AF} {Z : Arg → Arg → Prop}
      (h : AttackBisim F G Z) {a : Arg} :
      DirectIn F a → ∀ a', Z a a' → DirectIn G a'
    | .intro _ hb, a', hZ =>
        .intro (h.dom _ a' hZ).2 (fun b' hb' hatt =>
          match h.back _ a' b' hZ hb' hatt with
          | ⟨b, hZb, hattF⟩ =>
              directOut_bisim h (hb b (h.dom b b' hZb).1 hattF) b' hZb)
  /-- `DirectOut` transfers along `Z`: the directly-in source attacker of `b`
  is, by `forth`, matched by a related target attacker of `b'`. -/
  theorem directOut_bisim {F G : AF} {Z : Arg → Arg → Prop}
      (h : AttackBisim F G Z) {b : Arg} :
      DirectOut F b → ∀ b', Z b b' → DirectOut G b'
    | .intro hc hcb, b', hZ =>
        match h.forth _ b' _ hZ (directIn_mem_args hc) hcb with
        | ⟨c', hZc, hatt'⟩ => .intro (directIn_bisim h hc c' hZc) hatt'
end

/-- The iff form of `directIn_bisim`, from `AttackBisim.symm`. -/
theorem directIn_iff_of_bisim {F G : AF} {Z : Arg → Arg → Prop}
    (h : AttackBisim F G Z) {a a' : Arg} (hZ : Z a a') :
    DirectIn F a ↔ DirectIn G a' :=
  ⟨fun hin => directIn_bisim h hin a' hZ,
   fun hin => directIn_bisim h.symm hin a hZ⟩

/-- The iff form of `directOut_bisim`, from `AttackBisim.symm`. -/
theorem directOut_iff_of_bisim {F G : AF} {Z : Arg → Arg → Prop}
    (h : AttackBisim F G Z) {a a' : Arg} (hZ : Z a a') :
    DirectOut F a ↔ DirectOut G a' :=
  ⟨fun hout => directOut_bisim h hout a' hZ,
   fun hout => directOut_bisim h.symm hout a hZ⟩

/-! ### Argument level: the grounded label -/

/-- **Grounded labels are bisimulation-invariant.** -/
theorem labelC_of_bisim {F G : AF} {Z : Arg → Arg → Prop}
    (h : AttackBisim F G Z) {a a' : Arg} (hZ : Z a a') :
    labelC F a = labelC G a' := by
  rw [labelC_spec, labelC_spec]
  by_cases hin : DirectIn F a
  · rw [if_pos hin, if_pos ((directIn_iff_of_bisim h hZ).mp hin)]
  · have hin' : ¬ DirectIn G a' :=
      fun h' => hin ((directIn_iff_of_bisim h hZ).mpr h')
    rw [if_neg hin, if_neg hin']
    by_cases hout : DirectOut F a
    · rw [if_pos hout, if_pos ((directOut_iff_of_bisim h hZ).mp hout)]
    · have hout' : ¬ DirectOut G a' :=
        fun h' => hout ((directOut_iff_of_bisim h hZ).mpr h')
      rw [if_neg hout, if_neg hout']

/-! ### Claim level: complete-support-set correspondence -/

/-- The complete-support index sets of two claims correspond under `Z`, in
both directions. This is the design's "maps the complete support set for `c`
onto the complete support set for `τ(c)`", stated relationally: no target
support is unmatched (second clause) and no source support is dropped
(first clause). -/
def SupportCorr (Z : Arg → Arg → Prop) (c c' : Claim) : Prop :=
  (∀ a, a ∈ c.support → ∃ a', a' ∈ c'.support ∧ Z a a') ∧
  (∀ a', a' ∈ c'.support → ∃ a, a ∈ c.support ∧ Z a a')

/-- `statusC` reads a claim only through emptiness of its support and, per
label, existence of a support argument with that label. Two claims over two
frameworks agreeing on those observations have the same status. -/
theorem statusC_congr {F G : AF} {c c' : Claim}
    (hempty : c.support = [] ↔ c'.support = [])
    (hlab : ∀ l : Label,
      (∃ a, a ∈ c.support ∧ labelC F a = l) ↔
        (∃ a', a' ∈ c'.support ∧ labelC G a' = l)) :
    statusC F c = statusC G c' := by
  have hany : ∀ l : Label,
      c.support.any (fun a => labelC F a == l) =
        c'.support.any (fun a => labelC G a == l) := by
    intro l
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true, List.any_eq_true]
    simp only [beq_iff_eq]
    exact hlab l
  unfold statusC
  by_cases h0 : c.support = []
  · rw [if_pos h0, if_pos (hempty.mp h0)]
  · rw [if_neg h0, if_neg (fun h' => h0 (hempty.mpr h')), hany .inn, hany .undec]

/-- **Four-state status is bisimulation-invariant** on corresponding claims.
All four statuses at once: the theorem is an equation between the two
`statusC` values, so `gap`, `justified`, `contested`, and `defeated` each
transfer without being treated as argument labels. -/
theorem statusC_of_bisim {F G : AF} {Z : Arg → Arg → Prop} {c c' : Claim}
    (h : AttackBisim F G Z) (hc : SupportCorr Z c c') :
    statusC F c = statusC G c' := by
  apply statusC_congr
  · constructor
    · intro h0
      cases hs : c'.support with
      | nil => rfl
      | cons a' rest =>
        obtain ⟨a, ha, _⟩ := hc.2 a' (by rw [hs]; exact List.mem_cons_self ..)
        rw [h0] at ha
        exact absurd ha List.not_mem_nil
    · intro h0
      cases hs : c.support with
      | nil => rfl
      | cons a rest =>
        obtain ⟨a', ha', _⟩ := hc.1 a (by rw [hs]; exact List.mem_cons_self ..)
        rw [h0] at ha'
        exact absurd ha' List.not_mem_nil
  · intro l
    constructor
    · rintro ⟨a, ha, hl⟩
      obtain ⟨a', ha', hZ⟩ := hc.1 a ha
      exact ⟨a', ha', (labelC_of_bisim h hZ).symm.trans hl⟩
    · rintro ⟨a', ha', hl⟩
      obtain ⟨a, ha, hZ⟩ := hc.2 a' ha'
      exact ⟨a, ha, (labelC_of_bisim h hZ).trans hl⟩

/-! ### The design's AF isomorphism, as a corollary -/

/-- An argumentation-framework isomorphism along `f`: a bijection between the
carriers that preserves and reflects attack. `inj` is recorded because it is
what "isomorphism" means; no proof below consumes it — a surjective bounded
morphism already suffices, which is the finding this module records. -/
structure AFIso (F G : AF) (f : Arg → Arg) : Prop where
  /-- `f` carries the source carrier into the target carrier -/
  maps : ∀ a, a ∈ F.args → f a ∈ G.args
  /-- `f` is injective on the carrier — recorded, never consumed -/
  inj : ∀ a b, a ∈ F.args → b ∈ F.args → f a = f b → a = b
  /-- `f` is onto the target carrier; this is what discharges both the
  right-totality and the `back` clause of the induced bisimulation -/
  surj : ∀ a', a' ∈ G.args → ∃ a, a ∈ F.args ∧ f a = a'
  /-- `f` both preserves and reflects attack on the carrier -/
  attack_iff : ∀ a b, a ∈ F.args → b ∈ F.args →
    (F.attack a b = true ↔ G.attack (f a) (f b) = true)

/-- The graph of `f` restricted to the source carrier. Not a projection of
`AFIso` despite the namespace — it takes no `AFIso`, so spell it
`AFIso.graph F f`, never `h.graph`. -/
def AFIso.graph (F : AF) (f : Arg → Arg) : Arg → Arg → Prop :=
  fun a a' => a ∈ F.args ∧ f a = a'

/-- **The design's isomorphism is a bisimulation.** The graph of `f` is total
both ways — left by `maps`, right by `surj` — and `surj` is again what supplies
the `back` witness, since a target attacker must be exhibited as an `f`-image
before `attack_iff` can reflect it. `inj` is never needed. -/
theorem AFIso.toBisim {F G : AF} {f : Arg → Arg} (h : AFIso F G f) :
    AttackBisim F G (AFIso.graph F f) where
  dom := fun a a' ⟨ha, he⟩ => ⟨ha, he ▸ h.maps a ha⟩
  left_total := fun a ha => ⟨f a, ha, rfl⟩
  right_total := fun a' ha' =>
    match h.surj a' ha' with
    | ⟨a, ha, he⟩ => ⟨a, ha, he⟩
  forth := fun a a' b ⟨ha, he⟩ hb hatt =>
    ⟨f b, ⟨hb, rfl⟩, he ▸ (h.attack_iff b a hb ha).mp hatt⟩
  back := fun a a' b' ⟨ha, he⟩ hb' hatt => by
    obtain ⟨b, hb, hbe⟩ := h.surj b' hb'
    refine ⟨b, ⟨hb, hbe⟩, (h.attack_iff b a hb ha).mpr ?_⟩
    rw [hbe, he]
    exact hatt

/-- Grounded labels transfer along an isomorphism, at every carrier member. -/
theorem labelC_of_iso {F G : AF} {f : Arg → Arg} (h : AFIso F G f)
    {a : Arg} (ha : a ∈ F.args) : labelC F a = labelC G (f a) :=
  labelC_of_bisim h.toBisim ⟨ha, rfl⟩

/-- **T8, isomorphism route (abstract layer).** -/
theorem statusC_of_iso {F G : AF} {f : Arg → Arg} {c c' : Claim}
    (h : AFIso F G f) (hc : SupportCorr (AFIso.graph F f) c c') :
    statusC F c = statusC G c' :=
  statusC_of_bisim h.toBisim hc

/-- The design's "onto" phrasing: if `c`'s support lies in the carrier and
`c'`'s support is exactly the `f`-image of `c`'s, the two correspond. -/
theorem supportCorr_of_image {F : AF} {f : Arg → Arg} {c c' : Claim}
    (hsub : ∀ a, a ∈ c.support → a ∈ F.args)
    (himg : ∀ a', a' ∈ c'.support ↔ ∃ a, a ∈ c.support ∧ f a = a') :
    SupportCorr (AFIso.graph F f) c c' :=
  ⟨fun a ha => ⟨f a, (himg (f a)).mpr ⟨a, ha, rfl⟩, hsub a ha, rfl⟩,
   fun a' ha' =>
     match (himg a').mp ha' with
     | ⟨a, ha, he⟩ => ⟨a, ha, hsub a ha, he⟩⟩

end Lara.PW
