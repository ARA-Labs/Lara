import Lara.Process.Coverage
import Lara.Blocked
import Mathlib.Algebra.Order.Ring.Rat

/-!
Profiles, entitlement and no-promotion.

Entitlement follows a justification norm, not a truth or knowledge norm: only a
non-factive norm can be decided from a record. Pollock's warrant gives it its
operational form, an ultimately undefeated argument, which is Lara's grounded
`in` label. A profile states the inductive-risk policy explicitly: admissible
evidence kinds, accepted scoped coverage, the guarantee class and level, and
the error kinds the method must have probed.

Warrant is keyed by the justification witness, not by public status: two
histories can give a claim the same status through different arguments
(`Lara.Examples.ProcessFalseLaws.unchanged_status_different_basis`). The two
record-level judgments keep the frozen quantifier order: `Entitled` asks for some
warranting witness in each compatible history, `ArgumentEntitled` for one fixed
submitted witness in all of them.
-/

namespace Lara.Process

open Lara.Grounded

universe u v w

/-! ### The warrant model -/

/-- What one complete history says about warrant: the full kinded argumentation
framework, the argument each witness submits, what it concludes, which errors
its method probed, which guarantee it attains, and an external artifact check
(for example a BHL `ArtifactWarrant`, or `True` when none is bound). `truth` is
the claim's truth at the history, kept separate from every warrant field. -/
structure WarrantModel (H : Type u) (Claim : Type v) (Wit : Type w) where
  af : H → AF
  kind : H → Arg → EvidenceKind
  argOf : Wit → Arg
  concludes : H → Wit → Claim → Prop
  probed : H → Wit → Finset ErrorKind
  achieved : H → Wit → GuaranteeClass × ℚ
  artifact : H → Wit → Prop
  truth : H → Claim → Prop

variable {H : Type u} {Claim : Type v} {Wit : Type w} {Policy : Type}

namespace WarrantModel

/-- The framework a profile sees: only arguments of admissible kinds. -/
def underProfile (M : WarrantModel H Claim Wit) (P : Profile Policy) (h : H) : AF :=
  ⟨(M.af h).args.filter fun a => decide (M.kind h a ∈ P.admissible), (M.af h).attack⟩

end WarrantModel

/-- A profile's guarantee is met by an attained guarantee of the same class at a
level no larger than the profile's. -/
def GuaranteeMet (required attained : GuaranteeClass × ℚ) : Prop :=
  attained.1 = required.1 ∧ attained.2 ≤ required.2

instance (required attained : GuaranteeClass × ℚ) : Decidable (GuaranteeMet required attained) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The profile and model checks of a witness, apart from the external artifact
check: `w` concludes `c`, its argument has an admissible kind, every required
error was probed, the guarantee is met, and the argument is grounded `in` in
the framework the profile sees. -/
def ProfileChecks (M : WarrantModel H Claim Wit) (P : Profile Policy) (h : H) (c : Claim)
    (w : Wit) : Prop :=
  M.concludes h w c ∧ M.kind h (M.argOf w) ∈ P.admissible ∧
    P.requiredProbes ⊆ M.probed h w ∧ GuaranteeMet P.guarantee (M.achieved h w) ∧
    labelC (M.underProfile P h) (M.argOf w) = .inn

/-- Witness `w` warrants claim `c` in complete history `h` under profile `P`:
the external artifact check holds and so do the profile checks. -/
def Warranted (M : WarrantModel H Claim Wit) (P : Profile Policy) (h : H) (c : Claim)
    (w : Wit) : Prop :=
  M.artifact h w ∧ ProfileChecks M P h c w

instance (M : WarrantModel H Claim Wit) (P : Profile Policy) (h : H) (c : Claim) (w : Wit)
    [Decidable (M.concludes h w c)] : Decidable (ProfileChecks M P h c w) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (M : WarrantModel H Claim Wit) (P : Profile Policy) (h : H) (c : Claim) (w : Wit)
    [Decidable (M.artifact h w)] [Decidable (M.concludes h w c)] :
    Decidable (Warranted M P h c w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The admitted assumptions of a record: a scoped coverage assertion, which the
profile must accept, read through the model's process traces and reported
events, together with any further admitted restriction `extra`. The coverage
assertion is therefore never detached from its meaning. -/
structure Admitted (H : Type u) (Rho : Type v) (Policy : Type) where
  coverage : RecordCoverage Policy
  policy : Policy → ProcessHistory → List Stamped → Prop
  trace : H → ProcessHistory
  exposed : H → Rho → List Stamped
  extra : Assumptions H Rho

/-- The compatibility restriction admitted assumptions impose. -/
@[reducible] def Admitted.assumptions {H : Type u} {Rho : Type v} {Policy : Type}
    (A : Admitted H Rho Policy) : Assumptions H Rho :=
  (A.coverage.assumptions A.policy A.trace A.exposed).and A.extra

/-- The coverage assertion's own restriction is part of the admitted one. -/
theorem Admitted.stronger_coverage {H : Type u} {Rho : Type v} {Policy : Type}
    (A : Admitted H Rho Policy) :
    A.assumptions.Stronger (A.coverage.assumptions A.policy A.trace A.exposed) :=
  fun _ _ allowed => allowed.1

variable {Rho : Type} {R : Type}

/-- Claim-level entitlement: the profile accepts the admitted coverage, the
compatible set is nonempty, and each compatible history has some warranting
witness. -/
def Entitled (M : WarrantModel H Claim Wit) (P : Profile Policy) (S : ProcessModel H Rho R)
    (A : Admitted H Rho Policy) (r : R) (c : Claim) : Prop :=
  P.acceptsCoverage A.coverage = true ∧
    EntitledBy (Compatible S A.assumptions r) (fun x w => Warranted M P x.1 c w)

/-- Submitted-argument entitlement: as `Entitled`, but one fixed witness must
warrant in every compatible history. ARA argument audits use this judgment. -/
def ArgumentEntitled (M : WarrantModel H Claim Wit) (P : Profile Policy)
    (S : ProcessModel H Rho R) (A : Admitted H Rho Policy) (r : R) (c : Claim) (w : Wit) :
    Prop :=
  P.acceptsCoverage A.coverage = true ∧
    ArgumentEntitledBy (Compatible S A.assumptions r) (fun x w => Warranted M P x.1 c w) w

section Decidability

variable {X : Type u} {W : Type v}

instance [Fintype X] [Fintype W] (compat : X → Prop) [DecidablePred compat]
    (warranted : X → W → Prop) [∀ x w, Decidable (warranted x w)] :
    Decidable (EntitledBy compat warranted) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance [Fintype X] (compat : X → Prop) [DecidablePred compat]
    (warranted : X → W → Prop) [∀ x w, Decidable (warranted x w)] (w : W) :
    Decidable (ArgumentEntitledBy compat warranted w) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance [Fintype H] [Fintype Rho] [Fintype Wit] (M : WarrantModel H Claim Wit)
    (P : Profile Policy) (S : ProcessModel H Rho R) (A : Admitted H Rho Policy) (r : R)
    (c : Claim) [DecidablePred S.Valid] [∀ h, DecidablePred (A.assumptions.Allowed h)]
    [DecidableEq R] [∀ h w, Decidable (M.artifact h w)] [∀ h w, Decidable (M.concludes h w c)] :
    Decidable (Entitled M P S A r c) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance [Fintype H] [Fintype Rho] (M : WarrantModel H Claim Wit)
    (P : Profile Policy) (S : ProcessModel H Rho R) (A : Admitted H Rho Policy) (r : R)
    (c : Claim) (w : Wit) [DecidablePred S.Valid] [∀ h, DecidablePred (A.assumptions.Allowed h)]
    [DecidableEq R] [∀ h w, Decidable (M.artifact h w)] [∀ h w, Decidable (M.concludes h w c)] :
    Decidable (ArgumentEntitled M P S A r c w) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Decidability

/-- Auditing the submitted argument is stronger than claim-level entitlement. -/
theorem argumentEntitledBy_implies_entitledBy {X : Type u} {W : Type v} {compat : X → Prop}
    {warranted : X → W → Prop} {w : W} (h : ArgumentEntitledBy compat warranted w) :
    EntitledBy compat warranted :=
  ⟨h.1, fun x hx => ⟨w, h.2 x hx⟩⟩

theorem argumentEntitled_implies_entitled {M : WarrantModel H Claim Wit} {P : Profile Policy}
    {S : ProcessModel H Rho R} {A : Admitted H Rho Policy} {r : R} {c : Claim} {w : Wit}
    (h : ArgumentEntitled M P S A r c w) : Entitled M P S A r c :=
  ⟨h.1, argumentEntitledBy_implies_entitledBy h.2⟩

/-- Entitlement is a positive verdict: it implies a compatible history exists,
and the warrant property's verdict is `certainTrue` for an audited witness. -/
theorem argumentEntitled_verdict {M : WarrantModel H Claim Wit} {P : Profile Policy}
    {S : ProcessModel H Rho R} {A : Admitted H Rho Policy} {r : R} {c : Claim} {w : Wit}
    (h : ArgumentEntitled M P S A r c w) :
    verdictOf (Compatible S A.assumptions r) (fun x => Warranted M P x.1 c w) = .certainTrue :=
  (verdictOf_certainTrue_iff _ _).mpr h.2

/-! ### The strict profile -/

/-- The one concrete profile: complete or count-bounded coverage, observed
evidence only, FWER at `α`, sampling error probed, grounded acceptance. -/
def Profile.strict (α : ℚ) : Profile Policy where
  admissible := {.observed}
  acceptsCoverage
    | .complete _ => true
    | .countBounded _ _ => true
    | _ => false
  guarantee := (.fwer, α)
  requiredProbes := {.sampling}
  acceptance := .groundedJustified

/-! ### No promotion -/

/-- A derivation tree annotated with evidence kinds. Rules have at least one
premise; a premise-free step is a leaf. -/
inductive KindDerivation where
  | leaf (kind : EvidenceKind)
  | unary (out : EvidenceKind) (premise : KindDerivation)
  | binary (out : EvidenceKind) (left right : KindDerivation)
  deriving DecidableEq, Repr

namespace KindDerivation

/-- The kind a derivation concludes with. -/
def kind : KindDerivation → EvidenceKind
  | .leaf k => k
  | .unary out _ => out
  | .binary out _ _ => out

/-- Every rule outputs a kind at most the meet of its inputs. -/
def WellKinded : KindDerivation → Prop
  | .leaf _ => True
  | .unary out p => out ≤ p.kind ∧ p.WellKinded
  | .binary out l r => out ≤ l.kind ⊓ r.kind ∧ l.WellKinded ∧ r.WellKinded

/-- `WellKinded` is decidable. -/
@[reducible] def decWellKinded : (d : KindDerivation) → Decidable d.WellKinded
  | .leaf _ => isTrue True.intro
  | .unary out p => @instDecidableAnd _ _ (inferInstanceAs (Decidable (out ≤ p.kind)))
      (decWellKinded p)
  | .binary out l r => @instDecidableAnd _ _ (inferInstanceAs (Decidable (out ≤ l.kind ⊓ r.kind)))
      (@instDecidableAnd _ _ (decWellKinded l) (decWellKinded r))

instance (d : KindDerivation) : Decidable d.WellKinded := decWellKinded d

/-- The meet of all leaf kinds. -/
def leafMeet : KindDerivation → EvidenceKind
  | .leaf k => k
  | .unary _ p => p.leafMeet
  | .binary _ l r => l.leafMeet ⊓ r.leafMeet

/-- Every leaf kind. -/
def leaves : KindDerivation → List EvidenceKind
  | .leaf k => [k]
  | .unary _ p => p.leaves
  | .binary _ l r => l.leaves ++ r.leaves

/-- A well-kinded derivation concludes at most the meet of its leaves. -/
theorem kind_le_leafMeet : ∀ {d : KindDerivation}, d.WellKinded → d.kind ≤ d.leafMeet
  | .leaf _, _ => le_rfl
  | .unary _ _, ⟨out, wp⟩ => out.trans (kind_le_leafMeet wp)
  | .binary _ _ _, ⟨out, wl, wr⟩ =>
      out.trans (inf_le_inf (kind_le_leafMeet wl) (kind_le_leafMeet wr))

theorem leafMeet_le_of_mem : ∀ {d : KindDerivation} {k : EvidenceKind}, k ∈ d.leaves →
    d.leafMeet ≤ k
  | .leaf _, _, mem => by simp only [leaves, List.mem_singleton] at mem; subst mem; exact le_rfl
  | .unary _ p, _, mem => leafMeet_le_of_mem (d := p) mem
  | .binary _ l r, _, mem => by
      rcases List.mem_append.mp mem with m | m
      · exact inf_le_left.trans (leafMeet_le_of_mem m)
      · exact inf_le_right.trans (leafMeet_le_of_mem m)

/-- One leaf at or below `k` bounds the conclusion by `k`. -/
theorem no_promotion_any_leaf {d : KindDerivation} (wk : d.WellKinded) {k : EvidenceKind}
    (leaf : ∃ l ∈ d.leaves, l ≤ k) : d.kind ≤ k := by
  obtain ⟨l, mem, le⟩ := leaf
  exact (kind_le_leafMeet wk).trans ((leafMeet_le_of_mem mem).trans le)

/-- No derivation whose leaves are all hypothetical or conditional concludes an
observed (or even supported) kind. -/
theorem no_promotion {d : KindDerivation} (wk : d.WellKinded)
    (leaves : ∀ l ∈ d.leaves, l ≤ .conditional) : d.kind ≤ .conditional ∧ d.kind ≠ .observed := by
  have nonempty : ∃ l, l ∈ d.leaves := by
    induction d with
    | leaf k => exact ⟨k, List.mem_singleton_self k⟩
    | unary _ p ih => exact ih wk.2 leaves
    | binary _ l r ihl _ =>
        obtain ⟨k, mem⟩ := ihl wk.2.1 (fun k m => leaves k (List.mem_append_left _ m))
        exact ⟨k, List.mem_append_left _ mem⟩
  obtain ⟨l, mem⟩ := nonempty
  have le := no_promotion_any_leaf wk ⟨l, mem, leaves l mem⟩
  exact ⟨le, fun eq => by rw [eq] at le; exact absurd le (by decide)⟩

end KindDerivation

/-- No promotion at the profile level: an argument whose kind is computed by a
well-kinded derivation with only hypothetical or conditional leaves is never
warranted under the strict profile. -/
theorem strict_no_promotion {M : WarrantModel H Claim Wit} {α : ℚ} {h : H} {c : Claim}
    {w : Wit} {d : KindDerivation} (wk : d.WellKinded)
    (leaves : ∀ l ∈ d.leaves, l ≤ .conditional) (kind : M.kind h (M.argOf w) = d.kind) :
    ¬ Warranted M (Profile.strict (Policy := Policy) α) h c w := by
  rintro ⟨_, _, admissible, _⟩
  have obs : M.kind h (M.argOf w) = .observed := by
    simpa [Profile.strict] using admissible
  exact (KindDerivation.no_promotion wk leaves).2 (kind ▸ obs)

/-- Agreement with the core's blocking non-promotion: an argument warranted in
the framework a profile sees, and outside a blocked set `B` relating that
framework to a larger declared one, is grounded `in` and its singleton claim is
`justified` in the declared framework. This is `Blocked.justified_nonpromotion`
specialized to a warrant witness. -/
theorem no_promotion_agrees_blocking {M : WarrantModel H Claim Wit} {P : Profile Policy}
    {h : H} {c : Claim} {w : Wit} {G : AF} {B : List Arg}
    (blocking : Blocked.Blocking (M.underProfile P h) G B) (unblocked : M.argOf w ∉ B)
    (warranted : Warranted M P h c w) :
    labelC G (M.argOf w) = .inn ∧ statusC G ⟨[M.argOf w], []⟩ = .justified := by
  have inn := warranted.2.2.2.2.2
  have mem : M.argOf w ∈ (M.underProfile P h).args :=
    directIn_mem_args ((labelC_inn_iff _).mp inn)
  have justified : statusC (M.underProfile P h) ⟨[M.argOf w], []⟩ = .justified :=
    (statusC_justified_iff _ _).mpr ⟨_, List.mem_singleton_self _, inn⟩
  refine ⟨(Blocked.labelC_agree blocking mem unblocked).symm.trans inn, ?_⟩
  exact Blocked.justified_nonpromotion blocking
    (fun a ha => by simp only [List.mem_singleton] at ha; subst ha; exact mem)
    (fun a ha => by simp only [List.mem_singleton] at ha; subst ha; exact unblocked)
    (fun _ ha => ha) justified

/-! ### Directional strictness -/

/-- `x` is in the attack ancestry of `target`: `target` itself, or an argument
attacking something in the ancestry. Grounded labels read only this region. -/
inductive Ancestor (F : AF) (target : Arg) : Arg → Prop where
  | self : Ancestor F target target
  | attacker {x y : Arg} : Ancestor F target y → x ∈ F.args → F.attack x y = true →
      Ancestor F target x

/-- Removing arguments outside a target's attack ancestry is a blocking edit
that leaves the target unblocked: the blocked set is every non-ancestor. -/
theorem ancestry_blocking {F G : AF} {t : Arg} (sub : ∀ a, a ∈ F.args → a ∈ G.args)
    (sameAttack : F.attack = G.attack)
    (directional : ∀ x, x ∈ G.args → x ∉ F.args → ¬ Ancestor G t x) :
    ∃ B, Blocked.Blocking F G B ∧ t ∉ B := by
  classical
  let B := G.args.filter fun x => decide (¬ Ancestor G t x)
  have memB : ∀ x, x ∈ B ↔ x ∈ G.args ∧ ¬ Ancestor G t x := by
    intro x; simp [B]
  refine ⟨B, ⟨sub, fun x hG hF => (memB x).mpr ⟨hG, directional x hG hF⟩, ?_,
    fun _ _ _ _ _ => by rw [sameAttack]⟩, fun hb => ((memB _).mp hb).2 Ancestor.self⟩
  intro x hx y hy hxy
  refine (memB y).mpr ⟨hy, fun anc => ((memB x).mp hx).2 ?_⟩
  exact Ancestor.attacker anc ((memB x).mp hx).1 hxy

/-- `Q` is stricter than `P`: it admits fewer kinds, accepts less coverage,
requires more probes and demands a guarantee of the same class at a level no
larger. `Acceptance` has the single standard `groundedJustified`, so it is not
compared; a second standard would need a field here. -/
structure Profile.Stricter (Q P : Profile Policy) : Prop where
  admissible : Q.admissible ⊆ P.admissible
  coverage : ∀ c, Q.acceptsCoverage c = true → P.acceptsCoverage c = true
  probes : P.requiredProbes ⊆ Q.requiredProbes
  guaranteeClass : Q.guarantee.1 = P.guarantee.1
  guaranteeLevel : Q.guarantee.2 ≤ P.guarantee.2

/-- The directional law: if every argument the stricter profile removes attacks
nothing in the witness's ancestry, warrant under the stricter profile implies
warrant under the laxer one. Without the side condition the law is false
(`Lara.Examples.ProcessFalseLaws.stricter_profile_reinstates`). -/
theorem stricter_directional {M : WarrantModel H Claim Wit} {Q P : Profile Policy}
    (stricter : Q.Stricter P) {h : H} {c : Claim} {w : Wit}
    (directional : ∀ x, x ∈ (M.underProfile P h).args → x ∉ (M.underProfile Q h).args →
      ¬ Ancestor (M.underProfile P h) (M.argOf w) x)
    (warranted : Warranted M Q h c w) : Warranted M P h c w := by
  obtain ⟨artifact, concludes, admissible, probes, guarantee, inn⟩ := warranted
  have sub : ∀ a, a ∈ (M.underProfile Q h).args → a ∈ (M.underProfile P h).args := by
    intro a ha
    simp only [WarrantModel.underProfile, List.mem_filter, decide_eq_true_eq] at ha ⊢
    exact ⟨ha.1, stricter.admissible ha.2⟩
  obtain ⟨B, blocking, unblocked⟩ := ancestry_blocking sub rfl directional
  have mem := directIn_mem_args ((labelC_inn_iff _).mp inn)
  refine ⟨artifact, concludes, stricter.admissible admissible,
    stricter.probes.trans probes, ?_, ?_⟩
  · exact ⟨guarantee.1.trans stricter.guaranteeClass, le_trans guarantee.2 stricter.guaranteeLevel⟩
  · exact (Blocked.labelC_agree blocking mem unblocked).symm.trans inn

/-- The directional law lifted to submitted-argument entitlement. -/
theorem stricter_directional_argument {M : WarrantModel H Claim Wit} {Q P : Profile Policy}
    (stricter : Q.Stricter P) {S : ProcessModel H Rho R} {A : Admitted H Rho Policy} {r : R}
    {c : Claim} {w : Wit}
    (directional : ∀ x, Compatible S A.assumptions r x → ∀ y,
      y ∈ (M.underProfile P x.1).args → y ∉ (M.underProfile Q x.1).args →
        ¬ Ancestor (M.underProfile P x.1) (M.argOf w) y)
    (entitled : ArgumentEntitled M Q S A r c w) : ArgumentEntitled M P S A r c w :=
  ⟨stricter.coverage _ entitled.1, entitled.2.1,
    fun x hx => stricter_directional stricter (directional x hx) (entitled.2.2 x hx)⟩

/-- The directional law lifted to claim-level entitlement, when the side
condition holds for every witness. -/
theorem stricter_directional_entitled {M : WarrantModel H Claim Wit} {Q P : Profile Policy}
    (stricter : Q.Stricter P) {S : ProcessModel H Rho R} {A : Admitted H Rho Policy} {r : R}
    {c : Claim}
    (directional : ∀ x, Compatible S A.assumptions r x → ∀ w y,
      y ∈ (M.underProfile P x.1).args → y ∉ (M.underProfile Q x.1).args →
        ¬ Ancestor (M.underProfile P x.1) (M.argOf w) y)
    (entitled : Entitled M Q S A r c) : Entitled M P S A r c := by
  refine ⟨stricter.coverage _ entitled.1, entitled.2.1, fun x hx => ?_⟩
  obtain ⟨w, hw⟩ := entitled.2.2 x hx
  exact ⟨w, stricter_directional stricter (directional x hx w) hw⟩

/-- Profile restriction never manufactures acceptance: if every argument the
profile removes from the full framework lies outside the witness's ancestry,
an argument `in` under the profile is `in` in the full framework, and its
singleton claim is `justified` there. This is the evidence-kind counterpart of
`Blocked.justified_nonpromotion`, which states the same for quarantine. -/
theorem profile_restriction_nonpromotion {M : WarrantModel H Claim Wit} {P : Profile Policy}
    {h : H} {c : Claim} {w : Wit}
    (directional : ∀ x, x ∈ (M.af h).args → x ∉ (M.underProfile P h).args →
      ¬ Ancestor (M.af h) (M.argOf w) x)
    (warranted : Warranted M P h c w) :
    labelC (M.af h) (M.argOf w) = .inn ∧ statusC (M.af h) ⟨[M.argOf w], []⟩ = .justified := by
  obtain ⟨B, blocking, unblocked⟩ :=
    ancestry_blocking (F := M.underProfile P h) (G := M.af h)
      (fun _ ha => (List.mem_filter.mp ha).1) rfl directional
  exact no_promotion_agrees_blocking blocking unblocked warranted

/-! ### Non-factivity -/

/-- Knowledge at a history: the claim is true at every history the agent
cannot distinguish from it. BHL's `K` is the instance whose accessibility is
observation equivalence of complete traces (`Lara.BHL.Accessible`). -/
def Known (M : WarrantModel H Claim Wit) (accessible : H → H → Prop) (h : H) (c : Claim) : Prop :=
  ∀ h', accessible h h' → M.truth h' c

end Lara.Process
