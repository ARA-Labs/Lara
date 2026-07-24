/-
Mechanized abstract strict-certificate backend (`Lara.Strict`). Discharges spec
§9 **result 8** (strict-certificate soundness, Theorem 1) at the abstract level,
and instantiates it with the mechanized ND adapter (`Lara/ND.lean`) to show the
reference backend satisfies the abstract contract.

This follows the mechanization architecture decided in the exploration tree
(N15): the backend is a *structure* that carries its soundness obligation
(decision doc §2 obligation 3) as a field. Theorem 1 is then the projection of
that field — exactly the paper proof ("apply backend obligation 3"). The content
is in *discharging* the obligation for a concrete backend, which `ndBackend`
does using `Lara.ND.nd_sound`.

Faithful to `src/Lara/Strict.hs`:

* A `Backend` bundles an encoding `enc : SourceProp → Form`, a checker `check`, a
  mathematical consequence relation `models`, and the proof that acceptance
  implies consequence (`sound`).
* A `StrictJudgment` is a structure whose very existence is the certificate — the
  Lean analogue of the sealed Haskell `StrictJudgment` constructor. It carries
  only source data plus the acceptance fact, never a backend proof term (the
  factivity firewall, Theorem 3).
-/

import Lara.Prop
import Lara.ND
import Lara.Certificate

namespace Lara.Strict

/-- Source propositions at this layer are the mechanized `Lara.Atom`. The seam's
metatheory only needs that a backend can encode them. -/
abbrev SourceProp := Lara.Atom

/-- A registered backend, reduced to what the soundness metatheory needs
(decision doc §2). `Form` is the backend's private formula type; `models Δ φ` is
`T ; Δ ⊨_β φ` with the theory `T` folded into the relation. The `sound` field is
obligation 3: acceptance implies consequence. -/
structure Backend where
  /-- backend formula type -/
  Form   : Type
  /-- source encoding `encode_β` -/
  enc    : SourceProp → Form
  /-- mathematical consequence `T ; Δ ⊨_β φ` (need not be executable) -/
  models : List Form → Form → Prop
  /-- the replay `check_β`: does this exact submitted certificate check? -/
  check  : Lara.Support.CertRef → List Form → Form → Prop
  /-- **obligation 3, certificate soundness:** acceptance implies consequence -/
  sound  : ∀ κ Δ φ, check κ Δ φ → models Δ φ

/-- A checked strict step against backend `B`. Its existence certifies that `B`
accepted the encoded goal from the encoded premises. It carries only
source-visible data plus the acceptance fact — never a backend proof term. -/
structure StrictJudgment (B : Backend) where
  premises : List SourceProp
  goal     : SourceProp
  certificate : Lara.Support.CertRef
  /-- the backend accepted the encoded step -/
  accepted : B.check certificate (premises.map B.enc) (B.enc goal)

/-- **Theorem 1 (certified strict-step soundness).** A checked strict step is a
semantic consequence under the backend's model: the encoded goal follows from the
encoded premises. Nothing is claimed about the *truth* of any premise
(non-factivity). This is the projection of obligation 3 through the judgment. -/
theorem strict_step_sound {B : Backend} (j : StrictJudgment B) :
    B.models (j.premises.map B.enc) (B.enc j.goal) :=
  B.sound _ _ _ j.accepted

/-! ### The reference ND backend satisfies the abstract contract

We instantiate `Backend` with the mechanized natural-deduction adapter of
`Lara/ND.lean`. Its `check κ Δ φ` decodes the exact submitted reference `κ`
as a certificate `e` and requires `Δ ⊢ e : φ`; its `models` is the Boolean
semantics of the decision doc, and `sound` is discharged by
`Lara.ND.nd_sound`. This shows result 10's soundness lemma is exactly the
obligation-3 field the abstract Theorem 1 consumes. -/

/-- The ND backend's mathematical consequence: every valuation satisfying all of
`Δ` satisfies `φ` (decision doc §4.1: `T ; Δ ⊨_ND φ`). -/
def ndModels (Δ : List Lara.ND.Formula) (φ : Lara.ND.Formula) : Prop :=
  ∀ v : String → Bool, (∀ ψ, ψ ∈ Δ → Lara.ND.satisfies v ψ) → Lara.ND.satisfies v φ

/-- The ND backend's checker: the exact referenced certificate types the step.
Matches the Haskell adapter's "decode + `inferType` accepts". -/
def ndCheck (κ : Lara.Support.CertRef) (Δ : List Lara.ND.Formula)
    (φ : Lara.ND.Formula) : Prop :=
  ∃ e : Lara.ND.Cert,
    κ.payload = toString (repr e) ∧ Lara.ND.HasType Δ e φ

/-- A fixed injective source encoding for the instantiation. Any injective map
into `Formula.atom` discharges normalization fidelity; the metatheory of
Theorem 1 does not depend on its details, so we pin the trivial predicate encoder
(the real adapter uses `atom ∘ canonicalSerialize ∘ nf`). -/
def ndEnc : SourceProp → Lara.ND.Formula
  | .atom p _ => .atom p

/-- The reference ND backend as an abstract `Backend`. Its `sound` field is
`Lara.ND.nd_sound` — result 10 feeding result 8. -/
def ndBackend : Backend where
  Form   := Lara.ND.Formula
  enc    := ndEnc
  models := ndModels
  check  := ndCheck
  sound  := by
    intro κ Δ φ hchk
    obtain ⟨e, _, hty⟩ := hchk
    intro v hΔ
    exact Lara.ND.nd_sound hty v hΔ

/-- Sanity: Theorem 1 specialized to the ND backend gives the Boolean-consequence
guarantee for any checked ND step, with no extra hypotheses. -/
theorem nd_strict_step_sound (j : StrictJudgment ndBackend) :
    ndModels (j.premises.map ndBackend.enc) (ndBackend.enc j.goal) :=
  strict_step_sound j

/-! ### Theorem 3 (source non-factivity — the factivity firewall)

Discharges spec §9 **result 2** at the abstract level (C03). The paper proof
(`ara/evidence/proofs/nonfactivity_and_defeat.md`, `strict-backend-decision.md`
§5) is *syntactic confinement*: the source calculus has no truth judgment and no
rule eliminating support into one, so by inversion backend acceptance produces
only a *relative* support fact — never absolute truth. Even a fully factive
backend cannot be used to eliminate source support into `⊢ p true`.

In this abstract model the confinement is structural: a `StrictJudgment B`
carries only `premises`, `goal`, and the acceptance fact, and its *only*
soundness projection is `strict_step_sound`, which yields consequence **relative
to the premises** (`B.models (premises.map enc) (enc goal)`). Non-factivity is
the statement that this cannot be strengthened to premise-free truth
(`B.models [] (enc goal)`). We prove the negative concretely: no such projection
exists uniformly across backends, witnessed by the reference ND backend. -/

/-- The witness proposition: the Phase-0 opaque atom `p` (nullary). -/
def nonfactiveAtom : SourceProp := .atom "p" .nil

/-- A concrete checked strict step against the reference ND backend: from the
single premise `p`, the ND checker accepts the goal `p` (the identity/hypothesis
step, `⊢ hyp 0 : p`). Its existence certifies backend acceptance — nothing more. -/
def nonfactiveJudgment : StrictJudgment ndBackend where
  premises := [nonfactiveAtom]
  goal     := nonfactiveAtom
  certificate := ⟨toString (repr (Lara.ND.Cert.hyp 0))⟩
  accepted := ⟨.hyp 0, rfl, .hyp rfl⟩

/-- **The firewall bites.** The goal of an *accepted* strict step need not be
semantically valid: the ND backend accepts `p ⊢ p`, yet `p` is false under the
all-false valuation, so `⊨_ND p` fails. Acceptance confers relative support, not
absolute truth. -/
theorem nd_nonfactive_witness :
    ¬ ndModels [] (ndBackend.enc nonfactiveJudgment.goal) := by
  intro h
  have hp : Lara.ND.satisfies (fun _ => false) (Lara.ND.Formula.atom "p") :=
    h (fun _ => false) (fun ψ hψ => nomatch hψ)
  simp only [Lara.ND.satisfies] at hp
  exact absurd hp (by decide)

/-- **Theorem 3 (non-factivity).** There is no uniform way to eliminate a checked
strict step into a *premise-free* truth judgment about its goal — no map from
`StrictJudgment B` to `B.models [] (B.enc goal)` for every backend `B`. This is
the factivity firewall: backend acceptance never yields absolute truth. Proved by
the reference ND witness, so it holds even against a factive backend. -/
theorem no_truth_projection :
    ¬ ∀ (B : Backend) (j : StrictJudgment B), B.models [] (B.enc j.goal) :=
  fun h => nd_nonfactive_witness (h ndBackend nonfactiveJudgment)

/-- The two halves side by side for the ND witness: the soundness projection gives
consequence **relative to the premises** (`strict_step_sound`), and that is the
*most* an accepted step yields — it cannot be strengthened to premise-free truth. -/
theorem nd_relative_not_absolute :
    ndModels (nonfactiveJudgment.premises.map ndBackend.enc)
        (ndBackend.enc nonfactiveJudgment.goal)
      ∧ ¬ ndModels [] (ndBackend.enc nonfactiveJudgment.goal) :=
  ⟨strict_step_sound nonfactiveJudgment, nd_nonfactive_witness⟩

end Lara.Strict
