/-
PW0 — the Lara instantiation of the outer model.

A scientific context fixes the stable local checking environment
(Σ, Policy, Registry) — here the checker parameters `canon`/`Gamma`/`CertOk`
plus the frozen `sigma` and `policy`. A world is one accepted state under
that environment: a `Unit.CheckedUnit` whose `sigma`/`policy` fields match
the context's. The `CheckedUnit` *is* the design's `checked_w` witness — it
exists only for accepted programs, and it carries the retained checker nodes
that `Consistency.completeClaimFor` aggregates.

`Context` means *shared checking environment*, not a particular scientific
state: two worlds of one context differ in admitted evidence, declared
supports, and attacks, and that is intended. Nothing pins the program.

The two independent world-local observations (gate 2):

* `srcStatus` — the relational, oracle-free `Compile.SrcStatus`, read off
  `SrcIn`/`SrcOut` with no compiled framework, no grounded labelling, no
  enumeration;
* `cmpStatus` — the executable `Grounded.statusC` over the compiled
  `Compile.checkedAF`.

Neither is defined through the other; their agreement at every world is T1
(`srcStatus_iff_cmpStatus`), which is `Compile.srcStatus_iff_checked`
instantiated at the world — the existing source-to-compilation preservation
chain, exactly as the design prescribes. T4 is then `sat_congr` at T1, and the
valuation coherence discharges below are T1 again in a second role.

Queries are `Atom`s. The design refines `Query_κ` to well-sorted claims over
`Σ_κ`; the status functions are total on all of `Atom` (a query with no
matching retained node has empty complete support, hence status `gap`), so
PW0 takes the total query set and leaves the well-sortedness refinement to
the surface layer (M5-gated, out of PW0 scope). The cost is recorded as a
limitation in `docs/theory-pw0-outer-model.md`: `gap` currently conflates
"out of vocabulary", "ill-sorted", "not posed", and "posed but unsupported".
The executable layer separates only the bridge-domain case, and reports it as
`translationUndefined` rather than as any status.
-/

import Lara.Consistency
import Lara.PW.Outer

namespace Lara.PW.Instance

open Lara.Support
open Lara.Grounded (Status)

/-- **A scientific context**: the stable local checking environment. Any
change to a stable component is a different `Context` value — the design's
"new versioned scientific context". -/
structure Context where
  canon : String → String
  Gamma : LeafId → Option Atom
  CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop
  sigma : Lara.Sigma.Sigma
  policy : Lara.Policy.Policy

/-- **An admissible local world**: one accepted unit under the context's
environment. The `CheckedUnit` is the acceptance witness; the two equations
pin its stable components to the context's, so worlds of one context differ
only in admitted evidence, declared supports, and attacks. -/
structure World (κ : Context) where
  unit : Lara.Unit.CheckedUnit κ.canon κ.Gamma κ.CertOk
  sigma_eq : unit.sigma = κ.sigma
  policy_eq : unit.policy = κ.policy

/-- The world-local claim projection: complete checked support for `c`,
aggregated from the retained checker nodes. Unchanged local machinery
(`Consistency.completeClaimFor`), merely applied at the world. -/
def claimAt {κ : Context} (w : World κ) (c : Atom) : Lara.Grounded.Claim :=
  Lara.Consistency.completeClaimFor w.unit c

/-- **The compiled observation** `status_w(c)`: executable grounded status of
the locally compiled framework. Total on all queries (empty support ⇒ `gap`). -/
def cmpStatus {κ : Context} (w : World κ) (c : Atom) : Status :=
  Lara.Grounded.statusC (Lara.Compile.checkedAF w.unit.program) (claimAt w c)

/-- **The direct source observation** `srcStatus_w(c)`: the oracle-free
relational status, defined over checked source terms and the source attack
judgment — no compilation, no labelling, no `cmpStatus`. -/
def srcStatus {κ : Context} (w : World κ) (c : Atom) (s : Status) : Prop :=
  Lara.Compile.SrcStatus w.unit.program (claimAt w c) s

/-- **T1 — world-local preservation.** At every well-formed world the two
independently defined observations agree. The proof is
`Compile.srcStatus_iff_checked` instantiated at the world — Lara's existing
source-to-compilation preservation chain, not a new definition. -/
theorem srcStatus_iff_cmpStatus {κ : Context} (w : World κ)
    (c : Atom) (s : Status) :
    srcStatus w c s ↔ cmpStatus w c = s :=
  (Lara.Compile.srcStatus_iff_checked w.unit.program (claimAt w c) s).trans
    eq_comm

/-- **Bridge data over Lara contexts**: the model components the design's
claim-comparison model `𝓜` adds on top of the local layer. `translate` is
bridge-global and partial (the design's explicit first-model restriction). -/
structure BridgeData where
  K : Type
  ctx : K → Context
  B : Type
  bsrc : B → K
  btgt : B → K
  R : (b : B) → World (ctx (bsrc b)) → World (ctx (btgt b)) → Prop
  accept : (b : B) → World (ctx (bsrc b)) → World (ctx (btgt b)) → Prop
  translate : B → Atom → Option Atom

/-- The outer frame a bridge datum induces. Queries are `Atom` in every
context (see module header). Left semireducible on purpose: `@[reducible]`
made `Lara.PW.Instance` nine times slower to elaborate and did not help the
projection-headed dotted notation at use sites. Spell index constructors
explicitly (`OneBridge.it`) instead of `.it` where the expected type is a
`frame.B`/`frame.K` projection. -/
def BridgeData.frame (D : BridgeData) : Lara.PW.Frame where
  K := D.K
  B := D.B
  src := D.bsrc
  tgt := D.btgt
  World := fun κ => World (D.ctx κ)
  Query := fun _ => Atom
  R := D.R
  accept := D.accept
  translate := D.translate

/-- `V^src`: the source valuation of the design's `𝓜_src`. -/
def srcVal (D : BridgeData) : Lara.PW.Valuation D.frame :=
  fun {_} w c s => srcStatus w c s

/-- `V^cmp`: the compiled valuation of the design's `𝓜_cmp` — the executable
comparison model. -/
def cmpVal (D : BridgeData) : Lara.PW.Valuation D.frame :=
  fun {_} w c s => cmpStatus w c = s

/-- **T4 — modal source-compilation coherence.** The same frame under the two
valuations satisfies the same formulas. Induction on the formula
(`PW.sat_congr`); the atomic case is T1; the modal cases use the literally
shared accepted relations. An integration theorem over the outer modal layer —
the substantive result underneath it is T1. -/
theorem sat_src_iff_cmp (D : BridgeData) {κ : D.K}
    (w : D.frame.World κ) (φ : Lara.PW.Form D.frame κ) :
    Lara.PW.Sat D.frame (srcVal D) φ w ↔
      Lara.PW.Sat D.frame (cmpVal D) φ w :=
  Lara.PW.sat_congr D.frame (srcVal D) (cmpVal D)
    (fun _ w c s => srcStatus_iff_cmpStatus w c s) φ w

/-! ### Valuation coherence at the Lara valuations

Both Lara valuations satisfy `PW.Valuation.Functional` / `.Total`, so
`PW.not_sat_two_status` applies and no Lara world reports two statuses for one
claim. The two discharges are asymmetric, and that asymmetry *is* gate 2. -/

/-- `V^cmp` is functional and total: it is an equation against a total
function. -/
theorem cmpVal_functional (D : BridgeData) :
    Lara.PW.Valuation.Functional (cmpVal D) := fun _ _ _ _ h₁ h₂ => h₁ ▸ h₂

theorem cmpVal_total (D : BridgeData) : Lara.PW.Valuation.Total (cmpVal D) :=
  fun w c => ⟨cmpStatus w c, rfl⟩

/-- `V^src` is functional and total — *not* by construction (`SrcStatus` is a
relation) but through T1. This is the side condition that makes the source
model a Lara model. -/
theorem srcVal_functional (D : BridgeData) :
    Lara.PW.Valuation.Functional (srcVal D) := by
  intro _ w c s₁ s₂ h₁ h₂
  have e₁ := (srcStatus_iff_cmpStatus w c s₁).mp h₁
  have e₂ := (srcStatus_iff_cmpStatus w c s₂).mp h₂
  exact e₁ ▸ e₂

theorem srcVal_total (D : BridgeData) :
    Lara.PW.Valuation.Total (srcVal D) := by
  intro _ w c
  exact ⟨cmpStatus w c, (srcStatus_iff_cmpStatus w c _).mpr rfl⟩

/-! ### T0 — current-Lara conservativity

Embedding a current Lara run into a singleton context with no bridges. The
regression content is that the wrapper *defines nothing new locally*: atomic
satisfaction in the embedded model is — definitionally, `Iff.rfl` — the
unchanged local status judgment, and with `B := Empty` the language contains
no modal formula at all, so every embedded formula is a boolean combination
of unchanged local statuses. Public reporting (`evidence-blocked`) is a
reporting-layer concern, stated separately by the design and untouched here. -/

/-- The singleton, bridge-free embedding of one context. -/
def singleton (κ : Context) : BridgeData where
  K := Lara.PW.OneCtx
  ctx := fun _ => κ
  B := Empty
  bsrc := fun b => b.elim
  btgt := fun b => b.elim
  R := fun b => b.elim
  accept := fun b => b.elim
  translate := fun b => b.elim

/-- **T0, compiled side.** Atomic satisfaction in the singleton embedding is
definitionally the unchanged executable status of the unchanged compiled
framework of the unchanged accepted program. `Iff.rfl` is the theorem: there
is no wrapper-introduced layer to unfold. The context index must be given
explicitly (`@Sat … OneCtx.it`) — a world does not determine its context. -/
theorem t0_cmp (κ : Context) (w : World κ) (c : Atom) (s : Status) :
    @Lara.PW.Sat (singleton κ).frame (cmpVal (singleton κ)) .it
        (.status s c) w ↔
      Lara.Grounded.statusC (Lara.Compile.checkedAF w.unit.program)
        (Lara.Consistency.completeClaimFor w.unit c) = s :=
  Iff.rfl

/-- **T0, source side.** The same, for the relational source status. -/
theorem t0_src (κ : Context) (w : World κ) (c : Atom) (s : Status) :
    @Lara.PW.Sat (singleton κ).frame (srcVal (singleton κ)) .it
        (.status s c) w ↔
      Lara.Compile.SrcStatus w.unit.program
        (Lara.Consistency.completeClaimFor w.unit c) s :=
  Iff.rfl

end Lara.PW.Instance
