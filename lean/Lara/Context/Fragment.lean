/-
# Theory M4, phase F0 — the fragment/linking carrier (definitions only)

The frozen shape of the M4 context calculus: fragments, import interfaces,
contexts, the decidable link guard, the saturating link operation, context
composition, the fragment-relative AF, and the observation. **This module
carries definitions; every theorem about them lives in `Lara.Context.Link`,
`Lara.Context.Compose`, and `Lara.Context.Equivalence`.**

The design decisions frozen here are recorded in
`docs/theory-m4-context-calculus-decision.md`; the short form:

* **Contexts live at the core `Lara.Unit` level** (D1). The surface calculus
  (`Lara.Surface.*`) contributes a transport corollary, not the quantification
  domain.
* **`link` saturates and dedupes** (D2, D3). `Compile.AttackComplete` is an
  *all-pairs* condition, so a link that merely concatenated the two attack
  lists could not satisfy `Check.Unit.checkUnit_complete`'s
  `hattackComplete` premise: every cross-boundary contrary conflict onto an
  attackable target must be represented. And because `SupportTerm` equality is
  structural, a context argument built only from imported leaves can be
  structurally identical to a fragment argument; those duplicates are
  **merged**, never rejected — rejecting them would make contextual
  equivalence syntax-sensitive.
* **Γ is not a field of `Lara.Unit`** (D2). It is an index of
  `Unit.CheckedUnit`, so `link` returns a `Lara.Unit × (LeafId → Option Atom)`
  pair, with Γ built by `Admission.buildGamma` from the two `gammaFrag`s.
* **Σ, the policy, `canon` and the registry are fixed across linking.** Σ and
  the policy are fragment fields so that an R-L3 fault can carry both
  disagreeing values; `canon` and the registry are parameters of the calculus,
  since a context is data and cannot re-invoke the checker under a different
  one.
* **An open fragment has no `CheckedProgram`** (D10). `Compile.CheckedProgram`
  requires closed support of every declared argument (`complete`), and a
  fragment mentioning an imported leaf has no `HasSupport` derivation until the
  import environment supplies it. Anything said about a fragment alone
  therefore goes through `fragmentAF`, which is relative to an `ImportEnv`.
* **Exports are conclusions, and the claim is rebuilt after linking** (D4).
  `Grounded.Claim` holds argument *positions*, and `statusC` is `gap` exactly
  on empty support, so pinning a claim at fragment-definition time would hide
  the gap-flip a context can cause by supplying support for an exported
  conclusion.
-/

import Lara.Check.Unit
import Lara.Invariants
import Lara.Admission

namespace Lara.Context

open Lara.Support Lara.Attack Lara.Compile

/-! ### Structural merge

`SupportTerm` equality is structural (`Lara/Support.lean:353`), and
`Compile.CheckedProgram.nodup` models `Args(P)` as a *set*. Linking therefore
merges structurally identical arguments instead of rejecting the link:
rejecting a cross-boundary term collision would make contextual equivalence
syntax-sensitive and refute every congruence coarser than term-set equality
(D3). Identical terms have identical edge sets (`Compile.lean:43-46`), so the
merge is semantically inert; `Lara.Context.Merge` proves that rather than
asserting it.

This is the third structural copy of this recursion in the development
(`Support.dedupQuestions`, `Complexity.Encoding.dedupNats`). -/

/-- Remove duplicates, keeping the last occurrence of each element. -/
def dedupList {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs =>
      let rest := dedupList xs
      if x ∈ rest then rest else x :: rest

/-! ### Interfaces, fragments, and contexts -/

/-- The leaf identifiers one side of a link requires the other side to declare.
Openness in M4 is **leaf-name openness only** (D12): a term-level hole — an
argument whose critical-question obligations the context discharges — is
unrepresentable, because `Compile.CheckedProgram.complete` forces an empty
obligation set on every declared argument and discharges live inside the term
rather than in a name environment. -/
structure Interface where
  /-- the imported leaf identifiers -/
  leaves : List LeafId

/-- The empty interface: a closed fragment, which imports nothing and can be
linked into any compatible context. -/
def Interface.closed : Interface := ⟨[]⟩

/-- A program fragment. `gammaFrag` are the evidence leaves this side declares,
`ground` its contribution to the finite ground-atom list `checkUnit`
sort-checks, `args`/`atts` its declared material, `imports` the leaf
identifiers the other side must declare, and `exports` the **conclusions**
whose status is observable. -/
structure Fragment where
  sigma     : Sigma.Sigma
  policy    : Policy.Policy
  /-- the evidence leaves this side declares -/
  gammaFrag : List (LeafId × Atom)
  /-- this side's contribution to the unit's finite ground-atom list. `Lara.Unit`
  fixes what belongs there: "the leaf conclusions of Γ, the backend theory
  table, and the queried claim atoms". A fragment's `ground` is therefore
  expected to carry the conclusions of its own `gammaFrag` and the atoms it
  exports; `link` concatenates the two sides' lists, and well-sortedness of the
  result enters `link_checked` as the `signatureStage` hypothesis rather than
  as a structural property of linking. -/
  ground    : List Atom
  args      : List SupportTerm
  atts      : List Attack
  /-- ids the other side must declare -/
  imports   : Interface
  /-- observable exported conclusions -/
  exports   : List Atom

/-- The leaf identifiers a fragment declares. -/
def Fragment.declared (F : Fragment) : List LeafId := F.gammaFrag.map (·.1)

/-- A context is the material surrounding the hole. It is fragment-shaped:
`frame.imports` are the identifiers the fragment plugged into the hole must
declare, and `frame.gammaFrag` supplies that fragment's imports. Contexts are
closed under `compose` wherever `composeOk` holds, which is what makes
congruence stateable (D11). -/
structure Context where
  /-- the material surrounding the hole. Its `exports` are bookkeeping for
  `compose`: the observation of a link reads the *fragment's* exports (D4),
  since what a context distinguishes is what the theorem quantifies over. -/
  frame : Fragment

/-- A finite import environment: the leaves an enclosing context declares,
used to compile a fragment on its own (`fragmentAF`, D10). -/
abbrev ImportEnv := List (LeafId × Atom)

/-! ### The conclusion cache

`link` runs *before* checking, so it cannot read conclusions off a
`Unit.CheckedUnit.nodes` cache: that cache exists only once the linked program
has been accepted. Conclusions are therefore inferred here with the checker's
own `Check.inferSupport`, whose `inferSupport_sound` / `inferSupport_complete`
pair makes the cache exactly the graph of `HasSupport … w C []` on the terms
that have one. -/

/-- The conclusion of a complete checked support term, inferred under an
environment. A term that fails to infer, or that retains an open obligation,
has none: `Compile.CheckedProgram.complete` forces an empty obligation set on
every declared argument of an accepted program, so the cache is total exactly
where acceptance is possible. -/
def conclusionOf {canon : String → String} (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom) (reg : BackendRegistry canon)
    (w : SupportTerm) : Option Atom :=
  match Check.inferSupport Pi Gamma reg .root w with
  | .ok result => if result.obligations = [] then some result.conclusion else none
  | .error _ => none

/-- Cached conclusions of the complete terms of a list, in declaration order. -/
def conclusionCache {canon : String → String} (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom) (reg : BackendRegistry canon)
    (args : List SupportTerm) : List (SupportTerm × Atom) :=
  args.filterMap fun w => (conclusionOf Pi Gamma reg w).map (fun C => (w, C))

/-! ### Saturation

`Compile.AttackComplete` quantifies over **all pairs** of declared arguments,
so the linked attack list must already cover every cross-boundary contrary
conflict onto an attackable target. `crossAtts` emits exactly one attack per
such pair, in the shape the target admits:

* a `.leaf` target is undermined at the root position (`Attack.HasAttack.undermine`
  reads `Gamma l`, which the linked Γ supplies);
* an `.inst` target is rebutted (`Attack.HasAttack.rebut` reads the root rule's
  instantiated conclusion, which `Support.InstSide.concl` supplies).

Both shapes put the attacked occurrence at the target itself, so
`Compile.Covered` holds by `Compile.contains_refl`. -/

/-- The attack shape a target admits: undermine a leaf at its root position,
rebut a rule instance. -/
def attackFor (source target : SupportTerm) : Attack :=
  match target with
  | .leaf _ => .undermine source target []
  | .inst _ _ _ _ _ _ => .rebut source target

/-- Every attack forced by a contrary conflict from a cached source onto a
cached, conflict-attackable target. -/
def crossAttsFrom (canon : String → String) (dp : DefeatPolicy)
    (Pi : RuleId → Option Rule)
    (sources targets : List (SupportTerm × Atom)) : List Attack :=
  sources.flatMap fun s =>
    targets.filterMap fun t =>
      if contraryMatchB canon dp s.2 t.2 && conflictAttackableB Pi t.1 then
        some (attackFor s.1 t.1)
      else none

/-- The cross-boundary saturation of a link: both directions, context onto
fragment and fragment onto context. Attacks *within* one side are the business
of that side's own declarations — `Lara.Context.Link` takes their coverage as a
hypothesis on each side and adds only what crosses the boundary.

The rule lookup and defeat policy are read off `F.policy` for both directions;
that is sound because the guard has already forced `C.frame.policy = F.policy`
(R-L3). The caches are built from the two sides' *declared* lists, before the
structural merge, which is harmless in both directions it can differ: a
duplicated attack is inert under `Compile.Covered` (an existential over the
list), and a term declared on both sides yields a pair whose endpoints become
one node after the merge — a self-pair `Compile.AttackComplete` already
quantifies over, and which is forced exactly when that term's conclusion
contrary-matches itself. -/
def crossAtts {canon : String → String} (reg : BackendRegistry canon)
    (Gamma : LeafId → Option Atom) (C : Context) (F : Fragment) : List Attack :=
  let Pi := F.policy.ruleLookup
  let dp := F.policy.defeat
  let cc := conclusionCache Pi Gamma reg C.frame.args
  let cf := conclusionCache Pi Gamma reg F.args
  crossAttsFrom canon dp Pi cc cf ++ crossAttsFrom canon dp Pi cf cc

/-! ### The link guard, and its rejection classes

A rejection is a *witnessed* rejection: the guard is the `isNone` of a fault
function returning a closed sum, the way `Check.Unit.signatureStage` returns a
`SignatureFault` and `Check.Unit.checkUnit` a `UnitError`. A caller that wants
the Boolean uses `linkOk`; a caller that wants to know *why* reads
`linkFault`. -/

/-- Which side of a binary link or composition owns a one-sided fault. For
`linkFault C F`, `left` is the context and `right` is the fragment. -/
inductive LinkSide where
  | left
  | right
deriving DecidableEq

/-- Why a link was rejected. Every constructor carries the data needed to
locate the fault: R-L1/R-L2 identify the side and leaf, while R-L3 retains both
disagreeing values in left-to-right order. The registry cannot appear: it is a
parameter of the calculus, not fragment data, so a context cannot redefine it
(see `docs/theory-m4-context-calculus-decision.md` §2). -/
inductive LinkFault where
  /-- R-L1: one side declares the same leaf identifier twice -/
  | duplicateOwnId : LinkSide → LeafId → LinkFault
  /-- R-L1: both sides declare the same leaf identifier -/
  | idClash : LeafId → LinkFault
  /-- R-L2: one side imports an identifier that the other side does not declare -/
  | unsatisfiedImport : LinkSide → LeafId → LinkFault
  /-- R-L3: the two sides disagree on Σ -/
  | sigmaMismatch : Sigma.Sigma → Sigma.Sigma → LinkFault
  /-- R-L3: the two sides disagree on the policy -/
  | policyMismatch : Policy.Policy → Policy.Policy → LinkFault
deriving DecidableEq

/-- The first identifier declared twice, in declaration order. -/
def firstDup? : List LeafId → Option LeafId
  | [] => none
  | l :: ls => if l ∈ ls then some l else firstDup? ls

/-- The first element of `needed` that `declared` does not contain. -/
def firstMissing? (needed declared : List LeafId) : Option LeafId :=
  needed.find? (fun l => !declared.contains l)

/-- The first element of `xs` that also occurs in `ys`. -/
def firstShared? (xs ys : List LeafId) : Option LeafId :=
  xs.find? (fun l => ys.contains l)

/-- Σ and policy agreement, shared by the link and composition guards. A
context "may add fresh evidence, attacks, and rule instances but may not
redefine the fixed policy"); this is where that is enforced. -/
def sigmaPolicyFault (F G : Fragment) : Option LinkFault :=
  if F.sigma ≠ G.sigma then some (.sigmaMismatch F.sigma G.sigma)
  else if F.policy ≠ G.policy then some (.policyMismatch F.policy G.policy)
  else none

/-- The identifier-hygiene faults of two sides: each side's own declarations
are duplicate-free, and the two sides declare disjoint identifiers. Hygiene is
on *declarations* — an imported identifier is declared by exactly one side. -/
def idHygieneFault (F G : Fragment) : Option LinkFault :=
  match firstDup? F.declared with
  | some l => some (.duplicateOwnId .left l)
  | none =>
      match firstDup? G.declared with
      | some l => some (.duplicateOwnId .right l)
      | none =>
          match firstShared? F.declared G.declared with
          | some l => some (.idClash l)
          | none => none

/-- **The link guard, with a located fault.** For one-sided faults, `left`
means the context and `right` means the fragment. -/
def linkFault (C : Context) (F : Fragment) : Option LinkFault :=
  match idHygieneFault C.frame F with
  | some fault => some fault
  | none =>
      match firstMissing? F.imports.leaves C.frame.declared with
      | some l => some (.unsatisfiedImport .right l)
      | none =>
          match firstMissing? C.frame.imports.leaves F.declared with
          | some l => some (.unsatisfiedImport .left l)
          | none => sigmaPolicyFault C.frame F

/-- The decidable link guard. `Lara.Context.Link` gives each fault constructor
its own characterization lemma, so proofs and witnesses discharge by lemma
rather than by `decide` over a pair scan (`native_decide` is banned). -/
def linkOk (C : Context) (F : Fragment) : Bool := (linkFault C F).isNone

/-! ### Linking -/

/-- The linked Γ: the two declared leaf lists, read by `Admission.buildGamma`.
Γ is *not* fixed across linking — it is exactly what the two sides
contribute — and `Support.hasSupport_mono_gamma` carries derivations into
it. Identifier hygiene is what makes the concatenation order irrelevant:
`buildGamma` is first-wins, and the guard has already ruled out a leaf declared
by both sides. -/
def linkGamma (C : Context) (F : Fragment) : LeafId → Option Atom :=
  Admission.buildGamma (C.frame.gammaFrag ++ F.gammaFrag)

/-- The linked ground-atom list: the two sides' contributions (see
`Fragment.ground`). -/
def linkGround (C : Context) (F : Fragment) : List Atom :=
  C.frame.ground ++ F.ground

/-- The raw unit a link builds: the two sides' material, merged structurally
and saturated. Named separately from `link` so that every downstream statement
can name it without unfolding the guard. -/
def linkedUnit {canon : String → String} (reg : BackendRegistry canon)
    (C : Context) (F : Fragment) : Lara.Unit :=
  { sigma  := F.sigma
  , policy := F.policy
  , args   := dedupList (C.frame.args ++ F.args)
  , atts   := C.frame.atts ++ F.atts ++ crossAtts reg (linkGamma C F) C F }

/-- **Linking.** Defined only where the guard holds; it merges the argument
lists structurally, concatenates the declared attacks, and saturates the
cross-boundary conflicts. Returns the raw unit together with the Γ it is
checked against, since `Lara.Unit` carries no Γ field. -/
def link {canon : String → String} (reg : BackendRegistry canon)
    (C : Context) (F : Fragment) :
    Option (Lara.Unit × (LeafId → Option Atom)) :=
  if linkOk C F then some (linkedUnit reg C F, linkGamma C F) else none

/-! ### Composition of contexts (D11) -/

/-- The identifiers still owed by a composition: what one side imports and the
other does not declare, duplicate-free so that a composite's interface does not
depend on how often an identifier was owed. -/
def residualImports (C D : Context) : Interface :=
  ⟨dedupList
    ((C.frame.imports.leaves.filter (fun l => !D.frame.declared.contains l)) ++
      (D.frame.imports.leaves.filter (fun l => !C.frame.declared.contains l)))⟩

/-- The guard for composing two contexts: the same hygiene and agreement
classes as `linkFault`, minus R-L2 — a composition may still owe imports, which
is exactly what `residualImports` records. -/
def composeFault (C D : Context) : Option LinkFault :=
  match idHygieneFault C.frame D.frame with
  | some fault => some fault
  | none => sigmaPolicyFault C.frame D.frame

/-- The decidable composition guard. -/
def composeOk (C D : Context) : Bool := (composeFault C D).isNone

/-- The material of a composite: the two frames merged the way `link` merges
them, owing the residual imports. -/
def composedContext (C D : Context) : Context :=
  ⟨{ sigma     := C.frame.sigma
   , policy    := C.frame.policy
   , gammaFrag := C.frame.gammaFrag ++ D.frame.gammaFrag
   , ground    := C.frame.ground ++ D.frame.ground
   , args      := dedupList (C.frame.args ++ D.frame.args)
   , atts      := C.frame.atts ++ D.frame.atts
   , imports   := residualImports C D
   , exports   := C.frame.exports ++ D.frame.exports }⟩

/-- **Composing contexts.** The material merges the way `link` merges it —
structural dedupe of the arguments, concatenation of the attacks — and the
hole of the composite owes exactly the residual imports. Saturation is *not*
performed here: a composite is still a context, and cross-boundary attacks are
emitted once, by `link`, against the fragment that finally fills the hole. -/
def compose (C D : Context) : Option Context :=
  if composeOk C D then some (composedContext C D) else none

/-! ### The fragment-relative carrier (D10) -/

/-- The unit a fragment presents on its own, under an import environment. -/
def fragmentUnit (F : Fragment) : Lara.Unit :=
  { sigma := F.sigma, policy := F.policy, args := F.args, atts := F.atts }

/-- Γ for a fragment checked under an import environment. `Admission.buildGamma`
is first-wins, so a fragment's own declaration shadows a colliding environment
entry; `fragmentAF` rules that collision out with the same hygiene fault the
link guard uses, so the shadowing is never reached on an accepted fragment. -/
def fragmentGamma (F : Fragment) (env : ImportEnv) : LeafId → Option Atom :=
  Admission.buildGamma (F.gammaFrag ++ env)

/-- The finite ground atoms of a fragment checked under an import environment:
its own contribution together with the leaf conclusions the environment
declares. -/
def fragmentGround (F : Fragment) (env : ImportEnv) : List Atom :=
  F.ground ++ env.map (·.2)

/-- The hygiene fault of a fragment against an import environment: the same
R-L1 classes, with the environment read as the declaring side. -/
def fragmentEnvFault (F : Fragment) (env : ImportEnv) : Option LinkFault :=
  idHygieneFault F { F with gammaFrag := env, imports := Interface.closed }

/-- **The fragment-relative carrier.** An open fragment has no
`Compile.CheckedProgram` of its own (D10), so "the fragment's framework" is
always relative to an import environment: check the fragment's own unit under
`fragmentGamma` and `fragmentGround`, and read the M1 carrier off the accepted
unit's node cache. `none` records a hygiene clash with the environment, or that
the fragment does not stand on its own under it. -/
def fragmentCarrier {canon : String → String} (reg : BackendRegistry canon)
    (F : Fragment) (env : ImportEnv) : Option Invariants.StructuredAF :=
  match fragmentEnvFault F env with
  | some _ => none
  | none =>
      match Check.Unit.checkUnit (fragmentGamma F env) reg (fragmentGround F env)
          (fragmentUnit F) with
      | .ok accepted => some (Invariants.compileUnit accepted)
      | .error _ => none

/-- **The fragment-relative compiled AF** (D10's signature): the carrier with
its conclusion labelling forgotten. Positions are the node identity on both
sides, so this is exactly `Compile.checkedAF` of the fragment's own accepted
program — `Lara.Context.Link.fragmentAF_eq` states that. -/
def fragmentAF {canon : String → String} (reg : BackendRegistry canon)
    (F : Fragment) (env : ImportEnv) : Option Grounded.AF :=
  (fragmentCarrier reg F env).map Invariants.eraseAF

/-! ### Observation (D4) -/

/-- **The externally visible result of placing a fragment in a context**, with
the observed payload left open. Incompatibility and whole-unit rejection are
distinct outcomes rather than two spellings of a missing status list: collapsing
either into "no observations" would make a fragment that cannot be linked
indistinguishable from one that links and exports nothing.

The payload is a parameter because the D4 four-state reading is one reading of
the carrier among many. `obs` fixes it at `Grounded.Status`; `Lara.Context.obsSem`
fixes it at `Lara.Semantics.ClaimObservation`. Both are `Lara.Context.obsGen` at
a projection, and `Lara.Context.obs_eq_obsGen` says so by `rfl`. -/
inductive ObservationOf (α : Type) where
  /-- the link guard fired: the interfaces are incompatible -/
  | incompatible : LinkFault → ObservationOf α
  /-- the link is compatible but the merged unit failed the whole-unit checker -/
  | rejected : Check.Unit.UnitError → ObservationOf α
  /-- the accepted link's exported conclusions, under the caller's projection -/
  | observed : List α → ObservationOf α
deriving DecidableEq

/-- **The frozen D4 observation**: the generic one at the grounded four-state
status.

Kept as an abbreviation rather than a distinct type so that `obs` needs no
change and `Lara.Context.obs_eq_obsGen` holds by `rfl` — the D4 shape is not
being renegotiated here, only exhibited as one reading of a carrier that was
already semantics-free. -/
abbrev Observation := ObservationOf Grounded.Status

/-- The status of every exported conclusion of a linked program, read off the
**linked** unit's checked-node cache through the M1 carrier. Guard faults retain
their `LinkFault`; a compatible link that fails the whole-unit checker retains
its `UnitError`. -/
def obs {canon : String → String} (reg : BackendRegistry canon)
    (C : Context) (F : Fragment) : Observation :=
  match linkFault C F with
  | some fault => .incompatible fault
  | none =>
      match Check.Unit.checkUnit (linkGamma C F) reg (linkGround C F)
          (linkedUnit reg C F) with
      | .ok accepted =>
          .observed (F.exports.map
            (fun p => Invariants.status canon (Invariants.compileUnit accepted) p))
      | .error error => .rejected error

end Lara.Context
