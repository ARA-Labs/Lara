/-
# A `native_decide`-free surface transport fixture (#227)

`Lara.Context.surface_directAF_relabel` (`Lara/Context/Surface.lean:60`) relates
two accepted surface programs whose elaborated units differ by an injective
certificate relabel. Every accepted surface fixture in `Lara/Examples/Surface.lean`
is proved by `native_decide`, which would import `Lean.ofReduceBool` into the
axiom audit, so none of them can instantiate it. This module builds the
certificate-transport foundation for a fixture that stays inside the standard
trio.

## Why the obvious route fails, and what replaces it

`Lara.NDNamed.lowerFormula` (`Lara/NDNamed.lean:179`) and `lowerNamedExpr`
(`:195`) are `termination_by sizeOf`, so Lean compiles them to
`WellFounded.Nat.fix` and marks them `@[irreducible]`. Nothing reduces them —
not `rfl`, not `decide`, not even on an `.atom` leaf. They are reached through
certificate-payload lowering (`lowerAssuranceCertificate`,
`Lara/Surface/Check.lean:191`), which is why `reconstructArgs` does not reduce
and why every *named*-payload fixture needs `native_decide`.

The escape is that `lowerNamed` scans for a named marker first and returns the
payload unchanged when there is none. A payload authored in **kernel form** —
numeric hypothesis indices and `(atom KEY)` rather than `(prop TEXT)` — never
reaches the well-founded pass at all. `NDNamed.lowerNamed_id_of_kernel`
(`NDNamed.lean:323`) states exactly this, and its `hNat` hypothesis is literally
the `Env.startsIdent_nat_false` field, so it costs nothing to apply.

Note that the reconstruction pass is *not* the obstacle: `reconstructExplicitTerm`
and its mutual partners compile to `brecOn`, and the kernel unfolds them.

## What this module fixes

The two payloads below are the two sides of `Examples.Linking.certSwap`, whose
injectivity (`certSwap_injective`) and acceptance-preservation
(`certSwap_preserving`) are already proved there and already inside the trio.
Program 1 carries the kernel payload `(hyp 1)`; program 2 carries its
`wrapCert` image. Lowering each is the one obligation on the opaque path, and
`transport_lower_kernel` / `transport_lower_wrapped` discharge both.

The lowered payload of program 1 is definitionally `Lara.Examples.slot1Cert`, so
`Lara.Examples.registry_exact_digest_accepts` applies to this fixture's
certificate without restating it.
-/

import Lara.Surface.Check
import Lara.Surface.Observation
import Lara.Context.Surface
import Lara.Examples.Linking

namespace Lara.Examples.SurfaceTransport

open Lara.Surface Lara.Presentation Lara.Examples.Linking

/-! ### The two environments

Both are `canon = id` and replay-neutral on the elaboration path
(`encodeProp = fun _ => none`), the shape `Examples.Surface.multiNamespaceTransportEnv`
uses. They differ only in the registry, which is where the backend swap lives:
`registryEx` registers the `nd` core directly, `registryWrapped` reads it
through the unwrapping wrapper. -/

def transportEnv : Lara.Surface.Env (fun source => source) where
  registry := registryEx
  startsIdent := fun _ => false
  startsIdent_nat_false := by intro; rfl
  encodeProp := fun _ => none

def transportEnvWrapped : Lara.Surface.Env (fun source => source) where
  registry := registryWrapped
  startsIdent := fun _ => false
  startsIdent_nat_false := by intro; rfl
  encodeProp := fun _ => none

/-! ### The two certificate payloads

`kernelPayload` is `NDNamed.encodeCert (.hyp 1)` spelled in presentation `Sx`;
`wrappedPayload` is its `certSwap` image. Neither carries a named marker, so
neither reaches `lowerNamedExpr`. -/

/-- Kernel-form `nd@1` payload: `(hyp 1)`. Marker-free by construction.

Slot 1 is the first *theory* entry: `ndRegistered.resolveTheory digestA` is
`slotTheory id [pB]`, and the source premise occupies slot 0, so `(hyp 1)`
names the theory's `q` and the certificate concludes `q` from `p`. -/
def kernelPayload : Sx := .node "hyp" (.cons (.str "1") .nil)

/-- The relabeled payload: `certSwap` wraps an `nd` certificate's payload. -/
def wrappedPayload : Sx :=
  .node "wrapped" (.cons (.node "hyp" (.cons (.str "1") .nil)) .nil)

/-- The surface spelling of `Examples.digestA`. It must be this exact string:
`toSupportTheoryDigest` is the identity on the payload, and the registry
resolves a theory only for `digestA`. -/
def theoryDigestA : TheoryDigest := ⟨"sha256:theory-a"⟩

theorem theoryDigestA_lowers : toSupportTheoryDigest theoryDigestA = Lara.Examples.digestA :=
  rfl

/-- The two certificates as `Cert` records. `ChecksAssurance.cert` matches on
the `.cert` constructor, so the derivations below need the payload record, not
just the wrapped `Assurance`. -/
def kernelCert : Cert := ⟨⟨"nd"⟩, 1, theoryDigestA, kernelPayload⟩
def wrappedCert : Cert := ⟨⟨"nd"⟩, 1, theoryDigestA, wrappedPayload⟩

def kernelCertificate : Assurance := .cert kernelCert
def wrappedCertificate : Assurance := .cert wrappedCert

/-- The lowered core payload of program 1, definitionally `Examples.slot1Cert`. -/
def kernelRef : Lara.Support.CertRef := ⟨.list [.atom "hyp", .atom "1"]⟩

theorem kernelRef_eq_slot1 : kernelRef = Lara.Examples.slot1Cert := rfl

/-- The relabel on this fixture's assurance is exactly `certSwap`, so
`certSwap_injective` and `certSwap_preserving` apply verbatim. -/
theorem transport_certSwap_image :
    certSwap (.cert Lara.Examples.ndId Lara.Examples.digestA kernelRef)
      = .cert Lara.Examples.ndId Lara.Examples.digestA (wrapCert kernelRef) := rfl

/-! ### The lowering obligations

These are the only obligations a `Checks` derivation carries on the
kernel-opaque path — `ChecksAssurance.cert`'s
`hlower : lowerAssuranceCertificate … = some core`. Everything else in `Checks`
is a relational inductive or a small decidable equation. -/

/-- The kernel payload is exactly the `encodeCert` image of `hyp 1`, which is
what licenses `lowerNamed_id_of_kernel`. -/
theorem sxToSExpr_kernelPayload :
    sxToSExpr kernelPayload = Lara.NDNamed.encodeCert (.hyp 1) := rfl

/-- **Program 1's certificate lowers**, through the marker-free branch, without
evaluating the well-founded named pass. -/
theorem transport_lower_kernel (program : Program) (rule : Rule)
    (priors : List PriorArgument) (premises : List SupportTerm) :
    lowerAssuranceCertificate transportEnv program rule priors premises
        kernelCertificate
      = some (.cert Lara.Examples.ndId Lara.Examples.digestA kernelRef) := by
  simp only [lowerAssuranceCertificate, kernelCertificate, kernelCert,
    sxToSExpr_kernelPayload]
  rw [Lara.NDNamed.lowerNamed_id_of_kernel _ _ _ _
    transportEnv.startsIdent_nat_false]
  rfl

/-- The relabeled payload carries no named marker either, so the same
short-circuit applies to it. -/
theorem firstNamedMarker_wrappedPayload :
    Lara.NDNamed.firstNamedMarker transportEnvWrapped.startsIdent
        (sxToSExpr wrappedPayload)
      = none := rfl

/-- **Program 2's certificate lowers to `certSwap`'s image.** This is what makes
the pair a genuine relabel rather than the same program cited twice. -/
theorem transport_lower_wrapped (program : Program) (rule : Rule)
    (priors : List PriorArgument) (premises : List SupportTerm) :
    lowerAssuranceCertificate transportEnvWrapped program rule priors premises
        wrappedCertificate
      = some (.cert Lara.Examples.ndId Lara.Examples.digestA (wrapCert kernelRef)) := by
  simp only [lowerAssuranceCertificate, wrappedCertificate, wrappedCert,
    Lara.NDNamed.lowerNamed]
  rfl

/-! ### Registry acceptance

Because the lowered payload is `slot1Cert` and the lowered theory digest is
`digestA`, the fixture inherits acceptance from `Examples` rather than
restating an ND replay. This is the step that would otherwise force a
`native_decide`: `certOkOf` on the `nd` core does not reduce in the kernel
(`Classical.propDecidable` blocks it), so it must come from a proved lemma. -/

/-- **Program 1's certificate is accepted by `registryEx`.** -/
theorem transport_cert_accepted :
    Lara.Support.certOkOf registryEx Lara.Examples.ndId Lara.Examples.digestA
      kernelRef [Lara.Examples.pA] Lara.Examples.pB :=
  (Lara.Support.certOkBOf_iff registryEx Lara.Examples.ndId Lara.Examples.digestA
      kernelRef [Lara.Examples.pA] Lara.Examples.pB).mp
    Lara.Examples.registry_exact_digest_accepts

/-- **Program 2's relabeled certificate is accepted by `registryWrapped`**, by
`certSwap_preserving` — the acceptance-preservation proof already in
`Examples.Linking`, applied to this fixture's assurance. -/
theorem transport_cert_accepted_wrapped
    (rule : Lara.Support.Rule) (As : List Lara.Atom) (A : Lara.Atom)
    (h : Lara.Support.AssuranceOk (Lara.Support.certOkOf registryEx) rule As A
      (.cert Lara.Examples.ndId Lara.Examples.digestA kernelRef)) :
    Lara.Support.AssuranceOk (Lara.Support.certOkOf registryWrapped) rule As A
      (.cert Lara.Examples.ndId Lara.Examples.digestA (wrapCert kernelRef)) := by
  have := certSwap_preserving rule As A _ h
  simpa only [transport_certSwap_image] using this

/-! ### The surface program and policy

The smallest program that can carry a genuine relabel: one observed leaf
asserting `p`, and one inferred argument citing it under a strict, parameterless,
question-free rule `p ⊢ q` whose only certifier is `nd@1` at `digestA`. The
policy's theory is `[q]`, matching `ndRegistered.resolveTheory digestA`, so the
certificate's slot 1 names `q`.

Everything the surface grammar lets us omit is omitted: no contraries, no
exceptions, no attacks, no claims, no statuses, no groups, no comparisons, no
value bindings, no measurands. Each of those would add `Checks` obligations
without making the relabel any more genuine. -/

def transportPolicyId : PolicyId := ⟨"transport-policy"⟩
def transportRuleId : RuleId := ⟨"r-cert"⟩
def leafPId : LeafId := ⟨"l-p"⟩
def argCertId : ArgId := ⟨"a-cert"⟩

/-- `p` and `q`, both nullary — the surface spellings of `Examples.pA` / `pB`. -/
def transportSigma : Lara.Sigma.Sigma :=
  { sorts := [], cons := [], preds := [⟨⟨"p"⟩, []⟩, ⟨⟨"q"⟩, []⟩] }

/-- Strict, parameterless, question-free: `p ⊢ q`, certified by `nd@1`. Keeping
it parameterless is what makes `ParamsCovered` and the premise match trivial. -/
def transportRule : Rule :=
  { id := transportRuleId
    params := []
    mode := .strict
    premises := [⟨"p", .nil⟩]
    premiseLabels := []
    conclusion := ⟨"q", .nil⟩
    allowTrusted := false
    certifiers := [⟨⟨"nd"⟩, 1, theoryDigestA⟩]
    questions := [] }

def transportPolicy : Policy :=
  { id := transportPolicyId
    sigma := transportSigma
    rules := [transportRule]
    contraries := []
    exceptions := []
    admission := [((.observed, .user), .admit)]
    theories := [(theoryDigestA, [.atom "q" .nil])]
    groupMode := .quarantineOnConflict
    measurands := []
    comparisonSchemes := [] }

def leafP : Leaf := ⟨leafPId, .atom "p" .nil, .observed, .user, []⟩

/-- The one argument, parameterised by its assurance so the two programs differ
in exactly the certificate and nothing else. -/
def transportArg (assurance : Assurance) : Arg :=
  ⟨argCertId, .supportsDerived ⟨"c-q"⟩,
    .inferTheta transportRuleId [⟨"l-p"⟩] [] [] assurance⟩

def transportProgram (assurance : Assurance) : Program :=
  { artifact := "surface-transport"
    digest := ⟨"sha256:transport"⟩
    policy := transportPolicyId
    backends := [(⟨"nd"⟩, "1")]
    valueBindings := []
    decls := [.leaf leafP, .arg (transportArg assurance)] }

/-- Program 1: the kernel certificate. -/
def transportInput : Lara.Surface.Input :=
  ⟨transportProgram kernelCertificate, transportPolicy⟩

/-- Program 2: the same program with the relabeled certificate. -/
def transportInputWrapped : Lara.Surface.Input :=
  ⟨transportProgram wrappedCertificate, transportPolicy⟩

/-! ### The cheap `Checks` fields

These are the fields with Bool deciders. That they close by `decide` is the
concrete form of the observation that the surface *predicates* reduce fine —
it is only certificate lowering that does not. -/

theorem transport_supported : Lara.Surface.Supported transportInput := by
  apply (Lara.Surface.supportedB_iff transportInput).mp
  decide

theorem transport_supported_wrapped :
    Lara.Surface.Supported transportInputWrapped := by
  apply (Lara.Surface.supportedB_iff transportInputWrapped).mp
  decide

theorem transport_freshness :
    Lara.Surface.GeneratedIdsFresh transportInput.program = true := by decide

theorem transport_freshness_wrapped :
    Lara.Surface.GeneratedIdsFresh transportInputWrapped.program = true := by decide

/-! ### The argument derivation

`ChecksArgument.inferred` is the constructor that avoids
`ReconstructsExplicitTerm` altogether. Every premise below is either a
relational inductive or a small equation the kernel reduces; the single
exception is `ChecksAssurance.cert`'s `hlower`, which is supplied by the
caller from `transport_lower_kernel` / `transport_lower_wrapped`. -/

/-- The leaf reference `l-p` resolves on the leaf side of the shared namespace,
with no prior argument competing for the name. -/
def transportResolved : ResolvedReference :=
  ⟨.leaf leafPId, .atom "p" .nil, some leafPId, none⟩

/-- The reconstructed presentation term for the one argument. -/
def transportBuilt (certificate : Cert) : PriorArgument :=
  ⟨argCertId,
    .rule transportRuleId [] (supportTermsFromList [transportResolved.term])
      (dischargesFromList []) [] (.cert certificate),
    .atom "q" .nil⟩

/-- Its lowered core term. Same shape as `Examples.Linking.certArg`. -/
def transportCore (coreAssur : Lara.Support.Assurance) : Lara.Support.SupportTerm :=
  .inst ⟨"r-cert"⟩ [] [.leaf ⟨"l-p"⟩] [] [] coreAssur

/-- **One argument, derived end to end**, without evaluating `reconstructArgs`.
The `hlower` hypothesis is the only thing the caller must supply, and it is the
only obligation on the kernel-opaque path. -/
theorem transport_checksArgument
    {env : Lara.Surface.Env (fun source => source)}
    (certificate : Cert) (coreAssur : Lara.Support.Assurance)
    (hlower : lowerAssuranceCertificate env (transportProgram (.cert certificate))
        transportRule [] [transportResolved.term] (.cert certificate)
      = some coreAssur) :
    ChecksArgument env (transportProgram (.cert certificate)) transportPolicy []
      (transportArg (.cert certificate)) (transportBuilt certificate)
      (transportCore coreAssur) := by
  refine ChecksArgument.inferred
    (rule := transportRule) (resolved := [transportResolved]) (theta := [])
    (conclusion := .atom "q" .nil)
    (.here rfl) rfl ?_ ?_ ?_ ?_ rfl .supportsDerived ?_
  · exact .cons (.leaf rfl rfl) .nil
  · exact .cons rfl .nil
  · intro param hparam; simp [transportRule] at hparam
  · exact .nil
  · exact .rule (.here rfl) (.cons .leaf .nil) .nil (.cert hlower)

/-! ### The declaration fold

`ChecksProgram` threads priors left to right. The leaf declaration contributes
nothing and the argument contributes one pair, so the fold is two constructors
deep. Nothing here evaluates `reconstructArgs`; it is the relational twin. -/

/-- The lowered assurance of program 1. -/
def kernelCoreAssur : Lara.Support.Assurance :=
  .cert Lara.Examples.ndId Lara.Examples.digestA kernelRef

/-- The lowered assurance of program 2 — `certSwap` of the first. -/
def wrappedCoreAssur : Lara.Support.Assurance :=
  .cert Lara.Examples.ndId Lara.Examples.digestA (wrapCert kernelRef)

def transportPairs (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    List ReconstructedArgument :=
  [⟨transportArg (.cert certificate), transportBuilt certificate,
    transportCore coreAssur⟩]

theorem transport_checksProgram_kernel :
    ChecksProgram transportEnv (transportProgram kernelCertificate) transportPolicy
      (transportProgram kernelCertificate).decls []
      (transportPairs kernelCert kernelCoreAssur) :=
  .cons .leaf
    (.cons (.arg (transport_checksArgument kernelCert kernelCoreAssur
        (transport_lower_kernel _ _ _ _)))
      .nil)

theorem transport_checksProgram_wrapped :
    ChecksProgram transportEnvWrapped (transportProgram wrappedCertificate)
      transportPolicy (transportProgram wrappedCertificate).decls []
      (transportPairs wrappedCert wrappedCoreAssur) :=
  .cons .leaf
    (.cons (.arg (transport_checksArgument wrappedCert wrappedCoreAssur
        (transport_lower_wrapped _ _ _ _)))
      .nil)

/-! ### The elaborated carrier

Every field is *defined* as the expression the corresponding `Checks` field
compares against, so those comparisons close by `rfl`. This is the
`manualAllFormsElaborated` trick from `Examples/Surface.lean:2408`; it is what
keeps `gamma`, `ground`, `sigma`, `unitPolicy`, `unitAttacks` and
`authoredObligations` free. -/

def transportKept (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    List ReconstructedArgument :=
  keptReconstructed (fun source => source) transportPolicy
    (transportProgram (.cert certificate)) (transportPairs certificate coreAssur)

def transportElaborated (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    Lara.Surface.Elaborated (fun source => source) where
  gamma := surfaceGamma (fun source => source) transportPolicy
    (transportProgram (.cert certificate))
  ground := surfaceGround (fun source => source) transportPolicy
    (transportProgram (.cert certificate))
  unit :=
    { sigma := transportPolicy.sigma
      policy := toCorePolicy transportPolicy
      args := (transportKept certificate coreAssur).map (·.core)
      atts := [] }
  claims := claimsOf (transportKept certificate coreAssur)
    (transportProgram (.cert certificate))
  argIds := (transportKept certificate coreAssur).map (·.argument.id)
  authoredObligations := authoredObligationsOf (transportProgram (.cert certificate))
  openQuestions := openQuestionsOf (transportKept certificate coreAssur)
  resolvedAttacks := []
  semanticProgram := transportProgram (.cert certificate)

/-! ### The expansion field

No value bindings and no comparison blocks, so both expansion stages are the
identity and the intermediate program is the source program. The two `_sound`
bridges turn the executable runs into the relational form `Checks` wants. -/

theorem transport_expansions (certificate : Cert) :
    ∃ mid target generated,
      ExpandsValues (transportProgram (.cert certificate)) mid ∧
        GeneratedIdsFresh mid = true ∧
        (comparisonKeys mid).Nodup ∧
        ExpandsComparisons transportPolicy mid target generated ∧
        target = transportProgram (.cert certificate) :=
  ⟨transportProgram (.cert certificate), transportProgram (.cert certificate), [],
    expandValues_sound transportPolicy rfl,
    rfl,
    by simp [comparisonKeys, comparisonDecls, transportProgram],
    expandComparisons_sound transportPolicy rfl,
    rfl⟩

/-! ### Core support

The elaborated argument has the same shape as `Examples.Linking.certArg` — a
strict, parameterless, question-free rule occurrence over one leaf premise,
carrying a certificate — so its `HasSupport` derivation follows
`certArg_checked` field for field. Every `InstSide` obligation is a side
condition the kernel discharges; only `assur` needs the registry, and that
comes from `transport_cert_accepted`. -/

theorem transport_gamma_leafP (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    (transportElaborated certificate coreAssur).gamma ⟨"l-p"⟩
      = some (.atom "p" .nil) := rfl

theorem transport_ruleLookup (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    (transportElaborated certificate coreAssur).unit.policy.ruleLookup ⟨"r-cert"⟩
      = some (toCoreRule transportRule) := rfl

/-- **The certified argument is supported.** Parameterised over the registry
and the acceptance fact, so both programs use it. -/
theorem transport_hasSupport
    {reg : Lara.Support.BackendRegistry (fun source => source)}
    (certificate : Cert) (coreAssur : Lara.Support.Assurance)
    {β : Lara.Support.BackendId} {digest : Lara.Support.Digest}
    {κ : Lara.Support.CertRef}
    (hassur : coreAssur = .cert β digest κ)
    (hallow : (β, digest) ∈ (toCoreRule transportRule).certifiers)
    (hacc : Lara.Support.certOkOf reg β digest κ [.atom "p" .nil] (.atom "q" .nil)) :
    Lara.Support.HasSupport (fun source => source)
      (transportElaborated certificate coreAssur).unit.policy.ruleLookup
      (transportElaborated certificate coreAssur).gamma
      (Lara.Support.certOkOf reg) (transportCore coreAssur)
      (.atom "q" .nil) [] := by
  subst hassur
  refine Lara.Support.HasSupport.inst
    (As := [.atom "p" .nil]) (Cs := [.atom "p" .nil]) (Os := [[]])
    (DCs := []) (DOs := [])
    { rule := transport_ruleLookup certificate _
      θNodup := by decide
      θDom := by intro x; simp [transportRule, toCoreRule]
      prems := by decide
      concl := by decide
      lenAs := rfl
      lenCs := rfl
      lenOs := rfl
      premEq := by
        intro i A B hA hB
        cases i with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hA hB
            subst hA; subst hB; rfl
        | succ n => simp at hA
      lenDCs := rfl
      lenDOs := rfl
      ans := by intro j q w A hj; simp at hj
      qNodup := by decide
      dNodup := by decide
      hNodup := by decide
      cover := by intro qd hqd; simp [transportRule, toCoreRule] at hqd
      disj := by intro n hn; simp at hn
      keysD := by intro n hn; simp at hn
      keysH := by intro n hn; simp at hn
      strictNoQ := fun _ => ⟨rfl, rfl⟩
      assur := .cert rfl hallow hacc } ?_ ?_
  · intro i w A O hw hA hO
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hA hO
        subst hw; subst hA; subst hO
        exact .leaf (transport_gamma_leafP certificate _)
    | succ n => simp at hw
  · intro j q w A O hj; simp at hj

/-! ### The core obligations

Hand-built, because the executable route is unavailable: `certOkOf` on the `nd`
core does not reduce in the kernel, so `checkUnit` cannot be `decide`d on a
certificate-bearing unit and `CoreObligations.of_checkUnit_ok` is not usable
here. The attack-side fields are vacuous — the fixture declares no attacks and
the policy declares no contraries, so nothing can conflict. -/

/-- The relabeled certificate is accepted by `registryWrapped`, in the raw
`certOkOf` form the support derivation needs. Obtained from
`certSwap_preserving` rather than by replaying the wrapped backend. -/
theorem transport_cert_accepted_wrapped_raw :
    Lara.Support.certOkOf registryWrapped Lara.Examples.ndId Lara.Examples.digestA
      (wrapCert kernelRef) [.atom "p" .nil] (.atom "q" .nil) := by
  have h : Lara.Support.AssuranceOk (Lara.Support.certOkOf registryEx)
      (toCoreRule transportRule) [.atom "p" .nil] (.atom "q" .nil)
      (.cert Lara.Examples.ndId Lara.Examples.digestA kernelRef) :=
    .cert rfl (by decide) transport_cert_accepted
  have h2 := certSwap_preserving _ _ _ _ h
  rw [transport_certSwap_image] at h2
  cases h2 with
  | cert _ _ hacc => exact hacc

theorem transport_args_kernel :
    (transportElaborated kernelCert kernelCoreAssur).unit.args
      = [transportCore kernelCoreAssur] := rfl

theorem transport_args_wrapped :
    (transportElaborated wrappedCert wrappedCoreAssur).unit.args
      = [transportCore wrappedCoreAssur] := rfl

theorem transport_coreObligations_kernel :
    CoreObligations transportEnv (transportElaborated kernelCert kernelCoreAssur) where
  sigmaWellFormed := by decide
  policyWellSorted := by decide
  groundWellSorted := by decide
  argsWellSorted := by decide
  scopesWellFormed := by decide
  ruleIdsNodup := by decide
  policyWellFormed := by
    intro p _ ab hab
    simp [transportElaborated, toCorePolicy, transportPolicy] at hab
  argsNodup := by decide
  supports := by
    intro term hterm
    rw [transport_args_kernel] at hterm
    simp only [List.mem_singleton] at hterm
    subst hterm
    exact ⟨.atom "q" .nil,
      transport_hasSupport kernelCert kernelCoreAssur rfl (by decide)
        transport_cert_accepted⟩
  attacksTyped := by intro attack hattack; simp [transportElaborated] at hattack
  sourcesDeclared := by intro attack hattack; simp [transportElaborated] at hattack
  targetsDeclared := by intro attack hattack; simp [transportElaborated] at hattack
  attackComplete := by
    intro source _ target _ sourceConclusion targetConclusion _ _ hmatch
    obtain ⟨ab, hab, _⟩ := hmatch
    simp [transportElaborated, toCorePolicy, transportPolicy] at hab

theorem transport_coreObligations_wrapped :
    CoreObligations transportEnvWrapped
      (transportElaborated wrappedCert wrappedCoreAssur) where
  sigmaWellFormed := by decide
  policyWellSorted := by decide
  groundWellSorted := by decide
  argsWellSorted := by decide
  scopesWellFormed := by decide
  ruleIdsNodup := by decide
  policyWellFormed := by
    intro p _ ab hab
    simp [transportElaborated, toCorePolicy, transportPolicy] at hab
  argsNodup := by decide
  supports := by
    intro term hterm
    rw [transport_args_wrapped] at hterm
    simp only [List.mem_singleton] at hterm
    subst hterm
    refine ⟨.atom "q" .nil,
      transport_hasSupport wrappedCert wrappedCoreAssur rfl (by decide) ?_⟩
    exact transport_cert_accepted_wrapped_raw
  attacksTyped := by intro attack hattack; simp [transportElaborated] at hattack
  sourcesDeclared := by intro attack hattack; simp [transportElaborated] at hattack
  targetsDeclared := by intro attack hattack; simp [transportElaborated] at hattack
  attackComplete := by
    intro source _ target _ sourceConclusion targetConclusion _ _ hmatch
    obtain ⟨ab, hab, _⟩ := hmatch
    simp [transportElaborated, toCorePolicy, transportPolicy] at hab

/-! ### The complete surface judgments

Every remaining field is either a decidable predicate, a two-constructor
inductive, or an equation that holds by how `transportElaborated` was defined.
The `program` field's existential is witnessed by `transportPairs` with no
resolved attacks, since the fixture declares none. -/

theorem transport_checks_kernel :
    Lara.Surface.Checks transportEnv transportInput
      (transportElaborated kernelCert kernelCoreAssur) where
  supported := transport_supported
  admission := ⟨by decide, by
    intro leaf hleaf
    have hleafP : leaf = leafP := by
      simpa [leafRecords, transportInput, transportInputWrapped, transportProgram]
        using hleaf
    subst hleafP
    decide⟩
  freshness := transport_freshness
  rules := by
    intro rule hrule
    refine .intro (transport_supported.rule_namespaces_wf.2 rule hrule) ?_
    have hr : rule = transportRule := by
      simpa [transportInput, transportPolicy] using hrule
    subst hr
    exact .inl rfl
  statuses := (statusesWellFormedB_iff _).mp (by decide)
  groups := (groupsWellFormedB_iff _).mp (by decide)
  expansions := transport_expansions kernelCert
  program :=
    ⟨transportPairs kernelCert kernelCoreAssur, [],
      transport_checksProgram_kernel, by decide, .nil, rfl, rfl, rfl, rfl, rfl⟩
  gamma := rfl
  ground := rfl
  sigma := rfl
  unitPolicy := rfl
  unitAttacks := rfl
  authoredObligations := rfl
  core := transport_coreObligations_kernel

theorem transport_checks_wrapped :
    Lara.Surface.Checks transportEnvWrapped transportInputWrapped
      (transportElaborated wrappedCert wrappedCoreAssur) where
  supported := transport_supported_wrapped
  admission := ⟨by decide, by
    intro leaf hleaf
    have hleafP : leaf = leafP := by
      simpa [leafRecords, transportInput, transportInputWrapped, transportProgram]
        using hleaf
    subst hleafP
    decide⟩
  freshness := transport_freshness_wrapped
  rules := by
    intro rule hrule
    refine .intro (transport_supported_wrapped.rule_namespaces_wf.2 rule hrule) ?_
    have hr : rule = transportRule := by
      simpa [transportInputWrapped, transportPolicy] using hrule
    subst hr
    exact .inl rfl
  statuses := (statusesWellFormedB_iff _).mp (by decide)
  groups := (groupsWellFormedB_iff _).mp (by decide)
  expansions := transport_expansions wrappedCert
  program :=
    ⟨transportPairs wrappedCert wrappedCoreAssur, [],
      transport_checksProgram_wrapped, by decide, .nil, rfl, rfl, rfl, rfl, rfl⟩
  gamma := rfl
  ground := rfl
  sigma := rfl
  unitPolicy := rfl
  unitAttacks := rfl
  authoredObligations := rfl
  core := transport_coreObligations_wrapped

/-! ### Core acceptance

Both units are genuinely accepted by the core checker. This comes from
`CoreObligations.checkUnit_complete` rather than from evaluating `checkUnit`,
which is unavailable here. -/

theorem transport_checkUnit_kernel :
    ∃ checked, Lara.Check.Unit.checkUnit
      (transportElaborated kernelCert kernelCoreAssur).gamma transportEnv.registry
      (transportElaborated kernelCert kernelCoreAssur).ground
      (transportElaborated kernelCert kernelCoreAssur).unit = .ok checked :=
  transport_coreObligations_kernel.checkUnit_complete

theorem transport_checkUnit_wrapped :
    ∃ checked, Lara.Check.Unit.checkUnit
      (transportElaborated wrappedCert wrappedCoreAssur).gamma
      transportEnvWrapped.registry
      (transportElaborated wrappedCert wrappedCoreAssur).ground
      (transportElaborated wrappedCert wrappedCoreAssur).unit = .ok checked :=
  transport_coreObligations_wrapped.checkUnit_complete

/-! ### The instantiation

`Lara.Context.surface_directAF_relabel`, applied to this pair. The statement is
unconditional: the two accepted units are produced here rather than assumed,
so nothing is left hypothetical. -/

/-- **The M4 surface corollary, witnessed.** Two accepted surface programs whose
elaborated units differ by the injective relabel `certSwap` present the same
framework. -/
theorem surfaceTransport_directAF_eq :
    Lara.Surface.directAF transport_checks_wrapped
      = Lara.Surface.directAF transport_checks_kernel := by
  obtain ⟨acc₁, hchecked₁⟩ := transport_checkUnit_kernel
  obtain ⟨acc₂, hchecked₂⟩ := transport_checkUnit_wrapped
  have hs₁ := Lara.Check.Unit.checkUnit_sound hchecked₁
  have hs₂ := Lara.Check.Unit.checkUnit_sound hchecked₂
  refine Lara.Context.surface_directAF_relabel
    transport_checks_kernel hchecked₁ transport_checks_wrapped hchecked₂
    certSwap_injective ?_ ?_
  · rw [hs₂.2.2.2.2.2.2.2.2.1, hs₁.2.2.2.2.2.2.2.2.1]; rfl
  · rw [hs₂.2.2.2.2.2.2.2.2.2.1, hs₁.2.2.2.2.2.2.2.2.2.1]; rfl

/-! ### Non-vacuity

Without these the fixture would be consistent with `f = id`, and the eventual
instantiation of `surface_directAF_relabel` would be a tautology. -/

/-- **The relabel actually moved the elaborated unit.** Without this,
`f = id` would satisfy every hypothesis of `surfaceTransport_directAF_eq` and
the witness would be a tautology. Mirrors
`Examples.Linking.cert_relabel_moves_args`. -/
theorem surfaceTransport_relabel_moves :
    (transportElaborated wrappedCert wrappedCoreAssur).unit.args
      ≠ (transportElaborated kernelCert kernelCoreAssur).unit.args := by
  decide

/-- **The two surface programs are two programs**, not one cited twice. -/
theorem surfaceTransport_inputs_differ : transportInputWrapped ≠ transportInput := by
  decide

/-- The relabel moves this fixture's certificate: the two lowered assurances are
not equal. -/
theorem transport_relabel_moves_cert :
    (Lara.Support.Assurance.cert Lara.Examples.ndId Lara.Examples.digestA (wrapCert kernelRef))
      ≠ .cert Lara.Examples.ndId Lara.Examples.digestA kernelRef := by
  decide

/-- The two surface payloads are two payloads, not one cited twice. -/
theorem transport_payloads_differ : wrappedPayload ≠ kernelPayload := by decide

end Lara.Examples.SurfaceTransport
