/-
# A context-bearing surface link fixture

`Lara.Examples.SurfaceTransport.surfaceTransport_link_directAF_eq` witnesses
`Lara.Context.surface_directAF_link` over a context that declares **no
arguments at all**. Every hypothesis there is genuinely discharged, but one of
them — `FixesContext certSwap linkCtx` — is discharged by `⟨rfl, rfl⟩` because
`linkCtx.frame.args = []`: the relabel leaves the context's own assurances
alone for lack of any assurance to leave alone. `FixesContext` is precisely
what separates a link-respecting relabel from an arbitrary one, so witnessing
it only in that degenerate case is the gap.

This module closes it. The elaborated unit declares **two** core arguments,
split so that

* the **context** owns `a-ctx`, a plain defeasible argument `p ⊢ n` carrying
  `.none`, which `certSwap` fixes; and
* the **fragment** owns `a-cert`, the `SurfaceTransport` certified argument `p ⊢ q`, which
  `certSwap` moves.

So `FixesContext certSwap linkCtx` is now an equation over a one-element
argument list — the relabel has to fix material it could have touched — while
the fragment side of the same relabel is non-trivial
(`surfaceTransportContext_relabel_moves_args`).

## What had to change, and what did not

Everything on the certificate-lowering path is reused verbatim from
`Lara.Examples.SurfaceTransport`: `transportEnv` / `transportEnvWrapped`,
`kernelCert` / `wrappedCert`, `transport_lower_kernel` /
`transport_lower_wrapped`, `transport_cert_accepted` and
`transport_cert_accepted_wrapped_raw`, and the surface argument, built term and
core term of `a-cert` (`transportArg`, `transportBuilt`, `transportCore`). No
`native_decide` and no `sorry`; the axiom ledger stays inside the standard trio.

What could not be reused is the *reduction of `linkedUnit`*.
`SurfaceTransport.linkedUnit_of_empty_ctx` collapses the cross-boundary
saturation by the context having no arguments, which is exactly the degeneracy
being removed here. With a context argument present, `crossAtts` builds both
conclusion caches, and `conclusionCache` calls `Check.inferSupport` through
`certOkOf` on the `nd` core — which does not reduce in the kernel.

The replacement route reads the saturation's *guard* rather than its caches:
`crossAttsFrom` emits nothing unless `contraryMatchB` holds, and
`contraryMatchB` is `dp.contraries.any …`, so a policy with **no declared
contrary** saturates to nothing whatever the caches contain
(`crossAtts_of_no_contraries`). That is a statement about the policy, not about
the argument lists, so it survives the context gaining material.

## The one degeneracy that remains

This fixture declares no attacks, so the attack half of
`link_relabel_commutes` still runs on empty lists.
`Lara.Examples.SurfaceTransportAttack` is the attack-bearing witness for
the relabel corollary; combining a live edge *and* a context-owned argument in
one link fixture is not needed by either issue, and the no-contraries route
above is what keeps this one `native_decide`-free.
-/

import Lara.Examples.SurfaceTransport

namespace Lara.Examples.SurfaceTransportContext

open Lara.Surface Lara.Presentation Lara.Examples.Linking
open Lara.Examples.SurfaceTransport

/-! ### Saturation under a contrary-free policy

The two lemmas `SurfaceTransport` could not use. Both are about the policy's
contrary list, so neither cares how much material either side of the link
declares — which is the whole point, since the context now declares some. -/

/-- A policy with no declared contrary matches nothing. `contraryMatchB` is
`dp.contraries.any (contraryMatchDecl …)`, and `List.any [] = false`. -/
theorem contraryMatchB_of_no_contraries {canon : String → String}
    {dp : Lara.Attack.DefeatPolicy} (hdp : dp.contraries = [])
    (p q : Lara.Atom) : Lara.Attack.contraryMatchB canon dp p q = false := by
  simp [Lara.Attack.contraryMatchB, hdp]

/-- **A contrary-free policy saturates to nothing**, whatever the two caches
contain. Unlike `SurfaceTransport.crossAttsFrom_nil_targets`, this reads the
emission guard rather than the target list, so it holds with both sides of the
link carrying declared arguments. -/
theorem crossAttsFrom_of_no_contraries {canon : String → String}
    {dp : Lara.Attack.DefeatPolicy}
    {Pi : Lara.Support.RuleId → Option Lara.Support.Rule}
    (hdp : dp.contraries = []) (sources targets : List (Lara.Support.SupportTerm × Lara.Atom)) :
    Lara.Context.crossAttsFrom canon dp Pi sources targets = [] := by
  simp [Lara.Context.crossAttsFrom, contraryMatchB_of_no_contraries hdp]

/-- Both directions of the cross-boundary saturation are empty. -/
theorem crossAtts_of_no_contraries {canon : String → String}
    {reg : Lara.Support.BackendRegistry canon}
    {Gamma : Lara.Support.LeafId → Option Lara.Atom}
    {C : Lara.Context.Context} {F : Lara.Context.Fragment}
    (hdp : F.policy.defeat.contraries = []) :
    Lara.Context.crossAtts reg Gamma C F = [] := by
  show Lara.Context.crossAttsFrom canon F.policy.defeat F.policy.ruleLookup
        (Lara.Context.conclusionCache F.policy.ruleLookup Gamma reg C.frame.args)
        (Lara.Context.conclusionCache F.policy.ruleLookup Gamma reg F.args)
      ++ Lara.Context.crossAttsFrom canon F.policy.defeat F.policy.ruleLookup
        (Lara.Context.conclusionCache F.policy.ruleLookup Gamma reg F.args)
        (Lara.Context.conclusionCache F.policy.ruleLookup Gamma reg C.frame.args)
      = []
  rw [crossAttsFrom_of_no_contraries hdp, crossAttsFrom_of_no_contraries hdp]
  rfl

/-- **The linked unit of a contrary-free, attack-free link** is the two sides'
material merged, with nothing saturated in. The context's argument list is
unconstrained here — that is the difference from
`SurfaceTransport.linkedUnit_of_empty_ctx`. -/
theorem linkedUnit_of_no_contraries {canon : String → String}
    {reg : Lara.Support.BackendRegistry canon}
    {C : Lara.Context.Context} {F : Lara.Context.Fragment}
    (hdp : F.policy.defeat.contraries = [])
    (hattsC : C.frame.atts = []) (hattsF : F.atts = []) :
    Lara.Context.linkedUnit reg C F =
      { sigma := F.sigma
      , policy := F.policy
      , args := Lara.Context.dedupList (C.frame.args ++ F.args)
      , atts := [] } := by
  have hcross :=
    crossAtts_of_no_contraries (reg := reg) (Gamma := Lara.Context.linkGamma C F)
      (C := C) (F := F) hdp
  simp only [Lara.Context.linkedUnit, hattsC, hattsF, hcross, List.append_nil]

/-! ### The policy

`transportRule` is reused unchanged as the strict certified rule. The one new
rule is as plain as the grammar allows: defeasible, parameterless,
question-free, no certifiers, `p ⊢ n`. It is what the *context* will own, and
`.none` is what makes `certSwap` fix it.

The contrary list is empty — that is what `crossAtts_of_no_contraries` above
consumes, and it also keeps every attack-side obligation vacuous. -/

def contextPolicyId : PolicyId := ⟨"transport-context-policy"⟩
def ctxRuleId : RuleId := ⟨"r-ctx"⟩
def argCtxId : ArgId := ⟨"a-ctx"⟩

def contextSigma : Lara.Sigma.Sigma :=
  { sorts := [], cons := []
    preds := [⟨⟨"p"⟩, []⟩, ⟨⟨"q"⟩, []⟩, ⟨⟨"n"⟩, []⟩] }

/-- The context's rule: `p ⊢ n`, defeasible, `.none` assurance. -/
def ctxRule : Rule :=
  { id := ctxRuleId
    params := []
    mode := .defeasible
    premises := [⟨"p", .nil⟩]
    premiseLabels := []
    conclusion := ⟨"n", .nil⟩
    allowTrusted := false
    certifiers := []
    questions := [] }

def contextPolicy : Policy :=
  { id := contextPolicyId
    sigma := contextSigma
    rules := [transportRule, ctxRule]
    contraries := []
    exceptions := []
    admission := [((.observed, .user), .admit)]
    theories := [(theoryDigestA, [.atom "q" .nil])]
    groupMode := .quarantineOnConflict
    measurands := []
    comparisonSchemes := [] }

/-- The core policy declares no contrary, which is the hypothesis every
saturation lemma above takes. -/
theorem contextPolicy_no_contraries :
    (toCorePolicy contextPolicy).defeat.contraries = [] := rfl

/-! ### The program

Two arguments over the one observed leaf. `a-ctx` is declared **first**, so
that the retained declaration order is `[a-ctx, a-cert]` — the same order
`linkedUnit` produces from `C.frame.args ++ F.args`. -/

def contextArgCtx : Arg :=
  ⟨argCtxId, .supportsDerived ⟨"c-n"⟩, .inferTheta ctxRuleId [⟨"l-p"⟩] [] [] .none⟩

def contextProgram (assurance : Assurance) : Program :=
  { artifact := "surface-transport-context"
    digest := ⟨"sha256:transport-context"⟩
    policy := contextPolicyId
    backends := [(⟨"nd"⟩, "1")]
    valueBindings := []
    decls := [.leaf leafP, .arg contextArgCtx, .arg (transportArg assurance)] }

def contextInput : Lara.Surface.Input :=
  ⟨contextProgram kernelCertificate, contextPolicy⟩

def contextInputWrapped : Lara.Surface.Input :=
  ⟨contextProgram wrappedCertificate, contextPolicy⟩

/-! ### Core and reconstructed terms

`a-cert`'s are `SurfaceTransport`'s, unchanged. `a-ctx` gets the same shape
with the plain rule and `.none`. -/

/-- The context's core argument. Note the `.none` assurance: this is the term
`certSwap` has to fix. -/
def ctxCore : Lara.Support.SupportTerm :=
  .inst ⟨"r-ctx"⟩ [] [.leaf ⟨"l-p"⟩] [] [] .none

def builtCtx : PriorArgument :=
  ⟨argCtxId,
    .rule ctxRuleId [] (supportTermsFromList [transportResolved.term])
      (dischargesFromList []) [] .none,
    .atom "n" .nil⟩

/-! ### The cheap `Checks` fields -/

theorem context_supported : Lara.Surface.Supported contextInput := by
  apply (Lara.Surface.supportedB_iff contextInput).mp
  decide

theorem context_supported_wrapped :
    Lara.Surface.Supported contextInputWrapped := by
  apply (Lara.Surface.supportedB_iff contextInputWrapped).mp
  decide

theorem context_freshness :
    Lara.Surface.GeneratedIdsFresh contextInput.program = true := by decide

theorem context_freshness_wrapped :
    Lara.Surface.GeneratedIdsFresh contextInputWrapped.program = true := by decide

/-! ### The two argument derivations

`a-ctx` resolves its premise against the declared leaf and carries
`ChecksAssurance.none`, so it adds no lowering obligation. `a-cert` repeats
`SurfaceTransport`'s derivation with `[builtCtx]` in scope as a prior — which is why
`transport_lower_kernel` / `transport_lower_wrapped` are stated universally in
the priors. -/

theorem context_checksArgument_ctx
    {env : Lara.Surface.Env (fun source => source)} (assurance : Assurance) :
    ChecksArgument env (contextProgram assurance) contextPolicy []
      contextArgCtx builtCtx ctxCore := by
  refine ChecksArgument.inferred
    (rule := ctxRule) (resolved := [transportResolved]) (theta := [])
    (conclusion := .atom "n" .nil)
    (.there (by decide) (.here rfl)) rfl ?_ ?_ ?_ ?_ rfl .supportsDerived ?_
  · exact .cons (.leaf rfl rfl) .nil
  · exact .cons rfl .nil
  · intro param hparam; simp [ctxRule] at hparam
  · exact .nil
  · exact .rule (.there (by decide) (.here rfl)) (.cons .leaf .nil) .nil .none

theorem context_checksArgument_cert
    {env : Lara.Surface.Env (fun source => source)}
    (certificate : Cert) (coreAssur : Lara.Support.Assurance)
    (hlower : lowerAssuranceCertificate env (contextProgram (.cert certificate))
        transportRule [builtCtx] [transportResolved.term] (.cert certificate)
      = some coreAssur) :
    ChecksArgument env (contextProgram (.cert certificate)) contextPolicy
      [builtCtx] (transportArg (.cert certificate)) (transportBuilt certificate)
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

/-! ### The declaration fold -/

def contextPairs (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    List ReconstructedArgument :=
  [⟨contextArgCtx, builtCtx, ctxCore⟩,
    ⟨transportArg (.cert certificate), transportBuilt certificate,
      transportCore coreAssur⟩]

theorem context_checksProgram_kernel :
    ChecksProgram transportEnv (contextProgram kernelCertificate) contextPolicy
      (contextProgram kernelCertificate).decls []
      (contextPairs kernelCert kernelCoreAssur) :=
  .cons .leaf
    (.cons (.arg (context_checksArgument_ctx kernelCertificate))
      (.cons (.arg (context_checksArgument_cert kernelCert kernelCoreAssur
          (transport_lower_kernel _ _ _ _)))
        .nil))

theorem context_checksProgram_wrapped :
    ChecksProgram transportEnvWrapped (contextProgram wrappedCertificate)
      contextPolicy (contextProgram wrappedCertificate).decls []
      (contextPairs wrappedCert wrappedCoreAssur) :=
  .cons .leaf
    (.cons (.arg (context_checksArgument_ctx wrappedCertificate))
      (.cons (.arg (context_checksArgument_cert wrappedCert wrappedCoreAssur
          (transport_lower_wrapped _ _ _ _)))
        .nil))

/-! ### The elaborated carrier -/

def contextKept (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    List ReconstructedArgument :=
  keptReconstructed (fun source => source) contextPolicy
    (contextProgram (.cert certificate)) (contextPairs certificate coreAssur)

def contextElaborated (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    Lara.Surface.Elaborated (fun source => source) where
  gamma := surfaceGamma (fun source => source) contextPolicy
    (contextProgram (.cert certificate))
  ground := surfaceGround (fun source => source) contextPolicy
    (contextProgram (.cert certificate))
  unit :=
    { sigma := contextPolicy.sigma
      policy := toCorePolicy contextPolicy
      args := (contextKept certificate coreAssur).map (·.core)
      atts := [] }
  claims := claimsOf (contextKept certificate coreAssur)
    (contextProgram (.cert certificate))
  argIds := (contextKept certificate coreAssur).map (·.argument.id)
  authoredObligations := authoredObligationsOf (contextProgram (.cert certificate))
  openQuestions := openQuestionsOf (contextKept certificate coreAssur)
  resolvedAttacks := []
  semanticProgram := contextProgram (.cert certificate)

theorem context_expansions (certificate : Cert) :
    ∃ mid target generated,
      ExpandsValues (contextProgram (.cert certificate)) mid ∧
        GeneratedIdsFresh mid = true ∧
        (comparisonKeys mid).Nodup ∧
        ExpandsComparisons contextPolicy mid target generated ∧
        target = contextProgram (.cert certificate) :=
  ⟨contextProgram (.cert certificate), contextProgram (.cert certificate), [],
    expandValues_sound contextPolicy rfl,
    rfl,
    by simp [comparisonKeys, comparisonDecls, contextProgram],
    expandComparisons_sound contextPolicy rfl,
    rfl⟩

/-! ### Core support

Both arguments are derived under an arbitrary Γ that declares `l-p`, so the
same lemmas serve the elaboration-facing obligations (Γ is `Elaborated.gamma`)
and the link-facing ones (Γ is `linkGamma`). -/

theorem contextCorePolicy_ruleLookup_cert :
    (toCorePolicy contextPolicy).ruleLookup ⟨"r-cert"⟩
      = some (toCoreRule transportRule) := rfl

theorem contextCorePolicy_ruleLookup_ctx :
    (toCorePolicy contextPolicy).ruleLookup ⟨"r-ctx"⟩
      = some (toCoreRule ctxRule) := rfl

theorem context_gamma_leafP (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    (contextElaborated certificate coreAssur).gamma ⟨"l-p"⟩
      = some (.atom "p" .nil) := rfl

/-- **The context's plain argument is supported.** No registry is consulted:
the assurance side condition is `AssuranceOk.defeasible`. -/
theorem context_hasSupport_ctx
    {reg : Lara.Support.BackendRegistry (fun source => source)}
    {Gamma : Lara.Support.LeafId → Option Lara.Atom}
    (hgamma : Gamma ⟨"l-p"⟩ = some (.atom "p" .nil)) :
    Lara.Support.HasSupport (fun source => source)
      (toCorePolicy contextPolicy).ruleLookup Gamma
      (Lara.Support.certOkOf reg) ctxCore (.atom "n" .nil) [] := by
  refine Lara.Support.HasSupport.inst
    (As := [.atom "p" .nil]) (Cs := [.atom "p" .nil]) (Os := [[]])
    (DCs := []) (DOs := [])
    { rule := contextCorePolicy_ruleLookup_ctx
      θNodup := by decide
      θDom := by intro x; simp [ctxRule, toCoreRule]
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
      cover := by intro qd hqd; simp [ctxRule, toCoreRule] at hqd
      disj := by intro n hn; simp at hn
      keysD := by intro n hn; simp at hn
      keysH := by intro n hn; simp at hn
      strictNoQ := by intro hstrict; simp [toCoreRule, ctxRule] at hstrict
      assur := .defeasible (by decide) } ?_ ?_
  · intro i w A O hw hA hO
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hA hO
        subst hw; subst hA; subst hO
        exact .leaf hgamma
    | succ n => simp at hw
  · intro j q w A O hj; simp at hj

/-- **The fragment's certified argument is supported.** The `SurfaceTransport` derivation,
restated at this fixture's policy. -/
theorem context_hasSupport_cert
    {reg : Lara.Support.BackendRegistry (fun source => source)}
    {Gamma : Lara.Support.LeafId → Option Lara.Atom}
    (coreAssur : Lara.Support.Assurance)
    {β : Lara.Support.BackendId} {digest : Lara.Support.Digest}
    {κ : Lara.Support.CertRef}
    (hgamma : Gamma ⟨"l-p"⟩ = some (.atom "p" .nil))
    (hassur : coreAssur = .cert β digest κ)
    (hallow : (β, digest) ∈ (toCoreRule transportRule).certifiers)
    (hacc : Lara.Support.certOkOf reg β digest κ [.atom "p" .nil] (.atom "q" .nil)) :
    Lara.Support.HasSupport (fun source => source)
      (toCorePolicy contextPolicy).ruleLookup Gamma
      (Lara.Support.certOkOf reg) (transportCore coreAssur)
      (.atom "q" .nil) [] := by
  subst hassur
  refine Lara.Support.HasSupport.inst
    (As := [.atom "p" .nil]) (Cs := [.atom "p" .nil]) (Os := [[]])
    (DCs := []) (DOs := [])
    { rule := contextCorePolicy_ruleLookup_cert
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
        exact .leaf hgamma
    | succ n => simp at hw
  · intro j q w A O hj; simp at hj

/-! ### The core obligations

The argument list now has two entries, so `supports` discharges two cases. The
attack-side fields stay vacuous: the fixture declares no attack and the policy
no contrary. -/

theorem context_args_kernel :
    (contextElaborated kernelCert kernelCoreAssur).unit.args
      = [ctxCore, transportCore kernelCoreAssur] := rfl

theorem context_args_wrapped :
    (contextElaborated wrappedCert wrappedCoreAssur).unit.args
      = [ctxCore, transportCore wrappedCoreAssur] := rfl

theorem context_coreObligations_kernel :
    CoreObligations transportEnv (contextElaborated kernelCert kernelCoreAssur) where
  sigmaWellFormed := by decide
  policyWellSorted := by decide
  groundWellSorted := by decide
  argsWellSorted := by decide
  scopesWellFormed := by decide
  ruleIdsNodup := by decide
  policyWellFormed := by
    intro p _ ab hab
    simp [contextElaborated, toCorePolicy, contextPolicy] at hab
  argsNodup := by decide
  supports := by
    intro term hterm
    rw [context_args_kernel] at hterm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hterm
    rcases hterm with h | h <;> subst h
    · exact ⟨.atom "n" .nil, context_hasSupport_ctx rfl⟩
    · exact ⟨.atom "q" .nil,
        context_hasSupport_cert kernelCoreAssur rfl rfl (by decide)
          transport_cert_accepted⟩
  attacksTyped := by intro attack hattack; simp [contextElaborated] at hattack
  sourcesDeclared := by intro attack hattack; simp [contextElaborated] at hattack
  targetsDeclared := by intro attack hattack; simp [contextElaborated] at hattack
  attackComplete := by
    intro source _ target _ sourceConclusion targetConclusion _ _ hmatch
    obtain ⟨ab, hab, _⟩ := hmatch
    simp [contextElaborated, toCorePolicy, contextPolicy] at hab

theorem context_coreObligations_wrapped :
    CoreObligations transportEnvWrapped
      (contextElaborated wrappedCert wrappedCoreAssur) where
  sigmaWellFormed := by decide
  policyWellSorted := by decide
  groundWellSorted := by decide
  argsWellSorted := by decide
  scopesWellFormed := by decide
  ruleIdsNodup := by decide
  policyWellFormed := by
    intro p _ ab hab
    simp [contextElaborated, toCorePolicy, contextPolicy] at hab
  argsNodup := by decide
  supports := by
    intro term hterm
    rw [context_args_wrapped] at hterm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hterm
    rcases hterm with h | h <;> subst h
    · exact ⟨.atom "n" .nil, context_hasSupport_ctx rfl⟩
    · exact ⟨.atom "q" .nil,
        context_hasSupport_cert wrappedCoreAssur rfl rfl (by decide)
          transport_cert_accepted_wrapped_raw⟩
  attacksTyped := by intro attack hattack; simp [contextElaborated] at hattack
  sourcesDeclared := by intro attack hattack; simp [contextElaborated] at hattack
  targetsDeclared := by intro attack hattack; simp [contextElaborated] at hattack
  attackComplete := by
    intro source _ target _ sourceConclusion targetConclusion _ _ hmatch
    obtain ⟨ab, hab, _⟩ := hmatch
    simp [contextElaborated, toCorePolicy, contextPolicy] at hab

/-! ### The complete surface judgments -/

theorem context_checks_kernel :
    Lara.Surface.Checks transportEnv contextInput
      (contextElaborated kernelCert kernelCoreAssur) where
  supported := context_supported
  admission := ⟨by decide, by
    intro leaf hleaf
    have hleafP : leaf = leafP := by
      simpa [leafRecords, contextInput, contextInputWrapped, contextProgram]
        using hleaf
    subst hleafP
    decide⟩
  freshness := context_freshness
  rules := by
    intro rule hrule
    refine .intro (context_supported.rule_namespaces_wf.2 rule hrule) (.inl ?_)
    have hr : rule = transportRule ∨ rule = ctxRule := by
      simpa [contextInput, contextPolicy] using hrule
    rcases hr with h | h <;> subst h <;> rfl
  statuses := (statusesWellFormedB_iff _).mp (by decide)
  groups := (groupsWellFormedB_iff _).mp (by decide)
  expansions := context_expansions kernelCert
  program :=
    ⟨contextPairs kernelCert kernelCoreAssur, [],
      context_checksProgram_kernel, by decide, .nil, rfl, rfl, rfl, rfl, rfl⟩
  gamma := rfl
  ground := rfl
  sigma := rfl
  unitPolicy := rfl
  unitAttacks := rfl
  authoredObligations := rfl
  core := context_coreObligations_kernel

theorem context_checks_wrapped :
    Lara.Surface.Checks transportEnvWrapped contextInputWrapped
      (contextElaborated wrappedCert wrappedCoreAssur) where
  supported := context_supported_wrapped
  admission := ⟨by decide, by
    intro leaf hleaf
    have hleafP : leaf = leafP := by
      simpa [leafRecords, contextInput, contextInputWrapped, contextProgram]
        using hleaf
    subst hleafP
    decide⟩
  freshness := context_freshness_wrapped
  rules := by
    intro rule hrule
    refine .intro (context_supported_wrapped.rule_namespaces_wf.2 rule hrule) (.inl ?_)
    have hr : rule = transportRule ∨ rule = ctxRule := by
      simpa [contextInputWrapped, contextPolicy] using hrule
    rcases hr with h | h <;> subst h <;> rfl
  statuses := (statusesWellFormedB_iff _).mp (by decide)
  groups := (groupsWellFormedB_iff _).mp (by decide)
  expansions := context_expansions wrappedCert
  program :=
    ⟨contextPairs wrappedCert wrappedCoreAssur, [],
      context_checksProgram_wrapped, by decide, .nil, rfl, rfl, rfl, rfl, rfl⟩
  gamma := rfl
  ground := rfl
  sigma := rfl
  unitPolicy := rfl
  unitAttacks := rfl
  authoredObligations := rfl
  core := context_coreObligations_wrapped

/-! ### Core acceptance -/

theorem context_checkUnit_kernel :
    ∃ checked, Lara.Check.Unit.checkUnit
      (contextElaborated kernelCert kernelCoreAssur).gamma transportEnv.registry
      (contextElaborated kernelCert kernelCoreAssur).ground
      (contextElaborated kernelCert kernelCoreAssur).unit = .ok checked :=
  context_coreObligations_kernel.checkUnit_complete

theorem context_checkUnit_wrapped :
    ∃ checked, Lara.Check.Unit.checkUnit
      (contextElaborated wrappedCert wrappedCoreAssur).gamma
      transportEnvWrapped.registry
      (contextElaborated wrappedCert wrappedCoreAssur).ground
      (contextElaborated wrappedCert wrappedCoreAssur).unit = .ok checked :=
  context_coreObligations_wrapped.checkUnit_complete

/-! ### The two sides of the link

The split the whole module exists for: the context owns `a-ctx` and the leaf
that both arguments read; the fragment owns `a-cert` and imports the leaf. -/

/-- **The context**, now with material of its own. `args = [ctxCore]` is what
makes `FixesContext certSwap linkCtx` a real obligation. -/
def linkCtx : Lara.Context.Context :=
  ⟨{ sigma     := contextSigma
   , policy    := toCorePolicy contextPolicy
   , gammaFrag := [(⟨"l-p"⟩, .atom "p" .nil)]
   , ground    := [.atom "p" .nil, .atom "n" .nil]
   , args      := [ctxCore]
   , atts      := []
   , imports   := Lara.Context.Interface.closed
   , exports   := [.atom "n" .nil] }⟩

/-- **The fragment**: the certified argument, importing the leaf the context
declares and exporting `q`. -/
def linkFrag (coreAssur : Lara.Support.Assurance) : Lara.Context.Fragment :=
  { sigma     := contextSigma
  , policy    := toCorePolicy contextPolicy
  , gammaFrag := []
  , ground    := [.atom "q" .nil]
  , args      := [transportCore coreAssur]
  , atts      := []
  , imports   := ⟨[⟨"l-p"⟩]⟩
  , exports   := [.atom "q" .nil] }

/-- The relabeled fragment is the fragment at the relabeled assurance. -/
theorem linkFrag_relabel :
    Lara.Context.mapAssurFrag certSwap (linkFrag kernelCoreAssur)
      = linkFrag wrappedCoreAssur := rfl

/-- The linked Γ declares `l-p`, which is all either argument reads out of it. -/
theorem linkGamma_leafP (F : Lara.Context.Fragment) (hgamma : F.gammaFrag = []) :
    Lara.Context.linkGamma linkCtx F ⟨"l-p"⟩ = some (.atom "p" .nil) := by
  simp [Lara.Context.linkGamma, linkCtx, hgamma, Lara.Admission.buildGamma]

/-! #### The two elaborated units are the two sides of this link -/

theorem context_unit_is_link :
    (contextElaborated kernelCert kernelCoreAssur).unit
      = Lara.Context.linkedUnit transportEnv.registry linkCtx
          (linkFrag kernelCoreAssur) := by
  rw [linkedUnit_of_no_contraries (C := linkCtx) contextPolicy_no_contraries rfl rfl]
  rfl

theorem context_unit_wrapped_is_link :
    (contextElaborated wrappedCert wrappedCoreAssur).unit
      = Lara.Context.linkedUnit transportEnvWrapped.registry linkCtx
          (Lara.Context.mapAssurFrag certSwap (linkFrag kernelCoreAssur)) := by
  rw [linkFrag_relabel,
    linkedUnit_of_no_contraries (C := linkCtx) contextPolicy_no_contraries rfl rfl]
  rfl

/-! #### Admissibility

Both `SideOk` derivations now carry an argument. The context side is the one
that was vacuous in the link fixture. -/

theorem linkSideOk_ctx {reg : Lara.Support.BackendRegistry (fun source => source)}
    (F : Lara.Context.Fragment) (hgamma : F.gammaFrag = []) :
    Lara.Context.SideOk (fun source => source) reg
      (Lara.Context.linkGamma linkCtx F) (toCorePolicy contextPolicy)
      linkCtx.frame.args linkCtx.frame.atts where
  support := by
    intro w hw
    have hwc : w = ctxCore := by simpa [linkCtx] using hw
    exact ⟨.atom "n" .nil,
      hwc ▸ context_hasSupport_ctx (linkGamma_leafP F hgamma)⟩
  typed := by intro k hk; simp [linkCtx] at hk
  source_declared := by intro k hk; simp [linkCtx] at hk
  target_declared := by intro k hk; simp [linkCtx] at hk
  attack_complete := by
    intro source _ target _ Cs Ct _ _ hcm _
    obtain ⟨ab, hab, _⟩ := hcm
    simp [toCorePolicy, contextPolicy] at hab

theorem linkSideOk_frag {reg : Lara.Support.BackendRegistry (fun source => source)}
    (coreAssur : Lara.Support.Assurance)
    {β : Lara.Support.BackendId} {digest : Lara.Support.Digest}
    {κ : Lara.Support.CertRef}
    (hassur : coreAssur = .cert β digest κ)
    (hallow : (β, digest) ∈ (toCoreRule transportRule).certifiers)
    (hacc : Lara.Support.certOkOf reg β digest κ [.atom "p" .nil] (.atom "q" .nil)) :
    Lara.Context.SideOk (fun source => source) reg
      (Lara.Context.linkGamma linkCtx (linkFrag coreAssur))
      (toCorePolicy contextPolicy)
      (linkFrag coreAssur).args (linkFrag coreAssur).atts where
  support := by
    intro w hw
    have hwc : w = transportCore coreAssur := by simpa [linkFrag] using hw
    exact ⟨.atom "q" .nil, hwc ▸ context_hasSupport_cert coreAssur
      (linkGamma_leafP (linkFrag coreAssur) rfl) hassur hallow hacc⟩
  typed := by intro k hk; simp [linkFrag] at hk
  source_declared := by intro k hk; simp [linkFrag] at hk
  target_declared := by intro k hk; simp [linkFrag] at hk
  attack_complete := by
    intro source _ target _ Cs Ct _ _ hcm _
    obtain ⟨ab, hab, _⟩ := hcm
    simp [toCorePolicy, contextPolicy] at hab

/-- **The context is admissible for the fragment.** -/
theorem contextLink_admissible :
    Lara.Context.Admissible registryEx linkCtx (linkFrag kernelCoreAssur) where
  guard := by decide
  ctx := linkSideOk_ctx (reg := registryEx) (linkFrag kernelCoreAssur) rfl
  frag := linkSideOk_frag (reg := registryEx) kernelCoreAssur rfl (by decide)
    transport_cert_accepted
  signature :=
    Lara.Context.signatureStage_link (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  scope := by decide
  ruleIds := by decide
  policy := Lara.Policy.firstViolation_none_iff.mp (by decide)

/-- **The relabel fixes the context.** Unlike the link fixture's `⟨rfl, rfl⟩`, the
argument component is an equation over a non-empty list: `certSwap` has to
leave `ctxCore`'s `.none` assurance alone, and it does. -/
theorem contextLink_fixesContext : Lara.Context.FixesContext certSwap linkCtx where
  args := rfl
  atts := rfl

/-! #### The instantiation -/

/-- **The M4 link corollary, witnessed over a context that carries material.**
Two accepted surface programs whose elaborated units are the two sides of one
link — a fragment and its `certSwap` relabeling, inside a context that declares
an argument of its own — present the same framework. -/
theorem surfaceTransportContext_link_directAF_eq :
    Lara.Surface.directAF context_checks_wrapped
      = Lara.Surface.directAF context_checks_kernel := by
  obtain ⟨acc₁, hchecked₁⟩ := context_checkUnit_kernel
  obtain ⟨acc₂, hchecked₂⟩ := context_checkUnit_wrapped
  exact Lara.Context.surface_directAF_link
    (C := linkCtx) (F := linkFrag kernelCoreAssur)
    context_checks_kernel hchecked₁ context_checks_wrapped hchecked₂
    certSwap_injective certSwap_preserving contextLink_admissible
    contextLink_fixesContext
    context_unit_is_link context_unit_wrapped_is_link

/-! ### Non-vacuity

The first two guards are the ones the context-bearing brief asks for — without them the fixture
could silently regress to the link fixture's empty context, and `FixesContext` would go
back to holding for want of anything to fix. The rest are `SurfaceTransport`'s
guards, restated here. -/

/-- **The context declares an argument**, and it survives into the linked
unit. This is the guard against regressing to the link-fixture shape. -/
theorem surfaceTransportContext_ctx_args_nonempty :
    linkCtx.frame.args ≠ [] ∧
      ctxCore ∈ (contextElaborated kernelCert kernelCoreAssur).unit.args := by
  refine ⟨by decide, ?_⟩
  rw [context_args_kernel]
  exact List.mem_cons_self

/-- **`FixesContext` is discharged on material, not on emptiness.** The relabel
fixes the context's declared argument — and the very same relabel moves the
fragment's, so the hypothesis is a real constraint that this pair satisfies
rather than a vacuous one. -/
theorem surfaceTransportContext_fixes_is_substantive :
    linkCtx.frame.args.map (Lara.Erase.mapAssur certSwap) = linkCtx.frame.args ∧
      Lara.Erase.mapAssur certSwap ctxCore = ctxCore ∧
      Lara.Erase.mapAssur certSwap (transportCore kernelCoreAssur)
        ≠ transportCore kernelCoreAssur := by
  refine ⟨rfl, rfl, by decide⟩

/-- **The relabel actually moved the fragment's declared material.** -/
theorem surfaceTransportContext_relabel_moves_args :
    (Lara.Context.mapAssurFrag certSwap (linkFrag kernelCoreAssur)).args
      ≠ (linkFrag kernelCoreAssur).args := by decide

/-- **The relabel is not the identity on this fragment.** -/
theorem surfaceTransportContext_relabel_moves :
    Lara.Context.mapAssurFrag certSwap (linkFrag kernelCoreAssur)
      ≠ linkFrag kernelCoreAssur :=
  fun h => surfaceTransportContext_relabel_moves_args
    (congrArg Lara.Context.Fragment.args h)

/-- **The link is a link**: the fragment imports a leaf it does not declare,
and the context is what supplies it. -/
theorem surfaceTransportContext_link_imports_nonempty :
    (linkFrag kernelCoreAssur).imports.leaves ≠ [] ∧
      (linkFrag kernelCoreAssur).imports.leaves = linkCtx.frame.declared := by
  constructor <;> decide

/-- **The relabel moved the elaborated unit**, and the two surface programs are
two programs rather than one cited twice. -/
theorem surfaceTransportContext_inputs_differ :
    (contextElaborated wrappedCert wrappedCoreAssur).unit.args
        ≠ (contextElaborated kernelCert kernelCoreAssur).unit.args ∧
      contextInputWrapped ≠ contextInput := by
  constructor <;> decide

end Lara.Examples.SurfaceTransportContext
