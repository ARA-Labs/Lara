/-
# An attack-bearing surface transport fixture (#258)

`Lara.Examples.SurfaceTransport.surfaceTransport_directAF_eq` witnesses
`Lara.Context.surface_directAF_relabel` on a pair of programs that declare no
attacks. The equality it proves is therefore between two one-node, no-edge
frameworks, and `checkedAF_map`'s edge half — `coveredB_relabel hf P₁.atts
source target` at `Lara/Context/Surface.lean:53` — is exercised on an empty
list. This module rebuilds the same `native_decide`-free fixture around a
**declared attack**, so the edge half does real work.

## Why the attack cannot touch the certified argument

The obvious shape — the strict, certificate-bearing argument rebutting a plain
defeasible one — is *unavailable*, and not for a proof-engineering reason.
`Lara.Policy.WellFormed` (`Lara/Policy.lean:524`) forbids any declared contrary
whose either side overlaps a strict-reachable conclusion pattern, and
`StrictReachable` is exactly "conclusion of a declared strict rule"
(`Lara/Policy.lean:203`). The certified rule here is strict with conclusion `q`,
so no contrary may mention `q`, and `HasAttack.rebut` needs a `ContraryMatch`
between the source's and the target's conclusions. A certified argument can
therefore be neither endpoint of a rebut in a well-formed policy.

The fixture routes around this by making the certificate a **premise** of both
endpoints rather than an endpoint:

* `r-cert` is strict, `p ⊢ q`, certified by `nd@1` at `digestA` — the same rule
  the `#227` fixture uses, reused verbatim as `SurfaceTransport.transportRule`;
* `r-s` and `r-t` are plain defeasible rules `q ⊢ s` and `q ⊢ t`, with `.none`
  assurance and no certifiers, so neither adds a certificate-lowering
  obligation;
* the policy declares `contrary s t`, which overlaps neither `q` (the only
  strict conclusion) nor anything else;
* the program declares `rebut a-s a-t`.

Both attack endpoints contain the certified argument as their premise, so
`mapAssurAtt certSwap` moves the *attack*, not just the argument list, and the
relabel hypothesis `hatts` of `surface_directAF_relabel` is a real equation
between two different attack lists rather than `[] = []`.

Everything on the certificate-lowering path is reused from
`Lara.Examples.SurfaceTransport`: `transportEnv`, `transportEnvWrapped`,
`kernelCert` / `wrappedCert`, `transport_lower_kernel` /
`transport_lower_wrapped` (both universally quantified over the program, rule,
priors and premises they are cited from), `transport_cert_accepted` and
`transport_cert_accepted_wrapped_raw`. No `native_decide` and no `sorry`.
-/

import Lara.Examples.SurfaceTransport

namespace Lara.Examples.SurfaceTransportAttack

open Lara.Surface Lara.Presentation Lara.Examples.Linking
open Lara.Examples.SurfaceTransport

/-! ### The policy

Four nullary predicates and three rules. `transportRule` is reused unchanged as
the strict certified rule; the two defeasible rules are as plain as the grammar
allows. The single contrary `s ~ t` is the whole reason the fixture has an
edge. -/

def attackPolicyId : PolicyId := ⟨"transport-attack-policy"⟩
def sRuleId : RuleId := ⟨"r-s"⟩
def tRuleId : RuleId := ⟨"r-t"⟩
def argSId : ArgId := ⟨"a-s"⟩
def argTId : ArgId := ⟨"a-t"⟩

def attackSigma : Lara.Sigma.Sigma :=
  { sorts := [], cons := []
    preds := [⟨⟨"p"⟩, []⟩, ⟨⟨"q"⟩, []⟩, ⟨⟨"s"⟩, []⟩, ⟨⟨"t"⟩, []⟩] }

/-- Plain and defeasible: `q ⊢ s`, `.none` assurance, no certifiers. -/
def sRule : Rule :=
  { id := sRuleId
    params := []
    mode := .defeasible
    premises := [⟨"q", .nil⟩]
    premiseLabels := []
    conclusion := ⟨"s", .nil⟩
    allowTrusted := false
    certifiers := []
    questions := [] }

/-- Its twin `q ⊢ t`. The two conclusions are the contrary pair. -/
def tRule : Rule :=
  { id := tRuleId
    params := []
    mode := .defeasible
    premises := [⟨"q", .nil⟩]
    premiseLabels := []
    conclusion := ⟨"t", .nil⟩
    allowTrusted := false
    certifiers := []
    questions := [] }

def attackPolicy : Policy :=
  { id := attackPolicyId
    sigma := attackSigma
    rules := [transportRule, sRule, tRule]
    contraries := [⟨⟨"s", .nil⟩, ⟨"t", .nil⟩⟩]
    exceptions := []
    admission := [((.observed, .user), .admit)]
    theories := [(theoryDigestA, [.atom "q" .nil])]
    groupMode := .quarantineOnConflict
    measurands := []
    comparisonSchemes := [] }

/-! ### The program

Three arguments and one attack. The certified argument is parameterised by its
assurance, exactly as in `#227`, so the two programs differ in the certificate
and nothing else. -/

def attackArgCert (assurance : Assurance) : Arg :=
  ⟨argCertId, .supportsDerived ⟨"c-q"⟩,
    .inferTheta transportRuleId [⟨"l-p"⟩] [] [] assurance⟩

def attackArgS : Arg :=
  ⟨argSId, .supportsDerived ⟨"c-s"⟩,
    .inferTheta sRuleId [⟨"a-cert"⟩] [] [] .none⟩

def attackArgT : Arg :=
  ⟨argTId, .supportsDerived ⟨"c-t"⟩,
    .inferTheta tRuleId [⟨"a-cert"⟩] [] [] .none⟩

/-- The declared attack: `a-s` rebuts `a-t`. A rebut needs only two
`findArgTerm` lookups — no `ChecksPath` derivation. -/
def attackDeclaration : SurfaceAttack := .rebut argSId argTId

def attackProgram (assurance : Assurance) : Program :=
  { artifact := "surface-transport-attack"
    digest := ⟨"sha256:transport-attack"⟩
    policy := attackPolicyId
    backends := [(⟨"nd"⟩, "1")]
    valueBindings := []
    decls :=
      [.leaf leafP, .arg (attackArgCert assurance), .arg attackArgS,
        .arg attackArgT, .attack attackDeclaration] }

def attackInput : Lara.Surface.Input :=
  ⟨attackProgram kernelCertificate, attackPolicy⟩

def attackInputWrapped : Lara.Surface.Input :=
  ⟨attackProgram wrappedCertificate, attackPolicy⟩

/-! ### Core terms

`certCore` is `SurfaceTransport.transportCore`; the two defeasible terms carry
it as their single premise, which is what makes `mapAssurAtt certSwap` move the
declared attack. -/

def certCore (coreAssur : Lara.Support.Assurance) : Lara.Support.SupportTerm :=
  transportCore coreAssur

def sCore (coreAssur : Lara.Support.Assurance) : Lara.Support.SupportTerm :=
  .inst ⟨"r-s"⟩ [] [certCore coreAssur] [] [] .none

def tCore (coreAssur : Lara.Support.Assurance) : Lara.Support.SupportTerm :=
  .inst ⟨"r-t"⟩ [] [certCore coreAssur] [] [] .none

/-- The one core attack. -/
def coreAttack (coreAssur : Lara.Support.Assurance) : Lara.Attack.Attack :=
  .rebut (sCore coreAssur) (tCore coreAssur)

/-! ### The reconstructed presentation terms -/

def builtCert (certificate : Cert) : PriorArgument :=
  ⟨argCertId,
    .rule transportRuleId [] (supportTermsFromList [transportResolved.term])
      (dischargesFromList []) [] (.cert certificate),
    .atom "q" .nil⟩

/-- The `a-cert` reference resolves on the *argument* side of the shared
namespace: no declared leaf is named `a-cert`, and exactly one prior is. -/
def resolvedCert (certificate : Cert) : ResolvedReference :=
  ⟨(builtCert certificate).term, .atom "q" .nil, none, some argCertId⟩

def builtS (certificate : Cert) : PriorArgument :=
  ⟨argSId,
    .rule sRuleId [] (supportTermsFromList [(resolvedCert certificate).term])
      (dischargesFromList []) [] .none,
    .atom "s" .nil⟩

def builtT (certificate : Cert) : PriorArgument :=
  ⟨argTId,
    .rule tRuleId [] (supportTermsFromList [(resolvedCert certificate).term])
      (dischargesFromList []) [] .none,
    .atom "t" .nil⟩

/-! ### The cheap `Checks` fields -/

theorem attack_supported : Lara.Surface.Supported attackInput := by
  apply (Lara.Surface.supportedB_iff attackInput).mp
  decide

theorem attack_supported_wrapped :
    Lara.Surface.Supported attackInputWrapped := by
  apply (Lara.Surface.supportedB_iff attackInputWrapped).mp
  decide

theorem attack_freshness :
    Lara.Surface.GeneratedIdsFresh attackInput.program = true := by decide

theorem attack_freshness_wrapped :
    Lara.Surface.GeneratedIdsFresh attackInputWrapped.program = true := by decide

/-! ### The three argument derivations

The certified one repeats `#227`'s: `ChecksArgument.inferred`, with `hlower`
the single obligation on the kernel-opaque path. The two defeasible ones
resolve their premise against the *prior argument* `a-cert` and carry
`ChecksAssurance.none`, so they add no lowering obligation at all. -/

theorem attack_checksArgument_cert
    {env : Lara.Surface.Env (fun source => source)}
    (certificate : Cert) (coreAssur : Lara.Support.Assurance)
    (hlower : lowerAssuranceCertificate env (attackProgram (.cert certificate))
        transportRule [] [transportResolved.term] (.cert certificate)
      = some coreAssur) :
    ChecksArgument env (attackProgram (.cert certificate)) attackPolicy []
      (attackArgCert (.cert certificate)) (builtCert certificate)
      (certCore coreAssur) := by
  refine ChecksArgument.inferred
    (rule := transportRule) (resolved := [transportResolved]) (theta := [])
    (conclusion := .atom "q" .nil)
    (.here rfl) rfl ?_ ?_ ?_ ?_ rfl .supportsDerived ?_
  · exact .cons (.leaf rfl rfl) .nil
  · exact .cons rfl .nil
  · intro param hparam; simp [transportRule] at hparam
  · exact .nil
  · exact .rule (.here rfl) (.cons .leaf .nil) .nil (.cert hlower)

/-- The certified argument's own lowering, cited from inside the two defeasible
arguments' certificate derivations. The priors and premises differ from the
`a-cert` declaration site, which is why `transport_lower_kernel` /
`transport_lower_wrapped` are stated universally in both. -/
theorem attack_checksCertificate_cert
    {env : Lara.Surface.Env (fun source => source)}
    {priors : List PriorArgument}
    (certificate : Cert) (coreAssur : Lara.Support.Assurance)
    (hlower : lowerAssuranceCertificate env (attackProgram (.cert certificate))
        transportRule priors [transportResolved.term] (.cert certificate)
      = some coreAssur) :
    ChecksCertificate env (attackProgram (.cert certificate)) attackPolicy priors
      (builtCert certificate).term (certCore coreAssur) :=
  .rule (.here rfl) (.cons .leaf .nil) .nil (.cert hlower)

theorem attack_checksArgument_s
    {env : Lara.Surface.Env (fun source => source)}
    (certificate : Cert) (coreAssur : Lara.Support.Assurance)
    (hlower : lowerAssuranceCertificate env (attackProgram (.cert certificate))
        transportRule [builtCert certificate] [transportResolved.term]
        (.cert certificate)
      = some coreAssur) :
    ChecksArgument env (attackProgram (.cert certificate)) attackPolicy
      [builtCert certificate] attackArgS (builtS certificate)
      (sCore coreAssur) := by
  refine ChecksArgument.inferred
    (rule := sRule) (resolved := [resolvedCert certificate]) (theta := [])
    (conclusion := .atom "s" .nil)
    (.there (by decide) (.here rfl)) rfl ?_ ?_ ?_ ?_ rfl .supportsDerived ?_
  · exact .cons (.argument rfl rfl) .nil
  · exact .cons rfl .nil
  · intro param hparam; simp [sRule] at hparam
  · exact .nil
  · exact .rule (.there (by decide) (.here rfl))
      (.cons (attack_checksCertificate_cert certificate coreAssur hlower) .nil)
      .nil .none

theorem attack_checksArgument_t
    {env : Lara.Surface.Env (fun source => source)}
    (certificate : Cert) (coreAssur : Lara.Support.Assurance)
    (hlower : lowerAssuranceCertificate env (attackProgram (.cert certificate))
        transportRule [builtCert certificate, builtS certificate]
        [transportResolved.term] (.cert certificate)
      = some coreAssur) :
    ChecksArgument env (attackProgram (.cert certificate)) attackPolicy
      [builtCert certificate, builtS certificate] attackArgT (builtT certificate)
      (tCore coreAssur) := by
  refine ChecksArgument.inferred
    (rule := tRule) (resolved := [resolvedCert certificate]) (theta := [])
    (conclusion := .atom "t" .nil)
    (.there (by decide) (.there (by decide) (.here rfl))) rfl ?_ ?_ ?_ ?_ rfl
    .supportsDerived ?_
  · exact .cons (.argument rfl rfl) .nil
  · exact .cons rfl .nil
  · intro param hparam; simp [tRule] at hparam
  · exact .nil
  · exact .rule (.there (by decide) (.there (by decide) (.here rfl)))
      (.cons (attack_checksCertificate_cert certificate coreAssur hlower) .nil)
      .nil .none

/-! ### The declaration fold -/

def attackPairs (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    List ReconstructedArgument :=
  [⟨attackArgCert (.cert certificate), builtCert certificate, certCore coreAssur⟩,
    ⟨attackArgS, builtS certificate, sCore coreAssur⟩,
    ⟨attackArgT, builtT certificate, tCore coreAssur⟩]

theorem attack_checksProgram_kernel :
    ChecksProgram transportEnv (attackProgram kernelCertificate) attackPolicy
      (attackProgram kernelCertificate).decls []
      (attackPairs kernelCert kernelCoreAssur) :=
  .cons .leaf
    (.cons (.arg (attack_checksArgument_cert kernelCert kernelCoreAssur
        (transport_lower_kernel _ _ _ _)))
      (.cons (.arg (attack_checksArgument_s kernelCert kernelCoreAssur
          (transport_lower_kernel _ _ _ _)))
        (.cons (.arg (attack_checksArgument_t kernelCert kernelCoreAssur
            (transport_lower_kernel _ _ _ _)))
          (.cons .attack .nil))))

theorem attack_checksProgram_wrapped :
    ChecksProgram transportEnvWrapped (attackProgram wrappedCertificate)
      attackPolicy (attackProgram wrappedCertificate).decls []
      (attackPairs wrappedCert wrappedCoreAssur) :=
  .cons .leaf
    (.cons (.arg (attack_checksArgument_cert wrappedCert wrappedCoreAssur
        (transport_lower_wrapped _ _ _ _)))
      (.cons (.arg (attack_checksArgument_s wrappedCert wrappedCoreAssur
          (transport_lower_wrapped _ _ _ _)))
        (.cons (.arg (attack_checksArgument_t wrappedCert wrappedCoreAssur
            (transport_lower_wrapped _ _ _ _)))
          (.cons .attack .nil))))

/-! ### The resolved attack -/

theorem attack_checksAttacks (certificate : Cert)
    (coreAssur : Lara.Support.Assurance) :
    ChecksAttacks attackPolicy
      ((attackPairs certificate coreAssur).map
        fun pair => (pair.argument.id, pair.core))
      (surfaceAttacksOf (attackProgram (.cert certificate)))
      [coreAttack coreAssur] :=
  .cons (.rebut rfl rfl) .nil

/-! ### The elaborated carrier

As in `#227`, every field is *defined* as the expression the corresponding
`Checks` field compares against. The two attack-carrying fields are the
literal one-element lists, which is what makes `unitAttacks` `rfl` and the
`selectResolvedAttacks` equation a computation. -/

def attackKept (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    List ReconstructedArgument :=
  keptReconstructed (fun source => source) attackPolicy
    (attackProgram (.cert certificate)) (attackPairs certificate coreAssur)

def attackElaborated (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    Lara.Surface.Elaborated (fun source => source) where
  gamma := surfaceGamma (fun source => source) attackPolicy
    (attackProgram (.cert certificate))
  ground := surfaceGround (fun source => source) attackPolicy
    (attackProgram (.cert certificate))
  unit :=
    { sigma := attackPolicy.sigma
      policy := toCorePolicy attackPolicy
      args := (attackKept certificate coreAssur).map (·.core)
      atts := [coreAttack coreAssur] }
  claims := claimsOf (attackKept certificate coreAssur)
    (attackProgram (.cert certificate))
  argIds := (attackKept certificate coreAssur).map (·.argument.id)
  authoredObligations := authoredObligationsOf (attackProgram (.cert certificate))
  openQuestions := openQuestionsOf (attackKept certificate coreAssur)
  resolvedAttacks := [coreAttack coreAssur]
  semanticProgram := attackProgram (.cert certificate)

theorem attack_expansions (certificate : Cert) :
    ∃ mid target generated,
      ExpandsValues (attackProgram (.cert certificate)) mid ∧
        GeneratedIdsFresh mid = true ∧
        (comparisonKeys mid).Nodup ∧
        ExpandsComparisons attackPolicy mid target generated ∧
        target = attackProgram (.cert certificate) :=
  ⟨attackProgram (.cert certificate), attackProgram (.cert certificate), [],
    expandValues_sound attackPolicy rfl,
    rfl,
    by simp [comparisonKeys, comparisonDecls, attackProgram],
    expandComparisons_sound attackPolicy rfl,
    rfl⟩

/-! ### Core support -/

theorem attack_gamma_leafP (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    (attackElaborated certificate coreAssur).gamma ⟨"l-p"⟩
      = some (.atom "p" .nil) := rfl

theorem attack_ruleLookup_cert (certificate : Cert)
    (coreAssur : Lara.Support.Assurance) :
    (attackElaborated certificate coreAssur).unit.policy.ruleLookup ⟨"r-cert"⟩
      = some (toCoreRule transportRule) := rfl

theorem attack_ruleLookup_s (certificate : Cert)
    (coreAssur : Lara.Support.Assurance) :
    (attackElaborated certificate coreAssur).unit.policy.ruleLookup ⟨"r-s"⟩
      = some (toCoreRule sRule) := rfl

theorem attack_ruleLookup_t (certificate : Cert)
    (coreAssur : Lara.Support.Assurance) :
    (attackElaborated certificate coreAssur).unit.policy.ruleLookup ⟨"r-t"⟩
      = some (toCoreRule tRule) := rfl

/-- **The certified argument is supported**, exactly as in `#227`. -/
theorem attack_hasSupport_cert
    {reg : Lara.Support.BackendRegistry (fun source => source)}
    (certificate : Cert) (coreAssur : Lara.Support.Assurance)
    {β : Lara.Support.BackendId} {digest : Lara.Support.Digest}
    {κ : Lara.Support.CertRef}
    (hassur : coreAssur = .cert β digest κ)
    (hallow : (β, digest) ∈ (toCoreRule transportRule).certifiers)
    (hacc : Lara.Support.certOkOf reg β digest κ [.atom "p" .nil] (.atom "q" .nil)) :
    Lara.Support.HasSupport (fun source => source)
      (attackElaborated certificate coreAssur).unit.policy.ruleLookup
      (attackElaborated certificate coreAssur).gamma
      (Lara.Support.certOkOf reg) (certCore coreAssur)
      (.atom "q" .nil) [] := by
  subst hassur
  refine Lara.Support.HasSupport.inst
    (As := [.atom "p" .nil]) (Cs := [.atom "p" .nil]) (Os := [[]])
    (DCs := []) (DOs := [])
    { rule := attack_ruleLookup_cert certificate _
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
        exact .leaf (attack_gamma_leafP certificate _)
    | succ n => simp at hw
  · intro j q w A O hj; simp at hj

/-- **A plain defeasible argument over the certified one is supported.**
Stated once for both `r-s` and `r-t`: the rule, its lookup and its conclusion
are the only things that differ, and the assurance side condition is
`AssuranceOk.defeasible`, which needs no registry at all. -/
theorem attack_hasSupport_plain
    {reg : Lara.Support.BackendRegistry (fun source => source)}
    (certificate : Cert) (coreAssur : Lara.Support.Assurance)
    {rn : Lara.Support.RuleId} {rule : Presentation.Rule} {conclusion : Lara.Atom}
    (hrule : (attackElaborated certificate coreAssur).unit.policy.ruleLookup rn
      = some (toCoreRule rule))
    (hmode : rule.mode = .defeasible)
    (hprem : rule.premises = [⟨"q", .nil⟩])
    (hparams : rule.params = [])
    (hquestions : rule.questions = [])
    (hconcl : Lara.Support.instAPat [] (toCoreRule rule).concl = some conclusion)
    (hcert : Lara.Support.HasSupport (fun source => source)
      (attackElaborated certificate coreAssur).unit.policy.ruleLookup
      (attackElaborated certificate coreAssur).gamma
      (Lara.Support.certOkOf reg) (certCore coreAssur) (.atom "q" .nil) []) :
    Lara.Support.HasSupport (fun source => source)
      (attackElaborated certificate coreAssur).unit.policy.ruleLookup
      (attackElaborated certificate coreAssur).gamma
      (Lara.Support.certOkOf reg)
      (.inst rn [] [certCore coreAssur] [] [] .none) conclusion [] := by
  refine Lara.Support.HasSupport.inst
    (As := [.atom "q" .nil]) (Cs := [.atom "q" .nil]) (Os := [[]])
    (DCs := []) (DOs := [])
    { rule := hrule
      θNodup := by decide
      θDom := by intro x; simp [toCoreRule, hparams]
      prems := by simp [toCoreRule, hprem, Lara.Support.instAPats,
        Lara.Support.instAPat, toCoreAtomPat, toCorePats, Lara.Support.instPats]
      concl := hconcl
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
      qNodup := by simp [Lara.Support.questionNames, toCoreRule, hquestions]
      dNodup := by decide
      hNodup := by decide
      cover := by intro qd hqd; simp [toCoreRule, hquestions] at hqd
      disj := by intro n hn; simp at hn
      keysD := by intro n hn; simp at hn
      keysH := by intro n hn; simp at hn
      strictNoQ := by
        intro hstrict
        simp [toCoreRule, hmode] at hstrict
      assur := .defeasible (by simp [toCoreRule, hmode]) } ?_ ?_
  · intro i w A O hw hA hO
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hA hO
        subst hw; subst hA; subst hO
        exact hcert
    | succ n => simp at hw
  · intro j q w A O hj; simp at hj

/-! ### Conclusion inversion

`AttackComplete` quantifies over conclusion atoms rather than over terms, so
ruling out the eight non-edges needs the conclusion each declared term
actually carries. -/

theorem attack_concl_of_inst
    {Pi : Lara.Support.RuleId → Option Lara.Support.Rule}
    {Gamma : Lara.Support.LeafId → Option Lara.Atom}
    {CertOk : Lara.Support.BackendId → Lara.Support.Digest →
      Lara.Support.CertRef → List Lara.Atom → Lara.Atom → Prop}
    {rn : Lara.Support.RuleId} {θ : Lara.Support.Subst}
    {ws : List Lara.Support.SupportTerm}
    {D : List (Lara.Support.QuestionId × Lara.Support.SupportTerm)}
    {H : List Lara.Support.QuestionId} {α : Lara.Support.Assurance}
    {C : Lara.Atom} {O : List Lara.Support.QuestionId}
    (h : Lara.Support.HasSupport (fun source => source) Pi Gamma CertOk
      (.inst rn θ ws D H α) C O) :
    ∃ r, Pi rn = some r ∧ Lara.Support.instAPat θ r.concl = some C := by
  cases h with
  | inst hside _ _ => exact ⟨_, hside.rule, hside.concl⟩

/-! ### The core obligations

Unlike `#227`, the four attack-side fields are real: there is one declared
attack, it must type, both endpoints must be declared arguments, and
`AttackComplete` must account for all nine ordered pairs. -/

theorem attack_args (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    (attackElaborated certificate coreAssur).unit.args
      = [certCore coreAssur, sCore coreAssur, tCore coreAssur] := rfl

theorem attack_atts (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    (attackElaborated certificate coreAssur).unit.atts
      = [coreAttack coreAssur] := rfl

/-- The one declared contrary, as the core policy stores it. -/
theorem attack_contraries (certificate : Cert)
    (coreAssur : Lara.Support.Assurance) :
    (attackElaborated certificate coreAssur).unit.policy.defeat.contraries
      = [(toCoreAtomPat ⟨"s", .nil⟩, toCoreAtomPat ⟨"t", .nil⟩)] := rfl

/-- `q` is the only strict-reachable conclusion pattern — which is exactly why
the contrary above has to be `s ~ t` and not anything mentioning `q`. -/
theorem attack_strictConclusions (certificate : Cert)
    (coreAssur : Lara.Support.Assurance) :
    Lara.Policy.strictConclusions (attackElaborated certificate coreAssur).unit.policy
      = [toCoreAtomPat ⟨"q", .nil⟩] := rfl

/-- The declared contrary, in the relational form `HasAttack.rebut` wants. -/
theorem attack_contraryMatch :
    Lara.Attack.ContraryMatch (fun source => source)
      (toCorePolicy attackPolicy).defeat (.atom "s" .nil) (.atom "t" .nil) :=
  ⟨(toCoreAtomPat ⟨"s", .nil⟩, toCoreAtomPat ⟨"t", .nil⟩), by decide,
    [], .atom "s" .nil, .atom "t" .nil, rfl, rfl, rfl, rfl⟩

/-- `s` and `t` are distinct up to `≡`, which is what excuses the seven
non-edges `AttackComplete` would otherwise demand. -/
theorem attack_s_ne_t :
    ¬ Lara.equiv (fun source => source) (.atom "s" .nil) (.atom "t" .nil) := by
  decide

theorem attack_s_ne_q :
    ¬ Lara.equiv (fun source => source) (.atom "s" .nil) (.atom "q" .nil) := by
  decide

/-- The conclusion of each declared argument, read back off its support
derivation. `AttackComplete` quantifies over conclusion atoms, so this is what
turns "the source is one of three terms" into "the source's conclusion is one
of three atoms". -/
theorem attack_concl_cert (certificate : Cert)
    {reg : Lara.Support.BackendRegistry (fun source => source)}
    {C : Lara.Atom} {O : List Lara.Support.QuestionId}
    {coreAssur : Lara.Support.Assurance}
    (h : Lara.Support.HasSupport (fun source => source)
      (attackElaborated certificate coreAssur).unit.policy.ruleLookup
      (attackElaborated certificate coreAssur).gamma
      (Lara.Support.certOkOf reg) (certCore coreAssur) C O) :
    C = .atom "q" .nil := by
  obtain ⟨r, hr, hconcl⟩ := attack_concl_of_inst h
  rw [attack_ruleLookup_cert certificate coreAssur] at hr
  cases hr
  exact (Option.some.inj hconcl).symm

theorem attack_concl_s (certificate : Cert)
    {reg : Lara.Support.BackendRegistry (fun source => source)}
    {C : Lara.Atom} {O : List Lara.Support.QuestionId}
    {coreAssur : Lara.Support.Assurance}
    (h : Lara.Support.HasSupport (fun source => source)
      (attackElaborated certificate coreAssur).unit.policy.ruleLookup
      (attackElaborated certificate coreAssur).gamma
      (Lara.Support.certOkOf reg) (sCore coreAssur) C O) :
    C = .atom "s" .nil := by
  obtain ⟨r, hr, hconcl⟩ := attack_concl_of_inst h
  rw [attack_ruleLookup_s certificate coreAssur] at hr
  cases hr
  exact (Option.some.inj hconcl).symm

theorem attack_concl_t (certificate : Cert)
    {reg : Lara.Support.BackendRegistry (fun source => source)}
    {C : Lara.Atom} {O : List Lara.Support.QuestionId}
    {coreAssur : Lara.Support.Assurance}
    (h : Lara.Support.HasSupport (fun source => source)
      (attackElaborated certificate coreAssur).unit.policy.ruleLookup
      (attackElaborated certificate coreAssur).gamma
      (Lara.Support.certOkOf reg) (tCore coreAssur) C O) :
    C = .atom "t" .nil := by
  obtain ⟨r, hr, hconcl⟩ := attack_concl_of_inst h
  rw [attack_ruleLookup_t certificate coreAssur] at hr
  cases hr
  exact (Option.some.inj hconcl).symm

/-- The certified argument is not conflict-attackable: its root rule is
strict. This is what excuses the three ordered pairs whose target is
`a-cert`. -/
theorem attack_cert_not_attackable (certificate : Cert)
    (coreAssur : Lara.Support.Assurance) :
    ¬ Lara.Compile.ConflictAttackable
        (attackElaborated certificate coreAssur).unit.policy.ruleLookup
        (certCore coreAssur) := by
  rintro ⟨r, hr, hmode⟩
  rw [attack_ruleLookup_cert certificate coreAssur] at hr
  cases hr
  exact absurd hmode (by decide)

/-- **The one declared attack types.** Parameterised over the registry and the
certified argument's support, so both programs use it. -/
theorem attack_hasAttack
    {reg : Lara.Support.BackendRegistry (fun source => source)}
    (certificate : Cert) (coreAssur : Lara.Support.Assurance)
    (hcert : Lara.Support.HasSupport (fun source => source)
      (attackElaborated certificate coreAssur).unit.policy.ruleLookup
      (attackElaborated certificate coreAssur).gamma
      (Lara.Support.certOkOf reg) (certCore coreAssur) (.atom "q" .nil) []) :
    Lara.Attack.HasAttack (fun source => source)
      (attackElaborated certificate coreAssur).unit.policy.ruleLookup
      (attackElaborated certificate coreAssur).gamma
      (Lara.Support.certOkOf reg)
      (attackElaborated certificate coreAssur).unit.policy.defeat
      (coreAttack coreAssur) :=
  .rebut
    (attack_hasSupport_plain certificate coreAssur
      (attack_ruleLookup_s certificate coreAssur) rfl rfl rfl rfl rfl hcert)
    (attack_ruleLookup_t certificate coreAssur) rfl rfl attack_contraryMatch

/-- **Attack completeness.** Of the nine ordered pairs, three are excused
because the target is the strict certified argument, five because the declared
contrary forces the source's conclusion to be `s` and the target's to be `t`,
and the one that survives is exactly the declared attack. -/
theorem attack_attackComplete
    {reg : Lara.Support.BackendRegistry (fun source => source)}
    (certificate : Cert) (coreAssur : Lara.Support.Assurance) :
    Lara.Compile.AttackComplete (fun source => source)
      (attackElaborated certificate coreAssur).unit.policy.ruleLookup
      (attackElaborated certificate coreAssur).gamma
      (Lara.Support.certOkOf reg)
      (attackElaborated certificate coreAssur).unit.policy.defeat
      (attackElaborated certificate coreAssur).unit.args
      (attackElaborated certificate coreAssur).unit.atts := by
  intro source hsource target htarget sourceConclusion targetConclusion
    hsupSource hsupTarget hmatch hattackable
  rw [attack_args] at hsource htarget
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsource htarget
  obtain ⟨ab, hab, ρ, pa, pb, hpa, hpb, hea, heb⟩ := hmatch
  rw [attack_contraries] at hab
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  subst hab
  have hpa' : pa = .atom "s" .nil := (Option.some.inj hpa).symm
  have hpb' : pb = .atom "t" .nil := (Option.some.inj hpb).symm
  subst hpa'; subst hpb'
  -- the source's conclusion is `s`, so the source is `a-s`
  have hsourceIsS : source = sCore coreAssur := by
    rcases hsource with h | h | h
    · subst h
      rw [attack_concl_cert certificate hsupSource] at hea
      exact absurd hea attack_s_ne_q
    · exact h
    · subst h
      rw [attack_concl_t certificate hsupSource] at hea
      exact absurd hea attack_s_ne_t
  -- the target's conclusion is `t`, so the target is `a-t`
  have htargetIsT : target = tCore coreAssur := by
    rcases htarget with h | h | h
    · exact absurd (h ▸ hattackable) (attack_cert_not_attackable certificate coreAssur)
    · subst h
      rw [attack_concl_s certificate hsupTarget] at heb
      exact absurd (Lara.equiv_symm (fun source => source) heb) attack_s_ne_t
    · exact h
  subst hsourceIsS; subst htargetIsT
  refine ⟨coreAttack coreAssur, ?_, rfl, tCore coreAssur, rfl,
    Lara.Compile.contains_refl _⟩
  rw [attack_atts]
  exact List.mem_cons_self

theorem attack_coreObligations_kernel :
    CoreObligations transportEnv (attackElaborated kernelCert kernelCoreAssur) where
  sigmaWellFormed := by decide
  policyWellSorted := by decide
  groundWellSorted := by decide
  argsWellSorted := by decide
  scopesWellFormed := by decide
  ruleIdsNodup := by decide
  policyWellFormed := by
    intro p hp ab hab
    have hp' := Lara.Policy.strictReachable_iff_mem.mp hp
    rw [attack_strictConclusions] at hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    rw [attack_contraries] at hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
    subst hab
    exact ⟨by decide, by decide⟩
  argsNodup := by decide
  supports := by
    intro term hterm
    rw [attack_args] at hterm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hterm
    have hcert := attack_hasSupport_cert kernelCert kernelCoreAssur rfl (by decide)
      transport_cert_accepted
    rcases hterm with h | h | h <;> subst h
    · exact ⟨.atom "q" .nil, hcert⟩
    · exact ⟨.atom "s" .nil,
        attack_hasSupport_plain kernelCert kernelCoreAssur
          (attack_ruleLookup_s _ _) rfl rfl rfl rfl rfl hcert⟩
    · exact ⟨.atom "t" .nil,
        attack_hasSupport_plain kernelCert kernelCoreAssur
          (attack_ruleLookup_t _ _) rfl rfl rfl rfl rfl hcert⟩
  attacksTyped := by
    intro attack hattack
    rw [attack_atts] at hattack
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hattack
    subst hattack
    exact attack_hasAttack kernelCert kernelCoreAssur
      (attack_hasSupport_cert kernelCert kernelCoreAssur rfl (by decide)
        transport_cert_accepted)
  sourcesDeclared := by
    intro attack hattack
    rw [attack_atts] at hattack
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hattack
    subst hattack
    rw [attack_args]
    exact List.mem_cons_of_mem _ (List.mem_cons_self)
  targetsDeclared := by
    intro attack hattack
    rw [attack_atts] at hattack
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hattack
    subst hattack
    rw [attack_args]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  attackComplete := attack_attackComplete kernelCert kernelCoreAssur

theorem attack_coreObligations_wrapped :
    CoreObligations transportEnvWrapped
      (attackElaborated wrappedCert wrappedCoreAssur) where
  sigmaWellFormed := by decide
  policyWellSorted := by decide
  groundWellSorted := by decide
  argsWellSorted := by decide
  scopesWellFormed := by decide
  ruleIdsNodup := by decide
  policyWellFormed := by
    intro p hp ab hab
    have hp' := Lara.Policy.strictReachable_iff_mem.mp hp
    rw [attack_strictConclusions] at hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    rw [attack_contraries] at hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
    subst hab
    exact ⟨by decide, by decide⟩
  argsNodup := by decide
  supports := by
    intro term hterm
    rw [attack_args] at hterm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hterm
    have hcert := attack_hasSupport_cert wrappedCert wrappedCoreAssur rfl (by decide)
      transport_cert_accepted_wrapped_raw
    rcases hterm with h | h | h <;> subst h
    · exact ⟨.atom "q" .nil, hcert⟩
    · exact ⟨.atom "s" .nil,
        attack_hasSupport_plain wrappedCert wrappedCoreAssur
          (attack_ruleLookup_s _ _) rfl rfl rfl rfl rfl hcert⟩
    · exact ⟨.atom "t" .nil,
        attack_hasSupport_plain wrappedCert wrappedCoreAssur
          (attack_ruleLookup_t _ _) rfl rfl rfl rfl rfl hcert⟩
  attacksTyped := by
    intro attack hattack
    rw [attack_atts] at hattack
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hattack
    subst hattack
    exact attack_hasAttack wrappedCert wrappedCoreAssur
      (attack_hasSupport_cert wrappedCert wrappedCoreAssur rfl (by decide)
        transport_cert_accepted_wrapped_raw)
  sourcesDeclared := by
    intro attack hattack
    rw [attack_atts] at hattack
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hattack
    subst hattack
    rw [attack_args]
    exact List.mem_cons_of_mem _ (List.mem_cons_self)
  targetsDeclared := by
    intro attack hattack
    rw [attack_atts] at hattack
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hattack
    subst hattack
    rw [attack_args]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  attackComplete := attack_attackComplete wrappedCert wrappedCoreAssur

/-! ### The complete surface judgments -/

theorem attack_checks_kernel :
    Lara.Surface.Checks transportEnv attackInput
      (attackElaborated kernelCert kernelCoreAssur) where
  supported := attack_supported
  admission := ⟨by decide, by
    intro leaf hleaf
    have hleafP : leaf = leafP := by
      simpa [leafRecords, attackInput, attackInputWrapped, attackProgram]
        using hleaf
    subst hleafP
    decide⟩
  freshness := attack_freshness
  rules := by
    intro rule hrule
    refine .intro (attack_supported.rule_namespaces_wf.2 rule hrule) (.inl ?_)
    have hr : rule = transportRule ∨ rule = sRule ∨ rule = tRule := by
      simpa [attackInput, attackPolicy] using hrule
    rcases hr with h | h | h <;> subst h <;> rfl
  statuses := (statusesWellFormedB_iff _).mp (by decide)
  groups := (groupsWellFormedB_iff _).mp (by decide)
  expansions := attack_expansions kernelCert
  program :=
    ⟨attackPairs kernelCert kernelCoreAssur, [coreAttack kernelCoreAssur],
      attack_checksProgram_kernel, by decide,
      attack_checksAttacks kernelCert kernelCoreAssur, rfl, rfl, rfl, rfl, rfl⟩
  gamma := rfl
  ground := rfl
  sigma := rfl
  unitPolicy := rfl
  unitAttacks := rfl
  authoredObligations := rfl
  core := attack_coreObligations_kernel

theorem attack_checks_wrapped :
    Lara.Surface.Checks transportEnvWrapped attackInputWrapped
      (attackElaborated wrappedCert wrappedCoreAssur) where
  supported := attack_supported_wrapped
  admission := ⟨by decide, by
    intro leaf hleaf
    have hleafP : leaf = leafP := by
      simpa [leafRecords, attackInput, attackInputWrapped, attackProgram]
        using hleaf
    subst hleafP
    decide⟩
  freshness := attack_freshness_wrapped
  rules := by
    intro rule hrule
    refine .intro (attack_supported_wrapped.rule_namespaces_wf.2 rule hrule) (.inl ?_)
    have hr : rule = transportRule ∨ rule = sRule ∨ rule = tRule := by
      simpa [attackInputWrapped, attackPolicy] using hrule
    rcases hr with h | h | h <;> subst h <;> rfl
  statuses := (statusesWellFormedB_iff _).mp (by decide)
  groups := (groupsWellFormedB_iff _).mp (by decide)
  expansions := attack_expansions wrappedCert
  program :=
    ⟨attackPairs wrappedCert wrappedCoreAssur, [coreAttack wrappedCoreAssur],
      attack_checksProgram_wrapped, by decide,
      attack_checksAttacks wrappedCert wrappedCoreAssur, rfl, rfl, rfl, rfl, rfl⟩
  gamma := rfl
  ground := rfl
  sigma := rfl
  unitPolicy := rfl
  unitAttacks := rfl
  authoredObligations := rfl
  core := attack_coreObligations_wrapped

/-! ### Core acceptance -/

theorem attack_checkUnit_kernel :
    ∃ checked, Lara.Check.Unit.checkUnit
      (attackElaborated kernelCert kernelCoreAssur).gamma transportEnv.registry
      (attackElaborated kernelCert kernelCoreAssur).ground
      (attackElaborated kernelCert kernelCoreAssur).unit = .ok checked :=
  attack_coreObligations_kernel.checkUnit_complete

theorem attack_checkUnit_wrapped :
    ∃ checked, Lara.Check.Unit.checkUnit
      (attackElaborated wrappedCert wrappedCoreAssur).gamma
      transportEnvWrapped.registry
      (attackElaborated wrappedCert wrappedCoreAssur).ground
      (attackElaborated wrappedCert wrappedCoreAssur).unit = .ok checked :=
  attack_coreObligations_wrapped.checkUnit_complete

/-! ### The instantiation -/

/-- **The M4 surface corollary, witnessed with a live edge.** Same statement as
`SurfaceTransport.surfaceTransport_directAF_eq`, but the two programs declare a
rebut, so `checkedAF_map`'s edge half runs `coveredB_relabel` on a one-element
attack list rather than on `[]`. -/
theorem surfaceTransportAttack_directAF_eq :
    Lara.Surface.directAF attack_checks_wrapped
      = Lara.Surface.directAF attack_checks_kernel := by
  obtain ⟨acc₁, hchecked₁⟩ := attack_checkUnit_kernel
  obtain ⟨acc₂, hchecked₂⟩ := attack_checkUnit_wrapped
  have hs₁ := Lara.Check.Unit.checkUnit_sound hchecked₁
  have hs₂ := Lara.Check.Unit.checkUnit_sound hchecked₂
  refine Lara.Context.surface_directAF_relabel
    attack_checks_kernel hchecked₁ attack_checks_wrapped hchecked₂
    certSwap_injective ?_ ?_
  · rw [hs₂.args_eq, hs₁.args_eq]; rfl
  · rw [hs₂.atts_eq, hs₁.atts_eq]; rfl

/-! ### Non-vacuity

The first three guards are the ones `#258` asks for: the attack set is not
empty, the relabel moves it, and the witnessed framework really has an edge.
The last two are `#227`'s, restated for this fixture. -/

/-- **The attack set is non-empty**, on both sides. Without this the fixture
could silently regress to `#227`'s degenerate case, where `coveredB_relabel` is
applied to `[]`. -/
theorem surfaceTransportAttack_atts_nonempty :
    (attackElaborated kernelCert kernelCoreAssur).unit.atts ≠ [] ∧
      (attackElaborated wrappedCert wrappedCoreAssur).unit.atts ≠ [] := by
  refine ⟨?_, ?_⟩ <;> rw [attack_atts] <;> exact List.cons_ne_nil _ _

/-- **The relabel moves the attack, not merely the argument list.** Both stored
terms of the declared rebut carry the certificate as a premise, so
`mapAssurAtt certSwap` is not the identity on this fixture's attack list. -/
theorem surfaceTransportAttack_relabel_moves_atts :
    (attackElaborated wrappedCert wrappedCoreAssur).unit.atts
      ≠ (attackElaborated kernelCert kernelCoreAssur).unit.atts := by
  rw [attack_atts, attack_atts]
  intro h
  simp only [List.cons.injEq, coreAttack, Lara.Attack.Attack.rebut.injEq,
    and_true] at h
  exact absurd h.1 (by decide)

/-- **The witnessed framework has an edge.** Node 1 is `a-s` and node 2 is
`a-t` in retained declaration order, and the framework the surface layer
exposes puts an attack between them — on both sides of the relabel. -/
theorem surfaceTransportAttack_directAF_edge :
    (Lara.Surface.directAF attack_checks_kernel).attack 1 2 = true ∧
      (Lara.Surface.directAF attack_checks_wrapped).attack 1 2 = true := by
  constructor <;> decide

/-- **The relabel actually moved the elaborated unit.** -/
theorem surfaceTransportAttack_relabel_moves :
    (attackElaborated wrappedCert wrappedCoreAssur).unit.args
      ≠ (attackElaborated kernelCert kernelCoreAssur).unit.args := by
  decide

/-- **The two surface programs are two programs**, not one cited twice. -/
theorem surfaceTransportAttack_inputs_differ :
    attackInputWrapped ≠ attackInput := by decide

end Lara.Examples.SurfaceTransportAttack
